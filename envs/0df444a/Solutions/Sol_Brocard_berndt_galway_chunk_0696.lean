-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0696
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:12:01.059856+00:00
-- url     : https://prove2.me/submissions/3aa66748-c8b6-4376-bd10-069d0fa6edd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125000000 ≤ n < 125179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125001250 1250 125000000 125000003
    0x120601080f06010206130311191419080a0302091509030705040618180f030c11011803030305060d02091005030d020a0f02150403051b010216051e0625 66
    0x4000c0d060751550401070080e00308484190040e0040700200d00b4000c00e43c1c030f00042c00e40c40b9040480070b981910301c415241502c40d803001198008040300107414007d4008201c50f4501d1000040c3c404641540c01040c0c109058540080941d0300c006181034000d80301e0b60544449000040001038204c403000c40c20032160708042592446402180d070001101c1ca0540f00b000101c0c1d0b00c24081440d607c2000009600604000c00c1c10724503d4988441000041e03499190002c20520036200e41010512504104507011551030009060001070711070182e00e01c0111030114216640362901080950303440c0e0104150700000d500c02508010041c00f800340c20003600c00100181e5405408a0740400b54079807080380d0725001c840b0302900b104081c501c00005420100c041c0c08076000f074011301c00d10302a903954559240c10380d000d8019001541c02c0680680c81c0da4103010450068074185260750013581400c0000d4052011803e002005401c4d04400008a494070b0342a01c16060f0700c2c4150710b000c80f011880001c0360f07403d031160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125002500 1250 125001250 125001257
    0x507030b030c01020717070305060a0e060105041404020409051e030405040e0a080f03060a1203020f010b03030306100305180a0c031a10060309050f0615010806030303010317130803120601 82
    0x440d9442800e000512080c1c0450581c0100080f500d0700b09441b03d00701902c407800c8442c0c0181c40000c000b280041060601603211072400090b000b096442185c203188041e00054031441c20030254140c0e40301104001ea80140c0c040b50009010351591030203c0c50100c02c449042140d107200036070215003100c0440504200e560548080c802d20004041180d11080c0840e4014850401404980412900c4001450b0b00c05400381003404410380700d000707003503218001400c12001a0301078211045001800c0c003c803041c0200a5004504500380303540003134813803540c0d80d81a80c101a0313594000341da52a428951101c485e00321505640202c5214280384080c00d0711800242c54600740d10346052103286c070f4001210f10840031980c1c08100d150800e4002c9002c0d0440840039103162107450b10440340100d06018880c09062250700c00d45c2c1d0140c841d0000f51401c040103040d98400e4200f840104046041030508140c84006030025030390300c08558020070130710415500401607611000c6010306c00e01c000590000d009400036203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125003750 1250 125002500 125002511
    0x40b0d140114120c151303080f090f0f0f040c09030230030f07020108070315090203150f06040911070804271509020d060306021201030b06010906021b0402071401050703 74
    0x3d64180e41e0300c0b030301e43e402600b282d800d40800c458a54140c000d40700e00c015400454081c6036582d101e0709220380041c10030501017070000804420b03914001010b5994a0000e030740c17911800d0000c00c0041c00361082882e1860003613803240b01b20540c007032081440700c01850380100b001001240140b066210003400d6420100a1600c815400004a5002003130b50203000d802c017412454030701c81e540115034024025129405051b00ca11406800051880c9203501604044200684030701d4030110301150000903600706409564011000507181e191300301110203030f035400500030490311800310744200c25201d00e05014164030307c041030204412034142d500000c2d405242c00c01c4800141e815a00c2ea0441d1000b002940900c41070300400c101c940e0b02034014001d1001900d00001e6500d550341c60314001d0703a2060b001403440a118600620801c003011040b507420110038a4151805800c0c24130203035444494240018058006104d007042540d03903601251540742d4041182a0071020305c03201280602020ba60700c5000c42c2c18038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125005000 1250 125003750 125003779
    0x405040615080613080d1409100614010e0907050c0f031201050906060304030305070e04021b0d030603080304030e0f10030e0c19060309061b02160b040506040b0d140114 74
    0x180480c01000f01441400c050b00319a07481e2406544111181500d1075128500060000310071190700d4230604449024000302d001034070b00d1108607420358000b0f0122200100340088180da001e668000720040945078000d09454100c01500c40d805811286211031040d00d08181c1c40803004001742035190225001021280d88540801405c0f5074201e41c403a401c481c05000080100b4031a070081c540000b818144400c0a24080f404034050364060b411202c51b188008011031800c960420907079413802070030300e4108070550444c1d03110303442480054070140802030182d0850381d1640c2c86601004401400909410b90025403140142c040c01e0400032800e414061410085c407079007004210f1000c02115000003d611310308007903094000301094081a980c40b0380c0c509607045644111b0b02d0b441841c10ad560000c00c03e103500c1a0201c20001e540d60041014100c00b88001c010302d4070740000740c800b55100c1007841d64443c0094000c0304018104925908008001382000107840003402040b8803203480300703450780e280280c1207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125006250 1250 125005000 125005003
    0x9130c0b04030f060c090f082503030207051e061306020613030912050f0a060e0706020a0506010303050f090d060e120c0d0e0111060a05010914190f0b040504061508 72
    0x8a00c00500840b40401c1c0c3c0c40005980c030781c02076001c28214208402010b445100411003008070741c1041c919a8001080d07000100394110f079144400c0045501841c12030b055981c000d44030842031055502138201c1045080d200d6880450050b4034607000780c492600d43c1601030141d8840106445000058050a0085201d0000c0c110206064503010345032501e0b007038a0301050643c180d64a58040d10240160705070710300d0560050004071100c07070180601040d2198011121403c3c041643e1100b010b650004407080b000480103c0c000d41103030b400d400c1c0182c0341e02003401040c3c864480e2040d540d40c8060561070304420400950300580c00c4080300710481303101c4042a98061002e216600c00d4503074680c401e0f0840045070384a8060720541c1c42041c03501a4514008900e00341c0b40000555074808156111001032200c224103120318040070207405207041582c24002d0001c0b06003901c90203048541505d03400e00305090b801e10b4202c50305800e0046d1042089140a0400b04000c00805180316190780c010640007800090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125007500 1250 125006250 125006257
    0x30801060219080903070e1608100e01060e0604090c021005100b09060c030c0d0f0f0f1b05011d0109060b0a050a0e040c090905030319020a0e04091109130c0b 69
    0x100c03040031a440380301946800889804c40d0348540d925104c1c1a5012a007900c0d204a60303801a507000b00400e01c1c03e5560400501072031402406010107452500003000005808683c041c115840c170300340100100004030100d9031611954006590f101c3c00c00a1000001d03500003010143d191241c80c081099840e44180414150043c0c072545000b042c05100710402d0703142002c010600044000c0440c0d00d0131841c20455810003080c81076030380120f900460061405604240f04241550191522000c100f21a48002e04008000d2080b0245036841403680d80c2004001d600001d648281100c410b0b60040200c2c00e442c1c06000c15550455070300b810115005034074181790b01040c00f0b544004145480513800c140205100f244000d1054030f2610041800007201002c0384103040c801400758015540d40c1c5000c1440061641800a12817829031040200780480790f400503c0b1204228200c50202d44e0350214105200200280e4400d59401f901c6c603001d0181d84111802e44070005403140306000d040760380d900c00f0400300b400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125008750 1250 125007500 125007523
    0x9050f06090f0301060906120b0a020304030504090b0a0905090f0708070305060402010c060b0a06030c1b0b1302030f010c090f06020636070308090f09090304050d05100507030204030308010602 84
    0x1445603210700d00d00a101c0b15007180000e400094801c2d46d4007032090a80710550310808102c02c4c2000030304103001c2007100c841c0e806411a0310030340c030b0f608066a009107244124030030803200036505e504c0c110040c3c2d0307036800b020000e10040400344900e041c0645540d48885c40d4204856461050b0440002c941e540440c0c0303c82200c2d0004003400a5075a150010340c1c0b0580780b10703811100296660480e04041e900d034a8100081d014030361300054501c61040014042a405104040c3c8030b034600f01c80d0740c002900310040b00f030f44030b40c522101c01c4a42c2c4082c40401c0c9803d05400d0252429424807280b4494668000e031000c088492421000d420990b945205070384444054620600c034180c42c203108244804d5100300115841c0340101d076a905050242d000070305101d03a0303800c1114080300000d5804454a052230006001e034101311200e00480c1030000c3e0307465503842944a82070007000d01a05c51401c0c00014009441040c0859505103c1454031000090003940140400c4020500890010a07018070007d010014803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125010000 1250 125008750 125008759
    0x507090605010e091b070606080706080c2811010f05041b0605040603090f021002060708060a05010e0d030201020c12030f1b030402012d18060509011b1704030b0709050f 74
    0x584031080b5261907010b11740e094000700d100802c283c1c00000e07584d20561000b014000003901c5142c1c00c01c00e004044102c00717800315447c45010b001d401100000c1042400150310300c0b1003401c6c0c07000d108510030350b103d04030441c2100d459440c1c00008030b40700000d504503502c903601c6480904540f98102d540c41c01c4d040600d0050000082091005102c030754025800070f41468002d05150034640d001c0c0e030005042d182d10450300d10040c2c11410900c0002a041600542c000d8012244800c0d481e041600091aa1403408002d40c840c80f0360800707650a25000703504071400e0500344406e56144144c1241001019031040e5590608461340100085122100d05540040764820001203446d685584d001125140d140003041811402c2c0d681c6c02c00042400b4003a002640c20640d12156a400e039a1440008600c8039a8071030002c0c010200f2031480ca07681d104403491b290154150312002003642c10304110f64800070346800030122180c00a40401400b800e22003603445140c29540d004002601c030307000d10004184602000303400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125011250 1250 125010000 125010019
    0x60f0207120c0f06020703032c0c0105160f21171317030106022103040203030a080a0906050a0516030e06010b1b120c070905010302011202031e040507090605010e 71
    0x80e0340318108890390742e4024020700e04800126250007040b41d10541003100070a81c3c4000d0108000078424200c142d00388075003035100c3e6032001191810388452506c06c440c2d04007d00010002d22402c1c1128040c00c00d16040091010300c58200e00d00100c05081745012400d400030400b1031800381c01e01c40d190743c1c0210428800d040301d03141c940307041c0c06103020b101c0b101c1101c819241e110b1600b984520a07001c2c42c0200710b2540100712a0b07618028007450b510014040d0030500c0c404108102c056100041150340300400e914040845589001c40313100103004045004107200d0900040c440100100e802c00e0b40500c03520581007003204a0440c0607012101d1042004200e0b4000324010460003448002400005a402100c1c1c504080101055401c20f82c050300c20030b40703400002c644e80400d0982005500050260084104891750460300068406802803040d80e8200d81c00000040c0c0d038660310030032512204055120a1040e00f00391034165100c081e00e016407040c003031920600007001e40c420030301c0d4104010040e00c3c2400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125012500 1250 125011250 125011283
    0x9100302070501020c060f0105100309110105130902040b09011e020a03140c011e060e0121030c02060d050a110f19020a02030f07030506070311090f19090504060f0207 73
    0x6500489002e03a0207550034001e186001701c0a0060500c168003442c1c180402c0e604000800c04440c8407c0c4500040614101403074000900109800e007101e102420265204c0e4291140c1e500564003d40001801c030303001107070000e41c401824000e0300d042c24090b2203441c4214052420361030040c16509101d801a80040c0100c0c0111b4000c525000107144012052880d1030f1500c0c0580703095400c000c903040c055007002c0d05407076485c00080c4900006094620303030750b0456514088079000b50411542c00c607002c00070f01400c008201400342c4d21000c80c00b079002e0400703501c0300b00c0b2980c0080206022a850071809082c181226528070f03000044600d071304403c500040c00c021442090700081801504800258410042c030140540d60070003280c940c100042000b007100500350328103079003410006414030017407500b0302403520032013038810003680d2004038141c81041d045900c07440012105103105107510b00c0031000c44004941045c103600114800c42c0120b10900c183c064501d81e082c101e101c0e0460161246884911185 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125013750 1250 125012500 125012507
    0x606120402210d0806030d0201050f010b0307090e0f04020109090507050a0c11120a0606050103050f0106051e0c070e01080604030c021003020403020415290d0e07121a0a020910 77
    0x405100080c2052503180042c03485851900d5001c3e40c0c010b020601c00c008100c16803a04000d0070082071541d100074001c5041188440d1041e0b5418050001142da0102c0001c043e1b44c41100e81e80020710342000078030500e0500708018440f51038255000e90000d0a22080841c01144600915001d40e016640f02844d15181200c00c5030f0362508803108950f65581c40c40e01c1003032980d034810b506240b9414100a04100d20b0340b0319201044840d48d03401181803500b400c0c01c1102c68001c0945140c1112114184980c1c0c0305101281c6910000d04e5140ca954520f1020909a481e50310004402c070a5400d1410712800c0d59890300441507913000101c800030f00080e0307040e400400504260a940c40341c854103040250406869a0014050f54140090302c0112180b0502c00c0218031500d1843e00c10709400c2c10310b110303001c0a26009030a500c2c481c000c82c0c005840d0321800c0000c02401d040141400800c46514214081d1603a4901843d9102400300ba006c803612800e408100850124808c44000c01c0b4000c0001511580d0000c056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125015000 1250 125013750 125013769
    0x120b0105040801060303080711070b0d0203150d0b0a0e07080714030a050106090929040b0601170c03041101110c040f0204031406010501080117032d040e0a050606120402 74
    0x15040040600c00042c55203824040c81c40518031076111065140b5011100801d0620303546a200d1581d8000c035810400001c3c031808485202009500c056a80e80e20400c3c2c00104171550344410f03800108190680e4148107000b03c1181c0191910b000a020070f0003402d0650b55183c100e13029425a90308145803c01108040c510010b65000c006402e40b0414110307038403880d0841c1d03407a910030034001d511040c43d02c0c02c003d0400c8032080305849142c14101100307822010071141c1e02c80100001c3c40d2280440c040b4200d40c0c0245103410510700c900100800790714220002c2c11580d0800d440c119028103007180d5144440d030240d903458400100f81c800401d84c100c81501004003802d0080f4958251079400c001c044045600e0903a14800c1c1a51800204400c0d4905400100f400c00164850f200329148034502d10310030107011084400000d1040703082c40c00701c0c01c0d9410300c4044550b02564040d051741e00003400100c8aa40042492081c02c03001c0c02003000340e5410b0b0a210f503d228428511900d1120074000600610b8243d0302e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125016250 1250 125015000 125015021
    0x50603040c0b041212030203070512060418051006170307061a06030412080906060f0d050c060a0807111c2706020106032603040b0702030c0a0c080c0102070612 70
    0x8040c08150b80e0300722642c16900ca42c201006a0340a074200c0d03814021101d0041d200c2003110318045141d40340024004220f4091040300e07840c812810000b085181e03680307400500d000310384c003100154040c1041c03404076a40d0b4080002411000d0600038005450a540c4444501e080c055101a61500e010395668a0003841e222100c840840b0210701420703150f440d0b0074051407240741310b540c001c1c0c44401c1490700908603100082000030650700c040200b000340e8039601b00c0c0f240d106006440101c2040c0d02d52400c1400c0c189540704a40d003000011404510455000c0103542c022a041d46500903203448080700180c44440b0806048640035450030100c00c214801c001c103900045003080240c00117600c03924201d80c000c01c55030140c40103130b446078000e00a004a45d00c0815200710440c1c414000220409413686a9001c02440501284061000194102d009004a403480c0c6c11441c00d89200c00d4492a0000000300300740245002480b980d0b111034000d5000041034825a035090b100c25000082001902000d488441e60307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125017500 1250 125016250 125016263
    0x50a180308130506130201021606020714011e05091002060c0a0807030b090106051b0303011202010e0d0c03050304061b0b011401090f08061609060e0f010c14010b0f04140105060304 79
    0x44502254050011398001c202001c04030121305183e000080c50650040c1d40b01950f00309600781000341903000103d240485100364108071841e000b240068551050340300140c852500c100901e0007049030720030300510403030714102c03011410010440f408a0365400e0441d06c4849400040000300080c0e40034885140c0d00c02200e107000b18600111402241c0084405c4e80481c02142c0c001c1342c400020000300b044d114150309403900641c115898002d1014401000c220041d05200800e00c0c2a2070760389540032410307486900200e00000c06d43d56031401c1513407a80310b807003404002100000082c002c44411401550600d800c0041804541d081c2462240403640f400005414400e5001001405c40d204114010003402120302800b0390b441c101c60512005100210194200521290103128907600000d074041ca90005482c9682c203044d110380140c9911041caa0b0181603070510907612280104150041003032120283c1d8030544455541c1c080c80103a45070240050305041c504c10050145040007400707550310030b00618 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125018750 1250 125017500 125017531
    0x17030f0703030b060c0a0615120320071a0c0d0306121506090c0207080d0e06040e130602180112050603100902030c2d0105041503020904140106030b04050a180308 71
    0xe00036442e000b90308008a1f10340da2907840c07040200301c0707104100004000100072100c08034000e640080950080c154240000760714080e401050035402c2100c400070b041c440d1010a99803d400d40c0c001801d811030003050f0390f60301c117040100c0e00d00d920034001d0704201e5040e034008000001c0c80e60f45450000b07054000f80042642e075001d0015002c2c240b80611110000c141d00a400594188402c071424007c209910a09201c03800710510752f141c0340c040485084039001c4150510680b158100d00941c1c0804080260005002040300d2040100203884e0201d1070800741c83d4110004012a03074541501d00031107a0b258550421900514450200d40003282120300c010b041c1c0b81403110500000321078800281003158510300c1181d507000706194048940c1480c1800b428880e050a2070241c0740084000030440721410590041000c84031a1629000700b20138000c0003d480c81e0642c0c45200c001d0007030031420b203601d1103030307040c0030214001486134407c001c46134500c1602002414050340741624016000381c0b41440692416 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125020000 1250 125018750 125018767
    0x50d02010c060f0f0b03010209030d0c11030307030504080c091006030e07170f0709050f071407020406240302040f050f0117071e050306010c1202120d0617030f0703030b06 75
    0x40c031540d260700c00c0c1d0820000c0c1001c4c1d060000c0040b284445452800b981c0304200c0f0740b0b00c071360303001031501540d05245c908603031a8500703481c0041d1500041c0141030707054440030075460100340c1c0003800340050f68009422140310404c00000c100108100340e5100000205d030480134448248660427044504448d10110341a0503075882c024440e80d80e412280c008140c125203000281d00b941440310750020007000308140114145985410002080600500148290f0048050311000c0501c2907504c020740042040100a681d00c00b100c3c1c10220001511003110503d80d0240507060080c1300303588c25110b41140368a146400d040c28012404116007200703040c010001c03168415202d40c011003c0c800c5041d695110480d060740034a60000f0440000300c1b0080c4913080c002c20905036800140c40b199982c01109004c06441b51440c20307410001006d511450180000503140403290003600804201e403035201009030f610700300c6c1c1812900e030b02070341d00c4904001400700400d00c0800e120707400550040e80010f150510704541c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125021250 1250 125020000 125020013
    0x50a0f200c120d0c020106081225060c020a0201020601060906050d180c0902070201020c010507150c110d0e0a060201111209120706050601121116140105070519090b0301050d02010c 79
    0x303401211900f94580103085078055082c0251001450601b00070443c000c0c000f41140903e0103070842510710800314800031203004070400c81898200c0d07080481048501c56a10b4000c0d22011242e800341d015205000c00000e00601c00e42244080300c03810743d101c600340703445100080090502a4400c0c2c000d00c41105c3e209011904c090320480051400c04ca005a8680440c400a800c2114802c1d519052160a0000b00082601404104585c9603e4100003d4203e1000b60940390940021031082c0c0a115a450400640c0c1d0817540300e9030b08210480301e8541456480d07000f00c1c02c4c0c4a1174030b0300708003141050200d41004909820050303000640030b02528802003c5c40c01109481d00004000c0c0c03500c07a00d500500a4a50300551103440031031020381c0c01d100034101004428410f10400e01c40f140e401000c921380b2028800342040080e01488a58001c0c0110f0a006030010100d4007c0902951100070400c0b40301c480e90700855840040790783c2250300ea415030380ba1008010308290340d00c2c0e050703060004100422000600c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125022500 1250 125021250 125021257
    0x1b03120c030301090b03010516081018090303051b04030201080702251e2d090207060501060f050403030f0f050706240512070b1b010504030201050a0f200c12 69
    0x4400039510b80d89406440c078140c6107841d00391402a4900b4085c001c0310741d00c24108940709613160810080c241c507458008180001c50f580701d552080303541d800100c0310504035008480c1c2d00380290740c24000c9132903c1c945e03100b807103500d003204802d032120411080005502603281c40c2d50091150058410303520440c50b085032016006850002d1114841105002d4101440b840c01c0101010346401006a410001c0800242d07221039040e242c0c141d081040500c209070071142d1080a86001c001c15501e407111803506002428085c001e034004604800c003910845881130b0103640460382c142d941c001c14840c9804040e180c00d81c80030640c0301084000c00c95480030400d140102c02207000201c151540d9400030310000142001650400b610411086007424010365001a02e40d080c5d54516800340c1c0e4a1085402d003500003c0300c4d03207034211694203002c2004241501944007034800d110480d4240080000c0354620412240924013500740811485109400200d01070054000c0c00d0388001211004041c44540300c480381c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125023750 1250 125022500 125022517
    0x120309031b030b07210e0c0301020c0c0301140f0c1c1d071e0b0d0209091f0b0702030307030e0a09090f060e1606050a02010f060e18030307021b0312 65
    0x1d0070008104010810480e5548443d142c90110020000540c040942602c420451203410ba254002620504414400b140003004004c1c021560b9044850505440b0052440300c2c034803135482c12227031003540c0000c12000d902c1403130b114010310407540c0d54200d0124550401003603005449580c02100380b04000901c11080c45105101003004a642d18812907480c1911507001113098140121200b048150b22124110580d850340001d48d480f000c6a00c070f100c000707004540103590307c241c0d10340500140c28482e03201104544296441150055140c211060491059040082d0107031700401072000031901c23500c126224040018081200c959442c4818000c1e140203007820703181c000109003010300304807079441952103400034003024003104408001c1064003158903100712000c2c44400a00d10000710310030340c040c43d1003226031b420400a068a841c400100b121040340e1800360355001810641d0080c900006a030b10803c400c3d4001d00302c9107051000717080f82c030404184054251041c010820540c1c00350a01400410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125025000 1250 125023750 125023793
    0x90804090f021306050c0d0e0d020301061d09010908041401030b151209160e10080105150f0a030c06110106030c1409130308040251040e0112030903 65
    0x71507032064192000400340e072050f01803000401010800e091b010400042c8203146007001786120103070340c001c560035003c4408000e501d546000004603034581d15000341d00280310b020305110b0302c0766509207245d803c0728041000604150f4040c482085010703901d8201c19520403040c54041001000c0758081141075010540c010140040410151000d000c4240c4c92640008082c0082002200c101560200c07800240503250420301c00360000798240564480385401000e0602c001c01844c540a80313103084541c1ca66160903c10310410491040c030340390071440f4405880e0004241286180b80203030588005c2c0d82a02c0c500219501d0755400000f241c90b5201c200300070311448081245064a072010018040c1c001418405064420098100400e9018802d50340c0240e058841d4800e030816981d40d40090600f9200c1c002c40041440c5514004403102601c070215884500e0103115032030000c100d03c0c0000e0142d4010381a000701e032880104403101c0716001000c1c40f280241807034200e140e100d0316158202c800480c081d1400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125026250 1250 125025000 125025007
    0x90507051008060f060307020a0506010e150405070e04020a1404030b0709171018020301150806070e060d0207170d02040807050609030a020112060807170705010f12090804090f02 78
    0x3420304000d14586007031585028916454110001030003a401e032565030340a0000440002c100b180200301c04c020003604842190700d19a07654055100300c420460382c03454850f8001c044240c0e6401c05020b0790b0702403e010740740e2111030310500080c04025000554180c003040000303001400d050760076000410255000d0041007082d03140800000c0c040750302e140d0205004207460300e180750001c0408100c000d1200d01010340401d040700102d00301c4422020750300b0040c3d0301d94a8500c0110000f1880c4c0c6078202110281800c2c3d43e4640e440080c2510002103605507142c010100b00700b4030b0001d615990007003112034458840181d50003061070000382c26400c48003000610340d41c001024020501e04104110040000310340143ca04030b00040442c1e142e1800f40c4009051181030042448210000d170010707030103000c0c5601111542a9122103050b1034400744641845c080c043c584001c90a0352060071600c0b17030342d481d6486041c200c0380814000c20050036030384029207103803009010100c0d05507aa80601000412000301c00340c6c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125027500 1250 125026250 125026259
    0x1021b0904060b060919140a05030307080f070602120a0c1107050d06020d0c02160b03100b030604060e070e09100501140310050604060c06050603060402010e0d0203010209030a0605041a13060519090507 88
    0x10050640003591140c50105410009c80d42c000089810465010810320380301c4400c0c504900c0035020340301005212500215002c6428002c140d006c51044018004c24440780d490f40900f40c40e8907015045112440c1c00803d4107015a0426160440d04548038071401445d01d40705001040c05c88810121040c010b80010401980444004000402405644035030915500700b143c0611316541c02442100c09011020000890b555619800070300241480300700a540c0d03203092080104418100c00d5058452084600800c02c0660648a600300741ca406031905031441000503140c4502e40c0008020941400b00003002040e6512602d010300700900b01a12030059104030b610701002519401809180207503c00707810000941ea1045114007294001c1c0d914104255440c00402e0181c46408400b035007511540701030008008842e071100d40b081d40242d448011541500443c0c0100013000e5508a03449d0140e02c16900209031164099a0001c100d0046103032a036000003060f0058484d945015100707904407000812 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125028750 1250 125027500 125027519
    0x71502121819080c0d081b01021309090f0b10080a0308060909030c0c1e09040812070c0503030a05130b090a0311010204081504030309080301030b0601021b0904060b060919 75
    0x5204202d060726900300e16050002d101d58507080e030013816105600f05510070703041c001c03000212902a41c0d43e071006246d040c03032004560301035031004648081e030444060000914040d0f510561041c5e41c0d20842d480b468000315103d140c0c081c040904040e503e0419540000740740c13001000012000c901c80e888843c05071914800300f0280200082000380a90403c1061100284020582c0e2110417021100d1500416100044039034400c84030050f00c2d0131803503040500040c4040480948071405407105036500e260b45000c81100d00c4032240b00001d02c55401400403502400c015003215500c81d40aa1034040c81c44040c0e111030f1041070041e40c1c1c505031900650002418076032310885000c80ca498207002986001d240603001640c0e80b481002413400c07131003940c011804141c425000401070325006898141c8a584a003081c00c2665000d952150141c030840031000c55000c00c1201ca58480c4400400f600200e9503151200c0c009081c98100c11540300701c040003101f11903510700800350680d511526601d103030399041407100c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125030000 1250 125028750 125028769
    0x402011704030915050325030e0106060503091903090306020c1c030207060501050307060903030503041506030c0603050a091e03020f010f0218060306030601061d0607030e1c050715021218 82
    0x203c0c20050200100302061114002203e03c03c2210150b1002443d00901701710700801d800c0d03101003181d502f401000694150f01c900503500601b003c00685901c28003441c41075209103c0c42400070b01258a9001c1000401c01980c06001d542ca00402a03840c6034104500700481c0e41c04154821021943c00f1801a050000520481c0d000d468103030000c003199400e01101a0015420344002001c00100000140400c10300080d0030600390350107201400220f44030305d0404210201740c0204000030340b800e8002081c0da8414059401826001000c038220400c445004c000c0c1041d80c203005a06500c140e04036171421000911400414140c0700900503160b4005000c01840d2061250225201d41401e00c10321145035404034000781140c01c6420040b0f03462191940310612041c0c01f0350304079481000400c90400345900076241d10790000e0b0807120b14040c1154411158030740c440880c000b130590342c000241445081407040944000700303810f00403030f004045800713171052859210030301c00403000111395108192810074410b04c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125031250 1250 125030000 125030039
    0x30703150605030612010f050c191407140a1209080c0108010b030f0601210f0e0a0c03080a050d06080709060b0c1009020a15210902010903020904020117040309 70
    0x3502400e282810082c01c40c0030251007a4071514460f42c02d004170101c25400041c1c00b00c1c01c00d00c1031001d85002806288550028084050441600c03980e18001c0c80c418420f401c05601c0004210b03040048680b01c40d0701032106034542904a1080c1551080418011490081503144035a12110800e04094000d410010344861300c07414000315400500c112402541540d1b44000c0005545040780d540d00700480d12200c0201d4076042940d00c14241e01c43c20000c070f8010013181101c035001841810401d2a0382942e5407400c05000c2d0010101303003411700009e00c10314000c000d69500f9180440c1003d060140041c22201c42da4044202c5078401d81d0200510240c1d0700032040144200311140e400c0001c142030060711101c0c8100c5034040140d44204003400c5556030000c1c10701400742c944010381d28181c0040c0282c9030441e0003c80180d240341c4a06045200d0341c0354080c1d600c4455043c0c0d28100c40307600e10303402d10080ca040913100f24140045a040140340c42d6406800b503102c0c40c040d43c0e82c00343c100d181040350100c00801401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125032500 1250 125031250 125031281
    0x90e10032109090b091b190503060315010617041b08030c0105010506070b040611160602030a1406030a0b0a110705030a030f0212010b0304020f130e1c0221090402030705030703 77
    0x443c5245d0350621400e82c80041c00081c4c2e0303507030149a451522140300d00b0100d12240c50170041d0007900c095005004c3d41c4609800d6007203c1040d288900c2413040164244103e0b000101680e40c03032480e07005d10012081e0042e210700c02d4040c044516000700c1781c506c1c01b2034202c00295800410000110642401002d006141c140c50107844e01c0f080d03480705501541e000308040d20340c07a1583d82d00000c00440500301c82100024008844086100e4909100658400e9502d0b10321141402c404010454602c4029800f4100080c02403440240c1551401101c0b107004011500720765842e031f100c1660240401c0107215251050019603610005680f0140449980b030402040d81807040c499044111014050703e0b041d80c2100e443d941c3c1300e5a07244002041d01d000c0480c0e0f103420240c099200307071130894140c0000d040c0080c48015501c148600c1c810810665541007500c10044c1c0c0018117a07008440070040c0d629850aa01e880107103050040000710f0180e900903100c0b039000610010800106507894411600d44241085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125033750 1250 125032500 125032511
    0xb121006140f01050a090f0b030103020906030c061b0f030403030302040819020a121b08030307020f060618070507060204180c031b030c05070b0103060f1b090e1003210909 75
    0x2030105407050200b41c03126050010001c0c0c0456058000ca0000740144002580380e00c0041d10742501ca03086800a2000301c2c051088071011520a140100c0c1e1010b1152010b400383e0304080726030745522500001c00c007424916010310369080c2030140c420700c003c0025601030344025959500d040c03815032a05891461041050001941c48401070780c13062110412180102100180c5030001d060105900000c0c01c84000c4040b0b000000141e040c00103c040c606c241c1007902541ca4114820098a469040c220340650703000462101960320304c0c2e00104130703036040045e500c1d100d030800405a80e60412644241c00070101103007080070405c440d081354020104205154a0f0078800032030110b50142d03001d2400c0c00040185902c0f0103031410a940701d501034410a68001c200c0e03c845503524103005004103400030101c6466800e0a040141000514907110207071802d030741c0c55650091a00c1500011448080c018001058000f0030000216085110b0440b2665940f003d0700c45c0c030301e00d2990141c9060aa5440b8140e90f50a11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125035000 1250 125033750 125033789
    0x2030f06041a190f020c030c0f010b0301140c0c010204080a052505240d02120a0609020408060403110109390f0915030606080a0b0108031e070201030b121006 69
    0x502d80c2c2e140480300810201e4412084044d14001e80100d1004598034440415040c050560011710b410400104200070050803024209160aa6030303440d15081c05440ca403c0440d41d040041c1000f80015403011000500303068036500b8150030100c0b420410368043c5d005440d190011040d844003412040c2c0c291003401c3c00c03640f0b01008605000e00050490341d40c1c1a040c61601904200c440441d8001000080115610074501500c40101c1c1000d8406002c030600c8c0410124850990348200d40941c0d00c03000081a0907941c81d602125038030080031500303a040d521500800d002545451600d40c09502c003280d43c50715050030780c01c8040c4240615a8500e81c0c10840d0604110060034859100e05035400c160010440100034080450420139641c401071249280c03450000351102c000c0398a40c032071480b4046101b05030341c0c0c402c0303c281d0302e006030070340d4048680301c0845031026180640000d12200748181804030348102008006035641d40407032041340d8523402058010718003400600ca40c1001d0244405154807501e000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125036250 1250 125035000 125035021
    0x290a0e0603091203070c1103030903030702120109290a090b060111071d0108061b0a05090d140706110f06040305031f08010902010e04090f170702030f06041a 69
    0x18050814094180000030802100041c0100280c820030724030950703a00d0801c01001400309a04140c02e59603a0003080403040f961401000b25030141c07000400450401c2019002c1207805107030030740300810079035884007400c000806036035841c690355040c0c0300850540280307806200800f22000b8481c101480c42c19000000080001e80029000042841c00041d0741000c2d80c0294942811500a80000700d021071030034203032a40c82c3c960141070320002c5040d1096512000040e200500101c84506050310341800480d1615100700c002e0010010010b100b8524442c41d500c444101e8941441c01c03480b10382101c1b50502c104e903003041c0741c010380c00d891400400080c55800556919918080c000400f0081c000002c94400d0001c1000340584107c0340803041c07612680c03450218000d010b404403c0307021400403000710580c0d00d0144952000305400101042020b03034680d07102c030441929880680540f8805001020142c1ca00b001030188130010200200250708060034003803c107195160702690346500342001c00070003002d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125037500 1250 125036250 125036267
    0xf050d090c23010801290d06030204060b0712031e0906060f170a12050909070206071b0b160201020c0709060e011208160201030b12030304060e071401050c0a0c290a 72
    0x1201c00102007088291207112040d0310a001c0e41020084040380f84601d8901548c09030080307a02c01c8404100850b03540c0c0c1c98148030f008100b0050000103218454101890294218120310403074120301c1000000314810110481d00c07080e03016941c0c0e40d5620402d0110503403400138200500f1010368880c910f048200c034142e64400203008003d180c7e1012126180d049801082603e43ca06002491000c0d40d00e030440d07000355a001c045910500082c0c807a0701c2c0300c0030301110304920702c58a50420880005a030751003094000c4085408840d6085650070000d1341c05144040c412080901004a004100d1526003980b5411440301030304000420135444081c0070000e02000111445244240d0300800c08100d03900061b4010b008440388160854401d00e0202880764010004501c1503100b01010082d46003030704240c0740d441400307021302c25910003c0640c5011542c012809010461004000c4402003055035035001e003000010751010a607088001103a01c5500c5c0c0482d82c0d10940d2054040c02c1d810724041410081c0303500c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125038750 1250 125037500 125037509
    0xc122109060c04030807110a08032d04061803080a0504060909060b0921060a090201030f09030207060c05010207050706020723030c0f03010902030a0803060f01030608060402010f050d090c23010801 86
    0xd0404204947d150400b520300100502440c59035959921a40d1030783c0c0854107c101d8208c80b0341074a0b040110807803007400070707141d804002130405040082c1a2403105426520400c0da29540304000700180a250017003168a01a031769290712940341a82c09410310440d90008240107040403c02c1c8064100c480540351814012a0a080301c0481003025036424a40d811745400703d40118810444502155003049038042e20070780e020405518240400022030701809001070040c1c1100104002e4644911010044c0c83e005800040c58404180d403418a000740a40c03101016801140c8100502005204a00c0c800d0310030b03042c1081c41148081c002510b58080400540c810461200da041c110388095122040d4242d0150482d0300e4041c0c6c0b03051400440e0011250030b403041a641c0810f0700c00394072038020403040f511600000e003002d4070b41c2e50040d90b1502503d8011301c01c00c9010b020b1174a030f0020340d004009919004480b80741d410342c10300e900c01200c5c0f0f0013041c5911940c0d000b1039400f1500c1e40d0001c0d4050446 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125040000 1250 125038750 125038763
    0xa03060803120a0b0607050a060b28050105210a1505030f03040e070507060203070818070308030c0a180b0405032404030f1e0e18010303050703050c122109060c0403 72
    0x141300c031002984500179000c02500c9845810300100400080d6400820041c40071942c420b42405c0301d6405502d1070009504410180394990f40c100840d500450107084244100006080c0781119084000c2d2910000c075803e541c040e03110f01400b60082e11294020300509002d401410b020402d00521959074411841244c161b40101c0d80041c0c101d0388a102540c13034441d0f000e40d080d9524204010000e1802000b580c1500807401014580600d0090000ea58000c0365846104142903640302d91010203a41c0010f8140c0050000040300302c00c4500d00c6e00c0c0b0280141003085011612941410306040c0380c1416031600c3c81c05540403001e004400000242810784c040d03403526100ca0013903000780045807040703002940e0040d0b60002d00b0302104403031b4104030384408605e01669200c0590a500d4044400500288000b0300130800411000002c40d109030700810005050b00c040b54445103200b41109240d40c030441e045021010ba40258840258032030007959040322508000340000d0030100300710101d40c8128070008154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125041250 1250 125040000 125040011
    0x50f04090f11180103060209010e030d090902090402070803010f0806131a060d080d0b03010e03210c09030a0b070f08010303090512010b060406030b011202040e010302090901021b030a03060803120a 86
    0x283d90303190301e000aa008034030001403a650b0742c1d04d0888045c5d00b0101140d8041500220419110305000401d4101542503035141d05005283c101c1040003903024804080d00180c003000010701142915000307600a02c59035603040005881d01c1102424568007400d0144207012140700c10011450740a8036110201c8204000c00d07444d180d60b4001103803120b10800007400e0b08070226101d00c50540a0780178925907003040c1c009001d485a285003003500c8dc4200c0c1d080316203826120907002d055042e444126503004d0341d125401881d00000d00b0001e468404411002c407003542740d103010000c0050348080c0d840000e08032030900e505075504542e070141500c102070040310f0045941c400454400d48007508190b00342007001c0d10f070b01ea42c3ca4441c1001000703419072102044c082901044e8900b41c190007072080f40e08403200d20703a5a0100d80d00796401c00c621036001500607100c80d2340a000d42c0d00d0385840c02950140e490342400046688030001e40c006003d9030580d5000c4e02440e003007401440141050152015403210007040009107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125042500 1250 125041250 125041283
    0xd0308011a120705161416050a0b03130f0501090c051e0f01051c140a0e03030702030304060c051c060905010605040503190203011b0507061404020d0b092104050f04090f 74
    0xb902d80100a01400c4c61840c6d504010a0460100e01032480c00645440e0011160311001408003450b1030b4131503d8030352081007002410100448041c4241f45100d2031a4090b24a1140c0f039103800d51b0080348055440041261007005103250840b0300121255040d822041388003071800c0056280784030342c18240d06002d0000380d074101c0f03420303501102d2040c0300101c4400c0140a01e0062a407845d81d00c100c030996000c501e403007085006190000f042da07220700940d90007185035940d45d980d00e1004d065080a14002c1c00020f1080d1203100e40c00c40200681240318490000b00d040c40e00441405a0742c069004005100007040103108544001c50741c0f1003050042c80c074000c5401c0c0fa520202e030040042c1021040c0c910400d5105180e030076440350051940b6806680140080f500c000e906030018041500c00940c03281c0c040ea041c1e00000d00405005034003610300c4082e2090071030703ca002501d020345618ac2e6101442c4000500784481d03c0c003001030310840502034a042141d1201c0e039568680c00313400640050071600d5003d0f940f40c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125043750 1250 125042500 125042527
    0x305041b0305010518030412080a0909050115020c01090501021e0a0b040f0311010606090302010f11010e03070c12030e13020405061308011a090115030204050d0308011a120705 77
    0x30840103440a0109103a5074185a402040e0031340b50702480102448419030605400400d03a0140d40485080040d80c211641e83d19015601442480c01441802c0c10005079420742413142c00d0083c48051030444140582803002814034030b102c40c503e41071041c9040103100343d90b07001400c1da01c041c0c258022010b403005181190b607d0800204001000d140c0940104401c004502c0130500060380320761100081c03190841c50250076200c40380039410000d0400f00c810000b6601c14008d201204846041c02e0200ca110700ca0454203549046e51210407591002078076404020030b00300c001004004400000001403e141d50061001c015812851b118560200f415100801e00d80e04441c000e00d0300519003030713032681c2d444104070884826101d901050351809042440c2508803400c0b00903d420010b010902da80c0c01c20840309500c00c40c040440c020180d00f4000841d40351200210044418000e03121000e00b985080c110868a101d05402044450703001e11580030700001d08036800e074200a42d0705142d625601c2440e5501c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125045000 1250 125043750 125043773
    0x30207060f030f0905150a05010503100209040b12070f06050408060705070507121104060e0403080705030a0621050f0a05070303030207021c0f0302070605090310050c09030d020606010e100807030504 87
    0xc940a40c0340c0745130740041180002d030b14207080d102c80a6000c0d160703540e4100c45045402c00d124964140c0c11030340001c020381101c3d41c014540c5683c0104000385140440d40800c08020301e128114500c1d0380105418000c40750500d9100d00140b125142841c5442e01f0712403061b4807000b000d0704c041c05100c000314100040150a100503401340034154908080790348581420060b010f0002121805a850300401088480011030024420740d01619800d08a44407801d003103620341d01c01018141c1c09540c0b00c0002ca54803402084580700d501c005900c9144002081c1003042c140b041d03400000d0080d60255440400040000c16101c045a80505005844090703c5c004209188031035000c04000754500301b040000c000300400d080040c02d0007542201c40d1107454000a965910800314019810b038001290000d142210b42c125981c4070040c409480c0c00c0c440404c000c00d15000c0004100000f43c1c200c1d20401c0015640028124801d00d422107e568408500303032000380100402820744810161a24006428001d40c00f26a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125046250 1250 125045000 125045021
    0x503100b0d0b130b0a0b0307210c030c030504080304020904020316080a21140304030519110c0316290f0a140a0c0615180903090f050f1210020406110f010504030207060f03 75
    0x2405140c003402034460050034400c0ad40b0022a01c0c00d444141007520920031188102da00584491854540e9001c0007038006005100f00d81c5880f500c0b40350204048590898401040b1460060640f1620ba24091030520300b8100092081c10404510040c51a0f00c00300d088101c511480e0110f40da5180c50500307e0301c0d4403c404100070203001040c181005641c3c80303001d06200c0360707041d03003514004000c4000705500c079012040448a80016081c041c40b280c0030760198880c1d03052850000c00204195202c109110b60000b00b040f180500011501e500c00d80d40004000c1c14a0160f200701c45d03c1e080110030701503d10000300d40b002e01480e40e2505035640c441d1040340114050040254442400004030a200340035241c0d4003400c800050007000d000600100e0f42500740191400280269040700160041c4260010403042e0201a41304048010349002594402000504801e940c4e00251543d0100d41505c1c1030300e207000450700d80e80b4050030440070a81c042100016100f10b0703d0311011290341740300101c010b061240038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125047500 1250 125046250 125046287
    0xb0c0c09041a0f0a1505060f0a050712030b090f01060f08130b0109050a0b03010902030717030403080c0d030e1b1017010e01150c120503100b0d0b130b0a0b0307 70
    0x600a01c1e2041089483c80f03007803150340078484c1074070500c017010b0903882602c60309411100502151a0010350781014000d5100c1c5c0d850928102081034903034203040240c6141c0e10000c82d42ea8010740102c2e040800170075a0060341541800003070b5150450051901000c110083c007080002e1020901c01d840c00c19250078911f4100f40602c04958441d451003004100940f52055803a2030240c1c0700f000e41c14103000d25400759400501800c00980f500200310180b0343c810421504600040201000151070b04014080c03c440b10402800d1400f4003013005800c6647c3c00300d1407022948004c50110f83c1e0111000314903140241510740345006c1040c02d0f4180d0304501d868101714100c11842c40003080901c0010034050484584090483c00c5a034480b80079240f65070140005131001411002e1520300070b000344002d6812101d010405049140d441203100c221b074200c0c5840504040e101c13440d031919450807c41903407401e04082000c00200c60040000340f0344001d90300c5010b400842c04000680514016003d0400340d501105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125048750 1250 125047500 125047553
    0x309020f060c0114090109020a050405090705030a05030a0e01050306060d0c020712110a050a0b12150a06020c100516032001020310170d050a080a0b12010b01090b0c0c0904 75
    0x225894081d2803000c25444c481e80d255000216201c0050040c6101c1d16000350a0341d03105400d200900c8090000180854018030a2010000d42d503202041070840c0346024030046d41e128508500e006041154581040381003040038003e1044650301e16040710128003603440001061340e21a8400c0c4d0500ca251740c000c80c4401003541c0780c541132201c00414005030305404c64294200940310380c10000b5070001406040b81650b01030120342a102e1084032815085503010310b010184011031300c0010300c1c4e000543c00400060f04290790070085070400c0f40010414000501b004c90400c095041ca65012500505025040141c2c0b11140c182c4880c40d1400e40c40810a0340000303640d0780c070340309882011071055813241c1031805202d105030036204480410301b1041103002e80d4506e403400d0803102007150014400303000d402c3d9041da5004c0a01c2d2954441d50307a001e1650020380049004e401000026096514a030b01100011104204444501101280d44541c00c03508540b880450b44540c1882c142d01c0c540316115484409850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125050000 1250 125048750 125048767
    0x3120e130b13020a0c020910060c12020a021003061d07140a030906020315030607020307020904110f120726030306040c050c060708010e0903070b04020f06130905040606061b02010309020f06 83
    0x5c948600d880b4025140c8604644405c00c4182c00300d8818400e29002504a60b8900006010f0b804458820081441107034504420764002880304252a4044000700e039403a0343c10015100310301d050300081c03503403070b0024449854070341c8000d000d115000105e28000c001c00541d41c1c0305140070b54000d91406030000000c54803803070190548124010307201440d40c42413048100080c1c0c0c6520010443d03e507258040c00380d2013903407181c0e5299142c280451442c990f024801ea00c4a003600e46402c085c4124203140440105120385c901ba600300003045080c045045c030995048102c602c0d030000082103c1d0000c01c19100000c0c0300b00341400482d183c1c012094000c1071409420103000020780c3c005440f606803240c00c4070351140c544565031101c2c0e0f24070985100405000702200013030054605103181c900011000b5100074a001010784100d40e80c400603801c0079030b03110355400500c0240601c0b0722a0310f0140545050000080c0d96a00d402d031600c81644000038109521940002c1c00c540b141c0b8940b5004140191905848480c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125051250 1250 125050000 125050007
    0x3020c1009060204050f0d03140304021c030929190c0c030302010504030e0607050606010309050c19030b0903031e060409080409050703110a0c030e040e0a0b0103120e130b13020a 78
    0xd481a54841c1500006c940c1882c9000200548920342c540c40340c0780c3c001f0644220440d10b400007030060f0ba02800c09502c1e03150300500c1d4800801658829500c009420b8140700c0c1c4a140402d41c01c855052064400b110b10460701001400c8a0a049010440c01a2001c85140803039481482000040440101c0040001015015000b09003e80e22079100c1441546060b41406494011001c0c003500d6907000801203600b550180d48100951802501034a00021088000c9040e00207010030300103c0032000c5400b0424403150b154040e4010794410059451401e02d148074030108181c107400c50002c5412000460703403a94882c0d00000071250701040131502d0340d540714030900c01020210b03040b0b000310f4100b41c80002d001805e5812a2040d81d0140c55000381a0300e5514129a80c00240007810340080d540c2c40300b2000c1c12000c100403034115219182010140d07045203810642d070701c000002c580512840c1d101d242c4203035a80040141c5c0d002e40c840c0c40050214504000507168443c40d402402513217100090030810fa43e030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125052500 1250 125051250 125051257
    0x503030406060902180103020a022803020601050303161e0b040809030105090c090a0b010e0603040c1703030f070c03021c080105010207060203070b040602071a07080f06040e0c0103020c10090602 85
    0x703074400300030041c1c1e500c0b03212080e403048408160824026401041d680e60180d8064641c020a92040b10310743d40c61448a5400300c3d40e0445280308188106512008240e4104180d40c050502a4081c0d82001030080100c8107411605800500e803a0781384004ca51502c0a210203444015002002110281004d003400c800300c0d44916886402035007400c1c00120550700c00190b4030390003c005403148000b5921661000020f00002e04000d0400c00b5032051500c950b581c1030040c5000300d01031000101c8413440d200b51203032810b2410740030340881d41081c0204844007081c041c000750b0100c92030500c41c00d00c080c00d03d0100c0c1007000205070a40c2c041c403034018010040da44050b01d1416194280c080307600032500c484080c1d907240140b14004002c104840c001a000400c0740e0040e084203032141d960240e2003060902c102000320b01c112404c01c001021300d4100b0a440c0020f40d40c0540000c1c054608100c240e6003160a42c0d10b5442c50040c080c14180c0005250384054410841090252982c004c01c00c800001458000069030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125053750 1250 125052500 125052503
    0x405010905030d0807050307030b130501080124061d0303030906070210020708040b0d060b19030f0e03070627080301030507080115060c080d0501170d0306051c02041805030304 77
    0x38610800070540d030a00103402114403002c1e03190b040b4a596021011106503000601e400304040c1c0312804404162600c15a80111845c90038010400e0760501c032210b400c41e15a034074100f0015410104161310310004045030025074100b03242c5210401314400d00641c0a41c16101a980c06110000410100601c0420014051100d684c02d96003020440d1040354103a0142800290105008101c01c00881514200800600d0806000440d205503101c82022243e00b203038015400c000036044070f00800c0c1c0d038035209003103072045172080411540140000c0340ba502c2c000c440c0024034071a642c850a4030301541d050410420703114002c10310000c80303a26103465513083d04203100c100c901d80301d406070100350444180518900c012404c900c8181c8180b4040040720507164200013641c0340c0b481001610000d030582c2c05024046c0001042c588440182807031800d14140340c0c0c042c1c000070985050b10034030841e6104c2010700d0402d130748440b20141000c464000580240141c0e40070200c070281d482e828800b0840048050b40c840c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125055000 1250 125053750 125053757
    0x51e04060207300e01050423030106030b090105090a0b16140c030a08090309010c080304032304080f0d050405041a1002010e0607080c161b06020f070902070c030803062202040501 78
    0x700200c8030151380b9180340f141c410f0b0100f28180000d1141030503114980801202280e0440140025040440c1c212030342c42c2c109444d041507a5040000c000800d00039035403c42c4c0d40c44010140070240341c440f23500d070341c00c0070708150311031032481300d00c10525445501010100484102d10300d80d41c081340c60720155030350310400e400c5000ca0007820000b0390281c0007201b519190703481030312060441c0355996200142540300402c202c0a0115071000251421606d168400b01c6040d8200c5096940f41084481407500f00d4241062025a002c400c145224990140076a01220f0040d03a010450380041322910140788010340d49a6000103581d0382080b0950350540103500e072000b55506079a01a240c0001c02c60320080101c980c0120040100115550341d040d040c492910a40113041c100c900204d224400c1d03d200030700782c0c401c0005900183c86e1182d134007010b229010007020f0a05c400c510f0032181c2c1c2d440070f8801d4414400540240360220000e0602d4942030201421601440d18882e0500c010718800f9009411501615000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125056250 1250 125055000 125055083
    0xa1b021f03330e01050d06090f060e0a0201080f07020c1e060d150b070521070f0b06040609020405030a022421060427020301240315051e04060207 64
    0x3c1e000310700ca025058400240580c103181d00903442d410041c01404c1022280100c0d03012030b07003021910501c80c0071407031000d2001034140e00762075000062800c807000e45131031003680b1003201b481031700ca80014401030503030720035108088026000e1586288a1100c0300000340c000c2400100022601a1648140d041e0f40707031500c90310040c0c2c0c0c46100c88816801010001007041d0300c07022484000c0040e02e40c14503a18900803001c07901d00303289580d8110b100800340c01c04584903c03401040c00a01e24160040381c000d844e04600840c105450440026915010b01601034003030090658901840800401c0e280015031101c10060f0b40c030516130320380700c000c1d903041c0307820703903916400382c0d0104689140501840d020088645c00d505131401144d100055a00907000c0c040ba459961203c00c4d01c1200040c001c1d506960100c1070b04880e150b807071400e240c40120250308805100c0d030f01d002c04000048440c62400301804d00308880d480055511460408001c2c4900381014008680407210318280c064071800003803040e140d14a40052 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125057500 1250 125056250 125056259
    0x90606030b040c1b080306060403080a0309021e0f121501060c050709110403150b03060108030909010e06030a08071403030a02070203010e0d08060d11040507050a1b021f0333 76
    0x52504c1d11070100700c000f004040c0e1100100e030281d00a907800120080400f85065580e40d1b601c0d22030f621040da200042038454003a8011752802c04102103003405002c0c46240b091244000040003546240036161190055540499034401c0800100d680e24200c1d41404240e9610340002034503032003840d00d04075201d00c1061004a0082c007240102503204050309003290401c0e0440c1d0383c0d180346075203006204e04aa540d0301b1b074024450354100091802402840701540d601d01d102418404100016044038856200380c505200c1c0c03548001a034003074282d0701704800da83c0b940064503008000706801803895000d40b00100038064030401650092074140c1c400c400801104911091141e1074050907485c00001c10240300000d10305040007400d2914641c410b901038182c00d141c200000d006c0320f0f010399224000440c080307a0b0319003207904604040404c2c40d9901d100114060702ea1f00140d6200b94014801801780b000e4070b00c030f400182c066004000300d20b03100c40700f4100304440144000c40c10b00458242100002200c0b10025 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125058750 1250 125057500 125057507
    0x30905030616080f060118180b090408041203091d100e09100e24090c060f030a09060608190302060a09050a0605152d060c06060409050304090606030b040c 68
    0x100d1410350307403200c81c4a07590381380340011342d240000c29a90600c2101d40403010380300700c1522454003074040440e492104000c2c0741c40c41e200f1951100500c50041d4081428080440c03801c00a075800c031010241021340004491404075000d65182d442409210a4030292040e20140e000c402446510188500c2c400c09596103017800b0a5441528071b60481d40010b03640400142860b00300b4003803003c0074801c61300c00051595510a03106007a445043c81c50700500f0500c100d14000b44210880382da000c8a10300d007805a07000e030001980c4006807082e2625603488480d4020044950481d000801d0510705450503041c0c901c040c80716420845208030014001d00300001e40785142c41c42000c18050b0040014001c4a14070365440b002000c5c05003502c1850018813080d260181e4401072084c0d03c00c2c52490646030700050510f0401c40220402001c140310f070300103008041c5007442c001000f41e0f00ca0300807039010600b14080e0030018290312171504002112030030300e100443c41d260103030402d03004000160740403c403004a80b00200c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125060000 1250 125058750 125058781
    0x50301030b160201022512030b06030703150f080303041a091213080d050a0206060d0812060d02040510050a0f0e0f0a0e0a03030912210e03090603040309050306 70
    0x42801e200c0c0ca02080c06012022404aa86000c40c00014036254201040320107031444003c41e003036a5500c0c03400c44c1c010003c0021107415082c00900b8140003004200d40000c500b400010504401c1681d110310080300c0d10490720694000344449254000315a403a0b84d10f01c1c2d00ca500071a0b040c0d40d040f1700700405600c03032028089414401d07100b0074054055000203210018103a131060a000004001e07480c408100c2201c103018001d04241c0c10b0300c440c1e95600c040c01d03000c3e080041c01840710340315050035003d2201062880381281da03170700703400d886518280d6607010004446180308900030390001c0c5084100010380c042c258442054805c2210f5031a100c84d606e000316030302c000440c018042c0548041c40410f42c0088122204c0d0340092480e03401144c0d041200b10364a26001c070341402500000e413605404d00c20710611010100360f81c0038504e41051a4020030024045100c20901c0304048960396141a492600c41801a101d440f000240010340d00d0070315050080ca6242140a0b15200380030ba440800d81221520780310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125061250 1250 125060000 125060003
    0x120b13030504121a010b0a091502100209190306020408210d0b0a080a0c0e010603020a0e0108071b122703121b140601120302030304060b04060806070f020c0105030103 73
    0x80500c0c050a0082049101c450810102c1d1010500c2c400c115003200d01c48089806060f081b0002521110b0300000101201c01990096040201c1d19001140d4298041546003680c021030b10090790700c0d20200041030500c40c40300403030003c070250010040200306c400e4000704110303900c1d082141e0a115010085620200c0a849802c2c0070020400c194600c40020340c21108070b45e24020304810f0340680d1040d000e070614040e4441250080812070301131241d203602c80c40c018094000da00d01107041003040e010242c045490031110a060102980008038072034840d00748004002c1d4852a00c100b0004240782820b00000d4000c40c040216100c04500c07a8450140c10042c1000d1600c10324001801d89140ca03040d4400b0350010584c0200405801012a8402e000c201900d045108140f01c0e4103110500368171078140300040e00440c2c050003140304000007103640001640c1c0c2154000e0300004030100300710002801042207600c629058041d000401c021250030a800c806032005980030343d108090b0384c10044400d031209010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125062500 1250 125061250 125061257
    0x20d05090a091503080a02060402180603100e070b0703120b010302090d08070201090e16020d1809020306031608030a080c090d06020702040905030417070506190c0c0f120b1303 77
    0x404102c000c4564000c080f00000032070a58010f580c0300d860300c141c103030b10500141000d41c0c040c40611085040040e410003803901480c2003030145003030220004c0d032528120b5045060b4141c4591100e04103003004d00040004000c00c424a81d0344030a50301d00070705002ca0301500c008141e4a0910b141c0d9240d4000e008540c0007001c0148180b03146003095441c41203e070071405d01a41040701410300807503051940301807540505034031000300d02c1418255000038070f48010320401804100c41c52400788090030716051400c0942e00d06810142c1c40380c0d20080828540007540001203400090000c001130100310100051040142c10303920311034a42d4404000d030034284920210280c014001500e00b07804580c01e40d001e424198401400810a103034191511403850300241c00c000c0c0d6841c00c01029041030481006801c0040c6070650301582443d0708100d40300b50001003080400140403140c41021704104d0603808040150584901100c80f540d00e038004060494032000c0c0843d040c140c042e000c260300e036248000000d6107542c0f654 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125063750 1250 125062500 125062519
    0x3040608160306081614030114070c05160f060807090602030702060a030906050108010213051e011b08030702031305040b0307030615090e010c0201050c040f061b0b07020a03020d0509 80
    0x4106840c00c0700c242a898003007640d58203000c11140740a110340152804103024110b52103080040c0d51950004d941c9450f07100b03a1402e0490018040c40c62001307035224146051903085d030203190400d20f00f4424001800000b0000c0c00c00007141008446140e081610001ea1340c00354103039954507050f1000301322030003080c0241c0d1080c0104030051030010010402c8441e58138002c50100400da4441d41540c0c0c080c0c110482d9650003181c6d15442461018020004110071564051111200101904103400d00f20b40b035410042003007603108482d44040d186200e020b41c0300b1801a0b43c0c0c07034484802910b90708071907190030b110040f16200191518060003010b07680c01c8000d0180c40f8591440d507603440105080720051040ca64a444e00259404203845000e4104040c040049011412604003c1c02c503200108018900601400148099017184030040183c4005c0d0605828000749030040a0700b0100c58a401010424240d007080035060b40402d0401d805403003038084807100304807820299102d01403840d41c240c000d4040e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125065000 1250 125063750 125063761
    0x604051207031b0606030b0702010605010801030219121a1302030d200a030806090a060b070602070204020906370509041d01020a0203041a0a05070f020102100501060c06050903040608 80
    0x1100103100281c480c0c10f2803500701d0150551981911059001540c1c42583c4280c10802c0c40480000c140e8000080e05c02081854100f40001c1d080b2981030001034014581160070401c0c5000102d84c40d005030180107283c0404041c1303450855103902011400c103802c2011180440e0301250030209003840c40364010044c15130348038054000c6a002b0a60749400102c080d0134110281c146000f849040700150082d90340101f10703d0300009002c03580d039006c1c1c0600c0c17055140c1642000300843c140203982440d80e0100000da512101400020041d004602500b5030003080092900d10b52005444036100c0708151078001104038070480d092002c0300300b44000a1020070401c010900e40b603d0b01c1e80c0009001da005242c0c00c503001d00290516030880e0051528440540d100190502080f541c041510b0355180303201400510f132001000d0010a1405850780060481c00522007850071680240181006100541d50400466a446d1401850988402802c1d00d6042c40c00e07000c03072030071100032003150705551150301c4d20659034540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125066250 1250 125065000 125065033
    0x510050f070e01020a02060a02100614030a2a12020102010b031f0903110a03080f0a150302100302090904031d06090915060d021218011406132007050f060405 69
    0x10482e034114090303041501e0060741d400303018104054055004200441e800e4142600315071054024070400340040000305039a6070001039140586038050b4040b1074041c120005003817a48000c0d929920035010b0004042404050080311800761b5000340d00a0003a1440c08041c1500c1d01101006c000d03140303644001100d04e010703564106100311840380c5060096041003242c028101004843e0481c00281740d50309100c0390294400996810404550081059804044201001d0441440000d0080340c48090b08101207029038103032100204081c044280c14a0a841d00414071440209059510700b0303040c1525059082c22026990b03a010f01514500d07540d1286046840c4e03500d0b2540e85a94041400c1081d40c100034401d00250580345a80070141710241008404204810410710400c4501d07858900480503142044072820b401440a551159100c5e45018901000c0c00c0070000080c840044080010101c0203440c00400360b441c020829a18404172000d110340e1260f000740e03005030a60f4003464a03c80380910 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125067500 1250 125066250 125066267
    0x3060a03021c0501020d0203040323030f0c040b0d0608190c1205010e0a0302070f0902030c12060105040902070c030b060d0f080a0c060c0c0308090601061b05120708070510050f07 78
    0x86031030022000302d02d40d075881d082e640081004074070700b03030088180001c140d00141d51101641451280c818045518110410f041c00001d01d8114840c0741e0701c020a444210f84401c4502400460170307116528000d4200342809045540310b02d5205102e1220f50341b5004004016400e440c950020b12599054038121980130b0b403003081c101c2070711195603460f0007003d0390703404110360140280700b6009028a1b51903c41c42042c1440181d1240c07200e180100104901c9030507410480e0a03007007201400b2005600c81e000126000c0c05141c01400704544005080018440c6080e0010304030781c800c41c82040180d0302d14042c800d200791070b114020211002025884005600000500080718842c6031840c0030200e2900d9039410b507503003160031341e0100e000c40141c03a088c1036200c08410390100c1808020003070ba5140240051040340c0602004000750300c424028402c00c40c00b8040800b80d0044a00400d4403090503007401c4129902c022401c6030b0510078000840c480700058042d0b603120340e145c1000211541d850307a105941001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125068750 1250 125067500 125067529
    0xb031b0c0102090402040807030303110a050d0e100f0b090604090f082206080601020c0d030f0e150f04080d020d05030106120b09010b0306040c0309050a021203040e04110a060503060a0302 82
    0x1502440f0822554941e840904002c2040c60000c002c1c20740341d4200078007140d002010000b04903104100c1200d500350040300310703614000c18001c001405e4a0891034070b824401070340c3c80c6107000c43c1081c00401281515420041024000311010001620742030f0801088078120500104150613008134240412001c47c09003100351002a40322280188440103a0360309016500500042000e0303071f050262a50b4100300c0c040510400f610109441d0701d468402a15920a1503c10803c112132403488000f40d480d0300800c048401c03000b400040d21280d603900c400141d40c200c0c2c0a034501034810104640c203040e00c001641c170015805512681d1542e400d1580441d00b50007113200c207605080c3c45603504c00c01a04c80d51007c60003040c90340c288645900b0000d040105841080c6142c3c001c1504100303819002c070724042150f03150568121040c281503400c01021505502442c0d12603000300c0880c800b000248480d80315040300c4014100ea80491451301c0e800e0940c0d080c00203403240741d0032000b01401440107081011010303000b01c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125070000 1250 125068750 125068753
    0xe0603030403081201060e01030e060114150d0608060903040e130218070801230307140d0b01030c0503011508030a0f020c03030d1406100206071b0c0602160b031b0c 72
    0x1c1d807241c031000b5096004491060412049500402c600d030ba00c84e140c001c42800900c0c05000c0c0041c0c1d12030b0140c0e00c0c1010f014005010110503103031110355440000e151511626036480544841101c1e07502c00041100f40708000940c01450300162102c6004001c560070390340451224095038a406080c3c11100c04200000c9820121001458026007480b071000d40c880c0c98a50303104c00480d81481703d40c00c3c0303008802d02a082114201c4c1c43e0701c4035640e4046803480a030703003140c02203c1c0826840b0001841a01c0c6002c40a490b04003254008001d00840c00d00780e8041d0b50040e8002d00c03800c9c0900c614440c05505500c90440c40c2d810600007001d8941c404c400d101440011072040329008581c00000a040d503000410329404d0310341c0c4004100d41804610540c9074403403c11108601c0b02c04810b04083e4a03100c0c010300c1c000c200704204055000f40b50f10003c00380300240c0c00c800f00002098542c0d002a58455030101141000403000800180b42846d1100302c0307110381c00c001c0a00070703103180c418510034043e042011000000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125071250 1250 125070000 125070007
    0x11a09040f0f1104050408031006030606050403020d1a0f250c1b0b0c1011040e0712020d020403030c0501140403020c1002070503061302011d090c09010c0210020d0e090603070e060303 80
    0x4d550702c0c090389018502801c001a501e0500310840c003507040c59607202c00c0c245420420100030840d00841918222034040e41c080380e1880c19894446400041d0250742c0080341d04000c240b01d8041c80d42c0d17144a200f051500e82004407054515640d164041d008002e580009400c107600308001541502160b08100000240c2040e980d21808400550b030001c0f56052100d60009200e50f0312400309004030b118000180040628240c2030401700360040100500030410300007007041409600301d10f0360444141d407010850454071940c172403400420414008905861941c01c250f0b50040814409440d64000e40e03268000b0007010003000c0078000c1d6846d0201801c000c0d8080c2c00d100103000d48040c006a0b1140b0103281c0c001c86d00a10303a1001421041861000030740300c00500781003054030340720342c040c4d140c00c802443c0304180c0b00d4203078a0040f81c0c0c0707202c0c40c000250020300d4013600c158410b40010b84d440403080c5640325400d0080500301480310702a01150710f6030341a446418100249607c0c59009130300000c0141c147c0e842d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125072500 1250 125071250 125071283
    0x1709031c02060907050a14090601090807150801080114180f0106080d140c0d1223010e1602121605030a05070b0a090f0b06010201060f08011a09040f0f 66
    0x61a031420003000541c102108000c0700f181d081c40340401504049990f112090b041810f184150100640401c0c00f441c50b03400411400c4e809200d800c0c00410305032085030303481c94403a80e68640302aa50300000b40824071200020981c140107004061400c402c120174600f80d581d8111104203007a40c0c141017402d640c000c00d03030301c40441042070003034074060706840c0c00400380ca034000040101001600101d40e00d1448052240c1192144007003a050074220251510101862000850100a25040e4003003404641d905184141d50b09070000414122290246020341e16521220300d0740240030362459000060b0400c1c1c00a42415242001500120100440d1a40005444d44d20145942d00024200e0b000c1107010552038200000c50909a07400b200340d220034002d1034219600d02c2c010000f80240240b20ac0002e070005200e5905c00d5000320010311140048450b0981d41c2c2a072640203041e01032103428100c0b03003604803181c50f0134200c103141d028a50200104c05401c1c0301c0c0c1c40d4450000c3c0820000c64038408130240024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125073750 1250 125072500 125072533
    0x60507020d030e0a061e2a0204020f160c05030118030c0503040b0f12151528030c09080109110d0807050a0803061206060307060e040f020c0705090112170903 69
    0x1781c00036490300c44961480f42c0c14680103074060007140c0c0400040c0240d0460f015065a4821030301e015198001001c00c1c07480c400103000e40140c1200a140300c401086164209030001c801500f5540034020705003207103483e4020325099905500d0b100c800040d1400710f0000282c85480f482180501900c00d8900303054480140c02d0042e8060300c3c480d481800301090151038891228142500700d140107030150f060340b0500010508000f50344400c0000800d01155065407c14000d903019148002c07140294120514800302600034002540f0820000350742c080d021801510501c120072403150001e03600380b1f40e52001800c205a00103040b004941040c004d101000004404000080c0014441d400c5140c4902e060014444411041d2080c02120f5200005020464030081b915800307031481e0746420350b90042d440000c01c2c0a06100820480c0192002428106415010850b1800c1e1941119601e503982d03a02c2019406a8803078003806008121011006020091520f004201e0400082c09403213500385802d4541d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125075000 1250 125073750 125073769
    0x30206040f030b13020f01030507020a050106030b07030c0311070206070c0801050106230304150513080c061b030108030a030f0605060c060103050705040e150c131806060504060507020d030e 83
    0x19aa8076018400b03100b0000092421640100142c8140d50b80c0309240d000280020390705d0f88520705255440001c203014600c01e0080c203c1c81a0010004e0148942d20f280c034010a06045841130300291521900e000c0d000d2103030040c10101110381300518284a0b65400300f2050307600211040381d22a5900c000080e014400b80151402494940c81c1c180b142c0d80308046444a540ea0482e00c40e0007494200104000555250340b0307040c001000d4040021503a031054610f0240c42c8904002034a0414041500b004550000920b280b2036080400d04150203d05210110014002030045103590b804c1440411304032403080e441180c41c590407180204419603284081a490380c0300201c105406c0d048000180306026040214100500c2c0607203041000841081009031509200030800100d07040c40313400708207444801c074180e58040c0d584600000c1e00d00da0b600d80064001640b034040911250a200c0009802400703441a282250704c50340340c5074500306155003004002251504201c0034801412400d107401c0d107030206e01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125076250 1250 125075000 125075009
    0xc07231e010203041b03050607140903120705010608070608040605190603050d0e0603070504090e0a050607020601080105070509130510270501090902030307120507080d090212010615050c0703020604 87
    0x690b03d042070b05020f03515460010311072405c148003010800014100280b0b40b40d2000d601c0c9460010120950314803076462040100450b814482c0d288400c00c1c03541c040c00249007030f41c4120001c020035036998011a4580544c1d101da000400d0180d00020301146081e00400e91108500700c411b5100044040d00c00100c0d00c0c1d9400030788003039000415820381d060308040c400c0c0c0303a150211030041c1140742c4020014500d01c524052404020f854409104485008200781c2c02e601398441d003070356098a03003004000d540d140240b140d0640c0e5800e010100d03145034050012507605038400703802800540c3c515000d00005d032a025010200454201d58000745c1c071090181c00b80c0d100c0074065803210185108005036000d54032706801150b03000780303070241180050b41c0003c100c030045035000c0b070448624008407209071004e004029010340305100000e07060858070310350b6105c1e1807054402c4940301d071061960810142250001d00035003001401c502caa800742540941c0240c00061074480031900300f99200d9000c00d401d900150301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125077500 1250 125076250 125076253
    0x1206051504060f2c06040914040c09020301060509010e310b01081e100906030c090515031e0a0507150e01140301060c1103011a0102060c07231e 63
    0x4082c0600d5600071040c2c4030b05192890039903414188400340754264995140d402c0401e40030780e80c415080d612040182c0b00101903c0000300404111000c0b00e03890390304101c3d000c4546003040e82c1d011030704c0e0700c4500c01c0c3e9041e60410780d10f140c141039914006544170202ea0822a074400c000c07a10390248641240c0f18880711890018000c002c05a05030092419075501c0c2d4042030501c5000400c00c050541400c40104000c80c0c4003c0c1d25929071100d07a0301e260300b82d1007038014694950810300b000c021300a014400000700d40e0070780741c100b01d0b582c1d8501d0742176880e00d8102c0c0142c0e85a0481c4603070b0612102c1d401c0030340448181d0101581e25540d01581c0303880c6441c140340e2022241c014003441d804601904007404050700ca8080c20986401207140c1440041880140030723450500140c2c0040005011260f08a072645004c041c000b04051864840007940c200d110405084c01071007008002a1648526000d0395210b540c072250901c0f06030000038540b03180c030460541442d00d5124070081c3c0e01d100c007032455842458003109030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125078750 1250 125077500 125077507
    0x30f0e0a0e160e0f060d020a0311030c07050c01090b03040b07030e0114090d050301060f050a0201092004110f1c180c0609050604060e060a0e060a2a021012060515 71
    0x20b00282031141050076a80c482c0e80748481d100c030180c0300c10b400c603084501c0310140181d0724161070900394000d0811091428036400040104018095414010700440c0d006004a03001c2a49a0004680000032401004408101030020030000385e0b00c003030b40d15001100c90a003c103180007010303001c500b16000c95002141610307440092006070300041c8111003500a03d450803514640c101301c4090000741c0c40075240820810001980c245047c401c2d88500f14903a48034501c2402e194a51441c0c050030804400440d2043e4540441c0c4880803e00d00b007200d0a2a0340722508900b010801451400441c4d0f140c00041d04050f115030701c9084c440340c12441c06050a108a030741880480c00d28100814209044e0040e0f406030303004100a00c5000c0c0c0140713890b00a88003c5902c2969074014550440d6020b10b03840d049501300384045601004503070056000700a120103911541d00c0c9149001a0121003540f0140182d04100d84c242c808071124071900640403200741c0341101041d2159510f000c0340381c1080411345040600b6020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125080000 1250 125078750 125078791
    0xc0306131a04020d030804050111120a050906010311040c051e070507090203040f0b07050903010e010c020d1412060a0e0705040510080907140a030c080708010605030a030f0e0a0e 78
    0x249041c000da4012005845041d1425501041c0d040220210203030900040d00006001c0140941141d5003591b10382007600c0d140c1c2c0294a0405e00400103680c03042110b414000003441d440e0001131124100c940080040b02c130140d50409102c0109140303a981020040308200e144203190404400f0607041540d003202d00c2c0c0d80d40c200e08040d810b1410a80000d418580104248070102e800c0c1210780303c5894010b0241c0703026031030b912001d648510030741c11100d0701542440c41e002d000700019031281002c60342036000e5030180c408808088801d074007001160380751004c0600001d000000da145140d41c5c80303d4040c240e103007031544500d0030058000c001c03070f200c40c000350000406006034180101900c0e440007072401c0c039055509016080f90388030704580c0a001c58000c1003030035111840e91030380c41c2c060065070000c0503200381c140c032048004d40341c508034000c0400c1503003048800119401c0016000d0000c6816640e00e0741a2a00c41c0c0c0100c1d120642040710507403042c0345c88004912040050022402130000c000c06210070481e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125081250 1250 125080000 125080013
    0x9030c0712060e06040f0809040f1a040501050609010503191e0c0212070f0f02011b05060402330903070e010605090a050a1206020903070305063d14030c030613 70
    0x1e00403c0b007800d8102d031090000080c0c0c007040101845a1240c516a160b10310100420000c00c503c41240425500780425035148440c1c0c4440001c8008058906006e01e030780f0380307040c003d03244107a004a80c00100100002032421452030b502c1c0b440c1c00c0044401081c9000d402e81b80400c407529150b4440c0005a0320740741074013459010070100c908500905402400c103462915242c0030700d104141d01070459440311a00008580c030644006070b40300161414801400c5040c1811907540904440c224081d280f254404050b45808092800038008000c0d5200740500441c0021002904071040782501442904000315011482c000702c5400f03041e03117a944640b51140e450401910310071a910190080400710010700420302d0303090708060107a403c010b0240c1e55400c81000709240c01e0ba540d00242c030602030001444403030781e1032a01b190041d41c10fa990b00c801016507a460148085290f01e000c5040e4229004104601d1545c800302401064008003512a54a481c0000ca414500d0403501201081484400d8104201e034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125082500 1250 125081250 125081261
    0x1e0906040914030a0201061e0302010f0903140106170c0303040522050406020306040c0c0b0114011b0b010602060906060102073503030a0c0203030103170708040f090506040e0c030706050309030c071206 88
    0x200416080344020400300c01c4800300d030050000ac0d0400c03502840030814640210700c807400075031f0302241c41e0126415404005000300303598042c1c4d4406000715610310b500104005000007100d6801030182d0710b0646008104507500039180300303243c1488101c0c22404440c941070710403184914014080560f607440d10b00108401c5504050715801440002d00c1440d010424000b01c02d0b041d250600350602d8070b00610801a031306070380c1503c03220340170b040c00403207071010080500f820750b0417142d00c1d4003215442c0e220102455190f03a02180c0050050f401014104000300d4018580311904803060950324038800c040102e0007160141d00103003d6140c0c4000140b010400c86481040780007901c0d48003660a55055907600508030980e11034800855002090403410b109800c1700b01c5000300040882071504a95880c00d00015000855032640300c1e034070f80040c3d100b05050100300008440b1000380500101800e001c0140c5036908064405080c910082c03040c41442c40082007002d000c0c02400b02c442403c28000c1c0b500b1030540706c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125083750 1250 125082500 125082509
    0x7050d0e190306150f090212010501080405031903021207030501052724090412170f1f1706010806010801020c0a03030c021006060e040b1e0906040914030a020106 71
    0x8a101a030721488140700d140a20640368000c40100c2c480040440940c0c2d0b00740d0720b40061031000692200001c000e0025801081d5500050146002e180c2e40c031307001540c0200080380c003d07200d60010440c89c2b10441d11078408600a61040c100107060001001d2810400c070021a004000300f03603650018070081c58040450744001c20310f68130204a14032071468070074460300080d004481139020f6007180c030701d178500d9983d1481043e64003808408044ca41802d000c00c150160b00701e00e002241e05081410000b10a103000300d032140304082c1d616050313a111031022881a20b40c14000038000c2190340300108444074000341003da1920041c000301442c0d4100050203041a8040e03020321020313071041003c1d42c000400842c070b00e11043e41500b4002603020f2004800d81c1000b00031048640041c0c40c040c40401d10540040740305030b0b1003d060380c0411140d0644400d0064805c43d806008100d440c90301d0542100d8a00403a0107984030302d000d800414442c000c1d50b2040007810481c04070324030580000c5080040940c0c24807503c030080c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125085000 1250 125083750 125083759
    0x50a060b18091005090702061b04210609020901080307020f0307060f050f0706050a091a010609050d1103010e0c092206110c06070e0103060b040b0d1d0307050d0e 71
    0x30703000260301000da00820202401000700c00c0000700c02012942d44000108805030507600c1c1c0d4940080000e4980408643c1c52000f000e40e0301001410306160b100b510305441c607403105803101e94043c00c404203200c0450401194482d4840c00841d005896007091203008000010041d5181c202c548100206454448500d40c001c0d400500c040043d590b00c02c4160640030241c0c10419a249080703403240345548905d49000d05002e09210074440c84d104c5650061070050300a000102c210759105812148681c020b00c180d400007010f42400b071001d031134101440c58419100c0c8400300c808003000c2c808a42500d40241031400d05802101030710406041c44c003522507008007032507465100e0340c0e000c02000d40b000072a09005401d140e0340703150b0348510b0408001215480354940d0225217051801c040c0041102a211032a0341c0040d00301080040d03070305140070543d420707207410511035400c0c42c5d90450103400401e018411a000102c0030446038111040c14001044281d005d00040e00c04250a194050140782203c0d9185004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125086250 1250 125085000 125085007
    0xc0e0a0c110d1b0f05070f0603020c0d030506040207050f06070e120a060f06080f0c150901140a0201110706060e070804032007080d0c0515010803040909060f090501050a060b 76
    0x8030100451000c54159031418091850058020000e03040350480350010f01c10913590080400388000002c0c4c0c1d50440c0c403007a8030300210340c0d1100740403020f0b4000d07038120f50082e40c800c200c00c3d10024000d8018aa1143e00504014100380c51a240c2c0d520b41250740001400caa0040400d003c241503019150304000403040e070310b50f010100080c01301030327461501c2507002d0007603641c404a04031401c0c0c0715000b010040c14401c0841d103007610051101a240c0f11814980b5100c4c41000700070803c90701c480c0d0140c509040e0140c440424142e10b02e15508600c3d0b010901c6036046542e80c01e01005e6a00a000142c1078284c003400d40040c409080c8035070042c40e0907000e040e840502034001c1c20080040c0e4081d42448018814001c01030f640800165042c0c902003280d00b1000c00ea0188004401005034080200c0b03800754010b80c1114150b50030b400925080c41020b020784105900f0800007030000305002d82240c009548104070020351040040120740c222072403040201d0303c1f84d460324188944021103005400107000e102d10098035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125087500 1250 125086250 125086277
    0x10507030608070b030a060b040e160e18090a08040609080c0102010203042a09020d0e010515030a12050d09030c052a040c05040302030a0f05060106051903180c0e0a0c 73
    0x50320703400f07440b5030030710030300d000002580100c455003020001b02019550303a0340700c0f80c072032a14400d002401c0300e1840e401a040e0f0800c0d0100c912a030003d06241c6800341c00c1420030592a41203440e2007000030080040c2d03100b1940002c0000e002c071802000100015620803d03014149060142001c0c1d40c280707445c1c11a8014824400400c54030b038a000d100d40d03080001d0b03085401c00b0582103500c010030ba610001040c0d1001c43c514044514a42044161059070b4008100d0756660f507083d030369210328076090035030507070310402c884d000141e5090720380c402070109070601c075040007400811842920760019084001414407040c1504102040001c50706030002c4c051084400902445140d036800e1030113100520558503330000d041014080c00c00c80b8043c0d600076007951101c0e04da6007007002d03002c0030000c8221074901c0fa01000080e84c61049041d101e0094602c104581da004071900220050a05a980c0c02c0448110f604030000180d94007684000500794a8400d00702454000380070030482e0f049003820010321401c11101f44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125088750 1250 125087500 125087503
    0x90906011d0402010c0b040803070e03070f210c03050c100201021c0222030803040b090a0503030c0912100e0601060e030c040903140d0902040b0402090d030804032f010507030608 78
    0x1552480c08100d07019659650004031112007400305c0141a00700b0310310901041c408004010351103070701ba03603c034002c2010304041415941c0c0c00d81c1c416140068103491080c00602030ba000015860840e81c246040480c44076100d000b1250441d9008580c43ea111802080580c1480450088019001d0000f10300304015030f19207601345111048191001640000d03081c1c48075041d100200c5d50b99200711400c00742039803286040c1400360b000340c90507207580304508000350f544240011042503e940c444061030443d19808100c01d40d0303400852038071307500100c4050940c42c03003a01080b41c4140b4100ca42c5000c031300100074450313290400d441a001601002001f90f90340496440003e11038810400035900000c9001d92410215000d66892030b40d03540f503500c00520204c08078059005500c4250007100c040020000390720800c000c038450052115001214036401001190041c122254400e00900700f10114011006c03105985910401c64080a98025004018070b02c10901c2004d0b0701041500381004228184000c45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125090000 1250 125088750 125088779
    0x901060e010806190803071a041703090106090c02030a0806031c1112030c1803010b0a030605040201200109060615050316030f020f0c10090b070c030e18040209090601 73
    0x29061160b2200031400d00d85519002400040040103544201c41d15224100d0f2207a0142c4002d90b040400f242d000104d40c850005018040c03540700c8594149074091f03200c100700b030740c200070b0510505558070b0800203200c040074014000c80200682c065507039403c0f039900140240034050b09103400703644911202e1008c800301007602c1000300000d0a1940ca07024900d0740d264584029580c0f04030500402006001c00d02c081c0402400b640c0b82c1001c06840002c50250925088610040c0080c0d4031175401d140820100c0d1040e0301c180d41250062602800c01034508080d00308900f040e003a103961981d50307641081b00f44845407081f680606180c0c04020140030055400508c203000180081c8816000c0c0015103a403180264403102c00342c45040c00541d1505926070508659420a280c100c50030b000310401841c600e082480750302c820030f0b4000f82e05076050710f45003011942c0750400c29048062100c9408405000d59562541c0e4060211840400b04241342501c180200c041019041140b2130340644010702640d08000c2c041c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125091250 1250 125090000 125090027
    0x120306040906151205101103011404180b010512120712090e0424020304121103040b0d0609060e07080f0712020c07050a0803040605040905040c0512030711090106 71
    0x7003025000c604101006010407064086400c1031000c00240c6200041c80c40340115010380c040e1960a850340c8081010340c0e600c240b005405400810061089140761044d0041216001c0c10010f6542104110009403a0402900703546220350030004100501d443c1421020380c0d01c0c1000942a03c0d04420380c210240e0050b07820003000d8003d40520024414461181b4030000c0000c4103550403641083d040c001c501032411969000c0c0412a0414064501524000c80c0d00459210908581d61400c7c1001212034001108601640b07000402c0b00050715080c1c4e0002c0c04040714a0480041d00e289031450f034004442c40b13640158190207a403020070003060340041c4225800001d00c00741d03843c0755440e003000312020b0300d11302d000c010481c0c4003041c804061030300002c1074800c0d1030341501c0a900c103a0316200c07015039070b008902c246400034008200c203015176030640e000544c0252140014440c06501c5100103001c048600d0044000c1358008114a024081709000480c241107003614294240d5040450040500703410094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125092500 1250 125091250 125091259
    0x503070609051c14060f07020132070e0a0603060807060801052101110c0f07050109050d032703050d080601090e0103020409030e19060215010e070f02010e010f0b12120306 75
    0x41e040240712100c4d5007140c603030f5558020798155140803ca441000c26090314403000541c40c00016680b0769030890b4014201e07250f0110704605002c4171800360341d510034005080908200303510000301030640b04e245015025110710749022610714144290241341081c20352003402044820703001003241d504c8840501401d68908a00d0410007011401c00b5400f60006520800924800056a544040020400c04410b604000954810b2907445004490304000c1c2e0243e01d900c0703400001c0c4280000c2c01504402801d031220700320125901c0070011800e41100181e8419610b41d04040400080b550f440001c41d584400242000f0900b0317824030000710908001400001e00969942c800c0c50185400340c2034220000b00c0040c0310380503004070212801a922468481d0b00050710480100e400d080109100da90305850a15007294000e43e07510754110341000a0000d003505656941080e0450109d003030140c1c4801c40c0303040b032000c6400740814040c8a20700b001408051070301e4024000c40480c0b50040011aa0000012074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125093750 1250 125092500 125092549
    0x60a1104052e030b1801180b0109030b04060c180b04090e0c04050c0c0f0a0b0a2004080d0e0d200a090203010e01031a010f050603070302041e050307060905 68
    0x4103401ca80c82e888040d214070b00254062114105a068010242c0300c101030b0b5030142840d09014110662000a000b06020f0121700a84840844055405282c4500c0145421200307a95280c4410112140c103803416141c050700c03940342401c1d4a0b00720500000320031a4110f02d261191920f12105454082c2c3d0286201c00d90300c03210352428015080003920b2024000800420035070030030300e40d031040755807082d40c5003603c07801030820a030400200850002909038103c100d18545994003105003005113040f00c0428140d1040c0d0702281c51a0700e155000c0e00c05000041c0080c07034003035044c4c18041c1801c03000b80e45492103411070341c120300001401c8841414000c41c0000c0030b462003031000d400003855080e040e00621400c920100000075591010741030a0b049901600d0b0403164541e0303a210910f0007403003d00400c0071009c40d18004001d1801d0500c0110303401b03110381ca030060500ea1138550182e05d0300700c140007a860302d41140d402400a4036081c01018000d26140c1481200d50b403074200403400a82e0443d0904400b5001203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125095000 1250 125093750 125093779
    0x8150403080a02040503100b1e0607110102010623011e020a1401020c0d080109050705070506010608072d020c030303150d061407090f0b090913030201090615030302060a110405 77
    0x76019140034100050607607454003014201040109230f05404240700d0503070403030b000c544204164029410141c000c0c280b140382c5141503c1c2c8040391800c1c041001e0466688540000b500c010140a04140c2d8035418424650000c07004001403000780c03500e01c9003825101902c203011075a0703000030f440d89006034041148943c1c02c039076140f240d00900982c843c011050196018498616600c001401e059585072a820480c5d612024001c032802e0250301c0e801071066200c080140071880c06280b00b07a9209036980f4200d8100b1a0700c03030040341c4102500ba5060407010b4982100c44a2a40500c0040305492003500158110301d811b8000380d041821640c01c06004410710034005041c4002504026002c02c46000d10015034105000010034440c050300c620f0381030480280c030100c1c80c81840801c480c03140000805412694603622182d000c19901070340708a05540da21241400002e00c14080d030b400170800550804107040c990308020f0700700400104254426803030007400780300d645d442c203040d101a0351058030501ea001c180f2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125096250 1250 125095000 125095021
    0x1c0c050d0c030902330a0207180f06090e190302031e0c060903280906030203130f0506060102010f0b1f180f03030e01020109111e091306060815040308 66
    0x610901a4003ca085e0680076070868000350030310740140184503000d88546656004801034004c018501b001608550300820112007090411401003000c03100c0000c200b40100f0a00049030b55a92168a4617500d0351445102c1035402d00c803160080985400690009200e40e42c0251207210f46078040e01c00755404108502c0071600b40742625010995803013194001d0500e5809943e4940041c4c2c000c00302d031040300b400700b41408a0325070188079a402548a00116034100002507029400c01800300e0350b511003010070040441e00c0581c280e2855801803001e4005070410300002825a180b00f001e03004043d042203418880b64641c5400e0030458442210b40c40d014400c000030485184000754811090703d800075102103003555081d400d090840784070362201e050040f9030700016400d882c1c20260140204060380c07041c1480e8204900800d4800c13084e201d2581c0d12554900c002100f03503005483c0b614401c0141030344841001703a2403107910090301024006150051190032110304400004200508000408002c51001c801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125097500 1250 125096250 125096261
    0x90c0906090a1107060213080a12031a030d0306030302070f030807140c092d0f07031a060a030203040b0a02070f03030e03120f06130b0f01050f0904050c1c0c050d0c03 73
    0x10302e0543c0d9039840b403c6051000107500300200070324900c4401000040c0c483ca002540054841d80840c03c080c0c01c5014200035002040040c42c13580c5408251044964a85d0702880f4861800495480018586013141002480c1450540100b0040314500760705001080040064440d420f5200040540070101d03550024141001c034800241c01c040d030442804040c4c0c41008100061450701040443c0725007140c8914003c1c120155440d90464544201160105100e50006040304420009242d000304014003c55680d500c241c01c1c40c00065800320a100c100588074440581151050f0019402c00145d501c529002c40c1d00b0074002410b05a0314081d010f1644001e00c2914031a09040700d03103044610700071948508031b0030202e400900c5030402c02c10118410003140324803031980c0f00240110341030b8001c0340f00550705540300502551078180107010310910740e941c50241c0e6100c2c094503154161503da4031881c203ca222540800001400d043c5032a680c0a10340c04419640c503201401d1011030510910002a8000c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125098750 1250 125097500 125097521
    0x130306110405090f0a110a050301060c0201020a051c02160b0a08180d09030210020f0d0507050106081b0315060f040f02120106110705010311040905040302070906080114090c0906090a 80
    0xb02c1e83c1c8100b1031800f00c500c0b0038510680160364140044903100035180010310400562202050040c0014845c0620a213a4010414030600440381c08500d5a261149032a071288840d81c0308054400002000340e03070500c03213120008101c0c0c25240b40242040741c09610703401000c0480041110302000030751030207500414140228240800d03250b50400e485001800d4100d24002a03002d00800740745205803c0c40020b04102641141000c0c0031210300442040b5040c1d8171a0000790390a6484040100342103c0503c503440e043c03001d100414103244e0040062504081800d80c280c140c2c44d409404004080e103460304005211a070071600060010302e9458060000d005584a00e807810b00d40310700200c0c25a41200307003a20031035812822194000d6a440046040c1c5800f2109d00e070120310103200800c588180345c0c2210f07801030300c240181c544581d207601784801200c0d6158807542947e034554200d0f02c44074501c2441070740c02001c014003070280140301c100442d01080021f401b1a0081d9500704c000b40d41421551300c80034184 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125100000 1250 125098750 125098759
    0xc030d0e060d06030302031e070203150604020c0105090c09070c0308010519170607110102041202060f07021c06060f05031c02030405040c08090d0824042013050402130306110405 78
    0x102e41360f08000f50303641c010004040c030000340c10789a05c0c0c0c00c840910542d03030115402001054200c40d440c031a40020704003d890203070056001d1200c801305110078000c652140e0803c130000c03c826100401001410100545601c0c01d102081c0c401d240403a9000381c0070f6041d075400762880c0b40711740445560000c0518080d4803c01528424515038440c1d48070105895020354002c2c0e44070750b42100d802100500300d202d03d2041000d0203e00c400c3e60401400c00102404641c2c240700d40e294102603858001c01d4039029010f000301c0c200460003250400300f008030b05c10540942809141a141c05050501003a0b07900006040300d800180405030300301c1c05620030003c0b0380152101034002d01032020304e040050261001524400c0d07180c045d9080c041c09052107002e13028401c0c41003504107000c01181203200030540c10324001d1160041d48416444242030301001060171350100e0100055580c248402c0c1915541501390000d038492401000b0980c03030f98514ad0021020f482c0c01c214001102c15042621005a01c1181d1069801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 125101250 1250 125100000 125100011
    0x90c040606020102030709081902040f2304030318020a0b03041b09021c150b0f0c01090b07030b010c0302030a210908070b0a021e09030307150b0307080c030d0e060d 72
    0x3001e0b419005103014005940f200d0034000d480b0880b85407a64020050070080b400b2940c0307203c0251034542c0007011544500349000800840400c1c004945a20240014820403080e6062000305945071080780100218048020105002c950000360300030510304c5a034840c1c800100115061241100003504c14a048040548a80341d54200110281d00310380c0d0b40081c2c41d555201d641e42241554011400c803601c6107081184400d00345090821079400c03104c0403010940d003c0c0460a4911002d1045900440c040c410048040ca004a801030580d0b40c41d034105410040d49007607400c0080c2e000000d581400000741000403880d46150502503038612080054032203181090204800d110000000700728060144060300c8035a42d0300f100c103809170f200d480030780446090310b41810541000c041c0c0c06003c0c409001410b4030700d010603503154103000741c003100c1080c600340350f03140e43c11101850b00f00f001c0c100038035415014244400c104000641c4030366205840c1d0044c0803040d0f28003d840e0b552901143d031000c4010204006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 125102500 1250 125101250 125101259
    0x60d0201032a0e090114150d050108060414010b0a06031d12070204110c0a12120207030e0a05010219080c01090f0c150503040f110303040f0e16050918090c0406 70
    0x501003401e80e8040400c0c21000700360110f04111303103810305a0713201c8000c103844299400709000400c40942810107400106011001c1000300d24000c0038005c1405e40010b0080d4206802c141e040c0511118150351035030315100d102860360301c402c00c00d8400c8a030b160800264442c410450400d66500000100c601401100f01ea04031050011000d00901130082d1410400c01c003015074906628412041000450b620184c81c2c08001b0b0304003050b2071458286407a003a4019200e0318100c60a1340c0000c1d000f02c003c1051210029203a0074883c2c0880010035003480107000c25401c0d141144114119550301404007400090b0032441641309412443d40603a010303001d0584140c1a051910f080101030003030160001101482c001e5441c45002038074020b5401450061194040d40c0d11101d02c02500c0d5152034141c0001d200025a1290192162004226000343d0813039502e0900203111450b84480d04000c240300041c44451200d0300c4000080111a4038580c101c1da2540341c0c0e82a40d803501d02030803842513000c4c0c01c0c80343c0480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 125103750 1250 125102500 125102561
    0x1003051f030804170c0d12030204151211030c0906070804050a0b0c010501060906140706110301080a02010324050607030e090c0705014203021c02090c09030303060d020103 75
    0x41240c001d00340210284c01c00d62840340c0c407115100c0030319500103425882900402c4151200d085102451700f0300604e000e6681100034441d809924000c0e01050048071030b100044424013511005001802c49907240d880c000340c1d08001e0307000304402c190003504042410000c0022007800c4a01401e03009103030303060460740e540860b6200e83c400f5081000e00c7d400c080000a0b1507010b44000700c25924542c40d40c3d00c07500c00190281c10180c00405050706e043d91034455101089110314001c0d4048e100c85400b402540c00741e80005410781c3c801401319520006400c1c4c00450014180c41148103070350080344e80c150744440600b0200c880041e501c0394541c2c084406002c0c0001c02c1c0000300200780c03480c0301d440240030154900106c560501e1104d0440184a0383d4082d004103500f030b00d0380032080d102452000d40c2c48015200c0d004107070650b01880c01001c843d04620b2201095281109101c0c0e8480f2144d0001881d280c040c9000ca81c0700d01024000501503031001c00140116806908110700900c070340c101e03010038180d802c160f61 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 125105000 1250 125103750 125103757
    0x703030b04140402012705090c090406080f0d090f03030509060d110403110d231603050a1b060507030507030507060e010519020a02030702090408041203030c080a09021003051f0308 79
    0x200e01003441115004d4424079404603510649824150690106e40b07424240602010f00a01c003040c829070800c80e003445079407144034550140072050000c0c40795041000310949040b96050500042c003026900402003030803001c0350301c0c0a80e9814074141d42c40e00a240085030090242c0340ba4140c0050900c1580030310040101c0c00340007280c0c003a10141d02c050000e5010f00030410540702000d0010f100c00d1140c1c0c040c0c05c1c100c91079050092050401c80740124030301d4900185160254108580300c1c2c20400b4808140310030110404014600d0800303254400e840c2c50000341c410302c16008010140940415000c1c107260040c0255540690010410301c07810580c800e02c9802468215090091614544851010329056209460b0842c41c0c23a0004c5203820035640130880310f00380041045890032010080865031304110584a46424880d4602043c0058040009400d2043c010310070300c0707054a840d051401507a00c2c8410707013070320480c18200010141c031110102080b00702700114038040c00c0f819910010820078101c004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 125106250 1250 125105000 125105003
    0xe03070b0a0207031a06031b21070503010228090f4406011401050d0906021608030117061303030b04060b0f07030201050f010503030301150c120c03020c190b0703030b041404 76
    0x945050744c9041234040c540c25034019a09070424220178180107841450034580b42c40f41034140480c0c01c4103965100003400e981c490340c84d0780b82c1182c550f11002070080d420010000324100c1828820350b00c6083c07000340d45e840c2c0d02e28403c14955442203c94014108000307840e194501040d5640c1c030304084001c1d010078000d01c8a1501848140c841d03400000384d40545a12a40c40814059461500c4d00c0340300f02e02d09014058060301522582e6080003498844c1e50a031034140e01e501d1286004603140c0d07242c500d84818100d40214030210940000c400c01c038841440d440c100c50450303070500300014580c6031800410020001504241850000040c4101c0203148920240540038421360003804160340d8443d007483d4184081c401c507030b010740c0280018040040c043c00c880c4641001c0d071400500622142e242d501c4509810703000310300400c01c003038602401d059040c0000c41c10060251440c4169501c4c480e82801e10280a115045640001040e81000c041c440d80060fa126003005000b40940c501c0400d4450034034106940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 125107500 1250 125106250 125106253
    0x12090218070f0e03070501050d0609020d090212060906060603040f0b01030b01080c040204033305010902190f0c031d0904140606030d1407110306070f030c0e03070b0a0207031a0603 79
    0x300e01c88403d11034030400b000000c1c050080c000b0640b03014015505034201803c5a40c12544445000c41d00b003080c1c0c40940544880840c011414a88a00511a0308224040c904031290086420004e0203440011219000b88046d1241a80d0742d40d50300344900e0142500d4401400c840101000005100038080302074141d0341340d103058402091220701048124401c51000500c02c00717500c01c410859068040c0100c0f031003502c0d00e880b11030213440c400308102240c1e4240c104a08099001c14545401940204200c00d0320b0101c1c10b00c20044a000305000d03101c0754171502d0042c1008400c0104001078028541c502c43c141c50f010f018800d003130626150034040405041c41900c80e5200340c800044292070005944c1c10030007699100c00083c44c500503d411401e9020410a443e030803a54004664036486c200401031103650b290390780f103801c2d00c094107004056604d625420010003501c100043c1d10346e5004545d480c02ca50b4104225a5920625078007641400340541c0044c0c030351200201d1012902514440781d03803142c00100c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 125108750 1250 125107500 125107517
    0x912061103071812021c08121009110405210309040c02010e010e0304051e04020733020f04090203060409060204030c0e0108012304020d0b07020309040b04090308071209021807 77
    0x808020704e01d04949000ba44c018170b006090b03051410f03048501201035010301c07580c40c40e000115490107143c08058485450b0b05040c1c141c2004103004510441c080c4034400c80103d07180c5841c280c0002d81c01011100c803640460b170301400c4e03110205010021150380302006403042c482d0105004019000740000010849654240050180180404811201620300060603140c4030301c07043c1d41c240500c40c55041c19a4100d5802c100610100b141892000c008a0315110150000100c010381a111204840416030b180c5005022115260001070159802d40c0c036032540058030780e500c00e80000c025240d02440907040d14400500070090090f010800c1d002c0d04c91940f004801a6624450315080302c040501d419410b03410319940000107000010401e4109000615845645100b91134100010106852820160380005140c90140c00c05006d0032160601c1120100a440307200c1d1030241000c80000d202c80c0410082081c05c45600d075140e449000901d401a000c500b0380e01241011080d03c2c00b00fa00c000300407440c0f94 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 125110000 1250 125108750 125108759
    0x1060c1e05121314010f08040c26010c0c080d09020402090a03060b0a060c03091202190b030a0e0312161205040302010606080c0304020d12020f010513060c020d09120611030718 77
    0x74042044d94180d45910060201c503078100c903520700180040f12413120703452001549221003840700d4500b041c0c2c8040f010b01c840b142c0c070f4250b0869041c0c1c05007200340701040b20680007140d00d11083d1030228187e01c0c000f01d10002c49200080c024803890f01042d82c012000c00020003400717a6680a4880681d0a80b60340301129101c0c007040d101d5400000004000500c0490305105140000803007004d100d1015100c083e141500e0040d8031140700701d13604180780d0031001008010780440c0c0c0d0301621810040c5e141c05546804041c482d4540c01c40c0b0000c109240d403001e01e00c840c00031103100d00691100c00468070800c0102d400c0500c2e00a011b05580d00c40ca00c001100d41d03000c64020700d40b00044a001e181d00030010640e912481e81d0382d04e00003600700380c92170642c0520488030035044000c0c02924800c000f1071300408001d84140c0342400c06c6900034010a002c55201c1c00301c060065402004030000e4549040403c0000c00f401e00c0d00c80d000d0900700101c000e83c5507020080c80810b5410004080240501c030059580c7c06468 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 125111250 1250 125110000 125110019
    0xa14010807020a20060702060a0e010e0105270d050f0f06102304020c03391e070302040906020a171e0a0608011404050d020601060c1e051213 62
    0x400f040980704031900b400301078040e02d8002c0f4a000b04807015110034101420b03600080c450750020350040d40411052050350104c3d40e0322800d803c40e00002401c0183c180120160030600c00940700381c441c41c48441c1c0e84e061420541e21030807180411036001c0d00b01d900c091400355103544c40300b9080056001522032100071440740c402a03514201540c2141c1c0034114004c0e502c80d001d040528880d918503400c15401c02c0018200d01c030500041403c001950009015442c40074200b414440c41d40090a12801d00068841859030703000c52000350a4503040044905140c60b0171100e401c16101e0ba000a5106260040c608108120703500034040c404a01c2d19461400001d03039402c0710400c13070304079905400800e4001d40e16109810144e80c050300074144440001e031031921034007030500b100c0f200402030354a41c01070350800c4100b010802c1a40b001d90060f1014103129450208090301c1c1d040c0c80100104243c0040c250050100e2602e10400040b640107002c840e080c1501081e00c0d00d00e41e01c00110701c44045007400300403a100f83c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 125112500 1250 125111250 125111263
    0x80105010224062b05151005010c0503040801060906060806030a020f04090809060309030c0f0f07030b0403022104062a060e0f0f010c0305010501031e02180a1401080702 74
    0x9000703142e80c1d51520602c94680a071000240201d510011344401c00c04401d040040c2d00305a0321400100c1c1020900c1800c1c840d1030046078050304024014a50200b0444689841c1c5110441c0c2003030030300f10184d4201b0300d00700d42180125082152103610b88000010342c4021074008000310b50054685403210b44580b001d0540381d0f1072403000690800400143d08015017003030745c4609002401060b01504100f00400001d4081c0e00964144072107903c04540d1454508003801130b903104c00340d0103005000341940b1721115070b10741042c0e00c000380c9602540d000040505000303004c0b0380a141710001048850f44a040400071ba07a03082405040b001900411601c1c0c005800c0c1140c110002110049004200400f6515000945000720b80442240208850240f0802e410024880104d24810010811074402d0320000c00720b0358168051410107040c00001c112010300044201c481704c9030a103025a42e0f02c2c04400c040001d0b24001d1085401401c5000d00103440c00556020f9102031009a035500d1107900c6d400b100700e03134504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 125113750 1250 125112500 125112523
    0x7030c0e0102070308090411121b0408070501050708160b040308100305120a09120609020910030209040f02030106080d021509030a0f0e0103060306020703080f010602030f0901050c07050901150801050102 89
    0xa100102c00e00108170303940301519407484020b101041c50038044881c24940e41152904008190344101805082c6480d02c0409100b20b00407180380c3c0c01d0a250401c2c403581c9031164481c090610800103030004c24458000c0864502e043e844004800031086441c00c0c1d400080c0880c1e080d0006541d01c00441d00c14050361480700100c9400000030300710700e031540c20120b06560006c0001c07414012020b1001554000880701111130a00030080004c01e030362a0f0060080f0307548000c0646186180e60030003400143e4030881665000754024603030348600815440400c1c01848140c202d00064070811945a2a4a50000b0241c00784003910342443c90b203450360603200e42d40e400f0b210000c2011540c0c108240000c03522803da100d280c00d105260110383c0c190345e62110310032a407020304241e0000724548208003801e64500c4071180108441e2005601d40705241030b59100302c0c0203012101c0c1c1004000582480d400f4000c01201002e020000c107044c41c03950703490352006000d100503010f403c0880ca161000103000d6001140066075035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 125115000 1250 125113750 125113753
    0xb03090709050c041403150f01210f3309110d05070302060d140a0507020f0606010926060f0618060604171005150103060f1212020703050a030807030c0e0102 69
    0x83c00c2c00070520600740c1040000380c0620404113a1031100d40f6500c0c0150045448c080d1000103541405060140c1020542005c4c00e207411040b154000154190b00032040075801c125155480300d02071600d444500c42c01402c280788907514100c501581d0b11140c0c000c6010038452201d500a0365420024130a0301e17480000c000e005031704003010403c0075040110003003102e805d2246000804204030042c4858403841075403044043ea5842d41005002a010040d008829a1400c0101181c1c42c060000800c0d41ea1140190880303002c007441380400300d9641e002c1d0500c0310f4000e40180c600a00c5e0548083e019400704a444a21849400074050f8180780340c001c10b90702850001d04100d14041c20480391240d000c244541c40030840c441c581090807200c40724420180222101d21400300100c1c101e800050955015820064000034402d0f010008201030054204034582e000d44d13060301024000d035050342090990350000d0024080e4207180c208140e401446144689100e0300c00704105000c60b04200c45000c504d54545025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 125116250 1250 125115000 125115007
    0x1504030201030b060705010213060e01032f04030803130b1b04060305060f040c0c02120102130302100306080d050306030118050a0201030b030f12031503190807020d0c0b03090709050c 80
    0x9540700c0d0b00f25031041c0d40050b04036840c013900c82c0c0d50182264000041d401e0b69400d1040240b100d41e070b201c4070740c00901c10240780a0110384c6400c6039100074031003c02010706c40b9100080800d0304040701c0f60192030080d038018907156260305d0600d003400c410940201089900360005d500142078540d800f480900300740703c4815103e09290901405900401d8040c1a5a40c0048400014180fa80e9035006060801c40e2594a000c84101284103200e0b407a100c240c440e000c00d90041c0725840802c01440340c01400c0701c0d011507010b40581503e09066009004c1504518054014480580c07660703504440258080e03201503000700011076900035061841c0940c0100144660032010399100503600c80d411103469800004c044e00d501d00e00a0f040240b40411600400903810408010483c84d1500c032a408000600c1c16005000503042d0100d10303041c0c03400501c50003080003601003000c00c159150454601681a48001c0a55440d5102c081c8082580c1086a070b2035510702c43c440c004543c040c080d0150500812003020300c0b60070f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 125117500 1250 125116250 125116253
    0x19020d0212070c03060603030c050f0d14090a0902030c03010807090203010e06060705010b040c0e130c02030909041401020f04030b1005061b0c090f0403080903070b16030b040903050a030605150403 86
    0x3101c1c2d02c81d030825110f40d441c6200100c0400c240b48142c8004510a40364080c031484d161501a040050202c09403410340c12030307141c05010350b8006015031600c2900720301300c0e562119944000b4440c064203411100c1c0316840030013004183c038111700046050318240d070210f484007507032090350b6426448240203030f06410300e00002050701400c09030003174a1502e100708000b10350303215440089011503850701400c5002a4180040041c1420554000c0d01c40c41c00540080c85202c0003000d0280d6a442040f01240c080c20044000400344402401c0740b00010701c00307400035551601100144011034105000a035824030b01280894040c498001c1c404040340c0014014504000042500c070f0b03112002c0b89140b04040c002c0c00d60804450380d600400034403c0c03010611203096401c050500500c404002000344401d80d004212101c082000080c20300d501110920f0400c00c040880d65080703000c2c000e100385080c0c002d070818202008140d0000b01500715100141d50400c143ca680b4401c100d101c440c00388044c464100c00300010f20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 125118750 1250 125117500 125117533
    0x121f0b0901110c03011401090e120717040f0303120e0d020601171006230102030c15131b03051009150c050f0f0306100f080a24090219020d02 62
    0x1c02c040020025a1845280c100103e0300391401d91b00c003e0351406848005120310000d0748a046810302c88000108100880c5481d01d1803244205d110113044440401c60900d02144010b007120042c00701c25030114015540c914029090180106010000c5420a00c40c45000b1b000055220003000045d030081178940d1034800b00b81c070300b185075071a10350190044100e81d810b82d4945010b044001c03c0d0034000e410b03c041c1414040c24040c00c0c0202c110341190420083c14103401c10009003e42c0c0341c03200c40d50301809525900005d003804088030400800d00c0008884003502c8030740180c00901140d00800542d244840141f4411084484048008001c0c045170904a40301c0315150b40000b1050f880e5060042c0380184911070301400390030450300f44504110010401c100d5041c110004455480c1c80c0c105105d85902da00800740c02c00d10002c0048018550352480850030f101400b84000394030368846100c2c00c5050712014000040c1d80204021201a2403074580c1402080c40043c40355682d1b42d440e409000b4103585c030103008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 125120000 1250 125118750 125118767
    0x40305030f03160302210a0609020c1605030105010e070806030a0f030309020f01020606030a080d021204051609021206100915030c08010807051005030a2003040b070c122003121f0b0901 81
    0xc04056523985002c68194920710003040203041000082c10002d203000c400d2003040031250010750190741000010411003045962242c0c10030440c0c00c00d80b0560f5074070008030f407a0500420b0050203881e0040045010b068065114080c482e000b0b94920f00540120310042e1f941da90305640c46601035120700200408944290041e1840c100304030409031514188148168903100300350380a564030b030032090641032680c1c900407a40c0700400d4852002c0d820006404100008020001c0c451801503178120320404c803141c4204d40060242003080280c0343c40d04400c9400400030102004c90102180800c1e00108449500013101c204494008080c102240008101160560800b45c6500001512000c01c880d0001040d002e20071180021946203403685000e05028281d84030103030a1200788050b0010f80380100c1e410b000f255070300940c1030810b4200240307000c0e00036054010110104d40c1501000c01e69180c0002100b17a0907000f6000072126900e11000904e10704203110300c6100d10314280c14100a8120594000d00c00d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 125121250 1250 125120000 125120011
    0x6120902010203270a08010608060408180a09020c190203060604090336142b0f0f020a080f06060405060a03060906050f0a021c090602040305030f0316030221 69
    0x10b5030700740942c0a04c540007030608405100040b2460740008941802d007004100000d01c03111000b8040c591410250031b03150f8801600c06055000002500c02d5004103101e02a000054040c1c404801140e035103903070b417000b50407038030080180b8020020444298444584520300702d40d0018040c1c002501c0d4002040014003441104405000715008510180c0600040c00e07803070301d18100740400d00e005039011045461134041c0c01903540c0400300d0341d4000107030320b503900364035920300134a800f00001a043c400c0d2120266002103008200c400e40c010b00c0c00400c09041142c0d21510b101341d0f0106030a980360180d00da1180302c1a108010154002030001d41e1b1031070586c201381d4100c0005083c175841c182d1640c4540c0242e40344071005070794075601e4009001440c61103611695010400c140114102817200590030030b0800c201c021244000d8945040b8000e00c444d5504aa004641c4041100d0f41c1c0d1805220108803508200c7c2e214034404410720001006600034004c40b103010442c8180500c05410741ca440810703040000c0c12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 125122500 1250 125121250 125121253
    0x20c01020c0a0833010e150d0b0604051008030c0f0d02030307050f030403090512030a020d0810060509030102040f03140706030605090f0a0e160f0504090b0708070e03070e150901061209020102 84
    0x2441120f13000d50381d401c40c2c0642410345014000740f41054802c08035600e0100ca0a00800b02d030f49482001c240308568075500324204072030124440e00c4070074060303220303900759000076046000004614140c0c0b90002411a005010502503400030307426544181d0b00c90100b26010000300300100080c25208040000a43e4094800c1c00c14000668484010462203d031128100d04280e100143e45814250104800f1051503a6032030f011351946041d44540440300034500c921024480d02042d00712a690b001c1d019100a0071108801c04269552803c0a01604050000c20142405042030114485110380034110541d88050210701c41d42d10381c2c0c407180035180401003030f02444a50740d0003d001c0f0018107000c0014680c1480e200e060f426410502184501c080c40c0c6d0107240703d0362400381c0500c001800003005aa01800905040460b80d5074a00305807540711001d2490765150045800206408400080080c0034000414130281608508018408440710a005800201e60704119000040c5025084103220510610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 125123750 1250 125122500 125122573
    0xe0102090603041e0602030c03010311040e031909030b09030a11010228030b1509030c120a030c02060f030412032f030a0209060d02070b0f24060415020c01020c0a08 72
    0x8175030b0400c9800070764032102c0c98103001004005011070f0544500c403504080300c0800c038103010307500701e070356a8030685121292030b900907a84440000e016522000040d40c0110b01d0304240c3c50842e019a480744c0c001c0750081c0214600c4440300f10001c070140f0a0312000000801104100840138403454406c0380c42c459000b04240d10b5003e601c6054884d15401d0529101d24228142c0b036183c420100341c01d040400710000d0042c44004081024480006105200240c150400042c0032043d4004281e1900c203e40b803039151490000107000811150099403e840651640c003000640d9200c55071014541214103802074840107091161044101c1c2c00085030800c6002c400185889a4100450340d1038018558020420b41c2c0401c00c0000d200c00f0076103856000300c0880780d03600c8504e0440070850300e0781c01e00b52102000c5141c1300c09802183e2502001c4070701030019030341c00110400c22080000c0da44c4c01c08507501d9005005400b0400e03e1411310040550960b00c0c040040c08001004113850a980345d4040764090100003d103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125125000 1250 125123750 125123753
    0x2d1a0f0d090501090209011202060301090506010c021008060901060801060c110a09060e04061109061204030509040f050403020f061006050304050a0605070903030e0d11010503131e03030e0102090603041e 89
    0xd10070003002a11a40010402c40b1580c010025546e00c140c0c0141d031041040001d403401a5600f6040f08d05550220038000780356159000122035100f069500250010502d049585420f5000780200e4480c2c001102c002425a88035802150400c9003032084030082003c655582000039150850498098070142c81e8100e00c581d1418031000f618881ea004140301d1102030244424000a8050200190201e180051610380b07a01c1c0406d080f4070070700700c0580c0305869240101701098072440485811400040c0184074181d5000d9501b001030805907021800b61042d00841e904084000c01c0c180e1044520081f140d2000707250620503a81c1c0da0004104841a020b891285c01c0080d880e88601d07406000305a031241c1c2e10908500c1c1c05040d24801d61452032044050381040d05c001158210041440e1b4402c1c80c12a842e42ca41d202e0560040c2c5081800401d11140e804184040c4000724400c6d030112402680d05103c4a41c14040396400c030311511088580241d01000040d02144076400483e4007842c1036100180c12031351341d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 125126250 1250 125125000 125125027
    0x70501140106030e12042105120706050106031a01080610090b121603092f04110c0c0405160507080715090204061d0711030d05012d1a0f 60
    0x90b084200030039955600d42049201c10045102d840c501407240038641030809841c0c0e024200b18102c82c0c5030400c10100000208142402030700f007000400710070306031641c94518040000d0003090103120006882c224002c295400c12242800c8000c0040e15422010b44074107041c410b13110440d5043c201401305030400081c003028103000500089400d600480f11508029080b41c94104d91400c850042504080c040d0300030465a41e07141400101c143d01d085005403068141d0000340320741100e2142d0043c581403c1500c203201c0980241203a040040c203444d0040c0c3e12000b000200c0d1030030340b10070848078400380b540240140501c0040070b0040c09041245e003010580c1d510b0300c2c00300c1440d1601162580c0c40301d200c8011802c1c14010750b000340540d43d10401d403120380d1032500c020841d00240b40c0c408002c1c0500002030740400520403113102d451501001e0009686940324040c00312000741007044500700c2c0658182d0404055140802564002104e14104602c643d0011203a0b8002e0760402e100c1000400c29120403031030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 125127500 1250 125126250 125126291
    0x2030303090d030e030c100f0906150906170a0609030203120709050a2c0c0c0304030c030212070f0608220302061806060d020103020d02090303040b0705280305070501 73
    0x10380d54001c2001441c0c07080010259132008808022a500c00d02c0070044104001c108540d02c4031180000044400c0c12032481c83c082c0c040c41c1e1010741000e10740030003120008400200e150955072180c0e01400165a070b244001d0600c0c1e200e6642078820381090320724a0001d5010b811800986000344101d038101070b00000032a11030201515403101040b08508200454204080300768001c000e64021114402c180c0c040800703081180d11005140100010b002920100c1e24005985284618904880d1034984070701e8441109001783c0001e9218016001c40c2a2040e94001a01820b0311007240307800311410300d0a6401e4071801805454075050034041161108040001d6038280e0285010b0b07401009541007035110a1540d4851200146003500010200601900d54010b05021540d0a00c0c00603501ca6410801500901480d449140e15000c0000e001032204680800340880b00d0080e015103408401d91940300103100e100c941d04000d4081c40300620408030b80a8800307049807034025030001c65440070f2540c481441d00c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 125128750 1250 125127500 125127511
    0x70204020306060f1917060f010f0207180b04060906080d08180a060212070309020a140d0507080a020307060e03191103072403060810200406020a0204110a17090a02030303 75
    0x30003008207145c207150300441d00700c000c1c0141d01d04215a8285500412044540030405a050160310170440700420310070001341c00140160410040031950080480740640300210310103112345c1c00c0110204100c002c40c0b285d01c04580d820402800030400e00c0c2d10a41b40e0403402000d980c0782c22503240d42d0104007032041c403040e15414440c0d04016030325005407020101001d000b400000415180c40003020043c0c07104454031040d1400010810309024005c00020000174070884020014018090005061b07580002c03601d22041c0301310207946090352600c0d0121400000390312201d500d60320859009200489211481401070302401261a40369210fa000c03034541885580041402c00703140820306499500a0a107001040c8180303030900003170341ba242c04103503a141c5c520b014142d0340384d40e40c4120301c5258035070241d61566203400c007000b92100e9031503002a4441030f0f1100141c0c00f5038144004504210f0780541240d150b0049900e0780d658080c8491424840b07050001c105188901c2032070280780142c3d80c204003452250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 125130000 1250 125128750 125128777
    0x6040303030c230403020117150111101811090403080c0f0906071101030605040b01080606181008040b0106050406080a151e05030111040b031306060b030702010203071e05070204020306060f 83
    0xc40c0745d40300041c2007509503011100c0300c11070682444100c0c9030000c1e641a075881e0901e484030440512540321800c1100000351180311034909401c0c08640b4580d14003071101030380a00d04000010b10803009010b80144102c070010000780c3c2110004050100d040c0140c155030805880c00d9007004180750100710f4650058009403a200f9600e0390303200d229a0306008040140c042510b06215030b214400001e807a10300302030b000310312501020452841e0060b60f68001b504c0440f00420484000401e650054a0000252070944402c1e00000001c2030040c01002214111030070740d5281e009542d0b032320074100d0007819494941c01c2035003107100d4001a0b617041d0380d40b0714020741206040801e14614000406084500210b404480b5100502080101c1c0c3c4505082e03035070002c7c10340d10041411403a450400b005100c0e41c4c12409280002009002480c1e41c1540038500c26840350b220002c02111121450b14581260f00e610400224100b05042c01800e06401450308100041e2442d4284001c0703950800c075a401034126a10b49 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 125131250 1250 125130000 125130007
    0x18050a260106050102030f03060d2117040b0103020f03070b030711010e010b0307030219080102030a09060b150f0706140c0a0f0504060c06020703210c020c0f06040303030c23 76
    0x9418038a4800500001480001c11400e46401c0000c1d450b401000c5c0c81d412070600c04000140a500c13070880300080190300100a601c6070385003a59007000b00303038400300c018000f5540c2c40c85121070380100700c00c0f1350240d1740001c070701546030703203035a0030004001900000740380c06000c0e541000403404070a00c0507502600240d12400704142404d58100d08642d03a00e0841c0000b03a0503e4505e42d10f07920f01240400681350103172038141841134625440e180040740c55102c0d446a40c400001c020400400b43d20070740169114040038816001c0800130050f0320f48070907140210322081000510904840440185003a902c2500c1c0410189035401c140440f5a000300c8204601180018881070170650040442c03909003c82c0c1041410315060a000502e1615100001800b145c0e00288042c2418003802c2c10003c00c3d010b401c002c0600503840f2079a00041c001001c001d0b00036110305400c8202e24a0910008980ea40380501014180361460b1030880240c070800a15005001c01f00006440340401140300c43c00381d250880c3c120b40e0303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 125132500 1250 125131250 125131289
    0x609060503190c171614090f040b0606030907030203012a1701050d020406030203060a0f0612020f09070c02090702010203070e0d020d1b050d11040f0e03040618050a 72
    0x4204801c5070100d820300060305010000b07841d1103000000c2d2000103070149558050002450726006144081440c0e5980703104000541d828420040b103c50340e007c2c0c40d481c00c16207030704809003034400b81600c00420808000c000100281030890142d07603c01648003c89207403642c3c8c0e8003c01d0854460388041c2448000c42c1d090b00b0b55915541c180301c0250000b51501001c40e03040640d020f1800501800703054403880540105030f0946d40c441c1c01802c00307980c000303043d2520360138400c0c50440100b846a1580050303905001d000030f00d101201c2c42c8410015000b41c400c03007000300c25a041064243d0000e0000c01030200c44140f190140e111501014403c2c85a40c000584c0c1e070409100141240f0b00701d4a650344602c10100c144001600e45940c0c0003192540305180d03243c40074201c0082c01d41200203410054000c0120840c0a0901c45007045034030349800103441c1080092807550045095480180750b9019070b51042104001d25441119070f20400403801c4106000759890304006071040d909548811040126141180d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 125133750 1250 125132500 125132503
    0x181f0f2703090b18090c2104050703151b0f0906050304021c14010e060118091a0702010c0806040203010b03010b0c0111070c051c0c090c05071203020c120412061e0609060503 76
    0x1b504281c0720140e4a040c4074500c0c205501200c00c41161a42c034101050200e0b08000081100074051a40400c0503c40031242202c900c0051451042c003010911041800c03c00c0107004a9101a03000580c0d40c809420500340302e4103a1b015400903000700c2c0c01803090200b5000c05008030000c0b81c40c41740718083c490000da07a140d02203400e440446241e070049810410040144c3c5800465452920010150100300c4c200c290400003441c2030319280c1c21000b00018010824202d0303040d84000f00c449000d882e8400d8540741c0790281b0080307020902500103000c00420051050070340001c060818a90a07a0000c034030f0320031240345502c7d550010030781190419a41c02c3c0901285c944068040720380010009080100101612205641881d510070711442c02d5035407020300320861007801150301e44e503046008016040150031005009610074016001c45019012040c0010517060303080703c0c2110034103c170802c2c88400c40d07100c40005040c1c007071a8002041444000d101118514001c07c0c004109000d0000380031032610b0b0525 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 125135000 1250 125133750 125133769
    0x402030901320105100302070b0403050c1506151303050114010509090a0f11010903051203010f0f0f0302010f270312030e15181f0f2703090b18 63
    0x1920790004041d0b995406003034404a90455100b26100c0035664941034060b80240706004c0c01030120b502610400040c160070900514403544840e049a607a01c10360982c0000383d4109070fa09a07440040c244a40020350043c40c0a0220b00c0f03609418090126682c0e5525821a004802c8104030702c070051004000500d0114141584070450030b0180c01050040d58540c2c0c0300490300e090081c1101e59880e4021000d03403060441001640d881800c8400907860000c050a040e003091084d4948c0b1001a4404100e40041e801d03540100c0b8001d82900c000c940c2550700544902c00024551020004201c6001d50800d00300050004901074001c1e1071041e82d820740c242031070f5450703084600000381818119490314046000800c450184072001e4081c150391608024840c49040b043c400c1c610503c80d80c0c0f0240c50107000403242c03a140b00c0c0d160404110011071b0035010015188540b01e46d14007030010004c0d0388a4001c1c034000c03480c40341c0c0c480d2809241c00c036200c0300003500c2504210344002500f964198085098188800034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 125136250 1250 125135000 125135051
    0xc060307110d0f031a0607060e010b0d03021b040903050703080c1201030318050405011809020301020d020703090e010e100b1e0406090f0b07050a030507170a0c03020d08150f06090402030901 83
    0x30b05c0d060812036004601c191207030400043c5107581d071714103581c860502035000c2d4211140040c540342200806040095503060300082d2040b6038400700f43c080da024a014072031340f041c065060f190542040b0441d101a100c1c1c200062102108100030803140d04007508000c69680610320a4403101c1222a83c0740f50500c100c43c0726003001c3c0c0101e00d4040140f01c8a1407120b1004a0f1000807000452014218404a806405903e08403c0001e0020425804050704850b1000c2500c0440d18820583da0780c41c01d108034080f81c150740f07003071250402a90078005500748000424168100d00c0d100244c52116030650800c07035009a01c00c200203400d01d00c0030b11410590304800c1e002044140c0d0050300305a8140c840360348079040400c6c000c003480000601001002044070400c001e43e4440c050140c1c0706c0381f2620010742540c1903070300700704c0040c01a01c10f25200706014001305800b0340710f09051004040001c505111440d407a0b81031659100100f0700112202c0c0d81c0b41d000451003401282c0c00440c602c80b10162010560428920 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 125137500 1250 125136250 125136281
    0xd090305120a0605240f070605061f08180a050a0312060503070b0d240311040501150801050f06160501020a0810060804020108130f05010c0f0504080c060307110d0f03 73
    0xc04200f9603442800c518170540012045100b00d850052410300c1031b105101072076441500c08103e804c01d1040581c07142d4402c090545425288040c424a04c2404035080c980f15400b05103210007084c056040c83c1121254402c0e80812200c940c82c0540360180b41007a4040c2c1100002c4c19038201421281240c001d240c01070205800030300600b410a41114614000c00040014850b43c0e000c1000790f2012141802c0c6080402c00c54180209480303023041045e0400c0548528001ea040c0800061040c030711a1241d680185581d5607940341d42d080c207042003040310340032000d99444235050110701500760b80b09507041c180910800006035030b41075020002c0c040040c001d01107114906c00c0c08040240980041b500b990080c0c2c24a07100c8480e603a2401922030045034004041c01881d90f440606003089015846926034100a40b031380c01950b5146078044407540300318018038032035403c2121803000c24185040603642040d800d0038140c02c8034060081403440d101051951070700144000244048481c1c0500c55081300c10318111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 125138750 1250 125137500 125137511
    0x606030106050a0302061903060e0907060e0d0b0a0e030c15010f0509040302030304110607060e010b010e060306030d05370e0103020703171e13020405010905040b01031401020d090305120a 82
    0x8000400c0f90040c21f0f500e245e10040701442c0c241003486580302202405c2e1143d0318682e203080550209544441d0b900a00e0b01007100071064040314580a40e041c141190b0011f0401d0b0170f60394514440700030304540234542c001c82c4018070481d0241e110a00110410025041903079580c1c1d031600d00d40365241c0d141d60340310b075004458090030f0002096010044940c01900586070f64070f1400440040b5882748540440501002e1a103500c03102403e074190445150f505013661021181e00e108800c000c614030081c1d600b9036140d4031140003500a14041c5028240c0100000303016580700310711505080191600d640444000c05504e01c40320440b0740c100f500064403250030701e421420111141c0e00a0000f03e20200b411034803042d6440003858100488030451040406803000e03042900b00411320660b80040c5401c00c9128030305020001c1984030f85442440d1041d0b801480c0030103142d04c1c0d030301c6010400c07c260381516a10b54003004065444000340c000e41c00e40742d201c0e594060b40d81103a205031030010b59010380780810300f40c1400b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 125140000 1250 125138750 125138753
    0xf050409110307120515131e0c06050703030b0405060f280801140106110a060e0f07030c0807090e0a110a0e090604110108040201020c01050c031209010605030f030f0a051303060e0606030106050a03 86
    0x20804128040e40c003212a078a5030310201c60f1102912000e520049c0400041700c4080303213203507015018028480c0319071004c2c0015800c075020882541e0044907001c1c0c00840c1800c81248520b0940c90030205000c011b21550701340e0440010503079030340300c02d07070040e6509070b4644c0050201d04004040d41030060900b49080080364032860062a2103a01810b0041e100c0341d00c1d2424504010010b005070945101840200d52000b942c07890301c0703800d0007101d118411041c0919000090180e0b40e41c02501d0303070060560058516006590b071421003070081821401d40159003940003066451f02c0702500380c09250303070300024000c0b4030b031620b4070b0b404005408913800d0420030400144001030b43c0000300301441c0903007400c10316210544018160304d50301481d110703c190034010308140102c07001c06500c9541524010380a40d6045200b030245140c1e00d00c01c00103020142030742044940170301441003002c0c244800c60000411000c80d56074860340180c0e040e0070040350035501300c42c05010003031a0900c02c1c0d100a110559980e0406440e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 125141250 1250 125140000 125140021
    0x911181801151205040c090e0712060c030e03120402090106031e050a0b04020d060302120d1215090614120c0a05060706091406041406010f050409110307120515 70
    0x103110b1400314005081d00c010441d4022100c82c151000407003401c100324a0079043c5805258102c3c45180000c0e454021601100300c2c002c20810107441000319204e60300080c590b02c0c403004000304c0f40040105039595031104803003c81032005000880807100715100604050041010108041e484038007072501d4032829003822451491003e15500d0321213070000d1141d5490f00b801010300b001000c9903620500c00142400500001c0d4132044c1903e000b902c0c42d03032080f10280d0708103654800000114002c00d0030607031101d5074880c0b01d0300840b219205403141030080b5580c0d80580810ba5a1350f0300000ea000703001e002c1c15451070601e4000d87c1c078a000c04100500062440070302068400501c2d00030107018180009034580ae002d443c1c0c02004000f5030240d0f0501c00401c8005c040350700c600040d101103030a00f4030031411040c4031000141c0c15041e190102c4130059007514020400000300f030981d00803981c10000364045910703554207024020007010440d19200070021240340990900d4206440d0084001e0390308180080c00c030070b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 125142500 1250 125141250 125141299
    0x901051014130b090108010c0818071214060f0106180b030105060d0b0603090c031606020d05070302102c0a0c0b0c0a05010e031b0d121104091118 64
    0x1002c2d10251203416150303440d0406000490b10b0305800803169000080e000306c0561000c5010603039603032242d02c2030719051604590b0500d59140300a89500141c2c06100c030705c180e201c0069800d481540c03c2d800c802c041c030895a051050845200380b40321013040c010807815410040d0940289402e00400ca2406c1c00c041e80c00b840d600042c0201406001d0100c2c100c0c4800100c2d0b44038070249500103004070380f01c0c40c098440a64a12401d510103000b0f0080c0c01d0b0b2200940d041910341c000366280c8bd0003030800700250758800c441b00d801c15001070302107120340306c0d00254070302661089041c01c0c1c100c0e0201e0341500c031182d080d103650f90300c4000c4520525404800c2d900d0128080c1520901602c3e00700301c01d00d9544c5510044180741c03008400e40039000d0f518103180300c0000c000001c0200300f001c0b0303988200483c01d01e09030009a101c03001101500301284882c0b162090b8110103900c2051032820500340340c1d00302034442882d4822a0400302d10351400398400903080e840c018503480c404040300401c545000d1440030741c41e40d00341a000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 125143750 1250 125142500 125142539
    0xe0a0c030b070c0503070c15050f030a021810020a030206060a0f0b030402030102070803010b07030306090c0e010e0a150c051006121b0b030c0918010515161a09010510 73
    0x1200d02055095101d5101035803603d401c80100c0b41c880b616807e103903004403510721400c40c42c0ca205044548035503004400b500c0001884801c05821540c8101d8000d019500811800c003810a0003030440a090f51141101111400580c3c0100700c404410b1030045e00e4410003a0685101d555000401c01c40510881d075508252010102c1c000c1e00c0f5195440882d02901503048020000c13400400007085441c6071030068040240a0741d000d01c0003540c3d0303400d030307404554034500d000c0001101c101c5500300399401030381c0f20041424041d00c850481030f0303500380580b0b4030b451640605c0005010400d5240074810104004413240000080401050380381403400649058101d800400369140c08040c2c003585038500554a00904031000b885a07240b401009420555000c601e0041c4244080416071001350b40b21506603043c1d6001418001c00b03403104491440326900030010412030159a4a084000909010f40001e203180c1150035030004c3c3d0902c8110b183c01c0d81c00c028801c004002c00c2e0001007206480f41100502c1c0384 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 125145000 1250 125143750 125143763
    0xb09010b060a1119140c0d110603061210020405031501050109030f1a01171c0e0402090604090c050306030d0309030504091d0a03020c0a0b03060906090c07060c0903060e0a0c03 77
    0x400141c0703c03142001c40d442d080044110341d410146050100f85402c1d40c44004010003a43c0c0c1c10103a0000300402816100d20103081812286045803003428898010354100d58001c107403080d00c071440e204c05840c1605103031020300032580124007000300307080801c03001c441c100c4c000d86020080d40c10700000a0240000f031002038a07100700d4481040031300c1454000c484010b40960b0122455603101c40c05078064101c0040b40200c01d100702c0050000b028018100c0012009480c2d0702d11050404c3c1004010280d00200000b550081d810072000403841c110703218000010050f80c55607920703803501008142c140180c3c0c424140905080003000000a0392100485064426501d03000481e40a4640d45645a5100c40031100c040c0c411408e880c03080c0340d0001042c2c40c6114045032078200c607684860020f516030200b5a44680c208047c140420403a00d40313955500d5100c0c500d08202c904200f00741d103c00f001c0d145c0c80c0949002003003141c1824802c0c00214040c0f4442480701c280282440c03030f1241c0d01d001035074540d440054141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 125146250 1250 125145000 125145017
    0x3050702120303070e0111030a140307120e160506031b03071115090f03120a0207050115030309050405010b0c061302030f101512031d031204120b09010b060a 69
    0x4541e1180c040c0340c041d4519508494580c5000034015042e1080032510f240882c1800340d07029405000082150101c1e035a42d9602011010030400b168003903000a01424184031100e00340c041100c140344203601012052030000c00d885d00c0e0034420390740e050140d41c121a00411041003000340340d6074525401100ea04001e00701569940c0d401a00f2103440200c5650510180101040c0600c81c600035200d60b40214020b0041c1e5000c080c0410b81d1a58078864402803121000c000d100150016003154040c4c031286000e0360001ca115110108100e8117420700c3d4200f21301003030045500740b06c5c60410703100342030140040c8541030303180624044d40203968140082002c020326540c14048811503c0c01d200c40d4254007034031400c88942c41c640985040281c5001001107c80303807284240012210001509045556051b454800154150403404040007540070b9a040d01441100c00030800c3c0030400300200024007030040c01502e01788451a21400035a0080e2004440b81e0400755009907998990b0102c5141507042e04040c00e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 125147500 1250 125146250 125146253
    0xf1d01060f14030403020c0906040506100804060e0f0706090f0b03040615030213020c010e061509090102041509030b130809190909050a0203060f10090506012f010c1b030507 76
    0x40c0c8407180103042c03501c241d000c411300041540008001803090b00c00c940003002c1c0d90f5000d0034402121402c03901c0c6d503071015084e6581620341d4000c00c207c0703801c46d014040214075198104845841d0403418a5940030580c001c0b01d0402031150720804150203071089200c0c01090500e0700c1000c02d4180809003019125640d1135003a89407401c12803c142004650250490b110031076402042e000035003000810440c15400c282812000140105100384a8422814980408981802070040320a0010a0584159400c010200e1440001502c00101f03c01a50351280301d1030852801c40358218001d00b400b6507500c00240e443c0c001801a10a0700d0340034800340c031500452410070b10194003071591540140b02403850600c4210900c4404641d8240b043c1c000d070100c03512034440140c009114042146c10796040d03030074035000740305103d240d822441e04210145407200c1c1300f41d1151401c8138861a004003a2490a04202d05a030700c200c400e0061a59000003400e241e080311480c2c0c0f441c1c000000b01b0310801000c010700050b0680 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 125148750 1250 125147500 125147507
    0xb1e09030f0d021b100f1104030b060102030412080d06080c0a0515120a0f0c02030f030c070c0e091b0613090203090102070b011706010b0906070215160305040f1d01060f 74
    0x1045483d810210f0340c1d82040d102013050702c58000e1500c4014050400134803d003810201d00503000d01d20040d0414901c1d00749941c9072000014006000b01d0b0440c0404c220008030152200c00629049000740c40042c2d0f11040c3c0740c4101c1c119030301c507482550341c2e4000500402d2241d80319103a03407003214005d54131060300d680403200074012440780501204004e00084e081c01010a05030740a04801001240200103880108009aa6034002c40100c120f41003020000101c81042210181424900c035281c188841501c0d00014040c0900c2107d1000c0140d100c00c03040b940000343c0400704907002000341c031542d140c00e094079180b2a0111240c0200d01030b4580000c0400c170854001d5046a007a950040c466a1013941c4400801035010355501c1746a04034072500001042458442080f6912008005e007403502d807410a509000d819848000c5004100c0e0051200d91107000600400701d8000d44251f0b5429943d60a1000494079126660081c03684113849084107000c40c038074040d41170706541c00d90800200181c211030044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 125150000 1250 125148750 125148757
    0x3050d0f0f0c030e01140f0301030215030105151606090b06010206012102060c160303050c0d050a0c240c0c140c06030711070302030d050d0b0d080306060c1006030b1e09030f0d02 78
    0x4005506d00040c4240803182c445000c0c50603a0720072204110001410504e440381d5000c02e024407640858010107610000000c880101815000d8408a403a01000c030344403641114800720040e14001d5251040010031340c0d0620140c0c2c090944065219030310b2004200d8002d0518111100034000c2d400001d0404800c80200040b15017011113500c1c031100982c40e4a0010100e402400000100d4070420400074001802541503403400c81055071008038103002a00c444000903001c4608020b0240c3c10b440462200702d6500030b80201c60301c507440d60b8041c4c40d504c2c03900c00846111901200d0a6070490058942035503240d4080b82c3d00000b09180c222090781d04c01d00401d04159980c7d200940c035200702800040c02a070081c1c0a0400703242507000810004119401384240e206159400602d0540304000180640c540b01000d0845030f0481812134420003601304500d03080341d1213500180c40075403002c0700300b00c80110b002c00300c0e8251082d101c5c0d18240340c0c00e01e146406e64034042d180b1104440c240210714110300c001070364180c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 125151250 1250 125150000 125150027
    0x4060f0e03060106020d020607020715050906130303031d0304030f0b100b12010906080d1713020406080705100507030507020d1a040b150a060207091808030103050d0f0f0c030e01 78
    0x2078500e1941d513981c0203591924003515000c05030140d0800121400d0002ca0351400700c039100e000c0f01c3d1420100701c00441d140e500c0f41800a03405032040c885801d00344250f90401c405503100740c40c00100702c00c262104000b007522161420324280e004000500016210742d104200b07032075100b0030310030060302c601902c450010305940144c00d0030340000c1707201e030030101d07900742154100d4001400030813005844420450311004d1240d008004502d8044404050b0f005082d0000e0740090010030700000064503600090a80b02035604c020416404007a05004510300700c22a42600c001504081d441c2c00a1942c3c003900c076010b0144040e20400c22081d501c800d102c5411503c0d0040b02d40300d14210a14a0103242c0740111810544400080540207020010b490800c0c450300d00665000750000c000b00d51404000e0300240a234080042181b840429071140000c085402071030185110307e001d030030511a40c400007851030300c000850000300322015883c851403d80040d08891180d4051900210754507510340142e036100c0a0070f09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 125152500 1250 125151250 125151253
    0x21303080c0607120606051603090f09091704030201080103060b010201060b07050604050c06090d0602130306060f0812281404091401080102190507050a021e0f0a080304060f0e03 78
    0x5101c14100008115688103002c0740d120780c282c1e0b046035061342c8220b64441c01200302158040103180e8048000c403503916603041c824a08110340b103483d024075542a0314150f10151820751900259401c1001001a4030300342030030034031a80c1c1450b146400080904c041031001a1040359200c2400721180d00c00c2d04103001030304465034103a0342c5035150300d842552550121810350b0700c1c1c00381c4200b0114500e06482100ca10810013800c03110f030300d03415440d400300950000210000b845c1100c1c42c000300042e514000d8030000c108030b00b420000d152520354024180080042c2402c4055020410301281c1044070383e11852404054201300360155045d101501c045c0c10303a640fa50354262000c51300041d01d0b41f49800843c88040341c16191907040e41d845400e030b400d27401155140d0041ca0b04001e04514594812800380c02d001d8041c00c03c44140206c20303000300350340030203103841c103200d008406503050114180320346040c0308014265000320005242040041e224016400343d4000c0000900ca6144414415280820104030080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 125153750 1250 125152500 125152507
    0x50a02030c120301180506010e100905121f020304030c0602030406140a05161103070326072d020a060b210109110306040c0509100e270304030206090402130308 70
    0x500003c3c1c00074412661001c076810300341d50070000c0c64042d00f40140011784903010700c0c001d0b0744208403040d80c58890413010807211820000b103030741c0c419005907111044c03540a810300000000703242c00040301d0300181e10b0460f40100b0a01c070020b5405206c080b256a008480140c03a9140d62526102510340c0c1a00c084440103440113000d142c00d0321b58813943c010649010155400c0070007041c00d03120b151a54080d040c0640090003d4408070f40524500b6044070294030082c43c420104005900c28510265004070005444098008010346d0030780400002200300102c0c1d9410940300c1800075955076840c180200b00d551191100b017640d4944072901c1111103815165499488080318882d4001d000c1c0d000160ba11129403031031006982004504180141d40101d107011f00b440c200824811055005022082400310700000001d0900707807040b03818050202000040000d82da0742d9980f901e003080f01c0c5080240c40e001000f0820060f0380318021190007410030342c0c0c0543c0320314030444803454140c501e600141c025034001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 125155000 1250 125153750 125153773
    0x9070302040b030403200118080705030405120703060506090424020c030a030f0b04050f0c070f121e050301060e010806062514030a17060301061a1216090501050a02030c 74
    0xc103082210034075000c640b22102c01b00c00406400d0b5404910710358540c01a40c1000030209000c40020b029440c0140d0480c1e141a82d2607001c00d0f03024284030400501e03600640344c18410040780780525030300007400700c43c00f02d0242419124001d0400b1354469518920140501a04000406806403080c0c40b00b01800d5039213170a40d101018020f01091903880700141d14211449040b4509445064000c204460520200c1c1c1e4514001c2680e41d840f1800c25030b21104c400900320b00003044c40c00340c0b14420415980e151a00d00580f0b001c0380032004034540d49024080c0c1400103000b41580840301c186010b400340380285003501c07100e0214100c1d100c0c519440041c0c8811051190359403440d0716110a030184140c1c1032140c4403810740d1040e40c0f01d0040c4104400040d0002c051401005040001c0d69004003008000103440c2eaa90705201405100380101012549004141154404c07405903107076900a0702c0038005250404200001403540f00280200c40c10321802150107403200d8030800503294802e40c040119210025007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 125156250 1250 125155000 125155007
    0xa09060b0a120c05030303131203060b070c050f040504022b0b0c0a020d030902030d120b040c120c0207030507060f02030c0d0302090f03030c070608090a0804090903080601170609070302040b030403 86
    0x82c42081d1a07050b140d4400181604001003128410303100800d082c050304202d55a00740807602d4081c030744002c040d111140814ad00c1c280b1801807540d14451001d0340c040d0f030714140a10a407042045643e41c0300e2490301c0208800b58840e505120b00007400140c4890303841f001110b00078000008288080c18481c40b9408102c0017501c1c15004028850a41c0c0848e035004214407022010b4460303152009405030481501c540000740a2905500b1f1001c410001003580c407040e101213000c83d0441c40c0148001800c1482d5031090034200c0c8111883c0b02e115202810809065803a041e550320642c0c4524402c0021602140e0748040c0300740183c84800b1048e6040c2c034614004450001c0c083e4001c8007001d4402c04150041e840280b0700002114440c0c00e000020b01103080c600401550706007401820220f40c3d02481400b240020705880091000e05441000041c7d0482203060050910a0040205043c4088002c0c8500d1920101590a500c882c007187c12814035a0b420004901a019941c081c1840c008088180402c0580 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 125157500 1250 125156250 125156279
    0x1c020306040506060a0c1203020d0c030902091803121e0703050118020316140903010c120f0b010c08091306080c010f0206070e040b06040e180c0103020906030a09060b0a 74
    0x4880520040c0c6a0f9000c1001e1445114503c0300441c000e19690b10005491401055017964542070040c1000021602d0200b40c070120000c000c00a56a070460004516003000d40ca90010303a107401d415410104a20881e030303640706120003c005011a0800154040b03031440c00c08a02d0084556603404505040708098040e01c1c0c28080d02174000b0b81000740c019032036900e2003543d1103420b08001d4a075803802180d005407210f86100000c0d62480c801007250000c0754809000f002d002d40f046130385280d03907841c0e0003040b04102c0d82007507404000d160401a02d8000b60303902032111130081e81c2040440381d0754214480000c448400c1c0c00d43d01100c086c24400700250100c00810700401c41142a251181400c0035800c04036260b8100b12070500c00310741c103540c1e452014201540a44070b0680c010b01841d141903102d601000c081e00701250791040c1003100c008030104040081c40040c81051b03007800c055040220004c0003403214003000340702211f43c0e60788030b407c281802402c3e0000c1c00b103c0c5c00686801a401c0d101c042c03042100700c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 125158750 1250 125157500 125157511
    0xa0608071719051e03030412030e070b13050112020f0906030c0903060f010305011a010f1103070503040b0310210311010b100e010315030506130312060602030712031a090c1c0203 78
    0x104d01c99007400e851100881168801c541c884940f008070078441074158010700404c418a9014440c141c400301d90b144900c401400b902810b555201d4650b45020700043c000c1c40050754142c24030703006101c4469031103d80f0342640d13000c09085400c0c1351240c0e0342030480301507400350010130742d81441510f0500c0031408030059414141c0c2e0040000348640801d03009050309400c11a8070381d0780003510300045c585290740304204c2641e4000f52401035038600100b42d01e0f50751550b040b43e04058400c01700081403041e0300505020303010042000c0c0500441499654406040d2062654009014400b411080400c551070030750025508072002000503400909410008050089840c14540424980f001c0d000c00a4500c081070011240e008000b4030090340c44d9600549503d801c180c00f24140149824030040006642c001d100203450a64011f586941241c1041c00c02555045440030900d407809004101c0700b9010707429200006420b079001940390300c4030168002d0341e202d0294044160034921089205210441d00214040d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 125160000 1250 125158750 125158783
    0x20c061218010f05061e090c0c010b0a151704050d080a02070812040309090b060f07060204080f100c17061905040c12050f090d1b150c02060a060807171905 68
    0x4012901416012203000c81143d0351013030071f540010740c20208007401803a481e003c02002090343c1a2800c0030507030070300305908507225005400d130400d100b00364080c1401407100146800034800307042c103448076600c6203c1000c103002007140010005480d50080d80450f504a980700540781c1c0d40c1c0e0740061890b0f941180c00e0f102140021708503c40001c030250b050058080d11880201980e25001100c1c56840c01940300e007408a03541038081c400011201c0e414002802c0c100124005440b950070043e40d420b040340c10155140c41030010345206002c080604650306076000c4000e8440060101c01a41140301448087d40115840303810141e0305188298886018031015198003000d2016403180514500394000860700e024455210340740b80081148940740851032500648503001e4030840b9900c82018460070b118842081c10b44840c2500003203035040080f10381c0048101030400150b4101f900040e2660b515100742c2d4040c00d54000040c0ca00b41041c096114040380c0c1d0619000504900c0c40c1c002e4907011800c4201110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 125161250 1250 125160000 125160019
    0x1a0901020d03020c032508030c07030201050919030e04110a0306030515040f03120b0402042d081c09080a050c0901060c02060f0c0a0203010507030219020c061218010f0506 75
    0x41c40e009009a840100c1c1d41e40280d42000c50020800c100044260640d000950810000c040800c0b03060f001180606001c5580507585d40d158180a400d407070000e41004015404518a0b80148844076400d01c1c8aa91501d0101001d101d4070b4000350240040850486690100181d518210398240c2e01085c2164426001e03190210311005480c1c090701d400311000340082401c2104040040d1058a0328030700405594400140c442000c0c001c5012608a034110340b01c0c0d01d2081c503140e5400c01092030b801d401070200507000039030682400152511010030004a401d15200207112064060040e040130010300707100022a81898a241040c035620b043d850b84080c000c062910000c94040d1144944c040071076005042c4070b02c0c04d0046d40c035010050f40940b0340c1e001d440c0507551214006071fa0a005a07030240d07040340c0d000358840c03110b02914030084904800c4070066512070803a41405880d50f40c2038506800c011182a030280da98080340d5442c0415007031360100c030b07946030804c900c1c1d20504580c4858080c5109a420091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 125162500 1250 125161250 125161273
    0x70906140c03031602070e1e16090b0906040905040f03032405060a090b070b0f070f020606270103080a1e21060504060801020904050603011509090206041a090102 71
    0x955100707844101107160002c00002d0380504c410400303c40ba080c403620444401590300c5c407500002c100c094400b1050b210803175603800004d0140c0c907500c5410446c04040c2800d60740d54428007929034400781c4a01000008080303548040c598400c0203580003440c00000078441407401d03203840f510705603040c00202c01081c82c150282d2408c101031000600458040404a040a0700300720403c50305030840300364441001044c0c81c2c0403484000110240c520f40344038084248980c24001c0ea41042d640380188070340100524004d0343c0005680c0041c81030340280b0190780c0c001e9160141e041401c01c2c18000d20354080f0b50001080008200071980b4010050041c0360f13510b8000410b1410040b10a030148504180d000805101c808013032407401c0846100c00310001c0314001007142e600c401180945001e03500c5699140d50101d071000c003505041c0682075010400701c00800c880c84100c45601c00101c428024590300030758513100700085407525012940500301804007400317442803481d80c081896001c1c01429005001d000c50713644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 125163750 1250 125162500 125162537
    0xc020109030c17070611030601091505040e0903070209090d0e03060402060a0f0e041e060806070813030306030209100303031508030307141605071d0108030a03050a02070209070906 79
    0xc81040c0d0581d2090210100c030b8540e200040e090703550000c000d80042140700005142480380410360020000c0301500d900d030010014204480c1d962201c4040e080040c0754160050340b1408070350541e034900881240584850850b01d15502940d900290842507034030900c2030020300002c1d049080265591026500d058107000d04d511040107640c020340040003440780e40300c070b00d0140220050900300c5190010075440d000002a05660742821003d1410500b00c1820310041d0181c0074100143c1030b41c2004011a050a520040400c0801024010022144c041c8681014429003010004640041c5018983c1c01d115111488080c0180b1080b03010030f2030038000200c07424002c9a8082291006400396086942e98042a10b02010201c40c1e0102c021041181c44606040b510250009078015002400c41c2418081401c403800c80e15244052041d80a00040090341d6000003140c02110315460b012550741c4039442c11a029000b540c400039404400d00c3c0c1080511a0f0114100088541c13654900d14490091039144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 125165000 1250 125163750 125163761
    0x111030f01120f0303110903061810051006030b06070602040b040e0a090b0610030e031201080606030f0c1005071a150103020a2012040618060e090402090421020109060c0201 76
    0x140300c1074141c805000070071701991003541592401000c803841c1110500009040c80400c40b0620b903c0361040603041c165410420000513034500912041005040c03941034500720341e840b88150003c05407118414001a10b840040c3ea5040303a10400c10b546551b00ea03c04045242c02900414410341200340016030352480c0c9002d0b9040c0c068005010200f0754480405216421407000c8200d01807603180d4042c0000b07003104100502d41a071091601427010350420001e90304111010385a80c1c0709034800305213002d2104000c95000031420088440c1001812020000c0d1418015824090050049400e50001202703584665912a1031203907003101c42034501e0001502240a64064840012040e13040d10b0780300c0000b0386640801780001c0c000c407001203080606100503540300d81c2101c0e0004155400d980e0074510000c0309180a06070f1803c1411044440a020480550b80104041c2c4a40b2803c00402e0034000c003001d00b48809034074043c007040b03500d030119400f0740602040202140d82070300c1d03c0c0121a6541c07062241 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 125166250 1250 125165000 125165003
    0x1a030103020f0d050102040b040314010e06092a060703030905010b010f12020d06031b0806010e0103080f1803010222050a050a17030f030708013816050111030f0112 72
    0x3403210041c0c89406020f0402c0681c2001c980e690340c01c0102280702101d10000c1c000651080f004010382182c5d07181d1050940743e011814040d03d03444103042c07002c80e01012a40758400c01d0540c2c0d0440a824818140c4000c516901c824241c20040010b40ea90505901d0b810100c00385001d00000d0200e102e00000440f6100120740c80c000c00140742c1c0e001095103000701e80040840c41c4840001207961303500d07a203900c00005281c0010640e1003074200000c00c1102030520025004000c09201c070441d07585103884000703551180075a081d444400c0001c0c00d1380590122a400105420090000c5440703150010319901d4a00c7c001d041c0890307204280800060b9441d120840d50300703407900034041c402e02a1400a007004207000d03516184003540030138072900c03031109564400355220305410340d10910039500d04401401c2100301000d503006074004a05e503500c08a231100140f84080c0c1020512207541d07440da10300b4001450400d00d40100a5400d0182543c803c41c050f90207540241e214102d120b02590f80c5007007a04400303950010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 125167500 1250 125166250 125166259
    0x6060504050405150f280b130902030c070f031106010b03010807081b0108040305070b040b0402040b040e0d1b050106031a010f14040209040605060d0f11070203190203070b0c0105011a03010302 84
    0x4605009003899806510b1b804506044020810319420100c11030302941c1c0c10800c014407000c11814403e01d070034034a8070700070b10404004510314144007000712118410188064080d80942035041c0401d0f02c140425100c0e5809407041d1403241d6100c200440d0158001e100d05105403280d880d000c00c205502240066a02000d8210405e4101c0d04200646000000900a40920405103d00d40c041800040703410b201c0c511030a05107840b480e00d4810007040300c41c00199540a40c0c9050309080b4103840009010954100c1420a10440000700d10201c0802c1c0c140d40008241e5400d0103400400c01416a0001102244e042d80001890b070b219038141c04c000c00c16101e0303180d101203009a1850b00707043c80c1d4000c09d9081c0300035001203240c0e40c88202003529540810f90a40081d83e4541c10700d440042180306d1031892040f44144680ba0094940000b03540345481030921084010035584d507800c6507420802d0303034010103804072465202c102c0700742828000c1c8000d00c40c500b4036500750310340b6403210100103080724180da50050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 125168750 1250 125167500 125167519
    0x7080c0a050d031116080d030603110d08090429060a0503071227030311040f06050c0114090d0f0305010608070e120106090209150c0307030c03050d0606050405040515 73
    0x404200680030b04010039020700c04c10450130906402c00344100318080f03000000c1040c20b00c0c58401900e20788801c1c61208400c01d46030030303020300001f650402d1008040d00e003250700381c11403140ba00f0b00d03040c144076080c1800c0e807043c60480d000207030f214844d02c41400d20b12201d015103e107070030260501c4014828034240f01c0000ea410000501c5003401448a602c1c80012400001200c040d80701d02403403201c4071041241042c10002c8521420140c2c0b40c0078800007000e04c82040c0707050524202c03610103606907602030f9805002c0301245003401c903402580199440d144004111002d8100f00e113085489e0340001c5141400100c1c4032420328446030090088504031461039840d00c1c480e96a0f000200c0f80340040705c0101d0303806441c036044140d401409014140207007a08441c0140d44100d54010040401c1d03a001d189840700800f0301200d4002c40c004001d651856816090a2440c40341904e0111801e220348450b0082d51444c1c04c4010590560040117001500e400707450410264445d034008102c0043e4081003d41e22801340b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 125170000 1250 125168750 125168759
    0x402030718080c06030414070503030f040e0a0908091210050112150209030a110d0210030b040605120a060c0c0b04030807080a020720150c0606010207050d050607050711060703080907080c0a 83
    0x29007070b020849000900b079074402358650f80004c2c05c55200038030444904001081c1070140c42c003a40c00b050341025010204129503025503031000840d014402c40540715901c1803121a645400900c0b010784280d8941d4400c211960311100b404004001c4c041c4256000308aa4501004000180c0300315401d40000600904805000c0d5031a090545c403c2e08040d90404c0304c007151031005881e107400003a0941d00e56100458903110900a010407951140c2c4220b00c1030041c07180c94003500001054001199030850800b155094281c901070340c80d180c645100804c404841010030040c107a124039158042e034007a40c0e8454207a203c154905081c0e0040303500150007618481e805500c0504448400030300c21030b002e02605289480c00448100c0794101450024250700444100511980c0c14400c2c100030f00f501301e890310140c2103580c94185d034980e802001c110501c04001440828401440a800290031000740000d99602c1076103001000c0380b405444a018500c11000d002c91140c8011408444025021300a00c2d041840c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 125171250 1250 125170000 125170013
    0xc040b090d14030307020f0115050603040b0a0902060708030405061b0316270f0605132702040303022505030a02150d06080601030c0605090a1202030106050402030718080c060304 78
    0x540382218a40b04207a1107071a10541800507605c207500ea900a40b9040420400c00c5080d22040402c444041c0b840f10b0b0203003c40d1f0366410949800540251580b802c5039561203101000380995080a9400715000c0703000f0b130800900c403000f0f5204910400a51f0141c1d203541d0b5400c2507a10307088500400c0b8840a0001518010004414050411061416030384903010104004100da4075440103070048088004280071109d8010110790040030585801442d05050206840c42c4c51440c0c001d904242008807a1102c181413403556094086040c000300715591543ea10300655103001c01000c1101151000070070301d400f001c100301d0f64030440b10050064901110f0950070068034040101c2d00800100b01404182d182c51030922070140901325000c020308031035040d82880009081503030310500400c4810001603003551100d0126008440c40d049a072a0b8840203032000a000d003249401044d0040c0c4044104084c459000c21224110720540192429480c0c40c1c0707401a440d00709030444281c02070010400300d00054070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 125172500 1250 125171250 125171269
    0x40506040b120a020102061f050909030d0c0f020c04110301120c080703111507050c01080402180c040f0605070b010509091002043003020606060c0f07030c0306050c040b09 75
    0x4004100003511260480041d601410714080b01006911080c520310842d601000f40a40108900b0a0168000c1c90490b4000b20384030603001d032038095000340004c180040c004200f0354000e160400c0301400710a6030002c2c01080e010240b60744400502c11b19201840b5428a8450300100706602c9910618583c01e141d14100d032494100e101f2100700d0340c7c04500052100e814040390010394403c114059200d000002040340b10840c451808000c0d240411107180010030000700000c1008003800c106005039a2800020101d209280e04a04001d40000410040350040c200070310030340d000c4c40c9a2004494035440121400c1c06441d00060040811500500140c940800b030030781d010780018100c40101485a8010701a0782050f0710501510344680941c0b4880404500d00704441d1f80440da03000c2d030350134035510020741c1c5d8040500441d0048000044008009400b03204003800a03151034219030402e170b40e03898102c424132124401640ca4501d44030120f01c02c000c00c50100e40840310201c0c400b5090410f5641000340300c19 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 125173750 1250 125172500 125172511
    0x312090a030c080304060201150e041707081305130e150c0705030706060f1a0304030f0e0d14010f02030603030708090a0f030b0402090f16120e030c07060327020405 72
    0x20010300000300040d000341d0340780003408005028580f00d9217090406800d544000074800d10300d00c0c2e040b50a100002240300c001d40d00035000f034204154880c1c6122244602d03c900d070405003054000280800e0242c1d0804804c170121141600c1c0c22205d00c51403030301c04040368846145010160041c011850550b1110026150005510305c0510b01e000d410740c0d80c0034510383c0300309000c07501b9035244c000402030b09001c0c3c04607600a099a031900c030a4201d2341191307600548002800107007400f051110101581e48503024008070b81c4000b40000e80103410700d040034100c0b01100b6048102d65070a03c403824405e08100d0003920f00030140a0015824004a0b030b0743c4800580040742c240c1d4000e100030800088907800d02040702c00035401005620611f040900520000041c0180f00a0340c42c0c0d5000d0a124a10540b0b001000c0314150070315110501d1035450200c1000342441f404c2e0604c8510000c21440c88956010450300e04039052a02e0400c2a1031480c56200c81a03030416003d4142d568030f01d8007407005802c03d038120b01d5008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 125175000 1250 125173750 125173759
    0x91f0f0804080d0509061006050f0702090a1b0207051f0906050c0a050601090e0c04051b0d0605131506080402090c03070512010314011a0d06090302070801050406090204060b0702031209 81
    0xf00e0005941c1c0403502c00712003407a415800701c0305001d61135003000d18502c054030080ca050380c600704501c2074000c11480b4141000b400364007040700003101c4117025403101047da0034450031140551900e0000940c0c800d070a00503cae110f00b069048a04800c60b02d030305400003c0c4d07529203541006510300b00301270318070b0780140e841039649009010280001410a018150281c40d81c2c0800040780103503c400ca6103003020891009000303910304018800401d07000001420458401142146c0d07d1091a181c00702400f42988100e400403051500c0b030303111480b9078210711503c074003001007168001c0c0d907640c3c00c94105105540294001e0042c0700400c410a0f04a0300555005503281410352a1017030382c5030701c0305d18007009a20941313905100580d207510440c020f0044203c401c107403c4940615184800015910000044000b0130480c0c0d240b000c07404241c001e101c41001821090b00800c62490141440b00180c104888124400c5240c0fa074042a48801c0e10103962909401500411040b00d145c0f06201c1107074080c0d031406910 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 125176250 1250 125175000 125175007
    0x723010e18090a212001091502180603070e130914070611030f0409271a0f0c3106090e060102030c030d020a0903080c0102091f0f080408 60
    0x9420359040e00e401203682d0001420f9803501e5003080d0201d821042d0b540d4010380b1103803022054156101c05030341108007684004840543c21052483d00418000300018a1000344250110400031035501605c411010130b050f00060700c4001c0d04112603031201710b40510100300c0c15114401c0604018900d02c400d604042c0000440f20b626480b030140414445104401550100b1418016107910000280100d65114015810464969001400d40c0154001c4043c0140e580c2c1b261041c00c14800700496020700b000311110211400c03401d0007041c0340c0500510b030952281d40008542104a0404824469805003000a04040103400c030102c140900c0c0e0200c0356130500c41240851110341d2207441000400881d00c0c4c14202619160101c130313880c80000e100c80e05540052080b41040354012080f214409442000160f840303103010410354080345d0311741011300240070218104855000550051940c9842281c060780303100c40d529408400300c0c2013100c410001584007031070b40850700d0042e034102e50040d10840e0710500303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 125177500 1250 125176250 125176279
    0x103060f03060b010e010207080c0105090301090b0f0405010b01080c0315030703021e090f0112080d06080105010f06030509010b060409021315020a140a0201050a051c0f0204080723010e 81
    0x65005035001690010364481d040342240d03030090200c0c9a00042800230f06051840c0c1500301c2e40b21f510000005061100002d0b5500d6103550a50bc560350003980b16810300c55600307001c1c14184130084112421074480d860601100c0d11076010b42040d07481810360001c400e1440ea20340708403020086410066542500c250240800165a51060040e10824841c40c1c42e100b40000c1c1c0400c00142d601400b01c9203902d5441c001408102c090345002e01c00c1d10b41080405076505d014208000040645621080455182c0400410140d8001118008980c401da500b444261a554012800c03107038240304859214904002c00c00110406402a00030706100c0040c0c982c4041d0384009118107900703d2003d540050304030400120030004402d000d400320101480041000403071647c0081c0041c4190030f070034030910001113140305519240c403100c0400d04020308002d0242017000c1046001039007243c06290030074010301c4000318411414402030014103404ca18205640c0d03824100645903001d50f0b4500035080110410b4401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 125178750 1250 125177500 125177519
    0x80d0e01051603030b130908040306020c030408072903150f01230301090e0d0206060d0f0206070b0702070b0901020c0d0c03020d05030903070501030b01021c05040801090c080c040905030315010306 86
    0x1180c80c3c041d44000c2a0700c00e02100300f100e01c42540800000052804191502161071039098900340d0ba44500010381c1c0703540b0b05808600d10f02075540801c1041c400c10700e0210740d01d100040e421000e0318070340703201500d051090b0b45038601c1400b08544030030ba1034121010118903440c00344098220000d06041c0102c410a58a0a940303800000c0c4610415070301c00000100722020b401c2c400c981070080902c000d40100c0312000c500075194180501103a01c03032894044c00c0030502205d03002d0384140c15801449170f950b54101e40b40c0000898030880302c00000d4050b1070300c0041d4a1034404111040410168082c0400708008020000b489032842003d99810545c01804001030716004454151140520025500c8880c841c0c101450603a40d038110f90304240c1011600c20300ba9800140b01c4551030802c80018803822542c2100326101c0c061a0b100100700d43c00d180c01e640900103251200000c1d9008482030f124210b14100c00d10040d10303451342000780907030700400c0040c80d0704400c407120b80340c0041c0c140340c042200341d521402c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125179856 1106 125178750 125178787
    0xa050306120307021e040b060c0a030e010e010906141201030c031b0b0403021002010e030a09030218010b0a050307050409060609050108060d020f040e1f050f10080d0e0105 75
    0x40c8015a19600006541100a00096200c10705000300e240cad143d80d200300640119a0703800602069521402c01c41c149600d060b165607112916054048440d1010380c03a0078035030450188000380070b03070780212800ba000318080d4420790109415130034140700303800c00800c0c0080184030380781c0704110003c803040c00c0e602201d4040328070050104808a050f4054102c0c0c101d01340160100203546402c40c2e0f041500002500c2c002d4824200e54039400c8034103089000203004000c3e80400510400003c0e41c411001103911010301d16025050582d2041030b88165040380e00004040345d07a102003405217590000c44903610a01c111560a07240104e0780107d00c017522644210750041d030711455400031442e410400c03400d0b0880007050324444200b00c40c810328020007040d284029180d004001007000c0c080040c0000d800d98905902400c00d07040e00800903500000701c0f002c03160522400b848000740055100030710 = true := by decide +kernel

theorem cover : BRFrame.Cov 125000000 125179856 := by
  have h0 := BRFrame.cov_init 125000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125000000 ≤ n) (h2 : n < 125179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
