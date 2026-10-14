-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0640
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:52:04.478978+00:00
-- url     : https://prove2.me/submissions/a29fc289-25f7-457f-91dd-e29b4dbeedcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114928057 ≤ n < 115107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114929307 1250 114928057 114928069
    0x2190c0b0a0506030a1205030709090b0f0d080415050304021c0b0105090603031b061006020a0503070206070c0b070b060a06020706021c05040e10030203010f05041a07021002070c03060e03030103050d030506 90
    0x764440c5425828608906d0f0040160300191803070700201e444101c02048040081c083e0820554020b003a40b10781c483c8910401806104c2c05a042d140306004010100d00502c003100d201c0781106094a800380d403810f2a1040c0144c1464040c0d8690742c0d00b5240010200082650300344e141121011214080c15440e001d001038158441d42014903051182800c10941403800440d999102c2c545074240c81584581d10300e4141e84420801c1d000a00941041201c940180b40c0703040600030ba43d01512503080101e444104500180c0c0c445142500c1c02c40c1c00208000c4145404080440500000d1028045035071401c0c2c0007954940da000008078510024048180523284517000359401070050300d40810342030074403448580b03000300a808140c3c080e50070040c1c0d89450600502549000340d602c40c0c0389409454518405034031036200a08150214010700e61844180741e078500280000c58010030808041c039246103070010848602d000d1818498000744010030200c0c4000c200c2d005c005040d42004540c80d503946c800120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114930557 1250 114929307 114929323
    0xb06150a11030d1406030607030e03040909030302040b04080307060e1b01030209031005010b04030303060b0f03010b0d09060606120605091312020f0d030507080f09030405040216060e0102190c0b0a050603 89
    0x940c5181040f9444840001d080040c01185c040d02038441c182ca030020110141c0d049992120000d41c0f08100c20404d0500913808099018040e01d00142443d44800014016512139481122103900104092080c045107102d9112180c0018008004907018805c0f00381d15403003035200340760501d9070100720a907180c0c4050003d603040c115078150400c002e41e102d100c1e04000d500240800d500007807401b4000314103025040126100180b1404045007540c2c0f0f0214003006583c814a50840816254078002c00051154000c08000d04401e459540f10a6405079148041761030030f6000030f205540e41c0d01807104901c2c209540c03420158011501ca20b800c01080d2090380741003200ca101e00140c0c8902d032480b450386c0d40c1c56401140121019035481100c2e880e89400344100703107030076503103807000340c104000401080c81d0690040074118030f0820900c4001c170594076040c040307400300340168078283d400060f00704500d039141030140600a410305040480d8038203600e444181c1703500140031311010b541d60360104050355000c2050326 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114931807 1250 114930557 114930577
    0x1b011e17010b0403031107060c0f02040e1204090b09010e0705070203341d060918010f0e0d0203070c14010918091101020f06041b080a0c030b06150a1103 67
    0x142950b9540090a0680d20601c4207500041c2d00042d001c1200b0307401304010007220306c0ca41d1340490500f80c030344440e05a0301004a04980c09030303132007a644441c0c030018004030140070800901c5c0c035212460940d600040d2110000707c0d51244001600601c508900543e62540201907031805649655070361010914081110901034000d500d80040149403c140c0c2c604541c090004540c0311030440d682d4002c81d0140700c20705042403402c0b504400050b0003400c20700559544180340705060201d080c080c07199030382120415024512181e8564040300d100700f03410030580111542074801589841141c0e11201401c80381030082c81010f0841c050312810036131240700c072a0043e2215845604060124100038030007010000412031703600d01c41c030023605555800810050580790014001d807070a603850340d0b1161210b5050002c07111a102200a02248106080000380f403007601c80c0c00502ca41504501308414400c034028822441052008880c10345031000b003003036030303820aa5170800390000340d2000c02e500e0540c00360400355 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114933057 1250 114931807 114931847
    0xb0d0905010b0d050303060103110408030714010f0e06090607090515090303040306050a0f0b040509030f070c0305061f0801060506040303050a0327020405240904030c02100503091b011e 81
    0x43c280b240c0880218000e10090b2010400500506501c0c260341c0110302c40d41c501500103200142c0814503071559511140e0b8076000029841c400c107000d42c821191400d075800542e40c405810040d000d1410820b2541005680c00c10504140c6040c0009145034043c0524008190010030149141d8404000351713800b4507404413081c0400c1c43c2c03582c10301c0c0041440702c2071000c1c1a03003001001c02d4142003501c5802c0c020f90007440913500c0c1c40e01200c29104075912000080391a281d07007080000100d182840098000d00b4000070025201281c001201c0c2700c0b103a15002515180d15040c0c04000c665141c4088600700caa0504090340c56101a4000f5801400d2580184050664072440304405c410801040745419208403010040d9845044c1403140e0101c21421021b281c0340040340c0c10310140b030040c401c1540940709103801c0d406407a040e804101c401c18194081c1c004200040140030301c40a05011411400b010b80c4c60086c6082c0012000030031100020f803c3c90540744010414160f400d100e003948140040000c01e80c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114934307 1250 114933057 114933079
    0x20105060415150c080412051c08011403030409020d1b02010e032b0606030e0f060f01030b1b121b03060109060e0a080304031104270b060f100c110303040b0d0905010b 73
    0x1844000d04444c031f82210749005903006d103e030340440d42c2010302c128411542d80d20340aa00749a03e03145124083c801c1d01e9450710040c000042c880c51340c1c2c00108001c014140c800310708030f11080d0000b0307154242c085001d029a41005603a001004001080e500043c0800c000351103140c59030f10317000c9a0742448104070007025081900100700d60750103422240e140c10307000d811070711101101d41a49480720700541e98001624040030040010401d05000303141c016081101c0440c12a20407100d50060340e11600009040d2030395007040003440784954011111100c000807d107442c5290510000b04001d0007400750340b0070710103e540d0100031038880d0310f5132001504c1108200c0b5a07a035100d003005a40c11207400690f0384581d0421401c3c4a00c2036072002c00046500c0203550141c4010910b540707103e0102c1e80140010f800441e000f0401000f680d510361403171604515a10740720594200c1d420009000c1c0d44000d050782c040c0c0d00402007000311920700710480f4608503124a0014240c2401d00d003607800340c042040702960014449003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114935557 1250 114934307 114934319
    0x80a0302071e050105040b130e280b01020604020915120105010f1707060509030a02040212070915120b0f040207030914031f0b181501020105060415150c0804 69
    0x20000161440070720452008800c0080c4070402c00744600615000a0091104000350100600a00101c1c081151205002601ca40c1082e080410031901c00501500b0042030030300d0340b401060720003072800d030300c510030b2100c10115400030303680b001c1c0900000c0c094801c00001599401d495040c2c0c0124440c0244444181901c90030300300d000c1c100a02807203504a4251000181564090703801000d84010400500a080c3c500745c030555103904484203103509070050f1043c00c001659184001c1015201c06172105020b800c00b1200180444e00a0300039010340d080203071003048415040741d480900d0001904c000f044c2071540b040031680951040e249942c01500106072081090741208a41c3c054500da049d01c9107200746001d0400d40d031a0f4040700c42611882283e1070080005205401c0005170030000303400385d80740102008081c50300800c100c500d90340e03c1405000041056a080c0900e0350416422541804000000c07980c460900c1402c2c0f041940d4211405210010350f406012508405504645019181d82c0c0d184 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114936807 1250 114935557 114935563
    0x1103040219080106060e0f09040f02060c010f020f0c19081e0d020304060b030d0207031505070c050a0606053604030210060821030702060c030a06050a0b090f0a060c0809010306080a0302 81
    0x410a1f031203400d80d0407120040d030078141e268a00c0740390410501d050281160b020b2240715880b42204200f15520b5180300c8004064900040c45643c00c00000346a850100409603803c00e884055050b04540340c200c170400100d000c450175602c12005140c0603001c404451141d00e8918441c0b48588200d59002008200c2400720a03405607404400640580c0d2152400e0603041340c0300c51342e5000051940a21000840e400e01c181c1d4065a40030089041801c00d10b10f154807114900424803108454003a00d8260038095402c00070b03030006624450b0414602e00d0f0343c1e800040300e0f0551041c042021804541000103051610810001081120700d201c10824140c40d10a141c1c0c840403407124040c1101844900300c28003503034880850380f094207642e000e095184c07101002c3c005143e00141c00804015140c000c00700fa80e80d0758101d02c000030a12070711040e64031042102072040b03007001a0001c9124017002a0704000b444c0d00800d40050490380b0032001d56440b09480700580007001c180d0414421442012030703007002c0507000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114938057 1250 114936807 114936827
    0x121020a03060b090c0a080705071a0a150803090a09050a02070b040606051e1c170a02010204090e0304030f1e08030a0902090c040f0b0310240f0201110304021908010606 74
    0x10b41d80420a03980301d40b07a600146c4079100221002a0602000850301440783c8041d01c6000d00c203d00c00440c00b5111851010103e0094600c2d00200b81d64255010099a503e510035006040d400051820312441a00041c01c0d803450348a600c6801d82c82c6c20029560030700c50b40c100e841c00c55101c08070f50b516003071a040050003006a401458040c0d0700141c4000358820440303060b0381640c0c0c0b0003480c1c10541e10001d506400c0310155540121582002005a601185680302c003415070410254001a200d9142807003c1c0d0a0b00e200d8051032600d500100401d0000c40d8070f500e08083d0381508041310180418491130426203500940300041d00c500d001100744030614509803c980d0001c2d001f101c1103030540c2c940386d001c005144a203204014281c00204010014001d0110185611102c1d511301e400c0f010341e9410700c0165000000d0801c134581c3ca82c6c070b0101c00c04c0581101d615880b04001c2d20080000c04c01404c0590070502c000346c0064401d0440c4003c0d800b00b850100741c040d0203804801c00900c4142d60700e1034003510322544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114939307 1250 114938057 114938059
    0x60e07050714010b130902010c02100e011b351b01140105060a0f02031303060902090907080303060120070b030709050d0b01030201030c122a0e090121020a03060b 71
    0x114000803002d803030500450062000080c64031010424080302c4100500c1c2d460001c0341405030749660f00c0c0c05a079a41c125094610b105072500480c10710b5540c001402d003411445004100307207004122002040b5a0f9841c900000b02400c00b1182508458401c1034543c0076107d21a005034400107030000c2c008070450b03044a05d4400f250001c4c0641a4481000f884159090090a030440700520220792002c0c4a40500010440c00d401540d20701005814040e0703002e0016041901c0c1c140d12461050214200000516400b1400f41c0140101c0e83c2000c81b41a00da101c0035000b41e04118490000c0100300c034200c2031490495415104840347e03a42c1c0c92084050f40d400c100d80c00004a9101d400000d10ba040c04040c44020036881507034140315070b084d680150002c1181c1e080080c200040c01240441105851040400704040724074080d402000ea030400140c40c01000ca13003001048990b0003e46403503100c1c2c07005681502e03560b680543d0f0704a203400c95401c07040800d4801960041c3c5108001090000e568020454440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114940557 1250 114939307 114939323
    0x50a0c0603091101050a0905040908280f0311041509080105070504051f0309050f06090d0923010311040905010503280f0f020909060604060905070c0201080a060e070507 74
    0x5600c0400350304a8600c9100a0f00d1200745001071285076116400800705e20109052043c4299242e40115046800440088411540000b0341030801c00802d001040b012007001c1200d80c81c0bd000e80340040c0240c41a01c011811300d5143d807018a8050340760000c3e9405003004d0703c3c3c098101c00c00507000a16103c864814a22254a4080400d4100384203100b00c806944018003c0040200c04c600061002c09141c5515001c06581e24400400100180018500915103000400b81401c01a2055007082a1500d5100501015a9041010f412601c1e016107190504043c00e8035072042c25401a000340c2440e01e000e100340e0744005400318518802e58001416240207a045075601c007003504840c81f03e0803000d6410700706a05d28042000018106203d0444640e118440401e00303103085501190703c0b8001951030001d0380d049101000702505240c0319190051415040501180c00c021034040c105050751080a0b0400c0125800989a01096041907000b4280041c214981c1d15104400070300d40d8211800490b8224 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114941807 1250 114940557 114940559
    0x21002031e09220906090f0b06090f010308090d05030a021e03030405061305010b090a05040b09010c050d09110306010e160806091302040e060a050901270201030e0a0c03050a0c 77
    0x1240600c15110741e0700003d808007504403003520070440f00c1400328400d950003903203c482c2100024030a000715070240340f00c0c1401d84507900492505e681c12000041c00d150248017030004210044060301e041d04d04603500580520b80e500301d1900817448a400000d4003401034840000c00701030303403580000c0e40426041c0e4485442114203001807130680780c0c842646d01030701d00e511040c0810042e958020340c04006903c503000001e0001308840100d90445400c48030801855074131400c00c803d004002d2822540a042800204074086101002130101c0c09030020718414140e07104881d60401101001841078002c0007000c543e44d540e92642e06020b44c0d6422a1070300c44111100d0b950030003030f82c00351101501841c0004e1094156a8078104944080c0d01043d1003a81e00c180c40703072074000c0b00500c180f00040c085c10214502240d03d18240000a00396640d500003071548100c0481c10501c02d421840d0100350140c0d0910740841c0555039240c1151903e5038040c4040c0014509090000400100043c8039111a20600b9040b03201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114943057 1250 114941807 114941857
    0x304032a0e010f080604210210060603021306030209090a1d0106080102030a150602062a030f041202030a0806060f0715090b180a02220e0f0708240a060302100203 71
    0xd51800d4400074000c0c04442c3c00c20881c11f084c4a20460381c09810701c11985c40150024409056806d254014000710340e00003400c40c2d503d801c04000340d01600d0642800e62600c0a603130f01140000342c0041c8080d00142d85d44403c18582540c03442074244440f2140c000340156601d0f41c00e8a03001b54000d5522010307041c0b4045102c00e803610603107522021500711380c01420311942c0b030641000c441c07460946440203a0810080e603110381d1a810016600901c0842458011842c003840c101c040540c612068034159402482185049030f071001741d49034046015250b0301e4a482258601171721500034000c0c0103005850811000c02c9000f91a40701d050f02500525101200d5281c80403003400340504040402026000b2071446000b50610008540b02052019001040c00c1103d1a601040742c00c0000200da0359004442d00c01c6042e9420407459001c0c140c15006440d0190401420b0441040800b401240c0819850000380c039455181e8000c6c4015500a4010b042910702500f0003900c0c1c1d402869142040301d600b030154420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114944307 1250 114943057 114943063
    0x2040e011406072004180320030a0e0d0b0108030d111207080907091a0415060e1c0f030c020310050106021002090d05030c0a0b01170304032a0e010f08 66
    0x900840581003a183c240daa803a01403000c01c00c00711101c1c000d9203440c0034a9094a45100c3c10714421000c1e102050171100c3d43c50010041e143c034046d2404503401041c40d130404981d020040b035210841c241001d44001d08040003249000418410141100c248803000080c28080440203000b220382040007002106e0708500900b20500644401e000d4030450071000a00c0305008540703041d0042c131800200c1d8000c035510362280341500d0401c07030100301c8000518000d644905240c012444010328800891200360308004d001030083c000034952a07c03502805070400070155507401907080664200c03600843c40401400c01070981404000d080b8003910070b4098505880030b139446007a040c0c5031607502400091207907400003c041e400149196a0080300c003620703500040c60400c020819440c000c0c002c0c1c0510b90943c02c0142145105078800c200110611004c4d04031400d01001311025a507111100c0d00581c140740245503072529020080708224502e204000c90046e0760101200d0403500500a250151602c9910312a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114945557 1250 114944307 114944339
    0x20a080730020d05070306081005010503060f041502040b0a0e030115030303051803030a0506030114040803010b0706061e030c05030109080708070203150a0203060405010501090e041502130303020102040e01 90
    0x8100c0320304140c10401001040c0c8600701d900d001c0005030401c00c00620f100d0031100c0598030300001c40e83d02c0301c0c00c200d9605c0500c0f501000d080140d80c20000366152001107500c0390320061610201c001880700107420800b181914440150149030119260798442d071081d512a80110a00e0b0042038448206888618050058600d105403176070042d50010700d150340a50240c480980301c0040c036103800c00c4038580349500f00091449494000380114850401c14241402c4a400c10701e00316041e0309900400010614890843c1e04440126803000e542d4429806c20500906803500014114a80201030030703440d00800e07000f602564011155020304030760380d60406088450610000303292000034425100400c10f04005402c070301d40094181c41c140c038180d0342d01d40c4003140201c0d4141c0560381d012003031255600f807502c00d482c0034000a080c008089820b01d201074004420081004100d210b031462801c810401076010748460b282d003000ea15143c03688a10300030b03000c0c0d00113000354200624507030000240d07a050320b85441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114946807 1250 114945557 114945587
    0x103020f0402251401020c0321010506160c090c1709010b0f15070618050f0307082a070b0d0e03040b1e091309021206070905100207030b0a020a0807 65
    0x1094414103024141003903c1400801e85407401070301c01c8981243d0080c0010112407242501465441d010016005420401c1668110030001460010b104036103c01c5d01b02e45a400102c1140c00741c074041c1d840c1c43c81218181e500450903071400c2a82da50005a0410110b95a40e100c504520241c0e41e6540899400c1341c160401081e809090b141d101d040505041c00c292803020030701002a031421a01d41c83c2c100a5031000100d04241c495000781d020184041440b00443c1e51a03400301961030860107840707242160003184c80107541007c03110040c0310646401c1c40c3c60001a100e44d42030b0350b0016545c3c00054090b8200d42a89002113051580060003000c001c4122020b49201c2512181421002c52007401041c48040c443d0420b50400c12042c00145c0d030315001c0d0801c81e0169140410000b1061061180c082242c3d4546112688030600340060150071000102c02c2d208159032804446a51130307000c03450410242d0010b00040000800d0180c40412500103048000c241d0b01c68603903648901c98102c4148d25015040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114948057 1250 114946807 114946837
    0x20a030b0f0f0906060702010c05030c06010303170105010c11041e0203060a0f0b0703050c150c0a14071a190e030a020d02030c030d0b04020f0a090e150906060c0a05150103020f0402 79
    0x41c04c54540704002e03000c018010301d045090f201c600e5480300d15550052041140b03652122004204150f80700420f2078452004205001d0b040d45080000781c94040745c80c02c010040c510512595a0a8540c0d0780041e584000728103a600562540401d0500254000d8a00b076002c0e51503600081464400e044180d030407a800701050310700e025450b4070101d03616084466a00101d005c0c01c4009002c0ca81d03001d148600420712541d816940307415045024048482c400a218044082070104d6030229668a49082e003124002100356035584d140240402d00b0100e180800c050301d483c2c6000e5044000740080036107158500d80d005c541040c0c01c8c03003400780c1c0d40c5e00450460001e10f42c0b04120780038210032141c021041110010f84090300b411699401c400c0a07411510b05100019941c550411190f0002c1039901d40082610261186100190012032102d00004100038003900d800964400001c104111581c483c0f44c1000c00d17140c8a14402c0d150309c0804e0380a10050f4032610100f842e0f103031245002d10803039110950880507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114949307 1250 114948057 114948061
    0xc050301051c02150d0f06080c1e03030703030605041409031603020a02060a0f0207050109080a080708090d0f03030608011503021e090c041707060c02060319020a030b0f0f09 76
    0x410407140c5403481e210044241e11001440162a6031407098105813580c08500d843e04135024040c4c044520390700040b20f030141090000c00040d0008200d00e134500c107003a20201d8803141d28039641e41c02d25100d284240d0b0540310004908040c10761650040d41940e0045400388241c510a4102e800d410743c1c00e03154025250000c01900382440801030101d820244203005480b000082c64000510580092640d0030101d038800c40c031120354030390600408003d03040900b01680114200411a607a56040c203078020201100000c6e4031007409050816030309a0310300100551188582c0307241035080d035501008110003190414902280c0080180200b007014450800c064400c986580c00b040100740380d074601c10228801d087c020700ca41da15518081449101c0d001c10312a501c524045071402d00e01c04800340d00d4110f8122280500140344d010700181103154045130010340765143d108007001000c650084040c03c45200003002252030f901034000054100c0201c0d808003000c140241400780c40f91680c04640d501610100c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114950557 1250 114949307 114949309
    0xf0d02010e060711040207060f05070804080a032333010c02090a09210e0a0812091309030201051b19140f13031101020307080a0302030411030a0c0603050105040c05030105 75
    0xb024080f42c0b400781071004c01c0d00c444100458105d90010600740c80c80c5450b8001c058046140b0700505d60030012615040d495844c264640080600950001500301a100c002190f050240d10000c120240c22101010035181819407080d145600744110501001c03d1034940202c0f02d00381098a000c034103006844140601c00030760301f04100b000000308040c060750b655045000204d0300900c041d020700392900c031025070100b0010401421840c81040d0040c80380d100408103010440010603401440c220410310306842c0c511a0000031751445000305034a4001e403812009100741a81500711601800300c403100a40100c048010740b0006200c0c8603984801200c0c20740c80c1c111030622030901c0041005260350041d0901a108580314071562000f6131091814900311000c2c800c1c48074142d00700a034082c00f40000c52400e0b00c5503881c0402c41c0070305100c0005041d80400020180030001d0402c40c085100141540d61460007440c104c1c07030441180c080c02001a140c4000440c041c1098820105034861a03214030313041d44e207400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114951807 1250 114950557 114950569
    0xe0c09040902041814012f030414030705030a09050409020f0907260105030f0307030909090c15030507030e0d09090209040b0a030b09060a0903080117120a020c0f0d02010e 75
    0x35012a0019903409215000c844020a00701e0703901d124503a00700e20300ca091700d5040d0030340380701682a14400c2d002c070f481e51404c1349142051502c01f0103114004c1d91280e849082242c0c078400660200050b9002c0001c0700380c00c00c0340100013040c0d00032664850014058940341440308070340c40d618000b50812080b4011102a150080c646c07079015806185c030100324900c43c044500080c601d0604040c41c007a4032001805a03103028003450482c1c01489c0c0003035081c2480754070010041038152060070056603a44680c1130a100d02031808102602c1040200f40708000d5800d402030003810100e03000e000192401e800090480004105c960400005a640c50011401c064154000398450481075500c20341c2c0720203034003998443d05c100744000d6003c0c507102c42c4280f40c8564803900f005001003400c50214580348c003590011b60011003c80c15650080071101050803415040d45ca0b0000c448d501c0207200300d0105012040c40c2d800680c00c4108541a40c0351096900366078148174142a01e92402400f040000c44c03840301e141440303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114953057 1250 114951807 114951821
    0xb0402010518060c030703030605030102030411150702040516031a01120b061c06080709050405032b0608010b030706080c1801020a1202070501111606110a05011d06010e0c0904 77
    0x3403420400c001d2910005101c03540940c4d00c89016401c042000010300d074162003802e008100aa000b50318614040c1c0d166181c10344001c6503644600d0301c0c0b03010913010061a0058408081e8054020091400c02d88103441140320450443c0700041c0c10300344445903141c50700494525902041c0c40301a0280364800c0380802070b00f000900d040d0845402d01011071406d24101c0020036002c40701d07a000442c0c90400600c14203004e21a004100c4060038901404001100001111941d031860707a108100300d013a40314901502500d40541c650140c3c20f02c2c0d4045403260f810340c0010300040c01141190185951408155003002080329502c00c1d0b0501401901d4015003900801410b02e0300520580315003c1d1030359260580221904910401a4001ca40500540d40c0200c1c5802242a0f450024840e40100c0c8603c81c1001e002c901175182081018204907114002c20011402401d41c032100078455041c4d905100e01e4017001840b02d00070148104000021740741415090f0b10301403000c80310322514100c66502400050402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114954307 1250 114953057 114953077
    0x50a0b060423010806070206090706050304060f020c0c040b1207051002070806070e0102070f0b07031d06040b09100c0c0311151b0d050910030f1116060e01090b04020105 74
    0xd542800300005503216032003600ca0140b0403001d80550600740c440386010310040540081d940032005102c3c242800164000c102c551038582240c1c0c913540c0c0d26014002d041580f10100840d8008100501c5105011030344c0c10054a0940d000c00c82d2000c0201000710710500d8a10295042c2c10494040c44203061241002088184500440c1c080d0343d41d44a095140150499540300002d102e950500400c2da41842044004c00c9008030342c002e26030424003040118071860b000141807007400c03850000b0701c1a1021150446400040c0070585031541c2e4000d030351860784054138051181d4000040009014040d01044a4507a000311207400800d0465442c07100c074150102a4640c030041c820310202080042c4c600a000511815504412098001180515194002c500c003411b100c800c2c0080031060311880201c2c0b41100c030324600800c6100740d07240300c000103140040034407100e001d001440d2403510700042e070280c0c04c00d44500070421107484420308003400c036492244010300484a000c0850090347c410000340c040300344 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114955557 1250 114954307 114954311
    0x4020d0902090f01030515010b0f0307031d070305070b1315050c1c0216060e040c1202160212031c0209030c031b03120301050303070602210a090b13050a0b0604 70
    0x191503000590400c50445000403c004100700610411000703202c96040781d0107100749a807455040000d12110713801400c50840503084040001060b0301c0c443e8101b88910241700d840d104200141404040d1600c41a00096a99120305440096540183c1080f5a050f003c00701401c48400d06040c040901190302d4140c10701013100910106810860074040c0e102d1209c1c0007901681b804182034400b07401d060242da0031045000303840b40100140380c1c00400345501583d08480024403820b04400c03c0c0c0303043c004001445c50340b610118040300b08807501c0c010805454021100001c891900d0210f440d540e01c100b0f583c0110502151100c2408100e49401074005001c000701501c01080f0003001103882c158203042180084110307019032903e40d080c280100060140c1004d1341c01e156604000111741da80c45002e0006000b998005000c82c015131040000ca2060180ca03100210389040c1204c1180c003408070a041039405440101c041050114240b8907007841c0c0d940003010308103112543d210075190490040c660b60b0895 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114956807 1250 114955557 114955571
    0x103020f0d020f090108011d0406051909120e1c0807020a08010e011d0703030215070908061005130b090a0f0e07031a0f0105060409020a021e0a02010f020d0e04020d 72
    0x1c407080c0040c0c85080c2480202a84828520000508140043c2d0001000445034003125840715980c03243c1c10360058001c04045201e40340e1822200b22908801e84034680b03d440c1c0b50f0b45204022a00703068600c02c021070307666045030740b1301c0c0810026102c00d00300107030f81c00501120401000481b088050003081e40018603001c44c150392883c2007800e58031142106441070b5036900d20002403d00a5074a000d940041200415005080d96401381d500c660808c420302003001c401c00010120b0f8030074100c035000703485040140c40041c2010140c81e118041b01e4041d0701d1081e0700320a900c03c2d03a550588224080503000800003005a201c1d8400c0600500803d2041000c60f034641e0800b10700d42c802000031000941c4102c2c0c0901298280c41c4000d1360b40c079030182090b805480007500410440c0d8401d401e0703a09480c43d5500c0142d8034404040140d140c1041c0c5080e001d110904000f0a8150405c0890b600b00d40c28002c0c1c80d03500da2070305c545900300d8485541c9860100462404d0b10495124140b5a0140c402c441c1c0b00d0308001400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114958057 1250 114956807 114956827
    0x30406110304030f05030c070b1e0c012a020f01050708060d0201020c030d05040315050601080106050f0c0109081b011401060f0c0b01090504120206010b0928030311010e06090c0103020f 81
    0x813404404199850f52000800c0741e12103400300452801040104007460603c0307515440c0d8034040003080e40022844c200840c00044c181c0082d440108100318800083d001a03e10300b0381d00c0c040014000c140320150240411041c40b0000600070a0b110b20700d04d58954960b43d81ea8010000c80c103005203400d17411445518280c1045850402050f4010600d0341c459544070781c41c0d403500500c00288030b54109500b508040138032400380d0f00100c10505407122410459118500e03078801079410b0217200d40c0500030b5803c1943c440b042c010103100070300001207035000f400031606219104a007039441c1601d01e03031400e4103900010801d01c0e00c00e291403d801082490b041c00105025200d010b81d5110030f030820b030041d0740d0390402e1104000030007607203c442034420f00192159600d80244205036000b40084035019a02d03000b90401d4000c48011155080210b0784820345d2800d07100d04000780074800740500845198a490741625440700c000800a03c01c110328401032038414030003001100a5006203d40e03140d0200103000c900e0320 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114959307 1250 114958057 114958073
    0x30c0706080604060603090f0221030a05030708070e030705010807030e1b0a0f060210020912100c030e1203010510020c060c0a05071505181201090302060901140903040611030403 78
    0xc20166607160303030600b00802008101ca030700da8481d0b01030502d48418a0005060048254842d940441d40c007101d240400e01c0300280c0705120100b02056000001d240402035411001460141039241c1d42c605d8a5a5081c2050345c6007109200e90542c03540c0071400800096224042d5580c2c4913002d0b15021602c001c0b69014140741c0803031101c1041504468034500807540c24286440c0b4010103040788030241561a000c0040d40399a1180340c80b038400c1c0d07000260790040b038440d09407c04600400c1c40454040182d20844000186180c4099000113814182299020400005c1c6080d1007403410804c9480c591030801040341c01c000402d400303c198065001c010700035070b94480203001181d45403c05801054140d1034a0b82c14424950480c01c400c501114202c02c0c0e00d60301c4000d460b801d4100311555419107400c180000c8404000300c6006002d582405c4170030003056400314089010b82c2c8042c00030301000d69455906a820602102c00c0d00c0b0940c4148820006148503038a41044170000c075054131300e060740702d0702c42d045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114960557 1250 114959307 114959309
    0x11220061206330304060204030c030302060604060b191d041e0f110a0c0501090606060306080106050a03020303071e08070b1e0c0d0b0a0512070302030714130905030c07 74
    0x180400401c0c0402c44030303003030071400c40b98451000e400c03000710202c6a03544044401c4840700300303041c0098003100040130028140e0449018541140440391405d03603d280080d500e10341101c100c0e005070f0400c00b00080c00c2c030025059411122441052144410b5030043c120360920440d65100c0c145110740c45000750640343c034811142240c0980c02e80030b12141e500c020381016104403440d03002c901c41c40e00c0e10780f040310710260058607404807a031b280c00245c0c0290343c1020383c05007481400240c0054035065002846c540c03d54040c100f1610050b000788006035030f5904100760020b4a110194041c1c0003008100e002500c50540200d500d16540281e44042490752200c0519400c0641c003100c441004405026030902400c030882c50400c03221419682601c0e004208658070700480710381a28450300d07080001c2c035554500c1c0b58079010706000b81c00e510b1031051652900341c0e071b04800d2005900034010004046031124194221504518000d003500c2d0014506450080c000c000c0064140d070140000c2c015206030f5102805800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114961807 1250 114960557 114960577
    0x30b0d150209030f060105010807080408070c0f18060503031803070905130308060d1a07020c0d080405101b0f0c0506030a0e01050106020712080c0f070605030412030501122006 77
    0x58807000b40e502807500c0c004402d190200a58044c4004200da07a81c0700c8596644520203180c242d001345ca60b46805109030082a0006000604112021591651403030040c0c007200c442103111018982c0300c85a007002c43e07540d40146501030304200615421858550018a507040c006000c861481e44d40392500401c80360f05031030640c480d540310400c2c5000e25900c21005170b00401c040390700960000203541c40c0e5440504911192841100d48400035042d01d00900c207044014030080c0140712800b0461405040e2603100717000c0c20344142155007190209a01ca0040301203048010031000c0c425017040d80b12032040d0001380a04072203001c3c4500300480c4a48908014600840e25000b01059000701100705a09548050300404115400034904010807070152000c4840c072904074440d140d880341655140c5003021416102030a0a100d619800112507500c0001184218000d030600105950b2010048007514403c0c45030030130742c2c2d000c6019800440e0780a81880c2902c243c04101d0700c5100450b001052843d00300d80c07050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114963057 1250 114961807 114961811
    0x905030910090f09060806070f03061d06041d03030a090503090a060e030f0d02100902040e060403080a06150c0605130b0c0c010e0a0308070c0809030a0c05121507030b0d15 75
    0x42190658102c0f40c20090b12060000380700ca40e080000840c1d0702d86c001410305040110780a4100c80d421300032313441140980342005c070301c410102c04030f8046003e60409a03001c500070362504d00c2c0720941c00301400344800300c106224059032031034581203e008090980454140d03807038082008088550ba480040f104018103140d00c40c00e4105500804160800d00d900218004a4010805405640f9404202c1c400300d1290010001010352440c00804d00410031041d0700d2a09200315001d210906400640151003075020b00018000607850f4000401c1c1c00e01c0c41c09540300070800144017080003032000c0d0040382d841891650340b052010050b860b007944000081d1440e42c800c12000030702040d821000c2c0141007001c1f082d28001d054002066034001d000d4440107185604000d40c0d11034001c01c004c01c410480303030300c00001822a4003c0c4d0507030500c03403554180340c0306241c412038542c460401c00345404035500301900404100081c1c6c4d5a10500103401070440e40301e1650b400030100742d140e00000c555102100402d64a1070300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114964307 1250 114963057 114963059
    0xf0613021003090201090504110f0403030c02130911060c010f06150207060212070204020a0203040b1206040b0f010207090b010c05011508010b01090e0105041e090f02030c0d0c09090503091009 84
    0x1800225403000720400e040506040d10440583d030070880b039404070340040d02c00241000c20002c1c9804030f8011212070081d6103400240c00428540d000021840d00341c02141e400c0b0b0b2016102d01050100ca4044c0c400920119040f40c104030326181210281607110800000405c2c0c00c40f02c12403140494045400a0200071800203501406a60400101c00548842e00007070104031115804200b0b540128034009204a40002d441b616a80c4233200741d500400b40c0d80640c40c1c444660344010000c04904450982c05240707080c041e0400c601d040c86c0c1480350303841d042e00601700d441c0c103150103030010b40b99511405040c00b060520550014200344075404040c0ca4407214100c1c1141000000c03400d448a4255890401030218030600c410020700c0301450440f00121800510900460040300380c041c2c624420740ca1032447c0400304010f01406c42c0007603e0091081b02520950b500c01c00400c401c1468031000a040268152070601840d14540d001d403801c54000d000b00e03800d0095000001d080c401003000a000010400c0750 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114965557 1250 114964307 114964309
    0xb090409021801150f200f100906051506182101020301030b0105040b0109090f060f140306061e011116080304090b0d08070210031b0201060513060608070507050f061302 74
    0x8011441a4498607080ba1849103641000b48540706c20000c440c2481d9080d240014411800c020481e0b040034120f01f80c0300c0341640708805400821910009440b401d05200019005240c48051940c0d1194000c080c0703400e044d0500c4c0403e0410000040103900800b030705e0701459441079840541e502e030812210015a40c1e6041d03203015070108030181e02c243d014a042c00804030b2141e8000e1160003e4a0031688001141a00a50014050400ea0344001c45400714110080385035441d0180c1002c600c94150121485520744ca0140507010780103000300280c00c548028400b03210b42c410a50140c05048a50842c2e0000301840c1ca55806080998090020355000140c01c0110320100d02889200c1407045070080702021480c1c0b1414114460102c009110f10540105041c005000764031504851408804418145a40c00000707030083c500e1340541481000d02d00005d41c103042a5008620503105156680e00742600c83c0c1c0c02c1602d150b00101c3d41142c0c070f40605564810600001c00c0307061b01c207075100036288451042e540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114966807 1250 114965557 114965579
    0x60c02030a0b160e0409080a05030417031006031b081302030111030a0504051203060306010608280b15040308070602091c0507050f030f07140d1a0411030a0c0b090409021801 76
    0x9001365006905000b003000200344071030159500008641003041c2e13a55a00e1500501022214103d82e94085011040c000702d180c03850b0b1542c003a0785180c5ca00300001d030040007103c0680000d51554000103001007000a1029126440c8112018030107800800c0001110f626490141c00807507084c050b0070b58035000c002c14400c0030004118036010305440d803451402c5c0744011940741d04050040d03400b4001500007040b154182c2400300e28030445110940d00c2c2010326012030102800074802a0351040500400c421489482c1d1000c4a0807698401243e61815001c1d03542c05010750840f5070380302d5100c1c1c101c84099640744d00d180140d0400d03912507800340620070f04080400203150480c0705482d00a5000d104011000b440008810f4160360b86014032b0403190844000003000000d5095004100501e40c840c0c2075140c40301902450300031481442c040180740740000515a8600405002904110314044100304401d040300c01041d121001410208150206401140794a43e20080d0300d54041905070042003044e07189 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114968057 1250 114966807 114966827
    0x20c180a1401060206040210090e13110a060c0b040606050d0606060f0f020c0d0507051801080709020c190c090504080d110a21021b0303150109050901060c02030a0b16 73
    0x1d0700c1c44100550510b00020341e600d5000304000c1c020410582ca01c5d4405018104000c0100400d0200001c02d1908503240d981719480c4c1d141c21182100d050303800180900d0f001e0641c0003a551150382c0d00c0512107a40e200c902546001810555403a0341d1684003141c0c83c4c641c0100e00030150700030000401d00f82c0c500714000b0280321030420141c08002450555030001070703012618940f007400171a0100000c0196050040c00d080003a44040c6d0311080c13492100c0e5100250740740242c105c03118034041c0c030030642e80c4400d154180e106422040c100c540080c000302e4900301e00f40c03451072191805a261002e40c0303500c1e4074142044890981d0140c42c2c498000c550a0752001c014029078000d188043c0c0c04c00d04266001401900004140d002c02507120707207803480c55880814a5041d20120340501d001c000a4441d5003481949a6100351032000030100800f4600c001035004078412412100c01804000c601d07231a25400300ca40c03401e80001280d050190702000b0021401c000c1400b40148242c0c0f000340042c1c41c50349000b130600400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114969307 1250 114968057 114968081
    0xb0c0606060301032f36040302030f1b1902100e06040605070f06050a0b13090809060a02251403010504050a02010e1c08040e0109020903100c020c180a 66
    0x10400c01070002a6038080c1525034115684a030308145d441e60b10751814030070000d86000303400c02c040c00d0140092141150a14014512500802d00b00300c140207450107801000315009009030703100304094141d100103800280a0410420000401030120b0007c035410810805981036101441402c44021b40c5040262500e0f0002c282c00c142c034080c40380e40c001c910140514031524082c01400302c3c80350184484a100401c5032540403504202c4e502e005103406004007001d00704a400359008080e200c0042100344502031440d6002900103050188030380821510740c1c041c00f00341046000d00c1484404580000c080c01c01260400603010107518181104c0d00b0b82d00304c12086281c82603040c00b082c880403440114a56a00c01d40a20b08508869401c3e0085900c900c0c51070704151400d4800e03180601407000e81d002420130764480034003a000d140d80e82c40912007640641d00e4940d606d1381103c0104001650b507903000e601c0510300780c0103030742c080d0490f9400a0300c1d4212a8440c54141010031003084182891b5114150300000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114970557 1250 114969307 114969319
    0x40e090a0f1101050d051303020f030c03160309050303030403091701020406170717040b04050d0e0306070e040e12090301060609060507030c02060d180c050901081f0b0a0b0c0606 78
    0x6500c0c0c460035050a0000c0303002e0207034040380e0b2122050382d2090003181d9011118101c14800ea041107148104000010341054005001d4441c42108010700402110b01901c2800b0055081c8802d4900c040c021141c1c0032000c90602407a074000048607202130002e0340c40b0714040d0710f03642c403d10b10f03089100ca00074062644546843e4810802880100c4d00080d601c42e0444001d10410510b50355401d050390700c0d5910b581000760030f095060030081040181202c00d44118400c2c000c0d1100d140554405440485400c50754640c075400030360015107000c0c414100003014040040002c40d656a00d090134070304100c0c4035110302607850340001c1c1c058035904090003014000c0c80c440ca40740c0d5a09282420050541c05010002810841d801d000c0c0c2066681e90402d40d541407031460303020441c144850304040c0a004d1260000c41d604d800345000001ca44c038010001a040310f0340c40000d89000c076440703089030201030442495068025960301c244645610f40148003001317001021a080c0c6d65032048101da900d011801010648252 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114971807 1250 114970557 114970573
    0xf0b10080709022d0301060f0905100509010c0204020318070e070206011203090f060804031b0b011a0c0703030e0a0b0406021c050913050118060503030f16050d05040e09 74
    0x10720001125420100180c40d46031a01d80241030b03256040b26070380311011040044440040c0040194100c444d55100e06001c5214450280e5104005226041e031040440d400f803107545000754000c00342080140f4018403141c41540c0002d0480c0c000740c8191040c00c41c00c14030a80502010000940035009400c1d01e030400e45080b083c029a104014010b121200d130a0440500401d8060034020340a420300805054a0380d1b15800010203103141281d050f000140b42210f006001511081c1c4030540d039400800040703080c0e08216003000c08840103000c010804004000760b0712405400e1201c1000356204e6520710a41003880010001d0b4001d840e0061843d94804020030003c25400040320100d2199218028082d06525241a500c90040019130b50300040541c0521b04580c1d0a0380c00207040e12011010002c00407801c190800c00c8440c40d01a0030341650003080034581c009925000350003038a100e4030a061040c6401e68545007032000012040005c0b40001c501401981182800660300203082c400a01e030380 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114973057 1250 114971807 114971819
    0xb07050c04110f030705090109050d0f2402041206051e13021f080108011d0c130b0a08011415101416030903021008041703060301020909040f0b10 64
    0x855654084074401ca640300400c0c00701010410549884103250800d071601ca19104002401e550b10101d84240040c0350714802244500d012071010140680011078040366910940d9448000e4681c448045800c1c1d114401b44107400e40c090008101401d80c810b000c0f00320401525003071054480c0501144020000e2403101c02c0c10144c00780700d0503400b007440f900425030340aaa00120300502c500041c8011901141a408610315420010482c101c0b05181c1c001c03c0020b5503500d041201031094440f1649235040102a0443c510308090050944002401c000619001c0680010503100e05680b243c03160b41d45424100d40064191034000f41e0041c94400008101007450b8001050740764100780000511807207071014080744114100b907a0520003180024a8000000d04000d40380078140e00c0100d2080810000101c81c0da441415030301d008950140184d52000500140e8a031940c10083c429a055036007440450070307640c1c0d10b14100340206d0182c030744425601078a09000c044000c0c020800080020909030070041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114974307 1250 114973057 114973063
    0xf0402060307051813050f0903041401110309030114190b13022a100501080706050f0c031614060a2c070308040329040c03030c020105161203060b0705 66
    0x111007014a0f0a0f503a40c0802e1110480248080c03003580d4102428400d0051043c0403640100d0041030b099a1500055641c17044160380c900c0f03180900088081e1070b00000d441c0e5401104000c8034a00c0801c20340e42030800400c046030840d1050b07501042c13020005814080c80d541015812075040550031820b22000984502044e03c41240d910703400c058680c00942c90302c000103040450382c003503190040b00ea4541c0040c800003c0d03a40000642c6401000c1c034050001402030400a4624100e40403a140c0320b0074005188404c00319900b0040311070090740000c000003c4100d0760442c00c1000d01e0b01c41c0c2a100c0c203080240c40401d1404000a02c04000146045495040340d0030050002c4c0520007902c440000c0407802451250500038290b0006151000100f408404c00980c02c00b940c07002002c41080c0300d40802d802c41a05449101a503001d81001d180e000c0c18008280700341403503000c050042c10603a103812101a0343e20399005000c074041c0e52502289550b02e0f01640d060051200402055031401d0030320b00b00351a9079071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114975557 1250 114974307 114974311
    0x130b150304030c050d050c0c06041401080405071706011517240a08011a01020601031109070e0904111003020405150a11060906070305010b0f0d2c03070b0f04020603 72
    0x88880440010304062040255010b40e580c008103403284200140c8016000d6001940180003501a0549100d15810050180c408840000a2503150200303d0401911042c2010380291811f014211002c159030001300407400c000003d21000340003640c500300d03603258240c40c95056181040340c15502d80440e05e05104039280c02480352184104025804410149006200d0002c0b9400c80c011080c0001c3d200010f6000700782021f8170707030402221088000012a15070009000003409007950715500c04a0b0b04150761030641c031030040c1c1001084c11a5000015812b240c040703e0446003404805c4588405040249260806407030300d00701542440d007440300040002403210100344040340301040b86d028043c40350a0407294100c824041e50743c00c0c1441055a034950070f0031164200400c1c20100001201c04c00303030003192045208001005e09107907002e03c01c00007030141c1ca1a00c82c00d4002104072200502d008818154004483e6001150750329441c0c5081a07901c03800510000076005400d0410003d61205000c4903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114976807 1250 114975557 114975589
    0xe010614042312071202040515030607050705030717070317010b04060c020a0302100903051204030809010806010207050916020115080c13150905040308090f0c0f030f100506130b 78
    0xc155031040c40c02281d0014618030000100d441421400998101c1172615a8074050007a90705100560f598804280302d4080808480e40550100000903035041c4208081c040e064401d501741c0e441c0c0320450701d0304c8151440b00320140e603000a0010700c14040503001004020703d80c6a204c1c030352103950300d80180d040e020302403440b441c0184440500728404544d03800d4080130103180c0c0203106407128000c0c0b100007030035409540400c941500c40c18504840c01d0036030b40f003586c0440394408110391820403080c00440314210080c021310b055104104003c101c640c0e07000317032662158692581070071802480807030007820340d200007405450222048100f0b001c00f5201007221415020169110b07503503441003a00150003840b002c210f0b40910039603180041058480798020b0b41c01035011b6502d0000c6900c030320043d5a200c10003041d42490544c130510728080c9604000c01c0c0c940000d04000d00703071103c080343c911046050030314400d01202d8160ba41c0003008914501880404001002001d0402109885801044996400d042a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114978057 1250 114976807 114976859
    0xc020a02150f040f0e0601092304020f0c0706030c0e01090b2a060718050f0901051201110c030d0606050415121b09030605010b12040221070e01061404 66
    0xd8203142c1c40501203c00070011540d9010b00309550700c002c42141c25083d0703402800030702034940010301004002c500d90710121242c842c080c100304035042044025072101c100c40000c04410301802610010500101c402001c01c4e86020450201904c4c0091030500d003c80c03a0340c10f003c48800e05000786250517055070450300c030f42c1014203010880c00340c60000801301400381444901c0b510040155165200740109828680e201d1070709200c0391100200701c030003095084034640000880c40100598903001402440c0c0c068100c0001032100390181d00e49249901c0200d0100749640001103035008500c0c5817046800a104c6854181d08080c01d0485003020303c00041d00304802c100307110502d20b42e0301003154404d441b0001d40d45161000030140210140041410344819100a4540b500020f044072000f01103680c2a800502d000403960307200d41c03c0280303407891075921100292402492518042c0200060005040c039412100b04561400000070001c2007a5003c0c5512104203000400c1943c0c4031200c4e10705090500700d08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114979307 1250 114978057 114978067
    0x501090f0308091c05120702030706030c0507230a03050301050901090612030309030e10080a050a0b06070807050a0c08060405010b100804060b010e060f0a110d210908030c0a030c020a0215 82
    0xf8504000c101d13140003401c540078011000e2040b0541d90014030407544207409a640340350f40d43c10190308548a0118000101d40c00b00101800282e03400c0400d40e604182e01006142c0c540414030079031030040c10303240480102e940000144510315024034001e00514840c58217100300f07402c00408000c000c0b180040202415100c561030b000301030144c229645100307006807100c061442980f4004141203000d5401d4902e036403800c1e0200b0042e0915008506d003103480a010603290034015a101a003d0780100001e9549000300400440040c1c40318079664010541c01c4010401400e046c100380342103803c0312610501c94144003090015907a0400032281d481500818002101040240162441c000a1214940c0aa40041c89000300502603000c0d185658540c1d0320040181c4541040e150340e000d41c1000d05d00030460f00c40c81c4405852a0030703804d00751f0606034030380413444040ba5507800e1100e030270545400c134902c20040b445034011035140c8200346106c8664070040a020720260085042c50300b8440c5010110034002603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114980557 1250 114979307 114979339
    0x190302120d0902040906050411030f07290a02031b0303271504030201050a150317030c0c030a0306141801030206030c1303050109050d110304061b060f060501090f030809 74
    0x2004010960f0050414010504580f03800001000c084408039070100c86584106280c1c01d0000d0000110704008008000340b41c24004034250180f0020301c241d001c1c0d000c1011010018580384080c6c500c00d03650b0f4000b95112602c6500c0c2415004010301001d03810303031041c002c11803000d0050402c8074081a500c0380d180540418070400078100703aa01c3d402d0000d010280424001015070550006200d5006d04100700401c032844154071515511521024101d9000d82c0741140c0b04107491b000035504503802c448013038a490030801607141141c0143c401c420200343d9504c41041940c1c0c5201c241400840200d564010342d03502007140d4040c01e00c0c1800041d004034404000a540c1007905421101c03014510741600f01d42079038904d8900e000c0c00760f220003140c240c0219800d0f01c205a02910700c4540403840c0d10040e504040c00d10a08a81a0074800900402c003d10f900442011130380500c502c600340c2e0381000000c02c2103070800c0300142001c1c4243e40054007800007000c082000c100c00905880c1d0320301c01101c0400324901420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114981807 1250 114980557 114980561
    0x28030c0203012301080703170a11060a1a0904050307030c02030304050a120c060203030c030f0402030a02090702010b150c030f070609080f040e0604062106060e07020f190302120d 78
    0x21000a401d90710301040c9589a800c994440143c0b181c1403900000351340e80b6040e00b070b600c404541c40000c0030900414840a444401c0c00007a140001031450b1010100458040c030515209007510241d070341c1699030030700c500807034480c5860100089040c3c0740340301d15080036a61540d803842170480150070440c0c114000d00840d40e0905c110740040400a2400407000c3d103e46000c0280e42e1000000c6801d20100b0100040d001e00110030350f480303640e14148081c119501d04109490000001300102d83c58000d611000c00183c1d2545c0c200341c054200c50b4000601000d8440070b001c1c1032410700a101254850501ca16106094004100d98042006c07401031601c40c4110705e418005010529001408098007180003040f41541c0006030040f690390295052a40e2500300c18481218450301a1800c48212100341681006200c500c2d107200910405000a00980d907035825149844150740b2400103801241e03185409110030440c284a11042600507500102980d402035641c84401c18000140200805c5024503c8055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114983057 1250 114981807 114981827
    0x150304050c0a0b0a0206060316030b09120304080c0606030718020c0304180221010e06040e0309100305060307081203070c0f06020d0203100e07120b04020405031203060102010e2803 79
    0x903045460b81916a48900220741003016844014440e0744000360b010301c0d000901c0f40081c460108856200c6040d6204c0c0a68824001c0448034103101e203002401500c508071000358420f9024084007512001c00890a0f82090405400c00f4400d901141050190b0540f0b0014145210950040142e403a00c07030206250940c0266442490402c0c80d90301000c0e10385210360020868480c411042080c0014000b41d03c4092010a02400700d000b00240009040d6043c250311840030019034900f1079040ca4480400a074040c81e0007128440080d4032201440860f04040040001508070700f0084c1c02c00e6400c510660342c007400700500100030400c561102c07505100301d545851446c0354010200395629030b07146030344c2d0703010b0342c019641c40d9803200c61100001a003404500c51a401500e2a544110410b1000103540b4040d00c8030081c1541d1090303007000b0004c5c256904200c10080c0300d54062100361a460b0030000603085a0940840350f480e0381110300d405868002e903401c0052040c013000040014107030780307040440340b000d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114984307 1250 114983057 114983059
    0x2210d0e030705010e06060102060408090405102408090c13110c061608070c0201170408160510110901090303050d1d030309010609061a090607061b02010c0905150304050c 75
    0x400030300350b01400410341190301c4511120045a903242c5812004a80d50207044a02410340c40c0f00340508003142c50035422140d00301c11507100381c445454a41d40880d003070001030030f50040040c2070407c505190703a030001c20355640508014082e2040c03221340e80100b0490305000c0410641155a0380407598403255040580d800000100c0c200c1d01c0f02d14001c1004550701c5448918003021132900030019181a00c20b60280c48810b078180d4400e0304a2510450070300b4400c0015004032064441070140303108800003401281c98203405407004218440041c5400011501d8009042029410801401e078550360040152000c9990520b00507070380b550424130312002406100c0703a000c0100181c0310101c0d022034001016500550054000704586a500d4080d0b800301d444074403c1d0760340003000c1e614444800440700d002e02500340c000340410381380000035038510007103602105018001c4035013501d80d080b031035609224581d5400c10030302b0024025400d00000031524000485070802030a0700100060800400740055060a24 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114985557 1250 114984307 114984313
    0x9041406040503031e0126010905030a0e040501170c090c070609061b090e0105120a05070b0307080a050402030c090402060c06090304050415120201030209010c150f0b0102210d0e 78
    0xc0529115031a9070040e1030055540d0507800304551205c6042440368100d4402100c0ca40107440d68445000d40b01c2c0003030040050703655860310307a4800302c0c500344000c007014643c544c1c0f00111a12008200320441c2c0c03061304a00e0616510000711607420400041381345040e0b0301142d035911241d8401c041d1400501c24640000e21044c200507407082004000d402c0b070b4240c03114100c002102a82808011140c030f00040c4074140d02042200010009814000b0500c400a202c0c50192147d84200f5243d061400308141d0245551450000c100003815071b1060300550000701b03841007400242004e40011355510392800300240300b030210b50040f40840d5104411100c000804105031a118035044200684031f4000784641402275052228880d0036201a0780c2c04001d840000320460450081d50b00110000d4105c00f07045410f2017003002403800031400606141c1580100400082500500c000c8840b080c0c1d02e013650020705650040e80040050000c86c0c14900042d0780300f110054403580c9a001080c0509686840c1c292180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114986807 1250 114985557 114985561
    0x70206040f032001020102030403171b030103050c010201060b0406020a1104020c010e0606011e0207030b04020a0b0313020a0b070203190c0f080115060c02030717100e1005060102120909041406 84
    0x4500c2881e0400c00c1141051011a90f08810005a080c0c1c4001c40d0000d000410903c500d003403c1c0260722405802020000c0001c0d1102c44207038921403107074400c1c2c0080d18954060500bc524a60b424003820000c0c040ca21030301c5052901d00b2001030f5562841e8000100051080c48100005032903683c103032038420007540c009010700c407401c014080d100e240a8900c82d00150701000c1809010105002d418201c41083d4001e18001c0d103551a800d1801c40094007ca031700c1400000c0005441010102031802840118100340205559104104000301c4070f0f803124484074402e1000c4405680e000c0341000c0c200b540908808850111361510f04400c8181d81c100382111640c5000201c3d07102c2c81540316546c84081e011003a40842e40b038281c180c4880784600b10007545136020b680c0a00c00500b102c00c0f0a00b000002c0000c0711411030170f540085003a24883c0c012031249600200d1070221614050013407641141080c0060310a800b01c00992404512034081154024240c000100b4100510300b41301404081060054680c5d074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114988057 1250 114986807 114986813
    0x31d04020d09061d030a030504080c030a02060f1605030c03040606050a0603200301050d3008041b1401050714060705030f010f060e040e0c130204060315080a08070206040f03 76
    0x74800030350141c94407440c0100340d0b404d6150304282900c01001890040d4141020040d0850142c4002003048034840e005010401402c1420400303048103160b55006800e091829252503044450002c20300000c181c00c0040e48030300d180c2c0040c03c8a401c1401c1c07444255a80d680c0b400c0020180403c1d42c0402c1c2c010b141e1120010b02070b03070306601c150805010082035908500356601c02128500082c044c00f070344000940c4078039000070440b84001c0d8038400c01441104a0984a21018a22020310070808005c00c0040d020401040703500044200c04a440545400500d42040081c035080755101c60790605210000520074280100f82620b980c8900d01c0c20119403481c0341c4442c009141e5023003540c07110b298040314000454880050070325001030b02c20650300d00c0c2641204404101c060410280462240d00422161058076100c500f0400c6401100080250780c4602d40403004007140c00000100d1660b8800315000c1c0040740c404155041038540040c5003d85804160001400c64405c540c0044c840440c040000020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114989307 1250 114988057 114988061
    0x30c0f02090711160305030d090201110106060504140d030f0503090102040e01081b011b261204110f0102060414010b060301060201060e0c0301030803130309090216020301150503030403031d04020d 86
    0x4002c3c000f042c0d8689413444401c1d84400001c0340401010794206020100312000300e5032103a5071450052401140c0c10101000581c01c490b11500548001900090240441c90070781d02405280402a10408007000e03107524003c01040b03c0344d01c0b007030410a00202207107280c0000d40545001c1c00d10b4001034009540d40e118102c0c1e440110010f100c0449441c0001c0d01c040350700a41490500100c2e00080700d6010b44556290084050002e280710164803c0400c0303180302035084030251001c0c04240c61000001e04180c2010303518921080e0503640b158508803100c486590b0b020800b0340d04a41c0c402600030005482442160260607200044c035041800400005052507054110104407170b0030840340c1c155910756010320030b1148000d001c007411590301040494070004011000041c0f00b4060314004807640e44414041090740e01080300080b00f4001c11107140203528013071144265140000300e00400f01850000880d03101d00440c4000b6040c031206194401c500f00c080c1b2950f080000004004550710b00380c031484680 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114990557 1250 114989307 114989327
    0x1050c1e100207030917240402010e09070c0b060406030b0702100c030605010804080c07030501050c04050a090e06070522090905010f090c0506070305040905090601082503030c0f020907 81
    0x40511072005a00000304191080700c960b01e4041c1e48a281a50809051581414030703905206240d1240c0c0030142c058044502e900f40807280a180040a28105030000401d08100b800c41a48a038010748207100440d03421404085055500044400c80741d0b0f01c400c0000c004101c0e031380c0043c2554002c0010001007503170200396258100800340d401c00198002c150214101c0b10503006490200c0c0240300890b002c0703500301e0041c041d24010031080320081ca840e5914030742540c9003a40c0142c030040c0c001c0f03010311191509034002e00c0a0a50a4030421011500d804200d82d110406003e40d0103000c000202800c840c0109418900c0200c02c440e807000d04a80d42e809200700808031010b040c0c980d540b0b4403400c0e540c4203605000707652980d90002400b040d91414581040782d00c1d1b000580071420b018040100245214180c050240700344044805441c8943c5860270079420030032821907001c0c600045a40c4000b03d804407202c9034041c2c9425240c0420019481e10303140c807140a1134500030b035106880001b00321407164011090304c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114991807 1250 114990557 114990613
    0x12030c08030408040608070507020d17190504140916050912150a05070c031e02070801090c050a0b0406121d0307150b030c0d0b13150b011812060b01050c 67
    0x75069450b4081120180584031000354069506901c0b50041220100b480e0344001e03120505920308220031405001c0c0560dc0c0030790740301080b0007040c10401c04480d81c0c09201d00300c005075100001441d02e02a0303411061703403020b4202d0038440c020464840d50340319044c00a001d41828402c40d10460a0900e10f81800c0348120740c41100d042c102b00001d542c03544a4440d2980040e0705803603034285071611212281d2160515211310045102e10080000c11150074000d6401c454000c03403c0d070403078504140520005c000350f9084000901410132080000707581c00380b44c001031030708441800104030450075028070002184001d44280c922001c1051405d0180c2c9443c0200c40b4160480c0401c101f100d40000d168a907283d280605901c02e10380d14184000c209500141c9038080b1346030240c0d903102d0581d0758581803201003440c1c0d44d203800d503642c5003070b0105942c20202c45000c180511040f443e905182c05200340041d56800c500034140d44c2c5a03003800b86542d004401b901c00c45616a0203850740140b0042070180851006420a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114993057 1250 114991807 114991817
    0x30307020705041505030c2b030c0501110408060c070206040521010605031c081003020a08030309010b0603011a07020112020319060506090d12050c16090b0307050a12030c080304080406 81
    0x20300901103640b0300740e000311000a0003507c0544040410401c000581d1400c3e1142e0480003144900c206a4020a495586100740c40b00030f9400450f051031421034000c00b401140d103c0c420401402480d000103556a400701c50301c90082d50710b5100d4400b280345401254842d40c1c100c0300e0106407140c1150718500028501c042540200a8143d482d07003050b50710806181c04000c5142d500e1000140141720764296980102070010400b001540e90b80400d14080702903201001c1500040b003442502076083c01892440d60048034400d01750b5041c02811069108030b14800918403100150000459025400403403d5081d00382e411502c82c580501e07001410607020000070034103454100c01088030310b84001900c1d04410094803101100c40940c1e2200303501d840b9244400c0c00d010701440980e50f4900204034007001201e85518040819190401e49800e0324041d0548030b203c0c0d00103520910850301c03042c08400850b8008101d000a96070340f800c4c00c3e94007842a54029045120020800084c011404002c00803a0b105a1756 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114994307 1250 114993057 114993071
    0x1020d060b07200f041109030a060b0a09050405070608041b380d150e090109020114190f0c0f0b090d1704020f2214070f1218020303030702070504 64
    0x48012103c4440109a40401d5038000040b883c10264407054000d62180a050b10708110140020b242601c5a6403c460031034858003090118149590880014100e008082c0003030708103550b48a0303c40c1d0990140c1c00812031031000217024091080c0106a554601d5034041448523142c041d4030305102c40b903050b1038268100110400d0101c0562110b030500c0107000b8141241000e00b04090203004d012140740d070545a400020000c15a10801d621460041c452500009880885480003400038503031050001c5000c08103000e500c10088400d480c10310079100503d4620f014165803141a00c002244883c041c0c403000c0c11406040402c010918858040c0c0d68010413030310f250007200e40071219222403090360110714100c8400f00c0c005061105203034108420082c80e6003001c2c0e42c9030381902002c03005800742c1400140c0380c40401c201181c00541d40c58001c1800e16046140492068015100c41c81d0a002070303608036641c1d078000518190010291211917801406d40b0303941e042140c0002e40d200d00c1400f480c0d21451810328 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114995557 1250 114994307 114994343
    0x3020403120c1b1410020c03030f07060f020f030402300a0507080102040f0902090a27050a0515010809070504050103080408010b01022406150c0a1106030106140c01020d060b07 77
    0x6400001c4805036208804c8100340c84003072205c2804a003402c801503200d44141041c291341d0501c00b401030b000351141402c0d2102c41a041c1101965402c9603a04081c40c810010300344401c1d00340040745e51103030b01030300d084209641c18602c4030324079403042e0310264100520300340324069540045a05000103002c2ca0440e60305a440e070202c1c41c200d20840c400c023800d2180b001401c1001c03c45503005007130981d800600704015180e40f900040c550010300010301d41d40814080d03054903580c0261003500c1d00000103e0b81003144e13141100c21007400d80d103507007401818004c00d440014881c030344c01c20540003d40700182050199581d00d14003085250001c1c02212055402c0588040321940b001a404a8454034201d841c80640e1141c1d001003100309020b480e10b0b03080441169071124807440c1c640100b40b0306002c1030007408000d0450600c06c0802c40600c11152049004000401408c1c0c1c0c0000e40b91460403140304440d60300c80c20b40300c18030300a2042d8071114880c03030b051540000c0d08a04500240484078000c0607034584207151a6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114996807 1250 114995557 114995603
    0xa1d01080c091932040b030c090403031e020c0f06042a031202010b0102060112050616031b02030409060609030c06031e0e060103030f02030c0d11010608120304170a0c1203020403120c 80
    0x80611f8155000e110a854a8034218040d590028000d040005406000d045c8420a10301e215034a148500c0e0005164011401c0801060107100d1001c405018181095518031682c400c90b1079020700101c06043c4202c1030008400070302801198418244094900c02e00b4010380640000030f0681c1c05406528000a4441403e02c0300403c420340c0f140c013400c138580d01e0800050703443d101401580109540d48600104484e40c0b1071640a0b074944035002151140d1406140b0700c10390305d0710707006402004115041040003d1200c05030304155051400d01184001d0200350781401201040e40703c01d5040c0c144000c01e12500008204103051301d000342d540070100c01801c84c083c2c2c2d40c2c1c4181c41100085502500b01250341610800c1d190402e010890008a60b59039102d4003d441d1100d6400c51580349400003050104026010103451346800a00c0c194600305400f16101520700c044112024002180b1600c400f003110340700343e04175000345034458400c40d40f40d844060000c00804995008541d0001020b812221106500d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114998057 1250 114996807 114996821
    0x111501170f060705030720011409070b04050907020c0d06020a090b0a08070c241d0d0212070f080a030c030b03010204080706110f030a1d01080c09193204 67
    0x40c0e00140900d0f2100c4900302d0381c0d94030041a80080283c400e014805400c0541041d655005800d8004038000c880d040d0f240d821004050005805035012000c10002c3c0080030096078120b0300300b11115070b000c0d07550680a038100001020700d00d90003450000a0303010881c2960150404070700564403440c00944520416016100704c8200c01e02080e4105d0003d802c041c4501c903000340043c440e11990390303040011641d20380d090780d401c0900615036485442c03051102031804034107900032078200300620300c0901405020791151005c1c1c0d104108246c0005502082c44165200b494600d54041e6056a8502007020b00a00034030b0501c0318040040c0c04c0400c1ca1826243c1402910107407031003140a8001d99181039025210203252007a0400d4500a1a20411140e402440500103c075415241c0e103140c0c0c064000030314001c815510a6606000610041c0504962030b0801c0c2c801160b410fa48001400548039032525454410f5030014800a040c60400a942c2c5154080a0308207585510f0b0fa0b0343c0d034400001004161550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114999307 1250 114998057 114998083
    0x60304030e0d020d0605190513020a15110d0302030603010b04050118091a13140d05030703092a05010e090903030a0902011b0c06090e060112020a11150117 68
    0x41e10255500e51402d07070490030700329200810303102c940318550fa1501d098607005ca03198400c18880101c2c7c01480b00c3c1a015595111140c03445000d0303e00c0c61b540c001a2440c1c0f2a02461903225040403010f0600382c040d804502d202c180c004125090311406c904000c01940c41101c3e4640a5402c1400440c103e0900d401258140c6040c001058140c03042000e414000304121002620000d8102940b004458038900c04607002c0c02801600301c1e600e03009820080494906514441800d82c0440f0300f0b5114642e1103010789401907070b1071a01142c504c14a007850f0140c841000d5966000c9000d442010400108513090441101c5c001e80b0341c075201c070f40998208500c0020071508008a60010400503018403141e45c0007031501c03881418121140e030070f464000f0041c0c00c1c80c0c4c8011550700f10800d40c103102103a0804014001001c51103000c80c268039048000130018540880742007640e45c0c0101c0e1441c40c0c40e004418031010510390004943c0c00702070078250840c1d41c00080c8200403031500c2080b030032000000c0120380f220501d15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115000557 1250 114999307 114999317
    0x27060414010b0d120302090406080105060a1205030306010804030e030102030708010512030a1d040612110913020315061f03150609030c0e0c09091807061b02010c060e1f05010506030403 81
    0x51513448000b40030207189504820142d00304031120195855200d4140075050b8840009800c0c0303007241c03e000211203d504050041c170b07044028032000450020860740d01c00c00a2034208899199803805454504940d0f03240380e0306500201c10821027540c05030110b0704031001180c0e00707040c480451640c00e80340c2c81100b40070307400550032001c1d110800f0f001465852084030302400000d00d4a2b80c0703e01110a008071664202c600f5101c041d09040345203400300b81c45400c010f88444807540102c25900082d6105940800d0701d61065905000541541c0c40540151005003000c096100f10107110200500130218a1502041c0c103420820100d0514403680885050380da100740c2800440d03042840611001c03000034504004000304100310700e401d444180149004d811000c2c0b00c0c0c418885064009421b140807a004202008680c4200044003090001d00050b89a020b08100c46078802c2c50500502078003c00e80d08056038070410260340710450103e10100c03502c401d80082000180d89450404c55503100640c1c1c0500015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115001807 1250 115000557 115000579
    0xc0a02071a0405030f0f06070e0d0618050706090806010b0f0901080c0f0a0c0326010515070f08030402100504050303030403032403080306040c02010209030a03030527060414010b 78
    0x200d00889440410720715100c0740c41c00c0036034620000b45000c5000d05803803195085809022400030080001f96046455820310f00345c03191a84001c80d90b510b440e240041c004645902041c502c0d05412090900981c1d000001d82c0c0742c15440e840c01a10a02980c031903000c8900c42c043c0005010303a801810348000c0c180380c5490600d0004c0f03080044625020190440002e004c00300540c600301200b00780280007503500343d161012200394605001c0e0204184030090b480494000103984c2101102c5c024190643c0d00884204a6210500d0410301e0706020b001c600500000500030040184840c503805148558401c48140b0214405000c04451900640c0f10395a050f510a0000c640002d019420542040390342541e200c14035024070921220b040744551040e40c1c02803001082c40954101030080b1a182800e0340020341ca0040280e01280c0e8811600c3c2000d000c0540d20f5010840401c44242e110181d54140810303520005400d02c0029140c02040e10111501b410350b06001855040c18018034644c04e9000700400014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115003057 1250 115001807 115001819
    0x206061804020109080102040311010f03140c0f04090204090f050601020706090614070b07030905100b060d0e031204030e0103050f07120911030d0c12031e0b0102070e0c0306090c0a0207 81
    0x1038840540100d0510615400124000781c092029000079402400c00c0b03071b00c403551080050840d070411900b280806003440c4040140d40303a00348003150080502c07104e055884c0d84d680179140076801b070398020305821800041d00007038800c90b503040390071000d0907000304102039103c1d540166130b51040b07803040340042010b0450400c50103020704865036000c006203003d245050010750b2030f22400c1904480c0c02020960b07550492050000c10030000c14981c0c05070600704a03200c840000680d150140144c020310301030b1964806003191605005450b4292522a40c0c414035003424a40035040230003030034203140080d18210000b05007800c481680e600502403500c55540c10044007032403501400c02c42d40141d500c1d504100c22401c00f0348003044164001b203229030320b40329031020301c1c9481140e0a4030407200c60200f500703100c0180c1452030a02255014245000400116042d103600181d0a040003940160301d175408501c100300107900080001c44c8150000c44200c03480b0351301c0412240e600c0c003800740c0200069100c0e00c001d100d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115004307 1250 115003057 115003099
    0x31b08070e06150c0a0b010510021f02070f050703061503020609060c0106170d2601050d0302010902040203010605091003060b0f070f02090c0723122d030105010e01020606 75
    0x2c0c000341980d1100300544448983d15480010800c0e501d134007008a1000303018050402e180174020803501160f0380e14200500940d54118540c0254012201d21040c440c4521268101c524680e48441484210345041c206242c4600c0c582c441598040d040c86015542145400d07407010030359078020301c1c403402e014029091200d5500200d4941c51036640e12900840c0c80107a822507a03641400e105e00814070f0a03003282e001040060241404809203100000c2e210358a501b2000c42030641e2401d641d40e14420180c3e040c103e000d000c101780040c0d04144004000300b925503000d4018505200107850b640e82c1403400781011803c585041c03060850038102400403403041c4021000034440f0900540c0c1101d480e070441e40000d8004070041c1c401c01e002c0d0320b002a0300400c00202c4152840300803c2030707548200010700914182e84071210082c0e0f030600102e000801000d01c00c14604021150b40902c00740b03041251003d000b0754425070080c01400c0c0451900d42d1a840030b0b602c001201442910041d101c655000f8a180002d01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115005557 1250 115004307 115004311
    0x1615090e040212060a02040501022a01210f0b0f0306062b0512071e0c0e0a060b0a02010c090f0b040902030c0702090702070e0714070b0603100c02030301031b08070e 72
    0x30f40702d00144a4003030020420841103003c3c1c0404440140e07164070385000a450885041c01c0139519000250030f0312102000310032910564003007070038200c4c04402d2028038001c0324a9a07503d0402803e01d4803a44904d070f40f031640d101c2c140554042c0c07103c240c0c0c82112000c05658000c1242c8155203da1900c24601d41080a00b0609800e84540c1ca040d0011402c143d541d2418030310f03102640b40500001103100014807a01304003480043d00f00e0803800e007182c002601c8240c251201030251401d02c502c20408104414a25808000142010000e4a0320f403600100e0007806042441540000a641c0c1038000c20344400c0a0350181c201e4050004a0b0f24040c0b500000c200a50070042840b54180d4040c028000544c44140000b4442c46442d4081d0040c982403840380e00800d44085c07d0030040006c030039008201141030307604032036200e0340004182c02c059407030200092030b082d44da0040224031402d02140c40441074000000d5410399100c0c11680c0382c0d03e11520a460104c0d6118802c003a000e074810302c002c008400030480103039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115006807 1250 115005557 115005559
    0x1101020c0a0e070f350c0403080304030c0c091a0a080309030309011808010203010b071a040b0708040c0510030e060c030405070b0304030e0603010b18010e091501021e1615090e0402 79
    0x8031900e4044c4021245001e80c201520b4200707255011420455050341c0c0740b55010046c903078002d082c1811900c0c4e0060500000308004c091010a0802c00f041c000d009080c0300081c120300000740003081183c0081840c41554040c4c0300d0007862004000702e864100030081d1072174140c014005505000d0b80341d0044821030141f5501000c03070b486524022030189000c0c0000c43c0604004082996544500c0c60300c501c4c0344010700c81007500c901c84035003480005004040c0c0c45401001a00e01440ea507112824465081100c03036104641c0318a9131486030340c00d2501608600984481d000c25140d90765206802e0100b640f07c100d90040c8181c2002606000e111070310301c06560418000d1030444c8078034034800049603680d482a04007120940740405c0b80148569008203010400d0801e00c0d14814045004001c1a2811390182041507503504110001205174802c00410540c0e000401c1848030041007800125110540c100000e800810000c001180d40603082d0044444400b1540e540c00a85203010810450307800050412 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115008057 1250 115006807 115006817
    0xe01050a0c2a0b01090b10051305060c15042f0a0605070309090203070c0204060603180204020d0f020d02120f0c0301030305090103091a070329040b0f06071101020c0a0e070f 76
    0x320b0f0101c104035020f4200510001400c0b62030008024400c0c240400d03240400904100c000e26200440344c0c6031048880c155072990301d0301a0300154a003003007501041e47c07000040c080100424001c413032045000310821451690380d24030868000c48142d08070b149499030001c1c882e01040041038807500003081c2036406443c06402c5281c80e01c210310240d0b4800e407845c000103000340d481036096180c684102c81c010515800d00300800044040319064501c03100101900c034a40c0032498001c0c2c5070150b081080300781561141103503996110f03020700e0000c3d00100f0b041402c0d20f40010001e0300310300040101c1e0f8091100c0392074060075a86503980c111020741c01201650b0405403104c0d540030000e5103010b405614409448260203940c900300c0001001c03104107011118a02d4682810b00c00050100880c0c00c450040550700030410040c05d074081340c0c80310b080040442c3c01c0a00040c018048c4903400050702000c1400b6401c0c2c910010b1306a042011030740c0d01d0b0046800d80d0308900c02003890715025020250300c0503914108 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115009307 1250 115008057 115008137
    0x5090112140601060e03100e1c270906050609062212030804050105090c0a030807020d0b01080f010b04050415150f090f0e01020a0c08030c070203100e01050a0c 70
    0x210604050b401e03480726011400070564a403032417900744000301d00d00b040030004018403491601d08a0307aa901810062040e44c0c84c0d080f10a0b1124030808003152102502400000d28200c0040002d0381513403184501003003140ba00c03d0104d214608202120354011005105c02e041482d0640c08042103020310300c0b0190740031035559000a4081c070180243c0c1205000ea16134888a2400341071017801d6581c01010300f01c003500b0840703c050b103a9580b204160280c94200e83d81946400d0903102040072600780080181400705d04000004076803c0016486213440c260800074404500d1003011b11055034400d6078020001911310207000c200406a90103c103005030289105114543d03038500303480c840485500508000c0e5141d00d038200d9020b00038080e80c10300103d120002c5103440d1500000034040310002c81e00528030000040414003991410043e41c00558009007030362418441c1110305001418214015030300c40d400c00000440c00022032043c10b01c02c0e0900e4669586000d5000e1140300703030005d0f05000844070310003640 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115010557 1250 115009307 115009343
    0x5060103231009060b0301050603210c1902011d0114070201050915090a12230a0804150e061801030506040905100b0108130c060305040602090303030405010b01090f05090112 76
    0xc0519000c02c0c07101d07000288500942450003e032000c0c01d24160103a810306003030007541e40700000c21a5480448821035440340010840c0c0c0c200d00c1c4680403103081c80348a0041688600312500418410040c400d8036080c04d809100300b14142c052a040c0d10042c0410a00300d00084030080c00d9006124580c4145040c0e49042c5104000071126546c030007010440800c0840c02034810b040203010300000d0030f800a86062036002980d41c1001e0803810302d05205007405444400c030207103c400c010081049a0003031805071075035210131084042c50403a100c0700000a0541840440c1130404408454002c94801202164480407100540140501500868001d640c809113000402d03c14801d1141100312400003241c0043d8150004111040207401408001030580841f00040c0044000904690301401d001c1055601c03818a08001d0041d2031509030507002c000108820800190300030444030b07401740c1b1910b2a15071a50a01c0240c01e0080c09a1604209104010302030300c5500802b91184a119111540050023045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115011807 1250 115010557 115010563
    0xe0402070201120915050702150a09060b06190207050a05060a080928200d030c03170103080d110901050d0b04060312050309011a010801120c0807060509040e06040506010323 76
    0x13001e440b150f00e942d000155051082c090325800c08030910081c41150300382c050034030390078502802c20044280d94202c00020050316400c66601410010030b40303525450700c1d921650400021b410228014090900c0219a170b10388028008241c50010700f081c0e00b04039040354141c3e5a281c000d007010840717203c0c0345010240802d001302ea420b280c0300d008694040c84060351420101d403044655605000c14001000b2084503240c0300f0405d83c9c56501031a05901d201402d0500340c45c1002e6403801d01e802001e468001105005585005000c0c11009103001c0082d200b00d1500100240219224207001413010401030641d40030903003000016140007000000c14560f641c0d201f546181d40b001b19074012039004000c00c0040042840392500c01c084014150000c00204c600007001904140140402c0f0304903251f5420074403070342d81003080c0505080001c4070149616100d01916540144043c184614180024031021b0000460005d0095500400600c150303403c6039100300300c5083d0a17031940c0140700791035082d0421100c20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115013057 1250 115011807 115011821
    0x30601030c1110021c11270607030c0201110a08040603020903121207020601090504050307081c0903020f0f03040f151b0305040e06040218010518040e0c1f0e040207020112 75
    0x20300300140e4545417040c1e49801d0703002c0003036060040391601e04400d14401e81641100d2010040c0b14001001c210181c00300c2c00c00700107560210b50445000b1549808060f0820691107005000340c80c0ca40b035110100340e00c2543e800d11004000c00303021083c0000c02605020360060002c4040040985290242000103407500303410040090144100714400d1082c0c65405000031400b41c13031440428401c501d0141c81d0740b07603244204140204074010015568080406455a602a04000c07030401c3c480904281402076a0b6242100c5038805030095503429050940c0000440d0308583c401c0e280710070603601c0c24000709401b90300c032146041440303819030354121714a100c00d8041c08440d200342c5886803960300701a5400d0180c600240300c0c600a41c410004130300e4203151803014510074082443c0c205c0e40d954003440441c0440c4124030b409134000c2e0800d1703005172a809006c19222000001520100c4144408181808103ca0b542042202103075a0740c071040350340d040a07001021881e0043c10820320030a000c1c0b988804507110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115014307 1250 115013057 115013083
    0xc26070b07030501050d050c09061309060501050406080d1209050a05030708031005010906081506040801060806060f1f0f05070b0106051b0c0102030d15030602070302030a0905010311030601030c11 86
    0x5031a0811038040c2c1c0501c203c9014100540d000d51004402c1c1d515a035540248a003c1c3e4401d00400001404a54521984011900d07410809000340181803602c84040c01083c02103611070f134107141c40820050300014403080a10216a1501640525042210b000b042c1310403065482d4003549401c64080b590420007054418443c943e10703580e074948165a2504804160070050410a01c0c0713404005003076000c02000e82000510b00310300d401c540c3c400c0005200d40f146070300c035038019424140001281c400100b1028410304059881d11500444a410820042580b80a1042d200c03085504003403418130403540800304c0005400c15a140c60000e8803000e2082d04241c2c045000242d002640101400030013030f802480d02e01c00c200424041c0e8000001035200e02403003c040c11704682c0c03242000e60304450a050b038402960880421555500542030094599202c1c0c2003810102e4610880000c481d407184c070501d00c60901414001d800c0d52102001100600342d000d5140301046200c0408200b40306d002d1010540e8441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115015557 1250 115014307 115014323
    0x40902060a0c0606081903030506010c170c0105060a1a0c010212010323070b0d0e0307060e012405180a0b03070f05041d121e0406030609060909030c2607 67
    0x10283c54007005442d0a600007000d103400502c81070381c84600340354032901c50550508000c6190780d1900300403a0065000d44d0081c1401924410031080c0d034000e40300400d140c1a1400003402140c1e03480c028007111000c5480f542c2200b01c144640000002c00c490301500008200100162601c0384440740254812400c1c0c10a0301c4c1c400305400152040410704c031104007008a40405880003d181445031100750041443c88118242c40341d001000702c110a00c09c0720752440d44003008200610b104000c1600802d480300c2a48c146400d210103084800c501c40c1c1071801210340c0102640107590006108054401000e84403418040d210a02429156810700291001c0c0c060a030956115915201c2000141c0c0d2866021510781400310401007440d4101081d50b0405452101103582d50304084944180e0381502c0e000444510b03d40420045074095144d04088100c0f40c5040090049a8840085d401110585000200400c40c005003850001e400303015455858408216003504803141884000d01c5544682d1048500705 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115016807 1250 115015557 115015577
    0x6030c02210901110a0c03030f1202031f081c050d020403020603040f05010b04020a0c0b090a0b13050c040501120201080901060f060e030609151305031c0c020c03030901051206040902060a 82
    0x159000e0750380404c0b44c0d43c1500403c0c460700951258640911140006800c000080414141c01401030007000c440d212030440c04c540e6403410000300c3c070801d171400303644810900b00c0c00c1001030f03407000000d22410b05403a90b04582405600340c202c141d03030035408201500401c640038040000544d4500000d588600d0165595406420580c50070508560b0b0f50f07540107103d68030601c44512442d52040d1001c800303075485401c45107039481e02000c1514018050340001c00700141c010400601d80ea042c40c01d642590310983c115600d840c001c40c01c0101b035800900441c6c3e03c00080e2400700d030141d0300c15200c0c950022210400041c607a52030722500f4524219075084840420b00c1031a034120b250504014055003d002c0c0e4001d000003005011100261603000b03844842c281c404840e8a40900c0b50030320440305408404901840030301b43d90a00348010b81100854003002d4050711800c402c050a0110480b02100d0059580030703d0480198462501c060b4050316840e04690b40c2c440080c01603ca12006162021980e00d42070f2090b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115018057 1250 115016807 115016809
    0xa0b04090204090326130b1509012301090b18010c0b1f080106030215030a02190e010f170c07050a0510090c06090b03150111060106091802031006030c022109 69
    0x420152580c0380b4024003042044800e0100424081520354005103506c29500c8d800f050900c0c2400c1c44a100e40d02814040c000660100740132141c4420003a00000aa110722403040107540d40320851140603d620000c0024000201c807084010290000504013140011029114005030190842d01600108142d665400149020200c2d0600510308000284126820355010440d500da8000341303042c2040f0084086601d005030360b0140c61608100c6420b05c0b0f664403030003400420050307000701c2c0f40380455024081b01001c503114444c1040048000c2c0c42d00c03030b4a51100145504a50f20020080c0d40c035005076001d140003c1c0701400f690012000000010518030b20ba401c20500c1d02c122036202e4014850540401c000c0c1d0035400090741e910503501ea150000c41040140103880d254210018904580103507000440d045800000c041e00b90751441c03030600600801d1616440403031200b03590780300c0c08031543e10040129520a070407643e5181203902c151040364000800c1e201004554280c140100140407589145c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115019307 1250 115018057 115018097
    0x180d0305091002250c030611040302100305090a1b080709050615030403140310030b0a091e03080109050705040b04060207031511090d021507050a05061b030a0b040902040903 76
    0x1082c0e0101d604600d01002c80d120448100c40c008291000038803030303004220501101e02605001560000302c01d00c05a8072107003101090343e2203400200d00c036012141c18588941e10921940303220f040d245005003030907a071945407a4108080881c091300c45000d40b05010464410034000c84004259580020400d41070400030000e065925140e83c00740301c00284100404a07a02861243c41c0c00c540c01034055607078840c0e201d500a00c08040e0400740c00600c0460a10820700c9003580610802c5001e0203c1c5503590f80103509150820380003140280014030090010b00052055030f005a41000050810a19060b9508041c1815030020390003240960000402042804002d80c032425007403500946c200084c111090700c03002c050243d40d400078003913001840801e0454442c40030016034808211401070321841d1030310703101c3d668450f0311000321010300074100400d010140c890070344007c07680c0b0390745034509699409040304002c020708002c166001d919002d120300540c13a64800d40d24824080e5907110740d40302d010140360304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115020557 1250 115019307 115019323
    0x31211040f030c0617150a0b0703020d030b03011a060c07090e1509060705040308090a03020915120a03020a02010c030207120f060513020f060705010209120304081b0a050108180d030509 81
    0x144030b07405d81c2904000b41e00300803170755015407800080ca00440000000c214182000d800c1901035150008a800526800180b0010240041e981c03c1c40b00300d0b01c1e0b400303141c2661004045a0507482d03407103130505a075181210241c928000008229041e143d83c0d00c50038000d4501003034000305150024115614000600d0880faa40291640014400e5050005000300340344134502c0082c10b00380000c200d040701a9176021401c030086400400100c0182003aa07528562040d42819462040244e4a0324240300280030510702035441d00354018010340c400c6900103403120740601004070118051108080780c800c4804843d814101e000c0c1e40560079043e41403070a00129500035103140d003890031062040c0b0060b65800110014039105a13001a04c0d80110721b003050181c024030344030700d60040010410401425000002d80106d84811003126003020315450000d407000710700e602158201c104100140000c3d4003450155422404014072501d02c4070a40001505040c4000000c9000079150b0040c443c0c0c0d200304100c514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115021807 1250 115020557 115020569
    0x16060603061b1706120102130e2d1f0b030c0a0905010c0203060a020d140a020702010201060501080f0123040e060601080930070c0803030103021e0904031211040f030c 73
    0xa4207404281c06502c020f20300803d90b902c1038610000c0300040100039019104070302c042c22181301c01c0c15115060a070190108540c030ba840041c3d0048060840004c80c82d40c0a5064000801e1003401d84400c20710443c00403d0040041c0080640d0200190740343d810310040d403154581e284516220b552150005004607030580c800d07410082071003440e2003daa070205244d0b0300140140300050755886880000005084010f4058104240392020052805c200350000c14406100340c1c002c0003004d403aa0015035805000366240c608090190b070040c0300e1040d0001e104903074500e807a10080d04000c3e0220000d019103100c2c050560082d044241440607075604800040d4201ca82c1c00041d0100088840035550744280c0f1b21444840032001802104103410780c0012100c0781c9030021520b14034152200d003241d44c0d0b640f0038481203024082481c1c41c0341c0d07a4411111000e1014800a10801c0161140d48045401120300c11040000c1c640e144648442c0c042d4580040000b40040e60403a04003074a182081d40c0d8640380c1d54028 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115023057 1250 115021807 115021817
    0xf041e0503060f18070f1701050106081303140711040f1e05060d051915020f0405011101061e05010e0609090f100e010b03010806090109050309010516060603061b 71
    0x50040c0d66000c103046900ca040c3d620000416554103844903110341080404071000c0c0109000410000006440e00c0140c80c9110300044801460a884900303d85003440707120001041200070940089020804941d2a4083c0c50f02c0f5440001e490a01d6100c0d40c406d0310221800003802c031050b403003820b040c0100c03407072a01100410801c07985610030500511241e0600711404513038843c001003ca42e00ca0702d208910300d81080481d9105404101a8203050f20641c03400d4513040c411209042c0c413005076008856145480300c0030705003443e01c0c050066420090004600134030703540301e10000c0303007001c4a414820000104141009030041c0740c01d0000d40f0007070a034002c0a00555003001920555200c001c021500411603040c8084595154410318003415801d41041c50300e0385000000044032000c401c0518107803006001620a20389a8000c12801c0700d0200340b00612030f4109201c03c00d040d6004034003821414030b8400d00c0c80800104c643d54201129402d800c110307007055072580d60305d04411a00b002215414494280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115024307 1250 115023057 115023059
    0x20d0b0109030c0501051b0303010b030f0f0112060509011e0b100c0c0e1003051f0e0d090b090402090303040f0303030c1403060607061806060e0703020a090b0706060b0f041e 76
    0x41c0003c124440e0156506100700010441d45220481f0300c00c1000503c140141c130345035619800d041e0b0003030b407041c4c030340746406038042002c42c0320302d11001a264101d2b41107031040c1c1c0c035040103540c80c4005041d00401402c00d65694021605108040214035445401c01039000078003d0030f40010405440030024145080007801d1515000181349032025809590448090743c07119603501c00110781100c0c0a40008015015068105080075401c2419030000c41c0750702028800204d05640340c41d80d8040c2d1011007000101b0001c0100400925400100040b560140000d45403280c00030106e407960b0721560000d50081e003c42d40410034103070700d403142011640086c9030060b91031040c0c0006207075501000e404d030b0344a0b0000090000c1042115800340c1380040074079051015400782410401c004014522913180070604040004064038440c2c0300300d8050704503d03155945445d0510310030340c0300c0350068803040711029a19080412055200d902402e4088000c10f4a1030f600c0f030800e1554550f98a41d640601034035510404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115025557 1250 115024307 115024313
    0xe071e140403020f03190614061c230304030812010902190e01020c0406030501052406070f080c0304080f010e030403080d09060609020a0203070b06030a03020a020112020418020d0b010903 82
    0x8640407a60129000345030404e180c00024202501103034003c1605645008600812501c0d03080340d0b4005070034460104040e80ea050a1007010b04260707080c00303071140403007882d1000141154070000034103800100703608180e070300c1d0484141707954869081619681c8003c84e400c4062040812a03a015015400040d41001c0565004200079200b9288900c00d0054a085c01c2646074400c200c5500d000c20014002c4c04425540c2c14214001d060075640111a90701d8052100c0030101c260708080e030b403031101130b2181d840d000d9113403150a85001c60160448595600304106001c0741e0007000980050442000501488101003c4031821211000c0e50258179030800e110070800714411000751050320907601004034108a16140440007004140c0054140e148042071031041d6590000281008511030403000200791aa081099a42c0c8440f450040069000155210055100d0705145900c203403011400340c1010b84034520342c0300d0f07800c8401d00e50b442d0310b5000c10060724110b114010f0320141d600038201350f901242192 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115026807 1250 115025557 115025597
    0x90a0605010e061b060c1209060601200c060307030203071b02061912090c0501090e0c0f09010512070201140f0907060503090304050a0f06091502031806040e071e 71
    0x10840742c1c89054046407090004c540c418240020030340d000290f500d503207841320801c044c6802c6003403030702c88000010000901407000000c815001c2c00c0141c5911040c054442051075901e070b841c4041d50035a00880780d0f610841e0f220403004d98003445007034a01607168130301307144024080702d0000030302c1900101f0344040c0c1c0d025882e00000c0320403c000303010380040350b030030511010b81d10b036101e902030700c100e4602e0712491009009840c00da84042e01c100b603031594001a50f0709161055128140e803500d60040003045004184100c80d0020f01680d54103040043c04e01d035051101d6041154200c1c1c9150250b5128600760305494459450540d0051081d05a40c42904200c0085550f031441c0780100d40611100001203000c0030300c20000c1d40c0c0141001041141c19035211021295030518a1040102013100c1343d60128003580c508840d030504059641c020750510451f29241103034415010003a81e0406420800440e010a4050b40548502069201c5452161a243c41c8400002c1340000708800c0140301c0d01c1036854000b4070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115028057 1250 115026807 115026827
    0x301030f02011206030206030421030b010905040902010c17071110051b0705130e010b04140c1c0504080c0d030510030b18030408060403030e0d140c01060305010c0e090a060501 77
    0x280707040310f080c00b80809104000c0c43c0c0ca81010b0b41c0000f02204010401419a00b680141e0207518694003818100100940c19585040101400b0408100c001e2140d401d059214640340d038014500320941d6400394492049260089840b10341d04200025203c06000000c1f4843d10095001e81c0c40503181e0700300744401030080c0600000c01a20140490040410704010050f140140c0002040e401015881080d0100200300c16014481da40d42005280449842c25106100742c21070100d40041c1c00f0f58504e03003c8070030b0307610500483c03e59214415000300080780303902c15a4810b0f0710410b03005030b172107920000d16454101c01c000c1480c200750a2a082011003240020184c00300c0354081c68540941d11041d06c1c051100c00403603200e60b1144404200010301d0200040c0c3ca501840c060b803010410f40000c0c1e810161070b0010310340c0440110300081e080b9408a1080d800030701c030070f290580001400075102da58142c01e4035091035030340000418298200700701d450020060307074101c000c148080059070328140000c0c0c80c0c100c00d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115029307 1250 115028057 115028059
    0x11010905090103080904060803030705090f10080f090a080706021c0b060a050a020307050a05060612060907060c0203012315030703110d08040f0b0406260105120f12030108060603030301030f02 84
    0x401c00301c40311b4130303603030018405401c8400130369803030b8030f0300e040001e040da008403a00c2c40c8542da8941e1b902043e41450f4180c1403800080da40c1d015030320b9540c074541940d1410050700020480c421b803c02e600c0865414000341480e580b0444015070b031046a4030007502c04440040c1c0441d03106140445051031546d400f4110f80204506042094903107108002c2641036004034040504240a5840808100040030070310b1842610100c03403085403511100350b00346c2e49003021a1502c0142e0b00109060054030b01981c2040d501d07520040020588460050600307900d035080b02e4500a2541e81e0302c0501440c5c250000034000c0c240300030f80c01080e4491039a00da4115070f2904004581c000c0700c1c3c04840006024110085402611150b081022160364418004d01c2681c05403159600050501c09503162202070720a4150340319440c01a0040a41d0034401002418041501018244d00c0740d10713140c1001d05401c0c00200c1106644c0d074219910b82d0724050342107050920042038940710307400400061002901181d070300e450940e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115030557 1250 115029307 115029323
    0x60f0f03050c040b0d0f110307020c0409020a0504090302070e0105010f08010b0306040e061305100216140708150105100302040b030a1107060e0f0d02060112020d05010609060b0711010905090103 85
    0x6a62500704094496500104d02c040f01c0003650b82e212a01c1d80d08008004000014100013040d5851068402408169100700041c4c10681c940b10a91038070b50032010280740000c015991203950b40d00060215183d610703048015030040001008100301104460b030050500303007003000781e80480b502c0090045205000700001041e010020900c1920303190300c00041d1441c880100d5065003402da40c980c10040399440211200d214011008905406038020384064042d08080000072815503598003039801c805041c850350611450307000150940082104041071107010315612017035410001809207510000e4900000e02d801008101f01c04180d61040f680d10052080e400900004048141e00407881158005801e02d030500d40520b0000c02c0110b09006c060a44404654003850035881c160b0711260240b150401c21043c0d00060030160410400124003e0711400001136100d0301d079103003101214030b46c3e08a01c0e0350705000305030002088401454031001301001d0070422810381c5000c00050b0012814000240720034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115031807 1250 115030557 115030561
    0x906031f061205030c0c011b0803061305010f0f05060424020120030a140105060d090c030f080909071403011502030d09110a240c03140304060510060f0f0305 69
    0x4000c1e50001000e0400014210510300703450a0241d9290803074155240c0c14042c010324454590b0140795202503040f910aa4400b0342909500c03104004c1e00000e06003500049a001c0c01c210b01009032203018084d042ca03100c80c42c55103040680c071100e620540e812960042100b0042400141c1181d00c40c2400520341480920070720310105001c84c054000201c0070602001c034254403081199802c1c02461140100c5a030801c10001031050aa00c0d5040c0ac0c0b00e56500600100150703030b080f910a03003120a01a005210720303202141d8941e2407844942102c0c40c280c0700c122000c5908480d81c602500c0c1c558028140303191444410482c4002c00c11072740300600c02c910752600200c030303d03140c547d000344107542c900320500c1010071000040c0d0400400a03e211910f4a10400004101080c1d0064145d011191142500311820a4100b4080b058444002c910016014000c451f0076101079078900754000c52003944949808a402c0c00d008550004211154010005100140700741210017a4480c9c000c00c4e0b031006e0303840c010030f441e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115033057 1250 115031807 115031863
    0x4050409080d020403120807031506081b0c010221010806070c140609010501080c010903050c06070614070e0310050705030718050a06050702030601050d0c0b0f0f16060b090603 77
    0xb03100d00542c0070b0920b4004070b03000041c04551400d2010760003080d00c0394a030595030480d04600b201c2050401e9182d810206d80144070305413061340066800201d003000368120801c01d242d90300007900039009042040c0e4002900850721104010460003450300003100300d08950502d45115101c46000f00100c04000d52908020240121803110341070003421030007511114100002c41a019040074000c3c644c8078481c04010001c030f135100720001400c90350480007030304601c5444002c00c04903030b00002054600c41e80343d00c9042040c2842d901558001c42c0651982c9140710030380c2041c10305010080c4501d9901d54a030600300320a154108044a40c060316514020381150052010340180e06000c2d08500c0d0052070300100480e4103a001001490024022012101d590b82e8030300c1080780498131090001c080d080358200401c17442e8048006841001010b42030a400c00903169400c1c170b41c030b400106400c1c0001c0300e000b104405015040c8905a40798605540c1001c02e440c01c1c02c0402c0c1d1703800d1055142001521241891324034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115034307 1250 115033057 115033073
    0x5090a081809070305070e010f02100b04020702030102030c1c090f08030601090f080c01201c020307050607031a0f01050306120a120503040b0907060c020603060316031214030c04050409 81
    0xa81c40c801803882d11a0304050300c00030001e0070200c030710f8404241b01c1035020380d4941c050080c20380050416802854030204504481002e00b0301c0070007a90700980c0034804100103035802c0c00614440e94050040300e8690003503030003415101c504580c0000b60070b80b900c410032000c18044800b482130240c00850305d907902e8075400300498002ca16079200519112070790402161110010851401c4207800b44d0703c8041000c4400d205082d940710b0400c0c40c401550000c0400061038090200d01c64103455240113507410410385888190804004450303c000003903550142000298040020080c200015115141031191640c00a800c40c400a05164480c036855614400da02c1d070204020203125500c1104045030510301d00f00646190410fa4084800c0c01a020000705031180004107841124030a540d07503000d40d42c1d17680a2041941c4003426103505030183d198400064101034a2105c000c5125854100ca20055074500904d440354044103590440703420024450f920b9035079015501500e03c1110300003140c5041c2d01d00980 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115035557 1250 115034307 115034347
    0xf060c02040c0507060905010c030c11061f080d0c15020909070509060f0f030a060e0903030402150c1c0201060807050d060b03011419060605040302060714390405090a08 74
    0x1017500d00707200c9140c040100c19081000d03000c2464505100e154003000c82070780c1c114500b400c1c440c03180d40300c0d00c009411110405065540380d501051030000c4aa00c80c516181050300e104070302d8020400b1180b44d281001a0406a101907400d00c100443c144065440012410781d4090a200304100300810242d1190b51040d04940b00140460390180d41e8007003101035200300c2e40044a0043c08103180840000e034542c1110b20700b510420300e9801541c590740d229070070010240d0062006075040718042c0140c2c00c0203402040504142201400c440c8203a1001e00780090035a9031680024410387c0048038204040d40b900422400703040d510a0000c0b995028110110b070040043c0c072043c0c54840203500500c00842c103d01c44854401ca0304c1201030004603120002603529214921009400034020415075003c01e1480e05542c108518440c1039545c0e02c1e0419820056104020b2145516004807203000e4802c07444400c0032502c0054190b0b000c2c0130301e1800c0d07080b4a86500e100880500f0505000801825180c081a4208 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115036807 1250 115035557 115035563
    0xb160813060c110603010f0b0309010b1225080c040b13060f030b0f150907030605031f0b0901080705100332090105090606100c0203030a02030c070f060c02040c0507 72
    0x3208640e5901c10007440d24a03031140548410465006010203410312600300c0781a10b0700030648614561810000900d2640024452412550389130f912803e10b907120032010703040c10000b000070809241c400701325200c601d03401207180190a8004c00104a04040840c405560300021100003038007017400f0300441e000c008410780c4206140d00e406070100c0c2c403580740d401358000e80340250384445030341d5218002d540880000383c039440840454004c82c0205490130200d80c13944040d00745000b040003070350344e4082031401049070240600c003a64220500c2c92900c05101d0000904000c0302c90441c0d035458091044e0b00e641c0c0c28080c1502415283c005c0c0102240a80c10074a118080310f20404609005103240a0083d400031a1016036188be020104007219014082c0500030103801014010546401080110b0b00f8040d4005c1c03002d0195941c9071030b001d40c0d4140080d100307440316070b0040d41c1d80b18a885e05050411340a034100078240d4034030b20000e110707150b80941c4e4071007990780c16180040d4402e12a46d0554442c01001c07002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115038057 1250 115036807 115036837
    0x18020408062503060501090e040204090b0a0f0c0e06030a051806010b0a0914130e1207110306010503030a0f120902030a030e010207050a0e1b1309140109060b1608 71
    0x101040071040e080d41d041d0100314040b15903140e20300031022030a0701c105128150000c0c00711141408421070700034440c1e0b0414170040000844245658a141441c281101c0d48200d00c1ea43d02c49808540c1c1c014011800122450714003e100303e031407580080c00a00015103540c000ca40e07200005030760395407901034802170205074400302c564660f92460107517000d500c1219024002821504002101c101842841109520003000b5038a59460300ca01d00e0028050361a07008010306c903c080f8030140c4164513006140c0c0600840e01c590001c0251420f0610f4944182e101601075803080085042050b1721001d0100c2003202c0f46405500092865594009407003049806585400f40000340304c1007582100e0100760300d500c03e07000c0c5c40c107103562001003040c280e0302407140d517460380c14030070028908454007a1501d06108049054a060041d070940c40811850a038104e00041580c9180c4d5800e40c003180c1c05014010a64100305009060802c0c114003060701900c4a1780d6400704646070030108000c0341206454000d50b80a0301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115039307 1250 115038057 115038061
    0x203070f032307020102012007020f010318200f031009030306270606030507020c22050c040612050c04120c0305160905010515030115110303070903050c010c0c1802040806 75
    0x51040c0b10390003c0c00483c00340d0b280c507105901840e501052898200c0000000307030f080000e540c00303201014a000008504140e507483c6154140480340c030107c5d0600d0b0141c106921000c80086450032034480c142c402a110391004885d29600d03903800a0440b04c151404280460300801c02c1c6025000350200382c04c01c034101008444105060024440b0b43c41d18194206401d0100304e5031400150215a01a00c030032006030030212002070b403400c103121901c805500d00e803542c24400c0e2031040044200c98042d680d6040c8440006010031116500040e280e1111401c05000c01a4cc1418083c5801c644140e00c07031649240401c81c03541c024420341c042c04030001e503000700030740709001032098050300034444034001c0d444068034040001c101402d203a44913001c05000445020302d16401c0c42008199105d00229600030802c03006460300d9940001e0000d140113516540750000d000d802d41c60914108104001d84904004280840c0004a03040001c0e00b0304403005d01d0850060415160901e1000e489140c0040e0790600c54403003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115040557 1250 115039307 115039367
    0x4051507061112041a040819120507090806090105010f050f0301020d0e0606031902030307030e060f0c01092f010305151c0b0c030103150b04060312090612020a0203070f03 75
    0x25988583d2268042c80ca210a20600603003040d1825103007d0010319080c00940d00a561100e00301031602014144041d800d21030f002d02205032101143c45400185440703104000071101080b015401840410091103a0360424000d20340c00b2031603128152140307107040e10100054900b98101d030002c2030300f500140312584a0098043d40c601d03096900b60301074819003046888203007040c002c0d01100ca50040142d840c20100e903d00315004010030801d03540c400b608004060128100f00700809038008681c00108204006017851041e860f20041842d15801c1c9459034000c4409207a2a8120030007800d0a0000e46916240111500149081c5500347c101d80901c060359150750b5014050034146200e03980403c803681e07800c40500420b02080c4002464815442d003184020200f13178208500344030014000051540d5a500e4000c00914580204404100001d10610001340d200e40720521000c0408400d6190008002000f580c9118032003002d403152455081c400300305031003141240f4401c42d40511082c1840350942e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115041807 1250 115040557 115040587
    0x706020310150203040305061501020106121217010b0a030c0e0604030b01050306060f10080402030a0623240904080c062401090303090e04030309080d0c020111040515070611 76
    0x8000c0402603150b00c144405041d1001045038107980c1e2040c00380045460306c1c2c41500540c0b00605816056540780d040102c1e502d520b505c01080c205002e140c0644600d06040805400000d441050010b650114801031090256010031030350344203030703500e000039060103504400ca0b82442e00c40425640100d00240c00014070040241d414141c802c2141540e0190700e900041001c0051151052038001e46c0d1603543d200c0311030041c03c2e87e6501ca8005026038007900300582e2214221030405d4489404981003807003070b03540040b0080310309030b00495501e641e1115600a0781c1c0340c1281c1680210640c03094807154001001c0088250035a803400704a102107c0ca5130030a400070106000400c45171a9804031042ca003400d056214581c4507007120340580307543c10f001d810107080500c031b580d00620035818181c40f20800c00001c2c0d902b00040010310203449000408040f580d030006c0c20b444a05001200c50300c41400700380b140c0d5480d804a10013002140400ba941c03010245042d102401d80c19009001e044000b02d01000b46600c1a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115043057 1250 115041807 115041809
    0xf0b071b0b100f1d10060e060a0e030a03030c08100e0114040207080a0807120506060409020c0f07030c0609080303040809010c0317010e150d0b0604150503160801110c03030402040c050706020310 85
    0x1600845040c1d9101e54004c20500d00c17620400000030034011402c070741070074042c0042441c10100d103080c1034501400783c00f00b4075002404c002203000a5656001c4010550300405464211303080200072040c0342c1c170b0440070030810f103c10700810044801c2c01c08049820b5031285d04132640c2551240310030351191341100c3c02400307030b500440d0b058004c02c003c080700040d101002d01c6031504c03c48004100d0750410342400107140080d045040308805c240302d195080c401040c010400400194401c00d0346144035400d101c00288280b00c540d01c0107907103500500510000412210984601500a10700354960f622103007021a001440400003842d45480c41c1c00200d00c400d04600307120b2041100d50583c1c0c0c0717840d44450521226a8008101034144041c24020450a00d0150003c1c224801a90a1089541d0701d850000c1d0038240075a10001c624178213a813080103221009c0c020034440001d5040803900740040200100e80301d10000b40024400c41d42c0b9005031020034002c60550700401d070000000c54892a010402d0741c008411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115044307 1250 115043057 115043099
    0x30b010c14070e010e011212090306020c06010306180302070320180708060a08100f0b15030108010b1c03050f0d0507020303041a01080a02040f0b0402070f0b071b0b100f 74
    0x44000105d00d0050f07041009040301c5400c280c0409130030036510342e020941b803201d2840041003003201002000c00d030240040c01e4204821009805c10754954900309046440041040050f00c0000044d43c0120f9004a00d01e0110f0b901300c107a081008240c12005200451020001d82c0d00042c1e000345a05034011012099110762a10303100c1580d10f88950042040c0d00c030a44c400c14442d0f5201045207000510301350481c1c42080c4c403a0320080b03288225240011041d820000905103840c2c0c02200402003004240283e047e00802511704e40f0100f1030800684503c48100c680283c2030080009044d2603440c0080c08480e41e4004840e401c2290f0704020170020f40381d0b4810b40d4140c0b400710f40c0c928164a071310310000321141200c6110700144040d20700c0d13509002c09010380d4480038980f00e603940403810303558035180010000184a08000e1050460518020a00d824050200c80400165014000d40d030070a1868402c030450300005090078503034611200594260716604030001909203520000340c0d40380c100d010840b40a00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115045557 1250 115044307 115044329
    0xd06060e16090608010b030a0b03120d09020127060503090c030106030606030b070824010c0507080114010803031003030518220e030906041205070803030c03041e0f03030b010c1407 79
    0x10b03480f6011035011030700707000d0800000300400200d0002176035503210b50302500d0068151410800b84801081c0b050300500d11505005032a04104401c641c0e205418025110300d00b454146030222075a22101103204a010b401300380030303001020a10b190800c102d52250780b40020000d12580b912886c0100190107030b840101c0d90a5403a41c0442c840038000c0881a20031f00b442c003070f40b450344079440f55003803158440c5035810707070500410b03004050200e0000d010103006404401300210b0700b021544103a00d8440016401049aa0828000d1007100316018030518101d030f07003602d00760382c441c0426244090f4450000c1141355104007001c0034004120817070303400c0402d02c03180f2203410403401d80c8004015450b480b810742c0c4c480d48544100402c1c80250032034135802201901460481e8101620341c224240b4550081e1504002210040204001c210b000c100c0c09c2c0021010a810b50011a041e40c0c0c0c00c5d4454410120040900d911040c1d1900c0d680d100d01c00c00c102c5650001034408080311410b903155140da04030301030b48070004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115046807 1250 115045557 115045559
    0xd0305131e0e09060708131a101205150411120a0201120216150608030d0504200303030a0f02210906010801050405060f091203040809010e03010605010504050d06060e1609 75
    0x20010801a4030484224001d00043d070307945e841c00c03202084010a90350040060501c1800403c2c620400b08582090180f0300102d00e0426140d0000c1081065004c401061088010740002480104142c9074813180d0540c105080e8076949010b001303102041e4407950f0010a2241034554000000079680540c5000380ca84404100340046541c040e40f003500400c1e0181020440700c0b000041015001c2c2d40d0f041c00c0c02c030700091f07543d0b280c104190842c4d03c004600368025450b076041c041400654094190a00d4081d580700c4510092880480d480c2c3c0070041040c21255984c401100085107039070103c80400d11203403814140d1060b000701c00248a041500d403010395105210010410240501c41c1c14061a0801b000704490381d620720081c0d01400700180380901a00418600c2c050380c40c40000a54040d51041e4030440c0c0704c0395203000043c00c208070380350098403c0c5e042c01c20810099030000c0881e0300741d9605444803900000141014409015194000340124000d0400c2040110199100f02190482c40c1c1d40e0785112 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115048057 1250 115046807 115046819
    0x51302120f01051008060303070b0103120206090303010609060c1103010f020a17070e0904080705060c0304061b0807050d110a050c070b0405060d02030919030809070501090f03020d0305131e 83
    0x1c58000d01540d5009a80303030031114101809000341540c8050001c04481c542851517942c4645a00280e1049501803c05c01180310f0a03070f0140503099004001100039811580750200040c00d522080c4290701c14801c1034941401804000600c0790b80b81000031700240008500c0011039070095024852540010b0510b00c00001c5185500c91424019038250703840c04501440c1e02c0c2004480321000d0320842d43c0d584100411000114180700d428802d50702c85100c0c640303e01d0541006000e44064071641d9100440c900c030030040700307504a240c2541044d120728144c0d4640220490b041d0081c17084848030070000c1408a40b403100d0f25808070007011500860000c0d01c0c0c81036a20f403c0b8603001e00407402036a5001d28180a040c00304d0407246e0107107500c030712250111446110594540840c40214040c150000f58142d010490f801504006000c014202031814040c12490b04101607500845804000d1007030410310014820700d0b208a05541007400e40e5841035883c1c80d90b411030360415a040d1001d80c8540e40d070000340000d003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115049307 1250 115048057 115048081
    0x30e120304060e0f090604180b010f06080c030f0103030f02100509010209010315030f06050a020f0a02010902031b032a030304061d0d0201081612020d05090c060a020304060809010605130212 83
    0x6084c03006840a00a03032070328004c002c0540016003503c1c08403540f100d4840041505504003e0007840e065486002a0f0b0400400402e140001805014030410400034801283c0f1000c04250444c1e1b05864040c410242040c4100d041080710181d42010070708020030b01001c10b00c10f500178103041300240c800b084641b110f1100404445003d11002e0110120390703200c07001003046600140d40c0801542c2005142107000642c609258006508240060703544d0301c2c031101141010013100d0f00e0a0a2890005d035581c11070000280c0d604004c401240302000c0d15072015040c6525801c039140d0b1004014152600c41d603c8003801000e0801041041003011030302a480c0a0605249004407415034040e910786a0740e94072590340b80d4680000c0155070040182034880002d00c115140b02800d0b94034010b29000c1110b05203e00003a280010407005c01e0300c108400c00607101102d80001c00c135009c40c1c0329414a40c1c059515004000e004002661002c0d4002a403e4007500c2d5001d510303401010503402192452030140c8509400030302c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115050557 1250 115049307 115049329
    0xc030d05030106030c05130602100b0405090c040b030f0a080c06010b03100b0a0c0503041806080309010512100f1203030c02010b030c1309020409050c18070516030e120304060e 77
    0x80828000c2005000e89486504403486900d440d090080c504200c9100102c0f100c040b130341c000740041e00010192a451070150003004003550b000ca03418022800d061580546030b025036207002d44102d075101e10100098801344800c010311064042510310524a1741050f0f901e80e400840c0800850141000108094400c4020340b0302403400210f0030580d1030300b8621401c00b00c0c0c0c00b05140c2c50520911000903000074008100500c003412590b40e00c0279400c00d00d400c18405550a0341c1005a00d6042032207804110f0342d10a042c0e4203071303401042c1008280c2e1200c0e9030b1481d44040030340003050340900481d4041002c41d1000380f1050054826641003006d084c60003012802c0b20143ea86080d03054000c0048080e10345012404904d540d004100d00103242c00c0da6a000804036110b0500450b02501f007101b8401c01031030704400c800200b510b0203000400529207090010300707900c144010350784250810350181c0e0903d4450726445240d807001802c82c1015407031480e801c0e0740d07a400070b01c00d2400080c4070109800307003400c166400503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115051807 1250 115050557 115050583
    0x50106020f06041703040501150b130609050904020603040f05010203070206190c170a180c060905150d050c12040308060f01090f030b06061309050108060604090203060f2203110c03 79
    0xf11410030344c1000344196500150095a03550f40b60250080164015101203004103044283c0329503440d90001180c00c81e0000368030840c20700c20b042400708000c1d25544e40743e690069040300c1c81580c0e65290701d00600a40311034100a060381d84088100500b41d500000c4485c0203160030b0f001c5a0418003100e4620064a0560303200a0014a80c4030303415000c50b0410b1903182e0040102d00e004142c0380e00049600e101c07034031440350981d03081e40340304001c05c84281c0003c01c600107400140c81040c2440d84000c80181188155214a02c1082d500e030001140b0f1881c00050b00c00000d503c0e0302515039400e080c200105604000d9901034880c3c48860505417556000d101c2e600c084410b1845907030156071840d120411403907402400c194215004210781c071351a19902da5500003600d80c07442e00240b5941080e00c100c0c90002c008008900842c90001500c02694002800360b41c0600d0b04444918140d80b80086183c00d08041c101840720fa0b100c0a522074101074200303c5a00c40d004008041f2134a152080007010b903900d02401081d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115053057 1250 115051807 115051823
    0x20f0409050a0b0603030d090c240c1e0c1805060a0522060b030906040c090513080304021809010e01050a0216030f0c02130b0f01020f070b090a050310050106020f0604 73
    0x81d10004583c01c0169030b01c180c00900360303410311803c446980705584c8030010450398052090014072000b00c2c07003410030358420072860f54142e20000800d07000c1c0005a0100c40035001104040c82c04032608c069241031000030703521180304003a41e0f503551080c50a818044c10380610950800d000220315080a800c07400448070018510303100041441055101414421040030401d41c50740004560380700741c1c4004501524090740104400d15180c00c18408076540c0340c002d505158109018048140d5a0804200c034041e0401440b075038030303120341c070014440904c49507009500f526100200b1100c0b100640c401007002020030000d114665032210a00b089200ea0501440c0c0b507100031202d1000710b8410580e01c00d00342c0307941c1000001c092850f00011441540b800da40341c0e505480d240c2a6940d418141182c0ca0225020b0004050031400280c9440d2201090f00071858042004221080942e96103220207004000140581c0ea01441c414140c10240c00c0c240203503005403240640041d12800000707000d91284d038000440c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115054307 1250 115053057 115053073
    0x90207061d0330073903050307050c011d0106060c0803040602210c1b0309010206011401120f02030403030b090c07080306010c06050702010606020d030c0516060204030807030c020f040905 82
    0x20b8100c901d80365084100d080c0700700c0e480b03012415940c083c0e0350b8090302854507480c4491100f50350400b02240345030b10600d5000d20010300b461480244031100078000e541400d241e500c0750385c0e5040450f564082c1c40d480c0c0c1000c0d820610116103804203405242c40740070415000340802c03a00c4180948008001b0780e00105540300400024001c2a940d40c0038000e44d40d038020012243c2c1a622088501d940c134292800c81d03a2030b00010b54034204c419400c0b5100309a46458010718100805040081d45405051240d80544000c0c05030050141e842220310140310305081504126038000c940310344009405c119400c4011900c0c04844041c107150105030148503008204038240380078156502c111f0540c00240c4040c0c180b10701640d100e0006801801101c0c45a20700358000900075150520080c81c0c51900c0482d141414584a8558400ca90140440e49290070400c0496161241d0b4076050000f8842da9002a00d80e98000c43d0400803d40c0c8482a440b42c14000c545e0b06480c80c1c1c2143c03c220480b00d907220000c143d544a222 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115055557 1250 115054307 115054327
    0x60711030301090903111b1311090405060a1205070f0b0403051009020102150103050607121503020904020d060606050c06100f1412160305060f01030c030f1b090207061d03 75
    0x5106052286c60700290a1030705a004524005801203440c01154044030b10190600b444032000007100b0740120103003c988602000c080c500d100e920303440e41c022601c500018040751250f241040c01407030301282e50b4002900f0360802e55110540f03409805008800c4940009841c00c41200341c1f0309981d041000341161040c5e20401100034000217a00301c2c154010030111650410302504d00600850099014000300e1030000c4008013070480c40d1800d007442c0c80c035000c4088004481c40d14504147c9505541c061403a032901c1c000900a1880303120000c0000e41000340110303407160f000700a00003001c50721084464548400301c1d4000c203d8500d024442201d5441e4004100b0002020010554101d010b4a4114000d5070ba04007a401d02c0c551546200103070041100400c00c2007800c0220581c041c3c0346d080c00a0b150f5040d40e5403603800d00b41c40c0c403028105020850010040c0100082c1c5201c56040b2100b04010701e0303039140f2a05001e50081d8505841e0a450320320207c040d1050200408003c01290700518944074447d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115056807 1250 115055557 115055561
    0x3061502070b180a06050414040504080f0c01021b0a0c080724120c0503070f03060e130201110a03170105120c04050c04170106050f100203030a0207060b0904030f0206071103030109 79
    0x341074808a03c142074846040341c5540d10520007805480c1c2c2c429540f6130810210034038580b00d14074850701079480d00d020403010518540948140c0b20540781c0c07141d0341e0f185000d416070190085d07164410422058142e000020720780000d40c000000d22500305808510380c1d425905403103a919220b041012000044a07112141e24480c00d2035490059083c209020142000030070300311400c40500b040818000800c0c0200180c02440c4030800c1d0000f45404e0101d28141540eaa110820244c82001e5105601d0034500443e0300503161052040751341d00440744280a1810001d01d04400c800c02c0421201b4500b002003014100080664808004900102140074281d010300005100040c15804c066005000205160011103403450076081090b00110300c040c100020000740e0100310202c18404c0203599800c00d0b4898020040d658814003d050058a594060921710003600d90300b4406030303004034030900300010940c00c40c0c000540c0c01455400c0b12708594070044182c0300d40320b440c0200036441e441440100070081e055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115058057 1250 115056807 115056817
    0x3090a031803150c11070803040b0d060e1005090a0b0108130203030409111e040f030609031e0305090607020d210e2a03010c050403110d08030a090303061502070b 71
    0x80c0001d6901d19501c0e22585420003502c10140d00d429120108100c0b09903004100d4103800c20f03e940607100c1285072001c0c03240e80f031140740b00d4280488404110010454044da100000904d4680e900c5602803030500715004d441800c0d4011b2a110300c01d64808102c0c14a042d224840c80000182c440300c0c21a2141000096265a034180c107d03407520040001042004041c010703414441c41141e09613803070b8585101c0c074903400f564000e00c1c8000c25409001c100a04001d041c03c0c01d040701d40106000803081d00d0b40c20101c03104050616182542440c1c0030380014101e03071691000f03120340c030540d0555642c0c4e2a403410490301ca1403400789900005200c0c2240f1514160103002520402902c0c10b800943da40386000c0702810308040c1c0083c0c10a0541d16180c40021641820b80030884d05e50480080040d10f00003a00600280128003015240c0600c01c40403c5254036001005105142c00020b5181c40b86000c07808900a0a4801c501720006420140d00041e0741030003240c11800002150041e04410b03040510194041d001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115059307 1250 115058057 115058087
    0x81f050105010c0609020d080d060603060b0304050a17041508010509070801030203070b1804060e07021203040c060c0503090d0c050112020304020d030c03091d180d080127060f081203090a03 83
    0x1034482800c00514088c008142c030807614140840d450303251000203002c44010b6071014048a1080040100103100420b0a0081075400320202c460b500d400103208203603000f80d40042c414520061240c800320364000ba0080c0c100c4808481e403c0135940c41c07403011940208284002509940460700a0020111400251050140d8002d0b410109680701e000582542d1250380306016244102e0306000e040380c1d041c003000961100210040d4a1070426075101c680c12100e92142c01c1c00c100c1c480010204200c010700c203c030040780300244980e40d2903e5a090440c002d81e494840d560109010a1540300711500d980260b9104079001416100182c1140d282524881000e4400b202042a0440081621410005002080131240e9801c00b500d04d0002d2807020340e00d20604c0b80e4072540c0d00840c2c4410b0003503400f007505415560041c1c0f8007440c42601010090401450440c044602400c101010581d800b22244050499003200c0803034841c0d500c034411102080c03000f84c4182540d50405003060010a014900381c0300300800e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115060557 1250 115059307 115059319
    0x601110a020915090a0b040605030d171905070e04060503190f14030c07051903120e03030d0c020105190504020102061b0f0c0f0114090a0b040516081f050105010c060902 74
    0x1e0074000044c1943d204543d800116562080400310900f01442004040c1409034010009c603d440c1c0005400300f001c4254005803400e04200280c400f500d0044001c2402e81e0b0403c0610903030500c000050700d400740c0c0204142c01180303403d100150500e070000d4480011a41c03450358460440003a111845041501c8070207a802213a24164040c120001300001e140002424010b82078160801c2c08010381c1707108250b41b80d1045040c4000910101310110340140c0c4106190910780312480e54000400e0031405012102c80c1500e01d0002002d050310b8064108512500c80d00d10781e925409005002031080302e4080d0b0b0b01078016403080e00003d0003206020001814403c075000ca00c0c1c00c2000a0301850a02d030f10a00d16a900d54008080080c1d185000740125280d010b0b440e11385600624100303962a40e280b00880c00a030100200c0c3d004078040c004103000c0d040780380c0100e03550144019107501c41c4d2542e8855603800b114426040fa1000d0054801c24820030b4140c4005035552138800205841e9800078000704001a41c2c004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115061807 1250 115060557 115060591
    0x4230d020307030804080d05040e06010804021305070c11041a060c01060e04080403031e022a0a0308120f0f070e01020309030d09090c050403050d0c05210d050601110a0209 75
    0x1035010026100114410380042d5a05c0341041052070802404000c2c03041400003d01c0244008a5007070034580d440402803828040c01c0ea210300018058048504010140318500002e010019600510003075040e40144860b41c0c6180c7c821080c0001c0340c0070301c0c001010914018400c02c0007440c001004000070088040042000c5071145e042d284c14840035282141c0000c00080c0800405030000d21003c00302803505402061049070b000b001e91a0341c800d4810001d061140e04102d1410051008000340d00800680008280794982ca0004181e504c03003400034841200100018043c55140d03241648a0254140c001c03a560301c84903002d440c0c01c90b6040310b580c15800300b4002d592003610304201c1e900b40c0d8400d580d07507098403600d032a220400710f0300c4415800080010400c030034008120300048a001141c01c40c0b0b0445041344950a0a6050050030741060040c100c402d6092102a401d0801401ea50486000208565181e10b00156000c040c12407800100380c01689a5002505d054030036036030310a91f5905c50b03007402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115063057 1250 115061807 115061809
    0x61602150403140c040f0e0601090c030207141014070e010507150c09030309210b090319020607030b0d0b04120e030102040303050c07090c05030406020307030b04021605060c04230d02 80
    0x4180042c1d20f000342c035400300380d06480d0741c42e160050181400b03945904110000c030944803562101c07014040d05000315200c001c4e0140041c4254112120190095544c9010402d4003160300d07100c03100b201c0318007401802d16040000700c0c845100068085c01d05a2200115540020019034003a04880d0054400c40110052415003804500401508520f60f9580f10f025034218580580070200c1500300c02c007540b00181010750002c0201060080b01e0350401c1074205203a40e04070b0411710b588280318005402d41880030316a032999800017013550241341035450a11071840c0c014144683c40c601384034050650480c100c04600410354540400ea40c114040c03a01c0c1c40d0084070780b000b007804c1e80d200d80d004030300040b070002c0c0344007a80900b4021200604068031060101d1660910000c00b01e000c05040501510350000101e9943ca009138020008400058030a5481c0e880c0c05041c41049849420309488602803080001c14401c100800c0340c050b550b210b014900381c0403944035110800380caa0400160440c00c0c50202e4005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115064307 1250 115063057 115063073
    0x2060403060e070603020f0405150702040207080409060806041a07020703050601060c0b15060306011202121312020d1d0102070512030304030915020309014a061602150403 75
    0x6140034000110307041500202c101c1c600032080e4861404c151042c4003e410054240085400722141100c481100030102e0140d070609102c0c440000350300038400114007003001641300181040b240c2c860401c000159440d641c46450b120102d90080586500603016070144626069454000020303104482240c0d4480c1e803144c0c6010800e8100401040081340d2010400480388002c03a0f00040d88420301918020311400701d102d900019046a05000f10000b0010b04010642d059500c1e0101907034600005043c158012160340f241341c41c0944030200441440341c46a4000100307030141d8207065543c00c0d84034010111101c00cae241c14a035000c0c11030140b480002a2039680c490a0007480507a040035668034140340c0340c090602038840c1c1c0f0030784100c4818a091014240c02006503034216100b0309200b8052421001c1548001e00d190075106101c8a14030b0b4114a04481c54411076940c0001d803000700007089072502003110900614180607244d02e1400da612005003030052940110401500201e81019241d03038681e65 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115065557 1250 115064307 115064309
    0x91401060302180a140f06041202010806010c060c09030210020303070909020c010204050603090d0206010f0303020a03121d0a02091b03043c050105010b031e092d0709060e1303020a020604 82
    0x1850b0406010f24051450311b00d080b00401c1e01c040b2a00c5140920703150741417a1a4401480c041d051040b0a40041d08990154418003502603009004020f110020b010151041104d0300082e400703032501103081e4600c2030001040320702488441e152816200d18001d003001c0a0340c0040e545038800e5400340000205600c0e21006580580c0d03620b0301a061608420780001d1030800140c0c40640340e4091617404001107500401e254810b40c0d007616220246001c0e071000400907019810201c4451803041100d40610380002c06c400c020140300b11000341c0103459554a9001807600480c092030b02103000c001240c001011100c0c2c260703803641d0315140800c03c42080c012040a0300b80020248400030195035a41c02088000c0c41140e014241c808426421428252080c15000c01d40c0030355031000b061050045025034808222a1383c21030b0b00100240c1281281c00d40d4003c0e119030003821780072075108050020854074190b00940f010364041100c62191039486928150304100c0843e81a0154003600041d48050788a41000304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115066807 1250 115065557 115065569
    0x306041a1201021e071e050106031e060c02061b070f08120a0609110708090315070f0e0303030702031905040509040b0f09060709060e010e0901080115091401060302180a 74
    0x141c0b21070040d440000e0922811684c16582401080010001809510000e42001c0f03142c6480003460308030300d001c60042c205174002901a0080382c080d100b03540807501c00c1c039560034800c08007444074001840c0142da4600c2d05a512130854020100c540c0d02200e07034000a404258010520309944180548580340c45500c001050043d4082072420080302401074002d03100240f641c40c074100007000306101054054022020000c0590f540016800300720b03501000300640e28925841d4095050a2003000a04120710b100100703404280311224a03030040c40e001c000d40c2c3c4180419009145454ac0c0e03240e10740d00c4441000094420301c00c090102040c0f0b601d0741c10b02d45104910036444c80b002c6003002c41030116094401403d6940c16400042001407003a4803a0300b03c0c00701c030a58242015030300c0f000c03030060392030070f000310034041c1c0214400c0e0001420303000542042e6a000300e50040380701c1981c1c841c1c51200c03d49844280706200c042c004c000412195119500070100665500103414005005800045000070325a00030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115068057 1250 115066807 115066811
    0x31201060201061e03080f031807080607030b03010b0319080d020c030a1706130f0603061103040201110f032a010f05060901060c02090a09050a140d02070504020a050306041a1201 78
    0x103024408580c0703050301290340d060013542c00103443d6666028252103496a40c1d520440301102056840500880c4000522002d1056500081d2581a625035984040714000e0000782401210b22450406204440d082c1f503000d001340103040640c41d80300e41005803142045402c02000c00080824451a1000c0c2c01d008511501460742c0d040d8000380180050f868458496600000c00b007403082a540301c0042d210b0f0090010340204650640ca09620700802d002e61014008030700b04124065120201e00042d0711591003620b440d524520307035119455503003d51030f43c1c0780c440d6402040348000f00d4400403000041c00f0002c4112104010031407005909403074406180302056504d0b4018801c141c901007202d5405402a407500c0e03241e0200c00c5c1c00203030100c800039207240724a955035a4200c00303004c414030261000b030750002424070b120700521105541e42c03405e03420340c0c0c001030041240c04506440c6c1402100e0583d451380d91001d041d0784030002004000d003820340c8000002140e0703241000e003640320200034a003042e07a14800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115069307 1250 115068057 115068059
    0xf03020a0e06061b010605100c0203010510080303070806030a0c08030d050721090804030209010f0e070e090105010809390a080d1211040b0309011803090501050c03120106020106 78
    0x5206464000e5084420a854800d0402c51a0380352a0705580d0103d5448114180b5140642c500304d0041100e0703000709800c2524214040c16050f081001911050310a40003004559954030601e02c0400a0340075400352500100085815544200c682c6504020028155650052166a021020300300303503210b51419080031500700c0715030b00d0502c41d10740d000c0a142442800c84000c48043c2c1d0a06034250141100e6075504c6030300d08103001d444006d5801540d8054420101541c4510402c010b6440c00d11421040d5031280002419983c400c5022081800000e0900615a400c0000654130a00024095000e078800c0040448043c083d1034420940031020140c1c2e00446002d20b5240c01214603046495805040c881b0000c001a01c030024403402034412a00d000104489043d4512000d840d01c0f01c3d2903401300c4030204003c5441610710340110b014401c200020003a2500c079180091000c0010305000d4042032900742e0802c02540550002c00700500060260792800ca503841004d1210002a013002c1e005070b5490350 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115070557 1250 115069307 115069309
    0x28050f040303051003150c020f0a0302070302030609030403021509121e0706020c06030115050f04090605040c030506030714010309050304090c020c0a080c010509120f0d08011202090604020a180f0302 87
    0x11a007130b080324110080520450031602c5990909040c0c00c00708007002e9444841c030b02d840e8402d1217040340030510501a500c01c00b0740c42c100203580d6a002d0000ba4481c0c0106c0c408120b0924002085800700c0c3d60140c01c2000d0701d400d502002c005074001c1002d444e040100308241003805142442003846648841ea441c0402e0300c14020690b29065058100005643c00311a11207401da64080070750341150044845400048803054007241c0c90b01038141740041c0f0a80108002c10709181c070350030030015200300781c6d0100003441d0001e00403030503a8403d4a2050b0190440c5c24248685504d14002044511040c10041116840340da03442d4919400740d4441903040c0d40c0e40c003420b604154184001025018102d58840c48641041005074841310010241703414404005030300c00c441c0d145d40d0318101915162105540e05085210f4290b52522581d060358400a901c03030001080c3c13183c0c00d680d00c180c51078000e1304031141940c5c5d0710306000c02540711116541c00e00844603894140c207400605500301814148c02e1070b649840c9544 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115071807 1250 115070557 115070561
    0xc0c05010b060703080c070606080d080a0c0507080901080402151c0e12040e10030206181003060b0a0c0c090501081005070512190e01060801021b03030601020628050f040303 76
    0xa1074462003a40204054400f0aa0041c00b0582084035004007555a082c035190007130080c040c0d41e00a03640c6005440380c4401c05600080761034032070540c159003480521000d02007102d00d8483c0c00c0005051000170320140d44c0135445144031540c4184003074001800541c400100c815141c000c151603100103502d94030442d61103003090141050340c002c0e0350000c0c40300451034000b20b002c500a40c042c3c204000106800a0a04140c0c600c0308002180c0140c0310584d01c4c0d2071029005c1070b4200009503a03000e0902280c0c90050709110b44546000c81d0503c0410ae418480400c60403180829590b1055a50f00e044880100d822600d40c4990340c001d10300030004101c0c0b0418040fa000c16034138020030319000d00005209040c541911401016844200e50b45d69003924a112181e0314000c15602600560562130680045040e540c158000e00740403031012840320f0030110b0f0036000c5036240300c12a116401030700050081502042e645001344400901118001c0020001c41e0f115022190304892030b100503171118050009047d018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115073057 1250 115071807 115071821
    0x301090f20190611030306180910020a0806090f0c032e060c050d09140103050601050d051501020f01050c090f03120c0309040f02180105030601180308040512060106090b09040905010c0c0501 83
    0x1342000d50308500d030076000200003a0f0041180c080c01043c200c00200078140038050540d01e8441c40030115101c1c043d100c0f008101e0001141c0313090184088030b000c90038003060301185500c680e08117182140b03542d403040d0080700f82d54a0102c81e0083c460b0000680d103d144160000c4002500090b980c0320100401130500c03503c0c103044404100248250030205128904060944400d070b000300382000b051603162140100c2d5a4400d00440f900928a0202030040c1e0a11020f0b0880c0075410076400c480403014400080c0b8200c51058440c5c412403241088000d10a050901c00044800001070a48000c506216441a602e81c862880280310b5000055000281d2030f040c0b140d00502c4442040441c105940c003100000916a402449418041c1c04000110070380e101d0002c0030589880352004150300c80d0340b86058695178120b070242c5072041030b00e1405010704280000e030460484909640d1001410b06d0803032445043d130703c0242d19640040d160b25125020501c240a03110007070110741e80c0c4004029140c21b0141c00c45e606 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115074307 1250 115073057 115073087
    0xc0a08010522030905060901140c010e1209030307020f0d0f080307020d090302030a030305150418050606010201020a14070804032001021209010e06030a060f0b0a0e0301090f201906 79
    0x14100c2c5841c0801d40c00325095003520381c15600a47e40d0249100166070110221150803085580002c641294174410b4001c40007083c0304900315403000c4006500700209000d81807159415034018401480546813401210b250140d01030900358840c1c080707480b80c074507040f0020010740b020f185c000240300007d81c0c1041088003404071841c01c00300107410340e40000c2c1c5413a07203c107001d030070582c90302c01103103604801c1d89800714000c80c02802000349188100c0c100d40f0304d40305404203031800c0c06007030000f594550041c0219602d035055075840010040402d41b6680040e0041003080d6061b2a0038040440019a40c8442540c1010702c016000344210788900020300d0005034080d2a07501c40c0060120704a980d811400c0c2c0d448640089507625165078070031ba01c11000300119486442d2041246c000003600c20204002001a4103483e641c00d000310410005240c281c0d04420402800c1d810040c0c81080460802c034800b0b41c0300c0d620303e0003e48041100e240061514502c0700814401070200050401032550414400031840310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115075557 1250 115074307 115074361
    0x6060a05100503060301060b0c1b06030c0f1608120105100906020705060c0f060f0f090c0108190b0a0e01060306081f020a0c050604110a0603090f140c0a080105 70
    0x8180000705a01c145581419400c0c80408008600103070740a400c01c401401c20328800340c3e26140c4050107182d954900024400702c0420300f41c10040306040800489206002262110b407510a410194500320351154117001c0300e103449800e001c00080d0390760b0700408182c11194240481075042c4010005050b20003041d2034144841c55104000c05c07038010580c0e1044039822110a038855102c49090307802c00e1941440e8031685d00030f0400700070010709081e403154003400184d03070000501e03a00c140800e40c2c1c40d05080c0303e40340070071803500003d08602007142c15448201c100c5907000c104504100085030107a02c1d01e070000842002c080005107c495414803517a80105030444c0180100e00005040c0044200c03c104800740c1940c001815610950181300c003146c81c00d62241c119410741c5090b040501150075660480c0e80303d10380c06907000420071700c603001d05058036030010310722620ba44903580d40400450011030341b0303010fa0054030214084c030f0383c622501030002e000b507000105140c40c145054054110301000c460051341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115076807 1250 115075557 115075559
    0x309050a0210050f040b03091e06010e1306020c07050f03190206070203121602030c04050403052b1d0d02070f030b1e07030c0e0f0d020616080310030506060a 69
    0x1040000d29461154041d41c0e02400000e15000850742c0d48600c0803007101c900740008000400340a00da004500c100c050606a03403040f076a100081d112854006021007142d4040001031051103540d141290b0484a911503210f008280c039070b0340c0026600008005061508084020170460600e02c1d04008003030381c05c078007502054100c0300003041c2200040c50007a01031640450340f80119103007041050805c007030f5848000e44641034a14844006401d84e04200c0c028002c914150329507047c240112401158151189801d20070141c02454040c2e0380040e117400455040c44204c10003a40c20b1007180c4111148460001c0c04035040441245040c0c080c0234180c0866120141c100a688208120201525800380810b076840c0c0b1a001c0050404104c180030b5808140c00782c091007611074040c1c0c030a8820484580300d44541440348010802010440e4039a42d4111181f41c007000f0062902600401e001ca1085101d111f50b500030351540611a0412181d0708841c4c03100301d008ac41406070402c09250701132000c0314110b03055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115078057 1250 115076807 115076813
    0x30509030d0902060d090c06180f06050706091b0f0512030405120a0b0c0901110105010b030703090501110d060e01080c06070807053a020c061e1303060614010309 71
    0xa44901e040c40060300e03a4440c0c0c080115030311442101c0445031400c1003800340c00c00d18204140c04481138481c41000c00d4102203408194080d0b80e14100850760800c59102e5402d103000826122544880070442d540b40e41c86a440f000507542010400180100302c0501d0340150800300054100e465540143c1e01c55030700017018890000d40001220140c2d1030503580c045075281001c1c1d105160040c442001404202640700f00929000e80c0000703031140300026681d141d0508080e4918500b200c000b07020354102182e04100040081d802030b04842042031007000001440b1902502d01104c5030040c41d007520100c1d846407800c0007000b10180407035026200510142c220b9a01c2c0800280141c811001c00408a050100c0e03500c040c020203003e0100d0b418442c21501c204c12038044416034110700810183d501050340740d0481c05449100140c5486080005000d05152400800d002d02055500001d41510349404000030301c841c0028041400c01540b148901081450130030840010300e02c0d0803c80c190405280607064004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115079307 1250 115078057 115078063
    0x609050d060b150a050702100f0c1e05070b04080106060f05071113020c01050a0e010606080103020909010b10032a0518012307020a05061903020a0504051c03020706030509 75
    0x800c60380400d0004081c40a48080344448207201e0500f01c18280110b0030000d40c44c1c01070f006281c0c15201b1a401c00c60030f916000140d90701010075222400140000c1c1c044800580810b0701030b103413041086054044e03071665030b2b0741c80c0c0380041d2a00302002800c0041000c202c008424064039001d0409810400140180752500500e40e014060002d08100350055411007aa120202000c211143c3d04200790341c0d0704450b40d103d5020b00010f4400c4440e00e498640c0c1e1a00036041842640252512039441e084540d10b9502040fa17a039401501609055580d80c40a04845d51200040e00030070a00d43c40c04244084c1461190b00806000e5240610001020503843d80881d8001c2c101c982032a124540201d0030441040126018032128844420041c0d00c14640c0e01d40800d040701030170200340f0840b45040200e80307071130a0007098040c0b400c1c43c010503611404410616406a00500003000d00ca1510506040d983c03800291400d80f01d1740001c3da84000440710f042419818400074001d403540d81805e201500306481040d039 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115080557 1250 115079307 115079329
    0x6140d02030c09040c03240503120c0c04060608040308010f060c080711060301090b1e061b0c100c031704031409030a060e030c0f060f0103030806030c09040501020a09060905 76
    0x40080d50020000d04044004801d8440c00c6901504c100041141c82c0c0010b4007c0101c001903aa2070ba0100c040a040302070101c40c001c051381c40143c05450101c8254280da0303800e4100d041c09141e00e004507001e00480c1e45071442404014101680e554050313050906018003400380681203000705c400082c000f4040d00c0e8221036204d4907180c1c00300308181e880e0206c0c24104c540ca00103480159100380000b0000801c00d405804c00329580ea400c035100d8403021030412070003880d2240c1c0b88440790030501c02e001002e0f0038000545a00440b6404c40c054801c680c6103480058118281020050003280800b0342c2070003032540c08104903a65015082d4803a040b42800e48001d04240b04084101c0c2c980a00061030200d542c605010110850f5485081031006400340b1002e161aa0003000d4501e5161040f03a505041030400003854074010503181800907800c7e409e6031412555400c009045540511a420f9840e101d5110723640385500c143c0c001c0000580b0351a004600501e1051941e01c00c504004040f082848a9a214403c03a9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115081807 1250 115080557 115080577
    0x60b180114120f010617010b04090203061b040e011203090801380613140105030103030e040504060e06190b0102030f0d0c03110a02011509140f091905070f0614 70
    0x15841000400000e464500700c01c0311440f40d03500b0101700090541d200c0d907000000314540d200a0050b07440400c10310003294980c84029600d0790119003c1080c009001001c03184e991041c0d40c3c00c0e45003a4891204400302c01080c0d114007004000c20690b9420b03d03900c60050000750007600000c1c0165a0740040129451782e00e180303400444483c10380c200341168041c041c08810040c015125940300c50183d8900141d03007581c1c2c42202d1205618094251183d1b1050f000c40c0c0c16280c1c9a100c0c5401841450180700c0104001403045030110354440300103000400810006200f504442c0b00d0184024407801e030003040e42e0420700000d055500034040d011140c038031401038544c28a4880000624905025004c80241640c24000c104810002441c0740d01c00e030303064101d0040089211003061145a542c20350904860385910b01148414402000c500d40031803051070950419201070454074040640d19103c4241d42a03070b81c084401e070384401800c02c00001a004000c0040403039090011020207000090051403203003018035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115083057 1250 115081807 115081819
    0x140c030604110409060314070f18020c01090c320f0402090f090106090e0114130510030b01270b0a0312090b0301090e0105160e0402090607020d060b180114 68
    0x50720b5000a2482a5001020a060103024480e41c9040c521914443d450f00502e45028a0754042814a0304812100c01c991408810644079003140107400c0c0250424401c00d1007039501d03518a0804200320f21841c8020f001c5a101e02ca061301c41604141c0010b5826520242c11030b44140341844080c3d40340c1154000c108804e075009a5034101240000d103603131040a501c40c0c0d11400c01000841c0140d402110354040d42d4502c10f4030040c1e030b40c071803480c54038100241002c40da0240643c02c505401003040c1e081241c020b1070b419164106a0b480f584c0d2000340240980041d412942c400a1920201c000d144001c80c405640ea14100301405141011039150741590101a202e40641c640000c01a031046010400400c54a07801ca600d0b5612801800d01408840b1110016582800e01043d503209103d1542c06405046458001e440e10f5038106000c0650001e243c402c0c2d100304140080790240c0c88481d00203007007522805001500759814001c000203900c004255070f25841101005210b000d042084841a24000b1251 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115084307 1250 115083057 115083071
    0xf0b0a08060703180b090d020d03140402060f13061d060f04030b070212030709090c050a0f030507030f0f060603180c03020f0409080a0903110102011406100e0d030f03140c030604 78
    0x400310640e020132500800902d110001c0080b0a80080b40c1102c45252641c2911816481501c1c01c800b42c503041c0d25480d5078020700074003041c014075054009020550f000242c15080440304261400c2c060015800f02011444030340c01c803100303002034001403540074004407001400d0610502e402c88150003140401410305c054440441d801600803c43d108141d40b035060f0240e620b2420f208020450754252007680c05440c10018002102400b51040e01c81e060080d03983c0302c0403003500d083c04501501010740420103159450f4a054100446400341520a02842c2004540c07149400340050807504070030b0700c0b076004c041c520b5500300001da3308800c0d1104498040340e00c0303608010f003140010000e04a21000811400b000203c0300000c1e9002031a41c02240c0c05030400980c240c2c0f42c0710069082c0c844d0042c440c04504210000250703940b91180c00b42c000c582c0e403883c214021941c00c0020408501100c0070507404a031201c00c00c1c00d01c6d154076000d800c0d0010500303a0708039480e06104105180e10b0001501051140b40c441034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115085557 1250 115084307 115084331
    0xe0708061302010e0904030e040f0c05090d03030617030408190f030804020a090f1508030a020c012001020f030f0c181c050d0c0b0901020910080405030f0a030f0b0a08060703 76
    0x42104d440004084105a09045c07402038010407210302040d00450403e501d0940045503440b90040321400740c0c03203ea01d00340003141000100001c0000803010b040d502c0c20041815140d400b29800d20a0301c000055907160300303010311580360038040e860f440200700000c49500000f810500d082030700503a16040c0600591903a02c00184160314a0b00100c00c11464001041c0d00000c0365000858442c59902c4100111600c03400280d84038441c0b9014000507a020001100ca2548a54290f031070640c0b03032101c03010384030700803913940b90a82e40704040704081000d0210a00c000c030741d54840160f0300500307401000351400a007502031180360040c000c2d4191040489880740d240d06000d0504584109512100b03960700d8060a5038042c00060049005a0352481008001025034030140f08644480e0f000400d9441e4220024104480c0104010000c80d018007051102c2d5541942c0040602101e801c1514003040c8002034884203011030348c220003918804c465142e010082c840c030110700d03241c00c109146808200603d22031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115086807 1250 115085557 115085567
    0x40507030807110316091b0801050d15090b1b07050d0311132309010803030c0c030f030108060417030709051c151d16050108070c05061303030e070806130201 69
    0x240241e014010146845c007020320b10300b035100c10303501c84107010495021030203007281015030030310600c401182c0c1da2401400a0702d40702c0c1130000c003588185030040c2e144da00403554900750399052904a03074074800e031420310854025000c0300ba15500c00300340c0250308007c0b01d5100c8981d501d40d10880c4d2410300d42c1d282c483d00f5010300010215a031090f14055049006981c070070305104801ca00321950f1140350031040807a926480e240010604a036020070056085454400794114070741e110a5445107144020011091100e054001a41c000c0003680080c000c2450306040c0b51141000750000102507003010010440a59080a1703480250f8034103440c0c01d040000d00780071010481e1506d500140c42190288503000c4502c0d0241c2000ba5000c0c400021076201c0e4002c00f220555a41c6072090307545a540d580742043c001c81d4810300403140e1160042c90448040d51003610751a0406500303840c2028024071012902081c540c15025080341900500f00610440c1d190810454642401034142c4c465400e042d0842025a03100d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115088057 1250 115086807 115086833
    0x90601110303070f0c0b0421050405030312060105090a090603120c020d17130f0f060207030c120c0506040303030f1505031902030f0f06071b0206041205010e010606050904060e040507030807 83
    0xc1004206c49042c141131154802ca01d00c486002c990185103007a202d02841079003580e0488101500a50600304060071120140e0002028181003107024401480c1d542d4a07400e4000040c4200f07400054800d040d410415890044c002020081c403002109550058443c0c880c680706140d007001c0411121803a1858aa49a00c1400d680e01c0581e42c00c40300120700d814144100030125240b42c080c2c14405540c03000103a07102d11441c44060904000000100a40e003404800a45140e216000c000d805603241c00c00181b079038100c1e40007030340000e03aa0f05602d07003060b640e8400c281d95000010300d80106140b5202c00240e48088030800030780d0300c0c00603070318241c1152410000c84000e52800c02c01d640110f0341c1100600c0e0390741802c95103180024050703916203410070038400b0110036194024050b03030318080c2407681c6a500401c05640440320b030340d6200312001c1d00d00d40a100b070a0240401744d4a49030b07608030f007038100310554125170000208100d107001444000b82c000a205d4088036846000c140d10b500007400c000311041d00c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115089307 1250 115088057 115088063
    0x90201090e091c02010b03161a1b070f03051902031e0a05010903020c0913110103020307051204050c01030e0c0303090f01090317030a051509041704091406090601110303070f0c 77
    0xd500890712195010f4100703640f40c101c103804441400c806c0300c07085c00110265126030289d801581d0b860803141c0c80d951005001c001d03400c06c078214402c510700058903d4803c69034052a81810418000e004100091040401c0c8100c00c0d850050000000e4000a0710360414001d075202202555910110b903101c00d1084c4601550080000c05c00d0000c1820080d485031540c041140c8143c0510300054000e040300f00383d240c84c00b0b4110324506d9000420340f006400951001e000c0d42c051010030700401c40c0780e12403158114411849000602042e128a000141c25924006881c00f92500005d80c1407225031000030689140100480b6070258503488039006079031030f044640010784080c001e00300601c030100403500198045c0d140d0300820270103542c501b510144d0441d0381c003842c950701401c0a07000c0b40c0814520400444100c900000076441c044d942d40341c00c411120410310315000f244030882040103d2034a0071803644d00910038206a00c03400307074201c60140c417844024500c105220039140007991192249168804c0c0c994 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115090557 1250 115089307 115089343
    0x140307030f0f0209011e050a03051005210606043e030709060e0d0b19020f0a020619050424020403241b02070909082802070603090201090e09 62
    0x255002241003e03500c4490f009010400c485405400c25060000c200c640d10f0740e43d6030302e41c14248a600210068040900071031800110031304041920380d41c90420844d001002e803158a400807141007400e0070007100600c5207205a03e80320018008182e0080c10341088116508004d1008111031003242e8944010012101c1d0180d004c0200034509030044601001c0d502c1917100c1200220900040082c0d820b0558002410b00d03203020003040520004456544003a420400c0c0035041003410036441100c1d07000760310500c0c01a402101440101a401021100c81101d801030034004c070324007078840401c1c4107003009a03902180c241d6111006680c803568141e42c05158000c0303aa041d00f4000640b01204154800342d61500140340032880c14418198545110502c07050781c01070040ca0303243c50030b031400030012118141c82c2c00d0030400a21600820b0828848110781a0394042c84002010200007490030045800000034586840803403000b5030307082000701084170405c00b8000d9250b0345000880d4240030384840c6490f600c031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115091807 1250 115090557 115090571
    0x60a23070b07020118080a03020307020c060a020a0c0b130b070c0b0403240b030c010507110d0b040308010b030105060d020d0e010515030f0316020f120f010606030f02070201140307030f 81
    0x3001001c080d0244000368002d00607610144010b8440e900d074240c004103503c07000c01010b0a0035009801559001c4801c0c01515000141d4001181003070b03100101400058200206600411140c000341c0030162225448003810010500002c0d60407031040e0040c07064808e4007140da43c04100981740044060a810444591100c2d504d01c1c0c0801045c010036200d00903449403000d00c0360340c2403442c403ca5a44100040041103500390703680c01500d09601060081d24494210b0380a4501d5842d8098541320301d62013060f00301340c41e2500b402c00a03c0c0e954180c1242120107001c10040200c1d6650006450007501c4100700144d4682055a400f802004a40c0000c001e0394242420844280d070b4811200c51400381c150144c3d8910060349000036140e02c00d8481090905000c0272030407001d810028805101d090014200e02c820428500b8405d02d0b2500100c0007411b669140e541c10301c92039a260142030132030400c10009508201c0145e0001e05012041003041c050f080d0040001080d15100c2d8020b60641002400c00300608 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115093057 1250 115091807 115091813
    0x72d05030a05090901141e04110f0a030c0906170a0e0609011b0207030b1f05030708030703020d09060e010c110d06200a0813021f03050f07020705060a2307 68
    0x1c2e41084580f01d12070004a0000a1030300701100070302c80700310401480f685c0c40d0a80030079592a41d110701ca07105078021f90342d03461884808854100411990b425600722a403600c0301288000c09940c04105e0301c4e0200004450f04210260f00b041c40c8030800f0b1004449034040b0b940c0c919400b4002c1c08100e0382c48559104180074405040c4041d0700040d52150301e1855020707041c100080983e680d0103907100040000380401d00142e8082040b01041d0f00440d41c5821034200280d90b100003d2800c07056800c03030507035900300081040800d5010040c0c0030742c2d00b4031820494200ea00d424030240040605940c074a060040c4900780001700048106184a1003400400b80c0725060660f0400000030b04d4062090b00c50000032455003140f24a80d0310589503000314a40c0e882d4000c2d034404891000826512008a8002090788104669220800f0b424031780e0006994000485d450107460038502050050003280554000c50014410343e00c131141100c2c0300c3d8017941441ea00e07100c00709103040d03c000f11080206048400100e502420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115094307 1250 115093057 115093067
    0x171e0d090b06031f020c03090d051f0903090603020a0c0507080c2d011202070b040f060b0a05060901052104060207050f070b0a080a0b04050f09070605072d05030a 71
    0x2000d03014a500c46000e0b6224814181d0b0750201c40614034461010119450f0a000150014900c0c0d948840503241071423044c2000c13030b460301d0219904807865081201c5a10082b0f1000e20152460701441c2d00a0048083d6501c01801d640c280c2d0281034101a000a80303039207403d000e02c20050115900c08100c40010f5690302d00181c688206180e03052040300c5400d0907074001c40246035655a0021851650500d21800e1001960861f502440032054039400b80f0107580444c102c045424440d5004071005c1c0d4000809182c24012510703605d0401e481100100f2090041c2d4640c1d00985012802c01c2c02d100b42e40e10031188620184200c0c8040100500481a0400c020803003141c001d0f14480d0312810841c0e21001d18607991b0340d03c1d065030f809107041d008420b1016001c007a1003819081c0d0011006900001c065100d14046410b40354103d502845903030000c0c050100d445001c01c0344100030515880e03c1c0b800d00513290350311861a50320621050214403203406420203001035103003000c01140d02404a13581c0d002000b001500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115095557 1250 115094307 115094321
    0x21008090111030103020a0e040f080c03031005091017070314010902040501061106040f0602190e130207030507020f1215010608010f15111002040b120112171e0d 71
    0x21942403000b00707100c0d8100e040a0768141c960042c41d1010b001d0400110309280ca00050096506c10000d11405010801e000d00604407902c4940186607685042400d80315910015403140703004091365020014103240300c03c04070096400c4980c1c00e901c1040c2c407010040c9006003035040508000000410303585209015484002e41902c250303000d110613a6a0034080e01c42683c070f494007410b07d402c58000113001851300c410032064207114140c01410315480c900601032a1441d1032240b0080b441911421f605480c200e00c241e41601e4004070190320344222691300411502034030b907000340102e1701c001903681c040d501d203000e060500ba000b0040b5121500d20061046072624284219800301e403204001144808101e0008400c0d6002c4103021030320741c0c1c05c048080364035441103008148280141000c0f030440c0c001c903000920007071034807040341c98843c0c864200030300c001481079004505038014601c1c01d0340050030303507481120510f01e281134858030781c21340c6044201071305920305000701861000624500c2d0f03d40194003000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115096807 1250 115095557 115095571
    0x1508070519120f1a0d05030301030b0405160303051308010621060f05130c080604021c111207030303060e090d0c0302070509040b0114031b0f1c05011b090b030601031107021008 77
    0x7101c13040611060040041c10b925015101f604200014800b046034500c90f1504a4418011559221096112054507101941080340002c40000307409000e41c414614440161104400070044940b0f404020765004443d40d403601c03d042c10f01c001800502849038005488aa0583e44c18071136482c06480f4003003c5001d0600481d01000000320100c0d0003c00040e8040c4a1503024195540c1100702c502c10b00c8829003000c0040303c1202c072003003510b0410707180e4894580e031602001c80203080340e44c01c40c078000d8242c0f074980e04542901c0040e8020410020000103144c0d0086009041885009600f400d0490a196042e0032040d00800c802017404100405041224100ca00c0382c5945800c4042010070907403a041050380c2c40131004800302c00c450051a2620f640b079090b19004000c4004101005022034503500d00c5501600e8903592030701310300c6d101d10540e02204980216407400e84981800d001b141119400045d00490415a50b040070080445668040b00d03485500100500c0000c50308450045c0404c0c400c4400d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115098057 1250 115096807 115096841
    0xa03020306012604030318020406140310090213021c15030312020a0909020309190809030609060f04080d18060603030f09120b06281508070519120f 65
    0x14000019460020500342c3c1030321410b4680315181d68404030040c4c4501c0d03a40c00c5000c46900142c100581d100d1240000a02501079020360001c0f580040500784252450202070040c10030004800580d030b50700000707500d044080c400684800328685007090070014508043c4101e8a0070444146100e1007103825001c40c4d200b40d8070322544041e01103d1b201a400340c01c00180118000000c02e01040485030061503008101d4011107814a9002c94609030030050000240c800a10002c6c0c00655414244601c42d401210080289400c0c00d044c280035840d22801840031b400c041d0080b51390040000b841d08040851100010310322013408081c10503400801c910312007100460b040b600310b5512540500001001c8800c844136502c21a010750315070f4411840024542a032109807408040006940d40f005510386104a40440400a05201c804680c19400030600001d00000004211181e548042114281c00701920b24260780c0541c61800d0703c541d07440d010840b1800e8109000a071f40c496055202030160b920080038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115099307 1250 115098057 115098077
    0x902120307150b01021b131e050a0c17070912032609030702040f020403080f0a0e04020313030f1106150306161407080403020307030f150c0e01180b0a0302030601 71
    0x1d8108a501810f0300e68050317005920f00d24010f240c01b802603000c621003d001840c40000f800844d070b00b111500c400c1c0c0c6c4c004000001e0010402d071a1440745a51054205208200e40940b06801401c0c1c003850310500c40700c0f05a00c20015080a11882100b4010700e591081c0b805200113500c1e000c1e2000d402503c0c404580b0307020240706202c25440c4500703180510400c1002d58504007480d003c1c440034051031040080d6441e020480000040d410794000c02000f01c0300035280d6140c089120005000d803003036601640c40b50703005205200040c000304407007030100c6501d4108079980313040e1994256140014000303c0100c50281c102080000703410960303503a940c070310b0407000c2d56290340c0d400e00044400b41c00321040e500003840502c0b00c0211401000000e080d16400b400c01c2d1802d05507207500080c94002c0b950811940036610f1f50841040154000c55100184003d08050251424404008050149141d4810304100300c81483d0115404041e0441001e014001c1a0540d1480c9010029003c2e600030f070362075800a0840d0320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115100557 1250 115099307 115099343
    0x50c0c0117010902070c0b03070e19051f02010f09080c0d1e0806030f01060315050601320702031b120304030302031215060a081b07030509130902120307 67
    0x440c8880624020700d4000640d09185540b0000e410120046882e07550218010a61400020142d4030490b134698566000c441c000042c004145080401441c014181110070b025030340d07079050407086001c000c155a401038040c0c03010480c0900b51820040303c030540f40560b494203100600c5c00801643c4414030880f04481c61511044504c0750070240c80d0b8107081c00d000c003002051442690096007248004046403100c202411400d401c403030b1075a10842c0c3c4040400c8150720b0801641c01201d034001c2d02407c1144060084805402c0c28241030031140e003a2444403200c0600001050054904058001c0d00320390540241c0445907181c002100309003840366814045050411800000712070550358903a003e107082c510900c56100106002a229007102c2a10b5110361160380c43d00ca002d030505441990303035035160b0304090a01c04240740c110482100e614170304111400100b07400c036040380d08030b803c181c03248454880805000d40080820f403000943c00043d407440500c0b114800409803125500940c120b2107070003c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 115101807 1250 115100557 115100567
    0x3070e0415060203182e0201050112031e020115080c03190f0b0c040b07060b090601090f050105031509010314370f08040803071707050c240406050c0c01 67
    0x102c101001070f030003080180c0b03084204900c0d82031400006010b4100042c4620b11254840c00e0400c506844000226001076542c0d50902445006109000711542800c0c00e9850090031100d0342e544803150301001603258404640f00354455074001101103010861182c490300080d03164607007500c00501c240324640e120510302101545143c0c2e241d44c00090703d404a015607545284000c0010070b85450300d030301440000740c82e5048500030100c1f607210b81c00010310645e40c0d0040008813240604a18100b0004203400e011007592002c6600c1911024284281ca03070341d41e0300036180004640c8800070f402c010300d1000003041000d551441c0118807008010b4402d07605040466030f110b1a900701003035120706070003030942c0700d1411041100700d501c034040c41840e01105c85d00d440d5841282d00070742c40001141d00000361101407003034030b81340600040385030010586009002e0715083c2d520380480104501c12284114030004146505402c0130401c903403003030040e03100c0e6610303c00030b0229007190041108601401880c145a58421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 115103057 1250 115101807 115101809
    0x6030907030b01090c0e13020706110d0c08090601090f0209060c1507030509100f020d14060109050307030c140d0b0103080702010809010b01140a18030b061008090304030f02041103070e0415 83
    0x15038481406c000f20600300814007409641003080e6507801c10240e00414003e00601500603040b0081683d5260300c0700380c04040b87c081c0000001001588014011860401f107000750440324038a0001c03038000105880000240300303549100b0340c085070005503114402070100342004c07205940500710803103039034000c015000e40d50100c501003003907005a81e2111110741140e102440700e08103800c1c01414000040700c04021190340c400c204520014440c01c000312584d2044404c0090102500076105440c0707150341e031848003036550041400d61120b060403540d054a07810049a0303603d03008080c5250551b564148070302e56a2000c0310590000303500300000350708104140190a10200c045c0c2d94581044141c00d9010496000440c01d0b0b000c010f20511040440180800764038040c5000f00314400c041d013050010002e80032076400003603041c003443c00e0030031007030043c00b2050b142187c1d04401022020401840018018507070040f0005280001000f40907000381e010f4044103290387c0030348081040c0f59032241e0070708000c3c8403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 115104307 1250 115103057 115103081
    0x70b0c0105040b01170c190e04050c0a120309120314030f06040c140d1e020a0809061518070903080c031305010206010803041e0902030103050d02070510050306041a06030907030b0109 80
    0x1250003400f2860a001c0308085200600347c0003508207030788038104011804010354064445501c01c16a01d00545000c9220a008107100061004000080d540203800380e40320b440303420701007000b1690000a05025240351051610000c00c1c0e82da591511100c00340c1500c105655050146150a101c408658001e0a00b01d010000b00342c1d01e06c2c2098a60041c100181a00a09100c4a000084c1032001d1220450004d0100106a80c40d400c0051902c003010342d180540050403541c843c0c135940303c03a40c000e484202810081681c91000013225135100031094501001c2a8001860103000203480d07401840040042d000e0b140c24000313031442d0261f0b68001240c0e1024280603080d03080d04204403c010102480072903882070f0007030b041d10105480e680c14510b8103d800980c010b0303905400507030720324003403541c1802100054403040303e4202c45100e007400c1c02005408000d00c01402103948012600000403a0101c2c102d032800c005050750b03520b00d0035007545a00e94015110480340d040481002007484682d500400e0071441e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 115105557 1250 115104307 115104313
    0xd02060d0c0903060c05070302010b1e150f1603170106120b0d02030106030305120f220501090c06091806120611070b04030305010e06030a0b0406020309070b0c0105040b0117 76
    0x2144164009107100c030341030028821420000000228107001e180005401034032480e480d101c4504029094030001c10000f03118911070707421405404050130b41c1101c4480103070381001c40040550b6804005100f01110000c142a0104459264031440039890700c1c8079109580b4070f4003444004207420709054007801660041803400510b605680c200e9031051012980c002c00c0c26a150880b5000700b401c541c101c0c0c20a42c0082c43c00a41180305030303080c8111070f4021000d020010b4007841c04e102d0443c903d0076420308070303482c50a03c07200031014010250040404142c02040800c0d14540d5400b000d07194007681c0c402daa01c24043c40b01d915103441054411902203840c0c800101079281c030280c0e14403004025640809005060502c03003c804100c1000070b50340700340d20030b440c0002ca0754103041e000d01c00d01c04001c1807144a54042c1c0038850021350080b038242c0d0050741c814005610790300e8058005041c4246900200526003000c1440b37801008150041401140689501d00a81e602e0380d10150f040c81001c40c40b020964 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 115106807 1250 115105557 115105567
    0x303180405070207030c0e0906010803070506061c05031303030e010906021902061c020c010f06081908090301020c0c040b010201090503040e070e06030a0b09070503061305100302090906090c0d0206 86
    0xc1040d4200590001c40380c4151000940c680d034405000660f5a045101401d40500030000341410411403180035002e403800550902c0004d40d0340a580b844001e1455001f1900008a49241ca90b00d0380044842ca0380102580d403506a08440804400305170310040d0009181000c01a07000d500401c4003038259803035a4050f00203c1da0545c1030804c5051642402c0340c0180341000714a1680740f03d040d400f80c048584c00340140e6140b03005800e5609603400640c1c8140c180d40741820420810300001600b5615204808084020f000ca90410226070300405240e103415500010b104150000003080b03c5180400840f0f0402180b1408801242250028040100760f0742c03041100348041220341c591242d001c00303245413207000e9070000c401154280d001580c2c20385181da1030b00488100c0e0b1900101050344176040e4a81203040d4035000c0006001592480008010381d5692804a10000707510003100340a9500908030401c00d0601c003000c156a800201c454104a001d0840010118079000c1a070200180d00204094200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 115107913 1106 115106807 115106809
    0xe0a1502040b090127270905071701020d060f081b060a1404080a03081e0702060402060a030b1206090d03020418022a0304090605030318 60
    0x26005200900c4500c0000081e0341ca107903000d103807101c9020141001140514100754440300b2110301300c4400700c5c0060001c2070300c02c446078600220608a2044a0620301110520b14004000b500584070401c0342e441101d501c00701c443d08207000140740c0042418418211031142e40308503420f400e8840c0401203c401400305e14003000543c000c1280070314004000458600c146440c60301803100896444811b0941c10007942c0191203920f040b182d08494030304010b40091021100b08803c26958402481c6594440c40202e0260b103054000340441c2e1610380c20404150040c501060816680340c0c121800d40c2d40c0c3c1d0f000100180901e20150102e07003002e004007410302a80012407001e040c01007100b00145a060240c400361001000713001610740c0041c15404142c103902042c0c1440d13003400100c3c403020601000c80108100d031440c4208001c015030b1001495128040c10761181810035000c2441e54035 = true := by decide +kernel

theorem cover : BRFrame.Cov 114928057 115107913 := by
  have h0 := BRFrame.cov_init 114928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114928057 ≤ n) (h2 : n < 115107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
