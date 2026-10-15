-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4839
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:54:18.722165+00:00
-- url     : https://prove2.me/submissions/96e69d95-dac7-427e-a79d-deb5788fec9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 870143884 ≤ n < 870323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 870145134 1250 870143884 870143899
    0x80f0c041a0f1305011518060f14041a0705060702010506150f0409020a05090a090606080a0518010c0818030403350705150a1a0405060f06030a0515180a0911 69
    0xc00e6250f0410780d074504521034480820480d108502e02e461400c03e0b21603034000900f2700000c1d4141522031000e4141c045a4115000c1c127041e1181e03a1655014000c1c6040c607100c00000881004101c005e201d902c1d0b00c05842d0008105600e4a14089074607012032400c0c00403044400240614014008001c7d80e0140110890464495589060151490f4090100f40384900e400c820001010b0210b03001d0035060311001d946011198583d03518070b201405010340251205460007142d200103000074400e40301104481d0ba100c11700ca041a062000ca801e9007603401e06680d0300104402d00c081140740340500508050941d030103184808410070b41e03072000f0b501002c00078800d10010302803060100000780c2201034465400c0c005415145d04e4024003c81b03850f40000d0651312403920b501c032801d1807e030b849180e02c0360001e007506001401843c0040c80b00c0d4401c0319a6007e90ba503400501c14031a141201c00802c1c0a016a03003625000c1d800480c0100d4554000c143c810790b9910723030450f5020485111f0098041c441c002e45101c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 870146384 1250 870145134 870145139
    0x10504030c2903091002070f0b040c0f0504090201020307120e1f021606020c0f031e071d040206040905070909020403050d110d0c0209100e01080f0c041a0f130501 71
    0x22016800c0215802c0c1c2140032038014025480e010781228000c001e00e9000306840b601d10803814000e500541001d840e040158100341c4c0101c1d501d103001c148101d01c6816240000e5062100201030314416401260040b498034140d000141d800104460302c26810105099070306c0340030780045507000710b50b5030700b0b54118003c42ca214541d503103900c400d54450b01140d025501462000440c441580c002445042d0050b44001c1704a10309080040c45114050b1004c0c00f40c0d80e4400784144102c40c07042c07600c2c000001c1944845810040032903040c43c0d600403091441e1107070b042414a0380000310203000d180141025241d079072002c541c28500800b100001011080d10540d15903039a400c01c245c80301c0000e085640442c44100203810780c0b49000c10810303c12901600c0c0d10a600c2c6280c0c00384251500020008001804106400700380f00d0b9603014020b00929009004002041c010800ca80c1009040304241d4007542c10080d0b19030f031244250401c03a0340e03c41c05881e4402c0001c55500042e5505003026401051149041c001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 870147634 1250 870146384 870146399
    0x50307030b15030a08120703060f060903050f0a21020f01110403060b0a050a1505070516030c0b0306060702010804031e03060f0515030105012d1d0907080f06010504030c 74
    0xe21488a500541080c40341c540b061503103402c150324008000210802440c1030051035079040940101e028500020a00d071144844404c20b00d10303400840110b114140b0030401c128080003c0c901948401c800b4240701c02880c3d41e1542e40e0401810301c8a0390200040c520b804207803081098103000004000203205044503414035103a254480d0006a0703040e41070890040b460706215910900300c4101804d0030036000d10b010101e0440c895450744040400c0800c1050340e0104004018041650701d0842c052a43e0134610700d40030040d000103912a002c40c98041c0100401a0ba0fa501900d00c40c03502030802e501c05680710b107412902907203060074814900ca02c54040c0e00389650315a115209451401c04182d03039403a00d403030410100400052070781406410800040c003071948075850340400b03601103d03001d480c1c40000075032180800e1160340b0f0003400074006000e440c0704020b0380f0050058000d02582e0390106170620307020041c000300004140015a060010204106910841c100c1e8010368202840b1008a51600c12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 870148884 1250 870147634 870147653
    0x150711160623090f09060d14100c110706080606210709060e0a0314070e09030306040c0309050c090712020c01020306120606031c02010603060c020c040e030307170402040605030703 79
    0x1003081d0702c100b40001038070039040a0003281c042e40c01c000d01c2a000900b4040420a45480052405410041e140c41100010b0405880710380c01000890182c2806041116518125241d0010080030005003120106108101058103030903210b840c50550459510034005c2030140c85203a9155182495800c8080d4401c42c48040c903501440380b5544401e109543c07200d040320303400d00c86490164809070030a010400610403a00ea800103c10030001e50b41000d0741e07200984010001211f1000f1503400010821800e440c1030b110750000a0010b0408010502c5030b511010380ea44403105820f03002d80301100100b86450f0160081c103140440803081555280324508440e4040e400603183c240c0201a2041403400401010401c40d100d01d5014004080d2109409d0036082c000c101c980003102595618a00440401e445001e011825511a0010070110030300c98203000c00c40c1c00202182c11150002e1051000c40380d40196000a10004043da0143c20340b40d500001e40140016406140d241c46102030000c100483c245 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 870150134 1250 870148884 870148907
    0x6060e01060c0b0903041805041112060f0603120f0c070b0a05072f0d031403040b22051207050f031201030b100605030112060b0307081006081507111606 67
    0x51203d42c0319101c07000c070303540c0c0c0380601e00486a0340404a064844140740c1507000720742c0103016000541c0300d0312050b03020960743e090544034003560342c00c150700b0421030003d6124110b8010600303070003d040d00c0d60503404400b0035000c0c00e0100603642400280071030790b051082042001404a080205581e24124103010b08907503c000404c40d82c503881616111900500c03840240099983c0350403440c8031f80039000401044404100c011028441d060004062100141c40170703520440c0304460300d62603814200100c2141701c0201c0010418159407003080c4000420205010740401c90640d0785035211003691078910b041c465040d024604c1403002180c2c01003130709001d102441c100c07030045805042545400c1da03408410b04640c051900418000c0004010052440e02039059160052100191203288a40040e0620046a00004440c4d008917400d074801100c911421004084810003425654560304844140c0c0b5402001713607041c05801001d114145a040c031520710f0100001042182203511154058030b0401d074203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 870151384 1250 870150134 870150143
    0x120914100c030b13051f0e01031e051507091e060306051005121018060515131e0b0f0a021b0607020d080f0d0f05072a06060e01060c 58
    0x840705a14031406885120044000500007482c465000700324030026003409403202225080180000c3e60004503035158202414602d440080b45525508020144040014100b9072010540107a40d00196000840c0c8148107103450400340b1607580e904007a00c448045600400245075100002d1201c42141658001942d0342600c0070008562180e00f070000900740c444440002c18806c0001303100d0460015180c0c0d034801c0e00240100e9655403a500728000c442c07407412801005c01d0301c64800380300c0e5280c07440615200c0604900030509100001005110100b954400e00c45d94000740000d03a12800c000c4a0389501400b400b4045665406008014840690040390030720018000c09a55826030600b024221601c050010401414112240c00b0020f014040b02e10072201906c0800c44c4003440c0325003c024100349071290b030780082d00360140041101035600007420802041602d0104140c10310030841c0012111908100102e54240580b501d10010143c1da0008440f0560b01800028119481952400f41c40d215 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 870152634 1250 870151384 870151391
    0x90501090c12050601030308061c390513020f03071d0301090b010e070306090e0c1212030f1f17010c081501050a140f030f070203070f0312091410 64
    0x4400402c402c080c0e840e03000815a421801c010400300c0c0c422044281c100070300070140c9803004a8108180203e19900384120384013000700e469400101c0d03140700014214188900c05450030584030000098030301240c029144030781c0312841201031110107076065580100d18200526030b83d051050f0041c02c0d08002060814030a00c1040400505086c10300070059890f03400206802ca40c5d01308404003900b90b100500100400da9201070000b1024901d006648641e03454030054807150031131605009481d01000100105a4850350140303400a4084040f254451100d414144058494001041d81e450310345070384041101d012000400e14072144980d0b0701608485d44000c000c996a401004d590191003250414030551a01f114401c0950040c7c0080c864280e83d0300e44010080d0a00444400642000b0089800040040100b0003100b40c410f481c1d81c1c0004c0e290008504161035582e51a03010b070541321f002010040d00011800440389281c0104002d0340d80602d207030080c21a9034804560380e4400380c0c0c104001d14107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 870153884 1250 870152634 870152639
    0x10608030d0920060d111b0609190c030f051c0509010906170c2b1b020a0308010b0a11070b0a0905011409010c1103011a0405070903020f10052701021507051c020904090501090c 77
    0xc9049400c8ac215030b2001004005610355120120b0300c17501b54105603010700690400030f40c0080d0410800042e41c0d446e45034203844e0b40300800010208042c80e000403060180019080c0c40020752151015400280024819601d89501d5000700c0440348500c1d5022000d1a50b880591000c5801e401801380780c01040d201d00d0030645034002c01c0340e80d0f880700700300900420309007401030100c2c08081d0000d00310f146031030602c0c40e80e40d0080b901d490316103450707a4410103000c0fa0104181e11803640c81134507180180400d2a01a0465501311a00038080c4105544541803044a540c0d140401c640d810310b035466130710300900800580401080e01510601d9110000d8422442c00700050b48070b42c020300103a829a500901002c84003006d4005000b0b65030800c1d01c0ea030040c070030188414540040c0d070218681101c6007880d00d1000e00c842c40f03000a0300d0046850814a01c02c0d10000c2004000e950080560700303114141d00003243c81c840130080c600024820102025001402c20540005103c4150401c5807003900c610017448503240e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 870155134 1250 870153884 870153913
    0x3140105010914130b0901110c06100f06080c160b0c2d0a0c150510060906050412020415091505130b01020c0111010608030d0920060d111b0609 63
    0x43c4200c41644500760060406400710700020381d1164045112400010307804580080c2c25880d402900c01c214aa6100004010384c0c0c401c103881c504020b166030380807075881c01c0c24a00003070b011401c02040340d21843e038045100020901040c0c00324410303e8000b4200b9840f420f24a84894056024001c82c7c2d20480100c1c40b4248040058010b45c0843c601c040411414038582803012940c2d14804001900e41c0c928400d0011411906481102d0103030720144d5000c45814a0804041c1492402d13900081c18000c1c240000c01800039407a01d50740809604503030016003c4094010800e03142e0084d0048504d0724070784150600c0015080300850103440045520b030b10009a04400f00003905c1000302e00d80e0041c1c104002c0c1d500154081c0f002d184c00c011201001041c425240d0400ba4a16001440e03074044450300e840d5440148001c00ea000c070204283c0c0b5030444084001032000c070394144241d844a4008030340d6944d485d070f81441d01a00f0307110f000c0d424280c1c900c0300081211a00381c1e241005e0750805040d0081c52500c10828 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 870156384 1250 870155134 870155171
    0xd0203071b0c05040c20060105010f17150d06050f1f080c0103090c0e04030503182b02010e0604060608160f030803100302040e0f190b0103060f06031401050109 70
    0x55120022080c070a0800003440017609503203038900e0501c403010744007090202812014860101c844802411950b140a000401118038003046501b808220780008680140550405030700110b52000110401c03400000710380c10205036040508502d1604c0c00380a8450360a203031950107080c4c2c4207851244900c48501b0111035200501c1044400d6002c862060541e5009401001c034071801442001d41303059a030625084003e4044070100c1c00a08000b00704a1031015100011020390740410040030f040d590841030108461700308040b503803080031050400415038800d4101611041c2c1074030684081b81028a00303500078101c03600a098450103090700b5070010054410600003110241d0840d424001c3c6145c03611a0160b01c0502120300d4941d0011000c17000d41c484c0d000b0450080c04020050074071504503008107080c81c180824007607c50780c000d261078012401f04011141925088080021000121403a46005107910341c00282000c0c141e11801104080650140d03040f1446900140040c140e1049000c0d100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 870157634 1250 870156384 870156437
    0x141b0721051c1505041419061d0a0f090b040b0c040812040302030d03020a021015050d1a09190605090a0f08070312271a010f140d030c020d050c060d020307 68
    0x8604881000821200c42044081c4441005982c009008c1d5111100c009543d03020200c0000c41070a948280a03041c0c5292251820550f200b200401034002c030f0381d413101010716000e030018010110f0540031403d1503030b052040b10014103140d000c85891900c0841034241a40051209900c07138000c8507042c0e048a0300a000719419084a035000e0541c0b001c030409480018000000c803c4900400e00c1800709040d10380003458221680682d007031074210300714900300f402540402015410580c0000080b000000c82100e640f400155100c44003081c01d644185140b031500721020000b401c00058440c242c002e1044050040c0f8a0900940d10716955010049640e020b0f5245401c05080c0882c66100e070f04640d44c0105505000d10303105400c030300c41c003c9d0071080007450344100303070800420007480000810410502c2911010b00200c180d030662940d10381034801500c20504c000000e400340514001840c1000f005202d046d05c03211005000c44d0311801d615100000a400c2202c14070081209000785034107604441210910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 870158884 1250 870157634 870157661
    0xf0f05060f0d030306031a06042322061b080a090f0605070e030d020714010c0c0905070c060c0c030e0105030f0c0f0d141b0721051c150504 61
    0x40102100306019144100142c00d804140d900d11003c00001c03128a00705c2c3c1050141182c12425040c0f440c20001201c420800041d0700d07070540307180f02c1318004a00e150503a02c03031041f5812005110300382842c8a00046a250002c01c020f19008035101e81680180344243c0e2a6280c0d50307101d2040d03072540d03020004c441800b8005080003ca512101c00040c40c2500700c036501107040d203032490740d200120010901e4000f00010084c0075800828081c04540301c411f0242584080900c0c0c844082040e503126900b03010001d0103200c00103516000001c2c19103000704441c1d114503a0048042004038040340c0000c0c149144500c08500080003083d03031403032640c850740a5078054003d140d00505180c40e156003051107580503c0c50b40100310340900241c2540c0c40e2a214501403921a0a000281881c080c01c08540c0c0801036000451101024000c1c0d101094002d4905406890b6160f240c00d000010b070076042c0d03a24001c2e685000b0844265280011015219070025011280ca40043ca1100c50b00c1c2c1080005442c90080c0300c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 870160134 1250 870158884 870158899
    0x60803070c090902042d36060b060a0504030c0b0a020c01081f03050a120f050f0d090605090f0c060f0a0305060d0b010b0c060105030d0504051315090f0f0506 69
    0x2a4426600c800c9016200030400900c20005a103410706d0a10a83d86c5d9150000311469013a0200c038450160010308030a50302c5444005140c2440d503180040791001004400410b503413007004000c9580d00210b001ca40c000c0025403901030040b00109254070a002c1101c4024100b007002624a6222090740e1541e10143c02402c07103803510100446060400400822500045001034141c490204007810701542c000e4000c0c06400c1c08074144040c2c2d28410344070b600b040240c0340a5003c9455807010030303920b030394841c3c1590b107940d081041d9001d40a8102804081c0180d80350009006400707030001440300e909080241075071000750b204400c01c0313040d0080c4404140a9a02005203a070324904c00d900196101e24020005058000240c40d40c00101100340c2102d45200000540c50588060070064980100300440040000610803c0010924003030741c45007901424003a0310381508808103030010210000b8481244bc01640e540c141340d4054503961015509503851321205043c880e00758041d1912410005c0c0121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 870161384 1250 870160134 870160139
    0x11090f04021303080301120b01050a0f152c030f010624050c0f07050a0803030106090603050a02090d0606050a05060f04032406270917180a0b070303060803070c 70
    0x1010303510211040e50902d16410001c0001011200618043c0c2a00780b00241d940307016142000c204101070f00a03c0c8100707c102020400118903541d044240c6855202120365081113003016900e402401c000d000980b40040b1066080007203454000e01044411401c84800d422082200c5080340c44034000c00e04114050034000320300d41c180348a0302c0e641c0030003460300c2440c10f11324200721414048442d00102160708008030400c0140f400100070030141600c0c50180d0300c0c40d45480005894540c0034850f440a040c0c40303c0020b01c1c01402030341940c42002c405010b9084041e900d103028402001c803802424820004030070f01080f581410342c10f594048104028607860a811611942942e2a8900d001d0403070140c205c481e4601c2c80018054600100f680c0c0d0a208480f910000031000d14010604042c41840d140c0300305100844c1006200d44206560049000c0c1d0f41c1190a01d4031100d1030750000301c15080740c0002c50000c0c04031600300050134901e00955041000e80d0321001143c1e168072461202070112812131030b05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 870162634 1250 870161384 870161389
    0x103210050f010203040f0308030109051008060f0a060305030d1d0d17040606030f0b070f0c0302150408040b180f030a08190e1804030f020f0a110a2711090f 68
    0x101814554140101c2e42011b03918038204075140c005420454884802000411811046006030b6400c410124207a00406052111007959858010940700b00c1a14030340115540c86407961009010b943c010050740da555044030b00d80c0001d4503403e2000b444221010200c0b0301400d1010a031044169001d9403000903290020452441e030303000c0a0019a2201d61710000000010b8140254542c8684520011146880d0500c0083c00c2d00b981203810805008078104c00000280d8081008405000c4400d2988003d881c1d5042c04074542c0620b81105101c0c8400040741c2d1814981030702e907510038000c2210790000302c0303502c1e00a15031224039518000340042d0050242149030b100b0501c400c40301e01031503e45010204545000500d412002076090314801524400780014990f105d40c010f9001200340c00100541d01c425140c0300d03a03600b248a805412403150720b817a80200c0c0d5421554400070303c0300c051864070040902c0350038105440c03400ca2050800703203800c02555407008400300391042d40000901d0100c1d0200010b06 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 870163884 1250 870162634 870162649
    0x9230409050c06070c031101050703080412020f01020a020f060603241b04032409050304090207050a0209070f020d0f090509060315010801051b04080303011710321005 73
    0x2021a854082c841c50541e0a44900c80038200e5070b4000c4042c0c20040d491410403548010760707040c100d81041820031006010a8101d80c050b41c00503408801404a1843c5510403401e10300b041580c2c900c5175000280c10a43c0c2640050580c11010040b402c0d00c0307803500c44004242c1c2d100026000071482100340b20041d800744020040141d4000c0302400c0000782c940031040184080e500c04e81045403124000140c4001c0e43c80c0350203031440c100111042c2000f400034035840e410f5690089100c0c0303040d2603400084031020420140442c001050f0301034107545060030200c8000e80040c010001240c01071103001c0e500300c1101d00c42c500c0c000109400343c940c10748840c00d02d0140004154001c064542610580c00084135003659011980c2c002c254186c000111810700300c54240c0080d40306141441000700c01e02082c014900080300322811562014503c031301848044880d06e040c0610000c41110451600030b1401d11000c2c80d4000c10414240740000c0c4080c0c240003200113004140662300107052054203d02440142064a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 870165134 1250 870163884 870163901
    0x1e10061409060a0e0c07031413052404170f0307030f0c170a0e090c2107032405101115091c09030c240509040b041b092304 54
    0x41070080100c0c0c0381c044614120101780c68900b0b06003400608130b0241980640c0da850482c150709000345c079019900c900b5041407902c9014040c17042280000701c0d201c000c0d00c92403031840060302c00140b40c0c4480d6110240300e003c00c13110202034118003e420709041100700200071240314030b6041e21160040810341c80101c0d91443d140b50103c6c1c40000d15511040c90040d564068105c109181d5034542038402e2401c14401100340141044605000a0180d20010b50f042c88015424008210721004140c3d151a000c402030090490380441c510381c1e50b10440401c805c241c1303060040c0c5209945106092103800400c5034a41000c2d01100d500e508018035848140d2440c88003240c120031164200c90440500450003003a0000710703000c0c0f00121382081001c10800c0089450280207000019103038050038010344004c42e1401043c0c0d8240e0404c140000d80c0f40c4290350f01d1303105e21f12039540508104a800785840c42214152030394264000440c81c844000229680c0c21404e241c1e050400c0e54546040e00c80031810f210152003140b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 870166384 1250 870165134 870165139
    0x4120809060f1801022517031603110601060525030e061917010b0405062107202109060903010e071e06020706051b1e1006140906 57
    0x1040441265864900a4194001c1035880c0f0700f900c4400f44006482d242c11412510700c05000143d4020281c42c100c580c150481d92045407110038481c01c075000b68107500c40c42c02100c07642c50985003004241640005001c100d010540101d41041c1d80b1000140c0e118094510350300542007181c1206c003054003030100c0183c10301d0312070704003040106000300006070a60000142c50f4070b00e540201005414070b40c4075210201015092081c900c8550405094a80358460340c0075050003030000185408008485165844080240c00760208190030807400003003003410001c1c10340d144842540b4020004141c00f081085018840480c03c0c1c10038404184c101200d07800c103031011584520244942c40c032545080c010b2000d4a0110300c06402d28501742030881050311102141c82420306182901030103e160009101f8055948074141582c55417000c0141141c1117801d20800001402000180152070f0055031050810716047c00550341d1007201071030340700d00b240d01707901c100306103000e440440c040c450508116460b0000c1c0003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 870167634 1250 870166384 870166387
    0xd020f0615100203130e0603010b010329060c01021c24030b0711010905060f10060f0503040204021c05010315020f040e27030304120804112b080403050609030412080906 74
    0x2003145d098150000d584440d4141c5a440d040188900d000c2c4159201604c09003820840c07441d001b011230800c0780080c400d10103c44800408080140c3e1030038290358100030722038003c0d0b42d1000000100f85c48100e0892080f4142410b0100030768010004244140355003034400c01c440c000b81c1c03450f1030b50711440c103000c1c00c100c0501030703246241c6401c600c0070300039070261070b02401c010b00b01c9080a4139000c4e09840010505040316420301e00a02180754010a04d000a0442c1e00e0a11780b2070300e1b140009002885640784400f011403a8480e4044030580d2504014100c0c1d0040c1a00390050b180d07041c4c040168861700081458803442000103110b00002c0e05000c0741c00004a41d071140300b1001c00c0e224907055601d40395007028036074804801c10080000c0e803008451140c08503e811041d50074185d881c01e4601c1103003002a842011510130358100c01740409040300e900c100703c2c98121601411070a007041c41e82d000d40400c0d1003a0242000042c51400300004503000c4a410314640c0606006545a000164210340c605c10b601800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 870168884 1250 870167634 870167647
    0xb03070f030e0313140916050705100e0a0b0601080c04050126010602060a05090a02010c02120c1f080901061a212409310803090d020f0615100203 64
    0x7080000c2c0400300d004c0d80d4540310300c60038400650540c0d10f4a0351158450003500701000301500003040701000491050602545560140c82c1040c24001d20130684007e4030f10340080400390040014480f41b180c0c1c003859400641c1c0e2aa0001101c801000311020744104000700410009948142d100140900e0421070040180e4100315540902110a0380300400580c041014020054078900c00d00340c00c8440580208120003481d8000380c001080c528002e441144207244820780d001c130038010400c4224000300740500c0300451541c0404400c2d00241040002505c290018504520510440d0306855500c81070a0f0081c2200482c02d0035580840501e0481c0f8845150004460040d08000b0380501c2480000c10401b04200d070200c504c46100e0212688240c0c4400184500c406d0b082d01d0001c0002080341075190204100d213072100320680b00340c02c02450803400208000043c4404a14081250141c5d400c3d01c111031440d507810750b42d940013030f9480391000b059a20740d103070365150031030031905c5d01040e90054905024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 870170134 1250 870168884 870168911
    0xe030d0f14070204020301150f05130605030c070b01090218120c0607080c03030c180d0b0a11070503030c222d120f0308131104020306120a060c02070501090b03070f03 73
    0x2c200381c4c407864100d103020682d2440c0a030010b409e0a22455a481c1c51400c0141c2e0508200700000c1c0c40c80342c00280300340000403d000d181503004079070145400034424459540d40b900050000e50160030100d5000d03485400f403203007501d0085005a03094145900401008214004104d8154001d82089980350000c01681154540a0000c0c502c0b460700410b10b15102e92440b40c40c540d000022071a9580f160300500004000541141c002a40101481100040380844040720303a901d03100708036020b0540d20000c0200140780344094002d0224041100860400805159a01c1c0960009000e02c0002100c4c40785485241e564030000d41c0140811801483d01e083e9403500411a03890744800c0941e03400950b8030f1000b00307064202c40c076281c001c598002004c035417194944424500201c4511554425600040410129617800100d01200000601034507290380c02c51030400024150b4540040150003801c000142c00e600038102c0204469136003405500d11b41c0c50390302c100c40241501c00c940c0c040c15903600c0d0041c41074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 870171384 1250 870170134 870170137
    0x2090306071d010309150e0f01060e1503030702030703031d0a06080601021605030703141005101e05061204060905031306021509030919030219060e030d0f1407020402 73
    0x7007000d51100e108144508070505900c020010340541031505100703e440004242449643d00b40c522800700042c2c10090380394407424080a22142400c40d03080680100d80e0240781c6a040d03000ea012850203a44040e40300003403540364041ca21001c1d5050300909401c00119002e003550082c1d44d1030709083c0502c510381c400d0001d5140c0c04160842e0000030312080811025580400c00702c01880c250362941c074105454200042e030f462826000003483c00928901d0180038000400c10305440b0048101c0c1405035140044180d10030040c1c42c8646c4540c040f50390b0700d180054044c64100300c2a620081d0072180380054100640000b880041d008490303959881021501084003400035140314200c0c00c4849140600d0090000d01c1c0800b80c0d078120f1401d00002060020b00800002103401d240c5041e0f5003002c030302451540b0214203811550000e900401c1947d403802c0b2145601c80c0002c242c03081a01c805d8030b14840081815034440c1007502020120b500340905082d118060707204c0141070300c00811468901883d0f40d020030300381e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 870172634 1250 870171384 870171391
    0x80409060f06030f15060f030e030309061b12060d053a0e0d0320030301080a41070b0c0c10080c07120302071e0209013602090306 57
    0x10080411020700c50b0540c03500500b0344d44101d03481c080c01a00000780d2007200300122403217258240020250390005950280d0007070a03041c0c0702e4100762a240c2c0303001100580c407114102c031061040d942c0010030090103c002da058400f854030602d4003400554070300c4140140d0382c1c21600306446502c20002d0501e03c0c80c40782c00d00c8600108005401102400e252504212140f8201d006101405050405404c0c1519202010296160940750002c0700c0d10407501c2c190381108885000702c1c20303400004004200600006001c1000310300c100030b101c5800d0304003500540846200705111220207500300700307903000c40e940340b2400204060300f0041d40c2c41c25680b8240e9203600c2d131041c0201c440d5074000c1d141c81000b500e414112845020600e0403c04614900106210300d40d104d82b280007005000c1504410041c00e2096040d0365030203a1082c0607010303015044050740003404002d40d0407840354541c1da0010400144190050301c030703c2451440805000007101d01c152603491050021883c1960a014502c0070369002c001c020700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 870173884 1250 870172634 870172649
    0x913090c050909030412020f0f09010308040e0a1109010e06040b0d0603050607090503030f160b04050615040b01050a1407170c01050c0a201509010c0206090a0309030f08040906 77
    0x2480ca1900040c04140b210040142d43c0540092200b00b15841c8038902100425904880240ca400246000180000702441c0b040d50080d24010010040100001c000c0040d604a121140c085640d522241c200f43c8026456180802005101c2c400d0383d5409040c0240000c00d0060080c2d00346911100707400099042403d00003491a102c05041050020520026810850510b040b144203800c00e80400c0e602c1c82202c840899401001a41ca032120391407a182c00b100d1640507012010b1400c29042c01580d0358016160000b0300d240813010f01175a403500f4402c0c00c183d048103031030780c0d414010103420664161600c1c2d25014031445041124000180060382c00c80345400f5030b8484161103003618640507007100c4006008a80003001003040036000794002d50026a01c034078494001c082015000c04a0307090101d280710355590305445c2c00502040900c190007403000240aa400c4034281e40e6007034a500d58605031034001a02260700c40d41b050003c02c6101c1c1009001d02e005504242c0381c142d030703044c08508944980c0d00140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 870175134 1250 870173884 870173903
    0x150f1e03120f030617210c070303030504050f010b03192105040f0f0501090b030402011b08090f0603060a0e09120c062410030c020c03010207140706020a0302030f091309 74
    0x86458062141c1009400381c00d0040481040c140f9485e42e035405054440c644a01400214165070580c410448800342602429a2900d6507030b8503028000d0107081e24101da041c02880c0b0703007061326081403140b072100c2000140205803c11001044400d98101d002e415554903c10041e4070605006454592603804030581d1110313030719032a0607400c1207142d0300d5410620040004050411540e0fa10501c50015a5042c03681349960303485610040c0c402e01e68818040c1544410007041406100c800c50142182290546940c10080c0f2184200300780361100b203175042c0d0f000789108024810b8801c05115190b03c0708014041321400d0380d0300301c24031a15401030003448110b5400101004481580200c50000081c0a19011600101c4c40400101d0728080064540105a564902035240c1031080020f40345124000e0000c655440c51410140040d60600280121030301c208170300040c20601c001031400c81c031358140d40514240500251300300c040e588120909640b0200c20f00a101c06a9036911440c070701320f44a00c0088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 870176384 1250 870175134 870175157
    0x70c051f11040b030615071509020301060906030510020a0e06130f0501140706050402150f0d0b2b0f0c080f0c040b280b0307080a150f1e0312 62
    0x10800c1da2600c109001c2a4807040c40200407101920064a4000074100c503101d14820740c0c500c1900f030720f00654001030485d11034104203074101640e65010b0282503009500038440e00d0b8542440364141c908074440100f40e980f0001d10020100c4455002d03000e0b00c06c50f440c210303400200502c0010070342d4018290b452004140101c041100912401d0800c0c01450282060380c0c90a21740425a03543d07003c0d0840141400340c944000a00715030301c407251080c115440d00000e549906010130110920b400c456201b140241c0b81001c4000103113401007003400c7c2e0000a0080d007140d070350910807900b540e103000032040b10801c12401614000410071121100503100319802030032082980d000303c40c03401450140090207189022803080b03607070302c40e1160403a000020302a00d0b040000850b001030441e5001d9400084200c00c04400d0110f860341c00200a0302410b40c4100500504180401d910005241031240c8601c000130b41c00c04101c6011051184890707990031241ea0341c0155034980fa5040c91f0f803001c14034100010740301c0045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 870177634 1250 870176384 870176443
    0xf010c0503070f020111040b0a20010b041a091305070509040b0403030b0f010519050c07080a02130506060706090503221e14091012030530040b070c05 66
    0x1032000303c0b8480d2000b407251540d1619000014825801050f03007000000541c1300071039010b001c0d4011550980c1c0c0c07001c0100740c070100c0c41c2d500919085441a100f40d04041781c1000320700c0d103080c0c5120b140200905814040e03c403a0030f500c95028035000212600d00030904005155500c0b80b080c107100700d020307030701e03801007460549001000c5505955400707100f0314144000c100d490342d01c501910b83c000b40c90350102480802c0d0381c0c4107582030b0240c80c0700b51900c1d219040e0049887e150100c0c040c0340c0c0c2031082ea44504110244002c4600751030303080b100c0c60382140080c440c2c0000320701c442d0801da43c4540150240c82c5401c55220022680711081c0100462039104414104101c4180500c2680e4880000000601c03507402d0598001c141d404d01c0c07400600c00c40c0c0e05008950584d074580c000e50002d0501d89101c00841e8002d14010745507400c0910f00409420340e40d03440000a0038021804400507081800a42c129965030740c3e6114004400b8100b2000c0143c401c0700b20000840070800602d400d00504060003210244406 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 870178884 1250 870177634 870177647
    0x1180e0a0501150503130206090d0f0c241b030311030411130209090417041d0f0112030c020405100f0b030a050903070302070311060d020301180e1f0e0f010c050307 72
    0x2c1003040002c200b0402032061404c0705801b0055034101c80d0784c0d6032880e40c440081c20511003244080c0112940f00402410404005034020880e88070101c0b11501211023414200302d1428400703441c010511504c0e14840d100445000100c0543c804c4c1400030f444025449070004030341080b5021904225403401c2042e20385030102c2d201c9048400508150b00d01041e090104803043e001030b00080c160552402e001d04901207a100b56006003e0901800310816500045000424030076a69090b80c45139840010911354080f6070007a42594040d1180380100c010782d420f000080c90700426580400549101c0401c184005c0300c600e43c02030403641665034913030505d102c8040c200c0314003801d407006c50341c001c00440740000d4020400004494208004100d5024220040f4100341f00e20701400e1402840003002040c802e45111262040000c0c0080c100407004070f440d00ca90381c8203441385000400c91a100310034048408990041ca00d40c00e0301800352202d920441100c3ca095483d81c3d407178000405c5001c401c12040660010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870180134 1250 870178884 870178919
    0x602060a15270f02090a050f0a05060c03030709080a0f0803060d080c0304030c0f030b060607050a0503030708040b06030109051c030b040e061b040b0901031a030d0f0201200901180e0a0501 82
    0x30740031481e000394580086d08030382903403146a0007001c003540120170658a0f0950b4400421024080c181d40c3c0760b1201d02e640c3c595108403401c00203c1c012840118990b40700164408180b680315a10130703800b050720380360140329400c020089588030040d842283c0020700d498003d0104545072b10011600c440c00c600c1d0122200b4a00d801002e0090030310b08082000c250100781940c0c100b5025145a0b03070702d000c03905045007403413030f44075001d442c0e44000410703c41907a50005455105900070740c3c40b05401d480300381c2058281c0700851409081030b0b00c15003c1403054403202102c060609014200082c00c01d0310400400c094607000c602c0b07000303103401035030410003402ca5a265045000d1005c0d800c50b4902810030080110728024109028101550340c0b42c16005c0c802d51103400114841c0080c02c540704c00c444804024035699500c0102d000550800b40006040030742301c58000c8400545107605800c01c0d462070b0044858107660055032014400e20381300081c0a803e0740086600803900c0081c04503480d030400700e801c91a4904071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870181384 1250 870180134 870180161
    0xf023606392a040b0303130b03060a1d0a0b03030405040e03120c041508040f080304120e0a05030a08030a0212090d0e10050304020919020c1005060a0602060a1527 71
    0x895221207410a4442c0e030049000460300050342d03909031800b09282d80034010042104a03d4080081410054440514400c0404030380c0b51480b142c071101141a0300040365940d43e1000b1140740410215500e9400c80c41e12107002034100c0b810940c2d950002020fa9000b64040b13000b0350000222806404a1030440382d92011099a09070f19042c81e14114210001986408200b0081240b000c81c00700720402d40c81300d40280e0090b04560301d80c10141005190144084811000f281d90000018901d041c20900c0b03004a442c01800360046501e0754680402e540e0008041d410419800c00107042c03040800c0400e280141304030301c0101040b402d20880940100f00e000b80b0700f84107110b1142e1081d4800c3d800707001c40e684554150340b000e140ba01c80c09000042c140303060900c0d108442c00130442400c14200081d039440012262003040c002511541c080c007900f1a414016a40145c1107000004d04401d4241c12030100d141c0741c3d0301c205841507503079003c2c0c102c001d0b85200304030586091491714118659240c0180e0000c0d08a8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870182634 1250 870181384 870181423
    0x1c2a030c0f030c0915090912030b0a08032704061d06040203010f090c09150c0c240f180b030403020615060901120608010f02360639 58
    0x4640f540035403d0072a1041e0920035444104400310040c3c10140c0300f005000720007080c00700c003c42d490003c1c0040184400c2c0400286050145009803030002c0410080701c103030300050352501c1ca0a030582c3c802c0106486142c0307030000c0b0805035101350742c480303120b03650007401a000c910007904501c030310b0120b0024002c2d001d148918014001071180c00003401c84c6a04654500c1000a00b40c42c14900540c0c0c242096071000c0708041410911189150b00800c0c1e894880b840b0f01d144d0100c490b20f40080180105086043c1d1008030080c01c2a54030403401500140c2000f22207040c41d1301c90380c03d00309040c0400c02c00e54000500400c0084140020540c0400041d90040700c0c002500d035141d580080031408034040c0103c11740c108041c81f2a20b0211000716800b810280c1501c0307000317010003e0141d07030314000307540856a6404503060189280300d07052a4114085007002000c40341400d16422038003046078940100b50810544040e0400500b0b003140403145044c1605000d403c020024020f4075100350524411038908400c4890 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870183884 1250 870182634 870182639
    0x1201111810031e050601021e03041802070b040816050102040603140a051e0601030e070f290a1206050904031205090d080a02030c1b010b04060506091c2a030c0f 70
    0x1c00f005440009989118000780c1e59441d040102c1c41c1c0240b0051521803807081500e110720302a4040001d00a036210310220749809040c6246005c100e110385040500300c00d1f032003008540001d00a200820744211106046001c403481c1d9101e0a089034000d40c0142d0210f6910b8900b0200c103810102c1d042d50100b600c4d00100031615000c4c038000015403401d200725580ca00b20340c00180050780280d0042e4015003051048804403601d40c624004034401c6400740c503060115541c0000341c0c100c2c140205c401000d044009080c24894054400d41d04034901041e0700e10030307076115031001c0740344c0e01c460741c0c0e062289001c0e543c0e0b45120340381e202c992400c803a07015150121541100d02c6c0300e11040e402401c0542c0184040d20700603543d83d81c00c8a420480d0107840e0320150050182403c00c4540358054010324940d010031a000c105041d0f40310300b0400b90303218001e03807160004220500060000c04151070300030f015028004010220a0b1002511140d9207040718040398188017000c00e006004506d0440702c003522060521054a50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870185134 1250 870183884 870183911
    0x60408030d0c26042d020f0402040f090c09090e0c090f0702072303010c050703020d030b010807031815091104020c0a0209130f060203090c0109030809120111181003 72
    0xa0f403c060030000042d00d002180030002c90038101d8420354182c80d00d150411030203a10b2501980b80c0410164401c15800740300b42c20625080c4201c038101d4507101000088980303060780b18800341c04c2240745a014002d810000041280c01c034000d41201c400d4050190900c00568410041000300150200740141584002c0141141c2c000420400340c4041070100c4e40310140045a4a07054903003c0710f400d0f059400c203d020202241c002001e420114441e40070740b110300007815021021550030750501800a40d2050100b03100a009910070803980c000c4000c0e00a121400d03480ea464200040729100c5481c0f6901e01c2d04605010a8005140c0c4510080b2400d41c5045140c0704295600e80760780001910071900417020460b61003040e1800d00480754130122080c6001618200314009404c201d5501d001405001c0810501d90310401e298070980b0317400040a400d051080042c003c0486100d10810b84039940c0b01894940d88400a01810b603c09070a000049802d0079031040c018a018103217103040034182001303041020070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870186384 1250 870185134 870185177
    0x3080a11010b0306011e170607021510050d032c0a0b270a0e011508010e09060406020c03040b03160f08250c080d0504020307080d140901020309060408030d0c 69
    0x45103c0c401046c0340300306c04d03038503507181000341d500c071250030442000380518030315010642c2885100541c0a4902e10750b80c054550f0303620082210b140f83c24134407201091004c0d180a01003405018001e2602e9401e5020f5070284000d05014042d54100714550485c4001c003910b4440c1c0b80401503c2042441c030700305101050039030724543ca000030300c6074070070010b2856400c43e85a880c0300f0402005864485c2840d0b50b510340c0110110664a0204400605204001324071600710300421405210200001e043c140e88a40f1007600940005200140350300080100150117051003000d540200b43d60086142025488400a1729003100c1c040c991090003040e000304000c01100d544d0080400c41414800e00841200c0b10040f20400c03c100001448400c000c983d074440c0d462181e108500c0741d4030990032581400e031901102aa00d115003800308001450700c2100c0411011070001804d411501801202d04108103180040c030250400d0704000f040780d0007c0340500a880c141d000345031030003409083c00204241c0905000401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870187634 1250 870186384 870186389
    0x1050102011415190905010e0c16022b0507150f0f0c0501060306051317040803090d0c080d050703020106050a1508040c170c09060f03030702151303080a11010b030601 73
    0x44800160948280e40b11240d0f05818010f413a2030b80c114803500c2e07201e503c0050200780150041090204002003458024800326410308010b0349400300103404031f81c20040260f42e0310f65040780212511108000b080402030314140014420005401e0306414581d6076116098285000030421104102d1020000d4211007041080c0d10a403400ca0b9022000e41007003400760600740e100404c113500d003408221000c0700302c0b200500c106104a0100324080f07549522440300340034500520000b500100300b54642d07440d003200304281d031a00c40d400d030f10405039032400503c0c00c01c0e10b809045c0f0f010500000e2100105542803090001400c0100d80c0002c0d0242442c41000c411111a01c8000501c280c02d0041000c0c0140714010000800c03032440f2070070742c51000e03014403a140c403540c01c0c1c498002d01e0683d0110b1181e15225080e00703403103600500114240004c940802c00400502904e10094207410410f181d0501c01140d00c4030f000c0e42c0a80445030782d526004100038140c07111601c07010300743e03403424080c00110340d80403444504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870188884 1250 870187634 870187651
    0x71706061812030c030d09030e092215093507170d0f1508070308091c0b04030207150206090a03180b0d050a0501061e12020d020a17010501020114 64
    0xc071002d00d000c55443c52044000c0145944008100070400945a40120188031b119988581d0340103d900284024a4010344c4c5000403e4000141c0406414441808405080c0105d01c40300118203041a030a045034011101a142503440210700c0d0110886a1120164000b020740703ea03100c42035032890300e403070b501600000610400e404040640c5011307801056415004203004100010702d01030031842d000700500090480c180c2c80007080082e501002041032003c40b0b030841400713031911102e5010003a01003c8062900d5141c54000c3d001c8001c2410380c1d040c2480b95100760002c204007400c000690344400c418281c0f240455200c0410040d0304203010440004850b890700f040e2040019003040c022000c1065000750300c1d80c00f404161540e5030180c0b508002d0040025407401c010070390701c6d8001150421154441002100802da001c551680d12a140c0301c090303d0320a07400181003588512080050ba1b0200d440b102c00141d5103034014480200480c4034a00410003400200842c09412031071040802000340000c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870190134 1250 870188884 870188899
    0x1c02160602070804050906032806020d050f01090f0e030315060705070b07060b220c031b050d05010e060303120a0204030b010b0714061e100305070e0109061d010902070201170717060618 81
    0x801c800d98040e5803004413348024011440c080c441d40c01414401d129028035a03041150581218440e40706011012191a02443c40c66486403000c2c01c3e00b40c080d0040f1900200204442008540c3c107201070700140032071820031940c812640c1800d0303013501e10900341c45110700c0c01001c10103000ba81c01c4101c00062400c03ca00451100307140c100a07002013a00030908243d0380044524039440a1b8030400178007144613010710030040c50340c1345e64060200d03540c100d8a41b030705580204440c520141421401c1075000003a00d00c003610742502ea03603c404410500780d01840000402092410400040c180580321080384c0b00010500c1c1d01c3c00b01300309007680000011a00700084440d002c28844e490b1540d2a4002d15007000840b007055a5400b04100350200910414004518003140401c0010b07850b070111020303003a1502e60401c42e90805d805100254000032040f418080e00d50300403078400103299a203610840c5561250b001c1c0c01800540c07003407140f81c020f10861068004020540b040d001c0744010542400042e1004d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870191384 1250 870190134 870190213
    0x6060f120b03010e060a0b03060a050603030306190519150c080405221103010f0e0c0406050333030c0603010803121b04081c02031c0216060207080405090603 69
    0x1e0050070b200c2c0000304e6602400007081446403868100c400fa0725425411541e039540c034214498101c80701910041e03495081000840c1072031030015402c00784412071a002500c0c0c3c0781c1e10b100240302c42c211201f00c0010a5407030322040210940c1d080f083d0101c18181d041c41d502a2403640d40340d040c01e20a500410348075244001c010340100300c6012044054a01010b000c00c4140c0014880c00c405e03400034452000100c001c200c0103e9480c0034694040d012754000d1102c542400c0c1030040565081c0c01c024050442640c544400b204111514005115281a20389450b07804409100c181400c0c1b0510700b40c2d86018001c20401000028000411a0380603040220100c03034640720188103004c080c0e006056400e0100002c80c1c042082e0101080c6400194003403c010010002c0c0b0000c2a40c0340d006480c07411400c4010358009111408441c0c0061441090076000398140318a240d507603500300d8025440540d130745c0c80d001c14103000c0d40c14404440c58200740101d00414105000c4041954400d03c2c0d90800002c1802140c0507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870192634 1250 870191384 870191389
    0x2060402130e060a090203010e0304030332070b0a05011502100e0307020d0804092711030319020c03010f200702060d050112030807050c070b09030a0b09060a06060f120b 74
    0x1103003805414000fa6002800c1c0f89501d08050020301c0e206074425460010080c241c40b038004219811260f1649908011101d41071401000f40d4148803440c03546a44203580c4a40c0e1542c1704001e00c2c90b42d1041d850800c10b420800d140c1e50480c1c2058200c22401070000d41d000795400d40020740200001031600000c40c4980c201c240c0d03a411400b030720200940000c9002440e804101c4a103000d0001d84403610f01c204003051010026203140708541c251020354060343c05180e008201c94983c0301c0c41802c400782c1160720b001d94845800c1169000b244041005800000b480e0030149401c1c000e640b02c66240d05000d1048568070303820304440c20312080f2203080e040000030700002103480e00f0b026070744000d808140c200001e6a59030403001104800c010110700054415000481c0a809a410340d01c045074000010110f5506009040b141907100070482c1d6030620403070300a03074002810303d0303011445020640301910150802c101e2074403c0d50583d8200c1414400c0f142031460300e1075804190314a10460f42d0b0004109408002c0c00f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870193884 1250 870192634 870192641
    0xb030111160c08031b0f010b010e0d11191a0a21060b0409060303020d140418240e0c1c021804060306020a0e1c030e1207060206100e070206040213 64
    0x4000354078080490f9800c2d0708402e15880f05e03a030b41d03039480c15151b050341603414217401c0700c1f41c9a040c40d02050300700e0800000c6050074200c2025a9200c2c001c01303c9030342850030000c1c100903940c0480003048282100309200004014210f0750300012140c01141c00e1412100c000b40c103800d80403400d801140c40005941c0c0480413590032290003040c0c040c0c0d5060b0b4558440e04034102421460206401600c500020f45284d240320b07120780704c000610900b081e41003604000f1100c4207031090000c0300305a1a29040f10742c1c9603c034a400c1c007505a206015100c1c08035403030042c0d0a81941c40040088007015414481d41001c000042d50503400c0c3e07d01d010005907286000c80046210f1031102040c240c0161800e2008001c11420340c0c0182514101c075150151401841c4d01040382000c0c803012650400c62041d00301100080c0284064029007200604000490301c9500305940303810300a602110050303006100b4001108a07000e10800500540c0208074504d2400d548042c0d644c0402800090044c1d40300300b43c500f43c0880560 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870195134 1250 870193884 870193889
    0xc021807020d0906110a061e020316090812040905041e030215010f0b040e06150a0e0103050705121923061306030314030604110409020c010b030111160c 67
    0x14460414140030310000e680b1880150384101084032283e020a426008482d8802d044034241c008149000c1c40790b0711b28018200c40001c5104001c0d071840c6000001d44580040c40c456600301c00710181450310300c1070003054482d85d076210701e42e50780244169040031100e06041740c05440c1c00010210311501c1e54a8900c02280f548804d2860000700040990b007090790106451a41410181400c00c0380d0b40c852031240c00481c070f24441c0a4207014100300810016440e811469480040100716000540400503e00c1d4560b200310f461400050b00700300360140c290307010711403a50494002c0c6821424030300c0b4210141c0b686440a003882d0540a68820404000e02c0c068103d81e0305011103203c10006c802c1003000c505010801507503181d21500002c41301c000c0074a140d110f54004c0b241c055488040c0c0000070703410105d04d544094802c98001d52111240c00038807000100420003402400001230b500c24034040d04908480c0c480b0441c1d4800d0b41015082d03151400c90f0300c09d4800101950113007901c42c40c0c0034548545140c0159 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870196384 1250 870195134 870195169
    0x615070302060f06010806031510030c0b0c01050a0911130b030714030c0907020c0d0816030f180f0b0a030204050a0602030301030b070504061e21050105040f1103070c02 74
    0x4046080503030110354103014501c00b215030351183d03c0301c070010b580010701150410b0305070344050440700340c2030448903c20b0741012000042099198880d140d0040100940e0031103d0405000288540c400c3c40074810164881d83c0c00c0d07010040204540d907800c201100101000384101c15051554500c1d280c9580f2554130f002d030050448001950711801c140e146400c02c2e040d68440c2c011090140d2030350400c0107880e4465a01303039000d4014554404104009881081c105644104080c0481c016444014903c3ca003814000d0300c0769110782c40d42402c000c00803080d129041030040400e07003040100080c1d10030500b041d208c95610081d00c848140104600038005c60307015541c8500001c5000640940100082d816207000c0c1160a41c01da98001003500c540c8075600c1030b10001125450040c030b1000c1030900c01003c0601c10b151240d00701c0c1000115002c0703614582030000703802e90340e4170040145261901c624003d0300044503048c000a500c3c8203098040d03000040400b000c1c45034100d4036108645d100500c61000c6400d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870197634 1250 870196384 870196387
    0x240603210314010807090c0503040515040c0306060303120623010f0e060403080a11161a04170d030f0b01090317040506031e01050d05030a0c08270a09140f0615 70
    0x11004901c5c2d4440c4148140c2c08902c0c5030148005440b40305100304e9107e5500032008240700241c1c00214070004400510903611120095000f1001600074001c9000840c080c0d60303281604030610503009c2c1164420390280001c0712042c109000305644020910022a2003400c10007001054940182e46500c043c070405d65020100190200030801c1650140240700d11517070f1605040344036441c0b1203039100c1000d2006a842803c3c910100010381142d00c1c2100c01c04a20400c95040907074540d00c090740030401c07418240b480d402034007100c2c810329070510a86500d0080ea0f8000d000015422001a010010600002c2c00b200043e10740030110310f40d40300c00c031002010080e106555903d0700c03401c11049200840c041e5030103d80850000a420300d0104a13404520390494050352910401480540300840c0300c1710110b450740f10910621110f000d00c0e4224403036400841d65131100100c0080108000c546d141e4000302c484500d8094040090f20013070b803040340d001c0034014450b00651254800205810f03c5c607120003080e01c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870198884 1250 870197634 870197639
    0x108060f07021c0c110105030c0711040b0405090607080c0f090f04021b061012030909020702010207050a08070513020c0d0516060507050408011b08160c0f24060321031401 75
    0x7440102d001c8114015801c005c501164600119240d220036601c0503441d20041c45440c0c042018801c106450050052002030301152010100b0150769048911050540010f01040b0420781c1018501d40e0040302c1424a0340341544c031151b0740c01c03640900d411b25030017441c240d140700207503844641c1101d044080d00700c0c501e0038286102e2f4034256910001c0396403d03102c000c0d50314005038090720300d10580009a4952240c0368a2800d008040b402500105000d90451060300400942900d4248907a009040b001010340105803c1801340000c0030032400c0c0840040e8810042d1041040001c80c00250b55071491a0141d40d0704840810603c803d01107400241200740340105200101d504800140b04443c4501d00074031000c42e030001140d10484007d2540c4020030903410000d000005420038440d40310030541400ca2002e809038a4506054202a004171381201d4400385c00c1d075500d150b074880c4803001c80c1d180c04148881410344c0c0c0c0b10b650741102a8640282c2807442c4440c440300d80e00a801c0070f00c2c0c001301d444540003e0369 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870200134 1250 870198884 870198887
    0x8090610121e1b290a030902100207140f0d030c0f12030c03060806070e06030c16060209030f0f0a020402030727090b0301090804030f0501020c030a0206040303050f0108060f07021c 79
    0x103d040d80c420062041d000c8001681080c80d20080108160752914a614a0084c4515051a44082207aa080641d03900c5510016661600802c21801c16540141701c62810706140f003c07030683d42004a44200e10f2680c2d00d0010b03540e1900007440e8654149007261200c0f181e854600151200258000c00683c242800a007102e03515901074070404006035000d02c00a0f644402050700d8507001e460300400660680030402050800c2c0000b90f4007d444403080c0342c9410f10300103c10000c0605000d0483d00c0a0f0001503d249074a0f080200c092544e130081c1c0a0821990200c18131540c4200c041c100178007582e00400010f65041c01a1030301c0c2d0b0b040c07002d40550320184c1e42d503072401c0140300094040c04c4215460250035a082c1d0030705203e001041503000c45050f184c02d0941c4c986948108039281d01329050b42d001c202d0311000c10810320141c021030203150000c1883e410140344c003070107071100100f1920884a400340108016000000e140d46c002611182c41500340d1070310345080b030a18242d01d841051440c080018952000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870201384 1250 870200134 870200153
    0x90206040b070321090201140705190305040f030b190605030d0f02070e040807030908120702010309050a0227010602150c0706060509010f060314060d171c060608090610121e 76
    0x1c0d101b41c3c5d80300d5230303a0070252242071103001d8000003803c04d6022103d5560041703011b21160740c0d164060304020381403641c0d68008a61540c041d40048685010140a11404d00c0340040510b216000d503c100340505d03410440802d9480c50b040d0004010492508400c2e4074042c001d0203020094203007840240c1c0e60703151a080468595010b4081140014512800042d4804000c60117090b402003071400d03186050060f400460140080b500b054400b07008004410740183d44813480407036403d500c000f11900c90800b107040c0c3c40180c0d030140d10400a541044a084a031804444100c5a0100e0385d905d04588aa4403410418000e0125400039030f0001a150000704500340d41410440480391030350b41c02c4c04502c003032069040100005803820b40c0c01030340009c15000043c010208005020013503400d810b0800e0fa11295000086003207042d880346450b6191001e020040d4807a2034158000d02030700040c006410b10350100502d4440a20502c15181c4c40307002c152081100e892143c2d01303081081c803080310100489081c9031081c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870202634 1250 870201384 870201401
    0x3091d011e0311012613021f08131e030201020c010c03061511030c0d0e0108150a090c020a140102041d1b18040e011e090206040b070321 60
    0x980d0040c4820080c0301c01d80080d01c800c0c1e0760701420881c40400c03480010344001c1035001042c4422074140310303410101202c80360750900c10b507841103040b84040c00794014840e9059070560352500c05511141a03582058000540d02d41141e4401c41c50780e2294064200351150001ba08440d00200010161082c207055054019204115007840204411450303810242c0444100c4d220b40d0844524060038404120700404403468940e06040075640340140e030410f0181041005000e802c00b0a031401400840c5590121100d0340c007601e000c000a45003030003100010484101d600c50300d520b86032141181c50402e4400d0240b5030800f0360000c10014105100510300b0702070b4120f4003c0ca282d03000c401c0c03442003038200c11054090103561900d03948041d521130315580001c143d0105245649400703001000c004c01d6190351040c640742601c0b0500000306103502e12400c07090803e01388035a003901c82c00c1c0800000560380361021542101d42004005684811178602035a6180e040ea01071584005002c0e02c0c1c2d604051280c105110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870203884 1250 870202634 870202649
    0xf1303110303071d03071a180a08030d050109020a2001060b0414040c030b13051b16030e0303030709090b0f0d0b01082404062d0e011109060f0703091d01 67
    0x1000c0c0c3c04c582c14035a03520a00e204420101c42c000d40300480143e0510300500c491244d030183d0440803008071021841000582d880000160b10000303104c8201056482140d01516480c0302c103500d4400754020040c4811400c0000d030044140c511681404d401e82507208034010701e10418640c0c0c440c0c2d0b980d040da100c803108200105000c0c905008181171028400d101e0850440340060903451510302c40c86c5054001c2a004000184c0041c030f060814040f054070102525014054110120b458201031900038021100b048220703009a1051080c4142c85d0340101140080d12046a000034031151071800240450f085946201d400005446903c0107100902204a069420303020480d00940000b13000303864240b020346580d0154640c0035000c140020801d41158000e0b9034220700d00c903818003060018842c0314203211900d03030b070580e651031000d003020500380105890040c0042c1440e0500c10943d0204501c1d10920007103520011002070b4130303c1003501601810010b4210b041041809992240640410009c203004004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870205134 1250 870203884 870203927
    0x60516031d061311130b040b0904080d020d0212070201020c1203060a21051606020f1f0c140f03041a100303051605191205030f130311030307 62
    0x3100c15804007181d84140103041c0081200f66900c10070340c9640600c56008940300c050380a251038203a41c2e40c1c4407000e4002020380300043c01c10020300800044501c00b44a69000da2044010040814403000603641200500301c030140c0d5408002d58104024810900c061141d10b6110742030001032070341580a441c440544030101e8a15480304804a01d49000482e02c82d541b29000369002d0001d1401e0700615000090034158049111a01d81e44a43c148400a0f01101d0360b445000010044103504204c00c8072090051009070081c150300e048600c3c0300c11011469485040d48410802d54114841c1000400c0d040c40c842c44152614440148e03400c89900580d02a550074044031a042c0507440e070300703040d607008100715400d01000c1340c0b85690548044e041051403401d02c0c0000795001c0041501440a91034507858125881d404074070a161a128401824529904102043c010412550f0b544840da507008111840b41403036034240d510301180d5189184501c00c0050101005002503103820801a0700320b84003601c00c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870206384 1250 870205134 870205151
    0x200105090a1412180607060c030519020c060a05091f05011503020412110a0906030803040c080a08030103110604121a0601140f03100e09060f0c0a170a060306051603 72
    0x1540d85a50410440352401c101300602c125071035404240300b0200c1c201131715960900303460740c8070b00341150b40d0140c070040132944070420405584100c040506120440c510308604048101d62082d0390b814009050142e03103581c030004902c000004005a00e40d0828088000b00d68900120100c070252030f080c46940304c0c03684489260001c0c28028000e4800b50380141c407200c1c1c5200c0c0107480d2410a400c0445410390408002180466a88403900580010f10b00030800d10342e903030410b40741a1000c0d0b01141e0204e039440d0401a200e0b40040c01860481c0d04607908510008282003003080011400c2c03007254803c0c012094890340090803c19006881605222944007036440c1c0c1d59031000540d01044012090003150740c0c2044843c0301e488041c07000c1c6402010f0804602e81581d207600602c180702e0015904d00c1c08541c00700081250010343d8101055020365110649410840038003005032101001840d02001c0b1100580040c1562400358440c0d402503030864414840da0404407051031000d500610102c00290615004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870207634 1250 870206384 870206423
    0x60e0f130501060216051804020915040c210b0a180b0303030a0c03050603160612110a02010e0d050f0720031005010f08070b0a080613020a030c2c01200105090a 70
    0xc0349407070703401c07e003540000c1e600d83d0b0070840d0f00100100500702e403032800048020f2030f072600d2080015010035529a45110112810582e6511614014a051190400b00c0d1321030241c03200e554a00c1200c400f0301c0042c0446040f0a01403000e4240ca03500070703070180700110400c00e041100d1780002c6441081600d08000759150380040c1f588a24860401400c0d81040305010401e65118500043e03841c081030320000b03081071150003040c90396030281002d000182e44a0032401c0b48003000384102c4006140300e06145107072a2159510100600505d10050030b05001c600d00180a1120311b6030010085800070150f0b1088080050b00030001c10080c0102103004108203030200320b41078000303400c4040e076154109181c24480742c204100c41032140100020340002c1d0659003440142083d0000d40a0405507450200714500b90510040c514554100000001c2410812844001c004440b08240000c028604070600c7e40040040c17120720115543d07001d402d0f41c41c00041015004011501c015407506c52070300a00120030380b014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870208884 1250 870207634 870207649
    0x9140f01060e090402010807030e0f010507110d1d0d0f051605100c060c0e030318040b0a0b0d09060b21100b1807020a0c12020a080601060e0f13050106021605 69
    0x10b91541000c0540081000356004106207071340301c40786107008076000c181c000c8540c0c00c00345584a942c1c8075a44035401e020105412004400c41d42c100300c3c008140d100505903000380449140a00440c0b4058041c00a90309034071800f803808809604aa06036404404070714216903680602104003800e28110840810342e440c0001900120500c42c0d52880c003403a0454440c08000c100301c1c00b2a10900107141c00713040164038148081c25030441e41499402c100d000110030f100681d00700544082c41000001c506100c100d1028003a654031144034040001c5800302c628041c00184122403516a025000605ca100314180c68400602481c83c0c1034140c035120510310302c0c00d40580300749140703066000850041011003082e02211444e88850300b441201e031009c0881d2200c03503c05070160400e009003107900792200d040d4144802d10000500c0604002c0c4019854010010905c001400ca0340380701d0004a01a44525650003601492450700c0e84000c01c07081d6900e40c03001c2d41e0b40007030f0340f44e00440512a10b0002244d1820f480d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870210134 1250 870208884 870208907
    0x15030606051804330e0f040308010b16050102040902070c0b030f0c070305090406030b010815090d0324060201021b030f03040b07232d0405061309140f0106 68
    0x902c1d120700005884200009824006280841082010012190b5601d84005004a1200d40040781403030f40c1809101d00040c03800030031058110b000314040c40000380d800040681101c1c94243d1094940114071000e03003e401054078040d195600105000c17400324a00c0d4020b04c801440f0704a080685a900d002c1d50b02c0f140070031609104003c2002d4000b50301c0141d00070081010510a14203d0b2802907814009000c58040750015180650100014800c030241004502140c4065000030401450309195159070f039024001c1d690101900d40c3c08004282e418001c442c014030090b154049400c0340c440d00c009000350440c0b2000103083e00c114a0440302d50301c001c4101d50103042e4030850140b0f15500c5880350034003410050422800c11541084900d100e00030348000070000380d00d0b44446039031014003075192210700c85001c05034016001c0c901004031400340d55000b00c1301101c105940041d11564540c614048545181d44040d091504000c680c039034203800401041d00c15040c65060048a0b44c0720941142c640c861107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870211384 1250 870210134 870210157
    0x708010f0c0c0c09020a0c060509100b0102011a0f0a0506071a070504080307030e150d0f0c02010605011b020d140c0102100c0206130501020c031206030c040c17070e0402041503060605 80
    0x83d1001d000d41c14160b00200500300c224200740c403546030b02c5c0e500c0703800300c4004440a6820b07401400854803481c0d550300580c40310000c03d1000b440703c5950071400c940d0901c5004081c0e80b00d500c62480b620304580311980e064004140003001e45856110030b00707261071040c0c946d82c81034082c8810480040c0400380900309540544d80800011400c1c840b2550782a6014a032055505500000100c03d0420007010a0003c002c01b0484c0e04d00412000206c69020094410409002003964104181413220303036030101440066a4428494148200482c004105041c2e115040a0000800603442e5144044001010805d03241c0a0b421965010040e019140c116400c1e411301000581101d070108540340d04027900c01d014680a80001032604550300082851580600c00040b1240d5a4004010340b5140920400150039010765083c84030702101c040050910340e2080f41005042c24480200343c2c00b074454035040b0101003000c4c00442d500c079110500ba0014410301c0c61004002410200c01261440c41002a41c000f603041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870212634 1250 870211384 870211403
    0xa0c0c05150a030e010f1d0606060309030d050402040f020a020610060315150905090a0c08061503060d08040801060f08100e060c07050a12050304020307440708010f0c0c 74
    0xb141084029052120f2820003564881666141e0008540302e130007068031071f55000d11042d42d24941914241140104500e2281c1c0045c4104142000040101e80c1d070541c40b000e0008056499100040060034401405004a803001c00ca460303085800040b00e900034041c1d0803d610740b0550f2120104c0c207279140d0352002900c095005608000e490801c80c401c05104c1000d0400503103107a00c1e8000308c3c201900865009a285440e003a48554036070300464640c0d0409010340d180301118072541c1400c032451001510b800d00071000d110114050106140661b03010b004080024426155541040c8041542d2130140d55014090010070f1300c107845985c072a140300510028007030003480e03880c4030340d1034042d401001040e40c440c064845690f000900d840509a1015926104d050712410240107241c80e004040d005050110309070340c180000d0f00164500301c0d07200a0b205481c2c0317080c680745110007a010420984c000c0d0151040400118a105040d00f2140162200040420031101c0e400022140e464400c070000d00b29618 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870213884 1250 870212634 870212647
    0x60e060f0408160201021c02060a0e0307050a0f02060c0312040303050c0a1e12060b040801060806150603060a12060c180e061216030f0b0109140f07140a0c0c0515 71
    0x2d0f810000e0050050f101016540f8295544001c200f2581e0340040c0c110008000307520109108100d20088028011800e101443c0d40309a600e01c1042c0f40540f111000c41060021903a0705c404444501114034180c907122541174101d91f00c0f210040d102103011900b0300c0300103941407000c0c006490700c010145d60784c0400515400c6125012103001c801c202c08020724840350450b41c405034012107005140b200145c954952070b01d1102401c69101c0d40003201c20b504203801380b091081c00d1440c45203059800710780d6146d4a40340d00d00003895a95042c0e00003820390140e1103014050003019030001c0880070150f16004085007000354254503000c034500a007209840e02e20081009410005c08901c414107544080750400381c00046a400000050350044804c4040c000030b10301040f01410519004012054050011188854000101d1400103000401030001c2c04000350003640b0440484050440c0905150b0380d038100c60000600035031164ac0192240b0034111800503940c140071001105800d03108805a04180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870215134 1250 870213884 870213907
    0x3042408150d060c0e2e050f0a1d04060905071706030d0305040f02281a070312140c210c07080a0e210606090402030705010c0f0b04060e060f0408 64
    0x10813008040200900401d05821390b403559401030414054600c8020300d07003582c012040e000e601c2d0030616603003040424000802201001c0c0255004540b442c10899041910406403441050040d50241c1e48141010340000700042c00703a0100d070107442c159494140d400141554440300c40420b0714100e426511030704801200e54400c0d401039410503c544000500d21205d50002000d0070703203100300d5904103665074403080d0120b0f10483e2104000e15490030810b01c601640d107184102130040c080d0190600051811401129036950701807034118001c00b186a03100c4c113000441501e80d411425141d82c42e0080000f00706030111102c078807203120355005100c4d02e2410381d0702e90303030700c0d02035044400090140012190000305a566603509045000f614504040781a1a032001846c034101018043e00d02444d002401e001c0980c90116a040543e5020b00f04903d00d1049071800041c07030344180c58050701404481061108119442c0c1050021301c480908460150b202c840d241090200140d41c0100002c45c108981351125 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870216384 1250 870215134 870215141
    0x31e03092012030703020705090a0b03060606030a09052e05010b0d020f07061e0c230c0c04020c0102180114120705090d0605100f18020c03042408150d06 67
    0x8078040c0001c40c480029a500b5460b6404c1580102c0141e00000002d00c0746040212200352701c0264481c05100e0714114001007501c3c0c0c01d020f444280240c100000160240d0307519004021415480021105d0040c5058215078100100c00201c0c0d50702610f4001c8610800441d0041c0c1c0d041e544900b1800380741c44000d02c624030095010400c40000700c1418400f030001b08071144518188003d04040607081d101001d000703802220b608100032010301c400d961070382d042d40306030703981350003981405c805959940c41c1c002d060b0610380100040042d40c001e000083d4130700c0200301034000c0c0050110200301c1071070056443c001540d2041407078284403005641441031403888078500d9009900441107041080c940341d5480003080072084600c0c03082c0c135002d03260010300045c09503e00c0140c00500030150340040c00340c10300c000c0802030401944000703d2a50040b501456a00341030084900811100d684225014501c0343c00100c920500c940740408603051320005091402c1d0b08000c41000c000c000e2000b007a6208565858004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870217634 1250 870216384 870216443
    0xf05040c1409041e1a0d080702010e0a170a0209070e100309020402091503060f03011b0e0f0a0303180504020304030512040f0b090106051f020a021c020d031e0309 71
    0x3900c65084c0c484d0200003040c10060442c2e4500042980301500719420308080500c45140d008500c0340316110081410300042c3c1702c41030350901e05210310505950015414a0300c680080c94400d5107020010b1111f00c00058010000d0710907100141e0f141c3d641d41007940c103d900d000001e50048451403410281603c20351024020070710040005043c1040728010440100006c14203442c44d020000c1400081d207007450501c00c504c40114000e21031502281c040c048030b01c1e21609031005115410840203065074509108084000f03001d030001c111140d41e07040041841048419425038402c1b41803002c511420940200c038495505a100c01d8a44035412003030403203510300108161400c81c4010000400103200001c160b024081c8000045841400c14003084a46580050004070400b05103426184054004c10781501d8182c04070303040303500e4480502422100301142c1700000c0d4010242e024003410140c10080d0001c12049214010341c91004014058080f103052203400741155810200c0e45035103521040c45c10701c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870218884 1250 870217634 870217639
    0x150103210210020301150e030c03030a11010b090c030420030304060c1505271603021903050a06060905060d0c1e030503070f03080f0c180d0b07090f05040c1409 70
    0x40c40b0741c080b69101242c10a80007101c4250a03003881600c8258051215048480c044015040080710703100040e81d20311520282d5800d000e0000d944204c402d8081d4030800d01004054030f01c03200c62400c01540c1c0721651089034100c0f01391411820380c400d82650b480d00c90247c40b00181c001c5140c142001c1e4141c490341e2492404540782810281d031320940c000e050240e60f001d0580301c40300301240c1130b02c2e06000004d02c00c80385c03404409910428244801e040640502001c881e016030707008455101068240c7c0700740c895034101034400c0c42a80100300401840350b0102c0111292000c007000a40c40300d104211200280d4200581810072540083c410240c4d031007007008500f2500d000031441c550b034a0b95124150307045428190b03070140c0303d00c0d4000107040d00030500aa002b801c0c0c01051303203d0701c3c2461381c4034000d000d41c2440d1f00555150a4696032182c44824400f42e00d2600040506814600960018501a40360103081815084510001020b051902810070a074410751a100c0c90810f40400c1d910941c0c0000d800203a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870220134 1250 870218884 870218893
    0x203040e0a2a0201061d180312070804120801030b1906120c14040c0507030c0f080c0f100c021b030705040207140c03032106041b020706021501032102 66
    0x228861600b520700740c0d003581c2d030054582d0014140806402c43d04142d0000c0c1c500300f0030b500040ca51241003012036500041c4050140c0a200c0403114440c40c500a455000d1044101c00e01440604da411440861240d441901b0350944e4060741a03044804040a105c020900c1850201244e5101c0c0141480d001d40c0203025000285103039541001240000488020748040003009418040310101c0e020b0100d007040166003c2c05641c0c0040001422817054a174060200030003500c6050821212401c9441015001a203c1d038951450780143c58488a19000050441c81403141010005440340648070700c028198000d04041c0e071b10160398001c01c4550b11600359240c0507400004c540c55840d48043e00c0024020b6284406560010b220386140c0102e00c900d09219501c14010fa005424011000540b401a503110746040382e118540401e02030901c1c00c404000540380400f45444c2c440d40040c00108403140f03513007223822124002e0b4075a951400e0a00019000d0011400c1540031100d2010b1060801000c910494 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870221384 1250 870220134 870220151
    0x803041419020315040b071404050301050c0408010b01090f050f0303040503011a0a060503100b0912121327020903030c0307110f060c0607030e0c0301060e011e060203040e0a 76
    0xe904208201e98110500c084a122240960400300941982c140c03100d50003240340d06090710b030321300e21071030041441c0300300f051180d05205240101b0341a82d0007854068001d02580c06c3c0544a900560014020000c2c50740ca00b9810710040d42c0314542500455403600c0e01c05094038100018000d406555000054041c4410003000440703440034440d4160030101c881040002100000c100034042d45030b548203000f000812f00502c0104800c00460b1000c65461095599030786510380c01080d440744500ca03d88565008524048102c0400d4000800107074441c10382d9103503620f807500c00754500448800100d025405040030820b807a07804a500408280900400708e030304080407aa050791440d070003440e040760f41900c560a07000c0103007020074102092200c01c40786103043c600006141613940d00010801d400301034031200c09000e42e4000744000d154120000c5c0091044603281c0c8141004400b0078442c0f0080c40242500d03480e611094540d030391060740c3c1664040c0d4502464002c140007111400323042c840b81b456680002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870222634 1250 870221384 870221423
    0x905030a0f0c05010c1203020d061203020f0105060d050a1104060329150d120e041d07080a020916051b100b03010612031103040b03010f080c0f0d080304 67
    0x100e03031454401c0c44601d200110a1030301510400d03080e440541800302c01d4640303e00007050310300d100c0707591500e42c030300180c1b6184035590325001350a055003c44100f8401001203018594046489603a00151318020b00c10750302d80b1003d100c402e41c81c02ca80905107400c0088024001070402c588009411030044c40414120703100c0c0c03940034000e56100341c510280c501504a00000b0a000080203a004a0840b18101007103069008140c0c0700e440e4040083c80c4042c0703660683d4030540900100d240c00e8101403c10802030704000f070000c0c0c1085100030b035070003644140440082c880c0f40000c1d82c0350b021a40036107041c24a071543c2e01c209002f1340d092500b8505103d02481100401400804c0004a85007594014246038030b910b440030b42212002c040d131a020340d052500600a1100300700503085125454603140c0001d0b00320210aa00758051504900c420202c00000011015200b02541c815070750b440042e18110f204130000c000c188000310b42d0458200f6013000403180403a5a0030003030360307106004e03404c0140c8d00c2c00407200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870223884 1250 870222634 870222643
    0x1b1b09060b0c0115060e0603130b150325150302070609060902100e030d050c010b0607050105010e0709080d0809100e0120030c040e1f0e07140306011d01090503 70
    0xc8030041c0c1d01d0129403128095002d02030440110b503040340066840b0308200c002400c0d40d040030038990040030000702003a030004403030044454641d08a90502c43c50706100d070000d03001104641c4910f00c41e01c40e21841100900a400c0780344a000d8007043c503c0612441d25003a550815494025003007416401d00220012440901034000410b01c43d03a00058003440e607104118445e070402c0101c20800000a0494038161800280c3c541c1131912414800c0c0c0320410703040c600b4050184e40a405800500c0458803c042000540221741a40c0035020300358825660070758101c90030503040c030074440c0c90f92044000003480f5001312540e94004c0406c0c003c0c1c4403020b000e081d8040c00d0350046006c480c02d40c1e6403101b8540e200e04c0c10b00761003641203201c03065132031440c1030030542c0c80c00b540124003d082000440d50040b461005c01c0d4144070182183d0381d07103040c40055a544481c000004100d518001060112448040b032030050404c4a108000584900c1d240e100c3c0030b24001022500030881a042c800d001501013440d560070030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870225134 1250 870223884 870223889
    0x209031c200d0f0513171603050604020301060e040804031709190e061c0803061801060309021e010c030818010f021e070c062a030e0406061b1b0906 65
    0x401006078281080000b0155000503210104100c0184001a0030703207481c8541100b124a03401b1002440c3c51580c1000f4208002c5131007020510f084448004104440465050710450086000300300e85682e401403010b024000711001081104200710070303c0054491280407000050521026003403d100d240401c1803c08110300d940d2001c500f612040103400380295111b40c3c040f6041c1c2d408200a0100f0800650f0070107012170050005c0800b00002e0981e13180c101040c5200c101c809245451942d4543c03015006140004003039010755240c840300004030b02a0030b1101c0c11050107965000a0220301e8034202c80c8500c000c0c0000040405801500030303116404d0258011500c003a2400613912916501c5034240380104021183c0031500034003103240880c12005548045600a041c004a0b80f465010f120925100924040e41041581c000200605510045880400c101134504118140d114402038440e40c22a17a0200c0d0105803041382c940008800715071406501034106c5202640070f4480d0701d410265045034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870226384 1250 870225134 870225197
    0xe181c0203031008160308030a020c1608010606030501270e0715120c0807050a0c02041e180c0902070317092a010e01031a0d0305090307090209031c 65
    0x88288502e102030341070b000c0300500c5020000c0000341a15800080400c00c11b00c400b911011000c800150130800795011144816044402d55040c2c1d607035000408160482801044d101e0b40c40e20b01e02103102da001e40718990580c0c585104100801c0c1d000c0044100c0300032101202c0c40000d440d00d40c0600c180d01c040202c040034104603d015a05481007a000401c6402520842d204450622845004807a00003412540010130f501d0001c0d40d8400c1c5e4201911890300c1464000d40040ca0407110090406640514a84141e02001d003402a1354000c4c4400d503c041c80c402e00600f4000c4855810008000c060f8002d20030a0b10a040540e415407851040442513041152592800e811902c00c0d22801c0101100303031140211000300c000019170005000070f00c14540b03202034505041e0b40d0040079002c0080403600d40c40d5584001d0100c500384003640f80090854000c580303464024400c130310010801d60558008ea406402c0d0150040a80c0740d542900b0140c043c40198654042c09101040100c0343c0305190130145c203c000c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870227634 1250 870226384 870226387
    0x9091505090102090a03061a3f070b19050a021515180103030f110604030819290117060f040603080a110d0906020604150b10091a040e181c0203 63
    0x4290180c02d84451065840752440d0036008440c8800141d035400c9140c0362a4605404000c041951025040b00709c905441d58401c42d1000248000f4660080600c4011020901d904c00510715003641c03140180e000200c0544c001d0350306d80ba407241414120f180e20201e01d81c50000d0b044048404101d400101c5c0301c00001440c101c0c4c005000f41038020940c0d085001440c9800e2148806800b80fa80c0c0b0340c00041c200800b00a400c0c0082aa1230401071074012400e00050380c100450910344882d07100d00f0460146025a0b280900c1c031080c01c030760145048800e007030b42100e03012840e0782c0d0300e008004010800702162644295101d1021020400c14009410325554030346804043c0072003c6811842d141c0c08000303060070045000d0003413062070707808140c81390043c1e802034030071000d40201170104000e040080340c140c0e049280000044d07400396100030300c141124049003a00755407585442c0903015034452400b490304d840c0c80d0100400e4443c8110309009440110402c1542c81102c8644c0d44000c95170a168000c0d00160700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870228884 1250 870227634 870227651
    0xa1d040e0a060c05070c03080703031409160e0712020d090804030c06090509040309061b1712150d021003020c03030c03041b0e180f0d0302070c09091505090102090a0306 74
    0x648101100c8544a0800c0341c1080000c0c6c2e141c08200e10240001040000e020440c2010140641c0109032101c418022480c010729207000314590b12202c0c80d060307001e20408805d00185101e582801540101186da03500c00414005c080440041c2d8049000d000d2601d5861038404c0210700740c04d002c1d01c003a502c0b0300c05428441c0d14040c002000c401d00358015501c25103101041c4000030707810465000c102d91040c285080000074254545110011040c0064254006c0e4000c0940740308440c801000402c2010541d0004c0c1c3c1c90f14038180d904860360b410013070b40103000aa1094050b207405803403081e41e010545005850585c4981301a030860f0000d903941c855200f0301100f4070040200d4140046c1e000d0840c255036800007440c02c1d6800010203000350003d01c00001e003001c0200303035500a1082c6a40e00010504a618182a40000400940c003d400a0b9201d00036403102040d40490f6019504810390050403944044420181000040502401c0e194032503500704944892030312400d00060046004543c000340403031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870230134 1250 870228884 870228893
    0x71a0d0c0e01020601090b0f0f120615040e031632060103020f0301020310050618090f071707050306100917010f11090a170a05031909060905060a1d040e0a 68
    0x4c2040e003140705090b0a040f1400001d482c0d18054810b00101251400480c1c01d2034070100304482c203a003060b8001130090384104008542200f00000c814070381030300c04000c90251765014070340f203010b580da00d90401e00c0c0b0940341c0707404503906c4500c0f500305100f0b0811420640e521400d0440a0040e117029624040d000000100150301c0e020224400c12001035000303620354034001b0f41c00d80044001d40540c9115240118100c0420000d01444c040605c1000c0d001d00c0840c00c0500c030405105200f01c50f16070006071085015000306045203043c0d4040d00322501c071181175071990000c01c114080c281590303408100125034005221000070042c0300d02010a030000240894001e103240302610404020b4600c1000200a60945a154001980110784020309206100d006a6400ae410030140700400307403403440f020074810000c40300c9044403826140039446884105940d1079098410a005105542e400002030201c0f0300a03078020502d1f0518165094a4001114240c20010b030445440385500c080d02c1c3e2018100c8030801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870231384 1250 870230134 870230143
    0x60d05041a1501030f06050a060804110409030206041712130501051503031e040504021c1b1403070215070c0309051c080a0c0807150b0909071a0d0c0e0102 68
    0x1441e000c80300040a25216100000001640c692503040603551040700803021501d134894005040300602c000c1d0110380d140001400b01006a4050b5210b000c52842051b80d85001e02c43d0020091341030700588101e9940761140310030f04800600404540300c08010703031f50382503034441d5000c0d1042c1021052108820082d041017801c6460041c04191155114513041c2c00c0c9650010035206485008030310301311420040400340d420f50181e6400305170858000320704805010708400492903104400f41c410000325001c03518a00b2000900c050840c0841c203040a039820384030450008603400b4900380102c504c0c00c0d00020910a4094044031303007400082e0704c504d641c4101a406181c803801031000300d410004801580d02260700301a1101401000808001f420b13450329030049841105641d08200e103251034650509243c15a416036004d25820140351140715001c91504d01d48150159180b0001001140d003400340718280f000745182e03400d07200481407000100c0c001d03040c01056114285991404107001c5040000fa280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870232634 1250 870231384 870231413
    0x90204062604111201020403060507020c010f020318011407020907020c1908061609120c030314070c0311130f090308090601080d1409060a03050105190e13020102010209060d0504 78
    0x1858103010034000030403c242c031290301c41902103032245410440950708600910541d403004041608103800c0000844d004603043c0845442030b00e60607103480345100120386a229604450030410100107207031080d544a007030381506541c4618920740c075010103070300040c00c1442c0031924603006038828580020a8200002820510701d288528880d42c541444409511200010a81c3d146000e2940024100c035100d104c92a0007850500444e040d0700500341080141030034980400d07008140341e0405401d0a060150840316102e800480c0704004e641150f5605050512403050664403509590190481800c0c0f8800d000c03081c00f00c10310010b080866840c001c1c0c104c02004062201c40e4000074010007400101086848141c070451601c4c02041413540034684450084019464101c03e001c130710031840d030b900756000c2410382d0340840319102c0202d0030402044202c0003a00519070801500c0d008500c804400d641c101001500c140009810b000d000760100d11140c01140c140f03c42103803100e0900081c0485010180c0c0c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870233884 1250 870232634 870232697
    0x2d04020f0a060c06091e0c301202072c01090e100506011e0810080304061202030c0904090506010608090c06090d050c040501091d0a0c15030609020406 66
    0x710946480005840c409810801810325a1129464410050110912586070804115960300b58505040034144580c6900511108000c04031100649440705800c403400352107040d21070745490703d241d590450003840521129080d171162080126110910031184491034081d100000101c0c40200140380a504043c1e010f481f80301d143c4151840b01c1603000c02c0705a04102d034100b0105141d182c01004881d80b0601c41c1020b400408403083c0f00c00c1081e0b11444a41c02141104031505205846074800340d1a40300da48650380214486250300402c0b8200ea401840e805420750103054181451301000c01c060320200300e011100e94011200501c441c42d0030880c907075005050320004020304445d0b00c012034041c1c454150700910070b05e180c8441e40704110040160007080f94026000344103a503958103035200034084c1c09203400003800001420079032a00c000a840b01009401c90008001d041c506000b8122200c0d5142c6100300301a1200700c040b8000d41d00f80018001860b0590b80c103914031100d17810f221205e02d0361480c2901f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870235134 1250 870233884 870233899
    0x5011403150603070506180405180f0c0901050d0816030e0a0e1012050c18010918050d05030c160507090f0905100b03010905151522052d04020f 63
    0x102900c0005a100c02d840c030a07601c8940e520038880141f9404020b0690703455110741800d041280c42c61005003041c10401091b8210740700d100c564040c00d511110302110311608011500010440d500e0945040d90030710340035030201880c028110020307802281f800340c01503000c50403494600040e070525000340d600038060b50209412720b05158941440e101107601c2403107120150360f9802c0c0b007032002c2072016079031000340107045034070221512000c10052182441024a03047c034110720100340841030411400703c164000c02a1014841d00700003981c95803c09031100ca0043c0c414401514040780316003860b031115020b0001820182d20300b91210096500078400000800d0902c6200000a90002090400060180d00220304064440c002c42c0c018260010003030501d10500e184041d0005c2e45800d10790150058500c103880c030600c1031050290340200800c8000c1c400c50700c02c914204c903280c0b95102940008200703e05803124600340b502c5502410a121854a1801255043c48214070706460003568a21007a950baa = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870236384 1250 870235134 870235141
    0x9120c0114130302220510090507030e030712110d0c0b011a1803120f07060b12031e0f030f0601020c100f050315031203160801030c0311030106090501140315 69
    0x80b8001205440002e008803081c2d140441c4420f4000c1c841e2600442c10402007005242518005610b100b16101e20048107103024045a003040c486c0c01044486e4000400640c5003503043c1e950781d1360034103124526100304911001ca2150080b01440200482c0606a0760b0600c03019043c02c00214501040c1d220056002c0304840c003c180050102c1a21030840070344002404095541c80400d0078680310403400089a100000c0c0840041d20380000b51100c03c0c02420300b04243c600002c2440b11541d4440e00e140e50544c800c0c04034258594000c2030340119074210305a594100442050520400d4106031039144501d074030041001401c6d6410022092465000c4845034680386007210b001c1c0407840380341d1160080060000006010807964104580c0248001d0101c07082c008849032150496007040e120121440d502d1101080e83e144100303103a40c107032070700403200e072030302e07a103140d44e801685103041c0001c3d501075484c2c440004542819224050013801400c20b6941e10000b808105810711a4660002000c42c0400b002e2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870237634 1250 870236384 870236407
    0xa0f1206060e1e090c04080111070c030213020f0a0f0807020a031422032613090203040f05071710021903090309091a090a180b0c09120c0114 62
    0x85142d0b69040d20010081c0f440084030340e041075540d0495941081456042c0400040518010400c880070900200140c0080c0c03207070610244140310700a0b0110490300e00c10700242c49c001c207080003060407560700145460080c4071442c1464000c440c3c66404203054424070920550004180c1d5803110313031031000e8044c03804d1603a0701508120020f008100806004104840541e0040140f202e240d409520701c2c010560740c1c0c0c5020348110101000e01b55001c0c09601051542c0036059050b20114054294064481820106220000c0d00010815203002c0713910034440c004544180440340180042035901840070981204451030840d2800c108074030f00d44108460b00d200c103100c0c40303032940044080c03801103002c4400e424116081455034100660086c03914800e0000c00310a0641c40345e015100307481043d0305558010680c0100d03084040b1a0030b00004d007a120a00041506c0d180303e90003411610081c2c20044080c0c041884070440100c3c515060780301001007500c541c1c104040d0307607403071400c00f010034a0028400788 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870238884 1250 870237634 870237647
    0x1b07030326060333090a050c0603070c030c1a0f01050102280b070216080d030b0a12020d081b030d0e010905120304170d0902040e3408030a0f120606 65
    0x90b410142a200c4040070500091200801e0110b4140d851380c07209428031401c00c540ba0300d00e0b074078101c5d907070321521030000b207241003060030b49219400580724841c00b00c2d4651000c0d100c040c034038941140c140d401040651100f000780011240904900d0030880615030401c03001900e80300c4c0d40003503d0030187c07503210340641c504c580500c4032000c00e500800110a0b03031280e00090f07140071200150b1034440254803c020402c800001043c00001a0b00e80c1e00388107400108080c01000c12040c0034a511000700e89008001604101c2c82075a141b900c82d060080c5010680a0b00d28420a07031444002d2894000051560349130300a0b0081061441481000300806465543c40702d03558107001400c00303030401c0d0200016084c40a000c0307441e002d2400800500340d079102401311400042c407040400702e105a01c4e0003661001d9080c00503002180310381d003180200003105400c41d02804164a1203440c583c10020401c08201c0d003500384082d02c107040781900c031460520b2207041c01401038150314810120320303841e11908020301e603485103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870240134 1250 870238884 870238903
    0x130b090a0e06150c070803031e06011814010903050102040602070e0a1820060d05010509090601151d040e0304031a0c07110d0c290c0a081b070303260603 67
    0x3d100a07960b00300700000c40d003416599442494a4000070040240f101c4c0f1501094450612214a42c082e0703545610040d00c3ca61030892240954181c0000244010740038510380a5008105060074003155650342c1e41c10342a41d02035001800103801c540c0381004802c080002554008001c0082444000c002003084074031240e107250040c200f0194144d15a1000d4261000c10018041c007400709581c0b00200c42d080c034041e04081c440c0f030380986542300004810b0000840d145050381c40e115102448084403000407580210f000802c0130441001c2c100710a9581e035544110680105803101541c2c60354514180801601c801c0000b48d06422008400c120710b102a880407185542e5200d151300d0205daa2110200340b80c0786c5810401001010704002c04a1041501c00e19407502ea0304c9440815801040c040d04500c090085901a0410f50702580b81d880c0042c41003070141c4600351070744081d403200040b001c9605252109560054011410b900902208002d4002d02400990205440c444903824024040b80c1d495680c2d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870241384 1250 870240134 870240169
    0x1d1b030309150f2203020901080c010206281a04050c0a090b0f0903060403020c150405010813020312030f09100203060f0f0609130e010605030706091a130b090a0e06 72
    0x180d510340c00c0521015071302e013846801101e6240310100d40e58280c6044c494001a40300b800c954000140e07160001030221181ca4045e4040d090f90340f0703542505035401c042410182140039004054146540840c0300742c00c880c1c90100003110400a8000c00c2c04110391000c0c01c184c500200030403091100720380100152045484d10b000c00c56a410b140724040c005401016030060380b601881c0c050000b810780c0014001da90b00030071a81c1c08441000c1e40c1a840c805d20603031082601003500c0d070300000d040d11112801d45808030300240c2514030310328440d0180350181e8403c0fa554105001c0140c2405004807040010000316401c1c180c0441c514284000083d0000780342505044c45051260400f030300079103411040d20000030380a0b0504481100f6107501e18064500100700e40794541ca1700d40e002481c0e2400103401d00859003640c42d011a01410440803030000004500e1005030800b080144103588a500c1c401d80e00200000380c400d64a079880c040c10040c0104156005803004c8070a5410700035a175030381c1c1040e80d0554004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870242634 1250 870241384 870241387
    0xf050a081003021003090312020301080a3009060908070f050f131a13020301050120010e07170d0201051009180501050f09300c011d1b03030915 63
    0x1501603406040c01d8075040290450f1004a00e000f0305a0103800c042c0c651441394460070700c2e0403400c0d03032280100d0009110780141d580c00b4100c1100401e00c2c1000d1500d03080c0c403403140102202c0c2459040808956401c40140001e09844010456540d0003841c51002d00f11007006001e1a03480d28440c14110f148900a01d84581c00c1009e0440041e61140d2000003500340f003000a02001c0b03c14443d00042c1c2020001680c0900d1507408201220940703132084a060300d105860311802c92440102080170000e0f00864002c5965076003035405c1643c402000100020044042c800d20034808080d50030f8144000380484038156030501c414803c0b1040d614184000b81c5107407100c000b41c0c0b161401a0340140000901002d4190b5182c80d05109401500f181060710a40181049030302c01e0928241100000e180c40c00030000c0400b000f00704148a80910008240711803c0d1000411700e8011001c0c0ca2400400703a00d8100d40030303071052284c1007070040108a940300c9420308502440c1080e4440e80450b00c1d640c0711640e5060b41010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870243884 1250 870242634 870242641
    0x3030301090e0a17090a1d0403140d0e030d0e06040507050f01030f0f05010f061e0806040b10020d08060102160e0a020f0d0c090f0b070f02011b0506160f050a08 70
    0x40030083d2450710364101100d002000340500100740b041e8029800b440c040d019925000c6206ca42c0384601c20031800648400326150390361903c044418108100b102c800c6017104011a094030034060040d2108502c0000c06140c2e2096a1180d03a400c403600d40e021941c10380c000754204804541d0125582088038800d4400000044039000100e0007811300c400115544dc0c508120042c49030fa0550110b4181c9803202034050203c0d0302c2d80c50540d0303001c00240414000c0e00320000117400061084c111150010030141c408240e8000401c0000d0307001d02103492600040e804480d24260090740200c40c650024130078000342401c04020244c2e150b41164602071a14803404101c00f0440c2c10441d40e040724510a07a400e410b5072214000301200014041440c101000200d142001103105412503079410b00326400c003e40249407150654401c0064440f40c00144d041c010b44954290175900d669502c003489900c210007a01003031501c0d56101d070000121152400400091022071901103402400300d603408000c03810200b54503078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870245134 1250 870243884 870243911
    0x1080402191202030c030a231501091509110403080903030d05090a150b0f010e040b1009050a0f0b03220f150b101b06060509040b060102100b0303030109 67
    0x9901c1080003620603011200001d1030030081d02070100e964404ca007694148034082080594403200741401410074032091510144a00d02602e100c010100d400d415a44044055410210000000d80c40070086545480c80b0004410b0712503010b5001c0c10619008220090301240c000040740a240802001c050000901c08402d42d405c00545079055030b034050611082c584440380f192a44a044d50880c0c8840042000030408102d5016100300004040d20300d0203d20000001180e2244c1c81171409604181d90768140310040e2103a040910000405485041005251800380304032240903500034141200340b040280700203030104003140c0c1c00c002e0001e0b005210f40c00040e5036010400d41800c0041408142c0c600d10020840f51484020107583c2c001d0f01041030f1500941031040007071688101a000840200d002c3c0c080712030103860086503a018084c000b440079180c0c00812012101a00c1c1683c058044200704031003076904104440c404000d00740c1c2481824489800309940740018040d5012a5403140b50000840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870246384 1250 870245134 870245149
    0x80714060415020c130b092701060611160311011412041a160f0809120304050106052407020d0206090619022503060b240d1d0c01080402 60
    0xc0504042441d00440b075468081d40c2e81c200d12150a01071585140840702c201e00038462442560380142020030240c2e5030b00c0c0d03200541004c00440b0f201c1502d4000c1c010b401a202441524003910301038a541c0c040c843c405400ca46000b00d09000401c10402041c010301c0041d4000700303a04030500c000e0a148401084150380c60b0784038010395681400554282c003c00c4144012424103c0190710006004811612204c0d000404118844543d00200b00590600c03403034035110326102580104a41c082e076481060203005c2d2444c0e9442a01d05441503910340c3c0c01070000e4580f41c002c02d079400c0110464540c006448409a0703c0c68004c40750044d00c10050160b0590030748d04e46400f00c03043c00e500100006d5031130340c10741c0c1007a9070044000c0174500144510800102e00b0b001811142c040100f010410781403591a55481c1d41c05008941c3c030480d0462880100310080346400240c1c403041030700500c0c0c500c0c0c942c007204010004603501180e010200c5803c40240801242020034981c240304002e10700403499a4407070000c01d508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870247634 1250 870246384 870246389
    0x71a090d1704030303061a0307210606050909010b030118020903010b0d0f11030609030d0f1b080106031104030f11210c010e180708130204020f0d0c090807140604 71
    0x90300300002801a000740000020070541e840b98404001c0c41d61a42201d2041c20004240404074031400c20108401500402d1010100010600c00c0007814501014041c182c6199510560100c4c80104510741c0c07d16201000b180540f5000303110702d0841d85440009640100101c1e0034118560b80001e035800d0a0701d0039040420040005030400f01292146c0c9854403072440380e040306a65400b101c1b01040924900400d840740101400c00040d8201031a21030044c1c0141402051807207169902c4c02401524580d0301f03150540b8101a0711900d03010361520380301030241c0f0801c44030544811000c10040c000100e40048800d48a5080585131484121309404204008100b8a50924401143c841e03151007420000d190840c40c80280d883c1302440700504144411301403401d0301811240302030310019080c50700c00c4203025440741c8526140d40d2880800e1b00840c0c204e0340408204000c403800040c004a0320303a29030080c402048494942034180c035142906040d00e0301203a00a0b6410300e818070380b62103a6551240140c401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870248884 1250 870247634 870247643
    0x19020c0c03012316111b130902060a030b0a03060e011e1407050c1006170c1503040609022706150909010308161a06030115081209120f010b01080108071a090d 69
    0x6090100c0301030584114102c080187c0302e0f4001c01ea118452032201d0017405c02c22680503041500b0300003890350540242c4400a0000e4100042c0d80340000490501d01514124141c4540006503040f82885807a00309a050220039254600380380c032102411000680c0c031a84141c8a280254070391144200050a02000c0c051000600303040000c04200c8601702c0c0c43c0700c00b0749e41c41c3c241268032029850042c0200600c082c1d00f0b91034000c4052000070045140d607081902070a10003400300c41070744196844c040382e41c4807584a40503600500301c2040401d040405003158007100e410085410040c4100c0060020201404000d20841010400104000c04070405044490740040300340200180c01d4004031000c5000c4030309611135802d0a240b9203000c2c1c8098060000d0740c00036800f4118103100c6443c404800d6101841c1c0701e801c03a40520001a4220080c40024602018038001103220309015000414105060b080311900c0d0300441010407844000000081801e00c41641403a1250042e400080513141103200160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870250134 1250 870248884 870248893
    0x612010e0a0603210206011710110c07060e09011202091609050303070f0c151211090d0f050106080607091208070602030405030406090b070206030601030519020c0c0301231611 77
    0x42d80e00e204c005480c0b00d1401c2c41d0b089035005d0303030f80f0000d00c44d200f031403100713600041d070403115403c4492042130b000030303001084003d42146044400d504641c03900d50303250710160000c0d1000101500c0e600c0c20350000c5005142001003402c0301441900003462101000c0c012419203052105080001c90150070414000c081c001c06480c1c54010600f450a90541c2100d4125012010541c0204107030701c1e001e180c40c0c074240c0e61307544655a48104035104402000f17644c01d44e0041c042e0500581d030003035490304a0742c10f550303104a480070240d0b90a407414900b5280070350408081c54228808108000303601c0300880c02140d14259484c85c1a88490904803c54490510050030050000041100f030182c004000c10440354150b0707039940c40a0313036102504006e0040d01d41c02984020b040010400b03561007504142e8001c13001c0350a1203049028101c1d690101c3e80050403c3d5503a41003180c0700c0025203400c2c13041902c06c0c0b000c50010f041103e40302d0440100f4410080c203499103490843c0c0d5a54070240328030010b10711a100041140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870251384 1250 870250134 870250163
    0x1020408030c100e03040527100617151e030a0b0f0906010b07030e13290117060d051f151e09050a02070605040c03030e0612010e0a0603 60
    0x55032240e20610340c40990b03120f14001440080050b2183d512000b603a02d010b141824240800c0000002002c0c014020348040040001d103a101a201d110780036100c0e03481d614242c2440c00c400541307001030061084400e4211401007100c221074030131052a000c03108403014401402200c0c0450300c803181c001c001c2c0b60103220f031915440030410300214050081c66030f009406943e0352f603807581d6075640b5070900032042025010f005450010f80201c2035081181e0000f0011201004a00480e10440711402d40211200300c0c242c411100d910f4502d24103c120034020304c0d100c40081c20042849280002c09003856008a40c1521001c01303212061203060303109804d000302d40c0d400702d80c0d5051460150426084074800f92445503070000d44910341c841403810b4041c8900c521a1104d150540090081030010b08a803980341e02008801c0010ba201c1c4507192180784550001d841c80c038103504006001200881340213000301d000708181d80b14801c5032054207044487c000c03000d0b0010340c0d410030340c600648aa540300170301c034150010301c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870252634 1250 870251384 870251399
    0x6030507030f0b09060403050d1503050a050d030e0a08071403070b0103060912030209010c12050c0f01020316090b040b0703050403020418061a010c020d0206220815040b0f04060905010204 82
    0x103a02c03140111550b00c616190b4007952038a40d40c0aa90060108508100f007100c602090740050010714a0101803004455907074540b80c3c20b001d0300d808100c0d42508042d801204064043c407546a074080d035080144100c41c801e540741c4280e8459444d001d0600d044501c010030741c8032000c1080b2600158403040c0c11001c0c1d60350f46041400f07096011804c0b1120843d103070400500300d1180c4251000f00c50140c0d41c0048400154440c5002a0304019000c000c010381013100018070b4004010000344209a6000141d803441c2500d103201411400050300810044105410481c41c2c0b01e00302070f5000c2e20f109521a95861942d172500350381e5031103650300094209040c4031514040ba4400000d482d1500d0040d802440000c2240e000d0740250041480d410340410702240a800250070050406c403002e0344007408103031500d002c80f0281c0f182c211018844a81d1450032200500c10303042c06200344502c8c001401e00d2b4600798100b640c0e6241c0b00117170041c908140690504000b50a10000d074101805254022008660b215285c252 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870253884 1250 870252634 870252653
    0x3010c0903060b0f130504030c2103060b030606031902040f0f0306051e01090b13150609060c030e011119050c01031a030c04050402130608031222060c030603050703 72
    0x8142d4820345803041d00e11080c1066294030b1584031005000085c117020f04d11848000741406002581042034080c801c0d000686600c4c0350300181e5518440120384003070181d100070165240c54001140010051040c0442071700c0d4001520740210460f00d48081030382210702d8620090203594820010100010b200180c281940d00d0250290703805110306110031f41e184240f242010303189207c0001019a04c5004000702602d0ba40003184403880100001401d00e2091070740e03026940d040ca5408610b00700b064080154a420074890070040c402820101404105901c0103081c03050720008a50500503004080c0860100601200c41c042e881800f03e00c2210030681032082e0344000b52880280444d1401c8c84501c070781005100c10b581c3d9064001e00502c1e1044182c0180b02c00703448060400c80e00494110021180c810807401540701900d12070b4011500d42c0d0075024481800030300584483d844005012020b40040310518440c005660000c0f804240181429012001050345500291042c050b0f41404020400e10b0b48 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870255134 1250 870253884 870253889
    0x212040e16030b011707030f060306020d200d05250905011404080c0409170f0304021008040209040b072006060f0103020a1d0d06020d0e0d0201060f09050a0b03010c09 73
    0x21260a905a2000003070b41100c3c0c1c0c00d011103003c5628032000c00807a640e000c0400c6ea11400c07034580495040f1100c0c145205584554108480035600400c0708012200e25200b0080400c40c1c0d41c802c01a0342480440c1071a1034494070710083c40c481d8036180015580b420320342581da07180070101c06071245984221070043c05603600b4052540029101040890410b0103c0c0658007510803410141038030740b0107d07003088001e001c080400c4994030241828400300c3ca031150060310306101000c841540d20315083c410000d5a602000b0340702d040c000351000f4800542c070380c0450554042d9011700001da942c1c807400303c140e40b070050f00084100f8405003044c0e505606140459094040c020603549804240c2000c0d0054041e402102d02ca44c00060b00280802c50f40059640c03600072241c0c0c00b500b03e07005e1001c140c4442090768030610740d180703070151a050a241d9401d010800c84c44600c4852008101050030515950b03003078a441c0c03003800300c0307a61100c0201d003141d881640401d070b410341300078000c0181801107030024116040e140f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870256384 1250 870255134 870255151
    0x447070b0901150b03060a2304060f0317040b03040b150307081b04063b070806010e0a15122319050f040f05031204030503060f012d0212040e 62
    0x142000510300b0421070591b40103000c002c00c3c0c000c0c82400c01458800c1c0307030101c40410032080c00c0241402100d40b141e11901020300080000c00c0182c80c01c604210034500204040c000100b80100b10420011001c0810380307400560054603852140c4503003160b1071201c122100e24685c103004802c0d00040c40710300000c4101c00c01c03110048468010b43d110040008903240c900c40c04c0114819040e48911074450105042400305900d080301070341c5840c810707002d91400e030111500b07804201001d0900089603004011420300000031140c456000d8280031101c0015010854914180683c0c1c001200030501c00390000c541d9000c860345100000307001800c104284400a03101c502131003d80d083c174080042c0890184072310806180d90b00b01500d48595480c1c125113a0016401d48413800188086541c02c2c030701410303103401540a50790f5280c80e030030700300c0c10045d848980d14140e5050080c1c00390103ca08101e81c00110700c00c60f80745098035084803601d01083e42480001c010381c01a41800050206552058181c03242c060501ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870257634 1250 870256384 870256421
    0x405180c04090b0a0b030f16170f0703060b04181109100e0c09040e19141f090807121d0913060c110a080447070b0901 52
    0x284040c08112403040b080076003200640400503241d2031045d0402c00d10090068111241418000d0740c06050548811120f054600443c40030403a1003000c4400c40d1140c1c8449020306600008400038540d03982041c031000308129180c040f0101c1980e510380c0818205503c001a00b2644001440e00e1240b400024406d80c0c411002000882c0c0d8200080540c1416240c8030f107401011525401c0c1312010351b401c41c40307501d81c1c0292101003503c0324803030600c6003188030300413441c44078501c51403890304917441410b00040503482d901410041ca00303a008164060700203415204001080061401d0110040c4180280600030030820340070012085e511030078002656071030349013145a10500030108186410155214031700c1d4107070315001c00302107a02035000c00150005414420311003540e6900a0381031066428060f50070000109042012424080b2071210701c0742c0c2102081c96084070742d981c898042e5000d9145040d603070303450001c06020365010022250804d4200749548610f10340000a14060310030210a450312605 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870258884 1250 870257634 870257653
    0xb060f0312210105100c150f3801050306030109080a050706050604061202130e070b0d1d1f0906021305100206070f0f0207050a0b0a0807020f070303050f09040518 71
    0x19649001c0c1a114000c00005440144240442c1c025109520645444409611f030200d008001d00c10031230040d00341c00c1301180401d56000b40640c14141c3c004100104100b07400101c2e90720403580c2030220230741d000342451031b00c0c1e88070000030900401805000070514500050044640c2d5000806400d02c144110340a11603940c0d89001c1c00240d80061003001100c55107000001d00500d4034030004102c2c100030180010340342807100030311458115681d0003510315940c0041d282c02c00c1d4200303000305982a05514044031740d0000c01081d5540d5008a0070800c5a07a040b21818003100e441c40750002b06035250444010364451010481149100042c0c0c41014451070440d0350000040d80003043c1d0b00d100d0442611400540c5902c50420b80b8441c10f000c6425045003d0054040b0b0035540d1502075101500c110702205803110300006018008941c007078907900c15944608440201958001021030940e82d1500c1c140d91142490007011020b8081d001c0550b612904140c1000a40c0410111824813400700740200c52407a030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870260134 1250 870258884 870258937
    0x90932010e09210307031503080c16030215160c140a1212051305090112031112030106052b0912031104140307120606031b120b060f0312 60
    0x8200609501e480840030b4401e20500843e5000d16403001150802103180c0c0c0d5070701c4e0303170174640d0207907030400c5a0120f408503444c00c3d20b08003080002d81c09038000e554601603e00310f400056201e401e00c2e25015440c400007800e8100c0382149065500039680c0001d801002c66114088691015a6003082d24065880e2040026202d03403021404402103810a0401075a9011448226815400f40071400146400b0000001d0030341c03101b410040c000c05c9014210011060300d45030007010030480c141c04984a40c800902201d11900910460381110312900781180e5944003d003100d00340a1043d0350030755001c4555460240150400c0e0814507549100d0040d5100c9204031950580c03c8550030040a8440d5505101c1071016012544203c170800600608030303000c45681341e511004000805900300e5070180c4400b0200704000701400e9042c00980e545441364102c43c00c2c244652001d41e40e0510142c100541600030a00c50b03190b079541c10f0410440a410303070308903500c1c050358900709030f0105603000300040741c1b00800b0a001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870261384 1250 870260134 870260143
    0x18010302090a03051531060204080f070e0c0304030519090e090606030609010615140c0a03120e0304060c08070c030819021902060405060706060b28080601090932010e09 74
    0x1a620000c0c6d0100d07080031904000000150807046030700716820880410520800c00441414090040044c2480c2d414034045005456001e0208100e1540c01d2003840006a00f1405030344510040344d2101c5000c41d041d0348100c0300f00c240c1c0d81c8407003844c044200c107001200101062141c4940310a40072507401707403200c615060803a12203200c0d02c000240070a484151140c4603001041550081c0104c09051003030604c2e03a24100590240c0c11408907400b40301c260081c0a207806400e001000800295080624101000d0300d554460031006045500020340c2c03100708800c501800d009503400180780781e2190515030790000d0004002c41d68501501c02c51545c030b03d1811045402c00020380d4003404107400d0034a000280101a0854403048031216160070004c9211074901024007900c4120f07079240307074180c0c41a610b0b907480b4900d03d00110040040c4407080242c3c5982102401048642903200003e407140c7c143c5030004603850b11150b0044c03003402c641d03060109024460340127058907420f070f04200341521104005a0764 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870262634 1250 870261384 870261421
    0x312020f0d021b220213060305070903020d061407021006140d08131221030c090b1b150a2301090522030206040b010f0b18010302090a030515 62
    0x60344211104000c100d10240c020145034000340102100002100502c200312504c50a12544c00c3d9000c6180d404005074a0840c00081056040820850804e4a4010144012400f0190048000b0004a0308129080d4088007154803002103003201802c007000c0080d180c010b06056125403508180e400301d2101058080c52600c50401006402e5545295440800350307042802e130041d0800c01d40100182c02100d00000c02d244912450611040718031911140081080e403000080802d817416141400d415085003a280c00d841d81551040e0b06d60b10102c0a07032111050310303212600107020300030f0600e03001d8000d03884031405229002030a02c602036041080c40d054074000c0061000c01d003200401040a180380e81d00103600b210f103000ca6400c211303611150000c070b19080800100d0043e40040e080205000001407005d000d805265142004246441c1200605009071301340d00c1209070130116100481c0c0e02a50403280f031504040d101045c0140d40b41421511361005a42c84a8a154444002059020b508100710103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870263884 1250 870262634 870262637
    0x60b150c1e07051c050105100e060d080d060303050d06120314030a180f0614090703020108060307031b0e0901020a05220b042d060807050a030f02040312020f0d 70
    0x301c10725a052081c0d0724000100346000c090007010350100c0c1540320000007104150035102c0c03180ba01e40c040d161007401c41d000141196601d480303103c0244547c9100841c82600032104503480b201100322401c2a11702403042c08001c4048500d492000402c00d60004003038424903240306e8040003c1c0d960340f640c0d0418412905401130000f8951742c812605c400096024680104440d10001203044802554444278402a0700a03192441070781141000c0041c103008500c44120344501818040c00d000300e110b99241d26601000741840700d4000060119142049868021500114a4154248090300500c2620030b18000c1c0769600c100c80001031507840b81402120314686e550707558149410131807982191000e16010b007184400d81104400524840070401a00c0a03103c0c442c0c600800c1c82c2c007650804030102c00d950021102c8203a80790f081221a80051025034800c6280c06c0c0175940300c07405c0c1070440003407108405054502d4404240031041c005d040c0702204084020382c00300c0307414034803d9450640d5402c40000040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870265134 1250 870263884 870263893
    0x1902120c0c010503040c03053405090a020d0f051608010803120a0f090b0f0619032d05120a03060603050906010612090b040501050709060c0b072a060b150c 68
    0x401c01d51094005543c02070040d03c140ba00365490780d0b1598241040b54802c007103850aa2030740102103000120703081e07180744030355108403d4051510000c1a0416070040071092800c1c0c1c00300d200d980b4208250040741c0350310b00e0f00c001003101e4a03100841c201e507400c840c9650310003d4080c4001060b10000081258985c103440007000e030303084d540d004c101809045160841d640c180d44601c03480001030802c6020300c1c060002c508100416203400410300c070301180d600c982c151145c0d8589070200040f039140143c0c0c480700d8400b051050041d8183c180700341d86010b1007620044c440e100d800e05130351901c01100040d00b0002210b0340d050140580c0c0700c07400c406440c42518410f80c0b07500118010007005010701441601d500b01d00d0000f0900506035102c1e0742c0f90030000c81d02500d10765129010803000c40e0740000b100b00a8510380c140751400c0d90701521040d080200090001041c0300340020b4112045064800c06800e18214030381d480300404240c034003800a40b00c802007560003030007590060480c2c603030444161003081c200d407030080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870266384 1250 870265134 870265153
    0x302071d0402150c1608100b0f040203040c18051603091212150f0e090102131202150c010e0606030c011b0c0e070206091c080106050a0908031902120c 66
    0x803038584803d071281034981004021984010200303216011203003822120000319a80340102c8030342850750072100101c42500d0102e10010550380d580c003800d052401501c00523200d40c0d5915154010240c4c0d5009012900c006489001603098207401841c484c8100311f0b800c07001a84010010745c02d450f07078084020111000b90741200915445060005000a095140819002e650721580c01c0c00244a42050308078440d15402801340c400d100c0081354011007410700851030001e801088640780c41c0b990283c1ca902043c00d05551040d0360710144802000040e901300c0e039550f0440844e0042c001c00a20104034960700030315001656030700e40071414808007a010f849404140914500a480424a0460440355405041c038082682d550605107141b16400f690020b0804e0f0a2031000c0a1800c2c00c0304808000c2503101c0240400131035800301031541100d40303030b0a107251242c54800061300e0400941d0850485807201240e0300e200035402c20400000e81e242902a151441160400c12209102c3c1c1c000204582c0d1280044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870267634 1250 870266384 870266389
    0x1c03200708031506030109020a03060509010b0f03091507030e0c121b01020a061d210a050c0307120801170a12050c0a05011503060b060c0c060309190b01030302071d0402 74
    0x11544010800306640c81a004000020b0540e04281c1182c00025404503102c109c00e6014070130080600343c21a2010081d624004c4107085034420a042d4496807600400804d800c1c0e5420032070320044040106040d0781d60302d440390008005246600b07081d8440e10903082c420340075081520155a1780c22490000c1d01c1a4120056031202c1720310b0440e244d0781148109214040480c941d4030981e80510341c04015203001c111848a03041c680325105100860001d003201000041505000440307021454905103035880c1c1c68180741d07180c154020510082d0103003504d48250481c06520203c0b00f81620980321301514900c03900b103d0145e541c281c001c0024240c00301600d4076944240100040e007001d2012200301e4540300195680d0303c0c2516800c0c0580a0000c1a0080910801c201c2c0c0c040c100303100e4001c2d5210303410003c2e20268150389035a4442024051039001010507498070b07007800002103c0d604043c4942c682181da10f0300314040c07202480103400600400c04007003004075244610200ca440400c01c100819107607a001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870268884 1250 870267634 870267637
    0xe1005100f032318010606090605190504120c1503021303061505030d050d11160b1503010e0715050c070b0307021f0b040b01030b03070311030304081c03200708 70
    0x890f040c03140d400c2d07405803001c4550902e41c28400c001c40811002000080d0100500351062500080280100030b0f0060000035800070a4490400c01c3c6d24002ca002006030100307841900c40c5800100c1d500040c555000203000c51036000d14100d032501e440841810101010441c100c1c040d91042081d80c03003c011381080811415000a0f41b1450103180d00307180c0c10b50310030000380f0308039412400702d0209001080c00e0705403100c584640c1c11403495408015252900805400c0c504046201c0c00910b452004004641d40d44002002d041030b040018008100142e4082d803c01d58840251040c03c00550400036181d9915204030309440c824400100103188d0141440c0405100742c1008040e0000c40c4109107008080c41080424241401c100d9140021144400b10520050311079403981e40d4189410075000404035100014080d044030340012600e812941e420340040d0541c81190300442151003680c009034401030791621924000741d41038404100101d000c250681228400e0800200343c0d0005011481c00f1440b81070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870270134 1250 870268884 870268901
    0xf020d03111c111c0510050d0303050a06090204061d0f030d0c03120f0e0c1f0e1309060b0a081605010e010309060c11120c0709090218010e1005100f03 66
    0x38000c50080924180c3c400355401003d0b00d0102c244a400080e440c030300040c8035040d003044005a500102c40c1c180340224412040c00300008007090b54840c00900c142c48668090340241100b014295552a036603640209041014124264100410601da82851500382d080d400c1d100d4001d40640118024810103641d07216100f08154140544103030103810f0b00c0f5891059022040d44008005092551040d90900d407003010041c2c02c1c02481c051084203414900701000380074542147c500300c14500c445c84007044007011042c0000e0142801c0440c100d00f002550703006090b0844003500e80103410ba680b4120607681e401d20483e6100004060700b0140010b5108890301084550181000714414526036508405c0f6603d010b8803100151a2070308881d1441414050102c0e509010391140d070509001404842d00c81c6650302c1000141e55607550342d4821500c0d40c242c0110840c4209186e0030b5250395900d054118400700311641e03c600c00c0045800306861401e1000c030b1041c030140d035a8901160015440c2500141044e9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870271384 1250 870270134 870270187
    0x10181202030f07150b0301052e030c0e07080c0a0e0415170a05010c0e03060115021516180b1b07080a060225030507060908190f020d0311 60
    0x40006030144842c081c003c0c00080e11882042180e036034820055402c4072502c03c0700f54402e074103000601246143c40c0030a07040f1005010203280c2d252035006a0790103d05e0941e807004140c84020800000e4180f2441080c1d48a8146516012807079522801e00070418442c200200c0017080304100c10118a0800354081110040c20341d82d40c0000340e0312070f4845024910112180d840c01c0c1c2c4a030741210304221082c020040c0e10314003401c203031503041048400292680d60500820006520559000403418030802504c000d1031003201240303990f424012505143e039500303c1522008a03c051076070b603d550280440213400c461040e00c065080403605032500c100d005104842c1d01c0c65110740e51012400060a10207040d109119080059455a004140c54080611005000300d101c14145092000c2a000403c54260540c0034000141d65466490011030b540101c0c0040b03d21402204007501d0340343c1d081400095405059000c842c0b18414031941201500c0d00706011f013598287c01d10451f2454445d081c0c03086040ca204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870272634 1250 870271384 870271387
    0xf010903331a03101b08090a0803070207060e06030103080a1209052401080a0210142503170c0406140910030203061009031109130219081018120203 65
    0x801e0840d100380e91500354510409035080c10300488926040040701a410356851062100400e400001000c0001c500e058009211404001030390380302081c040c40c0c2c0c4484e80602629101e04003201c0096580f50140902e20100e0b680c6c041400035480d09005581c12a85d01c50030181c034104004070111040340301d80100e04600c0b42c50350140e00c0081c034180031622104c030a480500c1c14000d0072701021a07100301c06074400022a08032214106c056181c44540b440791030128100314004c440c2801c040540b910594602c6216815003e1892252091003202e00104600990ba100f10401c080244141040015500e500703a40108010810a4a0080035540c0d00c59030400c020509021282e0042480c0703200c0e090a501c0083e60001c00c002e01441e142c0b18885034a400d42c9441c004190541e550040d11450040c3c155110724440c100080c500c4801c00e0102902541c0504540c47ca903d141400d2003aa1005024000c0c5600581f241711142c0c00041c428110350012010443c940e414050300c1d040c1d1500561035416086020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870273884 1250 870272634 870272723
    0x9270902011815030f0b1804020d170301060822031101020d06170d0c1e0c08030a031b0c05030d090501020c070b040e1308030f250305060f010903 64
    0xb090000300c0001c0c5062100c0e481540c402d15402030440c0c0d40e00e140e2400c1d1070300c0d041d80500c594484640f00e07030f070151400381d090380181c5503800024200440030310000c0c00e4007200f80301620703041c0c0280c02460498026885000c040d40751001102e1301d640f001c400e2520f070004d84401d0080443e00c58050718240c82044400103107001142907000d81a070b9000d4101080000c1a1078141e100002c0c1007103d02c00c0c01c040380c5003816481007142d507002022080040982a1003240031344150030302807503080c02d10050800724101c03641c034641100007030050983e18911443c4100036016001040b40039405441003c0d41c40303c0514a8030080120f420001c01014006455941d400e2110051520080050700301425951f2949a2110310301421701800e2140240201f100761400452800020340d484107403504921820403210203540c0384159118450200c2c400000c2940d40800030041842d0580d2000740180300641e01455070001400065905a00900c402805440d454400d45011510340200304903420184001840421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870275134 1250 870273884 870273917
    0xf080d1d0406170d080c031602010b0a090c030b030c0d080315031615031505060a030b130b030114040b1602010e070b0406020f0105010605041502030d020d0c0927090201 74
    0x1540b6400c0001041c03403c20b2550000c9404021000c90b882c500d180000003031910142041842c00064000c07034a0607183d60303000038564001e40094080440c00f60505100c42e0352100500c000e0b210140c00440860300c1c04c0750900c118203000c14158962400907000b021150349070740d07400c6c100c1c1e4801850380500000d4800d40500756036080c05061881107000e400600c080b824540003902002e607950302c420602d807a26000244144004103d042102c404561080e1605c4940e942a00a014032200180d070160200843c09100010b42d07006108140c0c00703400811214400340301d0051078034070030345018214031042c0d40000c504180d045101840c0c4c1309a480081000c2122000303e515041880d0000000032401040c103110881e03040182c00384c2c0003074880007400030f94940b60000c0e140c0d12580c020354069140b0751150320101ca000304211840c204102e60110340d107440d81c480c5140180126005d500004544030000121807031310621818410f4030401c1c00c4095203800d860340100070090359404070b05000d100a418104503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870276384 1250 870275134 870275141
    0x190f050c0702030f010504031b0201050c010e010203100e010506030609041704060c060f0b1f030617102d090609120c0506060303040b1914070c03020405010f080d1d04 73
    0xa03024200d0280d101d5105104250a001848011000c541e140404010210760701c0060385100c003814180c50110b20400b400101d40a11908110040a60030144012406001580194401d010b542d400b10380854072a205181078041c207102c0e0720b903c9203051011414500e049001c994000341301d03600041d00c40f02d0864480640303420680c441c00104203100f98070403d010042c025400f95540c0000100016128600010240702d0841d01500c03411159059218900f4042c1d4082c002400c008c0d00742410400c1400840c65607020032007441d920260500603840c080311403080c03001c0b0303410045d480c0c0c1950b101c41201140c8020550701d00240e070559115030100000c00d03035018010043d40001c1c1c1e0341c42d08030341007400c116190460180490f40294010401001201c40600035500e2140c0c110001c01c1908409100846582c040c00c5000e04e80d03204002040c0d41008000301000c801c6a100781d070240840c0c0c1c0d0300d281e40d002d002018852a203094210040701c1046c5441100011041d06139840f032075034005001c90108044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870277634 1250 870276384 870276391
    0x9150b03031b06101d07110f1506040e010b091308070f030e040501060f020c1201140c12090109120e0d0606090e01050f0c0702010f230909130b190f05 66
    0x141e0890414804e0104190001070301503c2105c403450a00700a542410f082c040004100804100c0440c502d910740041c10302003405c06031040011a990403c088452411501c0296003c0748124607048419401800601451101400041c41d0301340300d588001014100f01020340703003100d40c2d5604000c0a40010780c0c070440b080c0c1190090b43c41c42440c52002041c04202d0b00181c01c01001d02c154850307a280740c0ca500260790300140314147d40140c1e86040e02400319026110b0704003400b940c00314072000c12410b014010040c001d028450303d5840000d455a0190350300302d070f000800185c10300e049843c5240c900360203800718010ac40801303003000240710348a40b50b01c01128181e40001d04695140c1e189a200c50000b4010280c100b04003481c4c410a608040ea00020750380300b4076200138140449071a04218050080c074401203101c00c007902010340d0000d9540200d10f0341e401104600c2c03080c6070180c04554003100e80810081910740c05000076009488a0b03100da001c5041c0341e6085020647c5a1a0780080d080b85402010301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870278884 1250 870277634 870277687
    0x813081207030c021605060f1e030405010c0906090501080a05041a040c06232a0607051306020a051b0a12050102040f0e0906010303050d18110306010909150b0303 71
    0x314a403084100070700702074078030a0741740710304800420900040da642c0040b9403110440181c007555070a41b5640c044039901c980841d103401e146020041100f401019080b11303104580c0d41da105031002e5200c40702a28500e0b603a0141c180041c1c218000108140c4450f40f00640250203803a5841c0011a0a110211210401c036012141c0c559250710170044190401000f22081c1302d9010302d403400508404501d5503d0050a002412521000800b40107010f40986840c9d840680241640d140703242c1a0b4001d040c1c5c0d40f046040359800a201c1c1c00024400e03202044a01d0107a52001c060052089070000710042c44078080403190340701c01c0300240010f44480e48100403075694804c600150320f483c0b0703015460900301c44590180c5544450a010000b20b4400031a040b0f05490345070502c80d84511040358068010510b0070030b21102c125180c40041d0a008000d4030358501c42c1030072400c0f138003284c2e02e0344500c60568040400051030340d200e0400039101c080030303601300102c1d402015080f00c0c140701100b80c0c40c1c1c201d407100d03003003041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870280134 1250 870278884 870278891
    0x4180c090f02090d11100e0105071b050a032006120f07090f060c05150603150403030609060308030a050c0f16021225140d0809010c0803180c0d03081308120703 70
    0x780e424142d0746c03411400d0300380c18080d074031100700d40000e421b40c42a0382c0700405800c207600550201100f404103800190070060201c8052646070301d06138008886000c0e24003042401c02c201c00050f850000203c54810001010040090300d9001296644c01c1000d0001018003a8100c0049940d45081220900404442d1b940c40000881130800f02d0400021000003400b02214a08001e0075880001d4900c602c00f80c00044015190b480d41012801888950800c603840d9060070000000e201c0c941020754000c01503240100040e4035020001410752240401100d8001030500c070070600007484a6071210f989001600114484410050043c24101c0c00881158642c40201001412000b081c2c011006002c42040300680f8188030740c0041d0051280d80c60081101100151070340080e4400c0d088840c1140d88807a02c035880341480694801d6444800e07120120b130f071044001c1020649003000c4034078615074041e25204ca1035100c8290306070401d012800c05484003242008682d050611881d2900d20501103940c002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 870281384 1250 870280134 870280163
    0x13090b03010f02030703150e040c15030b03010204060906023a1b0f031107270b12010e0c010309021003021b100506011106040b0c09030703080c070504180c090f02090d 73
    0x1f4200402a041071100003880700c10040041c10048501e42510000080f070700c00d042060900f04e01800c111034840390594001324000410a230841100c500f078818503000d03122400784c2e0b42240805c007003601024403002c03610440481c45061003d41c16030866203480c0340841e560120307400715039401d00003041c01b00c070429185810341c0145944686a00c0e1440c3da04405001403618047c89030b5296003100d004003444607001511503070030b0000e99001e21031100e0003400c08241f40d82d003001c90a00034002c90703a014166000341c0712481c20719032092282d0024558001e214402c1d200fa0498124002c6d00034038800c10019100303164081ca1260100849602e038030107100e01250f2840c280c0c0004100060803444488180c2c003200900c4001360b9000e21a662180c00751400d20b81715942400040d1600055a2001d400c840c0c0c001345004925802040d508180d540543d024809801c103d440401c0600c106040541180440042444103108681041d074449080341000750500081e0760001ea180d1103101811914111005a01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 870282634 1250 870281384 870281411
    0x120b03030f04030c2c181e1207020d06020306181008100b2409130b03010605010509011e0309021c0b06060306030703081b0f070305070b13090b03010f02030703 70
    0x642c0050894a111020039202900642e681c40e60a505d054084221510024000101c80701c071102c0c9481d1000d040780c224401d0306207141e0700354212924010141c0604411441c500f402e080882d140c5a501030040741844403a616400001c0d04080d02150740034418400360f69600f401c1c030008502520b480083c030000710f481c0503500f80c50b01d85c030300d002c100b0041c0c2080360030b4509684008508410054000603281185148610000d8038030581c440950f200000011989140700e1690100c012058240c008101d419194001914180120b2010500240e80f40f65244505400074035003030251084d03130401058800c80c070350000750045a07021410b1075580c0110750700400d00040b400400d070010030540d605851070528802194603800c66000103000c80c0800a01c680c000220303125240b035140e12400079940b04504c1c0c03403026501e50300a88000e44051203107440208914030807404441c800d01c1442684100070349000307805c0010300350380c5c0407a41c0c1c503542c1da0784514104821400114411364071071703400040e05e10f1040d1070b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 870283884 1250 870282634 870282653
    0x4030210050708042301110a0e120a050a03050c07180b010f0801030b010b0f0c01061712030907050114120405061e010e0c03090304120c0e010b0306010f120b03030f0403 74
    0x180c104021880c070034000030408001c46009004c03200c50300d05d0b4020111489070f43c05082d80c01011520048001a15089940d11082a445aa00c2103814031080d0349405c10503036503007040d04170140907500000002000207005030b0040000d11400700c103641c1d090741d660000308082d0311803500b210591506d0340300c3c0b501d440d80c0c460640b80c01c2c12040e00f0524015411911000d0400c4014001c400c0b02080016040700c600e103030700041d1107800e02f91000034442c1540710301c660b180d540044d50501e0114403c51000000c1e200100d02078a00ca18507600040884c2d03441c00c07004544003000703030750014020b540c100304452850302d80d00286403203a8015001450b8a05210a403500c54550103030380d480750541042c00511038910700c4002da41e08051601105902d948410703441c4d90544c0714940c03001010588800464040002d8098100c00300e820030140713000241e07a2102c20525507c0f04640490001d00040c001d01195801031404251030700c00d0010000381030b00038a0100307103982d000a4400404010209040080003c0000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 870285134 1250 870283884 870283891
    0x60123040e07081005011b0b0415051b0d050c07050f0c13021c0b06040e07020601030302160510080c04180207022107140301020f07210f12090c0803030403021005 71
    0x540790b2218544131150000001c030f18020907042110410050001c0da280c4070613100419001291800d50f03041c20f28028024891540319005041c1c2031900143c0303011030044510b60b070b00d0102041c0740d01d04403100000800804d001010390b090000309208150200d1810841d0400d11030304c500c010101d2a00c9001041004034280e4020754107103004010341840d410130140015481024072001040790708405001841500842e0002c00541000c0f104012505500003000ca048902031340079aa884101038030040e00280090180c99007004140b038400c019684180c507000d50003101000f038281443e0b29124090051002002072a05071600030800300198500111500781442c050f54a2103580314030b2800c92a1558424816003180410045103040191029012110348a1414201d681e41e0300042c982105181c0410f030300101c41200e9107001f2a80309010300c0b4915004c1c0d003513880d90b203a41030203901d40e80c0203040c500004548030700b480c5900040c4840c003000a18040c510039000b8014600c8412000021514010f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 870286384 1250 870285134 870285137
    0x60a0506040f0b0c0304031b031203110711031f0e190c050607060605100917010b031011190f080a0b010c02011409150903010b01050918060123040e07 66
    0x4000801020318080c40e1941180c0b2850762061311210814081c2d0300758003541e440900f0002440004080d003421000040090345c0c824980c1d6004c248084e14114203c0c0c880a80d4154001c508010004c08100340c000d81e440b21401c002c0807529400c1e13080c1d40c4202110b20140c0294516503c0b401d854191100c18002c500103884241030000c2560b010f5114950504168031074076001d4000016444140002c0383c100c2405810050134500c106000703400b00420900c03451281d014440f100c1030841c0c00040307041c00383e0280c0b050003d004050b40b000710007440c0024400840d120581807020003001290311088504001c07401955210b40724206110a400b41c80c682c401000000c4080c9000b01c030601680e046024800500d40a2901341148001910000300c14480c41c03c0045e07204d20f1422071500c0740d00200d00145505003041d4024001c0703140d11001510240107013a101035006954905070341181d19060700c1c20703030b00400c140340c03200850840d210013881d900540c0901518808002034140101d558a0642c03c0d0001c119 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 870287634 1250 870286384 870286387
    0x30d051314010c0e1503060d020105130b190f1d0a0302090a0b030d0c123c180f1a070b01060c052406040507030b030708072417040501090b040b060a0506 67
    0x200481303138065201c0100003a07c245801c823034175001c1da40326200b40c4104610b40b0156400c150346600100030580c208003011807148069208840c04103102d0011017000380e03401e459400601c8400d0017101041071000d07140e150006001000000981d030307003c2c038981c000d04040c8000030f500c11404090508003d0340303000c10818000120350180000d078000c6400c48100711140740c410b00702140f0071408814441e80d011030b0364020300b1042008001c00000d440070b0700c505200b0380b90614101014510308100c190f942c4520781c1c1e001d18131402000842c01c0c09031400d6042c22a003035103e10304202c607a2074084021080e0068000a03854840c61820082b0401219502e041075142040c03510354101d06100a00c440100518021500d8501041c2220702a0f002182d500c1002429289210303100d010045c2c2e9440248115101b00d03070b9080c00c007180000b280c3c018084004960780e4018241e800d100305001c0507100903004590540da204007500201d10b001c46120300030f5200307824200850800c141001204034054110391b01c030700c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 870288884 1250 870287634 870287659
    0x30f1605040513051504110d14060108061504051506030717100302060d0f2a1e08040212030c010f05041202062809020a030506010303080711030d051314010c0e 70
    0x80c00a0a41310320f03c01c460501407586e890b40f8101803004c06514080740c100140030321220070401e000351b0700003692189000b21034480e030381c45030310b80c1d902c400c03e6440104110342c41d4120b01c12410281c2140b9031010800700c549540c181031a0100b062a402220b0000015501e50a8131380742c00788540b001500841054103850f07480303003517400280d250302c14800350024031582e40c5c0181902071850b400c5030340b114605030781c000036550000c0c034050121881c0000301c2d0002119404c1c44042e1594412032151104180c3e030341c1003041d58440d400e020a510302104c0d003e08604c402c3c840340001c0e4900b40110070386040007803404221414285002e00b824600c240d08401035410032803c0000e07042c400500c01c0040c08041c200a40c4403000401d08900502d6400c0c0040d40240c09904003000740314001945504980c400d5a1301c1c1e402c1c1d500d0307500c100c41042540404241d150020000381d421001a5003146800542c6c071190910f00010554071400717007442c2291040c001d65103e00044d4011600302d02e02c0c24496100b5583d6803c20300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 870290134 1250 870288884 870288893
    0x801060c0308060622090515030f0c0d0203160f060e18070e0d050109050102070c050d1122020c0a0303051605030c030c0708070303090c170a0b06030f1605040513 71
    0x2c024070300e0f4014031000c1003803800d00760003c55400c080d510051207100b000341c848040c03001800d011079401e040408880304481d0b041c1000038450132108c8131000030349088040c000400481414804007aa4144151040d8211000507100413100a2400740111008a45459000307045202c40e00c1c1c0c0148624080b24043c007507451590540c6034840054584001801d200b070001845070140c03004090080d6184c405c0c0441080015802401c4090040c0c0200c6540f95071501000300c04a81c440c001000100d031303804e840010707003009581001c07541c001164101e01e418640c2001c2040ba00308241c140010340c0000500c03070500d5058481c4c4c81c2c00c2681c0e030301240c1c00c0041c4103c0240c070300d11002d01090420100040020010a0640280c1d503405900552080e550368003818020702170010341a05503246d0002c85800103c2c0326038462211880c1c00c014001e003403030700c01513140e031251074a0040255030940100041c0341030301c140600c00c0450300807500380450100350074541408112080100b192070b251141c10140c10214 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 870291384 1250 870290134 870290147
    0xe100f081c02030408031611030109050d0509310c09080c0f06040e040308100b16020105030a1b0c150c020c0613120c05010f0806090117070e070f0801060c03 69
    0x81905400180078241ca001c12481c41c49a40d000f0190381c000801c0d88036451003c4145801000e015900000084209104050803102c2c0510020000d60000310344910300b901620191076074480007841c0c4039101248900080895048030726039451500c4000141391010554454401034100a01e40607800c542005406a0354040c02c0c1c0080e44584007070780407101d056072002c0845010345018084821141030614001d0b1034620709881d084a039881152001c2054403e00e41035400c07401c52125a0921b00b50540c0054841794005004800c0141c1c0311390740040d40781c130202054440d414559a40800060050411001074011442410b03482030806180c88982640007807224451081169070aa4a81e124080128044482d07484800d54505444189050008980f0414100c60003a20360090080c0f0401040301c03d0f10084607180e0744054100c006114080000c00740e100310401c02ca046961040e150104810304485c01c032603910000c0c14240480c01c0441d8440c84660040c075682c10180c98030301350783e6400f9048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 870292634 1250 870291384 870291403
    0x303111b0a1a0c01021201060f140f07021f180f03020a03170d06060201091e0201082a0f030103060b06030405030a050a200109030f0c0b15030a020a0e100f08 69
    0x1c501204010110303412072001201e4043d441d2200865540c6190544141a500240300e000b000ca81004420101d603400740814800a0a0000031207140002401c1c0f0307103609401146060b6003050035a50440c030710107080d806416221038142c47e160120b44440c0c440c100c401c08141c2000380c01c45040742d810001602c6036140f01c010b50350700c2800104d042c0004280d0054070302411742c40e03250041c181000041c51a40650040034600d00620b5040c008000d03201d8035800e4007113041d83c0280040d400c040011a04448242c0d4100e03100d1140340f082114194141c806a129000703000c2c00c4140c49400030041081200d00d02c500d02110304140c1e003a50652620b601c2d0a0780f0b9010780d8210f00d046c4007001070307600556807280c00380c2140c000d928440c00c2041140705106a00030080e00300f04901080640c5042c000c1d980c01448401c0c2140e82c8400190000d81d10341c1400504078030001000e5406100d81240c030401a52900c2600cae0113460156003010342440c0030884900c4c260115402103140d1148000240b180e01000304804d0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 870293884 1250 870292634 870292649
    0x302031e0a0506010e0907060f020a06150801021c05090d020303070f0315150806040e2a040203090a0312090206030a09020a09050a0b0f03010c0912110306010303111b0a 74
    0x6110401904040c10064410070081981c000c0c40000706400040b40a2035000700030b060221b800c440c1e265041038521150100341400582c1c04128203000140803500325900103905550300c286e4255584529078260b03040602c040c801c0000e50387d48400d24913240e10401d0b601c1215000240000000c0d0940a5100e00c8081d1035242000801c4c50021350141c00307a006245000500002404401c2e41c60892203a43c000c04001000082c080402244040c0341c81e024405000d130a55010380300024400fa606030f408109008610f01f5002441c100241590b2284091889001a2000303800c04a000745002403540e000e41c8a0214030310b2804240d0405a281c1c4425294012244000062200038a000003807480741968880722040e810f2a04001195020350003445800030103860101007102e0450816090b00c55088100c4000307100b09404014038145440c0c6440c80c2405080d40c00d001c045900040307803e2003802d0b082039010400048003803418180400c00011913409449402da407071810340c0c0006900c00801d108014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870295134 1250 870293884 870293923
    0x5010b0406230415121b0f110a0303090309081504020906030a060c050c16350a0507051302090d03050c28020102060105030a0503090d030507080c0705040b0a030203 72
    0x102442c0c001d4101d15084654100030648442c2e5440911107081000c1000380300041c0054440c10381003885000c0c004555121001450300b1220541c4100c0c0d44e0115410400100102404040d816850612051942038065070700462014454200900101d21541c070002c80c0340c0c03080c003082c0384510481d441c1681184c0d04070f900e000f15489a0000030f00d49044020094280381c6881d4082c142c954005000704031007440c1c44196140110219641401c110140c03140c668080d28003481e120305101056180b44050410134103a0313a82d021040042ca1915a03a00c40031180766000b81014032441ca0140034803d109480329000703514002580c000304103081201c02005043c00004101e5040d420424010304d140030310604c007050142e9028030b02c140400d500191003a40540201d500101b01400d02140041c20755030410020f524020740301042c0441c1039407020003901080806d000b08400070b6501c1c4000d0000d048503c0060111038201010002220200740b8001e20a0071000001c00058070082002c80c02c00d0141105407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 870296384 1250 870295134 870295157
    0x60906020a2306240103020a0c0f140307030306060305010b030c0d0911061c0501060c0c2102040203070810051f0e0a031403031b03040c270606020304080c030105010b0406 75
    0x1040c501c980007803100950f0041d801000200700c102001c503180b59a0382ca4603500c0c00307000400150120722803511140c0008001c1e9038240d001c54040303900200800d1040c244000360381003212005046070050041180082c2d1a00c204210440d890b005c1c10340500b506124481c55400c003030a01000303501c42d809043d11001e480324480010302c101d10b40b003001d04a4014001c01d42e1243c0c4200a40300b0040d00f46807004641d440c10001261051085550310062a48080b0b40451542010440748122503d01c40303c6110b5104007400c0303801070322240003660191280341c4070b02c3c8141c2000f43d034a10400c030184c1c01c058002c00640a800b5907008080c481c0030081415420031003c40010799010944003507182d00301800c45448407900780303034001c00080258841c2e1506d00c12145c4c001e203080b0780c002e01403000742c801516200c900c450600c6902c050001c034500c4100708500030040606100103000a031030095110802681022a080000d5034080c0a04a0207000c110000c1200d5030410b0010f038418012802110208117418500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 870297634 1250 870296384 870296423
    0x1230a0c0e090a0b041a0a05060717070b0f0f04150c230a142b09051c020c01020102040b0d0c020f0604050a060e03070c0e09030d11040f060906020a 65
    0x544060101c05400409240361805118010f006042c0c2481e00a038540108240402c501c031981e4850700b9001003024811070b145c4010001a034000324070a1318204901e02000c2155401c80c030040075180e02c603189030021494500100c244451006010032040d070f00380e40c208800203c2250030b18424028841e00052100443c1d10200d0380800850701108270075040080c04400203003200d01400030703500c4580d180124440b030403260601d61b0090480d40c0388400b243c11a030000703c0c400ca4919800c881ea1000700003802201c0740c1c65982c40c1451100d82000c80c0040029200d42c2141c1c10b0102c07014103038080c0000e6240074a00628901036114000c00c4000c0c2641c3e8510550483d0b100340071801c0c0000c024401c80d61182000c0c2411a00c40b09003840848000b85801e0040781a410003105690406800031400003895107468000c031142c0300000c006007254082080b014801044601c1000e012240b540101d43c2c40301d041141d4544010402d800ca80c0038010596010801c036a8000707500108a81c3c050684038001420044c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 870298884 1250 870297634 870297647
    0xc1602030a0b0901110406020a0305071104021c0b030c280b12091b0d0605060103110406170a151a0d0606020f0d090f03021c02150a0201230a0c 63
    0x80d414020340c5100c0d020310100c52441c502600c8100000c00140303560701e400440c61300c00d52042ca005030700038a0030040480c0c01080035000482c0541c845601e64071a001c002000c03079001341484d00100c0c0420b102c0d040740d1804ca04c40c500541c1c90980080010000500c00030b446503034550f8440320b41000c1c400c4020110704002d0b014034014004c140c0301a4842c03084003500f82d0012000c60700344d4258407a003290725054803003040c0d00d00389c1c0041c0136000c0c0707541d424251118800740070002c2c41c250501d51600b0300c03988114032200c014002041c80380d41d852000060301c20302c80c41440b8098158032100742414011380b00c0300b035078090b800216040001c0041c90312400a0401191b03004030404400306e5840d10f140064002c0e000f00b800d009d62003050064981c0000000d1090314940c0550080124519404600380018109810710380981a205990704404640d0780c1c0c0000c1042c0300c1e40034480440b00020405281141d024040c0700004440e40302d100100d8542503600a01003c8010000403405450700611603c0c280600c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 870300134 1250 870298884 870298927
    0x5010906090c06080906010501090905090a15060306060e040b01050123040f0302030609010603110103020a031d0c19030b06091e0106020f0f2a061603080a050f07080c 73
    0x40080c0040c01d03072801c10850301080da101d1100440c100b04002096014081002c034180d420503110034075014140400380c40100030040c1124580d10400d801c1102280030035200f292826080303070b40070883c10705510380a03091328000d074051181d031202402807000052007040001d043d20000c2c6405400028064401480c00c4c00c9503a41a106840000380421001ca07190300c5c00d82a07a009400710f070300c0c98071041d003c80d08940d5503100107030402c0c03500d08030740810390311a4005244070b05140c500400e80758079617070000d126400c500e880881d0b03aa01c041030006090606010450347c2d0061403600300c49142ca581c592134407114000b1700e064800c98804000032240000c44680c1d0300610031082070300409685550010350f44d007018004403800d43c4200484084001c0300014070b0b03050700f11800c901440c410300200b42c01203c01c00984cc11640500140101f03409030b880c00c80a018264000d5692802d0707400c2c5200c080f4121603001d00035080b50a100b104002009400800c00ba8018162000c10780d44c0b60150040d50b4101c45080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 870301384 1250 870300134 870300143
    0x4050a0f030212070803070818210f030c031602070303052b0e060105132c0a051b01090608010509040f02122b0306060f0c080d0207080c010507050322050109 69
    0x86034400602c481000070714801c000e08e0700c802c040c0d501c8850014488182c56101c07518603500c031045803040e0a074140040c072050442000560304002540209000c1e6400c01c58440c290803030040200049011543c0744500e03003000d20700142c14402d0950b1001000c0d407250f00d801c00d15084c3c2941010616086803550402c5441a01c1000c0082e070440c504d40c40c2c0c44a0083c4500c0d8802d50a030710220822024512903045240d5a10503403a21480c140f1440c0001080707841c403403444a00440c030309000890f800344003500402d10054403415014540c0e4001419590f655049402003044040051141e51142c0728040e81180e0880c41c81c140800c1d00d0b100140003c41460810340981c001c034240394015100c1c40000340d24540780d03203172554042112240118104c500350b126000008400c001e0301c403d61405011003c2d545402a039401d8504060020108140c0e804131388e08035000e543c0050418682c0000b03128140e000360281c07a00c2851801c110440d00e00c0044030042c071141c0d00c0c000d01c44040811000358050802590301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 870302634 1250 870301384 870301387
    0x14090a030611031e090c010e120d0915081b030603070f120b011706010e09010207061103160807020615060408070b040f0902070b040605040f0f0506011d04050a0f030212 74
    0x40782e441e01d07070641080e158108052a81020060b149101c421000c0c8901590001440c01001076001103813031840c404e50582d004500456180c0c1400804d1000c22000d085a0b103622030464980024a900162441c0c501e13004c02004200744908dc2030800d120607100180244c0d0940c59407101d40000b42810801d0381b01081d905580e02001132414034035424134100902801e580c035866030341c501d8140410840e2002401c690b400c02e4005112076561079110a400a02d060001414081e0540d40d41080b12141000304020400c04010020040c1d8040607400c0400c60518014070542040302000c1c0d90791300044c2c428001d0500c0001c85445c0b079141c410a41c1d004286a5080b1036502d651058840803585c010b00030164501d1100c2e4020400c0719450003214681c3d03501400300c00403540d0b0350325101c2c02844003401c00c450942240c0c070b00d07001190700300795075034480360280b0003a216a524202000c2c26001e180035045155010200422003c2100850040d840c140c010040101003540da25080b0f00303241903401d0842503500d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 870303884 1250 870302634 870302651
    0x3031d1e0a0504060b1e040f081e0c0d12020109150c0318050a020f1206070806120d05040b0a0212040f061403270c33090114090a0306 59
    0x584040c050140034054941003809074030b81c0c041c0029218203000c0e40a90300010000310041d81c98524400d0801c03100074503201d05180d00c3e481f010f51b50a800c1ea0140c1901e900101485072080466044c04000c802d082c0018281c0242070804a2080352801d0406002c11018103c280c8441d4001e41005000c2c1d82d00001d046640d2122024280040c030446503000d0000380f401d1030300140e01c6400740350300c810250404000e10150015900b00a401c601c030400750f9800020451000c0c201210411805004030042c1c0c075100214901002844640418094802c40b2a401201ca6440c40350b0080112000c1e5060811090b5070b8203030303402040e40342c001c00854070340700d03164005000154400c2840c10030090b00c1559480380b0001c000c520300d00320103010980b145005c82407c1c0c0e440030034035025a00404014000078040d100c50310411000039a940304641d90300c11555100c4042404120301c0100d800d041061a410540e040c40c0b100000204030032107006441e0040e1000065041c0c244e41e42c680004021036210106001c040d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 870305134 1250 870303884 870303919
    0x91914010c08090706030608060c03100306290609060f070206070f120f0f080a090c050405070c11101b05070f030f060b01030e0c100e0a09090b0106050306090103031d 73
    0xc2c00b01c440710250300032800081000c034030900076203080b0703601c035030061a19480b5000411141e900c003600804070700441200010025005024a014010058040d404061306020f5921a6114640c6d1401c0c13080008115050490703503500c05441c0c2d10b11300802c54031313280c0c00a440071586900c589a0040c0c414146924402d0030403008a20140c0702004650b035902d40c150b00b104c7c00f40e406811065508010400400000d080e082081d404410303000c0c001c400b280b0000707690b20f001c10115003056952400107003145420701c060001c8000c98200e07801d020388004030060081400241070303d1007807100b25011140443c1e44018400c0404c40c460142000c48070030007226a0f00c1c9407030110f40c480544116031141c180f4140009030340c000d1080b18800c0c0300e260080c11025895900f0080c01148100140301400440c00d20700f8070940300c00b094040a4080f61500140e8040355090485850105034802e03010450108100903072519102540b50440780d26040c80c3c00340c260300c01c403000c00c800d112081c12900900c80d09801540310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 870306384 1250 870305134 870305147
    0x2a0e03121b1524091909320312010504020304021f050a0e030c10030f060b0d06140a12170408010c08040b1b031501021606020307021503091914010c 65
    0x3d20f14124003074040c1d508181c000c000c820889220301e9000e07110000007030040c144001000d8001c60001e1000400312410398800015410a00410080074003850b035820621022581c03000d0500030107070080d03052200110304004094414050640a1a001b00200d811500c03008603112411002480340f4130b41640c600d200802c2d6400050741a030021700b441040d00140d06000c02c002c0c2d506400a8820211242c00c1001035000e00300c0510140304040d83d41030005403046c002406064441c90702c42010801d90701d0410012035142c10000307414130900312108200002c590589101001950110b9a10301250342d687c1442c1c2d45024030340c002e11240d404d0441c188035440d0b018104501c0b8a1081e060702466072100740140c80001d44080a4100302c2a080010500c1c40041e5100462030700c90500c1110f001202c3c0b042c004140300700c2c83c0d105802503440416070604500d01144070401c640c405412540c118a04984100d54030310903082101c0140140d00010000c0c450301d541100402d071003160082c00111043c90303000703180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 870307634 1250 870306384 870306391
    0x90909100510030b15010e0409030206010e010801060f03031202070b070e090a021603080901270b06091005040b1305011e080321192a0e03121b15 64
    0xc0c41d1500d800114029045104902526040603418200ea80c0d28041c8000800104540300c1c180f040e40100940507684500450852074440d0f030140902e03500d0680700c412601c174184c004c02100c1c0d041840500030202c80700114821030360180744c061011000324869500070700c0341d05406080d9004400820001039007144405042900079100e82140307559262804049009048003440c20240c030b46e040c0b0380401c4c85241440e030006146800000d0038600144080740d44124001e001500304040350025060000c0040c1040d80100140e408034294501254850f42c0041a0f000309446941e0340e841c590000d0f20f0f0351141602c048079801c0d04011a50715140120301e0b40c000c41407818060303412050045600440441600e44501c0300040210f11810b61600c0c03c00805002040144c07110010044580820240d000e101010f02c3c1c20203406406901490310403102c0040c512518091104481d1008400e450016503849280c4110001c0341d00c510002c0e208060f6484103804403c0b480c8951b280c014024494120f85500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 870308884 1250 870307634 870307663
    0x20c10210e0c10050a030f06080d020c030d0201140106080405190302010b0a080111030408032505130b0307120e03070f11090105011b060c050702280501090305100b01020102090909 79
    0x6003480c0c804021025600120140000b28181700c40d040040c0030f60041c001030280740300301107000b5480703540107850b04841148201c0140d0013450034825904051000b089545601d01c001c0c4034070038a055207990705120601c00e80f000c000709540040d05001c4103014030003046240e04813041d920302050074000d01070000d481d400b40c8101910940058012014450729002d8000000d900d42956180d440d40040390304002c00326080c05400424035420303480144030002203a01c0548605864010003034542c44101c0307030b68100220b0402c0c10002c0c0001a500240c40d2004aa40c42d00041004800403d14030700314000c1c1c0b000281661183c0c1c0000040202c4400d0b146010502910000207031b0380c3c1c81004440e003092543c0b6103c00c0c450142207400108a45420021a10300329060503490940181e0100c0c44030900c01603449810100d002c41030300402020b80c2d141d8024030091a2142c52181152901c6441300340c1940940c60003940c549000100344d001303406a803980d03030008140f02d80d54074188070b92a80701c03000543c00f6030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 870310134 1250 870308884 870308893
    0x7030f02010504090507171f05040e0a020a17010b100816020c060f03090d020106150311040e010e04030e0301020c03090126040b010f1e18140709030302100507020c10210e 75
    0x3c0144030b522031000d5070341c41c1000d0f00401c210710300f0382400010003d400d41c0381054000ccd2940c031400751320780c1035001c0c004101c5071000103040c4a4460100b421162040320350b074850b080c13001d48405d0040c0e11002960300300c544000742d090300b058507410a915082c0000203041d08000301080320083e040303410000c1c510600061040c0c4d40c1c0b500741c907a000c17422580e59000e1030070480c90101a03265070703500c80da10200444030001c0d5158905500c0741c06030790320b6a02c240e1180b46e001c045002007000309030740003011003560740d420340007503040012a1081030386901035000d255042117614020040c0181010100c1e08110901206401e540d080c0303410070340c3d41d16500b400703040b2404009450000740700080e425501e49510f0304c1b014107849142047d90f80400c61003203140003100c15440d01a03880680c103a15030514000e07201a103c41c2403040c03551801a052203000b065452403d03141504000c105500803401240216046804024000c09071405441c0302e80c40082182103482d0554618000590950122540150000480c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 870311384 1250 870310134 870310141
    0x90c0b13081207080706020d06090204080c040506010905040b21010c1701180209040e100e12040b1207020a15051801020a0e06031008160f050a0807030f0201050409050717 75
    0xc0e40e8949065a4480440340104009404619124045c1000920561001d441d10fa40c9403281340c180c3d40180c000301d0105a0000301040120810803003d010700034143c8c9d00784040e1801d01d001030f00d0041030748901d9002d5a111140b000c51541d80302c0c1441d0b820788000312100710703420641d001180200000a5008041080180c0300d002088543c0c0c1c41904843d083c01500c480e500e02100c8402c00380d0880301402d60820303256a001c6400840a1000020400000e1400100801c880b10100e2030040842a1101c0d110710030001404503584071000c50f04a60001d0083d00406c1c0c5035030310124a800307252580078041c4041035540d004052002d400c0342c0d001e0310040c030002c80f2000750b828915080303220300795550700802d04806030f0800307900300b2030041c6600c1050b004003419401d40d01c1d071740b940c18884444080c1001006095040c8800721074850345501400c2d051320291510f41c200f204003035a07000c45000c0078100c100d0200000c8216803040701154040d200301c41c3c0500540c106800003518500f1143c647d10012001078001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 870312634 1250 870311384 870311399
    0x1060f030f05071d07181206091b0303051e0412080d290f120703110a14090c0d06051005031501022d0307080c161203140d090c0b13 58
    0x8410051104901c0c4d10390746581c0400c0c0c42030803815140410341940340000080c0b540d00350046403c0a40a4000812200842e01d0600500c0e40411075801c0f42040c42071061000c45d500c4416070740840b02240710941145080100c020850003940d200401c040440a00d140c2008419005452001d21012082c031000508080c541c52400e802e079034540f10050ad40410040610301009011020040502140c10420320201018100003240e041030f1a08a00069040c06078100030201da0020684c2c1c3e0024140280500006503d8070405040e920a512011940030440e580c16400324004050003010000d01000d400009040703600119200c40040f11424602d01c40d40d40041142c808008665001100c4039042c5a0b101110380c9220001d48058801030000300700040d00c0780300034024001c030280100304010000c10900004a500d070800148403490700300c00c100003508000b00030300151030641c0164441885000000043c458401c0151580c0c1d21110000740981c1440028204102e5048451400325202d001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 870313884 1250 870312634 870312659
    0xd08390604150203060117070e01260711030d0207030801060e0a030209070f020c0301020703031e0c1202071b0b090117040507050d0503120c040e162001060f030f0507 73
    0x38068410582c4050b05410021650300039036000105061030410880311000d014142102159001c0218603404903030b030030710368100e03800c40701c000701c050302c6000c3c200480080d00b07160308000b51240080c01812442e0b03401085050041d40d05c2059516011501c0703004a0400800c007020070f109200100b001c1003450307041030424401d01801d403034000d44803a545840e82441103a002c196604104114001e81c0c512103900c1e50280010420540a07039004250164100509440072404042c04e5200c1494103107a00551fa804c010401a8404080c02c01a101e40442c2040e195072a09400c0452400c003078024089080a0381c5000707414190000e0707942d0b140800038075607800b00441040c1d80240030f07a0310441c001c1146140124441031a544101c0c02d0340c1c20119010010780601c4e0080e2003009110401003400e00c26a47d50000300b0390302000390078400648440b0494041c05401445544004801c00001c40a02d0b0700c50940000005069405005441c5907507403d0003031080000400445482c010300c100029200780f80344 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 870315134 1250 870313884 870313891
    0x3042d11030f151314151602071401050f03090f011b0503043009052e081810021806030702030417011103010303020607020d08090c0d083906 62
    0xb002000c040d10740c2c0b252840c1d41a0000c2005004d6480400581c0c00142d1007015090585007550041040d007844070404028110000c002c41c9045041448000078941d00091000865001910080810040c0001200c80e071083d410b541c1805080082800582080022500511a1075100800c03002c0d901007001000140144d8444000030414008540403581e0b604900701c1950340404450a80382001d9260918102c03010284404501c0040040080781409035109a507070318244000e50960401354000e0056440704640401004070510000d4889503200c01d6052490007007008440c514184043c10001030745c00300411102c070480400b0301010300d050160130f407030083c91260091414503080550485103d458103200b20350541d202c560020f1a0340501c2c000354003031400f07603016110614003440c010745001c2e81410400c0c100035514080100351140400c140495840480e84046144000d050901c902d01688005c44041e10a00040e06909200086138045042006010549450003110301c2074840508a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 870316384 1250 870315134 870315163
    0x9180602180f100507172812090210030e0114091b120d230f1218121303060c11060a0b0d1e0b0c040906090e1203042d1103 54
    0x28000c1d8400260010a44503141d1205d035103c50034840301a9070f03211386410020341f4880420941451001c1194424007101c07610b50078031400d0150f01840d60118a212a14039210303002c040d92280408030070f410a4010780400000160f16442d02e0038945800c9440f4841030821051500c0c01090604650034100b501d1a44074400d00c000e4000c1c0080300800307079228550240d01d05900100e0070740b25503145000c40054084104000e56960700e41c144950101d0701400090501e000d40c0c0702c0e0178400180d82c0000601e502504020b43d01d41a250840e45000c8005900a90001012a07050007401e03402141c8c04a261451901c1c900c044503900c0d2030b02c1540c20101c4075204074141e0484c1640c0401000316030303400464059000c030b014112407440380d1600e81c050101400d0b03419a10980c00001d0400c0718410382d002c1c55000e0300c00300d1010400d00c1030400c0b026a03102c4110030000613440e4040001000c1c00300c0c1071048041e040d00000e40c1030411021a01c82d80e8888810542102c80414a5100c0c00050500244a01c11003003139 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 870317634 1250 870316384 870316387
    0x3070603050c0714030f030c04050f0f0a03080d06050a091a06030714070201120203070c14031617040305030403140106150509041e09140c0102010b0a09180602180f1005 74
    0x740c4a0200c80070013080116114402000100002c000341030045104902c4070304041d0b2a03500300410400381503009047d0501c10100e1040a5242e075450010500c202ca5012030a281d4989040c0498806032030242e01c810781c0243c031a5400070307810f820741e00122003000c0c000031200c0303611282c4020440c0900043d0340140000d650501a4103080c2d10350402002c006005040181784450100a424180d03881140d4290001e0601e00340c0e2010030000030880710718401080c1c0038504042c12082c400204a00c06070001e40002d0028000e20300b40c6018500300c80145800c21309403550345440e0b0078012049005001602421f6190080004030403801040c802c4d400c6030140d8411785000300410800c0042c01200081c0031111004002c942c0c840c040d9031142c0d1085500c1342680c01c842c00302d020202c0d401c00c0520650141964142403c15905903035070b554820a030340c03024000003010102c40740d64a80f4203050403002040903100184501250349820420284902c1c11a10880f842c0002820310041304258101540480c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 870318884 1250 870317634 870317647
    0x61605040b03160e0a031a01060207140f1302070807030e0a0b030403030c02250e0a060e01050d061b050909090c03030d020703020109020310140703020301080a08030604021c060503070603050c 84
    0x2002c500c043c20366a00380b4150788464240b4000035820010f0740c0c412250a031407481c2c1b00003440780070610180103010318005040900c0c6840300700308002c86190441c5104011030000603100d943c42c0450b0b81d052805c880c104540765440c600c1c0041690f84194020340201d03404030900412442c1040114003610280d412507411034945030303000d4000d0818030001405502554480e00181c5031448010141d801d40b003521081458980455610688400f81c01801403900301502800a00041c50384503045036400d980c4610b0119450903c00000c1880444a03001074034900d510b4184103a006000d0903a1501c116440303da6915411001da0343c803588a000785416800a208800c000700680c0c1c09801203c1c02070001023005100c90340040e08140100078140c40182d900c0050010403508500b020754400602d060031480c6504010b5415910358504400400386600000043d9058580d5010384400c810419001040c40c04551050300160000d0700565010303203e560000140300e8401c0c0207460040a82000080c03400c03c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 870320134 1250 870318884 870318901
    0x91f0302010e060712030204170106050f01080702070f080705010e0f0307030b1f0b0309012d050c0f07030e100302070b04080702010c0519060617100510050a0602061605040b03 77
    0x103420b19a603070052060141801050307044900b2608804c0740d80c1c0050303550b82013107800d40d40075114a041354956898003905100980b18511a010b0300c0909003414102d90b610017008a141180d507401c40c059901c1e19590024803101c0002d000425100c00340c840303000c080d000e01c040c002c11420309060f1f0381e81540051410000300d41c0458010390403410442c250000d0700c00d11450008001442e901030080080004100000c0e50800c6c41026a50420640e5144d80b5000d0001d000c0350b900714540ca2a410f2542d10400305129811080031100a100480126500c2d25068203020303141602480040d405900304074140c100e124032a10840e411140d020401c0c50702e82c0c8681d2034117902904090300403814030090121040c00710340d040068102d042e14503400c419004401e85018004d4440301c2c1d108441203130340302c9249040401e02103990440801b04020024071a076950050301003c0302560300250308070200784404619a036022030010311910801c1001c030f0156001c804204e840c1d1007140300342e54207440c051000c2207000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 870321384 1250 870320134 870320147
    0x210a1413031b05060f06030c060706050601090f030f02090a02040501091a09030102040b0403060c0c030e12152a0a1407050a2001110f0d0e0303040305060114091f030201 74
    0x2140a0318090010b00c2585040d0b0141c000c15080940e41a8015800c10500015824259a000d24180d0180c141303001c40c1e0001c0303402e50203803a200401c0700da202d00010380582d126158090042000190103140c0c0d954904005058030b01c00c3c0f01c2603000748800030002e017005903d4001c42e0b0443d04107035214405103203000c000246014108580c2e00032004100101d040c40c0d030342400a0000b80c00782000b1503a40d1031130352501e6011a0000141182803126441c802c1c00445c1e0050020021010709851743d074017801000e4541401e0600c01a420b555412603d4240458119480840f0840600343d421160380700d440c03c1203500060003000c501e0400111469501c05041e08400b0151803480e100d0b20032124050050b81d62100501c0d04070100d0003829691400e040030079030f030040c650f09180b82444040c10141d2005503070241c13a8960500c8150901a41052088142c0c4042003210002d54004060758059616001c3c00344980c050020035511414201c0d02240100040c14031141e0328142c80454412458950f90041d980e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 870322634 1250 870321384 870321421
    0x1c03020408010e06090708150105121914100504050a02011107080123060907091a0c010e030a090b13090b0103110a0309030801210b090f03210a14 64
    0x1055028040020401d00074014408102039500191001d4034101401a02c0c1144540c40708249612110001c03d1291a1402d00e5054400946903517a107001c490450602d429003040c40c5107500d02c20074040c0c0090000303d140c0803d803110110280c0f1150400c41d01d00d4810b40707509480241c419044905020015801540250b8440b020801a14042642c031000542191040c01d41041200700f505003101c5c0c1c984184400380e9000c4000c4884404500340100c0017023452559001d0540903405152981102d8580e07d81650340c00c2c80305500900004400225142c0c40e0b0304036003a460040f90112038040782e0300c0b020038280c50080b58100da50340c6407103180c40d5503003020b850f81d610100e06065440b603191009003001c0000704a0800c80d501d0101d6039451170715005040d0300c4140d000c0c041c4840c4c6042000e45038440d845440e4100c94002000394081d0f101c5001d000d0919000d201d01e0f8a980c4400142c411135555040008904441050300c06081035860521020603982c4002850426004410000c1c030918460310894070b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 870323741 1107 870322634 870322637
    0x207032f010309150f09060c02070605121f0305010c080109181b0902220b09060a1b060e1e010e06010501120e06040b1501111c 56
    0x40340000118090425480e86400410b100c851620001642c04a036402c00901c086607821000504202d1000c44103581440c106260f420b0001c500c030340898034a0384a051034a9070380a00f403242c1110003070010032210818983c0c01c1081040e81000b00246114000000b003210740d44d84058840b0a05030300c000910741c10000d241d885900454007000c0d4140c3c2c4000c4010603050000260072000a407a009104400c0c030108010801c0c2550b0800749078901d82d0350004055640d02d500c119a5580b00790880700d50058030401c01c0013216442081e900200e20150f02c00502c040707100750361f40c0041d0382c4101d4031601c265000003207400c04040d0000c082581c1e660104000c1280c0008054600d45030f0f401481042e042c40104d1309052640e010075000801481c91200541d03516140501e4040b0710303514103a81d240c41c7c1003010300100d60741e540902410000c1700c0d00030004061059240340011481e2816281150 = true := by decide +kernel

theorem cover : BRFrame.Cov 870143884 870323741 := by
  have h0 := BRFrame.cov_init 870143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 870143884 ≤ n) (h2 : n < 870323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
