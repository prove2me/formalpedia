-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:28:24.427122+00:00
-- url     : https://prove2.me/submissions/57999f69-771c-4687-83e1-dae76dd851d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789928057 ≤ n < 790107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789929307 1250 789928057 789928091
    0xc0e240403050619050601080108071a09100c060506030a0305071203090b09031809011518080a080d0c050309120c0c36160c0501060302090106120608070b0a050d0e01 73
    0x310a5801e04d062049580d200700446000e542440f40800c0355200c2402000119402415000241d1011815601c0c044440d0040380295984200ea000000c80d082100710600c4400c4c45201c1d0070000c00c8024100e1540152401020b60103298805441c01d03905044007402c0b540643d000510507648094041464907022024644a41101c500b88403210f000c80c6a417412840c207040d046c1d050b1a1510740801c04202c0d8400101d402682d0b007003100d0080002074a0206595108000c1d100d078181c07241c4030301595036040c101903034240c3c1d013202d600800b401824002e0200c400808148100c084203202041d544800f8600d1910f45030880301032040d508102400c1c040941840003c42d498038a0881145280110950120341021f6840c00c44221303030004c0c06140824201c511503119802c1e454000c1c4008031301d00f40c030fa40001c1c021034000c0e440500480c05600e02d41d04a0350040c024440113126420240c40000e04d03242140d0315521035100c40b0020003400003040e4030400680e074401011381c030414008112652002d100005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789930557 1250 789929307 789929341
    0x30f1b070e010f0812032214031309090201051909030b0a0209100c03080711070308030a021903020f030c1c0e0c040b03030405031903020f1f0c0e2404030506 69
    0x159040840f0008605840d0000d409002c000220340d4051075079960150850920071a8100e116a11048031142004a0212160000c1680c2e001c4003a40d0ba401c642056601140a50b504c41c000c064206806400940e0b004410344a080580d01490413110f00c0482044600c200960801003d5003250810302c07054000035806804580e2081d10b0300455040551003d868600c1c1404c80140002c004000082403144035401c03103240c44d8461022680c4d030315107a039141040c41e0001c0754550b440590204000c07041c0340035451800e11607046070404514000380d2218841e101d200003005500030840c0000c90700c01c3c40c0c0f01004000d81e140202d04041007010b8510714815118030081113018031036030400c80c520105140c04070868084a4004005201009440c200321100360b9160034250700390300a4040d80b0152800c00d004406820401d80189044c40da41200500c2c01c1790a562040c90402c4086414500d1070f0b1240c80d040c0c1c11054034484a041070304c0c00c2ea601d28209204580005225000340814000449403101e0b07010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789931807 1250 789930557 789930569
    0x8090f0a030f1407150b060d020705031222060b060f0703021b1e100507020a09090201300b0a180203060f030a0b13050102040e0c03040c090e030f1b070e01 68
    0x2da10000420192030755000304400176005e07580101544490340b10641c414210711501410791420b00d100540268103d030010001034401c3c0d000051280403480c40b04203426401485201d0140444401d01420003a039524110014242035072152601c00715a01c0105079005180702c8201c0d01c1d030b103004925009480b2240c8c03000003e810300c01c15800c0f0540d89801c0da182d01c0c5080380c204e0032004148001c0c0800c074101e4000c041700008c0c003208010365000350320f85490050107800c00801c085034501d06031000405100300c805004845076041d07040c5031550703040c0402c2500540240300e004900f0201d800006030901019070b10980003202002e240a4200d0b401740c010b10b01c1680100c03040301c8154441d000341038a41201c240000c1c2009484000035401086081d071180c0c1d90f40c0620001402d103600e64001180400042d905c00715162008020002013100c070b08440c1024102c0315005016040309454071030342e41e010340442424050300104001400c02e0082c0494450b4409400450f418995030300074101282c1428003441c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789933057 1250 789931807 789931817
    0x313060e06011a03060402130312090909120e0a2c06040b010203091306030203010c0c02030d030b030712020d080a111c05040303110f060103150c110601050108090f0a030f 75
    0x8028a00408a5494100d4010161590740716498101103925980001c117032a0f030295080c4006941c4581410080c0080c61040d2031016481c81d2904018010310520b5002002150801003000c1c001407415108184003202401e01010270150304000500702c20f819000005282c40000300030f4400c641c40c240c18490300d41c642c0d9402445072610018030045d01d80ca011400d0169008204400140c2071880c4403000c80c110340e685c0021800d449900280c00c0d204805090f100180d9007a021009500c1c0034404000851107a0400300012000c0344040390304c071080d80c0b00711030051032601c42e0b030015500e4a603604421281c0c0803e009595203010031010705030b00c1030301207003005a02c201c0031074290402203c90150a0700b0115107908d1b0415286540441d1440c103005440030040c003401c1c014011070b038800c12503140130b54802c958140341c0d040f822051008951088810704100000c0841d47c411022020603503505441007071900032000e030703200b080c8181b0300001d421002c1240c2c07080c1c0705088145603005000f0400d10041e0b0740c0f2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789934307 1250 789933057 789933071
    0x100218061c2a0c0210180807030b040c050d0b0f270114011205101d010c02010b01080a110301140d0506010308070303050c0414210a082a0d0302071106031306 69
    0x40342c555150300030094114130945024400e0501030110340403003000401d0742d05412502c503500e25041100309e60086609622140a000800c04032241c0b560103040c068590040106031501c2c0c1c0c46100d200076290300d960300c00500200f12541104201c014092544040070130908040500941c028104c1d054603c5c145100c1c80004500844030381c0008003601d03000002055210400758a003401020b4909080c1c3c0701041811000400441c01e00400d481c020064000240d41501c0c0070002d0481700000304010780c640c0c5024440e14040405105a034152108414440030401c80341c00800c5031811071040150451183c140000304004894000b400103a200e03076400e00036501c5045644841d40100d02400f0300c8c1000000626142d4280010030380310b0122241c650305c04200034400d040e030400391601e1040d034451900150b41188151b0203d541c0c0c007464045484143d4500c6503104142d1102d6403103041004040e00082c6900501c1658100c0300311018006041540c0da08028400700100041041c080b1134490400b40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789935557 1250 789934307 789934391
    0x30c230f0106060f050421020406030308060102010606051c150509040803010305010e15040b0601021204090c030b09391204060c170a090c09090c0602100218061c 71
    0x3030b80d004003a02c0c0d40305d050809040c81510140411302c414025510284064180301598550103050004c501031380724481e01341050b000090070742c0c44031340140c800e10101b084640049030303010a111f107541c840d001000601400a00c24404200c030b195118540c00341180043c001405024001941241e115400030440d600212155548031301d0aa8604c03c910414003000030049501070740300700c0d03104e0f0301441079580008409103503010341e800580014102c1942c2d62101490307542c061186103602e00c01141c50b00c42a1426090400c0307180a0401d03603035684c5844404150740b0725841d42c0416083c03103801400d40c0e102d0725501d501d4041600104d40544145040c06c150006050092036000000030030920003000e01e0b5581c034417801c0500074144046420511002c80000c240c4600c0c4107003401c4c03034850402002c2161074004024a07110110000d113800510402c01c40f000425500130800094805030388458030b4080390304601c40180f5039501d01035003890030a0161503110b881140c50383c0c03003064180725101c0c11049400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789936807 1250 789935557 789935567
    0x210c10080c090d03050d091b0e042607051902010e040507020627190302070609080d0f140a0e041518020904110f0d050601050a020a030c230f010606 65
    0x680c07420010360040000d02214104070745500c400b203011703040c21441c0c02c00000a03482202d803420010b4410704080e460a9032440100b2412100130407890a40390402c0c02d180e16014807403c5040101d1020700d0b205910f42c41e10360842c07400d440020b9000030a44501c080c8001c000c103814a0b020360101e00203070b008011003015207410311409000e4940c40d40185101e5a5114661944019140408442e055081c4120f20b041e0802c00100344042c0004010000741d002c41e00c0c010307140828540005052028114061100601c0000d14403000c2025290465180311807103025101701741c0c00d18a884100400003018000c0303d4100f0001d141034a400e5404202013441001c121070020118050b110f17500002c61704070300c030101442d0003810300301c04010000100a10348508ca0003090707010101416009001161003440200740d8418654444001e00300030346001240751000b5102d48080c0001014810031581000078800c180d40040c00c0b0481c2115580d10348030101d004c1e1a80c0c5d0008981e039510a608200c0040b4065200d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789938057 1250 789936807 789936811
    0x18010f020a080417040f030311240f0c040b0309011e0c0926010c080a1404020d030f090e182104050d060e10050939210c1008 55
    0x5540c2d610003c3d160780c0d6078040894210900c1003082d010510010030702010511040000314801e445401c003810341002c4140c1065050442e41010395910801e65044005243c48168401e9841090080c55170310081443c0e4075000f00e400100003850301104120700d070b040560040112019404514005444852405054036440000c031000154190420000c0080002c07802c107100070305002e070070340145072104901c0c02c44441101032070020f4038450908c03081c5005c9201d0f900c6520745000722405c4c40d2600d038000c2110b04072212801802c10012030300d1588090311542d5500068005140c0c903001350f00b4401244d41c1c02c0d00f035401404105004040e542d01d843c1901c01110280000700c0611030341054544410000c00074540c5105461040d1940f0b00117103284018404100a403403204000070742801c0c0050703094a020108000081007000ca5184e04000704600d15030804c000083c5030021941c1c14101003c11600600e10301c0c92140d003450603040904400c40441e6001c1441000e80d255140f055001c80708849032441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789939307 1250 789938057 789938077
    0x708270f240703050c030316120209060a0c031701170127111c0b040614192304140f060c0906180d0f030e01030e0c0415050918010f02 59
    0x52040c07156040c54880003405540d4080c1c01c002c2d00302401713a80950f0565000302c600700484a4801c403030031041d80d00410480030312050740c0e10450030104000040340491050100c41400d102c00c0c141d8202c01c1600c1707031f980c030080c000c0038445400955945410840c4404d000d20484141c40d4284601c0c1c3d0b11341c0180210000c011506100b01c1d0700d0080d81e40d29881d04140002ea03026401c4030f03003842001000541e010150716007501c125407401861a281c02c069007118003c1c40d02c0c001c250014030030b10050300c1c2010540342e0b201101076000202e0b099514500039030604540d68200607064141e04000c1441242c5804410840f03140e41503ca82d44840208182c43d004100d500032054581444091000d04240d00035003103400341302c2101040854600700140c04014a49400c03280c01d00d81d200e2102c205540402a4100142c080c00c0c20700c09a24a036070f01544403821002c805009a031b880e64420003803402c481840d4000c0c140580b800005007408040c1d80030164030b50030b08820940c00d0140030310400380180f08643da2140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789940557 1250 789939307 789939349
    0x1022a0c0a1a0f0a08041209081e030910080906060109030305030f040c09090501020d2d0b030a081606050106050f2d0a0507020306130506010302060708270f 69
    0x2061803220400c9003041c411044801500348400c2e040d4032258001412803a509840e460704c64138091404040704250011011f08203c410f01c1f04001000d0001511001d240070030420201200d0152803072495401079404446d4007001182d0600c1c4090341000156004450001c00d8948036038441c4019a0b90828600c0000d002510403c00515580003425140d50841d10448407042190399807030000054951a01003994141d500081a01e000c001c148540d1030000d0403000201061031800c40540260300b41c2064454100d503e07404002500d950a0100304d55240d4030a003156128070210060b1803440704007107800c4414602d04000401c0c1d1902890554030303009200036000d40f5108092034101c051031092070004c251080380c011a4580c0d031546001500031780200303565658584019004043c58030b0406000e6502c10f01038041290b02045011560506580e01078895030b645882500d0b01d61602d126400b014080803c0341d0307140c0e4034074502011034141001021031301051480403010820000e00782d04581220340d80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789941807 1250 789940557 789940559
    0xc17100f06080c07050a030504051002060c04050f04020712180b090603060135090c09041203050613021201090c030b090601030506060409110a020f0304140904110301022a0c0a 77
    0x28440c02e1199846102101910f04020b90703981c0311450661140802c9010a90104044c016820311080d0070308070400e0340c0b00404050820340d00f01c3c4020b200d14080c540c0140c880868001c41c40d200c640455065541c00101c040840380800c400900e607440c510003440036142020800140c504441c030035221008002040d46107161625001900c1d904140380c21801d90f0b01c802900400004404810784200c110341002648042c030303100100c5810041c5c001c2d50301d44550b280900741301c0441d40c482034400380d5148508000960743c40381d50028541d20000e1b61028105800082c8000c0c204905c441c40504840302044248500d070400780d410f8080da0200184103400180650000340f280d03102e0741040b83c20030310181c601031820f5210010f103000e851841b648a00600000501819003940c1080401c90002641c030185041c142000c4460180840203c80684103051060104041c4000781d2150308842000500031940c4603629114158000b002a02842c5c42c405220301c5000e80d40008950319108040c02000d0082031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789943057 1250 789941807 789941819
    0xe01180e04170304050a021f08010b070501110301060207030606090506090613110a08011a07020d12090f03050d090501050913110903010e160504090c0e070c060c17100f 74
    0x100001081681c5060301182c440342d0358030600d4010760180c0d008402801d0b8111980c0107000c4501c403034100a042d25051103880101c510b5000101d1810755882040c4e0590751041030402c54003605004280e1609a0400000081d21980006100c0101c1e072140400f44042591030904200311141145c50340c0e041914403000600d146088140c820000103074001c00609185118032a0031207401c000d408002148100d0010b104001c0000840c0107400e200c00d9500d407508540c4e6000c900f021a282800520052102d2602442c4c0c0d0b004541c00005012542a600c0041c0da40e41080c0366240300c600d0140c070100304010303400304540d44101c00700c1e03000000c040c2142c10304181c420325080040c0400d0180107180d0f002405582c0c13155a007800740050f4500b001c401003c0704281c007040d15101f8841d40d401a0310551400200c0c1c1c00094442c1c50070000c40304036882c81503060360f40760f0050b26003405108005003140e01d007940384000b50743c00c0701c0580740030900844035039107594841d420f42000c0020350042000002000c0420454 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789944307 1250 789943057 789943079
    0x80a0219260c1c27050c0306090c06030a0b031609150503070b0c120705030307020709090f062309070f0801020c0606042406020106091b1e020a08030c09010e0118 71
    0x51402c40100000d20030308003c2d042c041400e42d5503200d00301380038110f0002d040c0300341044a1400140c04074060001820480d24117580c2da400c1c1c0078400d0040ba80480019182d07409944031681000300136007612421608450950600030050265054962401d500b00c0f0010f4070308800700c01130325405001003075000e08141c204c03a0290007502400b28240315a6204001c3e030741a0354050040244980011510bc0c204814043d00f0410b850b04003c020520300060400801d86c0d002460303c078035801140000d5090741d8207000d00c0098100e81c120b084196441814880c592000188140071500d06480c0781103401c0d00c03801c2081c240d2054454401c81c0d503101342c1c04038880c0d24250380111140122102c1241e892201c24013061498526540a68090b0b5541c0c80c0c108510540303400b80761a001001c4407010440126030300094103103d051200500d44101100020303030140d008121201c145500048410f450307180000d0402103030b0303000b6199540081c2e002840454554040c2e5840c1201d600702c1800e41a85500780456034003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789945557 1250 789944307 789944347
    0x11d0108012706080102120c0a0c0f0c12050d0e030a0f080c0c0a0b0a08070c21031104080604110a0b160501021306021b0a0f06080a0219260c 62
    0x50845a0381210404480161041c3da00400f01100056120040c03582c9000d86404010110800481c0410110208a500044640d2005d50090b501c070301718035007030030161000c01040d0040d0540040c685040c100307021000030340404071130841e954207540c4065181856101c484444009140411403282403000415407009040941028821034407074409441c0000e4050103c0c1d4815015140005040703003000b0f44c0042c0c01903100c8a1828100602d004a9a9416409a842c240c04440c0103003400d202800328426041006034240c038505c11900c903a143c147c429200c1f00143d500700c541b0300418141c045a130500c40748802c00c0310b041d401010b042a04041d107964001642c4042152555801c00601c03050f190705003401ccd0041c00c01540284061032080c0342d80348030070b4050707207406108207966841000140e50401d030320f500340d50007413600c0e004a445d03a241e100080c0c0125170298401c0c00a01c40c0140c1030365404003d1508900400e118200e0191850ba000e2202c04000e5443c252491410800741e2550042c10303030101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789946807 1250 789945557 789945599
    0x160201031a09040c0305070b090a0b070606090515031e0d1107180501060f02010908041e05090412021b1507031e090f060e2b060903050702011d010801 66
    0x958452200c002030341110045600711039013110100c0500c144941082070030054042c0c042c00c2841d0545250000e01d0b0b401080c81010000000017459000b0050280c000700000d141c891010700c420b04000071589550110069018040e1207240066600c50702c0c5401410608040381002e04102000d208040b0f44001c0b0344440c900083c8181ca8002610ba25807a40c1e08440c20b01c41c6600007515410000011b0400c0301c81a0300300d04580c1054a0403000c00c0c2c0380d03030840701110c840c902104030880c00d110880680300c00f98be0107654414411010001482103042b95401d0380c1201d0b41c00c0c0c8684108800344440100100000c181c1c1111124608140c1505220020302050307010741000d40e02071142c0e0640c08124040540c1c0c410000380c240c482004400ca007145039002424031800c1c0042c001c1450008240208081403008070806420003003403103030610304800f05100a0b000031051000d19903506000c0c0207079002400c100e0000e11290051200c0e80c0d181c10100895000507550003020b41d01e4950315040b4401040548 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789948057 1250 789946807 789946841
    0xc0b1501020307080c071517070509030a06020c01090303060509010f03021003272114030a0608030a02061504050106020d031e09150c03020a02060a1a09071d0616020103 74
    0x14030100302c80d4006890301d6001d04009100360f40c2030181411b4050481c0908006100d040707004051400043c012207030f8002740324503190b0345428482d40001d14204852401070300311480010218480d81d41900104c0d00c0178020744040c840d9694400a01080d45800d10075103014800d040701c02e00040c0b030300d541d950044459034034000c01d40f0b1900070105248418070040c480d501852040b00c4e04100021222480360f12151a03048141c280280d140192514400074100702d92501c2c0000001c60400e2143d2007072001c0d01c6200700300d940310301d00303083c000e03555001c10b541d2818903940c1203c000c4103615041c000e05068030b41590140c0310803082d04e80140c01800380d01c94000301819800f01480e0a45882c1d2041e01042805140076114503a00a01c0c1441240c010f20500320815004100e000006a000180e194004e00d1156002410300c6120004401c0307102c42080f4164818030003000d202c4000c0e44000314060340300490029004020381707002004502e211741c0c0851808940e0506501002d91301070390240c1ca180001c0302c06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789949307 1250 789948057 789948067
    0x1501020d141b0309030c041a0411070c0f08010510030f02010c1a07120f09030806011b080a091e230301090803011d070807051c1404060e0d0c0b15010203 67
    0x1050b480c240c21440c061240c3d0310128402d103180c40d00304500e2443c00010303031f010010a8801401540804c40d02c214003030186413aa2074040710441c80c0320803289516001071303006450645038000f00d081c8840e18030440090b5030a01c0041000080d14041032012aa8054106040351220ba8010b4072944d8410070144e416041080c0c0d0000260744205140741300320095640c00c103da4250f41c04034030403a90351035400e0010070728182d03401c40000e0701b1003400b81c3c00c89824280f00d50f80c0d03850341102e401c444481e600d0040059401041000220b5000340d0840140c0da600d0071240c40040c8800c60803000b11986220f640107460181c001ea0480c140c103031400445d48003010300082152903503a203070988158004c1c0e2080d0b501c03001130010712071012200028070b42c100080745008121800e210000414900540c65203501c52054041d090112075203a41c0031030006e6005030300150309440c050070a0002031003110003100590044841200040d032003002c10f1400c80d680507005440e42d845928820584800340b05e192415031000b006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789950557 1250 789949307 789949327
    0x3090109091d0d090801060909080301060e2b0201080a0212070807020705090103050c01180b180a0e070c0309060314011403010e061302030111040b120a110c0102070b1501020d14 78
    0xf110300744880303aa07100c040d140b51914480508580305540b100000034a00508600020300440480f41112001c0c40c1041004070044002a0401400e210344c0303113216001601d0b280204558200110054000d803180700e099035484080909a100340c01900c000600790800144d48240035443e650f8203c042441160310494a03003010403e512820b800544150707000b03142c2c1c05859a48101400a003450f1444d61a60307452038500064464001c910b800d0108030076504c1c41c4100742d214428440020903e06640e140700f030415680103040e140398607105900240c400c8401041c0c46009000f0003c281c080d000e102d4616a181541c0f049c042e00c0320030082981552a2a0011034050081290302c0c05003902c125540220342c114030400d400c40312202005c0341c8100040c0300401099219006a401d5054919042d910950f01d031034100b80288000182c9606d1084080703002c49403060150301908005100e40606086525003488102101e0b06014103280164044070700c000d0400d100d0445014104030101519040181b00c01c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789951807 1250 789950557 789950563
    0x5092d0312160f09032d1103100c090b0903120f0d150513090c08010513050c03013803070b0918010506090f03190606061103090109091d 60
    0x60410100301041c0c014001c820080303084145205400303040280d400340e1508009002001144030280a40700d5409841980c40303034a0080720646801e58660000d81c000600e04009101e001d151110b01030f204100c0c004482c400c02d8810340d605c485264407019141c42c41d0010117405548010038030f40c0c15018991848480c1130800c4043d042880c60f0800b155240e0302890b180000b100e02405d4401c2c0401d5495000b0000c40d11400480c000132105220042005600da052244568035950301c00c928035841c0c4020403000e02c04c2000c00300c2c0e40520038010707a03188100800416081c0d4580d0043d001004014944000c40d5050050402103a070a40700340d2224040d8804000034280140e0707920002040710009010400b620b8175502404aa060351514030119504060200d04180500313140540070708000f03030750b0910564007000080c6604c00d118540c40040440303468103030050301540c400c0902203030303010700074442da00e40c04419a004000c060707655113034182c80d1042d010040d011089800f210b95401c10246da006101c00c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789953057 1250 789951807 789951817
    0x7180e24061603050c1e0f150c03040602071505070306230d050a1a06151303031d0d06090b06010807050f03130b090a03110a1104020a050f030f01050f0405092d03 71
    0x32040304191400300d14000e6040202001c00c0d420345420a20408054230303608901c0d580c222915201d195101d0703490380740880080c4a13100e0043d0a1003910800400c4482c003c2d00104e01c25200303517030700703000300c641e20f00390f544500503040c83d501c1030480000d034681480e04002e5a0400b615004000b29900f000391922034a01034a43c540503c000112848204070301f508003640700a1500300501945450b1407083d584402c024103141c000202086031042032070414081207120051400741c0144282809189031400e00001d055035402190385e0726094000408940c00350120b06e05c030f03103495150306281110f08640285150300c000c08404c440f80c40c0074035404c0482c81d0f18075518414460b03540141b0200341c1c913040290401d030344c451810380d030b40d4010103d01002890683d400c800303421082d0340c0940c0355014070105a41a0041c1c0d50f01c01401d54010041060011030700c1c81540c12944260b03802030b4050411020b110aa400440e02a6055408820107225034151200300c1c03507007a400c1c13448111a1400d40c8807a14210340c89 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789954307 1250 789953057 789953083
    0x30c020616020913030e010e0307080712150b010903351206040e030a030e0c09041a0c160b1b220b03060d030807180e24061603050c 58
    0x2406541c00c0440c100795001c0c0c1d821611a000c0901c0c68406507400030111005403404504001003c10040c405480c100701c0c407006004842c09075554a600c90444074009807481d0750a44200c1320b80c51001201524911a1400d00041a950a13000d00d04503260898000301e0b4000300098a0006411800001e058110141401e82100003061359251510f185801016015240d988501d10f0000e01e48010b07000082116110000c0703003004520707100e061491500341844030701c0030750700000f03a48200300403c2941c40074605240d0500c0c2031140e40340c0300d0180e0720311140180c0000105180d103040c06031000c26810680907034444c0c86c1414541c2c3c0d00300c82c0c6a030620300c0c0d004045101650001e146220f5400f842006141d400781481c0c4031250308500e07043e4000748426220900c040c082c001c050703020a40c3d49119010703810f41400940c003006030b82c3d91360362000c500d0080121120012481c041000710f89006049000a404c010014995400e20300f0b803842c80310010800440440500004101d0720704844000e109084074022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789955557 1250 789954307 789954337
    0x90308040b100f18020403020a080c1f08070c02040e070f050a06030203130f03200d0905030f0c040f0f0f0903030e0609070e10030503070507090e0307050a060207030c0206 75
    0x4003031620075000781002d880c0d0001031002d5101481802001003081e4100c0300d20b55444440004040020402842030750030180d0844031350030020902c000001422488030b1416140c1030f40541440103001c3e040d55280e9100000520948040351005224220701c0503020b0009200041e1042d01d14800c030310f80500c640c00346801c10003100c400c00040c5000b145100c02020b590606500c1c62504d901c2003181203020900041120003546080301c141032050310b03804a02c440c00c01181f8005010581c2c804d0755042c480200c4400608600c401003158140810443e2604003000c000b0958400c107902004090640b003951400410381d0303070913554288501e50041402300b4071501c4000a14800c9030070f005081d903142513401078030f591206081c007035510000509482101e040c10a101155108c280400013085045e0384007901318840881c0d408107001000c0341c0a81200ca401c50108640e00e1b040f250b581e100c1c055010050210340051042d8400705078907400906019100c0d14001e10554000d9000480756000f440340b06d54120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789956807 1250 789955557 789955561
    0xa060303020c0d030509060f040e0106030504210c031d1306030605150a030f020409081b071707032004060314011103060a270513020306010b0a0f050a050d090308 71
    0x140d01800031140c052010384201c066000c003070700c015205d84149a071840c082c1d1000a655400c0400b0702040d01c01405032000c02c50705c15652010000c011b450140e03400d543d0007000ca40d16900e039504c0741078495201c1c1c041d500c0d013610707542c2240c400b0b80d40d050451070b4404c5d40c103805840001d150f07580d0320000f001480441030000b03500ca0541c280f05003241c0000700400814007100d000c44030566200082da1044a9210710220341001440c400708001d00680c1c2002407101c04040398605485140030701980300321590701e085555050307861460140078594002401c1a6400183c010b1010444080d200202400e54655485900400e54082401c890065101780c1da0018010003e803245402805941e41e40440403140328214100100085c0c84c004951054040d41044a01c80c03070521015401c008a8400c0102e90401543c50b0100b540042d5a0180c5000ca03c240500030003c9402c1c14031100f40d0307030640305035594004003140d90741c010303901c0750303c02000c1806000f001d009400c560010b40c0038600d400c074400c0d80ca0030154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789958057 1250 789956807 789956813
    0xa170a050d052805160503070c2301020a0809040914030408150108071d0405012004181506141b1c02011806050604060503060906011d07270e0a0603 65
    0x7400641c60100510200e000c0500f1229400b00070340d42c020400c01c0705a04901c0d02c0b46003491441c4185d450007050100314000020b044c80340c0c54901700d0860241c076500040d0a0ba40401244c652052840050907458180803400035401c3c2070f4400c66040748203601c0e00e9444450304034038526641240e442120300f580f1040102c03140d100c601001c603004158100080040c036007080d1000b40c0f075070240c0000390030a0304c200c0000384c02c0c46400d41141d120711400a800d02d881010350800d0441a07441405034520440600541c60401c1ca80f42c4992026800300c26140003804d4285402151040e02c2640e0b601c22100e824000904144c443c40310035501054000000c1045024a404600302035001070040d000756454038500000e40000044e80e004159404000050301e5902c40001400400c0c0d141c02240e09031040c1d50030480039036000158281a11010031121045640f10440701d4001c4508036200340000c1c5500050841c590b1802070200f8102c4100003c1e4500720340c0351b08000000701000ca8284900303585902c010014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789959307 1250 789958057 789958087
    0x9080712020c1804170f070c08071a040b18030f06090106120803070e031212060901090b2d04020a020105061305100b0d11030c0a030608010603020a170a050d05 70
    0x2042c0065030303409000150100701c04007100c07000b00040c10060140d030010f80c401c515001240d4585560039182501d4020b0741c105900307014200c1c05a05079504c80c0174404284668090422a8121045041c0c1485c15040018145068105800b40c01c040c0080c03020780181607a043c005402d400e92404c0c01040249001b0761000c4c2980c120341d1000185110f8110300001041081c2c040729400003140c1840e00c0c080c94046c010a2a0012401d0742443c3c0b030380c022031444a1000c94000e001e001c0d2004960051a42e42c940740c94004807040d44801c03550020780e00c0c3c928150408000e40740440c06c907020800380510503640c0d002c142a41d0100e443d00f80113035510420801e0600e0b10201151200506000c00c00c590320380b80780e004207290014010f01e141c5a00100e000c0c0b80e0308416400812500d4854a08503890303080c46c811445440d00480c246c503010070300780200426844814400c070011250000d000507522444c2c2501e20030807510060211006002d0107a800340407038070821200303024900c25a40d280c0d645081c0d07640e0540c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789960557 1250 789959307 789959323
    0x1003200a180c081b03060102070f090e01050901050c040314070e0a0617161412030d06240804020409060e120405030d1b02090606070b0903031e04150f0908071202 71
    0x81c00111000c4c0311110001d1400703604001020300e0040d40d29260b00d00141c0c5404042e9100c00c5031600014008681ca42d02d075000100c407003c05e0002800180c80340700900e030907504111244101003400348020000b0844960061140319080030568242c95207465402e0580d1000300d49501056886400800100c110661040c0d40b41100c80c02401001d010156141c1c01007503180719240b4003103180c2c984002c05030340d84043c85044204440880f55100c181ca0503850280c03a50b8800d2410350040041480802c0c2c0b0401c986004211566588c00129a5079030b00b0030004000d404401d030b42196403448130905980c0b0802a4003504110700d50075035101c500c0c1030101072038545805065010001e00708d04008032105880e000c1c41900d58100c401014039541d52000ca051070240800c003401c0b100d40582070015041000c401140154220751416000c40c881c501c40c0321003100103850003042100e029400d1118a141980091140012118085003070352840d00e074144950049542610600ea4200344a2842501004905 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789961807 1250 789960557 789960581
    0xc041403010c120e0705060c280302031c090219050f061c020f250b010605120a0b040609020c030414090402030303070507060b040c11060108061003200a18 68
    0x1228410440300300424a03034181c070520043d2034560700d216410740030074071600300903040140c035268444504e5500240e4840c0f4a2062483d1700101920848289030031150415400b40c05400840c07034202e0401c1003010020181c07400c01401e55407802e20703100582c0c509150404100700c081d5400007450404041151030f08400f05650301c1000100311503034082d24202090340340781c21071031401a201c1d6528844141d0781d03c1402c040b8498940c1c4260840d114081d4852044842c40c010000c40300280e0303d41c04261440e01c1406d5113000c0702100e060000d001c0a0440d0845200c1c1000504042003056441c11a00103070b0708550306400d4242c2000c1424440c10b002d252035000750100c100d5000b20349041680100362a8171014000c10100200044c245051090f190060516090701400400c510f80c081440140410425140f100550080c1000011448000981c0c03c0c01074420020824400340b440da98501680c5c40c0c0401440e14a9103480c05002e51b968040c4403100610020044010303194104424000f110604a000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789963057 1250 789961807 789961811
    0x10060c03112118040c020d0806031e0601081015051908030307050c0c1e011413030f151514030106031b15110d0e0d17130503010b0d020402210c04140301 67
    0x2176032010340c0000c44410607921402d00d14100d4641c40d012a041030405c041c400102d100955410f4050500040d805041320360140235500341ca00403125480a0350000e10110482c0c1c4403003130701403115103000c0d88503810907284900c100c0700c1d040e56505120700715003045560601040011a02815280091005240740c0c07504a4152074100202c0b8082985a00580c10190411401100c82010010074030304580703000c90619465620740307a2341e03e07240b440708110101c1158044d806603400e010750841402000007852000e061250f80c581030a0000400b0071a1408040d850340d01ca000000114000180b0700b0702d036042c12201c440100d424034107540040e54580b4698010402604540c524a940101c0d0980203140c603442c05102d140e41c81c40c0052092207091001074a07205002d00c1c0c02c0303514501e51000301703040c0101c9000aa54281d03101c1c00c1600300c8442d07020481e00000703010b00c40c50061400e41d00410f0361114404210b00000303004040205411012200040410800541440a00b24510690341000000c40c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789964307 1250 789963057 789963071
    0xb01050c061519030f06060b1201030212030706093215040c1517010b12010e071707020c130204050607110301020d150e10060c0311211804 61
    0x1480d40d54030300141004616002c0716100700b025900c40001c42840e01140c00d0b400d000030b490b401c00610450102800f00c5116240480c0011003400301c200766130040441049004583c8e1840c0c00307004002c411804840000d0100300200c02c0010500d01c102c4036218095006038084440da03003421611005090341c0030344400707a90f401980f40c5090010351040c001d5a855804006922a840d0450180c2c0320b541040524500c1c40080d60342640d803000141d08105411050503d007030740e840ca584580c0e88101100d02e140c0014550040c803201c0c1900d0000d580150701d07443c0c29103000010364540600f04000351a0400181c02c400da01d412907203001041080e0070f000100045142500d0140042d007207200d0224024a210b00400b034021460ba005c0d070660780c40a016040a00c03c000d0b086840040b84041c5026042c00810038401068005140207198002d544507500e5024402c40e15440542c0c0c1c0e81e4014092141e9031080c14841c0b05e41c2d092450800305024050600562110180120180041402005c403400703076252840d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789965557 1250 789964307 789964327
    0x1320c070e061e1f03050601030606050c1009080f07080c010b0402270a1e090f06060804140a020a060c0b0601080c030127020307050c0601061b0213020910120b0105 72
    0x102c10324030f00149070100c04400b0600c3c400f10340c51200c508980f5843c100141d14020180707400d0340240307200e40800da808010482d20385400380e0b1503014091741c485042c1e100341140b0711400d0096201c8400c003805100340c58108200041b011405c1c1d0f0184108988802c2c0c00310b000001b401090181040d9450100d405505000c074450000da883c282d0700703680040001c119800c10110381c417034000c018060300c1d030200c07034041e030450740d0b07401c945a83c41030300c500b1005900d421201c0700d94110714070400048e100190307501c9100d9115522102c00100c0d2810700b419660103120594401a510801c908000b40b10070f4440ca243c0c4104c5040c0240841001805981032002c000f08201104000340304590554040000100c4100f0340d0084c07001d074000000320b01c0b2818902c000103204c03900da085005094540c41d00022515203030388690040b40c1003a910040c0101030740b4082511401441d00c1c0d0500c8800e000d000700011305041c031140019110074070f400d8600020504414170b0b00d00c1650740d0302400f4039605080c203280c2c0ca8010000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789966807 1250 789965557 789965569
    0x60305030d021b0a0501050924010e0c1207020606150a0e04020a05130b1218030301060c03110105070c0204050a1a0d14060106030501080613080901320c070e06 70
    0x1005040d0982c2c2d00188503120b540a4900c000341c0b0b41400012a181d14440d494050300815041d2900d4249200e820a0321008100320402601c40043c001c000c503400744d103040c85e5201e6445019096030811801404581103c00740c10024512801703a560003404142016014400340c001030300340c0c003a06280308000d2100091b0f000928801c0401d402e44006a40d1810004212510f0145060341d9402c52403c10300020712050020144c041c02208000c0c24025840e086100b201c80c407103c01000c80c054005100400a0030b0160516803070784c5000e41003010480342000001d50840f6411100c2c903000c100707400131680541c18540f0810ba4041380d962410401442c45126a58a092506442c1485809841040380c00c001410130010310f4480c150089407401c0d40c6070b04000d40545001d014100703080c450940007401c5102c2444030760b0709107030b0040381c41890480203000454040b107000300d4291210015400b001d10300003820082403000d0a0341030003039445589454200381801c149030320464a002d000c50038840545e440c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789968057 1250 789966807 789966817
    0xa05030a0b15030304090207170301060c0b07172a0f09040b03100903051803121c0605120c03060c030f060603072105041e080f0c0a140d1206030503 65
    0x30540341d03a5a40b0320561044601000c40780ea5058040401c2c0015035203202d4028005c443d11810309580c440c00314050803030302d5000c244554000207071140c03803490114041c403000d550005070030700d00b000d852110148003150881d41961150010001d0031880c00400d10400450a1042142da4541d4504202d800e2802c0e114003c001040344156a155204d5000395000c010000745440055424407106005040250254025045800c290852058480042e1030302141000441490340019070803c000d454680c00154201e00c04081455501c01002c94299914100f5285880c10b0000a010454a4400741418190003900c0e0440d1400301348280004400c101c1d0301c0907807000c0d040e1540c60f202ea44401c000c4039208080361081040200305202290541d005800161007207000743e40744070002a4803000c05914102c11400070341840b80c00c2c8030001042030302100170200d4519010482d80105119298016030074136800c80c03000b10364082e1504408a5403c0030781004000c1c1000c0741001080d00d0341d10340a0701c070b220b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789969307 1250 789968057 789968063
    0x504030e01260403021f11180f030f0304150806090703020c030f04030c0e0903120403110a150f06080a2013052a07020d0605040f02030d0216050a05030a 67
    0x41032240c41e10014050480004500c1c450101042ca00305410069202c001c0d81080c00002030100c411280f10318594001e4408040e00101d0580c540380a030144945560f80130f9050651204c03400900000950b0200314080b42c1d0842032010f1580d43d490006044030340c890301b2520906000140c4200007940d510a01e100ea800000c608000da0386030320302c617440d80c00c40c410b22038032400311880480c01000740003940d41d084059500c000200c1d144c903141d40b074009546c2c0c000c40d42c0c2c020401c0700110000e40024401d013544050b100d182c00403601c14800c2951015004c40b4200c10303011400d0380c0c07058101c0143c0058015000145885405840a04c5540d1688092000c80030f00c1e4030601118072034213005903141c0241110f0200c645d500c04100c5401d0080360400e440c4110568804548a13084018100748a030b2000c40d0b41503540241071b0320740c1c410719658031805040d000f0401c0c1c501c075044182e05c03000358030140722908210341d09502522100c00b41001d0501903460f103412030b038003c0c1c42200c1c1c01e004030b48000440c00b802c150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789970557 1250 789969307 789969317
    0x910050619030f0201140d020309010f061202040b130905010506460e180601050109062001020f030906070906140315040f02210c0304080702090408070606061707030504030e01 77
    0x43c0c04d000607070f002c21180c14542c0c4208800070b09428030030559406140544003000007400807180d2807203040e0a0b26894014010300305d0411803035800500d42a1701c2191000c0001c0c0503a0201c440889c2c00c4e804844444205890341d0351035404002e03491402203542c1c0704803032846507652030590107003121502002e1042d01d075030b030320802c1900010650f0283d0b480c90001005e440d103000b00d9514280d4200035005002c60003d460314451034001045641c0180c4040b030995215075280700001c015862104258050382e00361000c255070030405038401801002c0114429146940240044e040c01c0e08010001c1600754440801c00031280b500c81e4003056040c08a83d00920710716410424000103600050017480c2c4104041c07005d620001708001c02e1924000c0c8440f210b988518080d003ea6109001c5190070b00c4211802070892504108403001882c1c018006902300340108009401c0c130803207645800858610f500300070046440c080f071003c0406000d03501940e000300b4030310f0244118101307aa4058444980004100c0c1230103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789971807 1250 789970557 789970583
    0x140601080703150b1005120f0105031902010c06061d0c120c030a0b030d08010609240f170f0a0f0b01023403060509070b0712031a0603091005061903 65
    0x1039081c4c0c210a44950004005081c0400b0b00345000d0010360040d070f19210559143c8000030090201d03012090b04942002d40540301c0d41c0881c07201010b02c01c100d90401c90501c802d0302c17228030105605204005c05009104c041105842c00807107030200340000103110314500c400400c50440300300e460040c900c0c0c010118011445d220f40b200403c95010308100303414188c2504c23441d00c030800c01f5a406110703c3c1c1241c0864495090203a11071065a004000c903603102c50f100c050094411038001d1194081400c041014070b0003101c00402c0e0700301e0303483c000070030b6900c0d074940c2d240b0320248044031040707200d24113032a00e00e0700c0104200c80b0340c640003035200d0b18003400d200d10340c5083c000d042400d00703845203102c50100301480140915540301d00d040001040309031554001c80c4100c50003c140d05009204441a1a0700f107041e02d001c10a030b803141140981501e9a800c9100c90b50111490019220b400145000b0f40f03102d006045c4e00c182d02c0d500c11084410083c007181c8542c8a0201054903d50b58030110016a500302603946121 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789973057 1250 789971807 789971843
    0x10b0a21080705151906030201080c070c0f03050309090c04030b1f05030a050f070501020d17090703060e060928030305060d0c2301180b0702010306081603140601080703 74
    0x7802410070280180c020b8200c903d80e08074400f5000c0c1e02c04c4d61121940319032417101070080000c035809400000e000c160f002c0e0120351060100400360032420b1203081d88901050320742e005220926050750040b02d1036032020842c00c0c50707498070000d03440d400b4180001460410340303952034240300c0f160084d243d21540311402d4140c45107c4900c1440a000c0c103000390841d03000801d20702c0c003a81c2d40e0740646e085c1c202d1802102c07004112588003003074a44c0300c1e01440d900c4428401c02644d01e074200c03005c094108000352050410000009203140581c40d0840320f510003605d0185402c0e141d40782010a03002c0d800c003616814449440707040110400c18015a50140380005480d502c2d075000c10310f4000302c00c40c0946000900c80001802c100889502c0c00d022200346000d4603a00b8040b1b00640c1c0d4040b2900c849841c1217010f1100b806201c41010241c03559600515020920b107070b5030401a0304280c0400008400c100040c2c07024020700845000c070304c0d114124134004140c01c0d1314044190386c480c85603020080c106860345810b00390f9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789974307 1250 789973057 789973073
    0x11041d07092106060b04170c180723030a0e060714071a0103050d11060c030a0506061306021b06040e15010c0501050c040e071d06030a020417030309010b0a21 69
    0x9410380c030140402509072114010172184d045440741500e051059840507040c2040826990000d0b1000381c04400000c4070745420800d8900c00414403402c010410400090320803801c11601201c1c810150201d45d01d003400610300c1c05070780241c00d44841a5000c1014040c0e0360303501c001312400410302e01f6040c41c0c80700006e20340902e0f10050104652102c82002002009102012030381012002c0309459215141490b510002d4407201c0072103040700381c010103000003146903065420156211500810152801004101c407141a4000d6000000141e124070602800068a840116100c0c3c5088500b0f50400345003c1c240e0146c164018000da100e984200a1101d550340103826240c1c4980d40100240400c3c179000d000f01e14107801a00c5000c0400e046040400d84180c000c041840001e201126507844100100c001d10403a54400361840300040d40c01c1100081c0f9680b5181c01249600c20341000d143c0d282000d11015094030881356805124001424003040000050f44170302e5100102808a42c040b10610708011030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789975557 1250 789974307 789974369
    0xf030a020111460b06040f09050313090608031c02091504271112060f030708070503060a0c091a0d050c0a17060109030b061311041d0709 60
    0x9000c3c400c40704114078265243c58202e00c1c95080d100881950b02c5080181031030315502950280001200901040044c01c03c2d0304000d0300613120300c2003c2000a0140d644500d03691141c100440c030309a07810b905003d01c0d282d9000d004020b100b07280080d800d0040031007010345603031120001c07584900c1c0c0c0090b1580154a482501e0703140052111002034560b6510800640d926101080e440c16015850440b15802d03a111702c1001c0c0303440030001c030030741c2803890b0108660915000500066030140b40320308a0001c60b07030200120406040080302601e8061714100515242c0b000190030031200302c0c24401102280c507840759108048804c04400800110380b08040884648103c0001d008400d04150422103c1c2c1190002020042266a2104558a114031680c2400c030000d5031841e0028201c1d4a0800210f000d031942a501700340c0080c410764044048050041c100d402b8860809007201010138200002a0b201c00b51000b082d11000c0c00004901d070124004040c00c0c018040d00000044411180c0310600790040003507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789976807 1250 789975557 789975583
    0x312100e0f09060a02040b07032618010509010902060a0f0912030305061e0a0b0702060d180311060709210c0602060a060506040e060603090a0f06020a08060f030a020111 74
    0x10646007000c00444800000803280e058542c8295804248800400e1003103500f203444012550b13040136100d0350202c400900d450442d4003d030f41c02c060540f01c00701805c180e007401450900c0b4044c4041c0400101d86094480c01070005065034544500d14000d030702c420040310f156083c240382080003801c00c40c2c000d49003d00c09030814520300c0140c10903003080540560026024400031035504031100140b40d05400c4a41460010a8206032000401c000c0c0c5000c280281c8440340c8002d100345d05010341011624100d85d41e56a0204140c0460820700003170581082d00000750506500281815140440024141040728811030000c0c441cbd03480c1074210b069210004200c4903078030003880c40005a0b034810007035075100191075055106140c0180003590345001c40885d0100caa0141c24034584c1d9441000b000704513000140018602e009044404d00040c19519150031010b200da4001030b2540c1c20520000c082c0c1100402c2503024881d0503000900e1036900158100810b86d09183c800d01000c08000e81d9402d154441901c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789978057 1250 789976807 789976829
    0x61404090309150e04110307140f0f07060b010e06070b01060c170c010c09060903030801151106040b04030e040203040515040c050a030507031b051e04061d090f0708031210 75
    0x6aa0042d4024284d19600e82d040728180070910f10038511414520058031044c02043c20040d8807008030303900c0400381c103440c1101403d003428a0314525001205078080c10701160000d51750032007055150380081010018050a03116541030056980c0c4c0d9114201044c0549030910100c5803d0703c0c10814002985c50f180d03012098400e0700c1d201a211102d003e03004500785900403c031088800706009108910000c116038144d80c8408041e4649080c810282e00035814800030000300f861f0554207042c00b00000340c02103101386003004d01407415081c0242811486810180b040d401081400041a0001a09149801c2c1d030040d0001e00d0b1114981741c820564154086900402d101d80000280702c2d000c1082c400b201d024010380e41004c2d0041c4492486c20321140070740c941c008031041011380d07a003418040368101071601500001d001903c0d00c403810184462000b180d00c010402808100c0008414051510342030401d0000344011401d10140a8803402010000d501c41e01c540800110b500d07100e504083d00520300e01400e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789979307 1250 789978057 789978089
    0x1e02070506060f0634020301061509050105040302012a0204050a2007021c050709050c070203010b100909090609120206040c1d0f1e1503010e01061404090309 69
    0x405911200e04550711845820801c442e1032090903d1000c5a00401185c101c80c29400c4180c8007000c2e440b68098001c00155000f0440d10b001030f00e092140c00041d01140c0c13130901d0520304000d0f0040210056801090404c1400e000400050740c0100c2010125002100e52814480c0340141200c50200f000d54042e52040c140014007600b10115404000ba41c07200d020001d11101e03001e8845103062182d108003c1d0840a208005105200020510301c91a44904c0985000580da45080740c291030b02039590708500707200001c42000f14030302481400c4940b041516403400d09130103101d014019240e244201a081503c5002150070452180c0c48080074503807210b100b42003000265002981c0301e4048500700c0307010001030000305040d101c084540c8580709170100400015500c000803480b034060050b2400034045c0164400844444041503000c1c0300308060341101d0348400c0041c0805083d184107010710400307640741583c1844900c1003e00102400c1c1c03c141e0703011494110a1404880080155200f02441c8002c020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789980557 1250 789979307 789979313
    0x109050109240932010920091b13050a09020301170601030512070c12030806010207060e01082d18070506030c030f09070f0f03060e0706121e0207 64
    0x3460480054525555441691030000d856040320400e18000e401d481e82d03580c0c031000400c14090901310001210020803001001280140d00351000f9000c200c130812081106003161a1081c0400c04031800110358542880c00c20201d19810340300482d4140c03d2102d0000b44038050004032461600041801405083c0815560031404000390003c1c0101d684e03441c0d0300e158040680c0e80002d03009050761303000005086141003100000c2581c1e846501c1c00c40d0b08000e030140019408280301d0701103800a020707031107070f82032442c5c00000281081204e401c20014441d50444e0f021050b40c0c4580d0300d41d4018100c04070391190b0010001c0c00070020301c0f04408650185007a5042003110080d880d000743c83c503401e40c01224580c0303881e0000c01c0142d00080360b02000d5480d05200003504480e006410342d40140d0b003d015a059540ca440841686a500350000b400070b9669100420030400144502c1426085110191447c103007440001000c1241205070314650649031062452060501002e006071860300740011555100760745 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789981807 1250 789980557 789980573
    0x90405041e030809101b120f050a1b0206070f200601060c110904080d152103111606050304030509090a09030806091b0d09020603040b010e01080703230109050109 71
    0x19841e0846004055941032100300d070740622510030003054040f5101c002c04600445007c8919104c0c0104140c90b010765082c0305100303100302070284080300008980100540209241a000c24000c030046500100801503243e502807469401c1d90700510b009200d0810703001c503a18a014170b1a040300c5460042500003c1c0e016044001041c2941c03003104c03103800756101c2c1010043c0303501086074042c005a100704030302110303404076a1180d1b0b0407a01401101c0c0109403100e8a00c42c9076403068200c45611080f01f44400c051642007028650b40c21580d070010003103160030310b14a00e010000d03481010207010001c408641098056000c0e544021006006000705242101494000d0110298240c01007200703007001c15114204400502d00c294030803201504a102e0003039540e1100d5110b060448030480c2d0302e500781001a031300c40009500503400780801d81c8441d41000c810341c0d074180040e404610f907032348401402c00009140c04110040210660500d44409000011035800740c407003408000c00c10752802000034200070950b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789983057 1250 789981807 789981811
    0xf060f140d02100f12020a09031a09030313051009080a09080f030405060f1b06040309080d020604020f040905030d0b0a060504030b060f0a0b13030b060a21031808010f0b0f06090405041e0308 83
    0x4ac5590342c8100800200d071050580341a104a000340e0010000240f054541160301e0b456244228100ca004a01003a421f800701c40e40301d4000c4447c40000a0500100d59001d0319140103400d408001e084813010f548503582d66403185105650080c04c0114200f0001e840490964240c911280380104aa140b111040d64aa24003103034211b002c03c50695000c2050034000841501c80710940d0001d0000f501e8507001c00034142e5104030141e43c4a52504084070000d101071000e08500d151440001c9102c1054031704114680569400003010010240401c1002c6040f040310303503400207429501c0014118a81000c070310140e04c0d40d04020b8682100003428541c80b40d104a000c6c045a0080b0001c01c0302d0786a060801018450522560070400c0280c40d1f008080302181c008010306520a01b04100080104c0548989141d555070080e0030300e95503140540039202050040645911085a51440400b544c800142c41402522885400b6542d104006010017108042c0395007082012007407030611502515004022001c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789984307 1250 789983057 789983063
    0x906080105160c02120f0d2604020117060a0b0a080405100b0102030708180d12032f0306030a08160314040506070b0a0f060f140d02100f12020a0903 65
    0x28107400144018040c0e95488998603483d612070a420607640c080200c45681000e01d29194003480340d1010344040d04210031440072099031640d0856840700b6490924106041e19100c10b007180b142c040200507a4009100c110b82100b003600750030765482d03100100780f00125540242c0c0001400155000060f9080740c081c40c403461041c800c4411003440b26500070140d507094003496025030300a000ca4400501050301810314014540210300c1c0c607c0104e40004c0c5444134030307041907415204050248484a0340760140302440e811030a68580d0823861030544940510000e400d410101d9800b102082041d6030510056210f5900540724a4654018200c3c1040081c0b600004902240d81c0c807509245902c4500292021100020201e608085140c1c441020300400109200102655030301c5c41e12982c2418401e24010b0440014003148850070601821000d4407030800c060301c5680d40034800ca0060b654800c4407508031003e844d00c503081c10740014090b25540d60303ca40041031103001052481040e544a11040b0880b80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789985557 1250 789984307 789984311
    0x190212130b130201020303062106041a010902031006050a020f100b030d02060f07050c0a050601080303150306190b030106051206100b0705030301060806010e03011415060c0709050a0209090109060801 87
    0x1140c40030041d03080364150b4001c0c05a0000e1000425910305800013800100411070801c4195400c070707403402d0030541d0484d0111040803403410110144546038400e9400b41189580451442c20400d01440b103202080c403800041200014609915600c280081004882080111800700100c0703990f0380c0c094142d81d0505400780c40341e0344001107a540300080640c05440100d00b00b802980312410201d0b116840b00b080c0c1101352007113502c40b1f40000d0342084218000c20960024640324241705d01015071100c2e0039100207109a00001c28094203480e082c0c00407a084058400000c4d41166010210f80507103501c0d0b110b16440348810703038111480f010201e4281e1180003c468412000c540320000200c050103403040280180e403080c4014807256021b03c000f281c01500505052207000d000c280002d0964883d1182490500d0650f010b210364030140610300010000e0071500c103400c140c4100f02140d900c074480c1c443c0c0d06505485801254072491a03074101c0702030401c040e140411300c0da10713986500302400d4107209101c1c480d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789986807 1250 789985557 789985561
    0xa0e10090e03040e1902210411010305042a08030c07170106062102070213020c01060605040b0a1416050a03020705091003030c150c09030308011d190212130b 69
    0x520210848060301d503030340c1d451003d5485c1d01c6044900060414220702a0541c200030031601c1362000021404202c10220030710619107818030300410000e03594824141498146014080022000141c41000801740d02c0249900640740040c8a03072150f4681c8200c2c060f010008400024140204114050300c04d4501d054010b4409000003900321142442240001505098650030903580804541030000c00c840025041841a40020f82401c0b0b02078104000c080d030004680201507400e004e4034004244600b0440c1c00d207850082c25200a1103640000070800880c85540107410040d08295110003000b2030452840070001d180c000d0347c500c084207060f0094402d03200d000402d40b800890070740c456086c02c2d01d90300900d4956601510902808103049440c603040240b07007042180544200c100c50303181d96554031f1040c0d20718200a041d2030b8068001d41e09102d110b28203426050312a8000c00d801102600c0070710074640d8442000310003402415811180c082c5144207100981c1c0500c01d4401d061405048c0003031940d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789988057 1250 789986807 789986831
    0x11040815010b04120f080a0507050d0f1d010c080310030b0109090309030609030302161b09091a060a0b0403031709030705120d0603080304060507032412020a0e1009 72
    0x800e09204a03012190200410720000038150700900402e44200751128081140380d4800d41c250f000002044000340000c1180c00602c030042207120b003042c0c402d051003020010091001094540070070088090000405100b42c1640d20a0b0640d00002e0b400140c040d849081038072a0781c0c0702c1c5026200c1520160b0f01d55002090444652150b004003581c10303201c80b004603245a032420042c15285400750103160782805203190015035450406081c1c5d2241110440610101d400141407104e02d8000c2d460706840c00c207080e00001c0c0bc0075441d01c1d00360381a03481400a9950540000c265a00c69004004600d001180010415030000c0520040300031841d00c2464964a65500f15a01c0c06426170143ca07540c00b2103a4000786410000040c00006508440030491940300d48075020140d0050744c04442c455617400030888426032610444400c40090f075034009403418444220881010a40280070100c0c0412015004550780e900001009142c4901000074510301030114900300e40e200d09c2107100242c24011031281e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789989307 1250 789988057 789988093
    0x2004090f020f1203030103150618060603062304020304080702031b04060e040201052d040b03060301050c070c230a060c05070801020307051b0708070f060e0a0308090f13110408 77
    0x9540f012100079415a842c5403138101500c0410480552015581d010100702d40d444c0110700c00400540a1001c10003900d861030060440341560702212050030f041014015143c82c00b451904808000c403005600c2e2f85540c00c104400707100c0c030705000358580f00b808955002c80c3c00441042d0b015000840f010407625070364200010500b070040b140240041c0c030400035004809007584250b11900390400806171071244071040307100703180c4c4a50481d540c842008020481546001d01540f0781c013509481d0403500780301440c4d40c4c64001100c3c6004548101c8041903040440b50500c03d81c038440c0010041c02800780640c3d640340a00140a440c00c20f46050288507404145104140200c074001ca08030358640f40307000d8039818028070040c1d006078a00524041c510001500c403c5c04c003d10340240101c484400c005901d48a00509820f0981003070a01445c1c4042d17081010510000548866038030903201d458080c10b00b140040c21403402c0da08c40c1029070740b421b0011404011808060300580d211082107c1090218546401e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789990557 1250 789989307 789989329
    0xf10111009082505030a0c0c0906080c0105180411040608060102010e0d0e060408011131090b0d0c080102041e0807030311100f0c0f03050f042004090f020f 68
    0x700c850010000c03642c1080d070403c02e942d03041c0e4041e6080184800590740b441d085034400d0110714005094090300c041071107001d5000100600e4580420002e551402030565100e40d0b007200c4950500c41c0104d4001503500e41002da210303840c6002442040045101009400190454001c40b000203200c0303400a4800d50051244c0b0002d84c1c17a040050084482d0303a2011074480e968403a200d50090001e11001920110902401e10502c07880c0c0300c440d0319071100b68901c02c1d6044050b003403407803542c50f80380c4aa02812252034010701079404085020600c000420007082000002000003001052400d03800510324006501a1050324a0480b0300501038001ca07095171051074041c040c02c0c1050300020b0040000038001d07179610149482c51802e030b8a118042c02000001c80303400340055602c654641514010155115070400107640d000c0c1810042030170510740146102c03000800081034914400404038004040e24907039054000010414043d166162400c060b940c0314400d03040b030040c00108400c1c901c6203402400b42c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789991807 1250 789990557 789990563
    0x7030e0910030204020a0c06110a0f17013309180204180b01030e070303020f0d09031e0606080d0c02040b0904050a060b0d0b01080609390f10111009 65
    0x1803050340c25030f02003000951204a0a006000e03080510600041850081c0d001c01e00320f84104035100c1c1c020400280840794034594900400451b004a903006030604040c280c10740d080c0c42c00004880c402c807940c8111821340403056410001d07104aa07985441e600081103c1134030301134400301d10005800c500d8101079020b2070161000401d01c00003861280d081542c4061010074051502095820382442c41900701003490308140c005802c0761140c3d400c2c10104110055401c042464040c6426185448002240b616103803150b101d0a60000c3c000c2c140503c0740c00203800b81100d201030750002e40201c840602103400d1000221b0103a400c0890303814a41c608110311034400c5401c0009400501c500355140d03001044042401c0358040082c40204020400411101d4060003162009004a08005400500e0268108010202000d00c0b1500100032000c0c0380c000e42d0048041155060042d00d0103001500000c0c840018035000303001081205076150f8485116040d0072a10780070740740241d003031000c80030a90f5107401c1c1c06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789993057 1250 789991807 789991831
    0xc01020316052d0d05090d020f06220302120c0d030501090c2a0c0611010e0109030f121b02011b0e03150a1d0102031806041e0305041a07030e09 63
    0x4511000c100301003d46990602503a00345040b0008001c50221482503078189000d0b400441011400c5070100154040140b582009000b81e16003007001c0b404444c80d44da1030303202c00c068020180381018002c1007991714419009010945070101000e0050350381407100100d0002078107000c0005080301892281000303100a035900c40503041d0100100315411108515025020b960b0340300031002180c559121a00541415516003c0042e0031070340c00b80c00c0d25035056082c1c9259260820301f17000a9000200000c500c062400c010000301d14048021004200480c000c2c824504a10404c0d90215810b61210035a0031031620000302030b07222480c0031641c0035a4182c1d8a501623124480031181800950301c0c2c0c542c00800c2c00f03000b01e49071700c0001042008003440c2400c02a21b13034003c0180980324440c50390400c0c0243c0c84000410b00d03845c03d501c4682e2420740e083d40c0d42e520703468603070b20306030506110b07604803030241403040814420b840c455011050545e103c0201900080c1410700b018426140451140303014a0400741a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789994307 1250 789993057 789993097
    0x40b061036120f06111c050a0b0418050f0304140405100b0c0c13090b0406090519080403150c05090f04020c070f03110301050c12040302010605060c0102031605 70
    0x86030380075020452655240e51841e6000038103a600c0788040d40a151150b10003100d110407a180c113509580f900038110080c0c040a208216180d60007025950024200c22404107554603940807400080c0254180c1300d41060609a61007044244440540354080c40380e012907201592120565449004a0145c06018000ea440940341c520b403a4220941110309482800c0c0156a1001c0480c104c2c0d100c0c5004030f1841d00000d1483c085854900e400284074002800309021100307040d03131048011400104001c1030140c2c0d603102c10042c003104111402001c41461310290f05940c450424000b6600180300880e205003840844c410940304034050f2005002c1c03e03446031800c02d40c204041100c50344504a00300e07001982800040303c941e00401c142002460650b00c008200c81c00c40c1064483d4200b841d0501e07000382c1c103040038024846900003c54002d0200d84903561051b07110307458120301401b10b44d03100039800303000494140032004041d80114018514000d849203206181442520107000e180800d00040a504013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789995557 1250 789994307 789994367
    0xb132304031706031006031101020601152a020a030c08060606130302091e010f060306050f090103080c030423130903090501110102040b032503050408030103080a0509030105040b0610 80
    0x2450743e400c03200060640b0f601a07075405004086913000c3e4000c2d10100800401e1490f2940c040c0b000c1405400c810b10a03040400c0d00341c1c00904094501c5020f4605c0b41c450320440205c4424031248214602d5000b000e49481e503030380b405d016810110900400d444c2c1d00620380400d103540341117800c0f00c250141e820b2818882626540820015000080c16403010001c0950794992407002d02d5030130340c00780c210700d06c030790412074200203009045440640015000d010500000e0002e0ba032500040c5044076404440c6980d50941440341c0350640c021940052461101a00030500403008002d040d0004a002c0e01e42d039081030b02c0f1064110a075202020b01070003086505100f8840c40d44245103044a0480c0b00b0005494a0b030780c5c2031140c0b401d40c8129841e01090340b0a01c01c0f807075280e03c09110080b00c02c095180912a40c1070549485140d40710620004050b0400042d405100601a0701640d1140364003c0c004c000b2490581044009820103c51442c400c0300d50520341645680111800c1c9114413001c0c5600c00f03840847d503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789996807 1250 789995557 789995597
    0x120c0f02090a090b0708010f06050f040e04030c05010e0c15090a0e0c040509011706180c04020d0603080304030804050106050a080a0809030c0d08040602070e060f010807030b13230403 80
    0x503002e601c500d5180e64500002c9603a00300f0a6025009541d201c882e25894015800161030b05034102d0403c00c0410446000700078210010348040d59216001030520751550700d07040c0c4c0c40180f2444c0041140d401c00b03214008082010459a43d0f07807200f0b41e17031120300900002c0b1500c001c0c03003095a42540040045030502c1309420a07000341e42c1c04401c00b260980f50680b608001a4803010982c4200501001d49009403c070f084140a1141c00800340750112111031122800c0f142c56074004620f003030245a0104042d0f840d5019a00180d00960300485080e94904003400e0050401100303e40558040d030800038001220304280c410702c011501501d0182107001c071203070780d214032b1070307108060b1264184100b08280400366108030901030881e110b030981c0340c0c0da03600e8043e020b400c04095a07c010400e0040c0810801a500d8a4400200c000c509113000303410350ba0380130310582c01885071440c40ca030031156510044141c500c0300e07884241000385281d0100d000d03030310615200d1000c4104031401400510020302090401d0028 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789998057 1250 789996807 789996811
    0x70e01120b041d030316032a0c06050f24060409020f09040219030f05042102160602030a0e030307021f091a0301050909060603060720030a0804120c0f0209 68
    0x9101260714221880e001ca500000083c00500036000041888003400d070680c61584806103070306042c4040508103078540401048600489000d10040d000d44800c180300d10340c12108075502c00001c01a6080000e14406100b03002c84010141c0755406020265103ca24424150607280061409281c070742002c0007000603400403240114042d13805c0c0550005031f03a5038005408880d24038902d040c0f10072281500201941d140f0105200c0a916080512003c500c079403489042d59403081c0480d480504040c00d0032807821480300d0400d40c01401902000c14015030103c000d000e080510364482d82c3c1321103003800705500d80c8254031000754000b170030a0780c904101c10300f203100c8880c0c1c40b034508085c50040c1e91003440300f01204400e030800541850010050103a0302e08500f206801100c0307031000f8441d9142c031101081e0b407080058240f50074401d910700c1c0c908162484240c15203200210b05c0a4949030004840050114042a078007211006149030b10403201e07a20503e107040d041c50704801e0311804010349409000c845080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789999307 1250 789998057 789998059
    0x20610030b180f01090501051e1b222c10090902121204180218040b0301150f0305190c05060901090e091608011103160504030f06020c06070e01120b 65
    0x78441c0501a48802031058083c45c81c015000440e4a02d03000c030b0910b082c00c1180a00901c66070400c000e00001520810751240d0700e0b9090040c580c1d4401140401d1a4580f485582c2c3c084a210300400205140e140c41d01d00300d10102c0032141011400c08424503500ca800c80c21510b0b500108204101000066a1500b201d018a40007810708050402642140750a003a200254410f480d04005410402c1015019890000d80c25005007142098500d149032110201407414251103941c6604000d80c20360b030300391700410003c0c20980300400465583d484010754403820b480261098042c1c1d10742140507aa01d0101020155031040b003c040803420501084842d803c443c10b05d41c1000b80d240d10129503040070382e40d4240a500701c80700410f00318101202c800c40b46076003a0045100f030f0741091584c100d00b03444030040c0c0303810000d4055075002805040204071401d02030b40d030000d0300c2c900900180e103043c040703d0303801491a03004000503210720ba65441d105413900c108a0748403a00155100d407013000300105650003d280f03260 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790000557 1250 789999307 789999313
    0x9030c1214040603090510180b091014180c06071511040603091205040f030b090c06121e190b0102011e02120609091905030d0c0f020610030b18 63
    0x121041d6075000c1d00160000070220360350f282444180201000343d4408100e803140e003031001c200058410556903942042c01001040f0a40c041441068140a51081c003507681e04100700c580c04429048400320019511034181c103026642500c01c1c91400f040303042424002502851411540c0e030350b1410350819081480415954540d1491760500c0c0c000300810040010703036408181c84825080512083d0f0080d5419002c0c001c003000308202e004106c0d20300600300d940043c0c41c120280c1c1c1e0100f100381002048540c0c107030b0100000501684402c2600d241c107008040005120b100c25141c1610b001ca502000c0d55043d0100100e441c0414a8800503080b004a4504c18400450146080c2194820720034281462001048c0c010030940d1b0080c012120080e407090040311000d07040d040210001d9240e48a001880c05c182c00811200418410100205d40550600d24020894132143c010000e0000407042c40d10700042c00b54202044a400030b488000d420341c0d81104514bd995104c07184c18914418200c0c1c0c2240c41c0340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790001807 1250 790000557 790000577
    0xb07080319090b01081015140a050402041e0e06030a0210020c0a03061a01020705060d0c05040f0801050a060e0609060910170c010e031207060902010c02190302100309030c12 76
    0x145060044500c810f20400f803001c215414034601c18200114900d042c154a403418410300d82640c0c070001410100c80744140f241d511041e902c000b1030051136050300034507041800020005182d8008402c85141070400d0101c18041c1c60315101104c5801d03605031201940340e88680088009481c0004442c0740540300d500423244100540c80c04148004801c0d030040d9039080c2d503864042040100107000040c3c00100b4400342c060f00e07003000300090300c074012846410780785e50f03803001c51401507800340040702e0140080000c10410141d0361080d03540640411186841d01034102000058140480d822540c0204401490b00c0310603501c034010b100909800810042c24075003130b00c03000180c4108801c65070b2002124000a072039640e80050001d044803086550700c80c02640300424041c4402003182c142d8600303680c04280070400c0703070341130004039185031030150082c0d8031100080f03c4206c0c00814451190840348242c0740c00200c44000141074045842046006e0f005c80e0106101c040060b5140000ca4071403038260610136108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790003057 1250 790001807 790001851
    0x90e16080a0204081e07080703170315090a0207110a3f03020a02040b030a0309061d12030901080a0209030304060c1505130b1018021315020c010e04060b070803 70
    0x12007014a101400056440c0e05156072400c10701c144005080c400009023552482c0d82c0d5503442640d20542d0320840b010020000c14441100c9001c903445400e0000d01e503030f80f01c2c00c1a202140c003d5102a80444410f100204240c0e80c0b401d004c00240c045902c0c4108c0301c0c0c0840900c0d0700c11204000100501e200d001c01c404032501f14044c69035210001c16009074018007003c0c00501c184001c480c80164594400e80c07203000c1500010354800e00b8401690f40c0b82c6805c005001c02c1010321113403d402195450351220000c08a221065400030140200c0a400d82c2d4a9a00c1e45034003452004a200d00c8240d250150403c110074801c00d40144113020f596880b031104130581c6003c403440c10007144c00940b40d049441442081785070520010380c1106400003621040c40c14481e2409908841c0c2208413406900740130f0b00031072074030905141c2a840340000c0c54201004942e400c030b03201000b901c1d02d440c604801d0200c2c0c0004150311590805104070429100d458003c81d107885401e8540c290150070080c246181ca034522103c00c002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790004307 1250 790003057 790003063
    0x60127030c140906031203041217010608040516150c05031b0609070b0910030c0e040c020102040510030b0303040b07020607080403111203090d020f240901090e16080a020408 76
    0x504481d11510449004401000078005010f04030601c00e6000c8071410144003040307000c85c0e0f00183d0027012240e2042501d00207a400300c551103028540c02c0c201000000c0c00340d4000481d184101e10030030940340300251000760080510716500401c100c0250412054540f2406004c9009400f401042103d0500e41001c40e04034411003110120b1380c45410140611400c8141000035030f0280c000002c60350309112094021a20303015402a00b078080603160110b184c01780e8080c0c0c0d01c801c0c0206001d2301c280302048065101a000c0d6001348580b074002c0081c480c6030380645102e44264590b51030014080c501c0d040c9454801025500041c100f0b0f81c1c020010404130001500d034000410042d88941400c0742c95410060400030103024681e1441c0e0f550704100080f440c5650394656402010390304485070203503640c00101040022813948400c00c1d100c50f110900e404100b20440203040505400d907200304010761524030654000c030381036805201d03040d10030656031003150040c1c1e40940c1c44208000c005007003560302c1c81980c1ca = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790005557 1250 790004307 790004309
    0xe030c1207110102060103031d041407030b100f05040b0d0b1e1305040506190f0212040c1205031204170d1d0d0e090a060305060c03011d060127030c 65
    0x40d821500288010820034aa095101100400d00207007070550f1440d00e01038491240c00307070316141030810b080034490300380e4596002d4414134200d010782c43c103545086032001c2c0080c200440d4092150300007114246807a0b204010250204d1820360f00d01e42080d140c10103070611a00190400c1541589444003488580c0b600c51100cbc507050400070014000102e598213016a00981c070b5882c22050b03013001c0c10172010440c0008c801d0740007400e2280d50900c50f0b0b1550302c204e00402460f20b8160b20341e4000291485006042140c0d039002d103001e11807440c40e02e6590701c00102c071145c1469000700f160b08203001c07000b0501204440030b035129000313805180c055075080c4641251580703c041c0390140140e840201c0d052901c0382d008250700c552070400c0103000e03851b06150040e02048082400c18829980080013408000031038101c00000c40c0d0007400c9a4540c200505040c075a03030800d0180c40c95040c0b203000c0484003400c0901c041402401d060310784413030a408049180350040c1c900103000050202000c0300100165224075004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790006807 1250 790005557 790005583
    0x90b030d1b0803191109011b0c1e0e090604030e09070c050d0917012a09030501020708120907150e01050c0706030507021605181b07120801090c020606040e030c 70
    0x62450212404c0801103a04901802e0b007507203424070843c000c50340c01c010004001d010503105000641102c0c5000460051701d500f140242ca8200c2d200361303d6002c001d2407028151400024105c080755101440c1c0c9580d5041120082d00052035550300280d58140715035910703048449490044045c0540751101850b210f04480a44006680310104010007503081400e5540c07010004024052403450b4103030041200314401c503a2024103002d2000c0f0480500584800b802103a0080081d0345400607800d04110076000784002016016803940090040b0302e020520308140c0321030314060f0003103080d1020202c4821000710714031418000100064212414100580380003084965000728517403500d406c000742800304c805d68032088001d906100784a650b9481c441c0c0d15000580c4c032030a01641d0758442c9040c100416150030300c0c0c103004d400107403003003030200781c52410391048103945400318540d9880c500c1c182190402090000160400c2d404180c40d0b14040d000b03201003202c50001c490421a4000980341040d00d089442e07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790008057 1250 790006807 790006831
    0x2120a051b031014010c030c060203060102070302030a0c1a040e041203140f0411041401150504031e060b0604140d061517060c090a1502150406090507090b030d1b0803 73
    0x80090321004c40049843d001d080c41c100e034101d11259406000c0015143d001450a9008400100542d00c00c02103080115001402c6894550460606840e4400e19010b10355201c400071888124883c0c03030a045908403181001f142c9007a42d03a58841062041c9075614500401da1036501c400d601d9104071031128040c60702e003503e04a6030f041071724200e020014021840c49c0502c0c20304004030b102282558440e811600c0303000c1e1700e080125070080d080b01e00380300d5600010305c4a0400310640c603006d103640d0b0f00205030324410b100401c440074507034040080c035000307608c039902844d2501115000030303040482c410740200d40700ba0f501040315110f440c2420040381164000d075005503460b0b03d550780203001c10051190004207540e045850440311002241d0719500310300681030290030a800c11110248200f00181c10614020042c2c855803c1ca89080c00c042c144c1c0c040c05984034461440e02007549c03610b0784501d000c03a0038010300411940d00c0040e1700355908644004ca07843d100300c803252782d40d01213803c40d0002c5104040202d50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790009307 1250 790008057 790008059
    0x4140109060f0c26070b090706090b07030c210201020702130504020907081b1b1606022505030a08031603050108070e0c0c07080c01020f0102120a051b0310 68
    0x5000c10380952055040041d204445026a80c028407101922904019003010720b5501d0320740302c0000ea140165a00c82c0d0000020410140320001c006540500c031690309031021565070f544e007156118050301480c125140d0400c140800203020b00c215180061280808480301c6280060b8106290180d80c0072802613500020345c0e508500d040b40050404060102e020001400c1c85d8000c945c0942005240030b080c0300c400d00c0414a4820316800240d02800380c0c1c00c4469480611040003500c00c00c5080440015214048580b401001000810002c0e589554028003607007511001d843e61801c01d1030343c010600d0003c2000480c8a031014803040300824040c039840f03a0349003000b4043c3c410500040c0505020589850018840c88034007090141c12500c0000b4440525250305040c1c6816100d5103c00019910079640300003104070300440c4031007041c8400d0b001d903100d8030643d55450b4241e10840400791484a010000184c9201c40c660005400c400c6d26072140c0141c1c46151400034290703209840020084042c4c1750 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790010557 1250 790009307 790009309
    0xe040e1510170d0806010c0f060b0a08010c0e0405060105040b0c0109020f0d0b0705091c0f03020714090c2503080f011d0f09390607030f120b060414 65
    0x1000002c1503044940c2d28102c0021080586a60324821020f0030400b9080203da2160310484042c2e042d150001c00ca0220314400b803800398002c050303040c1e01600444018600048017074042c481d2411403c01500c4d2441500318000821004044c0200b4040c14480b0601001c50220300c0c2c14040e0411500b5070000040743c40f540d004000004181e88080c5200341c1503004580009107580020982202e6281880c50301e500403400061000d40a810ba03600480301d0352251101481790b407034500e5203098040c3c1c0a0342d0344c1c01d0f2688910381c02c481c44142e43ca034000041c1808540700c691544003c0a601c00000c40325048584c50940c0030003440050003060780050764140074040320084944075a4010291082c0030b203900d89d44120640029403000341103541c41a40711000a80806041c800c514902800d080307104258000c002200c511440940583d041048000c1e81d24946802c0805c00c42da081901612205021000800100c0f034441346034841c0e011a0381c451103049140d072600c4006c0d102405900d0304041d07125a001e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790011807 1250 790010557 790010581
    0xf1903050313091e020706060e0f040b0a0501060f0509210604060b01020303040b0402061606110d180f0b07020106080109030e18060a0b0a050702090403020a0b010806010b0a0e040e15 80
    0x60002c18046103850315680f01c4c4013042d000d01240141851000d600d81d0840d0401d08010821507110b1415020751404001c6403950b043c02e12031085204126002980c2c440010708001c0721400d01035440400c0c001000105418064800750415401c002c0251310b05604410000c4030940c1c403d80c01c084254001d4080c88204140d0740105072024100384015421440e0948607030010755030140010f8001d038800100e442048041c41d03001d8020340d0300319900348400d222005400c1c00340e60142540804862074403802035a140607000628002541241500000800301d4940c4140b8000c083e068405566a5550014040b00280070740c150240c0251125100d5591003030910010740800501c00c02c2d000c0c000c0c010004d0076a0380e680c2e0720b8150b072090904552035440c0720707c065031107204041010b503006902c0010442016070000d410780c0058454140c1000300e0b661410000d6485400303000752034241e03070309000704103810b0b200e202018000c4000130000b00b10b40302c01c480080e0505040400c00c83c3e004018130f0400804002d81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790013057 1250 790011807 790011809
    0x2160218041214090904061409100e120703050a0909090b01060f020624030f030414040c0908030d15270c0f170402010314010905040c140f0f1903050313 67
    0x2d09143c070009400c50701101080c404c01d40b40714410761629004c6000e200603a40070000495100201c080b0b0360030b0444400e50360300100064055410708010901c4007844010a400d8201c0c044900f000c0d08080c40303a5001c0c0c03407682002c8030b81301c200094041c00168900c4940502e000f00c601481c0525925414004010a22810094031b0350943d0b100c10240f000210381c1e4100e079401403401c030610307041c2c03200d95100290401000e04c0403c1c1d10b5100c04503020600c0c480802c6940c0a1030780c225010044c01c20005010355075484548948501b40c1c00c18001c3d0325005101f500300002d46640749020000e1181c66100e80b60310004480c0b081c2a1164080c20a00c040b02200d11400d051115517003001004e1040c0c000c3c0c010202940694a0348494505001082c11640290003065548940030704080036580c641d07215000074038040310b040d5400c5c2c5540324001b80d112074204081c0c2c0107500161401c06001c4030602480b600d10090507a06070482e883e0b12040d003142e045000e00202843c45030700903540d5209551310803000d140403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790014307 1250 790013057 790013093
    0x103110a030c120c0206070e12030c0105091c020601300f03020d09050609040f0b03011d06061e090910050a0905060c130608090c030d03091a0f06040216021804 70
    0x5408041c3c11003940006d1040c1d4070039142c0c80c05682024845000c6041d14010340030540d140d01c0041100284054190000e81c401c04401c02141c1700c000440e4031008101c40d00f0104130f0003580140e00180800d050229111042108580f120304581540001b40d801281c101b810940d9510182d240d20000c01d90f05201040007e006841e080c84094101000108944101ca0302c40b0320031950751030300c402c09070925001031448a078020700030004130048034021a80024141075000702801490001840ca150404108940381c0ca00200c0b4402c1440075800e01c0050b0320080c0c0154914400c1242031005072444c0e0040d80d10411201d200418444842c0c5000c83c41c8c001c010f020904944010b0010403602480b04040b1002c80c1d0051900200715110307080c1c0c0780c1c204109400461f405020300c11609000542641080c0c050b14441c40036580c0c00c1080600c440c080c541d003642d0303007814a017000010600c1da01d4141c014290402c140b01803026214a15070000340901100d000003942038001004000c1401010700000518003c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790015557 1250 790014307 790014311
    0x110d06090b06040b0f0d0c0e07080117060c0405040c120603110a0b03090a0231050f0106180312200f010e030f0706091401051512011a0d020103110a030c12 68
    0x3d00c0d00008080f41c03011703081103000e2031000105405100850814100501c61903040300ba03130381060200105000d034240510740450040304170700034001070300140c4503101d440782a078801c1c142070a12003000302900340501c201e01004103030450701c0344a00840c42880d00840c840d16441c074032070383c2d02001d0143c0d8040b19408a03000b00d00c28810020240e202040c50a0500d42c107e40e6072509107031401010b00e8402414010104000100441c4242d54009034401801140ba44030b44040a070384e204c4086541e4803402854030049604d500c4100f0010340803840304c3c00c00d00518284104141c441074082c40010b007106071610215484450102003a910038420207041c034000a0146150085840c7e902c02e0621481c41c0060409669548410a000c640e07140c090070f100c0100003e116030300b020101e190120607100946803041c10349a041411a490520444102030b50b02e0b0203070b2000e0307840003082280340c550b4a1002d906040e1a0900d0f41c9041940c0310084c090000030b51000503807004040c030003c5c021241a02d1400c5494 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790016807 1250 790015557 790015571
    0x20c0102010603031211070f06051f030503071401021b1b04020403020120030417010b03061006120513050f0a1a040b04020d0318062102030c0306010507110d06090b0604 74
    0x203501105c0031444050060020034a0705203042880e0091240600203403800700320780104030030841c858100c180036a5081115000c40262010b031403407410700c40d11004020fa402000380300c000841400f04a003030301203000001410a01131400700c2113415a1880000040e4016880e0703801c070074001d0590400d084009407411414070f400c40c0e0003c0c042c0f0b4043c440391694002c000c81c112550a20400440c2e0242130b0942d805e0b4002c42c00ca05500d4080d0400f040103520078081c14000500e102c410f000305004031190342e41c0b0565040c0f06c07140350708003c0501400d1038490518144000740460810800c54440000580040c2580e844a040651031004800c900542d1a02800b080c0b10100b125640c0c4d10b40c0060b0112010f2402d00d41610302565224400a1903000500d104100050241c1c1c2100107905604507801e054160b500762808403404a00c011500114619018400725516510038800381400d280300312105a821000034001845550603000700329000c5031101c110780304008208460f1500300c0ea06803024070140f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790018057 1250 790016807 790016813
    0x708030306060708070c0308370c05011401151e05090f06160809210a060902060d110a030605060a09060302220b030601021624120c0201050106020c0102010603 70
    0x80c0300251000d8401c000c003145a10500400104407200c0e10b078030040803680a956813804469075000f0070045080a040000398820303e050760941c49061800910f500c0004600303e40095401c0c04c207548060780c1542d40c4100060245c5801c4d10094003074014103202d00c0daa000e9424004100340420103e28460f00440b00104145ca030f004010341e01d00d1201107500004408541d070100e406406880800b4809000200c021828080384100502d05d140f0143c0d00e010150020b6442c1c5201d40c4090103100c20903074808401c42011034450b07403000084070303c000c211502d012310020f8200240e600130701c980b284039000029503060315a01032040600814040e20014100f0040300e101400c038030f20714400c440c289030b000100e003448102500c0c07030300c3c0303010003c60046003000c1d450342000328164000f1900c246c094801e22019204c40080ea001010449040d00448006003807803960b10309002e00a40c601000788a5000c5650800f00c0503801400400901ca0b070001400e9854501c00a251400c2070a5403415645041424408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790019307 1250 790018057 790018063
    0xc2107380910030b210d02070608060409140d050301050f0111150702070b0f0405030601090b1e01140d140a0519020f1e0d0525110705091807080708 65
    0x41c0700c00c8920000c40640600140c0c0503055040d25164042c040a40000822111420b00c00142030f60000f194803012000d04142d035600381d54010b50000c43d46142c002000c80c0f03800d8000c00702e024414403110001c812803120207840d10a40843d2000400d802100500140c10621640301c9800c01c00d1034004890500200010349540c031101030441c98184200004080f18000c00811009002c494500740c3c0c0c64000c08188d8415810601071103100340501c0d0000600c014040c020440340c914001d01e11a0007401301d001c502c48154002290b01c6c18400009028400101900050001407841e01c20104260619044191941400030480000d00c4d10301014046903007141d181c0c20880500c0ca000051340c80c1c140039880c014900a500201003500710864040c0004404400640010656041c0c20310081d02c4440b840c401c40305400c0c14010440e01100482488030340f04020040300c607440c1d0015a40403944600100314904411220203901e152070298800c61020200b0a0100401c40003000d80061414142d080d62 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790020557 1250 790019307 790019317
    0x8040305070212030c0f060604020a090608070e090a0614090903090d0f0210181202090408090d0f03020d0f02070806011e0e1510110c210738 62
    0x40080c00704081d02191518442d100e91005441c088a85500101413829511a000f054441e00d60040c0d0002c18054189402600d015031070315118145098106001261031310801403400c41004a42c0d0000801912160142406143c0307104021030810308081415080842013030590303014005001c1004442e0001005a880300041220082601007050401000900844c0000703580040c07400030101846400c408180204102c0c0c01c11101c0075603551035140b100310398840700a500518200001000201e4500050160000082c142d4050300520344071001070104880c002c07270140e0300c031403204140a07400810100240010f40b004100c460b040c02c1c0c995460b0b580611400740800c031140b5115620b25403441d451030181c403030440f880300e1916040c0303184200e803581102018025009005182c41091049510080b1061401c000b072070400b0340d140501407160000030040d441481d8450400112030014041e50008200c80c40c1e8070080d4442d1406000c4540d03000e00028442d41440c1141c1c1a51002d15205030380c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790021807 1250 790020557 790020563
    0x30304020a0509060103020c15010e01060c0506010303030f06090e010c020601050a08152e03122a08090303040f0905060d021302030a021e0705011d0c060c0102070606030b0109110304030804 83
    0x608581c4403140168048d000e5901141500e000e4041c0b4140300c1c0c40140e12541c102c404072040e081c1d00340d9030368a0a40300c1c1d03540f00c4006810b581000005101281c00780d0000d01d034a0b064070000003500355442c2040c0040b240345140494559458098940f04103604018040c09440700303d810050261512168642d190216110140303a4003845000a12451a1341e1200c400788003864109080c01200003100360350305d1101c0c00115801e015487c0151290f41c13060201c041604480020590107140d00351500c000800707a030400b103440c131004201c103c0043e10140040c10080041c4900192460b0410041a0032b44200900f0240540040c001e400d02594440703040010102d480c80c0010b03600c0e10350b0074050f8041d10844403410080c01903820a82c066501400007020081e01800c020490104180448030142d0104c80c4810156801500404c55030310b040030050104080142c001071910180d5514141a00c565500c1950710210f00030041104803c00d004e480500401c031501d5924502e011b5a001c3d1036940090006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790023057 1250 790021807 790021819
    0xf0409020a0302150406030e1911150d020c0f0d020c270f010303110d0807210e07030c06210b0f03010501180e0c060f1309111b030304020a05 62
    0x400e6403101904840a0340d005070943c210b00d00b207500741c2e42040d80316118982c0028a881419000500085000703140700304d08203001c0e4040201501d034501109409000154450565100d81c0c035152084e4004040111401d0409030b20b030050b052019052180106410783d068100d1051194034072341c0410300c0e604600d000c40740c0440143c00481401907822003542c044602c10981c0c400e100644101c480241e049910a607a0391400c00d00c040075142d110021810100c001c506040d02140a40d402004125804194001c0c04550300621a5a041c00e40e14030028040440c1c0100a0502c280844501610082c0c1414100600e01c0c040100354134178203603020201c01e48800d64401c42d0f00019076500c03817030342201c10008000340600e5840f040456034030503203111000d401a24088950881c540003058074484658024a460b0403c241009003141c1648200641a2101c21003038021801540510850181940070a5099112070004040400c844000000c082c01a07009000f000010b0341c0300f0b028403003651819101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790024307 1250 790023057 790023071
    0x1b24060d06021c0c410d02071a071b1a0c040905040533130f1416170a03030b0a120318050d0f120e0a181a0f04 49
    0x8160000070b42c007012001e40600b00f032003014200d0b92150440c1050800000f600702100c00d030291400504403040308040060611034032940e8075400c500040c24412106c01005071a101d116036502c00b40042c0c2500300610400c044051296a541c4141840500d0144410a100d0380f145034540c208419208a4034025025440307001903034443c000c505490041400f1031042c00355082c145005074031040500110400144400f49808015021002d140595a00140100000e4a54965800d41007980c1c070f00a5500b54141900c40c00051040114a50300641d900060041c9507001c0c44446000e02c0d150b0310450580081054007418084041940f0b507120341e0500340080c0c2c0c1401c00010445146040e0b020f0080c50134071503801d0052642001e000f03074032140300e000034014060310340082040d4203514000281a01e011013040b84001007101054008421160800c08587e03008000029240c03c110381140b04111410000716182011034014071b580d40c10007a038110640082e002c08507160103c10340c5181d20454680c20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790025557 1250 790024307 790024327
    0x130915020f031f0b0d0c0807030b06090d17031317040f0b03040c0806090706031103010806040803090c130f0506042007170703030603050706181a1b24060d0602 70
    0x115180c020030f600b40c100e0fa100c5a045c440900100340343c280b06808103140900280019100707120301040208018005401c007908a01840b52044aa00e012101c14911039129111107041c1c8000c1d61040d01602603950007000c41b8078003859011805c00c88149d031068248421f000b1408984920415101061f13044c980321340d15814005020350303066002012030701a0809120b03080102080007c2a200141c07014000c8a01640c180b003110f00c000d214461080d005900071400280c0303400e0056030410404000c80b141941d1b00e0002540101003140c20301003081d52920380300c1d41c60030640901503000c48200ca04114122840c0c0c0341a81e0010030b00c1000c43c46000028841e820440351031601c510348500c0066440e200c49031881c010b0024071090106840905c107000000800350710481e004d03425103490f016a01c90052138002d034011521204007151224540038442072007010710351180d04e031800320300703500401e46c01209009003281262801c000c03178141c5076000200002e98945414501c04184d01280041c0d413049082c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790026807 1250 790025557 790025611
    0x20709061d190f05010f050904050c2701060f030612020315060d060911030f06010b0f090a0503061311010201060503030306090907050904050a11040204062309130915020f03 76
    0x1c441c2d05440d515020014001c95074a0780030034140d42407185000ba003640c980301003011080080750b008102c0d80c84a102007810342851503a900f00580f2100b41c6038940000640c4a0418030002d8009030000b5908444610805600d4001c0038004c00b01000d0400090f40246c000c682c56969840c03c0c8820b8200e04804a107094407044070700c0d03a0054000804000e48401481d003845840403005d40c407803207841030f20742e140c5410301c0100e91241203074006001c8502c0c2034410b44d140310581e000114810b5201c0140440058507031400e02106105a61681c0400d0302d812540c03615200412000681c5811a0b1400005001640f000021030b904160b044551b02181c0d0750700780740b05142003250342001d60000da5100500c01088000a2000c2e80144101946085c4007000ca0601007240542e109081c000ba410000c00380c9038a10050320100f0360301074968011b00e006514030106417240300d09261802c44175074440c245030500c10410368000a0b941103000540c50010302c1c0011034980e000280402680b02111071007410524211 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790028057 1250 790026807 790026841
    0x261903051503070f0806060906240f0f070507150f0c060f0c0203070b1e01031b1505070203011b2a121707020703020306010b0904020717040303020709061d 68
    0x2001c441c001d988690300d290484010340300d40d003170794402c05001ca401031502445840c4110390160520881c3e4410300200d0017200b044d11100103044a0410041040340d0a41d00103205100c811030007545d54444c1341c542145000ea00e0780c0051344c0703030301b0241c00c00024541c012884207a00015151520340040319041c648010400142c40350822031500301c00501c0d1940100161803064024070440c00160358018080d900036450040840ca002101c1c3c00600c0060000b020011402c42611b00c503110769030302c405d4880c4005410000c0c030b00105101190010441c6001d016030402c0c45400103034541c0c0f242c3c0d06203024080c4080320b120310000d4185018200860941c0c170b038075041d10a80014100c1c1403562000f6010f007125445016140d509020980050001c50001a8103012282d0190003015103a20b002c021859603000071100540c016020000c500119101c4034410744c100c071021030f040d0f0b500c03450751a0203450100d07503a100240007801c00c401005098180e044003032146204240a010550b103400c00c80d01c21401c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790029307 1250 790028057 790028059
    0x31507080a0f0e070e06090f060f100c0b091f0209030d030b01051c1d0105060d0201080717010f060f1b0f0c051207050f0102031c0b011b2619030515 65
    0xd80d010005086140d12801703806640c09540c85102c6848850a8000802c02107800d66008101c2114034521b80c02c20080039540b2a41924007481c2c000c69a984000c981141a54200c481c1e0f80280c1c0900022401c0841c2d155181d607101d04218507011148007c02c1d26001387c0c9014a080c941d0301c20309004181d0007a0308036020050b12003e4071000352006000e482c02884243c02c040c007002c080642010701c8030014401c0344e014081c014992454012598011540802d0040c101c4003004401a403911f545449c0d102e12034082c1640d01c015a00044c02c0c41401000305050009001c00c010003828a035468078080c1030074804030b44d00204007802d03c0c503143c1444481c2c1c99550340000d4204464a108020100002ca40f841c1540c00481b550a0021400c900490b0b480c007414a019440c41c810f2044002042050303440440d00d15018101b6042c0800d4000c8081c1c3e031441072400c10344d0401400308035100c281700c2180c4a454009405001d0031f04269104000383e07040902d0b040c000341490f035610086016410294000038030210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790030557 1250 790029307 790029313
    0x10b030c0307140a170a110904150f020c010914011401050108010608070e0a1d090102040f0b131203050304060606020a03080a0c11010615090509040b0c07060f0204030c0302031507080a0f0e 83
    0x1692680c856880d01d02d40d100381c40b07c6c029403131407160a14100020707900480d08140f0a10442c41c1012407040244070403a04000f00c1d542c02c1004071894072007800340000c0d59010389803424144100c075510500303468030001100b94904a15005000c03d0383c01000c8036064400c0b40c5416907055640c42400d40d800321245060310b501440304000051444200c00c03a0720003003281c14804002544a05140500f40d028901941d10703103030301d190f005000c1c02041d45c019008164002401e08500c0307640300406108030110050a8001803c000100700c1407001c5409000014240c034402024a150380352401040e0002c0500003064003612110b00030001c07407003500c0d180b0900002c80e008202c942d40d20307521080c1048a01118001290301500005a0340c80c1a12126202d030380c110542d50429a504a840c90b91688040c1e401c4440a83c1c616104180184910281002d10300c20050701403042d003940101840c180208500c601c056001c001084025035100c220250050880400401c0c1c0c5003000a01070080c2c0309019012103188 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790031807 1250 790030557 790030589
    0x20706090f020117100920180307060903050c06072102100b060f04030204020c101401050f03010c020d08060102210a0807021203010e04020607120c05010b030c0307140a 74
    0x1c0205104118500d100b6203400b00850224040b10b071206008496003d45034032800301c1041186042d0300103259400b801c220441038041c61410706900d5800401e2540c8402210212800407414200003280103080c290518000c00e510795900c139030b41c1300107918001d4001c540105500d01005420610811a007403408a01c03000c5201c520b50003542c94840280351502c1904129442c0a00d09114084640c12501c106c2200d15007401e6400f8480a50b00c0b0f60643c44036442608200c40520580b4451a054000c070f4004900e506e5260000708070841e48501c038044d1099140001c10508030781c00160b880c01d107407907609011a49540d410010307820300b04410401c003910360000c40c4500001c420240148040c480d43d80f151410b6864025049a542c21100b440022101003000140400300644c0c460740d5100b40300400d2a46403a01c3d40e91182550b42800f45a0b10106038240c1e00d03803007004001e004200303100700260300034100160240c0000341d40e00d050780705107101011640032078015500c440090402800400803203101103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790033057 1250 790031807 790031813
    0x20d03020a05010c0c080d050c090a0803040504050f0708040210050f0d020301030c1212121b0e1003110708030a18030903050c0411180a0e09010c08011203050f0a0302070609 76
    0x6440d001400b11155460008010030301405680705803010b1342c0240d400343c103140341c0c00c05000c020078000d0000c5140d4072084c8020200ca075a070605020290825401031501c551808003440b0a85101525000640e440e90040001031076214801302c0e48150100c2d101c88808032074003815032340c500c035014243c00540000650020200040e400560407288210200042c0395524210380c0c2d240d0b03800c0c07034004007044205091031060a1141c403a000001144010008000c4454450300341111900d40448001c240440066016403620803e511100c1c246402c080c803803030a58842070709480c841d00030300605200c40440400e8002d03881d41c0c0024500723900c0720094010b01e5828180644040114842280d143c428103441c00300c5070610f801502410085810340da03041880002555901c1c1d240700e0340c3c0a070000d6407043c00142000b60324003818000c480031000040e1400009c0b0004102d42c0c0d058200800344107044001c4400a94050100c5e0424881480b40c00e0321003d440780e0480107071291110140040d801e250391074080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790034307 1250 790033057 790033063
    0x3160e040f0218030601150e061b0a0f03320f0403020d08120a0b0906091909031e05130e060d0c08030d0f0507020c0918070e040204140c0a030f09020d0302 68
    0x1260f021030403a540c030781c2e80d00401c0b0301e00b040c070301c8060740041d82c2e905007054541880c81c05006410381300e02c0c90304220703040001854500b807610360081d6460740310641500181504252070b002d1700d2401c80709003040c0605414203944075400086224001d0710300040c203040c2070b4461005a4000e158000c0802c00a00d015081c10901500701171220b40800c00c482c4080f131901e180724466402440c40103058603919507501d10801040c400001c244602da03400c0b017840811760100b40d11074024007621070740f9030780c11408080503101c420300e0204040c5410300030f0400102c02c10f0149070000301d0480724000805c5c801c5540e1600424444c500c0110010b004e0361094201040440001c0058003071104030704400c01604561408400650308143c88010168009400d120311342d042021446602507210203102c058100c0e03030583c0b80c1c5000c68a0344005c0d140d1508005100c1145898001d0314000715164500216a05040300301010314807540c840030781403560791100d040d004111900038a0409400078100081c130b002c1030070041c0d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790035557 1250 790034307 790034347
    0x3a0f020108011d060603060d1e050d0504060203040e07180b04091103010e0a0f23060f031c030b0a0906090b151801030e0c09090312070503160e040f02 66
    0x8003044040c1c0002c100a81c0601003000a442803000a01190304c50341d00f4011240d00c061700c60703904100c2d4440f210020441c030006152050510200c844030b6420703e400c11500382035520b513002c402c002007004200000365001050703e0076903006110750403c4e41c4440300d0a8030381c0454240c1c4034004000c808400035000c1711060180c0308856681e10103100030021007e4160040c402402421000500903004c40d800712959400404040e00009001130010344000307649260710034034101c0320a59100c00042250320306100c40540c518003030550090a2240941d03002700e001101244100c5c4c209580c411a03004190f841c451008028000c52008001c501d48605181010301062000c0340d01034075244181c69545058201181d00e149105d41c6124044601c2d40e004401404040c000900507214112503007603140e9590f01a140294265402141c1d0707900318642120301c070500100a0424482d0500820000011079a0b42c0d00140d070071450184004080300c4005001022481891103a00e840800d0034204241481d5202d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790036807 1250 790035557 790035559
    0x11e1d06010b0703020d091d0907090608031c05040f0f110a030803061c03050a05090a170d0f03050412110328031802030c01030510180b010e0f3a0f02 66
    0x24040b5210800a0715a581f962240f103048071041c1007500c10070b1890400180d04008500e080e0707070055a680c1501410b96406410404217604001060b503c403403020002c96002c800750160600640c94a81c49110860020f50f030090b00c020702e1003000b0010000c14039240c80803080c004010742c00442e140d090500003a08115403141c010382e4103541c0885d00d0900008501035840e855a549440d014071418101c500d40c000c0321001e5000385900300040380ca140740c141c03000c03c0128540001c20207201a0358000f08008001c5c06130100f49440c0000344030106e050303840ea5080b00d851506040c008075641d41d06403803461003080c0e0320110150780700480701a080b920882c0344072400708980d41405100c1e1383c1802c00e41c2c410503090b8000d500d940020351011407940650022a1b2081ca146e02020980b13682c5c240e40d240c000c00303003810340c0c07d03460ba2020312034119a0840701d0800a040251075000c40407084c8001f14105025940d4502d080000310b02021a01c0801400e2140e007122060f108c0c00d01d858000c0c54424100c01c0307502812 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790038057 1250 790036807 790036813
    0xf0f0607113904060801050610140f3f06040e101d060406020d2306040914070b0d0c0206060d3e090702011e1d06010b070302 55
    0x5194040d400540390a616900c00c00940c01d90903207102c41119004a903118071400d03011540040345956841c807540008045000000c90f040c9802410080840084030484050140d400300d114041415501a620391011301e05d01999524250b156840644008840d411001c0b0107901d0008049101c03c2038801c2c2c240c010002d032260355181c070000c010a4071038800264980c0d511200d918120203145070800007403138031f44942020300c00c00411001401c01702d0454050b6180c40d00001c50600f09503040c8a4030001d00f2601498400c4040f070b02c11031045074500645208d01ca1511606080e061007000203540c8282c10003c400c440b00c417a83d645640b1480d820005a022040d4500082d6009040c00452524481d10340242801200003450352414441c424041d0b054401680781e052140b4542600346035902c4500020700c2d6440700c01d40500410000c040001e0403001103906108161404403410807121840d143e00150106424129001d00c907220218140302040700c0c402c6000000385078010b0001402c0c1d240c02030f070075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790039307 1250 790038057 790038077
    0x15010207060e130b0f0607030215060d03080106080403030f05010906050306090d020d080415060e0a18031209020609041a09010e040b010501050322150e01050f16020f0f0607 76
    0x1081e102c0e00015002c56400c03914100c0503203500c3c1015800404012402081c5054030008038000c10b070140c100c0e000c21405030f4090580303003140c10801052264088000c85000d03240c403d265400800245040c49801c2c00d112115010a04043c020341091080b510713250f03000c005545c3c0d15401c4070050011442240c3c02030282c200407840c011400310351101d003210306400600d1b1035001c07580110f43c074070002070003030300c020080441d144200052401090b00900b2540349210184c10b11403680b0341150021840d0109a0a00e1014030380026040071003109a0342c0c0000d000544445a4000700b0504d11404409d03e501910b4224800d040d6404048441c03000882a00c40b6003050303817143c00b00201e1100698001d0262070145004022a622420080da030003c009203408040445104050f4941c500c8a407007100c422145503403245139402c6038458201d420030030100901407810003040704488046c0252102101d40165054444003900802c0b0311040722002408031000402c0305030fa07450300c54800755044e034009601003074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790040557 1250 790039307 790039319
    0x306370902040903021c180b0306011701030501050612030a0f11030c03070c0317040b090609010903050f060109150605071101020703080a0305090c0a0501050d27051510180c021515010207 82
    0x84c9502404c47c0b003500500a02d08201107450f46030801000e9a04002d54180948420000a403640c0e008510039400840c13541484820050000285030700701d04503900900500451540c0907000307030006017487c00d10304002c0b409814014154801c000d4140d020744030002e282c00c1000700c030031a04012a80a849030324101344824401da0790074810741c4240303000c0210520003150b440c5812002048401c505040032003072643d07070b6901c2e28140106010451032641140c0010000308000e805040100280400c00e0400710341000005062401024805030122100d1550500680d008121640155030048080c40d29000d0140004010301000c035040311850140d0028844141426020002a110143c55881c10050741194034801084d80d8646038029200700c52240c0701c9c03880d54006024426005d10042c188043c1e07000301c5110800409001c8a850044019082000c0c01d4071040b052030f042c2c469503001ca0b4014101404070b1401c2b83c00100209100d440302e0a118030410b2039240c01030440001e07020b5030700013035881c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790041807 1250 790040557 790040567
    0x3070504090803160915020f06070305060d110303040314070f05040212181005010605071e08040b03090102130b0d0b0405040206090d020406080607030b0306370902040903021c 77
    0x1c00a090303500c18404189001030710108030b40601c81c1c500c0d140702d440356680f203410081c00d40da502141c096040a101603040c0207090096036400143c03403c007032181d03061000103d440d0000c4d180d009402c2ca03001d00b1006200c0e540c03e2048900860304600401a1b100f4410481764035070356a4400d440482c08410800150303820580207590008540c44540786a40d594112261f800d9640842041280e0080710320031001865544980f60281145960b1903480e00024a81a070314424041c506500d051f00102c0f4003400154024101c0b400c0d60402034507a500d80d03da8120304e601900520600614224910601256038401503001d00301050191405004d00409013003404103c1d101650080c2d0469800c02504085d4100b0b0800721452030310142000a20590b2008850704020064030004002921007030f403003001d40703402c201d00c641140416410b50320b500d2034280c8501c0608075004013220010f5504c0e4294030040e2169100004003900a0000d106496a07468025290610b4010051302c4500050000c0021032141d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790043057 1250 790041807 790041821
    0x10050702151b210a1a04062607080f0d03050a0b010905060a05040509040606090c02060c19090e0f0109051f03020409050a0c0b070201030b04021809040510110903070504 74
    0x507030207a0601116840c00355203902002c0b80416001208203c4402c450320700114901c6410100f40c0040c81c1c84041a40030842c040d010304481c0300b1420714009101100da401414405c1e0a445d940ea07030152103c00300c02a041401d0756016612900440030002c5145901180c8041d50b402039503010850359603000320a80881c1c03000b011250015200401c00d03c1035040840c01040324410714180503040c0b40c0d45500051000204031400c9400caa1940f03c01c1161401030b002d0f0f044418828000340c142d510741407040b41e116015081100005144074100a0205e034000c40b0742d00c0162081351800c142600e084c0715600b500c1d000c2031244038081494540046c0c80300c0300d0162044580114403c14803507a0385141c003040b007d080b4080d41074955000c1e1404041c0080c01c2e405c444401040d03510409600e5002034000074045445508810b801517004011121950041002c01440c101c401c0f1400ad01e151a94103000d460000d00601940c6024274100d9800e020070003003400f820300c1c00c0d0214212107000762141d01748019100c0b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790044307 1250 790043057 790043071
    0x3040309051009150f030f060909050c010806011403040813030503030412080615070615030f0c0b0f0d050a0905060a0f0b0609150d0207170a1814041d1005070215 71
    0x78120215010b00c3c0f04040174211041146004101d03405041c240d030b021103400340c0c0090035041d9158114420460300b40881e03101c414003401e1241207441d003100060659000c010740d0241100340000081e080004040a0f14a81c2c5510704c88200115140d292541d560340c03082d01e083d111052150100a60075110b2035060b80b080e01c010348036188042d00b001d03440f040ca40222004441003034449440b210b0803804105d0882c02540565402e001600c3d0f14180700000c40e4035504207030400c140c2044512204030001b42201c01c1011658030000d000d60f1950b40400c000c100c14403006000303000d00710600040d0394081d08150b5840b1032401081007920444010060700b4440c2030399035900310761908038030006a5012006072010454104002d0300e45103075079032100c00d01131000c0c41012043c107001c1405807040c1c0d4494403051500d81a501114100c600b444100c100d01c00f50343c030120b0b00c52a11584004620381040290821205a0700304544404006804002c0540421610040180b1420441020304400c075400d1034081c1c48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790045557 1250 790044307 790044329
    0x90b0a1109040f0f0c020a03120c0206060d08090d03090512010905060a02160b1006080112050c2205090c1f120c0e09241905060a0c050303040309051009 67
    0xc200042c000035004440418032020340d035008805002505010b4110002180c0d40030744403c200c1850081c01d80142e4414200503146401419800190001034013034000341d089404c2950320301030b451701507603501c60f1844654214180c51030000c00c044e00415a0400e50310215070801c0921031124101e4200d820000000e13202e503201d200031421a0600e86c0c000c055464259403595560040d0751602e0315655411b81d03000003120112841040030b19442030300c06024101015a000100866894840c1e483c005402064400c1510f4030f0000c00d04192442c00b50031089005005000612340b030365586807618024403441d40a580c81c2d001c1070483c0780d0518049001c032002915014142d002d812880402450505032060910248401c41c070619a581103001d40300790550740c10011062051214401401c0b40000c050340111340f404e070885004920034180d0800e449050b0b90305a1200c20283d8200c03900304031650003800e280400424441890342c059290000e03100152880310802601000440d00c1a1140c82548d10920b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790046807 1250 790045557 790045567
    0x1505010f080a0b0a150e07020a0c0504110702192112020606090f0c09060705010902030f0303090a03080619030f120c02062703010e01091718060a050706060603090b0a11 74
    0x190103a0104081c200c00d030181d6070b80d11b900d036108601040c0c410340d014030143c1c1c080000700c000c20a14140d90350103840d003524203002070030303c4002d1000f56000340e9a000b0320541e94152405c1c0215204000c4e1001441019038000c1000c044440200c00320003140301c00d8910b580c00c00c0344242054000182507000e900701074208801e991b0707141060180b85c0400f410540e03003501c1c00c0140310300555511000d004614012030001925480610404d4580f00362128051146d400074004c0240440021880d009a20f40500b0f04403415a600c0001583c10310342c00c0c40031044000d13010030210901c2815000c0c41d41d82482884c46149260182005440d000880e910081d8404804c00810b140d2601307824513040002c0070025a01010b00d00d140000c3d007914120502e003c101e0703554503e0341c003c1c0140340408024070321250303c8103450980c502da01074001c071500081c124001c1c3e00c001110300ea003511030000c5404860f00100d042000c1900d580c0c0c000d02400ca011b1007501c03c1e500c55804a910103a440c401e50300b0010380161094a01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790048057 1250 790046807 790046821
    0x1c0618051209100513080d080a2306010f090b030403030222080a02040b0409022d010e0307050d03110303011805070203120a11040506070501060905090a03020619091505010f080a0b 79
    0x560100c0c06515171720740d140c50001740d511070810410442d0303400d5071a00c45a528110380d0020841d81c10700028040c05c6080424280030807401e1480d01e402130020701e4040440b46d0003010559800030306910080030300c0300010400c01816450350142440341204108a403c500700c45c2074911510310240140d042641100b1075000040c60603038850f10420304068004074040e10103400260a00191150f80c2c4105000303161034100e0148000202c3d50052030900b8181a00c518a8011903501c602c0d82c040e041c05442203005c0700c1c00341801105048d840c0721551040301c0c5d0300d40e1145851303403d2002c001c1c80e28544c1c504107408607048d50f001005646e4105501c1c1409a81a9285a800d50180010503115000c0352400c22001c602503c0d10002060041d015100100c1c40c5d5252100100441d840145005110b40000e44070100081c0e021460301c2c0c000c0114828012807545d0021040000e00007880014050f10400c1074102c01002242c01c66412036000e140407440d00c1d540c40e082c41740c80303180c262070087c03468450700f0010f084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790049307 1250 790048057 790048067
    0xd0201050726070e0910051f1e03180302030c0c060f03160504050a0902041811070f0501180605060f1212030a0204030b0f01030b100f051c061805120910 67
    0xc48142484d06402d49101d10740031034504001a00c4401d59105003000074041c0b405c09a28400d03903019420790040039072182c0c170700040c0000300300814103407014002491100724605c280c2064070001c18010b0008025043d13850701030754075031086200500c0d50060f080340e00c50346d213015002e0310905840840354500c1c541d0703110404107030305451030142001c0c401c09201c0401c1c02d896980106002c3c0c00740a000583d80c4d0300303000200d181c10f00100714500a4605141404212861903400e890049901001c1c50b02039a24030b1074000d026041541641185840c806095000c1c0b241680003a8059041507074205407402860041c0062900f034154001010703403001c1c4c8050481d03107201d002960700101906c0b00604113500c80c0e861643c3c901c0103a9101030101d00d5080144103110103846203c0d00854081e1400000602d081c80c4d8001010180c825544140142c08510000038010384000440c140c2c081e00801030141681341c0d80380c03092400e5005803501d20445d6650b200c40c0040c0340c02c81c0d00d4000028051910600603a204440f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790050557 1250 790049307 790049311
    0xe04021f02120309030c0c030109020f130209190303200c0f19031b140306070f030905060708090f061b0714030301150f021903030f020405030f0d0201050726 69
    0x4114811900301c0e01203510a503000d1400390f00b0484c081c41e030320240000d06a00d0300c21184803140c4a41d00d002850301c0103070f0710311086c10400601540c614102c0d1aa081d00c100090040c0d032981d82c2c0041840b450b001c48003e1030049042500e100c1d0b20b039003c0703c48886070b0080d55405890006103071648103180510092900345641c040549005251400c001c9066180e88442480c50748100c4100c020035808900500007022104003804480b049044d941140d80000307543d07003001800607801c1c0300d15025501101c6202c0e8118a9583e50480200e41090070007440c012701c041804c440e004054007481ca1003003d0b000001c00d400c0c2c0564003005420740c202d072140b0341e002e42c6984880d004035200c1c444400300d100b50210610180d402004a048110000c2004640207003068042c4c0324400c5c05c542212060720000d00c0c0d8088203a40094140c64001842d4401404000080c810398000c3c2e80d052082405e45241e03110009103404003c07606178001c0c8100d8a64640c2926840851a0300e00d6034503207003940040b01300240784170b110703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790051807 1250 790050557 790050619
    0x11401260d0237020f0303070812092803031a0303120f1506070b090f06160e01090842190605030d0c0c0f061101060f0501020a0602070f0b1905010e0402 67
    0x123440e084c80d0750780d509a20751080003500880104003080003a901d500b805140000c90b8008803076070310302c0301e0580790f0b001071410740c0320003414035030381d4400d81c105401040100c0c03c80310805411640e40f0301c400c0c18040c940c0c00c030841d03285c0c41d174264280002c1c00d03100050f5440c8402c2400688800d09040f1140e55240304001e0050000e4100e2107840c01c40c40c000c0710100511402882080e04121048042c020000c0500d07040c000098140005448208200800055400c0480041030a0580800658070b500500d5140402100b41d2122082c0015507014000c819840c1c01a076001c5030b20500510030710548010350300644101d5600d60071241d44101c02500801400205511441c0003140346d83d11070045001d81c00c11713900a07000080f01822212070b41082440388501520152005034a640c0c038050000f990740b0f1031150700030800c3c0e0300812828200120800503030002c1ea8007200d4507846e89042d5220480205c403440d566445c0364201400021201a0860914010750300a41040115200105020014140841e42c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790053057 1250 790051807 790051813
    0xb0d0f0e0c1e0d0c060e01020604020a0509150621010906050f330901030f05040b0114060c07092003010f0317070c080618011401260d0237020f03 64
    0x71010700d50b9900300c090f51140c071034816090100d041907401001d12009144207410b43d4804810b201c0960303500c3c1c51040868500f00c88140700d035502d104221684907225801d1540221010070f821011003007003012091380c811500d514042d181c1c2d90301000d03c192000b034810643c004003005002d0780ca0f418000c111100c0013005000b4450130507000041843c1194040041d05400e810120301c10040b581e05005400043c0040c80e0300b40024203007a100c2a0800700e040c42a4032002600c0e01644140d5181c034401e6600e00d84040b415070301203658552003140034025590419809158400080201716102400e40341640c05410008041c942559070b60030403081d1a00800718860024010040001d0442e14410702074074005006d4041801d0001c0e058030120400e10540d01240d0401d07001401c50030070411564110b0300b11203040d44a580b0340840c40c085c8404c507010003640e50b00031003881e15000c80e00000c0c20780a41140b410540c1070141541000100354507440d0045e010090202c6100015240040c4c07401c410400060503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790054307 1250 790053057 790053109
    0x705240304062d02040614070b010b180402160302070b07031e051204050a060f06030f0807020d0209090c1311030a0e0708070920090607030323010b0d0f0e0c 69
    0x40848460000c1010405144d000107041c044150f0050181d00d401400e040c80c01d042196a46d64a51070074014059510340900100b041c0302d01002c0c2444481c122500a042155507807540d82070122051074001058015104000300040c440c1030304070445101d82c0d01a5282c0308000241c101201000030604070410401106002d8038800c0c0e91094100c6000d00d22801c01024501310700e2828105071703401994058180c628040c0c0c2000030a12807140c000e42d140d071090f03045648088a01c0010040c103c8400c020750451000410401d071428000b070181400c200895a643c0c2050780309a040040d2612100700c1c114205d0f0601c00700385255175036001281440c92a409980000351223850301450035645901510350700d40c0700e41c502d11183d6107280440f80c034004082082c5240005200200e038082c480d0b0f200080c10981d0b100720300d08c1215002e070500e030042e501104155030309503560151f004183d007054400e9061703545410054141c40245200398202c08107240041d10400003c281046140486242030166195100380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790055557 1250 790054307 790054361
    0xf171e090105060f0a05060a0806060d09080d0f15050609030708010f060f080105090a0305130306050a0212070f021207031404060f11120316031d070524030406 70
    0x58524403411000000158074504042003200500125a4980c003500d01400c0a1243c2d45a8800f1500041c0b49801c00549513154100496101c0c450132900d048590329040300d01c070811512030300518460404d52421b0204042c214100000c071400b0582144401c20019010801c41c10014054000e019008050380e0b5105d039a4000642503034400c10034000b909640c0c3d0814052005c1c3d0000200145c00104020446494801c0f490365940c85910f17409400c0c010702181109c2949034011540000d1a8082014412801d011108402940003841c0c0454403060280000e01010b00c510034400540d06030340e0003800881c440080141d4140e028079815010031100348161014561500c000300000d040e00e03610402c900c200c0384402814a1621090300e0780c141c01005240410410090603a41c0002801e611004000c4050400f40e00805076054a1101180048644c010303500c1c012a4030313402c6440945683e440c00c2024a5a1140c54000031805041500b081c07001c2030200e8a2644802c6000012400c45414034030210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790056807 1250 790055557 790055611
    0x609040c09050a0602060108190c090e01020301050f0d0b04080901030207021806190f062118140a05060f04030207030f050a120507020f040b0310020c0610060f17 71
    0x440303914085810000704010074203040c150b0380001c1649101402d000d50621907810707154190600145420210551980c05001550540030003c0c00e41f00e03410400703c81c2301400c0d14042d42003489070a21912803005034010303604100010180440d403000d0041c00a40c3d8981c0c0e52001504141040c07810144e007400300300c0046c0c6404101ca103c0e01e109017400821340c42c0606c104055944c0103070382d285402c806c54400b000044080d074248000d6500354100001c0003401e411860032070360749600755824410300380010f4050800e00180c25088190142e50801e4250075411002540e6a07240b14000380300f90310050000d1109000400c126800500c2803040e80d01c02e82d03480c1c5a028030502d03107030800e440c1900010104810081a4032050100d5100c90810600b041020b800044020f11140b00550099480e42d400711075036641404101417012920208546038041094200da40710300882c2c100aa0030707482c00c000301d01640a0b0384d00c01442e122580d18540304e0401180d40e26000d010190560f9040408484c545040c10146 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790058057 1250 790056807 790056821
    0x2004062f1b03010c09030b0c07060207060501090f0e030310060c0602040503030406080709090902220b12030409050907030206091c0506040609032d032406030603151415060904 77
    0x1161500300003418078200340c00c450401686205102600f481040060a14041d290384107108a20060700c4102908048000c0d108503500206818640000803800c0d55a0340d0150040c000c2184082100003900f441403940d92206513500091042044000c10003280300314013007841d0354800c0c8805801c041ea5040800d155400a401c1f00c0e0100703016404100c0b035070f507000307c0000090800c03040c10f208181c43d40e00071410505501e25130311301441c42d1040c01c040406840e040f000e200c1c040549100c079408d00c604045900d0750860b005a2045604120100da1000700018006054a400404907481c0400c0041007080c2402c0315040c160a041d0036103180c20100304107100640c41940074040c04940b585051400819140c40c3c0804c903035115400100f20b000f090710cc0c0e031002d83c002d00d05040028003851a0340814136420111240019407034849100812801c0e4181c000000301c9110310324003d940c24032070b00c060090b104080c42510418101100258105e50000c3c4211082c00c40541880d1030712100001103000da4180f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790059307 1250 790058057 790058083
    0x3041406190c0209152103210105120c0915010207090c0504050a0b03041a0601090f091d03070519030e2e0203090a03060b01050417012004062f 63
    0x18030740d48107096040040f1015809001058420700104071400000e4103180007626031b01161011459010b40020200215081241504c0702100702552034a54000e895009005150051180190710208908000386803003180c4c000408401c00e5a031246800304140052080590452082c004002210118ad1161352800460303555819a5581401c082c0888074000c0d83c000070446c01c00700200000303e00720340c040111610100c0304002c0309445400c0101c0c0c142c4640c2c1c1007801d000c070390340d08001106851540320741c00070110207494201070400d1089064480c02142c902030803641003c035a044044c0c0c18000c034200814800e0402c0d00c406c5e001c0c28042804100050002120306141503128802c245205d00d0341102d0800d944001c61819503000040f80f815103461000510035902c42c002c40520741c0c0158156000381003583d8180d8035590001c0c8403503010b03004400d050011f0110a0b004003201c10310003403c50f07040e203440b600c411000c0b0107511811100c40c0807506148601c1501700c0342c40e90700c107601440000c0320301d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790060557 1250 790059307 790059317
    0xc0b060a0f150f0516110a0819060e0106081c03150303110c0f01202e0e06040b0103030f020f030c0703060b0901120f0f0605070c110406080304140619 66
    0x902c0310805032003002d643c0306041c00d0281c00d01640b1442440032404004c610380c0107850348492405071380400d10340300154008001c1801224030b241d0081c003020581c0b1000901608040c44466408412a030894015010f4500e040c2c0040305018000e20400103120181e411030305e0001031880c4690035040140381c450f00110002444c60000d00440302d81080031440140c021103004101c0714001f000139140d0626440580c0b0b8400c51514101014401403010080301a9528079902095211000d0303091920009112010143d181424035001e900c00001c66520440e4807100c0918031b40d0850324182e0340c149150b08039104601c612840800305220030b1016000245e0920010100c03203056103001c105490350780c103801e8007610302c4c0c800402c08003109e28100c40c2240c1d00500810745900301400c01e407903421400d44c1e010340745d242041c051007201540440c0c10103030349000d400d084c0c5990580400f0003064402503c21010075520500092100c551004516464103030b0080a8a20700501307201c10b40e252034207442d4004003048d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790061807 1250 790060557 790060589
    0x408120307110115051011030a05210c090d0f2a0801021804090512160b010b0c060417070b0c0a0305070c080d02070311100606021006060c0b060a0f 65
    0x29004841c00202c240c40c5002800381032028800400341c640244581340c4038030008a2021502802080010b5100004800380c0341c2d03420034178101a05680c4006041c02d5071070001d840c000410010044118001e241c103410161a24501c030040041c14000c1c940240c4003c1104100c00e00019124201c0920bd008100b941c0400302130300c10510b01c40c0105990040f21280d00400c00c000b0400f0b40002c0798684a902110f0004543c038060902919014001289840d24000054619041c08c041641d0003034051240c800c41d00b0607a00c804032282c0301d00503803500c105141e0040e0045000103507e4200c05c1848004400d8080c2445016181c0b03412148003a1030204018000249a611055160040540c0000542014104000207a030f54800d0392180d00402400300d94041000c0f001c00d8810400e260b00107422504480d035841e10560f447e0020300c1e07540318140c0941b14400fa04480784c80706000381000c649403030301c80340101805501c032a040c1700e90042200d07501c585c8448001c18000f03550002c0c00041c00170b6444141102d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790063057 1250 790061807 790061821
    0x6032512050610080414070e0103080904050703140a38030c0f031b0a05270f0606070809180915070815060a02070302040204090902041a1c030504081203 67
    0x707410242001d40512205032070700070303104d4100850641180c0d120f1000c1984c103000c0d052260500c600d03030300000522112480000300384594140900402c070300c00c0b54100030f04d4031826401d070111201c59000141a415100000d01c2d800195030103400c0100300d180c0c1d075201d40f502040c1e05448000440c945901c01e034480f140c4030111070408000c8142c210740700383d07100d0325520000c3d400a6502c0448070681c41d150001c10f000d034482da840b1b0802d54070003481c0151820480d42401c09428841165001d20008055001030001e010a200703c40014001c9501810761890f20a1686880c400c0d44e104032800c81c0c0040d014100701070304d00042c0103000d100f40c00040190030801e050918400e0711344009000c00c0100b06c06101444218115020301601c0140c2c200d95050f0382d075400c0042682414a03d0380301a42c0140701090000b41c01c1072075001406140c0c422282007000040e1080c40344140800c9080f5141c10548024048640402240c6140d90b640d01070b046c628103090b90f40281030710b170a11b030403280d4103803140110902c088 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790064307 1250 790063057 790063061
    0x617070504020f1b070f060903050d02341208030103050d0f050405120c12030d0c05040f060309170a1d1c0809040608120301080c010903030206010506032512 69
    0x16100c00c480552900901d0320703001d145030040c11440c90b1880c0840800c0707104101c00b007298500426001110005040c2d558201403c1203400e0322040d62240200075000120701d10114900800c142c1d00c0ca031443c00662094040558950f11403070b80c5000015032203011611040000c244155144a41d4500e0313581d41c1140390050a08420a0203507003400003541c4076022494000c1c095400f0b0380e000340c030b0b001070311032864400624040010391f100d90003082142a803c008040400100180140700c50184850030303072250201d5061045101e000500c940b0a081405203500c01d41220010501405101c000c0c5119003648404a070700002103c0e020880d241d0b01c00c0502c074010120007034882000c440300701021000d821540e843ca45528401040f49000042070740322551198800c1003d0400d007000c88454070210780703250040750300c2030052007118400c42641451561140d03a8520690342d0540c054011a482c1c2001d2210580010b001c00800013400385c0b801c41803901c604050641100f0716501d4034034490347c6028002c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790065557 1250 790064307 790064309
    0x412020c0303040f050f040f152301170705071b05100903050a02040905010e10140901060f06052a010c08090d051e040e090303100e0f01030312090204061707 69
    0x40a500180801c00013242c80c60120401c8441c140d481c08400b00c041701c0004c1c010540c0c9030402c9495442e0401052482c0d225a5281065890042c038030403402640d4108000c01200c0c0081440c0040d0700d00d20055001100e103103402c0c0c0c0204c0b11b82001c6060030400d903900c401500c4013420910420000d06410401c42c40c10f490402d501200d41d041c6207980f507081d5195a51030380b07070b48140a030145071200794000801600758080a021080681500c0004207001940000f401c91140e004404c0d0000c240410203449041c030a0b034044404d550382c9600d0040c5400825261504000c0140040c99114030b0355240710340462899180c8401c0000000813003014464000d4202e0b0006003800503554011186a205540c0100484100070281000300c41613404c01e000300c05240c4a40e400c8441c00c0d8038a03501b444000000000914001c4441f40c1c051003a45890710304d0b40b10f207660115540d0030010181c4c0c0c01040824012801040070350140c900101e80080c498021400345d60b00d40e8465810841c4404820b082078400b480504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790066807 1250 790065557 790065559
    0x290126010e0d170f0408120603070e13060b0933090106030b010305090a02060414040e100501170c01020601050d030302070c0806100617180319180e04020a0b0a170412020c 75
    0xc01070703003840e45031b01c0200c0c01080b180c5100200c80c900446d1442c1d5080041700c1c000c1c0308020603000700e4a8152304800b2404100340c0300b12021b03030034030300e1071101c2d46001c2d0b0703500340708200502c2070558002481c2580e1032080030201b810b0741b04858255000449442d641d070058080c0105481c00300b0001c80d550001001ca640c01000702015800510800c00141c2c0c60304101c0702150102e00c0710b01c0b01c0700781d0600010002c21340b013080600503110b51360101005c00915003220b41201c40c020006c402d60200e120780356403104001f403411401038105500610940c94a0b02020750614000c3c500182050f01c2a52802041e2056070007407000c99200704108804100b80d1858080039044620740403450300100b40e280004c01402a00da544503284c10404c0610402081080d62040180070101c65828044250050300b00c0403041040307000900b80030008503812030540e0b0914042ea40c06000410100d19009102d803203504442445001c00c090001c2c3c0704418000c40e80c5140c0150301030701e45c031520728004101c040d01d0028200c40072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790068057 1250 790066807 790066831
    0xc0218040c06080a060512010c02120c3c01050117010c0509060a0c050a060b01080a05150d02061b03090423011206021303290126010e0d17 61
    0xc0041d5000145000726400b6041c100915219014501c000d070259800664001041080c600b442da08150040b1440d200e5070303000c0e40c0100c502d03a10391840c5d601c584c0032089450ba01002028203c03c204807590406440c0c4000060001881c0d0030f904001c0007100882d1300400c2e07440e540144100302c80d1004841d0381e00212002000703000040c001c0030300b4502800c1c5100e407103448040b0318030400b14090008018144d9100060701d4403c50685460401851501607550002d000c003030000e45500428401c81c1e010f117641d04d0031140800c0601080040c3e4418030308007240c1007581481102c1e94001d60b43c03001507041c02510007642d11044000188421180d0007034242035416071011504034071200d2514290f0544444000b07528000c0c5070350910070041d21501e0591420030141800c00011310440b0304402003107005260104180c0040f0f02440c2d02c01040030b004003050840100300c2e4108106280c000072501c400c007500003080504d819403003c1c1c2400301031a064804506910704140b480c1100001391640711490f4012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790069307 1250 790068057 790068061
    0x1406010e061806150c150a0c080f0a0b03161e140108041a0f04031706010e04200304050109030f090305030f2109010e0706030209180c0d0c0c0218 64
    0x70b1050402040c02007500c1d200040801e8035902d412a00b41e0803402d40075907040c1c0d10503c4410043d520600151a68010388001c8045808080240204d8010f4040343e80c903440652a0050807900300300e8094401440c150340c80d00200c07559201440a00a8400c1c020010010245445100b0030003803081c0b42c1c0240001005401400628040e885000c1100d40a06c3c02c3c07080e81c1c1c4d13113192918141c1d480100380035012150380204040944100c000901c107502c04e5407a9075081c4592034140030003403001d6540e54041065407850300d0036800c05034041c2c580e0503d0381c154081d480c01d524102c3e0403d50b1064a0075107072a51120f0b00c003803e06402060046030890145403509050389152919130712030149454910440b0b038005143d110310075a14141070300c1c02c621440d4606450078016416402405a02c0300e204645c0100d11000030940d00134800d4610144025100700f0107000740348161003003000d0007407031518400c50034802258003859501c00c07210341090702d4868002c9180240100218039120b40702507246400340d041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790070557 1250 790069307 790069309
    0xa080601090b0409021c08310605070b0c0a090e19050f0903120a02040306150e0a06080304051c122601060e010309061b02032203030507080d090209041406010e06 71
    0xf01e082c5050702c428165115200452518a00922030461556001082d805042c1a8000e041d00d801b41e180805d203d00100c1ca43c9c1d1208140e5031401044c274041c0108994a000a82c5541820011b0840d07075032034a4a0122140c44220070311850900b5140040b11040030200c010304440d15201e4250801d1014910100314902031350100d540e07110707084040c001590b001c000300d052003100d60191406998008014003542000a0381c00c004189244540daa442500d60007051040120384036a04c251545a0051440d10b0704280034824107408608050341429200362018010075408410701d04002140d642c2e540250142603c90441030407203121000798a100000108182c1da0081104c140303a94007801c1c0440c02c1109400c1440c02050b16099040d42208425000b00c840c0c1d60101c010130b2210302541481110303201c0515080406a0b850000030082803040150b00d0102e0400c0026210013036030b400c00481c5100300e603804104504001d65003248c1d081d11900b9541d00465043c08068050505295002d55524000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790071807 1250 790070557 790070569
    0x210050106210b040603080a0f030c030e0c010e0d060507020a0c09020306010827030414040e0105040b0f22030e10030510050d05070b03130c081912020c0a080601090b040902 76
    0x800320400ba560741c410055141c440303070480c00040d90480303070f9a03450341c2c05801e01415545000404000181c0341080c1c0d80c106074000e04c07442400742107820003003000c010303998019210358014480b0329601905400c880000119507004961040c3d80e680d028040f04009442c0000f454036141c0c00080060703005204124070ba0b6030000e603c0d80d01c9450103504801c2c3e44005a58829049210704200c0814000020049203212504000d04d14101099504101e01c1d0100d01b001e034202c0b502503800918100005020404011070742400c540c1005a90a240c0d8000700300c001000d0042c0c2da1a40c046002c1200c84100714180c2c580003900c1c40942244d0b003001e021625010b003038800c520320240141c0e031081410f501e5120600c081001100050101c0c10b001c507135030b401c0040c100c00b1140d03800c3d00c0c11110400c4519011455170804900c110f404800108000e01d54500e40c0c2e038076040207074540440c0d03045219013141c2c80141d0f50350107145001060010042c050350b5040c0780c1d061041d2030087d407810f4002c60420941d0b00041e00c0d24 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790073057 1250 790071807 790071857
    0x150e03090904030e0a14010908010b09040f03090e070c0b07030c080624120a0c0c030203030613091a0a050105031912030207080301351b0f030d0210050106 68
    0x454441c4441d503503501e801d03900400038070710b5980c00c050f5450010444c1c1103013003442c25100909803140c1c143c07107603103040c10350030b072801540b016030009510400700b000104090092080f1522a0a0640565456200d811048401194580001000c3c900c01e541801100795045401100900d800d000341004040064054100580028000c8008040480c0c010200c2c4180200e5041c00c40c00703044d40c0b0611b0803040500303104161000c921292030103401e010703224040c071050304101d64913030042d506503981d02040221803a1081085c0c40201d4644001c04009000031000f025400d20241c4500b20506080c1402c404403403050304500d00a0b40080c00114182c400050050402070740045c1030850444000c4088001e4000d02c04014a001d0012001040c010011100310500c407012075a40b042c41000c166174242541c0d01c0c1c000d10070941d00401c805501c107055920880d02001009800f401c1c000981401080c9092444903501006030881d05628044140d14041c0900420302843c1440e40c82d000f981c1608800030b44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790074307 1250 790073057 790073059
    0x4170702094c0b030103030f030b0f06120a05090f070b1c0e0307030201050901090c03020607020307230f0a05060f0310030501021b16180f0b060d09150e0309 69
    0x1079800c0030b524070308814900d4401c0da81d00038062803101c003515580100000b41c03500074890321006010034014035040640b1304981e050703665403c40468940d020780090404001c03142d00101c002000c0d00c8151a07100c01095680d13500302c060311880c9040c1507403400301d410282c10710704950050200400c01c480009020019500340c085c040e0f641e9003000282c5018074001422a1500d18101103488800c200b021001d4a2041d02a400130300c4582e440b401e90b242219081c140040c082c0d07149010500150401030054000d580c80541140d011a84902007105000700303000d251064518400f6140d0483d0402c4041e01481c00e200341c90400486007032000061003405910003200141a01200150010359104044401981c00c64021503a030000c04200030107000484115031251b01c1054480801846c440c110207044811b000a07580003080188940c0021f400486c600074602a111070115031155a940d00500060005c80e0b40020128440c0c07810340044c000244840301d0403454120310748040341001c8122052144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790075557 1250 790074307 790074331
    0x7050615120601151808060702150f0c03070c290108010b03120f070c0b040308040f080f0a11060f0d09260304030305040c0801021306020105010b0406090311041409060417070209 78
    0x706015005d41141c002da403111000e48160410701040a1f0081010714400100c1c0c1220003240c0e459a8040e07846000507100070301003030002c00c000341b0003500c50111104450b115503e074048082c0140800822417101d4900440700310080c100402c98610309128180900c20160050038404090700760301c070454098420194004400002c0c1c80703041001555007003000d400900030341c5403503584a05004107150400c0c040c0c00720311040040045820301c0009104070045c1113403401880031400956501401200702d001c1246c0040c4180011040314025034060032012007a840002468074031803c0103c2100707003076100c001c42c5404038850110119a0703001126405509402c0210b0a0384603031818000c6c828a0327a00040d400d5201041d4407459403060700c812401c03103549034001d00c4140d8075004150750610541c4580303070210308002e1003080010040d507803c1021440040000031880c402d00030098401c081140c2304200e5801c51000c003c104002000e06481c010b00041c1e080381895880e90210380485405812400410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790076807 1250 790075557 790075577
    0x313180b030c060c0f0607020a020f0f031903050409020a031e18110a0914040507050102070f091a0a0608090d05070b0a0207153e0a05030703020705061512060115 71
    0x4000c01c10b0b2170b401d01030001210120719148000a4880030108412803159041c3d1801c1ea0640c500000701d0010080e00030050001c3c1c2d0708080010b1042529494210f081c440144400039060a071480600b40c560390760340340031405d25000b03206442c00c441100400f80d0030915151030040c1038580310545c501070b15844000001241c5030b0a0000d83d9034031090784092610b60404030001c50500103000d030f40340500c1c856000c65003130b55100c1e8010380e1101998000c0c94a801c841820802c4480c42e160451900240036400350801c081410300801c0e0041c00d2504078901040200b400d201e0324480c100606071481030b070307441c0180c2442c54981c1c41e000076030030262503002c040d40c01041c00024014201040341520300b0a8008000c800c5c031120561114042008691404d82800d80c405410045500030a455039030b02c2c1801d403881c0c402c10707050a1303400390400781040003010b5003070150000213601040002e0144d03006c8480004000070184c200303e507072a200440309034545c000900401041c051040f011040c170404d420040000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790078057 1250 790076807 790076827
    0xf07020705121006241e1b0507080303090609060c0714010b0a03050c1002120d0905030d0911091f030b0a02070f080909060a0e1f080313180b030c06 65
    0x1007000d85143e04603c0c40c0540005144901281e41c1e1040003111024080c46130300312170281c41a08603880c0310708131181c00070071034100a40700380d0f0007070304c841268949900090a243c0740c080c9001031340d030000c5916034070010a11654540070044d059110b00240010300c3e4502d40700f62aa04140038400c0020401c5845200b6802040402e41040003006006081c0e42c0d1659900e042c2182d444415420302409a0f01d03016034078003013a10120b01401102480b0781345501c2c056503482c050008000701601521280803d015000c0108000e00940c0101c900542002c90812884400c11800301d00c041c04100d946442c0c4800034403000801d021501c106c0707070412081034290380c1e03040e8410080d00c220080204101d108861503000c00202001408800c00203a9a26180fa83c80070184150390000e8010784600415101c0000d82c50150003010248842810441c58402940da081d0180703160040343c240f90700b04807000c00510600c3c0750500c620441c64a410000c0c4006440c1001194a0300314484085003d585c00064400c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790079307 1250 790078057 790078063
    0x90f070c030302030705161104050a2d061502060106020705090f0a0e010e030a09030c0b0408033412080f010b220f0f090609050601050d0c0e09070e090f0702070512 72
    0x7d60360b2400601080e042c6140c901c060f496080d0a00703201c0c5103840301040b000c41051081500080714000c018400e10206006981c00800500f040d1a043e43c0316140440d18800c003c00800c12400180c0007081c080d41000d8000c0c0c02d2158581129004e070400c0010040c800c141c0460054001003c1040028114000746d074540c00b420502511040781d100c0000c4a4151a604c000b40d00102e80c040d8944c046640c0c1c54200780c2c080d078466807144d034005500c24080c07000a01c0c1a903460b1286600d44900021140c4000c01c001d1554201201007600d84d800016003003800244c01100703140d40301020b0f03e15071044d981440300c05101c90017603080c400c41c0d440142504440040e0701900c032101410852030700000c219a2150f2018005500703001d0000b1103410240002a0700f21a070051170b0040750161520303814801015401402851504c0408c1c0070424600b40c00003a036200d482041c0d00810144e680c00c0a0003c04070184240000094004040703005c00c281000211503010a45a0075107004a42100de21141c4000c00b900d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790080557 1250 790079307 790079317
    0x1200c0a12020a0318030f0b07030f1109030606150a030e070503060906070212040605072a03060e01140103021e06370215010b16061a090f070c030302030705 69
    0xd81551004003500540010f0700030140782c442c1c1e94881c078071908001214100c0341240700090804803002d098070700255142e02240d51103070b040d24000138601207859400741658030307416031945601c100142e1825107007130602c44036a01040640c0d801e81c030044081000c41141c800c0450403000c0680d40c400c90f403c01502800700500401000b000c440d4582494000c0075103510f410369a090140c4100395010000c00b01d0402510100c60b90b58039024102071043d12052000003000e040140c80071026452000440070170300d9440080c0d070003443d0004103004150052400c5411204c401c0d01c109242000400c01651031a00654650b000711281e9820440410b011070907038000d9000110702110390b401d20b00d9003001c1d1002001900810760244140c00292400b0503070f10382c8244c172030300c5000795800c03030051050f200c0403030080c44240381c40c92440c0d41c50112a160001100d0b031000011030b440c00d0408000c181450300040094008034074030744004941c1441070f4003410103c241d000050a0507004000202000c1c020300c240c43e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790081807 1250 790080557 790080563
    0x7031715041d06060a060f030b04180b04020a1712070206190309020906040212240d03030506040e060c03070804030504120b070210020f0703030f0b1009030c0801200c0a 74
    0x201c00d0504000c045148402c034000d1a10540c840c0c030000810500c0c000340d140c000c80d0111b85400e141080352100880103016452400368000ea2130f00d6800c00211202d80343c01c0c980324002d80c44d60388142000d10403c02d100000c4d0740091100f00d500d40c188980a80c010810502105403c99030075600c13000b61000c0b5002d07000c3d804400c0440e440c000b4094903000e805410400029201321054000c649e14407007080100c1c040c1c1d441c0303806180343c41d03c002007030b402030030341007640c0140c481d03565159400c80703c8009088a05000300c00c5000071307103a1080c04a5400c1c240501a074211001d801ba003854900600e88a585020050007401000000400300d01414000c104944c06002080da441480030302904164800240640c0d64000510801d4103200d05680503202b43d402c3d00c090704604038a829101c0e24120081c1c81042880d160b00365032500c42c40819a100180141d1000151300c03050000c5286040101c0c040c2129808003030140d0415001c8142006498041da040c0b1000c407010f25114240818001d1508829000003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790083057 1250 790081807 790081811
    0x16090e0a06020705030c101802101701260703050d050a180605030106020c030c0a050f12010c0e03120705030702061b01050c090406060216290d0b10050703171504 71
    0x3d82c003032080220040041204900031900680584858201241c45051105280101203c000f00040c680b851030f25a1040e4146000200b024010004444854003070b4002d44004c0c403020a1100213008980000d0b88000100001d44076451954880940329900041520f00300302001903e804024000c4030300d121a000c0c0340d034180b20b003152611005840ea038001c0c0a003001500c20143d8649580c580018040d09040000c3c01002d8103625180920941e280c8101801d68404244046441c03801424401c5213400f481e155500c00303545c40000d05042c241030b8203455240d0b034408100101e2010079030000403070395515410b4565694407101501c07403083c0405484101703007036542003009121046090402a081e011811101048166540c0c00c0692ba100c0c89402d10b800400840c4a00f00821a0702c084500510b00d0b500500d1490700e225000486000d030304c018185241c1940d41c411186083c00c1c840b500d03421035a01030034040d1528106407006052104086901d41e250803c050024001e0319040303c2e100c0000e0005402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790084307 1250 790083057 790083067
    0xf14030d0903080103110f031b0102010e03070b070e0a03030509090a02090910240905061803070f0f0e06010c42052206090f080c06090f16090e0a0602 66
    0xa01c43c190a00c4196030301d1aa07401c400015280401c3d00304035a9400a0051854070100200b0b84641081c4040e00c5055568800d013041c0242c00900007000560b11a05a070318152802c1013004e050104c01504140c01400f0094003400020b8220088441c90700d0b0440c0c400041d590b800025901a01c10041c105400c18103a00c28400e5185c0445140c40c1a1303103100403080040300900c1441655880100c0c10707000004e03161030f002c01c000e04010b002000001095071150080c0328040380401c0c6000b210b82e01c400c210303450321042002001c1d50340e00d00d0009071080c2c12030101281010800200440c40340c0c90040c00000d0741510100f1170035052012240c20103c03c502e46a241119620581814405805403030311084c181400207030780300144001d00c052203107110400c000e00e20841d1102002070000d040300301d0f4035460454055003c1386600010b00007682003c0c008102a1034000d41280c241841c18040d034081d90301101940b84681810187c030030554490110004000480c0e11040e441c0101a2070003500e01480010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790085557 1250 790084307 790084313
    0xc07151b02061b0607020c030c01020c01031802060a0903050d08060a0e07110d0203090a290d0e10050a150e01050d0c09020c1c0801180c0509040e0f010b0306040f14030d09 75
    0x794248642019001e859a47c030150003810b0315040b0040314940141c01280d8401810342c01707580400e40318140701c8900b605a041130382c0803811941c00a03d1800c040303424942c0030010840100422400700b0740500d003403071550901c000414100800c82c001c030450696040c2c00602ca06204808220003280b41070100d0b2240c1c44180c502945a51000090038010b192621001c41c07124030f5148900c014400808005003c005084122401c68000c00d80e5482d5854590000d01c039044410402c072240015505400101410204187c2d02105c803565031900075800c12980401c4981c0c02d6200d410f0441d0300541d900b0044019600e405a41e444140d000000c216101240041a8034000204c140042003c40030403084200401410360b0300107002d04c02c07102015692254020094a5904a60a21803030307410154108200c007000141519031401c0030400950040c06449560042400390039a440d5059024140605003074891070604007100e04c02502c0603198a51700c045c06442007040b150f0f1a550150100b214450703500d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790086807 1250 790085557 790085563
    0xf06092d100305090601120c03080a050a090504090f0210031439030402040b061c151403151305100504060f0b130e071206020c07151b02061b 62
    0x4511070258220568034920079019100380d60260708000e00030301c0c45a1821303c100f1500d2194260440303480821040c00000100c8120280c00031410300c0c4c0f2911b0315103001e90b400405c208169806107210754103054040b00803c1d4000034819016406a4103a8000c000c030180030f502400d0450417a8100c00d42081c00c0081c1d1030b0b19902c589120f048880207580011400d0109600000b84000e00102003520030000301c0e00600c6c040d07100900900014000c80e06052003501b00b814401807a582e079001603170b2075801c0c1c00c00c0300300c02d120030001400d24002140303490901040403c2e601d003a552180309144180e83c01056000ca03565038007100da280d00c035084507083d640500c54400509401d80d021614603013010321624001069010f10030728201c0c080c1034032224034404480c80b00a446a07221515240c013881c03401289005038400c410030541c1c0100c0002d84e8403009001401c0c0b40c8019139018102e80c545a1150116442c1e02058054000800604007400b032050703070001545d00e1040004501035003508550754010800c0c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790088057 1250 790086807 790086889
    0x18150f060207150f020d08041502040603090606240503090102040806040326061c0c0b0a1809020921010e0d0906030e06270708030c0f070f050f0609 65
    0x1034403c2d05060740c50840d0640700b1030125041c1a026030408103081c40260303c0b4000d6554410b026082d10102942c44c0944a41264095008076002030340759032120060000e00d0142000800011a00b100c007180010464516140002071207800c0180c000b0101c0d0341917009405403400b070541035080d10700303038103080c07a0144c24220040301c440300340b508040081d021030400c00c008520410707000e0200394215841281301c00a011040703200f01c0340c1e84442a03000c500c000c0c200e000340200e1085511540d654040c4a44c08a900580ca940821041d500411409000d0b40780c8241202038010f40311039103400c0a0118030f65501502e1a16280a403c1c495036080301516a8094201c801715040764400b0009107421520b1140c6443c0121071200080a0142c0300a94440d03040e60008100105082550442500c0c0c8055605587c030041c900801c40c0d000b4150305018070000c0c41940d00800d0050508000300d4074140c00304194040701c100c66071003410080f40d08142a00c5e1030850209800a0151580c1d1203402ca40180c100d110b90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790089307 1250 790088057 790088069
    0x3030c060a150b040b030103060905030714060604060905060307030609170d05180616050d0e1603060501170a03030c031d0706020c1903022b060e011518150f060207 72
    0x121071000441c2c4402c03c2c03c4409032100c8407100c9107941c2c29901d440d4080e1418074400c89003407008021000118806074403100c03141c1e86800107880581010410001614480c1d040429520324000c00e20001e0399001590301c046031303401030011072030b44030700c0c1003554100c2101c41716000314100009500258072103a522140c8228400210521100c040004142c2c1c0c40c1c804a0391010744008035080361400b90302450103050b50311019a40401e054401d0003025082820f4003650900c0381e4035900d81401008000d0140d030b4054282c1c03c2e4813051102500d414140e0703440c01d400d0040c2c14143d03907601c81078031580b00b508450b00e00f440e40e8485860a5444074030440d51042203100d0a4010b0003600860b00003807a004d80241d40592508110400076400c6808116220b600c0c4025088010044801c1455503006007050000241c00740c2c00000380c1403184414182940c0059255002480100038244246640059034030319185c0180c0c1c0018000061003410205c10004d9000721007085900840061501d600042d8042500c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790090557 1250 790089307 790089341
    0x121020a08402306070212030408071704051e0a05030a030906080411100f1205011805130501090b01090b030307021e120f0d1b020f01140d021308150c03011403030c060a 74
    0x2660a11001036008c03d8a005240e0182001248041007048003401c100c0f00040310380d9032405980c2c2000803041465039000b0300402e550405501802e00c1c084481000a100130f4018081c558071a40d4000c1c00030580c5e006190078018205c010078103020760300d002c4170703604d10001c0e1014011151192004e0b0030a9102400c41001440ca0045c81c0d070820014040c00341295880a04195070036000c0c1c0d900c0001e8800101380071045200ea10351100400c809000b0f154005024440c181d03869410300c049038050f20701004100e0300a40c0200030100c0161120083c051002c500113a03000820110100024185400d02d41382642034498011580031000e404110454032203140e48680c2c904150144642c4190120f812000e580300800c841d20b503185500a000c040d810803008441e01d450242c402d0300900c12a00400d45804004800280c01d00c41441c0c01c2000c401e580c04107000b048024505400584164030050241946480011f02c006a8580b0708200740e840701840e0340c2c02d0720f0092401d01c008000a220064081e4507041e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790091807 1250 790090557 790090573
    0x304030f0f061d121b01060306020319060e04020f180c0c01150b042d080631020418020628090608060121020a084023060702 55
    0x2480c3c0c079a40102d1560400a04104440b40020103030b1a00f0072a4031080110750101d92500781e15080c0300b050051441a040161030f420503da0504904040c1050803505500c0d041c004d0200c0301c10155401d034810b40c1142c9820180300180046880c03030100000840e0356048030710a02c521421100e014280c5880c041d0001c1061038000f0070031031116040e5126245c1c811600b04814012140ba0040405031000f0140300c08022002c2209048125865540309108503004941032200c03008645106249944408000d45101064030b40c04a41140f84020000d2141e5a90007030a0800301e002c154a4043c16001028541c4401d0240000c0c0c2c0350b0000e03040300207100b544d01d0320f00421444c0541c1c904016035500381d403020301c2e13541d442005554030840c000482c4038042401c49502c03555949400103000d05000c540c2c500200341080d00203010700c03044280b62801040c0101600b038245c02403112012a110481c421112030702ca00c40d0900004141070404030351455070100780c1040c50840d0004040c0c1c0101c6280e402c0b22584 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790093057 1250 790091807 790091831
    0x191802040b0a0b09060a020328021002030609130203010b062a061306020c031c0c02101a010804021503040515070c120302090f040c0c0b0c03010605030f07020304030f0f06 75
    0x2942d21030240703090604051105960750b0410402802c5550014011645004000000403801480c0840c0d90340b0049070441c00022074603410b01c804103841d100c0940c25400c40c10990300007020700c18020001d04d90004009012003d5580c250000c00c0320402c040d0081d03039101445449903a68114942480150403440d0b0000c280c1020f0000d24070b4440c440000c401041e0580d40e94441010394010324207801c8900c0b040c01a040d42c8601340c130743d0b02d014200e0100009011100464064200307240d40e40780214076850460300c3d0640c191050031440d551442441c0c00e2103945c0e0b07240300040301c1013008a0035040c0c444001c001c12041040000703611002100708102030342955540074048a40200c503a43c020044200d50010060982c0603401500d9207040007000b107000d10386a000800d0454400da0498000135018a804106000c469002d864008035100e108501e95810480c014010f0b00c4094142064450401c000601c120b20a0080e600959440942011040c0260400d00d506004600d010b864440c58441000c40c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790094307 1250 790093057 790093069
    0x20901140d0b150c06040b1305060a230408041203140403050d1202070c090504051c0807121a0d0c03050105040803010e06180712020408010e0106060f08011409191802040b 75
    0x14810130103005009070703a516680d424020034050282d08080b0451504080080c1b000e0002c9803144008810002d01103001a00c101c6404caa401010f80f000d0f80241e0034030000c51422411034041e205030291001d07004a042c5012542d0401c6a501000b1034400820040108080855118608051556030300b040201140ca110124031460307500422030301c603d1104001ca5036040e000302d40d02501510544044180851a4000258014000c940083c400c241000304003030300404214034400ca0242c2c2042a110903003017607807280140300f529030f120b49550301c030403002c001e507220740180a141d0150080c0400c1c04d141c544040c15810a00030180c0040d41032000030743c2801c224080c500b41c008010800340590300c401c4030075544110050208844540c00308404501d1020900a0481c0e4008007000003d1952030440001d00c171180288425081094180040140c500c07000c030b4609010034100e588000c26110528200428020010b824150303030700b0516141442202c992000c11864000c0d5414130003a4001e00c01c102c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790095557 1250 790094307 790094317
    0xc0a05010c023a0903050d030506010f050a0c17071703091b182502060f060307030308012d0914060306011508060a090e0a0620030406020901140d0b15 66
    0x200402141e800e443c1c4156038200b807182d0700c121608006a10750b4172a16041d060128210b404c40c046a16a000e0003e0b80d40d0041e41500901c0c0c41d0301d4441d0030405400d0b8002c1c4140c04000c00900b046044030004c200d0761408a0441c1c01e11541304032102007416202e002c0000ea07401c1202c0f03a0005004003034100d40e0207007014000c0728461100502c0307040541081640380511010140c80c1e4169000c6070400b90a003480c9524040360040c029070010055454a002c0406010780700501e13050190b04a0f50b0104006034000d107810f815a81d030f00001c4a028044040300c00040000c0c410070360303a010721041e000903801704541c2c0701c017403114081084440c1c9991003605266407500d00b0700c5102500b21201e0288a21903215480142c0c00c1000141803401c0395035a035013070906940070b0300c0261a1310340060b820401041194494404e190415400110f0f5484046200061b0b03800000c201500b160b4000808100e560b2040d074000780c01070b102c40c44460300d41a1400b078101c001c0079442d140074090034100c22141d2100c4e2003042561 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790096807 1250 790095557 790095613
    0x30e0c0a0e01030b01140a1721040e1311120c0402040f090b040c0206011a12041a130c05100c060606090612020f0a05090a1a210403020d080c0c0a05010c02 68
    0x18641e1450310002350141c900901010281f4052035240299040f03188804829520b20300b4441500e0f07a08081d00c031055008040d0544090482c041c80c606c0c002440049001c00d07450701107541c08441c5001c1c0702182d0801c80c100304020303405071000401291603c0744221800a036030101000300407011840c004d0100307d0382025006005a8841c3c801040302214909a0806c0750022084190514401070350110800e28207940c00c075089404280641400500c61300513640c0b110a8203a4480c00b07400c41d84804116060034014640100412800b10600328021215441490b5100800300500d82c0d071450020080401c1d406008009603071104001d042c80c24a0003034901c410600b80d4258900459401e00b91070701c1c0d010014640d0020019800003400f00c4040d8201508050364066103980c5654120035100c0220385007801e8544c018007030f828000401e41c0050700d01c842058a04000d006c40d05c81d980005254040e05045084620440314a9030801a06402071a203844054003220407850b2000841121401c2d003100003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790098057 1250 790096807 790096819
    0x20708040e280c0203090301140610091d06010c050f060709060f1202070609080307030504030e040207110d08130b1b0d2307151a030c010f030e0c0a0e01030b0114 71
    0x102c140c480855009080a18640c0116440c1c04003000c0801e0940700c45000200c05a071402040142030b041c03d03ca0b00e84030340c440e1301e849130341c5500b081480c0140707040000040307490398400350001d005a406a01100c40b440d42000484401c011344a01c104d80d40c0c002100c02c40001000c4880005402d8054040403032580325a803102901c2c1c0c5040781e040c20007900a03240c255003041d08c0d40c52090100f00404000d41c05820190b50100d080d14290902611410643c540c80b80a90b20402c40740d80800c2d614030000f8180502154621020822414400703c14018503a00004000f02c1e44000620101008024442d00a5181c400200b480f003028106440b10b200c58040710209180791f651503009403400c020007050880c410000c82c1802c08030b4554a08400f0f007241d04041c1d0319914000c0e0024800b400c20441e1344c2c0c1c0b4044000380f89400010340000c1c03840315040d8114040c1516084401c05854040c0000401441b0240105251a580b254403c000d11000e12059400c2180b00c8004900303c449800c09c25072107070026180c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790099307 1250 790098057 790098121
    0xd061e14180405061e0601170615030c0c0c0d0206090405100b0d0f0b062107090f060503060f0d171c020a02060403080a06030203030717190e2803061d01020708040e 72
    0x41500f0f2064020200ad9006481a0001a80d9908600a10b01801080c0c1104c0d1321044901034141c540840d000c0789520500741480b0703150040e40c1b014121141020261004502d50701c841c6404503445882e50406186020081060740242c1015403055a003030015540920203115864103103c1948201c15400c860b08400022341200308189001607904842d032481d0449145540d004403502c0300d01640c01400001384004140107032807901440c00320580c0012510351850300503a641d0100750342c80010325828814800305080d4881d42c980c5800358032400350120255500ea00481000b512030700c00321001c82c041441040880c11040f2503110b00002d40364082e00a510302a8152a10b01900020141410071004c0c2040303204145c1c002565002c09004107038448100d01c01d150b900f0060345140d010b0405080b004c40300c090110030102c81d0760010499400500001c1c50007a05942c0f00f8003000d070040451001d600000f030401c20089080000c0044030440e03c900c82c0940c41d4180f6a034082010031007105401510020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790100557 1250 790099307 790099337
    0x4200702060702180a1d1b010f030e0102030907091103101a220509071119060e07030312140403050a030b040615050d061e14180405061e0601 62
    0x60000500007131002e50810b0340d20000400c60001244e040b644540c550105c1c520f0205001c0510000303800c100080e2130301080940f1a46100c0400c22203d5040181500c20070301018001d6019008901010000f50f44c1c91070000c49481e9104124856100d095141c0410084020664001d40740074140c52420b12102c146042070030092580c420040d8001034004109503440a207000c0d0781401c4907115164071180c202c0c58002000710740c100040c018410302182c2840000d0710306002c50f00c0440c1541e01c1303c4410200c800c03800c0500060498000408480c4240c44000c82410780040200c0c1074100030304002d02980c521880394403101d50b020749009020800074080321248034001d4026440d038010107800052165030340d40c50318003207400341425807003c59000215903010345401c0c0503840188c60b0408081d8a608030740180032245044501c1604d590807020788144500355039664401d003c5c40705c0f5845401d9541000d00740075458040980b0140c490009488444180030205460790303205030016161029544c1860b8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 790101807 1250 790100557 790100569
    0xf070e130c03020409050a090209070504150c05100203010e0912091005070f051f050f01050306270a0606061704030e040c090320010f140a120b0312030604200702 71
    0x1150707081c907400748008180780c961441070600c1068110f4002c1181c041c01d00502c41c00c602d018104808004040000307000f81c84c01104a00f540b0301140c03910b0b0041c13113200c0c00d0080c288250f41c0b41d50624a400000002108009540c2c1c181c0200c0508003074580d505c01c900400c8030280702d94150190042e17843c0850b0166980075202030a0a203014040700c000c0d16680b961007504005d11a980c180b00725000c0304070407031178405511403079500005035142100e45504240001341e580e0f80040084059042e038402d007200a5400020342c1440d040340c902282d82520440c80d103a4041c01c03080c040e900c001801700e0651841440b5444c81c0c9405184c058950007202400c1c08203200141552080c007909200344060004001806070002d041c1914a0f4624642e03455a03210004003100030104c0d0450811544265003d60682c5002c03c0300c3c0710080138204420100c04841c1040c0141600003c5a07903d4003c441c4900d2501980c0e2000354494841200c0c208145503400340e00e01303a552480129542c1c10350702402501e0041c1008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 790103057 1250 790101807 790101821
    0x30c0b0a09120203190501020a112109060d050c031803030f01140a030f080c060c030103110415050904030807020606100e0d0f0b1303030c030b06030403210207050102030f070e13 78
    0x5420b0b0717900d50075000300034004000c0340201160036a500040d00f003000ca0344100840540d20140000d8928140d62a07072400000001120350311480c0d400094100d4541e881d10202c61606060040c2800945005004d07074000381c004907002c03003c7c40b44c81c42c010502418080100d0388608180c844c00340c3c041e400c10b0340c01e0300c0c800f0b1505e5444c0d4020100340300202c0440d21880002c22024450002655181c1a880c4080d0038103070007501c00c005948081c001440014100254812007800585000540c00d440415070a41c00b10b0360351189400503a00070a0000340b55200541c1c03441003140780c0859080307854074070a0105002c010748016000035103294419000c1c0c5410316120031114001d540d51000d184054031414445541900c00000000f10400010100351305800341400404c018201000803480c514040ac400303100092008003040a40e10b802140061003401c0c0c1c10460300403442c00c544420082c507005d4001e500a403000841340b140035000448591144017940c003d448060800d1002080703042c0048090700e09 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 790104307 1250 790103057 790103059
    0xc01080c27030120180405070f05090d0b16020105150f19080102160506070203040b0f070203010915020d0e0c1809012301030201030b04051501050901020102070f0c030c0b0a091202 79
    0xc6001c040030700141c03444008490a401042155505c100d03410703103c82500b0722000c003806217081804000040e6048019a05580c0050800d5682c0d120020005407030f107a0480f030000e092440c110203001d4584900d030074502031424035230001c1001d515005030800c1c4810fa0110105c1c0d04c900c00d110480300c1814201002010f04900402c290380c0103844401d5107081e40c2045291103d00284400d2a50501070104207554004090703001642c601401c12804101d00d105900e1200781c5034800040000443d00c00354400f81c1c01a420a58000c416010f0381c2d5071202a5200c1d1860340410350802d50040b02e0304101050f1241c1c02d8100030041403942e004080743d59186c0c2d6000380118404d5580d03162014000701249410400b0074091b00c448141503056200142c01c84065001d40c40c095490141000740f51894149105c1118009080054440e00d036480100d029114040c001044030340d00d080c03280c041045c1c2003121004c1d43d116480c242c180a440d40880301c000e000d60f4070707800e0004000540410841c10803842c1d805036140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 790105557 1250 790104307 790104311
    0xb0a111c020d061512060b03060d020d0f140106050103020c06040303051b2d0c070314010914030901020705060c07120f120e0102100b03120a09030210020c01080c270301 74
    0xb030402038a82250600c4d44204190098135402002c4160b001c45102c540c07050750b880803c40e03241000000f0500b030000070074003802040f0003128401959a20202d1510541c0c2c0040044086540c500e170440c420380c0c0d442c2e1103801d150b0900c00301081a6010f40251041d002c6480020600340da55a18220f02400c805030030f000c01c188a00e05103189961440c00100080702555400100410015a07041d81c00541c16420342d105090034840c0c4990445d004c030382101140c0d00001c8002c42800c03040c20440c010306e02900300920207803841441d1402c03000c020001c0c00c10003000342c0982d0710456569046c0100c81c41000407440d42500011720070720000301d684921000d04d90182d900c108022045a07280364a140300c059a00d008140c800700340802540c3d0400c558a030351a01100203100164070f400110395200503e60303501102c50b0003c5100c0c0d441510480807000215002082e20034240410307034002c0e4444100500d520f00080100002460a64018080ba620f4441150350305440114605400c168441814440c90b8155 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 790106807 1250 790105557 790105567
    0x9020d061a0a0306050f13030c03030c1b030905121612031412100803131a0c0a0c08060a0207080f0a0e1914040903091e0513090b0a111c02 61
    0x2440d42030700c0b0805944204000102c03420401c1d01200000802051306100d80d041e86450740000e54000008044168181008100010014001d9601d400414003c00383d444194401d4024580e214075800e04954050714141c3c1300c3c3c0c01d000d40c682d4980d05074011a00984502c000104140e54005000340ca10500925110020302800b4040c5101944860060f80313440110b001407001c0c90301b0300444e100082181c400207600d400c1000b4001500a111440780c1541c48000d404c0d800a030410040031905035400e0310068515000040c43c1603041541e06026069a0b40b24036400a105d4454074401c9801035600305041c1801c02c61104040f052540c0171290700784c2003241300d404100d0700c0d4130ba0845c480900040d45103070110145c14034882482c0480710004c414801d034200800100400e8001100c081036a20302403659404502c4201d40c00c10901c201c1d4011600700c0743e296018192600e880d40300d003d0720351042c02400025101d00c41c05009a400c5042c004420b003208122540c01d02621480301595051103000c050300744 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 790107913 1106 790106807 790106809
    0x1306110606010f0806010e0307050306040605040309150903020d050a0209090d121404060c173c06061c0501080d0201050f0708150a320409020d061a 65
    0x110a03182079181013520f060142102030580a800c8075268200ed01e41207004004c1120250002140004041031900e1000b0005404130000d640b002c10850550f000c02910380c0752000210341c0c43c8a0b032861000103884141402c0d01c50780024000d840701040c20301c8080c10561891804d620340c81d2520a98109140080442c69080340d04842d000404140032030b020f0f100d894206051140c0d80f0045410041c11403c042c48600001d4200841d40e400301a1350740002c0d01c0d54207039090300300410b40b002000440d10304003031001c1c001382e03540d200100302c201c410020b00c0012110203802800725600a008000b61241d02402610b801000105424141c3e20705040000c07d09440900507003003641d442c9070158415601c0304c00e030a020304002011820704003070088400c0400503c01c59480b05050b12440c0344662481c03c2e01c941c41744c02d5000f8285584440c00760395900010b00d08401180c0c080780c3c07035920039485 = true := by decide +kernel

theorem cover : BRFrame.Cov 789928057 790107913 := by
  have h0 := BRFrame.cov_init 789928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789928057 ≤ n) (h2 : n < 790107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
