-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:47:21.017102+00:00
-- url     : https://prove2.me/submissions/923b8da8-f5a1-456e-aa42-288ca1435b93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919424460 ≤ n < 919604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919425710 1250 919424460 919424477
    0x120a0c0801050111160e04061514041109040c0c0b01050604030302151b0a090608180a11210601180c0516030519050d2007080d0b0a1203020606030d 65
    0x400440f0401c0d40342070216078502c0741c5d51a030210050302e402d440f4040c0c40f600c1d40113116440d00d41043d0081d02c9034200030611443d507684041014110300d40c92002c1005040f0742c00b0402200f00c0551035614082d191105901c9441c040b210030410b600300c91800c00f11482820b00003d03a03030b41c03441040002d001c0c521010300942c02014001d1102a48100740320741c401c100800b504848083ca14840c3d115400602c006008a10300c244140540343d00411100d5200c0f84c4c1d41c0300c405410509031280d54440c0074504000301508c01a00a400103903442031080e80380c46818918414000c48044009a82c400c428440d555101c010310106030741c5203051b80250070300404541c844500d444403d113207000702030700203d5080e001c200c02030040b450108050107031841c2c1c84a0a9071080e884002c0b0b046031404840c1d4061043c031aa03910780311006c03610500c40d0b0030303964070759002050941c5450709032207800f01801441141d80c1e03000f5030100000c11240c42103006640818000d03070869042c1d5880e5803d0581e0380e1080301201c0007080b90741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919426960 1250 919425710 919425719
    0x905041802060310091b020106081c050706240501030e0a08030c25080c1605280f060c03020d05070f1514010603201c020309030c0a0503120a0c0801 65
    0x400081d80c0007180d44c81c03100b8090380d43e00c80701c4086607001085091b950b1150054820040c2c0e090207424081d106401c041e00141c943d490031182490340c00703941c4000384100807403d10140240b6900101c1e000301021021000c25545600202e4043c6560180c107020901d024022100903500180b058038032075200139520b1840d01c4210385c54415400c50041e00b0b49827640380c1d0441030f60880f5418081c110742d102d0b0076644d80f1000d04074200f5082c42c1c205490f1000d400e080d450100100e684810b0f50b66161512007107003000d501900c941945940803590801c03040511010000516694050700c100c4070341e8025400e944507031101c51011141c5108002c405081048810400c40100d00e40b00c1000c401c2d811402000544100c0340c110312416030500740c0c08140400c1e540c8502c541d01e981c140782498500c0d40251403041c6440d0301d800700d0190f01041855450341007503000c400150406000c0003151031ba1904001111040500d902d031107542da81c01414560b58200c3c0d1a40441c0d0158194010b10705880380507140c02046070b081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919428210 1250 919426960 919426969
    0xf03041a28030504020a09021c0b210703060b01020a081e0409050f0406050601170f04080f040b03060406061d010c150e0304030b0708130f050307061802010905041802 73
    0x20040010394180c14108a01c01140c1000e00740d40d07070649480210b118035060040100368602c1c1d0b0f01102c03650703004020711005048103002d070901c44c0c41c600e80d00040c4110b0304c074003040660182c00c010040100c1c2c0302205851f4080001800d0084070700c603030700a200c87c0c0e50403001262108000c0000501301c20042c060380055094440035950001001c114071800c0550b5540140199101a140d02888902000601061002900030700e98810020309002020420701c41c12050381020007002d90801c0c5040e800420104202c1d84222a809943c0c03040407900e4680320303c860b4119910641300035120354075110700015114001c2000107054a1300d02c1c801041840c04500544411240244c1103443c02e80f000071724030030510f11b8828908502d0507400150f448a04616218480000c041c100c1c0e002d10402004001e50341300300c05009000194442c540d0b11124501e8031b0213900c0c41c00bc080c4003e00755803c0c08944035032550900425014603000f60707503030004280d440c414441202d889200c1c80c3c4c00c500c64101c41d100176050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919429460 1250 919428210 919428217
    0xb07110a0506041a30160c08090a090905100b0a0302181315290607021002010e0a0f3e030a02031531030c081b0d020f03041a 55
    0x154600e1913140c800000040c0301000d0a1403a84110302e805e2074200403030001c0300000282c0c000f010703448012005041000281c8200083c0700d00600c00c0500260840d0340d91070308489480280103d82060021401034540301e5155074010201e542140e16004440700d0360f00e0141d08a1088a80260041c517400082c40200c0300342c6000142094058007003000340f0400203219415103a841e01c1c0009000400000e48100780007a0410b103001340e80311380c600031064400c9589603800c45151035811a80b001c4c45840313213103081c4d014200301d20940c070b514081c004440341400907891200423207900c1001e20000b05040c1c8101c450142441001d00d000d1a000f0b4010094207000030003010754442001030440d1340d030801035400a03142850041030198100c12490500546444071524800300c211001c1c00c5510302803060550502540d4003010103030030400c460205d041031018076800c850400b110303105000c0c84003001e000403d960b9911075030020300500c1160400d40c8a001c021080d82c003544d50748260b4001058910151203920b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919430710 1250 919429460 919429499
    0xe030118080301090e070510050313080313020103060914072601090626100f0603020414070212072604170708010615020d030905010b0a0b07110a050604 67
    0x19694411441111018101a58014800c240751580e96040180800555100807002e9043d503120280a11180d5113001007200c4c5d2410038540141c481e0364500e40e607603003290040b8015020400000a01c492403445000240d1218001c2e2418400c0d01e644804100c11118882c01040420411034041005107205880340710541c0c810100031036007481c420161020b003d00030f034000500107035075010800c1101c0700180c050600410480307412140c54010355945445807121491544419a0740c0380300486594a0791144000d9900038000708040c81780c0740c0842c4003501042d039041c03026100e001041205020782000b281c03c41544090f00010350341d03039083d8000e482c2c90380b03404540140c0c10510000c02d801742805c1c1e4060000d0420402843c581d41707054111030031a4804d0304400d08140070300c0c0c080d0408a030001000080748039585400a075021a60405600401d140040e16a01640d142c80003e40400f0348805460f140f4021a00340580e14030300b904219404100748641e54000e013061000b0842d24561884014558 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919431960 1250 919430710 919430713
    0x709120219080d0201140702060106090b13030f030201050f01050613090203040f02060a0903140312070503070e100f140c21070f08070615210f0804091e1b0e03 70
    0x42d448070355a500741110b42c024080180c0d0368031000311800f0011100d8a800046a0020745419410b0620080011004e40142c02c0d00c0e903c00106101203c1d18904540020f5400c0614903011100a00d0001e0103000e0546400c5c001c0d440f944004101c516000c03003100d4141820b8205400c1075442c00d841c0308085d400050043d02c8400c4e80425100c056100c050003401092195034915841c581145890307000c1c03800c0f2041e180c9403540103110390558401c0401182c0d0b00030489041140c0c407659005000c5504002100d901c0da0056410051070f41126000740c0468045805500c2d2003003000300c0002c0180307141c0141072900c01c80d070380544280b080c10065401030098007104406150b00c0c040316603e400c581049410001c9a08010004070241807100c070348030712030b00c0c0001d0480d030034503491034104013150000002107980c00040304410300320100803801c1236007080c40e075000c20007075107590307698001c41d0040046101c84d550440c4405100100c140c5c1910403801c0388600070b0340c03644000c0e580810403030b85101c9440a06406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919433210 1250 919431960 919432009
    0xf0f040e01140115021b090703051807090515040e1011070c030c05011b0b01030b0603070e09030901031506020d391b080309060f040b030106020703060507091202 71
    0xb0a401024041e0688240c0c010542c14200360092a107203840c0e008031003c00d80052004501d82d02c1c2c0440c1600001c1c6450701140c0c03600c4502242c0307098580c00c0020449889000d000007211103144c0c000e20700c41c41c251601c10311510751100a11084d0361041d6040c814641200c0c4440700208a10391020801080102a00f4204070040d82c42704a00301a6400c155202e0840090812076580d00247c3d000c0c8400101e5a10041000709a03900c418504041c0002002881e40038000f8111b0f4804000c400014840713000111760a003407444409849521210700140028148101e40c401901368803030400031a142540100200c0120703040465024580d020040e00204034514980e81c064a2045078944d01c101480c105800b07405903250202c01c4451058075251286c406220801015070044242d50204605075640e607a140310442c0e0715000d03031290381c00418140342e0101c00402c0c2d203640000c0e03a00541c4c0c42400304002a80b21036200fa80e44024902c0703480351011040000f80c005003008805910b8410501c1140e0b800c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919434460 1250 919433210 919433231
    0xc040b0d3633050901050a09080703110f010c080f0a020c060703091e1b0e07020307080c0a0c0e012c06100c05010c03090605010f050f10021204090204060e0f0f040e01 73
    0x442e0664800900007680c0ca520502005030001c3c890141c22401d4100204604141591307250b410780207015001e014040c0d841140311080c482803248603409100440200416400507901504111040d5842e42c600710f410342c005110f4000a1080b511400491001401349680d003410442c05000300120480c3e0203448038001c0807c41c0d20f008101c00d4403620425a8641d5045203880c0040c01d450a50701c4004410341e61410300ca4890380201c12101a641c010700040d50700e512030f410320740c81c2c0003400300028404541e4102c0040c03202d850788015412380303503600000c0854019055070161142c1c56a10301c00401c0402d000421054035006903400c0c3e404203503086c03d4406012944466003150026401000802e403121950410000c4510900d4050409500301c11035131070918003c5104c4c0d00c0b10601031f500403042c040c950003056008000c3d007040304a803e0712503940d0b141c43d0002000a134216108090110f0400d80b0392101e646000801c4180d25400a40700300842980c5004110160003841400300300c6542e81c41880d030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919435710 1250 919434460 919434533
    0x6040b28051e130b130309030507090203091c02070e07020a12050a0f030501030503180604150e1305070816090f080c01090b0a0806090c040b0d36 64
    0x510881440745200d64a80c0060900c6502c404001c003c1c2c4000f5000724002c10000700111800c5401c04002c2d1408100700c0210700d01503c050103d604080c11511234080001803511103a00118400e0a0840540d0940d007a659a210342104152211303402580202506008000c1000c0314640e22607907902c112131503d0b00b00d8903144804c20140c5489000110700082c10603d5a804c81900401d2442a250030002ca40c91038580c1c680f01d01550034100341000a51051052994a980544024102504000c0f10000d0050000381c541541080101c1c01481440300d400c2840406100d40741c414405520740030714a5603694080a60f2141385103030041401f140000c0464081c1040641d0f00140030a00c1c01401c1100010b400900312120310b43c800380103901c0070017900f020540d02072480e90b0400c4080e15051415203500e9124212030150b500042c0000c800410075140c042a15008013101050103210791080143c0515103010700c214440c20303240401400b4190800254a00000914042c61741c80080403013000f010008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919436960 1250 919435710 919435721
    0x904060f0e1507020d0210020c0102070b010602032d120603031912050f091009021c060b10090b0f07022106040b060303160809041103180c0306040b28 66
    0x1884542d010b600da0a26018a140e60580c020840d800185944c0200360002076540b04140c21002200e6004100400c0301e03403003501901d0009030300c081c02c1c07086c0c0e40e1a0b10009649810600840ca400984688695040f4104842040044c410a5001480d00c000c50350903020220740507107070700d4052008000518491844003001444003050341d541e155002150040300c8280c4101904085809541c0700030b102400400082c0d94010098505002c20780c1074250001507000384070a09490b014500880300981045140c0c2e0000741c000f042240d4548148040005c125161140c0d40101000c890782000071403842d501c803001030269107100070114105410b80150070540f0618032044400c9652050302800104201028100d60054040d80290304001011010314104009020f0103480450001401c00300d50702d880d048158041c3c0404200c070f54070f0030140740198120440c00000b008030300544000413194600800c80c0d502a6030010301c071418588864281a805201800c010410703004440b84110b01720b11305c0d011300e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919438210 1250 919436960 919436981
    0x1101200a0303050603030310120f060216060f051005120f0f010c020f01201b07150221040e060a081506090105060703021b0a1208180109080a020904060f 67
    0x15101140c0c0914016090700c101402141c0700b900244100329a026004000000300c4070b071f003420100742c4c00d540d0030b00900c05180c220001c1d04407400040c00b40c91182c0b41090309900d0074440c1c0700030032030096803c850500302c54040e10910100c0000590401a61401e1480920f0400c040416034031350303019904000e460302d441c2d0800c5601c40c0c0d448441080103075406020460303403c440c0100a11007080c25400c40e08501c146202007408001010407810111001c840c1201640b000321012a00e6268407a1101c1060711003848200005218101110b000e010808007140a20480028170704d0401d41040c6144021810062000707400c8480014002007034a810002101039002e00c501c401024181001840034130f07241604140d0140f50100201d80000364001062100b0280181c42440c02070b0a0400050440407554000103820010920768020b00511000503d8041e0b90519407401c1c000e0007a0056030b0760325840c8904441c6801286040b00903080c00c61600c0d5100e8400c20000901030b81901c45039044a102ca0030703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919439460 1250 919438210 919438213
    0x20f0403110f0a060203030402011d0405091507090b0d0f0222080106173d020c01060801090c0308090a03080d0c02010e062e080a05061506040501050304110120 70
    0x20007042424158810814844195407103511542000700180d40c921020784000d0401c9068014265641d070004000101481e00400521550502004540d516000c0c1c42a2080360590720000c1401e45004010340340445405142c001d0030103c0c4620740100401420071640500c5808019146509407802c0c00c2e915442020300720388070b0080c1840001c9013140c060782c00455011550742c2c540601e03104006036100b5180e40304031906001d20310800b042c28030807074601c2e036480d10803198440988039881c20350060074840c2060402000134968400255081e02c2007a0006801a00c032144140301092043d0020002c0309001f034808144980d03a0b030b4030307100258010241d0400c10b69803243e001074070315428020600e0452442e03006003143d0414000b4010b910100c0751040700c204098401c024012802400700c840100848825100c40380541c2c1000b03511a03008449003201c1542ca00c0e0303454141d1030554281d8050741d006a550380d0a50341c495072990070f6031166000f0107040c0440321030000d0755540c03681176545090300c0040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919440710 1250 919439460 919439483
    0xe10140c0f251a040302060c0c0603270d0c0f060b06211f0b090103090f06090203070e0103051b0111010614030d0302031605030c0706050a1505011706060c01020f0403 73
    0x4052104001e2990803c90291540105022011420f14181e505070390701210219900c00c15902010300c2c01c0c624502c5590401008020088409811032041d03510004003422042500d2504500e40d48030b0a50704401d001142c0341d1031803100882e0320030f04102c4e0554401c4c2000100c420185002030b110342c11400303020038160207251800b2032482d4420550b607040ba410110060442402c55001490000c950040b40c0412001107480411a0b200707801c00c140d12900508440030865480c2090307801b411000105034002d00c079800b00041c42140307000d0b005040703c0e000340103440c00200c40c2211444c003120b40e0840383d040100031184446010800c0c403501c801024991440541110880705041c10014044200d605140c814010800c1081c151918407102e0780c41403505594994070209010441e00466801a0a407483c000401a07001c1ca02d03800340b10752031a410f998000c86035964004449201e64080f4043c1241e4101001c00c41c581043c0010304070100d6000c00245c10f00d0700d01c481c148030942095006032040158139 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919441960 1250 919440710 919440763
    0xf0a0c0507141e0d12030b040504110a05010f0806060a1e08040c060203090f0f24120a0504110409150e0c1302040b070b041b14010e10140c0f 62
    0xf036040401d900c0041e1400c1500380e02000041c60103264810103400e008003c0d404c15401840b80c0d000b00101c1038010801c1126003000d0403c041d00b203443c4e10340e19000300b9030390703a0101d025801008101e00e880000d60311440c4c140c1d00c0c03200340036681d08a049038a05100c2c806495004040f0b882c206038003050300b6942ca805131460241404215045103912503805e5400c00c1081200c075890300001d10a0040c0f00b60742081d03500003201c0100709030050589040900c050902c6400318200001070050030311004e010240c08640e00c034100d802044076000da60007801000014135034812400e15401c17542c6050f000d581e400d002c41c3d80c410101002c3eaa440180d10085030003458140090785000940303203840450f42c500850409017008545142440358000280417900b10704001020024840302841403803465951101d0695a142005a40105003280c810301254400380e42d0042401c0c480100021200a40d580301404461000c100340d02d03900c02e07a0038540c1401205412006c81c0700030410004075030f600d4150001c620845 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919443210 1250 919441960 919441969
    0x40f030306241808030a09030327120c03170d0510060c0b0907030203030a0302091305061e0d081614030c0303010911090a060801060e0607080f0a0c050714 68
    0x10342005140e000203025088503440c0403000999403200b24104800041c40c020002122804154049203d500c00014100c0956901ca060501103a12a40741c100407151158180100c080d28100368aa20b140c800c40104010003011513141d00f824003411000914984a49032144c1284282e02c0c580c110325000130b010890010315121b80c0d0b030300c5400803030340c0319403282805402802c4040c1e2900103400c80d0007207000303c0c0f800402800400003c41c2e0040032030b55030310356001000d0301a41099a489104080040d14040c80d100701d801006c0c411000184034074686480805803402640d031074541f41d82c010805580920000c0c821070002c00300526408540c070300065003451b1040c200a005500c2c80c680360014090b4030900040042078905581c3c05982c0442c0c0880d9500d080c0b8914000c04001c198812024903000a2044d000306901e81624525507034003c9001b1242c0610803103108900b4001c10f40d6008111304501003401001902c24102540740080007248140c481030b2400240d60451007128042c04c0d5a1551442e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919444460 1250 919443210 919443221
    0x15060905030f0604120c05070f0f0e070c0c0e0a060f0e06031c0f0822030e19030c05040f0207150e19120c0c082e1103010b0c15040f0303 60
    0x42c60310042900f803600743d4481c003451500d8006481031142000c403c4041100038455100988040c0080303900b9143c0d00d80c4226050440c80c032680c1c03132140b040740c0491015031150340d20f20b400340d0b00941e001a04e285441101c16000380024003c034004d80e9500c8010883d940b07246a5500101802c04a0440d1410400101410120349015410582d203644a8128a440d040100710380c0f5040142442c00086d40e4402c074091000f4401581c444d07801e14455440400c06030440c4800c10107201c10b48102010410140300b100d120003076408060a5429000e504000a01e0103801c22000f4007002000541020500d540b68680281445038100315640c42c0c5000303201c0010208880c00030801280d4058040c2a4140c0f180c603154040e4100d0034040200d040c0030724003131100c0740e96600000c240c01c01c1115800e02e02d5407083c0342e228203641801030078003164440c04828145917014084084a84080b118a540d20303100c02000b00740e00008418409014200ca8621124843c1003507600c2171740a241e240344103103030314031300201240c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919445710 1250 919444460 919444483
    0x70501050403210302070605090f15071d06090406030b150105181309140a0c0b03010605190e04020703050307230f070f02031c120e100f1506090503 65
    0x502800708002160011031014258811803032504803450031100101c0c041d20640700007800c198280f03414070141580018030000714441c183c0682d59064440c02c4500c0c0080e1003601d092000555034222a0b64240b841030755a40080b400600f102d2400e64400701141c103172565644284c941d803030500c0410000900f0511103070700b4171030240782241c580450409404465074542c003006000e00c0440ca003121030782d07105610128840d904090310844a41c0c0000748240c1d81c00141c1400c850700ea80d02e0000080170302c03800c0141c0303040e00c50b40e80700c80d81808003104030700818505101d5101c040014403082840b1688840c401425441c2c0079036034072540ca140000002d004c1080b24503600500120218072002058461400c0e600b800d100101c840350358038900d0400c0c40c004008514065814090b28000d84100340c0e818040c5054007001e5154520178031940080007040761646d0580061540184c001101c008106034402aa890015030001407a040c05426440c5840c000780c00140c0403c10703d03030041c003061400300720102141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919446960 1250 919445710 919445717
    0x405150c040320130905010f230402221a0a12020315070e0a1824060e04060803030a0522110904021804030302070c09090f0f080c01110705070501 64
    0x20315550740c00703c4460512600140e00c4581003251051942c54120303014200802d268144a02c040d2420514001e1220048000035149402a1b000000c100301c1501080041d6050b51402c03140e44580a01c0850040030300c104821032810016225a0302a9100c0c11020000b40c80c01600040b52010612590b50001d8003d100f5101089242c000140e4001032039003040b2004c000300940c15103e0030b405940c00000d42c641f203070b1700480c003910106511005503144269041055028002190f082044803c003d2000071184010040766800744071250080001c0300c0d00c810301a01c001800c0e81d40700c801074119001518603042054566080c0450845e00b909a445602c03048180c2c140910f0855580412451000340e041340038010540c00103056580710303a032070010302d00d502000010602c2e080c5801002580114011205140708010109030703034a152240313981c9141d0040c6564005103403a00c8407c008000c00340201e68410040008410b458800c0c0524645600d411200d1512100603141c003501b0440c1030b4021a040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919448210 1250 919446960 919446967
    0x150e0f060f03071202040506070b0a051f090209030316031d04020f0a03110409060608040b01230603090c120f0f0c0108130606080d050702100f050904230405150c 71
    0x45101c0459030001080d04000f1528000403c052001e80910744c0003030351040c030109420090005c110351207403181c80c00d0340041080f540ca909240c03040342c05070078007541e259441d2a0180503011150b4020184a00002e08482c14122108686041701c0b403441d00c21400140703800100c0e50007540d00c2001c0300c14070300205c03019030602e0070343c0b28281e10b58014000c16204140d1242c1092a10582c40c908803000341105400034072103140c55a4000e000440c06480c112030440c106000090080545104203500318440301c010100e5003444801c1100b00d0300060034444003030090805c8015907984440590100151400241c9000940b185e4454182401c8840340d5441d5008030a16180b00d80e40040c41da503000780060001c004085a50501e203009001035046480f907845058629200b003604000a0698a0310854013400784c0308202c46d04490ba03a40c0101c4660101c0e03400c2c4881480703850150009512403045081d107019100e01d261030300c9e58500781a60103440680042c1c089a81f502240401103602172a4501140d18 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919449460 1250 919448210 919448227
    0x51c110306060f10260601180602070b2104051b120c1002030705150a0b010f0c1401020f030a0515091302041d0f15010504110d050a06150e0f06 63
    0x10143c4003004080c0c07041d02e904203002e1905010304001d0300d1240010410f0480e941c0a5488020070300410748001c1d01043c08150f80e074906142140180c415a100c030313405040354601c2e006841340ba0b50444240038101440744604400c824016103411031103140110002c1000c038101061042d684040c0d00c000078010390b503540d07000e5000705000400701199a0b080c1c0706003908030a9030000300c0c20b50040060007403042c05856224020030141c400010700900d14184c00b041040100b00c015920000d055527400b0115010703158400c0800e00c0503031039030002143c030302c000340c68207000200c0c142c0503a10440d00b401159a542c000d0160800c3c40b07040c80c1d82c481109484101240c10070009601140540303800080c811a207400110351700080000d030040c498400d104c103d8500000940209459289214420007440301b910300001e143d2900340034200c40c0b24440b0b02000d150a8000030301c0b10103020020501080f6a84411000410b1001c071090841c03070001c40d07507e42440b101420208049603010820081c0301e04024807800d007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919450710 1250 919449460 919449469
    0x302070c0b0708130e0402010f08010303201e0a2901090213090e06040506070f0909020702040216080c060c04032103090209100f0f1d0709051c11030606 67
    0x703480650300c15984610103072038410310500c99601c03a40011242160300048550314030f0403183c0242d02c00d80302d0700031100114404441800c02440080c000503642c80c065141c104140084081c44890841500e001c100a808c00b0b4089424401750366100d64410303502c810500450503204c544c54610f2041c244e5401403250080072011006021f8403103a5940062807840200c1c1030890480100400d01092280080402180341c0300c3d00215030948641c00748900050f4201e228502640207d80c040e03c85804a5051400350b000035044007200703d800640c00c020083c2101020300c00103486031320490f03641e55640301c00161103080c14800782500c040c020302408144000b03085012a8800e180201c80341010080c0000b604070007404c5401000b0b03400c4a5078009201c1e46004070b45078001516000300949015950710070440080303000d82d1048100682111118011114480b00c460350031125a14210b12081e440d0400502e64010200f000c11008a0b02002003003000300d0011601e200c900202c001d8602c42c5002d0740802d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919451960 1250 919450710 919450733
    0x32003071a0f16020406090f050603160b1b0304170f150a0504020d0204090803180615400b0f1806010c0807080a02010e0303100e27160501030207 64
    0x20001c40400f10791111540c0c42992002c0d04140c004000b0300105503905009401842e94145001606050800149050a000410000c400307503e003140e01c6050310304a500c44064002590450680841044101c25400100080e20103010300c1641e841c15664042c503402d10307000c4132403c050707030175000f415103510100a9030604070313800900e511000c181da1344c6510002d4449040381c0c900a50051a1200b00c105001e10780700a11310503c0000307010a981600c01c40b116584840c00c07280100100300f841c0380c0c01d290b42401001000400320018080818210b1819074a168588144928524a030343c2202501c01540a01420706039040a07121002d0780c0c1c00410118803000f01081414004110610129245900c00c410840b111a0808045a220200782c03915010307548c01900601c006600380f407285840c06401104030390040301701a00d0340745500e2070701e07800d02900d1400404007401f0703c0d4109103801c50903441080c0c1d040b00f000075001408903c41003c492600c0ba4007282c201d14101071051024000040b51500760f0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919453210 1250 919451960 919451977
    0x13050601060c11060309010903180509041104090506135304060804050601090506060d050403090b04120c06030b03100b040b0a0b1801020312040f0507032003071a 71
    0x1958180c2c1581031410740800d9520b03003035400800010030041c0341c3d00c041d4044980244030b9501d45071540c05c92901c03048a00c800b8041c86600c00c40320b4011500140d8081006500040c010f003001c40c0301e2605031039080c20080c00f201c0086000c090702082d0340401502401280e818401041407130740c0d249001c03034201c628541030152580041c0009030500d220852240741c01010441e082c0a45941d40d80f03418009001100a560445140c821500040781c0c40c4103d00a280c800c64001d0041400c002800315220302404000e0f00c26002e0160641c000304801402a000300050801130701d03410610000b0786450904071960b603000d442014940040462155400f141c1034905440040c40440c5000f00740c3e0010b8002e02600c07104561061140c00e001a07204482000344c07222800344420390781495003100041e030700d0784240f62403420740e00140700c00540000c17400d84c00840307941c2c001c000b115400b41e00d03940d030503080454240c02c0c0c5c0e24100890000843da45010080300c0068104201205036507040c0464071034160013200c80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919454460 1250 919453210 919453217
    0xf050f0d0914011206090603021804050a020d1505040308070e03060412032a0e0307090c0905060f0c011113060212030c0901020316030e040b041e1e1d061305060106 72
    0xa0207003040e03204402000e890003036004d080010580e11a080001040a44405ca000742114604900c00340b510501451180d500440a444034108035402c101510414403811101103110500b07003c02048580310340d51045100e0303258101107080261020306160204025148280e05c03803c2080b000031507000411650410fa0308000c81e262541d80500100481c4855030000307601031401d12241b110364491508180940103800390755103030361a800c01c1c1050f5100c515414012a0a4820800c91802d0080c002c08862980410311420120145401e6003510078a02c4c2d2032034011070104800c1c5140100107030550007400030340000c1c40741d010301080214460000501040c02ca401c0800c0040080e4001d0040703803003040440001c3c0b42540c40510340a0181d500000d00203004502d0800f20300c40c18101882130040000289000c1d02c03603202e030040181c0c00303480d0201501c0325000000c007032002c4100e054026010030307507400c00d81c60800b8040b442e045450030304020801002000080c5a48000c14404203400d41075500e10318 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919455710 1250 919454460 919454489
    0x60307060305090307020d080a03060b0f070f03092105010e010606121802031e0c09150d08040f0e0105030f01180b0403020c180a0c0905010e13090602070f050f0d09 72
    0x1c02c0f0608502810b000a904901114026410010140c1c001e0150315940d07181044681c0d1500d100e4011400345030100c600f902d40c01c1003004041800807102100301c41c4289004200e0302c1c0ca407081010072854010307040410288294400c81001828001c00108a0900c2c00030440d962502400070250010507c102e4400340da80c4091001d038078a10240b20284035000307000c0b214030540d0038902000b1400380b56062032142c002c0641c514220303d491000c0d58006e00660502000c40820041000300701e40e00c5020403039a54008200000345401d80a0305000101843c201040c4c440d0f140205044c1004e9600c208459940d240006080c1c01507808402e10122680000c1071434520750f103520301a072400303664401c0b180d40005421055004042c540c6c08442c8030f41c070f00300c005000c5d50f01094005c3d00c8500c03c0b4081e880c0842d030402e80b0108541091645590204d5000801140340060780d00c449049a02170074065692004824035441400030401240788003c100a0040240345844d5000610203191030080480707001010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919456960 1250 919455710 919455721
    0x50c030d05090a05030a0503070306120b0402011d0a090b0f0303070f0807030507061a0301180503190c060c05040e100e070807030b0a090b0a06020f120a02100608010903080c03060307060305 83
    0x20480c440c0e900380e001040701d5403001d046e031006d02190000c65800b000a401c005002c20a000e445141031000c40e404054220700d078030386a00545203815090104c02c58007054104ca003903155515a2000700410b908a0700064005000c0c081c00510101c090505001c0d0f442000010000380001c04540403060300091110b80704c00940c502200c080c800e40102918003401c000704010b80304800307264425171520440007003010010190755640d0118452a02070100e030004d00c801e1600c440c920264900c201d4261502e42c0a8124079580c0e0000c44034040c406034002140030070140f001080c80103000e500300b0b0410095255403480c00c030180c800100002d20310320400c000c06000c901281e0081d000f03541e06100082c0030f41020b9813290b5078a802008401c0a15200341241000010a24000314106010241007809000c0850f1703803c401c0390f00c2d030303000501200452003841c40f0403000200c60320400c030103800d034000040b840d0002414010328a40e0050451345c0451020410301003281d9002030002d0072111a82404545980c1c0d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919458210 1250 919456960 919456963
    0x50c0301082802150c01050109020d141b0a09051f03060b07080904090809042d0e0312041e060e010b010509010f0e0a080d021e0601261204091506050c030d0509 70
    0xe05c11414110340c00c0c40c001081c0c01c08580c000d03143d052540ca0003041441c40c60302050300c52141c25900341622a410202c02907139500d40800400c403841682c1008a41c540c0d032100071490186014646150740c2000c801001e04090745030142d4802010050721089c01c00c8080c0d11811414441c89100c1880fa42d9101440d5040040d0581560100c1500500420032902c4005101540300403800306a00c56181022615501d01120b11039000000c01c003400450038200da580d41ca50603e10302820036580d11144081d05081403441c50200b80c0d4030782c4a14008206408007031196800d40340380c451201d05020b02408141402d90303000800c864140003600c0c200040329817180100e200d410f000d412000c054040c07512000c6642c1d40000342035455410703145943d000203084000c000c0d00d5070800c2c00380e00304070305000e6621048e80e480300c0c2c1107040110700e00b03007560045059440354002ca907105600c4007954544a8a0407420034041a080c8070040c01c46041840c42c0c480c440711501e84070f218004503100050799074000329644910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919459460 1250 919458210 919458217
    0x2060f070309031404092a09031104060302090c070b0c091302090d0503041205060a02030907121e0c060f110706030903030906060b04050901080109201201050c030108280215 76
    0x702e012a42c0e90350303a02c2d43e00003009882050442070510038007ca122403094034101502c21540d415603a0501502c2c01c698428010200f040302c02540f04d0b031103140c048052380c1c030200e1360b80c00765503034561403640c503200d03803801540100000780815a07501003400040c000d81c45c1d402c000c0300804a14500142d0718105407000401ca114845030250041c4804900450310304501e2026402c4540201c080b030344103039640c4030500164841201c2d000744c00e030444102001045011403d1011451154232520316551308886102c205920b00741d0261500d000100041184540010700030326003000b14940001e007400d000b00c0b81607035001280305507005c0665072407003001070501c40d9101004981d03008409125243d9914054030f03140d08540031b014811a00e0300e00000344030300b0500c2519882c40d80070850340304d491075006a900c00fa0440b00c0c800c40d000001202c0a954582c02885018811000d40d0046132b02c0c0c3d4103001002e45088100c0507803d40c03030790b000850020300c450160704a5244a5045070043e80081240306075640500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 919460710 1250 919459460 919459487
    0x9040b0423031c020702060f032a03010501030501150815010c08030405030307030c0c030e09190e0a1104020a091a070c0e01030318031109181009110102060f07030903 73
    0x80214a2070980c035080030000b40b1002d01c4400c450705074074401d070500100701d204603a8000d52041c800c0105c40c02410418000c0c50340306000030303c07041c0e95540d11041d461042c52007194100c0c2a2600100500c0b0660301071040c140034200c1d02600818000f00c0d800c4c054090780780500b14451903000c6140c1d00044d42e00c1240c15124044d0311514440d168201071034410b0790382d00203444050120f1b0400a20b608070500c10300b07007140404d816960b20280c1c203602c01c06020380b285e4040d0006070800e0852a240c40070840a000e0700180204c2e10000304140e040034200450018800354110348102d00410110050b1a4482450130917034420f02c40031400740c1040012404548200c00005000001c550b0b4009000b0f83c0c610ba540e8120390084d180e82c1200c04000c05222408000e901005010300400c0403040201d003404505280c1c000c5000340e20350007903802080d80a1070480c6001d40150102d840303042d50001c00070805030003a149030f400e0002300700c1810080a250240030000b0201020140c1d960700400c18503116030400121803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 919461960 1250 919460710 919460753
    0x6070f02060415080108070608040f0308070c0215030708010b18210d080403020c03011e090321020403030e03070303020c06030406090219080f12030a110f03100f0906030209040b04 79
    0x1c10f106000f905a0350f00340b140000794081e4203400922140a440c840344070320350045002c20f20b0030582e1f6050f20304500161200080024001c02c04e00161102e00c3d00b10300601c807441c4843d48a01d020344004044e07081c160400818100180000d41e1181c0e80c005c81c00c00d202e00111941e65042c0f803012084044840035210850b210720410300b100710398035040018103000e58040d070701b690701c0c0300c0300075003810b082c2d400c05407030018214074401000726030140c50f9011145551103840c2c5850108806044002c80e01c002c600c40c441e0311980080c04008058000700201d140344803d40240c9005031461314048e481d181030400150140d14004002410041c80d603110000d940d80c014483d90820411100c4400425064059010544a00e50741840b0800380043e22030f50742464440b50381e1071580c0e590b8031003001d03100105044140d88018091607242c090410080c51041030203442c6100b455180100c0c0078011071542c0d1050715603914281c42400035864030300d03030b090380b0507008840345c030341503d0f40c2c949010300301035082d00000c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 919463210 1250 919461960 919461989
    0x120207210302070b0406090525080c03070b090f060417240417090105070c120303060501091811070b07030b010e0411030406091b060507060507030b06070f020604 71
    0x8000c0d26900488000401481852054992120941c00ca20031602c028001001610001c2c0000e1110f400010200d48a602540c0d2090003050a614030580110602440344004200c2030204580400000a071400111f0080039818600203580e0401d2003a614000e0040f054a05450204d40320f0714100c03070042c85513280101c1501201d01c140c548568041a04c3e44460684183c0c50744010002c0a515015540100b03420401000001c0042060f601c40c000c101d051003402c0c080040480e28844402000f019904042c2d03005041c1450004c0131284240c12440c1880036a4400748000b130b00d003c08a00c17440502c1c40002415007180d038090344036030241002c005c207080c692108100401d0f40c184c110841844003a01c6200100c13041000300816142e07029016001e1034005e00010740412b000c0d070032031030300240100e0402499541501c02003020b0307422a004103000c24000515a401c2217890310819a1208c0c081ca02002001c050740300141c002d2064550140c040d08048843c4000e554803003003194000c281c040c8040c0304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 919464460 1250 919463210 919463213
    0x8010504020f092512060f050a0b0a05120405102309190809120703030f02100203010605030c07063b070602060601050a1412152d01120207 61
    0x60001124100d00a40c94080307084074a0800d44601c500501ea0714114050790313495003140600c0d003c3c03840d61240801040d4100c081d410b040a01c500b501802c260070b0389882c0c42e41450113105104450741d0103100c1d0100d0801178a0b10300c5511600f5101d00c04076084110003103465a090441c68640321352002680c540c50100d190041b40000f00007007284003030aaa14400c281d88406140e41c030f43d104000001080d42c1b0044900002881c1e08005003181d43d0020302e03244034800340d07161003840d0415039001100819041c0200c40e8070036404010400340580189419403956041c0310b8010068003010305071140028000c070b400c1d03007041026081201c00d400d40145000601502004003600b18244070030b07118010b19800b0441c51585004107468040e10200e800401143e100e01004582643c80054410b0400400125044144111400130320441c481c080e010201030800d60013179007580e032041c040039111318111034400441603c0001801034400350010031061061100c030040e40c0400b0402007204086100003080e50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 919465710 1250 919464460 919464463
    0x1080c09300a02010f0302071a010927110d0323031f030b130203330f0403090302100203131214030a080109050c041214160b072a08 58
    0x11a1000840c00c549203801801285916080b401d10040d0000c0c1a00d50451400c502035001022400e2060789540320301c005040200514400030307040b03201d0300c81c0c40d08507400016012000000407082e0b505280c1001c8125030741c461100405602003280141d0000500409141c000d11100882001043c0740c10100d26012800800b00d80c400c40346201c003128000c0c094084444419070b13080941e80e02000e0420f01e41c0300d004c0032002d10100e00400302c0c3d0611607640050f0b4040714500001c142c5040310780000f01c1d402c0c41601040c0005000901c1580d54016400801c00481c0c1c1c0310a0b8039080301d405550740615020721500c200d046100700c1e550313054940c9d8110f40000c2d908440c0b00c0442c003094050751481a030006510034041c0c680c42200c4e01c400000d0f56440041c0030a2199601098011801d00080d9142665030403078104900c20750701056818000041070130005180c244078046007081518641c0704010308296840180f8000c500000e09584d204941c00101c0426441c112610b804100c00c4040905030340d804005d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 919466960 1250 919465710 919465759
    0x1270504050a0e240108031e09030a0212010204211101030b04020d0606200102030907031407090f0203060316052d0307030507080106090507090608040c2c0c09010503010501080c09 79
    0x15844d48507030000001c000d00301005071169481d95071340c149611040c507411440245c0203100704c2e5030b2501421500d0700c0107a07283c4c41000858405400056211031034021845140e80f40600c20301c22000c0746154000002c4c20304c00c034120004100b402d00090794104900130600a00494115008003880d003070010030f01c42d4210701503c0640320b5402c108003401000001450a0380400d588030340803544000303000d000060910308034440e9aa11031084980142d50b610000307042e10740d490542e0001035400000e0220500781800401c03840804500c03c060071b5403408012604151030041e451031400700104424840c4492081050000c04000701142d074a15200c2c20225260246403040592541c0380034000a80001c007805824821005510751320078080c40c0280907181e041c8000c004a800c2d0110840106008409404030510000f2510820020340f403030705034582e003041002d0100c01900a0601c01c0c01120380c1c5c0042200d05641c000c1c0f0b09080d06486407100e000c0c0b00d000b4401240e90001d5000c1c820807442c08480d235103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 919468210 1250 919466960 919467013
    0x11070204052d28051503010902300109032a020f0d03030f0c031b08060a1202120604030e010e0f01120c0903060f060501270504050a0e 59
    0x1000307140c94018002c01030200e825048100300e000900d9040d0784103401c28242e0b81c00b425280c80360114500c00c1c0301081400034000d190f400760940d50800d102d04c42489070304116000d002940204605086a0002144910040e020492681c40b84401320319904904428440c10f110305070090050242a1402504003074a020b80001c0300381c401c41401000e40c0c040007072030201c150040c00c03010883d038038101840f40c82c14000c0c9041e0103064807030f0503144243c00e982c40b806508000c680c0d000954140164080b04900b11440200410032181800740112035a403035022004540c102e028450b0b8040680c400300d0000760062035234081d41d005903c104024113401a84041e81c8101c266150640101944200311506032441c0c0d11500180104900f40e00f07400c2103500c0441200b68a0a1044410780ea030781d20401070f180586824244691540410400340d6040440c10700c2d42d9034001d40c0300d03900c03941401392402c028800c0c1c401d581c4074139183d401155802860340e0003024002d40001c1582e1800038401a000344000c6103404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 919469460 1250 919468210 919468219
    0x109030e03030307050409020f070b1017030f0d0e010b150702040b0a1412010e0703050a061103040218040305072102060105010318032106170d0309020108220204110702 74
    0x1000c8024540481201d2089041d0303180c06042600385480c034402500441954444040d0070448007000c0f03854204054441c0300d02e03050714041030303082c40219203007111004a002841c1d030047c0030f00c005828040043d6094540c003c1400944e490030140310a01500c25a00c0c410340110640603400391411480b4020645140280e40600c21101c80006100700c2005900c81c1c0f031038503803070b2800b01700031880c02c01d6483d44003065090000c202400400240b5007010340303952084443e0382c064034100707040100702c0c05038415080b00d4400e003500f0b502d0a0703004140340481c000d19414001100c03500260805000f90300340c80c5031607004600e1480e070412941140583c2c04083e107441c00548144400001c0940c031030f0040401c1081114008506600c407540e0950764010081c10700241d04a603164030f030000348100d00c0750300c0051007800c507290103c00c3c02881e01400c181c6c101101400301030403d090348000d82d0700704d0035181c0c000100e4480c0c8040425002c0b1840300030384078000029402424a00d00c0c100010095014107200c600885 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 919470710 1250 919469460 919469477
    0x2070506030a110a1d031b09040f050d0c060b10051b0312101827030203040e090105010609060806300d02100c08060a0909030c06061509092f040e0108010903 69
    0x1820035655203180803142d0101103000f40644c1603424005008d5402511400c0340c58200e040c60358030942445c44103801303040000c1c800b41804050000c58081d001141c20140e45000b1203002c810340003852032080480c001096104030440c505c210300b041045942240c0c01010844003410401c0305503400e50001c0c81707480305c0001c0942c019488803041d807040e110410b441c4040c60547c0005003d4402c200303211100241e056000c00e01c4001025105452058402d2224200004083d0704200002d041c14900341c2004041000003030400105072200c0d40304c0d40e11a0400c0f046210f00039060501600b0542203908003035418050f043c01d0041451700050005018550b00009000c0b000800d00200d5405608456250340415440c074108001d050a5209102c5940a031030086c1c008000360319404291400c1b507010b882c42d404400740c9604a0b41d4041e110502405442c181441684070a001c50800c0d82d03c4c8190792034035210201127020611001408641c002d19010412119643e901d0070568000c0c0031601007940802e0259 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 919471960 1250 919470710 919470767
    0x31209010c09060318060203010f0806130b0f2d040c080a0c12030c0804030b010305100212070e031e061f050904080904112a03040602070506030a110a 66
    0x18000c010341800e07141d40e0081000d240003000c8015205807034841c03141451420440c80070420f1400111302a02034800f02c80c40f201d244c80d010740d184c000c00815100b901c0706502c90070b00005c0c21020440c0d41026841c00c4507451500c441505100c4804020410300a5458114050102c004841140c1d8450381c00740b610002900e03607401a172611004e1a0130000c0c180003e2801c14410150301940c00c0407501d0003490054000c803481c0e42e441d00c0b9036100750803d071414484040100200402008070b090031045401c1c05604040d144e2281010400c400b0b0701c46010f011000003292526102080304c281129002072000c03108811002541d07031107042c240c070305494031740c00c8003c20200360700200310080842d01c000e8050810303562140c5651070141c010000403a842500d0784140e441d110090b102074001c1c1240c0c1c03030541c1d46941b80000074924494407104000115002800704110080d00414940100d950641c1c03140c0d900e544003400c81c40108610052444c0000c07000c190401c1c1c20382e00c02c442c041054041074040d00300310b20301d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 919473210 1250 919471960 919471963
    0x60f051f0f0b0a0311040e0403021b01050a0c061a0312040501080612070b0d020405180a0c0c150905010e01020a0905010207231005210712090c030215070f05031209 72
    0x1680600d640c4620108070000f00c09129600105a480a0011a0f41003649652800d4440141543c040d0b005030721000c1c2d8000000307484902420001001d0074110f1a208040401403c50244510b001c4c0c409a81c83d001d0302d1017090348488440c0303080700080a81c1d8a0694090b1401803d03006401490700180030000084c1e02410190300c01310380c48002c4802400c0140c03510070b0002407648a41d0700e881259400303000c0024152a0701d1b0360000103104200f5020990300d020140c220444003a03079150400c0000c8610018003003120b40b40ca490740e400504a020811403d00e0400901410010b0040d00c40341d840040c00e040901d501c11a10410b60340248d00340d8042c0d698902c044141094920041420b80702101401001c0d07203400203a010541d021801d266003001c1d001024406200019080c031a070340e01459080050320755106514954445401204106c048400c1c3c8582090550324040203000e04000781d00c2c580e1220560080d500c6040d8040d12181000e803540c5002131f00e035000320902044103c0c000021a84400c1d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 919474460 1250 919473210 919473239
    0x140f0a0503030a02090d0807030807111c2f07030303061d0f060a0902030f070809030a0c020616080c070e060f030c09103501091707060f051f 62
    0x411900640c11600c92095100017540320b444165400700c2e0062400380040d003000b01402845000382c0f1100210300e040c10f00074028641c030744100045904512003040502007141c40322440d00c5190300e0070390710074120b0b1403400d81d64480c202d0480103004812048040d001c0c40000700c000c01c1da0b2183d501800815641d01d20400110192000c1001e481030341d500007541d11182486865206000400304280300c0d80e1551440102d034015034554141e02e00420401103556040402d20750440b030b110300214501042c11000038036807280550000d1041170009042085150b415402403810ba4200113201d41d00d800a08109954952038410003100c00350380b13000980b00d8942118208045e89000d03019103150034000f020001883c50003403e42420300c0c003001000c1103a809900303070412580480a04550510240011071f6894a00160210035507030406031040e0000c1c00807180c07030130300e5180300e111291101c00510b400c60207407142040d171035a01403404d030802c0342181c03c2c0d030241c201c040c1e81000c50918103901d07503913160322840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 919475710 1250 919474460 919474463
    0x2040909050a06112515050708090c0619080903360117010603021b0105090a11190e090307081303110d0203070b0a02030405040606110708061b0c0c0904140f0a 70
    0x5c940d8020280ba0020b00c1880950741d880380c1700424100c80b0203161201110f1050383c512000035030359020402e054004000280a202c002c842440c20003028a0125080d03509565886c0100510307031010405010707040081d50f201151a140b1120382e005503100306c6001c1b22104803c91b0f050103d2614a142950043c0c81d40d40d0101c40e00d481640140c0e0820a050700a5446603a00d07a00955480342c413803000c1102880f5003030050702d407400680310104190030259074001a181d1001d100e2000c000c0800c1a9148900501f411945812000031541d40d0303261100341035006100d4080e00c030180000d0303a045500105450941038a104007143c50307601c01d0b40300601c103080202c0c03680290503911031081070022444d094058482d83d1000e00c103c0c8d01d4a0340703c201207802d5903491b038000d0004c40c005220402c2c95403400d001c0030001d801e4400081c49240b6004d0100302050071501d0f0200318140000030282110b000c10300c4050280705001d44500c1c1c440c00c2c00d00c0e02da413814403803d8007100180504107261081410110ba00f070b082a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 919476960 1250 919475710 919475737
    0xf1002210c18011b051c030506132d1407020a0c180605060d060503010b012d120c02060a230402060306190b09040501090606050a030f02040909050a0611 67
    0x60401281d042c0e604038450b82c1103061112550380740f4803000c6a28a81c9540611613406068018004c40005c241200949910350916052404104141e2942c0c16030541c4406401c01c00f0500207905050800c43c0c8204c900d001054102164110404114941100c0074000b403040c00091942e0700e180049031295598407000302600e080300c0003003107000c0e003004681e00303600b0903684000340003503403000000c0c00c40d07208820b40c0b02550b07242d900030000d51a0038461804a9103080c242416003401091105000703452035035041c1d100c0943c18200d03901c00c900c1800310003060201d4000805ca060034040000e942c42e00700b100c00c08505410f0403140304800c1e51200007120700d2003000c0002e036219107942c2c3c00c01030250001416a034000750a14190310482070f168075003a00601403440d600c0c0c1c0d03450640b428001580e0058104194150914504006042e400360860701410980d20b0006181d9415141950281c40b8a50052880303074107120001043c820042981c1107898410030017008044100885c090450090781703400750f1b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 919478210 1250 919476960 919476967
    0x70e06090414100903021606050304080706050a110a2d0e130906090803010303080a02090616050a02040614090f311a040516080316050f1002210c 64
    0x240d80000350a802d02403441500d02c03000c4208007040454400d0b84066006074000c100e5070841c100ea1120340c0016241c50300d00b80b4914601030302d4507401441860300041115a55100080c440e560540c004e041244200720b0a80c3c1d00c140003440100000d40c4209503444d100303c0e100070170350640000b6580311404c03442c58a5403030300307005d40b5010895052101a192100b25071a203500e000024070611501c501d09105a0a0584950650900814058005240102c02403041181d00c100d6541d41055070754480e01c1841203032000c0c000c1c0c0392403801c0c8818900f00a40142c14071038081601c1e0890034298446650a50380c0565694039000d48205004c41681c49030460400b003030740b80c2404042c08240501400c2c454145040c1d04645580b54128a40f440c0e0500000c0440c0c0001e1004020040c80b002250f0740047d9000c103451420401d82e6a2280714501900c88201a02010103040007030500800303061510f26000d071040081d00d00d084d0800b80d808441920340350307520400301000240118018034001d00030030761190306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 919479460 1250 919478210 919478213
    0x5040902030309030106030501020310150c02102616030203010e06090c070804060203040f05030c0a14040e03040305030a0801080604030c06150b0a0903060614090c181206060102070e060904 83
    0x81204500681e00360108000140c91502c0074040c2c8401144550001a0b887c030304150740011800c1d640d00042c141c9800180140707450382c0d10032101081d10b50122048011420015015580881c02d14890040503400d01c050301c44a2508000c1c95124100b2803000b04000c0c0d004076022012032109004001d0054124004100103041c03071501d0650005902004501d004100d4540c440960480d900002c016800081c0c2402804180411240100425030003409003d800e080001c035003000034002d4441101c00f4908601040d940c541100c40d015410a0540341c1c1c5548038105a912680142c146002040c07030078000003100200001e900b0310480d01540c2ea96881e2800c2d590b1040600001120114240c0001c4000300c2c0784074015008201001c011b071101070b40c1e03614510f40743d02036440e00c0e40460040000d041300c4040e992240f6100d81c0c2d1241d0461101651028183d5513289015010b582c1603820203240c0140f403910400c00281c0600800c000d80888103103075907603500d00c000f04000301c5420b60460580f501080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 919480710 1250 919479460 919479469
    0x2040509040f080c060406150f1d070513090207020a05150703050a0215090606030d051e0915120109061202060f0d060e1e090606030a020111010f0f231005 68
    0x182d01482283d41c50714120803122040e1a0000030b032010b0f03861559521015408112484c130307078001081e81000703a20703d06141809540d00c641c0071481000b54524501d0010310260b1180007240c50703515036107079102007070750f02c0d2800d280094000c010200c4c019900084040380f41d2806584240d2100020f9080a182141942c1c007200d064100d000c0200035841868003400e03180110307424841c07240d1a042d008140c0f81c50142c0c20540740960b00c0c5c5e040402e001c810080b480542046200140740c01c45901d4001ba902c94941002c40ca81c800c584464214096010413105241c4403180d82090407580b88403420700516443c9d100c040c945005080c00294070445c100b029020500045000d0701c20001c1602d000240c141c1d1300d030481a003003c0700300d964480d06031003407200c3d214100f040c0000c507070809160001040c1d6460300e400401e0340d41d038811001074188180c03003c101900d28000d400100019803240c9050020268010103c4050000e540c00314103400d008001c0003905662100c0000d11600801ca07100208515240600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 919481960 1250 919480710 919480733
    0xf0f170a030c08070f03030e011524140409020a090b0a08010e150306190c0c020a06050c030f0c0c120c2404030209130b1321030b180103030905040204050904 69
    0x40782d0883c810b0112101180e40594803e0b2018065240421030300c400401080c2124494600d640300705619450500c002c500c40c089010921811900039601040104001d844072162010180006800041d0210b80d898064001c0c0802111903194403503000d032940060b50f46400b83d00017190029103c000100800ca10888d0a9500141d08600d4561201d0012000c00c1c24281c040b91100c43d00303e0380760001102c01065201d200301030f0000d86045030104095900080340745000e441024104080840c50f0084404180212981d95460848681e030703031000703201312940f50794607c40c0d4075100700226221480850350100750084405c0c001040282e40b00c50a0200320301100b8810184041d810040c8000310050302d440c025580101594090001c5a400520f405d030040c010040808242c18001081d150001d2000304005006409024111441d00402c100c110003c02d80070b401c040d07104e48a2084607550342c860003a401e068a00075901e514516480d6030501c03041c1c2c440c900c034150304524203000003401304030001c001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 919483210 1250 919481960 919481963
    0x110d1d1615031e050f010e060609010e040e010e0703050a05070605030106020a0624140f010c02030d0c0f020a03080c060c0c0714191e120b04061a04060f0f170a030c 72
    0x7403c80301c81203003000704403201110200014038260340140b2024001c483d01540c004012250145030510b00c0000a20500126079500c0c00b841e01c17080e521408440c01c0d000034003504c10340742c2190822036503070030100e964800480301070f41c0b50700810301e0100d829480744040b207050f03034003c0c2c0003000e00345020307034421008000c0c0050070300c020070340001c0c444103038804490302c04024820170114000381a012401c020304014401035082c103000704c40c0d022000584010410740d241d042e850401d0040c40740e00b402d01c1603886070071050095200c02f400b5000b000300100700b0054403a00d1043c1c0200c41c07041c0d5071188041400c1c031480806c010140e00ca40000c001e6402342e0380d048003000e14041c0601c25949445100090450340343d800444911200c1002001401c004003c000000c1440091003c0380c980c0b56102e03032010010203007014083c1034070f400e0703061503012002040c000000e2011780304214003961040140e00030042405409558080168001039841d08058880c8c1c102542c00c01170002607000740d9087d00c189144240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 919484460 1250 919483210 919483241
    0xa15030f06080a03260429180607360503010e01060e090111070b0a0b0d05060109110c0303070806010c05030d0c0e0d0c09110d1d161503 60
    0xc8841912100e005080c01040700c1c00041441068500e00a0103e1842c480b5007000714001c01540318250606080058210760401c1c00c00620342805103103e4180d80411810019920b00001032050542c0071802c6000c1c0240000141c41050703c800c84111001520305022074214000e00451008428902401005c400040100e84101340d6407140880e0940b011046441800e0b50b56800402c000d10f10030a000d540005100002c00504440315004034140c0541e100c0542809220300c00a040d4050f80c2c0c0c020306c03d480001301145103001d61883e00541e180000d000c0e0300c1015051180008c02211203000351004a401c5502440c11036403445400c43c0c10890040060f81040328200f480000304038140000d00403134000c01704c040b5030001858005040722002000442c001d940c038001410201d42c40c600795009480110f400414002d04400c4030720329900500c03101048042c1790514990040342451000c00d11004044c0a48100300c000c885928030700c00c500d100390078a0060f21525503066511136800700303282128644 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 919485710 1250 919484460 919484471
    0x1020c0409051c050a0210020912011e0e0111030609060d080d02070c0f06020a0b1906080a0507050603070503161e050a08090d0f120e03071a0a0501050a1503 69
    0x80050207451880c041a19942c0041507501003044440d03440d0402c0c541c10342400343c6461001c2da0002d40c0c1790000745864801c99070105034aa070700c0e40d42d500300741c046d508004000d0100c0a482103c004101000a80c21f00c2070529103010001e00d0001170290700702e5a402c4200d450b055a5070345052010140000300120350108407904410002181c0101400854181d02c3e001625849945810810000c3d55000700f800d8001c6e10b00200301081d80000d0940c5c840c1d501904d141a1034032103250a0100c07800344c420701d4100504289000c41c0200c400070308004464040d100300c480003542d030014000248000d40d00741000803c2000000d000c1303502000000700384084c4c0c2c601042c40010000041041c00801c802c0a03000410020307042050680c09017070180c1000e10032001d072035041c0c104c283c041d00c5064040001b03018045a1034030710040c00c485900011070485100700741d03655825076280a01600121814100384201c155012030f102c3e804e035101e102d0507928050300354448070b402d0002681c12854855088800c154454 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 919486960 1250 919485710 919485733
    0x60605041403191a0603072106110d020c120703092102150c010c18090e0a1a040201081f03020d050321062d19090212070914010c0308060102 62
    0x62030700300c0c00d80f80214104da4180c549004406108200a401e5134402d03440074200340611084802c909440000e100c92211003c180c51030720901030015504015500000030800c003200e40c00c250018201c001c465401e07140e02c403800e8244d4480c6801980030240010709802030500c0607404801488051544000095214480381c1d40001c03a4180c0219118414540202c0c071031820000901a403040d004103402c0c0300300e0b09122160101c855030a284201545c541c0c5070401500c0c0d41e1018401044099000080c4613070030b01c010945001c10085c2038504a000404d00c10009030911007a800d40503034403202c40003050001d880c2d40c0801000c840c10500942d418081049240140160082103d400f90a60480b580b60344c54040f00b000041600c400d154000d494044602039801d10b2072100c00d0008031801c0390000103800b6600080101110260040d042c0305200141e010b05040ca6042003d1042d019959081010f035241e00f00c030f103050802c04905034045040c0340005000a070250661545c488030610441d058004075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 919488210 1250 919486960 919486993
    0x7080322140f01210f05070305151003062d08060106270b1201050411130306110403020307030302071410022a060d06082803050913050a0507020d03060605041403 71
    0x25822904400d0345d20805003c143c0103900401e9440541e0b4101002903291814008103000b21420720b46204506480c5000042802580b0034405451038130301c0080000c40c40885c4021031100b08000503031005200400058001b000030314641038a10558404000c0c141c001541240095400113094803d01c8903c40443c169000c81d000e440c580c0d001c210010010352416052208540d0300e00c007002c654001c1040307943d01d0038400120707210071241e0000000448030100401e2000c3c5001c0c0ba00b0003589402501400000e0641c001200019a15100307482038800125904105c0f22a0488001e41d02603002010341c880843c4c29a442e2003019010340b000f2075a4102c50000040055100c1c1801e2454195114401c0c40211020000703800200780316801c40c005549203100310310301004142401000c00500240c805410340310742e410812910740788603040c0b0050504400172000b03080c0407140a4010302c01d004050140d00c1c1300340204070455116885040c0741a0401c01056180d040c450305098061150307004c81507100d42c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 919489460 1250 919488210 919488257
    0x20712110117011a030903041703070506070c020109031e0804080d020613051e010b0904030c0b0f04080301180204030b04030305041e050d030f0e07080322140f01 71
    0x403540300055045508000501030441450700c90007039030381c030300014000303203030b4403049450210030341d09a494990b520404042c3c9107105a0f048100c21502030303907012021010000180144620a405441003a520340d00304503540604808064001880aa810070107d800c0114014446d140c40307680c4800714103a44c540078401c0c0d12582c0071910680c800900441c11542c144001a005400c41007060280380341622159a81d4ac03206454440310180348600386d02010095100781d000c290098004d880b54581400e014003140d4210009541c06041c0c1c40010301034051115034507104a500402690943c1d09251910071a00c40001404008982c05c00001c400700d084005524800c038441c0e40c000c6000d141c10b2501003010298540b8032240501c030307040300720002200441d00414001c25032600041116094000c0f4014184101003000d15010300c80c0c0c04140954040003c01e41c0322210103194084a0000d01c4130302128450f4030a07a11940b00c2c40c2000b01107881c1111914030303a008149006204c03800184500c00c050756 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 919490710 1250 919489460 919489463
    0x304020f0f18100807080703060b180114090601050702030d0e0d21110307030804060f0605061c050603031e0702010c0c0e0717010b070b19060e06090a0c050d0c020712 73
    0x10072600403c10880d00e15401d03000500a80707400340000c5c5262082d595610102400000c0070291114440b2140382ca0700958000403c502a13040704507965250340c56409048403c0a003805120444e0001d4810750061048030720b0b899014000b8507038516041e41c01c540000301d07141041e44c8440341203017020108056a0380c4c01c4140c2044240ca84608008600181203214020240000c503002841340301c0100e6080a102c940c402d80052011a140460f5800701005004507000242e20000200305003000e00e10194420051107980507040019890740f5003016943d01401802c503610014a4140b1658400e801000c1c0c039009106040428046489a56100c1403a490380c1200d851040c1140030010042d6002305111f885024043c1c14a40035410100c0000083c8210354002c2e14419105001c03038690819103802c511b280c049044101b1501c0c0d2110000118454261030031072003403d80f03101056011645100750080c0c3c0c650350300d03210316204001e000580600392010340d40c07041d40603452001554440041d951110715 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 919491960 1250 919490710 919490749
    0xf0703050903010e060903071709130902011808030409020904151d06100e0d030c0b09030706060b030907050904050c1c0b0a1b200a03090302030d020607050304020f0f 73
    0x241c448400741400c4030700050b40000c4540c424001d00c02042d0b001b0085030782c01e40c1c10019000000801c0040c1e42c40e107104503000143c0207081051030721034005450b8842c0201034802d0340c4619100daa22000345040031101d01550489030420081002181483d80c01401003000c058000300b05147d170180c0161601505510064003103074440310a04800004000c5554000300c00c46034803081c03115606004041c0c20b4450b04207800351000035000c3c400e041c0100b0b030403034000341e120042030881d01c0c2803055162a0381085004456190030302d0300102e0307500300c46419640700d0f100c110001c025991a1a041205a0b0301c007500c165034500524061072070944440080c1808040000550715030220706141001c1c20150040809000e40d10700040314144a40c2a0003174605118145042c0e5232503449001150704030201d02580c84414403030001038100b0950404603402c02c0701d000b10213a50a003050750f2401d1f41c03110422101003001801c1000082c00615204016500492010742401003010008000c1200d00304d8500d45030481703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 919493210 1250 919491960 919491967
    0x60501030b191118031903020102130f0509160c0b070518060304030f050a020f030c0c01111903050711040c0c110409021f17040c06022116080f070305 66
    0x20000c4050500d01400301d0041c0030081a0040c0c1e4100b400c42c0035550300101d08050061381480107540070455440304201075110159031301524640030f8003c2d4010204a00061024540020241841c413400c004546000e41100402d07603503014001d5151401762608010710114072000c902080002150510940d1507032942507841c42041c224401c0c0d82c0712001c44500c5088100208000294440420010751410f400d00c3e80c2c68010a1030260b0600301c4008182c2035921002c0794030403a440000408181d03440e0f0a07280c000d410300c12801c00c140c03541d01c0c0392031083c004c42d070070350340c000000340b194005101c564003503540c03200034601c1c3c8000242030300c000c9040480014109069503081c44030084007100380c0d000448003040714100a60100389503088840c601c010000c05401000c0c502c501501c0c01400b803032020128000d041c5803901c0c2102800b001c5020f004010b100702c80701581512028440992440c1c02030b002c090030301d074000c1c0041150900c9002c08076102c1d8014407554110b0080d04002d405094400e440e610348 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 919494460 1250 919493210 919493221
    0x60b060c1e0c041b0c1e0f0212060106090b071b0303080f160903020103052508090f0c0d08070302010b0301020d02120604020a4404110f0f0f030703060501030b 70
    0xa00b914a00207030f8407841c40c01c031511410b0201c1e410b01c22285081800d00070344101c65030400140c0c81da058040c0d41413021004030100e00704080144460a49842110200007004614018036075940c424002c000100d4107540303046c0242c12419001c3c1400718840c6c0004081008590000c0f100e180c2c0369401140030810034001c1c4000101c102d41c0740b40d0f01600fa410840560060b500005103030b00128132029051603640c80200d03090500100c03401d0b001003142045400951100c10000304640400c44d220300090151102e5128000c20118030f5444218006000740798151007034a800e02543c1c00f04804909543da11040c1101c180c80a0015010300c00042d10016101e14400c402d25101c0480100918440d46c41041020750380c5070010303000c81c06038010900300c0e8400064065000300c00b0304000f2a569002c0c80c4291880f0036810300c4d198191045115401c0c0300210160b01003400701c48100007503050707070200c881405480309040000d1103050004001701162503203941e80d15004202c0c2c20a030015030303004810004004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 919495710 1250 919494460 919494463
    0x219030f0605150102010c05031911040b1e0c0607051c150f06031b050c0a150c0f0813060e01060905040f02180112020405070309060c031a011b060b060c1e 68
    0x2c3c941800780000c2c001360a4211005245200041c501e80191601040040045205512080514030244051541d0326200c0b0f1801d441500311410a944c02c1050402c19040307400743d00c2c07d58400b00b01100040c2800d44418006039425040600762040c00c56608051130b040d0402400788021005001c00307005000c03410603aa484040200c0d030080401d16052026030100320201c0071034020796a03004c1c40d0190312040003002c4e10b0300b001200100908080e0519100038080d5155a0040d545208240c0b070318840010040e030b00360ac8c00035040394885000c4804448180c04551030b1303040300c01c4032442030f03000140b40c5071600840f208840e42500c0640b09100450700840c114100000103a04815003140301294540c076220001a00e07141825009004684481c0805c0659001707401095000b40c0c1b003101441041d22404004005003060240d529a4071740c1401010741c203501500340003070110001001c0c14401031582d200c40d005003024900b5603410280c10411544400014080a2207007401018950703040034032011b145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 919496960 1250 919495710 919495741
    0x3030b090714092e0e01030f0905061807080f03070b18031602010201020405060a11100e0a02011d0a030c060807031b0c0c17030c1213030219030f0605 66
    0x12001c2c450280301e014034600002080d505440c400b25000200b44121070040491019001d000e02195a040c0850240d000d0f04426103620307145082e138040014001060010050318040c0c107000d40705400c07100120310a00d58540482d000d00345617108407002d440da244400c502d041048003d060742500049510341c1004440e0720150f0300030701c40712031000801c0e4014409503100d118038018800400b0661a071002164001c0d01918000e00380203004d551149030300813020303215a40070f900585240c0910007040142075000d01c940b070340121382d00b001400306202550065511070004002d51810240340f0f41c042829075030311840040075600c242080310095140c042c025104000c00341012060509200103402c0c03041e500011541010000e140803100741308c231420003811215080d040b142c048020840c80503030000000004000421f2071908a0704800c207151052001c9001700071a08107040c03501c8d44100302514020301e0300c4004101e00304000c1c02c0b544d660350300c110400340500c00c04c44a4075115400c10240c5000050107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 919498210 1250 919496960 919496971
    0x100c0623011707081e010b041506050d1401032108010b07031d0325050a0f09110c0f0a110303090a06030222080a1b0b2b0903030b09 58
    0x400e03003482820300d000000200c0500a090005501c41d001c90204a42001541d004184520543e00900724030524860b0510961114400395820501c0030308403030070688107210305521146803581e0203609052044030140d0113910310284541d2103d00f065008481c20450a0096100720002c4403890303101d058804110940e01400d100780540d0340c004001c2d43e001c41088030011070345450030342403071003000010064400046040a0b0503204010488010103242209110310742044403800706110b60b04c404100341e40809004d20424040310b6001002052030940129078905900124142041c0100c03880034500b0f803181c02d03d00c1c007035484a440d0109000d200c4004030401036013900594030b8403003080c011481c200d25134820704081607400940d1348090310341c00d40b082e850000c0030b1480804480d9590510703a5100010703101501c10351070701ea0001c0c2030103468099442c00c03210106d5806050018174040c0c007460300141008400d1546041d00a0386001e1154031610001e0340c429140090500c2c03104052000f80a802043c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 919499460 1250 919498210 919498241
    0x30b0d030903060f020705060f0103060e010c0509060d330506031501082208040f0e0405190f0c08010f06140a050405060a0321030b0d0807030f0c02100c06 68
    0x80190229038046401c4050320b8205001140201c54102100000d1144aa0103803540c0202824020f19001900313056040f01d020700320174081d51030310010b118203ca8442d0b4410012450400c4501c071070b4200ba8000d001480e880700070018894080d13030130354075042d65070045466203090459007403401d801401d0f0020f800340c10113540c07141c1581303090f040c00911911389503100f5041c420381400040d00840400c040c0460164560f1a1141b2a016880c2c817580c260400e008034055903962404c042807400c000700800e8410341d007142c0101254910980c18402c000702c40002913407440601400140440d144d240b03548001d01c591400003854056181c1f009088501d00d4000d140907862180d8403034510b586252140082d03410880d00040c0c0303520381c4800a031107078000d0781c0002c0030401d03d01c111808035440240081401c3d582500c05200648003002001034014110600800d411001d01161000c41c1c03080c003e912030709a981c00d20380ba585015030000f031500c0090140307210003c2c0092000104001d6280540d20a082d0207c0c0f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 919500710 1250 919499460 919499479
    0x504090c0305040c0302192301020c0d0f02091e010b091e01050306040c02031e09030616230d0e0c04110c030714121216050705060720120703030b 64
    0x252070008002d498400688102400b201e0301800c0c505003820f2100a004c148a5016000380c0c0b240c4a03c000d01000d0b08c5903025000d0517031400058144030040714402c5034408600310110845e6820000c090328050895107441900c101c02c3c4c103da1491000c0240030341041c0d651580c90f01d03c804208250b00c4840000750802d03001d1151154840c0e40c04c4001d070f03600054100d60200341c114444800304d1441c000d03c1d0b060360b04e03002441c16241d2044000d500505048500780c00b91881caa5a0710300640007440403500400004d07140081c4900502c5098071403503072500d03521445034601b8034808400800d0f50840022004140c0011220310158509441b440c0782414082c0052810080e000b1300b516142d004048000d0303c40204c9007440f0342551410b100028804c0340d580b840b02d4490f111880c007014801d50440c0c030000855101e1602010035802a000d0700c40d42d582c0321004007640c2d5541d144c115aa03c2003040d52004075044001c1102d072100c000e0026000707404000e40141c0d1500e1700d9080c0181600c404241c0c0034003d07030001c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 919501960 1250 919500710 919500713
    0x80d06080f060a0c12062c0f041203090503030f0f07020a020a090c020102120408031e0426040b04060e100903051b130203011d0903041d0a0e010c0504090c030504 71
    0x12034801d0344180c443c140050100700c3d0b074805071044514602e0412502d0b18021006c2031140c0c4000001c440b42941813a614026a0145100720401a00765800e011451f0100c1c00100040d23545154105850030500d0f021640ca1b40e540e54041c82e40e041906c0140380108018204052841c0c0741c3d186507840a254801058a4900303500840e080d20500e000703419000c2d81b01c0e5903210300b050003501120303a41c8240040d980c0440c82d140c1040202030708203a4000841d814480081e03040f600c030b11000507020b0380d00000c0305400c2c4e29000b40ea814585a851552000351442840001002e00000001d80010441c5071038002254418600308585042448002070a000414406002094001a80c4014485040c201c00351b0380d081c40d80081d244e00121459a64414000000071500550031003200101c628040284409078850b41b08550b120b014078001d002001014154160020341218103154004104010020b0110080348a02d42507500c13044000c0e01040c400542042000138500c1030055641c0b80d03240401071b030f0820703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 919503210 1250 919501960 919501963
    0x3010f0b011b05070b0703050a17062b050d0e04060e09060c1b12090108060109030b0a0209010e091611070609140f0a0906060e04060819030516080d06080f 68
    0x9050440302c1000d40600c2d080030040d0412119001d8030341c82181d65250b01c560b1900a1155003c05880c000085200d881040d892280c0300d203076409501c1c020141c2010400001c0c0c003540344280100714a00c210445030412021580038000003a5100e001d17a21456280c80190a101c10b60303c043d406081c401c11408104542080d02040c2550080528a113450b9901d41c01524010b104841c0081110345004541881c00942000c0008240030300c0c007030304c4240b06079035442c00541d07015001b4440500300100c8100080c0c002c071159170040003207080504019150855100214201886c129404130010200c080c5a03800540c010300314080300c40340c40000788a4541400c0c0014038503010340c0700b404c081e1501d608404400b81c0c0c0f4920004240d2001804d285070b120b54560840014007914410600032401c20030f01c40d0060704181c01420280d03040407006203141464035607100c003481012036098040020900001f550054081c1d0340e0841e0320300482c0d11940b00e10740d400c052011540b265000701c45640c4000030b41d07c00c0850 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 919504460 1250 919503210 919503227
    0x51507092c0c0310030c0e070e121005062e030e030c1902060d0504031e0f0e090a091a06010f0305130f0302030c0d0201020d060b0a0503010b0706020d0203010e0603010f0b01 76
    0x141081c10b9a00d070f0b00d8a81034110407003280e0f00014400444a80081518500c1004441c8244d034540ea4040210000c0400d1180a1210b114610300503008441711029280581d00465006500a400301801642c0c4109130002d070702a042c40094008131600300405210340c5400355460f8074414201035460051704829031a41d80e50714441110204180745001d00c04d541d50324081d1451015901c0060013213213401d18005014210b501c11044490307900c1004008800d00c01e1500301700c1400241c540c00c1d090407016017040f004550090880c44043e0302c1e400a00d00143c0102c0c03401003070000c59064003240c6e00300f4100150110700c0c40c0e4031501c00c06103090100000b0a4000448016064002c9481140580103040890551003005240e40c1c3c0d922410040b0507035142e0550007130180304a00201040780c2c5444a10107401e40c800c4041c04400542c0910050010030300101c002c00c80240f241000510f0301000a0110381aa00260700c5002c0d403102c10710400400e0301f02806981d0480042c0c200c1000315404032000a0040f40c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 919505710 1250 919504460 919504471
    0xc050d0e190b040507050904060b330c0309040608100f0b060f090103090b09150604050c090112020d051005011101090c1401030e0106080c0a0f060c020409051507092c 73
    0x200c0301400300781070200174809440a401c001d48031001510b00350801001521100140710300400300e943c005807414402c11070350382c80e0080380388100c5602c05001e002d8a606801100031842c660004000911142d500c0d441410020704441c1c01401c442c0c103e01e00d40008039880107580c18106420512a2485035580004580c46c503110074080680b500c1c0c40c880124002c00000500801d010b00840c1480220900050b0144208088991000155603844240001d13107200f503990144400040c4040c501c85d6010301e030384145c030207031458005040182c0c003080d100990b1025035000c0c07480080c114007030211b5607003c0c0000f05051100c1c2c000740090103007079848050078810741c0b042c0203540400c41c5250380d03540c0c800d0304a1282024800c0082c410b00d40c80b552030948903a40000018800d00d0b80240001e038440f8808486011100c0c030341c50340d04212f1142d400b4800549580d210464960103944010008891100401405140340c0e684122050b8200000640301101d0990186420480d0340e13240c40c0d2441a034007160f60b01c03c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 919506960 1250 919505710 919505723
    0x7020c010c1a043503060906030f0709021c0b031002030712060b0903010b090403081f3f0803130c0e040602270d0615090c050d0e19 58
    0x34074642440c56100020246020245016606120a204d006990450703c6182d03034144070000b0748010710751080d464035240010154201400011030901d001444154408000b600b80d83c84e041844113480d041419175000301c500994003081100802c401c40504044160949804101110700000002e50743c0c0316034200b00103450380010004042c584901c4030201404494032007441400d8036001032a02e1038210b2240207019620b0141c0f07980c01c1c4d2030b00c0300381c042c051601030316041c01ca511082c20744100d22400c030354801500e84840000107003400c261495542e0661107802011985243c55124000728206483c8801d00d0a04200c0c420700400c490108032500001d904c0c20101c05c060a0380707004412403145501a0082c6012101008184020764008000280c104510100d2000108040725100641c103801240c00150350030321580001c01c0c0da0b101c00100c400c41e10842c1d110070327030300c5040d5401d580009800b14001030f40851044080c0306940540700c00c002100780500101140c00b041084610714045003d4800b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 919508210 1250 919506960 919506977
    0x30607030203092e24030308060414040b07080402030313060305040203060601021b09090f0118061506090909051e071703090303221806050f01020615010309031707022407020c01 78
    0x10342803d10030b03007021080707505d10517845640da040c00343c841c0b00100d174800d0140e4105442c1c81c0a00c5808015148103641c0840d01035035648030450111105400200102c0e003502c820400d811280b0309801089004001c280c3c0d002c18140b5240c414542408400341031035040d980030310140ba81644100d42c182d14428416203038890190b403451701d45450314914000c0032016500c1e1100c00443c4210f0b00c0519200580148010310030078600791300044451707600d481134600090412506100105150700540300301801041103854030036111241d84840303181c084c840030050303016038030410803241101050f0f031030341405401842c01c00f080c61000c40d841780304e01250310b000790000c1d1081001403145100d080307024006409248650b5015091142d0003031042d03008240c03040000f007020003030b150310020340755100b0100741c04800300100f0000d0064010380030f0350f1411010712414014603900081c11274141c0d481400e141d40103000f111100e2f58aa0700010155031415042e84200302040680303a00041c0d50030300d00d10b0030310b01020f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 919509460 1250 919508210 919508231
    0x706031830020a0809040f0b03010e0102092e0e0d170405130c17060301090212101d03040513020408030a030c0305090c131505030607030203092e 64
    0x3409030100d40010030500320310442044040044907580071005221181140c00440c040081ea5925405503000300008030030400e0800741d0505402101c244940300c1000304400070f00b80006030960b1804180c0034440c0c0c6d4081400c0c1014a0840c400940b11070000710300340700c07442041a80c0c2d88440d20086070b810601c01e5602c20101113403601c3d401001b2968004903400c20360701c0c2c0350740740c00c9107a4001e04c42c59111f031000a420355000e68a45c071403840300c02202e444052120b0342c1c500780c049105000511450781550380d4412040580c50740700300b01c1c12031154100076000343c0c1c100c4600b0101f110758031602061815410549000c5c602400800c0702e096900840d6000c5980300200001c0020303201d285c2000c0316501012480310041501a0401c0000c5021610140302c01d5881928190780c860081d207449520005842a1401c51505507100400340c20812114070034013034403240440d1400030203450600c0026400810040720b60402d01c24a00e0070b0503214409014244181000c0194a511589459403030740e50300140e10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 919510710 1250 919509460 919509491
    0xc0117041412070b10050402180f0616061d07030b01210f2411071b0909151415011d09070f020709051b030a06050613150f02070603 58
    0x40381c00e070340451455a0f4102c5260900d040f0f2415100354883c41100940460b05182c640203442a001c50b10320201001c4c4222130030000070b810000c540d2500240100807014208a0090f01c0c026118010200402e0145541c0c400f000b08090700c64502d801608000f0040c4001402161540d046070040381c43c882401901081e50b440845581400514034004419410300f001003001204620100c048082c0280014401c10081502d841140b4801ea0328004c000140c0061950854400282c8a00f181c62034001e48a456803400c6940d1281d040c0c80d00c071090745241d4031010090080d0b02a0301016100003483d814544d09004c51060645145414410f2250800d07001ca000103107141d100c0640241201e00030300300400d01603c0405425150001806883c4012601d90b0103800350600860592001411210b4502c1000c942500081c11641c3c07056140c1c4000510340d03540c0c6001d40840400e018540d01040e00d0080c03180311a03280c1c0321004091210b0541865840c81d00803804108a52480c100856055008101d03c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 919511960 1250 919510710 919510723
    0xf0b031009050109050a1802010e12010f0c0818070518180a1506060c0503070b091005040302011b082e0b0d0203040c290d06090216050c01170414 64
    0x920030520b080d0001a243d100e0360080e50243c030f103034481040000c0e8415400d4000c80d040850207408a600c040510b84caa040803848100094185400000c0c0510741c5601e20064505030b8044c00300044c003440138032101c80390191056015080b0300e8020700390030349041d003c0345001060060f015011584640000c0742e1409400082d12060440b6082d6500018207160052450a030204400c84540ca40070001c18164011000c860302139801c44003c41c101740c0c50340c0e520882128000e01c244800e001e50070101c070b0000164040c290003039109400105000c20304800151905560048030000c01400e6003d00ca01c2441c2c00e0400c001c090301d40c805010703503800c0c105480c40302c1c49510707841004041c5000841d0109404a5806580540c1c41022140181e0780d0301c01414038080d6030305140f00c0c0031009003440e1780d0500c101c2e0700052031403070003800c008104550307609103031001c0360010349800c6c1601c07100c40414000c0050070710070304065000900b000300041119990f120300f000300091008020a4002e01c04411625042011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 919513210 1250 919511960 919511969
    0x815010c0c0519030c0b0a1202070204060305120c01200904090632060405010317220815010504020f0703050708040e100f081b0d110a0611060a060f0b0310 68
    0x103070100b1080c2640010f0701e140c80c52000b640c1d5400ba64101044401907801110a000202d0350b03080100207422003d90004e500c0000d040b03911540d110f80c004001441400301d030b0031389240c46403610344030018030400500b5500c0100c007100c028403032a001440c0002e200303029540f1222064900042c1e0706410b02c2c11000030030390407800481007c030f54128520000481d00019100c9000420440380c0c0e501ca031400d0106450302030100a003c4042d0744e100e104c0300840315014103459040070f898035100f4002c1012030199010341d60414240d6030071000a010a12041c400100e0040005940071858151451464a000c0c0282c0000404218002500c0010720241c2001c0d500508030f40c401d072002c40d0600001940050100e4802d4005000405100051411000c11507000e0200d4510441011211f054100001088909000c0b101064604201005034503110220343c080e10954490700c049064006c280d0b858144c0041c28401c405041040c00d2010b081d085041d503085400006100e610394440d00c0d9280000d1486410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 919514460 1250 919513210 919513219
    0xa0b030d14090a0e10050a080708060c030903130b03150a0b0a0f02030c1e070605031b0a2c0315010f030b0613090f020f04140c0309030702030714030705010815010c0c05 74
    0x1030000310089001c82c0006c036201202c1c5030a0090f5603020076034030b8218500c150f0341f403038200300d0000b40c000c454900250350100300441aa440c20038015010102404d0310f82203008050b402104012040c503030400c070702d128003504a4025681e00c1c680740c0d82c0705445c80b80395150403c003e02000201c003424001c0040e0f59002c003c0350306803411154a011446505080001d848005114000c1d00040300ca02440c1201d000e0710791101e00b1149500340c0400ca920651100e072624081154601c2d0741001c090952490b00140e40d07001d80c64041c1607035944200741c60b18484042950402103200e00400500203141c100c0412a035000a0340f8980e50788000005a02c0e560088444c40d0060506103c2820041c1e010702c169002071007280d20514214094060004903000501c0b001d84141080002c20707602e680000c00b859000400d401140e140051550100e030070031405038007500030171800282c00d01c0c0c6458103120b0b16014260a2901e2039070f610b866050010400260401c0d54103200b400e44001003445007284551002d843c0183c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 919515710 1250 919514460 919514489
    0x10504170f09092e08070504020f12040b010806010f05130c031803050403031d220f1d120a0801090b0303160302030309060c1c0b04090f0b0a0b030d14090a 68
    0x1344001c0e01412481500d2000d141c501e01c806000c8282c640a44090714036020003080c0050802c800c1c0700007540300700640441c1c810248000501c9900202c1c407a44254441c9940d2466949042c800501e40641a04080307039150510400388511b44420f291095442c84804c00825178000c88542036004210305040aa9091280c800c6001130681140041c01268440e5542e890082413003078005030710070200000b41c0d520030004600b03a0ba0036500c82001c2141c14072180301c0010a01e00050b00701e41120416901d20700d55a18034101410601030601c40000c1156081142514241030100000c000301c2d014082c100101d40c0e5001000c842c2d031410400d03900c11514121501041e48041c1c140a9038039002144c03d441c4502c200400154080345510aa0389041544429070070341700d0400e44103e02a08c0c0d52004540c03c00d66a004040c080f6019000554086000d11a0302640741400b01c1d124056880f95181c45010354044100b10109540c460010500b00701007024176508d42e00b00c00001078240846500c81d031111301848 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 919516960 1250 919515710 919515721
    0x20906071a06041a042d0c030608010903090b0a0203040b030c071407051f1e080f010603060b07080c0c19050f120d080705070f060b12010504170f0909 66
    0x1580581c800185090398641542c2d140410801a60490400ca003442d084c1c038581c441050030130350080c007413003c0c08100c280d584840600c2c10044010705003040585084c1c5840da0080500c7d018820000038042c104000d1051500030784010300000f03003522072510726640008003c84010f100b03000365000f400051072455502d00f44244808019000028241c0308080708000c80310203d0300001c0c1c92030407a403025100c0100701c50090400c1d072074110999480d400f8804940aa80b8448030003400c0501180b010b62502e800030b00344004009001d01c0140c000505143c074002041c4011003900050340e071083d601c0850181e5608030025413506007121003524039009000f0183c80b81404020751006010380b4015524202c901034a0300800c10f000600c1c040203001508141005c2104620614800d0b0f4480304505000c0e1400c2c51685d214109840300390703000e0b5203da0361414205c4003454403000b2034000007440300c0203001c0b60810340c5501031009011644400c1d003240002c0c125115104000542e0302c00e0000030011001071402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 919518210 1250 919516960 919516973
    0x29070b0f130213020a17041a090a03020703080a030f4217030408070305070905010b0403050c0d02040f23060117011a070c06030b1503091f02090607 65
    0xa60303030352040e8644480080c05a540320302419101e160002c06040c0380c41c2c0803000c01002540132a100008010345040c0b02c6031b0001e00986858011440f0f60a001d2164005001c2045030381d1014048190302d8200910070301c0441e600090002c241ca402800040c5d49620003c41034001300b4250200d400580e040c007801000c0f2401800c001c3c00c8844210104924140d2064951050080c500b8a505455810680140409041c0781c5a0481003910301045030310b090b494845203440d04895520403642c542c0b040c1c03c02d02140d03142d80110307401407840e40714a509140c00c5036501d1ba210780013003200d45e0260b00503540b0700c03055544a4020000c44958040d08100c440b054107400c102a80c000070000a40001681c00b2800329486556030300601004400750700c4203642840c00503402c4020480c0020701c540c2c030610130100400c401a82c0e5800505107a10001083c3e5003201c10f0041c04550390804011888060082000c080c1000c81c801c07800d03041720a2262810648440003a00030300440400580014002c10f909040024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 919519460 1250 919518210 919518233
    0x2090d0312050f060612040c0b07120906091a09030709020d14010b070c060f02030d1b080a0603110d14030a02010c081f0608130b191a0303042907 64
    0x10100c0c000d10081c0e0701c00f031494822440503100c030760f0400810008001007444039280c05801a1188980381000e40c0d035081c0540d20360300202c00c02d540b8001e0050081903d03a4024590f00c000303114900701440400c0ca4008083d00e01100801c510615060021301900700355014080d0002608801008648643c20303050f200303001f8181c1b06e1080302e86412000012820802c000306944601d5132001c40326407510300303003103040f04c144030341021036429807100303104281c1120200e016102d11030800c0c1600d24004100d150000b405030402401c403555140c0340c204203002244080c810040552425a030310b01428043d8503081d0145a04403521405601003c21045c24841d41900310902145059440400395212a900d046404804031800003001440240030080c007402070a01c00c0d4084541040680720300c02c00e451391850790340102e40c10000d0710102940d10748007002c3c503c20016125045d02c400300c1070307851080c00309a591185011f0210304c0708500760b84d0108121031709034a1421103855035500c5d85590b078510f020a08580e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 919520710 1250 919519460 919519487
    0x6020607030c0810152c090c032502030c06090d03150605160213140f0703090308040b0a0914010b03011d100515060c0f0d08010f03060f02090d03 64
    0x90a218202548602c2050914040d00c451920744410b5403400d2202e90b84500030f489030b5000e0000e4100b102082c8489640f41311031a8146c60000401c00c0041c40c104400703100b00a10134076800d0b03001d0041c0300850b0030480f40590b80c02e501010503c00c82408550a03859402040c03004010f910403041007142214020032901f25160380c0f514144250340140c4d250782d44124441c051400000c0c0700740400c0c2c09020300212410130390341c000b80c01080002e0010644c84c0a03106003c0201c402c291074034041c800c50302c4425505982c820520325080101c08c40382d6400a02d9281c0260010340055461404207080101d5544403c2105500001190100c83c4015450340a400311050181c400e51800d034112044041c0c000c59401d10081030000307004c0f6940401240e6000348009082850405180751651039240c0b00c500040c403000e002003009040600c01a804285002c4490048030208480030707004000201400710300d9000d90358404404036581d2001d4061a0003800b03100d0741550f10407100c1203980c0925030494024600f40c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 919521960 1250 919520710 919520717
    0x5010b12060f060d020a151d030c040506030f01090c0e10180207030e0310090c1a040308220f150e0f01050d0b030601031a18030712170106020607 64
    0x4960181080414200a9904032081c0c000c81c000401c01259a168035510081c000c00c501075800040d00420b404031016003028501c5010190004d003625040b08419003a0143d00506c007414241d22000b00e44ca07812004c54580c0240c2d120b00100365182e8080c03140071380c9000d0102c000c00400e40542894821078005114488444000714040317406d4103000c1580b102034070995200c0350201c02e8400e24030002940f2031707001582044002055413180e581c041c000381c400c61003451300c0819030001908240c416603240da800700c4d09512811000303a0062900c40c0a507012a5045003403540c03500b5000c1051380c070701e0396030405030256004d1401021941e1000b80e00c06400f5154080d10b105400d10300c00c002912980d0900d0b900b00e0744100c44d001400881c1d23200300d00419910364403002c003142d403541110129240140a0300120b844500c40342e0b03030b54045885060001e5100b0a440110b0a251051900c030540780d2160b40c4010300348640e41c0c01ca140c9958012407800c0c1e01c0c8074850401c131b01c503581c0da464001d48038181078800c0b0000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 919523210 1250 919521960 919521971
    0xc0d080d0c0201090f0c0512030a0801120201170f060103060b070506040201030b011218030e090702070b09030f1218010503070801090506060f030403030509071401080c22080c030634091505070501 86
    0x52140002a600200c16544862f20340ba4241100c4001d00034145904904022a02145072800380851456502070703111101c2111040c1410300000d029036800b50042305207008280003d8012500002d00305410980a00f03000600381d10340030040b102c504584040032802401c0900c240e0840103c540d0b0440b01a00955580c0480d42011041001c3d0035030541c1c000300140c0c0014410b204c400741c103100900300d452004003125140003980c45c140d420100190800014100c01081c50110441030b0703c0b110070280024a4407a24600d44120064400c1c00c060042c100741c1c560307601c0010f0761900c41408442c0d11841304a041a2285070a00d801405080121203441d96405506400079440313040101103800340c0d00584580d041c9555600070b08400740c12404010030000041006c1040e080b0b20070060801801e5460b015003c2c8105140500d8540b400c05000c9030054035240e120403c0c00741c07000c0d1001503103840d882000f0404c1c5860076000c441e40d202c03580100d80e4042a12600c0595950028020000e161080009008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 919524460 1250 919523210 919523239
    0xb060a021005070c020603160e1521040209040b0c09100c051e030a120f0e100e0105070c1709040e0a20010504030201030b01140d061a040521120304060501080c0d080d0c0201090f0c05 80
    0x6402013500e000350002190000f02d000a21070303030b403c50780c05008221400e00340508130300016500b04080013544f02040b01c184d40c0100340001886100f0000702169800303e180440320340b442c1d980c0c0c0b0540988004004100d00c0f5200204c0325500200460100910709003d1034000d04001034680140d0845002c96528004105610500600644bc072400041e15201041d0070162a5909014650f12032031007a000c0c1000120103d644e580300d0703e1390815104000340100005850a10560949900c2402000b594034202c40042da038001d0458044c2d80d0b0a00e40481d81240f90401070b02d00352030700c00076000d4400f404203403072211117003540c450303021640303d5561411211440040e0f4900c2d840749002e004d41014009d500700c2200c0d00d01d4a003d1080b62581d008132050403140074080d03141900182ea045406ca40c50700010003601c001000251007070b80c0c0484d40080401ca2564411401d03100700e0900340b02183e1101010300c2000d000f0350080d0400398000e00c0e120518000d43c0f0307102d0340210041c00340c4d5100b030003111030040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 919525710 1250 919524460 919524517
    0x41b0f0e0919110105090f041817190c051c050307180f030303021c06060206150102010c02070e10081e060106050f0313060b060a021005070c020603160e15 68
    0x100b046070041442290302007600c00441d22540b002d0204c41d0842640b521000513510355100d5030000a0031180076040c85c0c1c180c0d01e001014141c0181d5071034401501880a01d1085443c41c8213003814500600388004440050316105003030210902c2c00c075201c00c14803080155099081001903200b500640c0e40c40d8628440000319a0303480f01c3c14020000358600859007400040d000e503008282c004400308405500c200251000e0054403140d40040c00181c0003001130001e410001a1764141d8200700340000e0050908000300290340c0e100e18841c00038400000e03000304610702c0e12140d000010780741c01e1f81611007106c0b0491009a2804c9090300b03a4055119800000582520810985900e9400446194a07684822146e4854803041c1c85050710050368036800e0f1811540c1e818020320300811507401410007000705461030030856100800d0307402800111034009005940f81c204aa9100e9030310300c074201e0501c000300c80c11641420034030700c265080b0f00700b800e035550005083ca000d0101c4030445110b41204182c041d0000d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 919526960 1250 919525710 919525753
    0x60103020f04061d040602070807030c060609021c11210f18121c020307031d0102090607030c051204031b050a060e13151403070914041b0f0e09 63
    0x4d45001075001e08124240b07112006281c03c9401550098200001910703410120f0b80010812004100ca02190340104841809440001d0264910071424000301c4844029044070785901c0441050780d0300c0d0307a01e40c2815420140c4405014407a4501f0000d080c2c00036501c1e82031402da90810500240d00001481c032200520444040e130040b0001d00060301542000d40465000030380510404901881b04185040c0c4900c0a58442c200950317010524a5000c0c90780201d101c100e01d800e82d00360340100100c0c0403a85816003103e0a0136414684400d04412900300f041c20304903150000c20f081a00040d001043c000d25003600940d01c004600340811165a480401554403014480d034800314401441c0350301c0900c0c000e22a01000c408102000c2066486952240c0010200d5007102c9243382800034030030078034107040100d58064580b56800b003141002c038844464400900900007405c0031900c6119400d03440c1c020320407200034517004840780d074056100e108024141004a41001842c81a154001600e4030b107607655 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 919528210 1250 919526960 919526969
    0xf140708010e211e120412170105061b06130c0f0f05120f0d0f020f03031510050408120d0b090f0403110f0708010c03142401031d060103020f0406 64
    0x200f2442d0441c0080c0380f4650f001314101080e801c01e01c54030720f54003540d88401051585035400d455206880c061400000b1841c40881d248100584e4411034000552060085410341741c01700c60709510b0301c81c1c035402008840c03211011070440c0e02030a03081c00340c801081005928031610501c9100116074498000e21811490707449042c103000c5460b8020011070074595a01900003d4000c00d5a60200074070544510309a508180d400000303000c403442070180c0307606100301800d920700d074800795180d42050100880d50010f24402d19118008c242d03c568001c5008008a400624aa10641d8418a06401172000c1c68000c0e100d1411010708003c0c00d80205d14041a03290320480341d4584d0702c2400d07280c90702d0480b10700b81e01d82d003681c0e030302d00c25000140c006010400100000b0b000fa400040380210b60380d0320040684006420050154a082d010b000820400e03404004100070b140c0c0c0d0401c101420400101c0117044842d0340d02813044441041c1c0e483d045008034246042c2c81c029902164024010f10a0004442d4184507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 919529460 1250 919528210 919528243
    0xb070b010603090303020d09030c03111204230d0803090d050c060403030506040b191a0903070e0c160615060815090c0415080109050c18010c0f140708010e 68
    0x40c41072900035805807210501030f140050410b03003c0c880078800c650501a085d40410214804a010543c0c440e2540e10740200c081c019003d003035100c4e5290f6405010354060070b03000f808034103500362040781540c003507081c2d440300140903135015013142c10301c411282c0c000d841c0b140b000d0007020308d000c24140c0100d044030454900700c80100101c0d62292011802843c0140010394000d8440441c1c1d40c003542ea00c0a4062040340004162200394036043c03444841c8820901c0000150030148003102d1f0b50780e0b010803008200da81c620381c1030405a503010a1801d0310301c9500420112501c40072150f50900c20300ba4001c03403040110b44074460b60306844250544140b003044500300e4140c50981600c42d084d04102149640144042c2c84d03450500c2d483d086020803417003071a40e2980010b00c050004024201e480d02640d50050130f003030713141c901d00008811600d07006102c2440140c1400502c12500b410442038010030f1102c0398200507021540300032070312130030303100e41312440740c10140d40c2082c48088605001195040c0b80aa02c100e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 919530710 1250 919529460 919529483
    0x50a08060f0a15020c030105090616080c0f1303020f03010510150903200a0e10060e011b0c1a0c070324020301031112030c070b16021306050405010b07 66
    0x4000e50003031107107501a0410020180001c49261082c803240072008550090500b030b100c610241807c440c1d0062506045500038014848203511050490340c0c50384003450150701903a40c01a502046229180014400c1840000e01c1d007440341d040c48510050b02c3c400c885d422240e80b109001c0500b66002520007030460481c1d10010015090010a03001d1604c2e8507050008620340c1c1c9450b2907030045100350410840841c0c3d440c0b4183d4502d804485507024000c0c01d0302c0505107042ca04c0341c1d100e090040740540d07418804030b010b16212580c0100c0c102c1c0a641e507440d1086009264614001c031001e0480d11031004d4022204181001103140c00b025250b5180300d9a004100b0245182c44100c184080001c500e408504460000084030b02d0a00085000c0c600403440d205580310b90704240030b0540044000180140c00900440203450004540102200c44045555440d0207d03a4460803200b030080340001d6010210b10315100141c5c0d40c941000c4101c5808035400c10150780d903107400d504507200741040208018250f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 919531960 1250 919530710 919530721
    0x190503030f07110727140a05090a080f03150d0f060e01091106031018020c0c0f2409030109030e040b06160303090303320a0b010f0507050f0706051801050a08 69
    0x17118000000da01c00e6051107450792200c001c00702202c001480c8550b2400348581007200c100d840307006003038100e100c8000501d121000ca841d400418000c405805103c41d40004c0031a420b503c805a004200e0040140040c075054001e24080040c19040d900c2105c200e0304210070400200c2061051680813900f02d801b204100c2c0015080003001c0d030000705100102005114082404200c03440d0205880c000c41500694030f800e400b8505160584400280b4842c0c00c00061034200c64645001c0003000b0348551280e9540d03c49202c2d0006040c0c001d40c002070343c266181286007014550702051109075418180c40400290916200348180c40c40782445101040075041c0d04a4000382c0300742d00c030b400e05034064a80041c18041c091620100c4846030340f00e411908110346440e001241710705007640d80084202e81d080003000303a118000381840c001100000d0a001000c100703001485828007502841290300c500707071903d803a25840c0150482c0c00840e00c894641d2144608601154001c0d800c0f96801c207525180c11509507a00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 919533210 1250 919531960 919531979
    0x20d03050f0126030c160806060a030804090f09060c03061d0906161806030506131a270403030c110111031b1b01061e051c0203190503030f071107 64
    0x90440c3d061a5100070050a40f40402c14841c16048401c454000c801e80d034980007000389040c03c090310481c401d200815003000007130901000c075411503840b40c60114111070160304183c0100b0280402405203402c0078802c3c021070b507240e44684c00b95503038103044201d0041c0d034404010341c51100311003861050748a407012030450140000303a41d517000818503080511410841c40020125151360048002c40d80728028810b4602e0425455111002400b508008a602d03c1702d842e00040c801d416010f001d0080300440140e16800000d07507c800d020384c1001704036541042e2500038018035121021000080403460b603050004818081ca14421109000850468480441d003921010103149c12407603940c42001052545c03689005580340d480b0886000040c02858850940c101e103a2040c0841c1011501c0341050015544881101c3c490010040003440d20050b1403000c246802030414819031800820920042000030010095202d103a2550340d81c0c400781c650000039207181c03100f28101210b0f40c00c501c4003400185035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 919534460 1250 919533210 919533269
    0x60a0803030603250b040b040e0708060d240908030a0b030f0a111f030b1e0306040809060405030303010909051b0f09070203041d09190507090e03090a06020d03050f01 73
    0xb482c213003031412a039400c5c1d1500154481da01a0103d4407020908102d1550000f48150b88209207003849146440c0440008071111385180c0018542c2c00200c108600440901421614521091804000002c040c1c1000c0b803160f0400c0f5040c040316070415080301040d08010410f0012415810000e00c80989555034070070710b01c170081c0c0c50a0780040f032088950400603c40e41940c0320440c0d040c0c500140001803c0144899a101d14400621100200c200d109050f1000143e00d030707009400110706a02c2c1d11031000013030180d00c12640880d51600c001310001c9990401940603030388192050b0116001c48012861110b802614401101e500c902c211140002ca0304184445550007070961040d40c0c83c00d030b201d200000c22100b4216180b401c0440c001c2c2001b12036030080100100c805118041c140428481d80d45496030b811079405103401030f58a0300380420340d0140400c251107810030002e2000407100c3d1100380080d65400340e203400f0740000341414082032441e180000c2c0703123058801c00301c00344100d082000810041c012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 919535710 1250 919534460 919534513
    0x102010219030f050c0c030f1e07030203131a09060a02100f45030905090f22050d111603030c03021b060306040c0c06090b060a0803030603 61
    0x15020001c00800410001549103103401d035032400103e07001c0400310402298401010358002c800308104a441654000041d178145001d040724069079151003203000f03040740038049440e0541200100b44801056004005000c01c8680c02c1d402c008110b42d10481c3e04103541c00b00b5003c200342c0782e04005140c00307420004010071505940d401100d240c00b07062035080d81107e85031005144a03582d00c140b680e1402150560316500307403455104414490780b9401d10004002d01c80000d108901e00010301400030140105541741c003c0c84024403d0303034989402501b1a0510008a810108903c603c40700580340103900c0515410f000c2d00710380100201296840305031004511803070380c1286841100c070115501c00103018020b0182d0310a95800e0f02c4030940d440c0c0070345448000172070b0082d889480040c80c90039864000070740c0d40c004802c4030082a84a051001a00c00d11080301000d00200d0400b80200140035030401100e0241805907103d20b555550360f82c0464480c08155501d03945074201c0d00c200a0740102c10940440d840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 919536960 1250 919535710 919535713
    0x90e0606090d12030c18060309050f1c0305010902160201050a03022b050c0c15060604150e1c030203090609060937120b0a11040303110709150b03060102 67
    0x62280d0000300b40c054241001c40e58882034140c00c01c01a40e041c01101680d80c4141044c0d02c0584000610346000c00040c000c0300c00301580c445081040c0301d0300308a01c0b0000c103011004d450280c024503609010001a21001502207814003000141c50070aa20854164050b1007540304000307071003a801126180d00ca114154205a000d2091040745210004080c488554400b8101a00214841c2c6a41600c0d0000e00324035020700e080c84400e100700e070007243c07101e42416048511a42691904006041409142c2040115011850b1500381c2d040d006106110024000c55200c501d07441da003600b200c2d0503a100307400200117070014000200181081805054044c0c030007800c0b60b081000441c0801c0c04030400350300201c548070b84501c1d80010941103410744551340c075000380704158540c101500c85169118a00006100060342c00011b090f40442d84d2040681d480d00740300240da1944c3c0e9040040c040f45019610342a01d014112000035200068410780391103582d682000243d85280c0b06c0d07903007019000100b895056 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 919538210 1250 919536960 919536967
    0x16170106120518031c060f03120e150406021609051005010c0f050a0f060f020403120e0a0819140c01081609030218090613150f0e070e0f0705040303090e0606 69
    0x86200c24006400c81e9001041d00083c07142c411718840d010380d5696481220542c4400e034041c400300d5050201481002d142d414030300591a10b52000c2020000c0d401c406c1d0411650100d07011582560105072121041c102404454100da1211070741c0044610035100c0d84007010301203000b085075500541d07141c00f0b82e03402444e400c032007500d62b03840b1a41007294001c0700f107803003c01145207803080295074410500d0180881d070046007401d041d65200201d90441044600510940d42003d03099640d5400c0c03c140030b0300701d4100340e80107428182035000c41c803868001c040303562264121010204080009480400080c141d407400700700d49604040302030350128a44802c0c204031410101001580740c0e410002c501c8003989001041a240c41d40701d441c2810300141c0301ca04011499102c04c00401d80420303204107203184900002400c1c504e18034505004010040e2206001d0042c1c01000420407560300c055031240013407801c014003a80e960b00c0110b41b04e200f0f602004000c180000c409010070001580240d40c0b185016003000d18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 919539460 1250 919538210 919538251
    0xf0c040e0a140f0d020a0506060603150406030309051005090a0b07031202031009110315090604060306090b0906010e0108030d1a120706030b030307110409080f03161701061205 77
    0x4404000d515140d09a00c607042d41030012508001e011004e0340d1500c06441c4800c8541d442540f0b4403800750000f0301c0350101001189000211003500000104004c1003080281d80c0d900c1d0192420049104091240035032021141206010f8000c90311008801400c00000904141c0c1e140101d40220200343c007001021003012a2b00c1c65a4401140039484461480d0002c40c0f5008240043e100e14907200c4001000601c140007880701d00354208841820102c58920459030b48a0102e0b00400c0140e0001c1c180034108403110050000091340036028180480c2900c055a0700c41040100d469001c0c0b0410710981d10801c8080b08102687c0e100200c030350100070001d003c0490700c00004e01541c80031440020300b134110520030841c9903058402c3c180081c40990155091900c191901220f198400215030b005580710503003041000441000c5624030303180b00da0100d40300d041c80c9151000d041200700d08400464044040300c12100d8030401002e049031a00d0f55410070007000b4241c051b001e058054800741d076140303140700483c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919540710 1250 919539460 919539473
    0x1209080301151b06090b0c25051f05041703010305070b030c2107090f12020105090a150c11090f04110d02030f150a050105010504051903060f060503010b030f0c040e0a 73
    0x2540710b00a1201085e20340c414180700030301840184c03c911040c60200500000501c900c40f982400d24520102c00c81e46010a003010b27401c01d04d1101610288441c014101110b480c02648814001c6e8066008210300754202e100c04600e9110a00001d0700b02e80c846c02c070804c22000321000450b4807800e80040703c1c0c00c01088150035110507179803a10310301c17038284c5007420001619489020100101440b0502020080c40d100c0d49000c0f150f8072100203410803000040c41e00032615569034020040c860380405211500b0b01c4270005141085a100c2201d0000d018098403019107865505a03000d4a600700040203240c85075952502c11040d280d8640d500711400544e50307c00350780d050008458102e028000340c451105142d10708105540c00500b240c0034245044014016642d0103420703031b8203994068403030880407038a000081c0a50180c984c0000e1080c5d041c01710601002c011a000f601c12145d041d002488009200d108050311640300300c0c03c0c0155584002e0603140b807454683c005e0f0000030050303016038065a0494a070b90 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919541960 1250 919540710 919540757
    0x30b03150109050601020606010e010c0606030b01080309100c080301121a1f0609031505040312090f0308240f0a3812011a040803070c06120908030115 66
    0x20200c400c0c69000410046905000361a40014244080e048a291a070b0007e08403c20345050035040080e5a024a41000030360b60200000d1500070810200d95a545c4415540d607510400d0143e001e0303400ca1200c01c2401d405540403c007500d60250341142580e080c0341c606c400c40302d0701c4141035441d03000140880909100748501103020786500c3e46410450310914003d580c03078900a82c4150300300705000d40204081100c03100d00c2c5c84281e00d52200466151a141011524009043e42e0b500764245014142010004062320301c4620718400c2d2038042e0035036241c054030020f01c1c0c440124002d80c02881000e8040503d13041c0c0c1c0100d43c1e100c000381081c220940300d1504001000c0264986500c41030520340888083d00b40107180300001d0701000300d00e850f004d00b04000001e070520602c900f58032503034806036407060b04402c1d9007550040c01c09d640482c2c2d280c1000c1d0403c010500054030031100070541010907a54165800d005445e60b446c1c0002e40d00c2d01e0360b440c20f110a2401c04242c0200c400b00b1103590860280104000d035207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919543210 1250 919541960 919541983
    0x50a09120305010303201c02010917120f06090a2403110915150304020f060f0a1e0c03180e0f0901050105040b130903120f02041806140d03030b03 64
    0x81641c1075240107001078a080c0c00c0003030009031100c04410f000e500081c031241e110001140600c4007da03110b0045e4098620342c6801000c03038202981c200039482e06d06028211500e0300d44150f03400d0b07480c1d0130403040d5582c1e815580c07190409034120020f1038801381500b1011b031b400103c1c0302c1c241c10b61508031002d8021801340e4208a420704010300000d03401e49072514000d504100c80350302005909519100007034142921501c08000c0c110081f00090a650b1940b21940c01d04078041c00b01c2c0e60741c103101600c490301c540c00440158041490085031035114011056030610704125912031885200c029181628540b000c1c40502104654041c40070030000c80b250001e0340913101d0f43c0010080c40c2010790f0000e007529030503000035004915043e040100741d501c018800342074260f001e0000034a0302090404960000701403c410300d5003410120b0001070014282d0051040303503054074000620880e01d000e030b24240d848510994124515a0480003114540381c0c1142480c548a418000340401ca16004a400c15500c42030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919544460 1250 919543210 919543217
    0xa0201090c051503040b040f1509060e06041e06020f04060c020a06020303070e0d020102100c05030a0b030a0c140a080f0705180405150c1201080a14070612050a0912 72
    0x840308204454002400040c00d0119180404000e4000b0400c5050200600141000c3c0b0301c04042010b100b059003150312040d800c51031802c400c01c483c06040c000340c842000200c1b440c51030000c000010729800700d55180926030014001040400c0c0701582c51023081b80141c10799440e039081001d02e0180d2500f10040c0000c00440d11003c00c0110140108400139107035a1090095400c208100310005078055400c040f201070031580306d01c1c1c503401400101c2c03808a622184040b41460007080322025904000076501c203090b07034003040c09503840d40010300d502c840002c2c0d401885003400b44e405000380040a040b0b0f400c101c101524410100d99960005454014081c030424242d802c02c480c00d10540c10a0300390f041002c04407540340c21490038255035165a07420354401c49040341030307540c0101c0c1003055000102d4008000003d85010507584840d041510b034803510004a0303503601c86114810704040041035500c200d5900c2e84854140041c0650740c2005401c00030300c0d80c0045541d44d81c42c580095183c81e8040f4801010340d6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919545710 1250 919544460 919544471
    0x60602031e031b0315041a15180103090807061d010b060a020c1017011e0501030219030f0b13020c07080a02030601170c04090809010906110c130e010501233f030a0201 73
    0x3403158141c0c91800c102050ba43c00c00c0504c6c210b010380c278400c08a1000c28a400030f0510b5140c10540c28902a003c1300400da681007540c085000701b000282003680c00c150710002c002c020000d90401080c0c1c4600c8800c600981c01480315101c062500d120b0a120041450902d072036243d040c1c007006520280c00341c111030300074540203188481c101c80040e070400250600382002c51170804c039005044080e0019100440030151244110341d00300e002a00700761000f074400350480d02c40d507806503c8130010303411940c1c10314000d1085080002e000340001650750348464002d03000d070003681d0806034000080d00c406040c6501c3c910900e41a03074001d880780c0c0f00c0c0545a5004110454403180c00c1c0340014600d800c254461810468810061280c01102160104400704200c13410840000113004e1040a09110300b9007a03090b5180400004900b407002801c100b10495003000c00c0b151700407200800450818040c174041050807a082d1078045105581d200d0070480070000f01101e1200ca08048507032843c0c0c010400080107035141d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919546960 1250 919545710 919545761
    0x100509130b060d0308010b031f170105100b040b0a0507150c02160f0623040e060907090b030103060504030512010801151d06061c060602031e031b031504 67
    0x2100710382e0300b00d402100c50441d0444941c500401c50306041c010074822170000000b003607411100d56a08005000c06000400c0541d68800c421131050b1468200300b0582c2d428400021809402040d440c020b032042010320702e00f81130401e04030403050b8201d599150180002000800c002c01e4a1520300c550001c50742d0b0340840c04003a07005d00207091402c0c81e582d02c40d00014900044c80214000e000640554985261402142c09004203100d80c0d10303905030a80c1074805002802150700960480031f584074842c1902e031240d06449280e011100d5200700c1c1301e480b5005c001440107000140241d00311681142c0a440c01e10f00f006401480951081c0f402e07800300c00141c0d0345a02c04a00810341142600050526600e141030040c4041074508102d00c0040c001c0d4441ea10014000c1420307a840e0761000c0c5840002032007004001c0d1074140180d9240e0100d400010b40d01c0404a24400c003448840c1100d01c102d01c041654028980c0c500175a6019030009000f400800c2da808250300c22581302d9100c1c017880c180500032405400c1c01e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919548210 1250 919546960 919546973
    0x50901061b330b0d0816020603101d04030e130906050a05090d020a0203030714190c05030615031f0f180b3304060306110a030c0203040612020310050913 67
    0x10410a407242c1d40c02c00e8010301181c1e42d1207164184a54009940596402d40701300301300305012016074000c1d0300c600b02109010810074025000410b480321f2290328200d0500e100c28801856104490041c0002d80160100722030f414950001c03e0401580c000118610002e950344034152102240c2145e4082d945100b046001d180400c00c0340c00002c0c280c00542a600740d00d80100b41c503407092510191800103075201d9501008820011100402c500704081580602d0030328020382c000e24588150707446403042001142d4458010504c1c4a60031100070014044c1c4909404155100c10302e0044400c0c080d0740c4d502c005902c1405034080c802e071190401a48a100300094503207040341c040050004546205044051185c0001e00143d205152546c000d103030400c5a071281c0000c002e41001e402c014001800c140c116191b0a03070703c0303014042202d0326840c10300664441d0300c4e0032a0b03240124884c04c130004a8404214040c01c03842d600454202844080400c0115165004030303240c40410340d412011050698006020b0051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919549460 1250 919548210 919548293
    0x90e0d03061406092106090708070609170a080a02280206070305160606030c0e06030d0e0112021b070314010209100f0c02091503070602030301050901061b 68
    0x2504041003100d0602030008040411454810f000b020000703601601540e803044c1c211540407004800030004020a100d0390b48950b0709454180c00d6200e800c00108203201d000c100201601c0507039542514842c40c242d80c4c25034144400d400f0010358001c060f103190200340c11400801c442d09254008082c008042c50000c1f0700010483c4094046060003401440140d0761700f4221002c20750149001c9407070742080c205860081001d080700806062515000104102c0c07051201c20488850b04a4860741d5510b820905131a040200c803401c00141e0038044441a542c000c40310f103503070040010001030600f01d1004030403420000002009807250701040c000c10400100d8603c0a8042001d42c000f541003845480200700b240e007002d081318040c48100c42c40704100d14032900101e1522500180f03210b10b9402c0000072a000441c0001107203000e800f880e000030941a00010859048030b00240040783c00744e28141003100d401610070305400c440e004042c0703108041000501e41500c50081440c00100d46c611201c4c1d1000703042c6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919550710 1250 919549460 919549483
    0x1e051305040915050727060807020a02090708130f06060509010807031a19020a090513090308161103040e0a140601020303040f0c050d0305091905060f0a020c0a090e 72
    0x41c203200c8038100258100b80c2d181c0f80c842030b800c000709094440007070990325500400d6102d400181200b2180021030703a8014071908486041e1155441522522000c0343c40300d201290194128000e0790200300b400d0b11a0000715400f4801c0303e002000030000741d580300130404141209940f42501c03444140300c81c1c030f82100154010035215000782041c600d950350b001450007900c03106d800c50403840c0c000629030706150420182d40c01c1640e2011999810302e080040d011a80c940211801142100c5100b031013051039100d62615950552902100380d5900c0c20b03130f4200841c0f4840e01034104030040c2e407481e1501d48100f002d0000741440c1022104c680c5040320b841d408450f400008101d0402d042d80901080740d8000c02101e4220742c00494190701e614060400c1007041041c0d50086412117200d598100a06a00002900b04003508175072518800c2c03940c0385985020703440c03401041d5205008001c91200e000000005254041e120300540d43d20792020f00028180c00c006501051600391280000d4003002c5042c020380c00004e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919551960 1250 919550710 919550719
    0x20d0f141305070b0901051e0c07060e03070b0d2703020c2e02070e070c06050c0304240b04060303081617010501031806150810062102011e051305 64
    0x1d9036580c5441d030341d4000511440140113400914002c01c1d900c5242212507462050705184100c1c142c0c041000002c2c0e010010303025190180c203c0200300c4600c61480030034851401001800300034207000d09110550b00c14000603280b00d55505c103032015002c80c54002903182400c50b07103c60240c52103080c003034200306400121500c50300403866801c980401800c98803101d00040e604d150745000c45100f0030303032a10b10039420050b1000c083d8010070001c241d1082d55540300d00c0c420306040c849521035106482c0c40c1d0100f40c0d00240110082101c0c05504100420385184040c0c04c5800400e010010202080841f12180c0094002452290802008690790031188075400e045251002c0707210104000201e402c40107004650415444268072070180d0f0134080761240325500120b0403c024610700b09030301841d00040c405e9903598012041d10a00c239000a10450044425014a511044910300518020300000150817414010000012000480c1d208594086003c2ca500c880d65241d0151003000b00d030000992120f03209 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919553210 1250 919551960 919551991
    0x40b1905060a060c020339030a050a0b1e0a0204030210020c0a15140301080a030f09080d051b10090c090e0a0204020d0624081b1c020d0f14 61
    0x169107592800d070701181d80743c0c0741250643c03004d80300003810082e0544100303183e1140f21030004e050100c820300200aa280c2d02849610701e0b05000141516a601400080c00d41c0d000001e500022a150381182680031801c0049800302103080c00707134000400c1058070380c051700c144e01190a00031420900d05109405026000910a5015a4001401c4885076004900c00048000c528445040c0200040701007260001850b58807507031034031191030b59a1503000041d8002100386100001c000d0141c0c0401041e941604060150307440b4a140c242c60982c45400c4050303a6005800c0058480c007418400c3c00100c070f05100000c01ca040b00c41c10501040e46454010400e8903140803942c2c40041c800080c611740c042e0341070b90090380710f5811200c03c100400741ca03407000428418070704240c0800031140400181000d0251a0444951174031070718208181481542d043c5109801c12105030316281d018000b400400111001500d00940303074000d802558502e00c85112043c0e21466520410742000c1e801c01e80c072075400c00003482d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919554460 1250 919553210 919553221
    0x406050406260102090402120412030c0212031005090405060406050a020307021e010212070f03061e052103160b130b0c0a17010b030a1802030d030c17040b1905 70
    0x1582d0340e0b0300315007070705610b200700c1001c8900000390181c2c1c0c007082c4024411034403161030010400103001d04943c100d85049102082081c034a00922400e03101410130390081c43d0003600600400a81e900c087d08050180190302000221a40c40b8900c40344203a106030040c1103a070410340b8052050741d07001f80c5800a91401482003003c41d6a000501000c0d4040c42c01152207a0000701c0001802840765011000303201524500300440c07150018007100308003550395000c12910360f45070000e103026085600040d0701404500000c0000d80f522070007030b5816410806620980e0849200307440d145500010840101d200b10320b00280500402d103000c80d03408101c1d480c05c02508025a0341701b249840300204a42d802c0400400d000664611440082c800a49510725903c50f07961074904913145074104071080c0300301c40d051600e0b15850b943c040d0000221603074060003c0940900464055000d844403030346060130400d8040d0303807030000920084131600a6005811000b81070901b413102e01018950344124001c5141400705005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919555710 1250 919554460 919554479
    0xa02040f38040f0207020402070f1a10030b0405011b0201060609060215070305090f0d1e030b0a03020108090f0615040b0a060507410105010503070e010312200303060406050406 77
    0x51041c070300b01d800103070f502d000d0107000e07000340141d28000c1d41003840495450104448601c000c10241c0c0101d54150180c1410200d0720b41c050403c0300d82c0300c0303070501904080001441046140340c106100b2000860300c002c0d17520107a14054a00819607005030b446d4502045070580112001c409010188090f004841c100e400324591008080c1c41c25003010b60b40e0002a003070750003d100816100f098a026908640c0301018000e206e00b15049880000c05142100880814024440d2038044c0001a0010300568659001580d518800134184101c6004420340780d42c07485014040c540c419850781014841d40c81c403100074001255208064117019004065083c041c0c6034220341070391945540a02d014020101c12060914580c142d014101100780f594414051219404001429046001310003080503a0341c800815989071014800e884000b4055001403001c5190051500541685818215041e01204400c96100b01c4541004020707500007005021042c9050302540005203012103082c0802ea0801e607052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919556960 1250 919555710 919555811
    0x8010e1003021e060c0106150314130f020d031710080d0c02190602150c0a0507060f060515071403040b09090417030907030b01060e01050d0b030c040f0b010306050d230a02040f 77
    0x40003062440321240b020071040f9081034103250f37800b5058051040242c80c001c0c04040d60003900f0385115080380d0009100b040c902d20880101e4041100405c05c40042c014190740e4840155016604021425000e600400c2c0000c41c0b5001010164001d081c80600c0e5502444500805000030403020000c000b040070032580303c415214040e8114a002844a41c15100703103000b0a11a809150464218292502110416400b4203d142d0141d5000c030302c0c880600c0314075a100c3c4030300e01855050fa03c00f40848266420011141d561151145001d03041112503903140055a8008448881f019803040c0b0302031003040510a0100d006107520b003859100840103000103440c0340101c00f02c00600c03995840111050f0754040104003034003034015000300a512a44054070740600301400c1000c0c0401d080060014860400501c107010050f00f002100700b0466031030360199152502c84030b45000b14451a0b1075100540d0b1180304000c0c054208c81b000054441d002000c03441003c4144804200a401d2402d528611140740d2088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919558210 1250 919556960 919556971
    0x40314070f03080318100f0b0d120c06060b0706020901090816030314090a0f0614040e0424020f040906060c050d2007080d08010e1003021e060c0106150314 68
    0xf010748a0743c030b400c2d01c01c0d410701581c0c00d0041c40340f04049030385035850f00940c4212080c803c3ca40c0244103040d0041c00b4132191000f1594024003409000e01c1e034400d501d101d0409401d000f4070071300000c207031195502001c003480d41040106940302c5900081714465583c00c28503101c000c1c07510f00068500c03403040e442d20802c108054407015043c030080c58004110780300700c0d401310b590b5108018204200d007501c9090804071098207029103404500090752100c00040000103031412941c00e210140d1082c3d40f10754964905d2000000d260a03008400d5200b205100f1050000c0c2c540400c3c09082d8980b2985060b10481c156049503001200780020740c8400004584081004801c218040c20100e40d008054001c541d03144d84000f010004031701a00b80080344a0501040d0083d420f5403e80e10882e541e62119440ca907000c40036204c2c0c10820382034210801c0141482d0b5645031001445100f601d00f00e01d5154003088440d40403d1503000e07980d555032401d010314500781c0d084981800c11361a00304108803400c65240b941e01c501821 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919559460 1250 919558210 919558223
    0x1b080109020d02070b070c050105010b131205030405421b0f10090c0b0c100b15070510050a020c07270c09060806100c110a0506040b040314070f03 64
    0x342c491210320340d034040b51540e40d88102c068410b0b2070b10310b0000b0040703441c000040b5155400e01c0c0001400581d807106a406441c0502c110940344c61400e015080c0035401a403040b9000c2c0070500c4002020f55401826001c00a0f90b000350030518206440b42e441a0350000507440070400024000c503030b010003010161009108006241d640c2e549081d095503140c181c4032a103860b028403948400c110105050381040700810f2260360420704158a68503165a540503241000341386a00501c400ba2103200140c0050074400e1028000541448a01743d80060a40c42041e0545541d400f0345100c01603209a4410150322640c040001c5040c8200058103e46484a521608001d9185a048141ca200c01d583d0280c1c60014045010401d40325118806004034000740b003460046060360000441e2410a5a1038440c00f406a59620040d42c500f60345500d41c000c07044041d41d0304503100c00408640c036120313600140080c1c4641c4403181c0d216031035450107055116002c60310b29026001000204180b404040d805000e480c2e2084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919560710 1250 919559460 919559467
    0xf0c070504151403010f0c030f06091b05030a0b03030a0504060f08040c12032610060206060607120516150c09080316080d0c230a02102d0506041b08010902 68
    0x700005d000d081d10300d418900c114544420040010b425521000082c400e1480510040d80c0c4d070901d210484000c0000d0070105500800c101040c10b104800071544020a07800016040300c0150119245803c011150408184002000d00c001c41d042103814400344002c0c50901141e01e065620701c02c0340c0005128420311241c4040c054000c1601540000c0c52640f590801c960b002090015000201e54080d6008008060408400f0501610104099214500181001e89055242d5440030382650319192110100401803100030b105000d52401440e100d800b900700000b030b02010016a0040b109248036440501c000054100700780c10011056490f04a44d400c20445442040d080c0072550344a40100701070300525182e81d034080c4070340210007481513090715022040c21319010b03090108107114450714036016a012440c915101c02641d00810640d001c1c41030b0903d80106042101e1030f500401140b103442654882c2d00b00310903410035119031a04106080b00c11303411019102c00260480030103015283c40f01d90000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919561960 1250 919560710 919560749
    0xe030a12020d06050303030f010e010501110a020f010c050d20190b090304030804150807050c0606211b040b0301140c0304020a1208090f0103061a031306020f0c07050415 74
    0xd0344400300130403028081d69a64904001031a001070424092081d5440c074030400803481d94495560700104001180007800b090340c3c15000c11004046009103581005020078098001402c00d014000e0741841a403107441d040200c8000102800780e000403684030541c0302d00c00207030511701985221007001d604800c21010544903065018114403450b040a000b020380060300207440d00011845c00d50150f0310355240141a118064211617920900724000b08640c45000803c185203440007429164001c1c038500d02ca08414400011420f2601c5070300109120380710a40c07080214105401130303a40780c40003240208500d694809840114100c090040d20300804048005811501c40c0c070b0b988005421120100c400b01d03141c3d85818031142d808414990701810f00801444036a5000b4020b8500f41d4224245011115003000d02c181c0d800c2d04000c081d00703009000a11800d011a119200911004464080c0036a80d2100070021a103802080d0340028020392501142c205101441c0301004107a8038140d03196440704044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919563210 1250 919561960 919561987
    0x7080615040e010f02040b19051611010c060c090906150f0f02030409020f04031e0c120206070c14191a0306030c090126010213030809010507051204090e030a1202 71
    0x21004c05101032840003402144241481016100b5045413003408900c00c2c0c0d101c00f0071a0303d8043c5d00c1500011b0002c0040510001340e034030108039641c46040c502040415000d48030703081624940801c0c0b50108a071804213210f040c0030382c0a281c0c007a200c40c00014000880100d0010a100048078904041081140410108910134021034004101c402c40541d00c81d41c41d100081c5440d17209120451b0b80d00e0742000400c40d4924210b01000342c45800c40400e00744031f85003004c810724111314194200d1380704a00704201c10002d0343c1101214040e0180c040d003400700102030000c1c0140e03a406213078082034100300300304d041042d181c1d54000005105011318619440303803038480109280c10003213980943d00030382000021076440101c91120001d120590850b07504442a240c1c03403400c03071003401c0030303210103141003242400421510401828081d0061404070302c0c000040c3c0782c0d10b0070401042c5104165a100140c204410702060040c00307801400b100182d4644400500050017068085405045081c0c0205019200041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919564460 1250 919563210 919563221
    0x130c020f0a05010501061d030c0f06090402030c040503010606080c1e0909181c050412020a08030d09020301050f01060e090601050c010e0a060f02030603030d050a0f0603050a0507080615040e01 84
    0x35000111940854189410341c06030609000d43c1c000946038080b542c1008100406048000f64041c02414500d0300d0042484185454070300c46e81d810010801903521a0380b5188011413144804015044e1140c0c1003004160944105901030300800c02c0003c01c1c40080c0403c0c1301152960040341c14140100081d1041294240c00380311003c0d680a82da510400008400c0754031070620b0b0400104c1030b256000c1000b03401d6072000315064582c0c000204240300903c2802c2d5a03250b0b10b8900ea000a20b80c850040c0c0d21705480e89940e100c600040085030725030ba441411070409024158200122214544441d81008802090000c003a0f16003885000620080f0741aa4050400c44a40580c441c00900c01e01100b52a413a83c1c50302e21a4042321a117250042140e4060101d200b924020100140510b103011100d1a44101805014100600095981d0780a652030b550130310410340250300c0f03a009010502e64a042c4103082c80d80940c0140550b4011804000e039580350340d003449a1360f1a04440014901d080403500500410303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919565710 1250 919564460 919564483
    0x5030d050d15051c030306081c0e060c01110a020106060507150203150901141504140d050f07030b0105190e0c0f09090408041a0a050a0c020d0b01060e0f01020c130c02 73
    0x340540711201c0d00b1466107072028132050190701c0c01d108280c0d507001142d954984071001c41d2040854003004041c6242701e40300104a901000f0202400c09481281031800c60b03030100306107400350100054a0000e150280619801070089007065401c00205d03403110440c0c102e201910703003410341d80000003e4021b10616900c03007281e600034040040b0b640e166291301a0400ca0200398074801e0740b642000b501e41070240c804032400e46203107005901104034200c0900104c842000402c80b414010b06515078001d00c006c0000000850140c01c1c40754280d4500000d00101102948038603045206004080c02011010303a00f0315005220585074075680c0300000e4100c0341a006803460113034000c014000b40801d01422070081c000340d402030340b03d14054218042c4281c02d14807900914801103003041c40b510741020f004142800085002505610080c045035a070800140f00980080c404602090b408410764200301c001205200001e000030100c080800e4002801e1019542101d440c2d5a22464190001c903c280003460703e19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919566960 1250 919565710 919565719
    0x1b090a14090615120a03080c0c120a08010501020c310e1b09040c06120603240b062502060f030a0209040b09010b07060c0513030510050105030d050d1505 67
    0xd040c040c1c0901e031074282c20345040c514448500e50300d400d10300d400c02c52106101420313030052140700c05560703060360310740002020107401d00d40034040a40c941b07a0900820204141802d691b680d140103904001c1c260300811303001141154000e89902c1902d40324102c4540500440c00c140c161511300c1d910440c10905085150100018100303010150444400900103000551001c4803000d120980070a10800c0e56085802800010a00c04200006070088030811252082c5180101d440e43d03c9843e01f40c151009520641665918190154030203c12880340c42e120b10300c112012072801131507040800040c0b03c01e00505c0848104544a881190b81d03140881c1c0709080e041120b5500c070314282d0103c00003034100c02c0303010b4016800c01020f107000740303402d81c80d03103040c0e516400c0d004d401c00e45617440301802050303541c40400500c401000611010704801d54960000d601c18001003880303007910385280094070b0040e807195009138040c505034405240c01106484102c6001100001d001d40c078011030082c0d9a20341d07401143c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919568210 1250 919566960 919567001
    0x18031002040f03060b1804060b010c08042310020705130e0a050321130308090a141f0b0d02010c15020304030c120f1202070f0b07030c0207081b090a 65
    0x50381c01c00302050443c0e000d48010051070482038240114481d001c0c00d09600d41c030000c000940000c04580c0300141401c0180350032118030320943d0f00e184060b07019812038209110340500c02c2c40b0242103604802002d80b002d461082281d5880c28020390303602880d0050320300c00c0c001003c2000341688603500c0308401415880442d2003808050420039141da01c1004038103282030700d041503040410700549160b4010640719094140b4040c03c0d4a088504441c003419407040d60181840390300104043d100080702c1c1c1030100020309010300200f60fa84206c415080300300c55940d8107281102444e541c0303941801c0c0200e0740a0807d020143c00510300611400c40c07040f20030071010320200c148001c3c160721002c5026000d1090403c0d807000c0b01c145030203981582c80c05d52114002100c810116024180c1c54010300038592282e2010040d0548036542e001110000320780307810010b682d501442400a034100a46002024520090524507001c0901d00301a08126203a80d4080d612160104852400542c001a003007110300054020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919569460 1250 919568210 919568219
    0x10507081902070605091807050702030a11030c0306060d0803040305190804120804050604020f04020c0f2503030c0b07210b0a080102120f0711060708010501170603031803100204 78
    0x81210902041c00107100d80b94000c603810b80104101c3c1c5c070500d801045900010403075440001c401c5e034020a03401c2000400e200c0d003c0141c03010008082c443e4890401c4000f124000c00605180c08500e0703403200d00c02e50040b02404105d844450007245603681010708181e0baa81c0300e08058482c2d2045200f5104041482602810f1459004e0342640c041c0c0d201d07002210050324800011103590038245c070080c150750800d00201e001460000c40e00b0700c3e0305c0b00150001d03041c0780b400702455040001c0030564070030a0b00700240341010241581409004496080c0e8125801c9055803002000155488401030017012000d0110b005203014000706441b9220203e140c11401c0000c000c1701c40030b08200c401c914012104c40102040c50394040c002d4580416884070100e89513511100308200000001d0580b409104a180c050210840180300c0030388074444a40b00d25000e5450100018040c0d4042c24400c1d00b50500c590611901d90307808811244034506102c0c213008900c02c40000a41001850b00002c452507100040009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919570710 1250 919569460 919569487
    0x91802030c0c0303281103190b061305040501050409050a0305031320040609020316050708090918060132030f1609060504020721030f11070501050a0c021b01050708 72
    0x400d686100c900d103540482d81500354015605841110243c03000c1c14000107074081030710540c50031904ca013688042409c1c0000401b090702a4082550481d405030a02c906000c0f81c1400c0c001e8500410003907a041040051548078aa05c039020084000d041160000114294441448035400c0301c941100c90101407001c2404000c0100080031003940c0194103001e400a0080b440c0c2c4240c0c0c0c41a4210442880038030341d542d90807503550744840021a400c083c2488a44603940301e800c40301d03104a03031052040c4a1a0a00c000b520310b052016840002c80c5881d90b0740100307240d01420f2109071100b502c1c0400301c4201d2003070400642016540c034041c4c0010320a01821402e2201404051360449900b40c1081001c0e94a030418481603104458024020030440c8d07540c0c01d04124030b110000b92810881c0b8000811070790511202080d20280c030b000d030b10000004200141801303820b2154a0b04004c0c9070300c0404c0010300d035401c06511101c006091584d200c0031894141043d0740620115501d203a405207000e951034800c284541e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919571960 1250 919570710 919570741
    0x1413060509040f050708130204060b12061e030a02060d020c100b130b0901030f05150403031a09130b070201060909060c020d080106140a0c0f060c0f091802030c0c0303 73
    0x2445542804010300b03c070812445a24010920759942c21031607642c1c1400c07402d0064140f8800c9030860380c1c45800060401810000d8241003400541740c803040e0501c0408c004c040031035420f074801c0300c2281c410001c00799940051040c2075150706640c03050715003810058060007070086e80b04c00c07101e9000b8809420329134000b581c4041211181101c0031010908849003c100311105103000daa003111f0340c100144081200c80c02182c0e8014800ea049135041e22521a21682c0350100b50740480c00f0980b10075615900302000142945290019035404c00b6520300110744501c4204454000381c145043c880109848074800c0d000140600400e15003403100b0f4000303181220042c0700303182e0840014026070602c0880c0c2031050440c18100c55003a81d0b00c1c06a100383d00c04050066104a002c0c00c1808068004100051001113518000500500001a05000380b210103070850800e8444d1030100914814240725440416003280c0e1909800500141c682d03407003807601800d921407481011098031021040203494030903c1e182 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919573210 1250 919571960 919571977
    0x40f0201080c0f0d020315030d020a03080c0c1b040f020703110106060e0303070b06220203041703010f060c05030708162901030f02010e06041409061206040314130605 73
    0x2551031540e5240c14050072400340341c03d403030038400040107210340e8400d0580281d030304503a0007a8a4102402d110300024545500305160380c1c096008400310206040d0071070420742e130042c0300321103203803510301e045022580300c158081d91001625209405401d16440750341c080c0000303030610f00c002c6503100c20505020380410b8440e84003022642c01d040c0c2c049095803090f0f000c0040c1d108040c00940c10403a103507480c6c035100c43c8002c0196420480c12000c0c4443c4011a800025039520300b44030040e507070b050500703090700751484c03030076800ca10480c040004102d0102c8000d4140304841507441c00103020f46103481e00600b180b04a080c05400030b4070125000b0080710440c5442140300d0b2040102d03080030300380341c0700f000790b41900100312016443c00d1030300400224200d20f0643d101148140350402c160100100080c3c0c1540141d004132184803082c082da24645d007400e201e05500030b0011254101100310544500b641c030000180014104082c04907040004d01300d000560b4005568070303d81000131503c3d90402052504910750313 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919574460 1250 919573210 919573217
    0x207080d0315050a05012f07090b01030b040603050304121109040515010e0f0406110d150f2106020f071505160c050601050f0d02060c0706091a04150e0405040f0201 72
    0x10000b2030746440c0041000700c4e00c0c1078490750405100808500c420703032802203d44031460100c15034041840e6060048d4005030030340590000b100344e0340c50001022510b01001c0c40b8001d82c81e0107402d00208a002003968122000f480c28030503028440d2510103092042440000c0d0000f200b031090204000000c07403d96065010b07002400310130381c3c0c1c4915500c0c080034140c5045c0806d800a0b030104010079203a402c004a8124010300c4286800c6041c542d0b0011140d02c00402c1c06d04003800c640901501302c040d04024018031110004031300241303000d03110221110702a035000700300d02c2c1c2c00180030340490802e200351007400707802c03450400130520441002c01c041c0c0012074444c0142103c000d440582c2a02802201203101e0704480240942e07800c1030f06100c0001ea0340040f0310350040f041104840180d0310000200307a4140014086d10010740b402c00c0150031100c0507080b186c001e0803039079203e40140d03c40f2411b076001c03580320403141c2e031022018042c20b030b4568403401c20854004c2d08000412080c0107401c103403004114801c2e41d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919575710 1250 919574460 919574501
    0x30b04060c0f050d0209310c111f110409020a080106210c03020d02040807050f040b011d0109090212100f0b070b060a170f01050f0402150a0207080d03 66
    0xc404481e1114a2116100411800d002ea010006883d5014201101c0d01500d40019111030522005c50b03070f100e000144140380c000c58950301e1f0b400e030302e8060408560072078240216a40512803030540c49000391414103000d0640352244002c01c01043d00803903245410750003d55622911141404081e45c40321101c18017140b028400001c103607104000351b1481001130529200010a2a100d04002d0b0a020100000b015002d0050080245551000f03100802c4480001e00301140b40900380800c9040d00000746112310301d858a03000041e42c00c0a02640407820103000402d41e0003100d8010b0340c20040640103141400c0c40070580d1025014083c10290098500b030501c4050140d0b1103803040d0038400a4007400342486c001703000b0440011019a801504014020804004182c4900550700941710180c4411490340c8180c8103070300c1062080c4205900945180e20400311454180c001c42c1c01301c90034800740344080800045000c030243c400c3c49004080c000510a50380038880421004002e46203080310745002c45201e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919576960 1250 919575710 919575731
    0xf0807080c040501051b06070507030e030c0a0e090a05030310050f090601050f0c0f1204050a0e042102150a06171c0c0213060305150c071112070f030b0406 68
    0x8504591040e00d00750310591a0509103001100c0a4019160300c0304220219140c907101d44c0c006121052003680e450b92220740b40d4519050007050140e0408100740641c01c03128108034070fa180c5412440c1035601410a441c056100c1280d9649010072680024015001c04024004d00c04140e40c0c0201c11034074203c800f450400c0808040005110007601d041d400702c0c200300b0001c5c2483c1d200c1000b80a1542c858800d4503800380a0340c11050030700c00d00d54190b1951142c001410f11440c500104480f0250607000f0542c0c48616265552180c1e0480c1c06401020003003d10241515581c400c024104812404ac905c450701c9081c06041c2c4806042c0030702500c1d8042580d9a05210300301000603a01940703044400c4142150003840380155102c28101800f40c1e0130000c1722815100ca0790807030107141c00440c4640014000c1a41c2541e8408200a014000058840c8104416008110003000034050f0350300071100a4402c5640c610194500360141d4012130541030250000400c1c4607400003903600c5107024140a2040b00c4c000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919578210 1250 919576960 919576967
    0x30b040f0b0306070807020727050f1902180402070f0c050402070201020304230303030f070306090603030f0e060d090605160e01080115091d0702010b030106180504021503070f0807 79
    0x414070150903501c0071001030181c500c41c40c01c3c50781043d11801030b41c1025850b04507003e070240840d0490760414034030042101141d00684503059010402401011090900f101480d0850300d190000b40c09241e00030031110761a1a910b480c203043c0c031000900071551100c80b8600100501c440081c00d848001f0040070008641c2054000c640b202c1d94140d01440c031701800c121240360414544400b814a9980c000124861620304000035405400140070710143c61810450080c280d41854100d04107190500d00c041000035080b030b802d6007000c0c11900345100f07074603003079030200d80240100c03031018055605007003003c2c1c180402c951203107010b40c00040500c54640801d290503160b2030014200240001c072880e004100045580310256807007400d03480c0420380701d03a44140b2402c0103013000030360480e40762411003030080c5640c091040100120b0190000c1c0a203c2c80c09050004182d10b07418004100b41c0c5800002e0300319a80d035490180c401840000d400d84a0400742d000038145c204403101c10340410004804590003d01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919579460 1250 919578210 919578221
    0x10902011e0e04110c37030f053a0b060301080613050c0612160306030803011703040306110a170f0c160f0506061801150f090312030b040f 61
    0x1410340300c0d0100d2008200c20300008002d03140a2000070b2009128a044851041c41b41e91544a02ca64407492a050300184c2c0324500d002105056076072915050010340041e4001e440004072803001d003040c0d92955005d03002264440151516030300706924001c001a0041d140c90401c070500208034908104510320071090200ea0703c030a001c0c0c0d03c415444800061a0030f41d40d0111018158030800980e0185141c140c042409a005044207813610b84441d420041507004020f01d84003140300526090207520301c3c503200c1880324032041c059061190002c0011087d60381003041150300171a417283c0308005400d002100840103801c6204800001149050f0302c4e0144100456900d0180741130019540c4144c581c401031401aa011206a01c1e0040010082c0000700307008404106046009070007403c8035107422010000e441962075045000911958014007820131016250340f1011032a050803a0f403865160320544080b80568002071094148001c103c500079171581110144000595040c004215a03200c1f4905844 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919580710 1250 919579460 919579517
    0xd0201020708070627052a09160c02120309090606040e01090203070903120206070f1d0d03020a12030f0f110919091103100e0108100c0314010801090201 67
    0x240c1840b009000c44c000d680003c54508403440800911088095041c0d4002c01d504002d60f140c2e008205440ca084c4600001d10701e86407094001c1200c3c1d5000703040007680991004e4150364910254070045e00d070442c003919040d402d40390000c11803803920115640f00c55695100c41c450301e0040e500348004c9441828140c050b1402eaa84500580711107a0810381c00b24003c1d0001884401040740605000000c107035036807254030a071407559018041c00d01d0f11140c0504140c42c40141e8904200128a100e05c030004400e840c081090030460f0403440803c050f0a00b24074102250070007900c907208c0c1440070054190181e1040321002c4081406000001721403400ca400c48006403041208114108000c00745803400c585004a0065421041070038181c43e0520030007140c094500c0f04080007400806e01c865000e20802c3d50740246030050b08691690704003809262201c0c400400000c0b02500c0e03600000c04c0724041c5d001400c0c180c41d860390380c0c0000d41e50b0b102c1c0280a485030390307000e0780818481c845100e40e061000300d0781d20184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919581960 1250 919580710 919580723
    0x60b130f060503300a02120403030f0305010611070e0402040b0621010e010605040b0d060806130c171207060209030d0c022d010c03030204030b010914010602010204030b24210d02010207 81
    0x26444c006081d000c0d03000140350421801202c01c501c00b80c000b050040c0001e1070082c1e0f00d064001106000203800c90310f042c3c03c041c090000b41d00000e440f4603400251072050341c2c070306060b001d0145c86900c040f601415482000d16448400441c01e950440c018990914100c502d454030440941d03030301c9034100c02c203c4c400c0c000c1c0d6001031b408010a00c55510f1810040c804100e0310940055051b581d801118205802510030903522001c8940301c405110090300340f00c01038002000300450034901c0320b0704503580302c0d0040e0050420ac0c002080d1130061003076503410390b07601d28409010b581c1907000c2d5a1000b0000d0b44442c404920070030360128240600400d0b6001c0e8604030500200c00c0081c2c040790001910698000f100813010150200000700001f503108034114000c140d400008a805d444044002c18a550141c0145046a205010800c0401d40302a0119049101c81c403440c90700b0b11030402c01c480da155001e041e20390408581120340c800c0d1a242c06034040c5035003040c000d8800e100d01c000022400d0703200305e00f0050001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919583210 1250 919581960 919582033
    0x90c0212160204051e101712190908160509070f0e120a05070e060f03120702060313060e0606030c04060609051017041a01090b0d060b130f060503 64
    0x1810a64082500605445004207071710b5000c60310032070080710441d05140d9108101200300550220007070340882d21050900a0090744a02c0c5040c0301c3e8070b0140b44820003816115204582441e401200307020098080081511f1004080232095002c0140c14403a0074010f0003400c0014201922903c3d101d4021030880c0e5030800080400c900700034606410b40c0a4071080d0045558030800140100070484c018142c5d808a4103803458145d0400c2442c4e800185e400d40241c110700301d400621030800d4102c0d620030740e044a41c0c50f241c1e2105082140901c8408900070300091604104140c2100009586031240d40200e0480303e284000e4000d000c10b46105100e611302040c0001018822443d11000b140390f80c8a40785000502240030300c070300c206031140c160b80550b810b80943d44000c250600303440700d56001d0300502405000008015000c20748110440b080a840d10b640d42c40651016601d8035a11a2488494a02402160a91500319004211502c101da10170703c5201c41c040c0c0401c0050000e000b0401c24003660045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919584460 1250 919583210 919583213
    0xb0408030a140919140103060e0f04031205070c11120c040b06091c03022401030f03020106180b120d2708030a0306031a0408090f1504090c021216 64
    0x5000e02c2c00e019104550030140110045522158048074407244081450520f0a15040c0380040c02400c1d190341c0c2e0f04050408505001e216a00116203030824036402e26a40140c3d220300301111901e10b0f4001040e4510304000c00d01c43c2d1a035000c0380d070740380807801a00010090039080c020001035a091703545000d09074200790041140c07807030300340d011407200070011340101e04d409030360000685a4000007204001400c800001e100605904000d000c1140860426045508500007024603500ea0144402001a1025071078041054403e4010314018a59503212030310070b040040c17040b0060801015041c2c0a03d008595020924000007909840301c101500da0f44501211204085a905200f02082130024010036000031010400c00061000b44219500003c4141c00e40c03801c034009240400342920896031050501010514070400c407114540c003191481120007a174808034203220196140c400040c44041070024041e13426400c5a84841591b03420b6035034802c2a03102d900e80c43c0c0103180042d03034550840c500880 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919585710 1250 919584460 919584467
    0xf0d0e0d170f040305060f10120203030d050903030910060308250f030201140f100e07120203010f0807060f050d0f0e0307050703020a060e06070b070c2a0b0408030a 72
    0x101540c007841d4a038003031281e094104401c1d94030190a2400c41c82c80000c080003442814050a904441c14030303079180160502c00b100041e01a1580203000c0c80100f4005000115502002201c40480c40003074180b0051078456401610b0350802c9400300b00301c0c000c0001d200744984040c0b050340240e07580100414180324400e25140c1a8030070080d00081d418824040c444040307010444900c211074400e43c0041280900c65104400c0c400e000b070125456200000f00f8441184440e46d10351050356014108500c041d6a40b9804590103041d045410081031300c00000856024003a0b10780030142c0c0c2c2d10f04101d401817691444100c2e17403075102054120000303009122141d52808a50031105400c100800c003c86ca050401d030b80d03a401c0d41d01008048071298401c2100f08214206100c01d14010216401c00c064640f0b26400030030014070035a0720042036601301800081a160040000503055074100100d900c40d1a81c44c0c05049410801004040d01800d1070200081c2031320388201220107480001c4082c40c182220400700b42d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919586960 1250 919585710 919585729
    0x32a09020c151306230a091b030308060a0b030606040b07060902060406170907080d26010303050c0616050403110a092405190303110f0102030a0e0f0d0e 67
    0x2244140200340c0c0c014040e0030014241030254804216484402035107141003012509840603c04820100945c0c05051402d12036107941d00c42020308004c1a80503103450f040100c51303c14080c6281c1c47c0f54a44022080c50ba008008a2250500751014100c20b9140c0419030034501007141e041c0e900c200c00b0070050040854000190003d58843c03040814034040b682e0001301a0b8000f9040000010105005103950b128101030b043d41141014002d040c4041c10a000c0980741c1000c402d44800f031200da4044107040600c2c04e55500381c0d0703030000036150b80596100c0c600140a64403030440440603100b00d10100d00c0303d8640c0c2900283e0b521540e2600c918061a642e15040b00c44003048409038441c03001c43c4005400442c9014040382c294801c2c90580307600e580d103440044c01900d41e070492401180c000013040205e003d06900ac0c010303a60517003092690310b098000914035007541d144100740c19500104c00d009080103980c0010801c41c03848403d46143c8003200300c8080d52040000305c2d181c00510000302c0ea868900341130101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919588210 1250 919586960 919586977
    0xb0613020c010204090b10030e0606040b0307090219124a01020d1103060d0605090a0f06061502030a080711011d070608010b190806042301032a0902 65
    0x240c28440112000341c2260403903072041e0700701d5489141000d100d282401180a144046007001c00c010140074001d154ad6aa005200d1030046943c0d012298007a03404100d41001456980c50541d626510038103203035501d207101d40804000c11440300700190700e400311f0700514415002c5503580da0400f003280038400b2160070010f8940e803003401e050144400d0b81c0e0440301074480c15a6182c8000b50741c8180e0080303001c0894490303803200e4562210034014051b00d95904c510190303130140c0207030b000f2403961160300c421801c1c20210313100288500480c11201c400c2007640d4122038100c03541d150800131052091a0140e803a4030804110900051071400000c007194022009403881029400000880c451024000d501280001200e83d41940c46140c08102059000900c60301400c1c18080e800d041c00c4801d1070241c040e81c0d154038003200b8060283c0000d0b009032034503440300c2c1d20b511030702000c280c20395200341000300f181c1801c1c0001d480c6024511075454200c3e0002c100302d41c940d41d02c00da092131a14500460440290070044c030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919589460 1250 919588210 919588249
    0x120c0a0804150f18050610050105031b0c060a0912080105060d0504030908030f0c0708010902060421020915090603030a050d11071a0a0612020108061e0303030903040e130b06 76
    0x140b58040007014807139240440c030b42002d409203245040c1801841c1980c01401581d1440740302101b4011343e40d0040079290071085003c5030f2001d002208099036034078012056201c980c0d110388020440c102c0640d40004035511302410201c420b141544c1d00c200e81d098800d00886400c48000c010295420750340340d0046070b000340245040307840780303464005403400c41d800024032034a606004640c1c0d0046860600c040c4004001201c000c02c13075a09a580418000c1c02a440f49513a810041c2c1043c4000b54141c109240c0529402081c118007840d0503000c58110515103208036015035071140004242d410000100e41ca55812902d0715401c003010b8036026070140101004901041100b800032000080304a0789120046100d130051a00a00d02140d00104440c0351358060489070f10b0740d064060150341c00208460300840151502c0712191400da81045502d40a601c005801d0321000003049800e40300031000c3c1c404c2d10311846070f080349034554801140304414980000f5001444e81008074160703141c103501800c01c1144469 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919590710 1250 919589460 919589471
    0xc17060a081b03010b0d020307051e0619030b010c020a17031c05040b1b04030305180a030303020c10060317091c1a1e01050f060405060f120c0a080415 66
    0x400071401d00600c8000c0c2c00000709076020078181450f083c010843c00712420b50358038800e41000c1e00080d5443c09240700d0540540d0010501e20704144002440114007000a440c160341c03103220032942982c80c80030240d141c000902c0c01c04024030b690b100e065040c0c640e640042c24600091300700560044101410101c8082c1440100582015134401c0816030b170500b443d484000409191904042108090080c1418130041c20640304410103003501c000c1d901030760740516050b62036001400401c5c00080e54050010f6000412060002c2050341c19002040120811429101c0c041c00b80c103008000e0300c105020080520b00d00c2c06801000c0d8600038068241e00400808007a000c1000a07150300703030724034a90b5058440e00d14900c1585d0109192440c0780d074001d11a06001c001c0d2040070394080c40c1961040c000e841c490305280c00e0301403150780c4100549014100041035244d945410105103a0254008201d000d00c418400740010a00c6048130107031028060319450b4245255503603590703035401d0000c80707107151346466540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919591960 1250 919590710 919590719
    0xe13141603061d0604151a160b09100b01020a0309050415030c12030e0607020612040305040812030a05090f030304110d0f05030a030e0102030112150603141605040c17060a 75
    0x20700b4200092820200000300c03800c04009105c181e0b00459640200380c110540c0800072075a540c0b000340c40c0340f0400d00700c560f11511240754a81c1e0814200030080c000c680d0b09018042e8054003c545184040d0354160104074114130040107a85a80041c440a000b15501c00b03402c001d6414250004c0601c00b038648a04001f0907220707030b0752480c1c00619400404030444541038184c205a0000c209201e1848200c40c0b080c20021254001804c0384519500b010b40307200d40102240426000d41c1c256805454203605603450990b03c0c90900d0151380003183c641d9401d60900340070951064003c41c1d18028036003040061840d5588980702c02d640c1c0c005610840c0d401084c2d003804000480d200d41e01c0c80084502c508003a503a00c0740c12400040603101d80c0c409481b0b50340d00c108010402c40700c001304206015544503400c06401290110760b07000501c42580094054007018130100034000002c6110007007016101c07540e0156a131100d042c0800c031500c0320303141c0011402c9075107466580d49622080c0ba62005009041d05021b0751203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919593210 1250 919591960 919591979
    0x30a0315060e0d05010f0e0f0c150f090102101803080f090d080c040504060f05030c12030405120a0203071509080a0302120313120e010e19030b0709030605070e1314160306 75
    0x601e00d00c1e800c0d40e0032051032030410420030b1161005414040f144d5842c074500411000c0307040c0c402e12f440400030000004010a0503402070214018001107554108001d84004000c0c42d0003144400f01200000c000100088480c0703d40452a030180d4007a000420340000c0040c0309444a400160442c3d0480c1030a02c0001115a0369005400103012001004000c00740b5001c20715140a99588040784276144000d100c0403074050020a450485000310b41c0500c103034440381492401c2030020704d00650103026100d00450120041c0c140c1c44100b4a0940d0b03035600032030f6185203040e00c5404030300000380141c1001016a40c81c1c900354010b140c001a516151070a5026281d8480b40400c2c01c9080c2e00d40441d0303000000706035560f005840070760011000e4401c198103d003030103030840c2c402100380401413a03021040c01050000b84600f008001866020b88200580e00700a800030b0041500901028440e154046ca0807407200c0342e030f000e109804014699500b642d134803603c04540c94030941160000030035a8441d400140c1500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919594460 1250 919593210 919593221
    0x6032003061528051c11070f0b0610020613030305040309090c020c0109050d05100f021e030405060a0b1e060c030a030501081501030b07081e010305030a0315060e0d05010f 75
    0x2c140c101ca0468410011114140796501e0079034005004c001d01c0036a2590008401c06200c81c4090400011030100c0c0c0c8146a01c1030107108000fa00542480e2612010051044519800740c0d50032602184840d2180e0b100700e941d518211003508044001411941c0001d001c0d400c02d50708640704c2d0a0407004030751941104c4044030004903410005030320100c01e2007019600650070030041c02043c3c5107182c8001d0755841d103130380c0c41d504103a0030000355690f450402c107440c1d5203074140c1c1d441c421000c0c00c180900e004602c400b2040d40041d1001e0301e6500401010640c59034403803062101444000d040316641c209903160b0034800c80030907050160050020403d2000c20300c1d0500040003403075415100010359506180aa601d0240d0000b1101542000d560040c00490b40c2c00c0e51650303002c40e00d80340194640d60780c401d4448128a0142c111101401c07940b00110030450048054005030b043d0307540c2000101090317060702050715541e10270140414400c0380d02000f42d0409801e02c285c118028400410318400c4000e0b0101140c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919595710 1250 919594460 919594477
    0x102031324050705031b0a2f0d0c111c0b070e120d0e030a0305191101061511062e030215040e0106080603060c070203190305040f060320030615 63
    0x14130000803c500400040d0b0300840d00403825507203904002e00c0101c0036100e0712060040304880b041c50141f184103220800305007000c8045c80c02c10343e421541e102c3d2015203801a1041c2c00c4a07074590814030540d060030030301c0d1640b04051449580c02031600b01501c0b844e0700c1c400043d000c06c081061305040c031401d41d240c4095250b074241242c0300802e10440e035408010403142da52004548a5046485080007103544807050710310089041865403040c803403454083d5040d0208100400e4294240500061004a03101c2e80016454a80e103690103602900c3c000c542d120308044030403121844024450500d80b03008107001c11150900502c403d000325440741c00098051085464402040c500054180b000c6a0383c402c0860061400d800c101841d41045000a5110f9030001c022404180d0042140001d65508011203828900d134080c0040da50081820010107075800750140403a034000b0800001002d40c403a2103102981160340146d201a04042400b612056002400031607202c050300342030396011000840140f9008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919596960 1250 919595710 919595717
    0x3070b0f01051813061e1a0108010902190e06070f080301060e01180302240a020106090c1b061815020a031d0a032712020a050301020313240507 63
    0x150314010820004044041102001025003c00d01601403c420f540341821603100f940442d641110b43c0c4002c2018482010014103141015440c451120801c641100901c40a07a0703040c805030f0301e5148850581c807a000d500161114001f54000b401031044815282010300101064039081094659148604004000340d0b0041e900100400c40a03800c083c003880c1508007800d10401541c000a030b812414182407102900405161440c896110141980c8425800310964a19107492403607200900a101c03034040d21036018640545020303882d0256100c01c41d00380706502d00c0c08070340c0d14030343c0e850001e0400c2c55000041e4152881c07114000451099618550340c042040c01a20b84003181002815194030361843ca21424603000300d210540070206034003604541500700340007405120810040c00e1600184401c01050703c00034003280c40003419101540990007216601441c039201e0007014200e00c02a030b2000254180d89a10070001600c0c0b01c0b001070144802d8224581c0c01d0000c41041040c0c40080380c001001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919598210 1250 919596960 919596991
    0x405030601052b030c080307021b04051501030902030f120d060b13030803060f030609031e04060801051c08030406090203060a0606120b0a26060f0c0403031103070b 72
    0x16040801086005000840d040700660514010355030012070b060480c00d40101c01e183d81501458020300401c0412035018081076907a00d08440c000f074541c00e00b52400100e010480c00307010610310f001c0c0140fa008404c500c003c4008203080c0c0d070040d0011300011b20100d815006035044105014400d000c5051302c001c030050100c0d600e295203101e00003110050303081070024900c140610140300b08a8614002503d62090031103549448080008408404001c2c1040e414480c0ca81046002c10010004c2c00d100e072202d404031400c00840150341d0b201c9002d140580c3c0001035207800104894a4004440c1085500ca001003a550f94040c0d12a00ba10394001c031800e0f19540c1d150691202103007020002c0c0356100320800c0041118508002000300750510703031412980c000d0b4032400b84001c1c076524080b20100510300b0071203054401c0310090305d5110103103090746c2a2000e4090007001030615038180b1000d501ca4030362140760300c0c81e1509681d820b4565064070741f110346040c80f041c003610002a11002c001d0380150711443d4841703072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919599460 1250 919598210 919598219
    0x10906050f07050c06010504111303120e030a110108040f051203070f0302030702060f15040e010f05070c0b01030303020d0f0c12050604060e01090f090807060203010911190810080109060204 83
    0x1514000903101c5403c1007002c0040ca070b050030000c80c0c25415079104907408501003441008036081805034000b43c60066105100c0042000141000c0020410315600d0f801100e000c10000c0648a420310007016218000c403c1c1640310a622a01c116584a485640140030742c6405403100c0f45840000880402d84000010a004c0f0704c60300800d12031600d02c0d4070b180a502d1480c02000081d240d1030050005c40c55803a100012981440650601200c115006081000220b1a81e0303140f6000c0d0a07880d6004030141e140c48085294103105100150800b900070b46910f42d00c1e4a941c0d4100c00030f5028200d103061180c2e0303c44015a02c0d855600030703100c0104a0303075078844028503004d8030300040710009031807144550f1a1180801004c640030410b40c3c1114403c100000d18404043d0408000e880342d440e000f00101000541c01c02040721960140d0b0683c0c1c081e99041003000340c2007032103808910900c0070019244c000251200d420501c23a0408a038090b4029141482440d500c081d080c1c2540c0c4415801c440705a0046028407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919600710 1250 919599460 919599481
    0x3050708060c1c050705090415090506030307050a0312060e040503070203060a1506050f0403080423100c0204020d060e01060c15090c0605031023210d0e0109030501090605 75
    0x16041102c56140c503162962211810039400c84050018501c40c1e01c941c00110460702400954180d070328040c200b80601001261a207040080074083c011690b468078020402c1420300000b5200459032001c0240010440b82c2ca041d1489044078060355071103900c1e2030000c200c424011040d207004900c030700021511808248109400c03c40000c11690340c03140390810b0305035601d291900400840300a8244186d4650b0804001c0b200d0740318940002d0001030001600040b001c515102505183d00f504180d800313211009810810798142181259002a400241c01e40251900e64000c21141c2e464801c0040c9180c4d8400304020b852200343e11900100c0e884003118024082a1413101c114007a45907020024125590fa500c11003085034024101080004400284000d5070010101c1c0648500c034400e00c8590902002036003851100844e8900888a84150840250034510004131080010f0702030300c4940b580500450341c08a01e0ba00e41070400c00780950000100d1400e110b480f1170180103440c082014030701f47d042d89 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919601960 1250 919600710 919600723
    0x111090301051e070c0c33080c0d0f15030311010c0e10180f030609060c02010c140f1608070615030c09050601111b09060402071e020303070c03050708 66
    0x524021010046000c003050109034258007522a0a001c1c08001710790600048124840c0c03c07250103448000d064500790f040b00c40761580800c0c40420091303010303d41d0110450b4040c2c0141c40c0c460b5155010f0105407001b00058101003500c4809690009113800c12884070420308905900c20307000310b070106030080a00c44080c05036803680042c40c2891906140500c0c0410b80755608503903404108403025258101648800265500070089201c41802c4030f500d03814003800070000300300215002c0740341400f211420390042c00307491030400098640214030300a1568004c00e030b074014522520a1481007015008444401c01c0040003280951000d585070503503494903408441c0040c3c04e034130240602c82010030000b030002d90440c2c02c0c0c800b40200440c1a40300e0a00680d5072400d1440503c1d65400f8004003c020000c0213505201c83c050202d80c26502071701c0d8a0140000c17849031b584042c0484600d5200070304910310800002c022244094216440d00c05035445403004d0f004150801c40d501e4000b5501040b0280040011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919603210 1250 919601960 919601971
    0x110102130623030f040c05151c050105010c11042d11030f16090308030c27240d06030804150e0904021c06050a0e0f030a0503010e0c040503011109030105 67
    0x81e603000c0840c1140c200ba1500008201c0400c0400a1000a0420110300d01700c200030000988038200302d1900440c90a4140c10041000501d020b1030300200c11141000d00415040300c3e01030b198259109010f407101c82140e14a2103640350016101c0781401100980220364400e12038203c200030346c02c42c0240c0041410f17101100009a2a01c6090042c82904c40141030b286d900300c90120502800c4494031401a1500112036001070f0a8050100401030310301d90442c014007001480501c03800d40050520703400d0308000501c0e04120b03004104d01ea90032030350381d00000200504081076010181070544440540c803c0c2c03050f5400403500510003160402410300000e42c13200d00e14509040c421400c40848000c51402603005101a104650b11042284240f404100c0d4540040c0c0020040c1b0442c07a240c03290300c5c060010302986850304d02c50a82034030031450300842960310300340c0c0aa071240c2c40c591800f1001c0c2d00442c0080c0400c060498104000a8156000d2080c80940400f55204a803503283e808100750031203000416 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919604316 1106 919603210 919603247
    0x609120705180609060a18020c15130218040201140706090209071107060507050d050c0f071d061228020405040609050c060c030d020a1101021306 64
    0x440f03100321800d07034192915466800a0110800a13840b645e1180c2c9081c030150001546d41d50020140b4a29440403a9034090321003454260038034095403000120481500940f04504100f2055600741c03245000b904140c1ca00340c3c001a01d0450710541c040c000d00d400145040c1081104c0d4010101c0300e40182200040c0e00d8140740c040d04d521540f6100e08602e110742c403000181d851064040b40c0c3c4407a40f204c040e014400030610b041e90250058491101e0a0040104215030b01c803041120300d004084032407074521750a0340c1c3c03040d0003005180540040c0c0151000d54408424003400291410001211110f00345007019a4855541d443d404220081d4041d082006000c107011054101060503030052046c0c4103d103409104010b003a02c241034a00c040c41e0014003030a203003685103502825107580e603400c0102894005018140c03ca0303000d5507180b0000350080e07505210803030780b0413034aa000110305807 = true := by decide +kernel

theorem cover : BRFrame.Cov 919424460 919604316 := by
  have h0 := BRFrame.cov_init 919424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919424460 ≤ n) (h2 : n < 919604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
