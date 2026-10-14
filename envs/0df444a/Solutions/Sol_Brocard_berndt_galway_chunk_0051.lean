-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:34:14.312749+00:00
-- url     : https://prove2.me/submissions/4bd989d9-1018-495b-a047-8ab6bb7b0365

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8992813 ≤ n < 9172669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8994063 1250 8992813 8992831
    0x30105070c1212020d0606030603060b03010b060a080901090206070f03032403020607050f010c09090b01020c0108010b0304060902100507020103060812030c0a021c080702060f040203071505070501020406080f 91
    0x41100490145042020440b00603d8014800d0704403410501c020b0041c0341c2501001d506181c0d0014120f58942c0011040e280508401c201d212100403c00d42260a007045980c1c0204082c0421641705000c1c075130060b8885c0f91034001141c0c1c002141c0c0021065813118030b080b1141d98000075046c080c19854410180314007040074107107142c0003040701c41600010b03032440000e01c90000015450100030007403040300b000446200003404400c00c6140c02405481680c000e03e82410716100810b00d60350310000d68104010f5060319200388030313402c005e50987d0a60000307005988181d140c15030380005880304900200c1c403840136a25161920030510005007030f0b034855405140607602001a45018034516822207401c011800082d503607822007000e059007494840350300d0364100c640c100e601054023900f080c0b03814072a00f82c43d400c0e101641c1d100070b07035010080000d07600a5096803000506102e1452141d03413906030340006090403070030507a00e69907484c2a42d02940000740081c4000d814001c241c5000d403d01900070003c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8995313 1250 8994063 8994077
    0x60301090206040b07030903060c0c140601060903020f0607051e100603020306060103091a01061205070f0903030302030907030c030f0c060503040519030c120f0908191101030b060c060603010507 85
    0x1e4000075098051070051001584002403640200340c016007440700210b901110600143c4d171401406000b01c900d001e026a900059009002105900456014180c03071884c1c82d001c500c1c03030440c2c080c4140c8400d641219500f0407410026000030800401440c00350306003540410000405100545013030290b4800802c402c42d050480600050350003081d0154050001c4c6000541c0d400b4a0500d2282d800005450307002581c813510000c275500b80d011210103120003076120140f020781c030f03408012118070840000000c0041e2002c241880040d110790011074100046008440c140c035265110340304c07015402c2e401154014400301c201810050600c46040003041d0500300941185002d0316000d4072002401e80900f50b4081c18680b00c000c01d40145d61402c40301d83c01c41034070030400c4108080a041507040510241c040381c58880d00181c4440d0000d055080d4101e06110203404401d1642d9021000f5240fa50042c10b05841d031503881059200e100c050061540194010101818414241030071038501030040010441d03d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8996563 1250 8995313 8995331
    0x1090f030201020601030206032a030609060906010c03030504230f01050f04020913020102120304030503070206090303060121020c010207050601060f0305100e1906080a020306010807081e0102120a0203040b060301 93
    0x3c070343d00b1704480d01074a00c19600e50312500e20ba440308000e07100d1940c8841c12101c6a900601034100914850030b81070358242d6681d02c0d401c0401c00165822145180045c0040c3c8000d800a4402d0300116005449220310b9114484907030003162614040b00955103035a400340c1001c000200b024020340d41c020030464040c03401030405802184140310020038440c08032039403100303850441e442008031142c0c118400118944908040c90018a86c2c0d100784d44002c014440e0001044411502208403405440c05855100c81e8400c0c140e01030826241c0e042517a0b10580c1c0c00d001c2c0c003243c10801e0004150103032050340076089541c100b00740a84940540764101c0101442c0c04208a02c984041444500f668201c05081a0544d140480b81c58180600d108017000103040a10004660b880000c04424403882203003683e020703a80319a80a5500c245c10700c5000c001e5400302e004e1440300210b50603e9002c100d4030f100003500c0c04000b0010500c4451083e00c10400d074903230002c200818810080710030341c0c100d00120300074440541 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8997813 1250 8996563 8996567
    0x105010b16030f110604060f05060111060711010b0607080c060c0304031b05010b040603110a0b190e0a030501090c150302070506040b13060608030403030201111315030f0f060501090f030201 83
    0x201c0c0003020301c9a0912210b0b149801000c03d40710b40d035050021281c5603e030510f05000540804c1b807040350464208000300340958080e0600d40380205214005081c3c680d9a01740843d455080c070b00e03121016545e43e060a05c80c1e51100c10040c154035004413801a41d50100c1d809940c42c015004101c1900c42205105000009511030707002c140c034286a0501c0001a07000c0d04007280100900c04c001580149003000c0001003010481110304250800c0314008045603131150111243d108000090f0b180f04140f00302801d0301d901402c2301646140c80641540103182e00d0707030360b00350844050440070f580f00c00754a442041082040400d0141361480c1d40ba0941c140300c056544c49684200140005005034100000140780c00080b01c180c91685130407000902c50240d807510081d8581c0d00602040e0019428040c21507418801c4a00315200b0710700605481c1100c0d45000444405103000024500030035403200c110140d54010390080640301c003003c03500094002d15010000d48441c2890344030b408100324000d400c00140c1c0e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8999063 1250 8997813 8997847
    0x90f0601060e0402070c09020c1501090603030813050a0b0705130b070503030412020c0d030e0f01080c070303020307030906020301080d12050702100b0604050a0f17012903010905010515030105010b 86
    0x3400507540580c444103289010329601345d554100071f00e07251000ca890f85003814000b85110788140f811000341f40300e903222100c05003903c03c203001c0a00030400f409d0120f0202c180100c0c0000d892802401581e4001d039095a40510514007514a400000e50100f00100b00802501d0110000c00313284100300d117010aa55a0382e9280c3c00000c102411482c48141c1d43c1c140d4600030300003118801001002da0707140521074540602170784101c082c00341c000d181d0058034281ca54000c04c42c0500920b6008019401d0034900d0350110040d62008121404045d06c1d100d04d4000900c0d42d002441c081e20000018242e070001c81e402c0200141c981c041c40541107414503060114441c0c001c2081e00e640c1107070440124103c4da044000c00c40c1c0d0b224550090350882e040807000207103040400762100c20b81e507416030451205000b0b496680d090702c408002026154240501c106600030094007802c1208101800204058105481d41800c5840459202440f050811010000c80c03500388540e9014164031811a4180340024048000d07403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9000313 1250 8999063 8999087
    0xc0c010e09070e0307080f030403050f0a08041a0405040f090605070f0e010f09050a030c0501080a020f0406080a150e0714040806010b030c040306050702010b0a060203030402151305030304030b090f060106 89
    0x4070030f1810382d50300561418030440700a030a40708121340d130a00c451103060356039610070311065130305e400b44d140c5801c0c114a0108a40c001550810361140c00c00303041c402d40c40c07000c00c21200010444582000b00003070b143c41d280106030040c8080c580008185007182000000d0b20300041400040285803060842c0c190b4000c806000b44203802e00e026407220b0300c3c1303000c2a54285400e0f042143c0c0103c5290700001008048002c104c243c0341b007a6180022521100d1940007070b1b0090005400644006020a21415109078002d9601c010008008034803d03c5040710790b4100340d0301d0b0304904003002c021020844419008207826544008010800345002d1410950680340c05040c0250400742c50000007207175007284140300303481c0915000441045182810b00c80a4000d01c07070b103104240511109040083c9841c00802039a1203a0b4001d01040740711041011880341030750001102440480e4080c00201d100c2e10100007a2002d503200380c05000035410082400342c81c00340c803010070f03000d543d00c504014400154804654590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9001563 1250 9000313 9000317
    0x408100c14031e1302040207060911060f1207120903090807050a05090103150e0f0c03100204030b0f0903040b12010906080102030103030c0b06030a17120c041a09060706050c0c0c010e0907 82
    0x990345422854a1640311044e9000c1c0d48079002007641c00a0142c103601c41c1480c0f41c0f00d662114641c421b020140400c2d0f00580e0440c04e044841031084070902e909172103038a54440c19030b02c0d11541040480001c0381c02ca82904401360f000800b107440a00070030400b0000c074005040111452881a8640000070b46000700501006150f14054401901c041001c1e40248031400c4240042c0c8100340b55802c1300c1552480b4180b20a44607101d207810b00855a8040e1003204c0c00c0e607800c000841c01d947e4402d801900b44803005011444c0b07034072081000050000d894400782490000740d0300303154815450003402005581d0641c2040d1a141d10400042000070f0b0400700280f925680200007081c1960ba001c0000c2c00d150809902500b001070210700440220040030040215800b080a4038105440b031001c00d4007a40214010940300708a5142c07041c0b80d038111000030301380d240d8005040c0c034507101c903a68503038060301c80c25200355802c088041443c51141c5014008006004d40030301c1d00c800350810403000104070310130250820003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9002813 1250 9001563 9001621
    0x70807050409060b1f080609040b06041a0a080709060b091c08070803010b03091501081f1d030a1403040506010302060903010e121b070f0306050c0408100c1403 70
    0x41000201d400029984200070802210405c08100d4a03612604203c0048001084400010b00a1600100150045410602a498969a04007440020020a0541940d0b24480b1040c814565103452107180905550b50107004143d01d8040010300740c800641116161000c01e2080000c140c45590030711000c04405a08580c0b210b4039410b000b5103a21503158007800d009000000071580081200045019404031011118408010846003611440a0080c00440e4126488170199500c09540b114041110030b1800650505003d01c0000070f814007072022002d903003012588440c81c2c3e40221000500074480d545003803030340c5016a036141d11010140002407140c1004a03e1070506d480075032103121a07803541400ca40c0444d0740f508580000350403040c4005a51880c4041c80740c1c8440000c102c02d0300302d980c0310744c1c1c400c2260f0660381d0b03034800f901008004900c01c12040c400001c3c060420400000c9400180d00005009054004000e200f11089840c41da80d508080041c0040320354076545003105198200d100c50307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9004063 1250 9002813 9002831
    0x1515120403030209060d0603080a091d06060306130204030c0303090e01030302070b0a0e03030c1b060a0519030b030d0e01022103040f0303060801021b0f0a0b0f040f08041707080708070504 82
    0x1e0246c0c014801540383d158035056001c0308120070340c0300600b03968810361034640380103075035107003490440d05800030510140705040c000c0b03a40384c10448055508210f004040488244110440c041242c00541c41a2642d00180c0410021f0503008203280014000c2d4a1140ca0598115180a03503100c206109007911403800080d010b086903c00c1c0c2d4a6040b1500080c192655040601300b400ea890303146540e00e001e205003202000216150440494400790201d482c0c840c2440c1b5041e10f0700c2c480807010100c41c0e06141d1240c00000d03071036500307006607043c1c040b145c1c03100641007088100080c0744c414115019031400c500d0042402d00041100700742c990107507100c18a00c495000c0c1d0b14048011b803000d6480f140e500d43c001b15204038000d120000301c440c402440c208030303000c001004804d10365601460070094848003d8001007000d011981810581c0103004030b40c0c07017204544681d9400840d9006511030f140c0b4000c2540c40844d0b5403010301c84c0703800501000c03008024860402c2e00c2c0c142c4444451141a10580d5144446 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9005313 1250 9004063 9004069
    0x160e070815010e0a060f0207090209030c0f0a0302040c05030106030506040b0d02060306010306170709140f010e0a02090a03080309060a050f0604020d0605041a10030501030804090c0509091515120403030209 90
    0x4010041400b0302800e200d207585e041c0180008001c0301c5c42c040035020b003500100c0d81c0d410328400c1c0c41c03540303400900621080211105004040702105105a0060a10440400582c030303140a04030140107165545952585020401011144080e10b07191045082c148905c6280c0d4904440d800082e804444041da2031703c9131070050380242841c1d4040306802e0b000400158006c0000320f1802d04440d0741903010711801d40103007140c200c142d004441c422980d4941400500034400a44221035111075002c90040ca40000240002c071411030b15801100c003400d0010400400a806100250300981e03050424811420412210403200400a01003070040e1740c042102d0103614407a0704407400602014008204840c203404070600340403c282c198900490086803040340b458824480c2a0480e50000d1030035051600b401c00c00005060b0a0030f942d405c0100038050501c441e038901600602900500100140615110003030003814503c152594061507014003804200503000180a50300a60500c0c00581e515888800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9006563 1250 9005313 9005327
    0x2090406050703240503120c070b03070207170a02121902010305060303091f03050906090c060f0c030a0801030c051c14010603050a0f03121e0504020a05060c160e07081501 75
    0x884c2c8061407034000d00300c158180440102041d544150182e03064150040c0c0d26441a2052103041030b05a48203620400040720080c01450308410a403045c2e0340f035240e0759450f441c0303840e80a010340d02094110504501c21880c0140d030000c0040c039048050110034041c10070003500340c849003001030705040d02ea000061031550203004541081c50000c01c04004990340a440c0c48140948440e000040f81c500fa01144c00e40e400025940c0c451b042d040b005207048458a0141b141e1038200c504060868901407000ca1140c0b4401e02c0640303c401c11907501d0f040d0a626506103492a01d600d588054000c644d41100391500564001c0502e90187d0021041948000002d20300c0b070041003d80c1c006071981c0562294a0100b20300d81c01c00d074030454005c0d80c610351014481e8480c0d0088502e820381d401504401c0c1c0b800803038a07124540003141c3c0303d40000c25001c7c125075a8408203120341e04c5003000442d1600702100044034020b024243c1405400c41d001c81c4100c0e4174140d031002e44200d0001d803401044500b02014580141c1c801d0032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9007813 1250 9006563 9006581
    0x80402130905010506030d0504030c0b0705010204170102070204060b040b0a08180a05030309070503060106080109050405010b0301020307030e060c120103021309050109080405120a02031c020c0a150f03060302090406050703 97
    0x411035001a402e01c207000342402d80d422440380c001c01e0f004c02c011610850681c0d060320303000408076010502d03146071075005034003036003044803195000d020015580da540f2160b00c110401e000300240c0e031081207204020072140c00d50040350807050140014000400c0407030907070381d007011f041c10324110588910005100440380801003070050300c200300c501410420003101450103011603404031030801e6110700c00c040d1501803d0040758001888000100312100c01900150f030810301450000401c0d403940808203081e40c2c802c90b074400109403907806529986c0402c00c2070682c4000300c00011802d050640d9080740c1000f03010f20010b80300b504100120743e07003006580d000c0302440354440001c0150240c98501840300d90000d219851060078480349070240810b01060100f069980240980640e0707400c0c121000f50784440e800503c0840c0300e0f151001c50245c0318a83e013500640844145c0103034021000301c00404005800701e0940c10581407010400061b107518a0480d009540840085502e54401c242100100f010030303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9009063 1250 9007813 9007849
    0xc0406080319020a0b0a090312060b07030305060d050a030e030d020102030f0c0a180311090c1e21040f06060519030b060d06050412030f0902010813020f030f0106090b0d05060403080402 81
    0x81c0502186d0701d0541d0101c2139040c8030740c403084080d19100c1c810700c007140c5051160304400e030010800400007900c030b0350025502442c0202841218680c1d03445191511080c14411000f041e012001c00d6017510b0100b002c03107080d4580788000d502c5e61404030688580c11401074428585181e0100b030380d140c00c0f0301034988401d91110340c5030381410a83d07490a0034140e0942003d8010b00030b01c12440030403881d4403143d003202c0c000525a43d2100c0200060141902c180c3d1110b40071141c00007034400b600d9000c03810f09181d203000314051525104c42203000d08002c000c680b80d0764841441910b98065500c20001d040c00707401c0031290040d01100b071540c6c80c00c0119000d5050358200070a12881d00080008010303011200c1d140e00308060b80d0030030030019000c0a20f011100c550a001e8003285003000000e04117040c1c0020b006c4598405051003004d8081000480e181c413080c061000c0507a51600c00a2252100a1003032094125046511038880e40d40d6444958850b0000b800240800180c40002025911741d9943c443c0008410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9010313 1250 9009063 9009083
    0x50705092503050610030b062209090803090f010c02060106080901060e041506060813020906060f07050706080f04150c03060b160c05090606090108190218030c0406080319020a 77
    0x32000038003d1030110781061041a407025094891403080c0f1030488003a0001d40114a4411b481c80c94841451000d02604c5892060250204650070780d070140d0700603240f090f03a82c141c44e410250505814038150322004421a031410035490003a5a00244603411035a00c0e040c2480603031110b040f001d014041c03a03081440c209071100700384010007000c0b00f1101040031441004001441d115441200e500707905542c90746240142c0b50301700c00507180444e10b0b16004100140310900d0058544200301c040d400040060784c480e04884020401103420001c09170b402214881c1c40b0321a8030781a9600b6805941c0d00109c1498103644036100341c0014081d41c42070000d00880e6102c00d40710a42c44c0c3c0000707001034400300c08913a40b540040c0006040e09003003071140d00408004243d44d0420074941b00441d94004020200c040c03000d0307403043d070302c62a10551006014161717040c0b01c00700b211310841003070618002a40384080c3c0034920704441080f60000110a444240c00c9098403106c008904520482c82c15500700c1c400751088140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9011563 1250 9010313 9010381
    0x30c070e01030605070315140105210417030103020907080406090c080d0909020405030c1207030c0803070308010501020a02010207150e04050c03160f0221040e0f0a050901060305070509 81
    0x140c102181d040b2441440300344000d41c3d80060450075a0301c68800c030106206802c0c024080744802c00001800500107150413418030070340c480e203808142d07100710740e0b00b000b00844814041444094680c0c00f1000d1240d20780c03149507501d141e012403c1030740020160400c000d8041c0100b020441d9940028031202c0d0800344041d007450302c4001d038680300c600030020703000411181d480001d0283c0c650b000307680c00c58034002e001d80116030b6580c042c0b11044160009501d01d90280403c0807000549032643c401c043c0c40300f04000e648a607a186005000000c040c1c009a040d9071104c20108010707a400140b0000780d5405106040f501c0c01400002ea48078016024082d610a08003005c001d41030341c520014501c203550103a110016070314001d00c19100040300380800e80040c0c002c49072a030b003000100b116642d0310940340d00000e440c5c070340c1e510301403550100161303440c040804030b5605008581400d8000d0641000c02c02e4000c001645c0303141c1e5030316070b912010700c9000d004010740c400282e10b003038210704205150152107015940c105d40e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9012813 1250 9011563 9011579
    0x20a0e0412030b041a06030c040b040303030b01020705040204051f0207180917090307030602090303040b0f031009050c0a030b03030c03030718120b0601050714100903120207020108060d0302030c07 86
    0x2600074107000081d1400507104003a00d4240a070056803110744280c40b80c10b60004003804100d41c0010100e0300d14003000c220001d0243e02001c014401140265800500c0300042000241407145960180b441107005001c1840030395501507a8030301541e8829000d13001d13615240c1e0141c4c18650b040c0e00034184c242110244000005242d0420b01146201e409114115010406498641d000300c850850b016030040e10241b0000e0042e42c020098150000e003281c1c200f6640b40e0302201144d106150084450030044203008070380d4090003601000e807411002c1404280351029403003030b250003140c800c1c000305603c8050038206610701f401110000246d18003946d569241514000e06100003034509007010b00ca08100000d0b9803114000c1460b49141e12240d103c105848030801190160010320080d11a007880002603c0495000c00c000c540e0114051001728000d081801c01600080c401200e0003241c0380104030301c1c00180e9004264542c000390449141c50301d900d071400c0480c518016054001c1c100e204071900458904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9014063 1250 9012813 9012833
    0x10b0402030c090a0801020703020c060a18090912020120090f0402070c0512031207030905030c0a0506010807080309090c03040c03060e06042f060a1202030c0414010503090a0609020a0e04 82
    0x1c0404d440c4412469651030a880c00c070b106414020700142c004640c00f95072894540010002c0070f0080c83e10140061030703281e0078000581e0720b50002d8444e56603104418204001070f040d014100200b0b00080103540042070b0700048800c01146c0c80c15880000240e5903001d50b0710480070507811100030700219114520391400003003580380d5005041c480d12a07110546e101007030000441c2d20f1328951034200da20507150f601055018125071181204c007400306000b6201103032420004403144600403402030903154582500c190a049850304001c095400030400320245d038403003e500b2600a600221100c1d644d64460802c03e800d1000e9410041c411424512101e11100340040c0701c070700660240d0722003c1c44001c00d4030848042a421811700d504442d107503540f01e40750300e400070181900c4201c03810840e08038080c542c03805003240d00455104021440100e418001a6800312821040c1c034801c0c2061465400d00300b66460742c4180c08800200160789411584086458218240e8010005407074100407608052400707004007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9015313 1250 9014063 9014077
    0x40519060815090604030c0206090105040302100201060509010f06090e090a050f01060303030f0b030a020111032101031103070807092007030c020f0312070308090f070b03010f060806010e04020c010b0402030c 91
    0x41c44010000c202001c40104d1020b02695141d200c0d00841001c540c280052030b040500c060b0705000090200102580316100e01c0d100e041d40580c00012100d0501c0100003002c94180c0000d0f40c110b401000074070645403c02c0100041d00d040d0303044e900595840165091070400140350042441c05103810000c000381c03054000c0c3d815644039840038881801071070a060b01f141c900a501d554582d10818450001d940204501c00d2041103050507079141c919a030a4000e48a400c9035806424241c542d0010000c1c05018000c40030070820842c013070700a03a498040c0040da511800d001c1ca00c85550303242c207051507103203440507607840300c1440700e03441c0342c456845040c041c01c030003156078050f4003500c50315019159500d000b00311314003081240c1e41c0b481d040038030548044450f0745005040380d800d44204148440b401c5070401220b001032000d2000c0c1652503042c01c2c81400c48445075800714040c40a0081880030756030304114480ca0294060754010f03140c207210b4a900b400b41082d01e40d07998000344000b040c082d02c0f5031814014040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9016563 1250 9015313 9015343
    0x8130312020d030507020a0c09090312051602120f03010614070c03081c11040603090305121302030f010b0d080d0930020601080703020108060a0801020c03070605070f020c0405190608 80
    0x100c1d602e20501b40d0b16030646100c0180300600e020030a1103140942e40c04148000e02900d0701140d1101034201c3d807002c4070801d0700c20501d800d4a442a02ca180b950401c00281c91a0030340300340500300004000040da40b0300040c092001849040b03034005034001a0070b815108d0300c64012101c04607555580c1005803081d840008003040340342480091140c07031841400b804015084003a002d5181c540783c000114014014030100710100042040002050740d00c400c0128021a8140100b1900310b03d5032040500d0520000e0149646034109410070086940e0310415441046d0000d850550b00e6004030326440090810b180000c0182407482c40f9406810851420013000c0160050026051111180203030f981d05030034403a10102e548000c0301070005520510b01250000d0018001c080380a4031918010b00ba80c001c121740d002e5550021880005100d2203008194111001c0d040600c105920240300944900d48012034a00460311031010845100841c2c040703603180c0d12261000c0041c1138a030301d0101c0d103030403d40c1c0103203071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9017813 1250 9016563 9016571
    0xa02040509010b0a0207090b0103020702040f0c2703031d0d05010504050c01050705070b0d0b030d0503060103060b030c090103050403020f010c1e0302040e0a1e1410060f050708130312020d03 83
    0x11903a81500c04ca58106201e50000c014071031800380140040c05d51903201904243c0c0a1241c20010b0b201c40c06503440380c0f00c18601c081800c01c4400f00040c85600b1aa0002c1001411007054030601c089034100e1a05880c4c051400c02c1d04a01030350a640081c000789441603400024040400080c41410360189005500c80c6c0140c030740e90070300400111554080d884020b8519000454200202e0b80c031000204200090b02d00301041c0c180152002a080001030b0000030045040082007111540c0d0501c030760000707854020300d61400c40c20b00a005003214050200440e051660b9070000c502072500800c5921203d54203200240450008240c00074002c202003104600c88810582680002c68006d000341c5003600c038103c005040d00d5485400703502c09000300010808800010409040d80252030b170203020040514183c40d60014140303070940c0704500f081d9a00580420203044d040140161780413040b03c0300b85412014070760726107000d00f00c0ccd0b1140c0c1c0c3c00340e4401000700406100e240d03103082d00880d0b02c05c202e00326034030100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9019063 1250 9017813 9017819
    0x9010206070e0a06030504020310060b040608090d050409050a0905030c0a020103051006080601080c120c0403150504020f060706020f16030f02010e0c040f02190306050f030111040b031801050a0204050901 89
    0x5a02800b29505696000c81c0f1868280b0082d886680003a0f4820300040031600c182d5031103018001201d000ea0030050543da000501030200301d402105498001c200340c402407810900b10140205640158041d00c0205074031880440c2c03905449170000140b544d04041540d83e07905414a50b541d40fa02c3c0c51601301d02081c184000030340101c204078406411100d4075120342e102603868200444000200034694181a41d0501c03043c0010349600f1052885460060100750369070f421410078550011985280561043c100002c1200684641002c081100c000351155600c850051034010040e02031901c441441e6403000c03818440c110746852003c14101c4c040d880e650030300f080044003207080c1c580d000e65004680d480b0a2003c3d240d0300302a404140030b000726030801410001c610031004c0071300300140e00110000ba00c881c02401185804050080000001c800030494003078a0200030440f40183d10488241980210000d54500c41c0c00519000a095010003080f140c0f6250300d13403000a4225010301405084100004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9020313 1250 9019063 9019067
    0xa05090315100506040806011205030c010c02070611030c0706030b01021207050705010e090c0a08100302040504051501060302040e13080403020303070b01030c050d02010509040e0f1002121005010918020f030c0901020607 96
    0xe82c21b9134038000140c2403d03828100a40e00b4a414600100c4092004101c0070000e48800e00c00d1100541056000d40b100d94a03080004250002004240156810820030030b12043c4000800d4070860701c450074042025403130040182d06102c04054408841307100016a00d04000c0040780c410141c42090300d500e03c050004000b03100c01141c040f10801e021140412192280c6401820340b02e6114200384181001ca50302e80d0f0102d01501c00aa83c00c6800f68001260030105a510716502c80c00750005103000c508140c0303007400369500c2060140607881d03040c0c40c51190406114184d0203c802940c1c000d002c4a41e101e09034940a1086038092005494035900c038200410545001c1a510074020b40507510542451001820403000b003161341e44d906214411109200d41001092017800302c488a51000141c607410b6440960000c110010294501c07880da992040c807150307820644a170141c0e06091103c59a400340c16500e90700030b11a0001e100c68000e0080100300c03000008500410641c082070b0b00761041502e03403c45c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9021563 1250 9020313 9020317
    0xb0910060203030f1b0408030d0b09070903031101060801050906070909050106050403150e19020102011406060f0304080d05010b04150e010504090c0903080f0a08010b040501020a03050a05090315100506 88
    0x15600103800400202c1c07082900006840d42002105c201c0010b04c2c00c050303581c04040d034810f03880000c10f80c0010a101011030310030712800244d2001075400d9602440c00800041c2000d000f80801802d001000c00c80051000b400d50003840502104402042241082140f00d41e49901c1118113100141c83c1f81c602086112150103054102c500b41c4d02d6150401e42941e0b607001a200c9020f0840c44801d03660000300d0402003080025940880304540003000340e4041c0d0000a094508001d1402c0c0c00e5100501440426202c0104171400702c178003008002d4883d11189450515407064004009296042400104002c002c0700f009104494241c0c8000c0c985116040040e103601109860160100c1e8007070004000d50403064200070084d00039890240c00c0140c0303d41d2803140036080300800c084a004045800c54400ea0004200c030701401300b04590034141450580002c1d175a900c401001010020041951302c81c003809042079071507111006081d200091a00d0b008040c0c0050210b841c4005542c242f100001c403401c080003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9022813 1250 9021563 9021569
    0xa0c050901030902030f161a030405060105100507050a0503030f010e060907031802040230040f020f01090e0a1e0c050906030408070804030807200f01030b01021c030b0910 75
    0x2505410120345400640c001d201d00c50060783c050181c0300701e031030229400340175000344c41c41e45101c1f1580035070034a100500b00b10710040034401c403c0350400920000c903000050050440e40c2c01c481990003002c6400c402ca885000f0f40308000c003240300714414201000800f00103144a9442c05001c4120741e0f90f10090411041401c2c0c1d11a40c03c040c0040209107802d100b0340100c0c40455540c5d403042ea006403142c0c00706080703178490300011006040d030700303203ca290720740021a06040c0000b00781c00721528141034480d0030308054000c1c1c000380f0503411350007540c9a603401004100c00821003145e84060a142401c1100040c0ca08107851160001c1038260700c0121690501c0b421016803001e95a00381051a040c05001d0f20b644058029541c0c044140501c0d400105090001e0016600c00c500841d26540d1a240901ca6a210200c951030074286151f107052060711000400b1040074030074a00841c4640442c8010b0f400c115036085009402c07403200c007100c0d20694144d0840d01003940261031540d03165480910790703170700122540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9024063 1250 9022813 9022817
    0xe10060815010e1201060812130501030b0112020904061505070507080d0504051302040902030405100501050315061306030b07020c010e0907080403110102040b070303050103050607030b0603010501050d0b030a0f0b0a0c 95
    0x1411655890401c801e0b0380742c8070b083d0715000046d46502c8016803484c20b80700702030090000000040803e40000302a40010007060f0030308090003503c0d226030010702848001e801c07281e1200d9011440400fa984c0f42c1e082000242552440401152101e04c4000c145501c90f00b01075840b0701c1100710000349100002100700e0b6070902070341d40b035013000e080104000c02841c0c010041c1040755024400490584100c1c8000c5025600c40c0c002002d10900118844040e00d00582c4094030070341005111801e500010302845601330002c035400724003202c82414600090407a6000a040d003c103000c100709213250005260201c42e80300b40c807400340444040c81008464801102d090000524200100c3c000078002d6408801d1940320340d0000d820961143c101c10196000141e0030360010b910303100108240141404401d4100c00d480c40c0074003104d0141c0011507043c0c44103104550410100217241e0440b444a46c0c001d81c902d8034020181d82d013412541c03c245002c500c0304141a2401d40e601c4021031841c46040c070407000380045d69 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9025313 1250 9024063 9024077
    0x304090e01020c0105090607020d090b030105010c1505040c0503070e1e04140f070f0602010e0c060904110403080a0206071b110604030203030d060612060b031308040e1006081501 78
    0x4a01000040d0400044005180d9000d21540040d40000c1c020345104005075002044c9a1809141c000d1a10341220070610501c4080701c818400e035a0078508680c1034400c28200404202c0311481c09501da0342c4640c0000e80d0051070f040c00d000130003190070300d0081110800c03000c42d201c4a40ba4025000d130544203644000c42e040c0d20011a0780c1400c41c05001c568001e0058195003980c0c0c0324050404d0400c403c00c1040c500c01d4002580a000583c204030b0000080d05091008005080031445d185603201e40703103031496125010201c2d6a404603036842e04a07441030405c01d034a00f0748441d035a151280003508103800b5007004d030081100250707090707101b4042c1c02903411030042070007050255519602032644039603040c29004074040001001589042005203010030b210007002800900c1e20304010180c0300e84017110103000f030032708000700102d082c01d9007500d0f04044a803017484072062031807400e5000c51086910160400e900721041046000000043d80200c51036500d46190790341c0c601b0b4001c8104100441d110b80802d4103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9026563 1250 9025313 9025319
    0x80f0604060504060207021e01092301080c040b0a020304170c180402040f0203040308060f0a0b07030e0406030c03080c010506061911100513021206040302030901140706050c0a031a030304 82
    0x15001280c0281c0604c10062400306103801107008520510515407554180356140d03011940d114800e007000703000240c0c19051420711820340a41044004803100e040141107004654a5205141160300610704124260380d02c0d1946c4402035200c1e00244a40c0c62407601d01855040b0a030700102d11388101820060000c0309540354641c4110001750098416600a651101d00300142800340c80254000ca000b030711904410700c0e06c081041802d481aa550500945c000d04007006030610300070a48110b2036160504002c060030141c0403900500e820350004c0c00d43c07030034500000144201a4014000c968615000348280c0d43c644041c400a44503000300c60701480b50405801d80300d6440340041d25102d107400c4090340c034074280307201102d800e5a2003941c52248a81e49501c0d003100b14580180800e0b4078190807405003005142c15103000c0d480b0b020b8241c0641c144111440d142c2885039000e81250f02c0070741d02540411160805007100708858010340340000110740380c1000d042110704ca05015401d41c500040040d80b400341 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9027813 1250 9026563 9026573
    0x213050d06060b1b0f0a05030d0c0e0303040308030115030905030406110a150203090c150904090311030d02040e06031c0e0d0f050102070516060c0b071e0309020109080f0604 76
    0xd5408015660340c2d946210200b40c1e160314000911401444d88004480c503000005503d041000300300510041b54828080307280041e40100540300203a00e155000103000c400c003401515200c00036030049505002c002408402c0201a101031811707038200b40c00400703104510075015811904483d0000c3c0081c0c0c400d2004004041c031444c0809114401d000c00d0303a020700c0d01580c0c1c0802e591901c50006c048942c0100030400010b0040105505045081700c20700c58022181080413a6840307000c0085000c1c0f0b495451050606014150003002c4509142c1103039a1000d849800c2d0000b0340150040303141a480030404540720745030000313020300e04110031207820401340154032054640044005207180c024200c1000100403507901450350300e016000d60300150359149146007542c1043c161214406d003120030140144903543c2c3c4880d00030f2542c1d922044861041d1a0090207031460700d040148425410110102c8a1401c0d40c90380004c0801ca200385c032501c140715183d001c0c42e42c8a814480803000258418400100031030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9029063 1250 9027813 9027829
    0x803040306051b07030309021302040e04060203071403070c020108151f020106050a090e0601050603012102030a0206030412140309030a08191410090605011b020111070602070315021305 81
    0x360751007010000c803100032000f18005800c0074034240c0c013003903a0b0508103080d424206000a0100c100c000214a4182032800c688102070b00a800940307030560105c00035590b02d001d00307140c1c042010481081c40d00e92401700e800401881410500328001001d01010070340030031038014140703079016004114a0070201c61800c2c0202100c08003084104641d01c41c1c038005501d49039241c210000c0c2403000400710308d442502c05079030f150071f00c10707404103000724010801005074a106005604946007a6503200410340b800b800000c0c50080c0c0d1242c080d40c809000000e00c002c00203025072140600550361100d4041c0b00f076181948036030307000c115141c08550700704000a9044520910a00d94412170022000f50f40c614140f07a210101c413021021050140115820300c081180c04890203801005081002c0c0b01460070000020002d20320707100d1468a210810001200316070180447c1c4050704010000c403501e00f80d441d10001e41e10b6001e8070098600d00c400740d21000310b20041c0d000300c4880b66841860700c4c02c61490070080c82200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9030313 1250 9029063 9029071
    0x5010e0403110a1b0e0609090a0b0a0605040f050601080f0903090d02030709061403071203020703020609130c09050111010504020a03080901180609031208070903061806060801020309011401080304030605 89
    0x70f00607803460500040c405103100f0b5000180f0405004d1032070900f20b40191410700038050310300c6441c455003049081c0c000042d540c80d400e82c1c403202c00101c80d203852000102034840c541040b41d01c80d04026040e5030740f1886521040c4a040e00340d0702c1d0340084d01e400e049440011400e450400e03180e0002c02c0100c0b0a410f0440311030340c4607071000e012654504c0d03656002504440f0180c00031b4015411180c0342c0f90305460100119000390114050316a071a03422994041d50fa81d05a100080c010790000c00c421505035116282800000c50f5880184031400003104010980080e50081d2804034110b0400507002e000b052003003511440c0d004d8580c030301c2c5c60304580320249984c01010800e0304100c0303017074200b6400f0110200e00500500700764589000719420b600d048081c0201080410040007218020019041e1348061080c04a94000c140050031407022100ca4006000080018000c1410114000b400070015802540304040780e000810610f600e001014080c05000c0c40381c41081c2d0300902c401c0c400b05a09500081e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9031563 1250 9030313 9030347
    0x302060913020d050402040615080109050a0902040e0604020a0f0b0d0504051603060b01080c0315040b03010609060602030409060806090607030506030c0d0b040311030309030a11070b0f0d0c0305010e0403 89
    0xc0c0510440980181c3c1e1040c00c070525481e8640c01408110705240c05402c02405201072480b280031251900104100414480c41440d0368841001c01d5070380f40c2e1035104002c4540c0103030042c0b1280c80c012079800d036101403d4034100e0180b20030420002d50001038003684426148103110143c90320580100b110050b200140050302c00e8007845442d88010021554107100442c0304034800b042121b0a030001514180c402040340941303800c00c004000700365200c4600c00c0c2030403d00f1180000c0780c046c5240440c3c01085a81c1164800c5403a00c070300401c1d008c0c0c0010144c01110f004800134041e080d140c0794041d80b0344c0d00aa4117164141c0c40350020030340860081c0c206540c0154084d040b00d00324221500011199130f004141500c0050103101072205040c0d102c2d150b11104243e160065155040101449650380b2492101e242007207158100b0040550040c0041c2d070040c00c91075005520790010006181c81076200c100c0340c9500ca480d0a040601c110b019024903030403900c90200b9481e050343c840d201138545038040204041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9032813 1250 9031563 9031579
    0x1a090c0f091c0b04060506030c09040f0c050a060e15040302030601050616060c05041401030b01090b0f0409020d0b0a1406030105060711150903010e010908030c0703140a050702090c09010903020609 86
    0x80c070581100c00460340b0500800402d50b55003018100003044400103090300307001e43c1000280030860f8445190032504540d2051030008001201c0c200800d101e840794100923801a003c2c4c10008101c0c1c0c0c070400307032100744038100c0340350141c1c81d13201c098040244610300c402901904154010405841c01c50090700500c84a83d490194400d503941c0c402080312420801c6001049000c10240075881105245071004802800c2c108a4420b140c2e0001e03142c0302640c8164290140005a8032014088500580c2c000f840303200025500c0702c000b00a2240a8018240c04502030000300b003000072418156044042c841501070101803451342450180221603100a0083c7c0304118400415a6540c41d210001511021144c040e00d0b03c403642c000c201425110b00300c5010005078102207024021a6865045a401903800a0000d941c1d0300b0500e000c0d52102c446426a00c036003280410301d106810380010040c94414030880e030910701c03075484d540181c500e801039030f006900144403170005000605100700107110788840242850307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9034063 1250 9032813 9032839
    0xf03030c0203070f03020d0806060c06010308090d020303030114030c06130504020d06051305011a040303020705040c090e010e010905010b03070f0f020c13020705070807050d110a03020d0302011a090c0f09 89
    0x3504410b070391341d03088005034000040c08161a9110610369080f0300200d5000d454101800400c5641e43e2041c00301800c0804006100303403042d130b074000c42d40c4641030f0301405603a181c0d030307481c98503e400c2c20380f4030285030007030040815414641c40d000040300c11050889a50842d842d0802050200030740100c3e0410b1441ea83c3c400002c5890703500c07480c2580c42310a11401c0407440350f0410703111a2840e40d00901c01420b6400912007440080e40203d880d4042d00c2054500241030480307503100711612481d40d4400b011703440390580081808000882054103075424800700303100f071740d0740c900c41c884040c40100e81c0c000000384080c042000312840342041c103a0352581841141c80c0d040b0003100241d54500324500e803071200c0341c5c0041c3c0102040001c0c41020000c20100c80a00100f07480e00c000302e40704843c85e4000405525a03202d0b503d213207680e00e413008005542c010f000030780400010328019000700441b8000c0e2074810403002c4001014501004050b200c0c960880f5691f013420408094440a60007081c0d1060303000da0298030175 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9035313 1250 9034063 9034073
    0x504061e150c02041b0905100c061e0203040803041101090302010e0607210c05010e0309060a0809010e01140402090f070504170102040506030901020a080106020c060316020f011a0f0a030f03030c020307 88
    0x605107030700c000d517110407201400440182000d1415071005000c1d0814220042c0044e410041c00784035190004004194890340c011b4000c4c00600d0b078140501054170100a100c14030040501075482184241d414100010441c0019141402c06100003030016620044901b1079080c1000604942d5100e60111134400803401054080c6491210741280010112489903007404402d0003881284d04a01c0e01851421f5860008075000b446130301520780a0000c15008500e40100940c401084402c4020007041402d81207804e0314400711054a00fa4813810a03000811403500003142c482d0302400041d26a2890720749014542d400410006007402101c0d5070078000040c4944918008601c208009000140e803034004c200301911101c01a0820421540b120840745459100d000c01c03290061806000881e4002c1700300003c0b85020100e138803001e220f508002c0b201781c030035441e01d4074111140c0c4102c0c2c401002d0000703007007403150804035072101401030b80501d00c283c2c010a000354403029810744603205032440c10f0340603250307 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9036563 1250 9035313 9035321
    0xf0809030c030114100e0915180d0503010501030f0e21040e040506070305090706141c020703030b0a090b01020c040b0103060f03080403050d08070c060b03160308040504061e150c0204 80
    0x61103080c0c00f0131a08200c0542c510313441100291241c60321060b0340d820001c803229a29201c0d8014414000c124a0100c1d440301c00c100300d0001d4040441080f2141c18500782c9008000390003e01c06c00e404a400d02c0348502c05032880e4029004940803090040482c1d0036074081a4500710b10082c01c0d8038031000104008200c0281c0d00c00e60030721442c020710090550b400d15110041c11900d0007042881c49030003182003840103540c44040403c05209660882d5180c1190080d41450448244c1c03032102120b1002680a04040d01502720403640041102d008008030740c1c540c01d00054503c8400340e80d0044c2c011414980b90362400c1e80c0b10707071400714042c07400081c19510b4400c0d02041d051150370a980012010904001b0090300304442103d140480c41e250307134030382040b6001901404031007100401090301c600050002c0c1c4c40400c200700121101356200c4188036520f0600052650243c00b8240c000c1d42000b00c0032812003a4441210500041790309100f58035071a00d10b203d20444155241c0c0b0007002180c0c1903076400b50ba51405 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9037813 1250 9036563 9036581
    0x10c0302030103020f04020403050a080306010207090e010e0f0313060302070501090c03030822020d0201030903020c091023060403020603041713060314070f050a0201020712090503060c04030f0809030c0301 90
    0x5005075a54154010031040f9003a01d900705100318010042031000400205035195082e0744484007580341c4d1110b80060741040841d400080c9207924200e454039081105410003031654603040145e8401300300072909280c6901c65141407089030700c2c10b04e2041154510a900401b03d40d401200000360891507a5500c0c903480ca81c03944142c002030a020300b8413204441609400704180309a00c901305001d01c0a9010a40b41c140445011b414160784172511410f150081c00354000c9400002c180078020303e400041e00b1100e0071785001c2c0800309507250701c6615420081d1000ca920226005000e1410a40313541e08001441d44000d20032a061000c0f050005204001107028042440e0416491100c060030964014100c0d00303610328400300c00c61090240130005400558512a2200c0b43c9003a680d0740080d150141e01900c80d5250003841d850042d05088105548a100348054032030440c1070b40c1c911703222048400b0007801180000740a0081a40806000400940080022841c0034040d9943e10303900c00002802c5801e00340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9039063 1250 9037813 9037817
    0xc05090406020301051513180e0105010303050d150819080c0105070e0f0906090601050a020a0203030c030706060b040b0f16080d05010f2117040512010f0501090608030901080406020903010c 83
    0x3200605c4140b910711a00401102c01102c81810080402031400700c8401300c0c45482e056042842940910007019045025075285030f00003842a940c2d81c1c034004066500c403103a508400c0b46812155441e98018503200400c903403056008040700c1401842e0f042162801d06030817030303802d00300b0000c00c20b120600380242d40c801c2d00a9121600318034a44010700c082c2d41c58994850b48207102000810001d070341d6800304260002028a4125182c40803a07806915202c000f00c40a03616100200c1c0300d42c3c80300c00020040c001c06100709001d0040a070341c2c0644d280c950040340148107114006101c1072011842010242c03075805500e40a2105a0600351107150041d030005000b0b000c001c2c1c0301d0700180060003440c01c401d0000c02e2902c00070002c0c40b1440211890104a58200500d803c1e9038200d01081011202e00f80d4014010091240c1e400701d42d6003280e00e0090002c6280c3c411b44509140000510840c10702c1040d04494404014600d00382014004407101d0780020001c840a6500b80310b11005130f10248218680400c140d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9040313 1250 9039063 9039067
    0x601210c0e040603020603040b0405030405030f030c070801090506070c0c0e04050307120f171b12010807080304030305070b060409050f03091306080705010c030c0209071e0315050105070c0509040602 87
    0x44014054030720103a035240030382d040c40402c10040c1c0304d605c112580160480d050a6144d140e0f49021415485541d05c0140d2502c00e0003541c904080c804001000c5004500d000c613080f85955010a03800d0760b41c04200580700d904550002043c45014003281c00c8000d1003000409000d6403540520100d02e4001d075810b4550b584041580070800204e0403a034928104181429400c460014500400401109500d6a0011240800f0402c800d642e507907803601541103c03000544400345c4810030061110240f080c1003661042c0140018211408802c54050b0381c1c040d0390f80c03440e003849612103541720400540066081359890750780c880407a40c2801001041e090000285035182814020007200c02c00e4526980c02240c80c0000030082c0000004d003410890700300b070030700f0940504141070076111544582c04c043d42000040b81004403ca50041041e40b40d62407410303d402000010110803405c03030301c034030411700801c4484100c280415809078000d4501d681c07007804007203c0241c0b518040b401981e01075800711138103900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9041563 1250 9040313 9040331
    0x120c05060f09060f0c090d1a0c030f01060809030307031d07080f01061703071101021e010603020103060605030403080103020f0a0b1201060206091b040f0204080102070c060f0507030207050603060121 87
    0x9000d42d03a0021001e41c00c4098a060917580c1203201d2007591942ea1040c540d00310f981c410082c88951440d8451480440c070b581340e240820310f40c06260720451b0180e00c2c17000d1000c004143c00340200075840c01001d24900450640c5d841440980c001d0004044521171580081c0905101003400c00150000e041d07108090b2940340c012510460a40c0c440342c010707618000c040e0781c00c0b01ca0301c400081680d0ba8030742c000310705a041d40b410030010b1303042c0405c80d10120005c0140302c3e0b00c0884804150009000c6030f10070b03a400c0000e580c0d0b4400c101c60500060310018000740c14203004101509d0416041c1714480030040845200540e2070030040d0345035115003003007a071503240c0c000108030031038050048581c000075030005840d500c1d9603080032298811006104510881e41d440301007411503030590507203002c0c00080d80219561030b020308003000e0705922842840e001400071101c1030550380c80b40064030f00030307075050b0000d108050414007001407075040144403c4c100b00058290000614a00304000d1b10800b0300140040e810380 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9042813 1250 9041563 9041581
    0x90402181009050607020d031e0302091903030507020904050118050a020405130206030c1c060801151a090114070804120b09010203040809060702010320040e010909050a120c05060f 79
    0x107030440c9100340800900e0420079500c3c1d080c1204c9495a0454141240d42c94a02c0e0940f012400a002d40c000240726000e4800d0881e016402411180f00840d4001040240041c40040c000c1d01c0d400010002031092241200500700f60b580d058000744160000303c0d01462656285032801e4440070300f41c583c2d03800114008198201880342c1c54100d081c50f01d28924100054010070010311001d004000003000000e00101440e40c803004003941c0501c01402400003540c0d030100f4501030104852041d2651015200005402a9080200c014180902e00c618140400140151080f00034a900a05645c50030441c100000e01c0c00401400a40150954500c40301d24034203000c50060002000304019238810810300021402001c199641540104d50480e503c8030b4500c0120003404050100e2503a540d00d451040240d40100405041075425620613000c160b030380c13402001c003520703007513003000e03149401040d030407000b11340d4004656018656074100091044083e9487d1407400030105c542000115800092101c045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9044063 1250 9042813 9042829
    0x2041403030903060403050a020c060409050403030b0d02010e1c0609060203101203080a090311070902030a0c03060b030a230a02030a0f0c08010510020106080303010f0501020c01020d0c02090c09040218 88
    0x95055000703506201c82c85002ca65030b032a010b44080c042c0000881c403400040d100300402d846141001c0d283d640c480c0d541c0d801d298041c10f4162000c4010900b0441c0c200021300b041100c3c00d00307582c0c0581d0f0307900c5951418004d011480e010001c40c07031240e0242d00181d5000c00c505000303007540c582c49584010f035607107080e152014600781c0e00e4000d0284202d010021201090b8440c8449400001c0c1d14000207629550b454152180a2410500e260500403c000007420340180c0c0c3c095888ac00056600703000c519000c8908804950290161700e00101c0b0a0012500d410010703444000c0901d07900302c03107516007143e8203409200c2180480f0702d01103040c1c00004000004060307016007420110341143c1401302c6440f403100980308280500420340207214000d41c00f00711502c04d40080008040b1a030903a9940c1d6110081852411003501409025114004c230480140d44006020100d00009135590001d0140030350030000e400e00d000e40703039021015090001604a44d07071440108100102a00d14452000305041848401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9045313 1250 9044063 9044099
    0x819020303010b0d020906040503010e010903090609050306041203060302060d05011806080a03030c030f0213050901080303010b18010903080a08060f0405160810030c0f030c0e0106050f0901090b0a030204 89
    0x1034005000400551070040d058030140941c01801607142c032500808510140a40e0744021751541c00d2a0307072682c0101c01940500791403030013a0385a6006a8a88000b60740c5500f0038800c0c1a0140e01c80d10006011900c40000521040c440d403502164540e80d270b8000400c01d0f0082d408640402d0307074610041148000c1241100003c0703005036024050b203440c04203100d07142c1c10311100240503d9159105c20043d00d119511441c924108948219100da5000f010007290700c4d001e01419008010640000c94016000402d581c12100c26181c071900d088030100544e4420310901e4449e0307050040703000012001070f840340c0203080c5103100360313481c52803a05c0c21000f040902c80305a10018050f5180c501032100030b001582c00310001d652a4100041e031515800d0302c0d4140c0302c1c4541d0019090006c000f1021500d1100d0360088812a405080010801c5403251184a426202032040501294007008001c849200c000c3c05072408040c141030217608503a03240a035040035030260025000081e40090140440010303142c01403c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9046563 1250 9045313 9045317
    0x10305030310090c0c120e06130302030105150a0302010c030e030d0509100314070c020112050a050402010f0503070206150103020c06010f0f080304030804050111030d020406080601031b020a150b0901030819 90
    0xa600c100104c0505032442c0b41d980588102c2d010754032071007524045c480c18400b440000c0c0455566401020800780f441760503000403880781d42010086441d0341d030002c000d03101e180d400401a00303243d880c5030b005407554103e6130012000d00c880c442d0382818039034080c814085540a00e854040c0e5071840c480422009d41c50500070403090500c0c0010420984e20100c0500341d0104590a084030b404074107000503241d103c020507440480d075042c6010040340781c42076004140118402c0c0c07500c550107804640142e540c2e0104460820041c0d01110020b030f6202d0308107240e10030524060400520340012b1607201d42c24030340c0907040741c0ca5014040a040165001c000e040384024a4540e029600305420340c1e0360b5600320311562003000c0c1049140807800c58030040a000311807201096880c1107580d0743d0758040250a40408981e0f20380880c0c50014440301e02d40d58004d0a21410180d98040c110340010b0340c0d1419580d28a0801902c0000d54030328072040e0a4a031400d00340d0286004d890307601d84072210003010b002c100e085520080c00b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9047813 1250 9046563 9046571
    0xb010602061e06040605060f090a06080411060703050702031c11070303170901060503070315050105041103060d050c0d03020601050306070504060801120203030904050a02090f04020a0c0605091501030503031009 92
    0x1031608003004021219814801402d101d0762204030006000c2c05040c0c020b01c2d0b212000040b0a43c1c05007141004000660702a11100101d5658080a41d00c4050444014020084215400c0b00c50702d13240c1c0080c903d4521a003009418110f0320b4001c030745401c2030203c01c8030380d0480c403800d0307200b0340360300b2140c2509100041001000400d0842d13030014104100a001c4400402503000030500c076003030039041000030f02300140481352aa99a41040301002404021800c0d41618000010400e030500d8007541d6100101f842100e031440e210041400354140055006407010b0159030504080c3d550340c061810b01b054040e034003d02a55040108046c103040001c1d000c4000c2c400c0820040000035002064a170441da1003441d42c510445890001c81e0442c49014610b5920902d0a000c100702000907a003c3c0a0749541600d6203060140142d0501c4200c1c481c0c1c03912940468440307280000040c6441e081a40e018074103800360b8117400000180707850003080c01c0e0800ca4a0b50004070800c582007603400c6a10000300a81c000c180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9049063 1250 9047813 9047821
    0x80f070606240309050703050f030406030c031107020d030c051e0f06060102060f04051c030501090b0d200f03030414121204061103280e0303031012020102120304030504030b01060206 80
    0x80c844200d02c1e510000b411384070f41c41501407290902804000b0351300501a078410161812404e40c89500c00d00510340802c1c50021441d2001d07100f841003c104910301c102051a00242c5e8007081540402d0040c11020048100101d0001600510058034240040000c1001001c0440710280c1003401d03100c600540d5a000c001001150b82e40040c02a030050800c1d0b02d4444541c4071030402d903040201d42c08818001081c81c0d007001d810194540d100d107049030701e03007a02081500020003c02c0b101d010a404094518491119001013030822400038034041d040042c01e58001100e81c90110742075030002d0344801040e00c0112246503ca00f090b40050b9004518840075201461000b8400001c50045005010803c66000c40c2400b907400c0c01c008440c0862000302d044403006842428402c2482c6650140c800001d4040001100300c3c1000801e0340d0003040c2048022940310b04048084041300c100c850264114840c18010f61210711100b002180114066902c561751181103003003611508078182c1c070500c00c641c4048200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9050313 1250 9049063 9049109
    0x903030703050a170106020601031e12050d061a0702040b0d120e010302040905090f0d05090a0302060c0106120f0203010506010c05060a05040c1a031e0403090b030a0603080f070606 79
    0x1038204561504110351074200c1c5540c110303801c03c1a140702d111540500c40c00801c1c403a0300050407604882c0324518104c6114440d1050640da0f01d42214014000340e2050141c0d1041c0707000780c0142825000b001800545596600740c140701d032a042500c00025024006500c0f02982051301403616020000e84141d0807c2c07009513a118680c002e403040020400220424614442c0c1c13094046800411901800b840141081d040d082c4d201d60b00b0b06401034440c40307510b410101c042d000b0700a5854010b00141801c0a0a01d5a02404020f500111610a06540c0d5000126501406002201d00140900400c80015807184141400c443d0080e0206d414011288580700000d400041c11a501112201010aa545070386c0b5181590344a2a08000d400787d614500c54200000528090361107545030018201e100402ea440c0c0c50041641503c4c00f500007100c00b48188010041000216040302d9541e5000400ca0307560b03110450550040740003080e00c0c07240019001e0501095000d150003030428034500380c030203140811007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9051563 1250 9050313 9050317
    0x71428020a030c12140316020d020c03070b0705160602102901051c0501060e010e040c05040e100504060306022808160c051605120309060301090203090c10020f070506090303 76
    0x744240701d4002001629489261803181ca10580c1600035228100803e00e00540d842c80d03000c0c40018460170b9050800c851001540c842141000342c0376041450414402e0b07601a13000040c143c56a1003110704c6d0720390352220009400300411042e4041c004076207104210030b080e24010480c4e00c00c50246440c0c040718114940d41e24001008003400e0250740c54590310408600025000303d0001054981000007549540000e10501801400da89018004000f60100b0045030303500d54140c00014400e100600208031107000c41d50b08a5000d244046a465468000409840068004450b01034001c02c803420b88076181d1008680c0710b808050407900032204a04001c00c140c070010120940e00103001d0b0403040b058003580e000307801039400c4020f0f100f8008070040c0c1036a20440301d1007180c0c0180891681c00c0c0b0702d400080183c0303900c444010000f6146901e444620070103074001600240060041d10b0218844d60b803050f210402c0108a500904000c4881c13600303490400e00c5030790103113020320310030400ac1040b0b41d00482 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9052813 1250 9051563 9051587
    0xe011206030c0509071206031101030e070308070206030601121104060909050702060a0209010c0507091505030307080d0b0a0506120703050105030c0a03080a0905120109020907140d05071428020a03 86
    0x100d820181e505e210782251540201c0d0111403070303a07107000d4000c02441294418510080003c0e28180000d400084040760741d2581ca10010b443c082080c00500d00500e0400010f40e04104149014000340211110345400c03035480046060519000040400035150030624503801407040b08000c000c140b4004d54080c0d1110401030801c985280d00150f401785507030096070400e02c0642c0110464469a40750483c01009000c000e080d450068119400000c4c1480c0c00002c4500c0240d11841c440d0801d028100710380080c08240d4000e690003140a00013044940312540548090740c0d0104800702c46040c44c41000e401c441c01a0801402500f01c081c140019072600c849000032aa0301040c1143d4500b8005002c490401c541e800441d804120303880307081030800b015048554194001c9500184546803104155a1118281c6a07400301000601c03c8580d01d0641d58030580d03008482c7c0c1402c8882c41c0c801c041c0400903501244c12103458900e6000c02e10344002003914490241603c2e4001015845c05c540c90203410105040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9054063 1250 9052813 9052819
    0xe030613020a0b0a0207050f04020406020a08030c0403080309060402090a06080a20030316060f090b0117010f1b02060108030702010507080d0b040603060b01032003060409110904030e011206030c05 86
    0x2404501152610b02d10400100003200701c00340c8410361280020b44405076845604d1082d420109100c0040c6403610841d011070300ca94008104220182c2e4a5a2040d00010036040701603509010000c080340f184c1008500c2350142c580074156515040c41002101d42c2d01424a011061804c04c044c80155800034601d0302c5103401c02040140d040841c5104a000440c030095990540004244040c28000404030b004686108520912220320404030041c22120560406072911035441c00400c2148421005413413860942d40010480d00f103440301c60400e036001440c50815900700050342060706a41400b00501401045000e103180402d550002400c0f03002e800340141444100240b500304400c03071640540e01c070360300140083c0005a9079003024001082202a0305001c0f9040070000205904406030b01d07480c245000c0c2d4441d095071901300902c001000c08480c01c954541080801300055556140c405101e180300c0c0d0788218a18409000043c090540303206000038613402d0290038800184032400100580340d0507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9055313 1250 9054063 9054091
    0x5131e090206070c0608040506070201050601050304020f04020c01060303050301080c010305010b0904241508060319031103070209010b0a0912110d0f0210020105010603060f180209120d03020a0f0e0306 88
    0x6000090043c03040782c2008200910301c2c2d00018001d9001102c09104501035000e40d03000d50b803910030590907144101c1d811070025104200041c010710f0595040c1c2008a8081c00050522131090340039402c442c055001540480c502000400141c00708025618450324281780900840d4500384c00110781c1e014094069200e170f0b446d54404c44001c00b40300100c1c00881000e1280c0c413007480e43c51001d000400d404003400000500c01c01c0005095003000144842c0c1c604000c1000740094600c0c0d2400c0301d1407000848440c29601041010380302603600d200341c49000c0c19020f620155030b03030305111024002e080390364050151628510342c1440411880040c444403400103070b9540049003003a1615000000e61030340300941c01011b17042c801351100d905600440c141c85107920100120f81d01d46414100c018110302c0343c2020419010400f000000c0903401505031020098000000200347c040f2140c1011526096000002c0d80800c89900696010703a036500e2120301c1b410000b103040ca4071801310f900d5100007003104503c0081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9056563 1250 9055313 9055331
    0x1090201021504210e03010c08010501020606010c0c05040207030915020606060304060207050304050607060f05090f1b04020c010608150a11030103020f0f060307021f05010b0313080f070c05131e 85
    0x11360070502e0b900345030031400d01c0000c88070403074060700c000c003649002d501130340c604501c05105c5030180c1c1040b410398030140c00500640d554107004440c05044400225840a03155000144e00d80300c2e80090021070303201e5144c1c00034903814014450524024403201c4011540901c1c14482c9548030841102d81043c4c100c40d0150b03a8022504003148bc2d44101d5100a420080025080d070a004150740a00d401011140c024422600d51030b0714540d4454000f42c0880168100103200c00070100800e08860b072041e030140c000b509000c02d1001a5003190039641c886035541d08124405040e186082e201c0f41c1d400564644100640341e9100c0c0c02595138041400024010b0764403000c04005079a4401050300d0010004090303c1ea01e103024140203403071307042c5a042411440c600c00000f80f2104118050181a2422114010309568840b2240c1110000d0982c043d80e41c0f003c100180708442003540001c0030f15034065007481c640e2915003010f00c540910f035040d0240581345002038050b800d000c009840c441c40b610000001c210081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9057813 1250 9056563 9056573
    0x50315010f0b0708090a0f03060b0301060b25020603070207031202010c090504020a0201020d0608030c0706140a0e01110105040b060f0609100810050316210c12170a020f07060201090201021504 84
    0x11905c2d005642c40f4150540016044c00490503180c1983d01c07070303641400f11507148420306090301c03094011a200c0c440c05005510560301440f0300b0079000100703101c203000440d4050b004152598010307039904c001a004484140240401206002c00c60400c6100070080c074500214011301c4441940074051080d6000181c44080341d100f501030752440e000515080003003540c0c902445039070b5444040101c0b0180106080001e52a000701d49200c4015064860316140c001da40204465610300c00c043c8a0502480004031400c254091140a00c1144194a03030241410a04204074400c50134810491080c01d042015003c13031f4556240080380b8140c14244925907845991f000c02403000c41d600400c3c1c0500c034184800030060f140b031803250300f00c4060b41c000e01692102c802c00e00852190150014100c0000c6800c1002a42d0070b08141510003409020080b107080d9034500c2030401030b0320015070240103a000303148400c442c40c0140284130081c01c050000300b101000c90390000c2c0d2244555074500d0841d41c1d5031000102402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9059063 1250 9057813 9057817
    0xb04030e030d030b090108031c05060a0803030406140f06130b0112090b100509041a041b06080702250501030209030114070c0b010e06060f0c0a0606060207050315010f0b0708 76
    0x400202038500c0e140c0e02c404000c000f0103422495521550342c5400001380c18201000b103a010b00c05620340300300c2264a0315480005000040c00080d007002e40640c0014a03d0014405180128420078000c01c41610b21020300001403006011035078a00d286c202845456a81c110201c20000300303403400030030516014001610140c07401c070111403840782400007080c20010300c1c1060a02c621240409105256203480501c41001c4085600a2060601c00c14541500715181c145503031003403148070543e101d0301c07690502e40c0c40c2429540c8041c1c007041801c0d041c010030342d405200d44480111010a660504281d500300e0076100303401131050605055001803181130b02c1c3c400303422216034000312808400c010f00304440024a813110507802074640d00005400400c010481056650044000401442c14461710900c05541070b032001c900c60b00345126203440f0720300241050241500074900c03070700684009440c0c40141400d0000398016081f990040600500c4104003a140c0c6009072900481302c5519640e82d841c11014074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9060313 1250 9059063 9059087
    0x50f010e0d020a090c020f0a0507031e020a0902030702010e0c0a05040e070504020a081014090601050307030902030a05070911030405061803040b0309030a0e030109020102060609060604050915010e01020a0f0b0403 93
    0xf102440c0104034040e0642040c266003d2950881d4070320b00020481c036840d800605001030454000110400100b0700c60440b0343e010708c922081000b5486490760001740f006402d42d002c2001e058020007001307081502803080b6003584040300090845046070b500011480701c918000c0c58840d07999072155914000c0b040182c0b1000d014050407c5507260f08010001e001600704071101040065014000710354890100e60803042103a02411000c0b05031515001501e468100410041c2015a102100300250703034104155107a0301d02881c00f40030520706040718802070314214126015007078800c200340b2001410024a00e5030181c0c8180b05a407406000100302030551180768000441503601009110042e00040020104009103403980d04c0b0f0071021100345401c0c1e821441019015800590009a1505024000310380c00300c0020441407426854900290500d2429a40c16015540c00041b0400958220044468440c000d000074280d00303040380e86418012004110080078040d491000c83d00b014040e078040541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9061563 1250 9060313 9060319
    0x1008011404050f07060203030a110c0a0b01030314040506040315090b040605010501200c090a0e1002040e01090506060403060f0603140303040b07090501050706090203031603080a15050f010e0d02 85
    0x80301052085540e11044255000d0750280212003800f0a10301000407100200d510980241d4150360b110440ba200904964264040c0c0c0c030302c204114044904d003840384085003803044a000c9070329411400e00802c00d0542d4a1000c0290340300700800e00c0207030350b40c1e0259021654000070348050079a1003203121000c0d103149140240300c2c0e10b288040c0010082250403e078141c03039003039032441d44001412030000c544261018012400f50001c54189000342008652144d1080301c905003c5110a03a100029250140301910001195030206060081e46000c05409005200c5900c00740600d041c0130000031140d1280340b000404041e5210350003951402103405c528025900704d03420a031400e030021000342d100e5008a40031280412503a0004405c54019007294041d24410b035240d0781840c001d540c0d154020200791070140e9152005204110440200a41ca40c2c1c000d840703540c92502c0d0f405d05600c1781041c3c403030320060162034580c4a031083c05581c0b40c5000b0740c4414a02468040b0b42e0b2128240410042c0401d0403021750 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9062813 1250 9061563 9061571
    0x90209090304061202090a050d14030a1d0604060206070c06060308030411040f090b0112060e0d0903050708010504020f010c02060904050408090a061806140c0601030c090506030a02011403100801 85
    0x8a04001c0040c004407001c2d0b80f100c3e040400ba480c4c4100c104c1c401d4820b4a580000e51079002d00c5203051404441524920031040140600041c00c92540385402c002490700c0019034445254507100d9143c80105c034000d6094a40c1d604041c10403601945070b0744024011400c00c5502c0c030a00d0705000c0c803a004000210303040b0020980c1c80c00d0908011501f100380700e41c0c1c3c5000703a080140720000c0c0892440741c000c001e41c201030301352043d900301010303c03180c3c0e00354032016542207072601d501c0030f050081071010030071020070354450b01a02440c1d40b40203820300b001c6901100507a40f4110401016031103002a0900d600b4092810321401480b030300c0040c1203800f0b034540c02c54200c1e141004000030000200000c040c001d0003200c14024580e6204001c81d800f28140700c0c0801c0c0103041e5101004241d02070081e504003d40034a51884c1801003a0040d10b25001e0264008e9400c1602c980040010044600c00c040c2c21040980c00f50860510940001e013a5092158503c0005440080040c10108003010980042c0c81401c000340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9064063 1250 9062813 9062821
    0x60a0b04080c04060e090703020f01020c040203010909120203030f0604090303020f03130606090608030913020c0604080304030311090907120204120b1009060e07050a03060b04080f07061404031401090209 89
    0x1660b00d101e61001107004518040740420032032601c0d804e1310300c100003010007042c1d00c0c1d01b140e089c041300414141041d81948130740c840a241c5540d444c00a140a860b4058000440715098240030304104549203400041d5041001400020700c0c028080d00d50000307080d1004603d202152900310000d00c20050802c24521011041c41442e074880007610000d03c0c018001880070316100d480c074034125051403040104a80c002c001850880c01c2031b2585204680340300c80014200074840d6551400d25200329070172580c08400108000c101505486405959010303007034220305140c0980003144650301c028100c4c02c01e01c0000d500c0019410010b8040341d026108540a5242c610420316040076134000c180c6484200246444000c50b00700e5091240c42c084803190480801261075400050303406a100380100002c26880e00030105040384250300801c010282d00d402061301c801074540107400c0070b503d50015402c00150001c240558101101a0707019030350031114503000101c18221035401808046802034100740350340100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9065313 1250 9064063 9064079
    0x30509030712050a020c030309100e1203040308030103050d180302010503060a031401020a030f02070308180127050606030a0503030105042d060501080106020105220f05011e15030804030b060a0b04 86
    0x1501303030503140c0d400b00d80c1e10003003400c10542c6034002c0c954441e070080aa50103108095204400b07040c0c0811024040b006000c444e2001d0b01d04651045d08147c40012000004004201d0308221400c0c00708000d1400c011080d001050040c2c0c54040da2202034108800480494855507c0d0031000300110350160000b011310380940b0b2428041c0d0002c40b400c0e400309207400f1051040044a0003240d04d021703450380e04c03407000f651a094060142840c11202187d1503595502201c80c0c00381a41c80380d000030700c580b030345100c043d4070500d0003514100f001807003103000744c01450307003980000c2c00001503a0641c1c03002c54021070750166504c01d40b02c601d411a42a036a0300744000500885410440c2d1140d0140c1c2c40c282d84001d544da0300c40f4006d909840003501c032040101c0c135074107102200c0a00e41503d54055481406400080000360300c0d407a0035a541008806124420b180c07540e0343e044142d01c1201c1100380c14001271000d02d8995141c50059003d0703880b01404031000a0b0025102d55036182214028113008580e4a0b00e6a0f203440306 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9066563 1250 9065313 9065317
    0xc02030313090501061b0b060907020a080304080301140303120106031a0306130203011416030b04180c080c040c0e131808040312030204080d121805010504050c01050306030d03050903071205 83
    0x845c00410403030014160071114005145001c2074001003165150346804050002040004012000314012919080005030a0400450049001d0700495490707504042001c0740c5103c06601c03044c0700398030400400054031280011181110002e0a002559142a0120110700e200100005601d07004d04c50811a0420488000b102d049000741d008018103141943c2da01c40b50301c81a6210103200301b0038084105003900c00e400480303101b480078002040701c030500d00c07804580d0714092400f11012240024248100442084003c1080e9001c46050010040056020304266482e000c544d01481d00100205100c40ca59002402c2a036000003c6080824803410b02c0a2150058041210344417401044422100c0c8031740291070580d95a40c02030005081c4905083c0c542680920300c0d0040c0755160700054a090855910a111b0107002c0c00020916181034a0000e013429000507400341800000e00c140710140e02c00085009030f01c1c005003400111a10707000e12a0f4610700503c44020f20a04c4141d440e50075140d48000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9067813 1250 9066563 9066569
    0xf0303011404020903060412051306030506011101020307090308090312030108030a021014160905030106080102091203030403050f0f040905040f11180c22030c0609060302030103020904030c02030313090501 90
    0x68205403000720801c003d0784140485664140d002d0703008580469000740d0b800c00c8078102c900344540382c00c0c03100c0952514144558096000310303071f03076904220442d41c100882d001120344160003186145031458024083d40c0340c0d0300001e4103030000810b5051030f03900d08110b50380d81c01e00c105da0560b4403981d44203102540c03503000090090041c01041c0000012840728040c140840d040c5021015580d5034030100031800140c58405603042251491001540752000c0c0702c2c19001d0804e010000da0b030340c05070000f03021407000c1c08620480694030400402010903070101c181c1c0d01c4000100d420fa95144006024040b42c0e014603005010700c00e1401c070902041142940035415858414074403d903074400c0a0040000f05541d1813030740c0d100d803081c4800248416107144020712400c121501c0040c4884180c1e2041d2240c40d51540048030f1012441c01d00340841c83d0801001c1d0f00400c510702c1c00f98603641c10355020900790303a00980000e0034054200c071400115542401658900313a0700c0780003140c0440d5188246009003101b84 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9069063 1250 9067813 9067829
    0x1090501021e0a020a030302031302040504030203040603060b1e071515050a080607080c0306010207030f061d060415020f040b07120e0103090308010e0601090f080303060307170d0c0204020405030f030301 89
    0x780c62400c1c00c40d01c2e100740c64209034641c002d807010b81e015031400e502070b51008145190f8111442060401690380748680c03030103640664010b50300e40d41130100142c121140c9401103810000c051003240c1241500c034032842440600c4a0513180c41e40030320f103041034562903181100001e041c240034055070410354945070002202d000700c6444208c0c41d43d508990361120030a4820354005801e00c4001808641c50900440c3c10610600c110f030102503494a950400e0202443d040790220f41302c03610820900c201984007801c4603003038409400d0707505103542d61110718090b40c0108001c0d15004140c0301000349204081d140240302d20031496075905064600311702e00300000c44900e0042180401c0040311548244101114294980c4420306603909000c0b494103401801041c16042011100001c502c1d0388072560f00e60000c00142000f1a200d042c0307401094202072068104012010041c2210b41da40040000e060654480a01780200c0000301e07030022401038402ca4110542501c0703510380b19040903000000540c102d800305 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9070313 1250 9069063 9069097
    0x103060b090d0f1b080a050d0f0203071203060902030a0903020f03040f03020d0203101107050d020303070c1428150902030d050a030902040c030606180303050d0b030705030109050102 80
    0x900080355081c0110340d41240c20064034005540003800700c0740c0c0780c03196034025101596403a40c001103c00348590f1a0700001d100e50030281c0039004211080000900781d0046040402c0c070b040010000950b01d024602010b44221080310a164045020303510060281488140940d584e140203068140900f0b8000d40881c014818010072100003040401a1020b6840c1d2004002c5410b2450b001c02c402554094001e07681400341c000c03003070301c1d000341441b070941c0c0341a0000340162a440241070281c02c00614440e8401550810002c00c55501d9101c07543c410781d035a01030805c0761001c9002c1001071030321110056050409102c040036208010004013640d5103548581c4680b40d4140c940e002c240252220410029095400301d08540b40c1d190040c8082c00344049a45000102d8035116000203050b28030300343d502c2c00480e5a403402844403e80c8440743c400202c6070040042c1040b8595134009026101d00c1e50380000365aa00d441c0e50f6610380d424480d610082000800a0091082500b0020b000790f0143c500e1464040381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9071563 1250 9070313 9070319
    0x5160c0303020f060f07030209040204080105010f030507090228020f0601030302011d0304050a0b031f0e040b090a0b0f1005030a0503040503010605010f050306010c03050906070507060e0a14060c07030b09030306010306 95
    0x6440344584080d03580c28845446c0e815080e0040d410410101e0b0344181c09000200f1000000d10943c0c8c001c0c04000381e030202041c55402c0072801c010403034220828450041001c401c960b8481003550f00c0340d0701800300000360040c04040880c100103108569402c43c0c0546030000003030581c1500618a9003e03001812816856111034080c0d807846903100d01c1c0e401c20781080e400c001c4106c0b1840590750101803d13400f00300312140d04501804e000b96503040308546020740701c02d01051280380ca240359880311111004040700e19198440d0908c2080080c5001085045a8000b80500720b103500351100420005e002c80d141400b0350300d8925203d40150040c64003035032070082c0004203076104030842c280080700750300c030b2a1840d142e41e0011500071012040a0301400403c0149481e41e40305c010040400034000c10103410501e04100d00140a6100b5041e483d01c289007200d82482848105000b00c00c3c1420200c070070707907070711602442c02c1c2d41002d41c13603840904142001010480d1182c0d02000030341c03040c0006d88e8204680703a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9072813 1250 9071563 9071593
    0x90411100e01020c04020d0213080a0506010e0601170903160302070806130b010b0a03061a09010e0420090d0204060806150603010f0b070c0906060201020409050603031e0a05160c030302 81
    0x800880410b00590105040d080142030070f074000c02c0070380300c04140940b8000800110300c425014940c05140250702040e6070509012090111a014001d2080b0704403c50503ca0002800791806038001000e07206410701080694038104101c40c07005658000c080d50401540c00d020f9203890140c403035038a950056400045051108841000b048d550010003d504d40e401c3c8200010280c10040c481c106151350381001003001c00751412034194200090003040e91382d20034040018014480740318442d009905003a54600c3c40c04512012118041000e6000d649503003030000040e001c02504070700650414909038002c94820f0b0040741c100c0c0f181700b14454254161510300d00384107891000344141c100b4289180800d00c10300340080c000300b8415028004260702c07140c0b04e442e02d6088402c5d80c0d1040002d41c0d400201004200c080d8000c40e540848110080c50a014240c0150050040e0408050000f0000090300124a9003e00c050300e01c1c40000000403140f90340640782040440001d40020b0f005880354680400041c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9074063 1250 9072813 9072827
    0x150c060b03010606020a030c05120d02040311030a110f03030f13080f030a09090507020a0b070306050f01030b180601050f03010303091409060102070314030f0c010c0e030f0303010308090d0209041110 87
    0x80d00035402000c6c9000f0580f011100e00b1600c1004840381d010b03d5171284a003681d080c014110600c03c000300141d556266107464019440c1c28a0918080d4001c0c1701d001d0040350321400500004202503d803102c2100000b40040d044d031165a074142103440011030500701d0000d65516000980e81554200d50000a0044100da0b481c001d81c55444c000a407112000e000b80142a0400350308807000e0700445185050695861611360401c565501c00603580f41c20400c440d01e1320320032845241c402070070704000f4001d80a01040c0508004803429414140c00030110b40c03580d1003901101c0f0842642e8400310788950f1645001008486184200050316800d4030141e03103c3d2820401c81400b90714140c005122451566540300e54481c80940e5401542c0810300083c0c01c9680280020a050000c0c4000014003040c3e9900250940000c075070800e000360f12103655526010f00000480e0b0640b40c0018966896040403800120032030b0305c1c2103000390050540f0040c002007010356600d2400424088070100130485001034211030300c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9075313 1250 9074063 9074069
    0x90a02010206010f0b181f030e160b180303090d030e0f090c03040303050402060c0703061e050403021906090c060314011a040902070f0209040305030106020106090b130c09150c060b030106 82
    0x2815040204a100104000c80d5001c0351b02c01620542c01e52003154030400075001d07400340c90404a0789584401b0002203091004018003260030000d448500e0801c0403044290103500e0070f800051420700c40800c92550200143c5e54078000081106180519030719000b480c103602003494501a99102518000780e14010340824810461402200d08642d5680c030110082e2401503c181d8210001700545910083c0a0100d0400f03580201c01c0442c4801004104c030380580051204880d142d454a800d000c0003aa0100304200c0c13031605180340c80301610460900400502d01d10340014083d221590380000c3c05501600f149034a00485880c0c82c03078a80c3d03200c030190008181d900b4006484001004180f002482650203412118040c3c000503c5408070b41d03002c6003a449040d81d059000c25404401040059424003445c0013034402c50200340703c1d900c826004a240300c1c02204403501d02548600c60403641c2c074407500d4140020280e290496441f11816600030b03252103008401998081d042a00040039070505005020803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9076563 1250 9075313 9075329
    0xa030e0f0f04050601120f1a100c030f0509040603030306080607020f0d03022a0c0909011407050912010c0905010905040e0a0807021f080703050a0504050604060f1103090a02010206010f 81
    0x50050300c4020003005000050a03141804011811b000c2e075040c892040500580f01c01e540000c00740315500342c001402c038065041c80d12440c8401c0740d60003101e502082003042c0c4d951604085260818088050b645401804181c035041460441c0010502d0b500d50041e800b00c424050943c0c40c03940311901c0480c0c07280035454070303230405030b00002c038444c00c0510a60041503c90340880c03c0442e00400d4203074440c1e44940c58138040c101a0300000c0b00b04010315090444940288500c0000c200e40710b4904000391503010020f21003000e01c600801d445c2c903251105003120a080200c040200100000182c01605003601402032038009200c0e280017050074105446642c42c4140c480d170007000f041175079039601c40180d1702c4041c04a80000000c00c2c054500503514003401403401107520348102e0b92410310380040031540001d1902042c11300300818800401d80c045202a00286c0010307000c2031400714084c11034007502210349146500100041048107030310b00403400030340301c034802d80c242c403084c6e41d80c0c40301420501131074041d01d10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9077813 1250 9076563 9076579
    0x70b01060f0302040504020403050c0a0b0414010302030a020904050a0501210302030301090f020702030607020604030e090103030503040b04020f120c10020f0d030e0c040207060b0406050405010b160507080a03020a030e0f 96
    0xd0a000d03015a68a400385407030302616094807140480c2c01d0382c0050348100d5056004a55101981c90100c948601501c04008090308161602d240c40300760f541da442e00301e4141030b40000862004c006a070111810040c0150050146007007902d441d00c003d00b002d1085c0100d0f0b00b0040c080304102c000d00440030000903003540c0107505503401c002c0d03064003c3c070003c1161a0741075403c015401c0107032420701809100d00203580140509103403604024102c1211381403004e206640c903500604c0040c0c2c001e401c0d2500960041d840d030b4a560384034404242e4001c02d081906a20560300c2c4403e2001c000b001030381c80007406003500c283c10300340b00c40342090340da0b02d065001074541134114099064085219600c84080201c80c441110498940d00000c90100c0e4000706040d42c03060707190b408259403410940641e900070030064404000f150326100c8441d40500401c01d0414005c124821220300340321040240c0c0340070b00444826101d400c410351501940d80c0e145414220042a24002c480d10740340b50200c00940d0080d805003c480b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9079063 1250 9077813 9077819
    0x60403020103050c0714060f010510090303030f140a060501020c0d0203150702030d0212012301020601050d05030f1b060a090203060403051c0501060e19030816080712020a060b0303070b01 82
    0xd0081e290050004591003014070209010070703200310100041501a101421850912102c204003030001604014090f08001110381a4bd6030f01c100c0c090116030305031500245584100740dd4801a2121031000f000c21054401402501950303940041c044a109030204d4200070004800e020140c01c82c1362000c5d6041d00f02e101007894548203c4006644210540b050b42c0c90140c410b60503000300d8103c01007180305410b8400040c8031290031880f00100700007100620b40c0200b118100001e540f0001402414040c0c1460314941b01041001c201380e41d5122181e00b106a00d6104889801c00a01044210840130748915004150340141c1da204d40340110307030044d01501d40341d565601c0c00d4a140e0b101c030303144104040c541c0e9011120301c800e61090034013801c420b580d0f03000c0c030054800070414039100c3c40d450400c2100102104200088142c001c40f0301d1003050041c0c4172440e610768101300209000c1d000c4040d0010841c00b10071040545d0124840d600c1ca4401c400420800041c001816640c1c02250760080c00700d10080014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9080313 1250 9079063 9079067
    0xd03051311030a05030a03090c060203070506010b090105040f090c09050d11150409090f0b01060f0219020d080a12110301060f030911150301090b01030e0d0c050a0c081014060604030201 81
    0x2006551005000c40f42140e11680e80c0d9899a8040b001020020303a6901c02c0004000f400c030b1781500204020b200035410000680c42d102c1c6c48003410320410b00c14070781c00201804a42d0103502564000c251000e101070010740c0d00c40c004002f038a0b21040d00d40008030802d0700030a1515214032460809170700300d500001e00714120410b00c1a11410a602340c8480c04081c0000030f9203070340a000e040c040500c281010b00b0600800c0c9040d601c40041a0006024060106d00d54400b00e036002803500e601c250000711003c8902c4a900100c1c0c000103002034050f0121000003910b010041e040080d801546e030744003a003004010222030315035181340001e004803400601c1d50310303504007998800d81200b00c07250301030182080440c480500080401c696400c41c079689180100040003080414895040d00300020300303090014520300003002d80c07500410038000d8280001250b200303042c81810000360007001c0d80002c0c1035101c0e64a40752240e030340c2c0082c60f8103004d01c41d0400c02c0101c036805141a005005100c058200c609003070541c4c0c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9081563 1250 9080313 9080333
    0xb0f040b09060708040909020102010e0303061c060906020f04060f0206040b04060504050709050a230c0403122f01050a0b011d0105070807030806030f03040305100f0b030106090c020d030513 83
    0xc07859205005102d0320300032902a00003000200807007640000c8141071440003909641c0c8415440c03840350414401c12030b207074480c0500c1440d0090002900450b00c611482c0c120003c01d08210040c02092010170180b00c0d03081904010300503200d07103455250b0f0100300000200c0c0e60b41e0342110300400072025800440c00040d0103400c5950050701c10001e07104507503110440c1c0c000b21407048641d883c07000d0b243e00b8025104031680c903e040381c400d0104000401440d00304211000b5100328400100f074401d031004004400340c440c0103142030b00c2410720402e4007509024440210682d00010180d01e4952829010400c0d944142c82094030b0070388107844007040310509000000760041c50240d201d0510a040103440005901c6070001e118161207030303c4115007824541c081c076242c81c1e18031041c4c0a4540c4104014808a017001400c802c15001130400414181c00841d56640581225000223070550309050001c2400f151a40006058403007544c00c85200b546201401c40694105407008001d0000350001c0300c0c049600401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9082813 1250 9081563 9081577
    0x609090504050a060c030204050111010203010506160f06050702030301090e0c010903021009081905070602060103050c04090201110d0804050105060103061d09010209091501020111070809010804020f0d030215010b0f040b 96
    0xc1920b4000f0040e403030705401e6818908040c0300180d4000b806021560300600b0000c00c511a4800850566040c407002c540b01c0c0c81030301c160140c10610301820400304610b600c41d00001c9688540b0601843c10004006590fa410a001e005035450070030000041c0414006119074140c84142c0d202d224840ca15002e20440c040e48461200070051401c00c00b00d2072410400035251003a8802c00c0e070700306803e03060400c281040d86c1c039081001150400d02c0104080f520001d401c901c00c007004c80e000101001c01744010303960a90b9822510120f07008a01d0082d0302250017460031842240154001c1c0300070751341d500045040741d4403030107504000c2000004611481d4549182c45600200c030600040c43c000121b070015050030412102a8104849401581c240e541c0c207016160310050210511403c00c1e26541d1003840ca03005940780341e410081981c0008003550343c0c8420a038640c400141410245031042c0c10002e481d4005500040d4140b04680c4c00041c4649201046403a82155903401c0c90178582400c442c8074042e84003030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9084063 1250 9082813 9082823
    0xe01020f030f070507050a0e01060311040e04030201050402040c030c1209080405150408010e0601031104050405010f020309010605011b0b270118020301050a1104060507020102010e070609030c0801060609090504 92
    0x140081442030030800003086020481004652212420720306189420384d550007090003501000000c000c2c22800080050540e02c3c83d040c04251049071003642c42142c0660f91007400070340c21140c00d0009050301036005500860080e00c0c00e10821080800030b909858902e4003000004164104001c49104141d101075203591007000346600d801da03100700052100311b020010a901d41000181006000002d114001852003002c0c0601050742c519150541011400814980501d85500c0003404001d000e5005407001e14409100310340340e00307160f40498000c0034540a10350115070038408503028180c004100d20038940c4c2c04580c5041d10b584444561701c40204544003801c41c0000f0070030f0641e10450030b014101d0f0700c0802105194000b401401018203641000c1c04603541e9900d4454400d000740c02c5601190180c5025050003540c80c03905100407401401400300c85d81d414024800c002c03070455404074021085a0144c2241001251640c3c1c056088540360f00c62880403451103003007001a01e110340c20059200b230150b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9085313 1250 9084063 9084073
    0x5011409010e090103030807091d04060b010309020904110a060305010e0a150b0304030c0b06091b0901050409020f09040b010f09050d0f02040f05010905090c0102060415180803190902030d0e0102 85
    0x1d01241907002c2c217801c100c0105c7c1883d000c00c04082c1d4049140303401890f0700d043c00d106d072440c6c44058021900c03000e80050240c1d51100160311003a4040c0e000340742c0c410b601a09180e25850107082c096140da410b00a824442d00d0030007000100c452003030003050306813500c095414400c2d4032441c7d00d10b001003840c03030400c0540c90031100c2e0004500706c2e010b000c0c503c41c074003170303160641356450b94a881d080d0502c00a00c2248107012441c10f11900700c1c09030300400308004449028030341e0f035511400185c0b40350185601c8640d4403400010040d921046010182a1804090320184004240000191804d00084050f8000620605c0042150303240101007101ca940c000c01c0c2071038450340d56801080c00d1724188401820210b44800040107441518442d46a1144019015080c49480c0e480002e4881c000940013801651300140110404d08072540f080300c0701014001c88980c02d03591880e12956542040350011041d40569054246c1c0580a002d80042158003c02500400000886c140d0b070110f0b440501c2c904600c24 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9086563 1250 9085313 9085337
    0x509090f0d020604030906030903050a0305180d030b0f040902060708030606091002030316091a030903130e16030612080706110c0a0506010b0a020d050307021603060518070501140901 80
    0x81c4a0344898040030703030180c032041c5030900703025101d5031084e840b5404142c03815a405001c00d0b84102078543c0001c00c8d1a02240d0360301c451075101c070764088920290342c8500840410014154142d404808000c1054070788104480c641001c000880305501400f80d004a010401c1100003283c8038000d65202d03100a10450400d4034903030204a4074880f803550f030409a44004140300c4028210141e40d040038806140800d14a4101a23040031900700b03442c60700c001c0000100100e400e440003402520400020060404805c40d5502212581c0700d40981c9c2e4060b090041070f1001c030905100b0300032001501e2501c07030100c0e40c590b05540d407200940d10012098610a81d0791a000e5440108040106641440c000080c500b01070b143c206541401d8041e40070000000d4200720031083d203030700807c8180542005041043c0c5030ba0750074106a040c0550044e000100c0500c0b140d011040000940c0030a0041c0440b440c16001c0c0c17008110300300c4e610002405442d02050703040c0d0240b81d01a07080b80040c10520010303d030251006c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9087813 1250 9086563 9086593
    0x601031403040e0708060301180510020a030618090b0f0108070e0703020909010807080f0313060806010203070501050a020d0606020307020d021011010911010f050301030b010303050d091209080106080102070804050909 95
    0x11344070440080ca9801c01d01195203024054098044880c44100007a5946540d409036256050b402080c40140c000c5000c558039406a8425001040c1d40e09100c6100e045507550314005007c42e52085803007003004804948400f81c00fa04060586500e42c0c020001141881d141000181000b0103040c10550200800c00c82c5846004d801802082808000c180e2070b42061915030070024100000c09082d44103100840604140714004404c0b50600d0402002c0358890030300407400d600c0340c0d800c0a860b0390b0a103414040d208482d9402040e0056003103608200a40c0c0f00c1d24200d8492041140181d44181001401d130007514002d24a110101a142041200c5105504001d0700f0760784d441105645010010740e00040d50358002c8022400350980e8a0030300d14641c155601c640280c0c106000180c00c1040105c0c0106485020b603000111440d08802214164221a0001414103a441c0a44c400c154204400000c090b0030500070365215036400200103040905182c28003208450007889245144100f039010b80c900c031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9089063 1250 9087813 9087839
    0x304170a02010f0e030a05070f02030a050d0203030f060108040209040b0601091706010305070501080108120d1107051605060a021209040f050112060b0303030112030302180301230901050702060103140304 89
    0x140daa400102d12040c010310450201c80e074a540c01c40c0b59030820401c01e04a540c0c000700321181c195111001c100c0c260542d001280c030b8008821b20081c401c0c031030b4206400e122900000a9849620f140401c1c08959444000441d00f00f0401e0f0390094208980d43d02150004940710a51984604c06243c0301d0000d83d503404245c40c41403505800e0305540c1c0c00000041c4140032092080303101810003800d0911295250402180d0f80303035942005800e0b07a51020174040ca501c001c40c1c100031310b000f00b030340c025648402540c2015500c1c1d0a040302d0000c8400c24030f090001d1581811029034034100c0d1141c000e402840d89120080132164003905400e50f1145d80c0f8581044500003a1240c1c50203001d528900c00c0f0714680a03d0b0560840d01d0805085110b680f060004103c01c030340d802c001d031007a50723454540940c80e211410034480201d4610994a54907508064041200f2201489801000e00d50180081c44030386906807120300302d0303c090b10701100607004a001403005c203850100400750100300d2003c4921f440c0c0c0d80c1140c03d03d2a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9090313 1250 9089063 9089077
    0x1407060f08070c0b240402030606070b04110402210a090302030904110904090302010608100e0604080f09040501030311010b04061202010809030706020a0206150f010807110102120109050405071509060302030417 92
    0x19a404200100c20301145c5060083c1e440e00607502146141800390000d559400348210080c10070300440d0018007080401781c108803110902400540d00d580764000200b8841400c0520310000c0d6a8680009080020ba800744044458040c0c0103107140481d4081407001400d00030300300d00e62500d000c00200c2039689584c0300d6052900d019a000060b00e608020306541090510b004a00e0b5560a0180c85941c000b000700701560429442008140d43c0e200c2c403841c0c1c0641e4040c480089a000380307003000000c207154011a10b03410b43d121f540000c2150071003000c02c00c42211064000d043c02d50803440342030b0b40107500590030550018444c400701c1c3d0a1010b9943c034402aa40050808001a0401c009020301c900440c0c1e040c007110401203c2c1540d21090000000f060590300a00007010403100c4120614160820760440d1a031400900c40304550f5030312491481e0207440144c4085669109041001a04000410010503140c05564890010600c0c00320304401941010304180d90803006201d00c2d115201d9984000c1c540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9091563 1250 9090313 9090331
    0x3090206030f0405010e0f030d05061302070f0501150803041202030319030c09050a0605030f060a080a030e090f060102030d050901140117010501090b0a03060e100204060504031407060f08070c0b 85
    0x403a1a040c134009082d1007140700701c0c0300c49500c40940c034030120350084180c8261400d400c40c0001c1e16980c94000958001403500c4140701c1a00c0003404030148034050074a410712600a400138018803090740800a60100e0314407a0b200307990403d000c1031115004003800002d416000070100c074102a0700f4030503604218840c08000c0d0200340d035205001152504217070001d0080000711901d4400d0752602c1c80260051000411000038000c00f000002e24030360318200c511004c2d000040031a90808105d00e8054a02e54407644c0552113440c030513000a004240070f2325036a01c10001a0b002d0343c00c0460304003d92020b40009400c0c2503095481d40e50500325500e10f0304c000c134000e0034100041004044804213050031034074103810540381107003004901e800907241e5141ca84200d9038040c070001100368400706403504011002e1410080c5a0000400044655218028006030790140b040a0545440841500c0e51200c0f24410b12000c140c240c290b000b9406e018101c442d42c000340b0350800c010400e406030780742031401c6c42c1202e840c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9092813 1250 9091563 9091591
    0x70b0901090b0915012103031d030f0c01050901020705031c0b061903050907031113020d02040e04020111030307020d03050405150403120b09060906040e0708030c0304050906190b0a0309020603 84
    0x4d000c6100e01c18540c0181800d51003880400c84180d180308529403805409814103440e2075003e200c85410016150300c1c1c0181009a03511403400c0c104d0343d081588036465459166080901181e040d82040c42103c1d031241d808001146007002e249440ea411280c081c070a01149999041d00030050303201c0d08020714041425403260030a0f0020320001070100c0340c02a000c915541d02c03010307003803000078800030a1504c1c4403030032640e600c2d1020030304001001030300c0b5213143c3c1c82c4000d0011400040e10038250001030b0140e41b003601c40d415160307031105c4071660300c0c0000c940240050344501000741d0040d0280d44280e820030700031001d032090305402105e48541e401c800e0f1011400201104244420702c420b500c0781031100982155208060b007444000100342007030143c03141d8800e5a485203082403a400c2000200000d007a040280c82d15004c030319021a450b03800c030744640c0e8002c80001000954500e0094601510410300c0603050306107904000702c0f204560849000b000c14581c2e98800e80000d40d55841c0514428205081c4082d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9094063 1250 9092813 9092833
    0xd0b030f0f0c0a14090f0c0918010602070b0708180604031a010905010f030302100209030a0b04050c01080709080a140106051306150e0306040803060a0e16090501080c070b0901090b09 80
    0xc60280f003684003c2c041004840c141c0c149a8030b0000e0303140c2040d01085601c41540f42d201e000d91281c03041d0100298081e4031140718000c2c90001390034840c101e41c119000d58051a81d00da150528038810310740000e003c0c500400148924040001503400c041402416a45c02c1075100c0d0b48401048441c41928a4500b4140b00108680003007405041d02405100c2101d007500c51841e50040d41d41c24910080601441d004079094100ba1400c001d030440d4140c200c6a090358a0910342040ca40b600e04041c422070004442600003400315003c2c241d11021036003d0402000c084c0070688429801240d860302c032010654803440c001032240d6694200b103290107000d45000a2207454007440c0103018844401c407000780810144018071039074000c102c60794400c0d0041e0020760360f940c510000403030848561700030004001d2680b013440b1000d1426152070200c044281c842d0042282c40300010345801c0c0e002c81e107011000004100701000507607103c0c541500080f010b00085042d119546d0350040c402c038121240742e0980d100071844 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9095313 1250 9094063 9094069
    0x406021201060905011b060b1005030403020c01051218010609020f0408070905060303030402061305030d03090302010b030705100309060b06040603090c0e0c04030206070503120c03011505040503030d0b030f0f0c 92
    0x90051106042902c035062130000060418002c908640c5070ba41070744106201131007100c6e00450312104004100900c032218000002d002070700161801d40052003803040c41c00303195006400b141c40f108503d901c4000b02c0d9480e5120300e2034440f481981d1801d0784d5214400001d114003903001800d18030f1083e9824545a80c1006130561030284d80341d00244600e4202024000703c1e0b01c0200031250040d070181c1d401542c4074542089407101b04407650005030140f08280800c000e03154594801052244a58001d0260100b0001010b507905400e002d0654003076103138140012010b00070350040c1021381c8107040100e03c400c42e03c4006840c580240d4844030109854200b0082001030140100380a010000000480c6080c4040381c07034030301d000c2c600000b80074600004030081030103420400da8001003404c136584c01c0c642c03400f1310382103416410a11400c030042107500281c1a00c280104191429914040c0c019428074104009103409010031400154160003140d000d046068401e204d50200a50f0520040125800341000c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9096563 1250 9095313 9095347
    0x6041101020c0d0b06091807060513090e0c04020a020c030106030b010806010b0a0507030e0109080124050303040515070303060e070216170c010f0909060e040b01080606010c0303090317040602 84
    0x2c5481004141c5a0b10002481c182440380c1240c0c06644004031507070303440c0b0f0305003100d00c0744409108948241000001c006911200034100c00700d0b01000885941e5480107050142c841000c1c045116030003004910071503040aa000d041515084e104540306020140040307800c4a4154206403480311070b2030b0062118100c100031040c014891881054642a4901c4004140d4010301600500300840c482d00090340707070b11440402010704221002080f40d1041903146c034035070303405c141055107030310f007840a00103031514001c4161400c4503409040228031803008080c0031655400140101c051540e14040469101a0402103510a8281d60014a01f244590004010040e100d500c45818510307107082d9501b070f02c00085101c5e074011a081c01e20482c0a5113030b04091b90301510300d4110304040c030301e000030020305100d40c41c1d4401e000d18015000c0f01c1569813280d00035611114202c4d5040d001c0784074501e8890000f8400d5101c0d1503c1402450b1010401c034603840c0400c5074080a482c182d0b0b20940100f00c0344801070030118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9097813 1250 9096563 9096583
    0x50702070f060c060204090c08091501050102122206020d1d0a15020c06160b0903040b030609090a021806030c010f0f030b041803020102030f13080304080a050c0604110102 75
    0x303103000c501d84110444518298000d980401400001c000100803158060310080c00c600710061103502030300540240f04a0080b120320105100f007410300051416501103035416208184d010348a0300d000507440c0c03032881e8007040140000a46c400302804003c071040c40d20101601c60340c0c0c00350403001c030b0003040100300b01c0440d403a200e01703410ba47e80103038420340c0e0300b4080700d040740c250060345503400004000036424014040e0106400000c001074002980040300c2145150b00e124042004150b19a482419a203000b02d0040d000a02c0040010950b10324150481d294008090002c40340309004a5021030344240c4d0103420480c4440001c42401101d10f000e00444080c0442071030103151403a40090001c00d2840d00f01150740900d03a5914a21030643c8950704103d981136600005002021070518000b07000b5802260116110f10b18100400d1003005002d0340008a0380d005504681182c541f40c82c0d441d0298461201c09003807042c00c000e9180d408030140001b601c01d85c00307001081c21400021002a040c411410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9099063 1250 9097813 9097817
    0x20604170a050a1202070b090607120e03090d050a05011811010f0c060b15030412030501060c0f1205120405100c0215040b070207080303010e060f0d0206030a0b0a1206020304060507 79
    0x8070084020030b42c040150b03007038020746281400d000000941618000e02c24508090b000c0701d140010087e45001c00940b20740151850781d07450120340c40860b64202100d04413000b84900b6041000004c41c145819426568098010401d03109500b40344d50780e1a08580c5480d10070010342c80444000824851180c4011043c0e0346c0a0030300a00140724404005e01d000c5400000500703160341c0e1810340186868040602040d405448541e903500d05107800e0034082072280305040000a4205400481c0540c411807480c49002c0e800701200e11242856501c0543d140340900322401013100501c030703e2046110044d8642c0c09180168040d02c015511103444400f95044d900c925019940030000500c14018800c80a652290304280b42040c2da0702c455108030b0400600358410070103031101100100b84100c1ea0b0320024055681160764046050f40c0340144094005041d0000c0e40c032685c184001601840c1c3c1e60800460980000c282c5825142c4650107564503c207400000d45000350f0201c2003204100041c4035036074000101c3c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9100313 1250 9099063 9099067
    0x90b0702030c041e09110f040603020a060305090c0a0b070203070b030105010903080904060503010c0206070305010e040b0118090203120a12020405090402060d02070209040b04030f0903030e01050a0207090c02060417 94
    0x6401080c2e0b02d051242c0900d010f540d43d01c0c0c4a60a0b8200c4550302143c12042c000c003809480840c3c1020010400c0c820513940c4983c58882441c880c5260074840c0f20200c0340d01030056010a85000d400780d00030300e4010700322500303030103010114a12562000180c5025200e03800469845031041e005042c03901034140c0001482000820052040f82c0c2c0206010b0106c9a01440d019039030040507020502402d0705520003a0150b00f46610080b480e500410b0b114800c14241e54200f05a23a6912030008a1041c2501c014081c0b4107179100501c00752222403401c0e40700250500005c14101d00c6540400d103001c10130040d5a030040c2020550340340890340072403d024844024030003541042e090400047e201000030300000e105e2100003a54180c8121503405842c0c1640c1c000301314600b1031034982842c000c103007004c907411400201c80c3d84078491454014a655020390350180e8543c042d0400c04001518958801443d040c254402e083c000102080e41d4051106d402c00c47c1c0e0f0290003c0d040901d000d950078150540014038440c41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 9101563 1250 9100313 9100327
    0x9070903052a190801050406140a021801050c0c030706030c0906050403050c010c020118080a060b040507090905070905030f0d180303050304020105070218040506040b070302070506060f060f1207090b 87
    0x641100911880c00440702c0c508240d002148083c440005540403412a500740300802050240b43d610080c490810300312075160607501c1300410022880f5000b46c000c000c1004110a140a52160001d400c2020708101100d4003440e00d07000180c43c040744c642c07240b030000b51608516013034998800e40c52401899541003540c1850305581c0e405480b0039442c09610704000407030b0392030b00940e031007242546140948008030802c110b171500801601d580b941441583c1c0203052a646101a05152182c54890001071391244000c5003071a42c0d8030b01500c0094018030804c4082440850300d60b4040c00a040e42c404410002e040402c95500090550001c4050001c400401e1480403c007080d001400c40754800c1e82480e0040d51000c161000801030f80184480785000040b0f082000108040020b43c24000e034080e4600d1080c1d035841d00d200b2021391103000001812500401c01184081c00c015201010020000341400e061440c401e5a40715181c00c4541d8000085508009018100360084020f40250541030a06850108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 9102813 1250 9101563 9101623
    0x5040201021b060f07050304050a0f060206071b06050705090325050909030a050a0507080f12060a0503030414040b0402031303180b1602030106030204020307030207020406080303010609060807030204050907090305 93
    0x2000501e80d04044d000402108110043c0103c60142c040280040701468503075002c3c45600d0200d000d280007501c541c4011400c4540903460280603c010780c0c26441000540d40d03a030001400d40900420140b140510030b500180d42e06120200c00122051038440c444d419110481400000c6540114003d01051040c4483c2c1031340401114101509414036542c0d8050300c00c02103846102d18000501009000700d0707184082d800a10003800450b52040c020501510748a0401035202d041c0d108284d410b0380101b03c1003001c10031000c640400d440c0c0040c000101501024045001c1e0b0f03104480180c0786419a0b00d060040582001d41d4a1410b60307140c0d400a9254144040d508462050b000143c0e01895070701c1c102021581d09420240107141d01400c03e5489050600d07024000e900094001c0b4816820250046606200001944d040300e005646290030f03980340c0101a107010b440a4504070800d50204408640340c4c0b6802000fa0107040c1d9551044006031943c10180d040c20b100e0040c2000b904140400088500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 9104063 1250 9102813 9102817
    0x507050114070c08071a040b01030b06040e030406030b0105040b0301080319020a020604142202031009090206030a020901090e010308090103050702030703200f06010b03060307050102070e010b03130206070605040201021b06 97
    0x42d0302208185c0d44681d107003800b00c003910002d55070b0f0b000d501d0b507242007008200f5403030300080c101c03032082540c010b040e1651010401681d4042089410030340c401d00003000114441c0d00018074101042c1002407074540c80b40b160080b141d009801883c2c03594400561001190803c45e4201840303000c81c4040c00741400f0310f50005510b80f1952251100d80340c201e6a00c07102c2e640d54000d07108240700281405422300d00c41120b080b4040d410890703001d180c08418502c0000c0c182e15a020785820740758000c010901d165a00310042d0000e41200c1a01c9041014a00010a20565903004980a94040e4044e140c0b1134070b407607000500307541c0001c02140454000b403044200180c0c011480c0101c1c00d2184440c8400c45021036130300c2d480c0c50300310782c0c2c5070f070642c1705100001a40d203030020003c6015502c01d50690300015154001a40d4500e010b10804022200b04401084aa000724001d150001150344080e108841d107500001d6068010b01c030140c80b46c0380c0c1e54091004668040bc030030290007105400000c0c841c40100c0c000356880c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 9105313 1250 9104063 9104087
    0xc0715080c120a020f0c07030b011401020703120c0f0b06031218010804140d030504050712120e0103020d020a0807030506040b0117040807050106080607030c0314010611070302030d050705011407 85
    0x254042c400403a2100040750140c074400c0008102040e1100241d42e1800d07581c40300e52206640c5529030308008101503070018100d10200c6410380091501d540b0319516101d031801406044800c12000d08070b07481c00a070a500180a00501901000e07025042500405080800481d00c40d4407140301003140f2354070503144400164843c802420010415034881c10300b14003201c0300e854003120902440013800c620a8060740f095000e01c0c0220201d0b102c0b1130321110100000500b811000d4020842100d84440c01c5d44207102d0612514010b16000d410030451407011426038210038030601c040b401c1c0704100002030f80d041c454075a0012003105c0502c000da4600d030004c0c3c800401d024418003502504400142841206011a14440e40c040004c001d4140e0b41c464490326010160791800c0020f04020580610a200b80074440d115002040d0b014403503468114103640c2c500b4184000a442e0140d55070000141c1c0c2c041c0701449242c000da07207610350350380800e2800d40d0841e098105d90801500045041c001f103030394003038501958 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 9106563 1250 9105313 9105337
    0x5030403090e040f0b01091a060901080f070c0c03150507030603020f040f02070209010801090210020f0c060a0309060e010501080f0102040f030b04020a03060f0f0e0f10050a0b03030c0715080c 84
    0x181c3e44890800350034002c01810044c140c007080c1000002c0e054100d0b80120600301d41e44005010110a07e020401c42e072141c0800c2c0750001c2c1d0360308041000c00a481404030740041c0d013418060401d541c540c0d51920a4002a40140d80318802c4c590301440d44550b40c02450b43c0180c43d4a0704201450440d07001424901d080985a030059a46400c0801d612515a04a45119400610030000c80d80d6030200b160107014800000c80c042c0d041c02c40d10f510b01030b00000c1c22501e5245d41001a016044405007401001d40040c1200000c05890781440b00116146118a4140b0411007001058641c18034021038600000b00201d1071003603104001c2009090410000c00c030640c2e5005485101d2a242c034000918503590f10b4101800291600e007c1104140581c2d12980c51074100c03c4081c020f000b01e140d8900e03183c284c58401e80b0103c0c0c0042080c4001e0248a5200e01d07407004907040c00056810341000401d1454102194008a40d484410103014607007511441484215040c6852686498a1850004d0380e00502c0e29030a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 9107813 1250 9106563 9106589
    0x913030f050c0f0105010302010e090408040501080402041e0b030715090905060406170102070c05180609060102030412080903010f0c0f180302040c08101401020307030804020a0503030c1006060503040309 89
    0x40d0152160088402c4140080308842081404802940c0248000c0c88202e0204090149031902070601a1a00d4400c5070030a00480c18945807100640d95008001c1c4102c2e40903644005400300400349030759003400056882c60024092015406062400016400042d01c021002903d200c07c00d0380101140c098170540c1c02c01180d19194038011a018200c243c100c040b0381d0301d03110040c0000c0041540030745941801802140407082ea5042407081070071403070040401c074134018400074006082000b241604a10b0610440e490170781c2c0c0785900d84016040c404200c8034100c001902800a1409000d510183c07a01042c0821001200d00406002d24060f400c0310014450010401d1241102e00704088008540290040c4010400b4805c01007070901c044807031041d065420a80820380c1c021621603c030540300107030000c619004d19500d081d649044014002c0b64088411140410355480510252041040c420b0081544000350902c550954041b0b821150030400c00340104030120382d2040d090404c50b40000e4402c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 9109063 1250 9107813 9107837
    0x6020c0a1e050402041502100c080408091f030b0102060a0209090601180b0a09030201120501050102030904020702030102042c130c030b070e030d050c150c031f1d1005091303 76
    0x1c10501000da0103180e02a10101c0c000861240c44a030544121520380e003030b281c80c50110140c002c111140d12120500040000001500240411004151003240208000904a001c1c21022500d0103480143c4001a031240f20001071960100455600701d00e04a0f819802d01c6096008160175000041c1454104031026a0f80403440d8a984400c8014281c140c1002c0e84d078a040c5080a82000e426201c12400910f0010503582d4030b500600c18281030340c1c0c0580c05586446140d4003080040c0d04004400d0b0b9065608200018036405241d203869503030b046141708400e013070248140f14030301c42100800340c1c03029602c0403c003100020700010340c8005696010100c1501625800030444002c4000c1c4541a003610030b06282001c03564000000e401c40216010880341c1412442d1207040c0710f181c040c1c503410405c0c0414000b18a5414030300e0810381c0c0103130140035464115683e030040f9200401e030400e007100c4440c40b50b01c1170041c0044444942409441c054079910810308045c81641180020640c000d4200f1070981022 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 9110313 1250 9109063 9109109
    0x617071b050304060f080903070b0a0b180a0614030706050f16140f010e010c0e0607030512010b04030b060103090305091207050a061d0405190b040612080309010606020c0a 75
    0x1820045801c5000c5035129a04c0b410043c00e400701c0c9005120105160070300150101c10000300b183c42656220441c100346449204a542c0a45031403004640d0000986882c2420641c072030280038865074022002007181032410500901200403803032154041c1d00603007818090207401200311089030207208180d0b55282d0403802c0549006101d21001003d14900b0306030307916040c0740040d0b2480304030302440c001c006402d5071011941c200c520312038210000c104849005141440c090380a4031200307009080503442d1902480005030162803d1700101c1070504042403c0c404d1100000700300360700407002c0c2010003440e40191800342050042e00c0260f44600d00500032002c10000c01e1018100400020300701c1000d0684031a005400e0414054105880f515522120358451800b409040e024511030070551101c130007e4107620000c0c0c070780d420702030ba0450b4032904001028035000320050b003868000c054043c1c9908040011500352a42a4000c00466102947c0035041e681e85d8800841150410740303010085070411114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 9111563 1250 9110313 9110357
    0x90a12030309020d0302010203040311010204360501180c020307020f0d05011d010902120a08030601050309070819120305010311040f090203030703030212010605040608010306051306060306020a09061707 89
    0x25005504130b0007250070550150042c0d40242d2094590310001c0c1011300341c0d14200e00640c4a001d01d0400c5215415003030880180d43c8021581881c45500e081d5a101d0001d00281c90081e400031403000141001d1800c0d009152143e46604810f0344065403801080c3d0700040d04050580071410f10543e000c2296004000c400d50080b40785940c15a0008524030300f00c0d04103402448510002e038019602a0400682c2c0407003c19503044503540801050b0660711a00c0044890350402000c100c060700c14001d020070711250401034201e0260342e500907401d80c0700c4189424031000007001ea417002454101030041c000124501d1100b0142001a500041c200240300c5501c0b01401d9640c10203901030100040c02018190305130000d0000c0990704a15a0039030740c1e6500e080300d05100b01c1c032a5400094421005000050711034200d0303a041a1036200400e184401c03511000c0883d100c2d51310031101940d0001d1003001154000e00c1c000010042403d08414181c802c205003900303504000e103030704100140909e0f44881d94031207101c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 9112813 1250 9111563 9111581
    0x160f0f1401020a0f03030501051302040f0b0304020d0b100906090209030a120c02060d0605030106050d0b0708040f120804060f150329010f09060b030601020d0309170f0405090903090a120303 83
    0xa401e130a01c0c0e4a400c0107801484280940c40c041c1c44054080c102001c0b950080310210b41491031a41040b500d800c1c82201d10b030304081c2080780d1000a48051101081000e00658003480b2680740d10b41c1ca0624003500f8404407400b60344058503131801489145500e40d000725103015401d800c0311001480c5a80404110358861540c60004d40c0002c01180c0710074a103095500500585005800030014a81c1710010031a1542258000030100c16a03d00041d0005200e80c642a03042845066141d10250b00c0c1d5545180400c0c6126a400000328120100400e100326406512940446000c0401c88454218507000c48440f030b0f408064001150a4010b48986001520b0010003c1014805d6046561107482d81c0703c1c1e0350303224865103a001c0e003080008142d026102c404c690180a05800400802d00c51000036000b80c071890070309880001c0061003602c8020701d9040140150124400030513900c1c0d0600381040316616029149110503071080c80100b14a40f9220007403016511a9800302560000a21341100a403800750 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 9114063 1250 9112813 9112823
    0x10e07060306090606020a0209070c02040603020405040302060f0604060b092803080408010f020319230907081e1e07030813090507110309010e0411030702160f0f1401020a 75
    0xaa0000300540d1540c0140c0075102040c80038000c0c0355540c02c1c102e0351000009030195000392010041941c850041c1d2417040194805400070905554a0300010100c0300111402d501581000c030410807807405490a250303100700111401c11406003041403001d05401030b003503d240a50950025140c103a0159030001c008540c00e641d407420301603241e0ce0f01c05101c0e080b40c07080c0e80c110340c24903850351031000090090b24400e002c07107000c207a4074580e260300c6200a0903559036007074003c0c1c60301c8251490003440303050b0307481c4681100c20040c40300e9440c1510540c40c6c4900c00403c060451521030407801040d030081440410428068428102000340f03410b000d0030207109500c0141580d800007841e01d6440c07103c032800404c64034640c07400c014542d52100240d4100d984120880c0d0300e500100308492080d0b005e5603607102c40382d2010b000042c8410340d003500944c555000340c8001000d6444418143c019044250142c00607021120f1050041484d091070128000000d000d1402c0700700d2000303006203d130b901c00c001e4484a140c200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 9115313 1250 9114063 9114073
    0x30f10060e1e040e0309010206010902040b0306040209040b0406090b0a080a0b0a020705070e0412080c0c0a1b050d050f010506060705030d050c070602030a060e13030c08030703090506040309090c110d080603010e 92
    0x8544c4030b40e650310404509001d4051440002880c48a900c25070b81110824940d46182d5610101000700070341c401c041140d0f21999860002c805c50b250791081c58050074403d040064050803410800481c213115030b0110314250b0200f12000002890540129003200021070f01584603107451511a0a005240d0410852851041c08000500052104c000c0801006840d1442551036500c0d08040d80e20a441c0001407503800b40320703603d00051400301244a441055804035003030541721000102080442c007010786250703100100d0381d82440000e10541c3e80010003203070b00d0381c60064541d444648902542072041030b11640ca100055082011004403248640c0c0240115030740c1c9420418640105802e0103512203030b42300003001a89501a0240300c407042034250721101d55003015035031034041d9580024105810180c6400300000011010012903000b0f0b403007600c0d040003043c02c2203d143c2c1155502002481040700c0100600a482d00100365031344035800a28080b0070503501c0c0f001190240206105100003072040f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 9116563 1250 9115313 9115331
    0x161106040b0f0d140f1303050408010c0914060304020a030f030203120711010605030c0a031103190c060e09241206010f080c030d022a06040902030f10060e1e04 70
    0x1403402407030301290f5680100310504820020419050b0121801901c040d0500045051b81c01e035011541081d9210303240840c40d0540b500000c81c00e5459901c400408100c0b800c2003440001c800b41d010408400302070b140300b400c42c035140d00004e0b45c0b00c07000e12019081c500203402481c28148288101c2c1c00d5800503205818180c200ba01c0300802183c94480003840700c3d4640b92020901e0f24001c04c16040d1002c0040403601d100d030a41e107842c9003a02c5403c0109038148500501680f584ca02c0240040701c40740940303460a0030514010b00500700b07249030101648144100420445400c410b92034126000b0301030900d03c544000c068001c10406041070701640194481d22000050f481c036940c1007035041d60528400d8840340b1685c60f003490b03981e2414a4052000d40c02010b00803646465003c208a50204034080040040c50800b0100b86c40d0f611940086104980020801003503802450090b030300907601c1c010365098035103000340091201403a00b00d4184692680e48920502500244d035031403542c0f030001c00030401c1400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 9117813 1250 9116563 9116587
    0x30708010e060d03020303070509030703021206010f0602010b01050406110a1401051801020310050d031206090218010e1005030a0204090e03030601030b0303120403080406060314060601090b161106040b 88
    0x10901c10011054a4040011a9820300030400e040203580b5400075400c5845a02d026100c54000f40102a011302c90132900001595403148182814201403000d03090742d505107420414501c1090b00000f00b56070400d00580110790307005003150103c8440740741001c10080c002c40701c541843c2c84140040c00c20311510500d40031014065100c18064060b503203810200800c403030803240c240d0104840c07000c000b4910010030045c600f0a84c00e40004d1500c0703480e101404015041c888011240e03650400c401031640070803210000c044681b0205407090090800850904c5440000b0300320310001c41781c4800b045404400b081c80da10058040d05c001d068504000d004007161191404c0c0ea9400c00c9512070700017030400010550f40d050120841e000140032618a0f0038651301c584040d07504100140007150307015502e0b800000840d9800b100700031444244d001510f0b0905000f40014820030240e000350098070404c1003d00f40512044080b05030f01640080c100c06900d0141c0006592401503070300040d112a000200001881c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 9119063 1250 9117813 9117827
    0x30908060411040e0d0918020c030a0306031106070b0403030f0b041e050601090807030618061b080705130e040501090f0f1401090807020105030a0e070b0417011404030c0302030706020307 82
    0x454290340070410845441440d540c0c8405c007102210210b2501d440c10301c40140c000c01030101a8002072005450410b85d507401500e140e1040080b5800655601024020488074807030202c1c425004445081c10048140c44030300a4160141000b03040c96651142e10103034881c19080500b20038001803080007100c1c0c0074002c1040c1c442108040031651442c000020b0020341c00380030b0147c01d4841210003824101d00f035588000c010f02030705c0e4950071300048004021000440074000e0121500d01042c0100365101111f0000d000c0d40d0010b0300c0b080a01a080c40b0118401010790000c101f11540d86503414180e4440703081c40d0380140340c101c0c00070b012100c01c82c1c00102840303509508002581d104a85490031603100a1040d422101c080ca4020200041008224090b6201c1ca01554016942210000300c0070110890345103010600d9001c9501d001002c1403c20000030300c0300208981a240c1c5e8000d0041d80704560141c04043d0005000409100e01d603081c08051510030401d50b114a0361101e000c6650f030401c044090844 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 9120313 1250 9119063 9119093
    0xf0409050903030103050a0807030215010b040801050601021c030b01050d05040c05011101060f03020409020609090108071703030603070303050a1106010e06041a010801050609040917070506010f08030d0203040309080604 96
    0xa504150204070340c00400022203049a40200240000c4405683c509596074070030001070701148100d103009008001c800c2d80050007080154142c607580c80c45c01203001d0940da002005541550010440c241150754807000b40181e181080c0350000d000464a001680c0c43d0081a20b04403800f490a01084200000c0c100740300180c0e00e09172540071080044240316800d98915004058015203c01d00c1040181810f41002c18206e100810369420094014046440c0d84001d0b8840c03215a07100550030001e8902007203002d005140035501841c82c41c42c1a0b40130076070b50002d42c40000e0800000040d8030302c07091721a0803414001c0040c0c0b0241e031299603540c0c00c1c91304582420790700c0f00d00c0b492501c889540c03a06000d90f80058094810303140c906081e0320b880c0410140e13070000142c907a003207503c0345820400201c0144a140207103032007011068944200e420424a405030580100051090000062240400010075140b04108a54000d0ba03030740d545160454522046500c251410b10842c002c0c0f20401801c98030070003039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 9121563 1250 9120313 9120329
    0x70b030a14010f030f1b030f0309090b040212060f040e0304030506091c08070c05070503030409020d1a01081504090204110702130507050901030908040e040f060507020307170309120f04 81
    0x42c1d07220720341c107070742000507201c000d01c110b85500541000500040c64450070400000056041d141c4d651501401070f180c242c8110700081807a4014000e00f5550310910b00799100a841c03c60030b03c0000b12140c00240c801a2150381b0880c015000542c1659542e00300380300300c030100030543e5200d56591401a82c0d8404c20b03507000c042c5024a4425842049414090480040d072565605241d81c41c2d1702000d0f00c04003c3d4000c00c0d1042d00400714081281c0d02c04100400040818034801a035402203e550341044070f0303d5003080d18400c0d50400e21200c880c5c1e0312080d482e410181500100110712580e400050040041801c029040741c00e01c0702c54080c0c80c003480d000e00400c1e03000b6244a0b40610007a400101140c500316181c0000c10028050017a581d4403e0744410361540c0700d00f40b40303840c054031018010b02522003202c4c00c9a4034100c0c0c541035010044140a500d41004a9000860400c11541e9803102404607400c1c55401c820300210002d21740c1e0204000684004200300d010036070f1001010341c5211982c0c0107004001c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 9122813 1250 9121563 9121601
    0x3030c0227090609160504091a01060e0f030c09041205070501090c060e0301141603020408030d0c170108031b03130602010b030f061506130902040f0609080109030c08030702070b030a 80
    0x40c00742c1d002c00c80171402c20344103900d40301300e50800d01008010400d005c1c050301c15205107180a0300c0140707a2031a00d80a0030301601d0704003420307000001304600b03495940c04441c02500030801440380f80c2c860360070060700700380d01c0700304040081ca2840041307400e03010310381003e00707503608108a10040c0030440c0500c80c1510401d0380c40444050030001410b09a5075011a03d2502c912401e000070304083c02c0614038580300d0f640d0310740540ba0076500c001280c99504100310315400389680c0c0500c00d4001d0380000d42082ea0111750341400701158900740041c1e8032809220480348070f5000c002006101281d0610486184074140c0801224154541341d0080c000c28513414254064400c03e00c600c20300c48800a040c511414208803d94000d52045043c0b20090700f24000980402102c0c13280400c0440a60000e84041c2804130703044050107113007410042418246501c0220300e0b0340f41503804404207500620040741030341c02403a01c0c0e542e03071a003802c01c030310701107542d480317004421404000d000d000c607450b0308030504094004000007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 9124063 1250 9122813 9122821
    0x1090812010506070b07030b0609030a0b07080f04050c01050901030b09070c0309080a021e010c0b0405060603010c08090c15040b070f060614030d030903020c0a08060a0507020c0a03030c02270906 85
    0x8411442007010117404020890005540749100fa0070400c01c02101400d040c0c00d002503040440d00e04403241c40704031455054541004880d99101000f258004282490300b501402e042d25296150100a001c19040060000303512480364025003110105040240824645103000c10000301240342e041801c40000c0c100501c0055000c20025880900d150024242d19030a07101d4100c40441082c0b8103003290501004190b24408a500840514400d502403005800c86161140c105400c5481c004907400c14482104140b250f5882c0019030481c503640c090b501c07008030350341c03620741e200c83c601840c0e02005400741c0c001400c204100c4030340228582c1c1403050005102181d12102940e005588658506400d503001c030001c2c0c0d130307098400e410404840e8000c0c0107841648003084040388001195030010f280c81c0c1c7c008000d200c4d41108500c18507900c2000d620160100e800800700240e886c0c039443c4006020070814004000956035854291016181c000791079000d0b545100000d40350021046510343d4103400760b20300107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 9125313 1250 9124063 9124069
    0x90102040807090b1201020a05030702060906070801060c020301060806070e15121906030819120b092e030f021309031407030c060f0209040605010e03070b0307050c010908120105 78
    0x244050759441005000c68608141544000f440348140855100b0300c1014000103034902032006042e0048180d4607240e503494001e001901e0200081c041c2d332400d910a50800550590012410341503420310b00d40f50b43d48050500001e4054400c0383c2007103049020b4001405903454001c8005aa0701009640c2c3d410082c801038517050490181c0240114100b441d0710000d07132555040740c01041c030b000c50003100154490710307601c1e60b0100c0e802ca20170112001c881c04040e180c14541004d40a00c041d182224103002c4500c035440030a20300503014080c201d80c8005107202c2035420b0105483c001c1201401c03009220039039946d04000f416503a5640090303018007080c108561000c01c86009400d102038040e290060717081c6541d048d10000d6031100c00c081c0c3c20400c00c108104001030b100c1c0103100300c07202c01c090090b03254031482c0c04000891ba22031b8040d505018440381480d8150b200403c00c0710440fa54038003800e8492f80d034140261008c0c440c3e0758821a0b80d503e411071007030420450201030911101d411001d9a11030b0780b9170080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 9126563 1250 9125313 9125317
    0x150106020f0d080f0708060105071a07030605060304021305071b050a020108070206090d0c031110060503070503010c0e04020a021609020a02010c090815060a09060e04060f0504020105070b060d020d030e0405090102 93
    0x41011085130308400508054040d000298014106150151411010340c440510362500005502d004c40542000d00055540c035004100240c081114054950300306a4001610100c908941184c10f43d152000128068050840001010519141e10140a0703003490400c0d140d549140342240440d0056000c034002d03a00c0001c8407407181040740000c0480d003400038415248400008021400c0043e02800815414800e002d1854082e00003040132900c1402c0604150920040d1340000d4000c0c1e14128051580951090b0143c1d8407400507200140c2d54602c0b42c408074144076120140005503450003200103258040f65004255191081c3d0082084440e0f8010403103070045030b172181d940264441740250a400030103000d01504100c0007000c0b001c8180d42c4901d9403081d240c05500c00070780b03d00a031080105004a07400780c10a00000e18904020600e01030f40068a47e0080c03c10140080d041a00012030030345641d551f00c56800d400030484c0754107030320305c0c0b50003030902d00e5620100e40500d0410300807a01412050003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 9127813 1250 9126563 9126571
    0x5010504051c020d050c120406020606010e01020102030c070209040804030206041230050a030608060c1206030a020109210203010f091a040c060e03030f04080307020a06050f0301030f05150106020f0d08 88
    0x8042c001501500034211820b4000c031507020500c0c011f0b0402c2554002841c801000280596000f500c01d07407420200140c0400c0c482c0c0c0500d415640100100040084a40216101c1950499550300d054403142000a07850165400c003d4104100141c085151102018a852550f100b400c070004050607200c4407094100100d2440880384011074200c690440c02440a416155117510700094001d41e2010ba0382e151141c152131100403000b0001e002000c0341000060680e0080b800c0e401003d1941c01070b800205801010312542c2444030041c0c48002440016003c100c256540080090001e2500194240000d2003586007c4a074503802010541e441e228210901d48240d0f00000041010f070715003501901c03503a04207880c0c075505000412444a6210401018101030140407000f140c55560900c1031102c03948a03500400c0071302c4400d1040c0c800d0308070000c0c12241580d45c0161164121304040c6031040c6007201c2c0098210760810010b0010620a50008030010b41104400481c1e03100c16a20030140da089105139 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 9129063 1250 9127813 9127817
    0x126030306040504050c0406060e0102071706040303020a0207150302090906040b030c060a0908031209011404050c04020f1b0606010f0e010905100c0b010311010f030209030307170903030705010504051c 88
    0x48006000da01e407030741c0703d95803003402001990548a084d00001d0100c03071381900044040380c0318180009541d64101710300c0014101d214501c01300e01c00d030480d10390761710355004200408054001910001a070310910094008010310342c20780150070690320000d8069017020450760300a460300c2001a2244c0b410b806042ca424802034094508000903505010a030351004a0450521030301c1e600001303840b1070800040c0890320421a20181e80e0808034803aa0075200070143c0180c00341940b90510010a0001c1441c03540107000300d60040e0b56000d031180510081c019207003851000560004c0e0a450301c0030115146210780400d0381c404444039101c0409580d00680c00c0c40560001e40703c5481030013242450801451450350764100000c23044071039505c0001c030b00300c00d80007258030300346141710049a544c2104a0307482000e0b05050a40c1000e09070000710b6078034000c223100a4040a43c120b80d080e1032400c400102c60a11201400356595800d10b400c00e58043d003404d450072200f030310503109440f000504803901154504665 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 9130313 1250 9129063 9129067
    0x714210306090a090c0b0a03051806040503030f070210060605090a0602010612080c0102121303030b1c12030b03030d06030516050d080a120c170f0103080a1b05060708012603 76
    0x143d0007004241c2076030211441d40704c000000c02d0b50400d54000d040111820381d40498146814144018511506c1c1c1035504164408003d1000140022003640c0d804500c61042e645140c2d1440422442c1150541e449600c681c50980089074140e4450000c15200c9e070152420303248180c0e580c800f2400c03241c1520a58841c210201100e20000305450010000b00910034000b504140d1000c42e64401b40d041a00c65103180000340d84585c0130160540a6040f100c0c408440d99101507045000c030101a003003a1500900272000d0010860446002c2e900c80d400040b0060f00f00e03619824404624801007030280015a810b2103400103c40040807461141c4040c0e44004c2c0c221900003141d50340d81c3e4010342000f59110300740a1080c5020318a0005071080c42007140d003e645039100600b06021500c0b032468080e0020000900b1440140041544402144c1e070b81001854022410b10301e083c7c40074848000d0910040c000d00031070301800001a44150010305035100c2c3e80c08198205009080701403461275114440d000c3d9041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 9131563 1250 9130313 9130321
    0x50f060303041211040c030e070f0501020c060706090507080d0306050a1d04032604060501090c0c0201110705040204090606080105030d0c02130b040203090703140307050c120102071421030609 84
    0x42c0700b0040b6040303846541c245035001c441340c0018080d140c01e10342c0500001e9a640c2281d03940030007001208003c100f581900d280c11818840004c0d02c0d5440e0030b018500945000400d84208103440c2d02c00f05035a80c2040642c1c13806900c0d20007045e01c500d0707011415000a0f042500120f19403420040032421180d40000100c100d0310420b45a8a0f1004000e00540a00c98810340c51013640039030030361006034202c0201c500507503490a0714002c81100c2041e0850901c0c00c1c980000c0380c042d660000c20000203203409081c4201036240950f02c00d86025000d80050343c00a0010a0014600c25543c11190039038009403160703000c0d6031701c5e0401c0c540d0310000b00c1c980000150190800d64058246034403041c080c501640e90110301d40ca10600801c05a904c00e0309ca14403a1f13030110400304180030100d180e40c02168000700207907180070010f442c0d4a81c0e541c0e0300995a4481c1d5400c0d8180401c110095040341c408a03401554207154400004a4940390748400700440001507408003c0d00d1190428002c5a204850050101031541c072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 9132813 1250 9131563 9131579
    0xe010f020703020d030e09040501060e0c0304020f04111908040204110f030c030c0706020703021606031503110607060501030c140103050f07050a090503030d1509050402030303040201050a1e0c020301050f06030304 93
    0x2c540b041c05d41c10300102034803410b8075031034490b00241b01b5030292002188142c9011503034000d0356002010181199414410b1000581d40d071308443d5041c50301220041440710414880044501c1580c440040600c505440c401c80a0b8000003000d215071f000b200c0c04c0103140e402c0c4014102ca0721443c480300884c45001c0000446c0031619101440e00090040c038540e0912040303903214402c03644582c0c803c1d005680510040d20807403030440e02c01310181c20a80350038088210940341d480c00303e901c1d500000b044805070807aa001251524801d990020fa04010240039950752400e00d403110040901841c004c88905404018665010740181030081c0c1d64810140d1042c0d4491200300c501ea0840a03a0000304a00c071840003940d0740d000c0000d09100d66181c080041c400c403140329146080d2403503510408547d404c0208200142e41c01005507a4010340a0a007907a841241d4102240c44144000304106060046d4040500c86680000401c6502d031003503008015544403c3d180c000e00c0070084441552550040005008000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 9134063 1250 9132813 9132829
    0x20105070f020306010603020d0516051603050708030f0103030908030a080601110f07090204140f03031e0408010509010501060e0102060609070f02010e0609010e0c0d15050c04030203150402010e010f02070302 91
    0x2074018001c41e80c41200d00e03400203041c11803e90041c1d000a4020941c03070f2407018184a0181c21a08440b580740a840b00c40b8000303400741c0501200740050740941c030803520615000c0c00896441d981e00c1345040d40e81e8a0160075092000701c080c0819000190740c040040742203507000007101c100c407107207448070300301a9a808011904c6e000700d007031500040d0181180301c070507211080142034082c02c1070910140e11242400c5146980001c1904c10714800d03003034450003c07081e0b180071003114145880304006448140003160504400c0c45280d0061100750720300002c2041d0300c027041d0300441c16209203030f90b078050303890200004903a9090143c1c2c40c254045d201c24007003000d241c000d242c1c03120548402c0c0000309000346603810040c1010f00c22107a441d29651280b400380c0d41c6042c1402500714000c403c0320030040d810000d49540800030603e00014056564600100d03170b000500d1f074141c0b0021640102280d6406203425001e11104005a408a012891310040360340c50390b000e0030540c00c3c02c1486034020301c1014590703002c00c6842 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 9135313 1250 9134063 9134077
    0x40b07030b03010203090a050606190b03060105070212060702070f050616110d03080603120703050a0305100f03081c0b010e040b040f110a080109020a050d0f0615170f090a020105 78
    0x3040d500e0040d00350315102030024611500d0440c000d80141e010a00f0400d0408d44018103051160f01103020039140d4003107108410040e10740e16450f8980f40c4c2d0b520401a100303449501070295110031221101569001c002403040c1c40b50b20546d00792550242c0d2420400000d007418007410f039000c1010311001d492510140d031009212805403070340035440c00d50350001c01c170014001e020640024807014100142828100721003600d4181e000c1c611403410866031001042401190110020142c858002c85d40d00145000300300c01400c0c3d2030083c1052580e0360b28020485501103290131200c8540c0c58a0500e6020491007191511070041c2c4030b070741ca201030910821005040000c4003591103035451008560100e03191085e0164240100300c602d40d01d0700040c0c0090301c80c0c0c00c141d000c004030500401012034410741c0b100030b40d091403e05440200d00800b03002168800340849070020043c1001c02c2d01003100c0194403d1071917070b43d1031208481600c603031100d03007540700e01e0003045542544a0744000c0381c4800651150b0020822 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 9136563 1250 9135313 9135317
    0x30c0b0402010216080706090503060c19090f0605090102060a0605010206010902090612010f08060c091008060d05010509010b0109050906151b010c03090b010e04020a030b07031e0608010606020303010e040b07 91
    0x2894059105001020b10750b017043d29280e000450600156401444080103000110001c201a1138050403130300492040c0c0d110500310141c803180c141c25080c000c0c030080d330107821640c461420700c5854400c0201a07400c1046214011300ca81e5000c1109110725114078410303280c046e4098185070f800c040081c0043e510505c4003030b801c04010003401c40d54030400ca0300d030303400703001f507020341904043c03808034081c0c5003000c06060103407404001c22a007109a602c4c0050701074030503100d0426030076654138080024440d40000c1405800d9500b89010005c03000d0045d408002d03007480980320340d41d92540711800c0c00f504c10780c1250740c9a005001814201c100c99102809841c00c458085a49a4841a01c8150f070742507581503501400030a4582c0e0940c010029040142800340c030924400041c40e14040d00018160b071114400503209004000103d20114401c0c0c00084242d1403224281032504100c1210b040240001e21500c16103500c1d00717002144a510100881e412111140604502d94449864590241c0d00c05809001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 9137813 1250 9136563 9136573
    0x30a1202030915040905010b030108070501080a0e0a03020c030609010e0709020921071a070305090d06020903070e0a050106050c030d0e0c040507080a0b01020606030a0602070611030c04030501060b07030c0b04020102 94
    0x141d648400f2560000d55a00d18150344462600382038034252007040c0c01042200c0d90500051084a00014003030702150800d00c0c162a0640f01c030100300008000c010009085401002006405d041d00010b4200001c68180c0c22201d060f83c44c50f02c05400c8407009514102d00b034104580c108580c540d1038020b07146400004060300f44d0244055220076a420945100345c2e210b400c074040400c0486040c4140005415609071041d1030a9542e1354010424450046c02c02e1050000741d8174001807280d43d5040e26400302001e400c8404141d01c91560300e81111003142c429802c5801c240000c6640382c4a441600c0c002d90f0404021420211380320b42502c007401d001d54014450344906080c0450b1641c46008190050010f5110b951450501502c88400e403452412017a0543d4080c030701340002c0d43c0b0001220101c42d50072a00040c2c40f66031a15022020b800d4240c070409a5183c00b009001130018260010800c882c891030007041115640c6072000c07034900601d600903001c40c03202c5604402090310040284d900c144140b0540f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 9139063 1250 9137813 9137827
    0xa0e0714030c0909060f0c0a0801061b050102041217040509010b1e0f0901110604030203030a0e0a020303030421020106030f0204050a02090a0807050f010201060e04060b0102070b0d0f050f06030a120203 88
    0x4003802c604031240d90081c0e00404c288a0b607005400d850300d4000341f0026600749090382d00e82019100340c0d0184107440c20000918001c0b90a650342941421005500c903000355030325995901200c814020044050312103554000e18890b032425440115401c41d1006000410319a10303242140802d6041105601c001da560005108a100c00000040001d1030250012179141e5480c02d00041040e0a4482040c10b598019000e00012940000a484d07010510b43c001061003141800c2181c02c1256040000f90148008020f200400090301004851010a541041780710500800220300361090380c403028080142031030320000941403540091354000714000300945003412600104400020710790041c803141c0c002c01401d10807032130400002440340c5006d00c000d01000d81000c030008001800908018401940ca0344050b4159000740032a50003083c4685540d61903082c601401300180c40090441000146014001607403607071140c80c058002e0501400804810b0201d03a55010748c54804118a0107610050ac044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 9140313 1250 9139063 9139069
    0x3030d0903030501060e06130b090307050a03060b0f09040803040f0816050604060f020901020601090e01060b0d0501050f0409080a0806011107030302071502010b01020a0f02060403020409080306090a0e0714030c 92
    0x605a2244681e5000443c0d40c5006401412501406c10032407052008000d81e600f090180c040c41003c1c0e0301c0e00c07a030f925501c0103a2400203107040d24940c010b0750040090000041803100c0d40d0702000d0704c5001a9120003000d81142d0400003000c50072100241229024804203000c102c0e40c06442001a01ca03004052402e4101050007031642260300b0300300c88650100e0101f0042082c5030040e015907822248080d03040010020001c0c0d116001409507158140e5602e41c01d00d40c02409400c03003001860018a101d80d00d900382c0070301c01d010b0300c0c0034014035003d400040c605281c40c1c103007803145440c11904414054200744503a54200c1e040103015060307604209081c480214111020300c003500c0150702c2900100600d0346446003150918510076071610030740e49040c140f036005980108005502690083e98034081340e100f171001450b20f000d55007010790010714000c0c048081082c1c550046024050444041c0050303902c05c8098029100c840b881a9031641200b0710420801c9248807000d02c0000d4003c087da0398004281000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 9141563 1250 9140313 9140321
    0x301120807020402040e041505060d030809030f0c0d0f080103020609040b030f0105010b131d0103080f0c0a060b030f010515060711100314010e040302120903030c070b030105010207050105040e0408070203030d 91
    0xc1b600340d40c2e0300d400c01d210030044c1000308080c0c007207145082130040d807400c2000a05030035440c010280520160400003a6130392018412100c1a440c1c110109440d51030b900341c025076602100803480e002c03031110800745185901800c521030480e5030050100c0d15160558041c0409000e002212903094401c0007071034003041ca820302401d40605115512503480d03442c101409440b0140340c0d80500000b04600075024040304481402505607a00500815940d0307800c198030070f29a00c0b54102c02200c501520441c101040040e03081a100d4aa08404075070101d0700ea0300e201400c9a0096032483d04a2403080c0f0b000c107683c1800d03c060041c0354000d2680f0110039401c6404180305200d800f40c910300091b510000400b14010084020380502140c0c0141080da18056501950b11100d01c410202c0008010445110a0b6001c00442d5020212032042d03c4140e540e0b110300c040345420038091240035020354080408e96520400c00e95003240c5181c0c515807020f40b500d8440f0001075120340c40a07a0035000c20046c0070702e44689801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 9142813 1250 9141563 9141569
    0xc0306092107020306070318051c030507020c0108012303060a0902040e03030408071b0b120a1802030309040c0207031a07020c040509060a0e03040f0801050a0c0504060203030112080702040204 84
    0x1400503a00d00040d1001e58100a91034082074941c01d12420700561000101175074481d0440c00e0000e2881504556143c2c0c14000a0300280f00d803056800d540c44243e006084000300210350b450500032a1143c1c4011f988600078503115a000880d0000104100741441100910040c11800c0c1346000303859044c00f00342070036412210b01d514561546805d0045003002c0c401d281c480008603000d1415401c1c07039690a2468403070910082c180c08111091241c118019010381d0009140001d00c640c0d40d400010708520390000107e4000080c80e160690181101442c501c8030306200307500402451902c07c7c040100130003001120410380443c451040040005003869560b8400b01c1e200c400148080d10f00001c00a1078075803000500380c096070a00d004e01c00100300000e500303500304041c107801140c21810420518998002e41d40b001c15486600301000403020819030040740030b031540001c140300180320322100352594800c0c2e00c5003a005a1040004000002c50280340154151107502c425161003240d4000405076001b0350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 9144063 1250 9142813 9142831
    0x2011220040503070b0301060206011205030d0203070c0606050406060507020607050c0409030c050606010302070309090207020d170d0e030c03030106110106031a090c1509011209140607020609070b030105040e0c0306 94
    0x1001d20992904200306002071809907102031641d03044c084020f42b107a0042c4101e6080802c009051000c200c03042c13041e43c1800100c00e4046407070307242030796004200c00c030900f90039907003a40b5040300030031b403400c2500030f61703086d02c5503925001e281c040c0c1582403084560240c14241e54074060040c10810660350f034020741030000e0203a03542007001c41c4035043c810305010019080d981810301c108080380000390003440c130000b01c0e64a00d60050301e51f0a9400030400203030206200070040f034005010f0241c0e104000024000346d996400041005c01c1d0074000080d030f2842000e00780f512550052004000c02407080e210341d102503440e40d00110301950751303a43d031440350855034460508410f0041d040021018040000c031000b100101c0381c5028502d40c204030b808081c8210b018450404c03296011000d8a40710700d4102e07030300455106260503074401146800d00d4840c44242e50f801c0040c01044049080d00d40300042110aa40c0e01c01d000900d141d20b400c04101c01000503101c03030030050268890b80c0042d9a414401d01d48217600300703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 9145313 1250 9144063 9144067
    0x220e01080601030b1005030705100c02030106060504140105030105033a0201050103060f0b0f01050306040605060d02040501170712091a090d0f02010207050303010312030905030706020901020c0406060c02011220 92
    0x51301e440600d000000f440102c03180c00040040203941d03070004000044800a80d20048815800a011514101b142e00c02035055801d0840001e89a030b40700000300f0840e0780d002c82555030711820400446061000384104c65059010180c5010f80031a0348101130078400070036441c520203601c462050540c0e020851310060250759a04010410300100b0f0003844240410950100942415000082c0c80c40740d07072b41d1401b81005000700004078a511030b64010070150000500d6031340c4410607100300c03030065401405107071b0004040b802c0084540103402e6009000780300030303114004405100c80420f4028070403c0800c2d6040301042480f03440d11490081c0d0f003405490118050728440300303520405412800040550801c581c41041028045400802602d0540e0360207504050342c0c4810f544128040c024030303200503080740070018154081011590080410180a800b603490818240040004481c6288602800314428042440c01580f0540b200c044401031901c0c006114550f91000340d001511000b640030313001d000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 9146563 1250 9145313 9145319
    0x902090307050f09070807021009060b100801030f1e08070305190206010f030b0a060b0a02030703080a050103081204060f0e0714030a03020d0c06020d05150f0d020105220e01080601 79
    0x500221010b07040c00e4600c959000406408190380100061858040188080210b21418801d00505101d9141d0440501403a49581481c070001c1101c8101c1030700c0794000b43c0320500c80781e000f003400074100c03500444071300d804c40119103982003542a44889014042207170389200001451440103028600d00a955864840064524040e10f40d0405481e403425507012000410444d40402e61510a582d805582d042150b25804903000c00381450f90000b80741c008004c00d000355032580c000301416405d80681d45410454907003581c140101c8000b0302020345140b0081103d20300403012801402c0c0c00038414000041d9564000d04c0210844030b024020780313000d81108004020703510201107100c40c0368900704e003d0061007074181c2d40650703036000c881c02d00e500b401500b031184010702410b64195503641000700d0090160f40340c0b40c481090a0042e40100c00d04c01c1c141c51805141c4d501f0401e0034039142582c10303100c4138541400384071700c4080142d046000402d031b40d5503100701083d0301072451992802040880c008103da541 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 9147813 1250 9146563 9146569
    0x6090305060f090d050a140301080f06070809070501030903051c0518031c0903020f1b12010c120216050a050307020102010506010c0f030c022803020a0b04030503070206030a02070b01090209 83
    0x1402034940c0100b0303140403060000070000401d61021400c01420300035a901030180d4151980000c0190741039041c130011000059010300866030380740b6a01e0031005c5d0303a0203645203c01900c00110075151b0401641c00702c141071002e0350095204280050080c10500d0803e40c209032048101c0448001c808101130301c1d00d01340907410481c40211503d55070b045025505016003c0403520704881c09100d201c88458541c1c1501d41414000e00440b440506484c09482d0111454035510702909401c80314580100308074095040703920350620a4051035003040e650500784102da01c0e4910069003291180d40d0401c000c1e003100c01d0000c4d4007000390000b0300d48504003a5845682d50300001e801c440c4001d08136030500060324000000030b00d040c4090b01905526040282a8042d980007007181e16440310020385c446840f4811b10662101d0921807842141d10807a12070310742d1038032282450618002e0740b0000780303254424040c0c100140f40c19006941d12411000005050032081d0b221408956002c2c2c1c0701441040e4002040ba111741 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 9149063 1250 9147813 9147823
    0x703030f020c090a0f020f270901061e0905120703110406030209010e0408070b0708040212121209010b150d150f12111f030608010c050703110304030204050106090305 73
    0x40349030015064103802c000200d40311a40081102c5689551000501d594a00700c0e4181c03850300540c05c42c0103441f0031200ca00341c00710f001c0391400b1307840e8013443c0102c00e02249400c0e0040b5041c3d5041b6920785456071079860201341800300c84940c90041c89030b40340020442d501c5000381542c0c1803580200400c641d915500b0511044a040020325000301c1c200101400076031120348006044507408072611210740d66034180343e8007600403600c0082c030301e01c1080c00703101d40d0503442030050b0b0040d03000303c806000c038002000202d6961a01d80c0c0841d59034600501600c41c0c4403040000300d50f0300400d0700d0004641c0040c003200240022031030b0381080018400100707100894640078410b0802c4c0304917044000d00e4580c1000034144021946202d050200640b04d00c1c42c000f004a442c1e0854401440684403500d070a0380b038030b902c0d4030440c01ca1001c1c90001740303404000240d40f841401005809810f03030300c9035450301741c082e10200c03903040544041d03c07858803042100000503280d0b4820a8000d00807075803502d03c000d08500c0c2c440e0403c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 9150313 1250 9149063 9149087
    0x90801060b0702060307090b0304060605090f04150b0a09020d020c071202060304060207020103090c0b0406030c0c0c0302010804020a080f0309040b010e010e09130209180d080405060115050903010e070303 89
    0x5a89042800e000840303071641124030b401c0c1c04658003034607070740c4500d000c440c070501503001881c00100100500c030400c141c81d0030400a40d80122040b0340a9a00c0d200141c1040c0411600a00148500200a2451406540241c0e8004030180042021984452505050340d000c542c59640c603d0b400607918a84c62018811403000c1d06681d071403241081415000111140405000030b043c0c02d900050800443e03009521000441344d00850344064190f0301d146d80350080d0410702c50403001c0b84c2414424182d540c45401c4514810b6400b4000465041c03c64004490030040100200d800140780d00f000f10320b141e41003000042d071066403001550740e011401d040c401640c400c800c07480c0c184140e4200003402c680c1c0040703190300c10342401c1e1000001a0340d00f805400030500c1c2114065000f0000d1003d0045c0e1340100d40350400418840380844505400d82c540485107070b002141c02400c07513041080144071488841000c0b2540910300d241c002d0404280e03200003401c40c0c0345140c85448583c41014200105a04120300b00d50b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 9151563 1250 9150313 9150329
    0x2010906020a080708180414010603050c040503070902030402030f030c0601030512190804030e040903020303180705010503010303080a2714070819080c0d05040314030a0f030513120201090309 84
    0x1c0d540b09584181942c012850f0040c80704002107902c041c2d420400303000c445a003000800a201403010740c4071001d601d0300c0c20702803840041d040000141e400f80420b02160200c4402a0080142034070f0310024000a4102810899050040e0324110160f50005c001a0082600a1024010f9549140f400914044020f0404000f1110900c42503520011000c4802c6000e4014200b607003050361189001c540d14803402030000d038024984075500040c15030010241d032194414070000c0302601143d03040d840e0340703004a100d4240094410001400024480c4102c1c9405c009802c0c000310703800e5071018180f0341d10680d840004059901e00c0b010380050040b00000f5a8100b4802d80c0902050750804044940312184900b0310100c0e0441650300c0420840050111403800c2c400e5002c2d640241c0076208020940c1c0c0c02840251188004001f54601b1044003108640d10308096458183d04084140c0c42036014280040001302c0d0005410000c40119100c9040405034802c5540002102c050500d03000d041d6102c0e031740289a03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 9152813 1250 9151563 9151573
    0x80d030b0603010509090a0b0705120c0906030601050706020f03010e04120c050712050a05010615120605030a020904060b0d03031506020c0303040306021c0c0201090b09030306090a02250507030201090602 89
    0x3a03a120201100d0541314143d406283c1da0382e581e11560320340074004100401e000e011408002c802e84d07001014003038080310f00c482d0040a441d2900160b00601401020232750040d0b00f000802c1640d8007641c003c240603489404050300701544119000e0341504240e110b507010201c0d800c1003100b0050701080000c0000000d0a000202604135111955940c24a009000d8942c143d041140280041000b1228036030398040000c7c02059104d507003410f0314141080d11003001c61a0f41a00000c4a007150254105851020b0024219046d498080203a040b5000e4401e445080e0380d14441d0380c2c02d4032142e0100001e00d0181d00c012409607100d01e5551000d00180d80311508540101e20b50006540d000300c202c0b01240e40000000d600c5a600c0030a5040e4001440c01c594196842c0c400b01010300c0d60190083d96829014820342ea11a44d02d126065880e8032048a0300d40c0d1101c003201c0051b052602c1640030b0b00001288501040d821140c241c44120050096131041d580c0c0d92007031030100115a8802c49a802400c1d1901c0940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 9154063 1250 9152813 9152831
    0xb0a082203031a04180201031107060509010905160303021506130c02150604060b03040f061b080105041406030c100e0301020d24060f0c05010b0901150206060303030c040306020f070c030c080d03 85
    0x1001880b00d417800031b0406407a9800d43d1b215412440a652005801040402243c14040340150080403000c07811620b40c020702030903620303001d070581500c0110b80d05038002d0720203a2810910380311100001040554001000350222070504064801e16036842c20035002000c041003016100601d000d8024007003481142400c4040c01440c2405003506e0300540d0202803641c10400f030707103041409044440c240003c014000702e6818805e90703004000074121801035900f04170695000c3c1400a8003142200d110340c25a112030516030321801c207880c003010304d44054600080080341c2403000a013039074480507880121540300d4501044505034400b5100100030403260040b5100c0c503001006c2c109000305984402071140d2659441c0602c0420f40060508000060820415684a0070610092a81d4100001c0180b080400180560400004481c0580012409141400c0c9590350b070402a40c000840005101c02c18000b02c000141d1600d039100103540f04800c1c2007040d2f402c08400900c0c217502c3d509030008050a101e0f040d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 9155313 1250 9154063 9154091
    0x1e060f0603020f0903031303140a020108010b0a02010e060106030b0102010b030307020d02130216060203151206191413020102120304030c12031b031a01020303010b0a082203031a04 79
    0xa42112158100581c43e040d44240c0c0050a003d070340030043e0503000000d80d01d0344858040301d02c0c01c15603110f15544030080720340c00802c0d0380c1e550f0750540003030200304004010301504403040302030481010a84004103107070341c0c907040301410483d080e80014086500d89101901a40c2c0a0289030f4a80c1c0c0d050b0011030401e452074000030790410071a01d019000d401112100f0303024080d01d40488400085804144282c0102441e02c4d100a42c411900300c040840c40c561103c441d481c021a800384242c0e0140001e04064903580c0303004640c1a00500d013288120b40d00d60441102040300302e81c417441000c424190b110150f546000290810049855070042c4103404c0040100003a004000300340f000d60481400c917140306518205800078035004c00e050000100c500707030841c40c0640c50380000301d601034481071045084c0ca500c1c00690b07490001f800b501c08082020f03c41c400b00e07036200352030746540620151082c504600720048450348290781d40f0801d4001171340300d000088510f00c2c06550070b6816502940d08110000d140905 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 9156563 1250 9155313 9155339
    0x20705030d050402150301030c06110a020a09050c0d090b01090606020d020a03050d0e01240605070b04120e060a0807090f030201020307020d050c1201050108061308191e02011e06 78
    0x101003103a942e070314041020741d00d07403160300c0208242c0c40030b5090352540c403420003600441e014030920300040c0c1e641c0040101c81a020410b2503d8945c040c2424000c5030070000404041c14004051226201042c0300204810745a40521070a25010358040d820319410f0031207e07016107440c2e40144055500200c86045a2940000d65411054151400c1a100c0701d0542104010300750802c00841e881d070800e94407002054035000c2c9602410021060341c1c2691b41d44003c00c0c2da0a010300440981058007141c0013401050407000d040300310015528107079001d07520101c002003141d0000c40724100024031040c10417205941003402c640142904544d00000c407451070380001c0d52480707560b030000c0c050b0250301f4095080240130062203048040041c1041c01100c124003102e40201070900c10002c0a104010106c0c3e0507004100300ca0140c0390b005001d0320703c0d141d0301480036403218442c400381808024050801c04031303d600107a00a00d840140d68000300700c611160607940740c5038a0300f01c4010140361401000700008140207007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 9157813 1250 9156563 9156577
    0x90b040e0d14090307150201020c010b03011503020d0203010603020406080f0609010614062113050c090103020916090812070b0f07020721120f0207090e03031315090302060709050402070503 83
    0x22442e562a404440844d0400d0310f203a01c18004500c80c0d00c074031414250190041c3ca034103504880200a6508080101800d03202440420b42001c001c0041c140090f0800690801c0b0341800030303001182c080d640340c1c003041c101c8031141d00244243c2c1200400c201800410700019400c419400e00070322169043c1590f211002c08401007507445000005160503521000400100700f01c00105c5a03a881443d101c10244180c15402c44100c665000c0c1c00d0300c4d9042c503c0d000c07400906030394010300048601c3c0d4803a81c6124032003100184d07145c1807064100c000170382c001040021913442c0704907001041d180d00f041e20380360001042c06003d610846101401b00420680c5c001150360880f005960030b5107480c140341d10124408020407001070039072101d50b0110303580c00ea048400e0308845d4410b40c1c200c0e100307150b441c0d620b141100d001d80c240c05030b03039007040002c01d40184100614131178003170080801c1c0d407055907102d8402c0d00315201480210050f8004000b04002c0b0780d04a880c01c0e00819043c4e82c19842c040c2c0943d245601c0e841080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 9159063 1250 9157813 9157847
    0x3030a0503040212060103080c070602061317070503030103031e02010513061a03190b060603010305071503020904090507050a120302060406050403050f0301140f040b100c11040204090b040e0d 84
    0x4000101995980380981113001c0010081c2c82c100d50f104d0500140503403140c80500d08910801a000401c00c0c400100c15100300e01c0d04119000780c101d01d42c2d135400010500f44d5101c0c0d0400040c09000041041440114000c0d4400e84a0b080c0c100f03081d60881c424a03159551100035a454031b410000568a00a02c283c00303d503003c0700c00103661503581c59003090425003ca819030140b14101d01e010f20320840c040f41081080c0524166840e60342d4900400a0341e1209020050254105407401c1156000b4080251425005c0c0e040160a140511700840c0c00c403505500d098403142d015500070401810610583c40141c1171020051020008075200695541c03000b400c010011a550710000b02418811019101070341804042181c0c0ca503500d04a08110401c4c1410b001c0c410031441c6c41031a410302d882c0c0b00f6080d001d1400780014038040702000c01541c243d443c801080e51041c0c81041900d889a86510003000509062480020405100340c180320884460002000450381311075a843da00a40050380a46290509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 9160313 1250 9159063 9159067
    0x303030609040c080f010b030c030115090906020904020d0b010f230310030206070302240628050301150906090203040b06060a050c01020316080709060e0103090206070807060b0a09060503030a05 85
    0x15240092000c2100e50112119024a2540c04c031740d410190800050940e0450841e41030f642c2040070182240c0500780124a50b04050408100f8120107401c08500320780103080050a1814074004907041c0e9200c10400508103950740c03020111903810803812110aca40342d180c040c42a42d4110600b40e081902a00088461100440054000135103000c040c009154060035242e00c0d55120315010790340d029007005400c43c0d0400b900c11030001b140040d10b058454680144503c200d00c000c40f031406c030f50203985d0403c1d20040c6015540403482d510240581c0d0414400395403002401c5141c0518402152a943c000a10340783c010412710000c00c10140d201c98100c80102d030865030b00d20012000340c1e002e1060a4030440c0550000c02003104070403201001c041b6501a030344a0a14aa03540001107513005594002e220110b10101100c08240d4400d074080031586d03102400ca10719018003500c0c2d6041c9a04080310850742039403a035411507030030f040c861400c1000705400607062003840c0c14071000a807a03000c0c90540f4001c000380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 9161563 1250 9160313 9160321
    0x10e071407060f020705100203090c010503091c020f010b0a080a02010302030603031204050d0327110d0c150905100206010603050601030f0e0106030b1515090307080303100504060b0301050303030609 87
    0xc240200c074001d6a00c540108210300c40381200350081c1d04440020b4465000d0010401d800701118000c0340d01c140d01c0c0d0400342691000c040010b4542b80c2001d042c040d41403145604401e4100f803251000f148122882e0010a0051014100320f4295001a00d40b02d001e4a0482c10801c0b031160001981ea01c002ea0900303004d6100e65901c00131a1641c091100d0f080302c4280c503602070106202000c00e031010b0044050f517083c44034450408d10182c1c103000140d210207552502c0183d0ba00032a004540402107000010203c4020940d9915005031040b865001980c16411000ca031269080e00010148001e1074291101c0a01c040c0382000030303495050520510b41816242d9002510aa10a6020105035106244d0801131b24240d4112140202450b00080750340000c2000850b4020107c1d2103034000c1c5000082c06c0f0ba40c5d44070440c1500e0455040650400e4140c03003402000320303088505002942c414407000b8000e101c0d5914000800041c0d03203261f030244000260400040c4040e40b8040120782d488441503c49001c41e481e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 9162813 1250 9161563 9161597
    0x60504051207060b010e0a030209040f05010b03010905031b0c01320403050606090109110706090501140717100b0f0304030e0a0803040501030b0f010e0108130c0303050702090f010e07 80
    0x5050410301c010000000d00e401080f11990010815840c2a42c6014464660b80140a540d84440c0406580700443d40c0c00a800034204080382b00c0110322440000c034003500300301f022030700399891808100c9003500041100503194459071031240c0310b112400c0040c0b0054120b40000390490003d4007100d4958040040f402c0b80860320b064031541c3c0c000c1d502440310307651690f07424116169030050750068461210100009880015400b808035109040000507140c0348407644c50900605c0c002104031215500d810088082c0401d02c1061417044101e51604000c0c4d4000b140400c18180c00107045c42e86215005405000515000c001c0d47e441802c107090701503803078803141400e40e2404896809039074041c05250340420050000700150040350000e8070b0910404014108004a21200c807180381c0c001010045600125885190640c0c1c01004400000503182c400d501d03200343c40c1c18660000d0b400714400158100450034003003cce05038842855017090741c895043c0b07030395028031500140090081128a40328022091 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 9164063 1250 9162813 9162823
    0xc09140604020a20070b0a0305070807020a03050f0c1204080c09010b030403020303061e030610060201060b1e070c08030301030308061c11060903160f0f060c0b0105130209031510050a030f06050405 86
    0x106c40f41403030701e440d004480103020b420b08507001030000e00580046104580001101c802d66507240d20341c00c1c09c02104d4248441c05070003400e0003a103507114040361000d038014680e0040019003440030240c00301030326402c24058074420607400030010360410020000801d60100949030000022a8458140000a80c00c8040a414040903e0345401518148200c051039000316004030703010b0360001d2101da03075500510708032809050710345030550781d110745629500a5540001c2110910400041d8603441d00d901c2180e00c0c640098100300c004c10300c64000c0c0001803a0030b11024081c0440c0248024184d40280d88070741502c001c0c00c03201401400c000c5689030981d90140100100c00b2400046010002c0d43c07280c000740710141510510040311000e1001081461194040200e420342000c4660566403924042c04100c841640034031800c10b034203200c4031407503a4080c0928440114482c0e00310f04603050000c4801c000403481d40c0887d1084141c8075042000900d200c84131080309411442c0015107680e1424054201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 9165313 1250 9164063 9164069
    0x103090506090606010201050c07020a03080307140706050406111804050601020316060902180903040e190207060c12020c10020309010608011401030308070207050d0807020103090c09140604020a2007 87
    0xa001e4401044400740c00014030902c9124242d000348826150582c40f002a4411104043d4201e10b00380000e2003c15200f0b8002c58000140e0300c1c0c00240c000303645c1c0741c4d40f5181d005001d08499040c0c0302e4042c00b05103c05401101610308101c0f601c58030780b4144143c505400417816040728016900c940000d18541e009201b502c0904004550144405041d80b4000d401013014943c124405c40c0e506406c1c0d21214a02d00b03a5611031001440154600741c00c3c4a07914441c504020302034801c020710080b24621200303481c00907206151240314041414681041701a0085200d84030324906070348107009144000400140c440c10b900342c02140103980391030f400804d5014120540041d4601e45c00e10302261990101800301038100c034081d0b0380d41e00e09030320742c268204e890343d10354801c0f1544088042d522002092a160080104134030504001959500e25911104001025401001420f41d10449109040a208001684030340101d030218a4606111805004604288051059508152090040c40e8010802036000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 9166563 1250 9165313 9165323
    0x20406090213060306090212060111030d11030105040c020f0303010501030c0e09070207081002090a0b0a17010602010509070501020604020306040303050c130e0402100206040302070b0d02121509060a140f010309 92
    0x2d515045002d41c5202c03041841481c0010b403501c240050340404c14400d54400314942914100961201001101d0414944010680c0c1d4001000150a0b41350b45100d000d0381c0b10304800d80c598a03503141004020490f80c4038200801550003a045c22078000f42e02000304d034103458007402c0004d6100b80c13590707007196000c7c20084c034650031101c144140400c064002401004481d0f18000700c501c00307408588400c0c142e0051650722500140c84171001c5c1304042a1202402c4c0d201c05c5854612810104820703040040a001e03803041d00940d40d501d040c040411401d0200d03002801e07081c0018902801d181d400b0030741c0c5100040c8060105a40e80c000b0503410034020040b248402d1050b0a000d0100d07480d05202510180107580488c819100c2d8144444600d00100380280304d00d4054014000552400c100d904071540002910039040381d081002d01d4858110060642c003ea00076000003625552100c1802014600944120312481441a0800450225028500e00b1203015030700448031803007140040c2c015250b88500108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 9167813 1250 9166563 9166567
    0x52a060403080306042405010f030f0203040c0e010801090c180603021201050f0a0507050921120c0f120409020a05070b04030804060b090606070201030207020f060705030a090803030709030f0204060902 88
    0x1007442000d42c081c43c001c15003124200001d40064540768541079042011802409a00000b00300c00c0d800b8108041082103a824041a22250349248030100d07401210308440500700c07070703805110502c44086e01c030340034011f8900200100f030320b03a0722140d0310042d1910540e01c0b81e00b42d00201d0900b40d802608900000c40c1c0c0604001e0214114200702406010300b03c0340380c0c4001032a1000544c042103c0e008150007081192a43c51610190400b03010300180303446c10740c0d9801002c0040b0080300c85001c122215608040c0100c60f17032101c0f541020a030030940c03403c0c01c0e009940e10880104031384201c0039084a084407420600140c0d203011142050b070344d80c000e900020b4808080d071070401c400e03d5000000340c2c1c0b0451180008004007244003081000006003518825005801444002e00650080c0d00628403d800201000b00390b0051400003107035944542000c43d40d07500046012901d00e508200680040c1240030051425840d00500c000c1000c0d41a11015002c10f140100d00e20540d02d5a0340b214002e8990100c01f55 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 9169063 1250 9167813 9167819
    0x60a050d0507060809030702090a09060b120a050c030c010e01080a0608010c08041a07120b060c07080307020102060a06050f0d1104090602040f05011d0907050408010f0501050f0d052a0604 82
    0x1038a450580c4520f6000ca5031a07400900c1c1410044101c0346001d40c0185101700316141c102d1090b00501c1f05c082c088a10940d51268010566204080c03510302d1450000181031a800301c0c9095810b0082d00c5407000d000768080510352045a170003240042c503204084c038002c0341c076644000100c40682a2980302d032201d03520300401c942d410380d4803c0c05144118001d5a484614003601e14040348091011902800010941c100c0ca64174007841d90041c4ea503242c2c0043c003003414244102e98050409240e40d12140459000007040f0b03045507010701c80720f5800440400e0400c0142d1801b03020903c0e90841015007441502e903107017010200180d007250800e010700d000d00104880c40f0b2038503080c0000e60040c065203840c404040000112580308458252508641ca50075101100e0350b80144003048030040c25480500000f031102040100d424840c200c19500f11441c041902d524020511440b2610500c1c814051200a89008007103200052100b0803031301441203800c2c00e5070003e0f84000703110341a40b800503407001c8005800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 9170313 1250 9169063 9169073
    0x50903070b1501080603030a020c04020c010b0307090c030506060403050606101106100603051506090d0507030803100504060603061508100807030b0f0105040203060a030803060301060905040b09010c05031e060a050d 94
    0xc0452002e080e00c0d01e43d8580c07620000c05650780550a540001603000c00380420441c14240c000e8489045040000305070b46100c400000d080200a0304959005643c1d1646071035a0350741401020740002041e02c540b8503050642e250151100d5004001074000c81943e00003e038114466407200d001c548148042c0c82183c01d2034900020031450301d12031840081c0c01c20300460b404412038101044a40001040036103031141075001d1210605642d013090321503002d651000004110114004c51149009039a003000e0035061004000c00c480c080d810010800d450130209100400c0d00d280300822507016420300500c0f0342c1d1076480d9039440c400603411008560103102000800c2055203c880ca00401101a00040316a01c5a0a00080380011100c04d6444204e9071800c10100740c4820003550840f4014002050b400d03120700030f080c1030390015941101e8054101c0f04101800d80c0030320906041d03502c2443c01d5491401c042c4902c3c00c1c134080c02d0110030428852680481d1450395112040002040040c04c8400003044d6410f01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 9171563 1250 9170313 9170341
    0x30e13020304061b0f0f120f1107050d03021303020d0231061d06120f0d0e010e090f15010e1203040303021c0f030203150a08070f0f03020303070303050903070b 70
    0x34500d040854112101d20550007020f20f001d000d060f590b2210000317006c1a00807036961182e060f040d01200c0d40c40030030701d001031000c4c010b1064022820b4001380da03030b90301c2d03180c041e1500007a00c1c00c0004042c414004c1100b81c0304018a10f80440343c040344c160019544600010710214070b6807124034001541324241c403075451300d89903407a2105810034108200c2140e0b14812121118201c40304c0002607442440007400900c0c004900130107803d9804112070360205205040f03407420700e08480140208200000360340e160f41e8000014800542c2c251108001c2c0d0070700e0078072201d0205018014040a050340707141c28505912030380084001540007004251340c08a8200a80c0c0c517070b88070780010340060003009481e035184a03142c0560b554952003130b62401102608610700318000d40025041c1c40c0e80080c07a10405070f8595401c070100000d0132038103000d8104a0710380540c0903401c8540740d214184420184030f0400140e80d000c0305448401c0d4050a01240954460242e18250321034078000420f0070b0090018000c620080c0c4030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 9172669 1106 9171563 9171581
    0x60406030e07080d0e09070f081801090605040c0302040e0601031709040608030a030e0c01020a170f040302150301030303050705070203030a030e0c0d03050903060a09030903030e1302030406 83
    0x8002c1d00f05807510340660300003000310704c174810380d40743c02c0305003941100c0780f0f08004680c81c244200c0034002010040030b80c0900a02c0010880b15a08290000103910340d01c08010091442c280ca01a0503403950f501040e030045240040c64121800005119810780350072140e040784450b040d855a0f0041d500112109030410385904001031649005c00140105485d03035100442c50300c0701c032030255242640410180381194404c0c4d070100701140c000542d50207046c91480a144d515060603410220301d21990b80000d4200d03c1120040b44c030b42050030041c5058038400d540603c0551682382080302d80740217441000e58550400c10107407400714065448060580195010340704070f031880f01c2c0024850192090207070041307100004e0042c0c2a140078010340e0740c0050122410054510f079a100200340c2c0c80381c4d01008007805001c1030340d192566240e00700d021016019100666481c41d1500c0c01c10301402c5111 = true := by decide +kernel

theorem cover : BRFrame.Cov 8992813 9172669 := by
  have h0 := BRFrame.cov_init 8992813
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8992813 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8992813 ≤ n) (h2 : n < 9172669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
