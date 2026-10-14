-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1614
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:52:34.04791+00:00
-- url     : https://prove2.me/submissions/9a976faa-432e-4b88-9a27-ef59d4000f14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 290107913 ≤ n < 290287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 290109163 1250 290107913 290107927
    0x50c011d01050612010509120c030c011107060b150304080a180b2a06010b2506050a0b120c040f110a0503180a05070b0c190b0604060b030603060f0c040803 68
    0x640059205903004d40350340e50070b0036480c0c507600d0a0b00c000ba18915a140c0003c00b4401040014000511944120000302c0349070015050406003107818072807030149046004211030081107003500440c10010811030314050030380c01b1802c01b854140300c00f40000340742080c006005840d07580500952400d008801c00d038012150f03038450504034198402c01d9184030a4690513442000c41102003800ca01c032403454001056943e0802c0303041c115990000b607000c0511420a01009140c0001000c1d414185104540202e080d040240401085c2c48400c15013504c03505000c1d14030143e00c07000040300d14002500f01c80100e204034080f80200002c02480c0d427031951440000586c06002e070707040b4000758003034602d241c007100f184800001c0141d180d01c00202d004141c1d0b00625420070240b12a034010300f0000406105507900181c80031540e10603401c911408413003425089080128502d89449881c00070030a11540600d545409d40000b46c5400300140703100410040d0001044081001c203080e40d001e0062101201d5032040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 290110413 1250 290109163 290109221
    0x3030c03131205210103050c21030c0a1110020c060d020702030a060c11071203080a021b070501080702280507030b0901020405030d05040303360b0304020915030d050c01 74
    0x72096112078203681403104c292641001c150382c218100d0382c010b000ba250389054541007002c03040c1d0041140c0640c44502402c80b104a00c04e00c010041d5280c600002e2445110a2908800160204401034400c03240075803c1c00090350041040a1116001c03120707242e0307504841340280d0081c0103032400690103204001130001040581e5000d80401c9100ba1035160407500259255070b0740d45090700030205412100c00a08000a01a0000903000500e44801508024424566180103400243d00700190741c0f042c00104815604011141c1d0000d481b4406460107081034403c40c402c42c2e0340d58400d1411102480644c1040c00b07024400c00c40910f5010f4400301603810018095400303500315000d22031081c0214400444128040c40403a0103ca605803220500c05e05440500821a8881a60401d20402043c48071882c8840b00040c4070140000a1031035841341050700600c505544003c0080642d111025500803031036030002a41c0350f14441c982740865881a121111b18054481c41c0045580c211a445280c90494 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 290111663 1250 290110413 290110417
    0x1614070b0904050112020102030f09010207090e060a061a1606060b03070809070b0a1b060902060f070b060303070c05090405010b0a03153801170406051803070503030c03131205 77
    0x1c2002c0320248501d98a8450700202c2050b00031000b40940c0c004c101c51f04500e81a00090414044140140ea80d181e07030f1650414182c405100001070170b6001301d400c0003488010361080340068a850b0046981a00c540c0c0e041083c18840d81074824810480380021508001c1f041e00706c00007a214081c9020b40300d08100b14040c244000c00d581d00d010a02a0078030214550000506991060803030f80d507010030907205414080d00041c2c0901c0141e601c2d0791148a08000b40c0c48843c01419500c0300d6000c0c4070b5407240c085c1400405c115000d064035100e50010080350b00412440380e4450b098450488068605d0340300c41c0b5020340101800d50840e508103142c207400005000401005020100e4000000c0c0000f603c202c880440034041d92061a441e1600f080701c843d031300d4800c130003615003551060401e0f00c024440c001e081038801c842101c04442d8191594104400ca40c01c4070100f50401004000550030441241c1e91705403a03010041c11940d04080200000e0415240316010841d86904403070503642d5546032090042080d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 290112913 1250 290111663 290111677
    0x905062802010e071203080402040b040e0a05160e0603030d1d0a0303061a0a080f06060c030339120a061701330e0601050702060d06050114030c1614070b 67
    0x240c004c1c0100042c2484400c0b8242c00001e6055a408180703030349650822004240c40c83c42c154000f5038030010403000380000c00c80d107081ca0380124010811101680c2e44030101c042903801194804c80e000301400b0094400100b500d1076900c20050118000c00200212480e50500c8a80d4254030300c103002d030300c1041c503030141d0211050381e03000300e84c558400c400384004000c1c0c0e00c600b600c640005603c030340000b80102d07141540141c01c504001d124038540070301c452140386103400035115514444554905900c840c4a0700d130b4a10825402a500300881501e0844a640940102d0300f170b03488600041c1c400100002541d90041014040000310103a81c51800341c4410b0082c041128001555202501c40c04200c1004165031003003a204d001c0032003500c44c2808214240b00d00d0282945060041c02d1049900607a2848080c101030000c036040003455600e01400140b800307450b0b02c0398640c0d000c000c10505c1410100e0804a40782d046040d03a007460003d40c07920b8440d1035050003015850b600e001c3d42d40042600749200004102e5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 290114163 1250 290112913 290112941
    0x3131b060c1203020f073801051003050103150b15040605120601020f0c0d0f022d06071a1008010c02030c06010902040b0405210109030801090f050403090506280201 72
    0x402080307407050f0228403410650b090002000c4c00404000ba10804e1805c84051192889445103007118101c1240d8244a10b8020354910000d40140300c6400c1090310200390341c0f080e180c00e01c100e5146440f01d405032020654007059042d162a016800383d04d801040c00c4040341003010b115543d60f030b1245c3c003d000750070040100030302c1003500c030216a0703540c800225910000c0780180684030340e01d680402c11102200203082100d070f2404500e0b0510159441a0941c0580740154198101e003500720221f41d03e0070b00e0140c0d46d0034407420050241902050b180d10030381040070030054800c0155216954044140b400d964030000d2290b0810392880b01046c0d002c000342440000d054100c442598a46400c002a401540644d10b440c180920007000149002c0261110441c030a00b520b88440f00c1c410b8000b403d46102030000e4020440c0b000c0100802c07000c1d84500e406e01c0306504402c000b0781c01c16540040c8054000d00c6494451140842c0000c1c040c40700301180d02c00b0454551b00c80c4620000345034007030701074441e0b50a1010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 290115413 1250 290114163 290114183
    0x30426280f030905060a090303060503030c1c02122a101d0c03030f16060c03150b1c0506010e040f0912020a05101503080307020a020405060f0603131b060c 68
    0x100c10b80280580355159500c44080c0242d643c84a07100e200501205100ba4205034440000290300d4505000074040c3e200084040c1807041c0003544030440c40d2890a403400115441301d208088214494810b6403080204070310000a180740e544819500094854507100d8113000d02d1050b40b034414055070100002c500072001060070f43c03803407200c1035454180d211003668140c1c00070408801810b040000600801d0b030b44800c00e600e6201c042e00c0d40001c80e4010006074000c42e40c0c820000100d040004003820003000c103411120301d000d1290341000c0d03c404003042c10700d4070303141c0b40c2c00130600b82d03070003143d5511800d00060702c104046102d1014600240602c142c01b130b59104081003e1844003480422480705613a00f0200034145400000d90920042850030403621151000303140100015558000560241da415070007040d01e0181801008112031004e002584243e400741340000080c0c4840050780ea20000000c9000c0c038a942c217050030810174084407850358820126000110701035400c20261007407103000303030380d000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 290116663 1250 290115413 290115437
    0xf2101032006070f170a0206070e060903030a0f02031b0a02100215010e060a1205060f01060509030d0810030b01180e19082101060e031203042628 64
    0x4620700300e003150070000c100010701c0401d8000121403025480350440c816210000009410a40c001b9103807000181c004d4000e2005c02540215401c4d007802088076071905e850300c0e000019070b59200d8030b0340c14010710000380b101d07c642e18028000d03184a544001049880244441300a5031502c0300240224070440d010810702e00c0c5e40340300043c82c08829a0707110224490340d007020341c0c0302c0540a00400707041d8040004400071602400e0900c3c1010b003540304030010089828005031040308000140c00503400c0003c10302841005a40001e20441c009501d400c0054581d00d880c4500314224034180c10203011043c4400000481a01c50206603002e0a0a40c404016920720818600d85a2000900e41c07241c40348600c032000f0215402e04010300e000e504140c030050941c401c086000445030000d030300c00008500207400d10140d9040c2444041d40381e20348812044d00c0c618280d52040c400050001c0721860039006402140581b0009204072a105100000030100701d141e0b1600b40d90301040a440c00200003002d0791102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 290117913 1250 290116663 290116703
    0x12030a02160f1206060b18040c0c05300f1e0301081b03011e05062e030506132903030702010c030806010c0204180506070f050304080f210103 62
    0x203825282900a02c154441c582030080301c2410701880c003a500a660b814000a0880d0800010010074684454540004071224100012074920782205414040c003007100d0760000c3d00c08981c00e100c52100d00d5400c1c0c3d017442030581190404090307461070b210300e10000410805050b0740c080030304040b00c0b07010702d1400e507072660700031964080c0400e01c581016648810381e070b0341c0340f01c030f40c006207a185103405000000c42d0804c0040161240ca201c1d45400407150390343c000c1c8101c1d810814421726000c003040084c580d403104010980c000164a8200e00f800b0140c2c0c800101e08a030303851000e00c078401f184900051001401c00c0d0804031490307081026900307812140c00006042d80c200841500d4540350140c40c0e00c5c0e0700c10f0740d54600341c891482c0203002034104543e01299400580e25846550300450701001050080b000518010b440d000b4040c083d9018003458514003a47c45500004590f4041d9101d102c242e00c400d107600c052400c60060301e07801ca0116445440108056003c1a150707412a400f541130344403e01c0d034240c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 290119163 1250 290117913 290117953
    0x40606061103040302041a1f03202a060108030c011503030c0f0204020d0204230603010e04081e0c030d0f051512030f03071706012105041112030a02 65
    0xa030581e5002444200098a070175032001c20140184413551505140c0a000540c5440840d034141b80a05203c00e01d900e51140c2c54820240e0a400ea010b0b00ca07403121054441c00a98014106960030388240c0042c0c103501c1041420000340321040880844230030b0358460b07061603166004500000c40e2503280c0890640d03412050000e110440790141c0b101c03002e4111680300d005c40080106403d81c3c120703400700300d00044000503100510080950301d0b86100800e00d28940013010000244110f80b2406081c4014031401c480c502c4003540090f0b114481c15603440c5592030482000e014034001020340000440d1a95032400048002e03d103428422004001103500c4540440881d14150340c50030600c102040112005d09101641c8140b9450800440b400c0c4480c0014001d04ca9004841c81e00004864454401c4c1d80c0303031016501030304801c003403d105001e2410084405031115107190410300c44c64030341c00030406105500c00c1d02c0b07211a402410352001c182500e02c41c580d83e64000c0500714010710a8541081d404802d01c0c0b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 290120413 1250 290119163 290119187
    0xf02150403030806090c030f060a1e1404050f0c1606060f08160812090103020d060609260a120e0909030c12041a0f0d1a1825110303090604060606 64
    0x140d50a41c5c88011048c0341080000345141e400c10a2210041010160a01c03c0403c418000302203041c11401e004085441d0012205014000e0b41444188440b2502d50521950300802110a184c0c641c0c14800810f400b146521501600b104c0c80c0a20100340030f03a0850624090300c00c0c10003251814000840f40039031024880c40791520b2a0003204000c454a49600004c20071160149005410960181c1298049032810348c00b03c4041094010104080362105560555040e0205a202c1a4100d00c11881d9129a0020b0000304021500d43c0d1980c100d40c0507403094081d050014194842c180b0307000f181c4982e00e03808800c0d00d0b6528414100959422940941144c0239241003c503522003c100c0c140c1e100100380c1154104074210350381800450311146041c403a40640410414131904807240b03c230180050341541c00030111001404804110f0b0031000d007255007031996144002404040c09942003154030501403407210840340170010038030081c42d000280042c0600d01a080800084c0d0b40e0b03040603141194040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 290121663 1250 290120413 290120431
    0x40c060c020f0411070b010b0a0e06040e0411150d271a0709150306050f0103050c0909090f0109150b1c0308070e040608010f110f0f070f0215040303080609 68
    0x20981d40000c3c14540c104800f840d2169444500b40402aa20314900c098243c00c91802d050021800c8440158002050b800b0080c0a1b04c015107414240078007000344a2004002070110035619510010548403901c118196018200c80c1c0b13512102107180c040c01818411003205161044440740744410815140c52100c100d07404040d0070400481c03c0c1310003a900100030200014862142c10000c1c428801d5180f94114850f02d58000400f5401c000810952000c02c68141e810140381030308000e50100c1c12800c5480003001240d0001c1590380d42070f51180b0348207100f00100d00550819190404200c41060030307118070301c41d80c50305110130b1110380d06000124a690542001241d6218010000b1030300030320f00396400070980c0c64240c04040001e0041001d80da4258881c15103603550314000c1501c052244504034214a03c410f50a01d09209404101200c0c000c3c84100c4403401030005142d01041150b1400c20481d69014101d0300c45907890490480d42d58100344020740201307170340c0d20025040385450412580308007008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 290122913 1250 290121663 290121679
    0x140c1e030d032d090530030103030801140f0301020c030913020f0301050d0519080c011505031b0d020310140a1803110c1818070312180306020c06040c060c02 69
    0x9060024400495640014a090f65034400100440c0781800844003000960fa4114a034202031008004800c0e82c00d003c42c6d140e2841800184002903001c1851811a504801030081e40c649503000200d00c4040071100c075515601c0052a10170442c00403026005c403060442e00901050310448461080e803143c0102c00291840800061103035107000c2021000c1d03107000e0000c81d18401483c0310b410200300b401202c1907074003010101da214a4100d090044104511160609001051034100403da4802c040c00065000301c0000e040851183c46001c5452544d6030000c045451030000300704070000074070211800021541c190030005a410030180078110300001000380902188919403000c4038030402001c0309580d50b00699562402544d10140c00e03081c00c07044204a02980d0900c4020392034800c0459201040c160440c2c0f00c00c0010600040303803845600c2007410a591140c002c0014004603050030b40005150b6032020554040f4800e0000701148913511601c0155001d907101c09003680c82440c5507100030340c071002d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 290124163 1250 290122913 290122961
    0x31605071404060f09021e070b0109050601020d1d12070e0601020d050307051e09060c06180a08070611040f1401170f0a0911040f0f05010605040302010903140c1e030d03 74
    0xe65070081c012010908005261001c1c80307c592042980300788802d4030840c00070001440500200d1103842c2d040740c001d000400196180010103045400100c1034111450003001517900d103030f11100041d4180301c0880c010307211210303210300c49520280ca040d078801e801403107008845141d403800f0318103c9000c1c031301c1600c449040004160030202002c100000c20b1203454414001c0100c0b9031104405421103580e100050300b614504000a01000803083d00450159408200130700049610b032400c40311501d030000c80208100025445443c040d1096a03c1030346800100038000418a90100190b9407900099a4004031f511034000300000c40142901e0301c0a240b0340c070700301258401c02c3c10b5110380c0c4214072a00701080198603240001d001c96011a929148103611007d0a10044a0340e03c103080c003400c0d682c20003e0600e400d61300000c107440c000340001040034510320b000918100c0c04100c1000c0c440c43c000e12130b001c514843e40c00100341e44099415140244039880e40c0100303480c02802900390759142c0075903900c50214 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 290125413 1250 290124163 290124179
    0x1503010e040c0b0d020d0509012c0a02031c020d091a070f0507090e0606060f070210030b06030a060312021b01122306180403020a020409020102031605071404060f 71
    0x10020700100c0780d15101c000005240c2c20124068401d02244940050321440b6072413149003601c20007040c03c21613915100e600d0750010505001074030406a0000e501100d184c54045440c50000000c5010b0360601c25030640100540303281ca1000120503466090303580340148440142c03540381850141804030440c01c60050311001c0c03003038050142e040c002c2e02207454102594903034604190080d084200c82d9515a0714400003c1020020640c1115040c0c4089141200010304041180584400244103820010824050910a070051180e4040061515540b814103003210801003403144800c0341c0031100c00b40003c1c0054004510103d19a00c0007001040201e807650044644085c100c4a0b0901c0603590180540d0107510300323020096070b94036102e00300c1c01801c0c0070081100d03052000401101d0355403104c0c10840025404260401c08076415600070030f1260031880140d00350701904100340c060200c020302c0a030922000007003039400c40f0090a041a902c2800601340002d0b41c1407070003071902c1004140c00030041e0704 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 290126663 1250 290125413 290125439
    0x5010c0501020d0e0105011d0c09210607030f0e0c330706090606050604060509040203041707031d010c210c150209010305071106060d020112021314150301 68
    0xc0c4240300041c42c0c0101400f00008840b13001c4400300d81a0f5440f0018040380c3d41071004610380240c0c0c00c2c4421510b00d054074007034400d8410140190302a00291441e4242c0060b0712039904100b048480640b0b4907454000801402090300000c8850034600b08080e1141c201c10104050545510142a0b9000010880c140450f0f044011401c00e0349040d40d10f020310710011444003e08005d03407148ca40030a828043e418000d06642103500084e200c0d40c804c1204004913a0818101c0e550035106690168a0f40e487d400c00716642c5602c010f10207078614001500204041d4811030242c00c28003110354500f450350340070004540b002c3c040796005100001e04030301ca01c0c2e5554071b4904c0f40c0c8503088500d429894100b03140ea44000003102451400002d94020a01202d29030f014025154026203500d0708029090001d01c2c9150b43d085d0180ca940c7c060701e01088402d0641e481403618900014280f0815542c4803217800d6130200c9000213101c1e0400702e60a80303a06200c1498003c2c18907903050a0520914116400c001a401e60f070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 290127913 1250 290126663 290126687
    0x403080a1b0b06040c1812052509090203190b0f0108030c0a031d030f0312060f0a12020a050a0f090513030206041407030b04060c0206250e01050909011403250501 71
    0x84541c00001d54501a00c44009001407c04460341c503450b81d0461421901d001703c1c0c6100155880490015010f44207035048082081360030312000440d0250644c00400c0c1840b0325542450301008240c003102c001d00c41c00e01069400303a820f042c1050000e2b80d960016a442c0e002d4000f0100c40c6410244540c4013081c0b2075410415404048076104a0588070140020320b040e001d040100d1f604e03000403c0c42503001c6074580059502c181c042c2e400781804407103000007804d4405c1c540101e00399480300203070280c15503e500c070955014040281c0103009554032410121843c0580c0c2c0305e1082610704240008210032128a0f2801d031041d4550010035050302d0381c1c0e8a85011251aa880c11110700c00c80c0c4001022819600e4542c0c01070703000d2803002510100c0c800e402400c241008010000036040c002c9183c00110041104010041c1d1514080d003620800e031004071060f00c030340001e059004480000104150201d044040c025800860841d481d644000141c02030840b00c858440c400d45004410070410765001c0c10402c00d00f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 290129163 1250 290127913 290127917
    0x9150103020d45052109040510140a0506040311010c0b0406021902191b030510062d030803040f05030711010e0102070807150509060403080a1b0b06040c 67
    0x5621400030860703d50340d40d561401d030341c888507140d009440c40b40c90780320300740c0080c0c21038000040141140c031140c0d9a07a40d101d0000480a48426609a6003800107050710b042c80c0e40104180590b0400b281c04200317050207409102180c1c040172303544d8400d0340b0307107242d5002c21180081c029070300b8149903480300c0e109645200c14650500c00d45140d154001040d09050501c030b1481030b04010303210000040c0581400212036045015544000c96003905240b138008400d0100344e0010381000682c210303c40e034943e5444141d100400c0391240c800742c04140e00594000c0c20580e40f01e4504441c82e460400c0d00202c0003015510003101c0e00b91104001c0c008036045100940c0c2c40783c0501c00c10744104803550341322880c660084400b580c807021501010207882d03a21800780144101c0904c010800c0344e04000c01c0a071228498070904004050f50490f0412040c010410b4655055005003440c1d02d40e552414100e01d59403140d460706c7c002a41c000103d01482805100d147c0610750003400e02e01e0980e90f03040902c00100304008422003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 290130413 1250 290129163 290129171
    0x206060f0f28090207030c0b0402040e030705030d1109060a1206032003011d100b0a0302030d120605010207240e04181a010303020a032001060f031109150103020d 71
    0x84952a290300303075064001c50301101c0024001c20300d800040b10805410202903d8010080d00011a80c8080241d11154000c0c1d6401803039152480001c00600f0100d40441072030001103481001d0020103c06805007100402d414890b581c030000003500248504440c007540004140324903018584940c0410f64134079400d200c00541c160720780d10f50b40ca0409072403800414000c5c04803540f004074202801248205040701e010340d001c880d80c07850030030340b05c0b15021008017540359280d090081030b6940e00405c400031034015080d15140d105000340240703410004d110305003d05003440303400140d0f5440041c6040c1180c0c5082c580d081050413051a01492214008405080110780c0c3c2c500c0003290f45074401c0303401003001000c0374070711700c295450b10341e0803031502c1c402d51064911807200410100ea004628040c21030b6141c0381c8007414146162200d000300d000e07104c0129513507180c00d0300841c1d03506003200300b0702c256400f800908009075810010031a0900c82190704d1200e0310fa10840580255000c0d4003d0300e000c82c074801c4081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 290131663 1250 290130413 290130439
    0x72d08010614011707080613140f04170a0c0605060d061d01110c030f0306120105040b0105090a09051e07170307210c02100c05060f070f02010b010206060f 68
    0x982075030380740d0708001420100304000240c25a0807070411003404104501c50329152602000142800c0d500405240c040d045a03503900c40d01361100d038040c00b0210709403600c031030840c02d12161b000d05160302110b088512500c144080140f88000e403059170348101843c4d8648841d407101c3c0da00e46014203006042180c02c00040401040020075a0247e420200000310041000780148084107003500d64018801d02c0300741e81000000d4100a0100c0bc941503406000c0c01d40da03807611250046001c10400d51480102c1e94a01b0703043c04204000c21500318101c480440c1c52900689071030074014119400c2800040603a131010300e440f928005a07480c0307500c044110000f40d07804a0b42d12224200102d025090118543d003000a96004104e1168075005c4c3d84104400c10801400c8000006450903140ba00003038420340c1e1500c80c850345984688003620400e6800415280c040c10203081000040360300f5030302c200c0482c04043d00c01c580700344140f1070400107800590042800d6190001402072050642c02440c0c0c200382034403041d0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 290132913 1250 290131663 290131679
    0x70309050315150105040807030f0c051c0c0e070c020409030905060c1507030e2e0606020f010509010b031f060b0c0609010f050f0a020c0f0105070e03010b03072d 71
    0x1d01d11082c140300b6401c00514004541c00b840030b10b0740c1c03001e40c140324080c001030243d01000181941600d602c81401000c1002c81d0400d0145c0003460b61005900004581c5800307101c1d40e140c070b80107200c60710503c41d42c030709a40c4a081100a04c80f0484103600000c2e000348503e00986002c0c0c110032502400b82c24180445a1680e0100d0703003c0c0d100c42c91180442e070140d00d18004034070300442010b40c0407000b46420000d0452030307407445032900300d007440300d0114440006212000c880c030140e03000c00c000c0a0000030840b00303542e030a020f901d8607401c1110714419440d01001a941000c180154414030740001c0240c0802c403594018550005114544400d01d9a62080d001c00d0900411000f4260102002c0003080b0074030b00f0032683b80c00d548180c2500d4030098104424480514036840445070032485034040541c45500c092499031400c2042c0d45004210760900c0309001c800c681120200082c8041035009122901c040414190340784a50301c00ca00c10a0b494240f11543c101d00b114000c0c1c03524103081500c22805a40f2041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 290134163 1250 290132913 290132923
    0x3040b07120e01060303080117060103080c0106211a04050304060f030219031b020d0512151008070909050f01050f0105070f150f05070e060d020f121501090b03040201050703090503 79
    0x19411613075580000b4414140c0080e186801001403564030301044200300c01040d1142d1042c40b000700313001c2010403990b0815100303420040181258400140590a80421800440640324801c1c2e0340b005071640303940810b011002c0664072440c1c1000066140c9490007108803541290b41980c0c004141e0709104c2e18401281c0c08071350f1903400c0901e40d004905440c01c442003845400070b0711000c00c2550301c00510b14105c5600f04098490103110107280384400d82d100c4620702c00702c1001c0e051483e408111507810b01c0c801504a2192030142c2e460f5a0b40041854a4030f8840044074030542e03a00c0e1205403040f0040105191903403110000081c189802410090155500318102070059802c4519046901c075100b00c1082a00c55130001410200d428005420142c20207004903201411090044200141c03d0311144084e40440307085038810266540e079200c00d40c0e0100d04810041c0c07500c21000307121421481c1075602c500104419191b50b19407107441c40c0c07100d07401525242e126003003c0f028810720000020307036030390140f03c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 290135413 1250 290134163 290134181
    0x6271710091202070602031819050d030f0306120510020a050f0c0304030201020c04090218090115090506180705040b03041505180d1b03030e1501170106050102030f03040b0712 77
    0x152041003080402c401906010301c40d040102150302c2070054007100c5113445500002101e0944044a00c01d91750710074800d1058450300220380100c68041c1050804d070340f0051401551390156020000345031582c41d0480d10701841a80a41194400c1c07504520130301d2143d0051800c602c15003400d0b031402c1d0b48010466020b4100c0400308804e030300040340800035540c040c441c007050712a007210b082001c0c2c121a4000ba100c990501740d08450440c50703000081c88080254030840c03800c1040c00e44550090350310b624071400780804488040c0a003100d41030410008a008503440d00410b4692255030820703090100141494000070703c141d5181620b51601183c0d1505481b590f0b008681c44000e070f520f20048501c1403850911142024000c005540301d0f01d0b01d030704412040c0d0040c9560305260114000240a0003e80340084400507403000348800c40c00003404401e081c464518600d0b000b0002d106141e80d40c001641c0703034001d460f60340703002e06000c0000600203207074040c5480d0b00c8041c44c1003034581040620403079008c4072000e03c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 290136663 1250 290135413 290135423
    0xa0215061302030c210901060918060f110309010b0a0905090622170403140f07050d06060503011406090c0301150e011206060e040e03210601021203100627171009 71
    0x5c28031415030428007500c005041d00c008140720511100610002582c0390b103002a11031943e40c5440c1c00918115009101040e9614103d0380e00c85c1091441c41e0300905800482d14416140d10400066000c59400f5084c880c040d018080d00c0a996144030550401c100030380c1444410068280703140001c0d00a04488030fa018116400b01c0e00d8070304610300311030751449442001d40e8642c096048004110381c006400000d6401c03c0e1900c2c0c60781e5030300b460141e020300740c00d400055065003403c01c0c0c00c030741a2003413404a100b007204075101c8000740c4400380e00812500c02805407400c4081c02c01c600d2280603000d158181c148600601d440d01118860030a10021100141c01540004003039220050140c909030040c610300091417000355151000035030740302d060700034012002d580314011074002501d80d0780203110028002c0d480c244815540d20384042480d100b0036090140201081490300c003610b00760414014a404c8001ca0220703544010b040228503a40329644502011803441514140000e00c03030a401941c24080c424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 290137913 1250 290136663 290136727
    0xc061b080a0201050a0608031305010e0d0c1d070804030c0f02010512070201090620040e06031203010611060708060d022107120b070804080d1509020a050a0215061302030c 75
    0x240710b0346006c4e198103502142c000d030f006012320003200c20280c1c103910440310242481c4500340102d501060600c160814041d0452407002030000c1d8800d9038004488619440c400b41002c10b80c0c40c0e1800307843e1044107840140010700c40280420000d02c07031045003001203005040540c2032441110b255968800e0880b20100141d4450402c041042803601541d11084a82c450700f441f035940c0c0743c440044901851141504032500d0002103080c1d83c82c10f104000d48090004441a82c943c0c591101a00d002c5143c103e134015403150031b000403071891003214900d000d118010000c3e03c404c0380039020080c000002c0080b44c011058406803000100c2e104222000c01003102122284140710141000750300181e0062841080c001c41404100c009484641107031160030804000007100001d044c04440c1b06c40c0990010440140300090107100c1c2900030001c2c0458401cbe0390b0032900c0f02810390b02070340c440700c4c01507a6494000040c00c0c48211030b05265000385600c101c240d81840c2c1015007601e118800080d992581654803032403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 290139163 1250 290137913 290137921
    0x904110403030309171903050a11040b1803010b0105090f040b0306150a1d040201110a150209120c01051b010b030a0c03031407260d05040602040603180c061b080a020105 74
    0x40d01c800400c50919198800e0f00348075940aa070000c42071806c00f05400c0556a40c00103003010f001e46d00c609000001141c03410384031030311a500b480c0301d5031082e050159007600440c0c600e0350b50301d414000e4000790711040c0c1d06c0d40c1c103154840091005501222808a5000e91204a81d010b1514100f159a104000c44c5400780d02180240b02030240d070952640080700d01f180b44031001907c0c07640500300941c1042c3e080c82c106180c0c03004062003d00306903200c48001c04450410101c486501d165030040c0c403000c2021983c001000c1c00e000251507956002d43c0401e0f021480c10b1181d820840504601941c0300c1030364600100d2202c000100003810042485400c99080c00400824400e0641c40341c44404c0c44561a43c20720303d42145074072502c0d4910000003245020700d18203160f18a40d00e0321742056038003401a9503800d20407820300b850811f020350032502510700040c0c03038507803040c0072500805070b020503690b0000c074071729802400e0100850751180501140c81005040c0e40e4032100091103040280070980640c1d00004080c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 290140413 1250 290139163 290139173
    0x20c010f090503070611100524030c0d080d0b031522032f1e061f031415090703022e030b130c050403050d050c060c0904110403030309 59
    0x50034001100410102240500c20350700c00042c50810341d002410700c5658105420303145484c000602d00440e508506100600050303850f01f9642d200001d09045600809035010014035654045c0c0085150f4001c142065210100703000c800101280301c0b40780c00100741542c911000c0707464004001405240307006402c0800040c0000010851283c84880d14a000c001c1c45586000300f081070b200c40043c404520940100500318400046022040207880640d601980300360351400c00110282c80c4001c3d18054a0005625807401c1c403030500c14182c0400214010701c0c116103411011b0314880b50603d2542c86070706d2200c40d007804280b4040d81324101c0103004200044c11407041c80400481000048450822000c8003500c06000134402c152103040c514000445c8400350300020a011b42d102c3d01004900e140801c050b00840d848002801664002d9080751b84904400c0801c41d0588102e80c0c906146030402382c00f03d05e441501d10000c00000b94014400314003080a1503100540340e0007648202c01203a613901d401400c001e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 290141663 1250 290140413 290140427
    0x521010e0901090203060411040b0a1403010c0f021209040f05040b09070603050c0d0b0a0e100e0c0910080a0f05160206130201050405101205090c01120e2812020c01 72
    0x610038020f01c004922640402e80d1003c0141c001010141081003607040c523120b5030700445907640300500c2c202c41c1d56910421f41a0204a20250300c2c0a0750030110704c1a0240d010b182200180c000c1940140712000301002c640c2390b15044041c0f03280d40a6120243c038540716169001d02405075008820200c05410510f10f5103103800c40c50303802030007854203000801003601d00c440141d807820400c00304007049450114001454083d2107400c040260b480810a1002c500c40728030b102800d4929882c0c0300081501c508042d05880e01600859a0307226001400c040101031280340180e4014400417404908401454080313002d8035400c0301e60101c115102013040c4500ca50401545030012007000c0b419800780b2541d00000c0c80380c85a0f004503800340e075803103042c002c02d644a080034043d540151001001075051421191361103c11044c03003d8005032284074541c1000d54541710301c041c82c06510700103151401204a0707520168401c1c0c088145200c81a00c00b00f00071506995200c2480780b03043c2d02410702d010308500054940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 290142913 1250 290141663 290141671
    0x81c0c08130527010e0406020c06150112090206040303141201060c1703040201090b09151305090702030408300a030b0103060f0b0301030204050916120203071d070e010521010e 77
    0x1051010314043d4030500c11401031410345a0501d00802d03035554506041c0c0c003a10420625844030704c64001080918204004180b181500036079961000d208003c00510542e45200006540201c0401c41080040d010b6002c91001582240860f810080500d043c01d07808202641301c1c102140c0ca1101c15010000400754403219103580032592420f5040036000242849214003a055411000040c900c07003a660f1580407000084101c3c2d0300d181c0c1d44110040d000500c2c400b80c4661030160b0f00403404200c2540c0044140c2d4160307403444c4002c0000464240802c55041d1007001c02d1350341c41098400d0041300000c013038014060443d060300c0220b002400540010100c40042e40074201c1404003032414800c842a020440341181c3d0100c50118047c0ca43c0303601c82d07040200600310660348441e007220004051009203a60f50861340200c0503549041d54542043e60742c1c01503d200074140b00d1818001801c42401110b661004000c107240050404507840e205446402003601c50403010703492100108081c8060540c90703980 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 290144163 1250 290142913 290142949
    0x15062103091f05091306090903050c07240302070606120305120609161d060301030b071205042a0f060527030a0209150907050703031401081c0c081305 66
    0x80341c0302c00c030000d1141c000c80d0111846401e903d40680015031150700b145000d0044d02104100440403890040c2096005148000e00b902540100140031910f07070340c0c6940c404404041c1024081c500c01d0080b00258002e40d011541d859031403202003543e0300311503640c2000f00e129860710755494003900248804504000c0040380b20350b44000c200800f4803980c20710960729404505114550404100780e05d50f44d5644007036200d8211002000010503c41c1c00501140110001e49450f840b841c201d80810054490844025100c200c481d0541038007082421704250911500e5200e540f0311503212a0610041045603001800007200070482c600c3c80841400409540304500011000132600c5030702194982c0c1c02030784042c0c45034101000041201070210000d04441e60010645002e6150100e130181c101d8000b07942c1540024500355801c0c0b43c0f540c200a6050503601c1410081c85c122001c10340f08203004a40040c0581004941200d00f0005900783d406002503074201d0820200d43c40c14581880040c204c07100348202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 290145413 1250 290144163 290144209
    0x812060a030327090c030209102f010b0415150903050a11060408010207200118050f060c07080a2109140d1401061e06021506210309 58
    0x100190304540110f0710342400c4005250040b050b0a002200c5410035030240c2c80d2142030130100200b00d0b515500901040304119410702e40441120000c0f5041914543c445100140742d0901da40c1c1f00214a031007109548100001041441c01c41d808101a03505004a44095a21203041030080221218800004402910f0f00e610380c2403540d1250f0350745101c10140649110b1a000d9500c11940303d00080790701400c2000d000b075580b0280c500c2c201103c0403801b00500036400002500040c10341c401d00c0154100102c41ea06804c215040c14208980a820000d007594441000c10480d0030b00d42c010300601000b40b01ea0700c043c0498500b14188900450311801a2800580382201c0c40000a50402c1d5240c0030303a050490090141c000820108010380046280030704986007028040e01c1c0342c9415001941034885a4108180c1c1a00c00d12025501003070381d01402c00560081c11400901240e410a240c3d404040246507030b100076607070044016412107402150364280c00028031401c0030b080000d1030388084001c4142110b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 290146663 1250 290145413 290145419
    0x4140603010b03191b03080408150a020306180907121b0801140f19020d050604060f0501050f1806030103031706011d0609011101060b1809060d1e060204030812060a 72
    0x29400d191101000740704403c0b81401c5001541043c8440f1701a5900c024155950ba80700c40c507290b40c542044080c044014481e00000d10391b81468000e49004e05030240030603d04001c64400c804180a00030025032141c451800d000640c9640418028082800f414078004040baa501c0201c440101e40d42100185a0600080c010036100700b10080394021000030944089803500d241503071a406011515070300542c000702c0c1400c4c01c801d41c0e41c010341c05184121420041035544040d040f05c0800c032071292501040c014820071001d601c8420040004c10183d1404003940c1c031802c0700003030361a0800e030002d400184501702c3c44040e01007021911608102c09003030440c15170f60f100320f01d045845c00203500180585008148486980d014006580742020390380004d21056807504030390032042e00409402da1138034010b200c5c46200c13824002d1206015610141c5034410720070260312100d04010304202d82d40ea8021140e1001008180a4409003025504c5428010340c0c2c0c444448910031449405029030b0b101e074401700410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 290147913 1250 290146663 290146693
    0x21f1e020a082205100c021e07090c05070501060602070305070f050307090e0c031c0207060503150103020702010c050a1511161103030c07150807020d0e010e04060504140603010b03 79
    0x100c1d9203c10094000e1202121a4000d107503940200c00c0002c15500c141c0b0481c40070982150418008a82103a00710b4269444050340d41c400014070481010a94000c61001d10824090b0303000103070591444d007007444c600140c1d076442034211402c2e544082c2c0141c200c080180100074040c080e170002001440d940d2070b00301d41402d00003034407a5014851842000e0b52030fa602561290309101c0301030204801025591028000584007680c0342c2c00001c0c2c080103029460003c0340c0c02d802602581c0c001c0e1050011104212064401500250301c602800c1e4144040501380c840010420056001990710074041c0c0c900c0920030b8101601540c0310b0907900e010301c20f8103000340355900005480303105100350048076500039840040007190951240420600c250b000f0428041490311a28507644506003040d5a0310300a079403183c1c003c0b07840326030a450040c00540c608080001700c0d07203d043d1b400c00892000300002010742e950340024003181d030321040c4a444001c0709001c0082501d428821000154015000350416080349900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 290149163 1250 290147913 290147927
    0x4091803120510120b0f0c0f0d0b01210204081207030f031104050d080910030b01090312021e0c010e100c0305070f08030103080c06070912080307021f1e020a 69
    0x280100c1c15a1100001e1001d840c1c4880b41c0c0003000c55500d0030124040900381061100021100707040700c0040c200c049100c0f400d001c004c5843ca860784481282c14941e000ca54030000e0400440450f04000858014a80000c2d50041c2080120501c020069407039250406881c10200003005030b0071121001e00c2144042134114000104070301e030324580003903c6015262003c5460040780c00040d0086002e801d030908000d420001000c2016046900702b811101a0404500352880002401d0014501d0300003000018a00710f54100004081c0c01076030921120101ea66103600d00b148110106036200a540728032658000c5006804000b09807003001120940e01806031031a20600402030400000041c01810311117540e40b00d01c001076000c01d400b80e41c0e581d00d0038000410b0b0059034144e48140030304408075800501981c4110101e468403642d003400f0f1955611425601d03040145800c066000c0d20351a80c503000351038070a400c001d802c10701c40083c408051122140d201804200503450032403040001810082c1c001c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 290150413 1250 290149163 290149187
    0x61401050316172b0813200d060c020a06050c07020a15031103070e0111010c0f11030c030301030c03150e070b0904020c1c1701080a060209010909090305091f170a090804090204091803 80
    0x1080c1e0380e0039180040480c0c50888e4040001d40210f01d001050720030b99601103400c2d14018091181844130f5115040074100c0751142d00c600940c401e110f41003c12031038195614030100302e241400d0020b0608034818540b00b40d94412a61440011070340d11a4104035a005581150760b84041d200811540f81521006441d54944180003401e200414881c2508084104119a4141081002c2d030ba100d5075a4602544044c07081e0104a80300440250115000c00c202e106a800c1d6007010380043c0881441c14090014031ba000d420400d4005408005264241e0001c102c3c0c800005600540070090545500c0300034003241c200240c2c6161407042d40d00402083c1000621250044d130403440040e074800d002401601c0c40c05099010a040e0303418045000e080c550013001408007050705460b55500c1280400009003401010640b1101140c490b1140fa0620448418525030010350030170000340481d15500d840c40c02c0e420a40c8075007401c0e80c0000c2c0503c01c0050078011940580f400c004001e066450b155000342c1400c0c0c00311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 290151663 1250 290150413 290150453
    0xf020607110c0d060203061203071106211521070302130e070b04090c03050115080901060f1e050d05120a1803061401050316172b0813 59
    0x10541c0345101c0801d218228610780c00a0981040c8481850450041d40003140c806100f8041039030b000c51100f201000301d13008550710a003488000c2d1804000c101030f80e04111400c081603401c0c000c6818040310800f1a40d0300804803000d0b281d045545640801866034023488e08008207484418a40001c800002650420750f64100c0d050400e0303104034406007009101c0e81002d00ba203807003a00d00004602850380c004100760b45112000f846000810101501620020302c21450145040326440480d580720315030311508500e5000c0040748090380e40803a484a2101508050000c00c00d125100014050008102c0000c00303055516042e00c0c910f64850a403140c40f140103041e01110001011aa0b152203003070b2000039002c40c41c40349070305252a0b090003002401c40c688411a04080c0b81c00105952400141c9601c4e81408240224006802c1c100b11740802c1d04c180012002c0c9100f25141c1d1103405020500f0050b9028021401e101c0c1c002d0402002401c0d0b040180c01d052000010609502c0410a00c0c0c82c41c07018070a4031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 290152913 1250 290151663 290151677
    0xd031103070605131a040b06060a0e03030c0c040f05010b071b03021c020102060a061401110307061a031c1e020a0f080c0705040e0a1e0b01030b0103120f020607 70
    0x2000a180c25803040700001840c2910740010841031409a1041204140c041e80d640540e0aa101003501d05682094501414085c40d00380003c1c80d40c0741c404000e010344032041c80d0240c0030411041c003080c6140c10440f01c01d0740e10740004500b421103081a210307003a168040c140d014016941340c498111501e00c140b5201800c003114171100c0365281e202e100c52003001164003810301c40039551042c802c0300501d03121440c01c0b03005008043c0032400c0c0803454041c00c026503400a075800c4240c1841c00040d503098004e040d05004038041404000b01050180c410b81103c481c0d82e1182c40b000c2d050b031001701400d041c0c04560981c880007903010346840d566800191a02040d02000d0210441040031909a10703080700705000600041c52038102e40704100c5c03450064003402d444d00003120703000c03611b90b0200401d0b598210350701010355002100c1e00d40030900c98101511214030751501d0007403450072625140b0b01100240c1081c0e0712080307030700010000c000c2040340d041882c100a00d08032200311460100251228409440c0308104100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 290154163 1250 290152913 290152937
    0x62f0a0c02060705060901020d05070809060f0a0624020c030303010308030c0714011a03010b0102070e04080f091c02090a020a1d04230405071203090303031a12010b09060a050d03 78
    0x5040110f603c0c0f290084221900c0e860880c001c58041d502901480310110f04010200b64514001d180304c2d0301030451032011700f403503a65241100c482501c0c01001c0d02041034449200180740411644d10b103982181d0400d2a4810900108001e40380103c01c03108075010380d004000400102d8500c00c2980d40107828403101550b110980e044c4120101d900e003401c241c0552070b010f03a120a8401c0700c0c180c12110307103040d0024021131514500598079082c403441025001408400090b002580c810b00614507000e00c0141c513420452a030307010480c800c5000705602000c1600038400815844d0046810b07a20041401042d49000c1d00340d04004c08401c030b0007048018a543e00d1500030030310b41d80d03a006001a042c4410307100301c640d1103e10021070806c001b55815605401043d1001c04c0700142000040e2507503815489002a451950b94114010200c80040c0d100b401d0350640c00d21880d940b80c0f40b03184800d080c040008a030b00322101040103020200a00458801d61040000f0003054032034400b1034030f140d50141450808860 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 290155413 1250 290154163 290154169
    0x312030711101404061a0607170c01050103050610150906180e0c0d060906050619030b030d0302031e01031515030c030b16030c0507110d02030604062f0a0c02 69
    0x2010b149501e0740c074100b1414141c5101c90307100040c070882c0107030340c180800901d5100c2c2c500640b80000c0119004001000680c0105203004141e00161260341e05052070701c5444810f0600b114401e8100711680c2e00884103000c05100380c4a00c10020300030001d80528010158000074003060194400c550a01c60f04407440002031031502e0f2200000d0611100d0700340c862038424240400c42e48011445003046180c40008a04407200f0b120b0f1100391403020b01050300d4042d140304a0f1007400c08082800c8100740d10f0301c40c0d41005840c1849001031010b10743d00c015031a400c040781c48603d611030603000c0f8081070842e030004001140d241c40c5c180c00007500c0c81600048401605617a05007000040d040940405283c00b000008c00c000c943d280f07849803e0718030601604a4a0000403000da45904513000001403007801804041a00310f51800048080100010030b40704056002c6414001c084170244c0d4600e65843e00140c004040c001940412060080c500280c1201c12840304100d001d240088802c01902c48d1540742191 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 290156663 1250 290155413 290155423
    0xb070801080d0c1a011401090b09030c120a060905010203100915180f0614030606031501140d05010e0c030607050a080103170f07080d0f021207031e0903030e06060312030711 76
    0x130100300c0c02c80c0384c0e076071580d40f003401c200c44142c0580d001415001c000a01c1441c0d06060320342c1c1480040c0074042030f60307610042290741c80d0308244240c064011421810005640c2e8070074015810311610001d41c5a10b0080314002504051f503212a6030903051680c8040d41c0078a00c00c00b40d003900d80a00440034403061104081000b8016014154016881c1504c007080500d001420001030380c4040f42102d40503a42c01e810700d61070720305452205204888100043c02000c000c42c0061400c203001802440e481c5070380e0b0302e441c3c0c291010500510020303003044104c800317039050a00c070f020ba00081c00d00340180382220104000385500750510024140c100d8410103204202403c80841d404ca500c3c01c0386682e180c00690604a000d507000242e00441245807502640c0034851500a88040040e01c220b15400e0b691140e400390041c005a03401c500041e640040410a40c544910911248901a0b640011040504003100303150a0011303001900c40c0d40540f5546000920120403250f000d0f060b494088101000d8546142c500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 290157913 1250 290156663 290156693
    0x30507180f15030e0a060b030309090106050706050105040c0e13110a0906020c03160509090111040b090f09060a1a042402061810090206040308070305070b070801080d0c 74
    0x9000c0c00200007400311008000304240c5040c0d001803030b5500c12982064003144d803a10801c19640d0081401c00c00410759940c0010510305018050724a4104d001c00007175041c01c001d8120742c000c504d01040000c1840142cbc0300f0301e40505402d0f54100103030402d0410150849040d048501d11558030603002a92800e941e4008112404909440d40d40f0340c9420b00c0003130180132903409440014846c51038035a60307030328000410717089a0b04481000d0903060b0a1409219a1190003000003440d0f648507903092100c1e811301c0000b44000c010001c040e03911101e0203000c10854200031240f9034030810f100d40c140400c030380d6100d03408001c841005843c00c0d0304084089004500c0e004952113500c000c00800361855101901c1d1a011107808034a5003500c1340d035030325041c025405130b0101d43c4009899016021400e13002c00e1030ba0200d074809000815403800c040e6a0396070740e6582e900443d02200042c0c0701150020801130401c401c1d5402126030b00b0040743c5981888980c607621070080d240d41c0304024075039141405004002d2620010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 290159163 1250 290157913 290157947
    0x5031504020d050f1801090b0c071a040c051e0604050409150516090b0304120509040603080706020703020c06040b120a0e0609011a010504060813080906031e0109020406020d030507 79
    0x2040c5030444240780c80c2d031801c44006030a03046452605e882080188501842c4542c0030a1a900710b071a0001c3d0800e441c2c0100340111011400c00103006100c003800f8000c2ca01c101d2062003542a43c5044c6028001c88071101800c10050444400ba2444c280d5201420b5409980c41914001000a03617802c0c80200405c8000f081e03031030140f40100740013117800880340007040f8126985035016410740d560080803441c8000c42e030103480c406c0000701d288200e6220f60014403148000401c003180729616622150a2640704c2a81203440070350005d00102050303010b1021800302e50048507864203281c644140381c0058441c1100c0c40c84455003100c00102050b0031035004c10300c01030460085502c03501c0c007040c219000b002c4a103080d081c03003449895059103540c441d030112001d941c8255211260382d1164800e0451001c20032900b02c4450400740310900e0b464651b080514440c079100d0b02d0300714440d082c0800b07800f104170041c1c100f2418140100401e10070103800103400c3c400703101c1e1031600040036520303010300703c0d25070a01401c5841 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 290160413 1250 290159163 290159171
    0xb06030c04050906060309031603030e0f10270b0901020f0c0309030c0303090d170729060d1a070c0203011107020301150e07051e0d0204081b0105031504020d 69
    0x119000c20400035100755002034a50703000c0e503261001001068001290110340b50f42c0100441c620680d01c9da0600c0b458a842410049400f42d0100d040740c0c1407104899204103103512508034041c1a101d035020304100000d90000710b02c04c0d1504070944801c01d030701c5a035015004013414800b0401d1765009604032081c004c01c0351130040c3c54504401241d51070782d00c41c01d0818443d200e04c61500c14107150210480b046020001c181003011645580c1e00b403000c440c0022200341a0740180b10900201e800b100040c9020740c42403a40d0070104031100022040602d010700384601480b030082c0d800c40040d07a030941c7d45501103884180d00215507a4420b08845880040300000d40550a1681d90913050043c0030140c80058402c40080c04010103c0700c0c8481801058400c103a50401440049290240540014104d20280c2c002140246180c6681542d595220700d660001d88e50740020300f000391340402d000b4240c035000c40c00d4020b0101c1010070002045800040d1028030140f42c4d2411803a0a6641c0394100d40c2100d1386002c040c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 290161663 1250 290160413 290160421
    0xc03030712050a1e0c05040506280f0c0312091a090d03020304020f0f01050c15010501320f0909010f0611030f120402042a110f060402060a02010b0603 66
    0x20442125003103112015410300d4080f506182940c0103012005021402000b0f0320010540c103d009001c0c6503407a203040c80820080803442c0d85030b81c801840c4401e049601c82c0550102684c8110003118901030300e00401c10710041c4110388507440b11901400540524002064035080304d1800300070001804000c000060500e003190030340740b4081c0d400c0e118503440416140c03a000f02030b01c1034042c3c2c442128000d600001c1060005664a02410450303820501071502ea41030203100c828161170110b03510441c030240544c02c00104955a8852086010204c1d903511035022201000c2c4081e200492503c80240058070200c2c00107400003c400684030007400041140115580d102c803032080d0082c26014080010701014030b51112290000215030000781c400740c282c0e103050701a0090f01e4240b000904120390041c1c45806071650780030280380488006c103002c004c082c002680d44c04040c168110142c0c2c0301090b600f190b401c00301c0e10320020840503485034050b03c3e45903690040d8401280100080c40d092940030710080144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 290162913 1250 290161663 290161667
    0x112140f1603021e21040506091b01080a1a06040306150b0702060d09060b0a080309040f0524040e150403090e010e220c082401030c05150c030307 64
    0x216000d0302010900d010140c1d40c0440803800d074131603411080551529040d158044c41d0a1400801280404804881d0240b411040502c0001015501500c0300d034070140030301c041803006116420410460700c291000107041e890029000e07820041c0072803090340d91a0b107055504150003117080039034140186210350b150740301e01e820300081501d0b00180403035174500d110104185444004032150f2940080075203040c003111841c00005001005801ca404a0702c602c1076490f523445035061440942001d4002d19241c01e0280103100440d0804a218032081381040c1c14003580c0c01c0110b0300c481c407009000541e151582031031008200506007045603110103100d9940c65000582a070039806004520a42e01d580350700780c5d22048148010320070b000b010082d52603107000c1030701c0100c0d9070010781e040760840d00fa140d4078000f10f1321aa4030711251503000c1c003010b07040b540340c0120401108114141a030b0318540401455411516042820b41c168002e45004000103101c8003a503481101c107540e0319115480c21a9513918100c0c1300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 290164163 1250 290162913 290162941
    0x10f0b03090a0b181c051b01090c0f050316031101030c0e031903020f030a021b1f082e1202120106060e090a050912160203060c07120804050c011214 65
    0x14130f40180642c01128040b1a0010768824400c0c41540c0d039141003441c410b02030075000c001041000c07030719907030750b04124001542243d003040246559148e400d2135501d05800d06051070160b5161403900c005101e014000580d0201400064590a1800190000030310750301f0380c0c0006d07050900345d900d4070401c0c0c040d404d11a284140310003801e20a0b42901e1903155621f00041c1c1d82e001e90280c0304090303007225154600305c800385411014103900040110084881c4030740c041040d0406c260034000003448900c200000d030921072523441c1704a48011183c010098800c80d681150b4911405500400d8400c02046410340d981c0050140b8150905402007082c140d46440c00f6008103030300c06040d401105110001a10f055280c42550301c00c03134090f0050012400c0320140d804403a44039040811002407804d10203400340e01d04010481c460f100101c001540c8688a0502104203c5c15000000030041302508000016070301084251028100782020f24a4410000c0350030042c0c0407046920380c55504c07103800c01507404c0318040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 290165413 1250 290164163 290164201
    0xf0906070c030302070806250c02180a0e0c0d0b0a0b120a031403040506060d060e030c0609010b0609010c030e03010207080d050403030c09050f061305091608010e010f0b03090a0b 78
    0xb1208260707601c41b5007580318030007151140b9a010143c2e513aa141d045e840c1525034810001407800101c028015400665222404d540981c1c0c558004c40400c0034401140c81034070301c103000103002081d8a899071000108082010785005102010503804500502005c0d001548240c10003440071041e401d00200240d6680400b0720203400050b01c962038146060200e50031a80907641210140400b43d581d18244940f5410602c0f049541c02d0396103491000314401400942500c88551018020070305000d01c0030303401d507192400460b21a02d03042020045507a080300c0e000251503450b081448100c00c01300e0009009020380000509480c90002d14190249021b44c029407055100b41c03810021351802e8002116a03400c140145500001e1103542d41403607190010182c103171110812103562420752a100400c569100584010392508581c1c0740c1c00c0f01168100410760701410000400c0411980360041c1c06041d07140174821009121000008210001010711540350340340d0700502000c0860401a50318164440310303403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 290166663 1250 290165413 290165417
    0x507060c030e0a0b04030803190501060201090c0f260a120c0b0901110d241e060e060304080c0a0b0103030e032103070503060d0507081006060c05120f0906070c0303 72
    0x204000c02c80c40c1148126083d0303030880c0001030034582155121402a8405480703840001900c18004001309814020b00b0b010b01402e9001150b42c5c0080d140107130f848901c9411040c6013001404041c841c0c00300f1f0004412171102d42c460064204d1aa1081060074a441a40040c0030201d00c01d00c1142c40980103050700c40b46038410b6009042540d40c4200b1242211031030100301d0416202002080c402c00069081501c1e401020740c1030a89183d45554908460f00031a0b201c04107502030140501111940d00280100608403420040404082c04000850700d20005000030843c480215040e100e040b4104141090f5640c0205502e280e56141d08024109031492440e035442413040002c03402581b0707804550700a0541400c0d5100c0c0c113640700c0050a0319180c00c01054a60440b40801d020004980e0030002c9600518000000c0c0a02c1c42500307448405803030f00f6420403420700c0700081318880010000104903106032201400b20341c551a00c16500081ca200710004140e00990103c0c4072024090034a6541c0d0499200c2c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 290167913 1250 290166663 290166677
    0x7080408031b01021207080a0204231206090627060f040606150c0f050321100501080f072012040e0f0c0301090506010e0409060207030e0114250507060c03 68
    0xb2509401e034415540b803c030810301588003140c0050301480003246c120b5864800503040a8441c82c450b0f0082c4400e000c444080e004049514002e414076000700212003030b111018203403901c0c1028850f6500c0001514a68280c0c5510040307540071020307401d489000742202c1042d12480c0c14419210f2120080c00e540c1910b105241210000e1303245d9010107190001c017095220001212030390b403508416081c11a00c00d0352907000c01c008079800317211400d00600041422814500850078030108411039082183c0005040c007200c1010f00941002c600b0101e640405ea0b498009925280c003550280305000d0100c0310615842600600251000d0302d80c09813085d81d403040f40380e10640c0e442e81e140908008041d0b807094416036080006015109442e004180e1102040c101030301c1c1e4110003000300f01159508042642c8c45030340411881d08056000f04040a0040b091800920444c1c50f1031850328103200c0e501481c012210f10300c00305130f001d0b4a8080c60000300758018068682e82660f500c000b034440344446a044000500f1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 290169163 1250 290167913 290167957
    0x31202210601021f02031305030a27030312050405010b15120903040620010603050304090f0e010b0f0f0301091202010501080607090f03060b04140c0a020d1b02150708040803 76
    0xc0011303034803802c2c5050602c0c01c1440c400d4041d140000d6201410a400e100440928000458804c100401c00303d00250340b400c0800155803000c01c4000c80c00000c9800c83c0400250820110350700800e2000c080b51059000a82c0e0340392482c00500402d481d00c0c1c03142d0808030590074507114000340b2000d0000e00c549440034403034540d241d881c00ea44070321a03400350380046008240701303241c150349001002c0d00100b00c4000000da00307030711398030b5103851500715a008482031900c0794000620760703400e0b02411001958400080c00681c9042001072446084074280328014541e1120050b00d0350380c00d4000184458120b40303c0310b4849400f03007009011b4502402081843e21036100070410040c40303041510100c5041d00c3c04e8a041c01d06507a260b401400009034103640c42610380110070742044800030780380d00400164940559415092001908140201d501d00702440140041681e4001204138240c1180398120b9419030020a41c0750403e6441c014920054650751000c10007142c1c074280000140080c106500c03902c614045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 290170413 1250 290169163 290169167
    0x6251a011503090b04080c0a1e02100c020f090604090f110109050a0b030a020f040b0a031506030603080409090623041a060d03080604020412050c1302030103050d0507031202210601 79
    0x289080c0014120713182100041d011888903400b801c0060b03002025200d41004031340703801400080d400d4406505050900d43c0004500d8101243c0009041030b05250340c0c1415039070002188121040402c5000340040e1002440c0e698031076200c0b411483d48150045481200cbe4205800700385000e15842d03010a03500c1d00c0110790381c1303046600f031002c030361481c0482c0b440d40d618001a100a500302c6030b501220798200f40000301d10210b041c0003501c803040c02c3e50f400007490f18860040388900040c96108200303042c68440c0a1001c98105022034058441401002c01e4004132860400001c1901c840b40100c0c2c1c0003020000544102d0303c40000d40660b000300003101c030b625561038141007481015500a42c0c86a000f103c8180024080c00c082c0e544040d000f040141800da940c0c4220304640e04004d4111050b811001032682c044c94203001c50b0700011143c8804504640c110b6403280c2c0d0b2140041c6c46070f011703c84085981c2d01050301c1341c803401c0d40f80404c081082d074982072a228010601c020107488588200d03010400142154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 290171663 1250 290170413 290170421
    0xe1e040b030715080a11040302030307060c090e0c090a0e0c220509041a061c030c030924120203040f0f0c0b070605010608091501052205150a0b040506251a011503 71
    0x230303400070060352410001c2d07610507004011148121085c003220f9400025030904e03514405d8440e00d54a0701a47d0340740c035004100103500d1070a80000b07020300c0c81d0b1420710004c1d00010b81520340d60700c20300d10710700b102d104100581080d82c0c289911666202704c010040104010b003100050039110031141c806101c03a15281c0c208086000328019052194240060100c04070f031181c803100780e1040c00703410b00c1c0c80c410740c4a0000400300c15030950828541800d010781c840304168802c9680d41524880c91046003541096903604a414040d01d8004d403009007032205240900210b00e40d0b80b00200b46802d4000d9860245d442c084010304000d21500d404140b884000404451022483c145002141c00790303412b00d0780c204010800038a10084c8085e814008030075951000c1d14107486194060000005c2d11100c074021b6604100403915141c1010400003c24001044141c0b100d006a41113103019096900481507001c00138120b102ca00c20300540007030001200d5009407824040e009068403210742c410005804080c0080d401d407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 290172913 1250 290171663 290171669
    0xc1101021602010804020f0a08061f051503180a0c032009220605090c040506011407060b0105070812060109060e03120703180609060e1e040b030715080a1104 69
    0x714800c000008015849699000d900600c020003c4040403600c001040c251a01904a800075500200501101201c3e100e11082c040c102c040300380d00c83e5400c1401040300480908604121500b001c004241a007001c41c1a03038608160a8040314240c15540c00d082501003014401643c28104820404002c030b540a02401a0a0780c0036200079004d0301c4d000d858107058122212500e0072440f25298820004e40903009181c003038610200140b400709001010441103c0e03001e0a018103001000a90004038500c0c50705033388405420000016000c01240c0040c1c0e2103100b040e40040104100141c0742c028502d04500301401054203a0312103070856120101a82e0404140c1e445039030560080320710003804075024004160b0280302c1d10f814401c40031110010408100140c0120700450341e50001413008551204116820700c40849000c00b2190b08100c400390800e4100c421180030780d032039150090f550f4404010305801001410700707040c18840c07071000c0100700c40030a032025020a0b00700507540b801c0703511000643d029 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 290174163 1250 290172913 290172937
    0x90f040f0e061608160f0c0302030d020f07060f06060f0503090c0d230f03091c020415081b0f010305060102120a0906080907030809060d140a020903061303020d050901210c110102 78
    0x4c83c44445041d140c00040c5e000480c00c43c401003004c440440f4bc40d0000c0c0c031504594035452030b00d406007460401d0995003c07980c69045246130102c1000030310f0b48004880c52500050174001e41d292900e007829820000c00d0070742142c0000441d8100380c20490034403100c08c40f011401c03e02c100404040c1c018030361038800c1040d18075007560003070003220b0031484c2c01c00f16102409080f00f04e61070303011099400304044e94240c12025640355098541041003003c01c1c45150812038009101c00720710b002080c00031700d0200f580385a090405540341d00196490b4000c1020703580407012300c0c20560300c036140c2d40700c001c0c01c0f407005003d0100010071403000300d0f8036040e00280c8001907070781c0306840270b05240c0c186040c0f0485810900450f14070a03141c20031002e444084809543c060303404c0500c05a6582030006c141440c1400140c1180c2e0300041500600001c80d07404507140400010610b01180c1d00d50000c00100c0b8105401120590b41615100031804c0002850307000c020301c6280d60f01c0e0a080000a186524205d014104985a07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 290175413 1250 290174163 290174177
    0x26010501030c090e0f0d0201140f0c03040f111e010306060e0d2d060b100c02130b120601090b0a0816090c030609020309010c08010803090f040f0e06160816 68
    0x200300c0d44281c21518110f588801100e12005490005615010441d21b0300000751759500716501d03102c04e010f5030b0b071644100d0f01c0302410094205004400d8441c88001c101074403441c98903500c9401c008480c01d001d00c00c1c600080014070212040d5101c1c1410013509004103001c03c0c50101c00044041c021018410001c80003001041d900c1e40c1c0307841e4105040e981e40c04500450040c0c0071245043c90b1041700001c5200d00034800065040b0555061081c60b4462400c082d0a001d286103103000140d60383d80d0110003222030402c001c110701c40824007140240c030204c07604681e140510000171812040c01c0d400801513601c12601202c03001e03aa404020344821500342e050303035201c2601d1028458a60560499000c24049280028941e0346c0c45a04004a800c01d60b1000c02a035100c1c0c018017803050303115031007601404040c0059460880e0150008103840c08486029008607122011400a00701c0340d801000c4021658041e2000c07854080d0022291210400c4024003017200e040100310300e11424180d1032000300d0701ea00e901e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 290176663 1250 290175413 290175419
    0x70606080106061103120a0b03060103060c090603020301050303070f0c1d0610031104031b090507080a060603020903070e0414010212090d02070302010c0b18030412020112051320040626010501030c 86
    0x4001611b005055501d1140c46820f00c00711038504000d040c0c025405040c0000d010141450002e00c4c404269000104241c0140010300c04e5a40c04000c8805e80b90b4004082103000901d440c20128016650788042002009041482c50408215010501c10f420484181c003619009003400d07402c0b07030840716003072030f0f485010311051001425210510001181d80040919035a550b0060041561004c070342d8540050158030500000400600448015090340d082c2075040801d48030200f595822507108100803040e002d40400c0600441c40841c09840c403414000350350706d005810952041a5040c0c490443c0e51003501e06810b01c1601c0801d11800b541e0303059540c441901030b1611089000ea402612034941004217080031250988104000c3c00200401402c064a07000c01340005401107084000b08244039003800c041200640408100190f07507075020840b0480040c0004e24045400036144420b41c206280441c081405220344503040924101c084d0828903105e8a07001d4242039440a20008140c031152582c14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 290177913 1250 290176663 290176687
    0x40b16020109050a06060303030b030601230406031209050310050f042405010305010507020f12031f0b03070210060b1810110106030b091c050f09060f070606080106061103 75
    0x5012806240c8008540100d140d00d9580c03d00e89402421260380e40d840030100304154142c0608165200e0443c00340c96950314103005801c00324440d40440c3e262482445450480d070b59154006006503420104041d02d100c29034402519101a07401054480d1042d039040802c0407840b8028581b254941e03244017890390b1900d40d03c64682082051820541403000c94500203c0d603503d00c00c2500031801040041541d08240380040c1c03c00701840c0c80e110213a0007200c4c94a03005a1150300b1603801a80c0c9822444400d01c10301710b040040c2410b40c029810201c00041032155055000030054903280d1030300e40c00c11031640c3d11134414104e8415090070248200b52100d5052191402403070343d05034a019400d012050b407244003a040d00715049908200c0e68603c0c07110601030042d000300100703a080c9a4141900d0308a90001c03a000e0802c1c01a464040910300c000280314400b030f00c0c0c403015520440054050b140c0c41d00891310f07241000d8a81400764487c6986450310005401e8400c614114a02e040f58010354504101003040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 290179163 1250 290177913 290177941
    0x8010b070804140114030a0903120b0a03110d02060c1f1e0b010e1002010f15050d110406030803010e15060a050a1202040803040611010506040603020a060809120d06030b0c03040b 78
    0x1140c4c0c180a031017031031001d90748400c0f002184140d10300300001604001c54500035005c103060548110860b46001d9200680c0c0d19070425245c2130300c0d000310208010b202c04000082146001d1180250000c00203d070341242190000b844528885803520140034448540300c005d400c4a001b8044c510b0800c182100ca1040c8282da94456105a981031410b02d80402c0c401d408520341c001119511030050395620900550311500d881402201c2402d018141c00c494a4540000e0b80300310003000c0605055860800404142d52300e074420030081d42c3c410000c035101c2d0ba480401c4003406500303c8920000800443c0300700c28030300d4904211071b1301c40740a1f1035040c20048440001c590306860fa601c00d00c035803942004003103001002040604020656503840200800400c0d071400d0035200090180342c041c41c00c1140610050390707500661000d8444a2401e4411a5600c0f41140d152119a00c1048500300c00082c107031444032215000801501e005080382c542c03d88605143c15080d1000302d401500d01c4274090045900f9150550b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 290180413 1250 290179163 290179199
    0x1e09091b271802060a120f0504020901050105030702150f1f0b0f0904060305070905180601050112181a0106020706050913150f0b1305040519021e0f030708010b070804 73
    0x1a10740d19142d0310390b012a5460740003d0000b00820f9071000d40c0f200300000340c05030707445404d15654144500e040076400b09030900d40c180141818000701100041086208021900c0d441c00031128065890500070300074a4a80710956000d500c0b0030030000949c070200c001060080c01c480b112040c06140161003500c60071a5000640710f036a0098076164004040f81c410450342010344504040050384c3d0500480301410000c00c40300c003400c603800c040300400190787c114140c445040440900802c0120245c0000c1036010310000004000c0082301420780303802e40302c5090300e030706840e00d42d000c480d2829141d85041c1c64038001e21510360b07801031116a040ca0f00710100d4128013103038921012080d00c1980c81304a0380e00c1c0008030350043c0c03150313400100c0d14011150307034880b440005290a40341044242014420300222109496401030340c2500085d01d040d20550208c0510922401e0000c00c43d02d070754005105d0220350f80107940342c10000b40d1850000c2190001e03030307040354410303680500082e241525040d04145199240701c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 290181663 1250 290180413 290180441
    0x1020c0f010e06040e1503010c0c0f021311182706060702010201021b0c0f04020a020d0819090f021201050c030a0f0b0a090e01050106020c0a1e09091b27 67
    0x8480040c44044400d0914003aa0006442d40d201b0020003040c542110001c01c03005042144001c644000b04103004d032001b103419010346900c0030b034050b03484114002e003401d410f05a0030715800140548900b401001040f02d05642224030b05100c4050017141c0b40c0d45400c0108602c008410749002c6812440c0160041c200c0b24810300003d814507555652403c04501104288095900401c007114500e2a19952860016000701c800314100045540003d584910392540701050200a2002c14140d141954400c400b000003290b003402038101c01c0c41c1c03400920221060483c000c00e9015070b0703082180810b00415104101030024241141c0d5054540d00242c2098140c010480d980d443e40c440058450000f8540030b03024001d004101d4403240380c01d0b42d0031030307405901031021500040841000c0b652641c0e00f142c1201c2003d4070b450a201d2105d10400b50075003069201c1a030240c0f030560000c0420400010110004e03020f1614000420742c1c9100c429100d41500e0031880d55241d4421031808000401d0703001c208440020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 290182913 1250 290181663 290181667
    0x2061905092806090506040b0601021b0d030c0c0602031e19140706050403080f15030c0f040e030706060e0106080126190b0121020607261606060501020c0f010e06 71
    0x645a0f9411904d14507001d4801c1c1e0040f5080105201c115004a50014800c1c80207002585480781204005090345004c11f100301d25036542c10091600c240e01a0400766004031580b00e40541c0c50102950b40d50001d91650400c1c018001c0e0740d081e00301c210058400304119080c0e401200d60040504560310b42402d00c01070251401031140f40003141d260701c03c10344030f1031007901e0303200c810b00b400302c1241001c0e40000c250425030f000021034104240c40114201741764000070b070b078100d0300d00c0049030008001c0d1000b940300141d10300c4046120410302035641c00c81c03000c544000031812030301d0740c07100007c8a4101c8240900d14550130103c8104184c007401058103401e03460800c0030b5402d0040c05c103d03c2c62201044030340548542400c0307001402500820300c801090310002e1590400004080e50100e04a40208040908441590141e42c01d20103c01c0d459000c01e110a144041d580c1d04041c0c00ca20801a4031100948601d45040400302d000e5000099009500e14002c01c03a00303507018408011103030200c1a9001c13681041007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 290184163 1250 290182913 290182993
    0x110f0a0512150f0301092102010e10050a27022106040311010531031803050d0905060405130f0209030a080405030f03070b0a0c031b0206190509 63
    0x918000240164080c682c04a01d000e40c80c000c001c6400c640600b890300c41d925054008000034142000a90701440701c40320703502c2c07588200384282c1c01021010f88540c3c85008441030400305081035032085114803c081020444000000c202c1807180e4a940d202c1011101302e6500200580340403580903100b43c1500c190280b001081c0f6404504200301510104c0100315501401c01d0003c03400e0041e43d40c40b24400b00c60784c0c84012411030b010343da6103114040941c0305881d00150000d0621407034069100009100325094220355030310780640c7e02c0658442041c0080c10718100441c03589002c0d01102d0441d10010058441c0500520f02c0000070b11b80703981d1401d101c950800100c5241e4074188082e411041c004d0039900d44503031800080c181000740c04040d5840a03001005000c000940d40401190040041e040001e628580754005a00820780c0c2c10340c04c66042c3c0441e03188208140c0c00981c541c0f10300b00d85503080700e400303031078541040540d041600c0c181450b13080501c83d2500b0035810045503841e03149940a10207030b020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 290185413 1250 290184163 290184187
    0x3150d0c0e06040501290304080903061008070e011203030f0b0a060c050c09010b0304030809070f030b071e051e13090204080d020613060b24040603060504110f0a05 72
    0x10030380c0c0c4103141401040042045514261098500410035501d90300c0103a01000b004002d0004d908480c40090840800800d05014032003098405480025040356100d0400311001402031100d4813451006100b20440400c00ca024400d00d54101c404041c0030010b03040c0c15039030580150010b090101000390384c40c0e10360803550b91449102801003171140c961900034401400c01600300a03078201000c2c040ca40c81d0340100b000541000403280d2050f0540741041580d26039031285802d0a0b00c1c0d602c2041702c000c5801001c820b104141000074041c07480d544030031003107149056070796030000c5c100541c034004660240704040b9505505842d0b019142c07803288642c0c5ca45841020002c90380055034024603407265000c5010701940d40d01304030b1001c8241c45400103140604d003541d00442c88000c3c1610080109460390828185510b402101c09029841b1010340300800400300120503080c0c1051282c28000303401c00d01d0024003403d20340b246440312808214081e24107044a1310318450b5500ca00100c5080003820090341080c09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 290186663 1250 290185413 290185433
    0x10b07030c12050a021002040e18030c03070b060f0d030807110304091b03200d0f0f0f09020114090303120c0403080a030b0103050703020415030504031806020a020a120803150d 77
    0x24402d43c40c1c082c0c440358041c500a18010003001d401c2443ca05c10041401619191250517501c1041102c495512001c8464260300754050010f02c0c441034031022030007100700948600d14034440c01d0155041c507160782c01c030810004040303003046002d0701103102c03007011800c190700c654141584000303e0412249029034501c80e4100301d542c1c40c080c1c1e00000d0641340808200b17560600403500154a02c48411106c00c200440f41183e500c2101c085540c1070703139114407090045100c0c0c0c000402088030488108420291002002c0c0a0200d108040340010310000002e1200221203041c1c5007100c5000c3c0056060158a5101c1c1c000003001801040c03100340709100020010322010024103014035103a4022035200000c40c0058140d600181c40e8100745401400103110381c681c00700040545080310326000c1603e40301d5040a841048088404072005046030901184803074000030009880c5109503a09442c4543c0ca00c4501d42e02210000f00402410041000caa103602c100c8110000020000340120701081d0310b9603030030f481c80e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 290187913 1250 290186663 290186693
    0xd020319110415060801150c080403110f030d0f03022d040f050a0302060d022b06061116050d110612070f0e0a050d0303060e0108010519020a0206010b07030c 69
    0x60035066819120710306190103180070070b45003101101c110909100014100241c140608948096032031080300101f4400c6201078a000e410807043d075601d80d10b90400340c051451540300d00340a22103114440f01941000038007440701e00010343d0751129060301848201d010354401c41d003030b41c000c1600c01c01c410401b600402107460200304a40b4001c0d41d0700d140814203070207000158003480c4912a02d08080002d42c640d10102c0b20250009800103a60b1010300e0113445000d440000301a044d0b13242001456003880a5a02131400d4900c41e4803000485403c100e0080d0b0340d00c4010390600300c4240d8006040001c0e00704107011403140d40c4a009805818002c08011544c50380040b8401d00c0d87c0043c920a02028a0300110b0700710189409181c0384606800380e0b00031880d036504a01c80c9a026100d0100d81e40c0c00d1520951249010340715282c0e441d00c1d696580d051503070281c00c0590703000d4040398a0940300b40012410740b0844141405980141c0a07503880c1c291510160b8110000560520046210240005101080b00012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 290189163 1250 290187913 290187923
    0x1002030c0414030d0203041e0e0f0f01090504053a03060623070602030c1e0301140603100630020306012703080901030f09050d080601050705062706040c051e0603060d020319 76
    0x14ad45403001003080c5260041c9d11900009180c6000e0101140c00802c00300042031440100d0b0141c2000d0803218101051000c3e0302c0740074048102002030685925030442c10890340b107a0780d1a40d55012624050700c85a164154441c1c5503641000f0b2400000c2d6136130061a03120010000450402c240b03440380f401c44a81108096109000c000014000c5006000f0002034510b000e680701c0d8114544a8155280340e1014042c003c288003c03104680c0082e0540550701c0d030307001d0350408880f9190500301ca42d50082d40003950b056002c00c41e410140024650602030144407480041d8807079800628646644101e41d106129850400d0b8a807200d0119042d081d004003084a445000104001084120b0007042401c024041c0c0381000750030400a00490b000284494112180c02e1002c0070841d500e00d10520550b00d0700c601500750b402840c04000c1030103c10240c00c000c40d101a1901b19402c02c000322802d034180c0b04061110351262080c000b081044c02c03c0c8580f80141c0f88044c0071605d940e0455201d0045420a020302150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 290190413 1250 290189163 290189191
    0x306090809060a0305160c0803060d060e0703151b020a1e02090405030a03061a091908060702150a1118010903060f06080f010509120c1002030c0414030d0203041e0e 72
    0x86e150003120b10003840d10414a800820b482503951010103a2001614030b500c10300c8111180b10030b010320741c0c0c40003a4200050048450f2941d0700d203480003121001903902d458151a0450400c0610603807420580681c0d8a5800381000c00319030340d46c4807141a10444a002e03140d02e2048110010703152408a280035a01a074011901c0d44407040000f03094071600d40010b08240086110810341c640c81c601981e104c0c0908803030100e02178007461010302e09a04c0940c0561b1052290005100c1e00c3e9401081f035949000c0404500310056035441c07101c4080c0d03400c143c4003e0001c0340c10480e00900307002080c94242079140c145842507000d9600c0d1102c03002d44030711402c500c440d255105004c00c0301d110200b001c984c5256a0900a0140349002003101d03891340840c0101c50301025001901554042062148000d40450b41400710746070b04000802c040340360070901500e803010074045009240e500c0d00056444080150b40d008520b400e0802c0b05800080114010951100281c1c00b00420310a0494400d40d20440c1c6402a2034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 290191663 1250 290190413 290190421
    0x907051905130614030a02090c0708160c051203040605030a0b0111070308090117090309040c27052107050f01020f06041203110a0203090f01110d0809070603020f03010306090809060a0305 82
    0x10b0060204508805c1c800d512000010300107803501c54407103134040b0900b10711301d4490340c281c100b4880503c00d0b0203455810180c60703035444080284603402c50060314000d0b200715500441c4481c4099583c4910300600c00800d106100145218241c0c0e00140c81040c018502502d02c00702000400d4544050741e041199100d038081070a1119503401281d601c444c5044503807102e0241000d140c03954892050ba200c2502558a0301008040305008640059841540b480f000704610003515091220300101d0040350720641c1e0032242440310104800c1460000c00302030028061092078001080b001c1503000a906055010f500469078a00d84144010b51241e07008420100f429841031304024100c81c3c81c4902002018010b011042030ac560020a4541c51801901c8401e41e20001000585c3c0d8010f4064600c4040d01c1540507503001a41d01c141e4a500525480c41100c0516403110000d03030aa00503d01c201c0d0000c00e050004202180d000d800105500e4002c8282514146500e404603260383d1005004801180d1518184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 290192913 1250 290191663 290191679
    0x60806010b180a210b090d09030809010203090901080a21022a030d21230601120c052a1506041401080a1a0105060d0b030c030304150206060909070519051306 69
    0x200f46d100300ba403005440c4807003034260043c00c03022450101411920011460802a9001b0000c44040c9080101100c001c0e6035100013090b580c4290000869001407200d81e10b0912024041c0d20014517422a0094407196042403180801d100484110500402500c07a0381d45498406005034841d0382c00c1c1b039982a0003400b0081200310202510620303440101e250007031103801c4403910210100d030391100050b400603c0c2ca030000101d80b00181e8500910040b407900c900300c0d00080d0400000d2220090005112a80c0c4054044c80881031421203c41c802d41e82018015007200440108003960000c0014000034114001d011040100d0074241c02003065a4004041101800240344d075140c640c2c40081c44182c115810709000c00c00b00d0107800400c0e803209840e500703188105da800340011b00412801904aa07280c954a4a6943c0d80c10a0000c0d0388000d0f000d400b0100c0c84905046a0413481007100038006d106451504060007407640c0407540240c1c079804558800714251f03941c0041c054005c1c00c41032010500e0780c100541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 290194163 1250 290192913 290192933
    0x301050108030901020a1e152301080c130e0706020a03140301150806061b06061306080d050901091d0a2414040e0109080d060806010b180a21 62
    0x5520560043c001c840d090303a130004086101a601503001c0071a2402d4008140704142d8000005140b0760311007034025904509a4003d000944c1d465240350340e03c00e03070b00700d0b00b54030201d00307001d00e4400390001e10038407000e81005030301d00a0003c1a03e00004101b1520394506007801000c0d000000142c000c110f480052646c84181107400000a00045140d5403602402c210580e950441c50b01c28045424001011940d031a801e0b40d60358400502003020700c6004200060319900d080794141d20981d807042e180c0ca95400f0354802e07107098491070001009140e103400410b4503c0d4000703803243c41c10026152000701c0c07922441442d101c1f003140204030ba007041e0700b0411114425506015548800d1000e0b40b2000581090070307211307200c125040c59406503252400d04021078054640b05201411035802d10310360004100742d4500421006008040c1040780300d440707001c10741d2a20828442c01041c160b041c00790a00f41d401007110500428801041071420599901c1c40c04002e00000900360a540c0c0c41296090500c144024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 290195413 1250 290194163 290194169
    0xc04020f13170a12110d08070f05070201020a0b13080408030307080a180b090102130f030c050114030106030203060402360109050d0b0405070b0408250302090f1b03070e03010501 78
    0xa1000403281c071582c0e1030395605041c1402400d0a901c00c800354001d54010306200809490f01d200fa200da851181c0009024807405a0348040010501c49801c46468482e20176240307540d505030301408040c0001c0c0c5a0280044000d0081d02110102400315000188004000c2004007004009140c403450070402c05422400010082d0703010fa401c04903007143d110b115902840485920640e041c0d42ca031950200783e402801801c40c40848440c54107401b14482c2ea075a01030318203c0780700f40b14211080e42c81e20b00446510940c100d141c500c1c1002400140030240c0290082c642c8110041c0006050150068405c1c2c1e1b2581c1c072040252101c0384003801c41039046480700054800140a00f8115039aa241c5004581c014100b41c0c0043c200114150100781040414440d403402802884031142d15543c035404000d848462212040031004100d08a08001c586034501072800c807900200020040d0f640c00750510040e010042c12000703010401e0144001450b4490095405049556204084034913441c05150855070103070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 290196663 1250 290195413 290195429
    0xc0d09030c23010c051203070201060503160b030f130f060605090a090308010504090804080a1208010e01060509060f19030203180601050904121403070f080a0c1d01020c04020f13 78
    0x340051140d04040b01c2d802004500a1034013084012403801e205061000389000013942d05000001d101036170360305400070070940d00111b040da81003a034140c2c0b142a144406100d000007015003440080d079501900c00d25a44d226031700f0403428541d00801d80d6070704010b9030340e0002140e00e195190700522807400c02d900040da0101d5407150030410b2041c40d88015100590520070284142c0e1940c1800e8100401101500c0c01003013820201c03003210445280c003015180e1019000c0e000654000700003d84103c10000d0036048036030980324a850032031060207005844e4424108070b00c0440341000b0810504d10900008100003005660040c0c0300d081800624100110311401c0e8009903024400511043c1c0d1083c140e0b42d00705900006000c41180680829100c4544444074805c03805404800c03c10b5045d00443d19040b460400d41d54145c042d0b4454400380c04507000c0121050000f01c0c100b0152141200c100c0014503c3e03001401129601c000007400203060380c1c03108914604502022074078071007542d07180c0c5000010345018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 290197913 1250 290196663 290196689
    0x6030a0f0201020f010c0504170c09040b07090302060c01090201020606090f0c07081c0504030f02010b0102060a050405010b0907020a031b030806101b150f0501230117161e120e030c0d09030c 83
    0x4ac10002c1e42021000d000506039502c18000b050045018a0704080115400b40207076460703410140c40b06008000000707040e07015000344000120325140180348188992591120b91000e0303103400c9002c0e5016041440111203440040000b110b964017515401011480ba86e20013040c14034107850000c0072440c880d6001400d580c1404008006a030300850300b1130b07008802d0f05001655560f281001405000c0c01444150802c440d00f041c044400e5010420540080c080d0301c80340c0303805041c1c58068200741070034270020700002c0c51080400d5042c41c009400e141e4140301840c249103806044140800803100c001c004641366025108030f42c003822032070b025880c1004600d0004011640c5404010100400e24807111041d101031000904460b070700420300000340c0001c1d44e50748161494040c400d00c0c00c80d001d10040b5000703c2c800034581c24800414540c1e51781140260380e11452034910b0560300102038440c2c0c980c81d01c4180002d00200390000303005c00c0040ca07180c03280c0c1d8890240503c2d40c1801c0c10600d0346034020f9190002d030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 290199163 1250 290197913 290197933
    0x5060403230405010503060f060403030503100b030f04140c090c0d1a0108010b0706061a0304060b040903050f0a170702060103031e020706080a1d0f0106060806030a0f0201020f010c050417 82
    0x514802d03a02214000e0921994070740d1084d00281902c3d83c000069a800701c4003050110905911001642c414000c54400c074122030b80390319003517169000c1162580140d0180030f000400180c1c102e040265001403240440300c4400081c1e0015030f11041c1140d850707848204c086003400e0748003414001d00c0d00b01e140140a0f105260134001c0000d02c240343c14040c003a64004000780d088100090781d80030800a00c8540446c050422009181195a41c0292401d0703541c0303801c03c00e01c0007107807520f8400c50081c550306480e0540340c030b0308400d00c505c6182c000b01003400c18850f030b0f01c1e400704841c0501c01105200e98441d9018000c2c560451802911140241e11030081c2c110340d04050001c1160009414000d47c0c40c54241400c0071703511090700202900ba1020341c0041e45403512103100d80e903e4002284c01800442c1402807041503120b9000310380200307081f01c295606038008940d030742c0441c031302c2d046c840f02660041c4140d601030980904c10909545c61482907400007500064100902400081000600b1301010042c1061041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 290200413 1250 290199163 290199227
    0x10b040509062205160302040c05090f120109050307080a0906090609090f060503030a020f0d02030a140702040b030a0308090106060c080d0e0f0d080a06050609030709020715060305060403 82
    0x1a00414140303891401540c504940c01e1050f00d1614003507030100c04c0350f1000050b007112550700a50352008a005500300307039141c06081d001c1e0064445416000e040c04000013090010044545540c1d80c0c14001c955948174a000440d60600040c1940340c022a100c1c0c0c2e03034581e0f0a10051400c4040d030701c0041040a241d5040c400075070302c4402c0000f21070910801245901d505580b05000b03100170380c4400d0381440000784c3c0c010741c1342e0003090504000182c17005440b58043d000f0b8040ea100d00c40d107011000060740200d40c10595040c44d00217031000d01c0c00500f0000b0180b4100002c285400c0b040c0c40306034003190b4920b0030008034804c2401050054000c91070980e40c035803403d0f95160101d0088014000310161141607000401c1e00810600b000301014404984c1400c205040140a008007607814021460514901058505109003240c0c03020f0310240c010b0035240c0c9000381d00300081d01309130350441382c2d444070402211407000306000c4c00010754080c0015180509003850054000b040b41c441c0c0d05020b07040500c00d1000f9031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 290201663 1250 290200413 290200423
    0x1b141506190f0303030b0102010204090509100606111e15010617010503070b030f1308040909060e060c0405060a050409060e06010215070206060d230105160e060f0a0509041d010b040509 81
    0xa134035003004141d951601c40140d000e0f01a03500020482850601005010b1078001003060f065017250390308019140e200ea004880691a6100a07499648010b01641d0020864203032180403640c890143d6914044008042140b408280d1140b40000c0c42880700904180d040d007440ea005207000c8005000391480d00007400c000c1e00005140a13080b0a4080000300070800e90994214800e41c4801c07655902e03900d40c03805d0402807084020696640c2d00d01502100500703000200d0038021403072400f917141054a020100314441d4450303020b280400000740310001d01084203000c2e8002920840c0c2d0400e5907458407800092500d40a03c500440e2101241d044c040007540105599402650030788028902407194141821080310103005050b8100c024011a9001c04040d84007a024034040c0c00070b04d80c0d445e07072818111002002e0a034000c0c5d00800410101d504603580c18011f101001f40342c100030b0308001443c03000404a4000318046500c0b0000020000301154082c480c40f502d92400301c800b00a54100080115612 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 290202913 1250 290201663 290201669
    0xf0203180603040203150103080c01061d060402030403120c0e010f0216030605130b180f030304080a05030a090609030c03020105010b12011a0f070f1a01061b141506190f 74
    0x6581c00001140554805108880840039003c0c146034465170340f454400714541c00110000b416519044000c0340080700441940c0091303540003039002094407104100b000a52000d08200d0500ca00281d610041c0d601d0303805640040d030816143c0850717000c004400544904882c0148104542050300448813602c3e19440c60029680c0013580060301c0d9503142804c01082c220088040d185051020800c1204c641154201207a04404c0d025201884140c0c00050364030f0100351001061020b05002c0d0000b102d01c5800610390043c6103610210700c0c42d02980751401154409201034001402e10403819083c1034090103040e0040119052507403804c00a118000c0940384113000d607050040c1000c4100449801050640e0b681181c032043c0c2c4e43d13480c0392a1800345015a1410011184910301c40318203207015901c54440c1b812078000d0340300c59180203c12807054090049621045401e08404c0340c000d1301da40400c20129100c64162000380a00342005130400010341c804211000d140d030500b29003440109041c1d4901070407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 290204163 1250 290202913 290202919
    0xf070906090612170d1d070e0915091c0f09050a1503020d02250c0e10060809151e060d050304300804050906010e01090513060906080303010302010f020318 68
    0x20000c0c4001d1100045e119062410522505050190940188a0303406806034018013040f1000540d88000c3c21424642c00c40f003002080d04410a0b02510304a84801c480e4000d131180c1c05d84640c11140c00c08a00d4440c8a1801e8600081100840c0000340d0b070840c50200c0038040445190600920b0034081c041c147e44400490b100309900440c41842c1000f403034040d96540c07480420301301007150391030059031484000402c0940d1480c0c404000000c04004092403a805501e42c01d50030b041d05410924144d8401c400074041b24820720070100d024044560980d0b205001c1c0c181e0010011080000032411000f801e000f8003011b02c5101d4072019070f0001303900003081b141220084040c040154000107408903101c0b48a089001c1a00a008503000400951310020416144101c2e001d81480d21288011225000c10502440c0401d528080c240305524104083c404081c030301050209000d5150f4000b1420b541c02940205425400400188219a0405442a42c0e503185100540c10314845c0b0a108100358022402030b40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 290205413 1250 290204163 290204183
    0x21010b0702010f3b040204081501440a0305271e22320103081c020c07060e0915101b0f0c05040608060406050a0b030f070906090612 58
    0x40e200c03402d20040500840c1c0107100f1502c940c8d844500a0302d45d1100c011244000d80d03c60008242d034140d501a2488c01284e11034901880020200043c2500301c200b010f0407c81c0c1600b940341e48104604100428406102c0d030313201a110702c185410280c5204410540c1141e5031401046001151511844007110141380c9442101007100c07600460b18545203607428069060b458501082034551a4010203105003400210900c3c81413400f07500d0500e2804248010600d02c0c07032000400c0481c11110280c45a08506060002448041c03409002240c0c03002d500050180c1208104002e504d8000e000d03281109000e444051251801c5007c5180b4402034034101c80c441c3c00e00c07003409101544240240d4030b8640400c01c8005410340682040810140c120b28112902c44c848440400d903420180240011901c800700100740704e840d95600e0030f003e030000514095240b5a0790212000b55030382040200b03000068540034105080c2008241c0f0b040d118190800c60342c1504000b01000f180100d61103d1400c20b8000e08044c0e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 290206663 1250 290205413 290205497
    0x10e01120b0a0e0a051506091806032404020f03010504080d09261803071805040f0b040f0618030c02120a12030b011d0f010521010b0702010f 62
    0x303110600b25810001c1c10107020800c00410750b41c40d501c41744c010b500c0145010440003036081044030703510075608100d80014101001c0000202d0400c0310607001080101910412180c1d1200340c002c060503454000c0c100c10f040801e110540c01c200094503040103050b8001e0146103003986490700310340300d40b0641c0f41c1100c2c1d95210000a10408041007555488011921060030310010190f0b0942c0d0000c60f10260010000803074142246400100501255061003851401143d0b21490341e00601c00207105480240d1a16903c80000d44c807092103501c658411064005000c07164203081044548001d410854881d001c4000340c013203500a5800900e503503048a559800300315104d0040d050511540005100b0460400c10307a44258140c0c00c50b0345180c20a98604c442c481010003142010498071440503041500c81d0f091064030b510500c0200210051110070116100300c1814004400d102640401d208000101d4003c0c00c540c0c0c4a0a5610340340d500780f8240c0c950711003805842c0200c1a0190340340c00f514103010020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 290207913 1250 290206663 290206669
    0xf0d0e0106290c0a0804090e07051e04020702041d0706090f03060c05090d0b330d0201050f03090c090606090907050d090b010f03030f0f0206011505092706010e01120b 73
    0xf2040c101c41c030310a0301c600d103581d032400759000d070407070301484100c40c2c06c10805c021019030004485080f1500201186140220303186900160f51141348102d800580820060001d80c80701e001c0e21800c0e48441811144602a1128541c280b0300300b07401c0501003003030b074580805c40c070f1400d400100241e903005000002e803072140341d4095456106900d80c0d076800c005284064070910621038807040c8038038010310703250015050210700101903001c001806440c02440070191071032400c1030b15042c3c03400741c81030400724a0207812400c01c8405800031a901d00d02070f44085003d14407401c00c203100e290414010354809040205c0b000000f0f06910004280300c1c00c2003008659000c48049540150190381c0c1c000851004558445520314068465404242c000c20a05000160201d115000004190f616640502032a03428800110f1820f400701c5000001c00c1018000100f0660f1500030802110b01e004101e07250164404a1050038454024034841c14000c9095200850740d802400d280c07110300b0a8800054441a80000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 290209163 1250 290207913 290207917
    0x3020a0308220f0209060d08070605060105070f0b0108190305071709040c0908010e070f030b04020d08030c090307150203040b090d0b0702060a18080a0503070909020f0d0e010629 78
    0x9041401c03040b407907407031081c880858103150b242802502c0351000c56607060140219180c6804008203c5034040040001007200c680c040c0b900300405151003880d1420303079180c0708038400101400b0703900040450010000f90303504129865480300c001c00d0a014410385914040e00754054103202418018100403d0029003e5030811180034690003030041051503c02000286080030328000d845043d80783c4440b41c40192400582001100c5034101c1c180c0429003513540f01e101d800b0012300708030b0f004410a07651200003034600e00a5449080103a61380b40d00c802c0504101440d02100c0d500038100c00a940392103540840d4003104550aa41c3c070811850b99030441d02010480480644401402030b011060074881525070104030940601201c80f8288684070680c282c0e94500384000500506c034180420803070805a000c3c002942d402503003402c00b95940750396840104280c0e48030022112a03030b0000144410500740500c1102042079100340204052800c107050b8134030120b86442e00d81c5402c80b90030b141100d80080a41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 290210413 1250 290209163 290209201
    0x140610060f080f070210150501140f071403090603040609021009080d030b1c0b040209010e0c03070309141b04150f0b0f0d06090902040506030c01020a110d021c03020706050703020a0308 81
    0x71b41009000b0030840350700d050503924000c090010703013009034010103102e00f902942c00382030112000c1498100c41e0b690300100500940740d00d0b0941d000621195609035101c0300610700c42e60003070030b01255010651040000044400f00b0305018010050014895004000341040100b8000d04000030540d8902c00003501003070440d18000000404800711404000701d1000260003140300340c4e6410790a0741c88410710074066808840451034518240006800c00d846a0880c4503894014030b07074484812190940e143c1014130354040d08200c12003615802c41c441c1094400e030a1412482c581d4000c11034200b440c0503030442043d104240715100003007000d042c10402e580464001080981040000f01d507910103400103414145c809902c600d240200184c40341c200843e40041d22001640940482c0d9499030f00c1d6581454898882900005031000120050302c0e28403805051071090541114140a6450000c1c58441c1030b401000c10080144190000203400084441d0700650504140c0c845030303107150b1810f0140304601 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 290211663 1250 290210413 290210443
    0x90601091a0306010f06030b030703080304031b020d1a060307030c1a040e07080106030605010507020d02011808031204050d020c0a0909050c090c09010201050c0a120209030109140610060f080f0702 86
    0xba602145021703030822181d0b0741e00c00340452041c180070541c40d18150303c005031035100e0400004000070302c201128984440f250049032074030601d640118001d400c240c0d9003160302e101c1c0342c0c081203501d1440c0c000c1c00c1e5000d10100d0090100034159904c80701c03120610f100d080c5e004c000100d01143c0403140d031001d4038041d101d039030400355580c0740114000b00350490a100d00302c04030b49410741c04102d40d4824800c0b00d2207030b50050048807a50802d94011603c00d00401c0d000d030072080c1d05920104691106100800f03000482090038085070030315062490503ca40340307034124191761051401c44035946500b1244012140b1140c1c002030004000e040c55418844c000d0140ba80c0644c6d00010050450390001c042c020a85003039000304510385e545039075040716105408081010540601050404580540083c04030000290000c101242255a400380c0503010003000c2c4125041b0750700300400f4006035070a03603008248502e0401c1e4100c00b100c0024010344000303040606810110b50015404034000c104441007004a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 290212913 1250 290211663 290211673
    0x5011a0d020f030a0f12120c0f11070f121b0305061b04030605101d090601090b010c06140613020405010e0f120d05190804080f0703121401140405090601091a03 70
    0x1480e14003420a4903106c280c0206a1728110b40c005100da61040080d03421194550180004400c08280c40354101245001c03040d12802001103603030303406200d81000030110b908189140204030301e081066400001082d54210800d03071000c04c081503000030782c150000b8a070f1200d01c2140e0701245804505220300d400107040c0711b08080910071083d4020313401c68100c90143c801b004c00350341c90480e202d8180d0015964110182d122a00500a0045a500c80c610751981410258950413259490905507407107040f0500c10044440100900c50900002d48600c440280404501d81420400080d0140000c090f0282c011400c04500141585503440c0741c1c502b04110f507040f00c1260158450040103984140100100b00c070070307911800540e41c0241c0e4024020355001c4001810440301c800741880a402140c81a420811079070001c0020541a21595a070051107190b000d1244d0b050880280510f00c21203400e40c0100e16180401c0310080d03000c120035054820240001c2261042000842602d5194550fa0796250180b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 290214163 1250 290212913 290212943
    0x20f1009023105060409030207060e0301020705150703180f0b0a0605030a060c02010c020a020306040b07050f1b06010e0402092a131a030f0c1c090f05011a0d020f030a 73
    0x40d04120030280b0704501c030502442d40c0340000c3c001034130f00030701c030085c0540d11020007484281e0103946280035020001d0001820400161105445d2014184403c1c10540000080c040640e500d8016441c9010904401c0030501d01d6170303503582c1c2810b82e07689005040358810f00d0101d55608135941000d0024140201100c0801c04c441c18104007c1047e14a90009036182c0740030031044900114020140c6600103026207020390f04d80d10340703120010300189400304001c010003c0c1043c00070707900041e04100708030408405856181d10036107413800301e06800c0041c001e0514410000180c1e102c00310580d000540d5540303400d00302c1c29a2075075000c44130100300550110001194400f00c01600040c42000c860740c2045d0280301c1d124002d201c2400744010f0710160f0320f8040740000505d680300803c0081060866400380b40c29042c10415400e0115403180d0811502c849012200000b031000074020701903013900980d400450014141c0014010758001c84000340078003122400366000d9034091002c206401d230019061103c03048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 290215413 1250 290214163 290214229
    0xf160816081308071a180306010b03180316060b0a0527010f06020a030507050f060c071203060f1520030a02060a0207020616140703060b10020f100902 66
    0x805a1084812050900700103103c400020360f403400c441454044000100f0440300442c99070b07004c603806030318003007840341004d5458404202d0305000746111056541c0f01d08250a03545040100507800202c13a5005128034005800c03a1100f00884a51101c40050709107110004111411041d1b0700513a03000c0604009142c0011000082071052041c4801c84c4030140e0b02c40500c0c0c50f80b50442d005000059120032018000207000300e0044c144940107004a43c000c08001c0c0f010b41c90144200c3d010b4483e204081542010001c02c502d1070559078109040500800e4204030700801c09401c1031180450540d0081c0c3d2110345980036400103100b54081000c4140200301401d102680c9a01100b1210014454480040c02880e524801e680d20550700915107481d0410381c00030703180c1c54007a00206490882c0518900741c9082010000c0f03400030f61080070041071000404003040800c0c0400e40e400b43c10364016001071000510042503158001c02c260390002415004c0d03001241403440d0401a2100800307021042003042a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 290216663 1250 290215413 290215417
    0x70509012609192019060c0c090c020607080a06090f06030201021606050304020f12030c070e07170a050702031605010f050a0b18060301110a17070201020f16081608 72
    0x1d20008119248440310f00e80440140c0c9503250040d0030540c00c04c843e0100031680b2203840c550084000c100c115422a4001c0d68442c81c0003da11030300c0070030403901d0a07008010203424208020400e20004201c2c02c82801c8003c0d4484200501070800c01c1407074400104501451390196000e07158140041008400012002c001000580001da0151141c1510030f0000030414070500d06481095032454210303201c542c2403194468400400690017804441e050300341300c00401c00707803440002c0c21004220081c0380103c1a400e140c00500101c0801c58074900d00380050740301c0000560421110301c000103143d61050412825402a242c41c8044078100382054000e2180c15002003000d8000400104080c2c2c032100381c400100d440e0381183c260001016501420b6180c000c03e030165002c10090008078440c4200083c4141942c84903105a01040c406441d005440381c102d031010742c0c02003da0000718506903814540d110540902c00300d45104054200b54803003006040800d039100c41e00350300001c01c00c1c50001c1c07611054903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 290217913 1250 290216663 290216671
    0x1030c1b05071d0105031f060302060a03090606050423040203070305030f0304030e01020d140a02070b0c0a030e060a020604120507020406060905030c041a04024e0f0705090126 77
    0xf401c80e015240b01882070301e41241d412100010b00604a05100c08504072400c4012661120403580e2054008003503143c280060408074099070300003940c03840519150007182d0030341d00b03c6409103260080303e40e01124644143c0c00900740d803a1b04050b80d9079403171000a142010940000388280808261a54403128540180d4010345c4070392030f43c0c00300703850300d8004981d10700303078900b800380016008140c0110411442c001407911181e2841581c454030b4a0341181d1400350300a510400c036561011810000f40355001d000c44c103c0c00030442e0303642d280c01c81002c00255600001303440030301f801421008841c172841c00307141290761055010303000340300b0a545c41c0c2c005400610325218540c040e015546030400e0300d1410340300d50b41e5050034010300418100d1000c000e00c0000e4211030000c0b010f031031529000c01804590304600044401003840e0040d4620030f03026030802e00c58a00454402d800c1e103a20f05024000101d0340110354021480d10300140c5844169004842142c0102820840716101c1d2000c6210410920708032446 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 290219163 1250 290217913 290217929
    0x70f03020601091104050402070311061515040b0f0a11010504082503080a020a0c020406090b0a0e1b0703140a020d08011a031504020403150b0f060301050f01030c1b0507 74
    0x550f0f903104103190966814034030303d14a854040000707001c94a41a800341c4030080c041c4c075041980c9002010035910704202178803d400f25103ea808859103520b04a0000030b80702e4940e04401e030800d440c00d0207103a00b5010314030030f02c0c0450002098030004e4602c6181240315881098000388511b051504000f0100c2e13100040301d42c2002c41360402c20903103030700c000c1088032260780c50342d030345d0485235a00c0741c4650081d001840c11100300001e0030000b8001d42c3d12806004003806010b20006144000f030403c0141e88100359200940120f00074041003a4400c50900c5203419111001d4807542d2840340780f80894034030304040c11101c64502e02081c18004d44d0f030300203203880010040780c580c0f20700d40c1d880e02c0007540c014a5003200c5000d0f4a204000180440022880c4a081c030301000e40702500b015225070f6a108400d04030b440b0704c5115a039800c122015441e0040e2409110502580d90f00c0c0340d5410400410540341c211400e10741450340380c41c0c0d00314600344a1070418003004100e1900321090308191401c541c6404051150000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 290220413 1250 290219163 290219173
    0x2030c0103050f040b04110315090105060f0d06150902070b1005030313050411162a030b01050118030206030a06080606060909070809160e06122d070506070f0302 71
    0xa50091090902403d42c03c0010800c6507500d035141c001000c0010030448072002e0f00401c1207401d40303080143c02c461049828051020340707010701c3c400782198002040c00e4801c0d8910861080103446400521049582141d40031524090107548500388070401d50000b80c1c414070020b0450b091241109065026940c0c2200c0a00d001d0356442c105a680d000d04201d101220702c10035001c008628083d44182da4180d4143c800300e040a41500c5a074520014052081c0d070494208290b04c010402058207a100d105d141c5c0380300c0707240315080d9140c2094070b03c01409030b02c1c18040e0700604024000001c00303484004503401410a50303203103810561039014281c1da02c203000f018454003010601616024040d2004039101070010384090303850300d0007110280381c090012481401080c0c08581e2030203e2034211405440080c0403411141030480074844400c520701c00900d003a4005ca054100c494403d110000011080c51500418142034031800301c1c10800d280e031000360b00c220002a98010803984903070050b01b0502075020760f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 290221663 1250 290220413 290220433
    0x4050703090b150301060302060f09100801081e010b0d03030c03060506030c030f060d05011a09090303040c050603070908070f03030e090106090b07080c0d2003040f0b0708070f0f0203 80
    0x9000c1d41d4580800500031240d181c00034001c8404022269203000700100003107401c5d6030780d40201c1e40780e5004012040090000080901050a2024202c80912590302d00b1004942c9070810703540c2c40d4043d039070602c000c99001d80c02c5804280b03425000305600301002410b0400503485481c02030028603100c90107a02003400c0c0300c4001010300c1c01e5000c1d00d04c540380c8045004c0c40e640d1184400c00442200410301e80d84012501601d01c0410024440c5500105180e0034428a210402c4100035040380010010085980304008010000c0c0c030000c9004205d41c0251a402c2d200d840d0080c0c1a528030381c41d07401c0a04a0300c500200012805e070146000c9007224081c0d10f0341d4184031604401d21040380424065480419404281009006001801041c0450007808240d042860a081403800c003c40c0500311000a104c00d070402007111034001c9078115084801004620b0103280c0907450851824620403458082d101080d10400c0c030130108101c50045500a01c04189aa2a07140070900040b0f40a0140d000788110400e030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 290222913 1250 290221663 290221667
    0x30b060307021006170703020f151b0601321c08090a0b0415080703090b04050307031e0c0f0f08041e08060114040b040f05010b07150c0e1003022205040507 68
    0x4243c50305009000e040287d0842d001c0c44811188016401e030002c01d03082e0b1041c1e40c11016000741003981c01c0c020340700285801c100111403030903070306070000c2c07490b9091003103501c1c03142035a03056a80182c003814034a0340e040c2540c42c1c0026800c2c1285601d200703281c40344490703080820001ea80108001c80080340e501d150240c40b20005486809a03000d0001550385060030306503814000c000c4150b201000d460080f4031098990b803010300034a01650211480da0020881e401015002800c3c082d01e0b140c1f0030350249024096840051400200b107201500000d85000c81005018840d90100f400c190000c00325580c480d07450f8043c2901109000e025185001c690700c001c102c2ca080858994100c5051040c0c6200103941442048014000700801c5036010f680c810703901014034410b008860080101389105600d410140c1428926903200a941d070400d1480c0000c0c0c15115a00300c200074440f40700960b01d020007100040b0b015002486100c0d424840c0a43c25400c00d45100034070304040302612004c1d01d0a0205840314482 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 290224163 1250 290222913 290222939
    0x709050420070b0901021303030f02010b04111e190807140304050709111c0606110102070206030708090f0a0827030c0f041112041211060403080601030b060307021006 73
    0x140400244040020601180c2d20303140b0f644e00008000300061800c050954581d051482d940c0c030441c0401c0050303030003001c040c1e021300c500e504a81c020341b41480505030b080006a454032402c01040c0202c9603070720503030942d03090380c009035040b800c0074640c4e400c401d4900c0407003d8255003088810f10b00054102c0c240c03012031078034103040e02e0055911034000e100440c242a2080040e068400d4007480c042c1c000c4c480c0c002d04240010025001c012504400030fa03250911700c0040c601503404e10810016801000410010f880d88812280e20030b000389040c0c182c584512504c2403c048013041900c1c0a40306000c585810f01800c03500a000c040d0b604200c09207081c0861080036500c9140c0a54568950010480c01040f03042c1704641c460341c003000920009101c0d65070b20106920780c0040c210f440b201b00c04ac004000400000030900010084142044201c810103031170f1803541c0d0500280000c0812903280045007407a400fa4010544000b002000c8948910302010f0081da1000701d4a20895014200000000e2619002c0c0d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 290225413 1250 290224163 290224211
    0x111011e0501031112330a0b0f01050408120702011407060b030606011e0e03240a110306060406050c15130b010609140405093c07061209110907090504 66
    0x16000c0c036aa108120000d1b1405003003002d6020700c5002804401c1a07500c04000d100329900c0000003121083d6000713202004840034141418088100014001100001194001e0b0214810003c0e60b0b818148012513144041d03120036101ea00000c02d100080003850f4201c11480c01c819411503211307546410044401d03900903030203507031004540c2c07010540d180c0c46200403d80d040400b5040700c401d00c0301d91000320102d03110340f180811640001c20600040d11030601070524509100115981581070040009080d0b2040c2c0c8165010310400245041480340c0074440351070154001d5040300e40c0b80c42e0124414041c862550300454203c0c2c000b6001140050180c80c660301520000c2c9110a88042558203001c02404060403800700d620410a041c42503560741d0120440e03000c201c41c07507806041c0c04c1c48607890b010001c04081e00541d0304000d40078010741d40d0002c0170404000204901013503d45032400e102c0364800c03a95840540041e004020070200325001000a0202c482c00e840c100501500ba01c030003841254080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 290226663 1250 290225413 290225449
    0x10c020906040c171512060709060f0306080601030303021b0105040302070b09040608010c18090204061b140607090f060504080606240403050601061704110111011e05010311 76
    0x10300800d00d1030405a00224600b2100e091080d82c00503051001c0125400c05c481e141d5207901c07481640708180c00c0102a00000c5025040288106e0410f0b05001d0003400d494003ca10420408107003502980b407003030300700c040100b0100c4161115543c43e420010081d501103104001141180c00c425050a14144103280c4644e4055014102550410101c41700c0c81d84000300b415400b54480e0b00100b1031003403e00c900c060454103929201d40070500e0440c0408001e99a90000c0801c51061008200603500314922540c00007648045001840b514541070b00c08228071f652454284c40758404004c41c0d0360b001822081039806400840908503500c8104403400c0c49940994426500103202080c42d60a00c0c401c082c401b201c04000e02025070344c2c45900c6e0600c640043d40152916444480100503550704185c80054080e103131007622f006803419482d090904202281e2490410039070b203100c614864000c0d4003408207250031040031840b0340c1e000e607000400f90500303010980f081e11802c0e41c11162803400740800300c16410b4203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 290227913 1250 290226663 290226679
    0x8011403100c140d060504180c05061c0c0804020a080d140306030c09040803070305163c091721090109151707090f0320030307051506010c02 62
    0x310760359102034000d6007010014003d074a0b0001e1410846900a408210310703000c40014100d180404002c19130364204039100054103a800c0c4400825800944101520b4007030300c1d402c0d940c525142503000b0358050035044100545c5000b00350608698004082d90207107008a800440c080d4490385510345501164041c0000301c0d00320710400c06070a110b2005954041c00041c15103c0c40f0b21480f0224840401c200c404903034a280000420020f0340d01449a150021a295040040c054a00078050304007115801c0b5003e05241240c41300c51550355201801c40c1003e6041038001ea0b4444030580500000258003032880450305074000c0b440c11100006200aa507802c4c445c0016000801b00307128403d5500c56400c2504102c0c0303001020418210703c0d65007103075180d0b542daa0a12000c40040d0040160b0201a06040c108507452004000d141c10407660351050741e4010302d4a00008000c4523034202c0030309140c2183d64246c040440c6200503c040443c5050000e80700424038400c0c0d541c1d840046418040084009622440e8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 290229163 1250 290227913 290227933
    0x4060b19060e0d0206090306130b0a0510060809010902040c0903061d0d050a0c0506040c08160501050a03180c03030207150e010912060b1504080d0c1109040c0b0408030a08011403 78
    0x15083c0c0061040c009804145004e051901080c10000c00311090314074660b6100c401410009041304065001ca4009010849410500040c2c110071b20a4071076901005402c501144900c1420f41c4446909540140b04000720303c04044003500360181e5210035203c0514001900150701142c00d02980020400c5000d44401c1c0700d82003003a07400303030440c00c0c9050030030003400303032090006200300540d9000310300401403803880300e01d03010815190202c8181159034004420310100650390304101903420480444c03c0105440c600d0040a0302200382c00213014007101202840002495004070384101590490082c5001800003c481511032404506c1d00074001540d6640412241d20b000d6890440c4910a880c08954051003800140002008001c00380d20500d0005040180020400107203075500001e0800b2401e10b0065100d08103000140d504c2e1074022030014001408001c000f410311000361101e00d02040d110fa0716504a42d40d03a80009140c9008112414000f141507200c6509a00c00b000c0c00500a00003011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 290230413 1250 290229163 290229169
    0x1050a02071505072109030b1e041103070e090712060b03030c10062108070f08030403020c180c0a0f02030c1e070509040b07050c1504060b19060e 64
    0x102010101045000d4150041a099001c8202000b03002e626a5419164140c0d0304184c0c0e04803c15500e0314a2003146403440c001020707040348296044035041014030311148e407003514110b103e0565846a20041c03070000c2c10801000040606010112401d80c2158001922000e140400d800b084d10b0145e030640c00080e081040c1d40a103100a1480c2d4880c500106421011201103440e42d00541e000d9031881d044600c1084104103076200d400002d0401400c00441d5195a4041d40861303080400c02034811400010444140940500044207072a880100703030b60340340340c103080c002e481c0d0176001c51891003001d07039003016a0006807a02c0401d00a010303600c421407500c1c94605c420f80381c1b20513641c00324055004c20b0201108107582881460700c0d00102600101e0405880013050f4107105035034002d0752040f0401d005000c0410f1101c1a2554000c1280c03e02ca6078826201740c402d45001e5120012071040825141007100308245500300142070102030360044403180c2c0c0c0b944240f040ca01203004803400645038201d80110b5107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 290231663 1250 290230413 290230417
    0x9150503071701020d0501034b0f080a170c0703142b020d06091b08040c03150209010f0c02010503070c0c050603011401020d110303150415090c0e030c0a050105 70
    0x600c1100014540382000e4030540540d1400d03230041d41c1483c81240d8030f900d03500c000785440c00f16105255003005d0344175441c0f954000c2c6950300e6007050504160340142e03408200402c816030303544a030011115a1508044100140142c050141a100940c114400301c2c2da40030701d90090711000d0780d00d6141c0c0c0d0b4010080780d0b6027036030941003c01c8881d9642070305000c1c9a4203030320343e00541c081d1034507080e40075a072000505510010381d42d17158000d01080c1c2c504400c07072140da0321710742d1110892702252403c003084d911981407401d40f41d121600081d05c2c803100750041300c1c2d41d40c01c3e43d4020701c112402030f00c8040104428000540b210b20500001a01050381000050440352213507400c3d2810034460a1200142034468010410301c3e0000d0700061048804240f20f40703140d41c0c040094030144c00892a0102480740070034051610703800060446000c10b40c130041480f09580d0b81c0c0e0403000441000c0314003110002c0c1d8908600b4041c0084400400100b541900001070f50304010811100604025120291403854940115a40d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 290232913 1250 290231663 290231699
    0x902060714011805011a01080f06280609060e01050a0c06110d020f0a1106010b0d0b0409080c0d0905040204080303041226011a120a05090708010c08010915050307 71
    0x40d580c92031042c1400a110702c2c80c1d0f40c407070701510000801d02ca031184585010101500c0c500e0510251004206030b1480c0423041d254410f0741500ca01c0b080c4d01504820752448000b00d0803820720070346000c0c0042041a8080340700b2046035000c1c0d591a140c5a00d0b0001500d640c45641c2210000034a03503080c030008100f072034010204003d0311002c4e5520309507401c1201e600303d03089600305a0707802000280c00b403c100c2d0b00c58140080480755401030304655140054103101c80c03044c841d58002d43e40d00c90308045181e954903409116119088610750fa9268140701c0c0030b54866036500900000700d82100b0022800341054070a490a0392a40401541356403510f846183d20041e140c1c0780302d02044200d400e140105444006048200540c0c404030000310b5050032011a400e40c80e0300441001c02c94103010f01909202d24810064124840f808002000c0c0c40701c0c1c10319824101a900b101e10250300703213202d14280507400850175040781d4026004200480d843c0c0c00a00c0302a101c0c2c881ca81e0325911200c41486068041d0140c1c2c914 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 290234163 1250 290232913 290232953
    0x70302040e042d06061d090604120e06040e1b0406170c07140f0f0604020a0608090a02040e0d020118050c0603150d0605011806030b0c0a091e05120109020607 69
    0x44002c58065000c01c1480c400c01110810b4983c2820400702e104800c407021341001c41c10341603040b0310b01f14210f940d0b030b42c4000f400505101d603e014101203583c007403000c0d41a0018050190740e6250344036421030007810380a80d09580790680e05c0382c20071925001241134070181c40345541c590103a00c1210400c8240075101800360034400d44100b2641d000103604c03405014174020400054025049034460f00c5003410005000b00e1040d4104804210041c1d40c2c1c002404203403241c9050094940d180e00310390360710780714858400940051907c0b11019100100064039035440c0c0f0250700a001c4081010304044010f0665500104075600008220900e483e00030091503000311032120080780c04441c400050b038020392006061350600d54030801804506140c4440c0880030800000610a40c0e180d40d84d108611140148480e004880100e58042c0e85445030101800404003000d400500d10b440030420010541d40b442294802c110030a041d1101d860180110781c4c0003070f0010012820306007262030394000c0c41090520119 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 290235413 1250 290234163 290234213
    0xe19081608040902040f08070b16080a030f0504080d06050d0b010303030c30060902070b010306020904020c1e0f0f21190c06050901111804140f040b070302040e04 71
    0x2405030207503c05030001b081300d031161004035450488901d050501640000c4402171040125507128070300d41c0c2401c84280d0748005030300d0ba81c07024035004070020400c41102442e66070800f130900080c440364002602661a00002c10414181c1e520100012020041e10003020452400d00400100740668032024590310356050412040383e12192071ba055201d00d10010391a16208482c94010301c429100f0384004d003d00c0c0000f18071b008071380d40320201c4c072074814440240710580029142c1e659171101d40550344980031340307022a40034080e60314050f074104c805100d081100344a0340191030320320320000800748001c804e090040d040d003d40748940d072000415400040701c003100040255080201074081c02540000c0c180c2d03244a000e000f01d01d41030007902c2c030282589407103a05200c0004554075032003048900300051034104003601101580424041c0004510b1001c010440600700040c10100c1c200d410311030f601c220001929a42c4081c000d030124002c500035a04a60728102c0020005103281c2e011460304040000801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 290236663 1250 290235413 290235419
    0x50c06120619030c080f060f060d0209150406080715031b030b0102070513020310140609041d120403060c020312010506130306020a05130f05030d080c09060703030e1908160804 77
    0x1480c00085e030110809500520078031511110900c40203800503542c5034840e410741010f000090000c0d82d422006445059107801050b8415540341038140c0c2c19001820500c0602d030b8420030380d51105400e2150600d01036102c2d0322502114828441c0e02107445000c2440d0b000600c00440032801800200c2c0d8131819071180300310104050707441123920701e900d440a260160340c030301c0c2a002c0c070610715915620400400c8059110840e4680d00c2e034094801c0e511050720009008801d103403851510004500c1a00a14080c11381011205002840180103990003032505003c400c4650904030b81d01d20903241c06a161026907001404580b91490003071006520803e11407402d141ca0307403500340c1203030302c8001900042140090301d05100c114075407902001b01950010060340034681808281c44502303c610510400c00a600040c84001d603600035642c0c2c113500905400d0b2035104c3c0745070150080048402c8450980705500e2640701e0403c8010408004903800040d03541062440745400400d00c07070145044440650901002c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 290237913 1250 290236663 290236673
    0x21206040f240f090201110c06030106050a1b0327051005030903070507081b12060a0e03041802090a08010c0c0308090109060509030d060b0307140a050403120c050c0612061903 77
    0x80c40e1281d00f01c1e40050320808910000d042003c01074000318180e00507910040341d40e5a02405d90381100c046d400d0070303680c644c5e10740c20461704040851800c080140d1192074260a05501500c2e21140d401d07103440a1803040340785801c007400d40d00c0c3d9101d0075901c0b80b1400e014204491080d4040d58001c0e81c544102c0342040d80c1640c2d00750901d1981e401842e42c0c1e07800030443c1800d14200251380300c40350500f56400304012103140c4e111503e92800034000c0845c03507111140409085810403c442c000c1180c0000001c3c0f00300e240d8050b00c083d5102d00091031081032000000304020302d040c030800b9040790740c588820800c60400da03000d0716490401003120382e4655030340c01c44a020805034001c040c424a020006181d8549205d400c1004540a43c0c0100075004d8003070040210f0340303800140c04001e84c015111900d0715106071100c202e0f42c03841a500000e15094540300b850300301c150400c0300109900d110704180c44c4140c2030300041c4500c134094001300c25903c42688012a009091104030300c04c80c0c081003020166003546907120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 290239163 1250 290237913 290237921
    0xa080711090f19090b01031214030c090108010f08030901030c03021b07170708070b090d12081b0310060804020301060f080f06010f030c06030203090f0f0a021206040f24 74
    0x82c0d50341c515882c0c10030440c000329580ca02003029036940c0802201e0402c1e12a00443c100500008028010079031598203424017a08080c5504d1040f840400d80d02d141036280e43d05a50030090240b404100d82074004218181e00e201c0002c180c0b01c40c43c0084d0306100c070b03640044000e884213084000070f1582c20000300a4408604102c5100801035100420952349001000220843c11007100032898004000c20b004014000c103611040765070045a039505d40310300f2000684580c2c400c0034000c001e1903a5030880c00110f0340202c00a07200740a001070901020035034a035594060303c170464090150341080c49007849003500400780503800c1800680001a0700e9120303180c2c400c00c1811034002e41040d60041c0c09044040788200655130140440b000300c111044e1541c2d4454003084041e00800043c140c02000044001d00e0802074141c404422070308491084100c078070340d140c8130b62030075200713a016458100d4442c001140014040303000396403005012004010a45800c1c04205041f400c251000c0341e0480400600102e07401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 290240413 1250 290239163 290239171
    0x1e030e0102040b18090c030105090712020721090e06241323010c0f0807050d08070906170619180b0405070e1518060c01090b0f090a08071109 62
    0xc9865610400d16071000c2c2c0220703070300182601c11101d07a41001b50b08890307182504d0440340203640d140144d40381c61200384c400ea1110b1969220340b600c0807850f0785c107000c0000800b62013402d125150403095210900b04845240c3c5500800f404a00103c000c0344240c00d0050851502c4800e03440c09408440240c401a28240c0c442c602d4465480398070042803000000108485e5441c5070300e40e001c03251841310b200c0040c040103080c18001c0e103c2c8080e10041c90603c40394104540388241c0c4003050305d0009084110107801d18105031364040029804660108009005480d040030300191400c000c402030b0394450402031007982002120441c840011000a900310b4684800200814610400305000ca8002e0901c012207000a1000d0100b2408450640d0240c070b41e1040c507034050300300244281c0d440c0c0d2251845019901e03505181740d08076600041d072240d0b0340b9042d0710081c4e655100c1d09101c4c20307a44862998503a84501a142c90301d05402542c030407000624518020042548186002c5a00301c0c8031000041d60b00004071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 290241663 1250 290240413 290240429
    0xa020d110f1c0e010c110402130e090106210f0213150f062c12030f040803130909080f0309010f020705210301061706030f0a15060e071e030e010204 65
    0x4061012582d00290341d4061a2803e10b80b011562135146c5134250080d4180d2417050040342c1c00100952003115910011010382800d007400d041508103080154020041849a40450084c25507c184010a000721110350b15030849102d220030000780c0c0801134401c5045c00104895a0f650208101d88074603900c1544c01030010001450040340391030300107080c45940b12400e5140f2064080705080001c1071444c8406180c0b0161420310511170011006441d510407220240180702022800140c00c2c10004010143c07483c5a510109066a8988048054490800004140503070501c4400b0700e24544d18061540040c07040c001042c54140c0c004030b001240d20801d01544ca60b00700510050340500080036403807030740c1d8070690514a15071502c0030080410050f4017600d0322001c00c40000c24aa075078104030003a10070110201780c0e03201512500c0c180c801c0c10700303c035a101d0b04282401400140101d180c0d00c09803140090791a00035003002001d540345c0d040c2c1030161402090543d81c1944801140703091002c1d101503c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 290242913 1250 290241663 290241703
    0x100315090522031112040e0109090606231203090f0111011814011410231003020712080105030a02011b2a080307020a0e092b03110a020d110f 62
    0x10380b42c14145217804e03101c9101058200030800c048106c80400c1811038580c51300c00148003400b483c001e406007001d688041d00c000364130541c641e900404544181810901202d071101e0303810030421020b4a038000c219909500c07040300a29515254000c05051058902e82000080c001c0c0c420b0f8007000b141030001c00c050301c0e0055560b20980100c04244918000b403803813000745546529044240500042250182c580040514100140d00c11603e0005540800780100380c01032184640d10300400035041240300381c5404e4003202014050a00400c0c2490588070b014020f8010324100d0340042d81c148901c0c0f810380d840380e40460440f4000c602c02100410111100800c032540e2001c03c03003520144190141c02c0150342d500100100401039507150001c204407010030f03111042c50f90710460381604040550003040d62041c0400c03282d0040f91440c0c0324490301086580ca0030007030f130a10b15201d088180243c03a480c002583c01205071407030b100d000700e4444e00140d090900326401c0070b03800c180f518104a90000c82c6812002e02c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 290244163 1250 290242913 290242937
    0x509010c1b0b150112060e04020a050a03030203030c0f21090c0103140412020102160f0209010e070507060b210a050c0303090108071101110c0c10031509052203 70
    0x10110005080c0040003501c8201260151100ca00201c2c02a00a0007203034180015619141d0081c101c1c88850300340c402d810007078541d07140f892208590084900f20f20654500c0700c045141d103407000720035041d25056401182559070700c1102003150380c890f220046c05104244010200c910800d032265002000c42d2030b00e40154200031903e94070300700c02070904a05060515188c600500011800c41e6400fa0300080c002c1c110a0100200f03a00a00c101c00c03103130342e100300410742003001c0c01140310208a14174400d0390005061b030b9076210100d6041000b030b21040001101009080040342048c1c1010310400401001c50460004402c00b21403a0341c3d04c40c0f400d0322070b60000501141404002d00c02001801c8003a03010b14a4040b11000007019000000d10303000501c410103445d85400102540044d80081c00941c46d0303951031225241c40303a0b484c1102c406191042c004511091280c900c02e024a00f044004404583c107020305004010001c1d00e4000c040240c0d61070086240100281d03103a070301c520040c0c00394680041c00f1007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 290245413 1250 290244163 290244167
    0x28050f061f08090a022808011b050f07060c0504031205030114220c0306050405010b0702030a02010f112d0c0310110d06090905060c07020a03170d150807080705030304031b090509010c 80
    0x100d03541f180110383d1510325510507104900c20b14036608402d6107400d0380d50303c0400340300c210ba500500c000178120600d000314032414241c01100401c140d038000c443d031010318002c0b074000b2241072109004101415510480b02c03860360070200d840034410000d50341810344150350b41c03941901700c500f14222840029120704042090b03007054404c15000d403040d941c0051070856640c01003039950a58400c001c0c10082c0c19110500d07500d214018040000e501e00c030507079402181c030b030300a10100c3d03040300141d0041148011a0309908100061321180301c0038003401071300c21300c0c0000015500400103003e805860000420401807280d495104100c098120100d0001d1140e070603003080f510b040e20050285290031400c120001c0036035180507200701140c1c9d00c50351651481c54100e01980705070103804034070f050a604088c00d50740704402d10015181900c0303100341200d5005a852540d150b44d40d429100d410b0300b5400c10082032012443e04203404200c902800b40c031950195541e00d07e90104c50044688030b41c81e96440d9004800300d0b1b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 290246663 1250 290245413 290245489
    0xe03101401090c0203130501110307120c0b071b080c030c071509080619090c050402030a0906051609090509250302040506010503040210030528050f061f08090a02 71
    0xc011310003182400c81000301041d020f012801610306100c0c07402d511214242c400c00c21200c200d41d012152214010004d0005400d1140d440e60803120070103044005042d01d8801d1070300c120b0001d01c2d011385034a40407840c3c858010f990f010036043d0115000402c102d4403a10f41c1084007100a00781440c1d001d01e21103d00b00001c103101100d4000e01902c1c0c01c00305c00d0184a000c8850440c034807460b00b010010b515a4245810b0b8100b003019480300c2c8e0407600110410510041a0380109a014002c541c00e201640c0c0c4c100503080c3d00d4440058841c007140340728009004080c0c041d03000c3d42c0d02851140c201c47c8400071003855560004100045410072001d00b040607c21418a07001c1c3d9500002d00382401811818582d001411003c2d400030000c0400d5aa07400150520100001c4043c5005003102c446030092003a5240b18040c02044410740b00c0b407503040b4040360b402c1c2000f042c420200704c40700c840210307812417100c0c2c2220307942c101500d005401e10a10101601680d51444107000c0000e80c0d001c41d1660103440c4c0d40d450052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 290247913 1250 290246663 290246681
    0x7080319080f1612110d060803030702190f050a08040602010606020607090b1602190e13030f11070801021207030e010b01120c0908010c0804140304150e0310140109 72
    0x444480248000d00b81040c0760560400210400d404040d2200c00f000c441d8040491100103090f8104030004101c05003403001803001154929040c00b900f900c801031141d4070b100035110341006074050300f169030b403c08450360f1010aa5204202802d00c4140949556184c018503d2040d1840b4800142c01c00402d0380911410005114034006041c4524260b080600500031f90b1107500300420700005c3c1030010340703d9000364440030780e4001c110340700411031210003a01c06c40a45c011040a2103440f0302182600503a10b00d0190103903451307920140c03800c60b8414200e6581c1c95402480c185841100404180d0110030700240a4140c0c404030711600610b0b000718020306407440070001c02c010364501400d045032641d02156600c00d50312240c80204412080110031600080c0c02e6000e074041e0352070422098200341c6c0c49400b09000c0c42c010f511041402050f41c0c0c6080d148c0c49948034101903001e10a17101c2031070901820186444a1008065840a0f46402d801030705491440b844882c0c903114035001030110448900c911005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 290249163 1250 290247913 290247917
    0xa1509051b0f090406090b100c080f1b0109050a1a0f04240e0d080c13060e180405010903200c120106031b0e01090b0120030c07080319 59
    0x150304080c0350768044041c6019901004410001d14840726640460440300d000d00082c004119155843c2c1e280c8005103560301c3c041c4e1080c41c040580642e2a8402c0703d0b840302c1349820200b0a49000340724103000104e680301e47e440392a80b00400703100340c0c8164800e1140e082d15034050406800326981620b444000c7d00000c030218a000c42070308080c40416409410b050350300550100111202e00c1d407880c2d0851140700e0000f4003441290070006100c52000c000301d907d108941203503c0300901619800180c034410b01035015014620160702c0c1c1c00700415441611401210382003c3c0500d64400c84e00091002010030886082e910782c1c0d1a02044d0040580c402042c008203622200700100b080c070394070b10054603401c4504013288610044000ea90b00d160b030a43c0005e0007141e00220b40808040c200408507850840c0e4825050160035420000420340224021032100440503900e5209400010b0030001c2a090103aa20184a00c020f000103556094100803040c00391100900640d01e0700d0742d0282d02074500100ba001c1c101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 290250413 1250 290249163 290249171
    0x9140607030e012016030306170319020307020d030302030a020403021c02120c011b0218041a01080111030112032304050f030703020307030f050f011103091c082d0a1509 74
    0x681c4d074441000b0345032030185003520204900b40300d090850140c56682c00030040300d04006a000510303600003005254407004051440002d0b00381c1181a6140d0084401c0079421484034100000068803950045910418800c4018200307612074000c111000d440f0940208420700480000096281940708260f105d04150010a55209a00d000078807240c481409240000100ca45542c01c5503243c0343c4a482c241a8007820f881c06203070509051803210700ca0176205802c42c503880004a05c4002c103005680780c00d05511119851341c0d1816400d450801071000b015400c00c0324141c070022007d01d00c0c060416045034643c51702600c03241028100111140e610b00c02c184258040c0c001000142c41c040b0f01c0c101100d810400e00c481050313081c01d010f42000c1c44400c085000754a010b58403803110440201650240c4044800c450708041408104010103451023040e0010a18110000f010044c4010380d0307059800c21542d020100503465801051000380c15202000324580b00c0c10a18100310300d01d00703640c00401043e80240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 290251663 1250 290250413 290250461
    0x1b1c050f15060706110a030203010f0e040302030a21110d06050d0b010b07020112090f0c090c02070b0d061a0403020415150507060209180402120102041809140607030e01 74
    0x9100d041079507144500800010541c002440140e42c4004e000d6503020039a140c1e00c50b4051001002940f0034092603081c16000d42010504620400c00700d8821a41a0002c500e040c03003250058460b10288030130300000b4000ca115900840c41030380102140800903040c590703256074203015164195490b0f81c00c810300034400300b50b80c00d020035a00e0410318111003c1c18000f52b5254402c0c00102c0c0c05540d8007060340b2106092040c0340080112750f40c1e070408000d0190700103400d801e4851031010190f8a00283c0200140e000d0f4005107e9148284010301c10046c01420009440e65200c2c400c400b565100e1208480002000c0740410560400307008074005041d1311130680c404542000d240c2d004400789408410304206000c10f020081200b25812a22401c0009000b5100d0100312540340407010000c440490285001d1341d800c1030740000500940782915070030b03402c00401c0c000c2900789000414180205844030b41c420070701940096010320429004401075600800c20100d0300c1c060509580d03049150395141a4034034540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 290252913 1250 290251663 290251681
    0x5180a030c080c0c090103050606030114040206070b0c0d060323190809061606090302100203070c020108060406090219031a060405011b0507080a05060609010b121b1c050f 75
    0x1000807250320203441500e40d081481d00525064003424800d0300110b40b240040107000c00007072810710a4000702d000b44000310408404560300d000c02d030380080d00b0850a00201c000280107000c00d59020711705202a9040c00100f560a0341a140203500584180c2000d46541d10040070030103011610596900060080c802c0c4c1e02000980030a640c103002c2c044007404107a0300465a901800c0795603810342c1000c0109041142d0829a00400030f500044025108281250a044855000380d074440ca2460321241c07680646500151000600103180d01d80c0195a16800b0801f50302c00d00c090451069464161038400091200180032110400d0301c0848207400d064000c100360351a1000c403030959600b80703031850301c030740d03091466031030401103000c00902d14001c207403001c13640034000209182c015005508492403915407500380419607000780902da0b0003c0d0300304204071640300400d030b0241e084590b00140040883c02484202c6c0181c01030f441c000c0c42c00040c00758565005a040c09890b40106c2440400c2060303044c49254 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 290254163 1250 290252913 290252927
    0x1003020a050303032e15120c080c1602040b040c020601031401020c0304090c020307020a06022112010905100819020a06030e06070e01050702040906060815040f030503270105180a03 79
    0x154a60007005030218600285d4070810030006281c020320440d1001d11810010f008240d400508691706481d098045840078422114103004041c00c164003071404802d4903000d03401c0007004e80b0690300552070307410522040e1514450b05100d90110740c050110b65046180010814141070081d40640c0e006001844114102104907422100c00d01c03000941485541c806900b14000c5600280d0f00c408000e40008034181c01003411482d80424040100c08a09100d14503182c074043c4400840030003020b10014030400396103512640d00400450300c0100035640d80c401c12071410450000202c21030305058508411070411000c03100142c2118107042c0180c000c0b402290781c0c0c91038024900005c200308403800c07d01036400b9004407504c141d00034100740301c03503803040c2881c030082e201038403e811107403060301c3d81900c142c600d15840a0107a130740a00c0e624a82c912036102100c694102400e9030009080b150601120807080000021100ca04000041414070384620605094070304040c03680e081d60044028040082d80c001c103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 290255413 1250 290254163 290254201
    0xa080a05100914010203040303050a0f060f0b1803100606200616030e0d020c10020102120a020708040e0a0506030d020c010e01081e01080a0b01090c0e060904090b1003020a05030303 79
    0xc0001d0b41e00150800781c1480c040c14114150700d520010030b00c0f0525602d5040355202d2040b20209000b60000c0410030b0048464610500e60300540c1e1070310070301c0518200e10082c5101d458000d10103082440000c0020b04140c04100e000060380d60381c110410039503402402030301e0074104144030400c841c04c040f107125131140f000516020800d001d40715441c5010707000354802d12101800208036030b204156804065514228404010310548813410700c13131151441402101c11050400c002c1c0728540d01e8442d244030294101c40170448441c070f414003001c10302040c15001b8500c20000f100002c501c5081590600d810090b100744100219042540440107030b9800c601c40e00d903040d40a18003807009030303511007004807a0556802007604d002200d000001d0340b0301000070404005405403000c1549039036240b68002c00c80e040c00340d1140215900004204d414980407025141c06907029002107210034141e618129100d10440d04105064488107080c0b0546c1800c10702d00c4080d01c800d03001145542420035041142006c0d401e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 290256663 1250 290255413 290255443
    0x3050307020f030a02010e070e0114100e040507031e060501080115031811010207090507020a111c0818150732030d0b03010209130209060f040902090a080a05 69
    0x4003103080a8402c0041d041d0b59500030040c3ca0b112000781d20024041c04c00c0701881c42491041e068049401741c2c5141c0c07024121100b08080200110443e428024040704080482003400b000050103c41911103014483c820b507800d58001686101e10800411403019209410480034038101003131020340d03000074480b07040d500c2c210302e8001c07540043d040031400381410640707414511080c00084420048450003d042c2140d0903003d07280026154000301c0c1c01c8800485420300140e008100710804501990061103580b040907000c2d040000500d81904904103c4400880d000e2200017080b40e003e41c03447d140d00c400d14000b140c2410510a0192401a0710b00071340c6070180c06100020a51039010b4914404000003880301c0c10340d040c004600070b903810b4481e003000602d0400c0a007003003169000f03403a0601c01c42c1d40405c4020000300041c031481800f00001c2d0064800ea50700108200b020040e2012504090401044190405a85e4441e9801071011000083d031000766283c0c0071581d00d400040c00410040c2c4401d10074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 290257913 1250 290256663 290256667
    0x1502100513060f0507140c1f020408061f05060403240e0f0105090c090121110402040b1315090b07020315041406060f060406050d0209060412030e04060b070305 70
    0x50400381c42403285030003004004901e001c0e55010045002d402442c403030045901c2c4c590360130f018480c40b6540c6126100d015209134200c0740c070402d04021b11209a0541d4404144018246038940254628000040d1003400301d482070350401c0000742c400060b040d406054103440350f07401c2618581ea030031409081c000102c81100c10000e40320b0032040041c0c0c01201e0020b4a08100c40740d4000c006c0d08a0700803c419518100305001d12980303803100e0309004268131f04131030310b4003200c58648161104580880d590310104941040c02c0303940d50621942c582c0054809007405280c082d50b1000201601059041c0c19440810121006c40c510641c250304402e915003100c003501c9040d03550328100d10001e4100745082c400c241110950406010603c00c3c02d20400d105030b404841241c034941c641c107041064905101ca0096400f03c406c000a2000380c0c41340000d400300500c0680058200404040007400c0b54006400c02510a5441c0b4016002e140d03100c848000703035941c1a64100111401c08842d030844c0d200c0d580001e800d100c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 290259163 1250 290257913 290257921
    0x29120d050c120f04180506090c03060a030209010f0e1f03020d0501020f0d05090609010908160501090506011203080a05190b13060b03070e0f0603010509040c08032215021005 76
    0x414060b41c108074204184060382c0300e0704803040700c8964100d030240040c00c0c4000c40944442040900c1514014031000340000300c50781e14a11084942c0d0301c01844981c2046450b040080181c84052000d4041c11140c400303c00c516080c030b000f0204072a00200214034220030715155009903900030400600703594065642c6c03071010880b8202180039200e800c101c0040000001240c0401811301da0116000e040a94117607001900e0f5540024280c41c00c00701c024001030000c01c4103130424459540910011072180d030012601c2d440e552102814420241d0007105010140000350f0201540100c00c02e500800000041086080082030001c81d6184d00c518800485e07512444150581d64818140351f5155008400740042a10f0361070142c140c0d0402c0c1c07140c0340450140702085000c1e14040307080c007208030005000141503a00e010100b014944c0080c0c8152000c860540700811509801c1c0003c085200300000740341203041703841e54495403014183e444010b062090350200c003141075020625003001c00d1201d074007003400d4403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 290260413 1250 290259163 290259187
    0xd2606030a0b0c04260c012003180102011404030210020d0e0a0c0303032d0c0903020d0c0806010f030b070f020304080114060306060105040305060a020c1029120d05 72
    0x40181c00140c03090000c0c0342003000c0c2002e640014415940c4003c61703c410609140055218141c804008a0841c1c2051000340d415501c58070482004185020210440c280302c034030b40d5811580880450340d108017108401021a5809014002010071407035994961840e01703890080d00d076041d0085100f4510740008082e107104070710b0b0704403081116055050300c40641203460400e403400e070144421008242464018035012103c10005048081e00d1058940341c081200341c0c40000f419405604e009000311a600840541c4071900b045070110b1103035090303003021824145000d00d03200c0140c1c0314010b2641046414000104041038054000d401e508004070244180e071400d0b0f0035400b55400407101c0358030b0f008400c000034010b094814043c0310280c0944100d61103102c011611071203203020140c2268410300200300c4210540d0300825401c5508816502020204000c120544a4900b072168095641006105092035039000c031240280044900114998103683c035645c0b80d0120282840a00c50f0218224000f40c2c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 290261663 1250 290260413 290260423
    0x3030f04081e030403141912090c1d0a05041e020a0b0316030605040e1504050709050a0204090b010e0307090b011206151202090a090b010e030f0106080d260603 70
    0x4101907003803030700500e00d01c48060b01e0f81080b10103400007000341c40368a5000307083e40100d072285100903040181360036a0000958113a0302d044204580640c3e00c0700540007080d000200c5402400740465207068405003c40c41015519029101804c2c0301e142405020000c0c24403001007010f400c104a11000107030381ca00000c0d403080400e5010306030342440007040181080001821090381016514108052030321070341484110f030703213004449450790300c000c00324041100c40d0282c00d40d000348110100d50703080340c07180b00b0502540c10561b040c400041c1c000c1400d120300810750081c01465602880c240341d1000da2400081d81e03d0501d441100e410942e52160484140d2151401048000c07001d4024800d1680c0c400703403c0c80b169900500c800c002034908883d4204030180380202e80d051000185140b1000b400c241092000b48200c0c903049051060754144110329882c1802902340781c0002000000d007480c03401c00147d01f03140d01400d0701010090082501000205450044610405d500313140300402e03620040424508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 290262913 1250 290261663 290261677
    0x60a1211040606120e0703020607080f22051002010902130203090c041404020a060804080a050930060a0216110301110301080f070b0708030a0f0f090c1e030503030f0408 74
    0x3242c10103101152003034011030900010b24007807000304940c24025174000d032035400f01e00000350f10200030041000441d0b01603001d0941e0500903c0b4040c640440d030000c0307a51501120b0010030704103c0241082005141c104003172110250140024802d000c0c1070f500080c40c88079a80c0ca00c006465011021880b9400c080000c0030700341c88090000c206608100c1c2c18441c14600c00c6800703d02c41c0d500c403100030a50900c00c1140a00565009052908021008a0596858100d600d04c103400070014072001303008904011003030000d00c20138504003480041d042d01e0207040800c01042481d1040c010001401d50303e4251080e5505035030031011402c100084040000d015140c3c2521480b02544040001306000c40c0210704241c0e85c4541c803045450301070f502d9805d10300a0160300c42c040c1ca16281440081e82e02c11b00754125108440074000005400c00103452800111643d030501983c0c0c241191105020002e540301032445010302c0240e00c03031400c524554525650b484028151b824000d042000704041014181c00c0d034841c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 290264163 1250 290262913 290262919
    0x20a120e0d1103010609020c060a0903140412060e060601120203091603140f061302010f120c030c080a09080a05160c060509010e042708130f180203060a1211 69
    0x4503803054140700c03680b02c01d20301e051482940380440000c0c0802191003100c401e800800c0c00b034011540c51080c800c0040c0200b4000307500703104014520756640c1055030003c101903c1404003420200c90542008801c0303070b1175070022a14a6000c00c0601c4182e13a0001c00ca4100d14910300301c0917a60b0381d038003501d2786d0810000302421074900784201d50220422034030199910708040902d0444070301408400304643e8942c4255803400c0b07821180e00c0d5080c05540306003204542c3d103695081460780c940e030314400c10302118003004010b0006a030355262001010b51000c004c0741c004800b00e00500c415141303505c801c0124420f06840c8020700c8030000d5114628008034043c110025040b1602c0c03000309a950201070500c1c0c0c000080c89001510840301c400351362030144a0340031207403240070b5882204009030088860b2400040743c103840080c42400740040b40020300032403402a100d001c04c440400c070324100402d0401c000310f18020005030300500030001aa00c1300600e071780403104815500350303000c0680d04194882c89142041150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 290265413 1250 290264163 290264179
    0x60a09020f04050909030714010c0e06160f11040c020a080f0306120a05010b040c0518120f061623090904020d1a0f1528051e03070b0a020a120e 63
    0x640b800084082c18480740a00d041c4680f464140101ca822501e10ac3d0341003011425402d120040c030f080c19400f43c80c42a000c2100d2008001c11902d48113241c1800010403244191891440d44c02d50034140501a42001580024100303400c0f02c0c0e440c0e180b513028001955002103008800070b02d043d81e840e01c4004a6841c80002e0f81c103110660704105019004000e0240c2c0510f0a1040080040348180201d503401c2c86801d01e945034003810705040004140d102c04103406641f1a2161580c074541c0309100c8a401101c01c02c0c00d01d09617035540c00c4c02402960390490300400c82c0416104030b1441080c0784048520b102800c868410440d41c0d01d1002800d140c515502c00381c084a481c6038500d046010200c000e034050f1b0010002c030042541c074403c4d10079140e20410b1646070030120311043d06404800310a060540c8101c800540b00d950f58481c3d010814411803039843c0303007194091a0030741820742414030141014100070054145410139001d800781d80c81212190003802cce0b1000325030032140c1c984501d00b02d0041000c0145420303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 290266663 1250 290265413 290265421
    0x1a09030a140106030615060e0d24090b0604020703050706150902041d0a06060e010e040e1917091c05011407090f0806090c061e121608060a09020f040509 67
    0x5000f0b001c24001101d02078584045c003042081c2c6c1030f264108440041d40c414082104001c00e001108a0310302048900302c0100c1d400a1a0f408165401c003200e0002e0303080050002094188100485000340c42e20f800b0781d10400103800400c1c0c2c884104c4004c0c1e40c001c40003081174038079444072800f071f0620355001040c40f5101040116241c03a4680003ca40320310700441115003034070340c80e05a00c00c44806101d44001300f8900704101106501071403104620440060000600900302020541041755901d02c2c80c0c03134840c2c020558810415071807014031000380c0a0303d86509244910300400c250141301d18a00e10100c07808140700c01000001d42009121581c508100129030400c5003024240c540b05005044a82615071130200e042c4d03100060b613910a04041c40105005411001800810750005400885151049040d01c02a0420000505210034601c011003090320309030f40c0105081d5045030308001004140014402d482e690000c6840603268680c00041c2e403030b81c0381503800310780784180d034420b9810400c088100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 290267913 1250 290266663 290266703
    0x50712080901030506030f06160513060e090c0c0607080c160c14060304080d0203070908030414150304260d05090309010809030307050a0e0f0301021c0c0302041a09030a 74
    0xa000041070a8906003e01e80b502d500300758a50820020034a03079540560000303100a100d12000a00c0190036061251510101c0c5422401c1680290052004102c002c910080e403401c200401c0c0380d000300e514003c07504000390b00070313002d80300c0303501800c4003003000a84000718100300c55078401c65006c5404650042011340007407502d440a42c4091003408c601e459814403901050170320300100c03403145600c11282440c20041c0c2e04d2040007908040c004000f0000c10880114040380200000c01c0a003030707100b07a0f07001d8640400d42040604044030b0b43ca940d503842c081c02403200103980c00c00030300541c840b6445034529040c0745180284082c029021000c0d481070600307060005c0400e0100c000e025050702030b6903c02440d41c0c3c03041c0840d45c1c0d203c02c2c3c4007880014010030096080c14868410fa1a454100030580d40c0100c00c00c0000a0980c1c0154400594403a02d482c0c0c0c441c7c06840710b2250b408d07903070014181542403d28044140540c0c0f0000c541381e800e440303800202c0004c195010f0020700f010591250401201c0c21000c441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 290269163 1250 290267913 290267917
    0x9011209051b0103020c0601050d0c03020d110307122402191e0203040617070909050f100501020d120902030106030218090129130f020a0c0201030b0f0a050d05071208 73
    0x121011070078082c9042c0154424000c4506d1241904020b02951f440c00050010401c1004016100fa564000020006a5503080c0380c5104500510788010250811401c15041c00010740c03000c01c81c0301442d4811400544000b00d050311810910703604130340d400741c8007400c1d6000c7d120b4015419803003290700041c00c04041e0400a91700051820010380040358003440c03400d030390324800c902455010030200c7d420583c040c2c991b09032880d40850b0070f140c003409595454030344100b03035001610320001c1c03414608104509094001ca03400010b080910082c43e1008003080080c15840c0d00480d145d11203511100900c043d07450035007101000f958040d03d120121010401c800a120368140ca100070a5400d21002c0011703441d02c00754445802565210401c1d85854280800c001200000340c1ca5503c2502c1e102d002d80110464800b0382001c00d110340350440000c4161000604850040030303454440d0200c2d082d20003640d12611154802c0d25826242c0000d0b503280350600e1391800c0000d50218044411a40360002002010300c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 290270413 1250 290269163 290269183
    0x150a09020c06010905040b04140307150e0c01140307030b030c060a03140907080312061801081c02120d150305070f031a150906040e06010b1b0a170901120905 69
    0x205680309a6282c14000c42540d106403030240546000d9804103000c09e83d48805200a561103a080700d1a123221956241d10107822103031b14083e11a582d21a160b50360300d088c00100170300742c4240391540340c0c1e4024030743e603059500018100c0800c00d0350300c11550b0b0161701c08002880710000c0042a10b502c0c2c443d0380070010007a1500011240c0104417003c04500310241c001041c04c19642d1500c050340c103042100301111050500101703015401041446240c03900030300d0b52001c40c084d1104d20081c000b900b1220894030f4181c52841c0f0b4190842d4406040029000c0d001401e44803101c031740c1e09000c13410051035050351140606a400c01b40050203180c200144000364140c0f080c003100d05c250781e89069407010308a2509401c00465400c0d00b41881d0fa00350200c5e500c0d1074500e955010700300420000e402543c1003d01c520300340c426040020111000141480d85c3c0e18000701000c000320051004002e1041035031380d000030401c881220200c011001243c0311070740d0f03802881404c2100040d040100418a680c1c01e0140e03840f16210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 290271663 1250 290270413 290270437
    0x1205070e190f1d0402010e0d02040c0c05010515090f1308040801051512030d0e010f09030503240109090f1806091205091c02040b04091202010e070303080708150a0902 73
    0x1100018034281501c0701800000755814900c04039513144d03001900c1c1d10031800600c0c0e600c00a83c800707080050780c1e42d101b809549503140d80c603c40c80801070b2031322508481c4042c0020a00b0240e003840d181482c3e5400400c160f01c6002d46c05e005490f40c40701788040340f40003c1d910004006820100c0c002c1140034055104a00c06e03440d03560700e280800c4840003480301c0014400c55804042e001009450650865500200c1c52098840000a80361300c1c28440e0b1030481c0d1509400300c00140000040c003144020340c8102c1c3c1d07040e40d030f4810030b805001000c8001820710324152084007542c3d52140d107141004040790f40300ac40b09146101000010325281c0ca0000004c240c204402c841b031040d603191058100e8403031410b9a820481c0a00b03030070300384003071041c441341004200f00049234850b460b181081495155409039101c0346204070b140c0d0b14030340b46000c00603003074491988103200c09038000c240c204040b90f40409041e0700030300306040c1030303000c0c0c0c03610407258a8a031140e20095401140c07121000908044036402858090184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 290272913 1250 290271663 290271689
    0x60d02070b0405280804061b0b01141212030f2508011502060702070b0c0705060a051902030c0d120b0d080a090b130902131710060602010b011205070e19 67
    0x100b82038200c0700d1004d42c40940940c800340001e0058a000e4030908409040c2100307803260128066481d00342c0890700341c011081d0705406102020513170a000340140342d0020f09902914100030212000c1403103010041a04101d4000d1307101160070b109a9051700c0c11038002854172501100070010300541400000c2c441e498504500202c0c040d01039201040460180c1555405406003c0c03a07e400d01d02517401906024800b400380d1040052640d1790000248503602d00e40c1ca400d9210040c01c51020700c00d070b80c030f842ca14082d5041001030004406c00800d5080581e101ca0408881c0504c04509800007403103c18442a04005454026024404030b1806402108045d50301c6034242d6031038551740301b0b89000f030081f111a0350300c401c001803007400b569801501440e00c0301d00e11510810340d1402e11603c1060601c990b400c068120104903809900280120800381c0000c1c0000d11151985c0c81c00206500380e80040d84040c80d07507610101d80c1080c8140e6a40303d000703070010300709104410303101d010700001c2c885840b07400000c0c584 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 290274163 1250 290272913 290272963
    0x608070e1e13020408070807030203010b01080f0106080c1204200301090305030f04060209060a0306030c060309020d0212030f12010f120807080a03021e091003050108030405060d02070b0405 83
    0x8800e030107641c1c0c5421103106000c111605028800c0003640c0024612185800380008203501100f0001403004051280003040aa840c2d40145421038540152050410412108024803010642c045078111803007450310710b50303039501d1040b00d42c69030150400c0140c0100c600014042440b2807030001b558034408805101021007158001c1508031740100c240140031410610008980406000704075510500440d07000d85882684400100c3c2079000c2c2000781c000c40c0c0d50380c009101b070100705141c01001e0209401c003000962011b80006aa070305003200c0082c072640daa5180c4060030607040c0261100152481d0130f854840076526810724200409005040c0c0d0800348080006d40c002c14030501c030032a41d4101149519042c10358032649150f41c083ca01003c2071507002c001060f40c44405060741c20903420030030903607a05c9001402c20003400001c01e100c50010541068018000343e4008801c0f2021610115041131362620000c00c0507000c1e0142d401d000d40b02100c0d1104000a001d00401e007659143d07503c0b0f071031241c8480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 290275413 1250 290274163 290274169
    0x5090f09190f05010f12260703110102030c0403020f0f0301020a03060305010e030307170a06031505091b03030a0c060908070807031b1101080c0903010e010b01110c0f0f18010608070e 80
    0x1400d1190170311650017a1000c02c9449502e07000300c0c058600600008045911820307588014818014040f003201c1d00020700c0740c0070705134070026104840c071445000b94511300345426070b200503014030b0101911a0204402981c3d4568501660789080c2070301600035500c480018802800800c0703148010b0340c05508012060b19480701c0032048074428596626442000240d042c6070f800c0307588001b4006510b055603600c0200c08516a10300e03558210040d4500071a651810259550401c0da41e802000642058981c11030100d64012090b9500d0b44014036202c61a01010b051034400b91001503800307880e010000039107400b4444d8100040007854040d0b10760350703030281c0d080c01e5420841d0000031006c1c00c1032180b0490030a0640c450a0081e411001d00041c1c5c900340b0841c403000a00319449070a08011580d5550080d685958004c1c1c1e0a00c0300d5201600505065103240340801d0080014000c46031103890400d245000d00d07600c4103a0401c140103413410074511580c5070000500024010b844040106003c040510b040e45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 290276663 1250 290275413 290275421
    0xa020d1a040c03090b010603050903040f0e180c0a03030f02210703030e07061403060406080d02010c18050109090c02240f0f0411092e0f090507020d05090f09190f 71
    0x142d010841c10381c540c1c40c0407c210001c18019011940074082000001101680710162002401c1d800c0300c10107407414900fa04400001069418081c15017100c0b9410040c0c0d541c0021a030100c0c1c3e0541400351750159001000c900f040910130202200d98000c0d444040048082d6016081c15440f07070f00e04104290402420a40c4d0f140c4030b10800c000911582a180f00c85009034002e9038102d003014001203299621340320304034103180e02506404010f0790740d1809991802c0c0e000aa5281c1d16441308007181c1000c0c204030000300401250f014204d120b03621850014000c51003001a50f00c1241e141b021b003c00c141c09101c0800020006030ba806418507240d4020407107105a44040c0f5008039408103107150044018410b100390321000401c0082a0416590582c441040300305d04a01d00c81848580a0031481c00c0621003201441d00c2c0d0802d91800d40f82074104200950002030080b01c1008a05015480c1c52000d0000341000612050503034010a4540c01d02071602c644111012580da070701c0314280400c00603141132004031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 290277913 1250 290276663 290276681
    0x5040807080c100c050c0d030518150d09110a0b04090c021f0b1909020a0305090604050c0108100302040f021b15160c12021f05010501170a020d1a040c03 67
    0x12a43c1c4030b980312680030b00c1c80d1390311071407064055812138003a160029848070b56000d0141c010440004a400c1d00001c001c0303076503101d403a044843c80d1104081058115840c0a40b0201e4204503654070310100611490f07405a5107210f600406034000a92614500d0030150020300c65140c0480c00c4c448500c5250740085150700303c1a11508090001d090b90540b100060708480144603003102030b0410b44507010240c941000080c24800c0380140c0e448080319401021950010f20654090304a0814400090004148016130341e4003442c22038450384905280c010f6030341d010b80c8001c1d4064030f043c400003070a81e41a0090a00390f040c00c54415911003c0038070311030312002100c142d05201380880e40040c0482440e403250b40f20304100c61070003aa404007160b403031300c94140c2900d1440001d40d000040400b50303546c1401119011209810050240c1d514080002c0c1c844840c1c459a0b800c0c14071018001107c05038103134103030740b1511500001400041d00e2044080e14401ea1a50014040c41c14815150001c5000b070040c1251 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 290279163 1250 290277913 290277919
    0x80c01020319110709021b0102030426040b030708100e0402180703060f080a0c0b040f060806120a061d0123060301060305070927080d15090c05040807080c 68
    0xc0c00d814585032000804241402d1030a100c0468200c00d40c02c4020000c1901038100814010794034040c0c6801c0d040421f0401030b0b1a00c03140e0040003001f002640014000180710710030544100703440480030004019008580201c0307442c0b00c01100304111130340d0000420f0b0240c0c0e8000e00507034106407903655598006038111400fa4024050080c50b2401e003074103c0d500d1382d124a59203000100f240d142d4000f50480d4546510804c000c3e44407040403002d010b4224511402040003442c0245001d19210a20070b44021a2040d41c040c001000b001401985841072618102c008e00804ea130020380c00352034010000c2150b9581d41c03203185000411059852014412000700c00b140000c2c116249441400640c0790003801042e85406540399040040010800c00501c07020382011040440c0300340f0032103540c01080c11642204145030a240c001f400100b89000212000300405070310200300489080341c090a480326035030000305554580102c51401d40d900c42d001c0c00c16036004c481599035403907440f0010f41d5100005100c4681c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 290280413 1250 290279163 290279167
    0x9050612100b07030804110913030309111201020d140c04051c080703020d140f090603060a03080a020705130203040201091502070305060f06210318130504050a0309080c010203 77
    0x1003040610210268000401c0204000707081d21080c0c0311441d5000900214042034000e02072004001c20480742528150703007910030044a141208001c642c504a6100140c141982d82071044284a55040c1c020070f01803010f40082544481c0d18540350003540010060003100740307403425000c8072012056000340503c00d000707851801e103400c2c0750070040860124201b00003020703132400007000090400c0000c1c0c000303e802500900000940d1407009000c91045900b00c0141e00000c0010400c91a82c0005480580c203080d0307440c503207983d641d002245840405420140ca80c60003c140f409240fa8001038500039660181da001905040000844080c0c3c0815107001303011402c1c000042c009404840d444446c01c00462040354601035484e1645801c1210980e5812500080c2408001c2c10f4180f2501d485940303003000c40920b011444811065859024210a0084a080405c2d9000e043d0761054080143c2e060b1024003080141040e01d017051791401e840a085003c100408000204001c0200c1c1c0c05103180010b801a40c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 290281663 1250 290280413 290280427
    0x140325020a0c05060a1106070203090102071e03060b0d050f0f100501030812130812100e091c0908061515030702030a030221100303120e030d0f1b090f06090506 70
    0x110580d00176400400401041004541e021082040342c6405808150082c584e46c0248500090904565801c0b10f651800501c6007210031841c1052550200c9402c05000104e440b50580019200c60f07186901030300c2071052194215141c0004140384a900f40c81000311100e40a03100480d005036030003440043c0540340180b2100c0395020031030a03440c1e80100b840d0b6864500e080b40703907180703100e0b17400840b07400380103914010030020b040c04901070300c0d4003400950208003800e14001960b10350340d140046ea5001800480410301c1e8102d0b00440750300001c1c10700c46003514254a40300c100d020091000f100024441d1001a54030f80c050040601183d0158800754045c1d07182c0b4910440a80281d8400740300122661054195244030006000c034090103804058003050000c1c1c9541002025921032654007031031180381c10a010a890780010480c0c000140c0701802203611070b6008100c0c030080c4001c080c0b40d001e154411941d850450760140c4100191001b132540c1a5465032910001c968031645401001e4004000300100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 290282913 1250 290281663 290281669
    0x6020c1f050702190603180b0a0e10021b06010501030b060301120305040302040c020109060b0a052b06020c0d090f060c080c011d0c040b04140103030f140325020a0c05 73
    0x95404403005090941c40e003003103036002c510052a80c0f84c1c441c041040c0791405220b080e0307041c010302403400002c070818506003125840c1c030804020050704441c5800d54504050803081024000310319008004d54085440d00c0304207445403a90780040f15040a44d0046000110325580a44100b10001c5c8004e4040c9085a09104000e595031400c04c105505200d0103010000c01607481e0300604443c02c0c0b0310307800402c0001d2107250900c02c2e100c1010300c0c1441a001c007441071160352100e82e0405018441d0848681203001d0559080d05124100b0b40003034840c0f0700000b80c020000000250180105090703a9403400f1407a5191110042590f041c0550310018801131590f0b03003c6840f0704082c0c80f072a442040001216400d4101080c0c4c80e0588640c0c1d42d280790442180354001e0701d068440c0205420b0705903400d002d2058519080590004140001030a0005403514840e210348540204890955000c4a0301d41d242801403440000f0300d90101000000440e0307481c102c586900c003003880440c3c00d9010a0b420000e500345020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 290284163 1250 290282913 290282959
    0x8210406200d110c010908060a0f02131e09091a060f12010f06210b07020a050d0c060606030e06041101170414010b09010e0a0c09120c0f06020c 63
    0x3141c410701c60028000703001a1000e01c10b040740e81486880f4031030103149150b0102e062680746038450f4140800c040c03081040d1000400d44a40c40207a91600103030900c07021002400a0183d00440c49500708403080100d4200d150a415201240052200586007641c07910450149c54010070300400c5884000549264510140220368000d10700500b00c40b81c0300341c0c10000c81c40300040344c070044007107a44507511141c4c105d145210f071001621841c414154001d03c42c8031070320000400640010030400302d01c0300081d544d6209001c4010030a074800f044d103140d03640070080200a07400070602541c030030f8035004c800200c8500074890414040b00d51406010030b5510340e11400c50a001c0c00e0012411701642010b03080d4411a0316080c58859071040c0d0003a40302110700200607084030340136800c0318001e2034007400600900440d81c201d541c0c0108901c07004510502c0c907071012913990030030b644010340c4030047c03032800d40400601c09088000d80780c0b148d5220701103032f550702c00499407856107201030f6800140201c6c0c82044102071450b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 290285413 1250 290284163 290284187
    0x603032502060d020a080a050109112712010204030201030b060403030c1101051e0301031a04030909110f0403150e120708070c12050a0302010510140415030b09030408210406 76
    0x2d81010302c0e01c440031041c0d034001502c070700002c0c89040030000c400c0c00350701c00c1070f01400c0085000c100003205022840820321500ca03101001e6196100816032190920007028441000a005040000e658107a240d001c0d40150008a0119060403207281050615205460450342c2568445000c1070103a1901078036205224900350404c0300411000c0b6500795440d0800e0081d000120605969600d541000c0c041e102c80410040b001081c4001070001090340101c1000c250741b8924400202c0304003410980c4600d100b00c9a0482500d20f011400206116040d640743c04a4803200e802802600030b000441900c420b0700c00010390484405124200105000e8006400c00ea031056801060464030383c1d20305990719500c1c0398202e0300ba900840041c001c1580c203016071900002004002d1694600b001c0689202c002030806490040d42c2c2c45000b0421202a940510004c640056509149044c02244a0f480758001d004400036886440c015802451404444010795102d2508990606082c02f00842c1c4003d5440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 290286663 1250 290285413 290285419
    0x1205120a1806021801090506040b0f030a1808030708090c0a06031a031504030f090602211c020d0c020c030d030c02120c07030c05042a1b0c050301050603032502 70
    0x1841c010000b031840e20040400a541080d41010304502c0400141107005580100340203203020b10003048410421004d440101a02c40c80d510303100d6031500c2441000f8052072406a04070a8100010010300c000ca800643c0507a05a07580e0b40c100da550004600d648250b090703050b980202c10b24004100c0035110341d000d8810a600e0b400a170b51400208800646406000841980b002c28510180010143c11541000c008a054200f2001c081e1511001070344070f400c80501c1c0c1d050200721511441c5500011030842d5421951001c000c039802000501d904000d400161022094601d04400e00442ca0b0000609688040d4010020020500104000c4018000201010041d407280a400c0d259202d00c02c401740400f401f050740140210780c61810003682e21189540418003a034540b402000300c4100182c8084103044d5062034503200101c80c00d03001c07034144490901d0064100340d48060039080050722903990302140c104030000e02c902d8075400d0405440f0f100b035004405000d85001243d40d0070503201c0e40e58001c518001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 290287769 1106 290286663 290286701
    0x601081606020a0b0c0705030c010c0e0a050a090e011b030b030c01030e030a080c0405060c010b03011103241f021507020c130506040e0f07031205120a 66
    0x54803014018545000008600c41c121704202d48000340e10000300d0750b42d041818912402400d140c6440c00000368a5410401075140030b560200a550004008404041c68070206400030581d100c0c1805480d5264182100f81000c0c0821443c0800c500791004158035400c6000c2600380208800c0444c1458078000d0305801d0076400000381c880c908050708180320076450341c0c100d03203003180910390201e51300c00000580c101072403506411984c424031003540244005070103450112803e0004a035481388024600c0c0488600c012072140480742d030140502080001004144566200c3c3c1c4007440c52009a40402680c000702c1c0703c5100015480307419031001c1c10b01069040b0005400c0078005e8102c085172078462010404580e140e0703110040d550380400442c0c1c0303100480e4681da07440740071a110940b0460500a2941801d9024000b00c8980c884200703040038a90351842c21203801450030301100c8558404e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 290107913 290287769 := by
  have h0 := BRFrame.cov_init 290107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 290107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 290107913 ≤ n) (h2 : n < 290287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
