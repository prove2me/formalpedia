-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0850
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:09:07.745663+00:00
-- url     : https://prove2.me/submissions/64a28f83-955e-4362-b10d-56163facc94d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 152697841 ≤ n < 152877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 152699091 1250 152697841 152697869
    0x80a05041109060604050406080a0c1401022503230c03010b010f0305040f06060305330705071b0b0d0b04050f1906080d050c010e060402130c09050607030531 69
    0x41c54135010152001404000d00512840382c1c3e492105d81c84520000042d107070413640c0303403004c90b02d0090010340d0000c42e00c040c4e0040c0192504030040c9203d8260804d642e81c400d0390f03105000004070f02c3d015410341040f414802c9031100c00c01d410807a6841c1043d00d20080e070081e41810340c02126680c00081c040c001040c1428045140d80d200d1a110081944813200104203501c0d202c004414404005941b8102024002020166a0400c003e0003c1514903d20f410812100305000850340e910820180c02d24078410f440c1d10240e8501c1040d90250302407075800c000080c00c4041481203040320b9900910401e01c0d0b01f80c5c2c0400c00b500340418070810000c001010908401009509071f111203a03941d00080c001c0c0001c4c000c1e1595200100d10091455111040da07944070b60800d44e20810980011950500070360b801440c2c42c0c01d14060081384400f40040c2c114202c00e00103500c3c40040d86490391401000d40304c0c820350380c072980c9900340d501c054034486003402c10141d48440d01c000c0c401c40c94030031240c020030b652100c060352103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 152700341 1250 152699091 152699101
    0x9171507030c021c091d01050a0902210106112406063114030609070618030203070f0f150801030312110706050a06150206060607060b031c080a05041109 67
    0x210307115415046111030b90b03c030113250412990100001c4c09450300180001040c1000c1002521460820302500340c0c0305001d41d4080050038280e50040509240c001c1d55614522040b42c50403500180990000d00800d0700b10800c45500f0380140b0090b800340d22a180c603000d403080c0702c000d803d00788040108441d00407500000c441c48000201400520320f800c0701030319400305038400504004203a8051007001040c81c85901c440070285408692244140720750002854014074044e411100507040003100300d102a1111800b1001d41c40510030000908840001441d04500c1c00c9254043c10b4042c2e8891100342454280402c0c46a510010441c11a50589403074254024890380400c002c010f0310582003140f00000800b02c0400800750440c500c40ca112000801603103607114005607400010440c00c40050300181e00044080c40c1170340260030b0182c041c0328000344c0f81c11342001192604c0c840807074101120007180204a64250b00c01d50301c03680880741319418001410702e9600e0a50f10590300000f642304a95100c0024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 152701591 1250 152700341 152700343
    0x905090307051b030a02030d031a040209060d050403090803041d060f010801060e0114041e0506091003091e050a05011a100c03140301120201030b03160506070302010207020d0309171507030c02 84
    0x1344586c005040e50500c604101c40a00240b030712041a64540100d01d890711420f00c0c00b8401d40380d50381000303850b040c03034484680c1d50306004007401041103050080410011854a03002c002420217042c403250140340c00c1e265034519020b0004000d14092041c42c2d0078003a9046a6032200500b411660642402c03a603503e080001680e00007482c502c0d10b802c9600101e000500b100c0000441d55032140c2c1d469001c0d00c0381d0380b02c07014091144a0a40020b420039040c1015441c0144660b100310110741c007a1840c81c141d0748034414200002000070800b907506074040b85143c0b081c00402c2c0708240410044014003a060080c104c00700f1070000414800d1014000f10040500c207250007001c1140040d480034a00c5940d17507841c0c5211240180c851403042c0c0c0041d1038580344901e1818001580c00700f405070aa02a6032540ca02001c0000c0340e0312046003181155003e00a00d40162649440c04602e544a0f45550740c00c14106030754000b84000480ba01e2107540e00052032001401004200150041844d2a0226031060318020513 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 152702841 1250 152701591 152701603
    0x80a030804141b1309081c0905031306090801020304021c1109100602160506030604090206121e09011a0609011812140a0503300406060905090307051b03 67
    0x501c070b40c000d1015a83c0107540c01c880d402c5049104440f1101c9a4184042c0d6a0481c0e40784600244a10000c03c0415168032203007113041c0c2415299080440c03801031642e07910b41150020b140e000f880c0f003a4400d0034061503800211001c054200d0070021401e5113007a0300010034118525400d445030660820101c81808103100304490f40c004003400e5a041c07400c14804c01b0307510080c035108807401406504008030720076440000400c00c0340d90041a50341075072201000c020042510701000c90b4044000c10184401c0038030840b14070301c00c1071342509507170440d000c071400030181700f1000300065101c1c2d160030001c1042d2007188011088024080d110749840d0401400103851844205001c0390500b0300d00c403800202004400c0c00c2c4d84003207200e040c942000001c02c04800e99104207034603000301290018007000d0b404c030f100c03071800c08448604003503046454103012013000403070102a03805984003901c50344113100110050280300c0d0000c00b00000ac41c50801151240c3c1e4603104542c120f4000301031142a40400c6980c10055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 152704091 1250 152702841 152702873
    0xb010c060e0f1e061803130807030213050606070f02060d020d150815010303120f0e0c090105030c010e0909010e0d05071101050a090314010608070b090a0f080a030804 73
    0x304405401c0c04078203a81d503001c03090b21803614480c400d480c072221040301d00e0016010b1907810003000f06480344081010800c000d14281d16141c0b1040c01000c80050101044100401c6081c001d454141c0c15801442280c0c0880e4140c00d80107400d000500995850301412505640e4100c8103804249c99203100142a6104200c1c2c2d0882d02400031a800c098181a50300906100c10403103a00381020755100c0140340c54021041481c9004c0c4056401000424003482e01309000050304c0174000340c213016070b0059000701d90302d0340100c07845a80840003000c402e080c01c500484c054a0101c00603d481c441000c00208030704031922459000d10800c0d000b146c8940000d4000104d265000001d0382d0030402d68201c0102507410030182034034103101b0391009280300d5000b8002c8031300020161703560394a07407411512030031071042505140591940d610a400215040107000c040080c000c0f01142c1580c0311060002c03c07102e81c165800c0b0b5400c54400c4001004111800180f01410561500b0310900a13038071414100341190600c60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 152705341 1250 152704091 152704103
    0x312110c0303190809060606040608090715050403021003050f01090e0705030d110d1b0b04020d0b0f0118050105060d0507090b07050304170c0907030506060c030f0409050105100507060b010c 83
    0x40c0241c00344601c0d4841883c8440640d00d0390036954401c15015541c0c0400c3d80c420f13800c803c04102c1880113a103e90030450740f05c1048812550410742c0d628050800106000540c4c000410205041c42103280c51215200242a01c0c0307010b001c1c1d03040c060703281c42d444030061040c0100310350754582d400805041440b0307070001008010292240b0412084000d005641c514060440e01e006131040c0c913003898080e418076220f0030b18000c10980c1c020789994410a1800d0040c0090344d101d603511000500040c40c1100580c880c2404194004040d49041e60f0069090150504142d0040c10080103219580701c0200707461681060000102d21610703901c1c01070b0b030310100b0703034120303506c00c02e0009210418000000010700c00c580d0080143e041520740144903a03222550050300d00da01c00b60150109070020301c00c0e0081501b250004100c00d00d000710046803140385510601441c9d9240703401003420011a00c40c1c0c40341a00411040d41d20802d50300010100900510448000800070317581e0b030281034066445400e00044c030310742c800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 152706591 1250 152705341 152705347
    0xd080612011109010306120308040206070c21020901050a0b031f2402160524090607030908010c050304051e0115090915060b0a0516022d0405010312110c0303 69
    0x400c100a50f58007840e40c2c00d001ca4200b8030f0000d00d01c43d00c0d03100a0381c1c1d00e816544070807194071030b5804c200c0d103948135a01c1604c0c0300b69160004103103131103070040d02c50700b4401c10607008141c50300510612400100c140d001c41d00c958054a4208810002402220303801106022021b0003041c030140111071080040d04800d01200e0000c3d400318880104000301c40708101150220303000220320002092681649020301a0481c2d00b0001c51804208080302d040b58a1400c00e01c510305042208011818a4005620540016960001c03c0002241c00e2007106a805258500a451843c0540303c040e03440500e001c60007500c0216928040c2d0080b400c2d400310b01d01d00d07646a000006103940f41500c1028000300001503500c00302c001101040100d55100d1041291024514107050014024041d9542d401032641c811039900140c04050059503140241d00d0400b1442d81a450420300c986040c2a1001111102c640118070703110040c40890503440048043c80c01a1034580c600301c2111004a00301081c000700181c01d88804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 152707841 1250 152706591 152706611
    0x20702041b050309010e010506010c02010507210c02130e0307080a11060406090b06040603030e010c110d0614090a080d0c02030706110301060f1b080f1902010b09060f030d08061201 79
    0x480b00550003040303950001d0085000f000500ba0072988140c6041c5e000c944000c000700c1c0154069030141070014040c0c1c003007102d107c103010745000501c103c071107512001944100310042103140c040914071004a12010401c0580c00801c40701e0341d01c1c800c501d0040c0105101107000302d00e65214000916182c1c66080c152107590419107001405000130301c0c021281121500002819400d16214200459030140c3c0c2e000009065140151800c54880c10255070041c04004030030340e01c2d140c0780c02156040e80f007241c0029054201801040910314094242c0c00e2a401100c1d0300000301e440541900c0c0260f46401002a01a221b140203034698072807050010001c904000401282c02442c401442c100c84058855004464021104031070702c40750103c40382d42c8010445450008100d880d40038064850a8a400c0e518050062200202000f4220007107001070303460f40d02c98065030808030006500004251003a590f2151080c0c00251035900718038500c02085903001c0001c5507942c4000103a00d09001000c02044840b2003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 152709091 1250 152707841 152707847
    0xa050105073e0306100e07140313051207080702091009180c0b091305070c0813090c0503090604030f0216030303050108060106020d02070b1c0e010906050903030118020702041b 77
    0x100703609411800c2c848048840743d00300450b8607440781844000d22074066044c0228003003800c01c060080c0c020000b102e02800742140034200114001c190421a40d9000403461510503c0d000c44103030310002c1a041030042c2000200e0500650f07200380d5040740c0c00840e81d582c1c040d468005001039801000450300f4040c09189a420940800d8039081c0601f4424480359151050740585200d0111b080d070b000b0b000f071010099040c1c150391250750891620320340003041c2c42071a100d0514680091100e400030584000007008100140d220300d500b460f1640c00c1403800c6141200c1d0594840350014005414041d407484401da02606c24010486180301c04a1541e040c1d640301c1c240140104424059143c26216200c0040307101400041d03c59104051980100000c90800d0155501e68100b032209620010713003600c0481c01c00c03695002d009030249101f0300004501d05181401816240c000d00b04ca000c80d0000c1006005592941504260087c0010b01c0941c1e503440700c0c4003040c01420014006a001080e4450080b1001d42c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 152710341 1250 152709091 152709173
    0x7060e0a0b0c090a06081918050f0312090a02010f0e0d080301140f2b030509041e200406030c050c06010f060809030c0607080901020705070e0117060103020a05010507 73
    0x10203803000007104e501c0d4801600c24084c16101c880c00380d030942ca80d0b05a03c045a0700214000d001d20b4408400c2c0300e1403581d50703a24040100e5220038058001040100c0d8440090610660040050300101581c00342e03500041c1888040e0b8451504011344482403c4007902c03000c510513111a441035066035251380d100384400081c41680c1225119400e10307001703071115280004010103041b4407183e040c2031030300481c00810b000d951401812020300409000412241e5a14401c3c403990901d5011007100e045083d45110041703d4404004000c088042c40484400301003010555040d136182e0300b00021046001d10301a00d407401114002203161141c0301c0007147d074030740c1090550b08860b0a40c90b41d081035201c1401e440c0d240e019042d0101c036a1303444140010401881501c0700da03040700c0d007500014601600c0f511818146a55038100d02040180c00004114140c60b544003101d840740d9510280685506603400078200e00498803940e4100700011441100b80308a100c50040251a042d20364429003540b2020304403842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 152711591 1250 152710341 152710357
    0x8010b041a0906040e12071a0105101e051308030d06060c0f02010309020d0b040f0212030a0206062b050d0305100501020d08190603031701170307060e0a0b0c 69
    0x140c10264160701e19403039451950340381039000302074250719a143d0050100401c1c6102481c0d00c684103009000d852000380d04c00410712280a4800c00b06d0100300b0f00703009094400184e00c11809500300280607282c00ba8014149040513000d0451a00103010300b440841e100d000e801c100301c401100d007180000f500e01000001301000b00c0702140602210355180800e0b07402c2050b811010b003031011480b6440d4015803203548800c90b500e00c014014185441c2079154000c040000b210300300c401c2d5882c05004000d5103044408100c2c0c2050b101c00840c941012440000d4039400c0241407036004000484000000c01c01d6008480d8640f800d81d40c1c2c8034000a0a4202290f40d91b01140300080032a1a00001c6070301001c2e042185403e03190113070002c14a00021500440e91900d000f0007464448110414901344a4001d0080074000c41c041d80e07d0300000903520400844192060384004802400342c0c002c00741103140030059400c1c45400180026088800444160414029201c000d1101d0155010040c2c9080c640c00035014803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 152712841 1250 152711591 152711599
    0x1201090b0a11070602090406090501080f0c040e0c0f03030405030d0f08010b18060901030615030e0c040203010e070503090718050106020c090601021f0608010603030c120219020108180708010b 84
    0x1601d0304900181100c1030000849010401003080c00041501d039002031807600f074050400100a1390740c1040300115442a00040125002000303c846541c104000241028000325070404c5882c01d10b40e036240d07588480150003801a084400c50b400c07560740910644005240c054240c13415144c80074402003104c0412010000424000c44c008980c0c2000103094a45c945d1807904598160748019040180c0d91300111001410191509000b040500c9010304480940c0481c3e02c0114801400c440344904102d1a0341035940558414401002841845220700342c101c201410312944c2da0b168a9551800e0681681214400800510130180c0d1181e459100c44c0c101d4405509880720510004200480c149003600e040740103a1044da00000810b50041e0301d02e10402d141c40340021466682d61085003900e00c50340c000d8012500c00380040d401d01c103898542c0c1e00344070700510150001500ba0244500280c5010b40040c5c100301402e4000f4260b21040d103040d0029000610807144c459070b6594825018108a080060203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 152714091 1250 152712841 152712863
    0x90106050108011217090f10120f02030f04020f010203210115030e07060e01020a02030604050d1e211d060405010e030909061014040f0f050604050303090405040c05120109 75
    0x741144d0780210380441e5120303155a0000101c4602240700790070058400d60700c03d45031080ea84041e543c111280e081c024a5480e40f08216450f48a108103c0b42c03040301e045000c0d8010000c00c521400c800c0f201981c841c0d41282d130040c0594107600101d10318015102250010310000c00f10000840b403168203281200c0c0e900481c05c40d00990000103d050318154412000180d1044106100007401a80b29001507807040c0b048503910411500000d02d07014041c0d50030340d6140c02445110720444d43c00350724400740c502114052000704005e01c03401004840c01c0d0398440e114810724000322100c243c0e1a046000281c0402c601138268501103900f551b120101510111502d45c601640f81ca007000d804000d5074000f14009103545066601d43c0c081c4014a203400d2051410040340780707401c260701c0b1100400b90010705040305d07601c8101814403d41005800e415086248240001d010070041560004201ca0081e036040c0d401141c40c0e111468802141c50380b030303004181c0c0a0380801c00ca5800000550001403030b0b0340181d0006075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 152715341 1250 152714091 152714099
    0x3080d0902030106050d080a030515031f1a100e0409020d060203180610050d0204021e070302010c090f06210507020102180a1208070507051003091203060f090b0402070b09010605010801 81
    0x800f1610301b04004002240c240124170002d4040e81c0b02a41c0240c5d0044e0606144c010070001904003045400031402c200d6800507403070440c0030300380715102510082600d003421080c800d00000b4240000f014050040051040501b07103d030301d65421500e041507010b4500701d052011442c280c400b0307400440b60340b5215191041003060311a130018071180241c400b10564140c00707040c04240440c040100a0984c1c1041d002c004d00380c1ca000318404000c0024500809454030b031034451030b00070300f03403540101600304001400c0b0b0148038880c04980c03200215500d50034160640c1c0301e2860440555080c03a460306905903d03000c00c004540c1c1d010f400520924148000e64282c001000040100c054214024020304810a10344040082d61543c010309005020700b003103456007a69078002883d401c0c14510120002a201c01e074910030807500803c11800c1000038102480441e080501c40b0266a0765031107160300c0542c90f032580c4080e503126a41101c2d260758202900b20824078001c83d005001e001103120b140d0014aa1100002d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 152716591 1250 152715341 152715349
    0x60c061406090a0b12030403060b0a0906080d030914070902030a0b0904050d0f1e050a0809012a03020408010f0603050f060c030705030a180c030302060108010c120c020703080d090203010605 83
    0x6845614000c0140d0120f4588800e410018800c1e54111034008008020600322000100090300042d03100e000c0c0451140c10034420300140304c400780e10150803282000c005010468020030341d40d0101c2c0840c5000104001c3c00c5c141030880004110400895005460000c80c100c641900210f1042420303401c140303c2c0c001c40310305000300144110350241481e04115804144284100d40000106070545403a01a80c208609040001441d144046000c20030004d0408040c80d00901d07200d44c001c24420081245010a802403142c2940e084054808030641c0060200340394025030548000e044508020801c80340d0307045080008010a000c2982c2c140300c0c10004901d0701400244c2c0707500c04e403040c1c15a1811510790b89415501d80c1c10140002180c0c68903044540100000e511011140900170060480000d103076050103410b00074103802120042e410b00c1508503050740c10000100404132001c0000a20351044e813000c85c100444e5800080c124600081c008440b04a9508a2440c0b180210002c00850344d03a00204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 152717841 1250 152716591 152716631
    0x610050a0e01051513060e1804050d1202040902040e150402070206040e04080f0c06330d050f030f0a090501080f01180b090702070f0b030105031c090b04060c06 70
    0x25400d400d5041e0010b00140c2410495901205150104641030500794105480300100e140c02000000c2c1c3c04040c0e20341d09180c0701403041c2ca10b10000c84e021040703081549800d070f103880100d10600f041c407026104486000310b15504a0700106110401191559101c24006200003810b84148400340c22444401440380792038403c0f51303803441d80144103a20306807429540c01c049680040060b07070b62100c184821500405035000030454410a28080d0410303107416020a1202d034032146108031025203e0811034039000c0090411482c140c01158503c110010300c2ca4060f107030855580419a080c0008100c0c094101c0390f104c05011007107080d407954500d41c0c0c2c8800045800034000c03074409510004441c0104561508040215100504104d0102c0c9401c05030700440d0356200241c1d15100164012003080007100c0040c0c500e00040c18512039864a035500d050002903030360541a10940c51f40d10003110f05c0d00018010b882c0f4900605004000541b110ba46200140c410000c51034255001800c000080c80c2174941c039040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 152719091 1250 152717841 152717849
    0xe27010e1203101e05030105040b060112060303050901030b0319110109080f100b060c01140109110403020609100c14010501030b060316060e030309090a0603030e1c0611040909050610050a 82
    0x58150302840d00001c09000790304403081c0b541c1d004130342c5000f0945480a01900703100340d01a20030300c0310303030f007054400101025009610050b029180040034800039912004490503094240381c0400c0054074680028101140301d40c3c03c6c40d400e0704950000041180480e0600346c14082601c812408a5031240d0241e1525145070282803140c1142802c59407041156000d003482041c080c3c041070070807030065003043c01c65160031030a156054020740100150070700750242005a08031490002c2c2018078542c0810240e0050002180c4030314642c040032074813188540d040c018410340140300c80c44400003100b100c50080500f0b000070383d031122505000400302d0400146182c2001c0020840c0741031f0b02d207000000c0f100300d0504448a039140c0410044202d0701d540d40c0200701e0107501503207000100341d80346107406450103c0f5059400e01a031640901c94607083c07a82004e244901e07402040101e0250b20521000090340b140d600100c005038540f40d92001031020000e01c09100d0940700c0c440c0c0000584072000c200200f0781600c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152720341 1250 152719091 152719111
    0x1021501030b0c030c040b0a211404060207110d06050a0b0a0803090d0c090e01060906151b08040e09010b04060b040b0f090316080f0d14040e27010e1203 67
    0x4045000f0500a00045074060b680a90345d50a00da1a685415203d070302001604000a540ca20040c000142801c0071705043c81c841c20080148138840446110750480081002c0e101603170100f071034410300c030980722650307c0088000c11400b201e407030034584540140b00c00d42d024601e03240380c0514840503040240905c4140d03151a00254248007403d01000900702800038100c6007101d203440700060f01d1089002d2400c20841c8030001155141c1084811000c1385e0740c40d80805c4e4041e905400c41e94141d81c00480c0061000811074900e802c0049509001186120380d52011190b20109800c0004209040d44818078003c811101880880d5862624810038052400b071100600d20804c000812114124010703d03204401906030340540303103034003402800d070303004c9074481c2d42e591f084240f24908041c000c0c880d80c110b051030b41c1441182c15000c0064280c0d03501841c0140d405958134040402e40011024014500280d220480204071039541c0c0b5070103010700300c82c0804982a210301d6562619a22502d02584d00c6401054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152721591 1250 152720341 152720363
    0x70b060a181a041803080a14010510211a010903030206061002070e070503010807060f0c0f0302010b1509100503040f02281d0112020d0b0a060f0e01050102150103 71
    0x54200104401090103a140e002c2c2c808200007600d45000d400b214522128000050407854100a01016402403c0809640c5426411200d440a40c1d61840c1584c03000d481140940b91161b20035200c4001c4c0c11200359810a40a802c01c0a02040390440e94403a0941415000301662000043d108990f26010080140e0000c200141050410505070030b061f212900c1110b800039901c0f1840c42d0000c60aa50113800114008018810300000b002400d00416282c60004040380403520f00a20b122080c0b58010245482e1501030020305100b5003000b03140c0d00d401410202c0717240119401075100d80c000c0300c0c114022500c40d01c0010345140a1000c1d070780706c0e43e00b184684410701556420811408011800361189041d003485184140741c50152a0001d421602582c3c0b80700c284030480881c1c540c40c142d00035041800c0d940401001030b210887c20111075940403110030ba02d92101c4d00c03040d000e460207400104201d80124130014140d6200b48005040f98400c7e02500c2c00d00840d12030144680d0720074080504402d05c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152722841 1250 152721591 152721629
    0xa020a0303050a090c08010c0e010f2102090915010806040908091005040803070507060201051521120a020114060a0302091b090a0e190e070b130e0408070b060a 70
    0x381c00042d4440303c003260005540d81141d03154525800560003040e466036642440c4040c1300d070040581182d00c142402d20301500842c06600900a406980d5041c00156010b075003600105210740584003500c100600d40c0400c0d1a02c03048241119802c0703a80310b400580c100c8041462400c0c01d00c2841c01158100b9000c0d0b14050626050060940c00c07510f06604000003000005400c40d424009494124800d00180c180729142841c02800c2d1807019114030140c080154100c0040d5450fa00d400311302c906641c2d41a00d80e50507201086007801c8010359020300d10180000e02c2a41d580d0b0641c030400c28401c44142c01881516030303405001212480d4040250030150701d2000c1401c01c4c4600c005810982640d000300751814503100e02040440d0201e6101520101c01c03c0140f0a511070003600f03901c06682c00a0040106c94403603003d05584246c507116140b484030001450b14000c8220b490b0a40140c04110400400c07410030707180003806644941d400341e6002c241a400b1a0307103803030108444c108580009244401003218 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152724091 1250 152722841 152722847
    0x50f040902070212060106110106090501150c030905120a03030f0e03072d060204060809060403020705041107022709030703020c1309050604060209041401290c0f0a15020a020a03 78
    0x250b0b001d0f40e112080b8482c82000c1c410800890b40640041ea90340b42c92a00d84150326405d503200340e00041d500e18117010061021302c03500c40c4030203a403401c2841e00da0600d680c1400c0a0321861603940207150415031074450f10940850026008070303400c0c4682c0d4104101c40505448004588004154607010f4104000900102d6217411012800440800010f42500c1044603144440c5410140446201c1c2c0c0115040004981000b001ca134080d80c00400f80a01340381c240d400075201e034030f01c0c001e6070b2180350b45007012100d506003c2c05644d0030070345c040d01c424807500c500c001d40b0072500301c201c41c100c00e0410b402d40000c560400c080260b940303051713040d00103060711250082002011103031502150005503445409801140b17042203524000c134003c210041e681c03a0501b09000940d42d0070405141c94549140040003107080c0c684401040c4d010751a26004203200ca041c481c2c900c0d10524902030010300c2280700100c41e0180c0070400404040c8102148800304580b8220141a03004020544000d41c00402c410030100f40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152725341 1250 152724091 152724097
    0x417030403051201030c0314062a07170c0c1002031c0f0c0e1003060b03010b0a0c0f110901091a090403030f020a0302030a0f0b090c0c1005190c050f040902 68
    0x700c282003980c202000c0c0051881c07401c209038000d40d0001101c60b010018802910b400c2180e004c07401b00503107500d103005100280314024400e070440c0d14071120785880105007510015500301e65446648402002081c1c0d82419240c0c1101c5801902c1d409400300714403081c40c1c84a07101201100d107030041c5089c06507070785680001c1c0d0141024500259107a00c062003030301e034051140d100c3e0000141c46c0d54035624803000c02c1c0032000d0807640e8080d0078946403c00510180e049801500c2c1191a802da0316035aa80c0049411100034000810040c40007021455600410100d000c40e0b0130101000d8a40701d140760b0382d4007001000c2c0c54035890040b00c0d5007aa420704180608010300c4055009000b406c2c0401c1100071a1a090100d9200c1061200000d40c04001c0c00103210003801a00c050780b4041e80305104c0b0076a000005000c5035009020814180d0b40019441419a000d0210107408403641c04100708600d8161205030070300110255150b210b80c582168085198016400d40f03080e00000d81d0343c0c4d4141420820660020343c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152726591 1250 152725341 152725343
    0x1b09031f1a1804050a0b07030c030e0c0105070b0c04030c0f1d0c07110102120a090501080a0c050a0f0e040c0807020c01080103050705060903100e0a020307080c060f09061b1b030604170304 82
    0x20041c169954041341c2e06d80e00080c01800f1541c4c1c000303260049400001d085070030314034402040f03404c0f04070400b185030f078488181c9017010b4000c081440303207031030300401960540701d941e0005104040003a0002108000d50700c4d540200d0740811041703c0500c2a9a9080e40343c1e000448409591003401e12880000c140d10004040d040c20060044a00ca1124032201e820b59810000000d400104910400e00065034041c43d80358002074003100510903080004805852802101081c1040110368601c003141144208a50141c090000d0010402c02004440c014000130b002c440c007602500c03a40f2803e091030b501ca034160754120782d00032002e022118103007010004140d000d00303401c81d41072089009035a03a04a80f441030140a419680c0204800c2410748145402c01201d50b00c508141c1d00658001c01290302c0d40c200b220701c0400800000741ea6450303850001440e0380105600640d01010118032070648900000b0348403046c1c0d0441c50340d00c0c40c40c080d000800d951000c0484004100c0a854195148004640b0015542003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152727841 1250 152726591 152726593
    0x6090102040e2d040b090c090c0d270c031a0906010608070e0301051305070b0c030906031008010f050402040501051005041a091503010e0703060e1b09031f1a180405 72
    0x18201032881005080f0b01950143c0700038a8403801c0c00b10055040143d4042808166165151454103070700049507409100318507056282c4078040c040092881c00c03000c001e8515042803c190121084c20008192100c3e404221a55081b150300c040c64018120381e00c42c454070700503004025983c20503004627007c100150018043c00101864040d07a40d600b0f0045621400196040400c1c001d018100316180104c1c0e6881511801d0b010071206620100200440e454000240c5404d07a80391540c00e000800150554840c0000b94a040d00041e201103442c1c000d02d011310300072182400070b6600c81d02041440d81c5c1c91400c0c1e2000c503004000c2040000e800c078060190013050f500c9040d007032516540c00300e400056541b00c000c4e003203600003005000e0442c8882c2056000a49444c080150600f8035100a10204025140b002c0d081c030f290680d000c903407003224211501502c010f0706542211030b20240fa00000030200c8918110181000407050b60b5007201c020b00364144400030402003061030380c078100d8890501c01410649032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152729091 1250 152727841 152727901
    0x305060616021e0d1104060e0702030d09050709050a0203070806010504080d03200c06010819030c02060d0e030c0c01020f0c1011070302030604201008160e0909010204060206090102040e 81
    0x246556115181400350302514079442045d20711010081201c5198001c24190310103c41404400e81d40001904d0749494420000100446a03050a85c6400c0c0c01e58050f500721401c0c581000507000b42d94010314024929600c0d4085182c95490055031140030b84c0c06141890740c0541c3c5070402e0313a8032075004030030700d151491112807001c0102c000e144082d0303201d4544c8000681c014001040040020481514459500c4180380820082c60754028200409141d003e80f00b00da02043d183d2000712240d000d500208400340480341c1d40c682c10354038640c0343e0110401c1035016002c0c0c54a518042400071031400c00c480c0005042c0780781c40d0720303a0105640c3d05803900f280d07080c84e2041c55004030045c0c400700f240c0e901640c080c843d20034031f0000d1b0501014084140c2240d85009020380300f29080615000803140d600022003542e00759400c114000e080754082d01060305a5400101d95090109454040d030040066a0717155013610140da0310b40c00d050b4287c1c462403007045803442c40b10001500421030410b4040c0e240000002c2020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152730341 1250 152729091 152729149
    0x20d0f0905030a0302070e0f0103050c060a02011b032c060705160b0a0504140a03020714040b03120301050901060801150e0604090203070314090a02090a0b150a020a03030506061602 79
    0x12600c040d903041140176900102c8184225072981441d9a071111100c100c0310510f41c110354440b501c1e0f1890600c1140602c40100b60300d01c401d8003c0d0070080003450306c28030030f407241c0c00c4422004000e85081c5c0303000d4600b000249002007003500703401031031010480d0a00003811a51542481181d5079440f040c0b100105036680704848000a005100741070040c0b1190f10081014146801d118100a840310821a60365100b10034410010f600030800c00d0884801100f6088000001c00c085405032202c0405940d25000302e4090084110500d03000d1030684609582c0921aa0f0721150289e070700c24028041c000c4d03020210315180f0700700343c03013005190000c00d8040e000904040ea6600004141e8000340e0709070010035110001c07500c240e041136004951040001006001d05c0080c5c0e000f20321075003000703810505070390380f1503116100d0b0341c0700c458a13110380070004403013560307564541c48000f915881c000c0c508800290a11340402c0080c80c10b5030650b034503040b00020043d000c10150342000b030350a40e840310b503206210480c3c808030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152731591 1250 152730341 152730343
    0x1e04020f0a03021005030106020115080a03180f080102030a0e030403020a14010302070b0106120f0b060a110a02030a0f0c050f0603070c0525030606050a0608060d15020f0d1a01020d0f090503 83
    0x201d00c9184d01d45545459506210000c0d00b91403203202a10841003180c0030030028001c0c009075001440750075042010200311410b941800352203032a000000b07602103049001420860540c02540300b4090315404202a074540c0307442e25264442c41c0300c0a54040e007002414080964001259901004141001403800c00559550300302028264040004554002950500341101e8040c0c2c00c5a030881071410043d41018500250311400398003401801c004503200d040c42e041c3c0b81000411b803181d800401300c4503039011626040c0d14041080c0c1e400c41d07803c1072035100000d050803c2c4202c0590848010400360655440d048100e59034083e02d0002c0c0d440748a00d40c01107031014064944036085003d20207400e80c0c41c0d8118100881682c040e0340c0a107000d524000c00070030100350b000095640156045030480100007030703420030305200e90b01d03030b003525132820320000c0c2d0710f4110004040249145041c641051041c041103800741c000c8075450341c100078003507001095a25481e5100c3d030b603410500d031202e007060105103446070042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152732841 1250 152731591 152731609
    0x1080604080c0a02090411090a1512080717040f120c0504050411040e060601110303090709180605010b030a05011202090a0b01020703050f010501031e1104110f0c07030b1e04020f0a0302 81
    0x40c1c842a100c00c3d020750300790520b8212507a2108800270140050fa0a4040450030300f40310340710301320003100c061946000f080000740448248903080745d80a140c0d4041c040d0080703040c0d4014440c1c0d40742d0401c80000040d100c00d9140c2d0300b407003507608411079000c05450502840080e1200400c02c131034506079014640d00d95a40ca00c2100701d0b0402c203070000e016910304000090b109100002d0b491903c0d034001d10030050010703400070ba104262188214080380e510700f51000b0061111500d00020102414240085144041d000185105850b81d140500c07003642c0ea00c00e0844910a82c900294225000a000074040081c84c0c010f5544e482c010300c1203624403170360b0b038560500b8409819200245651144010024002c0842d481400d01c0c4803c500c2500903609075541404040042105070f00070781d00c50600707020100f5031710265a01c00b201d5110143e80d444a0b620301c25111400b0303000c1201c20158507004a89132124260030341002c0b4240e040b0a401c5501e56400b0040420b5200c00403030b51110340d032100480140c6940d610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152734091 1250 152732841 152732843
    0x801050906040b090a02031f06180507021006080c24041403010e070803121e0412030c020c0f060309120a05130e0c0a1d03010c02030901021501080604080c0a020904 72
    0xd040141843d18090442410292200341c050344034005d448050b9601244c141c0110501c414800c4596007034883c0e2030003900d86035100c8000251444149020086141c024a200342041d90a540004002e41440e6080300c419001c0c06c01641d10040e403100e0300d800c007455618203a40c5144511041c0c1440741e2103210b066401600201088a10b6120000e900c0c00d0074010220058004009070000d00e04259a660342c0c1d00420920000008260011400601d091a403160081603004888801c601e418204288200d00c4001e0201c0000d20742240c50071130610100d1005d0411b14001c0c40d00d20120300c0c003401c02009030009440051035000705000c02c0c082002d8940181070f595651740314551a80742810b60741c94084c0b9960702103408954540108514090000c00300da556a0050815030000a1400445601801004411505903190180d4040401d40010140940b900242d0071512150040400004010400c1c80b900c80690300c030001050010b08041c014250010150b4102c40500443d60005803085000788d030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152735341 1250 152734091 152734093
    0x27150608070905010f03030e010c1110080603150106080c0901020709020301030614070201020a080f1f03051b03010902060d090302030d180618020d0b071103040f05120a0b16050408010509 82
    0x60400501078180201130042c00400580702040b403a544001c1c14075409641b12a0400021911080800182c10011114144007801400c00c1d0442d112001c4c14421054a003680320b031080048032100f17540c1a0120300c0c140e88641c0d9403140c2030340703520072192040d800405125040d0301075590041180a5288055802103004200104100280200360301c64107502600c42d40859004100400186401400301504141003c460301d2281c1e6a880c101e543c2c450b41c2c24940e03440c01088690010511100055610903141001240102a00114209822038615540094210310300380300d81011620f40341e001d814001e0180c01a2441d0419444000040700c00e0f031000b44254075801d0b9050802d100e00d0703202d007140000707418568915824003030b00050750469140c280104040312000000c0e0030380344201c00f81d000000860301101e880fa612840e001e900201940100c070b000d810782c41c07045030384148006480042c0c3c41c0c2050017200c044c1c481d2480c2420030b1410b0359003032003841800c02002540003c240719141c45585044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152736591 1250 152735341 152735353
    0x14011413060c0503010807031707060e060f150a0509040303020c030403030906030c0c0305070b062d04050c03040201090b0d110a0203070302060703150e1b0703081927150608 76
    0x72600c00110b403101004034003040380902c0180700098002450b00141da802c42e842611150007401000410f20806500400050034000404040540004c0103070103880366a0540c0540e9884401c0c4011013a0301c480c80c00c0d40021241ca080040d030414411860300b160107881c0140c0340c40e41000f40140f0790392099000b100000c00c14042000a19032510806800700060305d0288060f2095032130050480c090060041e11b0f8040080104240e0340d640d0300d175680010b80403a0801d640000c09541c0c50074100030000c809004506017000512980034030b50440b0300c641d03416194144120308001d8420429000001c3c00030300641d03a6601009860050030140842c1c131416802560b0340d038001d2400a00b0207030064004811300d4180f5440000c11000c0c14900c50a40b8280c8c40d40c121960b49000c2d58079030710240258104241040002c0030414150f201810701e1150030440182480c001c804840c01003192490001043d690400131611007149a1515845113009d00980c500d401a00300002d03940200ca0103580081c00c903030b1140e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152737841 1250 152736591 152736593
    0xf04090b1603060f050f0a0315090b0606092238010c050c0111031e120124140c06010e07020d02030c0703030309020a0b0a080103060f0b03070314011413 67
    0x250500a040003101d10b414071502c0c0c0741c44600501244a401000e100e80511015908582c0320304003600021900081901080b980c40d00c14640244502c4100b41d84101c030030300c000b1700182004011205800c2d40541542c1d1841c0043e18a1101c1003014050f40580760746400701d0306a202c01e41c0200d40400040581100f40b880030b80030240700d801000c14a01c03818007100d0840100401c3c0d0105429500d5802800c0650240440114007811445020f4140d140c0c10000310faa0144515000c0c080d0400390340c815102c4415076201d0040b46051b44501d1810000100001e003289200d03445154080d540800480015080546004009003080001d030011041c51035101d040218035a07040250074440d80d01800070f141340990404426403221907500000d4280f50b1075a20203411903c030703000b0210080c036088032001d031201034407030004240100c01e10040d10000e0070300c8032145451030503114a144011004005100709440d555800480d802c101e04185655542d4041e502d0003a060140e03124400c0c0324440460081c1c0004d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152739091 1250 152737841 152737861
    0x1f0e01060815090f06011103090a031407060c080706090f021002010e010507090f0311010c150203070305010b09130c030e0304091d03040f0909060603120f031a031b0f04090b 76
    0x8640c00c803031190003c0010f2014054002c600346800c15028603021b603070603074050b0400f03107940b1175207045035008140306d0000028004c01c113100502240d101420380d808642c3e0350004503a907561050000d00000e000300402000504a9800210b40c1486070400d4448820036400040000e0b9521103240090303511160b00303004200d001c1c8202070340404641081c039082410028020071442041c040201400b6021040c0225a8083c40484051560104c01d004414a42e00225400394105562041c04241030070004559600e83c40d0540b103605070007a00311300d03440c02d030321803580086c0030002003036006d05a030383c1d88000002c1c2c4103100800c054240200d0100c0c0c0034051058542013100d503101e03c014581c205100510a442d4266403403400c5442050021a140302d02e030900c2401407515501c014131a0301c590039180741d00c94000c2d0030003000d8115178070200a80c00c2e4400444130700003d2a4a03403945030300030b0340b640c51a0310140a8440c00028024252072344081c1d8040c0842d0803544400701c1529148040c5080003080c003c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152740341 1250 152739091 152739121
    0x6010501020129030705031e01060e0403140304170d0b0a050d0305091513030309143a050604060501051002030406020a0206070f0b010f0f050303121f0e010608 70
    0x9007031008200000c14901c1c40c01c803c141500541da000a04181c4400e06942c0c00c004260103800001c2c241c5810411800881044683d102ca0603a004d500304040015607288030100d051096405803a410000c40c00d5842c401229803000f0422100455120b041141440b00701002c1e0002102e48040080d060724035808200143e5003542c0124030940c000002100001d5210301a600300040680d00b00a950a4101c480078a03030040745954468103040d13100000a1540c0045070100f140d0740303000c00040045000301442110b5100544007403001040b458a0080d41e0741d038900c96050581d48242070290525039581d4581441400d85040d1b48080d21080107100c0361406081402031b58101d40021440c2c503151400103074443d0301c0044068410040842c1142c14800f45071f1120960b40da05c0050445c4a41e11040d041c00b920f0407070302501401e0901d002c0c0210721418004120b038001c0040440390441d9a641484480d080007112200654000d10540d002031804503420786e250181c072007a00c40f14a0b601e041001c4a03c089 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152741591 1250 152740341 152740349
    0xf0706020304050f221d010207050601062a030e010203040314031206091e0c070204050403030c0e040e0c040c02010b031006091a010f0309050115030b09060106052505100c050c0601 79
    0x11207200a014205c0ca41d00118243d9101c52140441c07202c0c40c4140f520355842000e03040340ca01e035000165400030441c021030054160b9a0039101c0902000202040542c002d40b40310030104010320f104100c03030110340034031002c02842205204680c03919840766034040e440021410007901c268004200d060074001500981644a2426940c0c200c451030002c02d4403604250902151002d9845040440c0200400d0b20480304000d402800510503410a4a801002450b16140c030000007003041811251501d05030240c1c201404000e002000304d0080401080001c244201030b031030556513035030304a4100351400e218034042c006a2060002d442da10345400d8001356504003c00c1d01c002d82d841d50072001581e030402030b00546c00c4000e01d00042c4a50540c50240d0040040c030b483c118404035004800000c001c070341c448180c8980125000c6c0e0380070b6681d4410650b0780e0300400c02d10704012540c4841e19900d001c03580b240c40c06194000d03000c96290114041680d8210340010b040f810005a00040c00c0d091100c007080014010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152742841 1250 152741591 152741599
    0x70602010209060715021623010c1d0609030a031e050405060a0518060d06061214130516090c110601080c04020f070206030a021c0606050405120f0706020304050f 71
    0x152681c0d0005040340f107000c90007030071080e19140b181c00c40360091b81601d0390404074440d181004035003424000f04d048202044000442d8202641c021001010300410b100c4003816160001c40c50035803016143d884da03070421001e030842d8050042007a035590030468000e0603401b0361240b681d400490480d11800050004400e0b041c0901088100201c5d2650001c540b994003517450400d8440c4542c00c112400481c408000d10b900810202e5035000f260b40c0380d80f113401121220380b10051140000741580040c2d0740c11103107010030600e0400018104031030044201072401c0c4202c00b592200602c17540d0200094000b500f00d6825659101440007220360002400400c000c01000100017a40c900f4840540d0f07100c07c85007442c0130300e0300400d9501c1c014070351400740c4107915801069035841c1d10384284000c0003900401da8085000b40b0310010242161f4440c072401095032004c0c1d454625082c142000c0c010101a12050400306210b11720307210a01e4002070207903c000c0d1209501031903503540340804204c1400b510301801485 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152744091 1250 152742841 152742847
    0x14031807060507080f0c0a0501090b100f1a071704030606050a080a050c130b040e0c0a0f06050304060b0604090e0c031e100b06270315070804060e0c18090706020102 72
    0x404d40031025651080c030751500032a960007011040a0600c00307103000051003036007024050030400200700b503201e00c00c042814004626950381c1c40b20208038007441c860680c04942d036603400e0445003a2403008069280c040c1c0703c0156803101110030010f8940c4558030aa40c251799508040c092403804896102c0208a100f0041000c20402d03100c007a01c900182c4c201512a40f50840c2045c0f00140d03540061740c0c800002442080741c40c000041c2262103500c05200c0e21b1180390a0311003c109009400c6400003a9502c6507202c070b0a41d621a95142c0041c00320108003a8800b60a100004000989000300c83c11500d0300c10280001050040505142804c49a0480b10b0100d2411310150f50030300010714900c1e140b6005002040c3c1410b20300c04200c140c458091a1405081c07010440c0040c0420151020944001030301261041d81d0b18242c0600f107600706a8000001400c148041804101190064200d4405000560b031441c1d040d04009007900c1c000798580300c021600d40c0e080054030b035001c1c083c0800600c0c0900003549 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152745341 1250 152744091 152744093
    0x7030b121f0e030a1107151e170406111c02091503150121110408070909080304060b150c0a030201140c0304080a02030c011d0606010201060e010b0a14031807060507 72
    0x3803213000d040070705402c100f4920303241713102c007541008404005c06100aa555080a00107402440705007042400c14090031008580c900582c8200b100001e8240303016180d08c1103480e1030f5a8400a010320304414400c4140502107884c10541e0b0f100c0d10b13080c0c00450706005980342052002d000780301000b00c107880641d00b0103100308901d600881040501180c02407915802c2c00c0c40a03d01c8489101500c40122000c6207071981842e841c0c02d03170100401c180ca440408444d941681d860b1f428098544801006000280600100700000e25a03045a006030200034400c01c1d00200000c40c89a80f50003c001506099210355640c00a06d074082c0308410052264030011034461410320708011092001520040040c3c00c0043c2c044601c501c28410f651420031241d00a01c07078510074080c0503031506000c2c2e05d181806c0c0a00004544658014400e900c1250861841071060342e01e0300103000515084619450309010740e1601e07008800042200544c847d01c029040b8014561040c0d842070328121103908a0701c10300c401000300700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152746591 1250 152745341 152745343
    0x5100c050304060c0204021303050a1403040321021509010c120506090403080603070801060608040210110606040209030c06130f080609061f030b04060f1503030e060307030b121f0e 79
    0x7010f80d409801c00105040980c4080b0f030003842994000528880400c034044108603021542058580c001c0341d4400f4902160704840352031344514030005011900040701d80144240d80210300010301d90306e0040c0c61104407240950501d00c4c10842e00360f40c26964076940c0c1a14a84c01040200501c1c448200401080c90306001140404001070009000c0c1b00540002424603903041141e0000360071500001d021980d51210042c10000d001d8404070710415005140c0c041044c4580344c101462440840108a60785555042c40025071001506a405000d2002403c5690329940c2c000c1c07076005913906440807410316101c1855083e0003a6004038810380c12840500c001004c0004400b41c000d0b4217800103243d05c204401000b0745d451403da1000340b10541c010100021322039030303031b110700360900c0140c07001c1c4802114044400c0e1f0f0b00d00c580c007000307001c40c00d012a81d0030b481c10703e04050750f40001241000101a8030480c0098030140b4050b4000b5815400540b140c0f52014000d10440c08014500d40240f21703c080c002801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152747841 1250 152746591 152746597
    0x5010311040e01121103100509010513030e10141b0712020a031104180f030206070f1b14070b0c0c0f0901030602090a05060a05130f081e030408070603020405100c0503 73
    0x1490b04109500120018025030f014105c000c2200101141e456180b0b00c041c50014010807a440a125482d10002034004414020010300702545599082c04594020080003524680c4541030740800000840070300b244120340008200c450000002150180d070310040e9103141442c960810342a02d4080c1d110b080050700c07001841c0e003d1f00c2d840962a0000c4107100c7c00b0800074002d8810740c516000d0780034841414031140744248800b640c0244d09540302030366401c400348c1c0c1310528400d10000055001c1a40204013840c03141e0716503601d114144595015110f20061485c05c42d0680100343c0c488000071798880103600c2040303980814142603807980306250b4a80c0000ea008941407001070301c1240c0004000104d03581d03d442e100c02900004040c65114043c003e4021b11a82040c01000c910401c410004641102c4d10034010049602d02c00c0100424004c1c01400c4180c4203610700b0410643c1b00a0001007282401481100c4c05405541e0300143c0325407800302004a041000109001030003400010031020503404011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152749091 1250 152747841 152747849
    0xc151d030f03060d0807120305041a01060801050409050109050d050c16050d02040b0301090501110318030304080f0a020a0c0801020a0e0405100303110c06030f0105270a05060a03020301090c05010311040e01 90
    0x1c4c04815403e607040c054014803480b03500808007080c8102103c0050b401d980100c0c0128007811031046d0240d11458400000c800c00c1c021400800c0612004009a01e000e40103024940d100d00008150b500403980d039145440c0b114550400840c0d00441da201040c034040006101c4c10300e0103002d40f6201440c00e0702181030344064441c041c0c000c0c0d456850a55454409400c10720816901c24001c01c4500c900880d40059600142c2d074100500110150950701d04800000740c0b8059074215405a28005d4203680e0556168400b80340035095015860741040031505010180340103202c14000541e99090708400245402101d20400d48118036050600405000382c3c020700080d282d0504001150300c1e00f00080d07514194107201780c0c0b03901400001c01c00c0440400f1000d0035040f104155001c035600d01c50840521f98100030404031a900711141d41c0005d42d0070084d6000650800000b810030700c020f0b83c076078003c00d003075a580312429900034050b54400c21440d41d05226954605c044280c190303041c24101208800c80b88010303c0323 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152750341 1250 152749091 152749099
    0xc011b0815060a09030b0703050402040b04020403020a230a080d0318030c0b091c050711030105130f0305120f091203100303031508340308040b0a0c151d030f0306 71
    0x9155000304e000b403c0001c042c42d08241c0849240c0741c0300300014091f2004580403400340e030521302c03104854101802550282c950090071030015a00703040361401d81c041594003d2903000b060407802001502d40d1b030801d50141c4034000c06411120840100030703007034645002a911a20406540250100342d004a004015690200c250140d60311003140f094500a6410704034280c044008410300709090b00711008050191003001c0d260000807100040500701c43c02100e130b0f0140f0280203098a030024074903001070802070380701e801e0207802c0c444034058200702e01c1030442d90070b01d00c41e11681c140103100c10204100344404170110700e4070b80366160542d4501455400c03440010705041e100c0003440a0042e10300141d070302404c030b074808403500b10000c0a0b443c0c0c9140694207000c10303045010f6903030381344501d4008400005e90383c01a0006261502d8802e028905502c41c600302000c04c0790b03041e080c40016617210010900d43c12404408906240480c070b01d8031015000301090622684108080940d22200720305490340aa4129 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152751591 1250 152750341 152750347
    0x60302070c030203060c0405090a11040b071a10030b13080a0507020d0210030c081f05060304081e25050c28090c0305010b090109141201020c011b081506 67
    0x22070722001603482500029410b004a0080020354019107000e0400c40d03204452501c00c589035090304004aa010002c400381c010780422041c0841000c000040031450703c11420450440d6414000c4040c400060b1521041b0280d031480070001c4c8891031001e1604600340300100b8001c0b0000c0c2d55181c00ea84078904c0400c0c18003001042c22001d66a911162403d940d4002d8800c001d180c500f034000800502d25010b040f400b1528405c0408d04580d402054200036501421401e5415401c02d410011150402042120000301c10030085102603241242e9840c0d0525000040b030b144d10410005401c60380e610703010180c09100301c2690700c01140000a050b200302e4415900c1c0c030360f10717030039010407220000c80c82040c5100100d4400c40000d0b00e80c1c0d0b9900000100380907941c10401644c98420b0320801c1d21038115060300192070814240310090480c07004106026004100c000700c0003a001e140c50a80e045440d00c0c0038140d55075080a400d504102c001a2500c0300c0c00c0c601103419162000090019400b4005194060f940c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152752841 1250 152751591 152751593
    0x50a1d0403260903030901290d140d09080f030708090607050703050312010602060f01060f08060109050d0804030b0604090c0909020112020408010e070e0c0a1206090e0a03090b030c0406030207 84
    0x11010050742c10b010110003000a03d003028520783c0e07070780c03059900361801d40c6055100c5984000040030302405513801c0c005521100b1890342003000c2904a690103075080c01c01582114035000c02045203100d00c0000361038103034200d8a041078040c14408070703044046040c2c0003000382d40e000814220886100f00e00807a040b07038440da52418003501e007803d99003008040e4400003070005c0038042c1c60140f050407654545d080710703d291307614001070856076020702c44c0b070340400d45010341c910b100ba020780040e6074000410300d840c103101c943c1d50000406000c0c00300d600b0341d02102c00050a01c11301981034001507018006803001d00040107195034403081004144545540076640b0220181103a100d034124124070b10b04240190f4450b44c5990313160b402400e04451182241c4142180080c0114210f00142d206a10124180d4104034003103d0964640402c004800d48480d5140c4002c580d1600314446c106134542c1c90700040a44507090301e005001d11000341c00041002009104100100d0b0405040b14162440d500c0d015807120b0391 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152754091 1250 152752841 152752877
    0x507081612111c140c03040e01080106270e15070507050c090c091302040306050c0408010b040911010e0d231e03090d0218070305091204080d0e061e04050a1d0403 71
    0x107176a54080940000580081c145400b1a5018140c443d070300d00803c400b5541e010031001503007101c400c01324001c0840000040401d19603201c1524a04148152182d12080c008001ca00a10840b802004141d0110300c0c40d0a10000b041580c2000c0c10070b0324000300130309003003101c81c08030300480310402c1c420f18100031128000000c60301560000d5500c41c20034841418400b9020751650800e0040e40201e41c41c0ca41c1403002441c0c10301681860b69040641d0302441a1140c004464962052410030b40003072614081000040d058001e005206c100484183c80e00c100c545426030402420301000c1130080400703413442c0c6070385101000f181c03e1503004403441840903220f8808500041402c01e002078483d6100010010820340503004944120158010f1702d11302a08a8801d4070030340194014038000707a000516200705140216481081c640c0c0080c80307141440c8500600c419900303c0502c6c0118081d401003001c120b281400044800034154072000b0f03030000d0264031104075601c82c0041020b02045000030890302c903000f03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152755341 1250 152754091 152754097
    0xc0d0510020f0d0f021c05060102071208090907050a08010b0a0309050a1b090e0a080d090507030309210312110c03070605010e060d0c060507081612111c14 68
    0x4140203065441c1c010400303105201d500700c407100c800d04500700a0300208505042c0700300d58041d07103442c4074940244084034005000b410700414043c154404c0d5203000c924000004689080144140b60780b0ba40c4204000604c64200000341954041c44410300034030b1600c0b5003010515054414003440c0b1500d03440620f41c100e0141c684d446001d0100d02441d0b9444082c0704031160048944801da41054a209503200002011100c55100119150b0000c450400c0041c4c4100000c0990000f61400800d01d02015207405080c140b030b542c030860200d4a09082040f045500c0c034129030011080301440d10600c3c1c2651000b425155000d0031a45c0c0c0542e4600051981510390703000d4946840c0c5a00460340ca4440c1468242d0003070030203006150714049000001103452602e1030b01c2500740c40d841100c6241c001c1c80c02c02c040d529500044e01c2200c0c3c070501403020311420300a14400d5802c2c3c90084900d480e9413001040040d1100f8821000041d032034008054081c0d5592089064118914152500042e0a4916031241602c0c1c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152756591 1250 152755341 152755363
    0x20306041407020607031103101202040b12030c0706020c011205061207060f020106080d0f140d020a05030106120902090c070804080303011e0617010504180210020f07080c030c0d05 79
    0xc0c11050051580c2d0004400d881740c1e209440403c060070712183e02c180349000845500160008400d82413161400c035046a1040038800741010510b4256a000680420105815018980d0002c20007224100080282c407000308a9400545030078203058000910710800380e900006410348542c0800c1ca2500c40385140b45c00342070424184c03001c0d1600c42030020300c24000e4082c500015070074914049402c1d50042525404004503440d03031610241e80403002d582501d000511002142818000302c10f178041680000c1060041c5c40e5500c40e565030504101401180f0480e04180a140c0307000111001600ca64805540200d8000030050b01e89840d807414201c144a9508004050f01004c00005502d4810001d0380300d90082c3c07400c4d0340414907180d100465140c00c4e100d03d05100420204010822400d0a03400301210788519405400342c0c0003107802080d90300031039240450051f032080f405800480c00600c9a60080e1590310083d210128a03e00002c2d51450940381d11440780341101c17850010032070100100c0e0451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152757841 1250 152756591 152756621
    0x30c0409030305011e0b12090a060905010902100503040c050f2220030c180f09090706110c090f0709030c1203120b06220909080d110306100302030604 66
    0x21201e240090281070300388a0220482105d480c1c0c2c00060b82803400140654800100c605c0c200780340c07051913900554000d02124541e02500096038081092405201d1000d03000d1000421245400c2c414000a14400c15184042144c1481400b001480f0030b183e450889404540312441601190005000820826024507076400c0091500f156150650012054060b07901210761038480710b000410b5240c030044811110ba04010407808130303111601912061002d6018296640b400758200101d1480c980030741c0c420780c082c0d010381d000300011036000002e4440305000c0405800d5100e032500201d290b4505c003500c4044554951000140d04500c82d20025008640000000480d25a2820303803135004e00d4464070a400003a0200c1c005038441c001405080c42410010f81441d18280503190f2114003c10924900780a5200495000039044070314010401c0302409041219920745503201001708840d102d0b40070051084040c820810b42d661004009264402e05040141c0d5aa9402d80010000c00d0111042c1d80c2d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152759091 1250 152757841 152757851
    0x610020c220f09050706020303041a04050c0907051206120d0c0609050327060a17060301110c01060f1a0307050714060a0c030b041109010c0c23010207060903030e040902030c04 77
    0x407206078003c2160b844c052016524482e450788000c980381e200445d0084d10720f10390720940700c0e904031404054640c000c0c0a00c040c1e81000b12808006900c42e1010b0710904001600800c1c0ca49942035007030051034001c40210741c100240c040c004200c0341c0f205404028001440f803090f039010284070780398200141c8654080241c071780d52100040c9991498003091028a009001030b00d02c2c107040d080c03140480720222056180d0207440092905120040440213040903015500c4445041628039118050301584c0100d80011070100e04090a50041740d031581c0c000c003001c1c0501c1d07080a0000c001c1d002220303048406460300d0390b601d10306414081884880090304144c81c1c0705010402c4011030856001c1141075102e603030140300402c4510104801c1d501c141087d41c1c034545041100c0000d56005500100b280c51090071030900e502c1d929000c446010b00e4001540542e0141d00e0081929581d0500407400502020704001d05000c0c250b4800408000500300d00702d0040765111859019036a08214181c00d2480c010300c1030003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152760341 1250 152759091 152759111
    0x13030b1e0115090f0b30010302060711031b01020f070e1602120a0e090108010207020916170c0307030c020607081f1509030b1b27030f01020406080610020c22 69
    0x50958418040701100100301c020b01040c0506d6001715011710105002e2542e8503034215000c012103039015420481d090011038500e48120f072024025031111150b1100034030001c103940000a8105014001c16404581260800780880c8188038078103030b00b040c00c0d0f4500350300040d82c03401d050b40382802801c2803000454001c9407203002c06038400c064141c2a00c4c01e40e2101010f90fa14030781c980c240d02038110006c0d8880e0901002418101031465032a1400c510342c546407195200d600100400401c1c01d50b042d14a071400003041102042c0c06028282014804c1d1001f4403072172a211000503d1500e01524030b41d0240e41860202014880420044011b8140500d0003407118964000c05456810300f484203c1d040c00c000350024000621061425620401c05c1141c90b2410003070042410054000355180e152b14560380595001139202040300b01ca00c00c03504c800044c0d03501d0910030080c218100040c100c500c10340e4080c019084440e40410f004150240942c3c4010820300a091a05203504c0010385035001f81d858025003203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152761591 1250 152760341 152760359
    0x2030906030109022502030c0114160c05031c0c03050a0c0c0e160f02210c01050c0703021006050a0314070e070c02040b10050f03100b13030b1e0115090f 67
    0x801345c2c00c2d50440741350168402061940c65007603502e01944c16084160300c00b03100d5010301d01080020111480541c50409003a08001c0e1041d004042562504d0040c40c0500150604000c04070b281441c00d0000480d0364030350740e0020155078030400c0c01000c220f40842c400d0103903400384002ea16019031081a005000d030322480b88403001801102c417500c041410448010202d8001d0b45407070100c002e40d902426850f1440503400310082e10103540302d40c20313171810455000e80d040203125941c0178526419515a6503040c9040080c80c08010461803014140740039000c011580d00d0005410031240e00c00c03541000c4180c81c01c500e504000d4180d2000c102d58000344200041c8075400901e41030722620031101007000d00821b1084c0304240004aa603240810301c100310b201496049100039690015002c15400b50f007549a01100038190494256500c0d0000040824000c100b04030f031215078050f8884c40a000b0b2803990741020906083e06105a18480d65a40340000b51a841850140064445450013a140030364404c502 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152762841 1250 152761591 152761597
    0xd0210120207060c1e020304170c090901060608090c010509090c0c060906060415080601032a061d01030b031c090b031806010503060c481e15070203090603010902 71
    0xa00002d40c0076061a00004c0704480170400000792a402035060605080080444e200b22643c043ca0500c140741d811001555241c0c00f0318810741d401d0002141c41c42c80e2200142104401604841003134103e034100b113003507981c48029280722403001c5030f001b030032130700e6074803103000144101c4140c85c0f41409078204108a0000001d9900c0c0203140944003041340c2d004d40c2040b001d01100600607400e054000703d00400224a8882c5040300200030340fa60000706401458603000c004010b80d2002c008551101e402040740040c0d421740d043e40b0442801c081c0001c080d140f0000391103107175002508040c0000f41412010300d0740b0a42204010b862488110350f40ca08060a9201d510889441c0403402e610400001043c54200810083d020303901d5035601c1d81c28030050b103400d10394010640c84400324900e1034500c0c0d06140c04050720204103090710b103503400d0482d84690249905104038483e100d03d03440c510101285001500181da030110b4011145a840c0c0d540b070f0003504904522664199591002002c0008100d00283d40d000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152764091 1250 152762841 152762861
    0x30614040506070c0c0b0a11030a0207030606120506062101021b06130c151e0e192114011118030c010503010b1804110705060f0103020d021012020706 66
    0x2c44505a0700c40000325101d0228100083c090704150504101c070008060240031402c2d580d09240e034260810241c00fa00d150420440c01005a00010b01002030103005e102e410f0280c0000f8105003003084441c1c40f0300d03a40c3d01d0045c1c0204d004092241c3c20802c03111480c864141c865108800a42d660906520f0075032640e48401c842c40b509015101c04110139020403130f104801954010600d2079800d02d0f15200340ca28010162482c0b00f0310a40b002c0005040350703210050448801a5124400310410700c40500c0385081625142c1da000c0300003010140f12500c100c150503480b80110b948800c020011510307002c25440311054409505600308500b415400b80d03c80c0c050301400c510845501c00448844041542d07400303400d010107012035020001409034040030001007404480c241c8541c585880a18007045c102c40065660b14010b880c00701c0d00d20204641840519001012485845000c1d411500001c9001c248035a000b4815048107044101060107a10f05055101d2010b00c01c40d11201c080c28144054004402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152765341 1250 152764091 152764093
    0x406120b060306010c150f0504030809010509070513090602070204020301030303021c060501080601032d3905070201260f07050703090905150a08010209030706020d020a020f06040306140405 83
    0x440d608660519000307507881618169542c0d04161007607100d025199841c00e0707030000840d4450010154520b154018a80558800e5407000c400e4500120385600f114006449183c07039400c4410708105558500e40590800c660406002035000000c0c60507000030b1040384030094001d400400008181901a40502140111640c03003a1400912141d0b82e41100d010b8007030031303000c950050042803213944294010961818815000d4208100d5402032b40d808020540c098000b0070344803030030502101d00c000d0300c2100c4c000c482c2c2c10300d100311003440004500e042030600880f01000008903015065a00c2482da421a0650b14046002403022807050313240d103c4070480340d50306140140000f160400e4410003c946c80320b5010703540c9040207420840840054034010f40a0585025507a450a182d40d640c50001c1c00107000440c00140e66615840c10b05040401e50707402101550040d08031040750039000f00780c501405a040b40d0081101c1d20308000038089010350b400251141c1d240000c11740039104103140b0309000f580100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152766591 1250 152765341 152765351
    0x170705042003070c061e0b0a051507140304050a090f110913050601020309060a0c0203070e13060e0307060207080c061015113a03050c09100311040612 66
    0x1120305015100c000c104103072021010400103081520039841403046511410380420f42c528801c0ca0100b018014040014840703945243d1101d452801450034402024141e45601c0090b510a22084c614090610040c00e00452031144200e026000d004680140c100142091040f075201d01044008040314110084a02e1030040c18148421045094964242c0001c000e031492038074240520004d010054001c1d0305511003446240019901d11020300084040c60780c54454003485801054501030b00c0b0b600c88400c0c02400d9080c0a50400302e01e590400040c0c0119000c03030001c1882c01014a5441201405042c03141f010804100f00716450380204681a17084044880c030352128841d400074120688074000b960215420b50500d40b9000340b00400003d40200240c1d2480880311880c408591100e1040c00c6071841240c1c10070400e811008451512007107940340401082c42e100d11046124841c6022481c4520f0320300340d0b044101c80c442d40000c5003900625041540380c81d50382c60050240d02c00c41c499450f0f03141c205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152767841 1250 152766591 152766611
    0x5060901020f0d0e120f0705190203060705070c03080706050a0c0e0609040e0309040207081c020a051602120d080702010605041503170403080703080412050309070e09010617070504 79
    0x5000b07a4209501c09a1200d2030100791040c800010700d03800820705514050980d202d8440400034003d4120240140540340d070310380551404038240980800142c1002c01d946440c0d001503240001d00aa100d001410190364503011400c10000101160340010701d403100000310582001525040340b802027203903a03030500800c40681010350714010500300042d0000b1041c003c00e0001c1c0b5064002b8071410743e1803810b581ca4280800081000e0383d00000c000d0750310031400a000615009808140071610f00440011400c1c032004c0030004140c3c1c495004800703081800c882c801001e5660380000710040001500032102000300c030103009031031110308139010b0b00176510700b0900040a00b03283c01010300ac90301d50200365400030b04590783d0140c0f2030214617010300c89080a00001c00010210801031010a0194451540314980307449d2030100300084444800400a040c0107028a030200000c0100c150f80d00c00070310042965030305088600522040c0e12040e0303030341580301a9101080c03020403414141c800540d0180010254 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152769091 1250 152767841 152767843
    0x51e0910050114010807051305090a33120309080f0c04050601050418050901021603020a0c1a070f17070b0609060a030314220303170907080a08030c070b040807050609 73
    0x4040d0f010b0101d2001c00008042c0c922400052220002190503c0201c9855001180c401d0300121743c901d140c140d0f10b04090350300b07142c82038028100305480072180c00403103640044405541540d01c1410b00800b030080410080501840d00080540302a0044400040c40c1c0380803d44c0d18511800a140904c0c6044081001035101d90700700c6080d00c242c40d5040d801407000c4140301c2d00404000b4401c0351030b0f550a100189200b001a40541c0c400d49c000e9006051060290620302c01218083e0301558400a804040d0980808001700b9100c41c590030100f401c00701050350a04580c130a49660784100c007204000b401204201050343c004d8000c810541c2c8406066403007000f44060100940406408280c12040007144601200000e042200b10752460443c480700c960807135403440c1002e82007103000c15014142040c0041489002035849402c01000300305080c9440c078011344402e084203018240c1280000003505420980c0700300c1da003884c5d0080300e40070320b80303002d061041041e000070340c0803516400390f2000b007040424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152770341 1250 152769091 152769119
    0x110702040624050c070302030706090303030b0d1716080f0d06080a030206040f0305070b0109061e0f051306030206031e070201091a1e01150e060408070603051e09100501 74
    0x600001c9414101c5424a00f03583c0c07500b20b07402d10034280c0300b80c031804001610b090003000010101c540751421028203501d00030b802e4900180c480b40c001c294400c001004a030545040000c0300e442c040c411903035509811680032000f16a0740380030781070200c0000c100b581244002c1c001c1604c540c2414041000c26122600c05403134464440018005900c40d00208000c5156582020f1b0320340d129040080c508021b80d503621000580c26804031089a44d640310400c0f410741d07105c04504107a41e0300880091410f06240c5201c0b43e0b8086402071a0144241e050785c080c00f410076501c4400a0340c0c006003c10744901e06080030800c3c1044000000c0300c4001708102282c0700314014011420035540c403400146050304c481014459071300005100e41e0301070074280c030780c40e01d88001c40d101d16019044000b2030201031030358044064107900c4800e441c07501480042104110000003c01d16809403210752401140c01c1c0c0703410219112403042240c0c02e280ca1001181844411070000854003519001501e007400b4a070b80ea6030b4201c50700d00d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152771591 1250 152770341 152770379
    0x90617040c14060d050c03010e070c050714042c07120b06060708070f200121200307030506090a140f040203010e071806090506031b060d1107020406 65
    0x1d440400070320204850041c0040301d000c000c2c0040d41000c02800119058800036035031120709038400401030002001210950350f00107601c5c100421544655643d640d659012445400e4000c9074410742010700d0355594000f0480c90700940d40f20f0b008000710741c01d40d42e0440b1200c030003076160340704a000005044150801e11700e001500542045401c1d41ca8000b840781c960b0120310300f01d4144404211400c00110b2000c03088444d00d01540800701e0940c900f2800c2c5040160440e01a4144900380d0b0481901c50700304965501070541e88000841d0018506190302c103222180703811340f83d00900100070821031941c140e0081e807003404215280c414644541444100322021a074134080303003003041c00000302450b02986d442608544007400000349102590805810019241c111240806103500c4000051040d8010130018085c2e807242003086060203800a5901c440302c0c0030103080002403200c43c0e0001e035502d005583da0308080341d60500c50300d14000e03001e00e107551043c1c40c04c074402d92405201052030f46640c25449103103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152772841 1250 152771591 152771603
    0xc020c010c0303090204090b090c01200703060e0a0f0b0f010501050708070209061f02010f0e0607080118020c0106060504081506100507020609040c03020a091e0909111009061704 78
    0x35602c1d20210082c1c01c80e00c20590f00b040c1c44007040350000344030000e01c600c120304510107040c020340254001010b500c54611402c03020440340b0344c0c030303100008003140c40403c803944003000082c10306100d2801810300240031005419040d01014000a1000d00d4400a21580860007101500c0c0e880b103005484900030001e02078001c881c1403201d04c005080c4a00c4585d04410003c050000140c00d02d464960311203242140000180d441d0814a02e0b13640310340c000c00c5c81c112a04000303031469107000c03400100100700c1441100124109840c0d50715003000168100e558040290b40240700103070321404c000c1c245900610031035080e0710030180500c00c41c5c50342000042c0588d01c001e00d0140c0d81d08a03814102c1d1517400848082e03034016800c024008580d0340303d200750082e00f0030039103000d621548044809450590f95a01c882e00d20018001010351b9882e2106c00082a83c0054400144517101401c1c40880304000c201e4042d00002c14a9000000681060700c02d800c40741c031940c0c3e084510510705901e1200c200140c5006281d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152774091 1250 152772841 152772857
    0x8060a0c050c1608070f0e0601080717090c010807170c090a0503060a0501090e060103050c060f09271503030306210a0b1b030c030a0e0115180c020c01 66
    0x80040590840c0000080525100741440040c008081c10194181c00401d8050451001000b1082d0148041d83c01015041c5961352403914116000d00c54440042016041000c0417000138015070141010b04058000344482c989a0315004140542c1c56402c0d03515540810680300004203428030800c0030181070341d145210800c0c0c54540d45410304454102010b0258802001400811540c07410094a4480c00c43c004000c205941352071142c0044410300e00151001c0e41024005001044002514032501d440940f01c40b41d84400040d00205980680c915440d40589521013002401e60441c40340791104002c0601c954441c6c40344d17030f110f508001c00643e5541d0550428800103200e07142015240c0207000441d1040301140d0812041c1c40c1c00c1c110612070032200f2030855001c0c46480c0180d042ca1100c0030380610211495801c003e0300d000307018080100743d0001c003921940301c0c039030201c1c0a402c4040e03102d20504c6040e122039101d9005198140510805011640c54407034001c0f003080c400902800175010685820907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152775341 1250 152774091 152774101
    0x711030709090302190212011a040b01050f0a0c060b1c03030b0402041211030a080408030c1b0604051917010b03150103080703121401240806090c07060b0d030201020a180806 76
    0x1041782500c203002c0e40d020b0104405480864000e001c0d40303c07001d82c4500680500ba00c541c0400088030404402c042c10494140209041030881108035180c440d005d0502c1101c2200c0c07450030740040d11401034016000f08500c10018210041000042c140d680300e40c03803d00692600e10b06020072409284a510420a10300b65040041000c4150681c0484405030558440c0b90503600c45020b035910580c00200c46030f200044c12168000f003072200000345425111541c2e515110000003881d82e014038000c1c103202d06000c1a000071009582034a0308018140c525204010740d007040c0300d540c000d0802004641c040d00800c003a01a040c00d580540d00c0c180c99000c18080d080030915141291610010844901000c2d41d418095988078a03410b0468024078000b6040700c100e84a00600104080101a0007018001c6203018040d1540d42c91582960140d40125075a881c4c0005040240c00f0b800e04100064000100c54484001d0580c1900141003403060368032001e041450302c224840640080788078403081c0c1d80040e00410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152776591 1250 152775341 152775373
    0x2090703020a050d051006020d05040602070e130f030e040f0203040b0c03041505040807020a1e0303030b031203040804090b1c0206210a090507050f010e04021e0711030709090302 78
    0x10000b00703450300d001420108260811403c44005851001000461038001c00c1301550400407100710010901d0080d06141c03424102035aa0389080c0a0031846014080009082c0707907000c511086240e400281300ca041605504015150150000d0100d005a027448c54858554046008817030165910100b134110703680c2c40c40f4840e401500041c00881e00b03000c805110103410340d124040d081c0a64050528180c0c1d800c031a2040102852256000c1d14034402d038001061024050290380400702c0343c040c01c012030009824400a418410a0751705134030000e1011040c40280b01141004c0c0041c0e40002c0702c104080400302e42000000b208101c82e60002111001600d401403c00d00702800b0380b8a0b1140311140714100b200b42c0d4182850046030765a0070707a50f560800005210341040f1001c0205420b9aa81c000300500600007840141c08005682c080da400241070250200c0301f03816a00b031405100103454070b580d11031030810544000030070524400d2080344408a8030070754612541c0b400c0c80c1c1c190010021496101500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152777841 1250 152776591 152776597
    0xa0507110d0206042009010e060f01030c08040210050c0d02030c0c0301020903031e04121212061a0c120408160617011202010c02040e0f0f03030f040b0a0608010908041805040209070302 81
    0x18045c140a40441c0e404107490759906075020300944900ea112a1410009120a8415421056040504045020822a070070244c0160819016192810040c0c000701080d14680706a1007900c0301d500c035100120415903400b00150400050002c10740e20440d0000c3c2c00c2600342d000300324072035505400400070441e02c3c0f09440c0340e039000b0403080e65429080503540d540200071000c900f1016078400d41605018003d082c0d02003001a000c4a0028040040320b00341444c031142c20100c0d083e44002c44100103207004510f103003048501c005070400b608455a0f1600c802c402e41d1501a034020343c10074844d85041c041040e6000e040f082d0901c1c850010700c000103a00e05080c90340054100007040e030611a09007161800742e11140100c503902000100142585206a0080b82c500b91041d03e40d03410581050041c000300c14991058a500160031464070b0030181c4843e040e403801000c150b48042c400358a00f0391580f08000e0144060000c450411a03003103203044051145a0a4903003ca070003d50044441002455240c02070b806 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152779091 1250 152777841 152777873
    0xd0503010b0304140d05030609060406060e01030b010507020a080a050f070b181f0315090608030306091f150f0e031e011401090506040b060c060103030e180a0507110d020604 76
    0x800e80041003190f210f45c2800d000c0031031000003850020801c540d9061005000703810010584041001600d0030a000f07003101042401e4904054032042c5015041e0b1140d0252640351360012b1650400c02e1b500e281e00c581e00c201800c01141d03140145400a90051004603403407003140e0144001078501403002c40748806240302c0d403521960018203801142210300000480c2d040d481002d440010300c540c2c400050f0503007030486910100c0740509007030b003d00c090341012060303c1d01320b1025a135821041c1c440021101104807400d00780c81c00d007510b070b24001806c5025000c40d036a8003011621210340200d596402221007912135190386405501031865408003c81d218400e00d490080d090000501e00c507100d0000000103030a91041d6001601e59052000c030303240c14450790701511000c640840c60403180c00d60710380d100c0d44140b00140600090b40100c3c1078070f48034030201c21107482d520208268940f5104030140c2c02454266481400500d0034001d80c407040800250320241d0090301c0e0000d040c4e555039680d9402802048441d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152780341 1250 152779091 152779103
    0x80601031104060b0c0606011b050709110705030d1401050f060a08071e030f0e0a030903150b040906050405120a0c230319170415241202010e030d0503010b0304 70
    0x300c03001104060088171135200042c00c29410004001403440090b800f4019180348210b6201b0300088000407040c08031265601d010a4a03905036500007824011500081c0850000040328004074a407607100e1400c40c01080c0e030010250740c8a0007400311034100c441c0b0858102408000c0310794a28014410558000d2081c81c0c4890b01e4200100304111418000740c04002180d210f4107040d010202c02d02804100c008840010103e100caa603c0c0240b0404982c4005002284d40c40c12403480d0420139040524103d9014009010381e20151605c4c1e001880c08480176035003401065023250f0444207403412203410488903030b50f03003040036042e0301c0b05503548400004282d881c84000885c451120700900107083c41c1144030130704512280c055140940018040740b05036a50182c0307442000002802e04184410000e1403280001c0c200e40c0d0450b01d0580001c4034406111079284c0e5031000500c0d1841003401800b030a01c01e0382c1d0401586414001d16982d84541d010043c049501400144003a1f103030b840186522034000c070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152781591 1250 152780341 152780351
    0x8011403010f0614030609031305010f020a020a030f021201090201080a020901110a0506180703080a030203150405190b01020627070308031501030c05090102060c0a050c0303100608070207080601031104 88
    0x4110421100c881c0d00c03031030004c00d0a40c2050b0031850300340602a400315500c80a107180002500d1002141c0f01c260140c0c5061106119601075060b108104070b556007a40900901540c645a04150702c110715500e800701e100b03460301560501981018041c0c0e640566068603a181380d40c0315451180c005e90810803059040209000350b1813124130701000340014080c01032002d02110704220281100c0007400c14800c0546902c90001000010f980c04200c40700c00c107d038a4010380741d449403d20b654044c00c00c6248103521906180900c64098090f4a4888491141810030045100c0c003800598482c2021104207041210454400c820104010443c6040140b43e005541140e030316a5100f154540080c0d81c1141c03d505410b2100c105940c00d8820300700050600e06140703040003082c2d03000070f68a1074000d00c0b14011400200c0d40c086540d020303c0943e10042e0300c5000fa07135180d250003030800001c001248241400140e40c0004500300900200b010010b4a0098024007103582c20b60303c0708580314080c0f040e082d401555030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152782841 1250 152781591 152781611
    0x30818030c032a0d050d0f0b04022110120209040201020a1401050103030e01050921011d010f05100b07080901021c0206040b0a0e0c04050a06030b0708010906150801140301 75
    0x1d000810408600b070903400300725450300001081400150b02c908409030310000e04c04001c6a00b21040d00d0103120000c101080c0360512120b0360001d08940410140c1040c004a0000c2605022001d0301c0c081e08510003e210302652024103200200340b16116001c50805d5000340c03040035080910b005ca9000e80103004a902010319540c4089042c82204498001c0d03940d281c0060003015030080d20650f0500c424030707003a81003401c8080043d000d0b4814400c8060b903030010008c440c000800c02e40120030a900d01d0042441d00a4505202c40d000c2d045842c503c407290740c81c040005942d02080e003224000d079124000003905203805ea80c1c0708a0903038003044503141075101e01c4410f841c3c030000300058140801c520f130f806040c503030409140c241e403180006095448030604009004103007040001d1040c800c20403c45020078540c0754070b9070607402011280c05c042c0041015000300403c1c82c3d00092820f04955940c00d08028055036487c1c1103560940b006680e44c0015801001004214013030b50860058100040002514280ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152784091 1250 152782841 152782843
    0xf1806030f0221090c010f0f0c020f031f06051905060c030d0204030c090b040506030d1b050a050606090a020f07080706020c1b01020f030903071e1a1b0307030818030c 73
    0x14483c000350350501400030800030f00e03030a010002000b002070800440c01160031001400340e001e000495001c018a4022903415545d82e0019030b00c0400700a4103580703810315000308451150700200c655500f81400c4c15800142c0c0d0030180c07201e01e8420322504000101c01c1c1007004000c0359a222a031034002070322003031000907941c0006100410045100b04010300b5460302d090150400d82d8440352140b81305918080c200042e5031004900b5031980e44040c07400c0808400100b22058074000401c2e005020340c45084108c03004c1002c009078040c0141c03000c41e547c54207552141020700c10f03032080307910380c0700381c0303281800071000050900c0e016010903403160b007015007082d00d40c1c00d14030314100d0410450070180e9510340115982c0d580601001c5e00494507400613602d8105603201081c2e0743c551621507291400d551004040001c01c50541000103000a803030800215110000f803040c0982040e8008401200075280d43e256150002040b1000c540e815140c0200307983e0f50b00d8000042c8514400d0424250004106040103024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152785341 1250 152784091 152784127
    0x1d0102030702010b1e0904080306010c061407021c2705100c03030f111204030e0607050d0e040603030f0c0c0b0403030203031b041d040201020a0f050303070f1806030f02 74
    0x7055030b0001410740b41c400c0070840c15000e810305100500c10500700000d0591078482209034816008031405130b40c0d441e41c200407109981d1803140500018503110031003d03140320240300c1c80e011790030542c00c90b00f0282400c00200c0b40d1000180c00e403008180c0712000520600200100795003400f054078094260309a690380407645500d0088065000100040108002c01d60035118903a60503400c408200024090241100e81c10b00ca128444460980c0d400001401c06109144e0300105141c0a0304035500d40e801e5107400382d41c5110908441002c81c40300500080c1f01d040c18822041269010380d50054001110001522070102029098030007400030a0f010a42a03200c1c00184001d503c2030b4021982c0b480d1030186261078440010915081507030801c002c001e5560601c1c07203200c040801d4014500c1a48403480186d2800700c604d10b009001d4100da411950a101021024510070303400340e1070354030385030020607406c0b18800c40003140192060401c0600b40100e510a92000e80e4031b81036503c005280c08c505c042c110341c03119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152786591 1250 152785341 152785351
    0xb0f0a060c050105010b030907121106070b010f050910050405090708120d0f0e030306090c090301050f060316032406030813060938070f030e120a151d010203 69
    0x30031881012041007002d03c44e1500401410203654154109410036545500360752140ca100c10369001283c0050242150108103a05401814070340c0d00e800a240080e0780c281c091060140c8502d901000082e02d042001d10705205000020840342c0060070130040100410303018019013610300c03540001160343d002c00c00154024070b503032011054a9140741d40407e001d4602101020140604040c0b0001070248004140c0380c000800310381c8030016548490b1810868040c00c1040c551542c200340501400340f03206011035010700c0f41901915144890291240184d50f01444002d01e01034080d10141d010001e508081440c01c4040c100c0400c14580e81c0d00c60b1195500200d961000050b80d400c0c4c03c106164100180f003009000d622080c0c07500720b88080304804c0e407404214003440080c9011501e55034200c000c00480c4d01d20703584000305041d0f80880f810010004022603490380d0144240341c8400315000000a031207040d590344132860191000781d4220440140c600300e00700700240c1501c4c501020b0840d0081c00914818 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152787841 1250 152786591 152786597
    0x10204030b24031605280b0c0f030d02040905070507020a1503090605091606090b0301060c020414041b090204051f0201060e0702150c09010503040204090804080d080105030c010915030b0f0a06 84
    0x2131400c0030100007190040c060003c030055201070b4940380100350500107408691102411a4507001081110f07414404103403803d4040740070014035410034000c0d90b4040c00c1a00c0100c94200038968a62100707076014480c02e0000307940100e0012080082e25001504261805a940360115900c20341c0d50f60300040d10002e84e40502d0301d4001c940ea50180100b444946c2e40100940c1c41c10010306d62800c0076142d080c1c0300c103002d88800c200700340c40c9036000d544075030300301d0b0301c3c012440c2c82111414606070800c5041858041c4142d940020009000036490f8500c1c0240d03000d8800050064001e03d5070075816807403c6040c07004030002d55484410010340c4120101d6028800e00b0b654001c0c0440c3c950540c00d0401d20300c0000e01c0c415055406200c99021a40c2c090256036015034107031030000e1400b8203800c1c610050301485c3c0c00001c0c00e20540340d000c894182e2110002e4100d54055086a03c000d03c0720005644031044c43c000c849040301d8040c685002c05200e40c0028030204406440003400040c0040403a43ca03c40c40c0d00300c0b0001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152789091 1250 152787841 152787883
    0x180319051303081b0a0309090b0a031a060a09062111061912020711090711010c0e0415060206040209100801020703082215020a02010e030301121202010204030b2403 72
    0x240b40c0c502010a403113074138030140c880c008a66501410103040c5000341a076142c0d549800c0d0515407980101d09018541110010500c2d8134038080302218490200c03030140c095111408001010600f0340680e00c203640c500b0902c803031000e1580130700100520551200783c400c5640c411102e4699201c14004002c115803110b900b2015138161b18020344501100010440d1a80c8100080c0e40403485400c3c500d800c107042200c04400c04d484070b5001301c80f20001c201c0c00008551900125080c1c494002c1b0080c01444070548041c00050321413400f00041d0340641c401c4c20050b80001001178010316046511581c800c1c11021580d440302d444404d5075003240c015180c12800f08146000313228450520703685440600e000e180c4c1c0b1700c42d1030701c9a580d02c1d0014040520032141c13603a0082092401c5a0007900080c800348004001c82e0340382d680d59129915aa881e01c0000d6898214282403000c11a2040c0215401d681e008004c589040d2640200081881e0024506a0002594881c0c48299582c00e014031a06120041e8004103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152790341 1250 152789091 152789107
    0x9030d0f1503060b0108130804030609060e0708060610090e0117030706020a0905041812050f0403020d080403030305010e090604120c05160e1012020f03070e0a0504050618031905130308 81
    0x640b00c0160206034100c507a941a04005150348040300c050b0bc0d804000403480b00702d0351800344083c04030710110320114058000041009500068614841c080480303000451101240b000d0341c80342040d001d00c20102e0020300052001880c0d07400207951004801086a1174860309444450481e000a05e0740d8000034070108081210f8a000d004a160201440c440d111442949a44454815800d050004c09008002c215000705140f10341c01c0d28001c607005022010070409514004403c0c0d8094081100801e2400001040600381c0c034040b14400e0703d04500600481c0c840d500c0e030700000107040318218104041c0c0d0801e480050000e2204442c3e419002c0501001c9604002000340c0c81d410041c46101e040b40e00100c10014080b40320b411000c0560182c61540150a52102103810810b060b0010000c1d0f010071002d00c2101015a03002910550082050b0b40c0d0340e4540c0d203549a100010000203540a500034130524145250145640001000074240240b41040005d03e01d180344502d648150f0300e1900c086203a070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152791591 1250 152790341 152790347
    0x80a030801090c0f080a090c0b04030f060c020d08070e03010204030804090f0b19060305040f021c0b07080103020603061e130b011103040f170a21021509030d0f1503060b01 75
    0x2c4448201d8206031588041d1804000c1c18130300d005001d0f08146889a8000003440200b03013405002c2e12107082c04034ad0702c07034030390800f20403c5140e16070845910303281221400d402880419072820360502a500e14003141c40d20784003122410040345035141c1c95582000000700140801009200803c60400003085a000c8a03c0c80d20485402500460040d0f41d1a0318840c400c103060780700e481c00c4d5411070030000380c07944541c2085000e441c55000001d42002c200c502c04018505d1012054081a02c22480c290031a9030f03504d421280c4003000e1000a40051007407011034894500f10f600105085401c0503425260010b5000284113922074600e0801d81a030303200448a00c959104240c0c64144407988020741c80e003407812980d18543c140600c105c84420702c2005101800d00c0b01400214034894000901106003aa074518410003a148030010b00b01502c1620b1000c092404032410300b0b8400c0f000d0b1405103061441c030603040c1002d02555040000d425580c0c0c414029070400c01c444150280d40901d8002840102d404005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152792841 1250 152791591 152791601
    0x4090606060e220c090e0a050402090a0b0108070c030c0b18070b0c0613051011190e030d050309070b0d09050c060403170711120a051c0203030a090804080a03080109 72
    0x350103000104080314440d0b52410003401d0320b0442d0f940019160703284010840d04081c0c1c0d50031202800074103905122030310585170840d9010710b0084405141540354012a0000c442c80e030b00b41c403400b041521002074040c600980305519100d005c0d040203c580b010603590342d80300b40c4007140c0300559200700c600400c52400040004030041c003805140030f890804265100d50361104000c0c200b90382c042002d41100c00704042800490080703a034030310003031100c51340c440418001500510908855580004030b181000340c81901496000e030400346c081d10a42c840420119460f43c001008605c0d14490b21000103485152480108149403441d0700000c4e0b00d1005d458070703e0500c518800902d20803030050100384045100c01c1914010304a402c01030303179a84c00c01890b018118902d0113a0075070303004110030258078003e0b20101d10103154511071030658010080300761795580408603040c0000d00583c420300c005180404550b00000c0c0780c1c1d00606c0410b00b03150760f40c10307a2440c1441980c001c40c009103240004100300d514074003078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152794091 1250 152792841 152792867
    0x50901050703020705070b07060905060a0203010302030d030501060c141906020711010c0c06050307021e030c060108071404150b1b01050603120d0525050a141305060c0c0409060606 79
    0x154a81003141d107505d540c070300c01030140c85142100051503130100150343d44401c082070741c440d042c0c605500e0004600c6000b50001d02c02640039006d40120070740741c140b00b0300c115410f0341c4040c0c03104001c0302490303110b40c0d105503420b200d07110745071040c0510402c5407400112480d041074480c140160317490040c0c1c038004501d040e03424032541c144101600c0103030000b68820703015015521107152264881e070710000100d02d4106102d80c0da040c403982183d0a0310340000c01000030300c0003200c0401121a04e036600e0728056030b6182d140c400c0544680c01c040e200346051805400c4490900b0390240041e04a5449208070b80042d4880003104c181302c8210000450301c20030a001d440d40c40300048001e061025203250840c0c14038454642070016403655040041d01241c2240c1c400c42186c2071403450f00d441c5240d1028013420329441405044089848070360100381d1540d002c0c0c2110022144400c01990703403403600c03090000325000303000f108903070740100310a041c0181c40320310030b00b008035015400101d40f45180c07a030042c0c008501981 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152795341 1250 152794091 152794097
    0x2040302041b051e1e040608090d081b07020a141311031306150e100905060a050111070b0c07030201110105060a060e130608010218010504060215100e09010509010507 73
    0x4405402c00780c1040c151001c12141c205020b0090300e082443c0c18091003008102500e0b02c03106044243d0456000740500140ea1840d19a0b1101c0c0d01c036810401e643e0303000c490701c01c40022828400500e007100c0c07401c00070501ba40015034403400c01000380d00292034912282c01420000c1c05043c0d040e00385260a21414401c0f4041d1002000190300c641010340e00781c48002d254440000e80d0b1640001006400d138424007070260004041011107450301c41c0441226400d4806e074110080205010480048602c0740c240203101c010035280c0424034180c015680015540c41181060088c00000188142e00d000180100d40c02e00c000f0b41095800c510001d40a82c2d81c8001d0341e5803980c074010401030b0a0729401c0100c03081d5116400c00b403201400b004001200d04140e0a011078003d410410000380241c0e0540192200d04001c1c458000c507110200011a1140183c0c41090013780c000301c1303100f0b40042e11a000c203070010021425512181d840d1249407208040c242c0b0140601d03075460b000c0009600d001e100e5140c000b01245 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152796591 1250 152795341 152795381
    0x1080405060c070206121807051903060c02190c0503061e040204050604020405061303120e010207030303111b0f0105100506070206220617010503030a080a0f1e0204030204 75
    0x144500307035036010003060074120b4440010311005540e64007064400100c0720103140c1d8883e141020040e18001301200f1030890920518a012400d89491015000c003a60072170782d0390f0421469034840c600600b00e809000415401018810300801800c80b22a15800e070299201307010603403822083c185004e5004005003010141607100d41c0d40c842c3c0e550441c0307820079012580414581c444200140003440740c0c0e40002d40c03000000071100d02e00c80c07010302e4407000c9900405a45041114459040e54064002d58120b0f0050304141c8080c0f001a0180e0300c00d500901900e5203050400440c61030085c087c030401901c2e0b070800d07441310404d074682101c02d001e49940014400036a0002078504030101b0224054584000d10500300455200308490300c0c00b401501c90100e040c2003a01d038a65601c006007034801c4110101030340c460044004516030600004466000c60640d0b102a04c5581d20214440108120142c0c040c10301c0d1114051000102d00d02081149210031900050751035295104000c00c8917000c1035250b407401444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152797841 1250 152796591 152796593
    0x7030c08070b0a0302090f06041202090901050c030f0703110d02041404110a050a14030a0501170307030c030c020102100f0e0f1902040b01050c03070b07030b12060403201203070e010804 81
    0x282c250b03916222641805626142400700040d804100039001c2a003181001c0743c0007601c4c002288600c41001d0003960716051030b4440c9030605090700c40865409110306070820200355001c00020b251980a06540790005005c2d02039051411168840d600ca1a40150041028040101d511242840448046408000103c02109448924040d00700781350280701000c40c13242c02803800783d94030280400701c80207010303564900f09003080d005102c20b0007900b012844a064031108240e000044805d81601901c50a05415040e603007202c1d50b01c003002081341140507104d1a40c5e40c001650143d0550303410342c203002041da1510264031500d46160944498202e034001050107201c40e1551090b240e0301a01940d000c02d4519801c4016906071040c03c0e40070710b07a80710000c0c00d8428403d08180d214010701c01a03406000c1d524a02080040c0c030850300c2940c1c001d6801c40008030300060b0040e0150703214400186400340742c1004054115003000d8030341c0106412560000100016154040b40581c2c000c6804d080002e860306003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152799091 1250 152797841 152797859
    0x80604020a03020c0f0f0c0612060607080403061404031d0120070506070c051005030412030e0f0d0206040c050109081905122703070b0901080a0f0e07030c0807 70
    0x1414560059a00140300c5001610a4040368031100302502224030079400100301360b81c3c412000210f103420380200c404581062400d5421a00d117440400ea2022007500e594040091544c480c00089071714440030000017001a0b514020700c1902041c5503181d14081c50981000b41083c44040000480e4100100701c28510360303004841c01c22100c14000a40713140c4002d942e030709441c4c025a07400c0782c0e0b0321190201d604010004d0100194090711819600b61611034803440056805020603200108520403545140c40c00c2c511941c03100c002030900703004482c50914001c240b507081c2401c0c00c1800005030800c1c1c00304024007298195441c01170901786040000e0500d0700004d2034503044130710740070003007095083c52800a2010070400c100b2221403e421603940c581c0c150019101c107020310080000003001589401e54645004a516404c481c00e08002d10b1904d05800e00442d2040d10080c0403401481d640c01440076809140c0c07064040480000000300b114900b907003070843c103803103c0e030748240165446207800b40002c10f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152800341 1250 152799091 152799107
    0x15031a180f031204020a0f03080315030a11010503060406090f0902090606070b16020a06060b1c060b03010501050d0f06080a171e030a02070b070e0a0803070209010608190f020315010e01 81
    0x2100030b0060f8040c0c88520014880704a260700c03050200010760004424840c40400440c06002d6030006560201b000c4002c0c10703110072030700e800900030300e8189024201e85d5005400a6902c000d00038000640c0c01d481d20762410864001c220050000780d40e0344402011401c0507036105400c80000c4400e0b905280c42ca03541c042c2d549000410f10406101d1a840601e20b241c020481e05803c650f2042d0140030003512413940b00c40641111103403000c04803c15242c640c1c024090f108020030340c1e24005005196a00740801500c01d98030414141e61718a07a40c91101c40c0c008564440d032400341c00903c01826640310181451500e000250703400710007400f0204808411440030007500c01054410b890f8a644994644401c84000e000340c1c00084c04001c0724030100618903074461800003500404131080c216403901e0325500d03550b9009180000750000c4081005026040c054803685034032840350f6400100d25a18100900282e40742001058412034001c801d100d1814001d014507202024286481204a440400000d04801c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152801591 1250 152800341 152800357
    0x503010b0304020f01050d090515010e060a14010216080a020906011805010c030c050102030a0c0f0c030203040506031005060c01060302011d030604060b030c12060a1104050901030615031a180f03 85
    0x1141380b84514401e80d02440a0b94400c0301c052404001e03a0300c803418000e407100980084814030007071000000c10700e0041c40c0b4a09008183c040c2c640142e00b03003841032850015038550f000c3c0e41944145060744501e0010502501c01605192002d455101003c1c1306204190201402c1c490520070888204070031144040307641c0003150402d1808641409a50500b82c074103420451003c2d00650000040104030500d6400402e44001d0560380d406d44545440c500326440c1d18902c0009005070401c02041009182404c007842e04038125001c5244071555802c0003c13175640c060b00b00011180d4581d1810400c1d513800c403041e030a0030710b0300301082081c3c911254002621003000900c002d11b49692024110b446d610204000c401e004e4010300560b10f1000e441e01e60907900c04080b102d48241504109042500c810700905440c116000900482020f908564503d009015040355502c0140e01068002002c5540f212860401c168180020307035603810031400441441c1da00070403040700d07948610744104144600200b111703035070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152802841 1250 152801591 152801599
    0x1c050403140304150207060e0706020f030405041a030304170d0c03120c03090b090a0209060406050f2103031311040e0606010c050106030227090106060f0f020118080406020705010503010b030402 85
    0x40c0c1c2d51413400d002890022440e485902d44003003076032400c000c440c2e403014500c55000b0741103a2203d035441200b00c0e60b640500d503070885103070010b000401107810300c1d41003002c4420410401000490035180402d14640165008001490052a030592003920a10000040001920b0548280303019614054020b41e8401615803405035620703403a050300c5100741d224100c020703401030020029040c40d0140302d03609c90104000307030b1148000b040418018509440b07407108507203002d058040c1054a03102000134440211151401c20700514803040000e0b07101380b00840c444ca12a0001c54049441401e0180111010080c910702136032400003500c941900014015501400920300703128140300900c1c081d800b400c12a800290480030606484007003800c100c1891003148068880000c04d0340c0d030503540500781e0310184200d0010442c4141c41400d024843d11001e507024880d40000f00719084001c0c041c206001d0410010340ea000c00200e03003031055903418450500100310910b02281036505252010700c0612010b0002403107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152804091 1250 152802841 152802847
    0x30909040803071806090f0603090b01060309051c09060e092403011d01060302150a0804022707110d140d090f0803010b0c0601061d09060f0d081c05040314 68
    0x18091248601d0460985220b8410b034007190346030001b0304002c1d403074011072903540c0000720045030003882032140307500c1240c1110410304140d180c540141c0040c0010b003400d030350900402803280e245101c40110014101000da4418880c140f80880013098070b0003012441d0b1007001030800b070214204c400140d511050281400c484d0700c2c600030000103401031210641c100000e4101c1081c4000002044d4803000880380280c50800600d8004540413142d071141c2c132080320102c3d41d0500840c001d404c00041d082c84070012020a5401c40c0920300c106102070034205c4032040080c1030042d19001700c0e01c091040e0b52540005043c03481a000c40c4a1454251f409403202200c9074580c1c4050034070500c40300542e050749281d04551026a256101d5800e80343e59404403071208c096100780310000400c0c6e4070072903210100849020560001d0541e8030100240c884000c1c08860f4800160a21640e05a44020700c8440c1a44039041c60740d600c51011a10301105051240c00c110792038600410440801e800c071007100309240aa9200c50783d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152805341 1250 152804091 152804101
    0x150303071209080d020106080c0a03020310051b070609050c0105041208030916081c080c03011701110a030b040b0a050f010809030d020a0c021206071b03020a05010c03020318030909040803 82
    0x14004110b510000551242c8010a05130316010b500c0282078074403080c1640c66003c041000d1050b00340144c0710003901a07024030072500c448100b65208a81101d1445041100d010300785400021a810148050710180d0f40c0300b121000708003040001a071001020700300241068a041000c42050310b981401030050f400c0080007460000041c810440c40e01d03808041000d64607103413074005565034a0040b81051031000d48042d140918003c41c5001d01c100c5049082e545160f00300451417540030420034001c2900d640382d001460f0071a03406409010700ad5034a540004d04818590100303c103403510490101e000f6001a2410301c9075440740d01214131142001c3c20030030401e85030207031510302c1c604c5030700c891010741403001c110403174000e5004106842d40c9008484040103588080c1c41c10303803105800c3d108070f00822040440350003844500b080500c02c46000b030058130043c0c0203940300d0030700703503882c86041000080c1c1c00010010b40002504030a015105840001c1d800e1a0810307003c607554000142c00506070744070220000d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152806591 1250 152805341 152805347
    0x3051b040e0a05070e0916061d0901030b150d150207080c060c04030311010509060a181b0510020601150503060d1505010f050301020711060703180e0405061503030712 73
    0x8104070741240c00322001c845590a045031104020300900c0d05d42d44400000c2004c4010014440c038407030380c01601c420041440c2000a4420701c031101010307008044e0101e00c0070792a90360140d003d0700a41c05211104a42d14207503d5901c10a824020018071940c1c00f2460040425010004c6507140e4440c81801070b0b9034041424400078a000340c01072110b10b032003103104101460f80b241010f041143d20a80320512881c1d9100101d90a82d00300300c40080780c650002e40082c07030361022034101c4048800c5c0c00400b00a841d0f065241c2948482003628940d07508607021310104440d082400c1402203120fa18406042a941041d0a6000c119401c0d110507042101c00707c00b040c9981e545403000180141c1c0102c0008a1401500c0c8507005801c003440303003001c141c10800c1d0010301800d041c021140440c1d4072507100d4685000000800206812401e020380030404261140c02c02000d04032040006000840034500180c6840c1c940186045001070000d82d40311041c0300395040686000042c0d134803807a4421001c1841c204940c80c11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152807841 1250 152806591 152806601
    0x3309061b170915030a06031b150f1e02010902031009030503011208040512010902030610062106090608031308010c0905060a210b010207050307120b0a0615171003051b04 74
    0x503e4003040c002092040c40070803544170310100c900c41c070841604190106451010448188182c0b86101c0c280703c0b51070403052090b01c00c070410072000e0030000f241921a13120b000010845052040141c0c0d901c5601800358501041507820003030f5104403d0020421a98004001d40410b114000007510010200000c005684003560003800000d0908542e500c0d480a40300d01a090301c1d00d0581c0030307001c0c110114024010060a41d0151071594485040150005551250624504036500d09036a950103001c5a0040345002c0c030f070300400b81c2070021621040a9011508039620756403125039261f15020100c200650400c00c1841160340441d404c076114145141c0546041c040f80780709074110601284103920b4070080d9440205106004c2c0d080302c20094444040c140e4034400ea0082038808004850b0b100009448005443c0e808019030001040f410b0780c840401d034000445800300c801140c42403180e8034000c24002896a4060340031819204490b140d46c9076a6215a40b121a91207448449040842161601e07001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152809091 1250 152807841 152807869
    0xc0910051213031106090c0d02030322080f0303060f1e0d030908010c050c03071202070e090a11010201020313060c03020708040b0301080d080405073309061b1709 71
    0x46019240000542d401008050303000c8010409511522401820014000b8410102d940040403025142c008019503844100c83c200d901d84020008001a403002d00000d000c041c100004012020742007419040c281804281021441c2d80b050040004036a07401c0c114100c80b042c160360250403242034201000c00e030025512802d4102d070a903c0300030304040e880500d082c1204c0f0804000c001500ea100e608540901c10021050700c40c0e8824272180c800f0404000c03400d003001800e401281c4034107941300d60489580c0403c840e01e11441c3c01c50302d48181400341c403600a62054509100031407640c80d2080c0c50b0043d40c011640050400c543c4e8100d0303408424000c1d0b04980c0c5c51500f00c0313810303034480780c0d544400181a8024083c4000d28004d4101d600b8209001c2d0f0f2841c4d000c0c5d42d0010280084609110f55070003184105240c078008025266182c006076541d2600c42024a01966641d00341981010005052612044039030040004c0b02c0900c4408a10a0001303003030100445419666200c1240000810324004100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152810341 1250 152809091 152809117
    0xc0f05010c0216150210150302030607180609030209070f0e0303041202040b0103110f0d06030602030c070c0f0812160c0b0d0f05150f030a05060a0605090604050c091005 74
    0x5840c148031500000c40b03e4410019640469015444480c0c00b2504442400903002503805401084481c000b40c0e04071410f00d4aa903690a64200d94940000e894540203a90070b0021170850b0f5140890000e2040e01e410181c180c1e818030f0f068291469000c90100d00303004044508000c468054488038510a803040b03003002074010101c80d103d9803100580f402040662504902c1139280c60888a4254003038040d601c0d002046400642c18160b4100070000385910042e03081c420140d40300703808400034800d807002c2d60244070b5801010361078081a107424a00c076582500042c0b0700506020040004050004140c4160a09040c01e241c480d1400b240071111580c040c40011b282c800406000718802d60500060f041580300f812040c4102482c06070031104a84c016604c10080303c40386001380d481800c240503008a400c80280c211080c400d02a228141044401d55580701116103443c020040c521300402c1031904444121810420740c00c1112a0700c0d1148200c00409000d6079000c0d11401c1c1150081c0155a40b44038008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152811591 1250 152810341 152810351
    0x3060504050106020c0306010e06010f0f050909070809060a060510051803121c06060509060702060706050a0509010b090606040302010e0303041203020312010816030602030c16050a0201021c0206070c0f0501 90
    0x80c004c0e444070121104203000384184800000d140415000440c0542410b0f100c010303203500450b40c2290414044030365001030000c1040000082d8035104c2819102e0f1000d580c4dc601c0c2030401d19078003810700c0c1c1e01420044045041480902595507012141c18040c0c9084c1040f035541c45400c1e26000034921003c071003540c9801203002d80c460201030800142008001d40e4074480e88400120865001c451280c041c81002441c10701051100342800c80003042507074001400b8509000e8aa582c040036070708115110001c09440b2810700c0b0412809000d10a4198400c403400c41041ca440004a52540034520010b410442807400d1004507440901c2210064021045520300000c42420080d540382d02c44611018a0844100001280140403500141c0310f4501142c11074081d10750340300d0317501a400c046c01d40d44c0f8221003001031038034070200d0001003d02540b246024080820701030002904001c90410743d42040caa069281414440d800709226030702105506028403d42d0590030140085591800010984d40ca00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152812841 1250 152811591 152811599
    0x703050712060b091018110c0a03020105010b120406050403140a230c1f0b040c1805060c0d08151003090510020a05160203150f01060908060408040303030903030605040501 75
    0x40080304240d030041e8000d204038001c1c6030601c001c640f002c45d0541c040b2442d07070800380400b0420300030004008a130303441c01045910a4080c0c1c1400781d4170021608075142c0c40346114908141c1c080c0221030041c255031900604002d02d85c20300c030385502c40082000f42201d076100c00103803c044c09040e00c0441c040c4d846001c0c5440e2080364030b0191003000510441d6072540610016291040307681e1040f1003514800d00064040c00300308c44d00d607414642c9404003c0b00d81640718080098152250b110704140940142d0340c900f40201d015051305286040c49e000307113014080c00c00141501e00e50014040d100480300345000c4056540d00764180c442540105d000c60741c041c01d202904140d460740742d000b80c1c801074050707400e0310508000003458000f00d1182e620908040b400500094000004584000030140d00140c182e820141c01c0400101204008946801c4116007120041c8829581720b192840a44820001043e041c1005c0c0c441c40c080d405184001020151282051420948a600100010a4042c209001650311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152814091 1250 152812841 152812859
    0xf030e0703050a291603020d111c0b09010302011407060b04060b030601030f05040c12150906050f0703020702010915200c040c03060e0c0f0c030408030304060b030c2107030507 77
    0x1c02140c0c111480d07440920790038152004041c81c0d001c0c00d00175207100c01020038070b00e0503006504031103081e003c1d16030303141c01c5203074000741c018001c0c0303140f034820030942101c0d00102c0a4071003214204070b240c0c2d009201138001800181d80000380d101e40b10303440e47c001a40721145490300310050403095501c1c0d0782043c00d007800010b051540e000a1805480240c80500c01c1d13514002055044a20403100604a5031030b0a00c20081001e1403081c6094a6004401030040c5098626000080e5001240d0446a0b26030321030402801401c640022504580c0615042d407030501240c0000713180910070b0090498400320113001c03001050268002034201c3d44c00f184200d0718188543c46583d00c82d41800f622902440c00c140c044a4010b01c00d2003802d050318041d4910900e140c41c1c0720b00da44070b01d4000051001841d00100130401e0305220810203000201083c000542d1b60f132030503241c40c031309850b0005a400d000ba071051440c407002e0b80e1159541280c0c410340705031910000c0c000640325480c000181d44080c18600a1207404508012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152815341 1250 152814091 152814113
    0x20318070b090901060201180803101e060f020f2a03010c0305040308060627060f1204020a0504110307180512011d03090a030b040f0614071805010f030e0703050a 71
    0x4080300c824040385e0380d440f0264207851aa00300d4000001d11a6160400a850300e809140c1050802e01161210358842482c24039403c0c078102038081d29005002e040090b80da119804e08202141480640840d100c03201d101b50b6641d0010245140c5603010030b10020207000505216486c50b48024000d01024220010160081400390703410780011b034454000511604120f0304584802410103a82880d84c84c4880ba007000346052006d1096005404000308402d080301d0070003508146080c4424012075042c140304000303014030264071050086081c10b00c80c104042d82c00301070781d6100285040a0b4580301c2808800b000485003500080e901c08a12845103400c41e030b05610690941120900c560a002da4200700075039030b0300800302c4440d40181282824800203842504181c0c0040c441e4805221445c0c290703440c00300b511646081c1b0110060083d0401112a500880181a001d00444480c1c45a418000024180e402c1180040c05164640c0c0c00b450b50b092041003610001c6410405495481c910381c900410744003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152816591 1250 152815341 152815357
    0x1608070b040302010615050d0203040507361e180507061d0d0b040215070204020307030203040201020c090603062a040603020403030909020c06070e120f0c01121509020318070b 77
    0x9840c107100469002440c05445010341b00c2c0340c071120b00b084031440d0320101a5100500844060145140002e45890b20411324151030f440ca000e018600305400d0a07021540820040f2256124200014032151501d0040820740c640d01d050307404214200124044034180b014100010f040d40b181e40400240075078400300d00d40340300c22005040708580031100300300106900011006001c015114000c0f800600d48100c40303080c0001c401080314107082c21600040d0481c1c1080364000046600001008115a818401c119001208030b502c00090b082600200755980001080000804d00101100780c1032041100343c0c035000d80e80207004503522510ba4100801030340051004601056101030045140b040c18001e0b40c2041103a080182216662584c0440d07211032140341c8a500030010071442c818101d0248210111403d000008090021403040010314142c0c40404050300c903403601c00310381d05006454a0040071103011100141e1652180c885030515075903200008980f070b00c03800070300103162140140600078030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152817841 1250 152816591 152816593
    0x7080304083108070302030607030c09120605060a4a090c0306071d0603060411070b061c0c0e070201060f080f0d080903270d0c05030706050408121608070b040302 71
    0xb050b070b50b0490b96035440b080e0100a500d038110a0000c0c603194030a501c0040700045a1801c00c40259440850300c681100030082030312526140d0040240354100280c25070001d004c580440c203520650f08502c1c15280013044401e500704909130038140400c1c2d41c80440a6868898040c400300f0310b0810545181c1d035074210840d042d019004820005081c40d0203421241c4042c190011250001c0f0300c1101081b000b580b0091034140e100d60340340726170404c0242070405020b40d61b10640e501d160358201001080340040c5864100d40d0101c0d4224005400940d000c1c0d080000c444109076188400d0b100c1180a078098243c90f005401d43d00041d000000310b8140015128003011900015500900c8681310304075500d003021900c0c5c5810b940708000c21030841c42c003c29141400c141c01d1380342c1c284102141d4005503c2c1e1030a11800d03a000a200781c0140b0281c640ae2114400505250030010726003031415004684400341d0441540319407502156041c0400d000c101030b1021140d201c880d40b65110f001d450088138104003031320f0603401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152819091 1250 152817841 152817937
    0x705090a0f0801060503010908030a0b2e090f1503050402040e060408040303080606030601170402040e03040902180603070c0b13060c0309030e09010602211903060608090109080708030408 82
    0x2c2818188520000c864225001c640b13583c0c0c0d400c0055026214005000707420100c92201c0385001910f100c11010310b1005505100742c4dc0044000c000e00f846241d82014609243c03c0404102881a01c104200d41100300d04011949035542e0002400500b004140044030f4000d1070104403c1101d500003c00540344203440780c420b2502c0b980c003480003c0c001215a240452518000c01c0403494849103801c4d40980300400c0865032186031884203041d60020752028800a8000c41c450364030a400b138140b101c0307081058801d1410740ca032142d0000d002d030031030383c5c4050416003101d404184100700b11480580e50135004001400740e844440c41c01401041098016030010b0000d074054109450800302c85d034121b441b190f0042111000c600000c0c696400355820303428015800700034407002c181da0b58241561580241d1400a5070501e800809010300e00000c1c95078509900d005403a000042050041da00d401e07400442c040e44a543c0c07032502441030702c550131124a1502e1080307003400b05103802c090025414a211250f81c44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 152820341 1250 152819091 152819099
    0x30b01061d06030a05150d05070f06020321070908011107021302090d110a0302030715030e07060c060b0406050d11030d02010908030402091317070b01060e01170705090a0f080106 78
    0x180c14141c030400d403540610200f000c11848501e81d0042500654064800e20042e202d130000030740307004107580080380c643e00492402c02100f400000f8580092840e8000303503141034401e1241000400b8014101c10760905c2002c0450032035445032596402a00780302c5e008010091100022000175001801f08a2082601c4114800c13244480d0007521502c3c500603003451513480700b6940b0224001c0c001040c0f590032805a140020140e941002200000d00140010030071203412514020141e890205401c3d0035640080401c11010794004085000c07103800103000101c403500400003c001e016107500c1f255203c0c0f000d035480c0c0c05009002c0030316074912008800300c03481c075501b45000303034287c0700000000b402c051020b20001e8054200040e640394000303440c60040031100c41e0ba50704d265008640380b044a803200d40116110041003844131840b4050562030510041c0070001c1d40000708101031040e96840c44000303c2000c210503a00860907100312190083c50107080d01e8984400a041240501c262407040d801d00308000303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 152821591 1250 152820341 152820377
    0x90305121005190b1602040b040617010506011815020312091b0a05030a020402130e01120501050f01030c050402070311030a0201150b120c0714030d0504020f01080601120f020d0204030b0106 83
    0x20f400c40d007000707507181d0a2941c4504444035096060380140d80181d2134910300743c500d40d074510410001d040c441003100d080d20107010300079086560080005041c082c1d44044e2501c101c0d8580f107650116031032008555080d03032012388100c1c10b500400300140da400f4085000d02000c110041209c4036096001d082d1030850051080400010300c0a40c816150160881c00c508d2016062a800405d811550450440b06980c1d0b81d0301084018202680820644d5022003003100c200311017070103400d41251260901003c1c550541e22800080601d42c802c9074840d40c1e00151000401d0f0080d04000d0100080e041502c2e00c0d4104404042e0281503050820700b409802d60b5000700d09481c5500030380f004807010401656569980e250324034025880801c06455094002480d404010401c000800c0c461a003c0c401068a0505105104400d1007a0918074107005000d01003240c0790f40d1100060b4112180c0010100e61035003408880b1000f48941240b10201c6400020080b050101078405a41204c10641d02e42401c00340d1401e41c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 152822841 1250 152821591 152821639
    0x50103030e190b0a11010902100306210c0501120e070b0d24090c020f060109020403120516030f0e1302030403080603030403110f0406090e06040c06021f090305121005 73
    0x9141e01c050248080e0920a2080310310011009805c5d0000074414016000a540007040009440000c3e40b908028400c200080060000c0c071841020805ca26080f5541d400c01c540071a4015241009400004003404c2c480076041b14403040c9480b01600c0401e511450060510b52011001404030740c1881941c070100890303c41c1000d6a60301620205050500380303025800500f664a03203960441c031400e94018440101441224001c00102d200140c1e228954034000b444440c0d10640c0d80b0501000b4010b0780c0600402410190a1ba40d0500d8045c1d8800e03e403400a90b01da00c00c54050b90b4024614603941080221243d00860050f802a201c17850259520401c0603620310403030000800c240210310366070708207040c01d6455031080c0c64020804a0240e49460131301c01200d107203440e43c001541c05001404140181a680034014200d584041c2100b0103e0504c03000e005401642e9100a2542e500542d0040c0351107241640c0e018000d0107801c0f030351420540700c8800b81ca01c02d03004041c0324001103007020b01c8980700c1d5184 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 152824091 1250 152822841 152822849
    0x2100c0504030b0c0702040207050601060809011a0102032a070303050c010506030105220302010f09050102131505090609040f0e06091501150e011110061a04080705090a020904050103030e19 83
    0x143c00782d1640c1d09900c1800541000000700d0f0426000c0c42044000b0710103024440c040c0485981d0340c02076140005c1d01e20309648241001101c0d0020507920004207903404400c03140e20043c000c1456041c0801800c003444aa04c190070380d84011300980c80084101588070300182a6031544200900083d2256400c141c01c803002034031820780c05a000c94622000f00b00d03242d80c2c056414001c1c000003861000e031401401c26296034500072501d81e5400180308900c00740c1440310501038406469840b03028800f589010304648242c00c0060303c141c40c02f145e40c1d030160365290054011100f008400b8040003d030215074603030310401600c040107036000d0319140c8901d0340c601da6584c0d030484031194080b4115100b021410b643c0c8030341d44441c0d14108070109000c854004000c00c8548200000014001800f6191055840307668034900e0b010021881c0820041200b000300154001c1a40e404813028070050300d8175000038000303119803200e01c4d401c09e0910b4000010f01d900b146040078803480980340c5c44002c803909005541c6008850103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 152825341 1250 152824091 152824103
    0xa05031209041d0a14070906030c0503010c02011e0207080f070b04140c010e040203060d1403130e090318180901090204060e071e0207030602120603012403080a0c1202100c050403 78
    0x3c00c20300840c800350389800a61171400c09441806448240420a580c1c554100752036411107103404001d04d040c240306111070001144002c001c1000c481c9005a200b00c080e002d10724070940c010138080e052203404811113401c2c0b00f408684a0b5111001d00c0c00e820481c0c011a01929580304029150344980b8011803d00b500981c141c0d1040640703a03c84041100a40000d028507412501a400c1c13200003900c1c03882c5849440303103844000c0d504c444140342c50100301c840301c2e08012030f034004070024003415081c00810340f070900406940c60f50b5003405100c04615828007140e000c004505520051080c49001907200074541c5009950910506407110305a00d9030031030980305030307000032404844028070016154607035100c45003501c155002c0070342d00c0d10782005a802203000034204194003400d0111030702c0d09110720758805480b01050700b0210404000160038922034031014100010016491202c01d01c6000031680003680700f41d10105a03008900029030f5656540e0b450300d03c06107070007030340c0d00018000d0048e0790449138411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 152826591 1250 152825341 152825353
    0xc01020c0714060712120e0a0f05061005030703060c180f090c1b14120a08180a0f1205040504020c030306010f0801141e100c030806040203150f0a05031209041d 70
    0x1101140c0f28407580c40d820f4801c40e03451060b9100c7ea0401d01510316000c0c05442600000119410480d06210001d0103d00841a03032020801540d00e002c200359040745d0b0002070004a8448000c8241da103800e070704121000520440c03901207180310901c4503040130b651148004101c036040030b003001d640f1a4490160021042c0401c0000300004a0f06903480c2400103002040e01c00039200d100c0d400c5801d40101040d040492128801c20540000340a0009645980c1c00d004041006003515040081040d204028082c04110100c1030201405402210000d09015008659444403142c1e000e0b2a6001078607640e0000c0c2190030b00c01e1880703100d16040c9040c0da0440d64080c00003441a01000b004504070030501c0c203120300d404c460142d650f40342000c0901c1c0c240c10351100c195014191070010301e030b844000c000303900c99841801800744503800d02e181d0030211030082c1c82140310806154001024014942d00590349803042080982c40002c0032009003010038001e0704c1c01e06c5400b005004091040d400d00305d0020443e4081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 152827841 1250 152826591 152826623
    0xc03021e0702030a020a060c0b0603030405011e03140c0c1e19060b06070803060907080c0313050a0f0606050420091012060e040b09060f011403030c01020c07140607 72
    0x600500d1118401412142c04d1561540851a010410352061011614003e0300c1c00c10303c502d103100c040e40000308901031468a42010000b0f8940c840800c50000c40001c21240c1c40c00c0c55000e070340600c0c0d40b4a11040143c5607480c05020280d40750b4490041004d09004248003420f04040f42148a4030001e01b0b08054095184075110300e1580c001e0320700e0182c5903a929041e00b84260b46a1100804015000c0c9a42598914001060020719039000e800801000310081c104000c2c40c2030901a203801071003040078030140d440141001c628207040f029020340040141d510768410481c4503400001107401c140c80074402c440e23803000510f204e61500900114035140c100000c0c0040d14001d580526401181e003040304076640e41d40f20b41d07400c4640b143c01841d8035100070801c0c0018010305a1047e98421003444c0140560700e4101220202d1107010300c2402800580c00232210429a070a00c160f42e0308203229802151540c8401c001c4070359034005486001c0e040301004400643c0341c24401d0845001c5034014000c020303540c0107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 152829091 1250 152827841 152827897
    0xb0f010f0809030d0f0e070602060f0105101e0c11010f08010905061f050a0206010f0503030a030f1b02070509310201180612050a06081b1f050a030c0302 67
    0x7440390b24a800200071a2070030218074450018240c0442400180118003041c0e03e529242079a0401010340d88403000300036905a40b0251a41504e80a4803a10500a030b401c80c01c1e41c080b20f5030101c501c481d5891900d0080d106520003034444400c0d020f80740f4010b414000000540f2100c010014400009802c030005011b070052540249412801c061b00c01540384c03183c03000f075107540104d903c141c1380007600019001c4d07411641088840e02425400a003039965503e08000a540e03403040c0345000042c951a03918841344007030180e00030004076620134020031448004480013521042c3c58080e1600c40c00c2c07104040f94010b08585020565a0f020150910010b001a14803175808100c4140403410081080d500218100140840b4401080d29449403001255018000815070314010142201545810750404c2614000107113007130080000342e2342e64048031b061004141d08601c41010240c02e800c4041c02541803075849802801c4120641d50304000340c8015480032011b0b8440c0d101e103200d0404200300b141d84400d807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 152830341 1250 152829091 152829107
    0x120b01090b18060f03190b0a0203060d1b17030a02120306092202060d05061c050d030213120b01060f050408070e0720010b030705010503010f0303110f07090c030b0f010f 74
    0x2c0010500003c84880f0b01c0003e00e1b01c1000b170300194a203102c00110004000d0f412031225000090902c0079411458010702042203025a060054075080800450161010141200030301400349038460f4505007282075169542c951098500340c00500c11030081961421841d02981c1c01007100410040302a1640303400040300304c108044003228000c2d400d040c2801a9202c40003050441c84200c00468107141000401c580d1060780301d00580042c1d5000b9880001030340215002e071210f600f5040058961884c0e42c0c0200590080f50044000c10200308010307010b00007501c0da801e04a03241540c0b52044074504080844032801203100e148a903074001e84051040f41c0702c0e0712400360300400505c3c10165480ca060141154685846100c4403a80d40d62241080c45080a0290b04003511080c00c00c9071465152040d02400d0000c144005410420708040310081031900344050038030321181008682c0090b0312070300c0001c02008040e400501181c40c00c101100c142c10f2105c100d6a54510503151b92100e21400601592140303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 152831591 1250 152830341 152830351
    0x609040b01050408010f050604050c0307022e0204080f070f03080708030408070510050103050d0306030b01120c030b07080f010510050307030504022b0c0902310b0301120b01090b18 79
    0x2240c18040440c04000034400e960320405440c0300031480d8107044051108465000d17014bc188a03a0070410007210940001d120704007010321141c1040807500881c02ca040303080d005400600010b000040001e10b0000c0010080f51a802020684072900ea075030141c000751500b1840f000300442c00902c1039601094050740555403240c05518503e240072415076841e4101141d00050b403c415540d040180706005041007e446202c10343e0608000c2c42e810b5441d0414040c40500c115005800311900d0b00302000801074004c402964002c4055190341445000a08002e20407a001c0344516546000065a440e0551034901c42d1011604c5091558482100032405000c00a000b642c205100700411216010315209076a4100c2d6002c4d8130344070042c0c2d107151000c081206a807001d191a070060011500b64028540c40c414492034101c219048544081c00303800d240300c640d5001d500d0600000c07000082c0741e0340f44a825841188101401c040a07070300c03030782110300b1510041105600720601000724800400e50320310050b086 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 152832841 1250 152831591 152831597
    0x1605010507050703151107060203090f1f0902030a0f05060106030b0a120308070c120903061407090e250503072c01030e011404080909010806010819080c0a0302030c07090504020609040b01 82
    0x507020254143d00306d980822400c80c1c1c0326074000100031400c00c061002c240880c0c3c00c140640031080007a1655202002404014030403030340d5586440c8110764041010200c100c0d03005142222050040c2040d94031070344240b00d0003000c80e0424042c0346040c41c0c0301100760f00707460005882d0002c2d940b540e2411550660003c150800748501845030300040303070100d208400e410b07010b50b68207981e40b4110300d407803401d65040d1020392844030840f106011902e070704541050190341d10003411300125942c1160080c3c0720302c80440c401c00f001c01103074048040307194040000d6218041c507403141c03240c9110241d51115481d1101c0000c081c02018114140701640c401d40003280045844400810f01241850100003202c0040c9e604607094680003030065254205100101e00428002025009645c0341801d2a81c030ba541030300344d90100307003602a084010007a00303805550108075414200c0d0781086062034041d65070381c0408113460340d600c00c8800014012900e0300845200b141e01030451401d0408000901c4090041d02ca00c141c14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 152834091 1250 152832841 152832851
    0x703110f071703130f1805090303010e091015032f1504090203160806090c04030807080c0a240b0102031804060302130f05061219031b05160501050705070315 69
    0x13000445030a40c01415000e03040880241c541003060b1020380c402d2900f4500d260600e810030405420120940341150600c109202195a51000c8103081040440c10001300c1482d0140380241e103242140241c041c0c9108800203d4420350cd12403074560300c011030031007001c0c1401003502400d0b641002c01c007110346140203032502410030382c0f1a0b006006a81048a0007070000307000e800c1c081c103210382c0720fa5034075008941900c000449080c545040c0e1054800c5020240c1011000110041005003400841c5c034020103001c203a41c02902103240c240303011001e648040f880c4100130060042510780c2d40c4111040c1c404141c00a610f049110b404030005010301d0744c1c0d120b502aa60b042e0020144e26084086003401e20860400958030f202b4421600450b100902000d008212000080011480c005100c00a08030a01d800720020f4a00d0b140c11a000300407102c0040c0190f03003001c224420000d002501041c141014900706245588500046901c6d0054a202501c107900080301040030039402075010311880c0c411040821 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 152835341 1250 152834091 152834107
    0x507090e24060408012a05160803040f02040f0507030c05211008120c010c021203040b061207080a0201091e060809070504050106110114010308090f011b06020703110f071703 76
    0x30845002249880b1188506d401c1c1e03075070000c5000c51401107464541405070a002d0366060500141c0602c950081c901c1c01c0000103e02031140c0d00e900c0512043d4020018001e105150354090081e10042c3c80180204e402c0020740a4240d0142c1c00352001040004411a1461071034680359201c1c40001d8020094607000e0321021070340104c140031460981c254501960b61341c500742e0200908486020001c2411900301110781d515040510040b280c10581145800609441e00c9001643c1d410801c3c0e1121124440c02d2000201c4400c00710345010114000d88034003103001d80e80c40d041326180c00b030030300110040108103c05200840c052210141c120942c00c0448000c03c1d10703a0046401c03128203800075001f06047c40c0003c0a440000d01038a1845040241040c5072540f56982d00c080e03030b014104041d403007404c148820301c4182e44100305d526036522825220036a86c43c00d50a29600a5200c1182a40021160b0035030a41c20080004c0d94000c185a040040c14003600d000c480d402c2000394214000c1e40b80c041001001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 152836591 1250 152835341 152835343
    0x4110a0f14030a060501080f1009050601110d091a0f03060d0f050a1a010602030a020a030302180301050f01080f030c0604030503060a030209090105010807090902060f0903070e0a0507090e24060408 86
    0x2d44a100c00c81c0e0000784032030414001501d01c7c2401407043c00d46054034420056244000540c0e40201c400c8803c010540b03071034140041c0e510180412069129100b0707118402c2c811980400364104662444c22030082c40314124407140018412455010300f124800c0011070360905003a400700c05602e0082416410700350640c5d8906e410041d100c20140d81000f098108060303e40300d100341c11401050140011450080310303000203500d40b0014000070b4181030307001c909800740c460b4015a0882e403820050080085140c080105446030200f07020b00e12b80751090751b4418200210000c1158030620028000704904d0750b0300d54044805500083c696038028071420000401620f07003401a9004900c1c1d8000418190f060a001a142c07000941c44140c4081c00e00c1e56580268843c981181c801d024980891503035540c912000c01c3c0f80000b00d501070742d18920403000b08244411158031140c040d2038942c0d01c003600ca07591511141d0400106542642030039240c1200003c01180c0301500ba1402c8001901460606c0c0e510705100b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 152837841 1250 152836591 152836597
    0x7020927060907140d03080712060b1b010c0203040b031302130e03030619120b10080706120b032a04060b03090106060e181f050406030804050f04110a0f14 68
    0x40038440c0c1c04483c0c14003003a0203c00e200d91030a2425140b24001d03512030384000b0002c00020f000e8405106092940494400301900180080d054403c0050380d241801240000200e4008030811015441c111181ca9840d10120494040328600c0d1030540c10354440020303080c5c928654140c200c0e440040b480300b0201270740c414000c0b070b90030320640c0e03014680380d20780f0a09001d5680034106440c99a100b0035207040c0b1401e509650f40b503d5450308148140d186a0310150f450b0300c14902e640000d0054821040c00041380f544c0305600b82c22170010703040c0501201c0001d0040c140d503840c00b180b83c040c1d12400b2000031750201c1c040c0c03c100c4094001c001d0011480e256a50318451840d40180c9d09a0b07890b0b51940c0f01404503940111b0210b91600301524217034141c54103031480e1001100c1c00f801819a07003090040b20b49603403017103280c010003034000100100f0500b6640e24040450346e11521426005045000c0705109034071f09481640c50701102d00c2c0602d407909441c3d240171152040588207517018010401c000c454200081c4010b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 152839091 1250 152837841 152837851
    0x601110a0506010e010e090a0302070b0708041205060405100209010e04020901030b09040803091b030606060310031509060b06161205121005012c0907050408030c0d0f050702092706 79
    0x404c0c2c4541d41404a00711984400525100840d4055030714440001c1c2d00203603140c00c444124000c0703031f152443c0c1d2a00d24014403407940100400c03c1c5648030030007484800724030140a00d00c10002c83da0300f0b081500d60601640900f505003804280400c01541180c10160010a595801407500082c0c4c1c40507980003881d0b90300140c0d030986130041c000c42080717040d4004020103d8042618001035140e0140103002030ba0b10030005110703c0c0201e8010001c110540e0364001443c020b15848414416640c03c0385500c070005181000055840e02e040c10807403100d9040035000c4560b58403500c01c1601301c003501034540342c403a01505858042088800c019402c42c1d0b01c031208400e030040f02c84403000040589450001460817000442444a50030104c4032a69031581e4840f400160703890580740d010440da14601e00b07507464043d41c0d22044040c000011181420103003c104030200344030988481507800b412460031203c034018050300942064488000c0788140010030034410702c1180d0a50030300c1c9400c2d80064034a007003a006480c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 152840341 1250 152839091 152839109
    0x408160618050f12120a080702011505010206040605040312090312050a050705041203120207030f02070f0b0a200a0f1203020910050711090108070515040303080601110a050601 77
    0x51004503400300c0a56075520a010001101c0c6040c000021188558140030910540150440685800e410b1105003c18080b5148680d1518100417015168800444414005510b00310310588038000d0f00d20008143c03441a40140440d568a540e90340082a001d0401c0c0d040c0101d0310015500c24101d40101c02091384a540d407100e010500c1c219040c156400540101c40c92400d0004000040c0c0d4000e050354101d4108482048402002d81001d40fa03c101c10209070365960b0000400d82c086c1900081d40300c52050140e821615045d039140031203014850603004032902d4070420021007c0740e03449550a4001d5181401240c0341042200c142c0c0d038a0980480d000702c0b407008c8041e001c0c80c2400081e00700b04010304503900301540b41894150000300d80d1041c0642d840103100020400780e050003601b0080c0c0300d41a03c00b0b80781e0f000700d50b1591a0540c0d9006035114052190310b1012100254031010000c7d03904480d4140c407200d885d03417601d42c010346060040d4045011a0b20500951501181040100c3c0d0f0082c00101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 152841591 1250 152840341 152840383
    0x30510170a061b050304030c0c03050105011d0609060f06090f100206091002090d021302070b0901050a0c050c030a0c0201050c10020d110a0f0f0c080d050106080f0907050d080408 78
    0x2240410a03a40c2c020f943c44940c40d44511189402d1383c000c3c2c00ca0b50312030b0740741ca0041001a0319181190360103425401c094619031800001145110083c000641110f01103020f0f0941d40c0d4581c0d00f04511003008440d45900107015550749501810b200c0047c0c241440000c0c09410040a00740200b400c0c25041d00c0c030311005030311500038002c2d444824071680c115250008010741c905000003011400d0385d405000005c1c021203400c1031280043d44603030f064800d000d0340f06019456034182000710b540038050590b803084600d403030500d5801e40c06004100b118080711484000e1800e02400301c105440c02c0300c101906a061240421520220301000c5c082016000d110000c01600c1c0c1080491010071900100346c0400c0e0400c1c104600805542c05c66400308036181145402d0f45005400c250443e8842c503015002014001d001c942d0a80d0841c003500054182c0da1980c1c1d0301d0000e591040e0303060340e85142c00d0310040901d8000c000c1c00d0090781040342c81c90603014011034142d442c2c1692040054501503860308100030a12041c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 152842841 1250 152841591 152841593
    0x50909010f0e161a03041203020408010203090717010902010c020f0f1003060e0105010503071d1f021f02030402060301030b0703110d050f010b032202150406050a2d030510170a 77
    0x100c0040301c040d02d01440d49120540d482902040b4505c0050005059014210f20600415110746c04072000b614520009540780e0810480059031100345006184008203081c11401604d001446108000d5805075101005025950248100080e0400744540c0090303003040041140d4460b00450035100026030b6002528a240040403c00140103070049030402400b0030500085540c00070a168122224107000340d1204e040c100011041211006400030082040d4142068a5000b003409180180c0741c03403018140443c0342c0001000c84c0720032240254008070500c01403001c1405070480907805a003a08000506403000788241300305801c5a0300c2d2124054030791081081883c407070301206004082401c0054110704042c1c00e0004040c241134103080d0406034400621041d503681c007950b50400b003000c40ca102d991f030f80c03a24001002c44c5d021000e040b02084902e03c00c1c000c00d0b031100c0d440251009143e2388031070440151980c1100a0200540101d801e42c01c80c0b60007088005281e80d405032815004402407030954030b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 152844091 1250 152842841 152842873
    0x70c050a06170a02120a051f0603060305071208040e0c160f140d200c0a060e120c0d030c0206090307081e030403120c050a0b0c091216050909010f0e 65
    0xc3c420f541060040c052985060a42c1e07101035049244002c0110320340e52004180301c1c40400d2806840d404030310000001035420b80551101040d00d02900548002d41c0d1500040d000a22400d04001d005243c10801003044881c00101150081044103201e40b504e4489510324074001260142a100a80f000b040c560801032407c18003031404078143c020340b04a84035200094000c48a180440d134081c1e950007400f0380e104a080c841c04101e20f8004144081964a400004140042c511026400b03000b001190109845001618440c0303038100a0050140300305503a4112408a01c1410072038000d0320501c04540d440d501409034901404454005152400c1e80301c0609440b0003100e40d8810154008220500c0405c5c28410600104a80c0781400c510311206860a1850701c0c0c404000030342800c02c1602402410012440101508541121000d404110b400246d03a1a00500e0b103500c00e07807035084241001141010540a544402280c0001a1080740420950701340c829084003069950000003010104c100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 152845341 1250 152844091 152844137
    0x405010204090f1505130f0504051c021f0f060902160605071706101106090d1205090c0405040c090c05070c09110301090b19060e030d02010e1002070c050a06 69
    0x40f840c1802040d1000d6019402a9094005c0707900038048001100300c1041d0769000f501107100c80c000200424640303401d006072604c940e001001000c4e2905c41140c0d140e148000381042400012200381c0b0000200f108e525030003040303104043c2401a85070500003644032494805000c0c150414005280e110525203020411a600105900705100b200c51218602e01003001c42039500c000103482c42e195250005605a81c0380001e1050011680f24a1b0208141c804020035080602002c0d070319000c2c49090880c2c2e600040c0c0d10200c400c503500e54042c6030174491501c1d00b6004642c00c140204400a442c903120018403003a5403000900c9804104002a0041000045521900182100c000800c000d90211340713008400d10040c440d40721400d8845136000355907641c8194040c0c103000c8645a402c0526518a80a0018620003294502c01d00070419440f62440c018021300311207000c1c00d0301074003940551550b29002508036034015201a10318070b80c0454651908000d00019000a44800300d9040f0303e60850402c80c0c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 152846591 1250 152845341 152845361
    0xb0708092109010e13060b180f0108040605130602130f05040c02191109131b03021c14030406030213060e030c0f040b2d0a03050a02090c12040501020409 67
    0x414546102801c500008180e8255042c00d180c05401e00d080080000d035115245034078403003103500d00800001c10300001d00040c003449407400d02c0000d02158800410092842202e03039580429508070008001810a602490707115407400b2403562000c0e4103450345000ca8014804841020505c0081800646a0000d0a0307005040c216024002d03141c4041c002502c441313020007201007510090900300100410105e200107078135809000074000b407505502440e5140e44140341620009000701d003010911244296190680ea005091000b10410301a03484842e01c050100950302c40e0b4801500b42d02140d01880100010b01380b55801584a40a84070410107040480e8407410501141310f1040002e40c8002c00c804c00c150600301c0d00052401810b00204001d0501c09616541c400f15450b504051b401114040030a522070303160880740c0c007440324010f02c04001c40d01d00014026520081a290051801d040802d502642e00041c1c9810b00302c9164114000050075101200c190f5004a001e21051010b441424801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 152847841 1250 152846591 152846623
    0x5030c060a030518031305010e04020711100201020d05010f0510020318130f020703031d03090a0b0c01180b04170901080604091e08070204060f0b03150307030b070809 73
    0x50028000094214810800e455042c1600c2d100040c0c068801341c1c42010010b07009805036661441d0410503ca880d41c2c1038040ca90204503c100e400d0305030b0626100740e60a0540c0080c04990300603078501040000303444000c0c43d5086640030401501040700e1030044500a10395024240f03403403801c01040200351142c0d0304648085600900c643c1d55032091311a880703e440201640e00d802c9094100c000503010702100111680c020b40000f84041c02c0650541c480e0210303400035118464440300c8488181c0c1c49200340114154030a841050a01948250100a003415208600001240130300c1c04421044940ca500c8207a500e0401c080800041c41035010064401515a124061504030782c8400079298200241c0541d0080e96682e42c09000c201458210060b42040100d080ca180c540e285000520360b840039900300d010303d00700400000c0415983c0b4040c0c00742d0b0803d6100c41e0035a41c0b5100c44c88012020303601019070511500307400002154118098901900141da54100c81c1d15280c44101e04d0904c9841c0c01e8050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 152849091 1250 152847841 152847853
    0xd050915090a0b1009110d06060221031008010e0f12040608040f02211f0509030406050705070e0726090c15040504110903100504020d290c040504060503 67
    0x1481e00089110360380154440b044240d079488110b0b541440250640142d0210351074120142080113100001c0d241d1000d00100c10f109207600c0e900f040b40c41d8250805540b00c111104030308050340703003106030245501090592280d49899641c04c205070a45c5c92030741026865402c408080f0700a004244619580a46414411403902d0f2800d0401800118000c101030702c50101108040110358031442c81c00034400c0710b039040607060307100210003a4071002d5405a160440aa504948030b82d400140907803031150305600c005c3e50400b440c00405551903401050708580b503003d6104040f50968901c0307101c2e40100195610355400071120300303104262145c8040c00c128005690070030006400070004000c4a410025200310023110381852500710035008030f82101351301606020000700c1e4100e181c00941140b400440464651180f2528a01c0c00c880e000d0301c000c1e41042c03002c50603e020a400d1202c0521240340d16900070480b13254041d0895145000781c0f582c500c103507800101000b10345007600402c4050003085003d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152850341 1250 152849091 152849101
    0x70f020901170c04181b060e181812030405060708060402090a03030f02010207060614010801150c020f0105040b03130c05040204060203180102010e030f040e0106090308070201110c04020d050915 85
    0x183d5006090480d51281e501e0f00e0070280c140025968880403d43d200070b0f0019041e58a402e5141000c0443c09181d000038040710021500b03140c210440d10300710181d507101c02c0d0f0503101c190320030301c03042003c901212035881040040c031007000c2c03a1001540300780d00641c00341c1080e0400b178100909001d0701070845407045005215031042540c43e240c04008495043c1424502c0511015043e40a40501e03800030700220325144001601060318803031241c04803401d0703803800600e07138a44400d400701e44064800b000000c0c00c1407032900010304085061000c0070030141005400c0030358940070400250300849202c0e100030072001050b010429250b074001c01400003164290304080c20110000d5a90003480300c10005030741ca114080045034008c2d4822080b00028005996403480700600030300240c7d04c148591680044444000140f881c82031004c001030300c2e4003820462070700405800455520500c02011001402094950299941c4503c003d06c9000c40c0f503500032405103807580c0300030300f0850140601101e4110035000c03c0303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 152851591 1250 152850341 152850343
    0x2030a0e04090b0a090c0504020403030914120607080a090b0106030c02070608060f040f090b13110a030213090c0503010612050c0607170a210203040b1b031515070f02090117 76
    0x1943c001e144d8400000d10521604205608141c02d602843c0c01510015000c0141039024010000790790400001c2d001460441d4203000e07104c4004400e01400d034104034080380c0010300c10400359412401001022541c646503448410055070b00382c0c40000480d035101d41c4880f405805000c030300010300890a02c1344484ca04840800c0c03081500c80240b6101d0380e130301c800c400c0001507190300403800e040d040280d90900c0d2505001d82001e5114240c4252103a1140904900441c41c0040340341080c2c0ea4050f1004030020b082c402c1c0b40c0040d10031010200d82508400d04080751646007403040c4002001031070440318030011641000d9080032161682c6d18000c038130420900c80400c014221030712156400100f81c1c0d0346c43e000c0500c102c50790003a501242c060b0341c40b00d18042c03404da1683c0d00694000d5004030225049615040805510305c0401c0101707141c1e080c0180005142c00600b40040c0f984420007030b2415881500f010782d141c0c096440000102e4509000c04520025400c00707000f031a0150650743c0f05481d0444281c1074a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 152852841 1250 152851591 152851613
    0x501060e25020d0c0302010e030c010203100f0f05061c14100e090c21030301060e0f0303090120010b0a0801021e16110609041404030305090c1e03190302030a0e0409 72
    0x2044c00b80e40c4290b1802c25101754081c1503210890b50640e521542d20b0040c15010390b04c1034502d0002c0d00d0140101044c0340084c50005000c8035280c1c03811134007107880d00040c014550846140307981c8a0100c0e00c1d005012032450b0194880581c0e100d0b00e441001d26240c03003024203070342203034200b1030305840741c082000b4510780c00080c1c0c6274101c5002c446482452240c1221150f1003510703007015100034040413000207809504203008030041c1904940034900f02008409141d40c0703010709809039000a850000d01d44044d4202d59001304402401c0002181d10303001440410031840941c0c0c01119540c0d400148007441d80d03040b00b80c0d00101c00096141c42e01e00881903640713000700e183c0b001c809803030103090151a5613256108000c517200c3c85000b40051100b107003c901d01e020b0444013101c0a5000c0303800e003400500e41d108003095110b04c4020080c401143c42007a90784004021241c46481900b42c441c1c280d07480e003144041c408850135180300b640103580da400b03d4180206090041c2c01458000e90812890b8000101200300b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 152854091 1250 152852841 152852863
    0x308090d0c0b090f120d06091107020909100c0c150b2202040521070801150b031b0720090c0a080a0908160b130804060c03020a0501060e2502 62
    0x488940fa1900a8882c2c18800b0014981c50740e40f155248941c222401c29000e0300c240d40300a8800c01038140e1710600c0000755145a0510180c3c0002084000014036111142c950400b440c04101d910902c0001191402c4600f2031104801003200304049204000400e0088081d281403114140816041d00300031480c604140e0454843c0d0746008916201c2181c0660b040d1402440001d0442e25168404104485401411042403440b0b0048802c082802c1d50f0501441c00f1103090505000f4007607150082c40b0750660805022050454600d4089000181ca0390011705a020302821500d081c10740d410941041c04c00c0b5015025005840c450200b0034014410300644000e40c4035814089940d40e40c00d601b00b80100000c0708014184003020400220b079406480b50341d5101d81c4600d030760000549680d4840c180328107610380f00800f209401c0009000c59445610405070107031007801200e2040d0103a54981c2e0a40c3c885802c94041458201c04101c052450f500c010811114243e407503d10f1020001030094540f416040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 152855341 1250 152854091 152854103
    0x60e0c07111c02040513061505030c060c030c06010f181b050306010e0a1e050f0a090b06070f060c08010b0306102604060e1e0d0309031e08040308090d0c 67
    0x108441c110000340b861041d500e078000c0c4208054a46a070746007044000044041d107420346000009400341e05a0703000c0900380e41307000b001040e0107a09841040b51591010b245450680014880a060001d00300134060284c800c0b0120000c01c0345c00c280810028064581c81003204504100d031480c0900313401010300410000e18580156603698030401698852903003c00c50350081130b01e10f000584a020344031030301c00122040d1045195290b031442040039100707038050842e501041ca01801c0011206552081d100308002805007400d080d100e480e160700400300c4840540311a900d038028004159403080c0c0f03c901600c840b0000034158209040840c01c2c1c004e07602042d2042c003288441c0d00902e24070b0018a01d4042d201d004081841c2d1900b80743c03444c050301485840541d50303c15001001c420308600d002c40080d8108034002000c1c80c121070b040480150803040c0302601840134680ac0c1ca160901048001c03402003843c0d40351000e06040a2600418410000345000350581002d00d46011550740154109075454100d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 152856591 1250 152855341 152855359
    0xc1e010e040e0d020d0f0311030f07090b0307050c010f02210c1b01060f06230a090306090803161b03031d0613110904030504090c02010605040f060e0c0711 68
    0x180850002c100040c2010b54030f2041c91030f0790320f14035030000341900c0010480d6681c0d00360131000c02c2d00b03a0030b8130300400f041011001e092000501c4244006440d030f90203825403520003481d950f18901004250f1054a594000600005110341292800d004001410f4402e510841c44c11130341e50b05400004802c1144e0011054400e40400c4042580905070781400380c00307200102800c00006400d034028540c61082c0308403641c8901c40042c00b5406006800a503081055282ca89a120300c0c594004a5100b9031981c018031903150000303c0401c000c0c0c031803203203000e03c0b90404964a00f084441c8100f40c18040f03000e0000c0251900211900036000880200d1007685800c1c0130820301d1095a0042109000126400c02032040404001024011055420f01203019071407010b40c060100e02480304a44048030058046501084208110a003a9000c07440101c1148000030350b80b911000000c0c1641c800c02c0240036010703140e84060041c5008a00f0054200c0b541a10321854031170180c1d54800800100d2946600c12400c031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 152857841 1250 152856591 152856617
    0x10608060a05010f0c150f0e010501030803040201050c2d0c0301050412050903031b01090b0f04081b0a0209010906080c03070510030c0903060203090604030e0f010c1b080102031003050c1e01 83
    0x250b20305004440d4441c001b0580c405000c45003100416904501c0f145081c1401c54880700c1d5001807040f00d0580360011101450350b80c80d40c005407001d81c498140e50b550f5106060f9044a20f00034122800030380074547c4151000d02403511801d500d0b20141c203006500c42c0c0d15040602000542076076404c1c021310054108181c840e0345810001e4194010f50000344808407101101c03c1c2d00c01019032007060154450042c1c16035030f859640c19246401400c0300c1c018248507082060342e5012030103800f0030800d00401011914884c1c070680c0424034401080c0c0c002d200081d120724040c441c804040c00131400840c810360003803121030b20f008001000601251072034018580d0b103101d0b400400b4802c10002c40952703008201035541e8280303d0055941c0300b400301d50507000070f0f2140030400c15600d003e0041362000c0c1e5050f03481c611148880c0d01c666005180d0100b62104000808100181854007070000c3d6109035000940300400c2c51031810824104a403440d840c030710030404144100b80400142c220b0500c0c019007883c00500c0020340e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 152859091 1250 152857841 152857847
    0x30611040506030109020d05010b0a0905150403020d060c090b1e091504030309050a06030b030a300905030601150801060e04020904020f27061c0615050d05010608060a05010f 76
    0x494020030b820a4000001041505d540c0e002030003404251801088181e80c4ea85041e13140d0700503a44501d0000d0b003464020030041c070340800120950354440c0401444c0c00d030f5a500051060064450465203a0b4442c5440300c219a04850f41d42c0041c1007014a052401425040d0308140d4095490420070100011a80450a85801e4002e0882e015100380b0f01d5591900d82c24003411000303540c42900d10540203100e0200380c07240720340140d14508201070000d1800000c20782d42d074181d6060080160f80c2401d4200c3c041a02020744060707a0020030b04940300c0c045520304040600d410020140c0000d13510b60900d0344100c041d2030b0301650140c1110703494a8014000c80381840024043d10805c46440d50080c000f0550074410112540140b560840c0c007840804c100560503000c0c01101c020011550344500107100408845205691000701034030000000584152561894001c42400f801c0c00da0004074045042840250346100b5103014001500745903040d407134041e0018000503014080ca50400808800780000d480c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 152860341 1250 152859091 152859097
    0x1e1302220b03012301051207020a170c06150108061c02090403050a030f060302090a0b0a080a050705010210050f0105220606050c120c0a02010c1b1805011d01030611 72
    0x4040321040311025510100220550800c0c000c80070b10f10003951222401e0008100d04144568040e1140380c00c10702c60700700010709840010080810740c0134400029000449030a0341c00540b25120b0f41013501c44400031803091410200030001c025540742d2441c5502c40d6a00040c01c40e91208049a00c13440440c7c5130001d50031521740020b0025040200c4409200400da001005480503180a640401680407034411440680341640700107900700f4004004281c0844194202c1c1007610400381001c012169503072070440c504007414001b583d15402440c014000c030347e8140702d100d40360444503009001c1820480031015203a4030603c6400d12843e680090810a00c040a40f0700c03180c040300c500d0400a0f19503855014146078420101c3d401c05015002a4201c1003103944140d0341000003e10050042d100300e03500654152a21110030f54600b410304641620b078401000c80d14010380741c1402d00041816000e142c41d0103995040c0c00030509a0041c0100c403041a8030000300f1411030b40c01a001044d904010002110184 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 152861591 1250 152860341 152860387
    0x18020609031c031d0a0c060e030f0712112e0e100809100614090907030510060e0f04050c01030b061605030405130e06160210090308061e1302 62
    0x400c00609000349500742d84010b0401d00c01c210b84008800d02d492201c2d4885040e400000c04001b000d000a1050358803603000c20b600d01001400710b030080c0e0345500f002490880740d03610807100d551400d40d2903001c110518101625000f415101c03017508003400a2840c8060401e02010164174901c8160407000300c0c8100090f0307912500142c0002d03440c00e04248000d01003030048611116512a0948900400c8013501c5000c0c1101c4444007503400d1481040104103d200300941035054510074004080701048091000d0181820700078000113190746050300d01c1760600002800c21110048040c00c02007c20404034201880400911f03001500c40b051000081e041d02442001709501c201c0c50f880481007000003c000d006031b4100311900e41072140c039001000203803500ca41192100360001c1c408101182c4000229400c916031500686071141045440e0074200d808105080e0005459241031045a00b89001010301c006401c0310744403d401c0092000c5001d03640d01101c40c50009a000400c0c181c0101c1c1300120800d42 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 152862841 1250 152861591 152861623
    0xa0b0405040501020a080105030c010f1103090406080607020d020a080a20030313050f01020c0a02100201020c01050a0b0f0f013216020108090a050a03050f0903070f15031802060903 79
    0x50078076090080c000d400403c2200e0200340c001001144a18000035801c803440016034a901d00c0b20910342c4201c4a4041c10055040e09100070310484401e07660707600400d0040c050100003480507150403075000b0b1810312021040410354000c00c096101052142003200c40c1c050305418002100c1428810400d000c0e2000c0410401502000c401c0c41740070700d0010350601449010f10120307030120503203291041c00c038400c040c0740d410a540010500c00c0103041c014800003e64080d400010304025201c0155405c2d41d0b01144c5407040c0c5030b900c0075403495070300e046840760f0300c103600c00e0381c111030036004c604006004002254100b83c42440d080e0003401c02450000c1ca0018264402c100e500d0704e8024a101d440e00ca81c44030700040303002c1640c2e24005420840c00282c6584002e4019000700503000d01600d060303803550f00032455640c0c158010403a001494030308001c10310081c82080c400452061501101e170301d40035201e82241040600b03096402000100840c20b418078aa01103480503a50a06030303002901c1c081d20301c0d040b0140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 152864091 1250 152862841 152862851
    0x4050619180621140a0c020f06070306050a0603140c031518100e04082709152d04020901050c070e01050a06030203041203050403030608070803040f0b0c030a03050a0b04 74
    0x21030790780f290583d07526898250716550031015110844040d140840a10610818550001800703a41560002d110380010750056400b400c030612201414124121221000b003910b41404002505047e02c114004100601d010401c580034481117605080340907151901000020000c60400e80b04100b8600c810711005000c003100d1181d001c006295190100d900722030b42d00c0c1070080001d1068203050014800d80d440110380786056500074001d0700c10040b5800480b8110698006041a611181c440901402c4840c08601031000c40350200f1100f00800030150b100150b40214002402c0c0d41d072000b07251320080454000d61a0800324004079842c0c000c1c40d9144d05244520000051598400b0695505030380c2c0a8034030000003500e07600194241c0c030003550014050030654440200c6240f003580b189800074480d00d80030442039624803540c4c0c40c041040d04000f009410014040005e80f0265030003100400010900c5030030061500441612405400c1c5404207143e140c2c0000317403203051190703c10104100c00410401c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 152865341 1250 152864091 152864099
    0x6010b28020f0a14010b0a03052a090403120c021606050c011b09081c090e1003050106061d0301050c04030b04030207120309030302010b0a0f0911070605040f030807050405061918 78
    0x3001042d200001041c5521b0b00c690f0b070380c15003844410882640e41080c0284940c00c20620aa4400f0740c881c04c0c500c45c2030409299108240d030710001014003480c02981d9051700342080e29200c0d001c0350603600562096600400841110360b00c661182002c603005401d100d621515500041070150201d801d0b0400340c1c61000701650615600030303400b8001d46403184125000d11604d440780020150b00140c100c40881d02140e41003040d0b4818051440e4403820550402d03243c01c1d80c9540345070030b49200c0c0c1c100c080807601480c0c409040716a4043d50325903040b0210000c2c4414185010380700040d1140b400040c008500c1030001078107050081107404000c1c100a1400c4170099868100103120840b903010413401035092000020701032508604840580b941070441c10000c0d450138081c40020000510340440800081c4258000300d4601e01c1094882da0041508400c01c44580c80c1c02060b08200038945410701c00c05000a100e1070302c400301988d6010800c00056488a01002c030b055416506400c1309021960341498045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 152866591 1250 152865341 152865353
    0xc170a050f070e010602060712020904020c060405030a030f060e0a0b031c08010f090b011e1b0605090c1c0209060a0302090709060206070905030a29010f03030206010b28020f0a 77
    0xc003101c0303c80b0704000c92640c907000d00700e0b19000f041c0c2e040400144c03009039840000c0e42a500921500c0c0d0010001441c0c0f440c10100141014421202a1501d0300003060110043c0e07090701a090035004850020440315040419544030080c01400c1c00e0111961410804240c1e01c0c20407206228407082805000c1c000c42d8084000c04054003405808800d40b4003501c00a0305005a000c3d405242e20140c4445282850728440c0c02407499200305a1001c0000ca40d2903a4254681c190100b10460302801d0042214544074851510380800006c04500400c12030b58101c6c8160400d40707008071401e0303049400b00341c0d80d218000000e005c0501a0000380d4400b0030300b420f00440b20740211050f01110f005400b0740341680d441704415551645144100c1c0d8154005800d2600001c1114070000d030040309041140421200809007039080a000f40c001818440710581e0070310034542c04021403401010507402031450010042c036a101402000d0390120301210031940b20241c1c0034024044404e06480050841d685c440b90b50a100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 152867841 1250 152866591 152866603
    0x5120d061220040b0d03080712181b03030206041401060b0a0e03010b0907020d140f030426030c0702090402030106032f0a0501020721050a0809030c0405040c170a050f 73
    0x10300b5103040600494030181c14503004680307404000a00401c1c1007005920143c03000000201800c1c20854029022801c0c0c400301e2107140500503060410112108a928002c0400410320320300c1c04001d80365000800020340c1c0019510303400b0b036106404107102c581f5841000d0140c0701e00c2d00b0011200e8804101d40c811240d000b988400c024100714000d11084e4401028484088800d445090058104000003100540641103840131a21140304503440d11207042150541030700b0aa8040344c403c42d2500c0703205d601c003100000d0b14001160310758900e465401c0618a920940c8100d0900074000d020500004056590a5100718011604680340042507610080d0b02d00400100c401c1c8405031034805009441641400306007a000c5d00d0040c0c00400041d4107000c40c01c200707043c2c07100021490720000340e84100015824880d440b001c51040d4003458075200c04604060400b9441260a0b005516000c02c02c00442d04009400003201d404155503c10421042c96170303801c0420610010300640310328258400c441500183d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 152869091 1250 152867841 152867873
    0x53c070f03030c02010e100f0e01020c030d090815010b0a0f02010e0d0e0301060605090d080c120d0f050c07030909050903040b30040308160c231905120d0612 69
    0x2086180c4110104014407850301007101d000090320308230074000c0d00f0f01407040320b81c1846050044400003c900390001389802108001c00d000034580340c0e0104240181006040e000c041c96114007441d66042c007644990900504161004000050f00d10314641d034001e42c440420506484140d59041c0c4c3c07240009041c0300d0261401070300942c07820000007040c1d4801d206490f500303c00140745900c1d0081544502401e81c011800400ca14011708031100c1910048100800192075903600201d5950880d07901c0300100d031001814410740c4034080025030000303a440708141c81507611007480002e254940c0107500703255004940291488610000c7c84c59007400c0a114502d500149542d286003044088508804007480d040c1c40050105030104081856412882040d0101d81c805192062510f05151640f2042032460082501d40c1d42550020a01c2c0100910407040c5c2c1144400c07d14440c06005d541da1951407100059115081d0b002007220003540aca141c02041c010310003c00409030810740e03401d02881c2040200c003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 152870341 1250 152869091 152869097
    0x106080c0102030405330705060402040f05040803310606050901050a030213090819030921051e040902070c06080615030c0703020c030316053c070f03030c0201 70
    0x25081460741c0700004640550b480545624814450307881840720030328601469580500c465090904d5100000001c1c2a40078010002172105d420075005000442e110b2500103100319050104010208880c9004c90b600181303500101011500d0300d804010380104966402036114600803103407000e010315500104191070048070b04c4041e0f640e03100b04101c0071842d5403000075000a10421091420b5006502c260429802401e68500c1c00300c225850070380c0807001500207000303e40c0da00250818806100c0c070b4181c021140075800b60b9890000c902c05043c41c01840e90910313010000384c0c2c896256844100640c2e00400c1d11960070b544800b01440c00402080c070300e015038130001c0d0342e143c005280c81c80c001c42c00d501e84410007411240756445841c40e90800d544511029015481450315035681074608000400140c50300740004107006c2a00d140080c10410001c0341009402d040b4828004558001c011352446508241031662041061003041c5003080003c0c0d1100800c5400b6903c00014542c0041994041610036a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 152871591 1250 152870341 152870353
    0x150102010f020405030606060f0d0c200d27080a08030f2206020307180f0503011a060405010e130504060b010306090917090a081222061d12010509010608 67
    0x64507060490003248100c5916510100203e852414050000c140d40400110301920344900c10b0320603001d440704600c401c000520086e290705005403000788420780c034030345003000791050340324100006100907800403904000c5010f20039551140d810701040c80008150a4041e520b400c0010300703019549400c119502c02013490385000282544542c194074624080707400c210180c2e010f0703c80e11844001d420040110301031001c5202d04279002c00b01c14141200030700603a01d0098525040c070302811300352071b810742c0200c02c410740b400c08508040d80c0d4002134806507242807078108607000045000980387c1c80e125005454051400e001e0005108503500028510a820f8805001c03517966040300b07104860380840d000d00841140040e01415445510007400c1c0c000d0024000542c4907110041582044070f048013466104400040102d00344140585e00e15400c6400e03c7c500400740d14200024007030b180580300600300301d05032600300c030841d64803001d1150050b407242c0020020381c0780c0000c4803030090116000340c0082c0d1041c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 152872841 1250 152871591 152871611
    0x90c03050109060605011106040305070c051c02012307020409030c021e0f06090d0b07020102040b040608010f0506041805041e0b1e190506040605060a080f0609070c0b040302100515010201 82
    0x4041ea01c2a014102d40185680c0e07407190ac04803501e400207802221100e04540d4001803a68840d0010340745130402d400103003081c3c4a2480050b058400000e18615060384110341c02228014032415910415010340d00032810960760f00d0111560100300d11300039400307020f00740007022905040c00707c02e45260040d141c114074030003000d082014a0082500e410340c03010441030340d00002000c1c0b0b80c0840c0c02080d180000350070251262103402080c1c101d6040003001070740a2004118400060000c9030003040c0a8030040d28090410040b100e10411502d0b2907e400c0d500e440101d0100303d03004c06104005050817000c3d503580240d0b40f40580c807161094a5100340001c450300720304219500207054a018101003804d1003d05032452040c203000e004000c0c1078980c0542e407000b0011320380d102e00005044c0e12030740390b4801e0642d2800440400450a020303001c0c03030140c2090000c0010070b60b003082c11508900d42004148483d0741d5145012840c4c000c2916080f4a25410541400035400c00c40b003d00f920008240c00070b105903030036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 152874091 1250 152872841 152872847
    0x40e10060c1104200a050c01060e100b0304171204060c080609070e010c0c1d010609060207060e0d120203030a2a081e07020606040c020a0f080d090c0305010906060501 73
    0x11107a030240014403414410002403030640c0c41026581e03a4886980d04407041542000d030140c22155144000c154000361507140c0c4103003842050003030409020321004c9810110640b81441c0c00a0095410b0f00c903000001c18140310341a0000c3c10844900d405d101d039103070000c84255180103002c0d5001c668890400180f45155801414a80d2040321302a2403182156507054045800f421002900742c184039031050170704042082010004082e10342210282440c1d450081642d02c0844140c1c0b00c1e00402540103403d10099501180f040200c415900c1d000624141c000001502d2141d115002400310f032200350310344211a00800514401c0051035010814401000b0510031307420303100c074100c03d5081403a4168a0b015801000c6054020740c3c40e404040021031449400c501c0581e0548405000d42e028030100703d0185031902a01341708003158805440c1e10202c40c2d41c1d89030b41d41d1502d0002094500041601252400903174001041c00c5d401414240071b01e51389080c400e00800b036003101607412504046000c202d03940 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 152875341 1250 152874091 152874107
    0x12709030c02040b06180f0a03020301090c05210a03050913020c01050106030c14040b030a0e0a03033809040510020d1505060a020a03030504021f020309010f08150d050a08040e1006 79
    0x2c0c10001b50b02221002d213081200d81c410004603507902004940011015032402d205640da001d2280d0005000b80c0e0810303040001c040102c01e840c180119000c0c40000103c5400b1607441c03009685030a14135194000040011080c1c07100c0a18122454800b08044071003903815001181290f00030f8504010180782000120303591407004d280e50f88000010002004021801d1000f194002060b45d4000ba00c0345802417182d0510703503603030030a40000b0b4542400c0d400c054034590700101076030728000d0000010358040505080399040103036030510403a940b00024051050600c40d0401000c01c48004561347d44969041f0001045103c1c0000350344c03180c1440104090034007000321054440c042e001400100c00302d035401c4003d0700c8000d2040341c104400e000d4802a600d11141008a50030f80b540181d900d804c0301c00e00050100d10000301085c2040315035014401c008580c0e2910000d400400d81d88045030102604106241c44a01b04e40100f01c00000200040c2c41540340d10b03901e000e90361085501c0b5890ba51010111852a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 152876591 1250 152875341 152875357
    0x30f0e150f0319020c0d030c0e0a1202030f0609161401270f0b0a08070f090b0d110a030204210203070b07050a12050a0e18012709030c02040b06 63
    0x490420812040042280107180e00c86003085039041005041c4840f04241d07002a0a2101c05902c03200310719240c1901800b0b083d0548113146003c15500c04040c0010352141002c0c03140d050034400e07002c03914066490a0000f0003400008104940d080c2c100309240715641c000d0070000c404500d060603c0855080c91441050b12080070507510024245c08440c65601c6200c041c8600000c07800102c0f400081001c01288a0b10040008940b8280c0b2441d0b40c010250414900402c880c00b002921111a00750030f410001c200142e038444850380e5214a070841c8160002c01401c0700f02c00003110041000000e440d070603002482500d05880a40d1549046d40ea4200c00b00b0f0460350009505400146040c00903804800142541c3c07402a411545249501c1e102e000380c04225034040d40005e280000e20002c42070308811940316868098560709200d44040420308083e840601071585450140c0d0750304041c651031101e4084a20f90450000c201c21407503854003610060494070201e0040d41400400001c41c40d00c00e0a0350920 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 152877697 1106 152876591 152876629
    0x12110307030b01030504020919020f070c05010e01050c150c120f150a06021005100e0f0703050f06031b01140a0903050106080309010c141504030f0e 65
    0x180e060b1001c0715044c1801c28043c0001030329103441c421f90080745500000050fa4826140c24007a06c56400141140f00000c10f055040c401030201c0b0408407482600c8040851100c000151102c1c080d00c03802d03003095000403d20016900300021440c0d400882c50f0f802038038090a601100103400410349150f017440d2042c2e420050400c0310010724210744182140c104410714a0617500940d0b078006107100c00161a200d001190124090448484c06007070360100036031007444e0601041c20f002c1001c440520000e801c120218581c111046005130040c4005000790042500c007400064070220040c40c00b5041054441408600300c1c000406001050b24a07a00c0c0d9120900d075081440c251440c036000070a240d002002261030b01c0e03801c01c6c02000c2a0360f000f00154004800a1030761424220005100003450446004200c201588204040540510341d1111070002e404e0302b09005030000b08070408411 = true := by decide +kernel

theorem cover : BRFrame.Cov 152697841 152877697 := by
  have h0 := BRFrame.cov_init 152697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 152697841 ≤ n) (h2 : n < 152877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
