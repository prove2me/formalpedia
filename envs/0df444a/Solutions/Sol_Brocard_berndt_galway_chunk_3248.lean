-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:55.039989+00:00
-- url     : https://prove2.me/submissions/2bea34d2-ce0a-4fde-881d-b9102684944c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583992805 ≤ n < 584172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583994055 1250 583992805 583992809
    0x5120310030b010803040303080f191817090303031305010b130504030e03010903020d0c171207080121020f18151003050c0a0e0303040312030504170307170a06050316 73
    0x9980c00103a0704d514086850f4040c620005010802407030106000740000505294044581c100e125540d441002048095800d2a001080c20000d01051102881202c2c01111899420604040d16044800000c20756a21000f0a042c01010301124100100402900b11400301d403c02488007807402c206030341d100700810064030114089012107450a00c10704060050b5403110390141c014128040710300703e050750440c02c03c0604841f21010440100400b841c4800600741d1280c0000340c0038014504424050a01c00c3c040c1c100c80110040d154030090481c41a40982d01c031194150703038100000c0b40c060041a082082005481980e0300310310200f10006680d400700c0314a16004580b01c3e10002170380b40c001d404891040e20300b11403441c020460313901100d0003081403002d101809002c59142035a203444481c40708138410a2080040e8580084c481802721960320b52018154444d1407034610b0501c0000a8203000941300b0b8980c00900100001d91070140301d070b012000070000901075400c0c00d0707007900c0038a0b81e4174014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583995305 1250 583994055 583994063
    0xd0911010e04090b070e210106060801080a050303040818100c060f09170a050c060a0204060201060f1214010b04060b090a090e10050a0f0e01020901020709270512031003 74
    0x204a1000e280c1c50320b40a00c043d040e41003440c02c500e949a44074211810040200c0440d0010401384035400c401d9803039081d6000d600280300000078000d003001d0008000c24810b074818082e6a20803149000030460100850345c200d80d000c0e49a0f82e03100c25081c50110b034444203203c1c0982c0558021401010755030080350b001c1d4464400e0604000380304050400400321645050050b004c1d40c0184401c010107121000201207142c00f50500e54244440003800303501d040d00840b010300c941a008075003002240e409001e0f21019191110300c07825400d0a2461440503d948d54001034005041a102000c10722420b512908041201800511055894684503154ad03407101c15036500814900c080020380c00428800d120030202d082d4050920700e00950000d10140030042d100b000401e940d00308880721403145210b0503e80e406c2100000d03880306850340002e42444000d62104079881d00b41034410a401d950940c4403103448484071103800008110b41007042c90702c2125414441a80d10001c24402600011000b007005c891003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583996555 1250 583995305 583995317
    0xd0f050a02130e04060906020a0f2c28090b01090b09010806010c03030e01140f1b03060d0c1a1209071a03070e0d140d0305090c01080c0d091101 63
    0x3655051008038440c0c01012100b00c40c07150340c1400340211400310340b078000b80940000301d184c510f9621a5012a4400d030803000100780c0140301580419041250107507511480d441d114681c0440d0b0445688824280310120b11419600340ca0890b400c144100e03449402c00484014003030b80d5210740c000ca00030022000c03042e020401001001418144150440f4616001030f0754025094a56400542e5201405101202450384800300443c1101c001d1040c001c070040b00d0582a140c42c24030b046081e0140c04007502d0000541c040410f41c40f0003070343c5101100e811241c1600d2080301041d0a0600d501482c006400880c22031541c0c1c00c03800c140b51b00c1c203c064902c585004050212544561100503502d005502c80c440740f45c02c22809003c840c0241c0d201540e030080c128204040740c051318000249002c0002c01086921706090700d800d0707541840c10040c040d2502d5007814208107070b0600c000e482c0d940f410b510700c0302810884100300141394081c81c80c00f581c8074080304407010b10400c580342c03038003408480c14142002e001541c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583997805 1250 583996555 583996561
    0x72a050604110111010b1305072006010302010809061314010e0708070303030c02030705060a09150c120c0219060903091503020915030f0f0411030a0c03060c081605090a0b0d0f05 78
    0x101031140c003415920080c01c03104452600c1d0700010182800502109c107110f450403c0310312124404451034920102c000143c0101d6040d403002601444018220071071740d6214000b00525400b20400103c00303140c100104606030302c04043c605014101e1615800094040d2480024520000061000c250381c801e8805201c40e90309844106c2e40d0b0b008401c0041c0007a40704201043c10720a0682c0104400d5014038030361840d040706200004142e440c06040300c800604030300804650b0040384d00c600040b551003840508195209240c245066203c3c451024007100e580d80c001004050140800f140146079199000c0030303554845001600a40204007454050319004810b00c2014100038103c0e48136003000d43e2081e44d15160407008109034200180100d603042008500300506035010001c00700c015201d0614208603a0075450601c00780d03040c0201c0141844200b0702030001c2c403107508000c00030901581c50142c1d00c1c0e0300c603800000e034a00c9040d0b01c004100302000441c4548901d46030000366032200a0502070082c1d403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583999055 1250 583997805 583997837
    0x305070e0901020a020712080d020c030a090b13060e04060e01171b130b01090509150a050f090712060f0306020d0c020a121d0603010803120a05072a0506041101 70
    0x4460405420016001b0200034850103468071200b03004540910503041c204001c0e000808101da02c03200241949070700c04502e00c0300a41e481840c0d903020f002400c0091381841e01c40d141c120801030071406004140b20602c0740e584425150355014000408448041e8422035950714000f80681c0300b00c094801d028011442d040d0b05403419204060403114000c0c0151208407104e41030700004000c1c03d0350341c0781080900c3d400042e44d95501c0405900608100c401c0c0c00028005a04000402c1070990000c0d0044c8038034007404c542c9603680c102441d444542030500079680f584c0320300303181c00819280c1c00100d04600c50703541c00310500a0580c054803004080c1982000145803002d03041e0ba03200c1c4210740041804070551418141541708003600721080c4101c030005070741f007100761000880039002604645110307800422218410350001c4451a08105025010400c509102d08004c00e203564611121069105444500d0a100d44080c0030f000c00b070b60008103450050030180b41042c1085460591640051150741d030000c81c1c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584000305 1250 583999055 583999057
    0x203010b07170a140318060106080702010617070b090d060504030f17160f0306080f030c0c010c1505060f030109060f1a01090e1308040b03100608040807030c020f04060305070e090102 80
    0x3d540301c0c1ca5110145000741582c000b5640014079480035100818804d8500500400c5010b01030700b043d03100c0c0c48083c985800d009007180c11070fa215100a03d00d600d6407080500c804500c82003034420540b0065580e4407281e001c102c201003501001032105181404100600d13070f01c00342d02038203116540c1c0c940d501c543c0d000c00c7c03000a2200540311760040d5138046d41461106400765004403014525070601154069035104014109440c001a03c045038000107956483c8441c14041000d122a007424040b10725650713915400e0342419100a1503000c80d5682d00442d810b07070b40f560320300c06007004c00070000d1040440900d0308138050007101000c030012904040d030b8041c0450710741079800700000d01a960b440340c603403420410904000c070280000903121036818040303012806c004000c2c03026002c41c800e042c3d41c9081a1902090541007a0300c440e040281701820f0000260400d0116a50300c0c1c0c040c5030008858219000082e0b4042400720704c2a03000e460018000b08100300850b01c101202c80010000e22542da03464038150903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584001555 1250 584000305 584000317
    0x309031e0309100504060b0d0302071e0b2d041205010e010b011706040603020604030f0323070210020c061611090603210f07061a0d0803070309030c02040203010b0717 73
    0x640c0101800f5080360905501c2543d0080c050003000c5000641c81c00410606d0850410940068100e810203002c40e204e1540784139100444038003030108030352404100c003c0340c0c000e1075018400c1004010900900d41e4159110300c0d800107043c18180e90b00c070751380c0c1d0b11000b0500041c1c1c012a520f50030201c0000d28000103100b4a00d107990306845594802d01120741100c401c2a00402e000c1d0703c26030354000030000d070b144e10010b4000b03180b08030b0f0aa0080c143e50700700030b800007104030056408000200b403203254003003400c0d045c0d07020164151030a94003001160b00990420703004614054010f50041510791141c2500b01c203014100d4015503801d611001e2540921040c2e8000b15040e5425502c04003144d40380e201121703201c105081180360303c41e06000034501d103110b00b80e1055505441039a00c403d481a058101503042c0c0c803910101310f0f80c0308607002e200d03500d800d520b02004244030185640c500c100805d05d40110707482070540c2e03401001190350b503071151680c0380240c1000e00240d036580201c1e1402a50100a2001c40d16 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584002805 1250 584001555 584001571
    0xe1c0e100f1404090c022b050f0c0c1f030b03011104051002030705121201140109061b140312061804110607020915090c070b0f090109080309031e03 65
    0x20300c0d045012010740d814a00540c2c68040c03900104000558611503101c0c08440d5001e0307a0190640103001f100241c85088000d416000b04c1800c4518252916003100807a11126000000b43e600c9800107030110b81019054018981c010f05844007401f41d100c4580340031114546a52810010010750000b41070803182080c0906c0e1140200704420700c01403408440c1c00b00c00000a2046910702107540d900c2501b405100f140e40320b2980c0002c100020002d5030b03400030602420000c400303001d8001a0340c1c0003d2140c2d0b55881954184400381440e15091411100c24a030981e421000034480c1c0c4802016040d5a45d00544407081c42c20501400b04400d0b00c1c0a140140c1324000f40140c1c50040e840701d4039000c280041c01a42c003a0301210400011006071515082c651084031051a80e0721019070300c50902500103001887d014042d0340c1004241c0010302401001c540049d0310030390601096480d101154014072074904013401d88a000f0003082600d0714008014100481840e15202039001d4000388264180019980b6603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584004055 1250 584002805 584002817
    0x40f060b0702060c0c0d030e0f090702030a111e0615040209010504090e010f09080c010e0f15040c0504150f06051603080402010e1e0117040f080705010e1c0e10 70
    0x5015140c00009802d81813404e60a03110480608400140302ca10b5861044001c204141314104440c60440100c90000406942c4041607280080c0002d41764481c090100d4140009607401542c1e0300d5081000386000140440c8889032460041c1d003e5545410840342980c1c41100c882e01c0c4241403c2c240261800c2c0d60040c2c54040c10b00d42000f21881c0079140325090300c48103640e120010151440640903600a15001e201403035903070558840f8280c255921807040c0200c42c3e0025601c0d0079446000601e40100c02040c1060696988462408401d522101c0d8411540542080c1c41d00c1c02c01e006040c091000c60328100d0022103540e0351070703c2c252030500850030381c80300f1040d04c5a07140c1d0200b03001e1248642e21902c14945040e4001111700040c0071000c500141800760342d0310614010495070803407070302c1d2001d081c603090142d540e11741965002600300090200418840340407410404000094210480000c2c2d028152144810703560b40709845412a1507090000420003c41101513003006580d0f0394080c40d15580b40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584005305 1250 584004055 584004067
    0x103030804140d051b07210305040e0c210c2b06030503091905130c0203070b0906250f0e060909010f03030305010f0b03010905060402190e040f060b 65
    0x95030300e030000074415160b0000e02d00c400a5140c5081c004040c101040d9101c0f2601c1d0003064010305451000d16405c40099800490300b407150000301c480d0b400c40d800060301c041c8000b01545c603044038140256403000c0204828401440034208900e40a80707a200fa020040c0c080201d81c0d40d48a00b61110203940d4074110950030042c1500c1001c01c03010300b40390014404499003881c2004d05100c0100e801a40c004c2ea001d17080401c0c14281d0385000d80c6119040c0410541c0070014078140740000e504144040700700d80e5040ea5890f814070302c1900a00c02e40f0310396a04420380c2d4115203044049107454190880300031f00c08501c50130038221802d41082683c0104551a95000c1c40c22140c46001e0b40c001120305851075200c0024010b08020fa0f4640b50618041c5c9402000300600f10b255150140c1070f80c030107801ca40e40f142c207049010300001091b14162030440b1004072020416840300300c0464001d104104118031030144040c0f0f1485e502d070700b01c1d18907200f0000079030f010800d500d05d014181c0304480f01406000e07224a030401c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584006555 1250 584005305 584005307
    0xa050304030e040e100c12061a070302070e041a06010318061e060801021e0c0312101a0702091609170f0f0715080403080606030405010e101e060e010303 67
    0x458010b40c40242001036280d1181004c9454901c81510550415480d4504554250781c800d0000040e00b0b0304980510180b803c00c0d8070079940a02002c0c1030100707400b011650106061003004040c004000c0b40d450a6450b00302402d0007407030f020b803050704180c02c8800300d004219154420f10603444000500580301c502c140303881d078501d40a4405005000790780201a20f59071040c0d03034144a0722008110340800107a68403001010745089010410440280101c00d02501c0200034003c0b00301c03589140509030440381540c5110405071039140d190406408104a10f524030000e420007802010042d000b102d811450703a5642903504071116091012030005640d144041040c00600c0340102c04032043d0f201901e4001c50641252480c1c400811620900341e070001c1c20800141d0036284040700101c4c00b902c0d1181d80c0c2e180586001d455004054042801f4000002c0007809100c001c0d03004400e09103202007640c80700902c190500015102284c113041e0031042c60081c4030203680e018804c81d0304807072030a1000c80702130b0300e5030718 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584007805 1250 584006555 584006567
    0x60f030b0411010207080313090b090408120a180c0503010f1e020a05121303090602011103070e0d0605010315060503070311121608150705030906041e020603010902030604110a05030403 81
    0x380c40b0f05622603c01c1c003007405641440500720441114104440c098680003648080e2400d810304140201004000e00c004100010100d90303100e100341130407040c0d41d11a548100001c01004629400710f290380180d54003044454100d540484404070020b10124104421308021103844d0f28440750b96100000c280d40650b103980c0c0281545030040d040c414107010b00d00d140503440510444801d03441c003006034150420950031205c13500c0a00382034802040707c5100401e01d54200d00c00a05039005000440b504c0503003035038503d40e83d90307951540f21340140508d580d17a1510b0303026003401e02d241c0e28200b41008804101ca0a00280e588101ca40242c2654070454000d42070040c8c0c14140803442c02c06019a00800c1c048180c084001d90040034a2002003110652813640003810701005419042000020070a004410341d00140b03098206070000c1480d02e80c030640c00b14090b8804c0404e64003c2d08a08040000612714501c0d030301a41c4540f8056805001e15651010300c98802d20489982602103001800800c002c284219 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584009055 1250 584007805 584007833
    0x14030d0b09070e010f0207090e0102131a12060a08031209010608030a0c0b0a09120807140702031c1e180506072307090509010207030e0405010810201c060f030b04 71
    0xc010341d02e001341c60302072321000d84039000c03810807a5a40002e1903040801001d20140c005141d4540713280b02d070070715100038040144120150b2148860a02012448540c0c40300036001c018005441140d95800c40c8044c0740e80d13910303011242002d45502e440f6000440490100448200a4055a45d450264450f070395030301503400082c00961086980b641c0e041c0000341207051080440d07080341c48007201407812050051061f990400055031109050004600586001400340030070502a6108040d450020900300c4201c2c1e501c0000c1c912507103d40f403030751820039003000a4000000000401403c0e0741e45520034041c080c4103941004146206a0710345000340c142500c104802c001e464000e54a0142d9600c0c8090140c074000c0d5090441c0765400a543c0701050b0301b01c4070384a1151410f640a21056252000350360700c0701142e54a980e002c0e0344404c25400161206c1c0c4213072800040341010f143d190304401020000c80b04031407141141440c5840350104013500c40e2401c0c102100d601c0b01800b1950355032a624101c1c210f02e04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584010305 1250 584009055 584009057
    0xf0207180b12060f0c09090f0a0908041e09090b01062604060c0e0306040308070e210606090a0209030a022b08031f180203070c14030d0b09070e010f 65
    0x9401d544419079074041c0300c000032075840402400541480d40c81c45103551000b600700c07109400c0400c6081910303100d006030b140c0c0c01000c252402ca19039590701007030340142900c0302004100020002c0e000c42c002d0003401030f403038001814101c0e80c1082d80d280c11010045030300600c0c020b4030590400004005662141742d2554541b56640c205103900c002e22440c0109c1d000043c0d4084076034644421101e42c510b5401521102ca0b000d08a0003054141466100034062080c00f802501c100503a4016540c942c0e103a40107480341946190484005180325168165140c91041e941948212001c038042140d1041030700171354065420080241c0405585035003040480c801c80c440605502d507028404074074900342e400700e01210307a00a0702500d070f49140456205410503600c1c40310308980c55810f01d043c050540410f20352410100075a0005030781703407642d81c0d00313440c1007c561000070801940d00050504101021000c1c00d4128803680c401d0001241030010000c02044c201c4072080000c603a00090170881d0300c590880284001d076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584011555 1250 584010305 584010311
    0x31b01050c0d020d030e03090907080c0403080f040303030507180b091305270f0a06020c030c0601030615151b0c08072d03020a0b0306010311030a1b0f020718 69
    0x401d031441da041941000360308001d07070001c0e08122421074044c02412104500f83c40910310300b141340d400140e4050310141c51401000000713030025080500c100221030181d038014281750340700c1ca40300340c103030115a20500040300024140740100301d13680e000303610751100c40b00c0100221500d60300300055210103400c07c2007196440f6164510041e03003075400d40f040e02d01664038490b1000e1148440410b490104c4000d080e500a40e038801414214501070114902c141158007000c00740e510054810818030758000c11114810b240034110000082011950105181c0440d050721074801c00c1d07503518404a255000b00862011030107215194240303042c140f00c1d40803100d120303014809400380c44904c00c07460018070b60410540c4c4810900c2a06030611130b0b183c000c0c0302c440d2403818103403103d05503404203003140602d03c035850720782d60048049005603000c4c2e000014500200c1402d143c6901c3c0507510f8001038600010311521002c2d040440072100d900ca4400401d03c803401c2e400a1004501d001100d0340d003000003c80300c07058256 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584012805 1250 584011555 584011567
    0x1030c0608090111160c151709031306021f05060603040201050309070806070507060e03130302210d0903120f050a110c091e160f05070201020a0c030b150906031b0105 73
    0x503108060403190717050305003d0180f00860b00d0318a52062544e000400d51200d01007106a259034043e00e91171402c804845042083d031550b50700305145002d43c010189030b0401d2031002080513580080ca112403020111041078080412800c44011a0f070140c454540010f01040050f0155005200441d00011030701c0841d0400307960344075540c1c1040402d41e071000c0011400500d040c240b0a0394082c074070081044101548ca00001c4481e0b00d41d000c50740703120090044c200c41644001200158441e5440c61080c94103030703000d0a0784150001d045078154041150802c20310000340c59841e1052441d811210980e441d41868140d00d40341c02d440700c078080020886684229116610146c40e119030060291214940c4550001ca5010300d102903a02c00404d9051203480c00745040b00d40a5001010003404071241c20850394a103a1400100d0400d41051005401050b09840010800c05000040744c4108484150868900504801c204840d48265121503050740010084010300e050010610700508050400740c0c1350030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584014055 1250 584012805 584012831
    0xa0509070e030f0d11061e0c1b160e070c02010e03030d1e0b0d0b0103022e020d0806010e090414071503060e130f030f120f06050a0e01030c06080901 65
    0x3211407910f4003080e00000320a070242030300600c010414440d044058030441c41c1800760042c850b009441c00ca0502c2d00340c4804207141907860021100c0800241a0749030590703d080400599540b100082d049160208800c00205c480c80c03403100c240280302640d40c6400c040714035001110080c5049007221b5042c00700300182142c000c15442440e0340c101440f41ca1502c15281c90a901d4100c0741c0762203046019030006e1000c800001c00c8590240d0541c0e50455080181c850304c0400112a9100310700180c0220b80200403a0040070380001d030320141900301d55907040c0c02c0e540d9900111400c290045d002e64101324040b000c90000f8800d05440700070000040103d0300119580c1c5c40040300d9110600d40c49000c6030303540c0e0052107400d400c01c5001d80c0c82400b80320522540e6003255a2181003110010002d802c0203c88001c3d4000d9501c14408540e0030040d09200344041c1c840d4000d4600201920300c5828456001003200003101501155601d04036508500c02201e443d20b005000d95000d40c0041c0000415541c504a007440c0d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584015305 1250 584014055 584014063
    0x60a0513090204060f0e0406020721020f06091605010e030c04050408130e130303050a0608060a020c010e1912020313030c290d0c021c0807021006050a0509070e03 71
    0x100322038102044000050050004642c0fa9400ca2040300344441c4040c091000942d07040780d040b0f58401c0380182e40d00c0c03d6082c150703081e0f01d010214000810b40b5440c00c0c0328203680018501103502180003503d0058441d44007281d41c3c4d0901c40080401100c0111080105601900c0103070040076002d8180d0702d002d11041e000a0480b80c0c12603046442b0400440d04255a80410707502c500905140c05c0c24bc0400d085c416481c00c0380700e8615000808264540c000900d01c0d5405401c440c1c018055041124401c1c01c0284102000e50445001d5203629840e06901425a0a0000d4201281e0010713401d280c001c05456100c1d0181d04100064000035440704005c2032200003807080c0c0340402580030303080c1d401c070213414003140b5035a0740300b458141e0082c0e000d0a00c544841e00342c004215090150540000540800e22400590070003d450b01c0b1206482c444204207c070082d01300d000c00344200029401d50f0030341d4007080c00d0b00044501030300485030401c030b03110070030300040c145002c4903500040c0c181403082125072040006441c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584016555 1250 584015305 584015329
    0x151f03110408062d04140f0601030b1e0c030408030702191506090b0117060307030b0405030c0c1009030b07031d0d0906030e1005070e0d050718060815060a05 69
    0x164022410130015a00280d081c101e00440744c0c0b440c0300c1020b80c4003103001c203031a4003900151480c0701140c10f46011307810800c00c4900c8081c01c0001c2e5461980c0d281410501d00d101100d40d440c9a005000718180c0700c4c90500e551a1241713902d141e00301c0c15501c464656000c240c0000b8040c0096100e0500404480c126a51651010512440d02c030300340c00c111000418241c0b0402da0160b80d105040031510705040e80c00400c1103500b40f61003200c032601c0d9610180000e02c6e000441c0d00c040c0040b4141d030700b800203010000c00203100a0076901d048960310800d42044c805629100e003905c0001804007081800050006c0c01915003003030325407401003800c1c2c0380254480c140010000d882c045540c0003880450603150410300d183e000380214242003241c24140212692201041c40d01c1c1d2030419030b1000019511405070411115480c00139225144000080c505035030b4440550103503107000c03080c8855441910b10b150280030305584240c800b412014070b18a052001616000e400541d200400820102c2c1645903040d007982 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584017805 1250 584016555 584016569
    0x1311160c030f110307151d040b0a03060b0a150f081b030117060901021305060f0f0f030106032703030903092c0c0a140f091512151f031104 61
    0x8203c042c42010140381c00d04540c807241e0140039244981080d00d0700700c410910030b80c8940340822440403e0800080041072051006503200d0320078a0040244902544030302000b00c1c0030b445201000351035102c0030b809140d1400c0d4204c0000c65104c2080c2c401d83c85024216000f403083c841134101c1c1402402e0715030a64000341c208407500d00d42c00710098810582004455080a4080e008500d0001c3d8644c903c0340d0301c4080e0148500650700015001100700c2603a0480750004445038800380c490181001070001e0b58000e119100c002420806480c0d024000d80c4081e4030b4170103862441e00411f44081e5030640140522400940504c0a80c0d0400136152265044001c0f0001c0da4906010350f4000f0404400d555220141c0940d41e4540e052000d6071100307401441c0d10307039000710361903255031110702d5100c2001061140d0902650803501c180c6d172030b41440b00604050441d44d8181501001c2c180d65001c40c2c51035447e0003042d441d51018a07107080c104245444a211940d111240c58007241c042c0400441d964241d1103544051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584019055 1250 584017805 584017823
    0x40f020c06012904270606081807050405090307031d010c020409060f0c03150b030c0d0b061e040302150c07050f0d060e0f061015030218090906061311160c030f 70
    0x6140c0d54030100300245070310100410442c6c4c5080010061000200500013000c1001804289200c1075003004154020b040c0108144254034004040a84030b400c4074008402086c4426080c5032011141d803803584004006035220f010b044c201e07408101c00380c00744c0e0006482c050355032200c035810800203001315180142c0c140c401040340265809008100030b00c50388014800c803428030501130034000c01c0046501d04c1c0804500890b1520750500000d65a00c25441592802b4050b40c88080168260758040e00c1164000c070b80303465011481c095201c05600c01c1c9a4583c00942007000184014038002c011840da40030050300500d4413124564031703502210800f04652010f5481a114050b0a48040100315400b004800f0301840c45850041e0050521000d40500802e1580105220184c41c8131030214810320342d40101242032a0a04081443e101c141c107441440c01a0703e40042c90190f002070303020380307400d90406110841c82e10781244031aa000c82c1a425044950f03588441001000c210f5210b0b4a018160140c1c0c100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584020305 1250 584019055 584019089
    0x3050d02120a150b09030307080901030608060f040309050901080d0f03062309070507050706080613020a0f0f020c0a0b092e0305070903020114030a0f110702040f020c06012904 77
    0x540006032035001c007113076440400c442903080d00c0100c1580d000340d600c010b8090315180d6403001a0b000d0b09030b54100711514800c01082004030441c0c803502c5030149001e500ca0b207600b152608244009403009004011060303021040000e00c2c036108084420444085240000c5d8090b10340e480c030f45003c550452222020030031094250200c1c9001d101d5540c0058032030070300e070b49060f404ad9500794441400e80319010034041b00f040010810f4950940300707401481e81e6501190b5501c0300000103490107074013005c1d80001642008003030044074000a0943d004010040c05204500d1510300101c13010ba010011aa400000c50440c6000540e803000d00314021002c1e0b04040c0020540d440d20080031240c00511120800010010810143c0d070040e0714000c4140d44100751b1a5a90303903c2207d03801500f4441402c000d058a40b41500c14891a4440540100d03442200e051001079040c140c84001e0b03000c4d00503c6c00458200a004200e4240c255400302031008a020b1a190a0344000e030307030552107800692040034007038a01090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584021555 1250 584020305 584020331
    0x106200f0a02040501080318060310270b032a03011d060f0f04020d0605060303120702010614030102040b0f070f080d0501050f0d0f06110d06031112030a0c03050d02120a 74
    0x13075a405000000011410301c2d20b85000c58030b401401002c880d002d40e80010219003401500a00c000150040560310150340040480d1020b80700c20316804000c0075840e0650b034004510340441c50028605591450003900408a0010214143c80010141e81503581e088003050f2461010002c0b118040364030003400c841d142800b8500420500284664420b000c040708003c016590b00500a803070303e030040300c0042c0d55603c10000c240303035108030215142094498410030a106030f05400084c207540c21000500a11400002890300f83e0245000b40c84181c2d02c248078120005552002800440340104507035804e806503a140c10003151711440e100004152120010310031400d0048903107044050684034012680c0300343c0c885210302010564002c20b6035803503580124040400206440181503207980402c881e558034900700403803100d600103190041c0e14403110030648030350200030b07100125546d0300c8200410700942c0c4d0490b0140d0051015a280e10740c2030202000c0317a0102e50003d0720030610828005010901041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584022805 1250 584021555 584021561
    0xe07090e04031403070302070209040c06091202031005130c0e070305072115080d03020705101413030519020d1d0f0904050c0d080a091401080106200f0a0204 69
    0x1003020100c0000c107110009a1001e1202d200708101000c1070707102c0e210301030114007910031070328043d5022114505200521042a0010045600649a241041d640c1e0442280065a480c002a41c907400c100001d001c022110381000c1e03407044100300e00310fa8800d280d940342c5204a42c1500180e042d40650000c0184854241c030610381c0110403400c3c1030340e0030554003a030310400e0000c43c03800884251300c540c4040d12020308415108040c10b400000c1d540340c00c421a400800a4001010070344441c429030040c000329880911075610010041000410b00359112014044a0a22503c00310f040181c10011020381188010401e50b111403184d01a24640703540e4040141344040c00001c0c108007600001501580d42e5601c60700c0584604246c0744640141d0310b034240142440302c0030b07144940108044043d0020070209030002e10000c0001c2d00c40b80186c40c0c031120045107a034106800c890200e44410b0060003060300485070341842c9003c40b441901c0b0054095083d9003050000030300020298006010780d011407030030340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584024055 1250 584022805 584022809
    0x7140a060c05031303121e0209130911090c07050703210207081e0115060e0a120b0a020d020d0606050405120c06030103230304180b030c010e061809010e0709 69
    0xc50428114140000300f107101101100005080c4150006d030310050030100e4006090712281503a5032081b0100c0c10008a0103940300001451003007003840c0b014224900d50b0302c9900b00c036540250040c0703c050007860900000350005080b540c4603076002d0056800181e010400c14000e18441d601c0b166070100820018001001816529025900484024400c44a00241c00c1c10a0941d2360050300303420700002901401040420081e1151200e00030010504640000240401d9402034a4542c806540c81501c1462444107100050450750300034041804004071740c0180c1840c0107005c5005103041c040b160030b40115070195000402054011404102c0c80c580802001410481180508142005040000e07a00d2205020042605022120750b44070710483d60800d0100c405860201c03582c950710362980759150041c0d10040343c5880d00f00314071070440341408207240445071010b03111407621000d000104a1a5044400301014920700d00002031119a910890f0b10700030b0400140c0c40d1100d04102c10000c1c84034401d6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584025305 1250 584024055 584024057
    0xc080d0617060603060f0c0708190f1407080f090904030e01030b011b0f170d050603122d0f0406110c030c1c0312060315061a0f070807140a060c 63
    0x41070030403c4a4501280d12948040c4803003004170b16035100000c07607000307000305000900064400324480d4050020074140744948001d5460311100301c503000404482003c08800c03a0496000d0074842da00002d1070300c0c00900a581c403120003180c14420303881c0100d40c0081e000ca40960003d002d00c0f502c0007240d40c151140c0700c9800c0081c130f0954a10b8599050007550440320140c01003c242c4032015041c28000240d0030304404690411641c0c9d0703610400ca03a8100a407400b81c5151b8400d014007100740c010700c1141070880f200c0200000b1607640094000c00740da51401d490887e21901c5840c2042000e184c800e030036004001410701074440703500480d01c509d0058940b49a01c4c00881c0240d01100011640740d5581d1101c003847e1608140c102d68074052850b0407614462030341d5042844a0800d00c003c01046012035624031050040c40c0c04010255075a107644c0f10b61464803400494910003000624074192201000340303002c50041120a1400d1940e903108241204400d07540b41840d00300d03000c9041001064003c0c00708031482 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584026555 1250 584025305 584025313
    0x3031e020309070b030a02090901030f0c081507180302030613030e0907050304080a02030d05041a07020106050a0b09040209090a0e100203090c0904210f12020304050705010f0c080d0617 81
    0x81031042ca9601d4615009084001401100051202207190115061000080c2070ba80e02544d43e850071585581c0b01c0c000c01c5030b8001c907000c00490a9000010003000e02d5085c414509101d480e904026118070204081010204c8802807011001da03c0401c98a8003d0820519030480d80645040003040c5610010f0344500c12803c0c2000d00c071101c1c2d800400d80750400d0f0030842807513503650a0f07613041c0d1a52050304c0746c90711020f041c4020072060040020040c079062a910003205c280340d5841c40f04030300b254298000c04e03520a01030b041c140000c115841c05842011b2001d440146410400800980501411a10700f6201074a81580c812280000e01032005844a212004d50941c201003680b541c83c0c01d0125840b030300a1120f40001414480060300c001004100040f0910b00321500341c1005040c840c4414201d0301103500c400c20210f03001018400c41e4480c540000150038114200401143c10f821240303040030410106103010008515400300414956008100001e0f519103849600d1640c110300400700c08140e04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584027805 1250 584026555 584026561
    0x100e0607030c031a09060112061202040b01020c240403060e01050105010201060f03330207030c02030c0d02011403090304150c1e03050717190801050307080d0c0b0604110703031e0203 80
    0x5410030f45480404c0040350822400d6490500407240c0c40d5a42d115140c606042400015280442a00a440d40d5000b51024001e581004005a039207035204004a0341041c941c000c00725100d0480c1484922074418000003d2515940e42c490b4800e542d4400b80710907041e5558001000039603024070550004000440030a031549145858007451380c8107081e262841104c0f01c07030130741c403811254040c01444160400310031500d480e007130b080c000d2403210381c01c008a01a10441103101388514003000c83c116040e905944074501d4610220051038560405452040944414080450410705480300e00e5840c5049035120140d031115800d140006c41d02e028886442e007900c600424000c2035000c000c540049800c03509a43c0c400360300400d400c4040c412501c4c211003888007408041c0c20070740c0c8034131401d0484400f20101e0304d40f10703280c4142503107440100d4007034004038009124840008021107803c0703520000090001410902c40844a0110b41c840042100065910f00e1071040196010b000b05560a203441000c60840c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584029055 1250 584027805 584027831
    0xf0c0307031707020d06090503070611040b040b071e0302150c030c0409181209290a1d03030703030203010305010c0c150f090f0f0c08060f040201030e100e0607030c03 73
    0x44030390701d24101c10b0407000400009540b15540e01c030185070b031702c504200180860746c1403054407134004510440705c1ca82000180440004280e056800f0381796408107040c50a072a11281c0d00050b4041d00c0d040f2500060000c1000b0740890f0b40c201110311038002e8019044e52900d681005080380002051000c040b101802407040d800e022200340c40580d14031450000780c0900401d81803002001e184001850300710000f001021072a400620b80b0704945016804104c0411602150003030203007140d01425903101d0600401509511411801c0c05030146d125070300f10564042c60101341903501603101030b80801d80000042080202c24804c07060803220914051000d1110f643e00c1c1f0b100003e4014070008266100c0582d11a001a1039110501d01d6a2216424400f100c2a180ca09001c907030b658000e480f60407080100040115010134203d10851940c110218a45d881d540194003c1600c00d10b00c1005100c2c880600070034812a2165041407000c00005108528109000030161440c40c1201c00070076007000041c8044c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584030305 1250 584029055 584029073
    0x13140a020a1e0e220624050f07081b030301060c1101030b03060126030c0706030b030d0e091801150f0f0e0109020a030b130e01060608040f060e0f0d020f0c030703 71
    0x40c0c8030840344c0d00c5440c0c02000c852119040c0d030412011540d840c00d1800106005880d481c00d0b5082640d0111403030f8824554019902401081d15030110300b0780030026100011400002460940400022000141c0d94040003510b150000d800880224100301c9c803a20901002e1070780c3c50208002403030103100819110006c02d403907480620074849801c40005550354040104e80080350110000400c5a0f219180400202d6884456100301404249484081140f9040202d14007440490039225132107400483c6050101c00c0c400100510209041c01c1498082180213000c0d44002031807407452601c442d41400103428000c417441c1d124031402c0c0780d00e042c1003102038030000002d030440d07012100068462620311000d0380a0001401035561150b0020803203003601507507a0010418403001c5d4001c126081c0c0340c0f4003d4500304020790380900740844044000c0001185d80e00704080001030300302640c20781c442880311513141144401c01040581c229020900c40c0704020441058441e500304c00074102680355417104954 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584031555 1250 584030305 584030327
    0x70302040533130908030a0c0201020309060c07050a0b070522180b0a05151209010c050405130f020301090603030215040c03020d0f0b190c0c03080613140a020a1e 71
    0x403292011911410b16030341c0b9540c40030000380106042c0900301d11440d0050003540308079800b4000303034600084868160320510070760f0b2080e09000c00500c400d444000302c14103c3d0704040c030100d603144203d07042d940004100304902030281d078007a1140c5403500c99500606011000910110f1400d800b520020482c1c5c8101c40d0311603108040302030700003c4035101d58001c501040116041550058080f0b0b1a0b40e00141c0c1000042480d010f0f207660030885038641a45a81c2a1411107003c01d00240702440180100d1030244661006113504800002d0005d0251525100740c0c2c1090748490401e6035508810014981c041c4889038007c0070381810145189840d50b60f144c02c8a945000103400b52640d860424104480020f01715641600b001c0000c000d403800ca908480d01c0c0c22518030341e0002c0c07410312905c0303103040380140040c18429034035440340c4a440d540c81d010302030700c0c2d400303c940c0c0714426031144132030030201c0c0420044138000d00c88070101581d2188003440282c002c3c2038804e821a2001000900441001c2d4882e060842d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584032805 1250 584031555 584031631
    0x14010201090519050c1e030d020c0607032a061e150e0c0c10050403170403080a02090604030c0312091a04030b042409120c1104090614090703020405 65
    0x144401d0541806881d001d085070480c1d400c0760f01c6c510090346402e0010301140c0c103041c0c1103007203079001080c00d07408903100d04031440701c0f82e000740042c0030302800603002c0e4076401000044998004e18801c49c0c4110304040b032003042c0301a24903e81c0ca20301d810841200c050706032018580900e00744407400c80380301002240d4580c0e10402c61441c10791404a1444004801180da643d07528000300c82802264180307010046c4401e6804a020840030501007200c084115034192080f50941c890080c60b60fa62011600a540507044403a884401000080000b5030f9400404010718010b1590392001406a10080e00d0102c89400080131001d0840340b010703910b54a14202c0b011380ea40304c0c1c04418203450302e07c2d01001e240124030414100800c402409491043d0b80d90140d44118011104140349040081e0241d6080088820161510510060710f1425003000d8004410b0240704190000d105a08542c2900c00d5100980751402c0640000008005600e041c0c00fc0c0782c0c10149188204141d5070495021000301c10766046012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584034055 1250 584032805 584032843
    0x4051f151202090109081006080601210b10051003020d0b0a030c090f0b04060b0304020a17031b07030803010b0409050606040b030f040f0804090f0e010c0c031101090813140102010905 80
    0x10718503905c55014207004203c04400c48140e00d41050040000c0c0081d0300035030b07007244505000011264049981c6114112600c840205c0c11549515003840584008203a94918008524001100d0301d070060709190340b07019980c1c0140c0f00d8090310014030585d0100c00400d4490342e0713610414004198145040022514104000501e26200e12016400b41503034109241e4424606080014040814801148620300c2110b10100c020307129214140100d450005c0064158018041032182c404000c1c1007100a650710022294503954aa680c644164400d07088140094400f00d0100b0188100e405800c0d003101040f01c0725070a060404003100d40502004215074400081000420180280424550003a41d0011801a90341d5100c80480016180d00307012100c045142120b400031359481807252104080c015907403404184040e0710126080d003000320050a4070f550703802986000440c00d4008205c0700941d8038500066510700386400780c084682c0e0f143c06040d641040d90040000e1404282c0c110035070701c546249 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584035305 1250 584034055 584034067
    0xf07050d112205130203160f14030c120d08010e090d0e010e100f0f050c10020f2106131a01050a03020706052418060f04020904051f151202 61
    0x512640c4812003446110a480c3c0340500c22505500c0045480d042c0c025012a4420016640d4800750700d0001e10803a035500d030107041d0070300c000b420307582d110502e034031004003100d44842c00c541c0005c2c00031a00340720040141e4403c40b40c5c454001c0c3c000341c06600410f00c1100030034251421251403910750b0300d00003007403041100d8045003200740d03030054085031105040601503010000040c0c0001c0c088020704252940406c0300d0401e4540b20394410030454110242c5d40c0c000c4e00341001c61050140180d080a588034022980501440c80c0418117103241048440110280420505020040c420003101d4201080714241c2480d1001201d0401c010030880750344020701c0c11640d01d600c8420100c00a000708000241028102414003d8420041c40318002501140443c182261111000c0290000c44107013591150800316000858030328000b07408102d1010081c001525100f0a200014102d07881115220320080010108140ea42002402d510180c42d0001815140f0002c140c005072954a4104c005001c0755000504 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584036555 1250 584035305 584035339
    0x3110f040e150403080c13030b07031e0f0b15090f0604090609020d1a030706030c0e131a010503130209040c0b0a050c0c030c0f060304061d0f07050d11 66
    0x103100901c03002907a0380090040d48100c60340006840640004810102080805140c0c0303044034403141100000c800b24605d0740d5a15480300000804250905940350746040007560f15654481c00000c00b503c0c00286c4c4c081007a08101100c044c2e4174900d0040074050100380001c0c2041040b01c000041c01c603080741c10074400e60300043c100d00c41c507041810303900d04000e00082d40300c00c0d07500503101e1440080030134000328041609111480a1000700503034198401c1c9c50401c40d8600070b900240000c95a460300d01d00c030a94010110b5249485609842c2c0100d07a10520450780d903023a880c80f58074a07402440c240340742d402e0004401c1183c00394024003074456040a000f080422031840c80003030050082c1d030b1560391101035442d00030f021600443c8100d011030084884e0100d5524012400050f001030040100c1c071804418010b000c0c0e5a00001d0049801560f54902602c2400c80d0070400700aa0303031000002c0c144402100c0754541422955400746014403040240c1d0000a5044550388448080c155003900351490445c403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584037805 1250 584036555 584036561
    0x80705071a040e25020f01060e040804060f03150f060305150916020f0601080c1003020319050408070c080102090f03011103060613150825230f030f060f060403110f04 73
    0xd00900b203808a21310341c42c800c1d60081980c0001d01c2c0440300821005940320341d102009202141c1c0181154002c000078881e15018001d0390311000300b10701c0c0c0002c81207100308000701a011340742c00081c8420713401c01b030400a05515004003603200b840000300c0c107034040c484000301d0107058024021306141c000640160360064420851940354910440c102c80b030959440d01026121b8a018081e035009140440c804039a0074040e0080324028070150400708060071100605200400001d441202e101c0d8040002f440490b01e02403c0c0000742440704c00041c0d6031802402000b0500700d074040300c2c90103a410a1560030007490302c00182d96001c10103651300d540d26141415000070419581e00148003052440710291181c0f82d02244240c070601014070003590344076000c428207040000e00d0192030001340e265110403402600c40d00905039000308170000141408103144200519400490b510703504070384090200310031480c185070b2040588000380ca00a2615066881c0e030b07409444481e0743c01c1d000d03005402c940004d640382c2e031f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584039055 1250 584037805 584037841
    0x50703080906090402030c0406080c0a080112080d0e010b03010b03010908040e0c070c060306210b0403181802070618080d020903100501031a1b0405040f0612080705071a040e 76
    0x13042159240350010071420f10f0b07000341c0107090004e0342c0f101c001503c240320303c400c841d1808226101d0030440da1030640b500c440c509a0850031612400180300100e41000315020344100311554000204020850109150840b0000c42c0f106220342e04040c040f80114101508841c1130760075500e4002e500e83d41d83d0b941c81c40a40b1034030344002c2003c00001c400103001a41a03202005032507003d14115145642e101e1911280003a40c034000d0405a40070f404180080d004910300d1911200c0c03880341c11007060391002e10311105071007400011a03051b00001e01c0410421544908900c05420350081e100c02c40c005c0e159504507003c1d01806c00c400d9640000e1aa050f60b40400c10318410000824060099685a103000307200c40200300c0e0301065000140c80420040e4504100c0121403d10506070030341041d00e03010402c40640800f040030684541e458801241400005c45940d0080c0c1c05451301b1a614000382c03070400d18040141d4400602c410b000c2c44c00c0050103500e002114100c0e03a0000b90103110344c0300c21080c1501024a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584040305 1250 584039055 584039059
    0x60a050c162a030c0e01050f0913060b0a0915090c080f100902030712050f06030d0315030c03030c05060a060506031303020c132c0607050714060708040c08030705070308090609 77
    0x200c2c80c00400c205150b45072805443c4801c0715200141d036508140320003007107680b40160b84050034000080044284008213640c65000b41d00c00300301c4000140c0441c040d4002600014940ea0300c42501c42d841e5080e00e0b801000500c00d2140070001051031038002050390601800c000040c900d001c011a0340a4928104100502035101c0c08666a080180d0081d2000f08130b1200b21068030f080c000098035050300304c0f403451310900000d4007604096011050850003000c0300a06240085a40308011011561308049540030b544a80c580070740c500d1140c00d249140040c000c00c0030302c1407814080e05210549613402580c3d080901610100d003107200c3d070b140c1030b800d100e801000da44d0010140d101c02c1e1022901e580003018100c000d01c40b80a08121481d007491403400752030300108a90307401140810303038040c4244010000a402009803201c910841c0b051307142480030946d000c400140002040c40203000d035007004500140317801d200440c98840255195034448125100240000c1b03030100300031078240c5410003181d00001d40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584041555 1250 584040305 584040383
    0x7060c21140a090f0611062e03060203060432100305010510060f0306080307081809191b08061e04060b07050c01020303012402010209040e060a050c16 66
    0x31140b006100009900c14150035058080c400241ca500804d00707610140f003070350082d024a55500c2c0c0640000310520f92070b0181c8078601380044c1141c501801c45500903500c145405603813410030030701300019200c420605220b481d61411960007001003003090007094880c005e803040078035583e255586803c0700041c0c4c0064003d50034823081003c0d11b001c0d146c140c1c05407007441d100d5001c14811410120308031605400b8002c0c0582c010445500802c075610083c0c89032042035440007445051a40c04a482c8140c203442d8420032200581480010124500840c0c019281100340d00040c41007148005000d2140907040d94090450041c81401c0f01e4800c072480c0c00005000b4006110107660f401c654800c59000c101c084d038a502410740352020640c404000c0b641220302d0460505601003040030307001c00113100c03c0a04001c0d507500f0024480303d41c0302d50241840300c2c0340980141c030807460142e40e43c60548070028070486004d0010050b03403440d40002c0006150300c54021030882d03881102401c50114220040d164007584103c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584042805 1250 584041555 584041567
    0x10f05040e1c1e0f0f03110f09120d0f031a01080601030f14010b04080609161707030c06050c0f060708070e011b05030403031107030c032a1707060c2114 67
    0x1030048072134106202166108000c100d01c041003201221128039911200940070011140410807072009000b00714001003010000400325610a8988400c0185050110302e07440c092440c1e282c1c140c0700f80c0c00403100ca82910841c16001030002030000a00a0241c0d0516a407004c0700c131459003665020044508005107641c0641d6111459540c030f40d003042c0714a001078829440001c0044502180c5c2c1c3e0300602003102038441c81414078103a100300c4c090340c1c56102c5652245920000116502040705401400541c80381640c2d070405601003828165042d55a010692224052101c05507029002580c4000a031410310400b08042d401283c1c10183e01a10000d591226070b020010303c1000320007442140e1181e01d4203050031a2601c0845c0c0c0b83d01e07142c40090090780c24400700308081010305008094407000d525100508461040903a01100c1032900f04110003240b03ca1010502c1c14100700c5840942024107003021841c40c50768640101300b010300c41e241c42c06c49010030f000e032500f0f02030040f0b80000c402c05009191910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584044055 1250 584042805 584042807
    0x50706021908090111120403300c03060b03160e0301090c08032a031c0b0d03030c02060705090913080c06040318060e01080f0c0405030f06010f05040e1c1e 68
    0x220540f80541c40e54600b020b106074140c80e481c220b07282d04840c203d0b02d0b1050350b030340c0e1010b850b03000780d4121800301c42c403078001001d0030440e0f2560401c0c44190701d00000245094200c41c000c0843d0f003e80c000d500da40c1410400c0c800b202001c1c980c02c00452006103001e00b05105400046409402c001c103006103001c1001c4d101081d40c40011020b0701c075817900700c8404030040d4801d00d0302103508848844504c0454108200c03902c000b159400f22510b0700441c40700302244400011011562540120009400296072a01000001ca0341071104c0c9801c81001e00d070003410006c00400080000001810a9440303c0140b26039104008010381910403811554007a5003280c5440c0c1000740400c00500d203000c0f500c400c90400481c08902034201804003090681d00d81784c8a03650020600c2c5142e03005461103044030010300000446603010070105003454102000b80a807540b42400c4000d5104198001d1403040e03040c8861030002103400108860440201c2c000c416a0401c620006d03605c6034043c18002c90607082e1412008006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584045305 1250 584044055 584044067
    0x1201020f0d0504140109150e1606081f06140702040b04061d0610050315010306030212100e0a080f0a1202070f050c0414011401090e07031b02030a020d0507060219 71
    0x1e18000d6881c030780c1404d051034240d8203c40c034607140207050606402c000c00e80d1440585c406014114100103c0f400844030314500c003030000e4950301101c005a000d070100002c600e15001d00300058a1000001c00c021400c10001402211a0b071100103110351000c1880402e56880da0059006400b003d081002110b848107121080e000e441c900552144851001050751030030982d00c40c2030b01d851642d50b41d9045440d00b400c84100400201c4009040644502c800300241e07652040e0100d80c542c1007401040a42d815140d58004d54084882145041d001044140e001ca0020411035600d50940c8000c2d980d80c07200510242e8007040c424210080d010300c0400d0040400810a00c810b030064001d03c1147e04050390201040195110400003080c0110440300400c800070324840000701c2e24005040034600d45481c1c5000380507642040766a000001d40743c4000000002c120304100c156408144081e5280c12001c99001e580c41148003005020001d0001c2e421080c0011503041e83c220042500100308910404030300140307a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584046555 1250 584045305 584045311
    0x50706110c0a02010f0c021e040e120a020c03011a06030403174006050c09040e1b03030304030c03080a0e0a0c060206010902040f120f020315041205040605091201020f0d05 75
    0x41440021903000d031600810006d00d503e50300418494482c0d01403050840d80e80b0320300c2d903207981150300d4410304840750905101c800501c05000003800e88035903107800001e1506100c03034003030f0303020341d2421000b181007492812024515580640d51550b80c0c4c0c6443c6812a01000d0580c3c19903001100c0323105104ca00400d6a102081e00c0080030141c41044490070f4101c1000b00d030740302c0303031120f003c4090500000040e9550000c2c0d50010440a103581840d0840c0c02003401d581d5820061903141d004000c02c00e241c104515881046410103400844c19403501d81c1d0060b20000d8a0f039006014402280d0004800d10525000030251903820401c0c0e0311200c64625040f5025002c40c02248098003412001045050307441c402d0b9808c607030201c04030000440c81c0172421481e4080040041ea445d896101e0740c4e0000d61000c0080e0001c09140030070070401c034a001d04088483e0800e2446050801400300010040701c0d47c40380130f68500c2e1104840c410900c0301003003650340c0280301c1c040303607205200d50100c1d803c4180c520319448284 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584047805 1250 584046555 584046557
    0x30209070f0906110c040c091d0901060b030c0f0705120705010f050c03060f0402070507030c0e0708010b030402010818070302040c121a0a0b0a17010b0d0e06070f050706110c0a0201 79
    0x104940d2103200075190000210602025a44548205d103031910f4181c0140310104210300b0b01d0345031180c0b14016401100f021101ca44410103084041c41b84044091051070000e0240f080207078114204222504801d20401801080b100300c00b0910405210080c0203040c1750f40c02805000b80e2302c0c00903241c41c6000e0300c900c0e4001100c0d00d20301b000065000f6070f000b0440384240300c001c0c03400011001c0b4104100c029000081c00340c519108140e40880041e40051000b00940705d121151350603442d00520080812a0503002450b0000080c0240b10043c0d030000d03180c6400075070b1003070200360800d00007030701e00d00c4c103101588065446820103981d030343d1907600402800049145844284078904214011a070010701000c8407980020b1004403c005145a160240c42c50030070500e04244480410622461000c10a80201ea000c19001071400c0340e1041074450403c2c070b00c401601034140c0e40383c150005002d06000c20800c000788000046c40104101c55507203d07100b000c0c19280c101d80c80d0f801c1c04045644e0b41d0207585080f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584049055 1250 584047805 584047817
    0x212161b180b12060403080718092316080105060d1e1a12120a020f10060e150310021c0501090507020d020a0b0606070201112a060408030301031b030209070f 69
    0x10fa0803038080b441d03900c103a0b09a243c082c5241c46400e0200c41c6006802a2810b400d0341c09200424070217460b0003000d411024400810700040780b00c0c0b00d50314407881c0203051540a48040a00c4410030303038100d8402d03411524102d40d200d8850011049500c0036103c45200e044940152604a020041d96903000c41e8078088529000c0d04ca031081101400300c003000400c9410500e611406074601800c820400801c14048a0710540c0c1c00000e0900d641840c3c5242d1203809401c4070380303c4105104052001c40c049602c0300c00a50a001d4130354600012070b40b02c005040e5401100c58001449001d8840e420245a10f030702c1c2030807000c00183d0303507586003180108800d41d100001030150501020229100107a8000b4042d041500c19078151070309810400c441c1d02c80c1504074140440040d80402280d0240000310505a8040608400862500c8035034200080c2d007040034031401080c00144040c04001090328192030b40714044900c0303112400c29486407047c69a00080d4030075120800c11045c0c60b400f89203140c0c0110651100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584050305 1250 584049055 584049079
    0x905030102073012021b0a0f03030c0329030c0a2402010e071202150301031b1e050409140d020d030f0b0d03050a110d0e010212161b180b 60
    0x21038100518000c1c45000541022408541c44103130f9030080c0240d000b15601d00350000384004115003841d10280058800280700c080c05018150540280d040394209480e00b08580441000d20325030301c000700030b8090101118407894940c59201000002a1401d0007414002c55907a1403544c15a6201045102d5441c001410f0075195558014018000310102d4080905859424103640c8480031001d50800d07a84405a16034602482c3c1000e030045021310f0041c050102c1d0340342d080c102c080724041d269002e0409144500c01081d910b0301e5404640c401e96404841c003203410380d16824412105070000701042003a010b100c0f04c3c1401c158000442c1840e0401a88050007440c00700d419101c00c035000b03241d54030b0701f000c107040f0786000107442640105001402405d01d1031841c0d52141985140c0805081c0104c003181aa1980342041e40e0100105100f580465107002e20f1310b01c1c240080d1180301302041004004031190020840d40144407119100680740040181c0843c401c41c100140241801e01c4409014003000101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584051555 1250 584050305 584050373
    0x15020c09040b0c030403090909080d182102071e0e01090902090708040f05060a060f05030714060c0f12071a040515150409080a0311030f01090c090503010207 69
    0x32161145400c529500c08655914003681c5455200034401c4040007421030000c503e00005100b410031503801000940d45030b0145005005c103d400482d00e443c10b600440c581034000460604a01c10040310090020715000720b103500980c42d11680380c016075040d8420401c40a4441c86080322102121594008001c2c5030742d96008100485600c4500650031608050000d04058000d00f241600144100300c40700031030320991035803030405400380c501002440e00e48104100d803404e0b0100803070207030504401914101d4601805100c401c1c100e5038110740242d4012910f0301c6e4040003071205400c03500182068904d840b6054a0910035a8030074101254458442c1100c030f003540f1460000d0500c102d50010040030300e200ca608a001400c6002042e56002d2241545420100d41b15401101c101e280b1405210380c0f00d0790226400340654a80401e1241e50a00500c01c000b44d40c0d6428250b80e0440c0d156000004060920749411607019180d5002550590300000e04402044800042454601954002400c1c03080284036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584052805 1250 584051555 584051569
    0x60b0109060212071e0b090c040e070e220c0519030305030601200102280e030a0f150c020c0f010306050102030708090f03010c080a18080a080a060e0115020c 69
    0xa044010ba0200038683d51000307009005104440c040e010b8405503103d07018070301c000071000c0030f02100d2001d120001d100b81c211003041034601810003150140004e00c0061040d5549031454031441000c54620404240b01d8164080c040030540400d203102480d041c1103040203200209984503070341c011a240300e244c5010740e17030680400c0c0603a90b050391064070750b4031600c004403072013402c894081c9030042094034032000c0c02d4400d1004240e1088540f40d001c920074131403038025020489011210080c082e01c03101807134041c0d60118603509402c0d80401000d40801e8182080c014500342c4540085042e8903050390100e00c1c940010300d1940b8600125150b801c1d00e210745c3e0045090b910980718840c0568400e200c2d107030000300108c0150101007009080e4100402d90b820020342561011291000484c880601b4041c29414602030042585441c1400da11503c04c10394907056184108a440c0701004030701b001060340400d4075003007074006000c0707003804030f486584803105020145c480710455400b601c0760b40604144c50400031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584054055 1250 584052805 584052809
    0x41101090302090a0b0f03010e151510110a0203240901090320010902030106060c0c0e060d0b1510090602162912010906031109040b0a0b010c08070f060b0109 69
    0x5000000f2944420600e04040c20ba000010340d4810003054103c0b1103078609100d2902419034030310080683c451180c1850340000c40180142d90902078120382e88419450f1020510404070842c9801104d403081c000d02582000440000250303d4040e601c800c21000d80340744049210904001811840d43e107901801d2822141170707110060100b200120040c1c0d0b0402801019040d1a0341d1380d00116a0408540c0001e084502e19042800807a60000ca0f030030900c660140e102c03000c1d03c1010b91854180c1020400540304000d180c4008001c1821040040d0803820109544800c4120203406daa0300000075402c058006007041c00740384011b1040303a070703041c901282c1d1a5041d02184c2442070300d10007082c1070034070340300b42d80c045000c03003040c070b03101c02c1004480d90500200c801d4000e004454002412904524001e07020260300160790344600ba2001c2030001003504248029080051500001840310102d00140c804455240001c0c06451000c10002e05000a042600701d0030b52240d1020401c8d134410100640e00074a04d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584055305 1250 584054055 584054059
    0x10090f050a05150a140307030f0b0f160c1b050603040b06130c1b140303010e09010605040b0f04092d1505010f06030e01020f16050706092909100503041101090302 71
    0x10071304100006035204c0b0000788800103800d807654941c8070784854030482200c01080300d440e4010720800c9039490381403494a07004107141e1611000301c0c0c140c00c0004d000c07103510140500a03c42c032544410201d0241c442d00802004040c0c20591a803030a4180f580300c0a40c212200c901900388080b0f4040e9200c3c082c0b09041c0704200c00e48540c030061080b071080140d00c0c800e00b0002c45042034446800c6e40d016500300003840c006c0107038607840308a07482c0503a1404e00f5a01161710060050f81000090401640c0b21902c02180c200242c40c001074070807150400c2c1540721460241585281c4844100c4024520701143c07400c595405494040c41c160822010a82151003d101d01c410002c0702003424459184690864050350b00008009030401101c00840005039202d000c2c048442d00e110349800c3c0c10040c0c1408504018611401c041c00c0c00f91a00f92100c018032040458107007102c82c010090300d00c4104090070b9408120000c3c0400c41208071400010304158030694003601d00c0e245900740e0550541c881c0c0040310a072540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584056555 1250 584055305 584055319
    0x270b07053c100615020f0102030106090b03151c030e15040618050933030303011403100c0c150605031e010e0d09090c031a060310090f050a0515 63
    0x80190090140c12007844459850044482c00c2c2c4144805003d00300250001a205080c040c90404003c0c2c0f5203808890150a00e900501c010070000c0d030415025803c840103103500658079914203091000301c4403824981075109809e606000c002006155a907407445219844414202280310100211880c04d03081e00940014108414020240709020041540240700309841e4038075101c42c0000c07200070007121451012030401d601400070020b494881c0303681e44552240c02035642400c1c0c000c42c2c1c6900c0140034118400c1c20b00070200c00a91800c0003003100c45c1002e50380411558140810040092004481c2511200ca510a114001c0032061082e01300300c0704010010104540501003018180f00841d0400005540c0d84581036099441400fa20054100e00d9490b4030b4000d00340f007096011074640c0d50140b020035240c40f000c0100c2c8100c00e40c5a4101c0403088070040d07160ba6034407008101604403038101c108900d040900c21000718101d60001c44c0140024002800999105010070500c26141c0c02e02c0b90384416 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584057805 1250 584056555 584056633
    0xb010302040b0a0e040501290906150c0105090c0f100f12060305060f090f1204030b0a020910090305010c030c0e040b06220f06110706270b0705 63
    0x6440e074040c03182c458020f01500c040c41c0d80c1c1c00060f40284000c80701680d903070b5101c03c0d0046000360402c44030710380390003000c600103103e25181c2d020555200d40200060b01503140c003034603119440547c000340c0741c0800389000288050315290160750784a040740d1480c24010703c0c514603490f42c0362410105804130354000e82e440d4590f06111000c100d8240c012419a810000d507600c20100210718180b0100b403240020755103291f8241010840c151400a40304090182900302e440000c226503002c100311421a5085013072440180c85100380c040080c80f4455119510601c000e40c0051070a80107001c0d642240e00400c020803a030301410f20141c099860380c00c031020010304c4801504403030789015030016249003009405141000100741400e40c0310344015801039420780700f551080007190b9070300d02040060b0015240420302000d680800580c0c035402802044107102d103900d40e00c5008044030308999110a400040b07804015510908540e0075400135074141c1d0f8901a142c41c1004602d03100c88032142d02e450921420900c0c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584059055 1250 584057805 584057809
    0x120b010b031e0601050d0903020607140306030a0221010e0a03080a02030f130303060b0a0504030c1d13050f030724060b0a050d1508030a091a04051c0507090c09050a030b010302 77
    0x702c0d00406050501c82c00b8000032001e400c0c10b10401600a200b9001000c0724180180c000d440341031840207960008108104004180e240031450900d4607605413005100c1c0700030001181000341003240020b05540c1780c5807512408050000b44044074130b00a45034250503444490f8010280d00c000c944e100e04a010340e00c0460300307070594100ea0200c0c4c40c1c0a07141c0010641d1716038800400d244e201212070740014101003814400d001c225030003140100500946044071880045146200d5003000b407644c0b0179501841d081d407041c0481489a04420700c0b00d582600d9889a5a142a0046403c00d5803c105101070145440145088910929083d94410b0032040c4c00d000200604540c1c680c0036045442d445a128040d031000303035003403480d10800b800011001c0d41e11480d0120000b4954011a448404848030641c1032001340002d40c0b0449040c0c2d802076800d00030952a10700000d000b002020001020751060400c00202ca8920b0b84c41414014655036842d8615a601c40400020105a002c042e001c0852500104014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584060305 1250 584059055 584059111
    0x50a03021005070b0a0f0b18040b04151404060606170a15081f0b0d0c122a05030d050405090c28090503060f0f04110105090a120b010b03 60
    0x181c0c1c07404030700c0e00e0710366a240501e81e2800c1e00c44a407060745030060803411080c1c1e4000c0d00c03201442690304c404082d00004590007600d401401c0036160728841070114040c4002c05145048608002d481842045000060b540740c1240458080d10320b641b4201d00821002d208022016031030303111040032905615a00ea046004010001ea40388400b2800900081c40020500c112100024890301d4000c288482c15503000036641d10761b016038400c0f03c5603403d61001403000c0044105540102100b10100720b0a0f1030404080c1501da20b4400600c10184041100200201110025154103070140d40c5804003615040d5040c4c040c50040550090350000080c3c04241143d000c2c010078020011941c3c10714440c9500010010b1107800035030f0001d98038000600881c1001c0000c40c0d081002d1010000d40c1d0701d0300d201c0c07502d4400c0c40a400280305100d03401680d80c0c1a0300c90305c103a901c0d0030401082401d10542c0c6410b20080c85800142c120782c040500800040c421942c2016680300b541c11800700000303c00803100080103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584061555 1250 584060305 584060329
    0x9070f020c1002061f0503190c030b1302040c02060105030d03020c0c09010b3a050601141603020f03130303180e0709180605030d030218030105070e011107050a0302 72
    0x462103940381600c865030b82c01040800801c200d402601890510310180f100d02c40c0036800c44d07417440182d0403082206031400a178000c142540744601e400003003c3c61410381c6840c106075101034158a207003814044080030800200d82150310881d810088070310034031001e0740c41301c20074842e0543c150840a141143c2c1c2e80a0b40049c0341000300c0c1010313103500040107400208504400c0e00a025414004500200020400400400300d90741a450900c03840f15804030007040c0602040c81c030702c0c150f51500042220381e4011041054600c5003030f0355094035a0040807600644115002c800d80051003000007020b0500800701c02c856002c030103155903602550460b1400d4841e81c00c803d4410b86c295900c207000280440700d4410040c0150119900d1818580c41d0258901f00e40031003503030340c01081c0d1800900b00701a60740041c41c1c3c2800303001e900300540c540d006045161105084c01c80103980550811042107c910b500c080c843c0c00c030300802d032154448403039141759140d40c80f0000d00901d49c002524007000d03c094900b034180e03044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584062805 1250 584061555 584061557
    0x90316020a0906030602070209010e13061a030a03030b150301210201090b0c0319021f0b0a0f0306150e101a0d090c0602060105150d111b0a0b060604030209070f 70
    0x807419540788800c4044561030b9105481d426400b00760b05045180144c4041e00514000c010415241083d4000043c82000204000d00e039541d900c2482150441e007042c003008412004003580d491600c0c03800c3c003802929680005030701c10b91300b40c01540080008401620306075104518080c20a0001d40040082080d14110580c1405603141c400501a00154010314074510540080e41d1680c20f210011140085059060000c0d03400c400d10400601508403524000043c0f8554046694007051b408a6800030407900241c200d03c100340310100500c4203580200300001d000e009207102c8555603c44204200c0340550b50000004114241040700c0f001d20a0804c90105184118918015000202000312560004100e0b06076044440c20000d00d5018807c0718010042543c076040c0601a0078170052881c0316150701d4001c0103a451001f041000748050079034035148226030000a65010700c98821b40d580d80c003234004035035408490740003c107107040241c2510104ea5002c0e12040c42074440e042c042c1e03805612962444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584064055 1250 584062805 584062819
    0x60901050c0712121b030c0321050906060910030b0c040b04031b08033103060606050d0506031903050d0f050106030b0102011505150a09030507170f0609031602 70
    0x219008010320048000700fa440d814812440002d20b82680c0140d02508000140070344401e19840f0301044540403000f8079810300d04405906001d03d4241d070122140080d85624429101c0800441c150329804580101e05010464803140d540c0340801222601c21204003040c010203010400001703c00150441e00070502c07840ba181015211601c11f0700dd500154400c0d60302e00c036214035565100d81d212002402170003083c0702451030640c1141c004064210000400c09048400a008003105207040e84c010010710f500c204103010180d41d0340b10051080e042348020340035462504000c1492071500240462800404c0c5403001d0108520303071010313205500140400c04140c6c0d114904080790340010304c14075018003669200000c01d49100000242142c014901c41c0e907410000c20070a112558031807560f048120580001503668050300c0c402107070700445507070000345140701da140c01055122041300c1c0d050300c1c01d081b58101d8a0b2029500211680c4000c203a9411805403c208408001c000b201c40c020042c441c0058440303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584065305 1250 584064055 584064067
    0x6010e0d110d062f09131b1808060601020d080601020c1201020315040207050318030a15090b0a02131707050a08010b2404050105091c0c0807080f0c06090105 69
    0x100d501c9a1090b4401c507401d0755200040c54036031481075483d204c80d2200c4034056561300b0b60516030690f20301c0b0b14081eaa1141e0500440313032054601940100004900c008a001540d03045044090428030b00d60030215520074411401003202c210002e4042d200d044140d0080500c103420900c1030310a644081d08250450041500003101030300e641e5404400c1034070080005a40e8540521815560141c8211451080b8010488100400e4000098580085204450a41d05a003901c00245001d003c00402028404801d030301c40c0072400c00b070b807242c04202d014007003445c242d07540c1c0f4803000300302c0c81104030400100600e60818401c6048050000c7c00a401180032510103e464a00244040031b6a52204825a450f011409035034103084402c081643c000c0d421807100300001c9052031550f40a070340182410460301042c01c1140c0d940e1080c8400e0840ca83c881d2a0b8441c10140c10070090b50040d902800c02d091041040000e2030040024801010210724001352001d0000081040b0300d552001c4409410000e0500072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584066555 1250 584065305 584065309
    0xa030b1203071a13030e120c0d1a070c1e1b140a090209101206050909010b01020c012a06021b07030c052b050a06060803070b060906010e0d11 62
    0x5222060203a000f014421000318102608924000d040c40c0031400c20a0b144000240c0002508060010441c0c409109241b061840c170300d0212411441daa01906201c401d0040c0f002c01c0740d00740210300d00ca008102541e500e03480140c846c030220103001085210610300202d0030f0800c0d400d6200046204060340819541203404199615003d508011034042444402c00000d02d806440c0c07400134400341c0c1c002d50a010410002400600003891a0014011049401800b0603042c1c2e01030800b402000703142d004642401d01406009000e00030410340588075850001d599580070360b07003c00f000340ca0711050ba542c03080040d417940c1034003800354400c4504c982c00307012015540c007044940003982d8200034024840289582011411050341d50f11083c06403184000c05060040f4262402c0e4034260702e62080200070400d0724116285c2062808050f051314500f550124a40c0c1c1c01000600c0010300038506c00050783c80704410068002c2040d502c0d6408a40016005140c0b030404140320000350340208040e9902c1c6042d080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584067805 1250 584066555 584066557
    0x60f0403060f09060515180720070906030f03020d0e090606070201020a050304060e0306010b0a0e0103020a02101104171f090c1205030a20070504020904271e080a030b1203 75
    0x282004800d201c000102d1b010708161030101c110500000018030b242c28210380181c864403141e1100a07406041c22040c0b0b401c110300304195002084011403c100b200e95070b00300b141072a9401c80013100140100c84078980c036a445800611a0b46200410100c05600e0708006c100c407a0b40419800c82c15401924000f00210b0002d0000d0f100a000e191a2049090140001c060415405800081d2038803818051a101c01d6804021103c0060003801c00507038402109500340d280c811599154580d040c14000c50200010035040035004035543c4051a004520410080c40d4440624400e10480884160142030901d816504044405405a01d88040264035034070380c00e034580696181516940d0000a16001e203e83c008051100d01c20008034290504400e80000c2d41c54100d0b51040c10722468002c01d658405076201c0d0b1005030a46501c81100550110910820452800c8040f042d41c0d0355002c1c0c007103085100b0190034541100d55000351050b2400720072650540040070b12540e02d80d0004046110150403c400300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584069055 1250 584067805 584067811
    0xc1503090c150216151106241c060c030e030a0c0f03030605030f010e0c04180b07200a0213090507030b0a020708030702010f060501091a0c0102120123060f0403060f090605 75
    0xc80300c0ea0f000b2078580b00035007129040c0e6500c4040340d0019042000c0c2d5140015003002480d40308c54448400741c1d158000800c1205036401030400503a0443c60f1008120700303a800961074031441c2d2401c0c80344ca01141c0050f034070790090b012690301198640300704400040140d060340317502520a06002820680b500c0100f8a403543c03010050500c2d80d07599030203c1c0006820800c29a82d260300712020b201c24000c2c048002c0340f080e05460004e14030072102002c10002d5000304059180c5208400203035406c249441c50329030303a50794a12802d80c001c070025000d400340c0b10140d00901041030b8010008007000c134556520700c4040c9c0c900400c1c03101e41e0b5074284003040004007240011030107403100d6800810180400c114410454074241c1c081414810510030810034610314011002003400c0c035021454858448401c41c901a109030492066640314130760010640201440301c0710161810340b14001601402001884214499030007240340c401c1d410720007000080e0813504503001d45d0300601c8002c50f00c16259038401082e00c40076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584070305 1250 584069055 584069069
    0x2802130b04080a1115091c12170906010e011e051026040201091403010e0607020304080d0923010c02090f1f0308030c031806040c1503090c150216 64
    0x1072083c41042c0300a0300c01092030050221804280e5035101040c0221030320a9080b207a0140c11002c080307401009000125500f140d030004841101040d82d80c3c4000c0078000600314502c24000361101080001400090381416100e9050030103040364202398071803401005c401c0c5010340d4560203c02c0440c1c1511104030344062880c03a1340b540b003030304403005c00900b1041114100010004115604001c0503030b030700030f410034112203140e80a0b0440040c0321020a014115411010741300d48030f05000c6c8008035a000004208482d42c0030309a0754070000c1d809080b00c0c00701c040d101c0e205400031901000013844003282043c4100c40c00c14100716124006503070200314014400c80d0150010018503041100b102d4150041e14080d810203854113450506603035030b954142c00060803810704110003200040c1d20301d024600c1541c4101c40791b403c407a81403a080c6410b0b592081c04d8040e80103907015003030404c0b141ca03000f0302640c42d07100e41c00340b000c4600398100025201000540202c0000f1403080a03101d00c100c80d080a40c02c0e01030202c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584071555 1250 584070305 584070313
    0x40b0a0f0e0d0302060103080f0904060b0c010b0d050d122405010e0f09130503070506130c05040b010f0309031b0804031110080f060d0b15092802130b0408 68
    0x400d05000e46140715001005001c0d2480c0ba91400000e40e011034000d0641c0d03449100507449000030000340c0f68501a0080705e80d001481c0c040e002c581c0c0458000680580c0d00c10304000d000c2800340100380040580c2c01e560040c0258840021030080320f000d8018680842005c88000621140411100c1d103e484085090400e000d0042c005000fa541e202040480041d815542507040d01050b00c0410300c049002050414044a803503d40b00c00c104081c1b00b141c10180d00007041381c0650030055441c40c40d030145880100d41c814004980000c160074140943c0640749016115502804000741d026009800703c854204d0403c0502c481007501c005d2031031400d031102c1d80103512403511a42103282c41d5016918038040240302d072264150046134543e0004042d43e02c2034000c0000c480c075441c2c40300414a00701021400514140519080081160b041040207034620411106031401da12804504244695070025131900024510710541844d051500103142001c011103800125568524400510343c1080c0c100c6079860300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584072805 1250 584071555 584071577
    0x120c090925090f061d030f070915260705030f0c0103050a0e03040612230f150f0118051503100905060f010c15090804061403061c08040b0a 61
    0x210031141c0c0c1e40040542020584a41031240000e07803000c980c42214100040a036020001290304a90b049040130042d0450340060460b44a1a4a8890380d02954040300c0c545407040a1040c0322080c09400c48144190010071102d0421658031402d1404841e08218800c050001407143c03810800407201d074945002802e1407169840005040d039170040c100360403007810a4103c420344400070040302d08440c414240782d0400025040d010021344100c0c00d06401c4401e400060f0000b4880b03a140b010b10881307071640b214180703550b141d00c611001c10a0351450b64000d0000d0b9402001c03540103007490b031600c1055032a203840c03040c3c0e04d10028043c2081003a04904060f4080280310b00d00300c9400101020b41522002489541350080200c2c45003031140a0f80c034104800b52800c0070030301142c031908140c0c81400c4071007401070085a0801c006154000c0c490a00020090f8041415004118041d81d02650740103000362030403120901880104810001c080d280c400c002c100001c2e10305440401408195050341302d00000f00c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584074055 1250 584072805 584072851
    0xa0305010c0e0d02090f1f0609240905121006090e07171504060e0f01140109020a050d0903020c090a0c030534031b0309021e06120c0909 60
    0x48030501c2543d010720b41c0c550070b03803006943e5000039aa0002e80740c0d81c520b00a84d551034080607011030b502c04400400d1100040402d0107613110300031000351189500d0760042c44804560404180d071009151130001800070009001c00d183c00c2007200184002c10341100c4500d1040580e0300c04030391595016051540c1d65003a28200e410301484a40d0042c045108928032004046202c2a2200f88090703200e003480500e0303c000b034100051a80901006119041207807002013649406900811154241c030145047c00c400004000240380203c1d036110305240d90306810802070070303803680c09403010715801c5080d0301850b03011304100e4480040807031103280303148001306210041a20207811074502401c600109400b00740e01e440c1210140315094440184402841c1c0c40090b4504101c0040180600342407190081c01c080b1200c1c660301d83c2064502034002c07519505003000400c840b26130642000c0143d60000028080c0b0005548501d00b0154010211a202491701e00b015000410039401110218488031901070484180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584075305 1250 584074055 584074067
    0x3032e060917030310060e31061a0708070f0b040b01140603040f1103121317030910081902030408030a18081905090402040e06190f0b0a0e0a0305010c 66
    0x49a00b00041c40c80c5041c001c891000740c481e20b00507503040c04280300014005403a0303036115560070b080c031a0020031440c803c4107401c01030803000c401024401c2d00340301020178104c03030502c02500f554440c44101841c00e00d01e99100c0302c007a0003820085d00c46c00c1860180c400841d100c10b03030481c401c030300c940c04003802d5604090074180081d00c1c1c130552034050741040c8104000110205101d032a40e64205950150602400d0700083c80e200c00c07506030034192240807580408080d040300040c4242c66490103216041e80900310425600d0003041205984000341c1606800030a004002c40b03a04042c403062a5041c0104441e00e0f0700981c0d1050b28100e65003100081004900c42c0b4512840410040d80e0079201c4000000b03131207104c5140591125002400e1085011003181c0703000b407080364040d420182095403101c4e55602022090141143d40902590300e0250300440c841e0000794400595040003400c00e0500c1c14408140d02c0c603008540d8107400d0224192120025075150000000150710441c00440c03054841c1c4001806 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584076555 1250 584075305 584075339
    0x60e010c140a051009030509045c09061e04062a0f020402031509090604030f141804060801020c01091209140f06071202061e01030503032e0609 63
    0x2401d01d00100e080006c0d07441002c036000704200b01c401103011003081541880d8542104d04e4018200c2c1f41130b4000c288000c46400c1841e508192901d00350300d10840061010b52583c21142c0341d96001000c114102942c5402c001810042d45402031400301031607100018261980190002400b1607a03107601c42400c50307849129800d24511040704818000c103540c1e24420104440800217200326004030001d5282c18101041a103240b000a0400e5101d040094006888080503a01540007448a0524a04050041c02c3d07829003d0071b1031080c9440c01040d04580340030528400c3c2c00e15803154070380c00c4c0065000d50900103011148040c0c400020100085d1038405100c03101030001c4c1c1c0510042d440d0400080074000c1c800b0200d030b03505803010809540104005a607a20546400801100500b007070644c9a5900140081c0720704034444075401302140d141c0c80309051a000b440002e02c2c0307900800028200c2c0200c00306c1c4601d00113140300d1850a003801d1042105001450f500400c3c00244180303c2001005028104108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584077805 1250 584076555 584076583
    0x506010b0406022d0106031a070e0105030708060f06040612320907030b040c0f050d0807060c0c0209090c032a1c0b1e090610060e010c140a05 62
    0x4a09450b251001e915602803405504080080c0b00000e500c20140188070110300145000070800301c0c0c0c0700d207040444080c80c0054611200040c1c0005800140124040310758000c0c140c4030941580c0d00c17000b080b82c1c00100144215004504100e00d80c00c02e4441c6000740c405000903850b542814100b40c4440011112054280710b299255071030400386100c580090040d01c081e1800c0c12800c1c90f503071100030030f182c40f9040e403000300030018480c100801d2080c0403140406139002007000d403c01a6603141041100c80d0344840240c10340c10104807400c0056816800340b00035142e6030818580301c20041e0000b9010610444482030a6000a124007c079482c0901505034001d1040f0103078001e20b01205d8260344140c4a02100c680190000d100034080d01d03900b850301180e010790200021519181103410903440c0e000c4066aa02c61655900114034008804a2014415200082c203012400d1404d50100e980311201440384c2e050000f1009080c1c00b250401007448000798000c001082a4000c5151885c42c00e1201700c5001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584079055 1250 584077805 584077807
    0xc0f02011a061e0c03031501081005131a10020106050103201905070804030f02150c1b040f060801060609050109080d03090303020c060a0c0e060a0801030609030207170a0506010b 78
    0x500250b6a0b10103503060b5200c04a0011502d0400c0f20f0120708034860743c2c01005144c0300c0441003041c3d60425002071710030004280c0e1a40059202c03007030610343e002e2480c090903902132000c801224030300c035140d800245580d840a19030302c09500c02d90003048c1d50040c00d084085c0113075100c41042c44a5601801012504402100420200144c84074681140c0c011802400b91065800788088003042c07098095400712a04207004940c1d546e940d191207446510564800c90207001c05034110901300203a0350a8408034800302010340b00c4601000c2031010359020500c6540d034015640c0c082c901542c4601d01c1101d018091074000043c400f414105e014002524580c45281002044041030002100c0801c2001c40c1d01a203013804121198107190580181c042d6010178049481500100502c008042c1c1080b80c1072942c44d29820804c1a000742030143c14803841030301c200829600401000000c866034402d018050180c81943da0980d19100c0d41c1001684440400c0070640c44203140c0c1c0140041480410700620760701d510710b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584080305 1250 584079055 584079101
    0x40605160207030b060f04060e01090203090607091202040c030f02040308090f09061c030e090c09011220030406140c0714010204061b150606031e05010617040c090c0f0201 75
    0x32491610010304d01405034050703034606c18283c1c44540003000505a8401d01ca0410741e1141d02c410000e41044590b42420702ca9280071680c1c0d5402603485509454100c030045025000036000e0101600c4000405000c01d40d5400c2c240e00005202c2c03004d4800342d0f03c80c0007103580c0e42c01d0320401c000720f40380c06000e041d00c9141e000c01030100541e141c1d2802c50620080c0710704828408014201903402031605c0345c41d240c00203049010002d1802c00d0b8001040c05250036210001810f000e4804481101c0f0800d0000044254a000b1402e01403050300166030b00900c00c450228280003080554860f064080d10000740c07032200822000100b0506207440e200307002e10f56000714100351819000820081d07110440d800c0c0c034000d840100d02030040c0400c0144240102503018440c071a5104001401000744081c4880c00704542021070b403c03c151030241d80d040351403643d00e480380c2e07840c0240e0b00b1419500281088400340143e0500066021145c01a02035500300303030302c500c111100500001707400d4070100c910080303a0b4240000c10f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584081555 1250 584080305 584080313
    0x140105090402120c03030f0702010f020a050706051b0a0302010615230f2a070815070525030906110d090e070e09040503030915011a09041404060516020703 68
    0x822540701d038040300c02040c0250090400c80c1454810900c0640601001440c4151008418010b100e800e03c00c0e43d07012030b2045080000c90300d80b02445001003c94200c20300c20814944114050310300b61003649002c940344a20b942440346070003100d26003140541d45480301003103580d102d040701c089138008500b405c12800341c0c15400f0407011202c11069108140010803002d280300003120548603115040c0c01c02c0c50540c0030b00041c90203140705070198040c6074070500c2c8010401c90000b040a0500b58440e03078420140344c403074070026252a007020311500380100c000842c2404101000010800e00760280c1c0700c1042c2c5900341034000f4011120114840c816031300030128028607a0303010040008492840f00e000e0140d407910002241c1c12002da00b8203da012101c00b0074401070002c04802903005502d0202150a200000340304c0d031000840134491840c03440c0340800e0340380080d90030314010100340c40c008000185c00c224500d0140c0d0417035010340301074800c160385e007003007240d031030190340002c0440d000d68002841d5041ca5503035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584082805 1250 584081555 584081569
    0xa14070605090103231003051002070203030301030b070e030d030606030c1106040f0602040512100c030b0a0b131d0403031103160c06020d06060c2a050d1a19140105 72
    0x1e415410035070f0360a0017810035a09043c041400d80c4461000c071050742895041102c4808080c0803e0300ca40c01940319415040c3c81c1072080300d05c23a9034041c02441c2540e03c0d50300e84100c1d00c8402090b4601340500984407010340daa050010ad1501c0711141c9001986904010380102201c003500c1042003400100f003003041c0680710024000b0b82c4650f101c11034540c094802e180103800703400b0b690302c8540c000290141c0010000004100000c070a2180742c000c0000d0000d1030b800301d054508210701c594000c12003420034020b140406008100518051150b081d025549143e042d0030280d0016060702200e11410500041540c036026100100c0d0742c1d10811415800c04480314042ea503103801a00742402108031140040000a405952042584d681c00700542030740c03903a001e444160749601c00c6074020792484c1c000e500c810f9444030300407405102e0040210341c0c50a0409001407410b04240503101e80301e00b981e0a1001d00c0c2c0b0a01224410702d40c004998094a02e8149170340c041d16200c026074001c1c400c3c0c41c8c00500194650032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584084055 1250 584082805 584082817
    0x606060f07081e0c21090a0303050a110a030c030f080415090c08030a200f1509030c0708100e010b09040204020a090f0b130e060d12021e0a14070605 65
    0x42d1a95a07980001c8400c01c91601003604401030079404102d420780c007400820409004d049090740c2500090300c004185085200300e20301541d0040b507281c01440485e100368003800d496240c2d42801080d204481180501d0213407004800c500003482c050354041010b92059903807140c0030850800e0101810a50344100103000c0c00e000b15410999550390035020711035600d40845c010034581c019030742d441211410003130001c0030010040000e01107082e0b400b00c0c012400120070041038081e2018058100c4038083d00144481c000d0074110281c401404120000d0300e0a00c5600001d140540080c1410503004071200150341011020303000c3d591401d0042c40050700c0c0e007000c2a5209078100d0b00140d668900710b40903240c5021581000c040c001e40c1040c08103210120170014140c0414a0380b080c03440036941c40c8104581c040c1200d4081d041200c0c8000f0200240190060319006111401524981c400300491540c903001011400e002030340c80f2004038800c0c050214030208403101440c0140c1030003130510f030002e0110312690b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584085305 1250 584084055 584084063
    0x120601031d2116050c09012103030504022106070f0f14070f0c06030903020114040809012a030203030402040f09020109061112040602010c08101d090304080f0604050606060f07 77
    0x11032500300750402200c00c40c0c0910b01c43e0341c1c01c1c004007415414820356a40d5200c4c0c4140c040c101400020801c1035903009090304c2e1a00e0700e070109060b1226541d04401501d0050b2040381c1140e0a80350340b550000e80040245040c41c4050014803581c906440010000703007016550b5014003c0000d103078013900f0761200041d80c8002290f00015602c2c41da5190401d0200345240f0050301c1e031080070300080761495154100c2003446001c0e9009115912a600c40b4049624003a140145a200c0c104071003106940600d40c2042e80301110400b490900481d44a0f045c03010f800400202c0058100000308011403506200b07e0140600d00c1c0c1007000140c07500d600190103000340b030103010300384859400b15000200d010028040750480a41031691569910303200070b40601a02007485021921950005c0c00c64140e8042000440ba1490365a0102428030100200b00d910084c1c5121480d010400c00498420420043c401108070034800030045481c084c10564104540a01401d100355420002c0404405511081c0c841c56600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584086555 1250 584085305 584085343
    0x60b030606070320031b16060503010e0604090212070e010b0f040b03180715081501080a1a03060103110a080d0806090604090b010b1e031303030917120601031d 70
    0x34001001c3c0d5080001135132604a10000901012542c40c50011000305032041c01201c50884602200700c10714030050180c04000341003400100301e40d02c0e45117003550b0480b0700680002180301d0560041100c00b02c4c0140a03417181c0c2c0c402c00c410801c1d0184088454018140f611013681000e4400d0030460007031003640303e81c40c800340000c40031508000080e40c008030011411070031614202d9590341c0070703044800640c8000006c502140e00082401e92038400707400e00d1600503540c20f0301a07519071005500401c10b50381102100034001188812940701048218080c50142d856a1007140c0b5040070070440c230100350044031071070f00a140d00d01030351a0084400c0340c01c5402143ca1040e25034801c408100101703410791010342500c0082e800000c64804040040c4000a0103038180050480c42c40320440c42440181c5010000214020240001c80c0c448c3d030000580074410b80c0700c82c0d10702c40026241b100e607400c0030340658110801d0005004956800d031051445484002c202030410448074031a0a88449803d40da500003560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584087805 1250 584086555 584086577
    0x32103070507031413091803020a1e05030417070f0308091c0f030f0206010501020703020102070911040e010f060e2b080c150105150304080a03020d0f09110103060b0306060703 77
    0x1020701c01440484104e070000540742e643c3c00f02c0c4105c0c01e03121403080f07503469403901101001181203154261460b40d095001484d14080b60750300c080780201c001049162402034065980001038052000344000c00c54800c1c010540781e480c0000b1030406440c0d60002c840c00c01803440030400101d13a2810355030758600846d21091100d05803000d4045000e41c0040041440100b500c610042580107404400c10015980c02c80300c690381c80c0c80c0160703520961400042c1c0941e01c00c03002000100240e0b042120f8003046110360070308040c1d81d000003d402020a81000d1002e1101542c00d001440d400a01110720b100300300e8060142071040303c8000b50f016080b14a014010400700011030600c20100c04450505e2406c83c12100e4000c0030507415407500000b80500741c800c04405885000c03203074064069030701581c0c108490a00d03101a02c001640254032000c1003912194884a0400d41000c15110b09a0401c7c001e00202c0c051640110005040f5140390b00404d0b0022405e105210036529941c0c01d580c0c40550505007011641 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584089055 1250 584087805 584087807
    0xd090c1707170309101709061b03040f0c03050d1403010f12050c061602030708030f12090a020a2709031b0c030615080d0e01080406110d11040503210307050703 70
    0x104c10700c4020b64022900c0c00d280342c0e50035031060840030513000b0003030724090503112241c0071900c40005899401002c900a200d49811410140055410a21550b03005c000c40045540b06030310840c0d20303482030350140c000c48062103915030489004290550812030300e900d1507041840c5031104c68114040c07592600041d0300000704003d400c001040b80300b48024021a116034000700c3d0a0394890740c0342400c900034050044001442c1e4030001c256442c00d004490b6407402e00b00c0910101411401c024016002407081012139000b503126481e5020103800350301d040134400d9080482001c030545001032044407481c54020300c1c001080d4440017500ba84615040c40c084002c404e81864204001c0c240c1020b060310f441c0c001d040d03080800750402c590858950303409a402c08030200b14103907101c02800702c080303010491034000200051016841003a200c611003c54a06201124842c481203480c81da14040803010001414172480ca82003000d0103920310034502040074000350710030060550001620b054244080400c1400403d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584090305 1250 584089055 584089057
    0x30325020f10150812030606130f08060f090a0b040b0907080303090c0f0d1a04020d06021908010807050a0e0901110703030b04110f071211030d090c17071703 69
    0x101c0d1054211a100710034800d680c0700426402c141d81d19080c8000f14000b984101c08181c11203c00b8000c05c045003507036120340500c501035103c0407050040f0f4951500228500300c010390450041c0010f440103094919204130020700c1ca420103042c14505d9030210000c50001904461400ea05c2548840810016100c0120440ca8143c864014483c940400301c01c11020f50b200040f40d4103140703400c446281c0d141c548503040c007004420100d005041080f104400c5981c02e20348201042c2c12610141080f001d6540c036071104802c070b800c10003c00003004a1504092000780e480304990b8090b112040240507140e2400000415004041c030860b801c4c00c680100186e50707041e0a600c02d030511001c1004007982d5400516004008207a2504400d210b14641000e80c4e820001c807d081e01c0d01554101c004518010349134680303155445d0540c1e44501000064250218416801c1c00600120080d000e804100c8016070310300035540c450309400000d4507071003c8895420f00a07001503014125405041c200410b0103200802c1c0b411 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584091555 1250 584090305 584090323
    0x506090f060d0c0c0b15060f1e12090106050a150c140328030b060a08060316080f1507092c01032d030f050d090c06050301031403032502 60
    0x10614052154001e10782110440d1140d82c405c0b500005241c0d2888411a0390241034400c0c250441001d10054502d40d440b080202008020303a8044000644103810312075550f8081c2c1e451214540f044800c0c848407110034012140600f0040b10b03001c03401810300c101641d4008007040c501d0100302c2c41601c1202444641280800900c0c0c076542540e81e00c407031200907600110001a0038800c40c00c12801c024030014030070b2082060b007402c0140b64510b0107424690448a040001c1d1616030315000b0b0004080820078081c54110003040f03180050b04541020a2540303051150000500346ea040c80d1004000080c0d074841c040794282e92000e8403843c41081c590841e600c2c0c16644044400f08290404004030911524603810540a5802c02440b407404001c11242c6608620110b0001d000c00d0304034034814800d60084e0003820700103400140008100107030307880741c505041550b031200e000b040001006009021046414031454030714a40110700d1070a00c01801c04041c41cac000c2a81e81d180e81e500a141d02c1d035500c00d001d1412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584092805 1250 584091555 584091577
    0x206060105070f0614040302070e1012060b09070e03010c091214032122020d03050a12060308040305190503030a050711011418011109062802250506090f06 68
    0x170140010302100c0c2450001a60240c016101d200f80c00103003110b007006030500c80c0003290040c40300107103020211140e14600c00f204492094451000c86000c0e02c544d42c0c020700c614403940d5003019000140c0c1c185821035003022002c004200b95100705118900c443c000603071a540e80310050740d408c20300501c070040c118091044d52104240c40c02c80d40ca0080c0e21940c4485000d018051300119502e00000d080701c85c000014400250000b04c00801000842d020f403001e00744015180c1444100800d02d01c0780d0000b2201c4507041241c081401203000e01c1400001c00c188030b0007000c2c5001c21070241c0340350340303c2994a0100508994206498000195160b0300c102a5143c03a041c552000340205d00081c03c50b0130b1800411298242000e0a81e020004a05814041c96400311503908546107000c0f1040248400d0340c0c401800401c850103032102c51560000d0380d51228031b000b00241e010381b900503510b8031404400305e160383c5440070002d003441e000c0c030007640c0b000c045403500d0740c044502d070241c100000c0100d00c290180ea00005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584094055 1250 584092805 584092811
    0xe010e120a051b09060a0e060904020301061707030b010f03050316050a141c14300403051e1903020714070f090b040501080717010207050d0f030c0206070206060105070f06 75
    0x100540c1c409a125030780220f0885481441c1e84c0c0b020148040e0500d07030300c2507083c10301c18540071a001e401c0c4050080e0300180060000f00359551a440810520404503004e0b035851313408020200f051100c1c0f129210b01401803204030364030962443c0c0750b20356640a40083c040d1500381001c04081000020403801c140d0070380c0410501d010780d030301c4600d494030f07903922006500c09081d102440e04c2049110b100328a080c0e000107000300e0b046c4038018880350202a0002c5014040e421039160f038901c1303003a80b40ba040f84281d2281ea0f0740d031365400e010a800d01c18400e806561081080041c80200781c1c4421721404c3c24640c030740c5441c2c010f03100c905a0404d016840b10040503807202c0d000e25038002c03d030a5171041000b01502c100031001d2042680c180240011980c0034811002982c000f40014040b20300100080c00c0d0703503032584001609000c4c640e224141041c6100400c803001c2603c032804152865054002d0070b144031441d002030305013031401c3c0c04007a450760b000074049810808002104410040c3c1d0f8810001c101713800010030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584095305 1250 584094055 584094073
    0x6050d1506180b0405060d0c1401030207060230041709240d24063605130212070f090909081b063606130201030c0e010e120a05 56
    0xd800411603c0789280c0603500b00700c000b4119042c2440000304441d07001200d0f4040070700d00380c1c005c0d840c41c039514006070415400300044004121940094840107081d0640e1801e01204915140e00742009102c18000c035102d024100008584a080501d41c0c1c0100e072880301b5500d0301d00f0340c006207540160f0740100d1030314111080d60043c22194480500303003283e8071807002c1040081401c03014503568851603148004070520300c02400854490380c2c0041101a03040118014024080842c0b11900640000c004041100003405c12042c5048503102c001240c010004515000301e1481c0341081e510010043c109111580e507200392290310440700500105810082004880d8052400c04071a030f0000c0f5082e86000344546c8500380d49040498414000d1050b0385150401c1c99542c050b04103501d07581c044040c1140100620391455010901c1352904c00c551511400c5141040c5200140403612600000010001c0c6401c0d0301c189660881c030179408581045550300c601000302900c80b4134007038040600400381d000d44074003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584096555 1250 584095305 584095349
    0x6120309090e010207020a0504200301090b0f010e031c1e0203030115051c0903140307020c0102100218060d110c100f1104030201030203250e1306050d1506 68
    0xc00080d9545a101031240800d103503411400d07402144400ba40c468641c01d4108241d14140c2e000f202554410711021424200b020484c488a03003090303229400054a4040041882c9003030381c6801d281050900341300340c450342c900380801d0340c4041200b140405d42a0410a5019180c05540c142ca1000c00c140784e040c82c000e1140760700035103a4100380b04211528000c4070401c40d20b18024015141c418802885246880d64410003010141000040960a0040c540380d901600783c02c42c4011803284c1c500fa0010a01c641410000902d0310300ca60a018a41c1c51043c0101d000401da4204003403c6110101c90468a410340d04044800801c00312548051803a4005082e030304154000c1400c02d0500c0c64402e0412003104c86103146402c2e140c10110381140801c08000a000542c0260302964104041c5a44100a01550300060710801d0145021301c02040030106042c455203840e0703d220b1507405c0d0303005c418000a40b038000400e10034800d0304c400400890b0041e40300c00720140742e03600140c000d2869841800c08060910705d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584097805 1250 584096555 584096567
    0x4020a0c060c020115050d0201270b16030219050318040212040b010501090602070e13050a020901062111070b040f050124091e020f0f0d060e0915070c06061203 70
    0x100e003500340c0466410001d064640744501f18441a0180c440400948072117003c00720358500170b81118140c0e20714140126405002c400500400740c0e070202e00c0c900c06e554a041c068500742300303d64180c401103041140c1c100001c9022096402c508072031109000406800c000042c0680030302027a40d40c06501c08410403040c0480c428581d812200d0a807910940030b91101c07030482e2610020300540304a0a503d4020a00300342d121911000800c0c000c07415540c0e900115130002d01c030316100380d01040014060044807203541c004d024038029044211403003000b24020b200407145050040c0303a80039015064100000c2d09000b69002d01c3c0311800d501c10000c02182c01100c20651032241c00c0c01c2c204e0b52400c07401c1d0f00452109403511800c00844007502217070007401048002080650b05c40401e000c500703003040c80004010b1440398043c10070524001e034086106c6040c80c0c4040c508032001454841d150380480000d44c040d0825002c0c461b000051868868000009400d021000c1d011940c410400c440003951840c0915174044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584099055 1250 584097805 584097821
    0x607052e0504080409050f0c03010e130b04050105180a03020a021302040806010303030501080c0906011e1e030203011a040b040632090901140307120606050907020f060604020f04030204020a0c060c0201 88
    0x79070304219a40b134031f8190350501481180c161907172140402c01031140040c40d0107042e510414444556100d04503070783c2c0d4803c800c1c0c0181c4088403a030f0f4549092090f02c0132000c9a811100b0301e0000144110b1205e614000c1d51a518100c0c081d000342d80480603403d1020300ea404403806084281c0c2240c040c0c3d6541d19005000380f100348501441c1c0d005250104c0401c8c03802e085c0590180308169540d03100071140360240d20042e20b0b8071841c0414460400c5d00d11040c9400101026101900740e10016142c1d8540780803010000300880d81c1000c07913502004180600d40b07550702610181d034210f10f409111410102c03450103000d0810b03100d8088400310100c0b0140313520000c00c0144003601d01542e840e506640c1c2e608081e84284000e18900354941c112000600100c403c01c030601694038011603011030f4007540c500110303e02d040705540000050304064400c044c1c1702810464140c006409480071031404502c011508018019800001c0c811a0001005006c1c14802c414002e5a60b8024000300480c4000c184046d000340b40e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584100305 1250 584099055 584099069
    0x150f0303020c0a05060d0203070e0901062f0d05030c0f042d140f0310050c04050102070e07020601031401020c01110c15061f11030a031401050607052e05040804 70
    0x16000e03280c01424143c00c44011102c0160800742800114640a0080d4000602e010100000006034807170507600c075028180203082a0319903040844a24a180c10300580130160100140c02d6100d1300130311141e0025000c05201514541035403a500c0f0000514114402c4140313010621308041070102e00415082841808911944066615600d203884200207948480c0300310842039205034102c0c0c180d418030301118071400100506542c02028030f018100100e645c1a00d00000c8944081001d100310f58041050720b014002c030860b00b150701e26003102b0096a50340140401072070748140c81505445003030250107981400c00301200030301906265103c2070301d1315000344d800c5102501c60900c0c0d9020000840121b1405a1405422113070580701d0350000010f80d104280300c20080002c41d00140345006400d04c041d00c8014100ea4003c580c58400d00500a040346041c1c1160340f18000400081000410020b2403c0003020000c0c101a04040722000304035440100540000d0198200410042001002401001680c0c52 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 584101555 1250 584100305 584100313
    0x30a0c090b090a0b03101a0d060504030e0a080c0d03030207120e010f0c0206030f04080f030c0a170105130e1608070e0c04030f0f05100f020306090105270901150f030302 74
    0x4003a01d840c04c0c0c3d0481007205415030000e0024000a82e6039410581c0c81904d0500504500000100441e0703008414920680d034507550741c0d05001c02c140c0c1c4902c0c006052502184c501001e0b44c02d02e21041d8980c0c129400f1107205608201c81e920402d4065019a811582c00c6500d05034621401400641291460800c550001d42da43c4133510001c0d0060a0781b41c0a00d801070702481c15a0799206c212003100d0b001500580f9003a4040c0300040c2c4074401d82c030003144107546245599445486080340604041e42400d10800050301c034000611445d01c4800b440c80000b42d08500104860303020300d0103141040842c2c5142c3c803000004038008601030300f000074080b08985039008140303026500c411000003140100c0c0001486030381c04d541c5071004a8500d0000e50041c3c4c3c05441a191701e0b81d09140d00404030750910242c540300320340100807c04540b5000c1c80740d0740140025596160b15400484050026241c01441d003481e1660420104980030000d500583c040d40c0d40703403101c0c808662141d20641007807113584411801481 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 584102805 1250 584101555 584101561
    0xf0303090b0105101b110409080a0e0904150f06090c0c0b01080d020d050a050c0106140f0a0e0703020d0b032b0f0905131806020406120524030a0c090b09 67
    0x14076032403000d00d00c0959642d0107506440c01c2c42c0c1050950034664291b400700035650700640940c0c4d45104510000340701c0d86803207070761b0042e509000d04a0023842d44001c0c40b4444100410000c00d00c4602941100c106601c0300080c0441d03c8500344000b8407035900000003081c0707804028a010340d000885864007601a0181110a03a40d41025a95900c107104c20400160030a00c1e016204500880c0904207025040c248103050100c09254242111520b0b03100814090380348256401c3c0d410b01e20b560101c41c22007a21584002414400500c04d00030700500410105680045c24034070311106c0b03074040a0100300c0102030360080b48050f20304c0402520b41c2030943c650790196221550246004d80c0d1031440000240d282d00404901d844100061a070041b007071010300d582c8030051008004030904001c031210303108220068580341801c42c02458103e1500501541624010500c8600c06604410f04100c3c0b26078902031650801550109041c10002e40004015085001d80803401d908039070003020040070f0669030f405281d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 584104055 1250 584102805 584102809
    0xc110105040605150a120f03051228180b0618041a180613060608031911120409020307030b0d060218090717061c031107050d1703130f0303090b0105 65
    0xa85e05110740c6960596403015034001919106542d86981d00900f010360a103440c0c003c00019405080318424a21f10380d0340360030544510224a02c14400811701010403c0c0c840d80130303a00429007240c0c14041c06444c5200002103403070307075006040c003c0c03074200b605055198101031410380c00d050700d141c04200c3c01e00f0448000403180d01c188821416051701e1100100f90a480d036000040d42d180306404c0a40d400c0d1b484143c0410003020800007040c0c3e0385403480c7d03c5500307200700c0040103210500130140c00c841030700070990781401094001c003610140e640380200181e8035214000242c008202c50000b05810280d9a01c80506201c55903011340142580c070000c0300c5001804c00c0401407032842c2291300d4070120700d02120300d0311505169002180d208102030030079140030070008032080031000d60500232000039848078691001510f040c0240d00003041c09484448a030842944d616120b05000561166110b00100c0007509020b4106065200550429070311a24150542402030141c140700d8415038060f189500005454 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 584105305 1250 584104055 584104069
    0x306120a0203030a180314060a1413020f060c060744070207031b08010605120a0206130f0905040b061e01030e0f030301091b05040303080a0c11010504060515 69
    0x340c0e5000300954944800360105a5240c0c24000e00c0070000d00c1c0104001c400605c202400440e64061480282020320305030101d0410364140350024442140315400f40000c241c03184001c035240320381c12240d42e021004580013203005c9000d40160001c051140b201032051454001c00c46044025002c1000514165000480b6101c640383c100241c420050001c08104188102810242c01065500c166003506580e42c460390010711038200e02c8a0382d01005081000004801d210b403100a0106660525003c9034410003d5141d40c0c80c85006030040000140d0750416003a44103403680600000c1e102c004901e91521809002000d00f00c500b15a142010b10100e40545009a510758402643c05c00304c0074124451801140640f02c8901c0c005498850484d000c0ea0202c001e002031800b03800102c00000e000c10010b65200541e40ea0b400c0340c81c0600108010600129a10028040d400a410b107170101e8120706c01d00080794a90320005c0240e215501e844140f00400106030820f43c020300c1044416009069882c0c100489 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 584106555 1250 584105305 584105323
    0x9100506060a03020714071e170d2708010f05070c2003010f050a0507030c1701030305030c22141912020301020921210a0309080903030f030612 63
    0xc4a0402d12000e44032500c41d80040c012148513500700044022001d405610b481c0c0940c12014100d100717a980c0b6802c811044902c4e100401e0880f1381549620200c4001d1070321703103204124982c100010b00c0603003400407420790441030803c40041007070a032050781d9414140c02045601d00f00321419080c0400309480034880c1d113425010079044071521000b042c1001802d0b42d900a00002203030903549401c070403441d41c0c2007032281c00d2180c1c081c440003240d03524181c0e000900b1030f45407003040d2052142000006041903003c0d00501c0c15698141000e60382c9440b402084662801000b0001d08903818604100105098038021502101d15544c0418401c2020804001d10381000851078090001404400c210f828600401c1c40300060001e0001454001c1c03c8e00407c1e43d11365000d40c0b0f8240c1440191041202d110b041042d00c5990502130b20380c10507030300680c0c00c0500038480d0300082010151078010303803018494250700f100c8030040c0c0101182d582e0400c6c0000015103800482e84a071190100d8850401466004109150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 584107805 1250 584106555 584106559
    0x2806140c03180a080d11010501050402070b070c17030c0a0305060a0602150a060b040e0f0609040309050409030e0604180608030a0f080c0904090f0212160b0903010e10020309100506 79
    0x8185440555203540d86140d107a00e071a480301000d0000142c2d00c50902c403d0b48240020350300d01b080b018000c00c0060940f041030307022034042d41c0b040081ea404900c0808d025034200e01c041c0f80001c01d2940c1d03401c20b9010784001000a8009500000c00e01c00b20110070f10081c1039202690714148020764410042041d202d0151280f0030241e04803021100c111404001002d90124201c50006001c42d20380d82c1d8204941c000781c01c80440404502e05112449855610450b400501107a8503007040c030309036500405a001382e1042a0003151a040208100f602a0a4550b03869802a107160740711f90f9140701589038907081c0c62100003454030701f003030202d06c008011044410160590b122103410001845c030844000304004c00a00e102002400b0100c1290349500401e014180907814501114030240104404080b5480c0a40910383c05000d081e0101004c2030201400c5503000742c4d0040d118031003034001c2400f5001c08400701c0d15030300801c2110303050889030740d001d14001e17502c0360111041c0c0c41c501845441101c00643d000381d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 584109055 1250 584107805 584107807
    0x19050a0b07120306050604172a011e200a020d0602030703140f0c0a05040312120f0203040203072102090405060403080c210c0c191b12020409022806140c03 68
    0x40b20940441c0c2002c1d03810305e008c4040b5000401d80040c90990002c41d034178210a0140301c524445650746c3d1145802400c0804040d203203045070030a8801500c0801c000340044211440004403100e480340c180412880150098001c03a45900f0a1406000a5100704c0781c285c0881d1a0038001c0d081a4802d0603114030408483ca081c80d06038860a0300e008003030300f042c40c02108001082102000007098103a10580202d820b0720b49404102c10400c2c14030664070081e40c084030484c414000c01026943c00201d40c03048a02c0000303251804811314060946005810350080c1d000a410418401000000109644128003c0e580c51505840e0750560500600c10b0100c0702403081010901c510000742415001c54005a49040c214030708000d000480741441e6100d001094881d410608500500c880700481680e20400d41c680d18002c0d0f41001900b020300351070450080c0c00390390b860280c8011905c404803075210032906010074003d1907018181d1052030450324001c4100082d054480c856100c0030170f5040d90340c0c0c0b001d0280a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 584110305 1250 584109055 584109059
    0xa0e030c0c0409050a02031509060c2106210a0b0108060c0406180e0a1b030c0504090b04020f040b04060e04020a170901110301260d0e19050a0b07120306050604 70
    0xc400b900d018070095804d0b000c1c1048070300050b5820062a0074240d807880c500101460203c94442c1000070040114120742c8040081d008210352103a0031106411703040c4581c40843d12071034041a506414012030f02800764690100c01c2c3ea414002500c40b060a21889084000380e0700c882c2d4580e102c82c01078802030b8142c90284800e1003440d0195803040304074404c41d04075281099682241c0c1e15003400545d600160240e8a00311122003d240b502200d9a40e4440e09061180c0c486829000b441031285100d0700d04801e0790703a10940f4056070b950f011510050440b44049484039140c01e00d00c40158000e100700004111541c031104000d041c140203590008480392910300c07600385003031801e0003d00802840d00a480d507071010703000842010a000303503001e0304c4008081c0d1130b8403040721014554001d0004000c40d00c0e91220100c0c503060f41d0f00018030b0502c5601034420f140b20401d108000c142c000119042103500214000010480703d03400805000c00c940980400b08003103110718404c0c1e0440f1003074001c040d08880e0401003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 584111555 1250 584110305 584110309
    0x61f020c120307062715092102061b1b01020d020c0d0210050f04030503090a0b0412020f0f030301090b0307080703030e0f0603061e0105090d1209061103071b090c080a0e030c0c 77
    0x41071899035203540c00410a000381d9a00c81192354140c2103c800d4041c2c030100b0740448907604001395540065903042038030b1107180c4071280040074010741741645001d200210300016030880130b405840d045510000c00b55213918034803c050746ca0742c1005103428018800d8544140d80e200039800f500c0d00441561004864a0f2243d03101183e0680c4010f040d500d05100310203441c1c1c002103480204600c2180500c0c454410b042d0840c0000741010002c51301481650b01c01e00a02044038008011241140d0030408002078002d05000800c1c00c3c10a26400302c03c99000d105000424543c110305c07d0411420111104814400200e00304841030000340d446980140c28080341110302070650414455041c2c050402a0510320145d000400c0105046802c0302c1c2c001c142804007c66075007044180d0302402581c1010350030300b000d4245a40d901d000d54400503112400313540b480c1c0401d10420112a0140406000130b1200c0120610080c040f0181a60b981c41880d14010454000c0e460101c1030b40c1d00e012803203004e40144c59045003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 584112805 1250 584111555 584111573
    0x30f02010e04061e030606090221061212031006050703020a02012106081e0a030c0b04020402120f0412181a0904021b010f05061f020c1203070627 64
    0x31a590b001596410040780904145019908801c0381c548030004079401e43c50000280d902540c00104458010303c0340412968244020454140521003424a5603135040c000828440d50346070f09003620300500c3e40030322090360b0307000c0210310501c002100d00440659584044070940308913030300900147c0000c00d00c4001984211f010101c1244480c0302200e501c07070003114010407900c241d4400e00701030b8840c4514000c0109a040d0010341c0c82ca0010140100f03a1064038068408800040020400d000070b200040456031030354140d400150240060702000c1c0b80c620f200011001003694207540d81d81e030452041600314454151100c01d080b501400b01c8003549405049450030000f0034400d804040c0c140904410b649407440504500d0f0018000300c8124015124040d007110036844203241028180000c118003600c900d0311030030b07540c0e4042070490f4000a81040803030a010f07a80384025404000740d6010314510341e0002c00381603114094003081069034010140700304080c95041c40c003000005401901c03004070300408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 584114055 1250 584112805 584112827
    0xb01050712120e071805060f0d031214010609330518100207031b0f050d03020c090907150302030126030f030c0417010b090a020901110303181501030f0201 68
    0x10344080f07040e05606030a541841d0382d03600301500306048491000041a51405141e41003e0240c801036804258070001c1000f4031300a42000c0c00f800408005002c550b441903001c8801d07c0d0802216412658550710b00406000380c174440c4c00b201ca01c0c10041c00401204bc0510b415118003030f459071b00c041a4031f002e0266019000f0025080201c61680c54902540d150b01d000700f00c0d1907280e60b010f01502400c61910280a901c1d01c03800039450546c01406000e540460b0b0025410b81d01c013100c00070820313000c82c58201d240071031041042e5001104c880a00000340800181e0b102a80c1b81c1003001c1c52200c41f420412400c82c0001d118403440c2e07184199403085070001d0b0042d2034560f5142c00c403e0720f20701950700368252520350050b2410001940001401c000c4130046030300e0500e141200d0402170140305480340c001110110064440080d15500007521070260b0301868601622110400c26203842c0c1c0b42113040020390092407000701404e4000e01d00c2034400c0c5007a50005a05a990100c218040000580c00440d1a00780d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 584115305 1250 584114055 584114087
    0xf0d020f06130e0f011e030314041d01090513050a1e080a0c06060b07241503030c05010501090b0307152c030f06060d02060306030309090f09010b01050712 68
    0x10000901c2d04074110400700c0c0504900c140340300d4507003841904114078980580c008910b20350031265043c52404081c0d00c00c02200e405140060841c021644018602e10603a40300e40c01b500d8001e102d06212544080e6414104da0505e88100075503507031b000542c0300e4444a030a004043d41c010810001c0000c8250348401a407001c020341044540360103665501d8140d10a01324040400e000c3c06032301003000098002d450140c61511146c0e070a1491a40c0d9600310b64030702070080e144007240100302e0034221080d540502c04c07250313050881200ca10780d0b03800d01615050049000b641c9550034000045100c4401e40240881100050020301d560343c0341c036020348442141a40750404000381c00540c00100414480030345030280350400040310020810302094601969110800c48980180c01000b41a45e5260348813643d2540688240760380e03030b4076070001900314840d034508550b100900e002841040c41e42500031320300c207100040c0200000060b02d001500c03113001d10b0f540108501030346546040603900c203560408003400c2c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 584116555 1250 584115305 584115307
    0x9060f0302060d2316030903050a0509030f101e1a01051c1d060702070e151302030a020714191e0b070210060e0610030c02120f09010e0f0d020f06 64
    0x608110000c0308810120110f58900c004d00c20711544c0c1c454184481000d02c400e090030850380c0e48039030380503200e80104801d450034004003080ca140b054501707000c0c0c0c00d503a10f00070b000c0d1072020381341c000744a00030526040c00c0c0003104410044120703900d0143c030401a4004001108100c07034924000116903079400a03080020b21350511100320180001409081048055058800741e04c0c111a103c81c0e2401500410f010115030010f40f0411041821441564029090b40c80106070505c684000c1004844000140e41c02d1a1000080003003e0300c2d59406085100d1158415020600c1c40b020403683d00c0c006420b103035482c0713400523000c84006500040000d4604c001c107652451525542c1c0c03101ca901010484a10000d03810040b08012100d900b40308200143c1059171240d0401e06010002c039003e11041d91581060582e81d0101c000500d000b0810b8005c1c1e0001403241903a1810558244040e0350020b034017090110303620402003003c0e490009400007650102401d100314202582d020030005500c4241d40740e0304107034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 584117805 1250 584116555 584116571
    0x10509040804080d050703080c03060a0303050d021201090b0a0f0f210501050702010c030b040c2c0d030201020430060b0a0504150305150403051209030904060e1009060f0302060d 78
    0x4084c022451074401c1501c600d91a140141805010040c0042c240c2c441d003501001002419540d0801e40b41c16a41c251505030317140c0caa44074950000b8454010030340c8100d80c10800000382513109030008181e0100540f8981c440c0c0f82c1e01c40705404030130000e02900e036441c2640b9406110340c0c0005081e141c007120590845800612003174540301d0071924183c07a41c0c0c0041c0d455005c0141c0c03513030305400f90070401d0034151001c02a00142000082401840074079041034056100071007841606031102c0c401c10010014260140c00166103800f0b4000c1d44548500310001c02100f400c031951310149514644515052400044195000d5983e5402401c42c1c06405a2000c000b03000880c90b07031918480c412108606620f900350880c11030505074078001d4071080c0d1401c0c1d001010704000001e0340c042c1c1174030411000b83c0780301d01c1d08d0740360707000c2407400c1d8007038400c200350440e18202c1d00060044041c0d880c07038000c1026220f000030483d00c417200c04040e00c000e0700601d507695004c030300c08000509000b002415410b040c1c0d000011864 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 584119055 1250 584117805 584117819
    0x151c0c090509010b03071404081002070807050106080a06050109060e0103140f0d180b070807022103070614070309120509010306031e02100e010f0c051e0f24010509040804 75
    0x83e0808040b0110200400040e103410245043c1c507c0450340d40a814945400e03086952596189001c800c10358004c100e4808110340c0343d00b030710b03c4a58040001d00546072100c0003d9501d00d00f2482c00e882240c1010000903000000d8800c2405692240e05480120b07801c6403514040d40d100390070004400e1141c0904003960f000140708070707180e0145640c0c0d0710708101d403a0302d100680340000303402c038005408017000b1441c0040c20000441d02c2d0741c2c2d41a80c407000541c1060707520003101400207603000950b0000080c8242085815402411805148a000009078544520490031102100c1c802495001d06000030600c15004002404900348140b4011840701d0b125650702c2007031101e2614102070810340c407982804500d441c0e05107202100d0640b07849200d60b401d04000a00b000042c010364014040c0071112a01400010b022a4441e40f800410701c0c0c1080061902c4d0a6030b441410155100b50700400c0b03070076180689518280001003c0040140d00b440e400c0404100c5000d6026008884030350003003000007515 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 584120305 1250 584119055 584119069
    0xe030a0b07024218010c1e181701020f0c01090204231f0b030708010911040803070b07020a050a0f03090b040b1206040f1505151c0c0905 60
    0x1440268003402c00721000400d0120360703e1207106441c60b032440b61449000b034011407482d8030301c28490603521001c1648421034070034460300766036504803519428128640c0700f44e40c001c0c0c075040c0150a800c556110701c0000d4a01261f0848a01c0c91032382d0f4810000303004020510103c0c407403c2a210410000601d45441480e10070b0140d4000c3d200038003165120701002040d8901485610707151042c640e81108010401b00d061380071403400401c039442507a402452000340d03481c54000c03200986401d82140d903482c01d04000150261009200d8a0440c905224000440a9155096404480032203004600380503060b5501440a2002000e1309c0841c4075040e4544042038041005010050050009010307a90301414010b111102503044250004800c00c0f081051030038000c1114142d41ccd0520100107070f51074140000b009044000b64508016040c01c03d00101c2a07682040030741110743c2201c64244d48132081200c05214082c2840d420910203a4030138000d4680703416000b80c58036501c5450f00c0c82160f5140c10000b512 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 584121555 1250 584120305 584120311
    0x30806100206071404260609010b01051605010209040603030c0210031b03050a11210c0403120c02030a02131415011b1502070b090105071107050d0f050a24020a020a02010e030a0b 78
    0xb07040025184186c1909000064200100350000e228040e00b000000e0010f108043c00c4032903040030a4112014007500703505444128070010424413881d9602d00300101030042442090b4400c3c0c0c1c86540f10070704c3c2130092140303207924074000011404042c20342606030020b05008201c950055222007102031714144850090058121211b80100a011085103501446000624101184a0030401440820700d00c10440343e00510714501140c1030803851010034184501130341c0c02500184020390445107030049803c8141c00e01d016503503946c05aa5040300c000c001ea407001465901207a0031143c899050300b07032021700040c07150180314111410300142d070404040b80c0c014101613503811400320600600580c01e000c2c25401c1415403404842d03c1c88410340f143d44440091040354428410048004200b01c1c15214a14045400000743d607030080060a021452000c9520124902150310ba814103445045100755410f83c42c5aa00404aa022550056585580c95900103616110700c907840d000250074030054602c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 584122805 1250 584121555 584121599
    0x302013203011502070e04020619030b041d010c03020f03040204090206070b09031306020d080a02090409080f191e0c03171501020c010c080909040201030207120c030806100206071404 80
    0xe80c003071100f00003420440c00ea001710701c481d0000028000940c3e20002030310712000c114000d98807031800030a0290b009050349160b05030854108070200301a81900c07404c3c95030325508040203001200401800310100d21898030b41c4140c0240c180041005400d140c1c2c00410407610141c0b5052801c032503034452144004040740d0500d01d90748002407860060030380074000801042d482c002800583c03550f030700c040e02288005007040c0b0b9403940440c4900301a515500a40038664000c10702030b90300c40302c88446101c0741c3c0c81102c0780b480600090210000702440307040203040c024030000350b0004000702007a0444665116030401c0e0100001142c426406a881c100b42d94040e500340781800c200803495600190801c1c181c03150050500103d9140030000c16244030484900c11011100d0045641e580e200580090080e95400340c48546030904010056400c00b1034212014042d494102455031050200041402c64842d1400142c0249021614080c0945900c484841e020480f10b402c10713490300001900e150400e43e07c14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 584124055 1250 584122805 584122829
    0x609090c05071e11010c02011209020a0f080303090111090607080d110f07050606090c04030b0903040f061106010f030f0816080a0302210919030224090c01020106030201320301 77
    0x1c001c1101c20070380000040c000b070906c0040406c140c0c0001e011070710404005083d2685812030002195a0b1071440c001034101c0240c0c1e40d80245e01c40d40400d5a1390003c58101d200780d0f180c03001220a0780307070240c10b860321050010113081c50084255103a01e141d800c280d00b8440042e49447d26410b604402c000502020181034a2141e1200002e0801c586051030141c0018000c1030744000b4401d6001000701220141c3c0e03000f070580070741170b190b142d8054510312580d404629405206a07011840550002c11403010070701c11400c688140c0d0302c82c03081c1c8005001600c00107240d540b20b07030003080008403d1341c050f051440d0b180184140c400c009481c6c1200f90b900c00b41e00c4100082d40040c0b5212801d1144003030290b01c400c4c140040003186000c241050752483c00c0207a100c1d200b15240309440400d44200310f0044d54600b01030564a2034485080f401e00204003ea034110b1850007494681d08165105106000c00c480e0142d44038000d040d111828010410604407106c9051202e20658981324061040103500924101c9154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 584125305 1250 584124055 584124113
    0x13030c11061818071418030d080105150f0301031e0c0608190905030a0c1506080a020a051002121b030408030301052b030f050d0e0604030305100609090c0507 69
    0x410380382e160091000001400f18140028254804100c00b0340e840c40607440c56644c501200c65260360401942c5640d894410a0040311032964030041d050704a0710b0079070700045d0000001c1d0680030740d4065079082101054003071004001203001c83d081c1c4260112410180b600384800d0391220010660b40b40c00110111341c1610a1103640810030b00002d4a072900a00104032421803980c90f280c8900c642040d010810003111040810f12400f80350501c042c0c0303480c00d0100706035a524031046231151112101680b003127068a80018041c20800c0020840100660180c0f41c507590034142500140c00c03c050180d48010001c000300c203c0d900400c0100054001b200065440e03600d071900b046102d042246801c0910304036444028034256046080c0096154582040b80c510003008500701c641c1c0c0921a246c0c11154104411441e2515001c10114040ca000c0da80610207565481a000b020960b1344c455000040c072094000c1011040d1079211040401603440c0c201c0c5804080c1e100e9204500010481070200c0071039080c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 584126555 1250 584125305 584125309
    0xa05070206070c050a020f0415030b1902090f150c0109051e0f12160c0e04060e0613240c09170a1e02030a080f0a02070e13030c110618 59
    0x15455002c0c0031498600f06040c6550b4410b80c0380c0e0b4803000020702620041036a2502e6036541e410a240340803a141c10302c90b04a03901d040210803080c4c01c0e0b600c040800000326218130000c815000321068880003420340035903403040106000300c402c0143c10703130f03c45005c003448010200300081c0503001030140074070020101400d43d510603040305881e6a0300340c00d071540018101c0400c81c0c0c002c1141c15843c1c1082000c15102d051a418018100060010007040006105804901c0600e03514030607020300d000c6c40c0100311603084440c0f2241d0b108400d0300c000e04d041c58510140c90004404405058850701c0c00445450244001c03030312074058810050040010074400b41c3e051142d2030b109484000301c08181c81c0106a03116850b11245038405900510340717005220303c9500002e540f0700300014280c3e10f501030009940d031440c21000e80e650760080501d1300d0041c010140d0010b18601002081400341c04600c0039800760b0396569800303039000c3d520440308444198a81452031920f50ba04000f40c0350181141c02c40e202001e0000302 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 584127805 1250 584126555 584126563
    0x60b0a0c031115010b280807030c0315050607080d0e07030210090609051201091a150301060f090203040c0305190c060f02120c0703080711040615140a03140a050702 72
    0x4462a4103511003040c003466400403c00c03080c11143c2c141c0d4440c2e0349002c1c0350520036041d50038411449400200652640c0e00d141e200385000e00c0780b09a030350300b000036441c4003004806841c5548068403941d00c0e600824020b47c0782210040206134412500c0a18116440c0e0b0b4400544150f2403803103410781c221020400075418440400321071076603a8600400c01c10306107000279010030b0b6076001e0f4902821035031848101c400405d52000143e06e4000da54a060008110484c03050401c040b00c1500140000d440265014141401400c050340c20904103030042c1402c24900300300035080180152801d02e00c40c1c90000c0070400900031955204500d0381140100c192509001c060798172294085003c00c800204068212540810102e80008030003407080d50714048003014610b041d80c15040608100030004103207080041c480c0122040000540c0e0a00c0050f5490400c0c00ca20031405840c2008101b20b2426182806000ca0060a14840c00e003030000c0e4000d0011009408044121514211a81c0c0c035405c1c880c046030100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 584129055 1250 584127805 584127827
    0x60e0d080f130c0915090e01060b030c030705160c03050606010c05060f0711030a1119020102030f0306030316050f01050609090703020114121f120b0606090301060b0a0c03 75
    0x1003051101410304031034400c21104018080c1541c0e400840c404070410420720108801007502450030302105c0d440e5000183d1910082c42020807491038072041522100060040d0800c4444040c40d050456a6080c0c0d804000e6100a000f2810424200100740c4088280500d862040380103a544140350350861038613602d417100182c210740c10301c901002e1940c005040052140c4e030005640c0300d00489921040002d540825080c1c5110015010104038820000c3d80300a507c1a141b4009044a181b201c607241000c0440c5075201d00a030040c0c01c100083c201c16407181700250741101019089a01c1d10301d020b181d0a10b568810b41c0111000e4000c0564000501c00c240600c41d0414800c6426078600c4c240340040c02d81d98800c92000034140101011103290004d5041e09458184000b41140803032407410303058035410426070580d03d50495142d04404201c2010803034505445d260710486950184d00c501c001c00c030107500320554540d8150340740c1c08086041a4050050500740c40740b619070b0700215080d890081e0000e0030328 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 584130305 1250 584129055 584129057
    0x60f03060f030b190902041a15131a0408060c09040e0105010b04060311160b060910050904030e2d0f06280c0516030c1512050c04050d060e0d 62
    0x406070030701c04aa00107030016007194000e48082e600055406200001d402c02d440c020b54400d02e02040307035455421003403001c07407400812036070030240610758441e041c0540205d04003e02200600c18041c8800020114910b0002108940d205d090a95500815103400c50854016034507180c00303d10b0000302e0901d0f00030343c03400c0801a4000c0c0455030410034010b8490049119200130151070b002c140744003001402c100d4401e0415800315a0141d540c1d414083c0003d003041e54076a000e40c02802c0010400361a040b01c141c1601e0000746608210388070ba4401310380e1748100740e401176030110001040b0300050041c3c4000d40c0b003201918440d440303480251010441340d014800700c03050181508201005d582400c103045041c1003081c83c06e0039801c2400841045510410b243c0c0700402c3c521a080d00d005d840ca501010f00d0007181d101c0c1c0d00481c41503071115114210020f0203c100000710b04803801c1d0001201036900103541c450317020000c080c1895910f1000035940c0040c800103640751039a419020404040c18488180307001c03c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 584131555 1250 584130305 584130329
    0x90506090d0201270305060727031211012d0c020a060509120406033606050912180909060103020603040f0303060b0703021b0114180f0406060f0306 65
    0x3401020903a11009007400a04200051408802a888815040820104440200f85840d44078074000350755510684d08000460143c40b82190038410300400d20100c03200c08100d00c4907941ca19a900c1c0400c088a071450020701600d06500d4400e0301091040000c04008010b03603d0302d03044100c1506500382c10a42c04465980e081482e441c102c81d400003158104103500040005a50b558148040c2c2400c640100160300040001000140d0a5058105608280c0400b9200d2070140f141a800c3c11011000c081841102e4a001b4441c00843c40d150703c030304c2c5d00c03d0003401942c0d40591280503210203039011b8400c19103111000500403015003840704903a94040303c400c0c002d00711941160005006404014001015203004141c100e08040c420b4008900401e0312410542d1a101a890003035100c13010600c403074200707007018400401517600c54509800d426412550040c0790070581080890300702c50380380106420a90034941c90a03070340c8540c810f6900402e401d07034443c002a50280f00017400c0d644554085012046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 584132805 1250 584131555 584131567
    0xf050a051e15030f27031c0204030b070f030e0a1101080603071e080120071401020705060711010f05070e1002010b060f070b090a080d020a17010803041419092a050a090506 75
    0x401ca5510403031f018882004201115500340280c811504000d004600041c180003039603800055800c9241c01d10307102400204011a01c5035952074985501030002c1a03502c1840006500603540d044d0480707000b40c15075850b992281040b110a50046003110744140c048641040042070a1081c4018600203801202e1900100d1641c21224020b01102a0468003444605560007500b50f04807100c141d8454241c4270799152040003d451151641085c00d20b80d42842811080034045203d690f200300e00c592100d030350401c480420301c03101402e03a00401c2c05640d83d40c00c4c0d02583d5610400544440408103060903910280c5c1e2074056604c00c00a03040940c1c691001280c6d2000a03154810307644030500081e001a00c450460004555424240a4840e40b6500c1c280c000700300c1080100090003982c91035044050f00c43e13000f00900004a081c00d110300780440700844140013065450300031803d6038205580403083c1d4134540c04031005410417404401c005c610005240c4098981003600180209011075281341402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 584134055 1250 584132805 584132881
    0xf031203060307090c030b01120b0114130306020f0316020a030516150e010603110307050f1203070212210304030c0b091608070f050a051e15030f 64
    0x45a1940099018404800108161810411680100000d0400703210f001c0050350301500900144c68541e0014210215004001003d40280a00410181c0d50070200300402200007103243c00a210440032452020800400b03c1d00d0b5001030160340050801181d41c81c101407004404d64505000e100c015034000409407404250841c00751100070303a08241011080040749004040507c1c1c1a914010b03a5180c00c0708404004015401038060f80d200381c5c201c4c8661246441003560714421441803c2d03000580e1151004c1608010240344400036a140c1104e040079400d40c00240414442d3719040c807258061981800c001d45a400c501007038009a20425155040944004001203002c00c00505000c0c005400b00d0f00d84102000811014480f03005018076040c1c8801c0d41e983c45512501c100003264844507000305892030220810402c4560041a4036080684583c0a894004ca26101c10381d0089816202c5041c41c1f562100452149001803400d1003146840030582c0701c4418002446510301c080540503018030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 584135305 1250 584134055 584134063
    0x70c090e160e3303011a0a030f02040b0a060c0b07081308210a090b1501021f15030b090105090a033207030201051009200a0c0b0f09010b0f03 62
    0x10b5a14104200820798408a11404400c9000180c03400c10380c14480840080c1019042d03a404108110000d01c4003132440c4042c0880807504c14030080d4807096143e010030004645000707400070300d44098000300d00040740c103002822041c80355000b000484c0c3d07020070440821a03540103280d40300b586402c0000349400e1655440041700765064004002c0d0400180600c500300345401101c400c5421030b8141c0e00035250070f09541c0d002d040142c600303c405644074800715610038008403100703030980d0b0181d00605c040c045134151840c1d004124800d030a03003159542c0300001c108010703a10083c050340c040d12103017900c0d08240c1d445d942101c4009281a2190308614558000650300644419808608001d6090265441d180d41c442c40f8200008042485200241c402c00f05a0190000c0384901e404461311448683e4402c5034900341c1d0030108055462800c130b03500c510340124407400900209a50b030b142942c1d903124191f4031030600c00025150b14004082c10b50800c846504240564030104406036003891341d00092a0209a503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 584136555 1250 584135305 584135309
    0x1030c060e0609090a021309050c1218060a0911180606090604080a15140c030f100503030c010e010f020909012102030d1701060903080901030b0301020c03070c090e16 73
    0x400c00302100d0722100d6550341d02542c0300d803030004210880501340b80361044000c0d402503040810344001c403800003031920039910800b4403030402081150314061818010516595005060140b940c0c0c4020390000b40000400100e8843c4180a9001130800d0081c100fa41c41d00e585c89518600c601c0b4000440b02207000807030700d9650452030550b062070300c030462540041c50a001d42d4000305907612840c90301c0b805000701880d145511a5600d5400c00128000710030040f0320702011030305102c0941c0c0400124854240c250a216841201e203c100d4024944990029003140d0140c001070803180e441c0c5e83c000e0018682842000201405103104525206003480070640d1404140f0030400842d045900d41c1c03481c9039140d90001c10081e0700070182c806081101c20041c1410601c440f09540684120b0004104140601098000d803500020751509004460b001100540f40e1a10070340d030555003e10805a541c2020006800e03428810002e4185050a00c14004222180203401d10581e62114035150178900c2c9950000c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 584137805 1250 584136555 584136557
    0x51f060501211b0810050906090f060a0f081606020102130e06030114090a030801080c0625330218060a0c020619020c0d0b07120603060e0618010501030c06 68
    0x6822054840d01000400440718103000f6410b80d40210b802c00c80d4001109031003a24046800250036032524103210540000f210100e42250703540000c0b419082001e80116841840180491040c540700c68044101d1400d5a0000e440d540c0181040006245040000b0007d040140700071401c0c103a011034008000582403040030b480e41c13000c102144c0caa84085d08550308210308094030358000d09080c403480d540c0b0000840140d0005550310008a40c20401082d00c030b400c41c10080800d81440855032400c50100c5140d074090304200d0745040c5690010700c040c54000d41348001441c0c200e85c520f400740240300c00a003600b5003e40429104118280b51220750440b0003035000300c181d80d07040e00c80e1200c01d020b640003240300001a60095010610800c4400310390b000c00c081070a01d50aa480c00710241c02449020605c0b031500070174900c031080005540c184100114820f0482016000c25965680c0d25407030304581c10402090340ca90003035000c1091810b5100c1102c0030502e4054000c011071741c03443d19105c0e6118498081c202c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 584139055 1250 584137805 584137847
    0x30803090c040b1309170a0c021e0a141206040b07030608150403180b120411010c0506010614130e04030807090806070e0402121609080a02090a050c070f051f060501 72
    0x30244008100030b86c0f50920b1000c41c00e030351021040405803020b01088003c1344145044ac44040c80100c02120100c60640040e0410303082c80e00340310b00c80310f100c03030154100b90b003110369403d4002030900108a224001d50240b00c1d00d5659081807040101510341e035410600b42c0d640400300380304a0b9a01c000d4040e900a80500d00ba2141d8800d12000440c020040d621030f20500c41c0c00306816031203c0b20545414015441020000c00d00609000190f03101e40105401401942004004106280c050b0030740140030000b00056510781507000e940714560100340e4114180c400035040c1003000b01a00604059000340c418186291503518200701c040e41c0d03030740003051807003000415261344001e510356805030340300c951100b41032100918110a00340c0c3c40200482d80b0000160703001400068443c00400c03251030140c3c0252812400da9100c1d600c04024090141084210910820034071001c202c1c0c0c0c81054840a1107140503121020742c24140f40300310b0341140074103404940741c20f10800c0183c1e000754018130749103050700c0c5075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 584140305 1250 584139055 584139071
    0x30702060a020a050a150f050402030c13150914011a1e0f0f1801030e07030b1308070503071101030c0813050a140c120604030806060c03090604030803090c040b13 71
    0x40381070000d0018020034a02c101e174448000c11020304100340c10340b0400c03002080760100500340081607642c00c0d2406034040c0c0000c110385006052000d039108581444200200b1442243d018034248104e0961241c43c40c959900c1601e60008411110707107005001c0240074107000b41048545521620034041d41d051074040410998482c0c00e040070603078040071003030451103466540500f07982c0c080d40e0000005144000c003040348121158000d1140c2036945510744001c00320769086039610001c000018208525000c0050342110004000a0081050030712400255464604a29000754440d10740c0030650705250800b02e65540302c5502c000040c0d449440c00b2000b85040c11541440e0f410004040000752060a240c1c0303640b028140002001751840d4400c1d107240c1d4404118119081d29a0700a4800800150010020600c140b905202600400c1e08040941c0d140849150000300c8070340c0035500848804030003004203e40c034803041c4010569410107880a11510914000182c0c0701c1d980144015040795580d489 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 584141555 1250 584140305 584140307
    0x10803090a0e101a04031e03050a030c0509120106030b100e070503220b06100309051917031501090e0601120507031d0f0f03040f0501050715021222020102030702060a 73
    0x85840107092100b2420185205001c0520440e4094081a110f08103901000e01c1c7c1070b0b41e0316011811854060340c980d8146110408228050044d00c6405003c0010a002070704203540c4800c0341e101c40c000c900c400002e50b5403031850b0804007140000c10420480e0008807040040610040140c1d0744808145000c03543c03a902c1420703018218040191508400802501c0310f000c1090310800e40b405420111001c2d14212601c2c1e00807010b60310b042500030003681148240000c0800d2001506d14020f10030b1003011032031600340c240c085994100f21600f04000140d2031071818203580105030600070341802188000300303203410700028015030a2042c4045500e99900001080140710b030344804007492041000d40324482a54082c2ca513a4441c0022010b1030740107610094030311580000440d400c41d5003044009049070715140056407507801405060700c00140d42042c1d1400d10798a032005002452410b00204014208184030144110410009081d1600311a46000140c1c0e00007080d10b000c203a040f10f080e42d640a82c444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 584142805 1250 584141555 584141581
    0x6200d090314130905370605041107141e1b012a110312040306180201080c0c0a1a090f071809020d0f030818060708010b1305090709050306010803090a0e 67
    0x101c8844071ba40c41800c0d0741a000d200901d4011080c00240a1101e651580c0401c8129010f00303510380381c6000d0403c902d03000240d071070f0648640e02c00c090040d070302075020700c07126003081c5280302c00040503d80225034064950410101d00131000329081c40c144241c0f506075600804210030a80000031040b200d50198010081c3c001015401030202138265082c403011801e50107080d405c030780030481c0c215042011460368030320307030348007810669405944214080d100c4d214218090b5010351003030b03003150142c82a0100031035170b844001907001d07a00070915141c80c60320310784560400804d00c080b071600c3d030840708041000c160751500d230012548504400142c0010035100044091101d51801002c41e84603044840a01d0b4100031400c0c400c0ac4200c0c0d001400c081500304460316400c04890003004035035104014802c2c002004050b10364000e4a81c9440203103500d8500080c000c10040f07403a0710010b00c41100c148000d04050224a0050403480011814280c4100016008450740d0203091548081d80c000101c41d0742c0e100c0c1e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 584144055 1250 584142805 584142841
    0x10603051606080609270f01050123090f07111011130b040b2a010e0304090c0206131407090f020405150a0c06200d090314130905 57
    0x102118481e00003501d1040d18400248100e4012940400c00150541041010f040c4140d90340c0143c0b03208041500a81c020180b1030f01c02100a91003050444003a8a0003445824080c2500d185651058810022401403c4031014052801060801d00b8450030300440800c1d075802003490b04048411942c1556020f1408482080c00c0e82141d00748116020002080030080400484100c1c21803541600c07401000304921851050300e4045408100902550702600f034503e4150480d0101280042000311160b420b41d10f6003103100140e034100141c10000940340d44100141d8408a00107003400e032800c01e50302401e00b203443c4005402000c020440a0030584280300c1e5070302420748102d0070040c11001780c50f040003c0d08140141c42c017444000034030508003200305060300c10300070322a520895185207594803d03001d081d04001c1015984d1041c140c44520301030303c2000c1c080710142aa00015419410b0800914022000c400542d4581080014a0711382031000c282200390380c060800401c480e200c0703a4107254081404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 584145305 1250 584144055 584144063
    0xc0501081905040c0618080d120e100b0f030c0904080d060b0a110106171e0705040608340308070c0e0903070606080106050a051507020d031e080609070809010603 71
    0x502088200200348501c041602c03070300d03650710702980b2103690003810481c1b5a002e00c02641e031201c2d10013000d0324400e207840c000c469180907000c2801040f500a403407501d8200042c09024a4a4500c04d182c681003c0360045802ca0f003c0b0b000f0000c03032146101080360110054000380034190009204070a6054941010340144440030000341d803074030401030090196442900081d65542429030024030b02d0b01070b1000c2c80b400e0b0080c0c000b4200806800304585160004142005401c1c040c40170001419a12846800000e21001c0060858030395060100b01c0d028a500303840d0450310052081d441d6044407800350703800c240c0c0c0c5d1005a159a848540c01e014107580340381e40c0004030310b046001c1006002000071000c1e02c00240710350700520069480b0141107090b5041030140710f41054401004200d245007100454800701042c2d03058a02c1e00d030710b64000c14841120114243c000c189194215600d038840c00e502e2400d440c03124a844101d909000000503031560018003548204010080403d03141070080d40034000135584 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 584146555 1250 584145305 584145311
    0x1c2307081605010f090504050403090807090f050f1e09030c06010b07030824060901210209130c050910021606110d020615040509160b1b03070c05010819 67
    0x28425490303603641400c4100c4001d03080014000521540288200700d82c000f22500d40070080c505100600c0b0041038001c00540c200302c0a9070000504000511107080078020b091741c0480c0e0360003111800f40540304064180f0380e10035a60307400c01801a0305180d00941c00013201881e03d00949540d886a840c40c029100402c2c00c0d400780c04c2c000500c3c5160300703009050840c40390300d80301c00c0342e45c0c1c1c41d1006082c003045d030b20b0b0b1840d0511400e41c014554541100180703011035050608601d80300004131600c0c405c035800301d891280203900060a80c43c5281c803002e04418071002ca14113102d46014181e0050407030149030640c0b40101155401412480d000b808580d07a01d20500030600c900d03507620714004113440c5c0200f149040340e000e0380c0c800381084c0e440070842e00e102e8206003031f540165410705002c0c00001c00000f40710f24220f000e5032024110144962071280c000309030000c21349480341d0704291004400654050f075102681d00800c214800221040136440031945e09080030060382c1c0c1c41c9000142e02251040203042203a107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 584147805 1250 584146555 584146559
    0x705070510060501031b0806091306020313210e0906040905010e06040b0612030301290d0c021203060d17091512060a030c090209010c0c08030c0c1c2307 67
    0x20715031040d0700300c8009903010700a60390001c1424110207101442c034030004003182c001415a05020f0003460300002c00750260304001721540c032020b040360415240b0201200310300380400148030301c3c800c50084001302c9d18000e443d807410b9000003030241d450480d01740340140844030000c0c0e8159146e40c0001c1e441d5402c90000d0144006c4410610340380c55003120211100d42440c008a1a00d05155001c0350f07980382c00c1d1006500d16401c0c950314640081c85d8010300c0c03070704040d1040e03144c0d50005810054940254514008a00c1e2040480042c0c01c000340038095001980003441000400d944080380e03040303802c0d0840c1400c000e0b40300f80d95070213696208080f60035400081d84d422014490f403101e401401004c90440c14a009502c6610400c0300b001035a110240c03c010144ca400d20000381c107680105020f4005040840e803c10255550f0607a0409652201003940c00105110007211402c0c4000c0030224012285e0b40300303a4840501000110800b5200540040802110840d00c4182d00381d071146580458811100d00075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 584149055 1250 584147805 584147833
    0xf07180603020306120606030c0d08070c060909050106031a0f01120204120b01050406080607050a020114010f03060c030905030a050d060f0305071a0f03060f0d0b040501050a0b0a0f0e07050705 84
    0x544103450550180400c0c2110788200d45e00801c4039401018010098003090918400b0004a125000e2055941890030040c240c000f0b8000d00701200203008036124029158070b070101c03140856505920401c1071504242641d01141e8a14002906645044450140a1400034012285032600c3d80403001080d100090116070842040300904251703105d0340d44083da9a032030b076041c03206440003131041070743c281c0c46000852402801680904510b00440c8000500e041000380310082d00c81d000c1c0d0003084c40c400031540234002d10046000701d402685803410240544031075542e9441c0d8a204445c9030004001c0042903800c200043c40e0820401080e51441424a90307031039040c000d849040c03d10030083c803281c2c0600003490000c0e1381420341d100846140350b0079045a590105000e00c00d82400e04007a400450080c1c000d000074200c2481c2400350b801000002624a054101d800c210b821000c2401e1040050100c1041140c0740011080d003580d0785c0c154001c2c3c5948840d0740541d02405140030081081c003441004904113 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 584150305 1250 584149055 584149057
    0x61006050f1b1609061503020c150f100512060105040c030b130b0108060306070e04020a1215060206090307150e010b0a1d011a0904050402030c0d060501030210030c02060f0718060302 80
    0x45020040f80d065a13035108420004c640c40703446000202d41254440f01c2c0520700990141c8154000f150039142c088d4030309450407141840490790314030448003a20a101e0740610111072280130380800e4070300d44480184c25000713a80e0340c0760510415220319180e450000340b0034426004100c81d10409052072101c4042c042c2c02201400000802c503000965100002e107441c500069254040e002c540c03561480b000c4d421042c000a50f000e21021f106001000306050002c00040c03003200d09104990301d1258609042c044004c1c00e14a01500a503110350084c421b132000b186401e104034182503c02030b400131380784216180050250850307000403075014081d81000900006d00c0c8821042d80c0341a14500b04050307072038a60b10030341580c00701443c08484800340000005070406a00050704540014229070030840098001000601000c104035041ea03161001001107042500004401880034202448400a80d820096440710014061074010314100c0c0402e105601804503404075050070320300181c480d0b844880280103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 584151555 1250 584150305 584150323
    0xc05180a050703060b0f07260910050a1709010608030c15010803070f020d02010210050a090c0e0402030a030c030e030d0f02160e0a0921020703050609061006050f1b 72
    0x10604150000b0340062292080c603040e58045034045082100003031070810150405403084491200d041001d6002201c41e0041e164840c41c44058a0741e03c500d55030601c100e03c449030181ca004e0080500034901119004a00560b40b000d25907424a42907071060340503800b510403680300c00824000001c06281003240451840180340d404d0101100f00d91f138400741c2e5036881c0302c3c03140041d00014480f02c0100051401400700030080740148101c400441c6160f10200491340291405088150f4500101c810407915070540c800600c0000c070f90801c0e929140e008286c5598240000904000840c00c0076810035004903080036038450054115a100000c03080c0c050059900b80400001511440c19082d080703445c0d00d24a601510000100700300903490700001d00e005026081402c0703842d042009540459460040c448178401f0a07181d00918105140d410002c1c00e0a00203040000c0c2a00130404010111074407437100c2007155002c0c80c00940c0d80c5510507154009001c3e030310219907003003c503d4442a40c40400541d0040e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 584152805 1250 584151555 584151571
    0xa06030507110703050a0321060605040501030b010c0c141f030207020913240204030f0b010e0f0f04020f1503040309140a030c170c0306040302011e0b01020a0209040c0518 75
    0x101e6a04034290b1590b59042031200030900e0b402907a030b100000b40f040d035161a1101c0014000c04080c003010308040156407107500000e001a101090400040d070740341c06502224070081c00c0c500449886130300c0e41c0c41140c10601821404540c0395211640c140c84212003a184d000039071051607207804486100402035400b4010031b174810004c120100d070921600140300c2d140fa030352000d00204500d0711668201c00030b110000c07040422a60a000000c0407030300b03c00340c90300814032940b80c1c1c105640c140700744078210810151081203951079110402901020360f1010310b40160301120310b85241c81103040012240b1101d45102400c051020082c002050b800c07001d075800b40c40c460282c0b0030b03169000d8401e011820010744030181c46005450303420414a8480c598500f4414005025a00c2c0013410a001c17a1500300252400ca0060395100740c01d40d081e0055507000c0410b0800701e00140010391070040001d64402c1d000c140a441361308520003150400201c0c000792001000c01502000b1034a120806003052a20112120781c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 584154055 1250 584152805 584152817
    0x60f0420011d30011104080316140f1f060b070b13140a030f0206090a06093206070302040b18040f1109120f0d14070b0c0a0e040b0603010902070c050a06030507 70
    0x1880460100095600740c9a5410041d03042c04010314031050341c1c1d114080c00741e40106200d82c20401b0318505204998510072030000400e400cd40709000440e40354501200ca00e039203880c102c0706012002d044801c44260940000c0c074240749468489010b003810f100000c0040c2000400c8008503c2d49801044000c1450301036282c40403e9a13018600303988410040b940e0301c00d150020311039680010f4555100c0072225014140b40d6030380704451003808a0261039440d60070800350041c001284000d07000c124143d4040c0c0302d460b040d8109071800f50701051500130301e04c0940400c8164001c0b54107a4032558804030441c0000403041c0314015110207010210740c072440440d40507041001d80340107400000140c0c09002128503008118480c00c000c8212168070141e0201c3d0030303121080001e100401c540307280d56030043d02c0f190b09656960041c10b40c054680d00c214245140614100a00c80000d039550700d00340c1c0c5c1111881c1030b01594a011529080000c101c80340c2241e58009075020700810031030b51542c082d91090850392191 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 584155305 1250 584154055 584154071
    0x30515071b230606210106050d031107060f120225060209152503052206080610020c01030e030c0304260a05120a03020705060f0420011d3001 62
    0x110744403642244c00e150442154a40b03602a003c403002c81c00044502d6100000e011522880000c081e0400b02c041540000c0e20003110f481461011f11051008040a007414034903460440c1c0c024180103039400e400500b00740c2c003090b420482c104c1e100403c01050f448200005510456250040080d0801c050940c06a8020361001d100c1000c02c00440f041404006a060301c680034074401d00044500d5000200e042104c144802885003282042c2031032195100407002d21414201100246249030080c061403003580c405032200c070250b4000c90300f4100d140e000e01c1c01048001210140310310b144103803407800c5120304c40040c00040024401c117128015180b070b65212a80d40c0c18002115a5414519002420540050015950b090102c50003418500e04905000d4200400340e21040c2c10240211007005100140c20100400c022044065500c100c241c1001054506005800240f05180d00d0302c5209030680300c00d650510550311050705c42143d10041c0c00504400c1104052001040103c20061106608244017 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 584156555 1250 584155305 584155373
    0x313021003061712090603100f030f050606103c0921120c15050906070f020712110a09050c07050706030506010503130215210a0501030515071b 63
    0x264110049200c0c4c045007000a05800c00070180e0003c1c0880c42007812042001601840c40b248801c015801241e00030a940801c1c00c0040c01c1010003004240700d4046925070583c071980202d07039a580c81e040c1000514004100d41c0c42904118900703003044003441c4500e038031405450b0388800c854090361902480b119085420f4040c81c2042c0c046400d0040c10801080080c40c1e00a02c00c611040c0800e0044c40a01c403c2e01806100c1c6084807811b84551805400c600200b0055503080030820369504003a10003405c50501d131468074400540c1404004100c04514054003030b8640e15000c1d454090084204100403600f0594860b01c50740e44081411070b40340c040c600c8000b60883c000e114080c815078043e184c0d00d107181d032003540490365039017294401c030f0344924030120b00744041216001030008081014030703160380c070310407060103421030100145180c000c03500b04401400020000b241450180c0080b461121590300c1d40d460988000c1e109240e42d54000203000714031014452040ea041c00d00030314146034144100c2e01000c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 584157805 1250 584156555 584156563
    0x30b09040b011a07080a0503041a060f1c0203011a030601170304090b060705101a0904081b03071712090c150d020d021206090105120a0803130210030617 67
    0x1030050310100820340104022580c0c910021103a4142c03a928500c0c0030210758880405410040340303d0001400070080100b00240c03104c011400c5c0203100000031a40c5001c10000f04603032084900704e03004000804242004240c40d130b696641d410350040c000d01102445444013a58403801c00480c034800c0c495070700001900520a40c0b465080304124015500d49400c0c1600080948017980c4890b0b04000300f0820000499404e21003110010f516000109804844114445015040c0107400f48903059034001e01000070081030403071320110016010307001100039600c1d4850075401249005420344a140d50b0441d10803000ca40204600318101d0000c0c14540c0355407015a07940c1e0b40c07501e0425085000074448528001104010700340400406c00d0140c5020361403035545080e40c00900c160307407002440b4400e02070f2610380b6900c554054241a00c0180250004461203070307666054040c050704174040080031a485202d211030540a1603005846000740c4484200020000c00d103522032101904030410001d0f2220310301007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 584159055 1250 584157805 584157811
    0x525021f0f27020904170a0e01080a0c02030415090b0706020304060f05060d020d14030d02071e0c0e0406060e010e1807050f010305180f100e03040320010905120d030b09 74
    0x2d880c4807625820755092044115021303100303a0346135100c0d050f00803c5c0000c10000301507201c403980c1c3e40308480c09030f1800981044001740025140700e080c2903070741180c1d580c008155011181c220a0303c50024102c084140c48a1015811100e072441002420071b01307100c480d03002180a40c1c4203803400c10600004902c850110350080e10029400b0741d686c0e500102525142c2508100a40179624401d03980c465101c2e15469640305200c602215a008500c080a010b031400740c81a68484013a400c158600c003903520904c0190450044070204126800403030180b04041e40401d000d040810300844180d61141403110b10600211040000c001d03158a01c12000400440d1030000c660020b8840e45140e16904010760146c80010290322501003003560401d50000300b0080f14010b0060800a0011000390980c82000e0352403424540005174010401080050390461072a050315111955030070030f45c00c030f94004884901c0079a10880c0d0041d519801c0c42410030000c514003440d12400d840400a0800c41420301584050403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 584160305 1250 584159055 584159111
    0x41203171315050601120606020a0b100e070503090c100302180d03050301050607050c0d11031e070b0d091a011412030307052a0a0c05040525021f0f 65
    0x1c800d800c00e02ea01c050704850b40021050515036a0b01030044280c4003211895031201c0c00603408041c040f400c2c4040f440009821402417010761351234501345110030100610152020040000000004805280a001c00c640382c0390003c181888070610004020041e4001480d0256428007000304c07407055180480d48081c2055140d180e007825a0302e05020000c4030f421041b0199143c1c002c0841007205540d43c0d007648112075101d06c21180c00b01642c80c051600c0c141d52942c03813030040100740007a540c0c1c440001590004642d00300510b40d0783c41034104600400f904240c0030062080240c0d0304541c10011440888906030b41c2d1112242d070145d1031030410404140f4950a03841283d400803c040b9048520400040881d8000d60b01c0010308210100c109060040b4031040020f0582c00000d0502c2c00c00c41445680b0000b002d040381c0500c42c0d03081c0a0b031221010003d08410451818032040e0300c2010382d00070301401c1c0010300e07564110001c034440b600c4500b020385041410305c45103919000c906004010110500c2e4203032024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 584161555 1250 584160305 584160323
    0x20c1b06073219061410030222020a08010302100903020a030611190201021c050c0a0807032403050601050301110304060c120203160908120f0f0412031713 68
    0x840c0342180c51512401041d40c118445a110034070915810030100c3c40744400d5403900200d1a00d40e05001c4100c40201e10020b00f0b81c80e034003041c80003820003507071030300240d0380c0495850300d400200380100d02a241c9000f0302681000c1c00441d044c02801d802c5040903040380c0c02a0b0321008509051401213480d1100c1e800001d500c6540307a074081c00820798030342c841f42100001c2c141280c030700707101c21303001c07104070000b4a0700100141c0d0005030701c00001d5400504000d2946996805004501745007e06000c40d00408a011040081d40d03800626000c0c420307000350042003404400c1400c1c0c442910f0f500d09a10b0001d0200303036984d1140c04000a01810148070703400c91205500d0055055423507a54411014000c658004420041d6405510b00c000300c040c8029030007580c0c24240c150f1114100c081c0600318500580c480896a00102680004411500c007100c0301280000003041d544da45049095800e401250003000406680d8040841050303004401022081c011007044801a0f80d0f010f07011000390780e071442c0180a415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 584162805 1250 584161555 584161583
    0x1205010620070305060f040606050604061409040b0406170741031920010813020a030b0a05040309080307020a09110d0e031314060702010c15020c1b0607 67
    0x400c44020458941200d050b40e01407540d03900c4180c45c146090350b004840d980b00d03101b44810444039104902c014442520114181458480302400360040c801c91f101080300700280d11400c40c0e0751607101e40031000c8000c0c01002442e4587d41c0d03800c0ba4160f80d0740300c580355118100c4081422221205004100181d181e0f00e1045404c2c840c0008005c540360040c8040c142041c481710340d0450b9014007443c0b1080c03244802d203694004050a188480a4406541c8941003d1a1090b018182d9020100329889514120b03001e111400c9803000c20340e5030503681c0c00a070140c09007505000040020703030409402103000c0d58400a1098607500c0454407442041c0009521040c040420040f008031900004825104e410046d0b00341040a055182510b810780c290403440c0d000000c3e03003c1170008442490014044082c007041d091490b0383c0204400384a403010181c188518900042c0801200c400c02907240301e40b003071055445402100b00c0c16600d488201c0d6400c0740c0d64102c001e21840b41043c3c420303107048582010001034401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 584164055 1250 584162805 584162837
    0x501050a02070801060b19180603020c0a080d15080d0c020409151805120a080c03131226060303031807050d0c0e010609030b0a02090112050112020112050106 69
    0x40c0c420145902036004418001690160038410840244880b850302562442482c0c6080310103106001c40070140074281140c1046071a1480e20503007940d0080c1001690b59046654103480d02c40c0041e801402e001c0b0000e001507500c0526000b41e0a041c64100350307042c0c100d07190301415444404210810f000039a100b80c0131030241c41c1541120003100c0c01031603503041141c0ca00c030021058075003031100c43e0a0407040200c1c91081020400640340804032407020b0340d090030f2488038024000b00028080c203095a1022011605000038800d101499560014199407841c200c50b00c00390584455100f224180024582e5900c03604205c040c0480c400c240c024060342c9190307500b030f00d6580c1150032403030224000e1155502c0400c090302c80464202c01e0174010b402c4201c3c0d0b0761404000c0c61600308160071170030800c2007000c01000080d01016046800655101c0c0158030350440d280101d504000320240303044100c1c14400001404141e4500342e10025000380e8602520020303850b40300c005da840078883c4200145202005400034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 584165305 1250 584164055 584164057
    0x50108120d0c0c0f051608032b060506160c0602240403031d010204030b090c06190c020d110939040f09060f14010903030e010e03060109050108011104050a050105 71
    0xe0b4042c1c1c24000d0f030000d496211a8a000082c12046038564806812510350381100b198203001401990000c500e0300103600078442e04040300c1181300c4100c1c191440c09a8884480e600008083e100281000ea25010303001c41b880302c4014035442c02e40b02c0c1d840744400464281c1c03010951420181001c80c140362980c2104044038002e0303000a00641c1090f644002e08a403401b0304002d03030001c20080c000050b840e54250300307041e0124540600325803e554012031404001c0c2e1241425151040c2c110fa41c40700f00340d0700382c00307040e54107602241000798004c807a1301504040058850340c005203800c003a256180c0a40e2841e443c599841800c050160f0203881e1341a1b13680201100c00400e0245080c0f1f10002c030308283d03440d84501d0104031140c0124a101740c4800d014415501e040300c00d03500074981141d021807040340c1c89001814810341030001804001c0c103070846c860140d00400b0003048842c00603003155403541e960000200200001e000b8040ea03075081410095500c4806c1c03040e40c0a039107008101070042c41c60301006641f030f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 584166555 1250 584165305 584165321
    0xe060402060c0f0106091b08040506010302010f090801020403030512010b120a02030c091915020a08121513090c090204050a090911060c0601140105210408160f06050108120d 76
    0xc5102d00340b0010aa10001c1c000c0400405001c4004160307072041c00003e01d0100c00580447c802c0260300c808100200d100043c040b411241c080c204000a811940400c46650040d40c004880c158000070300081010b07400002030140c000c2141062030366076220182d19800c1d21603180c602c0d1205080801058050440798011074100c1d206170740740d41c50410880042401000d03e660508030300400d0704400c100e00e603c94030040e824240144041c182d031503100c0e502e80d4100d02954601030524060200020218215908051440c9000070705103807020411803d02d80250035212130031113489020940010b00c4003000c0c004e0710195040186501e1500d4201480c00b00105110700c01599803140d10b0302c2080b05078403031a0040c03941d902d800010b40602d40c1008801d1801514406d4201c1c1040070400440500301000a85042140b07011002c21029855604161519001c1c9044001415000024a1040103512038506c01464030511040c00a41c0e40da190740c40e2240100032070314917a52001c0000480c0410b0301e0340a080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 584167805 1250 584166555 584166577
    0x10816140f10051303031d04020405061207140706050403030605090105031504050a0c081011031323010c02030d181a04080721030510031e050a14011e0e06040206 71
    0x100305082d503440040b0f44c210341d520a4020403941c260781400e10701c0c00500001d12000903242549003a1404001c01c0c0940300354105001c62020b40c00112340f10324422110b60300201c600c056030350b40310321250402c08000c0000b6101240424540600013500341840d0000324122840100907003801800065221940c10b0010b20490300c500a071400704000030751080400c0003034420400103145c052901010401160010700d400c9800300c400b032080047d014020100283ca4941c0030808100320b06044110f507030310740b10f00b11030040b095080c810884241c60740000500846122401e051090414401c903541d1140700c2e4030009043c800d8020042d4802018520003503420921070f070310441c5010000d032a40310940300440080000c2d00800c991f811106581806016000200c204003803402e80d107541e035544c60032030140d1f42411113044e290004c40b0a001d81400342c02c0312540c0141062401c401480c001500034062081c2d41c01003c1c03404403285d042e10003103106050186848600600302a00c0b66020001940c01c5820011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 584169055 1250 584167805 584167807
    0x6060d0209060408030c21030c07050a150203242404030c090204060306050913110103020f16050d111f060503030a0903021e1c0501060806010816140f1005 68
    0x1070081e2600401400109846405980c4601907104094184418102142c9070700c07840354220114820a082226005003070003411540c2e807146494083c0c20036600b0040039080703201c1c60020f08848603046c9c0003544514521a0481940400b0303070aa022000103020206810400d1003c00c0504c000b5501040e800a000c4c54414a06140e0b59645410310150940c10000101d50013140800c4861741600644024010032128540e152900810700406554542700c060401401048000e01b0fa9000c0e504440c12400f5180c400c541d42c1c5d5942c032051448200032442122188603000c40199038621031200040700320544c0000c0c28041d0036048220161100f81604101190b54981c030015460342d042005288a21468803400300d80d510b1401045841c0c0f064640da104041004850b0003140da650036454900280020740c0c54944090500703046005042c0c54000d660360344100c000200e5181e100050285a002c800402c081d61943c9401c80700b019030781c0c4460340e41e0700300081d40f80c13034075003807130301c0903030100c941850f03180c40d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 584170305 1250 584169055 584169067
    0x61a100c0206091507050f010f091a0601051b01090b25030b0a05220609020414010c08040905092a100806030a060218010314060108011206110a1e03050106020606060d02 74
    0x71070055101a05c11612540114800c1c03803014402c0c0104442e4000700c103000c010f03500964440641c9552052202480d03156000001601c60f030041c01910043c01c0303d00510303940100500c000900800c06032030165034104220002400041c01c03040f4010200e956003000c4210a018124103a0103400311508140e8032900da4200401d8076180c0211404e041191508204082c40001e40600f045a5040d000720700100d00402052100c2050a001941c10110a1034403082001f001d09100200b4003030358003c1003545091030300703000c0300d500006115080318845a50341c08810242d1502c160100144c082d0b2250409070f0341a45800e028040c004140e449400503060b0f84913050750f9030342c0ca400c90f070207440d00390501e6119600401c282e59040c42148810000a600a50746e804d181002030b00204051003441c440d13070082c0c50000100324044d0010440010a81000351316082c28001c045c011021602c5224880c04101d141e41221511a009480c1251080c0d0082e0400303071615018090f55500c100510300e54942c0030405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 584171555 1250 584170305 584170339
    0x40c050603040b01050418080307050d1b050309150108100902060c1e07080a0c0506030601120203070309060f200a020f16060809031c09021309061a100c020609 70
    0x41d4415071283c0e03201080d80d03050408104c1101c001c556042c1c20096104103520004290300c040366004061400c20a481d403240017914400380c0024100807681030010300344109000e8114000e18000c0c1220f0050740c44261003042c1030015118244158030071540401e0790f40b00c00e0340366503020020460024282e43c0c50840420609454101000a100115105419031188d0b20030103100c0e24000d090440b018040070341d003c0e101c13002140c40500641d803040d1800404075901760f01070b90501c6005980e0304020f640300e142507078018004205800c0700b600d40a00305020084103001b6407091851184d9298280d48030780c9024429113030b00381c22651121080d0b00c83c10000704040081004000b13011080703142203000c100d04000d0010072280019200c6000c660040c00709115100c0314200c0d003004805d004ca0009240000c500015210b0008007400456003443e003040c2c0c0c03050003816008103481c144e02c0000c021060480c142440403003054802e5400014040c1000200189440b20080030b00250081c0746c0d1546640c0c0040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 584172661 1106 584171555 584171557
    0x180b15030c010e0f040c230406022107110604050312090f0a03050d1803150e0d11030a08040f050f0610060215010504020d11030709060e0402160803040c0506 69
    0x601485038810703c1101350b04901042d0642e004002c030101404070b923102e806030f00014003941580480c50b003040654040c1803200d903410a440c2841c0c0d500c030004007104926515a21503020070000a966500700b000004403540c4001255030b4070f2000702009941120355402500680c5020800c0004c988003043d400315006103410301100340d081c405c00d01d544400258000606061070b1884031003070604154000411310a80504481d070140b0400300036203002c170240103080c0b00c5500800044d40c001c2d204014880d040343c4107a00c0041d0441541c3d80312810411040e4100c1143d074891001c200309180c0088540000b811a80060181c00f208c001500c480c1100502a0501940d00040c1890120120380d01210380307240c01904450b00c80c1040000140301401c94400c0f440010700c10b1842d40051300c3e0510840d000700c80b2a02c000c01130aa035555907122650401003090399205250140062103488640c = true := by decide +kernel

theorem cover : BRFrame.Cov 583992805 584172661 := by
  have h0 := BRFrame.cov_init 583992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583992805 ≤ n) (h2 : n < 584172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
