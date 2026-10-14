-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1821
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:47:57.799977+00:00
-- url     : https://prove2.me/submissions/471dee61-6c10-4e23-9af9-78d8d0482b5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 327338129 ≤ n < 327517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 327339379 1250 327338129 327338171
    0x3070306172b0207050d15110408071e03020f0d060c110f0705030304051e0409080901020f06010608011a12040b07110303061e0d02130e071e060507021c0303 69
    0x1242c00949050320b0300310044e58410302481100d0042002085440502452000d29540300e40003440500242940006001ca140c0080c02100214000d641000441c8106000c04115030b082129008007014616020000f520591208040d00100d038905100002034440c45032b0021015a40c0340c1c0c80307081141418107850403c105420100641c4509000d214560b4000706440071600100ca8856406060440c004000000e50111a030080c1c20540803404106010000e400030b01820313800c407042c0b08240c0303904642c1d95100f84151400700d0071030b0006000d148000041c0702d040d6094480b50340e19160200ca100c1c001c10f074003101c05580c0c4a04020500280c2a48281008031500c2190300071415806c1010014a2288001003401c003c400350900f92000343c0c4603c5698054035400404031000c81c010350541201070122070705d409105002e81c480100e064159104041c0340a0a00301024140038101203050720782d907000c40c40990f8041120000007444940310000181e8a40c407a55003c13035640708201a5486100e0707 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 327340629 1250 327339379 327339433
    0xf05061012020a14030a05010e06010e070e0d0602090301021210093909051206041104020c0c0f01092403230708071103041e060203070305030403050307030617 70
    0x900d08403407000d66190910041903031190303140c0b200e40c0030440c07001918114030309000400035402c090101d8400b1101203101812640900355602d4595556001244c00c0803e82414030740c0701e85000115000301e087c03039025000442024000500c1c040400305a9a104c0c2c500b26a040441c42d0001014070103010107003d002c3d50303003074010501c11010410301c40307518241a454407010411884512134aa010b407003584464000d10024144070301a2049050742510f50f0000c17607081c2c543c0000541844a541410710841b103503070510b4406007114881d40c03010170554038640c090b0781d41040f914010200b9801542e400c00c040c105254000c914004032200b00140c1034544010380300200d231841840103d61852115002c65200003e0b20386508260b440402c29a032004441010b04254400400e0201307444200b0038032480d01040c40d51a0188003980d0302e41c101c0e6644100d03000280010310a0021070700003405600a580c10410504010500c0c0e41c5819025001c8044011031100542c450003001d02d07080d105041107102d140d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 327341879 1250 327340629 327340649
    0x1302011b0c0f270b03030d1e02030103110f01020d09120614090f101e0216060f230705070308101206060e070306030503160f0210020601060801060512070f05070f050610 74
    0x2244c6200000c0d1a4013400300302901090305e03000f48000440710680d40d250030002d0004215183d50312410f0200b001240d48040c18010842032051000541c00003d501c1c0d0039034441d0340c480c00703900e0074030401c4c241c10980400300711441d07901e48000300c0c44125010b9040e03101d407040c0d000a0140c2c2c842c02c0c252a00d82403220141c022141d15001c1c1c0c1500311102141220080c6440000c00b5a9810324014503120f550000d50300600f4452805442144064480d000b46c8503281c0e62500604810710200901d095a440544d0b0150105d0410003030040042c0c001c8215a920003205a40e010100e580e40240d100301c009408400c40d01240d40b05800d02003180322002c01da4201d8014901003058a09558a007a036074450348007403c2450340725000403410040f0b04c00c40c507841640d000d03210078070410100b1006075403403800307000d20404205030000214416102d181664103584500e4031b01c1410352103e04003604c50450510b81d800400208004c00760128060724100820280726600820403464a00000440e40c02c02c3d4119031188 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 327343129 1250 327341879 327341891
    0x231509160c060902131104090e070b160f0c08071a0304020109061101060504020f0301050102070501140a03111204032313180b030607090302091302011b0c0f27 70
    0x403541c041000c500c0c032540718000080600080c00000d443c4061694124251404c0c41c80020380c1611500281c000c84140c1e500c103100030608660303600d8441c8614020140c0c4404248101000818028190025140103038061040720006803280340100e8200c1e003001881c0d43c40f80380c0800540900c10701c0c050108270203468840c15810030b64002007010096108283c1080100290440051001e60089004142c0100304540c0c440000c00c002805400c02d1041c9409802000e4002500b035009e042e200c600084410452031500055441c00d90042c003400c2490300f6108400e01a440d148035201c450350340a240691900380e030407070880c000355620061480c50311120700018003203011614030b0100c0c00c0003543e46030300b5a143e0800c0c211220800404803c0503090b81352040000344014560000015010380b40250b40d0180e80c0d07520a4540b1030240200c5200074000340ca41c540740e8001c041c07154016200d03103105944040b000d0307903981c400c0301d4040c8044c2c0290b80710004400b45130b091a048034094040643c180c071018009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 327344379 1250 327343129 327343171
    0x5160906020a0210020715090807060212031b04050402030406090501050601050c10020c0a061b12050105060712021005180f0f0c0d0c0308070305092103030109231509 73
    0xb1807110740c00c000c2c01001015002c1d20424001c0c0b0140d405002d0341e00c48004107240c078040007401d20210707105960a0b0b0041200c041925840403481d240300980040c070b5240740d40c80310100048800000c0200055491090101184130364842c0001c6009038011080807681280c1c0e800e00d6402c507100a002c0c1d5052060800c00000d2100010030858034600c41040c0c01a102c284a0444504000000c0002084607140000c800c110b07160002000e0b071810308503a2100d400e0007081702c442080720003e01400e44e00603014000c02d00001c0d10000f440580c090316206407000c103856244d152040d46d80c00d03940020711982c40307400c540c0f4800b41001001d944918900c000d000101d8a608101d84980748411441d00850c10039482c2c001b03002d03504e184503005550040d815540d89105080040c580c0d04080c04462103000150bc0304005007281a030404040550f140240d45143d281c00b643d40010304115003030702400a80b200d9440320720041c98078000d10403144507170405904440c00d000c10100030350003887c4658041d201d01c90012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 327345629 1250 327344379 327344383
    0x1090f0b0102010e0616090f060c0506010b040f0b0304030203090409060204210b01090b120a06021201120c230a08030919210f050607020f1216020d170d0516090602 72
    0x40c0014034001401d22446c856001221000e82540040c01c5a54100074000303035040d030003c6e80300c540328020340641c0e02380d0b6240c1b00380145a11070b40c072415000078140003040c80240d080200440d08039120f401100d01e08802d11010038252004601c1c181d80455010504121086042c4280b12450148840d000d41c002101d5460340a180010b00030740c84c541d941c07120054116203c4017098941c01c0c1116080f9007100015240c4074010354400e140031520844c040000003842039240c0440600c603a401184c0201d5a81040f05081a401000031021740d2003030110311103038150311691160b6000d03014040c080e50790740742504180400c1c10308815881d28440e00b9507108200400c0d00000c04428560b11a040758000321442c2004400300a140401a1907805094140040031703400142e0400340380c0e0782500f52030070001128000110340c01584107100c1c600450601280046c5403034002d102e41c06109155142c805c001c482c81c806401e40010040d084d400c1d0b0f540003444000c0741c9100c040c0b8175003615454269040d034100780c4001c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 327346879 1250 327345629 327345631
    0x12010b1c080c0a0503091c030f030507020304050414010e07090b0a03020f210f24040e030f0c21180603102d0b0405060418020403020901090f0b0102010e06 68
    0x30600384881680c00820203001d0440301d181d2000c8045407002c6409040030b548a500500d00079110320b00c0a1501102c5c1c0b0100100301c003c040d01612803000440c403040080d005080010000c5c4214007003000b011510341e62f00d210b100c1c0c88000034115900a9070504103011242000900b80800303201103c4410403426500380120303041e24070b82d45005078450b04110348601e40c5001e04101072940d4001c000d50210340d060040780d6180300751000c0c4a0461075441e555a0881030884000040315045c0150054450700e0915030170800e07800c3c41c5181181d203000c494640080f119000556005c04e1508140056011482045031000344144554082c80c541100140d020004151071412203010f001c000c0000384105490004081c002c00d0040c6851019440b110340d00759140703004128102070501c1021010840700b8030391042d07074141c50000d85113a02d05410f01103042c00c284440030004d00310321f40800c404401170f16034400b030a0082ca0803c4000c101e41d03004c03810010540d5140c0101c2411a031400841c001c04203000034200d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 327348129 1250 327346879 327346909
    0x8271b04021306180506030406052502100c020312010e07120605010c03030b0103020d0905070815060d080913020c060712141f080f060402040b090106023a09030212010b 74
    0x91101c4c2403203401020b4034800354800d503030060700441008140031080d04614814004140c464410b10141848699041c40914002006074042038a03d0040e24844d840056003c4082c011241000004015941d10300c0090304041c05009039001486481034200c030b00500451044c900c00c1c00310a040030b0000f84540404030300902015104c1c17682c028035034041c0c0d046510980002100744000400c3d81880c69803000584104207141c802c40d0b02800c515201000040d0050f02c00410b0041c00b4001c5817135044180c0c206001142d03121090010030b1051440354401440840780b19409065249444d44000c0c1c40302180c001303580c800d14100050843c801c403004a91a901ca0f0090300b0340345d14900e1540002504c01c0041d00300c804035101e04000c803d0356040006400b40310741d03c00c88043c4100644030090224906088c07190001503805041c2c9407000d159104142ea0301382c40c04500c100b10191128035010414504401c044001c941c14587c180700b9410405500100e54001c00c000740b1100090700c0100f041d080d00c190803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 327349379 1250 327348129 327348137
    0x130f0b0d0b0604030203031204020a0605070c030803041406010303110c09010621150305030d05150d0303020a050910080604060e13110d0812100e041208271b04021306 73
    0x803002450342c0700c2007560041c41d00903003120780300e19502e02c0d10114245d0550301a0710a04041c000001c0c1103204504a03981c0e25031003491001c5251440d5a040c545400107407080703030308840c040d29a80351040c8c1080307070030b008500a031744180a61074251540d905282c0111701280c0244100401440b49a4020851480d1246c401901d010900c94000101000f031900503500301c401d0f0000740000003070090000c0905400c50304850704011903142ca100301c4041d402c414004035088481070b100c04020034007981c0a002601e00c0d50400b2403918125000107441040c000300c0c941b0100b111074043c0802ea00b043d00c10303c0b002d0010005901c949007810941c0c22403c8482140003000c502407418010b0703050b113170640100c0f4040c0e84040680e46400c0d4840542458100031a4185034420480e44006000607107003c0180c0159040206840310700ca80c103000f01c40c0700078003c046019803551106030310340c900c0300d44441d119480b030920302918260b400c00001c408044d084114080c404c030300600014850584038007404040ba001810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 327350629 1250 327349379 327349391
    0xe010c08041b0302040213081b032d01090b0f0a0506091302180f040212030f030402040207060e07090c1b080904090c0801051905130b0604050c0c1002130f0b0d 70
    0x200300c065042d090700025042070004c42e01015001041c207243c0c0903a10080140c442d041080006414240507681a159240c0d00a202000e45100d10f6034002d081d01c0854030181c20304091001c501429100036030030466821024004000703410002014990304590640c07000e11080c04d0290010340704d4003004c0c04002200074980e45000131503a451480e001e1540782d68130b42d001c091400040b030046200044805a018044a9080c03400c10034000c411100101c031842e00c440e046843c0d40e000c0c00002d420503030044a203a40d42d250103150401c030803c140760007005408001308451120340c000030600140c03c81a8070a03282e00700d06201c0050b2510056410841080e0b40014164203a030500e1035907001560301c032003415481c0800b4082c110900d450000030302c0c9210703078042c8a00c0e100c00708103034911080d064026001a80c0c02c40411250f00d03080c6c1119030400c91120b07070141007003402c0d5245400c04080d80d4419469076070000c1c407011031003440d400f00c8009003801d0380002c002c2c1e8a00100d04105100c1c2c81d0a0010881d5109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 327351879 1250 327350629 327350663
    0x12051e030c09030a05011a1807050d0f051303030e0313180207170a09140306270d03020c060618070503061507031106100602120c0712080d0e010c0804 66
    0x5000e075061460020100c911301c0c071090810f51300030700603411443c00d042d0240000c0c04c40c0382424000b05c60031201100c48095a56101441140d841c5c220b21400800241c80d88a030b0f0ba400801c901500d40603980030f00403640118601e00d00039088805040c17084040360002d0000d091000c40d603c2c03503003085400100c84420056078900d4004000e2054050090078030142c81a05004005080054000b1200b161201185162241d01d004800311140001c01c0c0d060f07100500003280341940d00886940410b12590341e01034003d1186940e400c010000356040d0001e0780c04103501550002c20400365400031070540d038603c1285845040c0c480e50080003000c40050090000c0840d0303451726101000c40c1401c088041003904d4a0035803500030a218004136442c44948506000b0800d450004003402044800381e40007000326007240314048605410401130b51907203018050000500c518039224460115101d820003554421345031100f40d08a589440112019a2504c40031004054001c0d0086130060303013000000c80da640040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 327353129 1250 327351879 327351901
    0x6091215060902030405030c0c0105090d110315160905060702101103090d1a10080706030c120f0605011106060918100c0f020c061201060503061f090312051e03 70
    0xd9110748142c070300c0001040300b805030100203401d800080f98196018031110f00c00443d070358000c04044690004002e900b40000070001080f802c1718a1000e0243d40040401c84140c410a1340201c40c03a00c003441d4203241d06448103178804024800342404841d21400d10706c2a80104148843c1d400074002800a010f031184003d039030070415500241401003c5000c0b44a29140c09528000d0244100002584e848040380e24012107a071441e05580014008108007850b00e0306c12005060381502c40b9091160011400503486554014405d9510340050082049440c00000414132407900101e02c005402400512215680f6034902640124008502c0c1e5070b07410112003098108464440080307c0c40307103822481c02100b5080111400e80d07000540a940c103144425061024900c25100c0b040b84c60071944005202150081001d16004000504000307400032048440e01d0382444001100800314864502c1001080408030620101c81900d00d0103038100310850001c40c14010450407240c002610220028102c0c43e80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 327354379 1250 327353129 327353141
    0xe031626030a2a05160806072c030613020a06080c091017130213090b13050a0f1a0a06060219060f1d0609060606180f060f0c0706091215 60
    0x443c0c460800020a1801d50750b11602c003003800b030303603010103d40009900c6404a0610310030740d0a500c40c0f000c841e160b111040c80c0346040c070700144071084440105440c0c6031000c10160780300c0c0640140350307250500280100444c46000e94000d108000c695001c001c1942c004c9026610001c00590742e01c0c650481c1e045043d255284418486005402214100004001008008102a802601c0082d80743c4150101041950383d4000003a000100d014046120183d10001c801c01c007502500c10386000744419510304031003400400c0142c41d002c0b20361156540907052244407503041555038108100b60351902c0c401a45803100150780d09042c4130080d096105000d41030b00090703d1425007420401107800c00003000e0030a8080c40d5220a110321500c00010032903400095002c0c010b0b80014201c0e41048083d500c0a80c5a00000b00c640da04140b0703403142ca6140740c403a80040c010301c6241804d103135143c050740000d40345440c115034058410400e02000030000c010101d8490982c0c0e541120384d81c00320207000c076411406814 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 327355629 1250 327354379 327354437
    0x603010f020a1e02071409090c04060b0c0c010f0e0d0c0b0309010c02010609060e27060c041502060403050d020d0e0d0810060903150c0e031626030a 65
    0x7000040680b5141c0d4082520700c0a090f9207034001010030600d080890341c4504074055141d203440780421a030300610780b403c01507a2051800d0100e039a05511440458190b950703503032050701c5410010030780c0100e5060520400030110401e10700249802c02030003008108480d810321184c003c0b080c00c41e5800034080d0304407142001d03200b202075465a80c24513030407581c0200f41104608005503e00700020a510307045005500c00c84030841ca9500080e200c2c0400d5840e240c1c0d1810720200410003103400240030f5142409020321035000f590640b03031100d00e414008911740c04c90900701c130b0443d00f00108110000b07030005c0c00e80300a0b542c403440050f250f03008104107400516200e0f0380c500f0a40703c1c01642038103241e8040d800c82d02c00c41900e28202e50507680c805007a02d510025000061501456180501204125511181503020545070403e012449a80480e0620304103507075500d11040078440c203005c61200102d40800003080a02824920b840c3e04000315141e001d812921000c0085030060303a4002c0c14000c3c15644649 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 327356879 1250 327355629 327355631
    0x60a0506030a0204150612141602070312030b0a0e13080309070302060d0c030b010f0f0f05160c080601121a1b031005030d2c1c0303090204050606130e0603010f 70
    0x21132a41c03513054801642c406c0e000000e044403180400d50300140a0040c4090b4a801c1d517041e41c0e140c584a0b001185805403000045101e4180004003180f030422452a101c082c9490010300302c248041844560465900044981d06089040c070403110003103010b080781c098000c501c5030b0322501d603080c072242451120792000c8d48c0180085035200100302c55500801443e602c0b920200082400d440041d41c918500c0c2e0380311002b180c0ca400c01040190300030481d0100300149841c150b850300011485140c6445440f050603a010803024000b803198000400105001d07249600c02c44c4040c42095031510410b0780c0c03c0c04010381c240004400b142c010680c24024040d0404154071180d102e284c44521040006554801d251091040444261205002d203e40009102c903600140080d800c0e078103a108500e0500c880c1031030700300d5400048951010300e400c0090440300c0c4640d0b004211140b0790300420003074410103050581700d0202044019101318607640c2c0e0004a40140c800d810700782d55807100180c01000a01e54544c110303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 327358129 1250 327356879 327356891
    0x3090c120803101203050f07031404090b09070206100902160204050f04211e20030909010509151203093001110f0d021903090b090c03060a0506030a0204 67
    0x1c50038014600c50303000c0741040c492240e0795860200800d0314510f40500071500030441c0401c211646001455018000e05183c8100c000c038101010f22940603603c441c80352540c600d00c0d814503140ca14070315504070041c0d00c010061420a40c0c040780400c040362042440c11580010201000f1254120b070180b03964004108204034a000c158001030745030121401c0360310884196581c90f10901244e44600012102d0703880f48070120b0741120481d480d0113400c400308140500064401c01b0a9100740c0f80b00c560056017400340d52036075158010704c619201e068010501c189666400c000510200103040e031420f6004488016035004d280540d64114800e4110346600104910340c0c104580c503411003011071034130b00c071100d401c0d801810110070342c00c985681c4040710714004c3c100083c105204614028190340c018035840140b404581445a0045400960561b00480c2d00c441850051040714681c0c9a444a1100302400d10204400c0000f40c489034001c0203c50019501d001260302918200000d086060707010380204a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 327359379 1250 327358129 327358133
    0x180a0b040503100501060e010807020a021908190f02040504030c0b01241d0415120605010e1003050c04200304030804021c0201020712050f1207051c080703090c12 71
    0x18952060240ca0302038030a81401d455854101d11405041314074580d1500e0b10b403d00301e001140c1305100a000c041c2188a800c8108c80580da0b400c085d2030071808080b911f20915482d204407507041c59600280b40200e0a124003103100883c4c0ca07190b0581180340d0441d00050385680d6071400b80d9a5840d40030003d00058089000444c0580801d020f04415181684054a46802c0f420085610040003900903c8020605610407018105a0401030000c030140d44407007400c036104c00d003d410001803288251003142e11280100049140040300355006030400402c0031500e410b40d00c640e40d039882c400c2c4d00e0324000d5543e000f01009200280a444100032000d82000303680e4141410024904a005c0d60164455000300050030044d60259900c00b8030158103801030301056103851100c0a900040b8003003601d65000e0740b16103c2e280c80041c0610346210a400005503100c01c2070f070402074500700c072416180d8040c40100d0854030400340c0001c4481d61020280c640843c6145051138005d450556a0b800348010500900e07000003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327360629 1250 327359379 327359399
    0xe0f0d020102040915140409060209060f07020a0617070f020106050a1202030c060c070b09030f0d0215070203031e06030703120e09060402040b070f0309080a08030f15030c06180a 78
    0x110382c03610f042801600b01c0064291702d910400d1144d074a00255640e6024001d00346034205c1c81c01140038000040c1411401c00102e0100d610018040040d400002080c1e411458207603140006003c0318a49010282d080180100400702e000d0003801c140030203030001039001413003504007202911020b81001505581d800f901e000c1c443e480b8108a202c0d002c1d10030140322034104841940d4441c0c10b020300a1a0b1940f42c07007001c10345030780000940303074050150324030260081c00c0030800c00c43e0004880d80200292410000d16144120020b4041c20440d0400c100713020b0a149002e11012140c401e5140c126410303101c890000b0724003612035100620000e04407001d240360540004039103444e8041601d6516584ea9590100000c900c2707103008031896081c0038065140480e50b804201c41d24180304e8141107229980310001c0303070b152450052007221144e000200300002c1602d1291256000101d0790800c1803d20140000242c03940008940307a4011000410399a611041111403004034000107400b00d00019226071000c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327361879 1250 327360629 327360637
    0x607050d11040b0c1c020c0d03050403020d0507081009050303072001330b1e0c0304030f110f01020c120106030b0c0a020111030c090108060d08160b0106031802040e0f0d020102 77
    0x6a04c0e4020114484205100d00c4042e80b1010401d9020389644c02d0b09100b08656406046004e404005042c04080010303241c08200c0d10400d030003100100304003850210706502e030100a4450110780d42c03d180d40781c0005207000060b030303402c400503050025000b102d11803000a60704819052003185d60a0103038421181e850050b6000c07252140390508078007a07801e200d1003d05426103104480742144100600c05110440c940042e258182c07a81d115840d01d00101c00c2d06107107410540007551288020011a01003240e03c00da901d89d402d1041d40c4440715080250000f0b521824031000b2540900c50500102030342020a502540286034890902c0341e490401c0c28450000d500301d04078001c0590318202e0034500601e940c03020780c0c5c45044200310403031402c0d40100044942c60000380c00260444013100c1f5040024006d040901440c0a07607006c403107070401c4a424410f08100041e40000d007450f00d0415210619654503105007c0160107840104690341000c204500e40007410084172118060715507101c1983d039040d0014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327363129 1250 327361879 327361897
    0x315180405060606040e010e060d200901091a0d02031002130503070605070c0b0a02070f0e071e170408040f1203090b0f031f080d26040201020607050d11040b 69
    0x15242c654a040070701c1a540304034092848500b501d540100f10021144410716800307100a05000700c2000caa6907036100440418a0762909210549189203003800e01c0e1014030b00601c4c0c1900181700d10040c1e810f1126141c0700e8112140d0160812007014415500c04014502c100041030408560300c0c500c10f03a04401c44c0680303008040c400d0140060004007075110702c0136941000e412a80d591800782c070b0861401034552001c84c14000758000c4020006100c40000942c40050008034040442881c0200d001098071450040c081d0852801e07070250b01949074801400443e400c002d0303030070362000e403518241a003c60242c1d03400b24691418207003011036500c2919418082c140e1081c0c507450307500c540750005113030180900200140e096070103000240308000c40611844400908000c1ca421030707911102110b06101c0c2d000c06110214050741c0c0d01f80d1850300c400103400e1052a108194922a05141c6d0000b5140d40010b0086810050081400940310000342d0042d01401030480704250f0b11381da1081102030582150340a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327364379 1250 327363129 327363133
    0x1021609091a0403022e020f0a0206130c120305161a0f2503090b0a060503160e0a050402031e010f060501110a02090711070f0302040e03040b0409020315180405 70
    0x1c2c590000e800745000c50700559150f00a0b003040e0390703604074580c07001281d0407075410000d0b080110307030411948510045c00c40007891960315544c1d9856082c0030345080d4002e81040540d42040d8160004544031413617035401d440c203070ba8852004070024181181c4500424001c0381d80800f54201070000c001d0442d0182060402e1a04e004800c0d549910200854203000c55207101d03c2400c03c040c01d030b03013000a00140c0d1046c07181400c00160215040c0c4a01089000860b031426246030390b154140014030b01080761400500214200d407d8507400d0000c05203048001501e10b111403a19940400e0031940c09000c12402049206050300c10745a00074055400780c9811900a06140c1c6401c9001c0f8055204685d210301c0304007281c006103c4e4121650901101c000300074039900400607800c6a4018540040c41184010003480701c46515a90a5004000c2140d801015181c3e090303104210402c042c41e107007400d40702240c4c1d44100043c0c03603076a140140890040c80a245651004140040a0000c01c0c4e41c03084500490081d01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327365629 1250 327364379 327364403
    0x703051005040308010f0b030c0f2110090603080d0c050f0a08100e01030209070c151a150a0c0f03030b04090629180a0612031116050d08090102160909 66
    0x11b81007016035402041d445c05010400583e400b40c0c003000408102c181d0140c250700e0900e641740d81000380311907001e0105400350b04400b4402d040840b04042c00c0649101e600c200400383c5507948015180c4140500c50307044a442d0726880d5021801001a901e24405040c601d65544502c28030080c001401141d425070182ca10200200c4e86003070345501c0d6030503a41d01510324a01e54540000a4032014194541100c0c1e5606800c41d1045400c1107005401d454081c0071254aa0888504104034000701c0000d40110307a41d1081c014a04c42a40c0700101d04038440d040080d4040182d5541003c4014080f0200216042130420084104000290307200c81041e8500c00f01d00ca0301079081e00640c0b00081010200c540d40001c4c83d80041440041010006400810b0b1020019071665100d0300c011241c6100341c015404a40c001e1080d52600e074040c0441c0b1980c941c6c0c4440c05031410309080c00114801800341000d041d0500104008200d40d008001084440c40d43e04948110b0580d2080b2410162890b100d086404d000420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327366879 1250 327365629 327365639
    0x130501050106051c090807020d020a050a0603060501030b06031006110307080a0f02160609090b03160605030f0f070206010306270623040c03110d080a02030403023c03070305100504030801 82
    0x5c403c0c450155448010503241600712340806c007000480c0102030381d00c4020760b2000641541d5114084004155540f80400c00c24070b13010000d0200d9581f65582c034002c410030010070a450b065072444038141c1c0c11a0924036982440c5440303036480c50040b07260080c07214400041034004e0a0300f000c513401c0080d100e075003251411101202d07102414101d0b40309170004903003169805c1c04044150f4100c9507040101408444251103111500c048600a55100801103140001801040d20403070a1155100a221000c821181050700009558040520002d009507903602107038a000444840b0350020840c08051140b503a100c141480d60080124603601c016491500c61301250301c20002c51007520660308001e40da0300a6140d611000c21009036101c4844c0d00440060054000512580c06801500c0c03c0342d00441d00c66096205015060002e135200300104220702c4a00801a1640850911078030701001480c401403401d08040303858200140c0000300075018a00100d91006039550105115a000f55100f9040ba40e8070307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327368129 1250 327366879 327366881
    0x120f070c0e0f0a2a020a0503040e04020a0b070f03031e0c02060106021b0d020411070206282f01110c030c0106050108130602131d0f1501050909130501050106051c 71
    0x7484030030740191062464800c1c03013400492414007254060040d106900344603540d043c110345c4940c0001c1e90251900c2c0a00c820350070418000740150600b040d5851518031107072540784003c0d400c00c10040070551107580200b042c2081e041c40b100303400101d80301030145054101019403203000034007c00c0c005101d00f40c02060b82080c40c14035582c2c10f080c0940600e110f801c0a800780720260950b425007420006080000600680300c1d40014804080094101c01c0035007000c4407030945186660580380101b1040200f60314841c1c4640c1d40b10100251094036041e40c603045c08010b1400352104852810128001250826140c2c03400302c0201500171304600200101e503100e40054411000039200c40d094045810245000600554014100b01d080c2c2e03031441503080d80c0c9049401130702c41060310300a000100d2000b40030312815510000b03030f04030101d41d580c04551860500000c00c0c6004500d4072910942d17500000c10282c4021404a91101d90820300920003582c46120140140d881024650718a1000004000000c415 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327369379 1250 327368129 327368141
    0x80c0405070516080d0207050d05040303020c0d1e060b032a0409050304050904150c0306050103360309030210030e07060503010302060f0f13090b01020d0e03120f070c0e0f0a 76
    0x4881c0c0c3c0104891410303115004c064000180d08001c4540c05c02880000ca00b04002c0300217244541d0351502d50b110f0852030000e00b007034078a829040c0203c2705c04d04a6400a0f040304070068102006541c1c14035841d205082a0024010304081c403a0580204407041d9480d05000b000103006038001c1d000010801c10500601049403050000030344503410511042c840c80c540601055005406450785100340154241e0040454039030f81e20b0500482e40c0c5090801865805003c0d0514201048001440302c030300d911a261552000106e218403d08218003494080502410440c409035401070603072441203000000c041d00030301101d00140301c203101d402400078240340b00f10210380c180c95003d03010074181541040c10035450b070131250306100751003800d200e03405070080001580c0c401003c03c0c5001082c01280c031800a42082c1e1800e51200422550b00480d4a203134030009004443c4405201409540d1a80c000c800450b900aa1500810541702c11b007001445528408089011f0240300c00384107842d4413017002000844034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327370629 1250 327369379 327369397
    0x606011d150a020f010c0503010312030b030a03050a1103030a0f1103160f030b030607030501090623240c030433030504080921060a09080f0919080c04050705 69
    0x48081000016042001c00b90004008900444421201c144441801e407000340007590300180002c001001071040e011020384954140e030500300301c0c028140012a40302c004c2810090140440021280c3c3c0880c40ba1403d040c8510710b0303006683e240e0030318540f0040a04150000d1551060030409401c0141e100e032000c03a805203242403140240e140d4141d506645a050a22110051640d140030b07000b603540b01030005a10883c1c09980000e032560400c403c071f0040b42c4680c0c128029010000d0701d043d4000400b81901e1440100c1211070b03498500503071150141440005a00640d0524041480b010700f1200201400a0751201c7c08011095500322603900c03416038061000c108031485180b4211071040c020f80c440c90704140600701c035601e044c80700000f00703a03000e040080303002c030311403090340c103126031600c248084c0c0c1d00b10080c0b440a010600044c6c903041d00c40c1c015280c28070320319500015000141c0e901c9001c8101021017281001c1c03d503580d104865074036075041003a5640182d04247c00990705910482c111b8180b11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327371879 1250 327370629 327370639
    0x301060b0f0a03051e01080604030f030e0309010302030a060b04180507080606030a0b030703060c0c060e1204030b071e05071e32011d12030c0f0702011b050606011d 72
    0x2c540c403200b14040c18000d0050030b1079011204800c058044010201d9000c0c1483c0001020113042030322340200820796a0303001d402010320308404410740304404011158440000d10b40541ca1340c40d000c0140d0020607a07036200e0a0303240400140003030740c0544810040405805408104000c0c0d580310000d032203c6130121005944044100001060340103d07510611000364003070200d41c003864880e40c8040c01c855a498482000c40d900ca200001004640c0c098800d0802000c1c0141c501c0c10940d83c0800701c5401140002042d05820100142c2c1c4070303202d41d100c02588080c0103281e81c9109640c84024007654400681500c0480003900244140590088040d409079030055200041d9101c030f15555200b980100760034139000c1d00c1d080c11000c80c420240541400c0c0c4e1758000c10728100715136040c0d07000d140c4220542c1080020000303000300800711001106070b8410103d03c1e25201e50301c2c41d0602c012a01028540c0150814060b104c40b800300f4040000ba0440c4141d02c20f88551401e140e1300c0545104001c0c0310b504040d804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327373129 1250 327371879 327371887
    0x3120305060a061103132303010e0325080301090507090e06011709120414041410050904020f1f0306090b0906060a09030209040b090c0a03050a02101206060504050301060b0f 76
    0x40c902c121000c00d04c0c030036040280c1e42043c1010b200130803c01040d6203c00140d8801540034040c121500380c4c0c590414030210003c005850124164980b81e0084170004a925181444400b501e0002001380d00304856010701030aa6030342e159490071006000c156042400942c0d034141c007103a0b0300322250450b4020310058540042c4a5078413100c62950000061080c60103020303940120307544600d004013070805050b945203c2880080088240000c50b817030050300c2601c080c03205080c0104c0d8038119203610203680c0161514442580d031800420128104d6525507500310808035590460350100c4040c1e561b240381590f0341070125a5031103c00c4400c0e0360a000c441c0c2d9210f010748000c01c4907850154018140e40016083c0203081d50b503250000f5a8488080318183c8070010944200300031200300348a08400d541c42140c5070118076013180c6800d60b9482c5c034100001d0144e052041c40b2402c003801786d04810801d13170b10a84103000180d103d1000800a81081c032401c1d000e982850000700324030050100352600ca0303980c1407805d410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327374379 1250 327373129 327373139
    0x4060b030412050c070609230a140114030c0304020909031c1e1d1501030b150d020a090b0a0b0708160f0c0914060a0f05010507051903080103120305060a 67
    0xc0312034103245400a00c50200443c4d0344000040c4013070f0b802003125442e888825407400c2100c1021646200c20018800c14013504000c0d40d640c1e203030541c0150307540c80c180408000520070041c2c40000740a0100345602801200700001e5052480086220328800d40e55140151140080281d8a00030407160501205c0a081d4205560120f80e0081d9074400b81510907000c10600202d0400c210786e0b00a5194002c079160501200c4404c504010140b4003000c1c5444110540d850350f21110340c121005407200041e0000c1100c40c0c101c55540002d140c01440d00289066091541c03844104020a01108102e000e4246500002401d49940c41590440c64000c03202c5860200700c02d201002100304032100701d44c4003050341b441c040840d210721a030002920b407800c8005941e40c0105400c00c5d0880300100518441d03510101d003845080344008401d000c4640a00f801612601145042c900701844906010b0540354442d03446c5080c50b503c40c2905040324043c1c00d259250000c061821020707101d040310640e801404031041000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327375629 1250 327374379 327374393
    0x2070614180a0b0a2304050d060b0901080c03100506030a140703060e06060a090c020706050904020d020310140d030806100917071707080a0b060301110d021804060b0304 74
    0x84803000c800d06282810418800142c0c0058603401c0703841c0e0b003800401c007411402d412060607680f520362007031450440d01003240503601501c1540210350103041280039940402072590031250300121300901920544d80c48009040d0303a082d08008052291140341064a00440d0b60710030f4600945020b03001d440968620f4039101c00d0781c0d80d8480000080d20907460004042100b522501014859103009409541051010455034103403e400c405015403500303800d0188641c0008620b4220b805034140542c940554200040080c003581c2e4600d100355000100300300c03540c06113a500f8010382e5645004918400040c0b4140000800343e06070090200c0d1170a00814490b103400300d140000021186003000f40c1c6a1034906402070f00c03000701d04843c0d20707a1010030140007040820318002411010701c0d0042c4002c501e4101c00d01d41d1800201006801e070210400411078070346003034105440304903c040070140d030703000c1e4411240000e502c1003804602046c450031000700d103441c090140350112242c1a61540c2140ca440c0c840f21 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327376879 1250 327375629 327375637
    0x9050d14030a11090d0f210f080a02220510050f0406050325032a050a0c060609050106080f0c180f031e0c0909010c050f0a0210051302030c0102070614 66
    0x409404024002521300ba55012940401d07540b1428100c54108420301e49008801e5001e402e0190062102d618074469a0784585907403042c40291901c182c281d1034a0309803030300902c560703141c0070450524844821340101c3c0f200300c803404842041e1011000440f506104964034068480d48044298003044200811442040030319001a0b000c3d0804000503004c2003245c00b608200044180440d072242440700c110a85000c01d0f020345002c088445481511000340104680700340d40c0d0380800d1001004641c01404030a500603001341800d0b9104000759612041c0c0608000c0044804200c41d00340400001c1000ac0098141c0c0c02c0308280c8100703000800745010030480946802d0b0812501482280211031004076000c039040000c141d040c010b04106000e200901c401198000c0c07036404140e041039000e101e01a030002c21144e850b03218289080c3c1380c480380c00c012030500c1800303a040240c850070f00c010b0095103006010600032a5208504031990074007018016030701c40d000e91142d007000ca160315850405441e1020014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327378129 1250 327376879 327376901
    0xa050d0c350f06151309051e0601080c0307031a030609010e060703020c0706050306010c0b01240203190509031f020307030605030c180a0902030a0503070519121416050109050d14030a 80
    0x1202010f0380314448007040b07440c1203e110788c1007084031903058a100d2500380100d40003c400e1814250a140c024020880346c0b002030520030030103503549003108106045400140314540700400f654814108289054040d0001001001440c0100000309031076500900c2122000c030401c0d0080d01c051403030a5800e448030f400080c9480c2c14040340034000c82c005009411014040d00007c4040e00070400e00c50102e1100e0349a10f090307803080d584200700552007602d42019025174101c01b417405942e50380759080402d082038154a1500c84918031002082d4807001d0980186103d00c1040d90100402135849003019a2600c40ca496240c01840c0184d4600c6e00c5689002d5261380015152008250002540e001c03a1614000a00a0360503400c00b040c00ba00300702007880343c40310040450144180e500019180c2e00e03a445e51201c00413013031017541d0380014402801101541c0503a86008000310b804203007420014043c041c00f03541202c640c06400214128103005010f041d14052004c0005030850340d035086441c004000075010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327379379 1250 327378129 327378157
    0x6091c050d0b030a031e050903030403150b030a05010b010f0305040b0a05100b0c06040209060409240f090803270d030b0a0b031305060c0a050d0c350f0615 68
    0xc0740c90b42e01c040181c080a50700c6542c44840008032a00307034908641e8030040080030401c04100d201880e03030700001510140c0e90445912000545074052000041c6582c00c45140c040c0940c99101083c80410b6002901d2010280c803822035011034214108d00b108c0089400803d00c8000070042101217400b5440151321210b01c0e00e4485e43e480e00d40648861581119081403550f0380301d00108011070504003d0950008020750b018448520199520102d002d2025880f10f0a0503c010001c1c014008035001405a102000c03420050220a418100141d9104441302c0d40c00c00d1940d241d01c0844081e0700c800030306d16450f05001e85420705032000102c2c00f0340601e080f0290f11050b0350801041980c1c010f030085000700c01400181c3d501d520585060790070320500900c01d00c0361403428040804869084001c8500b102c68080f00001c1c0d41031103090940d81da60800c0c0104582c1200200b101c0a090a01c000c01841d940901c06411781c03694a90011640d01c1c0380481e407458028a4400500300b4401e0b0500141c5100100038103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327380629 1250 327379379 327379391
    0x1052e02120408010b030c0d111e0907111608060c0f1b0105040507060c0b0103290405061e100603050702030c0a0c0311040228020f030705030c06091c050d 68
    0x2000708080e40050704460700742c1c2d542c0c10b21491240303001c1203034542c4d1f00000d6425280c6140c0c50b807100f48843c1400300c00c15006404401104c90f03403400c564200b100304c0ba00103020014609103204000e00c442e5102e0810543d51040b003040980e09805105420300310748060300200055075030702003c01c03c06d800203070949407414003d01a44100500705200b80c1c88000c0e2000c0002076510f40703800c00d28030303040031984224280003147c04440003280c0328030314031810341e81c02210369498a0b1030503102500d03c820200c030350162803160030188001c100780810720a01415842e1910400343c0c908044600c000c19083e03528000c03c1072487c00c10010940607400c420307400680d42c0180c0c1c1c10310b0005001c3d035041c070f01410300071118051070700003c0c410010203c07140407201100741ca046003400700c2c824008200e015519400040f0380521907016210310720802c041100100080c0c01d5944030748191038400d03940d4102c80300f007020030702400340013031090700c00010100b00d4803124000d1101c1d414003c1005031800c1d031001c00d50750600794684e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327381879 1250 327380629 327380653
    0x50112021c0e16030c050f060c0123010b0408060f0a06150e041a0904140f011401080f03030c07030e03150c07110a080c0405060402070b040f060501052e02 68
    0x4400101c91041d40340e010440300c900ca040e183c105000c0080703d009900f00c2c01c0c828408194075a078050241c038021b581ca0f91503100c1c05000280781c1e014110301c5800325800c00b039116040c8512104a54216039001c801716480c0c0e44c8900703050f00180194081d101c00d1341d009400040c071105031a1003441d0815404400040c089131900039040c8900d030b0300350005000c2624100c20b41e103030341071520800080d00003600c0020288120200007806e507400c0a00040e007442840b006120608000f44801c9507400d0003980200b1644000001150f84003209100d001c02d28010804c0c00d400c0740c44088112440703144d250840603d8041d0550b0140c074441640380c00c1641500c2252550540c003c40c0110541c05925418200c0351601c15915144404000038074586001c0c4102e001e040100ca02c0014001000160498002c1055565040498028000d400300038129140600c24132081c0041e240c014000300d8010401448240e80f10300030302806622184859000050f0182880301e01c039071841d441c04c1d400400380305482c0d2002142c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327383129 1250 327381879 327381907
    0x40b12030a0f05031302010507030210020307020a020f09010627030611181f03020705010b060a11060709060c12210222030f03050c030c070b040e011e05011202 70
    0x6908169456000240c08054190410350055a04845203481072951500c603841401180d02c01d1402814020041400c004250090055500d2014185400c41d200d01e4030701c1c0001c0d80d80d4036076030081e80100d0902103222240e040448000e4141c0b101d980b00c0c09102a5054000c0c40f52140310f42031580b000f070340e881000c030002d02c0394007031085ca950b070600005407200d68038402c4100404000a00c1e51142d4400c0b202120808205c1001003803030b20080c1401a12003019007009400342070140540d55000400080400c0e40c076800c0320907083e80b02c0a010403200582d0b18200b003902c0c518014020b00300891152204000001c500100c0300482460503d4a102000c140a41c920280359602c400350458580200711034015003540d50000c080918482c0e41200558616101c02a00940e40000038003040400501d03c2d0044c00e003002101c03410f0482008544245956980541c41c2e50000c1c06201c14201019000092075040207503181c00010074000142c00c00751a04c0700549449814005001110360240070310a50035080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327384379 1250 327383129 327383149
    0x1090806040b18280201080609150105090604052806080f0c07030c0b070c050c060f1c090c030b0a110a120b031608010204140108090601060c050304090c021b0a0b0f0306040b 76
    0x81d440300884d9281840050440e0800030305807800b4903050030400040011050002c103502c0c50030308065545100741030102d8a00d00c03840e049030b50000b5a0009003007241920310355981c80700f5030b45210703041103603120407044400410603510f040d0203052070030104601c403000000600c4014442e08241c44100b0a40d581c194440c3e20484003c000300307000303001c00c8041c08000c5c050304d035401c80102c41e0b991408404685100c0503000f854004200d001245c8041030000041e54401403038980c100020610040c0c0c0d0f0310f084400c98008a540020349030406c40d030803044807420340c203a0302d0442e16512004100200420744400400d00350700344c640c2c1481114818540c0c06045d07420140035002d40c01c009039840707050411081d0f10500c400e100a040000c004104841818040381c0103040d1152071400c2401c00402e8140b1301c3c40c40c040c94005025007490080240c3d1010b40001c0c01608014410055428400d0030301c0030403050f80b203648500f185014040060010340300c0040d004640c4050020700c0000e4105d490300214002c0d0762 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327385629 1250 327384379 327384433
    0xa0317040f080d090501030c1704020d0b04050609010c1803061e1805070815041725060b010809030301170f030f13090605030c0111010212041101090806040b18 70
    0x1200d51954800c1d80d102c0304c8500a49000e0a0074402c07605d212400a041c0828140d8803007000782e031680420210342d91000201c5404d90810480c2425041c5401d011341c9448099894040c2580f8040420203054021080c0c3c6200300040e503412a0414556120b401c007500c50400f00c0d540c96619040e54000e0f10f40c242c270036102c10105150000103c0940f5180c080c1c41e200c1135070003408156004610740310b08a50403000b1240e00c1684018050301d500705203022211280209224032204000c641d85000041c49050180c031101c0d80120010310007958118019520b8190649260055400070801400402454a92035a0004100b1304644c42c0e04050404182140c000d42c00c01c048860001402c0b150729034000003694050546a0400c1000c60b161600081da2001c0096000c0d0500846865000d0508001c2d0b058500b0081813098401c0300d8642450079150314071810010320b020460304507001c2100540083d45600c20759000000d0082c41d04d55001d1201d41500c0e1030300c00304842c419040d00c0c0043c014420b03d0242030127 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327386879 1250 327385629 327385633
    0xf0c0801050a090b0a03120207090239280503071b0602030408070306090305041206050a0f0209010e210a0c0e0618060f01050408070308031605090a0317040f08 70
    0x541007808000188165a010040860500c0d090350400e80c0d40d808010b0480340c3c0080080906d10004000ba0308191140e8400d0141a00c081905803c880301c21403142021100002c5407200740404940e41966819105110a0968080d0500c0411403807036403110750302d80c080009000001d00b841d5480901c3c540c4040d01c120341ca070455840c8003098949041800d00030309030b2800074504160a0601103507139910b841c80701a007242d407104070140906000300100c40180c60066401c00e4148660b0a100c1d001d0801696034140e0140741a04c0c2900100d550b10940b920240144e444508540c80b0008000d669940c58405074483d254042024207108020060011088e2003140b17145881c628200c20000c081c90000d280c42c1c00303240d80001c1900041c0c03001710744603072248084035548070741d2201c140101d80600458204a2041c03091b40030202c14406140d003e0751064002d140c0040300000174800032285070061101c0135400200c10030782407000821a120500002050340c0010382803a0b5031310b000c0040c0c85610f9000146075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327388129 1250 327386879 327386881
    0x9040e0c03011401030b04080d0b04020403081305030c01140d0605191e030308010306240902070506060f090f1306151707080d030e01060308070c2102031c030f0c08 72
    0x30341800c2c021074244802c182c900c1d00c41076240d07480d080d0424100410041c41c0080024207003148480660000d642d5000203003045441e90346918016109900159410100002941c0001503034507001070306069482043e910071703a809038860508403007500046404c042e120f4071031002142c50344034680c2c0c40c060405084102e9a10030b00d0185509042d052400445c0c011456014043c408280c00045490440e6486440050395504450348900c81c04c0c2c00c1d59420121413041d000c0024100c4440c1c010b003601c1805081680d07d2900c070340c5c08101c0380d44581c0007290342005840c07002031484041d17103d15035885102c0651583c07102e00c0903910442100c04200750411f2010b880d030710034031560241e5140480070955040c000e042e0b0a0600c0562942c038001c2c942800201600d50756041000c110070341250b40159401801e19864100910300401c14801c64025a401c42c0e00c5411549900040c15002c815115000303000740c0001b00c885940d031040503001440c481306040d218183c3c60401c0356248200b041c0121039a1b600801e03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327389379 1250 327388129 327388153
    0x513300f110a0f0c080a02010c020105070615080601080d180303081e0a060e0601021b0f0102030d021801030c05040608010608041a0907151713060e03030a05010302130c020c0f040209040e 82
    0x100e13140725000b603403443d4421401200140d1f0440c690040064090a099440e0000c1c1e01e440809409050890306002408941c0051400400244a41695211402d4504215034650101d44801d6641c00414101c08a101c0410220303004660454100403452500014840107021030306a114045c8c4016881994a640c1080109603030b80e03c0c41c2d00003400b40701400c01d9030540c1100da44c0341d84441c0d109500ca01401d4020810b03d038001c004071101d04828020a54440c804403032509803200d074165805010904024a44004500c00d60496068440e01e4841403100d90030b20f503040300c440c2002442101c540c071080f21082086a0f06040750340c481c0404400500000b4188080d00c220092403e8508061054003905070154130030a40c40e9941c0300b900d440076601300740301500b0184003030604104042540d020000900101c0d0001780c200700c4c1a2130003a12209902c0c621a000d0200300d42200114000681080708928418640b032030301d41c000d9400003403015007032100000001d01100d002c5410410b45510090107504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327390629 1250 327389379 327389393
    0x604152c030601140f040c03020409150504240b0c100e030310091802012a031139040902030106080d090b091005030702010603060513300f110a0f 64
    0x805400c60380c031090810350740134010601c459240c0c00034511950712441040d01c150f201e681600c0041410380014021016058003c95201043d405514001d41c1000c5c47c9813a02410305002d041e510003040d1074ad003035076460506960751ba90440210300c500703401b804414149403513040c01600b6240c01c801028581e24282149503005240e010707480701200500701800300fa41c0c0070703284416101310381e020309200e0b1903085070300310b0300400e02c10309040c40c0824108020000c0c1403503403141c1031140858900c4110743d807901d08281c02031640e83c080c18803800c0c9440090300c2c240c254070f145491420032810190000c03070080c6581d4002402c0d0b550319040100340e81d00030032815a089034090200001001450f40c540d14107111240032030244d1005641135418044000003154602e4400d502076002990032800030001410724800d0b400280c00c03100000d4030140240b200003007035055000a06500854000100c803070030306036024152000d01030352074040700344850305844120b4180144084510a842102580310116051400700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327391879 1250 327390629 327390631
    0x3030703020409050a1e360210050c06071b0203010c02030c010b06070c0b07030c050703030302030403032702310b0103140c04050405040f140f010501050f0604152c0306 74
    0x4094541443c2d020780115503208641140e0441b16000440c081ca915080d4002076040e181211664500081140d49141210303505048001e1085819858402e10f00404070f409000700b00341c140080e0060404691007d0080f01c40007104c024101d01031040141540010b42107500b840c00b50030240c0c200280400c00340c14217201e891728030002200c41900f44691511a6004011036000306546500000740d0381c1c040c0b5000b0702e0388210f0140e000003115151601d0f0724008000e90819039080300420300f0058070003202122456511841d403414001e280c0405566002c010704101c1142a10341458400000100c00044100302c0f1150450280310101d2810312400006007158510750032003103803e110105000c8000260401c40e01142d4003102c003c6059255401c3c4000c50145045d0014980001414066802c4d10701040d0300b412091903030300030002d40c2ea80c0d006100b8460580200240c0c00f0720200000d0007030125100075100240c0081c904120b44001d42813a003400714041000c040c000c405081c0c450f070542d2408102107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327393129 1250 327391879 327391891
    0x1051203040605031803040b16020405010e060306060d0312020d060e06010c051c02010624031a1c05030c1e0706091820040f0305011b08071b02030303070302040905 72
    0x1103141c01e18140c001031540c00003801c210100030319540303035806640003001a0b8000d04100c0e88010380c1c030040412030f60b0301c0c1c10f1b10000881c06541484000070b40840400d00f00c45c03145030040d0150440342c1d1518100450144502d82c100d01780080b07400100c3e95202c03544040c0444c000d805030300080050511102588501006100701d0403c0400040034001030004103261400c070040050400c5903040e4a03409901400d80e03030704014609423070740b0361103c80003042c9038101400c0b1000b52030801110f0b031450001e42d65200f503040c1490708031820100b07240c000401d910711039415502441c10703641000f0043d81203074108000b82c071a12020250305107202407008401c1c00440300401d042c0c04d00541aa01c1c0500000b400f04c038901c643c0f06000e55641c020b202800640780c0a401031000020040e549039240e100f01c05480010b0301003917071107610b490304510641c0030144007501c07241441d0f203a921080c2d440c0c490444061012075a04071044650249440041c0c808002550041c01251009038580e0308204000b0100c078801000c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327394379 1250 327393129 327393133
    0x902121303050406081902030c03010519030201050910050c0d03020c060a091101050904020c161502010203061c1505010305100f23071b05030a030606090605221d010512 74
    0x140800690002c044a044520509041d5081d5541100e0b0b143d124030b81c0544c1302015400002005580704a8200660590f00110b40b1904040898505501c6281c60790000071b000c6a002c00c000e02461820703200010b03d00c00d4514081d450030654a101a05040a2030740d004042034000c40c1d07040400c0b0050240340d6002800e4003042210b45150b450304403e04550300007642c14410700040c00409622240c040710040c405040443e82030202044800a01401c60711a14008400140080203114810f0080b240148001800d4100c0c5803444202d4407900d010032801201c01108290440c00341d140c450140074000c41c010b070060107a5001d00d0500b84240d9030b0300e18500500620b003810001c544034400e0f0a4540421260b084035080d0754405400380d5000f424503eaa1814250401d6250100f040010050040b806d03079036814031005070b9071042501e50710401c3c05032602148091051800560b1001c140002611005508103a02c0c0e07503401d121480c01c3c0030320110400889440d00103000908110640100701d44d80800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327395629 1250 327394379 327394411
    0x50c0111060402040506130219020610034d01031103010608070e132f250507030c0e06030d08091b0a0f08060702161401030506030115090212 62
    0x258075161100140028841c0e070707803140800c080f03449000d64090400d03d0840119030744c1b41182480240394801d54480300061060b080059202d0403101c0e0701d6070403a40d10158400030344211000c69800c0b404400900302159036907885400c1c00d60401803c005503064059086144a075410713000400b954202d610356050006c041004001596000410035440b40c07140c40e0400074020914002000340e07503804003003255179041002946003188a00d42560003811581d003101c8c000303101c10700a5541e0b4040c21202c2034890400c8642030300d0b0950070b0030328010610721500c1036070b522503141d80c0c03500402ea80e80e0b008291608141c20400000e403c081044180c1d141850802040c1b41c07405000c51580e41d00800c0c51100030304448210982c80342c40d800d085002900341540701104054844280d90303034030082103480b075005204100340058801e009030341000a40d00e0b024154540704a28000642c042d203005400d1640641d6148603e4001200d11740142c03001e0103a5500240ea514520009000914000b0f080301c0c082c258114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327396879 1250 327395629 327395657
    0xc0c06160e010306060f0f0e060c070504051509160903051203150f0312070204020c060c1306080105030c012607030c1202211909030e040e1c03020f040b1303050c01 72
    0x301e040311546c0c0180360910811018040481d1011001c001c0300e03030000004588608003800214a92040d240d050750100841d540325000c0440012020b0701083d000741603000800e488000f015641c1400c0c0d80d0740d040800f18507540759241d80c503204401c1d6150000c900c0100a01c80a09505c0040000141003103400c2d40311a00c084c2c00007501c41284000b583c2d00d414001802c4400c5485540580d00d41e200450103075012482c003d201c1450b1030b40a6006c0c030b040d0014008011444500401415040e80d6015000b414214110001940c43c00849480004400000c0114028150303854140303c0c8910f2041d600822884102e0300c0c081c054405d11224540800c1c01408131314060000104460f1100c5170242503005691960a01c00c0020b854548095103082c0c00c20090500b4140c000b0301c86c41100500ba6810444006090182c41d20703441d140c90114030611200f40c00c0c14525209402402d000c205003411549884c1d920080c800d800d40c01000d40c0b00d42003c81440410034000305000c804c502e141d080c01c0c50040d0710120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327398129 1250 327396879 327396887
    0xe0601080a020c07061112070f1707051b1c1a10050607061a030601030b040203060c040518040303060518090d140406050a0207050604090518240c0c06160e01030606 72
    0x54000c00c02001150786c1b4124100400b00100211020f071922881c3e80e461030340c20980300201d603005c000d944035000d071130710204440d1b058004c4450140d0040050310324400c07800c07005031184a924941c258407802108000000f2188094102c407494807841101c050128010140c040324140148000c3c00d120001104001c08c0e254502100c00c0b0b44c0e440803002079400e8421105401400d81c201d000c03030301885240000300400800949442c020ba000701c00715a103680c0d4024600c08540b04601400340c022880d4080030117134144404000c0d420501c20706012500c161124080343c0c0742090ac0c2040d5007840910810321080c448140400044540d281c07034001c001000e00c03c01456907128502c110420044000b5499040034400d01a010180100038001d80d030326551140c0603009800181c4900008018a4500380b007036044c00694403454941034032a0316000044444001c40502004152001d01d0900704074050b800c0711306007c260711030030690040c807503020500700c0c0c02095002e8200d00070703047c0b518150060100c1030700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327399379 1250 327398129 327398143
    0xd0b03070614070c030b09063709061116030818190302070b03010b0a110601050a120302010e1203100b0703120b040902100e012604060902030f070e0601080a020c 71
    0x8002c2e21140d03034043c00c2ca01a52500c01c00c1d84040c200100401c107000111401091090003000104800a0303240309505030301c1400403402c0c4103100d145544021010380c130119a0801d1130054050100025a1101460880c0f615404101c005040d1900b9401e440c0400d40c06c074080607000b080c1a02801007003c02c80a600e96150500d00c1c000500350f40342d24030a0101032081024a0242250034240c54070395a45081c0c04c4d1040d004540d007440410f880304c151101c400000282541200d20007480611307440d2610b0500161100007850540865490360000310f2400420090020010030035188240c0c0c0b403805940214102d210f6070801c401c4c140341040308101217a4004a0100030101e0140001082e9a00d800003c4c000e0011900003500070141d0250306090903000710f04e1054500081c1c0b81c9461030424290300b01c03840000035501e0390015420343d000c80c1c0402c0c41640002040e0344060211340412088906d0186401c0990340030042e001051001c011955a0102540b500448501c006504003206040411303120344d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327400629 1250 327399379 327399407
    0x50c091f0e040f06021308070f0314150105100909050f01030606050109061d180a090b0106020a0507120503070b0903040f0603090f0b06130213050910081c140309030d0b030706 77
    0x45c0218012642004101861000300554000c54082ca595072800000088461001303450001c500440104483e40c0801c250780b07406c01201100c2c005a00b403400700584c25103014240e0341040204070300460044028455140561780260318461250f1440c507240c010303685150040c904000e02400100403190308a1340030005011004042c3d02c240da4080d000c1000c80700304107400c114040085041c001d03403803503540c00041014080c41411025a803038004c160b9498070304003001417641d4042c000c208600c08900003040f40c081e200d0340a4a2a100807a100c00000000940703c51000d81c00c0000d003001656000301300580140a1406c0500020900e516003103140c1214941c050302c07203112440010f60039507800348100e01080d08401e0440d1118951040198521000e010740c6001c0d200340c0c000710300342514080701c11040354001c40c002c03c0c420b0049070006000c01142480c61090100380780d440c3e00c460700301c2c401540c882d102581c000c544401c851202c0d0741c1600d000c0900d06029820400b0b0a00c00c0c15845801c04c440c1507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327401879 1250 327400629 327400631
    0x60f2304020c1002160f03080603010f060b09130f05041b050d0305180a08010e0f070f030b010b0a020102091003020306030c010908030a0e0d05030403050d02060702030c19050c091f0e040f06 83
    0x3400320b490700c002c06540c0c4400141120006c0811130b080507040503040d03001700d41c203030000c01c442524890710310100d0720140140c01810109100c1000c8615000d82c8143d05500903000c041381c2050020044000d403001564200c90b6039081c3d030761084000c086101030000500c0110b0310454801865100642a80720b124210800040e80355034512060302c403516403e0090140c1002000251407616081d5114180b035050000c0b50f000300180011912146c03082c0d2004e481d040071030b0b03401c0f0382d02c0c0450301d5066034020690402955000c3c8040004c59a5070408015180d990303440c0980c1d80d24084042508002241d02d405051103031102d801e00481c031b400025100c00400c03508040c10030511440c00a8245901c1030070080c00761000080200401001040e1140590003640031940c0903141c5000c2603171280101c5070410321540c400880036040342103590030f803070440d40a2420360300004522004284840d000311882504030003415030307160441c00b2175942d031001442c0c40381c00c1100d503040940c0c60380840f0021000280901e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327403129 1250 327401879 327401887
    0x27060105090d05100b040f140f061503090d030e0d020c0f0a050a030602040f06020d0c03030902011e17010b0702011b030e0907020601030b06040b0904021201060f2304020c1002 77
    0x5519004080c80c0101c3d00142264800d60780141c0c803402400003000d0340360040c3c0c2400c0d0304581e25041801407900e0004803120b141c040381d403010324039006860300414180d40014280f41341c1b40c83c5440d503401540a0007078030028141103606000007800b62901d0f92502d030321560008158002c07441d804908a00c05501c1254911151684600001d8003c00c0c07a070040c03507018000c2d80c03000081045075402070049031018269284003a0b5a808181e86507229102c0820208031644145e1002a1185d800203048a105040c1100712945d00340007200e003031442c0f02a9101007010301010708103240c2024040c90040170364810aa280441c40d9000a1031108042108203950010f85011001c06020705e450171940c40c809040c1c00380a281c00900250364040a00c800e0341d0035508100859840d00b49801556044040a441c0181035103c035801d002d0591f803c0c900c000c0c0c05550b41c00001c9980090303820060300800b130320f181124440711802410380302c036102184d00b00c1c0b180d80b040200c5c0c4a0076001140c8540c07443e091450050712 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327404379 1250 327403129 327403147
    0xc0d0209130b1011030a0f02100f0e1501030b0411011b0605040303110a051b0109060e07091415091315090209090708070513020c0d03020d0506030c36040b0627060105 73
    0xd030080f079524040105091132b9180e050b800c044c0c1d02c503170030500c000e00071108011000f887c6421401000e00002e4102045000002c006c01c141e4142c06880f0313241854111508040e49988070b6000c051005c04554a580351014442410741c140500c88095641d02481880c21010410150040c422a06019103041000f20003c0b8510720030751007068542d8102d0f0060005840e8050110340756610380c0601c019441ca06032400c1a42154034034451300c40c0c280f0754111205504410104149440010a05081c0644040000001406000c6020f81d107940002021032800407500c10880b0996000303040c00f00c00d83c01250200144a0000b803840116801980c01003940c4403011550b1009e8425008900d14a1003030a07031860380182d165000385401d00c4644003c01c62078175140101a140c3e038030b00b0001da82c4800047c1207082c0c0107080018032041e8000107005038088122819070700c4003200045506a40c000794000401c111410300041e41070010415919402c0307800e601c40413020041c3c6c0090507082c1001008901400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327405629 1250 327404379 327404383
    0x2702010201060b0c010203071202040f050405042303180303030c040504050408121608060105090901060810320a080607082e05100f02060c0d0209130b1011030a0f02 72
    0xa403101c100d00650320518000058080d52048d100140012120b80b503080304480d4504c20740d01510103680070310705414035003010407000d031001a1098420b1282030401002c44402c1514841203109910059522610b808600080004802d9810741c0603400402c1000401446841183c0540b4070448002450703880b02d05040485024070900310040d6050a0284200c0c201d012a61000451090352050b04990381c40d00110341303a000c0d84030700c150054010001401018003691644c0c1d80850014a4409600d99501d80d03090007802900401010040000c0c0030a041400a0403085211800742d4141d0000791420781411340c0c800000b0324a00403c0b0580003c298840000e6003e450914000c00e1400144181900d02003485030891045034402c1d511907240c00304150140c2c0443c600618103801900d2103648800b900d807070795805003505411f003503404c00c032400496989205001114070081e10010340c1c0b100c0c40d024040c240c007178400c0140a001c6544c200c541e100b9400011942c1c0b1507845e01d0105502e0440c0b103000c1c0c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327406879 1250 327405629 327405641
    0x30308040b0a09170c12040e04060b030c06130e060909070902030703090c060f020c010212040905090a020d082113120905120d1403070e0607080c0d0c050f012702010201 74
    0x20710082130298044c42e07851020f0081c0100c8191103080e92556190781c0d02940c483d00c110301c1865021800758001401103040c640c0714841c9103801030161448580080c00240f650340c804840030840030036800080c041460513a009682c4154141d44400442c10045d40007a41d800e481e1090748200d036000000548445d1180d0401e0034074584c048003500489440d02d0024015001c3c0900550051140301800e01307003503200182e12041150396103070b104e00e02828200000c024240003003400e50240b190242c030304016152898071120890207200b1440d168228031005024441c03516280e00140143d40d070a00c83d5100000019540f11a4054101103030f50f96400019908000950301c490390282840c406d046401c2d9000c40c4035100500b141d99801c0c41c1c0d880800c40300025001c1528280000360307480a04600328100500140503007806a13201900701071110342c1e00d0f8034001e401140c14001500c8003603500c041060400006c10b0260940c0024040401062181540900002c0920030a100c1030000842564001c0d4402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327408129 1250 327406879 327406883
    0x9090c31050108010e01050727050d0b1f0506041404090606090e0f0303010e060d03020a050102030c0409060b0a12021b0304030605060a060f0903080d0f23010f030308040b0a09 77
    0x441160002456840041c81c0034800d100309035080c03101001541c1c0701171003800d00c16a0726881c1c4000710705030b00e000d01111044072103942e007a8072018000400c10b561240c000520070b901c82c25140840c3c0c45c04800003448001c1310025030101c034840c540d040c000750b41d5000c00d44065502c0240011a6406007a000802801070f903000507040c0c925011303004c60008005d80196055800c08000c80e0b590032950018a643c92009202d0b4142200d002c00108509281500b2103104042c061f104071092800e0603100e56003243c1c01511680203d650014040000d42014040c0d10700412400100030b080144846c0050201c03192105407000569002030709901348541000c01d500c44c0010b1004498440381c40c2e29106c0d000700802d4400c544503402580f00094035500c41c402d030f0076403281182d4401c081c0b1840c540c1c4a42c0160410300300e504840781c1341e68070000c031042c0920480700740d5031580c0c00480a0b44001207945081c0841a085918070024500c010700200b070b000414079401c01d602c00d080b22455a240b81c4910000e080202c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327409379 1250 327408129 327408199
    0x106060c0302100228030f110405220e030a020703020109090509060a11040f0603024902090d0f21090303050d14011e09050f1821040801060509090c 65
    0x10105c2d029a050384404229660090b081241204001001e000c0c0d0160744501e69000d01c800b5100c00a95001c4c07000001c040d280b00802080c03548003001c00500f076400c414202e0006902118041007550303030003400e03a03000340700c0c2460810590604107959503c88030000d0941030b210351549007410032006e0207000c407030007498600c1c010f00c2c0c03298503030034018041d5022000c540e00b0180300309068205003c1402c01076002c50020360280c030003e1003024120294929487d500850130f40d0038800000c682c0c8504000b042d4041c07088400000e105401d2502c03030b990342425804001c3e8041d41c5442c90b060b42da000400c0394281c0342c050610075160340c5040031182c003912415441c9892021178000024040c2070100d0806c0d5030380e01c00c042860a6603110b00120044a80c200d8420803030301005004201c822044441d2500c41030903a0341998440c1030200e10848990129102001058030001010000003400b8402d2401421003210620100e00b03109213541e9440120303030172440c42072080602400b00e00078180e21441608002180e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327410629 1250 327409379 327409447
    0x803040f110a1e0807080c0d0c03021806191a07020d050318150f18120601080d030e0c030a06150e010311010f03051e1005060c010c020106060c03021002 67
    0x10741d034040f41d840d6002e1480b240c8411401207280d0300c003c5400c1045d11106070042142c01c1d8008200010403021840540751102e4808000c00580c403082c00c0e4144100b00844590035a00f03000c400d10205480010940d660130340b0b07e600c203010070b000b220640301c0f4030f6112904590303c48610340001074004080440041c0603120000b600b49040c0040810140003480c111003000c20010050286c51991280000c85d002d5010104115241c0ea10100000c900c0d041e400350080c030324a0606d08490345003500c2a00a03950aa00518420403241ea15000703042d40c212000000e4042c3d4840c3c0e001182d5a58a0a05c00800558841c0b40c3c0e944c840325000c0030400200744403a851441941e59080c11a8400070700c560150002d04080309104c03006029004003400380b030b200c3c0c20601040c218140c401182400c007415920341d0000e81c0400058a9032104050000f035607035107000286003152124083d08560007039001c041440504d200c0071b40803d40201d6100e00c25942580c0150342c400c0303101451181c00385161403000e221402c80c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327411879 1250 327410629 327410639
    0x503070e03060906150904030f05030a0608010e01050117030a080411040e060c0a02011b02100b0f06120105040e0c01080c0309011d0303040303060509010b0d090510021c0c0305040803040f110a 84
    0xc18078015403110174140c14a15030305c001c0c400310510440700940800c00d1000100b80c40c6102d03200845e0f000583c0c0d003001664581b0b8002003421344150001b00d19482e910b80c00103111010703030040398140e91451f4400841c42e040300f65001412004004202030170740e8140e00100c2c1400e868a0304940158010314059070003e01c0d25021104064025981c2c4c40c0040d03180010004074124076042a81600009800030841460303083c06003c0030303103400900240c008500500500550302c1d2100548807039010204448500e40c100800d000458040c9009003c10b580044801032880e42c1180c50160040c8a2044260784c0307076541d05600e4050485c02c50384c0c80c2c1410650a01250300718001c03000c0c6004520075036060101d00d6591f4204829a4020b000301c007000c01c82000007550580044d40b10000680c8690107507442e0b1204024100308136000740380b9101c07000305040c017800d00920092280c0101080b060074104118203294582e030205010003000103000c02003081c440b000f03010b41d04074405840c0f2001024070780565195 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327413129 1250 327411879 327411883
    0x51008220f0b070503070c0b1312030606020f0601050a18020903070b071401050702030f0c0c1c0308070801031a06060702040510050a050a0509070e0a030c08010603032a02010503070e030609 83
    0x80005890b0030a600c0d0219200c00d2043d82124003504840c3e07509020365803c3c0e118030484003805064040c15403d078a250000281e003805c0e0895684900747c900151161070201c02900303007075200101341e4868000d100140242d0380c4240004041e0341e54940441d4400c600f0b01c0143c402441565034059140c480c0706c04c0046c0d002046001058a1072056072090171554050001c035082c4c8a003038443e01d02581080c00240c1c9222209000b81c4840078200007101e801d04500c0000c6a003544240d25083c81890380b0b006040107040d0000301141e0000d2041c50544925031654580d03680c44040c50218069010152020406030b81e40c58081d50011074000f04104840e08207481a4030348812503203d15800317890701c048000342c41c2c58542991421a88040d1a500e4542c2e64000100c40080741c1140c003591064481d000800416060801600903080c4c00300000358407801d500300605650f00c4440000d1111003007a0005078840c80200d00550810740c20b0a000d5200c2e112008140c034142920344c0100d4262198808000c0a4000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327414379 1250 327413129 327413153
    0x50705150618010e07031a01020a11010203210a060b030106050a0e0103020c10150504020c0303060d0303150807180209180c0f070b0604060605070b011418040305030a05060102030405100822 83
    0x45c0e42c6007000360101c1445807645032010758202a0150b08000b04810118401015000d509074052040d6440c0040390007296200e20460070700c1c180d9840c291010015201d90600c1204081c0c01100c442e1800c56146c590000c100b03105032440c0108100c800c0000c61502d034002e40581e40300d021005c00340c0300c101c100301d845003009008c8050300260618041c000051303141068403c03a180100b0b05009035140d641c4038070a0042e0346244c00d000710101540e40790015981c24900a00c44050090703c4081c00a440c6402c410480044c03a42c1d54421483d4410410b081d0a55140209121a0001e88400000360755403586400c09070b014003845021040000544142085140c080c0184207002c103d80400c040b527201c480840c1ca038020940014101a484030041c80205c041200c090f80b040002003003001d41000c480c5802800c9407040d0b0741100451001b02c00d0000c02602c9004107a0301020a10055090500c0d00380000c030900c114080181c1070003844e602083c648201005481c170f411503038041c4506803940501d00000e004034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327415629 1250 327414379 327414391
    0x1e0b16020d08010b0906030c0c030301080a0b011e0e09070509150a0f050108130501091703070806010c0213021c02130302010f0804172a1606050705150618010e 70
    0x1607801810525000d01c0300a41030f0b0f29021225420070303001609005030f5900c05080710070041801d1000901941c8100015800303840700c0c1c0c5c00390900c1e244500e4003003525081030b0401c01404004e20000d021420522030303200d080391100c01442070a40c584030340c1d00d81400b100350401034100114004000ca0b030300c0304260000da051803c0e130b0301c04506ca5079209080e40c0c2c14444d004036070015001202003500c404200c02130120203801603000154811540d610318184150070f000d000c50740007000c008c0102c09504406a50f6029600303080c04e00310781465038005584420300381d403804611980401d8070802800d103a411900e00e80f4400310115030341c1842440003d100701c02407000724000751104005c0706032280b0402420f4019580b00e0a410b410070b14485c420601500200030454403c0800c1c488600e0307910216015255a001403c041d001c0c6400112030703c4102005038021b84240081000090001030001540c00490701212a40000039101d00e000142c10251900b0f0b0030b0f40b100025070021035210340081c501400b41e6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327416879 1250 327415629 327415633
    0xf1404030513060e0a03060b13060e0a0e0c012a171819060c0f0204021909090903080f0405070e07020c040f11070209040c120c1401030603020d1e0b1602 67
    0xc3da9442c0071200e1030000304215410000710b5104000080070340c2c0100342e0100c401410502044801c4500f0300803640035070320500103840c004003804440c140900c41c00f2143c90011014110340d120354400a0440c402130798880c1d28100150000c0405803640280c0603052551000020220145d1102c115640350020710a440c0744504402c1400c4140c40c10141000802e400c5c09030842e0210710300402070742c0c0c80c10700040c160f40d001440d91109005a03194401407c00c1460400380348511706c00743e80c00401030111034214004941c908180d00020a801c110002d038044440c1c800d0303d000d0780e614904241400d187d540148014079a02003800342d960740201d101104558103560410107005002d00780016200b00200700d8020300e8041001314050705100c0e20440d441401420704044440d030385d01c00703152010010300d02514a88030800c414001034030410341c0003c41b03071824a0148001400c50700001d60300c41090300d0040a0421b8070803111045060018031000036900a4003620180c42c020f44200040700c5030303c074010014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327418129 1250 327416879 327416917
    0x5042f30010e0910020703090f030515010b031009110408031b210307030507140c0d030614180703320f010b04060507030e0603130c1a0a030f14040305 66
    0x5104003009a510030443c02d00100609902001c9403402176212140607001c21403c418041a00a85d0705003030740080d0b00c98001002c0c00800341d18800c41070030068111845000041052101c840000b113000b000380c44440000046850b40452084d08900c0f441d40401040d02002c01c541c40e4003400200805020030407101074135075500b000448010901a4200314401341c50b0148049200c4c0d520940c03003036601604d50300708442c00450190402660f0b030070030300030000b46d80e0180c803840002079458040c040c014001407280c070340d03a09048000221032000101c1540729100e08080004c03107940c0310750001c0d649074401045541010091188a4a11915010100c107411100c1c2c4041034202c611014001c6c100c4000701038890910341060340449a540c008c0c0b009030100507407603110308010342d1a04011409640300c25400d00c6400210b2401000c6c4124030f0b07004c50500500e000307100c0900034948046039000700e01c51a0014400b400c07924008010440340f0348034000d182c0c00404010405412100400c900700701c4c40c01e06518 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327419379 1250 327418129 327418139
    0x6090f13060603240501050712030915050702100501180905100203100f0e1306050c040306060e0919050307020603040f060f1406030a0c050d0201052b0605042f3001 72
    0x1044c10644245030001304100404000300e040340244401200051030f0115801c051511039504813000d001c2e80c1c50340c1a550341e00780042c003034040000700e08008003207409014940c9401c650702d1383ca01c8200101000c80d9207401c804030030484203100c0d00c00541141d48045481e8200b40803e42c04125103030186880c81012190041030710701d007119206204200c807403070041100500d03543e21760141c60007522246810700e080c0030200c002203950040d20080e000c0701c40c41141c80e10b450001c3c1c030300d000110f500e55407000b5010503900000c580e01004541c59160142da4960b41c9807035902d0509190403003040044c0541d80340603107038035011a0a4004030703252120003801002c0c9403192010145c5981c0c0703090004202071500c500801007410660b803010b64641c0141803080c01e10500928207500800c05611a42202150851011360703402a4802c9a0103010155000c0111010890b00142c44140690000030f4405074200040c0c0c040d2600001c0740c100d035a4034811900d0b80010f42d00303030b01c20700040a42902107401546c0c0001c41c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327420629 1250 327419379 327419441
    0x3020c220b01050f22080a15060509240307150302030603010c09081b06070b10330813080c03091201050c09011407050109240b06090f13060603 63
    0x304c2d0304680e414140740911038104103024400c1c4414070048034002010000b925101070001000c40d90207041c1081071041900c0020080b07840c0354101c3c1384102804000d000d9009101c00c480c298801240380c0a0002d40d41d83c6000a103401c3c00c0c1d0740000d03c2c80803407003480c000c0315505030040c0d4001c6209900a21801046030fa0549088810f030058049a90189941200d280d0541031404000e4038080c240b0b0780380041603219800e17941822104d1401400c03003110100440b19001e20b0303100b14075081d0b81b143c05011500002c0f5252080311440c1c0c0d1030401c40d1440100d0300b58844031012481080c4c0c0318401c2551400b0b0000e81c60b84a420103d2814070462450540503c0500d041c003e0318880e01198118504d020350301c02c01901c0400c141301000d030a444d414403100700011805d20800100d980501100780142d00c40c2081103112f9207c00540d40c0d0064100170804219441d081305441680108480b0303000e0401c00007020802061002140f10344140c01d00720002076180c3c060340194403415456540704049103041400b41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327421879 1250 327420629 327420637
    0x90603031b02030d0311040512030a08151323040c050a050109081914060a02070b16171b0f13050303030f0402060906040b03071110060806011203020c220b0105 70
    0xa50190006030380712032a45d210754400807074607590400b83c5007015190004200103010350508070210354400580d00c03080d29040f81c0401c3d885642c00c0b00c1c1c0b11403207010390b01184000c0080106900b1075030311840710700700b0158514010b50001841c10298900e0340350608111880c110f207803181c1c50184c030f0303060008203165100d044004244d03a82203000b40061044042c9450050700985001d85101d0b090400c106040300701800524041c1c141c148002d030301c982850811301d0702200302800900084841c007440440b034503080707003841c081007a2501c4040344071340d0390340450080104805503d40321a40e000440c1d21001c2084c10103018500e40c1e00320389080403900c440606503030744400d9894110005c14000018010714040c2d00406290341d016004034141070b90b50100307101070303002510040c004c110417280500d1030440800c00340380134602c141004c3c404185440e10740c980301c48043c040d1010317400c901421941890300030041a111250302809641c01d000c2d0000c2620b01c20359450585440741400c24040401c2503114006403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327423129 1250 327421879 327421883
    0x7150e0109170c07180b19030203070501050720010201020c2506090f090b060d0204141810140613061e08010e160909180b06060c0c060d0b0901090603031b 68
    0x6092040c10081021710340020708001c242540d851380740f006a2510740c1c038000341c00518219450807099003184109030816180307070402410400c0a101400100e045426107404a025048581642200d0032004070301902c10005942c22511804007070001c035540110a4061040c3d4603800f614502e0f449420403103e900c21840303850180d0302100011b11619203294400c6400d1040200028070381010984480140e8004e0fa200340f6a4103044600f40e0007506000c1c4602098a1496800c0011850402c0486030074a186005203d00e0780c500700d86076807082d103601d400c4a10204021070382c01c80721566518000c20f40000220300c10003c3c0c118510a4050a0144000e103050b00c080404e00101d5645240c000a0844000b00081003000056480060650311602c02d104042d2401000d0b9588030b403880c01c000c48202000b901e81c80c00b4a40800051032400c4010030042c440d00310486900d07580e00c050700c107100090310380c40c2d41c11a8406e040310000551040c1030350040e4204ca11a84907210004401c41404030ba4445ca8040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327424379 1250 327423129 327423133
    0x4030c08061e090c180106030e0d0203160204021e040501020f010c1403091606050c07081903030506030f0d0305040303271205160c0617150607150e0109170c 69
    0x600c001d60110b122254085404411103d121a220000455030051850100991842c07500107210465060061030482c03540000102406451003a0003580d0348903018200c80a003021200300030440d5115011160015240c00d08400811030304808415640c0c40741c0300ba9409441103080c4030340a21018003030021000555100d001005035030b4400e0548a51000b086c9140fa0301603031030003c00d002c00f0450b445000d0540391741c03030548600049803031524000840d000b2810640c004030340c01c0400e1001c030b421a00841d9142c0b40116040e1a4100420326100d20070840748c0a40c01800301c0801c0d5a036060b40861320446c041d58091011500d2071031101d0f47e50245480c40542c80200c1d14200c1d002c1041038908a150030b02c60309e004d61908c0745c02501340c1a0074260301411101c4200e181c41c00c000341580a15000c00310350a02c40141210305014071301e0300b610038035840658003407034011400c074040c04900740b105114071a4581042c4820240e02c0480350080004c0703042100c40ea0a0000d01c0c60038110765030140e034a02c1c0303241e0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327425629 1250 327424379 327424411
    0x1210030c05090403050906130f090e03250f050c041109010c0b19060806061801081902031c1707030e0a0f0512130e0a020702060405010c03170c04030c0806 68
    0x600402d0b2200500c00e80602100b0449600c154441c200100310410341c0c10411407a1905210040c4950304465000c164000d04062294404c0d5502004441e1031600c011100549490881408016800ba4000c0544124102e201c50414000701082508200804035410095a181205003490b00e004000316140010b0055038500f000403000c140f0550010381440150041c4200c9030815401c2e81c40540081c0020b40010040c0005ca080160702d40c5145559040d410519604114035107958400a204041d802c03840e2442040075920140004600c210300350781e00200300e501645000d40f000c0c030143c6611861452600c001a40548688a2684407000e100c000d0840c0300059250901c025401d49000d40e41402101c020000301c0001340c2c001c150140c403c103018200107150054000314180014032081006004009003801a03903150100c5007030b940c090800d00c1158422b1b00f000c483d01069001d0702000442e500c414402814802000350048a01c9800c40b66040b540b60206681c42d0f040a98200c0202c0032591 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327426879 1250 327425629 327425639
    0x1509050103020a18080d020618060402090a020d0c0815030c0a050f0a0b07030806010206011409070305041112010605030118020630041b060206041208101a1210030c 72
    0x2400810500c030301c0c1e24048403078000390401300c420f402d0130f5400300555500460514264a4051040607800301e403000307403011405010303444a43c85a900030402071180e000704000800f60400c40e0b05990480c1e5000804000542280f5000f41800034266003444d2554100c188041891a00089203201f490002c4c201c3e50650b407030070301406558001c01e0049540689845c0010411460013000703403d0301c6000f07a4499903039051610019080c68030681002d00a80c5c52103d413248141c03035581e00da80c0c10000c1d030b03c0c00007807955540c00c0100204140040895015001041107035510605400c43c0c800d42c0d030220000c021840449581040391602d90ba402074100300c0038043c089121840c4207280c00c600c503044230b210320054003142c41d44200d038a04450440f10816040e40a0740300150844085002c0d0495000a11b61410540c07a060341d8809000c00c9074040141c2c1c48000b444031884459200001d100c1c06017800b0403182c8004a00c0c41e21381000c50784840b28020600010a4892151940011640c210342c0d6031169900344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327428129 1250 327426879 327426881
    0x80f09010539030a0209040b1504031e0515043f0905100909050601030606020a0209041b03050304150e18090a0f050a03030b060306130e0c040c02030a03061509050103 73
    0x850300c041d03410407110003090782a02e4036030020361042c1c08003500140c0e0344098500f000100d40c480a0700c540200c0705141201018200306044400381e03600a440505c075180e0f142c54440400d032088000401d00c7c050203501f01001603d01380060b000c0e074031818001c030008c4480c030035a9501003c140e03440126061550000d905000040301c2c3c0034140056450000c08494403580030540029403140810700003481142708000134243c5101346a001942460140006498400c0095446a210300081c0c403441d00d40c00440e003080200c9107000808031001200c600036a0350303030420702c4c6c807500301c0d1150054240507419000191803060a01003c1c07940300030009007075095100510618040020000d5500b44600303940140801d0f41c15102804003440741c0010b0107408420b19006083d40c400c0c2071050300520b418024408a0399980401000c1c0f00e821200004010b440064900d1408004848864000b4604103050031180e6000c80200311150468034184203039a43c0329644003201800d20400400580a039074248903544c46 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327429379 1250 327428129 327428191
    0xc11012007020409060e0a03030b03011103041b032003070e040c1211220b030a0b06041e1103010f06080606030c0c030738010509040b0c07060c080f090105 68
    0x41c000080e4004c0c80e030b44200480d20465600001584010000810154140100212414154000d201c254110a10040c081c0409000100002c6114484101c4c07240c001c1c1d800b00080d500075844500991000c480c0000078960608c0140c024060310001050400c08018024010f42d0b01c078100d64034036841d002941d08040a03000d0b00b100c1c41741e019540300c08585d41e07100f0f03845025400c030408640009200c0c030412048441c039000d200e0194002010b0b200200e0070110800b64800c105582c0880d02003440301002c100883d840c003a03400c41500d8841252101105c40c0040c5041c0c0b900720903202425901e40c6000d1300e03038003400c84403694400c008000107450424000080d00201c0010700460313081c0001c40e07031a8900010740710fa501001d2130ba80c140c500098030001301a01c0743d03040c06c001313507000d80c0d4101b601142d41500001d0001d00052412070100710058081000c8403201a00001d04010383d4110b504004e1000380300b581c0b4600100041404180c80c60303418440c0798010b20040b40e00061a40c4440f03140600061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327430629 1250 327429379 327429383
    0xb1c020d0816030509092802090604030605101401020601030b151804030c05071e0923010305010c0206070e0d030807140711030d050a020303370c11012007 68
    0x2050010b01c0003000c400c411140c10318031a45035240c0390b0038048213000681c40c00900300103150140c8a80d04111848610482c51800c2541c10003507540ca882c1c0000c01c2107032150340c0c40206128548402c001c0b007800d03c03554410030790384050000603180080b58012a51500f0030702014200002c40400b0035004c45c903240701001c4032000540140c11264401051500d0050708890507000306201400354420403070705000b0000500842025510000203190f11195a6441d60260080036690f901d00d05030703000611002442c000e01a00061500d644e141c0c03a186010b0308007600d07410302601c2001d02280030903000d403181d100e107034002420518000d580c40e28106c1c0c2402c03000e0105001e125000c0b003050300e00300321a40107000d094001c030710303203c0515100018140303000c0e880340c1883c04004040c420020702d20350200460b504003160500a1b541a48000808000040020104001468143c2c00b40c018402c00740c00540d0903401640303135144c494607030a1040f4240c54828400c0c446120071489620030800045000c0c007981e81c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327431879 1250 327430629 327430643
    0x20717032704180f020a08061005041104050303130315021608070311030c0d0e0d03051b010605060403060c0e010e10031a030303040f0b07091d06010203130b0901030b1c020d 76
    0xc0f014610031124040c500030658107000d0ba400e1034401d504055400c14014000b010003440c0700d103055509031410781c12038060309200c0c548031315003840003254020546010307001c000e058958030740c2c148680184030310062104a901550080350503000504920903a1081865907130511010f45c900d94441c45140d1200d101181404840e844801c0705100400c0944110384680c0c5c001d0000e104074034070252412003079100d01071151200c42c82c40400a5030007003c0d2401d103042044400e800c5035081c0925805005031750031036600314002250002c02d205032904102000800340d2281030f4040380c0000111286840d04292073307000014480450700240c402c1e80084150b078094030190040c80d4940001034107552059406a61140b034016155003440f110006207500700110341410507030309141c44000f4084005680100b00c13400030020015070aa402841142e032011410b001c0348015580f0749041c01d070240c00402c0c01c90700107460301104040b1800c00d00800c1d80d03c161161044420001aa070030803101c1e614a03d002c035201 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327433129 1250 327431879 327431891
    0x809100203063006101d062b0f0f03030b01030e0a122a061b0f08221a0c0405030307060f090b010b2101061b05120406020717032704 58
    0x5074406000d5a07000d0010698030403490761a054041da00d1210f06d034245441c2c3c0310b021050184544d00d20300e810f2502101c07006441c0f140350614030900b4081090750409490b10750508003800400000743c041c400d56900c641c40402c65004404011422189c58200065055202804203408541c1100100c916421a4604481600b104000c9000d086041300c503a0f054030480c55041c0e404100031801441c00b59070300780d601e0b00460581d11300010040d21000701d0b4001030017004008102007484808441c952400f086035402141107261814805001007a44210b0902d03100701e0100c2c100d00400c0703080758101c45008000754240700154407400002c04904016241080d66882c0f818002003079580010300030081b104019032a0b13881c03044880030351184200528894a01301d001030000c0c0d60040021240c00034510f442080e2400c140c60618540381c000c0090810507a40860300107444d03980055501c080d5040d18240f281c1104c4880e9005a890007078146401010200c1c954a205c18005442c121070592070042002c141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327434379 1250 327433129 327433219
    0x1514042f09090f22050304090e0a0201110601060c11031032160c021801121b03030203040b0c0a06050109060608150108060d0303020705010c080910020306 68
    0x4021200c0592603590000841c48622a01c0c00c50781055012040c03503400301c00c0e0b19052034600c1c0c0c400541c00308000c000792941c10310000c0c06020001c0e40c000d4110100e04101c81440c0a0181e40e80d20f01c000e03c100d002903c270301c0584962100214099040394103a4940c84403484503556200b6134104420b103e5601352148040702281c100d107038040d0709a4a02040307020700511036419104c0041c00a00e141e0240300f4113140090000300038555403680308404603032410f441505203e10000740703004513901c3d081044c0c1c00328800209403003004219032160304c0d114060343c0000c44054803102c045107005100103405a0824017080100000110090000282d66800e43c1c42025107036480c3c50440d4030a820a104035680c555042c00119040f44409400c0040e40241002d0800e582c80002d000c2400240b04500804041800c40d040502076010b682d652684440240480d00c801e020003000c848045440e008507100306603012580301c0741171080b01d0084401034805042c4840c001c546081000780181078181001405030440d81f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327435629 1250 327434379 327434441
    0x6020d0e120a1b0c091b030c020a0b130f05060a0b09090a02040507020f0102070c0501030f0b090a0b011b0b0601022a0d020d0803151002030f0403110307080307080c01151404 76
    0x1014040802000620651b0b1204c0020158452010002410b281940a1055580000380c0d28891a072281c014440f0350b40d00d4900c0c10641d40119401408040700da41030700c04100021503140c0c800c44c440d0b0003c11100f6503c0741040021001a650107165800c101e100c00058101500043d074050454012103841d0f4000440701801c87c0d118907c140c60360500f82c80e0500042da810b005040e1002c5020f80113000b1400141c000520700c41002d00f0442c0340659941c1e03041c58a9001c1c1c10392002c84c080d40b07188003070014054209901d4071042111103d005004050132102c0300343c131101074500591207588500079400381e4407082c401d009211841c1644c0c0300002052280008a407900210311a00c15101d8401c2c1050228043c01002100d041500c3d040d0340040c0030801c002c01a4034156002c682d007004005010b4441100030900b410705980207a0402d00002451005000b000c4000f03042c2c0c0c0c030344d100081200340a0b41035060301071002409071001c421000c0803030380030520349600310144411030701007001e22b0351004c032010750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327436879 1250 327435629 327435653
    0x12070f0b21130c0b03041211010e07030305040e1803160501091e03090e01080c040f020f040b07110d08030a022206020c040608070b0a1803080706020d0e120a1b 70
    0x15200c502c400610010440b40603400740c018a8401c8a0340d04604041c0d65034039030b442c3d0101c152000c01401c2c0b070fa00070f0b98030b42c2500b00401c040401c40645201a44130300b4000d040d40d106010b9412324000040100f000440c8040d51000340100100145050050404502002420302c0100b0707140c41d034a4005600c04208407a5000c44c1d0007071180c01c26015500f186c5405451094a94841d20504407190010418440045a03112030034000721400a41d225641030b005001b40078070400b071f11150700080340c0400d41108a0f40100107041c080e02c81454092046010000a42c11030381d001005844140042000324103d40c000e42000300f1603a1003040802100b188181103107207940d03c46801603128102664080c1000c0c440e440240844030094081030b03092903580c11051084810080401580c0d0901c00c800c1082c0704500c001441e030120b031141e030702c80c414140200a500300d01d0280c10702c6450449008040c40000420712060500c40c00c4460800c0e5290400b81c81881103d13280c0b040c00759210101100040303d1039090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327438129 1250 327436879 327436891
    0x62102130e090a030e012304030602090909240a0b0d110117010f0510020304080708060105010e0d02031209030109060509030a1e08010302060a0908060405070512070f0b21 75
    0x5060028606944010151000b81c007080e5107820980700180400c2c3e00154013180c0090030b0821890040c0b0003170303041c5403810a141408038802c4001c2404400c000039500245a1b010f0125401800b54582c41030150711255003d070a4400511010b000c809020255000b89a1014400d500059040500d0b8041f07154541800c2c2e049501c0e0b030480c100c0040641c4c2100070300040d085441c034078648a40c100560f2110209050060620400445001040240c0f080048030080c01030703c1c0aa801495480015983d1010280203480c0440d0480d00e150306c0f94240f00000400040d00240109030f0b00ca046014504190b01c4003c8090b0503548850b0002c000c075a06008890040c4a010000c40d0387c0c03054414010058a40e500b01801e0007442c691071608100d47c42a03c0031f0549404a911640d542d00c00d01003500c1c1904198010525800348100b08005d02c8004500c0000b00e0314140c50b0140403210411402e900c03441c9074010b4820000301c10505010502050000d4140001118480c013002447d140041d40a04012211 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327439379 1250 327438129 327438157
    0x20904020c0a12111f0e0706020625020c04050601030b041401031b0e0f0703090f030203120a02030108070b0f0c0a0b010f090902010f05090118060c2109062102 70
    0x201e00c080000d88000d84441003e00c0c0b503c01480d40c50b03010f03030a45a400c40d10303546030355103003504000c1c00038181035014601d0160640d0413035102c956200c40182d15003408450000950000c090a2a84c401c0041c0b00b0021810556029140c036207410740c200401020090b08050405a68988140860302c5600c03c440e40100c5256110421f03601d50b25243d05412802152841d45190300301d02004090703107801c51140c20039910141c0240f40d03981c00324210002c100700b0030040d00200e0a80440740525070003100401d020101f003072070840c0c603945501512090340710a10803400c4550140c101007044c050b07409c015000302140c0010080c0f0304419040351514180035000156100901c5000401600e41c0e0a801040105008002888001505d40000c0c08040c151070018040c480e0019850249038429000c4015803500455507000c21911214000c0a6881410301114107007041202d6814a0700c4d402240c2034003212a40e11560f191f41400d030200c5401221b803d40034003c58140e09500f11186080c0080e0040343d0107002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327440629 1250 327439379 327439393
    0x403121112120105420703030b090a060e070c030302040815071101050408090d110406090213080109082d041e060e15030c160b010503120a050d0c03020904020c 70
    0x2c052180303224180c0c411807040007444a81c0041902100b94081c80c117000381511240c040340c000510985921055510b1a41000011401c0800d501948403280c44602903540a95070740c1ca904c00481205c05a000b514204464100000e8002c0d10500645000c40e10914002d4200b43d07486056601d4046c00c080120004203042c4200100b40764007403411080200080002e12241c1080e8803243d52511070039000341c1c0986859102c22080c0300c4904244000180054420015140d803911100001d4000e80911105120769800006002c401401603141150300903030850300d465405202079581d2582c2501d14480f02541c25019800090744030081e100500030f081003805000301e80f807074206401c109500a0300c1070021150040c00305840740c05510000010045880f0382d26242c1004150392402501d8940c8140382800b0f4501041044407201c19049510583c101d03180b426142a5400040c003881061600155081c0107154134100b01350042888244035003170040c608200000403d05a9204280c5520360740e1010f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327441879 1250 327440629 327440647
    0x9040c03260720150f0a030209030d0c020405090c030c06030a090c030506010503010501300804051005070c09020f0d15030210020609060a0204061202090301060b1308010501120201050403121112 85
    0x38483d4202d00013201c044142160280c1912010301500700302c0d05600d41c01081441e4420300a40c1210380101c4000d01f240d00941c3d50950003017007a41c0303d400803070003203041102207540c9030400074089107040c1c030003005447c5c01c81a950a01c4041d0308001c194680c0c7e1070701c822680d4042a038428150b40691300030000303402c20350f0505040c54251481030b030100910500c00e001c110003584007030328101545054050280c903d4050b40c2045402805641c0000c0c3e408904620300300c0c20a0342010040508900c5408a5070016503a9581c4000324010145165149681003042604640c0308d0780c0300c0c0c070200f071121080000d61502c9070007151080c0700d002c507040003681c400418007000113810044168000d1341c07000190b190a08086000b0a0390015010040145401052000700e40c1c2e400e41009010f4000805659183e0100300c02203848500d051041c000c041d440d03d400801d980200c0f00c0c10a41d1590180c40d100d1400703245584650720b035600540c18900b0020039450f0058041824407100340140502c80c0200e03101c0741c0354 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327443129 1250 327441879 327441923
    0x108010e0303070f080709080118020a09050403020a1e0501021917040816030e030d020705090705041a0d1e0b0a240302030c040312180509040c032607 66
    0x840e00d40030154024810402150341c004d0104400c0101c0345042d01c0d083e103030841e095400d101385800c480741a5003040c010030350740e901c03404214a23000d0003103c008101503a28503110007101c0301274901500581250400b000410106101441101c6c02e24070b10b080650b00b15140c03542240c00202e80a442c4d5110b00100010142c0e01c81031800c0d015008030910b0340e2605050f62841e4184c40760b400c048915640001140382810300601325500b501001500355814540c3d0024000c0d02e5006a00841d4490741c190008948034600c510180e4040d51080284054426a6810460140d8100003040642c658481c6a04000494032807c0428000000c2e4004159045400d042100715601c070340105d00080d1081e0a508400c50600801000403d404d040041c0e507034031503a10b0200144a03d406c0549401c403505e1f002516076070704c418080404404110200d48940c0ca800401c01540c00607100036040301c824500c18004580c0e013107000710000810003900e500e03815008c0c00000098100781c0c4261400100c010f0703a80c8580000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327444379 1250 327443129 327443141
    0x30a090b0909060111160b03040c061b020f0406031a0604181106070201090b040b040e0c0403230c131b0507080313020a03021f030b01090b0f0d020d060b03010801 71
    0x404045500740207209011500b4201c0c000c01040c104094040d0700207454170107001040800410750414000706480305144029075005803000c8803500444100000e01c28880d00589840480e5502c10b40311401d410313000c101c0040c00410007503600c995200303030001c0000c0355250b10910b5160b9080b40402503142110803c400c580c0290450442c0311410100000026001c20706030348445411204c2940310003060004075541d0b01b498100d9455402d0000340810400c00510180088400c01c1c40f800645541b620000b0710309014074070000744040c1002c40910b03046043c8500640d6003981c00c40071500b00144690010707a28603009480020440c0e0f071090780d5800c3c40500c0000700d01d03000030380c24554078103505642c0700195440020b00d1400074482d041c3c419070031941d55204200085400031308180e04040109181d40107880600e403100046483c003003950280d07500445041c3c0c225a4112506410030540703003010600c43d840340c210f50075140d608101c1d250700400b180c40340d00040c15403144055140c0d81841180f90071201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327445629 1250 327444379 327444389
    0x9020111030903070909140109080c0706020109021f030b09070f17060108010e0901020c01050f071d0907110a05010906060612090b16020a0203010e011a0603090c06160803040302030a09 81
    0x20092008035807000600041105e003101d4000034100071509000145101e00c010000055007400000424070094170003070700c0b003014604292100c8940e81c2c03205a0880300780c0138000b03401010182c9030340d01c0c4054010440c0004503035800c000c03854400d107a0001e50100e01c00c0322241e0104000c1005402c8896020030804806401062101c0841c20b2807800a80000c005108411000440c000020419502901502c4101d5805802484141000318400c02a0842103a1280c0011221000c0300c000e024007094000062002800900b8203407101041150400071040c3c3d02c80039481011034070b00c0012000d215940310701d03001d8400012800c3c10400005e100c8000d901d40030045c0c5060141c1c4034003141000040e56007051103101180c18113051400103034109120084040d40c95483c00b00c442924110640001c042158500d0410300e07c0d0030040c04021043c0010b507650485a0701c040016010f40c10910003c220380101903403411116082a55180c08562003207030110b005810103d01035070200e40101c0d190001d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327446879 1250 327445629 327445633
    0x30609030d06300515010b03010905060d02090f180703060f0c02030c2a04021b06070521040201020a050f0f010b041103042607110906030f150c040f0909020111 70
    0x1031a07102840c1009042d00d0f40310140d0200b04200031082200c1000f6588007010000340c4c02c60306603034407139554000d030b0401d219401160341050002681858840c1011081e194000d2400a454841c4920521080c000401c0a59016122245030582500400c02040103501c2040082a401d20111131502641d461003001030556200348902c210111003c940d0b80e54229154496040c404c0503885001e00054800c2c02d0241c000341b000594a00300c6552080d41d031080c400c090102c4002e0345540d80125018850182044480300302d20f0b140f1b0480390182c8182d1a0801c1c0144121840204c5035140c075400c14060108081c16036102c3c00720044001c400303000f42d00c0320040c11141040140d4103680c210909202c01440149001c0144400150700c0c4852107018580c409a514401c2e01c420603403038618404951000702c070344540c0c100c000003070300d914000448480680040713010380140359410408214000000e0700350503840d1428000840c90550140361640117140307607000402c86c00143e000142c146c806040e0301311815 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327448129 1250 327446879 327446909
    0x110a0504112d030406020708190c031103130509061f0206040b0601020715051c230f09031e0d02030a061d0f01050d020301060b0304060b0a0803130302130b030609030d06 74
    0x70b400c8252035000d6002800560340381b00030301c5c00140c203115119000094130740b007800e04640181e005081850280c800c0d10360210b41c1c040c004030355950780500100da01c001d1500000c00c0c02582003d00a041d084900500107800280f0f02120340c0441104000c00f050050384681d0801003800400c06003e50051400c0c005401c1c40e90406001d8262a8941440401070080004000d96000400c0d2004800409915801c01081c2c848140d040d0000403004d090f90f10302000c0c0c9000c6500c0c3e40201e40d00030f0092045100562921445040d00d44c0720101e0f040c000c0d514403800340300591400c08940001e43c07080185040005880d03003080c8100400104401441035011b080104100b00c8072010504107040d0b400c100c40342001d0320042c0c070019000d4112034001803003003030340401804100705490304040c1d03c44404940f61011a621390b02d64503a2401031801c0c0140e146c03485c460420241c101410490201c440904010039810700c00320110345440b100b81c1c1c40d8000b540c80003400300e89403004c920030b000207406110b50302855 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327449379 1250 327448129 327448207
    0x30105011d16140a0e0a030308181c08040813260a0c03060506060d1a03010b0d0c140f09090703210c08030a020c0709021c0203040f110a050411 63
    0x50700f1552829a002c410001e1403a401d140100d014000740c40000b000c001a00752a032900904150061380c02144054018506040301c40d00030403a881d030583c0d4a00701581a82c0002d608507038004000e801911024002c020240c040c8040240305406401e1800d288012140e80398007403066024140c0ca02032030794202c5c40c0c6900000390300c58400710484e42c1010011550f0b444074400502030380b194000b0b1441c05850801c00491a00c1c40417440d1896a800b10001c00c009805481800300d8007888400003041c41e031141500740401c40780480e981c141c8a2000e0003905510020340042040510250b0b04120580c1c8500420420006c0c164052588031300e11050041c103202100c0005002c4410030b02000f4040300c2d01000168440031a681074507031400700380044440003691910700304020352000d80d910f58425111042c01c0400a214000c41e40125801038200f06e0740aa076032510304180407a040810340c040310b403a9000071280c1e1140102140780601c204910b03900e101d81c4034004da190040e1680b2104142400c181c1c004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327450629 1250 327449379 327449387
    0xf03060b0306100912050c120a02031515060a0c05120906161403042d0e0606090411040b04060323011203050c12070506072d030902030105011d16 64
    0xc2c014005a41c0c540c0c000c0d0004405641948040e004507203503545151068042c880d00085900b0000802d40700e880000120f00c508075100c503a400c0380130b90150f00040c03844002c0e08440781000c0c1d000304088060a0304000c440002099503001c1032540300010a00081c000034088288410a0545200d1740c2c4145408500d0700071451074021291095002800384140c80b0a001100903900700d50100e220036265166100d0408001c011081034000302080501009240d00c003401209190544152010128060b5503d100f004099804241b609801503107070b40f482102d2041c5c0d034001e00080c00d20711a08039140c60500d80001c00316240342925070142a074405841a2991070010458103543d05034001800c00384841c02d040d030b144d1040303501c4000c2500c18000200044801d040103040c03107912a409a40242d10b554a04540d1040c4904060300c44e0b070280e8000c0601c030484c00b9000b031100d40c46400c000c030700c4078401c0d00083d08641090b4000e862400c2c004814000841c0003074519903002d181d894101c990b0701e004400040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327451879 1250 327450629 327450631
    0x9010c020c011b0c090212090c06090909100c020606010e180103030f090312020a110108090c0907020106080115080c060406090501030b041b020f01150617180a050307030f03060b03 79
    0x7a05011541c00c0c0300202c0210031800400f19908401d11401803130f5a07085590095200600314188288035201141c41c41d08042003032410308900030086810414280104640d000c0d020b03200c024103209540c0c01010421990041c4040341000307802801c89031400c0c2001600b401005c90b4440d10070844a0264152131004860aa055035054501001e0050104a00303403040b03001c070340001c0c0034a0140160322003959400145100c58502c0741c80d09001c03a0480c10010b41d40303a101941d40d000a5041a4051030007810032800b40d81d803240c1c1500c000719110360b40f9540907084456a020080d5508545201485801d4041018440720b55041e40d88038a03151070504001c1840c0e8440c000c0f58105504e50010b803100d0b5946030001d458040015455030402035007010301070745d03c003050114504154202240d4892079049100c1d81e038104d440ca078076100c04008411000b821074110007020054100200300b011010181c08000011000744604000e640c2c50007103007409000d00210300403440030907003000300900001002000303403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327453129 1250 327451879 327451903
    0xe010e0a170c1c0309060e06071106190309050705010527010c17120a060f050108220503041e120f02040b151201080a110d110613030b09010c02 63
    0x40619061164503203401c02c1c1c401c41c0d95951215000b9800041c3d040006002038805100761903c00c0c0041d0781d0082a180000042c00135035000405000c0580803680d0395040c0001c0350801069680741c00d00341d090041c0c003910750181903000283d40d40289010041c0400503030010708400d082523030600d07001a481a405030003550088002d038003040f0700d220307503a4000e405956286920164202401406002030034050300540a072a80b1071039100081143c1d0300380f41c490a0152210720301c5481c0828100001924468000391074079031003404524060094290a00e00d5421a9104402442d91149405100c01092000c41c0e54400b50207001e40c0100580c10360a0f00d01840b182e449001040f0151700790001130014910008856000300d071050102540c01003c0f0018005880e00030100030581e41c070b68500b03540d41d41d20700384000c00c900c04407404031445103003941e410403040f88075540803802d030080700e000324007682c0182c0000105110b0124050003081480300c1140c0e480403540000b00140d0912020082d0750390451050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327454379 1250 327453129 327453149
    0x6061d0f2205190b0702060703200a1407030207052e11010f0c020c030d0c02091506040b211e04140f0708070608010501090e01140f090a0b010e010e0a 66
    0x4008008050001c2c0032500122142014210a44c0c18a014590701c01c880c0000140102c03000640c00078000d100701c0080c0071201141c600c200b07080050410007540a11038000c00d00c03500070740004a0012480c01003074250711a80c06049001d1515081c4816540c43c80403c42c074502850050005608050a500d000d08541d0b1400700700c074041c800d84a0b40141595040425980e00b42510840640e0b000078840b480490141e00319000300841d030f5401c881000f503409000b54082901c1003c101d1100d01c070b000e0622400c0c801081c0c545004c1d0358018403e015803000505c40541031a00400c0c840100c41010301c00c1d8050a07952400c5c0070380041d80f08804500d5002000240004590303540c03822000e02c10844000c0c1206042c088070401c0c0d8442071a140c2d43c54942c41000000390281d400440c00d544591602011258101c82008059003052043d42c18540e10a11003074000c418806010307002c0d900c0d002d50a02031800c4180c0083c140c8180f400041075490340d014054180400d0101c811303116240c4002000849800c107035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327455629 1250 327454379 327454441
    0x20603060d140a0308070c0503120402061903051515220f0e090d020c0d06020c0a0807030309120824031606080901050609100902030406060306061d0f 66
    0x1001070900010410040c150740c11030319110340070100c001a220403060081d2265030403661242e000702c0d04807055501c010401d41042c0b0981074500b0f080c0100941282c4001d1a0909100921041141c9131405200c5540000c0d2074409100f4050041e0854400011042c0d039001c014002c0b601d10341d44d580c03192905044034080400000c0d14003078400b161141c0036145030107424a0071a82c6035417580c0c07841419140701d0028000d0b03444a000507400014003400f902c40161141415243c5500c50034001d400040613000315005108484000815580003401054803a88000172160350070304012038614643c2000a0600c80840c0500a808144000b8003420000c207080101075041d800d03010a060040e103103120910305134845404034103e50004201d51080047d50f0080246035140010400c4030305080e20710340c004c00500d000a1000034004c1e001103034898060385001c1281d540e240c0d50201124540c0d404030003411040c1018440c00c42c0300c0803e0b607410082c000303006c506a0402001d0000d1002c0901c540e2862109400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327456879 1250 327455629 327455641
    0x11121c03090c1806030b0702010b01020c03011812110111040312020607052a03030711060714030a0f1415040e2a03070909060912020a0f0b060d05031803010b09040f020603 75
    0xf1304401c02441c0c0c044604400d5007481c54001c0c1c00781039200002c50140c09003007640c1d41e01d8101446400800e41380c854220880c00b10b691a149402000a401d6104000a51030032504d00b00c024000c507840a014441c4c07030742d5035520313506045941c06d2070483c9100840d00000141302d02a82d00c90706a80070300e595005200040300d03210080c0c800c00b20300703036900c4034442c08084200002c2c15040300040300310351007020030f54449076209503045506c080030110782c1c101c54400b400070030545109a84144001840080d00049401d8505140401c14404588190700004044800c0c86603042c980114000b402061004015071918007603544c0c1d6503801d211020500b06030260015886a03410400030340100f1000508004a000c2400c0c164043d1100e40019260510054200d0314410b20002c0c0f01240030760801c0f03420500804603a44c0b01c2c58050003030085d540c03014407110f075400031035814801054100d6031410343c60b8403880a0002d05007034030403411007544105140c2c0100f101182c081a0403400455040343d4007540c2c0e039102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327458129 1250 327456879 327456881
    0x100f080a020c0a021f14070807082118071505340305070611030603060a0c09080717010b0102030a12090501020d0e06040201140f1611121c03090c18 65
    0x40d42c0a50701400c51803c82015219109540341d03645c0c603641e070305018114040c00100d50740c814103100400e00700c0d0402c07a41d8003040c0070201070140200d00d88084c0f100c1443d801a0340800f0307501034901c141e81940720200300550300b40070455140245000701c10340040959404028080b801078040800c040301142600607815101401c55101d43d135543c05000c81c503030350207040040094200303040449010380341410000c074082085080da4441c110050061103540e03a01c2c0c1d180c20241403480d031030100b03120106001080790482032009001030104581c1004088100c0c04266003913540078400c2c6410354104000201146911500701000f040d031204011441151615065009226414501c00080d103080f80440c000500070034440d00441c000d0780d8001c040c5401212980180c03140400c0300030420020041030300020301412544048900403260944640e07040408100b2424840034040199007014802121007034100320340302002020b5280410000400360355403d01c0b40414000d82c40c02882d44481c1034118111 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327459379 1250 327458129 327458143
    0xc12040515180a0b090a05030406080403141819030804060e04060f0803030c0319050711060a0b0109050d050a0602070c05030706090b0409050c07120e011b020d03030203070507080a0e100f080a020c 86
    0x3116040b40d40d10b070354401d4000c0c01c0210543301240059554038000e6400c06801c401d4507402d0503540500b000000c031030410401c0e103001d0840440d500c403115800002c080b0340540081c200410182d11040700419084003040100c1d100f84e00311500031049071009208540000007542c0e0301080408a660f620b0725501121b812070f00c400d12072108191305204c2080750a0303601c00c18402c171f00d00c412021520b4603103580403580240d84404484500107101490104114603010b085056568011019120f01c100035895803000da07400302c0c00503245102404400c10040c102002110000e04142ca4103034034550030442440a070744501d02c50220300a0b100e9002c1070401201d0f0301103076480c1d40c0c84225039414802c0c6d0788000d0221006d104c94280072a4604103588000401d04d4071004925a000b402c12500840d86d59007a8000d4201034069020042c0c140686000510708038000d004420b5592a02c0c500484c141c02081600b04400c40240d080146101d0780f0a045030f00000c0d007541041c0300c540b01584884014606502d4044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 327460629 1250 327459379 327459383
    0x5090d0c03110d02030a110303060108041e0807080405030d0801270b03060702011b020111070b0405070302210106120f020f010e1302031005030703021003050c12040515180a0b090a 79
    0x180e40c43d0b0350300301034001004081000039a242c40b101d4040480509849001c103c8856001c030760080d00040000d2401c0f526181c100307400c41c0b810003214006480e88102504688009c40c5c401000107010301071407078200301d506224541c500d000c840c071350304111420a00e8040d85280034000c84400b01d2601d0710460940010101a0000d030403900a86410603001340a46422460324101c1c40c48008420300c11071040c020407842d85403501c25189002056038454003490720082c4140c0d082c0c014030308084016550101c01c2d000694200c0c40803040b00075140d5400d421240c2a501c01140b03085090640c90001d89200210b5110a0b011503010b0104008000165034041d60280003130741c040d60900109840c00d901d94080c500412500940d160040e0f00d66091669450040c00f01a501c00440c8929100391446500404e9000c0010042641090f10758420610270750410395003141d00d6000424111095040c48107201d5124030703d2050082048410b9a0481e281e14040801500040b00c0350300061750140104031111650f5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 327461879 1250 327460629 327460633
    0xc0f05030d020d050f0f0601090e10090203040302070e01080c1804050a05100218182205070e09011a0a0603020a030e062e080c010309020d020a0b0414030105090d0c0311 74
    0x840045012001400111110402141c008022600040c00601d0306c41c458001030b19841c0c0c5150604000c8000c048000707082a9445032a44030108811010b80042c600451090300100422420640124501c0b00141c02c08402944112007800c0a540c2d810b041c441031682c100b048104944950901c40e0412801030300280042c800c122000c668151309600034810350800e0620360074000c10700d2081100c004502d0030710841e000300a0003c902072032400d43c02501e000b80c00d07007903100320204603565550a01040c2e50090315108840350410448141c01e000d140440440b00803004c103801100c00c0000d04128041c003512081550100b0351610490017030303000300445d03a41c013011100d00f071070300d515003130716030950300c3c16500c80710200258401c650810030407a0f1043e00c8400e0701a01c50700c0c80b104011002807080354800da0b03108241140d010b0168607642c0008010700141c2004d142ea95084c00c00d10041d030084e406066000784c1c50300c010401c2e12900400c000502900798a0a89015250703402c085a10031461000f880c264 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 327463129 1250 327461879 327461887
    0x41709030706140c0718150e0c0a210606120b1503070210020f04031103060c031b09130c18140d0204092004050a0c0f0807020708011a1903030c0f05030d02 68
    0x85843c400306d41008160003403003400000440014140508032510500103865002000b0507405120800540481740301843d04e50304e00d010340654140040d410800071131131180d0711601440940e9000d5102c0d419503076008402d200c610b1000d008070388518044021132650400c08404a010b451090003188282440c1a81c2952603c020100440e401d0303006205c00c603030607090b20034640c840e0b04010690900c6000c5011403503003181c3e9103103035041034901106c1c0f00b51410442040b10201c6507540c41c000c5180c2d0440880d000401502083c40a042d282c450100407483e01000d110403c040da060008020110300c054a02c40759a40300340c800700d0b001e042d0300c035001408030050b40c3e031420060518511400b1105c000b01c50520032501c0e100305000445051514400009040e5482540c1a90003034070002d0700010144111910a55164502400c44494002c1412211103140c0c0d01407451400c00c8520b00f036503020182e103500ba18a0b40d6006412415500b40040002d20134030300c8001400402c1c0196007412013054015591 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 327464379 1250 327463129 327463139
    0x60c030209030708010f0509061003112403070f480803070306050603010b030c03040f0204020d1d011119020106180605090a1b0c02040207020d0b041709030706140c07 73
    0xb0b840320300191006d0342e00d40000540613040c0091410b00803854494416035590a42d100c0031261424040403a4020182c129030030b0400c0d011040480000c401101e0880d16820001c8005000040090441c402c001400e40e41d030f1601c0701c0180d64404080c001e404a03000081c0070b014803034214280340300ca1120700e1004c2c0b03910100b48015840158814951075404110882c1c076031042202c00d020a0281d40c06141c001c0c40000c0c4a4030010000b1500b084c01180c4210a1003030b1940002c0c01d90b030180480400c0151100050810100d490700c4119175604504000e00500880701000550790040a0703074048095200200012460b0003940300700040d202414445c260401e6079003c050103400e05201d8140105d2405e40000d000c1c0d403161003200502d61041400820420b0014822281c41c4810001a0fa1190b0b0800405006985814040d00620f20030b21440c113152130103007050007448000d0040c94000385000c0011981d95680402d261f42138540e91300b403580c0070b401d14103c4412580118100345d00c02e4490254046a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 327465629 1250 327464379 327464381
    0xc05120a1115090601060207060f030b0409020a140a0b1c0504031b060506090112030e0603071101140f060604080a0816060c020a02041d06011a13061205070905010507060c03020903070801 82
    0x21003507448108584c0b050745e948000702d0740c454061080d600045c0d0212480b01c40e0314429086051202402440403801d00116000981c900074580d018402c20a9210900d60709800d010074180018a42203505900f07008070203001c0e12080c0800d03051450b0325036a40c80000c04050161140b052107902c121149036140540d0302e880703801000c080c0c55035071040610800009910403500c0c2a4030360381d035044d40c400b04190403a02c14018a80c101502c810140042a0312510805400344205aa45101180500c055003000c0302491440e45018000c1401080d0402080c40314002c00100765140700c0c0d0100c4010340e5005584103c40c0c8020807404006c1100e070604105000c00c80c0d0001d59511628000c03102000084000041d42c00c2d00d10544032070040981005004208488920080a07080c800d40a00300c0c0c9400070945900780000056003220000c02d201c02c4500c00c019446200d10795000c0898281401d1480c1000c00280041c018080e008200e45d454880f135801c0d1602ca90103a800170b540140031204565212400d0314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 327466879 1250 327465629 327465631
    0x30b0a0608011b120f02041d0402041103010f1211060703270f05010e0607020d290705070605040c05031605011115042a0306060302100c05120a1115 65
    0x2514940c02c0c0b8050910300d000400c081c0300001002d89504c4a241c0b103400080c009007540ea01d5411115500780320010b480281c40c0e4000c1034108041155020500c3e240c4100001c440030040c5440c00c1e11010320050100c8004d44500c10700f6070b000001c960240d0346251070551445c0b80e505e1001d0350000408110b000806800100c6001554041184404907200004a0168000761446a00c1c50791640d44c4041049500900580050700b40c0a070003189412215000b04060f038010b00b1045034842110000744000100c2e00200c805040400c2c50382d0780c2d050800080082180c06094405840a0f0b40d64001c1010460445600c0006041c0507040e59801d0100703c81a07e81d011980c4034207030206062440c12822164041407848038000c40c0c071200c030300039101e64481c00144900c048207251401254002c01c080742440003132110095100e8840824580e0651040c4a501500c0750f84401c20320200541080000d86d01080c0a070030701c5800d003c0644c45406a2004031250fa04040c4140b025029100041d006031a20088003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 327468129 1250 327466879 327466889
    0xa0b1e040e0403030506100f14132603070b04110103091401051501050301080d080603150a0501031106120106030b0d02060c010e0d020f0a152c01060b0a091806030b0a06 74
    0x40210350f90f84e40500a987e014450140b00150160a0b02a03015014007a402c1101d40441c500d6070030100000359203d03019083e50000f1082140d40ea01450300c1150044600b00030b46072810185050400a548416100401810040c039600a00d00030041c107920a60043d025240c0002000140e2564418118000c280664810380d02d810304100714816940100c00722170403240c0b04402000450b01d034440c00c5442e150b01030031403070303141c002d035911740044a040c02d603160b000c4c10341751a0010341545940741003020107510544c501e0040100f80081c804001881228038119031040c10045980003061002910046110800940c807810204901e00001c00541c441d06080d40c0d06030845140a065a00603a581c01e185007416440750300890129002550100072074038240705400740402c0214a200016554010400b10070140000c14003503014074a00c01d000321001031060303200036841c003e01507800030310560560082c40706540810203918100b0503a60301440045030088d1800c1d0090824107460f9000c0c004030f22a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 327469379 1250 327468129 327468131
    0xf030201150810021b0d0809060601140a0807091508010e0c030609040809030118110109060f0c030e030a02030624010206060603040605040c0503060a020a02011401050a0b1e040e040303 81
    0x301940340c440d00c6080505941c44000100820140d20030800041e600045c0411100c4070143c8400c582510300700641541450f1035181c004403494048030492520702d006000d14104010314502442680c0102c0844800c0b0450b483c1918055582260580d8103852940c4941e42041c0c110725210442903118030200e058840d052010307407084d140c414014010717010541c0d01552201c0c50390b000c980000d0811009200c103583c06000071442c901898510b18580000d01800c0e501c0c0011034000080660344081141c4c090001410100c18102800703500400f6402c0c01e407001014484c040d091406241d40400c00034259550040c111400da00d000f1100f05041584281c00080390700000041d075001d980041280c1c0d11446028002c182103655036101c1d0703005880301400940740c0c0712003410041400c3d00d090010f14410307641c68a0259852010800c02400c4554051300041c00440c0140140031a80d00e918180c01101c01c0441416194900d0365848440b00341d11900e07088001200040004580d2010300d0114802c9004e034074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 327470629 1250 327469379 327469391
    0x7271401020c0402070305041e080a0606060806190b0708040b040b07140f060403050723010b0f181602070909051b030a030c02062b0e01050c0a0210020904180f030201 73
    0x10030f0009078045c200d8002c000c02c000b030005104d8106003405020b0801101d5525501841d52103001c1414900d00803001d40702d058540300184007041d000403030315030000c07001d0340c0402c90403420701e080542c090741500502042d0000000c2110911010105a6004d400301000c865511503a81e141494503510a0350203c0b10f45030f03101c4482d1240a004110b0070b25a03040c0e20090071030b90344c9941d0700321103950090904954a10f8003400c4c0200145501e42c01c0ba1404c2050703030000403003801d0b0608014508100360380044c0700d900042c9150000460007042103404c440307042d4052401c804845001d0741070010a42103420b03245d1510311004244000000c09941206001e980b60b42503d124005242d16603141341c01c080c01050500c5402001410500e000700070401d05a20740200c0c203030200e914050031044210300001075030344606251060301800e22829400c154003ea549150120f468406502e442d06140446411a4007080303c41e440d80712a0040c50056076030391600e9224098601e80944000340ca032405800542c6042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 327471879 1250 327470629 327470653
    0x1201030c06090b03011e080102030915010918020f0102010b030a151d06070e011202040b03090106150c06150e040305220506040e0a0f020c0d020105060f090727140102 73
    0x80c0000564204003c83d61460f820002e03280e0324090007020b03d079200c2c242e41000180c084820b102450081d03080d080541441510b41e000d9280840060704100078447c03418506240742c90031800907404c010b034196489002d0a54a50040c0d0051201c00300039038141c06020500000c0190404919201c548070311002c0104001e103038200b241c0b1182c84001400b4550211003c10f15107400740e200043c0e24171051516140400742400c0c5101a070b0003c0d444040c0040e80803083c094000c80a00541d009825101030900030102a403800078650b581044000d842c1554501074a90545045502003001d004150700c0c50102d8101860001c0c015400401054110800b05805152041008654400301c8400400745410300d420300d40c04003001d020142c4541140c40d51540c4000702c60400e40082c04120030b08201405014071048c0e40030f802e4450081089101c0e090f500c8401441c2d6440c00d8046401040078900b146400100e1041101c0c1c0c070700001c00c00c0740e5031890740c00000b400f40e04400184200060a03030035600345070700c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 327473129 1250 327471879 327471887
    0xc010c0c0c030f050a060f0c23040b030a0905011107050f01050405030a121401060203040f0603090c090507020c031203071b050a0b2706060915031203060f04021201030c06 75
    0x91402404800c20110420110f2510000320010324020410b841e81880203a4a02040f214882444200701e0f483d607a40da544d1075080101d14050000e20704009a02c5000120045014861405030a075130910102c00b046000d02c0580c4000c40e1079070710800030040c40300111841c132041c0d00701d90701c12903461194003003442403104103001d07540c0210740c0b01000718200006070009691042c40d410196120030b5442010300020a040c12055000b4001a000345903640e0509444da80700c0d600c00d4100609050401500400040004d03606400301c1d0310340300002581d07440d054012410511007000c202d501d031040340c444140462a86c8001d500405094881030034a224145914003459015480074109401168128010070010740416070303c140703005581c003034011240c8034140320a818100e0540007a8014402c000ba181020742c1c0c059000028034244080e0905040d00195a03090300c0030002c1050b2001002084040d158051160414400280213640368660300340e80c04007080c000d200980361602451400119240a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 327474379 1250 327473129 327473147
    0x617010e060a0203060f0913020406170a080a090306091a060f03030d0f060f0602070f050f0f040c1b0b060a0b0304030503070c020609040e0c040f060609091a0301060b0c010c 76
    0x2210301901065a40300030302c4000790001003407030350070030003100d01980150384441010303120f0200c844103111031103514014401102c00b0390300200141141540660701800300068100300495110302829130b203c9030610211214a800e42c0f0050540e13080204510403c03142c04654841070502c400c100d01c5950340d540801c11269005d11089400d6002003010500c1e1a0301da420854030802d40500104d081542c420030410b030401664000e03401a00111014040c4000c03524501d0000e0a04864200e403185030b401c0082c40c2c100030071102c4c0788507554511003a00d0880c043c2d450602038102030301d00322009100c00d080845001e13800f201c0140c810421528013240b4115260140d1303002d2a010750300e00e81150b8511405562004006a059911100c07d0280085035a03442c09030704480c0c130b18440604411508070091000707542c1c000001c01000c13070030b0090070b115255000300803808031070752148041481500009424001c3d150744000b9601542048c00103c0d41203c41070040103c07086030380082010f0030748990100c0d500c940c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 327475629 1250 327474379 327474401
    0x3090501111602040b04150305100b0a06050d020309100203130b06090408091504050402030c0901030c0207082a060a02150c030c09010f1101051006020d02011e020703050d0906061701 80
    0x2d00d021960000d418541c1c8404040e801c003410010f06491011050700d0f420810741d008403140da00c0480030032144ca11f54018102c200c4000d5421009041c1080400742c03071400384c00410541c4a0f404400070301445420003144022003c85501150b032418401a24511010f03038550645200101c8008603c41c1c0c01c101c2403440c4155005440e00781402e000000b08000b6041d00400400e04190078400420b40340c0d901e00c0214001c80001524540e02e40c50b1f04009000e9515500021082d500207690405c401c0201046013400c5a600c10a04501401000c08900408054444070303a00074402140b0140d03200c1d00081c2c1c0700311725070703a03441c542c40f0b15901c0f803081c20303441d1004980350760800d101070150703900d5035000e0b400c0d070007940100d8209261346021030a192800c4a0080321458403151106004200b026014003040440d41400d100900070f01000c0b2900d602a029803416032902580d0020f030b0031041c5840364050340c448525031b031414003503d4068103040d40602181c0c00350055004040111104490b414425090040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 327476879 1250 327475629 327475657
    0xb030105011103042610050c1b0102030402010c060e0114010f03031b051f180f0b0105121e07050315190b01210209060403140f0102070c03080a09030606060309050111 73
    0xd8810302e81c0d500d070a4002c1040d42910138004210b0582580303004051060348e4a200841d21425004508804003c151041101a134070420a11000d41d0b404001c00c10080d40110010802054a21009005189055000448480000020410034200000a01140d020365141d000395608006e03980323210f0440001c010300d00c0d07021040c125a440c02c11001090b40c1404c0d69000944007010700f20206a4003118038003120f2550402c1c810301c0821221f00c44040c09040d00344d880740d420010703001030a95140007040f00319071403101e4842801d40745101006441c01400c8054161800c4507285d920b03001c21110203403802c81103000386103100c0400d01c02c94402c0b0070064405070349801c042c8071190742c108074000399800c00b8000d268003000b001002c2e40f24240100015445094980c4d4554882882a4180801074643e241c0c264010004000070030200a004002e403600b0480305962103030f24402c01e45141160713502c000c0410f828610000307202a01948501c2c5101d00540003403000c9030241920902038440e8150342c1c4460 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 327478129 1250 327476879 327476909
    0x1050f010f23040c02010c02010509033612100615082403070b07020108011205070501360608060a0305071203110a1113091104091b0b03010501110304 66
    0x100b000103204058140388110422500c1c071402000c01c040d20303440d80345103000d43e450703d4007a01c52035070911405604c43e6405000e982450b404520750310720625000303000d0543c3c0d48134005003a1351814424030044200c400401122600c805e0342820368460b2482e0119100c03080c5042400680920401c0300b1185904071969002e003165603001d291240445403c60100ca04280c100c469140350b2003c201c0c2c3d401600c400058141c403035100344001003c0810503040880c00e4085080700b500007440000f06001542d8090a02e010a21480542c1003814807440444110a018106c07070040c18540d40500d140c1560080d032394140940d41e8100c00e001c040c003030358480140705a005071010040084165502c0310228402d140c00030030345510708505032500456500982e6140d1074440000d205182403401d041010380300001c2401000142d4039160003901d80203445900a58a03044840b081048140e0001503a035051740e0354070425a00c0700120358658001340203480c04106d018840800306207001090b030382241e8000c4604010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 327479379 1250 327478129 327478139
    0x106050f0705010b0a03031107080304031a131e0c0501020303060315101208030906010f060203070305090114070c090b0604120816120f0f030c020a061a0d06090501050f010f 76
    0x10350080e03405030b4940d562034804036100d07620000ba08000f1402980c80b4811818110039640c10110141c2c84480d035540100010400034601000100c04078450a40c40084d80c0d454104c03004101c1c113404001445000c1c0c0521506902105824410480d80521082e001e42134541006a0b03032803009560460389070340015600701c60110540d180c40e900c446000d07684079450351359a040f104505e6039540d007212102c9000c0104580070b4820401c3c58010996446401022031800d0302c00f0b5143c0c461920040d0820900081200207a4040c1714041301c492095040790307a4400d9641032980e5410524024000349504000014185103000780940f000d0b1403000e4650081c044940d55000780c16800200005060203e0441000c00700311494594044524030f5100c491003540d00d03910040001206c3e883d021b0906190030300c4180c0442e400200b0030002c540c00000020521140540c0e80c0c0310343c24403541c0300c1d070000c100e00d00743c000c1040300c2d006011000d1181001f032120340c442d482100752841d800d0080c034040b01c180c0142004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 327480629 1250 327479379 327479407
    0x30f06040903030209060f040e0907030309060518100f081807210210090303020f0109030509011101140a020405090f0705030606030408040f0308120a0507050d1e05011d0f010605 78
    0x40c1c12442424010314040200b408074840d60490045854494004101041301d1308107000a030ba8000490720184c46440c2c1580d6000c1d00541e442c3c01090100300c0301265400ca01d424000701954201c100130200340384000d46d6040144002e22040c0f1807030000742604081804602036450481e010b05151001c2d1a040d070404000071381141042e9946040c08901600200160301c072580c4564101ca40e50740c070f2848050845c06c0107460f2200c4149044c10b103030301d403800da03201103503001003038030610442403900525502d50324040a001d03100b1200b411080c1d00c40c070414041c03a100f86c0d90007070080310800d5450781060346d985031034522005011a1401d0116000b00005038062424000566110384913134412424a0f480d159410201c81c1c080e0021240d60000180c800c0004d0300003540643d01865818080c80a4509030b00c004041e80500010450315944628030b4010600c3d40310340c1d004040c041c603070080180750780d5500d03603e218a000762020007a07100b0f0840451010181024024141c54103605c1d01031500000307007070100b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 327481879 1250 327480629 327480641
    0x3090f010509040203090a0c0617131104150f060509090f10080307152909070203041d1509041115041d0411010f080426030115080c030f0604 62
    0x141080410401d007107560f41c40d1300c0a54015402d10303004000c06440e600d403e5803a11034503003200042c4856041d84078940c0075201042e03a40f1860158864031012900d180841003004105000343d0300030f0a100045000c0c00312010b41404490180901c0180107030b50341c5040c5c800384240500c40303800080c0c480000d2800c1030b02407a202d4102000300c00c60140d00766103185050564204c01c2c011500003024070f0300e540f00014580a6004514000030407402d4000499100300740940da504540c0740102c82110003d50345500a0040e14001c140d005141c1040d80b1034090300101030b8204986081900e81700740c020b210141000409c40c3c0c810381e400718440e20341c02c40308010802c44102445401d460350404010104d0030042d0588000700d181134241d4031340301c00e04161420000840300b002080e4100100d2481040b02c041e03008106070b0b002604444130b022503208144200c8080910855541400b19001000003100c1303041d18440001c100160380c0d50380e141d813100720b0301c0e0700503100985000320070142200100305107203000c2d4814 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 327483129 1250 327481879 327481909
    0xa05061203030c250501020901091d060d0203011e090506160210020304150606020303190e070b0708040510020715020615041a03010513020f0f1c051f1e09050309 71
    0x10404d0701c3d00600b10300f6418012128100c4240c2d4021440228550300700d00c4c103030050003440c42d0000306110040c60100d0804002809036101722902e180040c00c2d51000c1d40003c20000c20030204100403019050000c01603e0040780488181c411a000035440b50001c1e00c041d09802000da0181006416034004d40c00a5000500150b448000300c1d406101c0303480184c8140001000307640c01940c2c40f413400714500f039182c020980c200082c07541840100b07a410303003010561a09640d602d42c17010362108000d0400303001901407600031a41288a02c80d440d017501f50005814070031111a10556020b031305c2e2212049845010503260352030020301d05080782401d0716054000101031265842d0340c40e0107040c410700190079a00140c449448100b00c01c00e4109c10f504012a5070308a00a05503441e20f0700304020b0010a0443e8401b4a14080116154041034100300060120f40001c110a640c88140412100301c2140242010915143c00c480a03e1100703514130001c0c0100c05406403c600918181005a41808450b043c1d610302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 327484379 1250 327483129 327483157
    0xc170a0b1507050a0212031306080f090111031b1b0105040213180b09100f06050f06040e04020d080f0c01021902010c020c01050c01060f0306061403070e1317120a05061203030c 77
    0x120640c40352801c0d050b41e000f0309d00e660f5034810a007400981c1851245014206050b80d0341003408400d44580f840007100e070881c0c9a105000e02013001c1d102a1600e0b40030340940810b24080d105c183c10114541500b209010764001c032003a044ca14601640541141d000100c0c007a10300448100c0380f0041008a00e0966118180c00305851403000031b44212400c0b144003903030102a0b250755000602881c10700f4082c4860304501520811f14081c14010030000020008100034405c0c03103100f45034000c0041807030a032078450720b09641003521f42203201582030203034004845405c4905514602e00d403d0038414010070460912a4000d4042d024115004440680c0300d1201e200e12592030344000150217030a860304200842c080e482c0025860708061000850213804060300f8841c2e44081c60500516442c40521500000d21401401a82d030007864900c190790701040e0000c1c1d40d01004a070f030143e207001c058800303413103081c80b150100141d80e510700400001c0300520107180c20550080c03000850104220b00105000c11032250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327485629 1250 327484379 327484387
    0x303020c030a020d0807110709090201021203091020030601120e120d05011e0b090a030b0717220303090203070e04030f0801060201110901030c170a0b1507050a021203 73
    0x1844034038540c82000b19000680c0007038144e00096034424019600070b15146064a0207054035070310b0f107558800e40d004844c20543e480d807824003160b008000c0607000c204140a903a441e0b240101c80c02da02ea040c1c2d0750425501070700b801c8811004080b800c0507100d090788054443c500f540c1310300300116980701c4102d80380c0007000da46104112081400304000c9240c039020802e4195074010700c0352070038255001030384500c1c481c4041090f0130100010710380703500054a0300f003d280b0b40c8509941d00001c040100a50028081c05001024480d0561b40042119941400003e0340b5040e44c842c202d402e08280b44141028495088810190b000070b4801d81020327001500040403035a0300d541390b00e00f2031848002034400320041044445644000343d005002a401007107113000070005401d00c0048501c50b40b0450840d1410581d0300c154080e8003600460307428010701c00201e00000b903490444004002005c02445951040140148544441e84518101e0304910b13804406440d21501c949c4c00e1042e081500008a02c4900040c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 327486879 1250 327485629 327485647
    0x4030c080c03090310050106140a180b0a030e060c090618040c03150e010305061603020c100f0b03011e021e070515010518071202040503030f0d0c0c0b01050d030302 72
    0x14054280c1c292104095a501c05101c4101481d182000f04030842c91402d2100410081d40c11607103034039290703a039525025074440078040b0441e14607014940d415004510b4902c0803a8840030f42000e0000c80e15aa1070410070708003a038282c03c0e40c0d4182251001e550000801400c11391341884030103440340d845034a80c4141d80490701700009058620030780b50703400025910340c2c1200e0800000e0071640001d00701d0940d00307101c0d94156220b164482c08c0040428035005d040641c0c071303441c49100e941141c107a80845800d4484c800040c180d0b00d005801d00c10502084581400164a401e00d8184260750b107048c4d40440301d41d03010b070840d00303c51301a421031110050a100c908081035504000320b00140202ca22410152521105d0117404c400c80702c0040e040640070716661000820070103801200950004031900f0911260f00d00d410032000039114640040b82c02d400049100496190310348081c3c480c0070502c2034144a115070400b401c460440c4003110207001880341100411980c10413008050607607020b0303d8050700d801c2d014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 327488129 1250 327486879 327486893
    0x5042103020904110a0305011d0a02091305040b060118290903030a11070608090d0806030c030f0616030e030d050c090604030807051c0c030813050703030203032508010e04030c 77
    0x980c0f04c00200400028014612640c544a5140502144110303090b07000b15826044191400041611092070740c000340c6050b80f6560074038500310f181d0720f10f41c09201618107407a0140304c0354415038005003c150300749284408180c2c0558407038140c1c0c0d015940d04902e42c1d00300000c1601044600611130700302104020b254a19101400202640146903c80a01241c00600e182c0e14164041e4803034401c102d02c800c00d1000030240801c3c1c0810402440c40c01d80c0c15a260310300083e04000d03103240155450702ca041c07507000344403502041d0148145420840c40103484c04603102903056441c00740b0000e2103038004000384942245154230158009041c1d0044a0134414024046081a84180c01c01d40e80d90001041c89400c0110400807c0f0038001c8a40380241045000e6102038100039442d40003c0520428000042c0050006100c240d0440d03084412900c40c1552810003035101d600c1600e018281000c101600d99601c0310601c2400c490301141d5480610580c41c08001198200001d0012000c02004407048030120b100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 327489379 1250 327488129 327488141
    0xa0e21031201060e01020a02010e120f0106180501092d110720030705240906070303060611190308150d060f140411041116030804120305042103020904 66
    0x407a0041e20300d9418224007414500585108604641c0910084030041c0d07440100e0f041900c40c252441e54000c9003c480d41420b1515004c03080b02558a40340f800a85495902601006407400203410821a40c8805846d0f050701c0000c3d80d4910342e581d0403086044020190703405000c00001e880030000d0a200ba9161030302d810b500440059803d125100c0030041803100c184000c810292084000300721a5241c080850000700c9440c1c035840c008445005084c440c0c40099080741d040d00700007440c455403100c4c145400342c000c0c40140228000101030500c0c180e0100e90014601e403c0c1c112000040700700c0c0030142c0d1704a404d035030000c200c0441c0c2d40c15a007031101c01d921068004510288071b00804544d8480042855084950089690b03c840209805120105060803181c3c0668101030780c0200310b800322032042020038490b504440800d154032045507414181e1003684580298801c403500e0b4803213004075204400b5500b0a8070702501d0541d01c2280d100880007103c0b0542d458080900300541082103080002d0200c0316 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 327490629 1250 327489379 327489397
    0x80307050415260f0103120e03031b0c0d1a04060603020d0c0819020612090a020a080c03060109142a0c030d1815050705091c1203020a0e2103 62
    0x2140e10700c02980426a4000e05150030800f0b021502c0d51520b00001a126441840007502580c4403900001c030b858403030090f0301d0040f100602129078802e00207403480c003064001910310845004900e45c83c0f0302032924035540c1c0046a00585240c20080703001c851041001c10150003250205d640760000801a00c03110f04000c4080d0141001640e00b510b420502801d044040242d071202c0b10420300b0840050303a0386030558501c841103010032400ca41c0c44040740b87c42d0454040c00a98407100000340020106000288171107148020b4066902d1640c3c1c0380340d85400d130b410f040403c1d140300c3d8042c0b0001e02c07081c1080f841290804034407070a010012030f841984105603800420f9001290300001080130032000540a05115800760040c110305201407902ca40521308e5100700290103a54456002c038510318428800d031a01864014800e42c1e1002400100700f0f080e85414500710b40502c2000203003501d060103032080d160001d03900d03125042c000d0341000401400907012000c0c4160301c1c1c40302e8100f101c100ba0402c040c1c80030350 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 327491879 1250 327490629 327490637
    0x216030c060e072d090203090a0507060c030903060f14090a02011b0f0b07030209040c0512060a03121b12030617011b0e040b090702210f07080307050415 67
    0x55107040030020745030003034407040312a0f200038810003c3c422108084052000342d4200d42e20b01c02070550002100080301d034042d083c65400842404810345000c580c2031827180c8030700d080741c2003e503440e1010b450040405002601054002c0d00400100740c0e15089498140c25003080007400c040d105000812011054400003074640c00944145c1c11940c0100d0801d02c6100070004000c040f12140d5101050207035401c4008090f1002e00c80400c1015000c1d8059454500006000340480300c0e00c8070340182580c020600380c5c407201c11440d000c41c5403400d0041c0020203903034024003910004181c51409031046407000602552900d10b542c500c0000c03540c00306441038400d01e19070380854400d2412940e2100b560303580494060030f902d825120000d04120315460760418940c0c1c20034071030313080450300050b0042c0f484602481c1c0107a80138040003401740c0d0103e16109880541e4421800d005284d4011014038091021441010841040081d0109001e20060740c1d1040b002d01e00689440c1d180c8004002c50000200380e00041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 327493129 1250 327491879 327491897
    0x30f07030e0a23030c0d0f02120609010212011211040b03150117070b0a02061302060903030c010c0318080702130b0a0303020709140919050115061107080a050607050c01021603 77
    0x70001d80200600c3c8414220024000c2880d46000100140300c1088000c00c0d252580c0700840464940c45240b1010210407400d84000f0700c4c000c000907001c0c0d4030035402d10a5500d0000d002040d0f20040c40341002d03006421901d440ca00002070f0b030a00000b0102c45000075030504c923203020945003200701111030f40030740440a08034a100a6a0022504c0c081081c2c1210180038014460300b2000f641c00600d107580105280d03c91071200340c40d800440d07038500c1500c110035098040003480440d000015040b0403030035019680e01f0040130070040789102c500b001c00303c0c0c000e0400300300b045060b0242c5007443c1c0d0b101140040400029002c11100000380207403909134030840150f000340d84204400c3c078180c0b10f0004011080c5640120624181c031076a500c82031a22803200d8a40c802030020030a1210941c0040081980c1c4841c8000c07603a224071019000d44583d046c0c07c0300d58410888042400c80c00414015035103584400100000e8a8820003910380c0c1d040500e10180b19036081c030900610480780500303410f00b41c1c003d44a035115 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 327494379 1250 327493129 327493169
    0x21020d09060b030d0c1a06060729010e090703030302090604080a0f1e0f0323130e180c0105070f0c06030906050f0c03010504020a030b09040b07110f030f07030e0a 71
    0x181a21152132030280191a03079820b02003580c0400308180c0c1030010f6076902c402c0c1c0e5000e00160f0035001c0c440001d048001c800000110080c0364444e0700680203960460744d01d260384d80b0065401c40c44401c4585610079081203038100002806900600172001c002030040d414035848200c801c7c41c0640f4840c055440f400c0c01c9010005100060241c500790142d02c1c69424550b0009880c1c1c109043d0704c0503401401c01640460841d010500c0074551100a002240250f54414041040d1402013126000d00421541c5540c04035003000001080892500071f02009060029981c3e4019201c0313801c8030009490740c4403924541c10006030001111800b80490707440001e02102c0c641460011144000c012040701c140340d00a00514810100c02d4a045800032500560b07910b050100c120007409159601580121032101030100700a64004080d115603a9076039150300300041c44000c25070301c2100703000440454008002c0442201c49880003000780c10f029040c440518141e0002040d00b8022a90064030709604001481d00303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 327495629 1250 327494379 327494383
    0xc0501060e1f0608150f0d02040f06060318020a120203070b043506010302090a09060e210313020108330a060906020c0402070507170303040b06010305010621020d09060b03 75
    0x405040c075850000628580080e4291203000300c0340317540b44101c210350003180c0247d031215042e0041d1035002e4000d001e0303000290040c0740030b09114040d20340440c1c10b02d103511f01c8a804210001d460300b80c004004490003841c011031913105500d00b41003030340c0500072110301103a031482e454010402800070050703c0010800710140c03480704c83d400d520210200d05600007910100c0d500040c0c6517064a40456900505032141c8031207078010216484002c00392800c0a000702c1f9820000325107100d0102080701e1042d4605a0b412400f80c41d407000700d40030ba45954540c030002c4095442003250ba54840a0080c08000003010816080030140040c002c1c0e80700314901003121011030501c89100001000d00d401c01e03160040c10044065265250000a030b40910340c0407613a403043c0a002c00c003007c010101804c080201c100c0d0b14a5680d103950007120150f44841c80600441c141394800c0c82814121156981c84c1c00d2540c0c10501ca02850b605001030b8031204540034014035101c22751038469050303a14813500c00000c5000380c0009040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 327496879 1250 327495629 327495691
    0x3030f0610050405060a1103041203121a060a0f02031303061a010503100512070302190906080601030206070618050d050d0e0f0d0f050f0301061110110a0c0501060e 72
    0x442049010f0200304001e48425095079000646070804640070020b800c1854a980115400500346100c110f0a8409158000d4800030800903c280e040c0005d00380c0d803d2080b0b14002400d00c6640204003040343c260220302c94404005448440d1040d0392419a040e01135a040404035002070795800e998420701c0c200380c40c210046011541d400e003080f5046207000030004840340701030701c2034901411404220800d101000e2200001071a4002d2000c0d00f200074108000c1d049180328003c41c405207180c54804030385d0520006189040320381c002d103005e11308803055032604090301003551900b10040c2c0e0420001c00082043c0111802c02c1100d5803400e8480e40f2030703040107040e41c84580c0e80d407246e40c22605e1100c0d101c1102050701e680e0783c003480c1002c07200080351120884d050310a0101044040741c0c08400803d81da81d2200e00101d2030000030088540c00c03040f0400c0303c0110350b20041c8403200a0003c01c24803800307500038440032000c1c40c054000028101c5d0b0b01d11681040c02c0d07086800701c032481e6001c2100c0003540c200891003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 327498129 1250 327496879 327496909
    0xe0603130b2e0e062b0215030106021e0114010501140d1a01020c010810050108060d060204080102040510030b0a030b0604091a0604061a1c1d0c011e05030a050402040603020303030f06 80
    0x2c80625561744035024624444515108515882544207549880120001074400c03041c00076070344e6940d080d0003501e5188440f150000000c0305008150400d0741401110250800e50084608991a100c01514100305100044140da84144000c010448042c407401c6482c10243c0c040c00e0640c414407000a051101c84074011f0b040c0b001c40024400760070a00000041031301c0085c04e1100060325004001841e070a80c030f00000345043d000180c00700c3c0e0071006401034801c03104280d50070b0303054811306101078041d50108040c140d00541d242608001140c61140c8540c0c001601520004d210b03c01c90300c8a0000a0a40301c0e0408010b088800f40305260030544100d6004081c04001500c18401c2c8502942840c810700312450440305c880400ca803a40a034039032114800c82001c808d840107001c4101030898480d106807030820b020803204084000c0b02c1e400d040c0d695103003940c6582d91074510340da0401c082c0c00404014100f603070400d544640120050b2801c200441c000c091400c8803085520b002c0c010082084410050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 327499379 1250 327498129 327498139
    0x30c0b06010302121308090901090c1715041a04060f050a0902090a030b0601120504050c100503010f0909080c01060f171203061309080a0f0e0603130b2e0e06 69
    0x1d031303806501d41e1a01640d0130000c0e40d8513076040740c081802c1905680c0155910650300900c2c0000015031090030f607020000c02e40d401d0300e03110000082c50320390040c3c46034100e4480c60302c510590741400e294505980724200009030b0307020807841031200c0300c08030f81100c1030303500081003500420300e0500c010300c2d111011100070b19240c0c20070743c0b4100540005c20342011603844024040d104900c0400e03641c2e0300034540600220f0210200b0040c602e03140c18580d03954100034460303078040c40301500a01d505601c1502124166204100030344070480c41c1c50307007080051103943c000740c4140d0701c00d010241001b1801c0c000c4200619102030856184c40c00c1c106000c001e2500c541251005070f2080c0e240f44045c4000d502a01da00040441d902072081031140e5511020381801c4c1c4008019000009152100c02d4101d1200c91620640340c1d151a0320079840000d0bc1130511054492403613501c0700384546400a0482001c00e5808220340c226180384900104c110340d00210003032064414515941014005212003d2003d60b020b241266 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 327500629 1250 327499379 327499387
    0x3070513090b010912062a0e040606140c030c060c040f090e0607030209060d0501090c031503050c190b031e0a0507170603070315091103030304051b0103090f030c0b06010302 76
    0xe071030500d2905c240103441e0074030501c040922a140e4401140700d5482c48208820860032014407180b007000010307110118140c1c2101c180c00f403d00b4816127041c1c0d60b05441d0105881b42007094036441e50059410000702e44005c01800d00150030a100d070600984542803007607200e0b420103440380340c100b00c47c2e00301d0b5900ca17140401e0340e0200100010910b400641900f80103035551009404210b05114110f0b840d8070701400c0c03200010f024166940880d0114210340c1c1c00b080084d00c02c0d082d0401840451001408a5000040240c0380e881c1411801849075803d400c0150034954038403028030140c10403a208007801c1d08116900010140c041c0156500a80d5108104024039020324054400f1400880000b0381d60310749000541c1c503880410070100036542080328401d0000c80355075880c0c003410700300b082101e002c1c0d000c804007491400c000080e2801603a00c1005404990140074a007248000c058041604054a5a010a010a41c01c24180c0007140c000e80e0389a40d504020b080135914820058506410548100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 327501879 1250 327500629 327500651
    0x50a0b041119060f05090d1101080c07020a1a0405090106050703080a060e0a0e1002040e1f150e030115120b071e080411090f010e0108060c0703080603070b0307051309 73
    0xb0940e01c0c01e541c0c50b070074031021040000500316120301031a00c0042d00400d00d00c2d034410900005100030301141c00c0c240c1e2548403641d01c00d40c0000302e40c06a041c1c001c3d007101031001b080c003800010703510104407130b1523207480349040c640c2e5240029047d2500b0303440b0a010a800103048024940d10241c03140c0c0c0701c0795800b4280092882d1000100b85c004004024104e45a62080d5091400c0d0b0144506080402c141c01c046d9119078441ca440300c00c03400141c0c0c050f255010200d2072009580c650064900860750704014141c0c841e404d402068426000d101640d690555a41a44402442c0749a1000b400780c030a2003107500400d0b00c2450100d006200140140c414842c561601042d490103100c6142c0b03003111185041403490f19203203881008078032070b11289a401601e103401c104000344113154142c100d441202c0c1005459907600e04481d101e0b4010368400400b40700800005010900030605250008806030403212240e5072041c03010000c4d0400e58001c400103030001b035205007507441a044a000f401d074042d000c0100742560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 327503129 1250 327501879 327501919
    0x30e0a0c140103110a0e0102010b0a05010c0b04060b06031501030b010e03070515040e04030c0506010b07021c1e03050a09061707030507110a060204230a061b050a0b0411 74
    0x40c400c0415692600703061030000c0c1d01c43d4020200c0c0301c10b1102a1a22000402c0d17003d0054089410030a00661801032450354910308400000100c9006031030341c44292101e80c540c6000c03001c0041043e41c1d201d4a034070100d0416294140103502c12000104c2016095600720300041c1038032080e80c800d40c10807240d5200031107a91340205403a030450b1400c9484407200100c5514411041c00740b03900286000750035104010134180c008560030b1415103d00e0a0b40d401e607880f1849614039000e10304007c1c0d040444032000241003c0300c60094100540500729041a81c0d42780a04211010300741001140000d9020508644040c0c21440f00380180c9914103101c000d5100003158800032400083c407420030140c513030001c0b51400303000f1a01000312908031710540d864484107044c172801952051040b803840540c2c0103a56900e40078107092019840500601207950603203059801c1340c3c8603120050850488803d100e082000580c10401601554400c9041c11070030b10f06814200b2035a504082c0250003a0030841e4400301c16801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 327504379 1250 327503129 327503153
    0x503070314070e0907230703021e101136040606050d0f2c1501030816240b040507020a050319050913050a2405090c0705030f0703030e0a 60
    0x1564000709a1756036170f000301e807500020856058a214801946070124541c00300401030b0b02e000c3d408807602d03c0c0c0d040a00c260a28004020081150060000700e031442c02550020f0310400c1c11840c4a504000c20340d4907189030b0207c52911200805640504c1410fa244405c52540d04040704990403c6240d180c40380c0a4818030440700003094040d65642c0c2a1102103540d8460310101480e510000c0100c4800c5125481e041406550508c40c1d1054105500070700c40d0850100f81666480703c031550402d00c903240301d2040c200400604459011088042c5502030090100d40d110500ca40a400b2401240241c24401210005000f8004540000580d500894070020880ea21503401010345010450800000c44050007001c21540d844030800a000c005c024040d0800f03409040c5040c42041517090f401c00320751032903c5440304040e000c078184104000d0703071800c2c200321907001c45a01003451620443d5a01d8504550010304040c03841c2d540400c1000038141e01d84202c0794692a01001011100c240c0e44409c0c08400c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 327505629 1250 327504379 327504407
    0x501200f0904020d1d0114012105150a0b09090c060318210711010e090a0e0a1707120804020312070213060602010e21040603090311030703050307031407 67
    0x1200040108003629181d04890440702032031810408010321286a903c0c0d40612550345c4913540c28030603000e4005652600c0c080c1203490a60000100c0903820300d40102d40d4050350000d484a008000701a042c07a101d41112600c600c1e42880001081a100f4041020500018000c00a01c0d800f072100c0c140e03551600300480707400041c0c0c0707046030004d00044001180780520b00c40c0040c1c0d180071018801204140d40d00c000e048114400d0b03800d0007100c907071400115499044024420382c0708542401168441003a684104003a9001c5c5003034038003200c1b054480c900401101c522042003040002049414808000d2005441044030300c2d01242d0b508040d000213944d284244488050301ca0f00081700c608558524407941b00380c00c8030583c144032403550742002034003c1a071400303104c60b40d0143c0d07601c4034580c184a040340000000d80040701428242807080c21802881c40b10b10450522500300826a01c4207810005415181d00ca40ea466a4a107070059006094031360180400c440e240c4120203104003e17401070401a0450 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 327506879 1250 327505629 327505657
    0x60b030108070807051315150e09010b1e1b03070c2402100b04091b082401170a0f0b0105030c0406031218150206041707030807050901031b0309050120 66
    0xb203a0281901e1f09822541c803400707210f021400000001a04045801079008044484407216aaa41d074000440d01c00c501c551940400b565503c0850071400d00e000e0540d08001965528400d9000f51902e455a44143c400307071401c1d0724440003003140f000e00f420710008802c2600307016440150b030424080d5507880000b081d44015034648500303514a032181d030f001c0c0702895000341038040c03150258046100404003038003c0714020b0040c03d06082d0400f00740a601e8510108005120700181c0c03a00454a001007210034906440b801444024404542c000142540d0b15005d51036455555141c441058034003040c004507240140e050500410208014581c108030321038160030303c00d42d084070048500314440b6458011b400442130400404d640154006001c501c11407107036101c0c00350b44804070b07041c0400d80100c950081c000740c00c0b58005800300380b00300040c08180c1c0041c1804100f4840b186030784034001d8202083c40c00040d50761034a40c42800800d0090000040d004039000c01c506401e120f9a80043c441c1e240e00075489 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 327508129 1250 327506879 327506891
    0x30a080c09041a0102161406160605240a0303090311130f091a040203031b030c07060e03060a050114010f050702060c1e0609070303030905030d060b0301080708070513 73
    0x4940800d08540030510010401c10280342c0b900d20301d0100c1d4800240d414018032800f0000032081c18500000400c0d6520801c002c400c9103c1601085100d50080280b041249a40006600001c2c958000c6c03501075818001c410390080d0307190540030181003107282c00728440c0f0300040007000801c0d0031035110010b50b504402c0d03403030324440321902141e000704025018403001460840461031402c41a8014070752240b02b840e20b0400c1c0302c590320080181c4101510b01070760540040145107a030809241d0500540c40c852802d403410b0402120701c860911045a010001040002c3c01003441c81c1380a201d1540c0c0200207050800c101d504000e40701140590700084641480088200074080c5400782c010f40702c403281e00030b100580c1d421940c281d40791915803c401d001c400078102c54080b07198480118520b4440d0642d02c006181c01e506d940c40c100d002d8030100310700307851a00040001c0c1460813141d02518016081d03400110303680e9454050058649181c07a0300c20031564000340420f100541c0c030f16110000003070501c0d0f004140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 327509379 1250 327508129 327508141
    0x20a030b090a06090b0604031502091c120807030213050f0a12081b03040e06370501110304030201091a1c15090902060a14040510031a0a0503030a08 65
    0x5040c0c40291079403004040040001c0d48060350071a8040e10b50081d000d1065150aa0038424640150b001c010101c8110b5001150380400369806803000b913030010728041c01c027848400c0000541c0c40c83d11040d6030300c0100d0161012843c1d0400c42c0a80c005119280440c5000d55400644185001c18007610b481002410514211130743d840101c580070780250b21001006a10078075008403d6401070343c0b024020700d819425003128000100c103a5080341e950b0000c1c4145651100700b0040300c1d4500728101882d240140e25542140310000c040702c0140001c1107048241760f800e0400141159101c20754101c0141d00c00c010900c0141da10004010444801400c05652310304036140381903e90141500e13005180401812018a801e01078005c0c5190307503225619454900c2e15504460706a801108019411420400849503040d01c20702d00640070341100c1111a0506403210005007040b07901d0341101c00000e8580d0b01d213400e11034071004101095542110f01d001714a1801c8042512400350000503414003074903500040d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 327510629 1250 327509379 327509381
    0x6090204020f0a080a0b0607082b020706051b0913110f03240103060605300a0b0909010c0206010b0703020316210e06221a0301080607020604030c0303020a03 69
    0x40c0703103014400e42ea51203424444004020f0401281c20480f0b05040c0985130249050190484d48041d400480d6140f4003000c140f51940c1000c0c919410b0202c0070340080b40e201c840001d80c03010700800c501c03c80c008030302030428400001801c000c0510b524440c82c0b0070000d0039110766445084403080e400c0f9242c0480c1c15020076040c004540954036010821800000030448082d003070140401c842c1e52480306061078401d0900c011001c490a6008150100c1d00800854407682008004d04401c242c4800c01da121907140c0402c02d80a40070242e070048140d684131505c3c5051450020b01071580110284020401da03965280c00a54602e010301c25103095020014002040c14428802c80e4648240705100c8c8501e54200c1c540200c8400321307808555001802c110101c3da0f1a841040c1499800c0300041a15041525000c0310b1606244000035000d500010440000b50b0f00c24500924410b2008000d01c40761250b16081e1010b0800600174450011900318104000000e5080541040300d01d0305881d0040c1c44000b0810264 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 327511879 1250 327510629 327510637
    0x60501051e0d05010801091208040804030215091003020c0f191211010203090c0405160c1e1502040314030301150c060b040e0f070815060904260703090e0103020105070609020402 78
    0x1002d01802c20001080510054210740700103407040701e0400d0ba03001008011100c18005850080205074200402c00140c0381c040712000c04c000c002c2070704500e042c2c8a40002144038125080b00c0d40800d4004c200400c68070f900340480c0d0029004e490191520b80305070172010b401c088045000802000394499101c107800d03c110007222100c0c0a40008541d02d0030410440c0383c0c0c0d034007051401c500c00c900700000202d50444c586140c0c44016600d40302e1039840040b07a42d45203801024a0020840b05511280050114034410400660703041d4103400140c1d51707030a60030081110a0101d800e170180342d0040004000c0000b040b0005507515010f490a107950003898546800070f850810120340e40f16042070115030038900301143c1a0504441036044441b071540d41c480075622030030100524040140d03c00001a02c0c0e00f40f40c04140e0f48503200341020600c0ca8140908211400d00035129078500520102d040030070160804207402c09045d00042800070356143d540001d04602c9014001050680c43e4510042151920740541d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 327513129 1250 327511879 327511897
    0x120f0d1a100e0307050a120f08090d0605060a12170304050c040f020a0e03011e1a030105090604170906040501030906110a030b04151202091b030708010315060501051e 73
    0x215600488000c004000400342c0c20001d110b0b00410700d00080c0d91612000b06012600505c1e020b403070340c00f41901e96079200040400d040c2d58034841004441045d942d03145500d12214414100001c450a14030240250304511340c00a02d00f14004081c07600c04940710700c40f244010801000166601e071780b2440d00032b080c820818a0143c001c0d007010709125030320307044c4d4016140d441d0650340ca41e6001007400c010182a118102031101c40c0c0c40c0d080c182019602101d40100c824941c003003107900d413002d080c0c002213800c41318126806503254001c2e4040c0700810034048045c1d01080000c080160800700000c000805a00c80c07842918185a5542803103c1001402d81180c940c41c201214120744801c403101001c0d01800e0f00c003403010310a41c500319118180d800324882100a60390700c1003240b0303131544190382030048421010b04043d0282c414440701d1140350103441c0080d8072a64a9035260f4416500d54504840001340303046288103083c0c14004240510b0341e11000ba030b105e4542d4821104000c1c100350003070300701d00d04c600524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 327514379 1250 327513129 327513139
    0x100b21100204090b0f0301060e0105010509010507050304091407020a0c0e0601230d0f02180d02030f0109080d0605100206041203112a1b09040201270305120f0d1a 71
    0x10003c0c0321030741a84030031000076050303420b0b01d42c10605104042c00c03601c0900490300790000c541d00500065110b000034101240e01070410600c0e00400782c07a82803541e003055005291542d2950410380014005818a90704490103000905103010a0303500c2102d034116500031005100c1040b0005081c0d070388624040306003400d988005440781040081a15042c0d03000003a5006c08504050b220710008442d17100300c5101240404c0c80104403450b410030064800241c0e41c00740e034544a034130505140c01c4420f114a1000510881d9903e039140c5c0d400c12840b095903da9840207201e40c00600c20000304540214403964420760000b07400c1610041c450054000744041c0b1a0288250320104441c07110b200200031121441d01e0a242d0001ca150619200395a1844001c1c110074403141169050b441e01c0c10308600c002d40061050420850b1044d0340c0c04100e41441110340c048605001c460010814484144042203c0c403c100302c3c00c500d0603100c60f180504034407031102c0c603255403652000485c414540100202d9900100181 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 327515629 1250 327514379 327514387
    0x503130b090105010f1502210f1201030605130b0a050402010219050303101509060c031209080712140708070c0e1014010e011e2d02100b211002 63
    0x10965000f0b0500740910f0300c2c107000b440c401080c0c034080d440e0348200c01c2415034002c14204014400d082e0131402c00b0581418100d505100041e20401ca08000d0310444a20545c904625032650419105584003d030400500c0d54817400900042002e0480c40c40c0c2c00714600c44042501d48a138030040340303491203107a0b0000c0c1c512061302c0b4050400c03002100450085a044003d44440c80d154003c4050b5064440305400210301c000104200341800350f441d0305801c46c004c1c1080404d01c514030300310400360351980c001203481e0f0a000030b0035001c1020009110880390111300d800108079150400c450442e20400304c0190040c800801c2e40750411107000803a501900400008003058206a4090400749906028003514050103002c000c05552044c1142208a40141c0d50700302c10054084034400c1e0380040031091010402d840e503061584c0350500e0750100306030084d68030040100010210080c24040c2e00b140c000c2d03030b10741044055201d030707541c103a00720031021324600541c8014640070001c24540a80550a401ca0318000310b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 327516879 1250 327515629 327515641
    0x3060a0503060c0717090d15060f0b0403020103150602061311040903030506120606061c0209030703050705040b040513080a020703060c020102030601030b01110a030305130609050a1205070f02010503130b 89
    0x83c094075102d4403030070f00c6002941c07172a41c02c01e5182c00380b00311040e04010b040124a0101310b00b50300d0500d00c2c2d040d2a100092050f195107040104900503007021004d01070006041003196407600c50f404802d500c900858040c03d041c500004e4890f4005044080c51080c800803a80a0058040b0b0110001c040203000300300340d4002d8503018001d4501110424800c0150b50000d42d5007010109109214920003041307940b900b9141d106101d4802c1c5000700c80074a5070350a001980d96030310108082006140548000c01c1f0481c640000c10040c0e490701c0b840039009904001c01d10403070b00c010b2600d5080d0950301181243c3c80341c8600030102c0c030300400d03580040c0003103041ca4500d544041c0c0660003503005203000e076018001900c10724015504c50320740d00a000c0c071680c080c00302c0c100824031941c0016003080c4d0b0b110b201c46601b10707603403103540981c0c410b003c2c156820703002440031608115000074010540c0340310f13081c017606010b401d4480705440410410044d050100010001c2e4122680c210035041c6284e00c11f0b0005850f080030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 327517985 1106 327516879 327516901
    0x220e0408030c030709091e110a2f070e01030b0604050f0601080a1107030809011802060a08090a080d0c020607020c060a030911031c2d0503060a050306 66
    0x54200840c03580b640b8014003682402003413620452007240c03000c00342104d2000030084480b5008000100c226500704042c984a40720f6028013204c000142b4200c0001b08402001c0c04002c0d006542000c40c00082d402d0000c0c0c10b80380900c180340301c141e40b0320f81444102c54040c3c032140003a801d0783c1e000907595803080c411568000e030390450100c1c107006203a40626a41d0030650b81203003c1100f080070071a403620244034171102c0a0310240d044005110070b4000c1182845100103200805c0070070310008100b0402042015840b0340d1201c484e55a4080c41c0448000505d031030030032038005018400c04125032510001c1c3e060f805e142c00829823440e0840f1141c0c1079004101201c0111400a8020010b007030350f55091160171401c2c500410006441400440c2c01000000d44880c01541810aa0114003c484c1c01b60403249031605107060941e50781d01c4060001e403000440da44000d50602c5004100281d07030400c = true := by decide +kernel

theorem cover : BRFrame.Cov 327338129 327517985 := by
  have h0 := BRFrame.cov_init 327338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 327338129 ≤ n) (h2 : n < 327517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
