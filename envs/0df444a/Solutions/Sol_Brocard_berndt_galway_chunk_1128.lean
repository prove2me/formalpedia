-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1128
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:21:57.029878+00:00
-- url     : https://prove2.me/submissions/4d9dbf48-bf52-46bd-8e9f-a5f0ef173504

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 202697841 ≤ n < 202877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 202699091 1250 202697841 202697867
    0x60201022118150f1302033d23070516080909010e270c040906020d021b06060306150d03091703040512030a0906110304080a1505060102010b01020303060d11130902010906 75
    0xc0c80c00300c1c007039034075026680144260740c0c01c1c03050b414040b5111110410401d60040356019030005000382c4101c449c62449110502c4410741809103000c02c02081d03005810703180b9101801f0501d1204048611380780c00c1d01c0c842e038199507500c00c41c81d500124591141014140c811074801101041903c00401c00d80148544c000344014554001103494005090035000394580c90b1160b000942010310070788800050360400540c40450850a4402800280f010802c2c1034110605902901550401c0741c0c0207a560700c480b0500f54018481c6090400806200e500ca081c020081100d000003440071041446880c0d42c040d12840d8403603d280b86d03408203100008011141c07075200070b48621407145c1ca41082a1410321000c1c02d9030806010a100c0060300c0001801141d080d9842028074400c5000c03160fa42000711034001d0b001030304580c94110b520801c0d9030000112500840b0032185545011142c0c9000080007a8443c00d05030400d600d102c2400103515030303801c1044c00324400d80301d83e54981c2d1a10402c82c0c0322456411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 202700341 1250 202699091 202699093
    0xa0b04110306091e01062301021513020607020303070f0c1a030f0106210f060609080610060809011d0d02071d010510052203060501060201022118150f130203 69
    0x194130b0100c1c1e03032880c8540d100b04401400890b40943d141c484014503040040820b144803142000e51100350380c10b002006c0e0305071224480351404c0c14600d8030320060320070300e1000a0158800050740b50030355404009607101c00e5440790b640a10104140340c848504600d1b40f1a008200c1284101100c0000081058900c40c03210303140904203580c80d018013100c2a05031240a40003803132480b0920178401507580541c0011650819010031841e191000043c000446544104015003104081c0460080052000811140d1501e40115562140b5108500401c880030202c0503000920041110100000c0740b41c5120803550340a455002da0b46043d8000035011009258103040c0405005005a140c200c201c108080000e14010b802d049000140c120801548800160f6003210360808204008031801858050901480294100340000781d59005055882499040c112038079800242181010300042640b8941001150707040c03080104404410700b41960200c078084d502d00d000030180649105452201036002d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 202701591 1250 202700341 202700353
    0x1303290606070f0b040c030803090c030709060e0412030e01020c0c0906030114160302071e0c050a0b0403020103020708070203071e0f06050a0f120509030901180b0301030f0606080a0b0411030609 85
    0x1613501030000784010000c81c0c00c460301c4140840400c84910182d44140101002000c000c0903810030545002425440b884015041140c24841000030f194140c0e0095030110586410442141c401d80c081c00c45822a42c400d9072001ca004a41c200d800964200c02200c00c2d00c10381d900d40c03611000e04d82a283c804012044000940001c190441e40c240043c50045502c0c0c40e0050401a0954507070b6841d140700c08001c80319107030201ca170009009802e003101d80180003c50f1003030911803902440118070f014a11002e41803590208000d0103010510b411240300715401410740305141c0d2601001000000c403100ca24421190b08500820b41c1180c039507034101554055240d150804007080000c442860701e920640042003415900044651a07038020240210510030196403500102c6c40014041038501e03039005040e00740356804120b400d040100b1070f811340b504a0100710f400c0c2013606000001c3c2c40e041d032142e0500c1c46503600c140284602c00d0025409203110f0520103c00406d26000c0580e0340c54241c410040070f4000c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 202702841 1250 202701591 202701593
    0x60f03030d02070c0b030649050c040c0801051002100203040f0b010e04081219090b0717011211031f0902040605041a01110109020d080d180f03051303290606070f 71
    0x712411815010403203058400401c450070f90703400c40002c1a40003400343c000c14230034810003409002e208200c580036141000030740c0040030024004541031103403074020300300d12040d901c03c68800e1003030341e18100c40075006541c1c81c20b141c5410650130a80100c1581e144010030700204589807a00001405075400600c0b043c10b2034460019080300c2c0c00d0181c81420b810b246c0156840380d40e22940a10344406004600010062922500152442c68020a450b6500008100602ca800e5002c00c070001d01c10303042202040d4003141f55001c00d01e080c001048041d400c0c0a4442c0402591120b0b0708442400b40c0300b520103100c01d43d662000d10040d100e0941c82d0a0580e111600c0352107140d482454101c2140301c26100224070178000c1c1d004a4042410380324140e52000002525007413000700350003400c03244906190180c03d2800661180744800c424000300608100002500301c06610780062101d01031a0054882e0342400074401c0002d0f0388002c211180044100540c00040f0585885415500c500da00108194004801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 202704091 1250 202702841 202702879
    0xc0c011103041415040e04030206041e0b010b0705010207081305040b0906100c02030c06070503120601080c0d0905010213080d030b06090d1e061b0e030a0f0b060f03030d02070c0b0306 80
    0x100325200d804c4282e060000207040c0800100c650300039402a005404c0904150401040070034441d4007900d841c2c8904c01d811400244201c02c4281100d0040800f10307140c80a524010340a4400c1c0900a00011004205c68480c0d4072402c159100300d9000f2a010081000b000c024002c0484040f16a5503010310900c807005000c60185481d51300552000b4190303900c1d5a61030700040d00c81d400002042c3c88503440400c0c801104402d9601141d0000824204601c4902c0c0010760f1404500c942120500560f4030741c40c103282007001c250180c50300c191003006034114458607142400d541e05505c01c1b1490000703081c14900501410013800300d41d0500000341080e411100503481d051002e45502d182c4041c10500c9004240104540b80f062031800102054401c4001060010040082c0322162000c1d2080e040b030721803000061032041001c800c1e1035015103a0b00c2c00f643c403040040d61922080d039441b82c05000c00565801d070812164002c2410520903004100d81503240d0803101d40130700049842da90000f008a04101200315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 202705341 1250 202704091 202704109
    0xe01140307031e05010b07060f0501030c0b0d06150804031d100e0d12030b030d082205150103050303160305010f0e060303040b040e0105040f020a0903031809020c0c0111030414 77
    0x541014076600c0f0703203100c0d04003012034109a008590780400851070303508100c8140610b442c40b1580301401d01c541d50441e00c0d6901c3c1c0d414144074030100c0031000140380c0d20002064010380001c2c200c0f004044c0f150b1107042c0029059003403c032022400120041c0d20081039141501c0740200c005805000c0411050004505440c510031000c00c196004032580c6100c0c002950f0071345851079813041a5004540035039060107161030700c8080100b080a0042c2c110070083c4903201070907115a0450080740300d00c10180c0710305055040038031450f1201000c03540c50340080b05004d0000011800b0b030300354080c02065000d41c80c2c400c504641c0b0a0007048211181c4003020000001040741c100c1e0403010003810340349403650341c13134400c4103e90080d4072540c0702aa91100422070303464944986002e0105c906001c1d40f400c010600000c041c0f88480c000181404044001201e03050100e400c9400500101c0c1411036072a00b61211076560389480c602010f00040300c65000001d040408005d6074125184003049010001100c0d0400a090f6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 202706591 1250 202705341 202705361
    0xb0603270106090f0209010e060c06070305060402070f2301090b0f0408220501020606010309230c1002060f1518060d0210030b0307090b0d140a0f030f0e0114030703 72
    0x5920382e08080340000c1d280c0304401000f0500100180e540d80340c4800074024440115010380309d650309000d0842104400324006512140501c3c00280695034800000d0080c01044400b422600c140d103607000c108400d02c1807610fa89954a0401d030203e0107499041c80c02c0c1c1d007007132200801c6841d0b4100403800000f003c40380b0540041c402e48000d401c28a501942c0c0310050710481c402404404101c0040110756018058070b5004a02841e0602c030404440d119186030407810034411a901c60b03d110400d180342000c2c40b03e03c0700f0f03040050100c1c030b00e210f402e88001d50780c2200ba01d941181032620404542401d8101c1244141d000d4041d00e02c140c0780e5100f11224403052801410103400c0000700308503500695800102031950302107618000380c0c48041701c05162030722000750040c0803a103180294030071850340e800840071511541b0690705100303141400c4945040c020f103020001d000303400200d643ea082503002400c00a000085980d144e00040c0d26400440e9801a209407004c9041c50800202d030106100c1c0d044002c0d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 202707841 1250 202706591 202706593
    0x1050609010c0c03060c120606170103120e060f0903120c1509160f06030b010201050411060f1309050f0705091e0f15030a06090603050712030c080c010b040b060327 72
    0x4680e05d803189003d59039400000000565400816501301c0030901c41d9101408261526026140700104103546403407060001501d010056011000218807803140d0483c4004060080358880c41503144005184e0841003059110740a041591968070b2100402c2c1c90480b0004002421400d080f0041c0544040002d0606001c1340224204001c0c1048014010001042880610448945400d000404903043c14a006045904110a120100d00c003c4080ba5201d4811038043d6070703a880d00c40071501e140c80b0f6448080240007000b400052004900c6e48281c3c4140d201385040e00300d0307a0b10351400f1903440c89646100340d40100702000001c580040140300103080b071350152440021240150004940b030150b00b80c040e00e1801d00004021130040c450040c0402000802c0041c4816410340c1e0b036032900d620850181c908414015010309084c10320030520000d4440d00140100d640d402c01d40c52246c0601034081401e80986d045c81403070300444c14041c4c00c60348036919130920340c1100d808445001c1d0302c4580c81e000041d40c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 202709091 1250 202707841 202707863
    0xf031b0405040503040f12020f0d0f020405100e150906011407150f090609020a061103030408030a1d0a0b07210b01110706030504110105040b0a050307180605030a050f01050609010c 79
    0x21b040032194010003403c12244054a4403443d0700c104000c3c412000e020038001d55500b4102000500100061082d440c0d04560204c0c040c0d4803840440c02c88011030707104004108c41d403c00c0c0314020844800384c5c090864142e4684040c0e82e42d1800648089030010b80d0103c0008007008084040b44039894024070300fa034410004102c0c21454450031054600401080d2801980c0300360307000852401d24029001811541401c40415030400501500c034000180084c20400b400800501e5500b021b0b40100801d070040d0340d10406850003034010740e585400300c0004a59000004000c1040c05001d001c1205c0000d000e02c140ca00769002026040000c1c0c0f020a03682c50500c40d40e40010111000184514000340840d603400091f01e1a1134240540d9545100c4000360521004000a1058160481c200c800e654104c1c00c089949407546401203451540e41c10a030035184091a5011510715030180042d40140c2c00d9150921a0b070f2194805484600428480e455000b80c04000c0c114055015082980c102402282c03080c103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 202710341 1250 202709091 202709099
    0x311060f0d02030604151406030405070e090708010606020327030a150c0305012c090703020402030f010509070f0504091505101e08100302150c010e07050f031b040504050304 76
    0x1110381009600704030081c1c011040040300e040034440c2100308014100c0702950b4034a0618101150800c80c0c05103402188004009014400e007003201c500100300210441c5124a802944103440b03020500400740340b5400c022000545620010544030390305001070a1b060442c3d84031484000303c0115011131038150040c07074a040c1c04074103100e14480c07240b030742010081401643d0780720003800c850050300480304040ca6141035000c065000204c0d03000c180599107109205450b10120310746000007a60009620074000000c0094040220301028125481035409151039214290251001c1c00302002900004070300b40030420117049190071802500f4440b0500c410640c0c4c80740040307212000300103400808610414032041d070100c00724100600381c1310103241120403400e01c10700c50142d60f0f0b01d501c40a4840c900f21207d107039032040c6500c2114841007140c0d000300460507000e04110780f95601031040e135201e80000f8410301500e0401080c400130900b5809018400381101c402000010040503105980c64401400086 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 202711591 1250 202710341 202710367
    0x612270712030e130e121303020f0d060c0f080c0703080406050a02160503090f0105121306020c030a08150102010c1e050c07090b04051003020907030911032d0610031106 74
    0x1c4040980404c0200d001034050300d40e1880c008503940c10120522082100c1c0c076600c80400603007000d807541103074800c00700700780800001c440e158410805080c5514140403e1411038029000540400310380e201d40342c05907601003a40645008401c2c010b804220702400040001d81c01e503000c2030b400720080a0042c200700c100784d19021754151744001291103510005441903d803500d0149078160708001d01e4601e160040d0381c41450780c1c000e8082e040d9090759030583c00400410a80c1e8064900445c6041c1c100c81d111640c0d07150007418244250347e202004e46100031400c105504c180190a43b01080d61100140030301049400a04c104094504804105080c07000d1504480c5c1440002e000381650320005c148200e41004200840d000a00f900c084080803010400050316030341d21302d5510040340c0c00c0c0018000c0950601e0042d18031507074042070b0306000b0004545180c0500c1c00c124140030301506100540360220b400403d548032416184181000ea60300c0c001c0000480c04060200d01c0c8001500312428044600a04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 202712841 1250 202711591 202711609
    0xa0b04051c050d05060a06120c0201180b190c0203040303080402030313060801080c0609010f1d0a06020d0e030c0a150203070c0603092f01030b030307020612270712030e 74
    0x1000050300000ea600740066040c044c041e08004215410740c506440c00340b020b04024000d19443c41680c3d00c42c03c001c0b80b03590007944103001480d0342907004421083c161524100c1c102d0708840c4d65800f043c1070b0085c02e0710015184925528812117400441c03606045071001d032903044004204a03403510040010090000d4040c1862004052070740310a02294104203205040040e03000881c0c0c000c0005100710b02d0b441c0c2e44840003e00382003032802c0c01c0c4210303060700d060321701c02c48601c464a40e00300040110000d502a40001c507807480d0000340c0c0e13038070b680c480201d401c0603200c114034980190700401c0240c06106000f4007800c0e541060070140103c0e45890019a103651303550502e6444100030a0b511200d8006000007645010445000182451440c02060303240103240503135074441c1810941c0c0c1d8640f90321961010412602072030f800803c041c0d125134402071a64061503084807203018036955a40e40c2003010041161714012950508060005241441c40a1003030026100080e42001410700c0340211700d449034002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 202714091 1250 202712841 202712893
    0xb04020f0304030813050715020118030806040b180a020a1107060201150603290402070503041203110d09030605040f0605100302011d030c0613180b04110304050a0b0405 74
    0x9050744920300340c2005001c040006100401c114000314900f4000f07131000c54030f40e066aa0034120a060884120b1040780100300b40350103842801488072020013456040191184624000c8505203c01d00503c0d041c007012071070540fa003000c25802c0001080b500e9a5030f4029200103265850585040c4100510042c580301459001c1c502607503441c45403040240c0c100403c2c90103084a07040070301044160350519600c0ca140c0d80498426080c050a12140540e5a601283c4240350070900326a150740e1500c2903049840c1c40c41104501042d960300d040312400c5000b02d00c014501e0f80c503481c0c044010340341d91180310107080028004c40e0402801a0751400060300382c8680350242140700404d0601d5402e520000d0081c4c16160b00681031181d40a882640c0c0d036800003108140050241e400036120500421800003000882c0c02030f00d440c00d80d9540313200c070800c904e511503003a4960031542480002801c0c00304200601c002e40d000740c02a00683c007160b0118000e0362070b2640003440348046541c007412910400101c3c1841d804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 202715341 1250 202714091 202714117
    0x11811090106080603150403050405040f060e0a0b01021c12050703090215250c0b040b0a0306140105160515070507020f0405090607080a06080703080405040510030201080117010b0402 80
    0x440a2500304050081d01421003030800f039503241081c01c0000d0b039032885481418100440e80002408141c81241070703030010000a44180000300311101030102500250041c0f00e014000c407000501d907110107004000c0e145c034040e0040d0140041c07a06a50740203000441780881800906601c02c000c60410b03108007881004030395400a4449110310410210548500c2c0c2c0900030701013880b5418601c8103e0300350040c0626100311104400e000d030318144060b41102c1c1d0200149100c041000903d80040c0c0004109030462503500b04049070701e031800440500c0090345c1c0c00303000880510480c0030b60300c2604456402c49000304102c4541c1e2088400180103045c00301c90307050010700e0110b400e07030842c107081007035148440040b501030007146400da044c4ca0351550002c00c0301080080c0017011859008842e404480581416000d48141e2074503400c0c48100c60b4041c0c49041d02071071801d40007a404003401246003094944c140d680b4040780c0d2130081880901c1d41c001b64420551b55881980b0030155495100500304505004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 202716591 1250 202715341 202715363
    0x4030303051e010807060e12060f06031606050a0522080c01170c070f020117010803042301020703060e10090b011e0602030a0302030a140f1012051b030118 68
    0x141c0700541102542c010714401e1494100601481c1008503204095031014a840d60303c540a0b00001264903460701100d881c039000300003c0c000341d4100303c188903200b101d094080701c1c110001ca80c000015401d03a40710b5000083c0040c030103840c00742d1295000b880301510482d00a0b0500d201c24070f1101c142030165100b101030381d00c1801c0c50419946c1003243c0000520701d400c44220640340032004602d107813050000c01801001040010403c40e80130f13025042d060001ea81c410780e03556845405c0d050b501d80c03240c05854490703c0c855030120001c1400b02d40403045004180d001d800e840749182c1d180400b0b000700d0707108031090b4081d40303100c012a65000d00c51a039201c4e0041d00a030740254900b1904800003106100b83c0c02aa21000ca0203016994001048a107544090b00c2c00594030b0344d4980c202d60082c458101c201d0209420f8001b840f80c40c800041149001e61840f00e54000195540d12100c8041e03180008010016000314440760005000c801d1480301c401d030043d0001c2741d861951030108100c40d40c07204084070200520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 202717841 1250 202716591 202716601
    0x3210305011a040306090212121e0301060c02011107081207020a0e130f1b06030c0306051c2a060c050d08060f09040501090506070e1f050a0f0905060403030305 70
    0x940902070040c160707a0081c1200250b0303105006418861800040c1c45140c84518030f40442d12841c2d07200500401c0388040c2c032107042190a56264940c081055950302030f00038103140c04884c0c14002228104c4245446004440d00030383c0c01500d2040e5414030000c40f07401030780c10004070800c0901003d64a607460700c0480d42d0720344061042042c0340580e9007220358515071540c204500b141c1d03030448404a441e0031500b445154425485c0000c620038500380070500300000880c0c0000c0c0190103030400c4c00b54051944052140300d8803070f03060262942e84d80380c1200c41c4040d000b044401081001103e80070000d00d100c960036910131440c2d10316010030603a903c00400101082c59410910405000c1921200c88615215205041480c0042c032044d103010801807241305504042404c10500750301c0211002c1c0d105041c1c0314030f45440a030140c80e00c01d07611183c0d4000d0000040b0001d040e1884048003890400907184c0d6030400441790300488a081c1c0039007585090204154000c1840ea07500f502801c001d44c4a0380e0b0101c1c0d24500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 202719091 1250 202717841 202717847
    0xe220507081509060f0705070c050604030b0f1503190201050c0d11160602060402120c03100f0c05030c030c090a030f06060303110105041a090a020d080309011b12090201090321 77
    0x500780d0401e600a0014048800704a00da500d400142502e01a0384480140c28900c608820039840ac607400540014000208245d400c8076a125800d4100c05102950720054030740d11845a158083d9810b070010b2140b5151017490003101140c550041c5030440c14040356901d40d0385071100074910b00001c9100841104035003075003004842e03002d02d480c400d000c51340d40c80c0c120040d45d500c1c00600028814405c41d0902003038010204813080040310000c003200c010803541300e40302d4000c12200814900090420081114040c025011680517a02541005185549640310f01446407c00a40d5507481aa980030010100d80521044d503011350207080002100c1d8618540a44182c800010104041e4140020000451000c03030f48800a0354003032180201c3ca0741c0344a07a490070848040002580328100c03001c0e481c2032045d4603004c1d505c17410b20701e4020000b4407a43c1c00e15400081500c0140000141c0c05100c008910080383c1107020842e20605200196940700c0e6180303203180d07d01000700e590001c4041d11030300074154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202720341 1250 202719091 202719133
    0x3070e191406070512091201020a0c02031204080a060207080f0403060f1b0f1805030304080a0c050910090209130f0209010201050f131b031416050a0e22050708 70
    0x50450b6681d15151003941c6058440c4410001c0c80e18108001ca100006a106e070038403881810500c000840d1b4494003140d0260083c4108401a8064811f4088000d035414803c411102690040d00013000940f4065031418041e510514003103581c1102401100001c2940501070800381d403103503c0104004a68100c08800c45d506182c07400681c4440381c4081d90f0954003e02051145001841e00090324038001c40000d442140c1640841d805110000e4001100940402c1c6001d00d98801c0414110031035903201045000c070070a817031906003c0498a000c1110072416401421000b001600203101c00500005100488101c40006640d00b030b00060010441e44e4207104a81d48003d0f050841000d5003044c505105403080f030013400130418201c403070717848105404210b0000d00171680b140031190020459540641c9514414034462004000402c0204052070680c030050151201c2d50715824066450300907284d0501c501488000304140b8440e00c6201240c800d01c10b51024060041c000c0ac4422a40c2c2c4122410f49 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202721591 1250 202720341 202720379
    0x4021218030a080601030203060420091314070c0f02060d090b0708070e04180512041e141309061d0f060f07180e04030f08012903070e19 60
    0x7420411080c2c65040e04500c05903040b403c01e1800580341d94450010600821400304a9001010410180b0f8058140c110003411441000c1d030355507101c01a05004001039a010b807034184030181e4510006410709200740400d0140740e004085241c8031002540104130503900c003a419801071074903448413030f091190000920740c1203105403800381e41a1a18040090400001166441c81591203441c0b0784501d144003207034900311315082000d071030440e120441904000e602900c0b882410210b8004203030781200420385014100c030245d01c00c0ba407040c1c00d0b140c10041d08000c0990310b031071116070701c0d018071003c250781e4424007090050100e0200e0040b60a4142540340400348000c040c686c0d0300c02410007003841d04e41803010b070704400142480e125099603528034241c1030b0919040300040e05007040c01c110a0640c0614644410003c039107801d041d607600c070340240d02c1a035030665036551501450141c0e5041c40d080200150350021403450701030381c0c41c0d140c000010025a02c00c1c00c240d901505050741030000301507800110f8211 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202722841 1250 202721591 202721593
    0xf0f080c090f0903131509050d11010c170a11070506070c150c050610061409210106050a0902030a05070507410604120810050904050102070204021218 66
    0x5004100141c001d4030001c11980d086920307200407910814040060780d01120781e08100141450311381d0008455180c03120704c0315000510413400000c0c00d0400800e01c00a0315042140c0d045149120801500d041c0300782c04044420f0704540b081c0710039a43e0785401030b0010b0f1221b031f901c582c149198040031501c0e03c01c00d83c020030300c1048200704d0140001c02d40c43e1890100e50711000000a5000b803800103442034540300d90040d0060040da401c0181d070380311080381d4000341c991701d8503000c4881a103412004001d004002c882d903009020502c0712001200c880354141810701d5200c0010030344945903070216203d0091075200500c1d40342c010041c0501d011050081a43c0002a0310b045820b1486980b202c40006031a00129500080101b00808100d54803103016101800b2204034120342100c100004c80ea2841d007120300f59141e25401204104480c0300704007080c05058100c480b50403407802c02c000c22101d10802380086440799402c011741001600c507400a852210928001e50040c0e01c0d11070601d10324400403410b00906 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202724091 1250 202722841 202722853
    0x4122609060a030b030109081612020a170c010605120703170316080403020a02040203040c3215040f0b030105102109021207030c051201020c07030215130f0f08 70
    0x1541c1c072500140d4505202610340407030250f504a0219004118034100541148000604d0780c441400303040140300c1c40c07403250001316149068240100d03241d2600560007041489188009200806954040d1410150a000004040f9620400190300074074144280c003284e08503850400c1400321449000e44031000d1100e11a1851401c0e40e281140d0010314a41c580034050910082024180300b00500141d081d03024001315a20304042c1049c0341540c8440c41000e41070400f143d2494601d8032910303a90315032055011a5010801005020060300c0005090718074140d282c00c2c40001102c0060090001c003d00854445640d40c1d4142010310091510680d240020301c68181090f501c401602c80d0300f4600c800203103000103a49841807001529140c210103100d80f0f1807061100100a0203071180070f60f000c03188215440801c0d01040e01002c2c0c00e0f4010014104030355040a00e04001509083e03800005207040d880042e4a00072900d0300760314440c003254110510029100c3c40c1030207080380408903031016103684001018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202725341 1250 202724091 202724107
    0xb01110f0c0d031b05070e0622020d0e030304061d0a05210706020c011a0f06030a05060325031106121506190c0c050406050a030602030c041226 63
    0x364484107906030380d000c0d040451409080c10700c0b03444103c81c400141080b41884030424149250385503030340e014403012146a80c0c04114240761424a080703001e00c513100c99015140d4641c0c41c8400a405c4001508140c6445601c0b072003400c441440110b20231841024005400720b14201c86c41c207100e12500043e100d5a00046100010400004a00503410b0003540400408500c0111451480c002d40c0c234000c0090780045440c02138044190060070390000031406400c030444a40c001c000503240c0c15101d064001208101054054269401195000e078020302161300550b558800400c11005c0d042003580c5d00f40c52440700703008000d000c1485180e1070f00101c6095050145244000703040b45070261800d4011192002015019190030f41590856100f0641d4640d40c10542c40d400342c13242e00b440d1401c6461844c0540d012815280c507109940036190702a088414090859950701d00a42c0064491103c04409201c0000d9120a0a400030000391007144c6442c5003400b07940d51580741c40d0034112640e076187d50a0094003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202726591 1250 202725341 202725343
    0xe24030a180f081e040e25052203140f0f0c010503010e10090f0605030606040603030801050603070302070203010f020c0d080402010806010f12020409020712030204030209010302151308010b01110f 86
    0x30500903002050349a41d00c1c100c0000c1c580101c607144c1425100e050208000a00c84000755100b0310075120300301509084a0510711540c5500f01c0005007002140d4140040700442111032100c0c840c1d0401418202e442645984070001c00014ac1d0702c407080164030180300c45040140a004030f070700c6243c1280c0148007a021030300c0040c2542c041401a02400d034060400501d00070480c1350240028000d002082001192081c4072101a24450090a000e44640c0020402300d040c9441402d080b01c0e050b64491146900b031104000e640d6101071b143c0b1082580030300180c80540ea0a100e000e110100315000166201078000741c490820a06003a035a00b0704c000c4004001c0941d0300700c03083c0e1358481c10900c1c4c0840a4000c5800a6545080c40c0e401d00a0381c61000c100401c0615040d401856280d0291541c00381c061038442044081e407065010080d0042c0c1c55100400060400051101c10b010102010f2824104490100c40445015500010080c0c0d113070302251190756040a02c410340414118040c200c00c00208140d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202727841 1250 202726591 202726613
    0xd080606030a0c052b110f03010303030e100212010f09180809011715010810031509080702040e0c2b021203071e051c0c030e24030a18 59
    0x40110075031190f08141c0c000784a40201d03100194044600216401d1241614400307203100310601d09280d1a08503003160449503102a60326549080c035205203107030309550f401c40107054140d2100a0703a1290744103c1200c40d6160003e84411525505061000d615010801c40d881c1d500f644650011854044100048100f030f1490f03000c881e40040100350707a82680170040b20000107070060801c0f46480081801305818041002c030102980076601c00760703039403241c14403402c0640040c03100510354040d10070003600c80003140e041301c22003901a0003001d00b45601500401d0694641013030310384058001810000381403514600c61200d100c13000b18001d440149442001c2d1400d001010080d21480c2e0b44a140143d2a20400464044c0e907030287e441d203e01c1104c030024281882106404072100c0c092007005842c0b0201901c0c001c7c1c60189551740340c1d41862810740f0705440c04074039514215003000611140c0c020107601c1d0b81d000301d144a074180600307039680b5044940c402114010300c2400e012190343c00c0c541c00411201074071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202729091 1250 202727841 202727851
    0x309040903140403050304081e10090f080c0606120d0507020103150504062c0411010c060f020324090601021e070504091a0709180207030201021e04080d08060603 71
    0x400a1545020300381a41c4101203840c0c2e42d01c030940c001070b0100401c80084003070310440d075080e0b044484040513014030080145803941c90114940c08030603180070203110f0350406046640105106c0c10780e09010340b1a95520790002c03154450580c819406d1260f44e0600c0106201640d40220141c40329024000f001495031149142c083c1c1015200c051070719442c40328101840c000d10000b0030800116548540d542c400b16040030801450196000342a806550740b200308030b102d60f81c045400c000200c648001511500ca110b402a14419550114044464030500c0254055030b0004900706000c2412812140c008103400505402900c020080c4080d90b600007070443d9100703e106120400f889811140907241603184e0b80440c0d07000342000400000d204403405d840d60020007548250245584480b01039030064803500c11020100002c11900c20603100740d50150031864401e1001501e0040e8000c410346080c2c070030b0801510b044000107010001c81c80304200101100703425003070001e51846c0200000301ca41c040202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202730341 1250 202729091 202729099
    0x904080a0f09080703050d08070801030c050d050a02090a05060a0512070932060a090902010e1903020301051e0106090b09040b0a0b0d1d2b03110a0203030412050306030309 75
    0x78114190741d0007280450701600c550380803108502e070703203041c00e5a80b070810010b0b08011074101c0e804108414840c014581c140c07504107840001c014501014040c0c042ca9280050b21140078408407070b001a907800141500031091400c1c045814200700041002d41100307030f80302620801e18000c4400980703401140744c104440074440300240125008240296030108003040442e00e050314031a20800c4090005184d028031010340e800304034292502c0707000d8102d5030034040c0640800d444205407003803854a085494080c202110354581c6865a03076000c01c0c251602a00c1200010520740303520325250700b0b000401c5004003440e11f80b28a41501d84015030034103129221101d40280e0316480540d0f5a501d401a500c0010416804400e43d06c0355035598000c01809034242714801003c0c00312080d800a140000c2140c800303041002c01601c03841c0c154804078158000024800181601ca4070825120441b40f8042d00e02d01407507030050350350b900d094a0500c4e020006d591803031081c80300600901c160b0740c4000045d21440e8400351 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202731591 1250 202730341 202730357
    0x1050c06150307030203100f06050103020c031204060e070810050c090a0b070206040b120a0b010f0f03091109071107050306040b04230316060509060c0304081e0f0306010e0904080a 79
    0x201c00300e030504601d0740000e9018810902c0d0b500240140b035202d4988842141420405561544d00450603031041d6500039602e5030042c03110b41d4040c83e209420a41061040c50005404a001c2c02c4941c20450a948a60a03a03045806072603800e00703031401046d40c031140199040d032808c0c0344400020309148081c050802d071080c01080344001c64a403081290050202c0c402881e4460005501c06122020b00712a54503401d41030001c44540e03940205c0d80600704010301c1e1180500e02055010844c000c02e0489801d8030356042c1012a2a8aa2103401a003400303413490f90b603241e40204c448035105e451310307155500080c00707030b40030b4000c01001c203001d8254160019171014680003055282892a155500c040802c0c1400c2c2c000050450101443d0014106001307104102c184880d545200c84651640c10444840500000c100009000912000000c7c052802e102e2012011f90494007028189508403c03340074101030000107005440da081400c0200008040351016403074030305641c4005250040c120350301c051218070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202732841 1250 202731591 202731631
    0x90c1526010608070e04021602011206080616050f040e011a04030507060507050c0307080715020705030a03050a1119110d030e1003091505040614010617040602070f0c0801060501050c06 81
    0x10b17841301c0301103050050040d03448803080400346400134110603049012900760800600c8610550203400c003200c0c004030140115a5503111481c2140b41c1191020301004010010f058409220303202400251881a000f200f0f00c0d81001c0900e034200c40841e07040c4542c024140700801c002800068a0410b40700707140b5015454043c0d0f850414038154440200c5907060081050200b03601c0c0c00012481d04880e0030103800701583e100c020040c0c6e282c41090080e56015080340b1a000013082c0200004c1030200d00b180307404007940305540c14881c102101070300900c801c0e009058140c002d12211074880c1080010445084284640c250703005004514120401030081000003501032003903010b40d200e1440a50804a091390141900101800824040780c04030350746441c11084c000700101c0d0310040342c1a5031064a9505646c0003003d5100e07070031074005000f2138100783c00704031000002d15410a80840140300344074003051681070a908609403185a0003450401005202840c0d00080008202e6000380020120344619620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202734091 1250 202732841 202732847
    0x9060b070c120f05010e0f011d060c030606040f0e190506060306040b04020d090303050402030607091503020f0d02040603020912240606091017130312050a090c152601060807 76
    0x10703c00015229501e05107a88280c2d82c03001c60340110f807065010003000729001e2084560140e0011140d0a0203551141d00001d04104a0100458200600509050500356209031392462a41560030180c03085520780c06000c900e5890288003404145400000d004510708017000c900c0300c0c000102020322513a103418040e00d89495540c1140d0340020014818401d030005420302070060003041c1c1c1c040b0300a10070200003581142c0300c0c24400c0c00b4bc484414140d504018410021406074000c14801d8201d4042002607201000c0c0910003440100910b481c0540c4810961081206100360114411480e4018500901c201038080c0390161820320031400590716522003401140160040b100110f4119080e4805400600d403c040001415508108041c2c0c03c1d40d603402620b40645c1c00b00800602203010003501000c1340e031450b0000742e80a084144002840029a107410380921140d92004000d020032441c00700c002503010b10701e0048200120081a803040c5030444250442c001449140100801c40b404a8920b0388 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202735341 1250 202734091 202734113
    0x605180a080102180f0402071707110a1d0f10090207060212040b010513020c030f090d0c060f02070e01050307060c02010203040e15210a17090a09050109060b070c12 72
    0x101c0c5030007151142e403202610b412a150b1034000d244030b0390f59281503910a190900803110340e164090b080d400b4001c0040c1c030707a0b04190044402112644510b00700031142e62600112100184141100c0d09600e545040b1281201500508822070440022082001044064000c00700711840c0c1140103030348510605000b4020700458000c0c55100b0b03141d0040c00180400d03400d85c0c5041e581c048840d0030005038003071410812840741a803c006160001e10440011050b58409050660400751400d20082c580b40d5900c1c2008415400c0034011640241000f8205903041007004003401c1c4040c038a034401e50401c00021340e60702c0b03144076440070400e440710380d001164801d00c140c030002e150010f0002414281138403240783c14030300030368940d0080c3c801c0182c1c0301341c45003481001c16625107620090500d405a5440319400d0800c10328078418107007401c0150b11101d440e00c0c2d8059000308001000001c140d4108600401030b2803250740000e1070242e051084a000c5100b0300f1968080f03e000281d03290ba200e070685070400d0141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202736591 1250 202735341 202735349
    0x21008042301090b150d12090306020c01020a0201060806040b0c0d14040b0a150305150a1b0e010e041a130b0d051006080303040305030f071b0f02010906050408282907090605180a 78
    0x2e00100f00b40940cc01c05401603c001c003501d4000744001e07a240d400c0c00d0f80d1240201c40c050048070314200490482e044d000000c04481d00020f002040070700000340d110b003400006550456001c01a6800c100b05251a40b142e400b01d01b940302c0d2581641440d584a4540e1414262100d01f91070400340081800d0b04440d511200c1c4580c0052440c0c0078441c240712000c0c141050f9440e085020a4038070003469124542445100f043c454044501003062451030140103201c8091040340d00216500c1d4001109680c80f0a0010200742c0b1500c0200070340401d080d8104103441c202c0d4000c4000394000c2c0b06200003e500001920b41c025141028508150b80c0c510701202c0c030464560008147c180018410b40034800c000241400060003030301e48443c400ea640320202c1ea00e111768400c010544c4c01c200344440b42c882c1400c0500c0f6104142c182104c00b520403544840000080080c28010b030343d20001070b54005680d50355070301da5111002d42002035200c0c2c13070110041d24a100d000810900081d0300c0f11846816540c1b08140f030050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202737841 1250 202736591 202736603
    0x102090a080a051203010e0109020a11010f060f12031413030b04030c0515010303020318030a14030a081303020d0807110f0d1b021008042301090b150d120903 69
    0x469981c20426403200c2011009031418007070740c40000512084d407411a412603c8034035418440782c1c64034803913200940100c0c440004228612310b2241000b4024001d416400d4565000003030100d00d0645a02c407080c0c0550303c00c0349102e052038001e5002c25080081d021300c1c5042001041d5917024486c0e42d2030404111078100a107105100010b020501d6801111904d002e44541c00f1224600c03004a050b842070b032400d12005005a04c02c010151031688100510082204040e044075000201a91810381c0ba0301c4c0586040c0884d440401c0041c945a486031007d0f401540a60400500074200d8034004d45624011250078244211103000c52009031103502030626100a01c0b0948040e90301e1103072510380300e00d01488400c1c000780020545164104038000041c2c03507194010301421503403c1100050380c0c4c900e802401590100a07883c4a04203070901404561000c0d800c0000000c1c40c0700c8507141403d103000c0c01510f0226041400c4040071340f95107032410001e03603a40e00034040103809009840d08844060262b00000c101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202739091 1250 202737841 202737859
    0x20c0709060e160c0b0105040f060504021c06210b1302060705010b0a3201030e100903020d1b06050c0c0312010f08031c05060a0902040b1b030405011d03010209 70
    0x800e0142c0c5041c0ca0040c040780364160b10644510034100c03441e03121000040d16140800e401002245400c1d884801e000400c5000803410399500d00000701240c0016401c28651b201d106c4104020020034420800a8004268103c0b503903400f000000402240380300f00101007100341e038003060010001842e400b894580c002c01c8140d69464600d841c034043d08140b00b200e4001c6003400004200c1490303001500e42006590300c15080c0c0041801034a80100ca440241c841c1450303a00d41003014102c07014004503091075440700010030960f07441d1400074546030001c0800020000e0005020500c3c41c1c44021603c2400d400003400f00d09038640c0070031054584a126611505840001201e688070214101300c94100d52004036078100b1103a45081e521385900c109090a0304140c01c4051100080030b2980c8015002580980143c14164071003001c1e004076130007900718840c0f0902c081240c458807a50004c8101d080d0301800c0145040a18000000c0c02405241d04445044150303a0306603601621300758103407150a0b40081c980c0d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202740341 1250 202739091 202739099
    0xf031e0c021e13150305030307091802040f0302010507030e040f09030e0312041a0c060421021516120903050913050f0610030f05010f06090515040306020c070906 71
    0x4a680c00c24128000c858807080303010b0000440048002400d0080c02c100c0910b8440c141c61402814420703960480100101c03070100c081041000a5841603d00b0344544c0c0300715080c020003100c074032540790003000e005004100500c800c0e07440c4c2400c40c04a0358207007462900c0744024039050b600404820810b0b074001d03190040010002c20183c009118540c000c0e1a960401203e8909040d2104501e9649258541c0104820410204800402c0030078508841d031560074100c0101d115130500702d041c3e03000c1e101000c6130301c6245414420303c6041103200500e4001400030122682a141c09608000c08410000c0d0f0407003101290035014681802c04001d0300c0c2d10030001085280303030107000d54019a10945c090f140520981040c0c50103489428001c21744c160204250340c1e1107404100b40707914088401c20425840301c044504c610320b2405014040e100300322107c0112400e1100c003c00005155118a20900b1013481294500c0c0c600001c84054941002d40981d0341d51001c14514034041c2e966000135003051038180001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202741591 1250 202740341 202740347
    0xd060e100b2b020f031e0304210f0b09030c1c1b0b040f0807350f040e0a060f0902040e0114090f0604060f06090f080f0a0f031e 56
    0x24a4003044814007112080034400c2c1005401480c11892107482c220908005403a01035101240003000a08645403003000104400b525424000b0f00555944046002c1c4000400f11000120002e61040134960070b075000e40380d1740007180644001801008046021800d404002d01c100d810b40d602440458403117020881c01000d1034031140d6900000200c4203040075844061690300a030425401080c000c609031245d86485902d524440f0701103e8900041200b200042c0541c2034103092800040310f41002244c00c803900c152000500d503d0354607003038004c20011040d28a0881960300f60795110085454680d20400c0782d20041882d03802c100c0f40340340100c00000b5100c413241c004000765007248020900d00c0c1d0b03a8a00c07a4420500450b4a0381c2e204d607226000648284030b02e15182c0c0c2c8074100a10105a480d955104045c8520081d0000000964601c4060152040403444c2c1402400520020884805100f1058ac7c480b040100010301180c041c001c03600926224205403040d4000841d40178807241c118400103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202742841 1250 202741591 202741601
    0xb0f06070c170606032503150c03050105040b031e0f0114010906080c06040902030403090504052a0406020618010921020d02010b060f071a04030e0102060a0c05090d060e10 75
    0x4605102d1070a214004014002c20518001d00700680140840141d480b5104148640d400e00c2000d51001850f0000201c5c02001030072204c0748116000140f8859800401002e80f181608110f000c0c50a000c5611840c0d20001048400308000920940d5440d55003408182865229035aa0700c15608003840e22110184107480c040c1202c01d00e010401c086692489213036100ca0b84541030a034044014042007103131400503002154803c4c440c2c40d01d00d11a40d1680d0020b41118026651a4460361122400b404015805031044c55034882684080741058600080256262401013480302c030704071107201140392000c00f500320038030250b4409000d07c8034410240c0381c1d4034103100d500440001171149843c107440407030043c80b4040001c0d40161415191420814400010b80e010040850341003440a00c00b00c41c0710100d0b0449400755110303a440d2104104010002031a203180075143c3ea180c2807405410000039500101141d01c20b0400740c035207c010b55aa07003010002004085008961030207003520074000c0311282c2d800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202744091 1250 202742841 202742849
    0x11060904062c0f010608010312051605030d0b010804080d09050a0507031b09020307020c010513090f0504110909150a140f1b04060e120f0a0c0807090b0907030b0f06070c 74
    0x2694410f0b6a12880d030b4004010a00c203200100e0170304001032002c0f41c103c0c2000245001e0b9414a50320309091306020541d03119055000707481a070004100c840314101c56024523000c0010074a071503100307410242c82d81e221600c9481c074001c8515640d40e00705020440f0a02580c0ca5058020084e10341140e40c2e4100107005801140c410800e04d041c40c6000b0403e450144260fa014403400e60092442c1211100156003680c09114071903c158194100003440e28100d0180c0901c0000403440411141811301d03010040d0400c0000c590b11070b8400508101d105100000d005068089001c0700500c2611080000002060ba1080b011100540b020030404141000d400481c010015803c81c000c02c40e2071000d039400703280600e0091100060b1401ca10040d503141103214251441021400d80b034508000410051400010340c00841d020280c619041090304010f0007000000d02d03003400300340300a04601300000d01c9520300030042c0d01415a1902c1102c900d442d482000a5810006400705544801a0a085440c8c5c80a0700c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202745341 1250 202744091 202744169
    0x20150708090a050402190804050c040e030d050c040305060a0f150602010515030316020f061b06010602010c020706080708100e0c12091204051201020d090303060905060103091106090406 81
    0x2c00103180c10940b00300c602000b000d90407603010600501c001c44d0001b8004e402542e0070700c1140000c20300342e40d0701d1007600118803142000396901c00850842c8001e5401c0141b036034000303a80500c0104082403011440c0c5030701600b10b2200140041078016107000030001c0001c400031032040f05402050991f015031005002e81c0b200e0006005111190742015600d00c19144d10704414102401c0440c01420140c4110180c62030080503a428200350148105130780c025a004142d060748040010005141c0a2103414030061440c40600886814848003400b010009007000301006111000103002400c004000c0020307010807404c42e001c505000070b2041c0f2642100c400ba100303206200000c9500b00e0400984040d0000360652054140341c900020440f034001a030b0085141035400308503664188520303204100b801446a21b0029001e800e041c504030440d04000e1a00341031514049090740406c50f4882d40c420843ca0490300241d56030504c41c0401d0181c68150321550143c11041001c0f101c00e00b0840c1c01d2074039405014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202746591 1250 202745341 202745359
    0x122e03080904051302100e0111010203130c0b0c0d12090b0702030d11040305060103060b01020304120c090507230a0e030105182107150b030f0a0314072015070809 71
    0x28542d044c40201180c00254044896154455051302500c00355400380360504260b0303601207907031201c2d60a9074401c6441c03400012026550f0010459500072041c050410f8200580c1495440104e10740e55260501921b014048091803802e40700150b0b822900c9880d911048924003411300710406992508090320282c0510b0030301060111460341801583e085942110007032810380d1958441c3c4000b4120120f0060450008200101d088001c104002800034420001941168502201ca801f1180054101c0301000586002c8401d0940348240100806007c2c002441da103075860301e41603884c030382c0034640d140e015420601000320b41104001100003482000e810f175214200800c100000c903401c0d856110710b00f2001404640085041070b000e201c403042481d0b200154840001000920b45808010455040c0d0b00000b4140c4c2010b500080c400c6000d0001c114460409031159198001c2040790301040102503104130103c81260384e802107403490100c0084480f940c07018581800020381d40b280c42424048c400d18 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202747841 1250 202746591 202746601
    0x13061d210601050d020d0b25050307020c09090d210e0102070213050618090304090608030c0f061b0d0617031b070f0b0d090602030705090411122e0308090405 69
    0x414403040c03081354000c00500046101d51f49840c0c2904001e070002d10013a064600f0703201015441c00e80049180b500c3c0d1180c50700da20b09200000e15000d0480c0015000d0ba00740e000740b040c2100001400f00e10740c04141000d4869181d4043c2c8404c0210700d00641d440058106840c84c000d030481035005040560007903c520b00044004444c00c0300391352007038405541103100c12800450041d04910000d4200121406072850b141c0c0c0c40c00701102342c60700398200320f02c42d400000c0d00c02c080d120f0800c04040b0504000c005800c20f45050403500010043d9101c90180d240300000d46d0100040c260340c881c4019000a601006c0d000444039030043e90b03500254100080c5c1c5180184034107101d140060350004840b10840700b031034901c0c01d09111207256004110800f0f145d80c0c46030046000104c0310700182d8811117480c1c3c1c4941c0ca0300c00180421060782c008250f000b1440c07608000f0724a50104c000710340e90384002428048188494a0f5103100840042c5550b600d80103011507a0100401c00e56000500000b94100e070300344515103503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202749091 1250 202747841 202747849
    0x11707090f08150606160b0a060611010504231005010602071502070510111504030e040f11031f03080f070605060616020f0a050a080a030f0513061d21060105 69
    0x1d540c0c8a00b0303c020703407000021010b14248008201e2126031001082843c1e20304c1c3d5891a0811003694103080241d00c41900f44103550348420f0040450420740003d101c0d6003025240c50000b2034038081d1300007849800381107c0740b81c41c204100c0c20322040341400d81008290f81d070f050002d446d002c003801154202544125401c4d0610310025a0000780d450003004000500744020040d2036251940ca00782d14213025251481402240c81c0c00c0c101e1055000ea20b0b1115601110350401045a01ca204103203240c0d442d041400c6c05d03551036641503075440400e60200c1c1c1301005444c4081c5912520a900c000c068000c00500240303000f181f8006440340520907003080c8007940301c2008000b0240101189401e00440038580e520251170490b102440011004d0500310400d512100400c00c83c01160308041c4080c2d10448199013090750104c800701526401d40350882c00e1640e0000845040c40c481c1c8034090400914180008040c10410300e00403100304010a00905062040c1070720b2645142480c01500c14040c1100029003418 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202750341 1250 202749091 202749103
    0x901090e1c141608031801110c19061e02090f010915120b12012301061b0809041802010215061005180a03050345011707090f08 56
    0x1603152500d4040500500032000b9540101e80c4102e03501e900d441018010990f018000e5000342101c40c41c407801c281c100c980d003600359410b4410021808204110020a079800464400380002d482030fa00e2800040609100000d0800031107000304400141c061881c002416900411081105961070088000c80030300640351130420344110044180121190f03151203102c0c21000200c440382c40000509a060540445d04112030558400c1c01d5a65521015550002d401229249000403030b16a2141c3e40c103000e0000c1680f011000c690b07014920514405080104190a99000400281c8108000b0040b4030404003000d0007014180c0c054014441e50700e2843d404c2940c804d00c03800002c0d10582c2a581e0000c01101d0503840201e00007000d4641e80c5c0b601c01240e50f003031007040046004600450300c83c3c0c0001108640c01000442001d07526040c600e0502000120b034207101c040b0200c405100304070741000401a101c403c1d90b22076a030300400301102000031071303504001142e0a9844210305002d61586070102075544e0300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202751591 1250 202750341 202750393
    0x301050112020f04090b070908060114010e010f12020f09120a0b18120408070e0a02040617040201030b0d060213170601120f210305150d080906090901090e 68
    0x52001200c28000d801e19407890050343d440038100041c1d88400f6154452615019142c0c140017076201e040401c19840200b085c00e02404c4403e840c0c150000710540061312514a2102c3c42d4140560403040d104000c0c081c8202492107210710300c055649a02e248202d0100b6408810314922a510902d44c0c240d00c04800259900d02c41c0d8401800d68054544020380c03160300900c0018030006201d401c0d00800780b40300d140058002403111000070030031241400762920b02042c3c0181401100c910510040190550000e281041301d08a1113000e81c40f515035000480203800ea4064154219810200340e01c01c100c40b5a004010030106d034080d05078060b48a1008049034100d10001085950200c001070041c1c2e081403030003141e9903104200c2924100c0795070b07540c24085289250542c80d0b500c4495a000300d841d405000b0f9039400340001c3c1d0024009d42c906400106d084100c000060324002004c03403804859110f400441e5800400203040e1030140da914282e4001400181c0400d6603180100f0a000c2d0214901d807500b00c0000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202752841 1250 202751591 202751609
    0x70b150127090203060409081209010c020d1e1413090606030c091503061e030b0c27040e0102070b150a0b0304060b0102030d06090e060906090c0402031003170d0b03010501 75
    0x5190141032406904058030046d8455910145000010681c03c020700d01c41c00540741440440c5841c10030242191036520600c0c040d9081180140c8000b90b0144401c0642c042c10208400e40003603941045400750b02c02d0712003500090000803050031102e031054402049035983e020601015454400c100c098886d8980400f02040011006100321221880c2d1280014150325001a036141d84055107410f41e81c01c070380044010410400203109001030290507a5100001c403070480d20f00002c6d44401da00c40083c40b0000c180000c0e910603d031042c0c0d079451700a000d481110714000d6485050718140740584100689600c2c252140341e0a03681c281d030034280c1c01d200440e0398903104039045a80e00d44412020f40f46444c0a581140410400982400c0c0a8440d01d0060030f450000003d500c02542e4040c0c3c503003c400b40c1450040d502c103208003c1c0c1104005040d510b408415140947c4070346494940c20301c40101600300400c81c0079661210701410300400041c04003c1c01152050100402c42400c2c0b608840c401c3c043c417111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202754091 1250 202752841 202752917
    0x8030708070206070803041412210406091202160e0105011e02070b161103010b0a050f0a03020405010b0c07060c0206030106080c12040606050f0307120215070b1501 72
    0x300d4120805051128000340020f03240c0001a6922801c03680202c40480d802d481246820300b00c81d8081000003504803d8800e001c2c9170030544035012003440c13a1005600e0000e102100040c0801010f03030400c105107036100c9200000d001c55401d0194450840c94001c0074047c0c08650005040340c4102c2c811030403280181c6500608405019100e441e2541c2011800700390701c10300500040500c5901c2c000c200d094140d40d1041c02c0c0c400340d45000b4400300724041845210368180050300440743c0d680061882101d40c01ca41d9200d1144107680030030b910605c00c0c0e0029600525003000000c0d824441030042810f103544006881d00d09469210580780110b1102001c0d4000c0024801885114061850590440c02e400f002900b0718a4012510040c0d403802ca40440c0e40700e8961b001040f4605002c100d500710007031b086014100703003820481030040d105103080010b44140d0800f49440360070081541100d9009810a0150220785002c01400e102000400c03461800503602c07800c44207121070134074010114107403200303104a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202755341 1250 202754091 202754093
    0x40302010c0c0e0c0403140604020a090f0627061707061407060c0905030610050603040b0411061303020312180d08040f0905190b0907180f03030522080307 68
    0x1919407001d0400c451102507620003003940c1090412052003080d00100d078980d218254a070104804051040d002070b0307940314a0a004c0140d9034019180d06940c0e00c0c400005112605200b5030029207516801030054181d81a5900000034007822420303142c000341d0b07009102641d41e64800c40b6406803030702101a00342e00190814031000740b11350111070783c45036a44a0300e400d001032034442800701c980c011310910205003500010030150070180111588820806444010289008041003192000800040070448160000b0f000c001e8244031020760100007604e4140c59000380c0ba1140c800804a00090344a0b00c99150b918002c001c4800440d0500740c100240d90313071348103c00414031000182090040341d849a091002040c1072400c06034003c0180440c3c00b010031541020030240070700302d05844a8903007990074801d21107110b4540100c2160000030304d00e0712281c3c06001e14611100d5030314a03004160710007021040041407503480700c050f09414507114141496000040010000c00c3d100b0300c50000f2540050180130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202756591 1250 202755341 202755347
    0x6090408090f09071106070201021912060e010e0114030606130b010e100f03200a140d1103090c0906010e0d02011808030703140906070f0f02030a06020a2304030201 72
    0x101040941a00d10140382500010403d0318110784900016218000c00800640108035490b017081d03542c002103151400c1042007100c3c2d005219084014000075440d000d1121800340d00c81c0c801402000d9a0514550319007422038042e84085c4222010000041c07244509464040341071801341070024807021a8108000081e009841c034030046606100c40118880e400b9210010f4040025200f9a0380c243c0403102840d019084841c00c011110300c45485016506030101018100d40d030f0f0615505002544166180d440c18680c032507080604200d5085c66805c0c0c1ea00b483c0070001e503000340d03a401c094400384950031050200401080351450b0004881111984980c102442200f03045801890007a08400b1110308115000010703910101e005d034000606901815400100340c0212551484210b00e00f132074090000c1c50340d00070204050074a00d4940120030030800300442d08228103501400b0b6410720b0300e803400c0c40030007500030345400c10214200e815030348007403080d051040c240d16000c000f00c642441c5c1550011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202757841 1250 202756591 202756597
    0x405090f1314060a0e0718052d070e0618041806090507033008072d030b100210020d09020307080307030f080f04060b01120f050402030601080606090408 67
    0x800c5451207030080d14003241e0001e400046000c580e20090040e030902e40c60b80000c44a000002c0070700354000120900000442d1000b0000010700300c02c0c041810303240d482d00c0250304881c41c0401304080708030003011500d9840b50300034a8401c0e000d6846880c0004529020b0103d1481000d1981130050020b0f522020f851605030f100c84000c446c1a880d0032000c01d03855480c14200d0707802540948103540010300400800203412810b000080d403614015501554144a050b00e84400160060902002d100010026032050150242107003071075203c0031480e00c0702158499400260b043d154002030829030940d0144c01c11940b0000e042c58a503004001200613a44014000d40003050b003580c080751a8415400560f40400c0380030007801040c1c0295585945524028041d000b03540801410f0003070104c03c00480c40c4000c54003561190b0400c0d40811302422a100490341c000c901754110340707620300d010301460402125a001c80c0c0708920940481c1c40c0e0b42d0b00c4030603250340c4080442d4042c1e84986e440f00042c00145148020b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202759091 1250 202757841 202757851
    0x90906230409170708120601050a0807260106080f090f03180f0a06050a031512030f27050a09050405030913090501021b0d0f050406230c031903020405090f 68
    0x1408002c40f51081d000c5056600a03082a6881c1c038010481d1400101d013202c034140c2004007424a10b180c500200c80181a814000340000c00740321004500101203600a011200584501c8064419540e100c280c05440035030140e5180c0300780ba0000700062018000001c00640085915004605108940d14001c80803515041400d800c4101502085000e84030f603100800a007009840701921400d086000600719986404034080c07111554500b0802c424514104080b0645c0516045180c2c070b2040800703403000c0b494078140c0790400c481c2107003020400460540ca202503600413100441c241e640d074035a800c240c0708181c40107403490f0400c01000410303151100d9848541d5004040c08034406203141c50302822600140d203081c20380124001458400b8500344000303071a44006042520030555020f60040c41030155005035000c3c41200301400d445440c5000305e178501020b440442c981d03a000c07030036411510b075006003048009904d0140b040b8503d13035020b8000d503015101c024092120a07568182d10001103200589 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202760341 1250 202759091 202759103
    0x50d0f1e0e0411120a090807031b0c0609140105040b0d0203040201090b0c070603050105120c040c030605030604080d0e030f0d020711030109060b030601050d11090a0e070303090906230409 82
    0x25401c21944a50040e403000d040450042034941803100490380345100010b01c01403803146022030310310004018405880d07a050305407070546c02540b00041c418002d221041400b5103440f024200c00901c0a90142a41c800d50b00111300190680350f11344c005490340d0145008104540307005204a0b4548203240d07002d1342d8824014500b019400342d0701d001542c02da51099040e500c80f60059482403002d250140502801480107540340300c4544041100a511079040c031440510403519800b2001110307119030810000b8280c010140e030501c0c242450b0141c3d15602c0540c403172400c07509200401c240745001009a481c8031410100e84d03441c040070780c0075110080d444001c0480b510798040260441c291024815004841e224900008000f5040d404052415205078001c03845038280ca1660400905a51a04404603005498915903611880720004c06040784203c0081c1d80d08c101c0340700005140e40801c03000c04071002098104030700c82d01c03a4a01548004002e80240010740600642010350816600007680c80f07020380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202761591 1250 202760341 202760357
    0x5182a071217010303020105010e0c0a02032a1902100804030816050f0d05060414011a0c0a14060403030b04090f081c15090e010c0c020d0309150309050d0f1e 69
    0xc00885441420380017500143e40d1070b0014031502c100c1a200f50f0304460400161401c00e000b80d50025982d10444140d00d030312044c0380720790401e0340001d13507540e408804940043d07858505014040224a400350b6034160320945d910726595003828080e201440c0034640661303840d16a41c0e06c03910742030062030b4042c4070201005000c06c9282094129640034021010308118046407500b450000c020599070140314440c00c0d00c403040010000c81c206092501c4440c0001f02207940c8441c0f00d400710a05100e81c40c9006405401021119500c0000105006100314442d44040204000a03401c0c081100d8558030010301c1780c040c00d91101d01181040340604215000d0401c070b44600059559110b0a44041e2244510a00b02000c0f09216040345070040c0741038088514001c12100481c84030040030100402006405603c002d0b1004090510400c400300c0540f6144000304c0000c80a036030014000c0003146000d68040c0611004ea085443c440e031000302d03004100d07540710ba03400808400b10202860300d20071400d0500a030303a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202762841 1250 202761591 202761617
    0x1a0a0302030706111906051e070f0f020a020406030b1e04050705210d050a02010c0509030a06020702060f030106090f090e0c09060a080f032a03160303020405182a0712 73
    0x4100c80c03e0002d10806e0040b42a04140d100c180902000080015185048400300315420354484100300205450341342c60702200b44824001d03410600150400b0b5002402c081d40802032180b84010203000309800b009030764241600b0032140b90038400544005100742c1069008001c5854041908040841c40300b2007024803242d0088024505a09000e040e000b0481c0419a6602180c0a00c00c105010b0b400741030083c580b51030000020349a0a6940c40100710560120354203042d0b4480344185c41d1601d5400c008145d8070750312080003a00c601600e20a401e0040c40412001c40e0b11302d130030b014075600398000300001c0007595459010019182c070002d0038260002d0030810000f41c681c100700401507250900c20040c6a503607401005a004800340801c1c036041c41303542c0007420701d401c130300000c2140c2c180000b20591000d20711503441c2c22400ba10481e481203501c07e01000f295000701d1044142180240309440d50044004500541041f40c00741c000350210b000380c000d100c0d50000c01d01540c0301807020615858401200c03102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202764091 1250 202762841 202762873
    0x503090f01090e07021005060a030b13062c0d09030206070201031a040609091a060d20120d03051b04090207140604140c0105040f17070b0c011a0a030203070611 70
    0x400c81303c0c103005a010600221510302144505900030300d040c0e0f1501039075400d5484118403c00003134800c15408203580100c0d014096140e00c000040001c1c013210000c90300d410128021084013441d0300c5185070040780400b411640c01944010101d9070b0207000c0305d00741542a00150000c3c99903800403005c080031611309913080da03218456100902440080010407521a00f01110729944142140d4614021038040c40010343d110b0300b80091103907001c40b0440c0c100c0198003000c203107002c18036000d40e08040c419201c05010030001c11503030440042c5a40401003552a19802c1c41c0c0909a01c000c2114058100030901c0070360041e400518a1601a0000003011101d400100c0c2c90000c08070303002c0d03814148070342d200c045464042c00100340031842480c196041500b0440c40d101950030b46d120b04100c042108841104040044c03103e03100a00c0c0b40000c0c117403a41a0181010b010300481d03806031841340c08102103c10740740b81000182050305d402400a00107541002c40944400c400344200d001c081c452003a0035049099 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202765341 1250 202764091 202764119
    0x303040906031a01060507020d050f0106060816030b090c070f02030a0305030603070e0c0d020d0b130507020c04050411010c0c0e01030807030f03050f070806010e03060108061006020a0503090f0109 86
    0x68600140c441e00d5803d105181c160601c0801c089640c510004204080e03001081d59003040c0c0485040000316101e180640c6000f51442d5040c0040d404d1600005500e40c01248542c4121044018207c0420a01004504035040c00c1e81156100f800d80c1d0205078151480809001c00d2031140c1c10007409a00b0a80000303161805e8100c0032400170314000100116800d0030703c0508001c00984401c14958148800384102c00e001d802c00c03170b04482c1d60105046094445941207950b03100d41c0075141543e10203e000a00c409080c0c01c580b6007000d4407510b520080a820503208281c81650002408081c05401400443c5d061110314004d88051001000c0450700e800d4800204d402184a02c01ea1940e541e21441c02400242c02c035000352040c1490311080002401000401c1c1c0d5203c021450090390f01e69492005880c074808041c074807501442000b002054415001602c240925071840e000000d0307a507a42401c99450390002002485500144130000346410800341c054452201418104001e1b0744450f03008038108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202766591 1250 202765341 202765349
    0x14031b03010905090f030705060703020d0b041b030605181605091e0a060c0305090f03030d0f140c0a050f09030102041a0306040f061a0306120f0a11010201090b0c09030c030304 77
    0x90380d5641442000e00c402c0005d10510398208024506103041a01c82940710b070001400706c824943c002a49040070440da600540c6028030080c800c10500d0015030b00c0c08070f840c0d11814000042031520001242d1072614011b400c0d00d4400045c03004041d80e83e4481c0c5010007410703010300c010520109002002d5a07036522401918200e03c924650b1030708068283c00c1068078a0340707034010010b0014401e03144012130350050488100035000c5e01d000260324542c001103032440c811000c8903048145492079808012916400c66140350200d40c80210b060345450690502c103101c0e01107203801140c8100116800f252000300a8130304850014001030504da6110308103c141c00a5a4088003070120000800840c2d1800b44690084d181010204004650401550250f80710980485024031070340440002d0039951402440e50030b0400010a1303540084220391425030310007048804076141c11203d500e94a842d4414030078182c07001e400c46030b0785006480711303125820f99a000b0407242e5010300070b032810380c115a03c00b000108010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202767841 1250 202766591 202766609
    0x60a032309030a140901080c0702030c04110d0e0613020d060e100507030c11030f07080d1802030f030f030412021905070923070810120b040201080601020102090114031b0301 76
    0x58a0f0400f8014688000000064041d007410f000101d02030341e12003e9aa4490383c00c1400c1070f0f46601d240000391400d041869027550003070404035848080490440508a5010180001d20080c8810545241c913548100c4031100402090500301d005407a040288031045130142e503000540c00341c9180030798103041110815074200c540b14010b220b4419451311500880d4003c500d0060200c4481d070040640302d00c655401d0030758622000c21842d007849041011583c01c40c4160408100b0759050f9400c4010301560341c04142d211b8001c00c00340f0303403001c82d0210480700600c104501035840c0d035032580d68106003150669003140c01c600c80c1c0c201400c8903040107800c94110500503001408980d00d0316016206071840c019108400b00d10311541400c3c01c82e459088182c0003422070600b040c495a612a910b00b10780500e600003241d00440c0c900e0702d400d000b80410601d0059000781d89821060780c40c000103909078817072500e071180043e004c0c0d816500700d0380d1300001460b04880300074004540300740c800c00c050303406400a030481110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202769091 1250 202767841 202767847
    0xc07060c11030a030806010503090c030303010f030c0b120408180424061b11030111040608060a0504180b0402011e090f080604031e2a0201030b0a05060a03230903 71
    0x14400d07640d07029840c040d8210000c1c940e400241d900203110b41409080039051200200101c0d400c1d038000e0007804e0140700040d044980300e45c0d6858084c0c606d83d0035072100f594130820030324010980e224907074102c940e441c05a00d20403000303858070b544041140d4442d440400c4621008103002011350f07282d00404040103c000280c8040c00c0c800d91000320040304540c4041e042c4100c259503041035416100360196016040741b080080c131207084000c00e014248420240001d03c07800034001c00c1450b000001e00b17000720130076617182000640714014442101d952080c6032074a81682c40c10400007805a034542940f00c0c0c03061500300712050300001009140f6000481c0c0c0000308a0000c030512009404802000003442040010035440c02d081d2030103400c402e0006c0034202c524141210f140881409003000c01201103c0b48095543e003800c0b0380098000c620250001c0380060300388841d5040d10701d46502ba42d41a46c500a01c0240f500c014036201741d0081001c00416801c41005504ac241c0310403481000034451020a809165 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202770341 1250 202769091 202769093
    0x3220510170108010209101214010b03100b0301031104020a0e090a0f0b030a020f101b1101020606030715030b0f040609090308100e07080c2701030609020702060a080c0c07060c 77
    0x49280503001442c050717106100c0c0c2070041c0e481c070541800861590034001001074101120030041c05103100c0c00541d03d00c50364000141d803c0380000461152000424400c0d4403511781c0c0084101d0321080c4800740104820b0300e08510341c0d00d0281d0060a161402e03090841c0306205c2e00010400c6100100d50002120741d0b1461040d6182c40380f8018094241c4080740a044451455130000300340e450081c50b1940a10440040d50b2032071801042c0741ca41c903481000c40d100b124503052800d1040844c0180c078403801030050601080d518240000e1074000e48280100600c0c80b2110940110002e2548101c6c450348103555690f020040d843e5481180302504442802084080b46802c000e42102d1700580307140040c0140b1601086810001c048098001e0854179012400761200c0410b824140140017810040d201301c10f4032508060444024801056020f0b01c043c000c2c1039540720500704034010f10300080d402000030058811414866180994041d210310050342c00d112815841c185004256000f00d404103050390f04044c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202771591 1250 202770341 202770377
    0x1b14010b040501051c03090e0901020301090b12061b1b0a05010518060a050402121506030d0302070b06040e1606030603020a141804031b0506100905070203220510 71
    0x188128400d407418440342d450400401c42d088906541e904440e41c2004050003003500c104680e100805a4001003030841c01e05900f814002d600c20305c02c100666103402d030303880010305103404e200d8540e158503006003c43d80d560466040385030201c0c14904408520420111000e107800717040600300510030000a02e03040c1581c1c03500c01d003101d401601041000c035040d49200603203000003a4843e8090b5020b4404212601c49201003000210283d140b09140e004844081e0507905007511214070410040301102e9040d1300005055040340b140290261950320520000303522030601d5000400d1800c480400c0301d0a2955545d00c010680304175070882000a604e41d10108258646064424045d28074010b840040072011000509143c1ca500d482d10b024041130320000b001d250068060518030091002c160420521924142e52511421280d09000c2140844003144541887c440e0301c0c030850280c0c008602d0010b01c1c0c01c80301e6200c014070340881c030113001c0301071302051603154804c10660b00380c0f09841da1540c1e103800d00100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202772841 1250 202771591 202771601
    0x130b0a1806091119090b0c0f0606011e1b020628050a05040302100e03240c03010f030b0a0f0204090506040b01080903090607021305010611190201020d08071b1401 71
    0x8003420b400c00d9264210f40481c1001c5402c40385509808807980c0100d090181c1c3c541d090b44d03005441341c07100070882040f1480042400f166540d04881a24100d0381d03100c006403201d0012800e50104200588100140e40d0f000c2d9140010f003003002c1610b03501c41261603000030841e50044144071a41700041000c01e00b41c200001003015500c40c2420018180304c1003120050050245110282c4030302401a4241407117405401c0e0724502980c040d0503600001c84a0070031a00c0e85203594034003011103603841c1c0064000e030b5050080e607068070ac00c5504401728514640b507540107100b0140c5035203075407603450307448100c03400ca18401000100151000400c05107046d1080000325102c407030034641400040070400c80000d0011084a919400c105e903400c2e218822030001c0703400304000f1044001214a004008644160441803400b03414070100119142c1012010700ea07142c5034000c000003405603220301c1401d07104600401c1980e50043c51841c200704102408413445000000c0c80e0802c4d07c000c4410b00492000803000c0c028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202774091 1250 202772841 202772849
    0x30f0d140a0c060b0402090414070e0f060f030717090c0f1927020304050c0f0d0b0604020313020d0f0b160c020d081306031b030515130b0a1806 63
    0x11050810041c21800341c811012468014900d40da603009060295580740c3c103030340d40c800c0d01a20410009030051808580c2c06415140840883c0002109405034a045040102c1b07285010307040b5400d0002d14981140c82d40c01c098080024486101030701680000c6540401d482460440c004100d9034540e0002d11110840010083d4011100026401c0000e00ca22401004842100e80c4091030f091685805206410760076114441460001040c00301f80440000d00110b84041110b540198441d00700402c01503c10b903d0008061503843d1340019040d01e480d82c0a181d02c01c8581c0c2d2041c0030010720b540081e00340000d9800c102c1c0d0100780000c11200380710384c80741e009901c00e480d00a5800507401503400641004d09004000703208113480030f000c0003004103101c15149031b012852402d00c940c6448600c084e0150000c0c46c00c0f08822003072001e422905074800d0090600032903900e0325200000c03107848103100302c0f28403030070000c0a480d850301c075800700c036880d2100003000506100a40800080b61346554400382d40980d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202775341 1250 202774091 202774127
    0x90504020a32070c0504150602060a0f0f09050102030a2f0715110c19030507110a0302060f1305030a050303010b1c020304110103050f0f190605030f0d 66
    0x300c011441600040414140b016101018181e445940c000714100004610310400d01880820b40104000d080d1301c216060b91412201400700c6284c07000d10700c04046a40c45480c00583c0076001044c1c203404260b0007060741e600750a0001c10701160780b01d242e20a5541d0703082e0840341a90f00204101c8005021f204800601e000b0460b001d00200901c0d0b0a010040440e186207103841c54001508001c05c482018420485074121200303018000130758085907200c2d0051500c0411600810510090020b400803807d800c10303602d600c9035400e00340705e600d501d40045826040950802c0c505a8040f0141e9074007030181102c1511680e0150355000398140010700c0c40b0007940210b001c1d130320000c44600012004019a81580c500718007094442c04240d20403030740d81014480d920109403000050109010065900a64160302078074103100588590080201c0902e08803401126800d144021401d40c11404c101120848100343e00852071581b9030000a04241c0019032021450744a901c20602180c1c108e0b042100d4a10030301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202776591 1250 202775341 202775347
    0x501110c01230604021c0603060c11070e0c09030a06050903090a05030105010803070308130b0708160503091c030b09010e0108070605040627030503120a1b02030708030403031e060609050402 83
    0x1010070442001400c05446540c010804e280101d0f01e0300d0921113861342c001c6d41071114507500d0406000a0061002e4400003407200f8000580c1c4010018441d41101c148001042c1280d8a40700001c0c0070340c01405940d07a150040051300400f2074424011680119205805995103e45e950100006e4003140e510040c020390408004105409020017500c154641508000080380c0c1c5404030038160102d000d000511802c002014010300a5201181a104440481e840c540c0c10341801c03c1650640000c03507201d8100d60202014110840f92601c14641d401042d060111b0301c0d49050303001411000090300805000c001751030041044110801c01c00008101c0b5082aa1826042c00802400b904c0840d40c562000d81004658a945402d00200800196004405d41340c59201c40c10f03030301010b07140940da681206424504840408402c440d00c81c00c0550080d00110701d0191303603030b842c2e0645400090041c0e092555410241000f4009414420500ba004010004405052200240848250350815402a803042c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202777841 1250 202776591 202776641
    0xb03070b0f0d0212130308060d0209070c08040b16020f01110a060504081201060201020c0105091b090405030f0a0203070303061203090504153516210501110c01 70
    0x4441141c800c0c1541000d0303156281d801c00c070001e0107441480c0000c14081680b8040040e0b20880310800d404031846555210390030b4884804101d1241d10080c0007035800b1303041c2c202250314035000354050a440785c800c0c1c4500303082941e9541d0380001038003c18400342c0c99600c44030f100030452400d40c0c00b0b602e8240090a100c81501060315401c0c2d0354500f1040000c2500d6901c002041c2803188000560b6580181700c0320461386503848510080c00703504022400300b215820040464100c8802268281e084968030300401403829160b01000000320f4098000e0b201400b041090600345843c00b0001d01c0e569082e0340055503100342520700142254843e41c00007081040500b1190006130780000b0542c200d51080b54003080440851811313040b107214660000e20714981500c2000c4000d43c45038500341c135050b5412103443c4032040c0f15081580b281c5800203c69000c14250b2000d00c00782060080a03000003110288103104070006075509421540c2d40c1e40b602c40840d40105411910300710074051140305081c0b01401441e54502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202779091 1250 202777841 202777859
    0x20c03070f05090c090a030804090f0603050d03020a05090a0e1602030f030a020c03090301090b011404050105030309040c091d0a0e010213091107061a150310030201031107060509010c030b0307 84
    0x442e0080034440d8a90101103290724001e401034030094500100303441c041d20f940b403500c144583d02500c0780c4e416103400c10700d40c004446401d01c500f80132a0b4100002c0c08032000e000008600a40c05640414140f00341030020340c6050711400740e030b00c01800d10340580100318100789288150310f507000d10380c61085600400241e543d000d122015644c00c2401c080c000b686032500c1c409040c1c00d5018040c3d02c030f5007561a1101c04402d000d455045141215107800c8800d02d411182030501c410746209005260305540304000812903800d00d50f120786481001464400d20310398960300020303064142d4480620581c1404818070801c035481e846a19621452000210700d032540368041031107500031900c039000805581d4070880356419504012107004c582c1c040410000920b402c0c00787c0300035904031a00705001d00c00c001303000e580d80d685001c01c890190303400500380001d142c41d6900440140804440500040c036080c058200020014040c407800b510b0420004100c0e1465540e00030201d40c00b0440c0140b190784500c00820031100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202780341 1250 202779091 202779119
    0x203062505030c19020106090e0c01020312060a0f06020109290f07050c01020403031d0118030803041509030804020f060a09060518060a080a0f06030c05010f020a0605090c01020c0307 80
    0xd40c60802544a0b030b6018403041c014002c2c0500c1d400e05040c0940c100300b9155066001c10705495403184c0801c8103130301000445c3c0d95080e0400105001d40e00400c4a48101c0c00190016a030104004008512045c1c64203070280503034106900110140c0e44804902040208035819042e07522552001c103a144100c0340e542d19120840502441035100c904004a01d111303126100326402040600000d56070b6a03a41d02c4c006000c01440800400c40300041040c00c00340d58400d102c05602140541e0181c5109811070b1640d8900754400f400803520201c813013881d5541040325004807107641d03000b81c640c0c88007464a130040c0113000908004462048100f08240081c3d84e030030606500c25100285000c6445942c036020301c0c0e54400e0b00090542c1c0c001c001188074040d4982c09410f5610940700410180094a6607440b01c5050380ea039400002e0481c900b850050050354404c000e4801045200e1045641c1c035246900c0f04405c03600203498041040c1c22205a0051550b010484100c0d0031000b500140109481c2c0040084201 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202781591 1250 202780341 202780411
    0x717180409030e0a0f03020306013602070f0c03020906010c02060a23031314030705032713060801060b160b090f0105070207060306080109030c060f27020306 69
    0xe58030030341e50050520504000c1c6039000007401c2008031503180c0d08442200c0405201c00c034440e2081000200340030466842161003003114040092074842c28414042260a002c105009616820311203040815108498000700394003800b8042a8941540107201100500030407182c184602110a040182c80341e40403103c3c01c5583e4500035581001c60005e030103850000e1451251960004024403011084402100000c2881500d0601008a41100403130f180d004180300a084d54100340004000e589101121401402c0300e581d10003220f40c015000a0081c0711b40c285c0b21001e441e6902c00910031008248241d1000c1d040c02c2035250b050111181d0401c01075880d0010040003848102c01180d0750280410901101a4010b0028889450302800080d9134014502c40d010009040c184005900324043c407071003041642680e01c4524040c02c0e5190100580313098a080600780f9610314541f904409004409207050a8404001e80e4404a50042600c0c204004d000290000000701c02d03d20519607102c1080384030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202782841 1250 202781591 202781599
    0xe0601110114060120030301030803060102070501090b0d09210f02010b040603080409020a0e0d0305070b0705090117150406030f150b1c02010c0204060e1b040b0d0e03090d08071718 79
    0x990f9007041c5c1c101440501116030819204c007000100401c42154085c502c20442030b402c643d425584c80d00110748080c45445940c0011504002046a02ca1076410a0045034045e48025040c202c110f00b140c0059404d558100e000101401e0744450443e60a010790040c2002c02c503402d019103401e548520b07585100d43d1190307100315540040e0003440640160b000455140c0c00070049041400035007406403150303014007030841c2d1085405d0002005a800b6100f580c1032120113070360b0328189000b11800890202006080d014504001c1010254199200e001d2000076521415041002c02e409251541c2070500762010100240e0a0440c0c102e000d846001c0d08423190300d802000483c1c60031250005945c0a10200400380d0064200a00450203a4014400c14080c2e0381385d84902c03a0003c3c601c0c8640319240100e019100700c0e41010031007081a40d485d03421800001c0b02d15400c0c1da117400b1110000071006140800b040712400c10105400082c065900b058814080708040c080740b804009000ca000602c038060020703486 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202784091 1250 202782841 202782857
    0x5030717041802090411040314060606070f06051806091b030c010e01050304060b06031005010e040e06180708060708010f090e06010605030c070b070e15160809030a0c0e06011101140601 81
    0x180d45ca90300864403140e013107000580e940b601ca04054020000030080d400c2503111f54404160542021011600b815400c05042d150800c02c0b036880c0d001402010f00543e41c42e00076410440504041446411300500440d0b0040000c01c41b0607402a03002a901c1007000e210341c0111454a2b82d0366046100030200312000d01e4203556075038691a04000510000c07101c107400c100003008028851551a01040640b40240c84140f03801019100301b00507150761450303850942c0c0040c004503104905210900b620400e100c0b0a440d0070a44940019140520850b0761000041c0210010082c0314041040704020b06060030050207d050148800c50792884103100d400301300100000092082da440303000307072550554440e40405031030501f881c00400104070024410304c54686c5c10001041c04214408569103980141006001c401e034030b8440e04003503049000c0064160040d0b0015000080041c2070700703409811421504070b010f05141000500c00031840c85c10b170040740e24040c0c0ad81030025070b01c1c002d0f070b510140034600000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202785341 1250 202784091 202784107
    0xc07091d010902060336070e010e060d061107081c060e10030312060302060a12180510090203030c0312010303020c010f020c0d03020c040c030b15120c0708120405030717041802 77
    0x103e11a1000d111b402d1070200a60402a42980411070400715486c1c080400340310f903203440304001c20b900e099403501d40c0820390000702c60016070f0a81100000c8196a0001802c140341c43e151f052035540310b450100c0c0d020344503400540d580d2080c2c3c8108006000621004216031030905210704c0c030040540805800d0042d01c26100750004440c0d0010030207140d01800a5072284140640602900e100d000664005818900c4000c00300074040e016883c056081002840340302c109004100080030786c400c00382e805010411840b544600c00b007008009400018690940c41d41c51410000c0c1030010305110541017002c0486080303100c03580021040c944200071503503d20604482c0c80e007a40382070880003130300d9082030401d28410ac8c55a019805140d00e0181600c0341e21014089050380c00c402e00c9010601c1604501c3c0d84045240444c1d80000380802920981c40b03d898061241c1d11803407141c6088500312244e910001c2c9010401c00c00742c02e0195442010f50401e402e050034880c1c0400300c02e01d8090021302895000c100c0c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202786591 1250 202785341 202785391
    0x304050d0c020d080a03020a03060812040b090316030503120601020102031905072309130608030a08040303201909030201021b030a1a1006020304150c080c07091d0109020603 76
    0x3c1152540084416030b651000100030b40a900a0090900841c0ca80800091600e0b40402c4001d005d04c0000d026034079003401e01d005240142c101c40ca80b00e4161250350300000e6034454501c440d0014501440040d5101c1c4984120f15984420007003441d0304590043c814000600600002224070302d0001e480490141e07070307111080b114070308190001a64121140441c003a010804001400b42c6881502d903500d441260307105a00903039089116504d00c076442001031a955622030442d59800c14401c1c0340c04558000000c601040e104109070140040c188005a45110711800e51a140c20030751240c2003980c0c1e800d1440c2c0000c1d490701d43d84003444800e044881e1a8404030740d03040c8001d522450f0f0004042d546d5402e403030361900d9401811a4840b0600c410440c0c0451428000402c1d00c08485d40304800d581c03880e6003010221088481d004040358020740601ca00c0c88605c1042c012503025001030f030b0340000c41c4060602d61013021000040b80001c56458100000056190030044a0703200f10303200346411010b00b680d9944 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202787841 1250 202786591 202786609
    0x6150311040504020d0902032e0507021009060204060212070f081b010c03060927110d1a1e010f092c0a061506090e06120f0715030626030c0d05040315020304050d0c02 73
    0x5240340a150008038810044194051c0c010b175656a401c440c00c60f990545003542521503a000a86081040d40c0c0d24000240c0407001070607a10f043e8425414111003719180d401c3d10324101050001c241c8401c2c2c00c0c0003502c200e200341b11000c3d01c052400342030800b40724030600700e01c030309010041e0000782c4800700326400e078491440b030045080d404003108480d907513840e41000313880805955102c440414076450300c00c600035180c041c1e410b0b54000c807040070303600c0d240c140068010307c0c80b5400b610440802c40760790a842c40d50004581d0f400300d007000c060440403100e8075007082101e410300324107a11100d4901d4240501d0754004c441c10141d0300000c030305600175203480780001c880110626004c840c070f11900702c03a0307044164085a0740045a4540058200103403146070705509861690040204048007821040381510400580c0e0707504c51181d1303041da4a001840701115013021421101c1402190f0002000c10801c69001e64890410504080c21415810f1a83da034680b1349103644601c01c00c0090340b0861000790354601c451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202789091 1250 202787841 202787863
    0x11160501021308030409060608040210080907120317010501140a230c030c0c0405010e04110a0b0a20010203090d05070602040503030307080402030c010306150311040504020d0902032e050702 83
    0x81180c1d6521030f83e00307a480d0700034001c1d00103480c1400c3e00003034080c0c082c210725401950300815046145220764012580c18400400c80580303849084000a01d84204141e00c80c0c0450096982011200c22100401840d0710113901840c108002d01c2a0040c1c9107890f01d09542c4120b44a10b403d194803440650140c485403000d980d03d5801c864002222903060702e000000740500002003041e2184201c0703200421044900c24400c0c0010303858038000160000c0e04d181c001c5002180c0040c04001140d40314006080c1300d8005082c0e20300440d80c81c070220008468010006003042110300000d40c550702d40465140d4a03500c0d40c01a2034107101000c20500c00704a15601640c014081c0501169240c0c41c2007040280204020340b4168020701800d080c1c20540d5100b4004c40068410060b84403c400d290743c20203c00034216220708482d0104140300c081055511800202000c0344030003008030700c0028074010141880d5440746004913031012155018201040c03842001c200c0c031030329040000c5980e26640240d0a06102041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202790341 1250 202789091 202789117
    0x709021c0f02090310200313120905030f06040503040e0402010207031502030f1e060609061312170301141309020d0308011401030c210608060a0906050a1116050102 72
    0x1003408019907440c1e001d0075200604500703e5407482c80b400845011a00098152031010182d0b41406010b151414000c50b005566010b80780b00f016801d403200104205c901d0078540c0000c2100c00b04210615041006152001411f005811030b400d05580302c650300c0c4a40e01c41c010314554030034001010340e0b000340a071000031500080381d280d000c010701f51540d0095000300d0341d2492203083d00d00480c08802c0200c0e6909241e120410a40810f0b446500c1009807582140712055032200c0f041000425010040384840002c16030300f42c1c811012043e03032404071401e040c900c1115448141c18001006203803541c40c85030180000c01c1c0ca000c4c03165807041c50054007918a1620103500301005a050030101075021904e241215440400365404084d40304c011003d81d6035040019000410650896500041c901d02e8440d103000203800021385565a0400d00d401c10000722503031000c40da903c0c0b00c003405000d020f0140913446109000b0801603050184c03400c0d400c0340105129440c03501a54180784040100940c1120541c020b611 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202791591 1250 202790341 202790351
    0x702040525030b0415060c0f022b02090f040f031b12020a1502040b090f0d050a05100c020a0c181e0207020102070f05061e041206050403020c030a0201020709021c 71
    0x1181c06005032025110441c042e6141c00005070049485c448404199000e9954a18454800b510350000003002150306983c8030907540001d26610000da455a0f40500810018207181440390040103200640200001804502c8008100c00907103800e0003900c88651500304082d28190325904142c41d0514203c00030965843d0000c840084c0d42c0005480b10002e00c2489101a0804000881e405a01451190003e0840c0500811806d49003d0591480c21140034020002d011441d40381e2524080c0250402d44582c3c108101602d02050240a1003075400401d000a000c6400c544e521131034034028034403c0011003240324081500d44c04903034000c0f450072600aa86030350728920800d1030030025402880c0890151140b15000a00d20503000c141c002200e80c0103280074102060204d0300d00e01da00c000c203004e142c903030000c00c00824101c04807411b24401d9402040000740c98982071501900c0c0c0001ca503001da20a038004894400140e9000178840141d94101c440561a20190404c0d045032a040c02c42940400d030500e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202792841 1250 202791591 202791661
    0x109020303121f0f050d060e0706170108070b1c0b090f090d14090d030c0803040809040b060c0d030b0102150a0f051308070605150402070f0507080d0507020405 70
    0x41802d280c040c02504401d09005003442080c240600c407148640d07024070107000340c02c00152500717002c0701c00d00034043c92011a0301d5440308060ba0605030941c00c5100411041c0ca5a01030780c010448116000d001ca00008120050910350440c2039401410354a14607406c0400700c0040c060783c2c81d00140043c032005004c04910b400d105043c10a4031b2000c480b509024419480c00c84420b6209100e6148113541001115107004507030024080043c2c1c039100103070305010b0071560110004d054040114403407070042510340c2d110003600d401c00050f18010300701d41f07108940903c95000c101c0000b08100d60b9001403405d000a06102010050303003440d0b80c3c0c62000d074800741c01d0030800490a8481d007055490920300030f000c21141c0d9545420501c02090030380054195402800f801000031425404240c0020a40d06141c0c201c8256000150aa0b4040001281d00c0004809801d08102c820083d03003000e8942c8201921084030709840040c2a40900301001e88125180c0c001300d5600f8040b1040648450f041c412003411071002d0f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202794091 1250 202792841 202792867
    0xf01110d0806120109021e0127030c0605040302031504051c020105090609010606051615020a030b01080106050a0507020607020f10110c0d0c2d0609050a0e15120109020303 75
    0x1086440501a000a031125440900d06218005d0301541c002e0070021000ca1801050850901904042d4140025015548104140c0c410340e410003821204101e401d1900310700d09421420199813000003407140500c030500040c0e07804108602a06802604420550388604015140c484030080a01c20141e06681e5078089640c103412080c880d0b06a481229004d441316454035080380d845101d042e000031024040740c2ca02c03241301040c0300e05880c007564040c01e081586400140407030b8400c49440012a58440309180703070303581081c030300c900404150402604010300110054190311500500074400d440004d0114210750f5254800d0329403d001a0454202010321400039007800c2403003031169003e100340540040c0b1454480040644030b5406080b010080b840c0c240003141625071444c10b90b008920910300100901c0144102c00c0c020203441d40d0352180d1b0303894241844a500181d070044080303c007000d010020403e1908a4040c400d003001c0d24035025040d040251280117005200000350f0500000074042c0c800b4030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202795341 1250 202794091 202794107
    0x1090b0709030b01150e0127060503010815060306180f070f0f0b0a120b010333061103040e0903070b04080a2a020f130204082d0703020f01110d 63
    0x4401c60015103da6211040000d4207890000c050002130391190403840741d948520712880060040750341b0b40c0100800350358020001e030b01942003000014004001080104003c00c41844c000560312105140e41c01d040021035101c80000706801c2c01d0050039818120881c00c200300a44c010038621083e030701c00b1512007043d201c0da8036013880b0b10808031111410114140d11180700701c444611094a884120003d0030380b9150281080710000ca050550320300425540c00151008640901d41c2410034003082c01d440d01c08031003a040d0340d070885010002d00070621180340c41c00004070303002c2e100000d4401c150759542d503565070b25502c2000300042c02d0005880c280804c00555001400b22184c99445a0420b01c55400d1101d42039108400c1030540c1e0409450600050b04040c802c0c1e20300540d015201040d031790003540c008170583e4440e0380b1480701c0d41c1c010002000300c1c4000e10002c0380b058440c000d040c0a80c1c007051807625690070482c0070180c8101e2186050340c4042e0301881c0c0d10a821808001900c1c0035103181000605002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202796591 1250 202795341 202795343
    0x19050c030d052509081005040f15050a2003040f0606080d2604020f090a0f0e0a140a022404030f1506060819020306030c0603010e01060e030610090203060301090b070903 74
    0x150103104034220703d900a40c420401e8544802c0188a0224680c24500c05090050020f03200084820540000324829840382c10341913040c241d0110307460620710100001c40e41180458108503e05000748980143c044041702d0704540c00c502d410b090550700307081801c01000c1319070003004284113819034802c0140d0800041528a04101422001101810f46a003411501210029070054440704091054502800c80301c0d04915100400514641201d20741403c641c010400401c01e5030041001c1d0080280c400c00d40c20341034201c10b025040b6080c0590110305220510301c0340c90f03224801c4241c407000ca80c14800542c0d000355085415100c1442407400c000c150f2008010b41840440e00305440800d50724050b2100e540254440204198416010f0000c40300179080502800d6142c02a022400801e0f40ca03017000d18040c20342018084500d5140c10b201405c403150340b080d42c0d4082d40102081101e405c047c0d0a6450850300303000d1000d42d41c0d42e180301c0000d0040408000042c0030340c0481007402515030b40068031809403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202797841 1250 202796591 202796641
    0x50d020d030212010b0d06030c120b100303080f04050c0a060302041d010f090f0609020c0f060f0601020a0b0405150109050601030b06120c0f160308040201031119050c030d05 76
    0x50410a00c04400341d2141d40e4151010110794401000860304040c024443d0322030810b40000c50316125520080c401a05520030400081074203480000c0c001000303892a003084908045d4181c075031850743c0103400050b00810aa4044640100040502c41c0034455a800300000825032059180c441e507018000b500a4001c4c0c1c82d5010300801d001000c0314222252074161111801000001c0d858117212001503e40300802400f08d0780c0b9402c1c00104a034041c0084c2001e00180c001811112003c1c000341807074a8001492600d804c890311003408050390300420030078207040d00300501ca2140e950301d0501600d800450701200c0040c00300c0c0400045c19600b143c3c0800d0146a00340c0c1c05025441030641042045c1c005d445051503491140c2d0041440c40195500405030b202002c407035075003412500541c110003c54070300400e4001c90380301410001190380c0340c0308400905010310003260030040c02ca850003021803480c4050006000d80050315200700700042003540d6a000d40f02c1030900c0149005811501c078449104181500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202799091 1250 202797841 202797853
    0x150403150507030e07051302040f0b0a02010c050a120507030b130903090618092403050a0b060901030f03031a0301020c070315020307080a0507090f031101080c09010905040e0c0d050d02 81
    0x42c0d601c42d0181c51400d401d420700808105007007000700070303001402a888075421642017000244406a805800c00140b03407130003480342c4503100d0071070184c00d5503a40c910390410001c08001ea0b00c41c4541100b0b80b212845005040010749036100682900140340600001d6480442011046503264140d00b080c1d2038107100f0b03038a03400010303a00c207001d9904080c841704c1e003004074120440074800c405d03095000407403c04600c90311041004030240042c540300415002a62640c0080da01301d000d200030310844941099040e20408200c0d89141c0703e18611400700e500080801d510780020314032241034000d0081c8281070080086590300da00e030200fa5a070307220501c401c4450540109040702e059005100390f81c4180450348031181140d4130302d5a00c0008000007850301c824854000030101e000440c0c40c9a080c0518442c20041c2d521008080015181e810000c001d441450420801c901c10360f607010101070100e0ba002d490119401528003041401c0881985c1c001d90000343c01404007090190002c1c006004064640a070340c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202800341 1250 202799091 202799101
    0x2070501060b0a05090d0c170312010b030106210f0204080a06110721050c060717330f0618011403090a02060307031410090b0604050a141504031505 65
    0x440c05011440d1012130020701c030b121001e0504540885139144a040d500800503180c050142c11590021413034011507001040b4000c64228074040503025000c19a5007604541c50301030010320880c1c000c00c8020a050044100000c504103030741203501c544a4400c415510b0781d8940c401d00d03a640d01c035100241c0d00203040844c1902c00f50150401c603060680c00090250522030884c2179010038080304540a0200902045500d0540d8070a0206501400aa60f00e400507408641500f071100c80c1e02400c983c60640c2500700585441c4040840e600412840c0050360b403d8182c44000a04caa41547e4610754100500103044040880c06059004014100b40c0302c1000e12801000480c105000407a141d50351507006029a80240c508a4007841e400181d500d00800c1c005601a060045100240e82c610500e08144000f4440c074841070188005500f400d64906080a14000000348651041d02c280910311128010b03003480354a0f200650054292009030756aa11580d0f0725001c41e003001d07000c909801c2d080c074003001302e0307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202801591 1250 202800341 202800359
    0x180f060a0b1806090606071505040b0709050105090904060f0204030f0c06090e0115080a0207060c0806090c0a051207030912090e13020f0f031c020a12032009011209060207050106 78
    0x41e000f21000b50980c082030351040c040c0100c40c1e024100c140c0f0b14840b40410391103140b400f40101f51041d40300d03c3c0d0100c41404c0891014010004a800182c1402010701141e29a61207080003a540103800c000041117204100040748024841c641001d00622020380205050005001c800c0044420b65541c0150040e620498519443c1003805440044044031a2484880344204000e6810040f56000186400355560700c607002c0365941c0c00d0001c00b1843c103204100180c9840004c07a50b1114044044070700d8000014002801031280b0100010703201e00500114803440e00c240d011036082c59010a80071809c1c4113480c00075264188901c29a80101491000a4050004525081035481e4050b040390b400001c0c2c1070420040c041c24026280e00751003044909541ca10107101143d003010410b0700130302081440ca05141c95038000c0081104207240c1041485055401000c601c00c6004030f003a8034498071501310380d0040b10040b05924103809810708181e07202c800d2195960060040a220328000c20032542d82c0c030840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202802841 1250 202801591 202801639
    0x7060203190e0a0306090215160606060f0210090507030c0f0801050c09010509042003070507031e0905090c07060203072c0603010612090f0506041202070e180f060a0b 73
    0x40f5000030644008000241d80ca030000174481740300906032044c501d00101c9006150704060100110ba40b88000603109200b464403412016000b2480d01b500c8207111030f0380103903941d10b01c4078011082c256101c5200042c80300a0001402071640080b83d1401e40b03580e400c0c210b01645060103820703000d503e030a010440752440c0c0002c8076251041a11401c0c289140101008028024440544c0c41c1d0f2450441c000c0b0304001e000b000303510a0780d2507190b813520380100c0d0900414218485400002680e25400040d0801d50408100021228201c9902c103855680c0400c0070118042d0001c02002d0a001105102889800511902600003296202034410a081140d66120000004d1440c4c0140d0108010301515106e90400c090b40071540d200819941c4941e6240d07406041030717100c203070358030380004003403000f007160080382040308613894801004110706040e102401640041c000341440180400d010391595400d102102c1c21240c00c1e8191344a52074010303101c1d4050302d1503808961060f09600d160004c907006080c11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202804091 1250 202802841 202802867
    0x30903050a0803090f39120706031103060a0b1b0304030c0617040b06010f05130e01030204060e09060c0a110105130506070513030609170307050c060703020c1902040b030706020319 79
    0x10001d400c10352640e034200724840f184441501040d14600144036110544005642d40c1440000c01c0c1240c90409d00a007200c4416802c15882d14081040c451280d9481c0c00c1c0200751415440500c0d03458404421048500b0030f070241c0e2904a000224000041c84486080b01045032207030f4079401388840034000d421003602d100301d400400071980500031174000c0d44506115505402141002d40c586520103c0c092404c50080e40840009220540103001714141805604010140385059101d0b17420030601407500c3d070000078210b040d150004a03904c10501c1c400e0701e41e105442e0004e40200034038244080c05c02c80304500305106541510402001c650340d40e1041045400c00f00322516a07040d014150b079980005071080000550b40504003043c0d005066000400a5000f00c4040c4c640075592243c8000c1a41840e400a00301c505041c030610a0768030174100403651238881000400f409094951070700c0094000d010550740107400d40309960010a02640000081103030902018500c200c5a81c810411a2a1110011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202805341 1250 202804091 202804123
    0xd0c050604030c140f07051302040305100f0b04050703020703030b030d02150903190c200901090e011509020706060f05010e0618040c0905012613030903050a0803090f 73
    0x30000300442e2150216214a9104200c03c0c4050782d90852002c0c034050f003034083c0031281d07000954200014901410030000c01ba103100c1040d82401d1564460302d1b110b1822030404480c3c0c0c0e0701d8401e40c2840c040d05900031460703803000810400c03160400f070100400941100000b100071130728118154010f85400104141200c099a00a20040c40801a190385070000505401118441404200d5100c2424a2410603c4e00d866070340c01c20f0b51042c0c0c1049032041a0400c16804908008000040d440c0c07100524030b41901d680c0b6201050402c04400d8071401011030490003522401140c50201d51306c4040c0c1c0003059114050f45042c01819112a007440852880344111030200301100c541ca501414440c0203040f0031103500f490a00404000750100c0d0a5420038141000090343c40d8806000f44d40c0c2060030f401080340080700d454005100700c00e5a0010140c05400301260074900c0c4e03840d10415106001c000c4c061580038080da22040c0c3c045c03070211515003080d02c2d540510300625280803102e081c0081d200c0110380d0096 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202806591 1250 202805341 202805353
    0x1101030e030f090303090d030309030801090e061311030601090c120203060a0911160c0306050a0506030a030e15070614010501050c06130609050f06090f0a02010c0627050601080d0c05 80
    0x450b04020320b43c8644080c542602092006024039a103251000c00e60728020784021842d91021f00e001403003030070140c01440c0320900d4050901c2080c3c01c0000c400b940315030101002d070508040e0703042a400080900d86c0403075161040b90008140308016801c42c07035028400d81c0f00e1030040280c0711002130a0780812501c2030740108001004002d00000d9400024041104c038180c1c603d03103011150081c10605a1000c1602c052241c0e403010010441240b03e0254003640300d40b01007015061980c00a80c60300107a1801400308080392074103a10554030102c88050002c0b81d14403559503000c082c507100e809000c0d100b69000c0c09000b40000099254000d200f03c0b528640094064107456031010b80d44461000c2c40b21054034103640c4c50030031000150b02005002d0000c00ba600042c505858901e210515050301e166003541981c100110b5a00103076003007480c1d0498103a0020011582079288100a80c102c1c40360301c2000306001030003402600f880008a80681620000c40035101c1413641c44a00f907845803100300000f00550b0082c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202807841 1250 202806591 202806607
    0x1120204031106031005060408030c120903150402060d02120109060b0f030a0207060603120810061b020405090f01150f1401090504021305030f0102041706010602060414031905071101030e03 83
    0x3c580110780c03001c60020b5260800d92500041001c50b00903401641e40c5600c0010442500c0e03104114400110044a01c41c07403402600d4808030b629a400000361003007441e082d5000c84c0855403078009503250f04d0100d2800b191a010000410240400203201e0308c40307040e02d80680460b1414a1108840352040f111505610b962910288007000707502000f000e032107482c1d0320500071000840241074502c004215558810341402c10b62020811078404c0d43c8030a0600c40350452110141d20890022664140c046400103416039510000c030b403c0030350b03c0b4000762195182050900c441c0c07510b00d0b4102e0075940c0030348045c04400d40714044801d10043d40544940400e21440c000c00c0b980c44e00c2d800030008a0000c1103000b02595955010911b080b4050400401903500450103009590f071812800f141e520080c4002e0031194900341c1c000e510b4031800391000c0d01c40b07110089041c001311410812926501443c0101d40550400294000c2541d080b40d0000c450040030300040744081e610a0180c82c1d100704454000c0d43c540742c0310b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202809091 1250 202807841 202807849
    0x4060f1b09051503160201150b0403062d15120b07021b0a0302060c030706060b04050f1807030209030a08070f0b06100e010e0312040905040506060111030405010f0923011202040311 79
    0x17442662104564075403110450100c071650301c00d00201141d506480d100d0741075103888000d41d2081110100089644070740320300020089203044c4030514000b000020441c4880f90509100420303038002c60046440c111041c01045041e803603052040240340d00b902c1c50030940c556500c6160419010913580403141c00303014809440c100e4000d00c0c006005004491500b4030de0360740c01080d207121740d00c103114508000c03508024604141c0500800b86504451100502c81411524a80340401508000c1016400300d50082d503034400304503c2480f02c0e04060465101c000030700c0c256044042d80c04040314408a400041100c07420101c0c401c02161806448000310000307800011202e0f5580b074466150300d4411056041d0034050791000420180c09920800300302c2d80f400e400e00e50306d00440902068100204081c856400e964048241da041e2482445c1c8031683c58070a000403500350021b0f030090013520b4100441c80c4400e003600c0c0700d00400a9000e8849000340c007510113040040703000e00c2c80060100180c000d456100d81ca0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202810341 1250 202809091 202809121
    0x60207060f030e100c020f0c030a080f0405031219030516030f18060e070501020307020109140303090423010509010b3106050a090506180103020304060f1b09051503 72
    0x454680043c1d41c41014880510782011a8241c1c0009aa85c00802c1d8400c1d40c14019208021440801407503214403900109a9510941c0300c0904a508040382510215410108980040400404441015280b0005044240c1c00074140e000c0c102000b901c894000c5000380100c0b840b82240413081004024040303800c0d00500102d01030101c0c41a6a0302c440840846e2801c14821014011100001c02d2000c20712428038215140d00520305560040c00007400503a8054004d0059542c031140540704010084003007446c500030044c8099001d820200007800300800300f41811700342803880b031000402d40d0741d80d402d100c09038900f8094680f2001c0200f003605230703210b2410084d03240144d00c5901600b608080840301601c8007100d0b08500000b94001800c0c2100560080340403014040840c1e045140641c1a9128842a0403203100e080c14503801000103020300803582d00c4104404100e0009100040301c2c0e42c40c480c0a500c05005074070100b44052004200e42c00d0024101030002c458626039442c1d502c2d030720080f840c264 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202811591 1250 202810341 202810367
    0x906010e030607051308150402190504020a0302090405071409061e041511030405011b03030b1f030c020307020d0b04050703060f061403030c1b01090509090609011506020706 76
    0x220080c03049256241001880e2241c02942c0d142d6450311415040482c07611030f00d03881416150710444540350140001c9805580144d811502c0d402c060a0180304101008215445603a1040c0b000c15000405c5815030010000700074107c8041009503079008083c1d907240c01e034080384c00e80040c0a10058403141481ca00900c000512820501011480c0c002208070903801a00710761100b42e4240c15a898458100a0003022101c941c00914140383c280800280311007040e40b81660341401b9100d00b0018140a94001c08400c1c6c00504500c100c41d400c103120703e008040013003001000034904040311201c28404025120016801084000c298146407500c8100440150050b141390150240000018201e0300c80d03000700041c442d60202c4d10b1480c0001b0780448840c1c07000c8090194108118103000c6c12000f02c0d0f07420300c0c0255140e5001c008003040c4012610401c1603045690014528400d1216001c80010300c18440c51202d80240301d40718102418080850540c0b0a88000d80d0012400f44019401413104213214 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202812841 1250 202811591 202811597
    0xd020a2a17070804080312010806010b09211006030c05181503031c06050117010b0307082701140703060b07110114030f041202011104170a050a0b010f140a0302090601 73
    0x40540b41d2118003a80d4401c0c2c0c0003400c10b50000039507004440d00015420b0040c40301002900b01d540c50902110600d11039501441d1049030410b0010703940e040060020940c014081003180c91401c001c000c0c14004100a00090301c0c808511207002442e49800b6190041c42e0390f001580401b00d8881c0c03030901c0b030003035100e171155507050100780005074920301395403800b000c1c084840c2004a1854a0007001503c45103452400508c0c080210005004040c04001140d8201c08c0300d04d05400103071307124034504490400e07070556032440e1500080d00314802601504102c4d82c43d890400c5074a02c9403604101036003202c0c0796201301c14460783c0030b01220303010030b5400380d01041c80803041c145a00350720810104404564011a003601c01e07071149074180b0080c0040401c14000000890000300521160400002070900452160308100d1080a50042483c00203006061409131321008442400320702c7c0c604103012030400d0052610b1145800b00c0041e4210344a0300941d050b0380c010b0002c0d02810301710307000e00000307200080186043c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202814091 1250 202812841 202812847
    0xa0201030902040b031501030c09060605030718050942100309150c080912031803040509070201060503060a090b040602091801030305091005030907050111120d020a2a17 74
    0x245c90622080074401c1403400807150039030440c82c3c1414840da4542103c0c0e0300d03e03d070240900c215504003085a03000701c414142882c2c08842c80140c1e01d0080c60036042030b03420070032030000c0c84032544003c144c1941c0107002911004049100c0031441501d00c98214500b600082c40300840c3c4a0340c107000300e030300071304801620700482c02c170391182c0b00d40b94505480d0001001080d40e410100041a0348180255040114a00604045050a10348440303900001c1c2220002d080358045880f445c14041040ba00201b0014003840054a414540a03000307181c14402e80740280110710016031064280d109181c69150b00a14516654072580c07540c2c4001d4011010003030700715124220344e440c2c40c40d003e40e0b224006e5100741d850711340e00c40040f02802241d1601041810a1090600502844480108118080d40e10a10300088a03800f000d003600c0c605100ca1060095202d400202408003902a030018880302082c0e440b401807605040031903600410541501d4045580300540c02000100c2150003c2261410f2070001c41c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202815341 1250 202814091 202814111
    0x11060115170405030d0c18090203060604090e0f0105010e04030206150a0306090b092a040b06220f0e010e1803090a060806040b0a081908121501030f0c020a020103090204 74
    0x72491410758040e6001e900214540d903c4003404e01030fa000d4070002d890700c41d001e141a40c0b40d00104025034018240b0580e00400015500d8403060300740d40080c000b003c42031220440e6140d005850b00481e02401640d54204000031520362648400a40507a0341b5030700602c2c065607a49903d0002001820f00f8a910a000040020228640d8040c1510301c034001c502555050500356182480e100b10120586100113801660001d0300c10010358005818900f501c01103440d2840c0c400042c1148922902c40c000220300d20b041f0318440400700100c005036520180e20f8800c054079a00154031b840800d10035036880385049400030f081c2003580b0340c1d2001080440400c49040000c03100028a03000f0542c5c000000103091441080b0052a003070040c000f40c44800e903035000d04242001d00d001e0300c0300103c0402000300b0546120200810904108607002c100d07005070020400e0400102400d61100c0e80c40725035000a0400b2140000b43d51984140561070510f0340080400c4600c547c015070140c0301c1c160059901070b80d200103d403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202816591 1250 202815341 202815377
    0xb04140115020c030f0d03050c130803041404021206011b02030f0f071a0406050328061701050906060d06060308030c071b120201120e010c020303090c0111060115 71
    0x3400790a004400350010301d128040240741580b0388040d0b5209500a805c14150800d0201c0c4100e6003450702d20b4045441d607150107030040c09102d0301400100d2500540400107040d00d011000c1c009440745804580030b0101604100300980c002c84201d240707181016000704103070b07602487d03140c0c007030b043c0780095003403081440d0300028208511aa4854401e4000f8244800c4064081c0503503c0504040345a90450701d03489045500725003d240a0300042c0040080880c19004080c0700c0e0149074203080300040d612240c01c4550700050500c80c0300b2000c1c412080780400100c0c1c034044c00b40b00e00c10180f403c020111070b43c0e1201040400c0c1701d07a00302642e40655805010010960b8240154031030b84104424540c1c800561922940b056070301c2580100500c16042c061101011a00003c0003880d02480d20b08481400841144001c0c100c001e100d004035884c000c094141d1a4001c805903118a0340d120582c0c00340d501c01e10042d90880d45100303641c0883e4100c080180421255516008002072051400c04481c1c0c84000b214 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202817841 1250 202816591 202816631
    0x5030613090f0503030601030e0304030c0b160c09020a0f0507020d030e0f03030310140a030c060e04020c16060e0303120109050a0e0604050c0a090b030a03030e160e0a0b010503090d030b04 82
    0x1607803d50000410821a540c00d806040210300c03442e401140f5207450754950301e0341880b0b41c2c080c46015103000500650b01026903a4080446900a205010125905c0703503a40001d501c4056948089135801440c410b5050148069600058010300481c40c0124a507404a942105c5d103107816501480300c264100040e14100042d51045807414000c4020701c4c03c008840781100b044524a40c42000780c4141807000a1003094120704035126403c02407481d200c0c240c0060080d002d48a8140b0b060300c503412050400c43c10358081001118129242c00b200421070605160702e911850b0100381e03594060700c2c01081889900d60040b80e0114011100044241510410343c7c140442076505594075400110020403520700800154001c050080041040c0044400401c0d150100c1a00107007d140d59084c5151b4110814403184002c514490400c0b42c5c0980c0325800301c3c8a01900396010807425107040c0030132006501400850b030058610000800b0202141c900803805414100c0703c65400980301c460b802401c102d10004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202819091 1250 202817841 202817843
    0x90906031612050f0109080415020304090c0e040b0604061b1502030117010c0207120b13060c020a03140304021c060209040603060504060c03110901030f0b03070b0714010603020105030613090f 84
    0x14182e2100e4a420b1036440c2400c890840803143e458408070f00c000848580450b0100c540592140141505540e026401d600aa6015044c038034204003a201105a110104001da40400c503010040b4403c0082031103001c6c050380c050700000c1602c201c040200366001025401481c1c0c41400480304a100900340c40c0143c1c0c10a900c00c4100601d50141d520310a0020b000e403191400c44c510081528610700b2134074a442212400001c5d141c4000380c0d011608403045071020401e4250860014801da0078410350095441c0014482900062201e040c81900c86001c6402c13280500e80003000e040342c20307144132800c002150914900310fa046900300f2082205032250301800c0000e6000d40030000c1e032841c25081c05e03000c1d00c25a8402078101890245000e104403081001d849681800380b13030008012803140822002004d9000206515101d02c41000074503058010042412a200311f403014000e4a03001202400d0b02d2947c00001d001c280240b0004529040c50300c3c01100340c9442c4080400c82c0308030303512280c04030003407008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 202820341 1250 202819091 202819109
    0x311070614010501091a090607060b0a0609050f0d0c0603021b0105040f02040f0507080a05180106290a020c040216060f0902100f0206130f1406040507120201050909060316 75
    0x100f20968004910030004c0500713000030b0400785c45001c82d10032103201c0c20a900788110408103800e01800000da100c0400c1d1040980020b40c1642c07202c402800900507407103090700c41c80b001031203110035007010280d065807140c0c000106824541030003810b07000f0390001100ea0450503109d80f40c64110890900501740180d0049414030072080ca42c2c014030040d113880f0320400642508020501c2080d65220380360310751005520100050f00e494512441c40d40ca6010300340704620790b0a00c2d002052144480c0e020703140016180e00801c60f03456500741d491b13903580900410300015030000b543c070300c3e0b243c00c15070002c0203c00400d00d40118200d0207907a035142100d1450a0b42c00300340780e55004840850034140e5480b4417011f0303e41030041e0f0ba41c518210080da1414010900e08030841400120400c20801d00c404c58030f007590129210b802500340f4070709156111400c550036074031031103948400208955480003405480d40c0696809180815610038400016005003001d41c1500c43d80361080e4418a04941c004060041c043c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 202821591 1250 202820341 202820381
    0x905030306122b030c140d0903030b042a020106050d0f080708031f0f050f0d05030904110d0c0801030f0b07020f030a020c090a0b06031602011b030c08130302030a03110706 75
    0x508018116617030100c2c0340c801d01c000c180c8a1b100000c0304405072440391a8814000c0346002c6103260450103442c1c072103201ca4005003400103084144003600510780040c00804014044070307085140032803d031030140c03081a820041010042010030b0810311268011401905024070304000c07a651010160300455507400a5032103514850002105d00450b60b000b400c1c401404060f240c10500014101c000080c08544110414445002004014070540740300342c000500c2085283d80542d0320004aa100a4a5100c414030b445100d48210780541c3d9040d068a03007003003a1005014282e03443c0f00800703801802003020340c4240202416050010030003052040d400e6070160a43c01684418417000d154042d00c00c441c00780c14400d030500180c40711404d403507026021810002c1401c1000704160300404818185132801c01c2060250101c1d107425810007039041c4400e17a0360704450354641c00ca000c1040181c031801001604100301c601902486a0000403075406083d0155150041c030b5a903480817984142d1088040001803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 202822841 1250 202821591 202821673
    0xa330e0306060409150c0c080a09030201110a0b01060509010509031e070902041514040e0c21070f0807200d110607020c06131706040213090503030612 66
    0x1070001680115041d07405211800341d81d5282d403109100310440403402541c0d50161a0202d205a030b2140445400a00050b5501071038800282003152600042c0e0100f00d0000304420590310009000b0342040d084580040240d00745001203c4a0780850205410043d09001508580c1e0b4140007455410b200c1c200100000118109510309000719640329034030365403060004201119a03101c46100204452a0000020840701c2c00c1110754003694201e483c510201e071007044130740c0c008600188000140e421410854559800105000031011103800000030301d9170300581c0c00c3d40c0c011545140c0001443c1400c0e507443c6005d055129581d800c5140885045d40544240402d181e00b000d108544105210042e20b41c0d840c00c00b01c003039500d031201c100c800d000d10400180c01c0e40402d1020500d2000e016400c0c0c0322640a01c6880400c0c2d52204290b405a22800980d0018445208280f02c0c0c8841254088061070956031140100708250616404042550080e4105076200d1b8aa1603406810381c01c241c40c44421000c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 202824091 1250 202822841 202822843
    0xe0702100b0f030a02090901110a0309030e0a050105090f2b06150806160512010308091302130e100305030c0d17010303201e07030201020c0406050a330e03 68
    0x2202088034000c10501e0004080c030780f404280e20120316016104504940c464001e5103004001030800c44441c0344000c038a02e80784540c580c0051003624000d80d10901c40454030020003851090a01c601da000c40c404021181180c20441144041a030700204065800f0f20464840644808050703034500d41d022400980d40e041155501c60f0200f003070382450740da54003281003100d6183d8031a03014144a4010403501c070b460000390700c110f08403620784251040441e40e40d6524500000a03401c01121740d4422888440c1d0201807402e0351090312501c040c5090b03850480e40c41c2c8504003410000242c0946d1646c60481c10110124500b007009000b5885031000812540010100003020003000c00044010015401c00400c04070b940041c801c8215083c500e140300d030700d0f0341c1031413442e2a0040d007001c0400b02d40c41c40c043c00c0940180200c1c0400c2128000e13000e07141c2c4128220f0402040344c00500940e94002d1003103405110232504e110b0000111684090000402d00800d6240007000380c030540301800054402e22880f1080c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 202825341 1250 202824091 202824101
    0xc020603012903100b07050708012309060705180423010e0108060103030c0312090b0f10080a0c0603050705120a020301030c060c110f0604090207080d0534090e070210 73
    0x15290344218210306022613203021103400d80c443c450888501190300410f1000178081ea800510045000700720b506c40c046041c0b581e84c044503501e020051140c50001e25468004526144185040e9591520b00300648903821140006440e03659049540e8240b440c102c80c0460320882c0410740c42251401e820341c5410f4000a00b040e050b0403280050b04004010000282c110b405107203810740c10300380f0410060300511114000c0c041c80c4005001c0512034000d02c10040064484140a03c5c00711040a8603951581070495948050002c010300007820300d00100f01c2c01d13220741d0040343c206d122840d10390304e02000315208503000e820aa41000e5a2a0300000400422400c160070034000e0805081c029034500c5240c45015261480002d068003820340c0710152002d079a03072041100c0260080705402c6440354503a09200c00b494020310143e11000385041c0204006d404d80300c13a0301c404d181a2121148810f040610314896201c5014222024010702901c00304000100b51480b910030103a80d80103100b641c40740310b034400540d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 202826591 1250 202825341 202825409
    0xa05060f0109180207022205040203060a09080702060a140403030f0e090c0304060911030118020306070504050901060e041d0d030f1a0607050c0d031701060f08010509070c02060301 79
    0x301408804010441544806a0b8001e043c400d005072500428004140c09036240f4502c480d00700280c50000590f410302e94041c03401a4002c0d8212410303070b59002c0345441201c90401d00641248400d2041000500d482d100401100070b20f854201301c404442001c03000150403540044008c20460009907205c554011401c6080e2803080f0761210450418400c031a516220143c000303000951151022810b02002c480d9180c01c00300080c008012110110f8401d000108110108900c217016000204030044e1003441031745c066a0f40149081c020f41d10300700c2e040d54400380c2d050206400540354020040340d9488155641108650345c00608107643e1030640080403a0400704c1461000d525200e042d24200f884c00007400c003442c00c192920341c0d44008504210f8504070440512540c803940000b4642e08045d8401020b034500a80d08140c609540d0321b424090310085001480a030004100100411440c85d121078443d40100f42401c00715a071403038a8001c50880e40c400d0300661703508901c0c58480010404c1d1141e40c16040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 202827841 1250 202826591 202826597
    0x3020a0311120307030221131109090d05030403031e0504050c10021903030b0415030506010b030f0a0b061603090f050f0d0602030601091806050906040e0703020603070c0501050a05060f01 82
    0x20a07a555100c20b0001034081000c055002c10950800c44600102c1540d0200103130315400f09291000b00c0001904141e601202c05d21304d460001091800e0001000703016600d0300000d071035450488ce03011100d64100800a400705500c0c1c01c000340c1c1c0803042d614003060444003604085854907045c24160328010034101800e00899000005080c526070118401c21000380301101805400c07000c5c1800c030b01a00c0d0038221035600030f00c2d09801b4100c0040c04403082086903c190195071719070b80e9030800200c49000c102c48000000c40c0d5a0001440303c92560b228581d1080001c0c4140d0600045c404104408080c07160b0480c08074070101000c5c0060000320f400032000749022614900040c3c0d41c00042030603101b0580c07000f061550040302040d0035070b001d04144805444103010301206842c210300f00c00080c00c5503200f0b45019408a0000c111903080c540901102c3c089004000c00301031313245600344407072940002d00d980100164070070001c2c00601d00b03004860003010440760114080c04c0c420100305034000e01044803414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 202829091 1250 202827841 202827853
    0x905011106010e070e030115060905030a0b010b030403030603081305010206060d0206070b10031403090901140904120201020904021b0708030a170411040e01150906050627090403020a0311 82
    0x10300034000900d18151410314110815644450805540301100e032075240d6455402c02c0c005000441000000104445040e030303541506994a10a140d168008080c0141405200e01c0050240c290804011901b20348a03160000d0040d5503502c6048458000c0c04400e40b0318185800700300403542c1d0401c4101d400060840c1c1c4114204500e03800101d4a00c211800284104200c8000032000c2c1041882c000086421400404a20108145082d203035405501c000b4450701d4040000f045001d00300315021304540010344044003544440d140d010b03224950b200d141d41103640030010070780661150f00103405a101e42403004450020170b0314205051651641059a55030b10a00410000b294480525085440e550000e44140c2c3c45038100b000503404440c400f150000d051010714400b0007015480003844003088a1003404082e100c0e442070060301e010384201e9034001c00500082c4c001d1000743d08946044140c0c007442038520590320001c54103140c0e007240c00b5805600711400303000505821600c246c040c850b542e0040c2c64 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 202830341 1250 202829091 202829117
    0x9020405010f060c0f140d1e0e0d0303090c0b040f090e0a0f0201082d0f06030705010815060403020307080a051018030813060f050603120c06040809031603030f090501 73
    0x11100e203140b40040c14100b04c1850b103000340f040c030441b400c20701c0900c0403d0303500424143e04090102415140c0320408070305a1101403820b54420086400f90400007404861500100d4900320060403075800d041d6100c4021440020702c01a0303c10080004088003400d00c3d00382440e10400d20304070b07002501088820f812000b5a00000b450948000550a0742421305078441d80b41c2845150381805a40a203038401080a010800d5088404118920403000004c6601c91960340905060302d0743c41522805021680740340102c0c584c4200f0709041c0305e04a1000d40058100380c1c1e40d0f000640340110582c03080320070f80c010010340400d0220074131180d00407511894060102e02c030940742403039510820441c0a03040161b418046010715000312078a89460307810541c14810707100100c1003d0010b00c000c0d82c1071403280c031414001d0640d84641340180c2e10f44111102c0078124039507a40d141e1084991104245030390500818400301e00c000140904a4007550103583c0c0c041305401a1680603001d203400d900140d0600c11a188000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 202831591 1250 202830341 202830347
    0xd08010e010b03040c08190210170f13081902120c120a11010203040309080c0d150b06040b0705010f060b090904021201021303080319060f140a120609020405010f06 72
    0x41e04480ba00400c095032a038507410300d01c0f140d44040d04001518000c40caa24880105c03400440804907000300c59412444070780078416210f500c0c46204220000020a000504109070003041386e6000c05050208866000c4640d41e070801640140e05840060a03080c0c0190710300d50b4100300c1507110124001d9030500d45541403416175030703c072510240c5180024000502c007103414405c0984480010b9028000c1d51a4100f074031b00075004010b03e004031602803107004000310003898088079140501d0742013029404c03031000349074107a00500f02401da0560008010071000410300c0c078900087c42d69070702800000510441e030180d0307041510010350040300d01200c00d100880c026503a414056404c140e044884455994098000d240039000381446c540410030f03010000000c8c1b00c0080c00840c030903200015032081c41c0e0442803580080b55240d00441081c000c3c00d2005214480324803040780c400b80c400a0040150356980d5501c028820001c010807501c1c2134444126100310304141c0652405800c0d03000c09080d1880c1414801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 202832841 1250 202831591 202831619
    0xa0507020304210614090c2b060504021212031015050f07030c0c0b0405090610080c03040501090b0127050c0f0912030307210b1f03020d0504030306080d0801 69
    0x5005a0203d261100200100ca92144415107462000301c481460411005034a030005900124000c1c51480340301c81d1200c400d071110b600360950259007644032484075201c1740001c010041040f0381003032a0352032062078503404101e00c4034070324040d6510503601d16214a800007520002da04c22180701d5240180400555089415038442921603401c0a4a50200c0d0404031641411510050407000b420140490005c124100801c1541c000740c0300c900d5207403549414040300c8040d20590f8000200c41c0000304003141c3c059002140c225000d400046130303528680d1145111004207074400c450802c0c2c41395903000c508224031601598181da84404200078a00840b1181c0c49101d4805441070380100001c0e140c13070302c0d503486200c0d0190f40b2040046030b480340b90156001c0c11580c0350203a020100114284e9008203554603000b5520010409003262600d000d00f5000f049601c4c69800c07080b070525409000e011004013541c400c0354030860007a94007185c52843e2841c0c946c284a071065403d002c01c00c2c0c0c040180404c0c11850f0344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 202834091 1250 202832841 202832879
    0xc06011d16140d09080a0320030408070f150501151d120304090e0303060109080307030e01031112040308010f1d060d020f09011202030115030b06040b011b0302060a0507020304 77
    0x1c081d9280e40d00d88205442031041041640103d880d04c1c071200c00b4040c00034040e0031801c2c2c898804100d00020032a004040d070750700000380b0084440410029001a41400c0500302440c41080c411075880790613519046c00c0d510094410743c0703040d41c03000100304840c08818a40018040ca003010700249a64500101d001009040824041e0300761584068194a00b007080303500421042c801001034000c0051801e840354030503600d050004856150104d0605808801c560101d079154072029030780ba0040300150054241134207402c08800007803040392441d024200d8094455442655410030660402048224001d43d030340106c040c901490310500d07000b154407000c01d904142c040b03802212038031240c03002a40f0580b00080194110180100008201c0d1040c400b80c07200a1084001307101159408030070440028591001030140601071000c00d080d4246540500d6100b00c061406201c09280e05100c940391034071204007240141d00480070003a0b024914451190040c10310300c05146414034044d0f00190003084414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 202835341 1250 202834091 202834097
    0x3050c0703030b280906050f03030d090303090b010b0d0c050306180604020403122006070903031206030b0c09030c090106050403170c0111091207031e0809060c06011d16 74
    0x750812044d900c01510014050142c000601d18800d01c9030028680b00301803080f603101904204012070701e80b400c40380c0118581c1010b0700845c141030300500c0759405071890407001c0e01490f5030742c595a004100c001004c0c074082c001c40380720b003a512044142900111203420030010100a028400e111b43c130395541c1e101d50201504012880f465448a60005000348a00c0d44000c100c0201c6104005942c0c0e081280034030480c10068407031081c004071281d20354031a4022a54840002e41c6051b003400003074002d00e0714a1400f4201800040d46036102c1d80d0b03006501c101a22010132080340452240124601003064000d07181c0103507807029071545400000360075801140401485101c04041e1034506a0314103080d28200c61040c002071207420440d0342c00800f00d0380131490b1180101e2841c0304d092400300c0c0016035201242ea01000840318484108000c1000b031a0302001100c5820342008002400c2e6070703a402a100c0c480544000c4c1c070341945448008000e015404143c4105c45614100f003220504c1c2e203607040c44010450381 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 202836591 1250 202835341 202835351
    0x304050624040c03022101150807051b1006030b18070e0c0f160305030a1128090306020301140f120a08090a05060d090c06090f090911060d020d0b0103050c070303 71
    0xf0106501a009450007400080c0f5240000c1d486010f0794101e02c3d0407281c60210382c500c6a00700000c201e6148604072821408940c1c108021612040c090190b44180440c03c0c09469001c0ca8001400081d120703241d00986500c1c4801c0140561061025160b0b10325075000d80c0180807031840c06000600a140060070320711030b001c0101c0c0c0084600341d018200c0d049040d200040f10341d40100c80c03801078095082135072403120940c68150f800305c400d000903080742c1f40c0314201010710b50001003140c41401c1c0c1c40b8000c03d242040142c0103400100050300c2c0e0016601a148468070244025000e0061241e01541c040381c25105043e0070100c191580320124950200c1c64000341c016607142407407408110070451541c042c98100c0b4000400362400101541304c0e4044500c28a1000d2016595901c221030907401409090580c41e1040802c00000301d065010003210361280000307000003007066001a4064100c0400c00c1d5660b0740005002c11600b840e482401a011024201040342d4141108001d03510b0045000040908d0354072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 202837841 1250 202836591 202836611
    0x3020c211002030103030e04020a1b0201020f01140a0c03200f1e0705101e02030a060e0106170105040204060806091b0c0723091b09030307030302030405062404 70
    0x1032090340d06549800084400d000386408454009510910040e4005101c61b440103100b86054000c0324140c040c550b40e51020000000d41c2c048408803202c00490551040d8400d42c2c0000e02c080c010060644004d40c0e0608442c6040d01c483d2050b82d10182c80e0004040c54090000303c604018482940d1069443d04015114101c04031002d01c05d1240c000d02c02c02c0c0002d10100040c101c0a00e00062400511860585007012114580d100c1942c0707414010200c20f02415880c2422004290b000e10b51180e2101804110907550300311105800900f07030007900018189082460351180184c0219004003400e8904514113841c00c40018207840c00a031800344242d103c5000301d0306070310300d01c1345040340c2e42c0e40f5048165913606560102941c40019110744003503003081c40940c142540300e01000040781e4101801141c07503591880d520b14507809442400c54600c080601c1400003076101040540560ba11075200141d0300e0910b42807041c070f44400100b013907000492a201c50750204203c440c1c010044a02514041900005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 202839091 1250 202837841 202837879
    0xd031b080409060b0307030b09070206131509030e181501051602040501060e030c01020c030d0513080a0f061b0c060e0718020405090c131203090b18030d0c03020c 71
    0xe142d12040c0d18600f00701000c11100c0f440d1005502075080c9440400c1180658800d105c0b02d603004481420242c0c208074006a10488000700d200d240305e116403006491a480d401e000001c82d070800206600084550315450032500b41a6803510301182811440c9040c3d1826000e0600401004c1c8050742c1001030100f80b10103282b41e051b0411030440e0f0300504c00d21041da1145801001d4403a0702400c24483d2050001e414420b5001243c852102080503000c2c0076015241c81c0180ca0961020101450503031720344400081d0140f00b071020421081c4142a440503441d0507091003c107865002c021000081034001010780c00ca40c1144c3c4802096a00041c0030401c040f0f0340740c104d0f060000039401014100c070004191110701441c1d9000380103446e4111001d050740d4481008081c110b020701c2c07070302407408000d1754003e000c08071414100c084114400d00d001c003030b50b645400e02000203030042d10308004541e0145020807503a01d030600001e403007110035180031404c6500d581c8000b941c031765961258500540002e40c9654445030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 202840341 1250 202839091 202839097
    0x2060702011e020f010609060b0304080c0703080f0d0510050f12010f09060e1908180d0807050d20030f0c0705031903090506030f0402010f1205130209060d031b08 71
    0x1c03201080c1d00c00c501e0390320b02944440070310503405020b500c1c01d40041080501c0340700b031605982850100c01d05550721507840201c56409030302d000220703100304c0200100084c0c400c0003c18400e00012107143c0c56820450003141600c82c0507054450400020b5020322040d11402c0045441d0b05d4100c400700011410380c4031b903078010800407a10000e0b040c101000903060001c2c0b500b10000c0d5100100442c2e041c002c0521044098002e403400003080f079001088102c45a444940244000000003820855200c80710342d5040550790200200b00c030250030580c15000280d4201c0071181d03a440d000d010004108200d031140ea84c03680303d940c41c0a4003040e804514003e9414003002a00d0207040080c0458920a40000d5800c001d18050402180003a0722550080b54900b805401e4900500c105004403c55840b65401540c50404076248513040280c262200354181503a030040500039032003294400286800c90040c0144000014500b0707015080901c10b100c00607500a2507511400c180119a1001d0300592801d580244 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 202841591 1250 202840341 202840367
    0xf0905030d0c0201080c03010e070f030209090117190b18010912050c0f070b180f090c09120c060409050c12010e100501030b03060402150705010e071e120206070201 72
    0x11050303492806846802c00c8901e11894001d0302d8411340c42e030391000100d4242c402401400520780443c40810605401010b18030030020f00d40c1000750a000d281c4020681c0c5010990042c605001d0360070f0142d030290000d0089036060500044100280030641d00c42070200c43c0050412038040f20b0181c84001c1310703402913004e40c0100d0741c41107031403190384000e8100401035004460391440b40d0068020020014400050607001c41d0440c0c95a40d00303214000c0c0742c48645007940c2e4451600f040d4100d00104240d40c4101e000c0e445101d1034070029407070703404000502c071540a41e083c650340d45a12170204098940e480f00c040d541180e0724a070020410b996020419246800707049200f9401e146c009002080c2000c0008540344140e95440c2c0182c44181d9550044082d101028000380d01034200340003040160a0600d9604596034480d100301d0f1420341161346136821209040240400d070740004009202c240b8407508180c000c8480d20102030189810208c01008103100601c000384106c1000038842c0840e405070002120720 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 202842841 1250 202841591 202841593
    0x90a15020903100b0a12030915031116060c1b14070513020403062a030b19061101050604020f0301090207022b05071a0a03020702030304120f0c080706050a0f090503 72
    0x1014040d160b8805080140f1354503205526a085c017288480103a02c0b1210070942540c1c0d480fa10910b00b1000d448100c01c240054810141c071010301c0c3c442440e10100400c040d400c0d594440b0038045090501d001201c2ca0b0742c00b20020010540380d500c41101046040500c3c094020665034410703944105c9192070000340b9031041d13410040f001360140c2d0641c466030180003200c2c09a0010b028005007482082280441448128851450308005003a507501c00d030300100c82503101515251004841261a00d00401c0582c0030a0000f1880b0000c101c0000081c011180c00038020389041d41480b12400d0843c44d030340414003845038240c3c0d01003044800e6680b00301c400f0002c190001c3c865811405410750041c1014003a11302601c451046441c00180d8101c1c1000141d1241049440e0a0030440f140000710080c0d804140b040e68184030500020910b000c543c9050031507240302e400c0b01d540c01105407911003400c1000e40c1c4401c216800001080080503085011200f9044403450410101c845144c020340380014107401044e01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 202844091 1250 202842841 202842853
    0xf050f071208010f090513030509040b030303010801091704060e0d080409060e072007060f0e0603180d0e010e06030601120f20032e0305010203070509100206090a15020903 75
    0x1910b401c0b800c19810b840d4000e00140311261078041170000e8401c1504c50b4010100300120080c0401c0c482c0d009071009400040020851702040700004e891034000f038010307180d2a55200307032480802c100e404001002c0200c00a034203003010f00c0e1090140c08444840f481034059900590188208160101201d000c1d1440031410040582c496407000b240c10001c842100c0071506c40304004c8189406005a803800e000c2210040008909100044418120103040ca105006541040100c0c6a4442c03003d0340c4038032080e86901c1d07001c14405050515000340c002114060121059000750a0b992100040303040d82001e80e0302560725120000100e80340b4410025810340c05e0f192017007408000e0a13a400106905c030194600010b00700040c2100e0546220640c0c0001510541d400c0c40c04050600f40c860140459000305156101a42d030345403075099034070484899000a100141d07007a02131505e480d0405498030944000e00345807407c81c00055840071400800785c0140f01c0c14045207a10301c901e40440b10085405420307920 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 202845341 1250 202844091 202844123
    0x50403050703090608060a050f031f0c020705220518010e010501050f06130e1f0f081504110d020a050a08240c2709090c03060702030a0f050f07 63
    0x1000790004042107001540036080015050b12a420b1603010f486c00800b44000d1501d0403040041d4621680701e80340d014050043c440c0000b0b4140c000c41d104001459002150038000306600030306022030307a04100e2058454120b08a20714218005d040e02c12020040002011745682c080030444c040d210004500b25070030301181a40c00c020640026048131001d03036444050a8000d001c00200b40110300c001d2030114409482048501b075001c10683d04202002c0c5240f807500209014481e00c0031340303030b0060004942590002c1082000030400350389070305003082c501016030a040d03544a1100000b1103072188681d580c40940c20955a40b400041c0c01094010483c6520695a103000c075101e050301a115000d03c2c1c0650703040c00b0b881c840d2210b99882551610030305c52030040b41d00718500788148281e01c000d01015446000740d2281e2a103105250090a618000b040d40044400c205890b040c001801c2c07508540091007046a11608064031020f9010541890364841d107020403182e65600070802c0192180d17050010000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 202846591 1250 202845341 202845347
    0x212130b070311100c0203270402040f0f140607030e150408070e090313050d08040312051b011406010c05030d05010909020a0f0b030a110705100506100c08030f1009050403 75
    0x91076031a043d07060ba20035248084041040350713112078103000960400c115004641c80da2a004042085280710748900700000c00c0301050403604550007107901c200b20701505114080001030070000074490002d200c03403103c900502040803400346442c018281300540c248200140e03504041d0400d0494050301680d10386a8581c1c01e19962802e52180e0400a034210010441c1c400000c81266024413061007001006442c043c20f1050201001c6025a4041c50520000c400110701940c2440750407440d5840300e441d0b0001c804d0071465100c0740c8001345100c2e85440d0300c1c0c001c8461445c2a0662200003420305011040f11428400c0c00d51141c10203000c5800c0c41d003000070aa5800540c00303220b4643c002c0d101c40152903125840c1e103940b481c060054034102d000510010710040095041005442c5d40340c2c005508010503599001c1c80c0107030030384504405035158810001a030404a061080a0f4100d1410701b0380c49000e03860f40c1480344400b0302003d402c2d40110700059290084a0f141c0e0005190784081002145840c1c1001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 202847841 1250 202846591 202846607
    0x30b060607151a01020a171c020f0a09060806030715020f0a0f29010509040212010e060a051308040b03040f0b0f0601180b0d09021210021306030204060212130b0703 72
    0x40b1180d52222140c0286540300042006c2c1140e80300f010031041c00400d5045081f02d8009a9409511040c41031a10540e440c90f0300140514140480c0791649a111f0018003804500140e048002004002e0040001a590004040c2c081b19503a88400f0f41c8010171a404a0418100c1243c0b5100d5205915031402048040d04010703282c02e0007181e10794141009030850900e40c00d1080d02d0010000e04100040c0003910300308107013a40103840242140e0705d2622800499080d9131084078034200941000f410437110a5040c043e9581c0031000b40c141240303417074440e580d001d154002e60068108001001c00090100302800d1071100795281c001381c505c03e251620162440e000c0900700d900900086400040e030b00403001254010301680d404003a5941403944010840b4014052044240d900c00b104071003502ca00c450034404400400b040410250796544c0019580c080e5014952001c0101441080100045079002c00c000d011000d20681440d0b6a000d0708a0110040e07121350060f0018050000306103041580100724 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 202849091 1250 202847841 202847861
    0x40b2d21071256011401210b0d0f12020304050a05060304060f05070203070c0e010308070816060f0504050c0d0b0115180b0c060c0702010504030b06060715 68
    0xc855a5603191281420400446500208481964030080c06441042d205050120f80e03a40300c1d003425015160301040c2d914111400c10202007443c1c403407441c5101030050041c0e0140140c100004542c100c1c080000308103002c4421000c0103000004c203a8200d4000507007090704140e20041410750044807a0600044132030b040c1404442040d4210f000b003106da80088140e604a4030020811030303005207024240505640000c008442c4a0754070900f10030880f101e80710343d601940c41c0313600440e102c005030325046c40c9030504c0350000245c11200800410000c0e6490084881c0c80d640003414940300c0206810380880d0b000c1d0007400900c41e40c01d00b10b13010601c1c3c003143c2c490740c859070040044803c1000c00300c0130301c00d005071844030180501880e80c0051001b00501c503103800341000320b4941000f00307240701003200f04900c1103904248084500050320a42e00541081001c1d000080721800da4501036051f4006805071250340300041050080800050701640c1d120103032501d80360480e03102045401162141c500170400d84032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 202850341 1250 202849091 202849093
    0x9021b0d030e1902030c1003020903070f050a05062d3a05040c03060e030c16061e05040909020609040c08090f011808130b040906060e040b2d21 63
    0xf4070b01454001ca2061800913034000e0b018210505080c410300648000da1004102496002c11403040785841c2004510010201d007042c03003800a00380f208110550100340c2c0400d00c01c900511000c0361200d90b0050032141007180403c85280107082c400417200e42d000c0c0c01c61444074800d41310340c001055034040380342041e580310850804505811f5808103004030380003a2000307080614a0340302800000c2c2030750b004800c442c18600c112410408170075051403800480310b4181120842905082002c182c005130710142a00888149004540c8400c0f001481c5024070f101e00354005071620030b50002d540b0f40b04d0807a0281c1e807015006101541d00044003900310b001c2a51010554800c0c1010b140340e00c4010311a00740340402d800c80384540498141c0f140341d9543c00400b2f0303d0004885400c0e0001d20030078410000d1000f13010048010403c1c6142210140003140c08840e902c0c0101d09142c02c2e40e41c03558485400d100003240001448001c0c258030704c030b550344c0c8402c070810080e0014001805a42052604401028241c0c0100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 202851591 1250 202850341 202850353
    0xf07170606120307031404050a14040c050c250e0c031e10030f02130203040b04150501050609040504110604060302040807080d09050603092107061a010909021b0d030e 73
    0x801c0c00302c60041920010001e80050000f01d00091064006100c029060744040f0b041644850000302c5a042c01c0e40050f440c010603413070404041c2040d0245415141039030130321904140341006402d031510f400070300701c1e034124090f55115a0500441ea006c80042e01500303903c2501071602c140141036942c07050340c0303030303a00c60704403420b8400030550405600c0e1060740460301380f100251070f664038144005d007959004c87e0711080d0303103001d40c01c0c4203424070165100398000c6244900900380f500309902913040b180f101c80419420078005100079111001120102a01524002584c2e0340e00e04004207031800341044158406000140003400e00e038990040d00c191034445056600c829900c40010b0f035100040300b102000300b03200710400c2204d4600400a95840401d80381513800190b40c21341d400c3c40a02104841c018100c1e80803801d88180800741c0728602c16801401c41400084545c440042c003000e845101c2c0d080f5150300054090303c0704640c9a00142082d20000171a544d982640300050041c007007450050304248110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 202852841 1250 202851591 202851601
    0x1b0a150b090f0702030a03020705070b0a030b0a0e04050c0d030e031509161203110709090b01170a2f061c0b060406090b030c160b040302010b030d0207090506030f071706 74
    0xc2d191141c0151204d8000318507000c8645000d80181d00981421b46680c0600c0c0c4001030740080000061a954445560024035074264500f08901481c50350010790b208900c1c641080000b0700c0c00100d040b5480320440701801d00c0d0000c0e107000c44081100c50180c503094004c01000d850614030408800740909000801d03070310100c0c070307000500c0203444544c8244002200880098004680288285400580c1c900d050f103070075070348804e2800165100c1c070504446a04509004000c4202d44400301c030b100c040340b031010f0542c00155407158268074203800c0d1980100390041101414440c14001103040c194006480d0986440c200400226200000c1c201018001e0800c07a074080e003480c0190454040c0c072020344582119900f0944128501e410003041c0d00b081000c100704050310856040800101544107913002c00c102e103041d203002425940107200041c040e40c00200d4440c0c51ba82c0100d412020754021001c00181a0784110000b40b4100b00099802a20700032841d02050319004600d002410725420403c6070032a84070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 202854091 1250 202852841 202852861
    0xf020c010215040f08040806010f0510080f0604050907260105092407031806090210090515070203010b280b0f0d050612010e01060602060a0209061b0a150b09 69
    0x50101d80020400100020b40040c0506161300728840c0100e640908141c1c07106011860080213800907607200039812420010741c0b9042004040070f1690f49041001c42c2001060203070007a6001d00904d214a890342e000942010040000c9001841c0051750004401e011319103030f44260840f8809180d06508240014240082c0003503a041e10302600b130203400d90400c02c0350603400c08200240c00c01c030400d5281e120314003140807611210080b960052034006051111881000809840e05140509100380c100041109a40d000a84102c140c0040c2c3d2841c0c0c0d40c00c09100181c010309a100c00c13a680804400f6250f00f0441e800120009286080c0c0e144c44002d0b80c2795084208540513000691904034001c010880340e5036150742145070018000b80c0303811046600220321509407141840303900a140e6440108010b00c03070b8100b05c0a9000125154110310704031059001c9407180c890101030503140f10080d00041540c2c0010040348064642099103031403d1108400d400005c0c0901103001c031300c44e4903218003140403095 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 202855341 1250 202854091 202854103
    0xf020f0a030623090403020a06090309060201050f0c030105010e0a030609140706020a020603040213200310060903051005060105040e0109090c05010f0f0e060d061e1e0b07060b060a0f020c0102 84
    0x582c0c3c60500c544020812115142c020012000c40c010f2007007200010b000d50040c030f0303007452090702c0c3c40d0341c068181040203085403002031001d1142c1c113046043c00b000150101c01c07207042d22030a01e04050000d4000000c0761079414035900041c6511f1030019880244041411203113a1000584241c03882e0503904ca1f03040340d442030210b8010f94091000c04c040b03001407a002582c040ea5071043c810101d01c080480002152030280c0710005840d900d4001300708001d0b503100d901801c000e80014101800c4a0f41151200e60b41c07080340f1243c46103090303034440100d40144e000303130203680c01842184004001c643c1c48211610241000031004c036150241000702203460341c0540c11006100b01c05039145c00441c0e4081d80e00f107a003140008081c0383c0045082115426040d102e00610740a0001503105003407214211039603824100c025480396111078017014404801c01406864075007113408480030151a06142c4c14000c3c0108103200016500c14070018850030082c0d0441880404404240c0a03102982013a0b001a030b1200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 202856591 1250 202855341 202855379
    0x3060b0309030909060406050405090a020120120309010605060a020703060506041404021302040b070605150901031a070e041a100801050a090203130203060916080706090501050d0f020f0a0306 84
    0xc0c0003485059030f241000505194005001040030071107550700c002250072100160780c00e1017640c10410030081596008101c105540c5211b06080b18500b101d40c40c074544607004454244000301000010a440c0350b002d4004001520000309129500d0b1502240070756105007911048031140d04240010f5658901442500c41071503008440c0342507555182d00f001904001d10260070034040c0d0038030000c20f030038088401800940b0b215000c00034103418520300c0b42c2c61181c00c510380300d4881d00e8482c005000040220140300b5410316488801503054a4034001a02c01580d81c4003d0740e01f140c601806995040084010300302d11010980303c50300031404013441159002d00034011550410b01f103100400c600107072130f03008683c080351b01200b000141907141e00103070800000751042450795224130000f03080295044165001000c2e11401071000a250140c0680030745600d1140905006001c104850100c0c2c441e0449c00e5803441810b800c40d80e900450342c0b541456041082c444000902c0c0240101c3c00c03100041080c02d082d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 202857841 1250 202856591 202856593
    0x7020d0201140103110d060f1d0c010e2704030c03120b0604050d0302010908030f070206181018141b0f130b130f05010e0703050f010e09072403060b0309 67
    0x180e0031078903200a03008901000c5c40e0011035401c4100046881442000251140928040344040020000d0400e0180003600c03a003c030b8001d00d441d000e0f1030380c003c01c6518040d8000c3c1c0b00b40c41031040e030b0155190340b440614001440c0c04403030000c00040551180c0c2078250b06103c2d07152000842006801107007101e40054145070088020003043c80189802d00155808910034400400d01d810726036a0a140740e0410350b00c5005101d00041801241e60301440781c00d1b8010540801500e40131040a1081e41d6400c0761220810758aa0f51420b00101008001a011000e50441020711030001c0d5030300d01e5070b640c200c3c40403256400c0b0001c0c800300010707141c4030210f14204200107080d4400e98230141c05810040901c0541c0130351020858011806d006490f0141c03180b18000e9203800940d80d80362048031100d100004020104051074072040029402c48075400c00c0c15151642034001d0550744090070285405655080481c042803003000d2080f2041103181c240129010590381806040d0396004d420401d4003080e1050411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 202859091 1250 202857841 202857881
    0x3032c1006380408031c0c05120f04030504090e06061005123408010602010f06030f3306180e03030a020a03020f0c100605150403060b0613060807020d0201 68
    0x41002c5070001000c081c03a140c9240507901c601841c80c0d60b00c407004481c0c0303601c130303644403a08100100e20031241e104002d41000d9103016842028590900d2005040b01114618000410185417290064501a0a81c038004000d10551000a82d50b101e100b01c070304d00d1207404102c500c2a40103104801350781d420040c0c031042c0b010a441e10100600e0454401c5284080170302c071b10f520111101045880440ea000094680003100e5040890007400d550600c42020241801e0500800019151100c0000100d803c5410400e20300c03400303000259010242151440c0e03206010000400d42680d5a01c050101c070f40080d00c64ac0e00040001803e82070303071521004214550014400952440295002042c007084030340340c01490140e072184e1240b0280c00072214130a0b80c3d4072108050150450031722070400a401c0890b003003034220101075107542951050340402025030792100b10108558071820281c400001c400340c541040161104402480760a04a948500602c40c003080f50304001c0c01841400a404002c2c501520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 202860341 1250 202859091 202859159
    0xc011412041e03050309011503080406050904090b01080c12011803080705091008071d100c1401020d2004081902061b06090d09050d03032c1006 63
    0x1140041c000d5403540c0700c401c0d034103011040035003084042600c213441d000d8070b9007040744c112401c441c1c03254110284541404014004102e0050644048a00da450580e40d5105040c01040c054481160300800e024481800480e2462000c5060703100d105080e200b141c1c83c1e5152114060a0318001c800c0848491001110280800e01ca03209240c1e100c407131410100d01c0c124203200440e00100c040d030192000a103004c030034041d0090384100ca42118400c64400500b200b03001100285421440c100440f060041250850003080003285910b030420209000840d111034455a02d080070740030500800010030003500707102103445003110070359040d2000740b0010b111111580d116044840e40ba490260390000e014041c103007603002a01c583c0c05c01c0e01c5200c40588918200351608500d400b4a003803004050040c1039905105684904100c2c009141d050700d00400c40a1400000c40300100110782c0202e40c5222116906415010010f18007150018400c070404c1825a1400d81d82c40c80303650f4200c031161200358099845 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 202861591 1250 202860341 202860367
    0x150b0d020a0507050f01021b1c050a020c03071203081f05040b060c100c020c03010c081308090319021f08040204150f121203020f0a210f0e0c0114 64
    0x104441242440d500d4519592900781c030b4440b0091a02509a40009004045403109000100001d090710028604860549c0d102480001140007000c20007102080d4200303071038420401d2103c55200034040d60017850319058000031804052405170040345c00800481d2121001050901c0d5880c03007443e43c1c40c811410081080068010201c90300d034450b0f0103000d0195030940c10f02503034202c3ca400384c00000301080d81e0140a0308100d10030a145d442645062500102150010701959000100e0344d4075052052a91074152041d0060511254241c41213100c1d000120740805121480346008031407088600c1d14111b0716101781c0c160744203000006141c01000c1070050800d600032500300c02c140b680780c190031078540b0104110301d407141e401074003a0b14815500d10309004420030900c1090400380340c250301d0000c400b02c80d1641c2d8860020403200308244032503801d00c04024015100004164100c00f4880c5901c660842c0020b803c801c00086101c2c05407840d00f10140d030149045160782e0303002c551154201030f0001c0c114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 202862841 1250 202861591 202861597
    0x607020708100f110d051503060601120e030408030406120b03033a0e010b1807090b070501020f0a0f020d0c020109051909020c0609070f0303090902180406030c09150b0d02 75
    0x20b140400c0d1200400400c249210f005803010700001e900001c0c0600d03001c0c542d1f81aa00c10400f0090081c1c2200c400c0c001c590742e06c8000e40260510811b0007182c00c0b010001120f286200b681c0c802c501c2c0d0700000ca40030411992103022004442c50318a810b102c80342642080541b64030810000354090225410620441e41ca000000340c0001c0810049000808810381002d0a0740c940c80d08005c040d075515150814546450b4031450104a941010440185403542d400742c107040e03003401040c0001c0804101386c002c2000940490354289504102203481d14440280601001010070418015004010b03001d040d036071060b4101a02c451f0140c0d141c00c041072521040c00409841031642c0e40c10a00050404120001903000a04400480d80002c14180c501080c4040c2031200d16004030002c070701c1c02e100c1000801c2e880305e000c1041d41c078608001a600c003401d424211145210094040d040380c00d0038000014410b0513100f0784200c841d50707581800020748202444e20081a81c2c0541d502042c0248400300c0348940690103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 202864091 1250 202862841 202862861
    0x10b07031202070203010608031309090203030733050402210d0806010512040804140907020703120318050f07060e090a0903030605091005150703020309010f02120403050f060702070810 81
    0x4010f10300030141d0082800e481c015000401140d20000d01c2c050303500c0c501ca0018006000d400c00c10070814003107500203926482251000340a2412180c41c0d40b203141c1c21624003407408000c14540301580c04245036000080c0c102200d09034850460141e40c2132410100306070001c880762101001d0184110520010b80e9902d1000e48035504111081c0014080911442106809640100051516903240003001e82240400810311070003110800f082c400700b0707500040c900c016a80c0c031200121280d000c1000031001080c00003421030b048445800a0000d10070081101440140a20150fa04003929800700396035001c1001d00041d0408950f01c002050017002c0c1d07001d8400d4501c68074002c00c10782d65400005001100c10b60b04248038003280c100810851526200c0034481d14102482c4a0070074049480c0a5128095035443d05d05001612a051000f42e2007400041810324100500984680d100e00f840303507540b191070b0040c0540b48605800702e55094000501e41e0100c401c0d000050010106003101c801c040c00610301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 202865341 1250 202864091 202864127
    0x4110103051e1807030c0e0a0608070b03040602090d12021005090712060e0607081005030705060301030b1806090c040b03010e061f050402040b180a0b0d0c1211090a0b03010b0703 78
    0x202c6a0180c0800d01c0f41d81c00460040d00c074191000e08107000887d0101d800303000c48007a98500300c1d041001c6040850103d046415154000307840e6aa5400e005d00a8800c041e540c69120716408614000c0226482602d0b0b41c800443d0b0864504401c0c040c120b40444c1c0082e500507140e6801b450003001040a40d66642c415a4840d04002c0703220540600218a420300c02d544040205554408000140401b00e22200c0101011070007002414a4000464400e100c10f00015205030040f200080c01c42c5201042590079041c21800c032481803400c508401e0311030b180854400d20840c2850440881031070140a05103803820501e0203401c46440d0b0780d010310050002c0f0030289403150220140010280d807070380301420080202503180b07a9070b20301a1440807201108031031074521581c810f810902614106000f03859062445210011b2041d0000a064400c400204818200300342045500140d0100040c09801481d6041e11648805a1100c070b04595a000074016480c140c1c07400e12480001ca8450000003551800c050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 202866591 1250 202865341 202865371
    0x7121a130b1003091703040317090c030607030f06081204050415080703050304091b0801091e05011d070f0f030203060d140109120c080904230f04110103051e 69
    0x40100e400e14214000c5080842c1d640c80134003080c4602152004603040104250a19505d413550b40503215100c01c1c24580500c090000c001900310b0000c0000318040b14008080350301074034004c200100a41044900c0c441b0143c10400005260180003a140242c076031065505800c1c10304010030310000308440b950040016485c688005a14101030000b03d01450140340610340e620b09040c1c0686c20b0f100045902e00e0300381000314103041c010f0740c0041c034036054680085000ca000040007085051080e00c2d10701d800940d502c1d20000141c00410319100e0000140707606544065566440401d8a03680b000ca04590049100d0700080002c09100e64021a031007840102141001040c03903c8250500700c1d421003045560f0f40d00d62160007404070036401042e0b040e42c24a001003e40f400342d40d841807540152a5018012502d600300c0200c214800386501c107060942c1c0001c0c14981c507040a131041e210005840540310a5203040880d0301c00d5100b80540c500c140506901c1c10404a003440c040551100010294207100e5804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 202867841 1250 202866591 202866611
    0x702090604140109050103170406020a0201111e0708161211040204031a040501060801150e04061407021b01030b0117040201020a140d0207080c09010b0a020309060403060507121a13 79
    0x11007000b6010b030205080020b0b841d815031511005820118a076100000414001000b4281d400500034012360350a10f1b1a1061540002d0b1a81c50b00464440c1030f00540c079001c203c41218800056210100c0f1080401c030381400c6400707074a2010418003409640080015217980402240045400f161043c00c05440140b400383d8070388440d21018610500c00200e188250148010302c01c0900a0707401600115000b041031098651114400103981d2150ba2940110803000500f44517031580300413882c40e18044028524030302440008e444640c03200c0025460344840c00b00820300e52207032003050103e020686403840941c43c0e044141041c00c1004001301d0452090707414190000394031aa2500300400200c00034003003408600c20103810320806401c504101e0388807400b90015595001c0d42c1d5811030f052070040d030341d8842c402c000407408c62081541d8a41c01c0b01000500004200050307120078810001640ca5490500710301c1c0a0505440d180c10030884814110720760b4100c10302c1d2800030100212031580c4002510024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 202869091 1250 202867841 202867871
    0x1080903040902070804060e0a05010e01030c0302130803030426070609050c1e040c020312150a030b01081605100e040218090c0306030106080f060f180a0b01090f0b060702090604 78
    0x1c0721500300c1720b031180401c0030002079412075645082104102c0ba030560150824000034040950925410b04241e221b502c1d00c2142d42c02907044070a0f0300b040e020b00011450726844071981e650b10a450407518039107588030b040c1000e03600040030320030418406000c5182082944454000e840651000e2701c15000c0c1808090655441070703c0740c44c4880e11030390002e1007000490708200c01c80f0000345103034055400030800f6542c1e6400c02901c03164030a03c8800f50071300e18600e4501054000c059604010203d0705210f0000c10b031000002200c0306003409400752112995201d50502c500ca2100707140080104161001c8881d452070103030050002c03811034801c1000d11345e2615000038140c603c25102078040d08000018480141028001c860143c12030000070040080350098190391002c1c01090580000098808244102d8041650074402000002140c1e480d15590812111001081c4940300c0a2854644030940d240317043d014400c22980c008080a080800136001d01281a20050034247c1c41943c500e000c054a0301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 202870341 1250 202869091 202869097
    0x50c100501030201020c06070302032a030c0303040b1503060f15040f0f050f0408040e0403050405150a0908070b0d0b060c0a0b04030e06190e0d140c03061008070501080903040902 78
    0x401000041801d51440c000039080501070407041c0e0103404204100c80103c2d40000031601121a03501c440d02c06140542115415a84071080034422400000741c00d2415660020146000b203005006213003a40d1142d00055107041080540150550007000002d00c0c0080c072480302c140c0c007900061001410060031400501291900d880054000d566001a03a100012510030542d204a40020708940d6003019261000e480c0100e00c5581d04040c1054005800c1520031426100200405025a0803030488030891102980020030840c0005021490008100f4000207084003100d40000416162220b11410794024208161606410000400014000d040304120742004140501c2440900b0b061924008180150181c01c05124003007d000ca640d00e0f1201090203981c0801c0f03400c000c0fa60740c0c5407902090710501c1100b0040c00050850500d45489600414070a03542d9000f181551280e070b5030080c8601c00c0046900401007150302c40e46007804254041c41d4a1038104840c10116410700369528092021380e8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 202871591 1250 202870341 202870363
    0x10614010315030c0605040306050c030105010e19030209011202180705190306081002041d04080a0e01020120030a060b0c0304030b07090308040f050a08030c0616171003110102030c1c050c 82
    0x1b40d0002400c00034400d10b80302e8143c01003689601c0d40d14551501000030324008401f032206104a100c01050780c0101241e0507020001e44c3c0c040d0098440b503a55020003085200710203010384c0038800451400b0620080c02c1182da2081c003007a15018200410314082c1024100d1184000f4141a512300c4007050b140000c02c1544440007442d000941d8407130902c131411020800b800d01c181c043e07001041c180000180d4240a51b0fa20500310320b0000c0c2181e45c0c03000100e003d0018a0080390400300d0103a0321640f810384800085226288040b030501030140d0311039028003584108501a80e044d0410b010138400074034403c411a811080514000012071303242d07161540d0329800342d403045d1691071000350100700c21f003804413103d40102810005141007200444070592501c00051550050540100340300c0c1c60304d406080a02d0003400d4110503020240b504424072800b0800380c0c001070b2494510701481074855032000049600e044148409043ca00c60014440c004c2000c00001c42000e1100a000c92000164200a10300c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 202872841 1250 202871591 202871597
    0x10c0b2a0a09051f2d0f02070f0506070b2503090b0105120607030b030106090606091a0f19030902040c030b1203030702030f09060f04081b03010614010315030c06 71
    0x1076001e420000e480d0501a61246014000c2603296841c505003c5000d00c0f40d0fa01d0604000401c0c0e5a1011294011802251500c0d20550703490500414241c3c48402c681222942e5021600c95580307070480b58600005601c9555482007081012000141c0a801c860303130800406006a42c03e555803184403030725401500030060000769911a0b4606100124404600400f010b450541c221246540040d803180030080002d002e141d150304400110341c0702580401e00818008104108003611528028107901c454812204941a01010000c6140040c0c0440311080104426940340c1403c0e10300b080031105134040c07000103260f6a2101e100150301d95008003040c000c801d64001441f407201108000024200c1c62000b80240e009004215885800204860a11140a890a48880c96134000900350700c03071000720074800c1102140004600c080010442c4461840d00465500d0031010b8040c9402c0b00d840380300313038188a1340943c5c90101030750003680284000310203041da001d402a100e840b0480140001e03446a000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 202874091 1250 202872841 202872847
    0x20c0d0c0c050f0603060925031e020f070314120a060905090c01020d03112107090902070209070e0607020d030203030106020c01021603080c030d0608011d030306010c0b2a 75
    0x10004101e0352034026000849000344540403180c08640c50b8040100001d00441c8050089035100d00340d4615401d04028081018801c05c415420040c043c000c0c2e6281e07424203100581030700e40585100d000741c590b1000b4018245080c84a1a00c2c111303040300000100e5002c40030100440c414411a01854900c540c035101c1d40410400e10740320025003200c100901c24080d03504a07112150803030386d0105421a480345585030209060078140b10500b4507119012002040c888140c0307090200201600c01c5078442d880310b4541c019403c0c3e0f0307110b0000a91040301030003940302100100090505004504002504c03001a05050800080ea070104082d0702c14550240e0141c1e1002c03004200e061380c1040804d007201c20030700c00b92070740042002840103190628000201440c0000c074030100d80401c2003066841d071283c20581807150507070f144100381c02441f414144d24540240344040310401c00000048a02940060307580c1840864940c079450312011002e08241e5150b009014169031741e521514480b0100c0d0740303081465503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 202875341 1250 202874091 202874093
    0x5040609020f030105070e09090f0a0f0c05180406200c0703060b01030204050f060f0702061b10021206040902010e04021c18050601031b09061d090303011a070501020c0d0c 75
    0x2818142c80d40303010300c2a0b05000802c1040c60344000121441c050649800e1555101c0b1a1440c0c14402d0446140d00b080c407030304004a041c4800c054000d851740340144104002c1545a10030300c6640c513200843c42c41c0e417850000c0490006602540225040030450090a00d1000e840e1050f00b1180e01680550f0381d0b5511850060041c0030303403403181c19078881090a045140131301e09404a40e0319661440194811600030880319614281603040341c65a56000340342e80d07607a8011a85041818400000b0152144501180340149441c0c40c0700b1035824001c3d5400b444d4180d03640c441044045c0550103000c071b04100d01c40d24040c80c50386841c0043e01c1145102c540480a890081c0108002c0320120700d50300209074a500f6420011a801060150540b5080000d244024001496003200c03104c1c01d80c440e0b20702034a0460001511080c51400d082c2100318000a01a1519814280f650b40c2c0020b010f503c80c803d64040403151031044940052200510540000d420905445921410300c0640c080102c00b241030301000c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 202876591 1250 202875341 202875349
    0xc0a0605070b090f120d0b19030606080109020f240c1516050f030a0608030703080103060507030501060f1808031201150801081b0d06050106020313051804080a120504060902 76
    0x40d900140910003450705059490007a59078040c00420441c4149000581b24800d001c1c40d0801902c1e498080c04d035004510306c2070401c0780c80941c10300c020303100da920f4640003255820040c025055942c1d00285000307500e804000030003c80c003038040d101d409051511038880c10b1040080002d010316140d910041d040d804e0502d1404000103000a0442d160101034024054945401c20195001c4404000401e03480f5510010402c1c000d02242c2c0100382e0307a100202d600e80402d680300445c681600c7c0b0035902440345850b804010307400d0354028040c2e030f00420325000745951418400c5800c50041c1003a100c81042085c0d0300c150041c1142d0294410300d591700b8280005109850600c0e002604940c018900000e4a41c506281c180d1036a403020034414481024103180e614542c0d880c00718403282c41d0002410822940d5078a0060b54035884200c680b4024903000c40300240c2442e000600c00c800212000c20452180d86613940c6120980c00802183d090109403807450150110358400d503449688910000103001032030340100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 202877697 1106 202876591 202876613
    0x60705070f03020a050105070b012c0115020c2d040f0509060f0907030512070f05060414011a0d0f050f150f0112081b0c0a060507 57
    0x440c901c409100288202c1c1d02c2110f84511099a80c0c005644500401c8009403960184000401002124503c480500d8801a1000040580c80c0543d042d400e00c083c0c226082d038819039401000c1c00c5804021f046105075080720b10030000455440100958540510340034202000515000302580b200c0d041040d1010080b003042c400c52500d1260182d4500080303a1350301500140a02180070124042807460a59401c8409441401c5004a40c0c42503503210190441c0d200ca000400390001c03900038809a4091032191481c01c5014442c2200d80b03007501c040309034590401c3d14086900e1000c0d82e40f400204803196000c0b200e809806218180300f400c00380d217590104018081c0a03410a40c031541d000000f441883c0100388d071220750341c99040910703107041220380050000349d00704000140040e11440c1422140501805c450318807a180010800d9074990b5440304d0b002c00d4020921400700600c400da0 = true := by decide +kernel

theorem cover : BRFrame.Cov 202697841 202877697 := by
  have h0 := BRFrame.cov_init 202697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 202697841 ≤ n) (h2 : n < 202877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
