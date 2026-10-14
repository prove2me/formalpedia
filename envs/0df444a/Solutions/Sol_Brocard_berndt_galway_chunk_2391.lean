-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:34:33.580675+00:00
-- url     : https://prove2.me/submissions/f0849403-9091-4958-b7de-a2c3f987c519

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 429856115 ≤ n < 430035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 429857365 1250 429856115 429856127
    0x1109310c08041b150e03010c02010c050702060327030c01110f04090519060f03020f030d08060d051c030e0c01091404090606050406030302010b01020f01060f0501051c2406 75
    0x40c0c0a000030240300c08074002c0340048400041d802c503040d01e00410240c0e14000d60225500d0f00300b094010480c5550483c0c4503003030a0190075115500da1000300001008050040c3c69401488400390007500084000340070380a903204082469400818158004000c2803840c0d0307501c0d40300d40c02d07100c41c9500380121400c007001c0a0041c0c558502d84000b44034103250070301034040c004210041c803928604545140c46019034803188184409443d1004020f030740c1c2400d5006105458520b08120740c020342c440b080840d6402e41c0302020f40c0e081074003200c90000303500b018100f540c03070510072002c0d500e80229003d0300c52000b0398260340324014217003050040e50901401c1d00010340e182a01840b85902c0700380c0c440030a803107d150587c8a031003000c0c80f91600044131500d640100d01101c2c03c84d0011400350b9903c80c510007456030100700203125484108001d001c228204444a9204040e61040c541031120108811411405130141c1d24001c2e01c074001e042100a20032000206404c40030318040070b00001e940b43c0490040e100310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 429858615 1250 429857365 429857381
    0x5040b16081501260a0c0e0306061302030618130201080c13031403070519030e06040f09020702220b0f10091a070203030d020315060403030c06110931 66
    0x411454030303602c4070006407071010244c018048524500070081006a1080102c113000e5030038400c00084086d18044041d1411240310001c87c4a6440002003110f02e96401c0c0b00c0314003a0003200c00c05a10fa48907070b004031300f00c0c08160200403400c2c0c12030030802000b90418510403100c030b070003641c4510060315680c4402001e03108840391114102a02901400411440100702c4d4415103044100d91601580380c6405041014a403000400e50828140b0202407513403000c444c01d014201100d0b400d103098603021100d125400c81d4862000c2480c0c010599805644e01c3c00540c4030309103003103820ba051b502440741d020001410b480154900c03414502c110707805281800d4542d0368000f000d42d100c3c0d0943c0c03400c10300241c90b03401000840c440c000100700f2540c801a1000d001410b06655000d202503100d0401e907450071070b8400f88a0400e8000d010500c030810109600c04120403500c1d8100c600066480c5640c800542e15120310350b5042e030080083c03143c0700c1c506280c0154900b05040b001d140d501401410340b0442c42615625 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 429859865 1250 429858615 429858631
    0xb0d11151c11070f120207050d050114010806010506160f1a0403030609110919050a030813061d100309021207380a0903050105101502070305060a09060605030105040b1608 75
    0x2800b240c40021740d40c40c403141012030490044528690343e8500092001ca0402000c641c681d45a00001c030800c940031340020b002d412802d0284c0782540c100349c0440c0081c0030302818150280c41d94144003041c4540380c07042d07480b01a040380c08222182c0c49035203030162a25050f2411000280f50810020b11214684520100e6241101e4090714210b580c00401240602a5200d6600088400000240d9664401081c0000e602ca031140c81e81f54003c5080c5071941490f20341c007040510141600034450300c0c0200700c01403200d000480308c0829024541004a00402426200942020583c40b21a0420344001200021125840b5042412042e600242004003c11140111220b00244000d070104101103001e8055100790f4a48000825640d84591342515026035840719010096a0203010304030440c488126580d82a00041111a1031680d0345540c410b402811600307016a904440010001c6540160008290050080c819030901c0d0030010813108050b00d07020384490404c00e20001d03150103a100c040c411211 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 429861115 1250 429859865 429859883
    0x3130b06100905100306150c02030f0f0a082506020426070504050606070f1b1d0c0309030409022a060106050703050d06051e0901090b0d11151c1107 65
    0x5007509100c4d0711401c9503e10401d01d601c800d00469280790400030a00c440840d03581d28a8090100e005041c02d052411000c000c80390028003d85401000010303041c5581503001d038055a8941407030001c0f00d000c889810345400034200c00c6405000b4040d543e0080e000350b4140f049454201d2011580d030f078000c110f0201c0300e1171180c0c201780000c01a503e040d031b1104d0341c0508090b11a42c5030201581c0c0b0440b82c0e05800304112090510005180a914001c7d0340a001400588105249102c240d0120000302c1c10020314410303104074004001021444140305441c0106000c00042d9201c1302440034102c0d403a0354664098031910b02601e6400c80c1d0400004400d41203c5154503442d01d0080151030407251580708030380c0078446940350b0300300058a44520317a014000c000b10800c0414661000010002d6400301a88180322040c20080c130b14086690342031079042180d0b0b011844140a0481a01040707540604000410800e080400c524070b522510345500072035541d42c0001004412031000c5111100d01680ba0054280310b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 429862365 1250 429861115 429861119
    0x5060c0703020d020321030703050708240112091a0603030a081f050a090e060702010507170603070b16030f030903050708071a0a0207020910050f01140f03130b061009 73
    0x9000c540c01c1c030054000f0701a203141d00180700c07210351b502c4904802c1c490000e0001080240a560522800ba0031007030a281c0b11400d8104048241c0450180301c20078034040455041d070b41d506a00070403e80c03e418400c0345085c000c5490038108183c0300074050800c0e80c00214640005a010702e0040115190500c2c11f0700c07503a07241c1c0c48404d6414000c504441d040040802c00c1d5001192aa130350308403a0b001495015008a03074007000c0b4102c41d04050020381102e05584c1000148090135411840d40c4d4005140d45901115694500380001e1910381c81c0e90261130036001c001414101d003d0000e00c050f075954081d844050455503004411001c0340c110007006000140d06000c000b0020f0580341c01012103c1c0a15802c40681c200c03900a80038a0000b920701180071980091440e0840c10520780f11a0b20403442d0010031419071502c00071031703503541c05883c206040081600001204c0300d803020a59000441c9164815220f1500321107082c440c20f2194000d40747c010350080003a4103440d003001d0796481c08040781d84e0f4200c0c083c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 429863615 1250 429862365 429862369
    0x12070b041401020c120a170f0726010330020304140d02040606020303010f080f0706030e07090608060a1d0a02100207030624170307032003030a0c020705060c070302 72
    0xc20705080c0301102e540820611810b01c404001d480e80c075900481010f0780e62910803102600031858a4002800d543d10181004408514101015400b00003070512211640507a40c5801d04403081800401e90085100004018003584c0d019030785001c01f100042c200c030070745003e511450b0703604269060740041e8020082404100c600c0c0150074011030b00608070001011182e40000c080d0307115a00301800592010004001c1800c966082e03100401078000a400b0f50344002510070385540140c000d20040c0f40e16001c0481d842d0070b0811480e002068074a0003084100d0701d0b0605207440d10400e8070002591810600190480000c4464440000060b10010908030700154280101102c0c4c5100c04015800341e4440080483c0d420b02684044c4411000031a0315101c89640070345940b000350308405544004503810059881d80001264107690301400c1451000041800e0b202005809002e040424000442400075014280d040b1300801c14003a0241d40b210ba40750424840309000d2051a003800c0d50054400b0000740c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 429864865 1250 429863615 429863633
    0x14040507060c1103060405100513031422090b0f1c0b07020f10020c0f03030106020303010b0313020d0f0c0602011806050c0c01020c16050d020d060507030e1b0312070b04 74
    0x451044120f44030b8205540000fa0401400316415503840e0042c101d88400802e641c401ea03940041c04003c560b4040d841c90710b00a05412084401d50760701c2c00300103084200e841840074403030b0691f40d076010754030411a00c1d154075070060044140d64900445618145188e43e02e000007900c8600000203c140d04400095220f4032070f00764000e0f103030303000750700400d407601c00c0d500020302c482044001c8000e40541d0740c80a026800d0700d0456680c00c0728655801c2440140001c2e5804002c032170444558040140d241e407a5440c0c1c0d6071034001c002078001d41c050035078000300c010050740040003002c0364054000203c103a9500c00042c0c4c02d96441072201003d000d044412000045c00035402107401c490680c0400c6c0c02c012000b1510b600720f9010b0080141107501c80d207002603a6001c00c60400001c0c0c4026507030506602800c2d404138490a0290a0007003160740c4403000501d606120b98044111070a10404550407254107820291200c0200100e4a00a00441c880d034214040c070074040b1000e442c2e2194800c22680c0d51500c0c2c200704 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 429866115 1250 429864865 429864887
    0x5060603011a1e16050708060c040e07051908060906030a170a020304210203060a020415030b01020313060305060a0b0c062a0f0a08071e0e04060504061203031404050706 74
    0x10129000180f169000f84240a4100e01c0d1546140b01d1001406041540c60020150b001d0b040303550225040000e44100c080c29038046641030030b8070201d10348400078190748078019070340c1d04e091080406100c071402d103501440f6203000740c0095400050b80d0b01c2c0c040a00d9110740340035070003400c5c2030b03001104011030700c08880c02011901c000d031054a04280e215041f4001c00030078203e0181003c5132841011065280070f1181c01d0308a12110000c40c5040d01d0801001d0140b0400520a801d160342c4030b0400316a81d00030702c11a141c51690451b00c171002511014060001c3ca020b990702c0340140040c12010601c0d00c0000700303c81610070030800510090f500c03030f4000d5140305400244030030030f5000303d4076540c28480400c0107000d450000d46a1291110320f6003000078499240200182c0030004a20044110410f40301240f807011030013490800e010660440c04180503040f41c1d40450340191400f80f0004030102c0068820824501ca0f41e002d005044030240305408009080c1c0d4081c000f40c02840042040c01e00441c50044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 429867365 1250 429866115 429866137
    0x6170d020d0e06070605040b0901051617060103060801020a0909110901020a02061806040806060f1c151508101109011704031e1d100c1425060305060603011a 69
    0x7141500c05e0341c0710f90940d0801d95084403458004014400119000e01445900c20610200000c5030110b000d1b0091980d005403900311114076011000c144940d120f5000301024081c03102c029580e490390804000d22006151040f4121030b4076003040c2400c9003214400311810100140d004204a0704d198080002c6a800b8425840141c0000b100d4120f140e202c1001520041004c0d20107020645000303810b115601c9851031201b40b181280c0c100110650511021801d0f1407600107404001b50003445420400400481000b6614805048130005040100140285400c2c04084c4144014108030412049034000c91111f50701088001148480900311205580c1c0d10500030b01e441000f005860306000b003030803112010000011000094080b8050340c40c22800000442a81d0180041881900080c8101003034a4010034400c00320300d01c250410300400180003803101d800a0305c6041c0400e1031200380328103000d00c10500800d04080015246160210a8a0498500407901c0208030718410180340d05900c13100b2504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 429868615 1250 429867365 429867367
    0x60a050909160e010e010b07021212090310020909010b13030c0308180901180c020f0708070e0903091014070b040506090124090c140a0306170d020d0e06 67
    0x915591505000d50040082034082d29008000d140071180d0b03007075540c0224850300303810300042203000141d444c22411207034914559601c6040902c0080c030300c9415108604000d00c0350082400d91a070451000305200d0008604442c059444000304906a000340500789a0000040004021107802d050040c440f4500070440010000c0c0ca80d0345820200300283c000391114440031600e00c05a000b0143e40340080c0c2822207010002d0b600d4a0581040c1398001899130071141d480d14601c3e00d2560081220642c20030101c000d40b0301e02600c5840940e902d403903e00c580700c10300c6164000303c0d11981000c81260345036840500480d021224080050b80c01c01004a0501082182000480c0200788040342c042e0260f485040075000d1410001c101c182507a4207282440c008074886104508490065454101215803c2402141c003902c142c0c0241c070445844c070124010100c0024400c500301d6495801107040d01d8940100c5540c4070030305000c0790782e11442d034603008000d0f0f8072204002140d6400f9000b00441d01900500725 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 429869865 1250 429868615 429868619
    0x62a1403071a060114090d0201030f020f030a0207110901061e090b070309031709060304020f01140c0c04061a1e1c0509010507030504080a030f15170d0906050f03060a 73
    0x48150800702c0482e25241020300090010544e84022500701d0841507540741420b0200410000e130380e81d0f8020704000d040c15580c0024241009032078041c0c46c01c40f18100e04a5480307241c0342c40c610f0041c3d44030348012606084011071881582c90311006580c160381143e51209001c0c031a40c82d010041c0500134180d0010303c02c0860707000030704008040c024040144039a4940c0d054518503d0400c025150045a8103200c6c2024030035100251a10304c1580d6010350111a400d551032007030001a614200b100000c44440d00c0006001030160000149205000e001a0b40400c40540d60700c500030b400300c550781001c0340300002c00c109103140c3d8140040c283c08915810304145240c448a1030b404c6080070740c2c10060340021512441003050310282803007201c0d8850618141801140791565482126204052481e005d15540c0c1d80a65081202a4840380013100380060b4000f11a45490306841301c420440c2c2901402d2188064035907000e0701c100707154012180e458403894100b04a000141d00d054200030001a08400e88400c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 429871115 1250 429869865 429869873
    0x60712050319090f0b0906190b1305100812070b07030c090b040602010f05150a0501050c0a02060301181a010516030c0b0403111603080322050105010f062a140307 71
    0xb8281035248580000d0345805003910303242c41d012100414903405600701c801085806a401311102c1c1500160810015809c0203000004185448011503911041e24200400c0100c2d01403100f01c0007a61241412201c0902c08150814024411850700a050840003004182c110b4080d41080c4808042420820f9582c0e8495680031501e80041e13221000607034642034330440903021449003d801c140100301c1070342150350003008160211594411281003040c001080c080d4190f00303200c00183c8a0303004044980d2540d6881050580140c05600840c00a103440c90318004010950503141c640070041e140c250401c5404489000c403813114403826000d01c20941040000102c03e180c40342c1c403552194840d18510394069041c185006034041024202001e02c100c1400450104826281e0003201d4203038411040c036222511f081c1c3d0758086d01c0010502d608020020904c1c5152051030000d58000399100207002508030300080081f080c101c991800b02d541028104003141250341482c55a062110840e4501030141d51 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 429872365 1250 429871115 429871121
    0x712020a0527240109080d0804050316060c03231b0903060a060e01290a03110c280b01050402070203160e07020d0c050c1207171b060712050319 63
    0x1810400901221003d12201c1d1010f03a4400300c0020286403801c07540b828141713800c2e80c4410040b0407409014004001400700b007010801c407100c00c0b101905504110480c0d01d050760240c41d0500765103000c81c0c02d040380c124080c01c480c1450081b03070042c0e40910210391180ca89040c118601d04802d401d05800820090300107480400030b850140b113030203a000038810f2600ca6021606d100680103400e2036a040024170800c0c4e000c2d0803ca64440711942221176941400702c00c190000c2c600424002c0109a01054070019081c0101d10b4804600d40d000d01c55228a80c0d41300341c0e00824008400081001800600522440c20306038041c0441c81d20180c1122044522600400c000910540c00045900703e9102000364007541400382103410074007410b000e0030141aa0b601d0940f1208a9040b03140030f442c1142040c1c1600340100300c01c00043c500304011034110b44c41c0401e00c42d03c40c144941c0d2030705040f8403440c09006505001080351005500035a510780301190b032103001c5600d82d00140603000d0500345440798100341c2d52a84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 429873615 1250 429872365 429872371
    0x181a1e0712110f0a09050a08011e05100f080105070801050306011a0f09041418030f070204090f06111209070806040f080c0102041401080717270f0109050712020a0527 73
    0x521030f4174035140b1308402c11283c21142c3c3c01c24440c40e414103c0301c49100030b81a001100c2c107880101c002c551550340400e40e100034159588941e1007e000240006010001940210700489a5036658015680c890060643d81c01d000e20075601c00983c0140002c4c500650000500103c65882048900e0301008100040541d100e20081140002651341030058800211510710f172404240c001440c00d00c8040d404550075401115006406107032141c680808010482a01150b00c0358081410080681c4d440c40000c401c0c0c200c50305c0c220181c3c9540000c107881281c001005030894130300e84020101c2d60b64607905c00c0f188800e0710f5400c03212880140700b0b140c0c4030312080c005000640302c11700d94002c034084580001400d40e00013a00c0a400e020418419003100d90200310182d0380003024407814452401501101c0100d2121130320f01201c1c40c000d041e4184400c04045d0095003450340a00d04566036151034811055602c0107041000350b000c103000341c080016045c800301c80010f41644a080d810f006000c04400d0307001c1d900c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 429874865 1250 429873615 429873617
    0xc060c120a032f0304060c0c0b0a0509070608040206030114150d09061a0a0b250b0124020c012303070e0418020f04181a1e0712110f0a 59
    0x20340f906400404030300360b424048141d922224292240349401c100080e110240001c2d01060325141c0c90200d490080709078110340d540c0104020010b2401d040c2c100010720302a920601a402007650000d842ca126000c0039001703940050030326186902e090340002110301c400141c903401c80078030354640342c12030081c40c003400c00402101008112400a450208121000c1e107048c0d07200005031410000c1551a074803c2d0400752040040c0050b40d41104a031038100e0303080d0084001003046d601101010420500301c582c11b0403034001c5152034106010411007585040441e500203001a03011101e41034082d0b00c10890203004420a060b10a85610201c0c00315110b1741c41100da500115a1301c007070300c46440c1010320900388a03446659007000d01903007a0380000c9407442c0c0d0708a00741c071a40c0c807601e1204047c2403811a8004141d48000f00e209020b6807500001181b4004840406149141410704d80c0380248000c80c2c00d00c136501e03647d01e24150400c1b1084240007000e41e520b082e606403100307114008101c66003400400c0d000c030f42d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 429876115 1250 429874865 429874871
    0x607050106030b0609070f3006051f0210092f030f0c0f060304080d0606020a060e0a170706110c07030c0b04080c061c0606050c06090106080c060c120a03 67
    0x640c10b209500e05000b0f42101e000c0c2001004010300141d001035660704400192600c1c0c4007235502244d80000a1111202c407115500812014a4101c4690b84c0610101c0d00180d074481e44044286170032025902200b0b490b840960005a03000742e641181e54410072109100d4000110168421744108014880c0912024495044403000717401e240780401103a8400a60007004002428948020031110901038202030b000d01808030200e81042000c0c005d0380c00c00000d00f102041070a0b1346400080d0346240e08001543e110b1325200300c0c050108404150140c11a410484c00605001c0700081c031141a440380c801a5003c95071550b01501c800318030f000618500d44008001d011070f0f425410b003001d401da11035129a00030384081004100f00600800c0360b06260b04101c0d80c444d00e502d143c40c2c9a510320030030021402c0d40c180c940800410801d4005015154049011048500c50f5940c1c2c20170f142281c085d8050204170340d10180d000e04c81480c02000030503a082c0e0744401d45080c26454416044540c1007401401d022a031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 429877365 1250 429876115 429876119
    0xe0c0408013b030a050a03060b0c063408070c0f0c0f23040209060d050f01140414061302090904050a0b091203070c03110a57050607050106 61
    0x11022800103001d544080421002e07103045540d036a542d124401301d8409126000c00d80324684c9000750700c41c2000301840051300e980d0310051521070f515100d0480b14135001c800004201052b0107500a58401101200400440200200c09041c1c40ba158024800c10400c1020000b2030000744040442da80351910406c81e02a00c1801c00d24001d0345040541c110603100725560150b0064200000c14168003104291801680c80000a012410500c221b030500d552107810f100500802110031100d042c1290000d845407001c03001c02a0811082e103040c1600403202c29404c9000c51043c0c40d1000162100701c540030001840e00300008045490020104d40646c0d95402c031440c20420300c04d184440941c000c64a030042c245a1508500c3d5107a14000a0000740c204005000c1e00c5c1e0030503008030b081d0049103041c07600300c070303040d802610304003081c0c030f0100c0da11502040100c108900f000303800a03071144094802e0703a0341c040040b9051445040e050301602c005d0201c50600000050552146001014800d00035400400d200e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 429878615 1250 429877365 429877421
    0x1181d0702010e0307020603150f06030103050c04111912061505040e061c14070b0f03040c060e0d020405060637090303080105010503040507050a0b0703030615090e0c040801 76
    0x5194003880303c18a4104011601c016a1075804695204101e4400c2c4280c0c021007602080104244040c056048940040040f05000e400543d20785040c0e000c075418400c4040c0f400c40303980240291100c1c0d610011404030614100c2c2d000d003a600f450801d414100180c4181c1c0e9461b06042c5030010f101460204100150a1100d84648595542d11400c15105005121140000200c3c00c0c52001400f030003120354040007903407100c2c040c8880310040c59600540390b222024141e4040e042d074025641166044101c843c0054664042c184010980c10700400c00c0c1d010702a1764003440f000e4200201010f6001604004441480720180c915201c0c0c2c940b4141150b241c0642c14560880c01010444e0306002d1010080302000040e03804006241900e10a10348103459444528106141140300d8211a60210192034003042d40c1c02e892000c0e011050080c0d605000107540c070501e072400c210300c62103040005416000c05100310086001c07c42d411190111200b417920380e0b00c018850858113510100b00301003c082112510349 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 429879865 1250 429878615 429878621
    0x606060903061d0304030305030405010207051506010f08040809010302070615060306030308090606030318040209100807090b0c070b1608030c04170613020f0301060305150a0c051801181d070201 85
    0x800584030900c200004402504c0c0d0300d014520006040107800800242080420b406950000f03034801c0c1100c2e038085040350b10908881c0101c0e10b0742d000030464100d030b2062b1803148800902680e00a541c0914140c0c080004401035441401c0030313a0296118021618240d061020480c01040359a40000c2c9950540ca8001c040b07840140c0603242981c0003c0500585a07000700031580c29260500f002501d078428440030a02038042c0000b001e6002d21200e01c505011a00000312034030a540b01c0ea6600c01036600c82c00000001e001ea140003140941c406e1000340110f80030500202911203898005048042580e904c1c8a41940201d40a4044003000708003007141c000304105000a80c01c03254064085442c0c00200f45030a0390b10804c001e0320910503c1d4031107800d91405e5100b030303000d1500030099464652070112111310a02086e83c0c2c0480c052b1a000318110114407610650302c841501190740a00040e1100c01190300350703048118180d000550b000c000854400403d400d2602d03900c8008441884c0c540800c0281c21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 429881115 1250 429879865 429879881
    0x90c030f030409020702120607080613060623042102010207051807080606161109010609050607150f0203090d02060105010201060f170106030f050703050105070c0825060606090306 79
    0x254011200e00c40480c0010003900d0070703101604401600d032560f9000080850b401c000c0d4000241c01028240401c81d03074810080c03031140c1c1c805c1d121000c034200300d0f00c4410220744c241c4c411540002c1d9414090a8000c0c10001400300c40054620314509181e140c0c07540b10081a40c17081600802015056545c08658060002c030f001400100d400415041489080300c01ca082c004203044c0800c0130010001d10603988442c1941c42c10740c01c08101c0b65400c20149807520300307686440a103911030703005e4100008100d40b141494906988000e4466424078070a650380c100d84000c2d4011000100707440d103280862645003032001d1032017020124000c4c100ac2141c601d0180c10041c0c180c000604590619409000d00450184804200c0c2c65281100c29034404104507a4010701c855080104221584070040301803041c002001800e60b40154001c10440d2100142910b1000c2c0040c00249098014044c030441c0c08885c6014905800311134060700c0c46181c1c2a5604000c44034a42c010b0710200d00d616900f81b090003a1032188a034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 429882365 1250 429881115 429881119
    0xb0d021b01240518150109030b07030902011b0c03080d2417010e0c0f03010e0307030806130903020d050304030e0d150c050403170705031210051216031214040806090c 73
    0x3140181304c0446140c0c65900409844400001034804e00c802e034864054840299041640703508030b814a00c00050240c003015409078001200f0320302d419448050070040400d20f03640403200c03c1c8010f2540d55440056001102c0401103250750f500324180d810726030080d02451801500130038842605001c40095400c041c1c0c05120b90b542e1600d280030b10841e40014204e80c4104007120000f43c001402e01c0040c1c007500710200780d00407500000c1900410541c0000c04036000e0402241c1c10912400003401400c100c5201810207001603001d00c00c204120740c001e10041da0400e01914021a043c0e01e58804289000c8007050304131040b0040c44c0f1802215120f41c42624001080c40c034100b0b00e000d10b5a20381c8007818003188141c20307100c540020741d20100242002160503000b03801e0048030031032500c403011081440da0b030310455004d0105944402c00c0700307201041d00c2c420201d146d00c03154181340c1107448030070600d204100040180010000541e0b044082100600020168900100100e00d010020745d0f090074402c484030385c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 429883615 1250 429882365 429882379
    0xf03030a0924050f071e0e03070320040b10020a2006071b0510050708030c0405090709080105010918060e030417010b031902030a12021e0d08010509010b0d021b012405 73
    0x200d0354444030343c0fa2400105092031f00c0c0b5905a01403000074140029540000c1c0109040d020310f001000c850b090402030000c0c00c81b400c0204e42c90300300034002848814000c41e4010b030820740c40903001460044001076181044640035012182c104081140ba41c8100c4042d03911b910503003403007000380030032401070009080700703071203807015000c6914002d8058003820000074496400800021011000502550010403004241001174204484060040005070080700403c1d402c100000c81d07d40443d0150141000c0007002100001c1c5c030a460b40e00003440c80c4040890540002c0000040b92800d040c10314002d010940b00026001050004040c5013642102350194020400100d00d809a80c4c0030640c4040c603500610105400c4144c140101d090488407030451a9041498511034007501001a0514061489840d080c1c0c069032904100030700104248603444400c00200103500045d001d42c1c000d0442c1504c000c1c09080b2440407403031001d096941c428040714000c499040d14100e40981c089034240105416940c01e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 429884865 1250 429883615 429883637
    0x3080d05100b040605070f02220c0905060f0a0903020312090a0e0610050304050f0631050c0d05010605090a020a08010918020114090406150f020f03030a0924050f07 72
    0x42c0031640510700c070340024050041514818000c0041c0e5207444158002e110a0500d6050300d6525400c8051642c640c49003842c00008103660740c003130445042a03030f5008000030708207404849401d5156201c41954070400024090010050301c04008036130100448410079511050368034107001c10013050343e0200421904e49018032000344c460703140d04421006946400c1d556643c0f1400c100785458080d100c421003610444080000007803c00203002c2501700b581c8081c4884400c41c0e0340c80301407001505030103001500850141402c80c41d003401c119103e644902d0002c541181d903240056040482143c0c040d401c1034000983d101d5580d4019450782c090005030604002d00d541020f00d0182080120000a0510545001101402d2030a070140c1c0e4004030001c209001d1262241d048400b50308052034100d01040c50a100703122050b0000c0b407803400c0705d100400158215520140c55402818140f82d050310440b4100042240b0506400d0403804800c0340c0100101f26030070701003101144070400a10500c10085c81400c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 429886115 1250 429884865 429884879
    0x7031401140105070215040e0f0601210e190515060a032a05061b06060d030203030c2203030f021506090414030c0304080703020306010b0c0d08070903020a03080d0510 73
    0xc0c00c441d080030f20f01283c4800d00d40c03000c40c004410099800f205044086400904100100030703940c0301e81781186107139000b80c40c0ea10043d1005284020308600003001c14104c0c1000c0e040580c01033071501c0002d0f0442d040700d00d030255400212aa603040980f03450300505007101310008540049500300c0d00503191551000d245440311109010b112184c822450118224000c080300400d00cae04020788070051038160b0764140c45c5555290300c01d031880004018002d8800061041ca09880041c040c203806401a40c50740c0d451000d4010554040c01c0300c3d1151074441000880c400d200b00c0d07080790245109840300f020b14071003404045e24007a44020814044c011000401c40729482e0785003d15042544007428610400140c08034500b940180701ca804c2c1a440007140006210000148400440303000b5002e40d100b598031906e03c4802803092418400d02c07a8040c62010236580d20980d00d07076034404600d103070a01031103449a00043c5c040c01d40c2d03130080c0c40a9901042c2803903144042d2259a0b04840c0fa0228400001e1170104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 429887365 1250 429886115 429886139
    0x31c200f2806180b0c03090d0516030c02030a080318060a0c120c0e120a020909060c03040b07090801110a181a0d0e010501080303072c0919050a0507031401 68
    0x8001c202c2c40c0c5440003418440ca4158140e50015400b5000040f10301d014084048290401c0f1000032440c4154911103200e180600100e17903402411a1340c0440276200c6072010b9070001d070140401c80c0c01d885070500da2400f003003038400039600501c21086941300c4455a03902441c9410805000451030a2070002c41c0d2240f10b400440085d451042c00001242600c0c6034001520020410204c03d80c010307400c111020001c08000c0b60380c41d007551089502840307545030444500c0c1c0d01c810071030301c06038090000c1003c580883e9500001301d0b4040704600d040c140483d02c0701006030966894002442c82c644011660395112030b00041210307204051042440401c0707280041c6000c5003030560741a1081803c0000d8268003036880c6800510f58000e03031100038403203540d4075201d641d6680e00444203c0009046040100c030000e04001800082e014289000b111a02d40c0703108000c0444800380c840c89409a014000b01c000c00c42ca809031500c40c64400350005560315149001078192003020040c40301c0d4920200c01440210308c046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 429888615 1250 429887365 429887443
    0x16050d140901031a131d070f050603060a0801090308040b130c030b1008030408033a050c0d091b06050a080a090f0804080105011a040302031c200f 64
    0x440d0108189642e02e100304d01c0c900d01e1401042d0030518490a030308054400e60485001410000032900000c02c041d0410360320f611160140c000348180041041015203000340107190040b00c014a294201b80d900e00c21a803c44106c0007040f004240b645040006003e458025603134856a11044500c041c0e00c0e9075149910607026000080c0410350204c00b05090401208842c0b019215030400c50359181d403a01c0c3c169559030400d80d40030350600b10700080c2008881d816901600020004002c09589411030048030001c0c160040040b6908803062207040c20b0b64032180a106106801501001019281400003541d03c0c0311607045601800400c0050359066a44504403580c000900c8072b00040c2e1442030720f02a107c03c003810001501008000c100480e4014065105604807000d0fa00b4004d0301101519004182d8041ca100181d4150132000c28410744d81c1c1c400e84a480959000d00e40b4120000a00e0b8444c7d441044c0d845680c160342e802580c0c644031204040082445007486c0c0c2810300c10311010380d0350040c3e206402c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 429889865 1250 429888615 429888617
    0x71e1d071b061d0601140a05100f14070605040c0b0f071b0f031406090a0201051c0f0c030209030c04090c06120905010204320a09090807050316050d140901 68
    0x3002401e000140d40a08841c00c00c0c00c50941104965007003080e500d1100780281b0b00000c84280407243c44d0320f0300400c0e031412100040d02c40006001003a2043e104160b20584007030038003088045a604440e400c200410445104100029180c11b01d4180810710b80d21a821600708014108026100c085a100c16112200d070701110801601102207460b01800405620500034805828004802c00c5404a54120061514000c030341c00c0c3c1e91000003080e510f001401e40640441e42c104041e58440440a40c01070104040c0d400200f0340fa00307030144910031105100010320019a020801380c81030f103001d200030121040100c03824130405550307844054202e10b55102701000d000751030421800c2650345070441484907402c04000c5403075030b40d650200c8094801c05c004c281c4c103507000300070558022507488401227490f440c00f509a4250a0801140704020004960141c072080d00512243c0b000600800042c2202c0049815540a505051600600c2c100c01180785805000d81c00b5490442c40d6060801d5a0361360500f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 429891115 1250 429889865 429889907
    0x40611150c0a121404170a120e01020910030c120506030c0906011b0f030e0102150c0f1b0106240f0c021216030228051002071e1d07 58
    0x320000940e00a190f94a80741c680e1400c10307076518000201c0ca0a80da100e14000d180d882c080200800c040155880f41d00f404001140700084000145410b5500450780c040001000500e00481900013400ca10340a449010000303807241d44e5280407075400428410f8003c2003910603c90b078100900001d49661070044140c0c05001c0c030000040e0585e100d054010490a440201014409040d080c040340c40c50000780241c011841481200c0032651000602400c9800480c11000c0a502c800303c15003225070040c45540c0c1c04000501c0500000c0640b4000708018000d000c0c000290b0f646804181449290040e8041e4046d000480807409040d41100382418140420300e0301901039061b510020f9016400300aa5241c5803240f070380c04141d20f084d4064041c054034002c98111420301c1c60f00000d420b000a80c01d40d240b403181c411a50410031414900300a024807041801510900c0c1d4a4035403000c1060742203444240a400d4507401045007401490003036020103102d0008030404c0c5030410001c0c0c04150400d1300f0401c9070340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 429892365 1250 429891115 429891127
    0x9060a020102070f080405030c100f0809030d0f14010909050303010608041e03030c0809070609030f0804150206150f06090118050a080a0b0f160507080915040611150c 73
    0x4030070350444070b005034002030311504414035040807003064015002d064040e205120800180d0700e0000741641e21078a403070ba0350700c0c0701050351a001c4032006009043d61003280303c180302e0050200d00314003070341070100c0078014005040c0598018505032420180c3c002c26110f89404808030110f20044201d034150340d054284840c550300c076480c20a0b4412221422880038a110b017420108140c0e050700306101120f1203650710490b41d00c69405443c0c80308481c1c0b042d04041028410b080001400c40005d045c0700c0760041016a061a80c4c800c003c0f041c41c3c0d1015886d100680083c820045075108200500c0b54031841078600180d0300c0b4601002c01c0d55481040907070b44c1440840784059000e2069116540b000e08400f60100d46c0071940c0c1d0594a540750310785072040390708013400d800003114502100400d5100d500d40c500201140c41c0303503501c02d40300c59000075815541d026007040b90350720a0300c40d4441c400502002443c0d02c0e13640d601d0180c008100b081940c04410680d009406189540c40311464000d0300511034040f5150340b96 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 429893615 1250 429892365 429892367
    0x5060a03021f0905060f0301030b152b02060c01061a040609360c2c0907050c01050f071409030d03180209010306060f05060a0210180f05011d0c0609060a 67
    0x1900652044e9071104000494107426503581e8080c50480e031140c00454a262202003854012050541c80180c12618204a9210403d00c00c080810300500c25410407250f40a15004510994001c03c0b402c011a91105c0040000317141ca214882c80d52441c417181c0600b4203043c058000c2010b4414440c02c4040341040103800c07003151580d941d000401c80816000b2145902c0314003120090000480e009000c42c640900900c410f16001101071044d540444034451165150010042e080030041c180d401000320500001180400910440d405501902000701e02441d05410040c081a22034810000c9031409101501d644c1c3c50000d402550f481c00d60402040d003240107004602012420f8038080e40c485600e10000052103200d9100c0d000740e0300d1300448810340e01c1c2c803081880031a1040c2060000180d2082c4c4000382c20410030303405036100e031803064000420102e140e210000071203048041030703d142e555441c4078405545007001028000724840007070185000ea000000384a40141c0c010280501c200240000f031035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 429894865 1250 429893615 429893627
    0x30705030a08190f1406040908030c0a170a091205090d030e060d1d070902190e030a0b0702010b01080609070909090c080a0302070801060605030606070f020d060c1205060a03021f 78
    0x6a2403401003001801c44c2132035400c010700075209400c441c69038814003248081c1014014a010a82c0100c1c04c149103403102080c0343d04a50100c0500b504000c3d411010404180c0031100d400d00031810b91070046101061801c1c800b035511046071030003047c0314040000b00f5094856200000b003003501410550030300c201d0a0041190303445140002d03156107240c205054044d00c0c602c43d501005001e2071040b107040f1501c0b80c40c064228420603504203924856a0359442d10036105c3c800c1001c1612026007500c50880e226607031618400c6040c0d9103000980d445501c080040d50744041020713071040044035911400d040014000d8079444c494011000d0090b01c0e511090103104510b038030500184050f8040f90452522800c00075140c007031602624005500300540020f0031031190054900851009000c90716106880c1e9444031780d009241e600301c0c0c0081c0248000400b04841d84100c11143e2010b0300d595445500704008102110720040410b0301c103451a150600142c2c881c00d03018040b103000c1100d00606091540700542d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 429896115 1250 429894865 429894901
    0x9150301080d09090501081f1b05180a180213031403040e07090819050a05060711010c02070b0706090f0f0f060605030f0c09100512030714030705030a08 67
    0x500000000009000000001e5039a5903052965501404684a4003003d0036a0000c0c801e0340081c3d4030220004103800c1c1d00a461000e1090740d100000b032020051244501140b01520451000c104049040b035030f01c1d22480c04007600001c084030b0059146003040007400d11101007510780c45900d903001c14038212400c110103090001d5034004400b4035040803201d5010384c2d04d0b40700c1c0c0113501201d0b68040200e04280e0042c030404080c1c6800202601c900d802c0510b540d803078142854000c1e503184c03140b001d82002042c0280f01907401244035685026541655103802420754405000d00002c650010030108004968082178500ca00d51000303000c5004001810681d100150b51704016002c1c9040490440070001c401c5030006100e03118020031300616039680308254546c0088603c001964020601c164240d24007030b40501d031b000e66040f85107013465854030041205d202c0a45c00f401080c4d44005100023b10118034450b41026405000239440c002e2582d079081d8a030b0213962600c00600c001000401d09107180c1c8415004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 429897365 1250 429896115 429896149
    0x70f0e040908180a1521020a1d010c0c03020405130209130317060d150608010e0708010605030a03050f0702012a03030b0102060c0403030806040b0a080714010507110609 74
    0x4030780d405080001c1a988050400c400d540094110071100d0304081c03d00030101c40003035407050800d078034800d030507194403081d40c628040f11803500c4800980f4412601c05000c0010032580c84400d00303031140c2800b1000c2c0411386001418051201c1c11440000e002c10462000d0300e9054801144540f29081d071154240d5260800a612010200410100d450710312036000440d400781e42c0300403a440c903450042107201000e80f406030308101054807070804200c402c0441901c4440d200c0300026501d50307a000040c21240c401e10060f4076600301c40320030045502c1c24000d4902134141217020780310980159030042d009200c1d545464440a41c0803a1036002d580c01621424900f2101074a040212509681b004181c100543d1049002c2480d014404030154400141c00c0d21a030b4089442c00d00d89411500c0587d90f1400c000d04403580540c4944084255440b031072400c900500040e4020080c160401c10113000300600c1c1c994440c1003000c14448400400d00b0380c2c2c8040c40f6114142d503400d81e03910340780010030f4030040c914154403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 429898615 1250 429897365 429897371
    0xa1b1d060c0f011b08161d01020723040e0c03250e100905070306080309040f06080a03021f0509030f0c030d0603050706020706030516030b06070c0915060c030206070f0e04 75
    0x10191a2055070545000401c0e660303808195030301c1c280c0e20011054051300d040c002903202071240b5100c10b811f061304401403030140111940f103503070740620446941016444005141c0030191083c0780d41401e000305400e034a00d08010b040d4414564002c80d0303a6000b42400304094108a58558111501640303142014005c0a14001410715041c2c00d110022031040c490080c220b8640000107500d14032034840c01043e505660091854250340c4810407002d4a02c0060120329150b648000041c42d450401154186510130b80141c8411010f0041000500710b0760881c0460450500c0100014082d010080300c14041503c20b820303444490041d4030341d207180900c035451007242d841c001e004010300c20000b9041003100c155500f00ca6001d919040110240d0300c0c141c580544243c841c1200e990190300035040703070400302c20251000c1c3c149034264540e1440c0c20803951000d8180c507615a02c0000b10628404190050941070614507010105980c000b9038503800144524100649500c031748002c1c42c49044110360041d4003c0c000c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429899865 1250 429898615 429898631
    0x81306020d050402010e01020d09030209090111070b0708010e09060105060310092307030917070203120706051b0f030424090302030d14011a03071202030a1b1d060c0f01 74
    0x850300400b003d9a041e404248010442c0c1955880000c4021495256a036003100083c40c642c20721501d100054024003003075403540c800440000c0204054149030b40507540003002c504013030350068807604040e0070003408500c2880400018000c0091020b044640c25070310980d696545060703071100c506264204000242c10140c00c0403411406903244607052078180b030207201a80390300c0419011500810741c010819407580c02c45001c9003529401030300d400350019094074070036041590745031050760009004079460b40d5600c05000100520b0005d44150001c2d2600081c03424161012841e4540401000100400d00b035910f40d0003d61200d4100c4e000d180308501042c0410001032030040d40b81c0c4c0141d003a0311f500ca031402c240c0741100200143e100e030407102c2c444074141c40c3c06506181e00505034001010b02013404140d00d03081103c000345100a5208160000c4002000e4803920100100514104041e004005180180040d00b03000040805003114007241d0086d56404c01c00909400c1003400e4010100c103518120380c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429901115 1250 429899865 429899887
    0xb0c1b06040e1f230409021507150e010513080c1609090308101d0a2003180a0305030a090f060c05030106080106020a050c0409081c0b03010c03180308130602 69
    0x750864032500450b103500c205461316060705030701c0000d040e9042c4200341080da00390103007880e41c80403c01c2c5001a01d4000c80e003c50102c450866400b03404c0449240d5000302400c0719001a40c401c1406c98402c220080c025400d001c900602076008048025001c007500084085542c0810080610502c80b0072822541c02941e48031400001c0c62440c00542c00318012f180020184030b54804003000ba00c1c990a01507507442000c420480e0000742c01091054115903400141140030300c07000001000e01f84004080e80d980c50f1550983c02c0c01c2e6080040d00f21103034845801840041c0d007200542e03a020780030410015048070039080154018003c440007402c0645001c5d07544d0807150303204004505079102178440e60700e00c0c7d0ba90181203a8a940c40c513800782c410340002205440500c6e083d0001a600c0d4040c218a9081100c248d185066418001702401c004a9032030b4045901400c0a00034054240d03128181089078401002841c030411200030300080800c4480c100048140d00032060b2180081c0c0c0008085403200c840c096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429902365 1250 429901115 429901141
    0x51e040905030a170f282d09030804060509210702010306120803011e03060f0509010b0a030209041104110318070f18050c09060a02030403020405010b0c1b06040e 71
    0x9900c50001d0010b40e034543d001305030aa0690f014807440111a00f0594422588441146207407421080700da084200c0b4224151180c002c0b1520f01012000440b000c01011460301a000032181f200c0150504240400c40400d400002c0b1640c400e400810104140d642d41405c0d0f4100403484403488214104203031083c1c51107513808050b08000e8801e88003040bc494848251603001103041d24001d049a400300b006211451814864061030729008040b504204d480799241030595980d2407000f00b46540d107030104004010240680400c011050f075507880300c1030450b00840c61100780140040d1042c0d184000e4041e080c0c80d99400102d10008042c80c01d0344030b040c408016042c11009a8140c02d040c40f0301c00c00465402880b08601040b101082d026658170b081090754035001d010b0040009580360400d010351507854994a0003004144a654040c5a856045104010403950180c0184204090070f1100400e5800c1c0001c800302100420745509014695460004105100d6900448981f0750611b0501c400800c100d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429903615 1250 429902365 429902377
    0x40203060601021504080702180703050906070e01020d0302030915010305060f01090c0e010e030c034603080a0e030d050603150402010f1206030506130c06050310051e04090503 77
    0x40503510300391101c000490713640500c0e05150a80c401c1580210740024a250010310580348090141440d100b01070740c0b01d45500304100d03055000300e0f4455082190f01907041c85141d038490400c0c14208100d60072140001c1d030b02c0c141c08070100d051580c000049110030100704252280d030b03140304410840643c0c5900e0006e0700c3c0c41040d10351406a1400740700104083c0c000b8001d46402d0b00c4155a0340b05c900080600454402d011800390b250180214040d52509843c188060740100c8503410062111b005014144602000414042c0d4081070000300501d000001568002c888150540781c0400c454580c035001d44000c0030104a056414071001440940d43c8499030005403080701c046050300d0340c0810300865040c10b603504690007070010388203494005620340a44a55100c010351480d002a020340c80c1da0318a8030f8000b0503241c00c8519049034001c00c0800120000c4607000d480e0501c5c20500f1070404005540c0440c1e901c0c00342c0d41c821384608440e5022402d5044901e0412a8000c00c1480b082c4594102a5144c0d80a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429904865 1250 429903615 429903619
    0x1c14011e12110a061b06020d090b0f07021b03030a0509010513060c150221150301060e0f1e01060e062203020108060303040e060405040602070f03120c4803080402 71
    0xf403540002d000c1d002c0d016280002010a0001c2c41141150f0ba03088000d611400c89901120340c0d604115000c00d41180300d4a01c0b41c142d42c20007500e13500f0003400c0030b890700d080c42c401c140c100365140010303900540700030090b181c0ca41203034144140c41c1d2419400580b01405600024448004003000000d46030340e03c102c012031503a0182c980301e03030414801c101d20800e9201c2d07039100c1c0c0b81e403240c10030000460501e407459050b8044100d4206400009047e0006400d40e035150307001c4a0000030403c01e20030740c620308448203500300700d040c5503449103c000c000d181010900141704000507c0001e001403004c0380c172042c0c1243c84100c0e5200041080d1680586040903090040c08141d00203541c140001c0c625090010480742500c400083c0002d09a40da81c08000c040d041c006d00450b1003d80030700185001400b0801c083d144280700b5111007d41403202c0741c8083c21554502040d00c2000359500444924200b445030080303c400b850041914403060303413a000b00c260000100a1405441e54440c10b00c145540301c6e20140c051442 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429906115 1250 429904865 429904879
    0xb030d05190807051e210a0c032309030409090312060f0515070c090207150e063603030109020c07050315011e0503030f1c14011e1211 59
    0x32848225a080000c43d2900040360081220440c88040640039800c84c45a40108506d011101100ba00d40c17290412000082d40c0d8004007404174a000380d002d000c0007140c0901e07041121481614078040d0358410919214003110900000c0b601d440b400b4411035015040f90001880410800d1030028525043d00d0004107020f41b4000e004215aa1074100c0740003202e00040c00640035240d803506650072035002070340440344041070042c00a0021a0340c0090b10b0381c50b005060b4810388402000e203480c10b80e12030b0213502e01341d07400803020045000740c040240108100c1380080000514840407079910780c032a40021000da030740302c04400014100c009400810000400c00150f4206950b19002d155035100c6625054084c0707504000140030079001001e02020f03801400318081d415a5591010908552000e08100c19241c000601700d115140c43c41c681c0c008448030b2201c204150744881824ac1507605040c00345080491403c1d0080341005d103000c25a40141251642032aa01d22062406611020039400e17000d000e41c107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429907365 1250 429906115 429906157
    0x712110c0c012102090604030c080c010206070305040b010b0f12090f0c0301021305040c090f0e01060e0d030c02091003050f070f0b03190c030908130f090606021f0b030d05 75
    0x100c1601002c90b28683d4849401c008035141004101a400c8a05415006181844000003140c40400c010f0002d003c5003014001101e007060009081c075a006202c1e40c01c0c141040203100001b102281c440c1d0450348207007200b07910b40d1805000301c2224401c8500c403072118880002480752429012601c1e903048064203044541c29a0120113142c240d0040e00704188410385154401c1011f03040c91b42207480e00f0040303460b00001c202d40307812024150040c3c81e002607542e0201d4400621a480d08122030508a0901325082d00c503030115a9070090000c201d4a0000340100010740102c0c010f40390562041004c1c6078008190f80e03454410010b0b8998460a81c842d154400c00c40c2c3ca00051145401c80480e400b548005490139240d0440b01d0260026080000c0d071001003559441c00c10001c503481034003512011450b1107010074020b14041035410400d030710f0342103142501e15241c070412626400050707664a00e60652041444411304c4c1441000410024031741d20f0f010702a50300e201034000d03803090007408081c440c17814185100e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429908615 1250 429907365 429907367
    0x8060105180a0525020c0306010f180c0912060902090c070201090303052d0702120303130f0204020c0a0506040606060e094512070206030402090712110c0c01 69
    0x7001800084200300080494040425600f043e075110441c1250001d210320004524925010409040001070b0800b8a0300e040702d107814080a401804881409501a0b0400e40c03020300202c519441c6640e8140c1e55555414081e001d5541c20700207015000307400701d02c2c200b00c0c02c1c00c5002c0c0c1507078030040384507000d500d0000b111546144107032291107406954000c1c0341411540c00f9500c550041500e081d507a0036070441510007007501044040c04120324914aa1101c0d40c07407040c84280301440c0d010382c40c290003d2003081003481d51511400241c9400c004001c40c03042071030000c14001d1082c0c1d000c800d10340c021004003a0074030200055150103544100406c002c15640c0300740c1110382c0c8160b950080c7e401000d0202040403182c3c1c46251040c840c80001c15015040c142c100400d00f80301c2d14003182800240c3c0900c0030700800307006001d458040400100d82915110b01540001c2007031000800081c07080e5008000324480c0c0e403080852981c00c406901003049644942c0b0103540454000f12817040582c401c200405480e9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429909865 1250 429908615 429908629
    0x6060207080111040b0415030b031c020d020a030e270703061e0503070b0708090d0308071701050d08070314030406050f0105060a020a1e0b1003140304060e040c03060b070c08060105 79
    0xc031780404d40300d41440c0c01c000c00032000200b810240f00030985c82c0c0005251640d42880305c0f00200040e1400348803803601945020f4100802102d0707103c10f41d009201360308007080c4c001b8400031000c5421900911600b581a42101601e0010410701a180403c0c03020481142d8241e031114080d00d9000c200c60860504200300c82c1801c0301d90b402115056081600b04000c805090000b41c00400c1c82013461a05041400012915110050100758005882d03981840051078000c41540b40d0341c4202000420345606020125039143c0744018000c004140008200301418442c5507001c807034140d2004a160713a42007074148500034040036541c43c01c2e0149454000582483c00e1000c403494607400d0b0300940030510181d142c181040a001421030082038145d400500040c240a00680c8100076030f039682d440f010f0650501c80c11440c00b1003e0a0305d194000c01007409480d810515501c0c44110403940400c1401c1300040440c041e140f26401030342800d44c0801c080c402c0114254094081c1c45a54088844d640c0ea03510412144d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429911115 1250 429909865 429909869
    0x10f0b070f0f0305160312150f150504030c060903051002030f070341090c0303070803070203041208090f03010c050706150b0a120b010c02150c100606020708011104 72
    0x15081d1149000000a80342c080c012007094040c0c144603060200700910117280000b01401207001500f03c0c10f004c811184d03035200e020301a204030341c54010000e06011000c001c8505034001c0b01e401d5040061000205442541110042c42d4007150f55034041d55120700c0903080d605940000c07601c5000b400704a0002c08064400ea074441d0402c00c03110001c64444420680c000c0900546529003400c82d4484009842d2180c45485415100201212074142488010524000300a8090005900003440d43c4100e0707036000041d20050f54009070200e91b29265075209a15510496101160b2003e205c1c0500701031100c040050802c144003030303d000070300c0e184403400c06088800496a0b90f000c00d02c20b20006008c2201a8880101031510a0b8018a00c0f6120420200c0c1c0b40c019030044400540350120300310b8181014001c89901c0c15080c00c0c200312016581c4e000a5119001c400c072440e03c070001240c9000d4510381080150948545400204200ca45a0380c0c000c3d02c0781e20318051500b096003401443e80c02e00c2c080300200c400b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429912365 1250 429911115 429911123
    0x71e060513090b040e010e160504060b0a08090a06060314100506100e010c1a10090b0d03030e010b091807051c02190b04080307020907021506010e01051b0105010f0b07 73
    0x16101e030516060b040100310f51055180c100b5641c08130000103403003d204002802c503489000b0051080707558101d40d40301c0240d4010b0fa0003241081420840c4818100640d003030070300a030601011583d62400010326000b0610b6019102c18100f00000040c8a00c012300b56404504000a454001840b000030806980d01a68140c0e000b603d240c003813100c46449221700e03407a6104149041a90602d1580b183e110015500ea911046854401b0030321102005000701a001040468010300c00940702c9c00c0011240248110040c01b071640717411503000a11400c0d80200e05a080041207000641001e44000d94180c3e62020b4500030b5208401c3c0201e41440c1c184162541c800c210781060040003515400c0c480307103072002c207403958002400c030358003140362003404010304081c1019400641e129056801001800350014101e401550841c04c0114915814100c01550204003820b020382d0003c0d150004031060700c034a41c0c00c504a02181000c2d404802c0c0103400c624100ca4503a180c43c0450364031071140c500140304000d0010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429913615 1250 429912365 429912397
    0xc09060d05010c0327030e270109050115020a0515100b1209010e010b0901051512010312020d0309080d1a100504090e19061a040218040f02040f0909080c071e0605 71
    0x141023480e0503c40b842c0c0303411160484c08901c12880000c55440e070343c00e0b0006101a41c444005000318100d0f20350b400140304151006006004482d101c80e5182c400702c03d50440078880c50000a512402d40d03044000041c0101440184e4413000203082032441c1400f620403400039400c2141041070404140100507049100406a40c0390ba40380400308481102940c0345400c0b040803e2094904500500e001c0500039030090300c54441045103040000c0c01c10450701c40310800e05207001c079108007040c581c00641d20600da41400010300c2c2c0394003002d6050030b100c0844015921812960f008561039038400c01805c02c075914660184802202003500d99182e10140c64210016407410b200c0a010400b00d07040018800324000484000d0380d1510045026070703100201e00c40340d054017800c04880c0c0c1e040c41d100d0006101c0700c004085041908088200880d90420b1160801c81511900e240d024084034604846800f20008212000f25540320312405011260100240010300302e5800010740d28080c0c403c1320010b0035440552 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429914865 1250 429913615 429913637
    0x15060c170910211d010f02031302120c060406091d0705030408070f0c0f061205070e22020d050f0a0209010c031b061d07050f030c09060d05010c032703 66
    0x126180b910340000802400c50408480500c03541602c29180c030002130340d900c0104968070750718080c2551007003001444060b2040081100481814044000b43d42e030440b880c8a0b0049448442d5107000319010550b41d00c4500001d00244a6412041c1c000480c1d0b5501c01c0743d503104519000509120004460502c0070417020400500082e41d840020482144a182e8020303841c01070303880304000d1000a400000f4032a001210030b001158201040c44162a6500b005003d503181c24400108615440d80c0a103000740c01600012a5540c0840081959904034510440d00c03518041e0805010f00030556400541c441e0340404a56645058000c8030050340c0181c42e5400528259034040381d40c12500346020f154107120320b02620020b40070f40101c0000d00d00e42000000500c602c03442082c1040702aa210f13a1085001c100000a1900c000c50100660700c02150644140da403400f001c951094032a05c1d004215501e00f8800f000d169405911000600340204248240400240001101d030a00c10764040d0108041c4460 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429916115 1250 429914865 429914867
    0x4050118090f0b0a020a0809010504050d08180604080a090605360306040c0801050105010504050a0e0a02040308120106030515061602030c0406090e06060103020301030c0b09030115060c170910 84
    0x44900302070b1044a0302c2941c0c441c070b6241c0b5072076030100f9501a42655000140303e84404d42c0030180c1600a500c2c08020805814650b0f03503541c2da20b42c40c0b1908400e000c01000024464001e070080116507000c800d00341c502c0c503d03292600744900c0e131240c1c3c1220086201d254005c140940b007002683d81e940d5250b40e40f4040c03409005801d400082603400c0040d04000040905011910700348680d071f00550cc03c03c007250546041159160940710141c0161b4108881400200015501d140300e40045036400070110000340c90f140350000c080c0c800d54002421094001441e0001b0000c092000c034101c0d05541e4003080349454018030521780e4030303088151541c004820b100c10701100d80c000250008941c8002e08a400340075489010805541d025401440d0103996010017101402d014403c0c1c0798002024a802c526644c11031b902d0100b203412a01440b540e452012a40c402291000d50001140d003000e00144103036295280801030184420520444403465144008940074034410241d540c2641e000b40f880e110044a100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429917365 1250 429916115 429916121
    0x706050f0708090406270b060a0c0515010b0301150c03270e0a0c030501080c0108011217040314010b030a0c150e0a06020a02030613031b02122a04050118 67
    0x3909444602c070030000000703540c4e12440342000418034020450911100151000d240c810391049000a190501012200d199074460459031340f07050354207194011000307504260340341840c81c1c3c1c224015084610004502841610003450403559615110401e940e0400390880c3e20f604015402404143d08040e00145006402110038603101603000141c81c1582d2000d100c02c0421041d80c940c42c50654540e4940041a80f40c0100745c05400034a0050584045907000285110014818000c4842900328514200620300754240070280c1800302050300c481c4c6034148903481c0710006071a000c33590701c1c0c54800101c9043c041a0300d0f01842c1c003c100305845900c0c0c180710803008080107000c94100b1800405017042a6101080080901640da00914010032244181450a0030142614036a811030305c042d9000240c0c04440100c09203000c10031440b8581e5148003261000d480c64112030414010944007051641034002109200032060f022050703107010300005d0008850b4203028594151082411100701441c00b50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429918615 1250 429917365 429917377
    0x1605010917010b0301060b04060e06090901030f02060d050a0609061e0308160602180405010614091c0f0f02030606010504030507090e1c02060f010914040213020409060e10080706050f 80
    0x700046415825034001908483c0301e904105a41c00d40445d09202580c0e0106c02201d11060660b6103614050758000020459081440014181c4000d4030f008011901c8036010b840004d15010003d129070b00700341d11a0800382c02140142c0240b189407610010360390480c01080003001144000041165045172030791145503214480074032140c03204901c031400041c1c60b440100350140c0003203501510444c1460800082e140180c0c00f4000b040700c0c00764501c099100f18070440c1d5030003000701d8240040c140d101e1b41104050341c11483c0a440100345442000034803040f44c5003101020710840c15599181c0d2041c006440500907408050541c0e80544801d0103603640a910110020f4080801c448803680c010900756440900c141e1102c005800c0038061100d118584000140500782042c820b102c0f90000d200c0b044151040108040c0c030403551443d01300d120b00415411200500203d160601c041c42e15401c1d0b44000c52401c0d613004108603105400024008004929101a50304c5030760707610300d0035080f01e100880a81040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429919865 1250 429918615 429918659
    0x1905010b1f0c02011b0807120203030907120303060506030c070b0f0c0a08060d060c020d020c0d02150306040f0f14220803071707030504140a0203030d0f1b080916050109 74
    0xb038807018454170036103080130300124490505e8071703615845450800141131080c0da110046d03500a00c00d10140c0d9402151180a9845191415540242c0ca050440141801c0e07441244c00010010a1000c0b0705e68040c003c02e0b40c0c60145401d512161221080c031025017800b00d580d24040c000034026202141e00c03500d9125007003140140300f03102c1080c00d81c48460441d0b1400e1811400340c0c1c440c0c03560320a207640500080d007118a0407611951840360a8002c1291201040c0540000c4040000060510703503131540500b911030a401d0040092451101050001381030300d80d48400001500c00c0060b482040406040d802081811403c0c0c4210b455a07642020907040602001c0600041114250100358051034052283d1190340e004100c0341040d040507490000ca81c0c2a505035604a05094009a1400012a00204425640051611400b420003c010404d20700c01e044125130101c00d040720103a01101260040f440d68003074400c8910701841c0e07640d040300c140c8503042c0032174803608040040200c01d0005416400c3c00e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429921115 1250 429919865 429919877
    0x14011806270b0a051b1f020c0102041a04061e020a1509050a06020306040f05090309010e031504210c031d01090e0405030901080c07030801030b220b040302121317010e1905010b1f0c0201 81
    0x2503036142ccca222660701c5c034401404c0034046000c000d803c2d4410061a1480e0191071405051a00004000d45035985110003800d140c0a41141b038400000075030100c070240d504982581c0198100f441e018010f5072003030f5100c4c0d10540c1400300200c20510203104513400341741c1080c01545002c141c2001910207482400780b55515000302501d540040800a0120f44110701c125019181100c08042001003840035240400820820304050700c000790300541a80030300401d00482d24a41b218113401280e2000b1a50071421840080000384010000004051b124882d000d0301e80b09103035541e0000d454a0385c050400043e00084500b001007010969800c051900030048500c0d080b41c121844071601c00c0d4401d01401161600c10762001c110506070305100c050310400188a0080c903114181c014200000360b0741c004c1e140400c00b1000fa100700a02d00358000d420121041090b41d020300300408190105540d02c00703081d00d0035400c0094045c0c19103400c490282c0941c000d04018011114220b80031103501001c40c1e012414018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429922365 1250 429921115 429921119
    0x7020601240516050313030f030909020f07060b0a05030109110307240f180824060a0515040f060207241b050705090114011806270b0a051b1f020c010204 67
    0x41006d10b102c003960040145070300070103c500e00101000071940c0034040c42e52041c840c00010070030800403118419009580462581083c40000d01240416440594958a010600c00400154840c0c0e440c2802c812010b5500c1c142e0b4030540d0340d2911000d4400000320300000310b02c0924040c003c0d25111140c2c2c0142c502002d00c000a00042e81148086400140385a801b0120301e50f4020818032900d45229242d10f1958140d06000f800315280b240c0d64010144203014039035511020b605001c003603e00a101064404103013980d1080065181d0803980035000c00320202006010120a0b010445002121155140c00d1000701012044100b10100c071004ca40a016501b40004d41d91359460940340a0404440d070700300341c60240800035125528818030342c006030b00f1040e410400241c00c10034030704050f10700c4c92110444480110a00480c200a60842c0c1c40c0c1800210b420500c46500c00c000e0885040f641e81d05844c076041c4403102c299514840000310b000940148031a441c01d20054000e0901014150300160401f6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429923615 1250 429922365 429922387
    0x2505030a030507062d020901020109061b1107140d15110315190e070c0b0c030105120c1003020f0c0a140c150f0304020f0603070206012405160503 64
    0x3100d2080a40001d04049035550600c078051092040c0c0488400c003e0010b94031008803502c021000e070b14501502c44d40450440e145034000c0d0000d141007075200100b00700d1000e00203074081c0d00044540031000000d003000100c00001400141c4217007996030821144408a02a0302005803520f0104070840f0b01904c006030b001400c52082c065100c0c00038100800d181c8a18244100f02509481e00103000d1080c081c0b9100d40c0e01110300918101e05452050308024a2543d0380d000c25101da42078500020700100e800c40c208000b086813800a507050710821111100030424440009a503900349030445e80e0b2000002640300c140b54042d500800c450400401081c0c1000e1f00c0c80c0d906402c00700079080c10303107101401500007104040140003031000000c0445581000a070012202c4110780a0314428495103107000011400350b507102000003441c590000c04240d40e078504040001d444020a2150344400c03110482182d0901c5903084884070304880a54600742001c0c1105600c06444001c090152240e0108100501c800c0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429924865 1250 429923615 429923623
    0x6060409020a02061914360106050102061021061b23070f110d060603030e011e020c01120b04111209010501180f0b030d09031a040203250503 62
    0x7103405500070300124900545c0203081200e2010701c0c950719a16015140303c03c14100c800d000e400c804418180ba401e9103a40443c85030304000814070041c09814411520f209280c1504030b02c1c00d4030000c6e4252034054940c2404102c008165000c0c1d541001d0203184c1c4440140d40254891041c1800b030b500115100100d144200d06c0120a03104178000602500b621001d01c0d091800c0e03840e01c1580c003290707103440c1490381c0c0c9899a0082c607410000700482c0d51200c40700c2307803075032005441c1003141d0300b03d1400c2107103660303a1502a11000d50480d0389800318103c4546d00c040450240d040d000d402c0d074141c01801c2c81004001c0119583c0465003040402c0603651000c40059440c0c5124281c803074074003c17007816034400034408880040c200082150007241c0c1001d0061120114002d6901000c1a07200d9021400b00c18040c03003070000e011006161074141c0715116100b00c00c1648118040c2c122070280d05402d5401d0b010b1000f22510940c00c90b07010390550b10400a08840900c4e0f50700c0400410b00d242c10b49030005886000184c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429926115 1250 429924865 429924877
    0x6030504020325030b0606070c170a06020307050306120a0c09020f13060203120c041202210607050d060503010203010e070e0d080403050d140315010f02070f170d081e0606040902 78
    0x182000a040500801c170310084200d03000b08044a2003820040c0c0380e40c40e58046070041c0a81500100e8007008001d50a408000c0121140d41c0079800795182d25010200600a400403114070788200c0c0c00c0710180025440201d000360310b00750000b004103201820920040003a501c40410306000510811482544003042c602480c041e040301d0380a15611460680e8494480401810700c50040390104400c0081240030001e64065030750644941150400c40307605441030448802101d181402510200403007954800028107840403821001c00000342c88905150807800309000c0c07140480e80c03070000b01d205240505a51103104a00030444008418561364400183d000340d80101c46607449000684800364001d591407006c5802c03000d2050451800300e440c45500c04010100c01e05106410f481c034441c452007401410003410036541706e045a695a4100b48404004054440a05000c0d0004c4100c03401d20a038030a500034011002034400100f0707100400800e840b00030b441030b0352000e02003000290031070b00c50000c1e01c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429927365 1250 429926115 429926173
    0x9050c1504081c031514220e0622030503040f0204110c01090b060405070c030f090b0c07080c030601030308011806030609080c06010602060105031506040f061514030c04060305040203 80
    0x245410080c81c3c080d007503c800186032034101848803030500c0715000c2c10011a00010044030380c2c000c58901109035450400f103110703640310158101080c014028500040090050300983d4034020300303c1924041c90440c0840d02e0000300055010408100452102c00113070030b03881e0000b017000590310049216141c03281e0203488041078030394442400f80e0620032459a040e901c4201918103001e18640382d4801802242001c3d03005051120b2401811002c0f881079055101070b200d81c019032551080e510310303076270b5482d085481140c22904c900c007101e80c418100491050b04803070745a19030416503424120221a1001a0008481c5007030f9114400008134201d40149041c050089002a9451288810160030b00c28160040e0055511180041141d6100011a400241040100e100013520361000180c0030b401a003025514003400c1c2071001c2003071a10030310003005041903501c1e40303030600c001c0c0c0e4071004a0b4042192422007208051104002c828001d410103a4842d02c0141a50f014080200040c44e1002494090301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429928615 1250 429927365 429927403
    0x20319060e0a1b081f0f080a0605091203041e06020d050103021804030f110a02090703270201090909022e12020c1c09080321070309050c150408 63
    0x90040410b20503810f01c4802d190801400d210010005001d0703200203041e00150707101510240c0c03985503001411700040c029201145100568642d051590382c003882400f1f075a054a4071011a0043c0800a4400c046200002c9081d0a507a10fa8030b1b50403d0210304040141180981c034040c40000d5000e200415411440d04800102e41d41507006000d01e11808103000c041c0c4a08600034407011035004602120900c0441c60400041c00c00701d07412a0810798041002074120340d0784e0781070042094050300030141010461000e400e1484128405510459460710060f02140e04400140400c0d4080d8000c00328a81c0058100484420000150310b103898500003002e201c041202d503001d40807030b40f10351078501250502000794200780140d000e00e9102d4560503040301c01c0f0020281500d46c128000c1404038000c11404050700d4444e0b28044441180d8116046401c05000d550400104180d02901c00e0030b16880e0132070000c0043c45560424070000760f074002c00302d281c090000e000c0024001c1c1c041007610090b2408011354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429929865 1250 429928615 429928621
    0x90408070c080304140f0109170304080f0c012604020405070e060d0b0108010b0406051602011b0c03030305060a0e27030705010603020a092f1603020609100e10020319060e 75
    0x11450304070201d0340807840b4982c6e074808552142e0f444501c0c1026940c4003181840300c00d210f06250b40c0380d0f21403584040198007407915903000084010071070441c00c0c8001c0c0c0320008403890041c051194080c10810b50703c442142c20000c1009070a00b5801254010341c641070140303081a4a0001030700503003095081008003038507107440c541a941d100340468010140040c0741424075003080b00103400c0d4010102c00313442030418045a0303000d681c8608542d008600251401010305001400e00314002c2041c0c0c0802d902090400d03002c5056400e0042c5000106c2d01540d09200c00d40d102c0c0300c8945481003261f2035885822414000c000c8203010140020400b1512038400000e1440c034601c14400011029407000b035203203282207040150040d100d0714108502d0402e07401d0941c000004451030905000d40e045074400341942480351401c040e000108280189004011a00790b1420840e005060720003065403c1c05680200204042214482d005981c00582400006400010000d4144116855035000c403442d00700003014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429931115 1250 429929865 429929879
    0xc060b04060e100803131206091e060e0a1505090114070f02010f1109100203070f08071a100501260906240f09190f050702010b060301030b010302090408070c080304 72
    0x15010040c44c050024505010b0b1045050000d00b45902c9180344950303074044460108030f99035110183c4164040c000e90300c240f480744400310196112a004486161030444000c0c1c5210340010801c010951023030008202448090400e00603200c090403209496403100d0005201108040078580b140c1115911100002c0070302c00003e0030344500b030300c9804100d46450101841c04651408071036640b503003550f40700d240840945080b40346110384100038008400c9040c1c40000c001c0c40e00d000303065050007801d11162202e2001c5c0e030905103a01c192520140ea5102c000e081010394010b08a1605041c40b900c3c00d8500030110b16020748490800b102c204543e500483c080007001110503550720055441c5c02010303070a401c08640400d40004c04c40340003d100b40004000205040c00c00d0307499907003201e9108014007042c05824074100c0a01b5013982c04402550a01c456000c440c01c01c0d2058078100e076040300031079405910310f400f40018800e0140090720361350002c00c0540007050307643c802034000305404c4001310345ea0761401d96 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429932365 1250 429931115 429931141
    0x220e070308030a15030b04080f16030e0126040209220c0312020d020a032115030b0718051216080a0506130b0f070e041e0e011404030c060b04060e 64
    0x495003446140080910104891b0b4201c2c40d40305610a011650b1152082000903d50044841082012240e0f04000080503840417051042807400e0300c075412902000d00d07100402400241c04600c0c101a100001800345c905103262581241d1003001c0c40d00d40850ac0d00f03c484d041c00e5017502c00d4542d41c0d07003a2400c00811003980c9030011510b61074030180c040a401090000e444041c01540542004030010f410b00f120340e1170b208030003084c8032110070030003a00042c601c3c02403040105120648103003c0318000200b600d80104d402c42c40581d1501642180d00341000104908201171f448041c9440c49406801d5207007060520b4900301030b1800300000c049a00d0070b1f2031308503d0002d00401071403000c030f080300424001903203100050303410402e61900040c083e82c07003080c121050b5400b804801e030710a007410001e1203c81403080000001c0104141d0900119000c03c08081c00d0b140b5280c0d040c609401d41000040c0468810700300c0301820b41c032540003c1001031510b800102640d100780c005080c5281c10600748030914402d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429933615 1250 429932365 429932381
    0x90e060105070b070509040b130c0e040e030d020c0a0c1e08120712121a0901091104060f05040503151609030c18090602040801020307120b220e070308030a 68
    0x440c00901e45041c030355545090340f0028003000d0034040c01050211040c0c1c3c0da40c21411481602030085110507110b03445072005000040800400310f070701e8201e1065603051500480b559942144025841c00c00c403a002c1000941c40140300e00c1c01405441c0d420740002e4900c480b040d0060540248079420003039008810f02041c0c4503907000d4a40b5901600007090a903007108103603000346411801c84608510600800c0d94031240c1c03054640340161074140e03108840400c006440900f4041030324080700f1030380c0381c0a81400b115000301183d004000701f800100183d900c5800c0429062155103456821b00766564040707440c15250b60342e403582c4c039500d074410884000b08070520318142078100d14010415510b0760b01c6815681e4484e024860000c42000c900b40c281d100d00350440c03802240d004000315a603658880c1814001c1d001600c10704005140400c10314940c800d14080d1080d041c40c000c01c000940c4440091003031030b424020001d03a5000e61030b00107680c0d06960601021000b98020407a05940c1d107010071030b00c021140c00d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429934865 1250 429933615 429933617
    0x61b06090f0f030304111c02300c09041101091205070311190501030e15150f1203030c03100503060a0b0406090c1b0503070b010f061404060c20030a03090e0601 70
    0x41c400c02c00401e403421103c01018001f9941d00e44c0318000c00400da20340c42801d90700070b50052082250b1100d02500300030801e203030880c03414100351048200034016444085d42c640181d0711000d08000301d408a407001c02024202e080504216a1069407031403201401a071301c0c3d106850070740000e0030400903c60000b80403001342208444000305074003042c5a004200b1602d001d114100342d518000518000410000840e5041e01039032040f03441c1c0381c2000140100c21410800714004c51401020307484509200c10803401c1c0f1074408005d03506540d41c000d100c541542000340440e55940c0c405900013842d4800303001681c00348041c8517003c40d41d56100380500040e1071042d8800300c0c0e580d06d080e6006400a81c800c0c2043c6a41040c020500c0c440303440ca0038168a14000c03130b90080c000e28a0b4200002c4d000340604c20100c2126003681300c80c484206040c03609e500d113008074800c0343d0218001e4196240041c070103000c4400c02c80048600000c4e0043c681010900d0502e40010403400300f25803400078800106051070540d405482 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429936115 1250 429934865 429934867
    0x105070806090c1209031c020417030316111501031a09030a0c0602130302060c07090b1f180803040b0703200a0f080d020307030902040507110705061b06090f0f03 71
    0x21150096625105204d0b0315001c412890001c40c5152005200b22404020f08290216040820b0308541d0000d50040c4103005014100e07000541e0f2040c1e0110540b84105860502401c1c950490101600e40c085407440240d43d03401350181107a03a01104500c4d44c3c1c083d500584010302280d0f00c442b08401400005003109481d03030300c21320603541082d0b4410504044075500103005a280c14169440075018820364000a610480100718090518400900b56044800d4410140304c02d1039078005100300308980081140848103441c3c4410030750303805480d0f0804031002e4400078030529076032030185a00310303045500040a0480001400c1c0306160740401d5128181201c600c07001d40707101c440d41015031307a803413040b400034003070303207510303c0b220b00b4004172000b0740d170141ca01c40c54190341c1e070318242d01d00130002c200d00380b42244103500d08004103403028815001c2c015202035600c0100409402c0004110968001404c4881d83d2012031842d04001c3c04140000380c01107503039200910030036020903c01c905040800903400c040e0380c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429937365 1250 429936115 429936121
    0x3030d0f050709260316050d02061f03120e040f06050f040509100c050f03070201050a0609020304110609040207021f030c02030a0e0d0206040806040b0f060a120209060d0f0302010507080609 83
    0x3080106103c02d141076048901580700d0640717055020b82d410583d0b03901d004122260034018081400d0084801319426166030380c0d5450135006500804900410555000800500c00242c01142c00603014109007490200354603c5d2001900341d807054006200c07500e4031000d04100a080c02e010034144468101c60a2055161032000c3c296580e1a00c403170300d01810740b601000030046000e501100d0344d2003010b10a49030750b0b140c03810029018010541d2101e03e070600e0100300255038181c078400d90b8092548400b07014a0012000200900340d004542000c0d03120b603080000d880181d0310b200e10800e41d08214410003898408640018046800040c00003095400400050414a03880100e891500400329014219440e560000c02c240c1c1c0a0303500301078014401e00083c0b0080c4007040f409075125502c500384a102a95625045c040c1014507071081001210001c0c400b4070052404900d1168000c4000d0701e13420141549844004004555460a50150b5924070921004580c00505194042c0d018ad4510803141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429938615 1250 429937365 429937379
    0x50907051c0312051008060901150b0f070b04020a050301020a02010b0f03010e06010b07061b020c0f01050a0e01050c0a0c0b0d0b030a0803040609062904050a050f01051e03030d0f050709 81
    0x701803c00c40007011542e07880000e40c403000c001d800c9409050b2800880f4824603202224600810801c5064600d11000ca580000c0400c846001c54088a1561205038200489503848928404002e04100e074420030011000c0380300c0d24248090310b0a442c190740041000441c20086c0521420901c0740e95000340d0504c9203408180a0005045044072400120680e60304240e040c44801130007080e003042e440000440c1041310907980003820f152540c00455100226595083c01582c2502c51090914042a0042c0040e0895805500500340800c008410b4071180d080659032001041000c0d0040541280041811418001d440c030510080701c2056004161965840e01c0c2d10902e40030041006001a403a2102a404c10110317401c104850145220080c3c4814485aa8844602413000c101c5000d21b192000040d2000010300956005203031601c0e400c03000741d0030103003401480c00790034010307400c81070161071060784903101080100400c011541d000686418404144415602c1c0604803c040082d82a0141304030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429939865 1250 429938615 429938627
    0x403022b020d03020c06030106090302190e07030906020c0d020726030702150c0609030d0c02070b090f060f0703030b040501080d0e0f0409051203011403061003060f020d050907051c03 80
    0xd50100c400d50303000319192404a152902c0b01c0d01c61500300001000000d10160440310718401e4034400c840f04103443e034040718030564264a40c07141e8401c400650001c01d46142c02603004949042c0a0000589005d81c0d14040614004485440030016408100700b00500400340040c0c0e00005419400703d01d43e60340d140440c2d5900d00490001a00c1207141515507440038500004480041200d00142d520034a00b400740e50ba2030750840c4059031f46071420f10840c800345502c082160810360322041403031401c01d0340507420b0083d0010903203000e80c1c2200c42040381e103072564035a80242c22454884c0d500460a1313080c11040c03006403070303040c1e0010420303502072403440c2001a002144a201103000351021a0030035620b200040242c0074075030000d0014059002c0d05950100380310020750680744038410a0103800018400d26568034002c8601070300b480d42c2d2207018000180d5980148503082004e80c8054101070098030048104e410a50381070745143e100c04010842c0b03051404078010424030482d0700d4410421252005418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429941115 1250 429939865 429939949
    0xb04150e0406090e010603060c020d0914150c030703091205101113030501021206010906051204051e0c04110a140f0c01090807051b0604090f06050411040302 69
    0x6100408048803000d03201c9622020003001078440500c071064103003244600030403150009a13101410440d00340302d0f903400014541c0e40c40c8841c3c1e0724404403600d0403001c058050710342d0960300da00c0f0542c4010b000f1403001600150a40c0c03d101800355964240c2071801402e1200d103680301e62211400030350004e01184012801310559515500082140b207101a410001841036041d2003501c1d842c0410003005000055000c1c000c050510701100007240c031040015520028144240301c002001002188140c0140b82d1010703070414414000c0361951035540c10008504845104065402d81c0b181041510324074050182250b1300e41d054110514088000c01e0013130240801400560006030002566003181000c41c04071503c2d0f01e8050020004140e06203003603e090307407240300281c0c1d25119145c0c0186034040c1901e908081c0c3d03140285824902480c1c6844d2102038600d03003406094850343c032034002a141d01d45010f5482203000c807030246546d56045104010074003c03a55444614102d2000416001504444208070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429942365 1250 429941115 429941117
    0x1d0706141215042d020301050906210d0e100306060503070c0f0614090f030c0303040b0601110708030a020f06060a06140409140105010e04050f1b04030b010b0a090b0415 74
    0x3185588980070100c103544086082d0740c009141404c0364001000140654542e1344800300d07440800700d00c0c41c1c2c0b410700f83d010070b005641d400440100410741c2c503e02601c0b603080d04104d05014134000300d00c165006003000c603190345070004203e134104601c060307180c1811140314035026810104610303424104010840e010082032082407250001c03100081c0800c142c40202c0d200e900c01e405100340ca4140e507455102d00800e803600540e612070010711201d00a004011780700c043d4100d000031411340d51030352250100c00001902c0c86040c0300c08074110082c540d00c240460805071045100459a48024420091402403602080a003640016040c4901943d40000a104683c100c0c80d240c0340c02c603420078181000d4802d03079001d850344626117010039040d070061300d981074102d4400341c13074403120105a6800e11050f500100c806403c0100c1040003d1034401103558181c1e03040d03c80242c0981015201da444004043c4203070810402080045110724429922036040c4e4003600241d0505800c2c41e10300325002c01d1101c00b51034820 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429943615 1250 429942365 429942397
    0x6010807260a02130807151d040b12010e0a0b0604090b040f03030209060414090f07051b0309040e0105011e03020109093602040b06090a0e191d070614 66
    0xd500d000403034069800351041d403460341802c40e6455062a907264036034420680351180890000c05d50601031012308855603d030107542801030442200f000000c24200203540d034010001f403410a07440c1c00074418200c480105200801c41d4807420704080c01240710091203a807145003490203440004118a41031504a41d0006d010b449018451a056010740210b0b44140e400c4000481d00140060340341c02400f081500c140c1340041c00c2d88800b030780100515802c8503203101060003004408820b41141c85000d00101204040d0f0b420003000c1c6001500f9610395101d101d01581d128001401101d2a11581d52a132910a40b15800154a1503002074001e107000e229213103009540c0c620480c80042080b40782e60441c41041d000100003401d002e5aa02c45d002d54040584c0982e1816480c0718450078410100c0388001001055500303010b1806074500c1000d14018082c840c103400c4503510703001e0600b9030301a040c84503101140c103410501c0d40c440380a2400e10b0729032000041040d08940700301040e0650048852400d1450407103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429944865 1250 429943615 429943621
    0xc0204110903061f0807060503070c150609020c3309010b03100c0215060a0909030e060d1b020d0c060e0f0a03020f010b01021c0c0311060a050601080726 67
    0x104aa8000d8151103030b054080e41d0200050882d000c88400164107111000b071081d15229813000d0b40d01c64440c01a6804034208001180606014111114005e4070840e2507e00030048106404d041c0d4000d6130142c00941c2e000b207090100e200c014041c14055000a00303c84020b4012a107113960821503504041d10303655625004104611401c1d04201400c500142c200d610400f003801040c1c00403e40c0004040050280e40458040700081c1c40400cce0140e2001084034201509040d400300080c00358030002c40600c80b00f15001c00090702c5080141c44410b20450f40003404034540009200c1d000d400000720740441d04681c0741643c405801c881e044030402c1d000840000e09044a080f12031400300180c00c044910b01c40c10341d001c801c165000a42d413200004a1000740480d41c0e0000059941f03000310b140d00541c0203280c0c55a00940c506c951421907803e400303481e100c0380b1041c280c50b500341020000e13151107100503290b1041010729600815030750340110491405040c03d07103445030b4544091521007451140d001402d004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429946115 1250 429944865 429944891
    0x8070f030b0f04180503030915011509062601080f06100f030f020f0402070605071103160b071407030302030702010501050904081206011814150301080304120606150c11030d0c0204 79
    0x22140681d480002c40347c0e80d00340121020783d070310f410300d21600348003061000210304403e6410381c0d80a19402c03500c07040c80083c10200260341103a100b842e00c0d0000402464078621908041c0881402441160007410014900c0c070680c1b800d00400408400002d40860b10030443c4039003e1210707908490304000c41c1260800d8910000383c0a102000300180e00500100340403040c441a40c1c0454001c0c1c0041e1a60101350401e0194140c50380580424909104080428400410b9103042a0b65000c0705c03e290800402c8043c0d200030070203401c040c1c000d4001071340c08010066034540910466005d01002c60b0900410300e403550300e00c511480f0b090038042004a840001c1981030b4003861905030100300030000604c500e030f2074031a000922081c00346250b00c1144202680c2844005c0740c0100c9041e5000d41005d18609802c10b0845852407904038021900c1303903980d450005020300040aa0040d40200f0340d1450b40c0140d4504181029080000350580304c2c0d0020000240040d4105041000c0e40742c0c142c5000c00c5031200045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429947365 1250 429946115 429946151
    0x70203070902181206090d0e03120705150f100302010e0f150d0522140c0604090506040b040c022d1006060f020a110f0301150608070f030b0f04 63
    0x12140300802c1c00822012030841d44020424842082903440c01c244500b003c9030907035074100940b01505c094000c0c511010302c0a1081c0000301c070882d00541280d90580d801c9200f0605540049002c0d41c0300e03084130300d02007010071441c06032603049143c0e01002c40c42c6050450a80c04075000f98403009050000040c1010111b48404141001d0b071140242404809260600d00111962100f05031803206441d101c0000c02c1c2c010036501302007140312415007040c0a43c40d15540c0c2d1443c0c048190910020b0b1241103a0500c40390342d4040100040c1500c028040b0319230601d4418002074907500304001c0e200318141005000e0b1b641e0f000500003565098006100500c042e026220078401c4503000b400c55607030050790f44501c000081074000d442214502d42d80c44c0144240c200e002c0b03840d03240c044402040030920000b0451f551034515003c0059501c018000201d0700441e0a200d603405030326910010100c3e02010800554135040905001e00702c00038201405003010280024220303007540400d19205035036400e114030241d103e90f8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429948615 1250 429947365 429947369
    0xf0c011205180f0c0301181109060d06050a0207060c0806150a11100e06100e07030902061b01150f08030301090e16091416020d03050702190311060f060901030807020307 74
    0x407050f1000c0151860700b943d03e60760040c012034040c0d82400000041e580d580201060055001040b12092020000400c145d000c070140500e80c0c0680b0f070540507004240b0358860750340164484880166941c0f05481c144041d41c14440341070301400401d40410100e9200d00d05012040300308503060599aa801130130a480170000800030091034070500d5000300b4030020319840300c1c20594480e012540c50740c0e514001d0b031800c18642d0043c0c445112454011030641c1c1e002ea002100401e01c014880f5003000c6541c5113808403151048085d0049a444001c03e0140c00340074420040540003001a003801c50382040c600c0c5a80e40f1040c0704005881e662118404c003000300602c400c2d0008550b271401e03420880e640c7d80c2d142001c0e101300c0100988070417049011583c2c41c031205209404c55126600645003207031240c00103030f00500f4001c3c4064154040c20000b482ca402d032a01043d000c103031183d240c01480d541404601c610300b00d00200500301040841c41440304c182e940340036a50440b9441402c00e5039800a1f44046800d00d5107907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429949865 1250 429948615 429948661
    0x1050a1d0a1d040606080703080d0f18060b0a080c280503070b1e0a08070503040c03050111210403090b1e18010f17011806050d0b090f0c011205 63
    0x101800141081120300c1c2c000c44c01a0300c2403100a899401d05900d071401c610000300b80301e03400c00000786000d40d06d40042c40801d4500c0c20008200c100d07824103440e400e200d8070049450641e12041510346203000d9203050040e1100310002c000320449500441c2c8000c0d4000020840300d030142f0130740c02c1da0007600740035203000d894050195002036a0b5540322840d1038200e100c003c080c2c1204c0c940c10035080d0a08406070307642c0074450b6403900002e8035441c50564040d44007a00940e04c07001c6606000c1301023082400765100340315256505913039170044100c1c9480c00c87c03249180140844084030030310020950000112080e03c15802071180d543e1004803903000840c0817002410250040421680b0844003003444000c07940100780c81e809140485100d0031115605949402c0e0340601c10140107002030034003203152090001c00301070001a0b11343c8a1001400d214024441191b03141c084d0001c000c903084080c00410a40700780301c002818070981c00070005e0840100c0010500300d0945d00c100041c4c80b000c032121040e01070000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429951115 1250 429949865 429949889
    0x1c0206091009032108070e0102010e0106140a17030405040e1e0601030215120106050307050f040e010f1221030b0d0f140d05040b0c07080d0806030c01050a1d0a 70
    0x550391018020a05910080d5880c2c400d010a019200010300c144c4004c5460980c0ca0540d42d40c0c40d1203007643c00c1110000740074115035032080c171003418010900c288406400034085d040d44422840042000c0752400390084984403e26100b0b910074000000155001d40c0d104440c04504a5014022185082c40401001400980d5414090b46103140072a041d41621700035101e102c160780586c80c0c886403500c11074016196074009080100070080c801c001443c0c10601e1464018948680c401807114540c0084d000b0143c0030b00050010803070007002c0c9042c04000c0c581101c1604e40d01c0305a0f20307809024800518001800d43e10544c9034a49144254010070b240750004224501b404a14200410b50141401e0200c680707880c0d00c550082480c0c0700081004400d0403130780d207461134141011911200c2d900004103561942c4103026004c0b603070800074004d0f510904220b035100085441c00d882058a0908544240d50510a04100d0454015402044444203c588541400006202d40c02051400725a5071060709203c01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429952365 1250 429951115 429951139
    0x30e0607032a0606060c2f0402070c051906230702060309030909060f0a031e08030106120609020301050f091b0d02090f0f060702010c050f010216021e1c020609 70
    0x4407500700c02c2c0715103000782003c000341c9031500d0090303032810385415000d000060340715400714440700349000d02076107000e100211240880e07000303000c24140d80025104461ba000b11460510039402d10045100f244151409810502d42c90103101030002e60281d01c200107c5102190084001e1040310704407600c0b10f5001e00460b0782c81c80e20105150300e079005844800d125011200110300240b4144200b2406440014012210145150b85103081081c100080e158005920300e08d50700030400100255000301280d0322a03001782480118010210f0b40d0300d80100ca462841440140217913190381c080d0001000c010340e20503100f41c442000f11105c081a80710340480c2a5400030f4089000303840c2e50080c020400051744c0d10b804e91007500c0100401111034420441c0c008106000740b070003661294102c0d00780c0070301560941d0b500500c45101c07182a03a010801001c00c65607515080400c5080c8406000041078551410304400c00d40e103000a481000131500341095205501c0d080c4066540e0582144c0344010000c0602803140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429953615 1250 429952365 429952427
    0xc040f030c05090618010902071e03030e21030c0f070b0108011a04061202040c0527091e07050d02090604030b0f09122203050f100e0109030e060703 65
    0x1040700e004881c024075a0401140703590424000c2041c411402e107103200c1450703007002010402500280802c1d9401018032014a60b120554101641224001e6030042011500e2071030b440c0c50401c519005024542054540300e00f122490340640f600b0029003032106a503804101100e0141e0f000b000700c054041d40540c000004c1c00311055210400d69866040d40e000e0b140f0403241088225000303441440c0300c0000c0400d0040c018602035100703e40980840c24040d04001208001440d04d429020440016282c0d42c2030a520914000c0d8080744d020780d002c0c1355403210b40e5400710320250140c002340c100014081c0200d41c2c81520303a010340559000300c40c060895521565030342060122484280c4840740c40d4005400424038032040840c014408001449a0324904084004e01c0072034802900309c0d004c0400e07000c640c0800055000d0003a405003000541c0144a000b0304c1d007501000b200c600807056a2180e00d090303999800a5006080e07191013038004c444a684468031810203440502c0c4218042d40141d030110f070461055 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429954865 1250 429953615 429953633
    0x80a020705040605010f020307060b01050408030705010e0c09090c0112020421060b0f100507060b060c030712110a0204050a1812030501090213030f060e030c0705120d050f030c040f03 80
    0x19a0708840070703c2a01d5483c0015120308504011000041c5c00030400310011a80307a401040d03001e0010714003d407800313980e10107d40c2140c1215200329280d0351168100c3c5403140c2c3c10008822000b100700c2c1c1c5031050342001e021040e03459140d203403c3c0d03051015082880340e400c08180d056130000d01070b5440032200006040c00059190821a808031055071034040142803d00b05000e050994000c09068a26a083c52110555490f00710900031a002d9447c0c07021811075485401c043c22841384d20000031030f1980540e20303050040005820000c1d003080050010001d0704d0700005003442c2c1154060320001490345034000a0300c0031f4111100075074054441d101080c820080c80759142d00713404003d41d0f0700300702a9803151070380030a0f0710038100b500c912416010828004111444903034211944548000a091070554001c42d0943d0462040d0b0b180a4004040c20050707401d004c03044805000d081c0007c5c0074449a42e02020741030340541c02c084c0030922400300005a800e09054100c41c01342920807a0b110304a40c2e685016100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429956115 1250 429954865 429954869
    0x5011a090108060f1c020a0b250c1a0711040e03031303020c040c0203090a0b0a05070201110a0b100f050603040f0822090204060306051c110109050409050d0905010809070e0403050403080a0207 84
    0x505c1d1b000d13070000c0c1c0700194100703489060300007403a503000100e08103004220080b1591024ac68040c1500000110760240e80c0c0380d80080340700760b01034944520b1182002c028103411040458000c0b814050500e0303001a02000b141e5010a6001d100700e803039011814100d1070003090850045e045450110038102458000025011a01c011501102360548801c14017609004694441d13001c110700303201d03030750056000c0c280744907003880c4440803900e049540f501c403a9183e1200340c8108400101000d002c2c801d0300c0c1c080d48044042c1100765009403540c00c0c25a07640280d0785d0a210050180070021409419007174801c40000720740455102c401004640703900000b0004c2d0302c1441203001183c0b4000c00043e0a00700799070080ca0f0400c4c1944041c000e000181c03901e603d49602c61100c241044101440440e40b41c0c0c8a210300340d4041d018500802d40030a80e000080e21442c0700e50041818002210100b10a003400028608161000600b6828498075940340c1030340c1501035900028190000411212801c5500048170b0003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429957365 1250 429956115 429956119
    0x8010f05010e0c07030c0b130618110d020108130c05060d0b040501150f030c0306090f1506140403060207050a06020714060606040528151205011a090108060f1c02 71
    0x1042e11801032026a91081c4c12000f00400d2003800d40c00301040c16900e02c0340d0300c080807101f00d0f0180341a41d9a0401202c1d114074046001038442c25010080c000007150000c81c074041a6900741c03850040340c001a00074480104110055104503041c4010450302c03d243d00300a210140480d0745611544150f1030161202d1640c0341e01807807500c000040c44c0c030868129001d4050160b261001454540d003411009803180e04070030b0052644813040054207512910462102c6192201c0001d01500000b0b54090b80f25415440102048034041d0551290080742e4215400c89610640059460b1080d2078400d0500300d8500004c8c222510116042c0107000c1d014520840321000d410680d580c0703555690411155009501a09801c541d040c086180c00420300c5e605004655100348000d038080b542c490105404050150001c400642d07000040c0d24400316034012140540003907140420130790402c0c07040a0060040507031040c100942000810441d444400d0344a2041c2d801800304824110000d450b4107020710100c208074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429958615 1250 429957365 429957389
    0x2030109030801030b0a020f09040b010e0a08151b0a1b0b250201140c0a030b0306130b100302030c04020f12091e0619050c130305210a0804020108070908010f0501 71
    0x940381b10824400c40346035000141c46103050034039010920008200d450b22260600080c500c50a5595560040c5075001303084580040040e0b0000e520781c201c000c440a003120068040d2118180f184966200550b85054072134504114000b180508400486149990140a42c2105014000d0b00c0d503800d00c070100c480d040a40b81d4140e68640150480c201c0310161980071440110002261142515400924100d035807880c01092200750003000a06100c004e0380c58002a4102142c1402082944041c1c140d020101c0140300041500d107801113a240c4910391004e80c8941c2d0300064160580c50080151116644044041065440d0100b03400c0e5580985072181e110323907041300c00340400d160400100c0510400000e006005008600300358440030f418090020071500c50309102ca100c2d4075502d41c8000c1c1c010341c0184001c1075a8802418080130081313129042c003001d248204812022550480081340d0416420302e81040c060380c0e04601150320480517086802c681d403c003080140500810782085041c0d5000345419 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429959865 1250 429958615 429958621
    0xb040c080609150f090f1f181104080613050708030f040b0f190c1a04080a0f03180602090a050109080a120e10021b04020f0d0506030a02030109030801030b 68
    0xd561854044035015481002440042c903040e98098164101c3c0d040a0310040a40404d0000903030354040840d072a1001094180c10416401d1401c141200703c0701921118025050801c413404001c001640c100d42030280c2c07560304400036650150200c42c010003660042e60003509001191b201404103025064440b4869076401142101c004011a400c01040c17050842c0761515090000e182034000707a151040c2d040050215500c1c0c91202015484614800e9583c0c00d03801d10145042e8114081549900040d00000c4013000006501c4000300d60640b030041c01c1c1002041e103001c40c2100070300341c002c802c000e902592100003803c01c100c40e0041c0100c1d05085440b050840c0d200c200454140805210345541d960264031000301162501225140300d1066252400150307004101113a903590302c901255005900007542d030f0001c0902e2542c0082c20707003402c607019480c0a411640130441c0c0d00412460341c1aa941d64404548541d0f4100007410509902400034446081d1354140509504800d21058459030b04902c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429961115 1250 429959865 429959867
    0xf12020d02010f020406050a11010e0a03050c07120b221415090309010e191d060102010c02010e100c0c14010209090a09030503040305070620090f01181a120a0b040c 72
    0x20b440541e8551f03a221406c0c00134003202200c0e411580050014213540c2d40e074108030041024400544003034001d0322500da030354251032640f620301800d0354800140c903c0319081c3c0000040b984401250000781c00000701204802001440d0000e0154110061485003044050f040741300010a201020303c1103205031044554482c0c0e2015200d10540c0c0d403040c006007483e1000d90452900c191f030401e01c8450403031401095034480c00d0300a0341074202402c8800350800b1104020407036a09014480107884544000d001000700d807070b0416580c4445114500034940c8074250b50301380740d204010550890750401c13540c01014135a034040f14000c0d803000039164040d01c0240001a843c4505009406175941e1503aa4a445c582d1203840440e003e40000300110b403026201c00343d03850340c88441559003540c40c000341500b641c0c4103440030400141e010003241180c14000f50341280100c044000e5005400c80c0e030602c1075125003a0204c07042861502c900311112500030144001d200390b100c1164071603405080184c40400000c1e218840c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429962365 1250 429961115 429961117
    0x3060509040c0911040909050a110102011e05090f01020d020c0106061107090b150703021c210507110d110709050405100903031b1215060f05070f12020d02010f02 71
    0x81d0191614504400800280940ba4400b072600b00101c00180e04141d00c492401081d030311390b000181d0729548800e1480d0207106900404c12a161001d00081000c4029200704000c00c0038901070300300c5a0356440c0001403000d00c003403080d100d081300ca48008650f20392031040c4c410020341000c0b200d003401e9072034070702c0220700341d400340c001e80081181c0344004007d11490304501d01d016003062690150403214a50703e203001c0301c2208015240c0e0501c2600039042001004182850942c444155502044603410b560540c20800c00ca09011400c0c400b440440ca80c1d41c2c40703030f00740c510f9080150b400455100c1d805860144503031040440706182620002e60b40300726a40d80d8580c05075141618040d2454011501d80300040c10342d45e21078030450b480390074089000003420410340c0d070310340d461a008800706a01d501030140002031845070b00c1c0c0948140a100601c0c0703003801d00090040c51070070440c00502c603000641105100c4480a640403080d4043c0c050501d0500a51000391183e0005c9070441c050345c2403180c944155244c0340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429963615 1250 429962365 429962371
    0x6021312030804081602060f0a14040f031104062112022a0a032a080106080d05070602120c1207020105011a16051b1e030601180e150703060509 63
    0x20341e40408a8070f0710f4481c0070280d0320940100d4000b180030f482080040c0c0f03aa5003c0c1c448100203e40c02d0791603244801e005400c52081024000190340d0400c0140000040040c0300011380703420018031800e5100d0040850000d007410b802c401c4900e0001c0040000701d1480d6040300480c0c0c5e10034004065220082c99051b40c0e40c8100c0c480290312004401505115a1148552001168401000004800d58a46515074807444402000d031100c609484005442a00d0303c00c14001890060700030400f042c5080d2001e511090306a409031704205000450000740400c94050350600c02980003044840d05004c0240c4a6a5100c0314513107000101040000f11141d0040c13003000c0c100e40c41441ca41c0380509582468012644c0400904090354038030360980400b107001001150311101c0c5103103006030340c0703505502002100c25400d6541c0c401070380644021085034802044460440d108900c01d510803041c2c8841403030241c0500c9140c6000c51040c403005d58451441d240103d03000c3c1456882c00c011180e10b0b00c0910900b1b40d404c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429964865 1250 429963615 429963617
    0xc0f050a080606030c07060f0506040e160e0c1e120a022701050c0105010905090c0306100506070206040308160b060f2206150f09170a140f01090602131203 68
    0x400300003200c81c100040103642c4650017042c0586820b50666410017141e8201e1510080b16a40c0c40c10000a401c081c420140c425441070f000b0300340c0f801141c1320101c1d02c46070b5008044e03021080002142070b20410300300f86c0d40d05040b00881200b00f405e200301c440c80d543c1c11042010b00600d1001d004115010b0b15407080315451a84070b8150b82d40c82903100c0016424980d207016050402a00b00a01100385100380304040c080d21501101046504210817031907c0c000021088038403c6e0043c07814410b6100c010002901150404c1c0c03035480d00e9000307600018500340100e034400b500071940010340703194810030b031030328510f005104510031191625000148070120721290ba000d80c00c6038501600312550714094591010809403e800850829202c008411308110120101000700d040d0440404550740c001e8011790141203d01c0082c03410220425582d691500c424001800d10790740314001007070402c0e0a00c1500002c0340510b0090020fa4180d103031802c029400007040151159000b0300101d1500c03c4444110481a05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429966115 1250 429964865 429964877
    0x70f09080a020103090221070e0a020c0a1704150e01020f030c030f03130507180b04020a08130609080415030b03062e0e010605120a0c020706030905010e030d0c0f050a 73
    0x7990040d401400881426a405070101e00309440040ca000107a107112402d00024141640c40c0c4481c403480a400a40442007840c01405504565440020355046440d0002501f5001074140c125040c00c901c0345401010110308001e65000c190781c4c001c031011301d12441c03cac6c1c2190800e001165034107403640585545c1001d250010410717240380f080040c0156401c4070b0304952180600c400d1f50784e400d251524592040354400d80c0400140d00c68040d911402000e6401a5001d61a044820400512400700140200d03c46000c4110000c1802500ea10030529141d1049485942d543c968001c403141800103030300200004c1c2488051211418007240050060002072400003050381e100f648030320f41510b000010300d184c40340c140000404c0c9132042d503201d00802c030645420342d4072078041103080005070000340909251418a500d40382c0d143d80c00251441100c9091070001032681e41442c1c41409464440324201c1540300214495008916607030151214000c10b032146004000b00ea1070990321030041482090200704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429967365 1250 429966115 429966133
    0x90304090e070f0801060f090605030a1212051512070e0601050703170a09060b06090f0906010e1f0f17010b16060212010905010b04080c0f0117010806070f0908 70
    0x1466000310100800c03032001d80b010503481c3c03816202d4500841c3e11280b0180c0d1601c204005020722502180043d010b40d41e41840802d0800012a03560900c21200612001c184001e00441c0340c801c00d5035130392081c0100320a0000741807400c400000c1e15482a0303407910070035a0304890802c040d0b0000b811022920342d04060302881d6280d000559558200401c00da00b48104000b0315001c0c100d081c143c0c1c6200e003150307400c00580c2d100c0d103050010441e000c4981322800b13101c0030800c4d1204d60380c1e0b140390000b00240480c0c03540000d54480380104c5072111416101e07500306401800441d03c07000308030035011840845542c0c0c4054540c07200320868004448000004104043e400107000e030b00015402000108403510034100007039190f40c0d0300800c0b0f92085020031003d0403004010300007008907010305401407a1031070280d42050304100200380c80d4090145500c0c4140480c099000059000b500700f0101c0c860401c520b040d49681d9036560b152184411641c007070020340f8415098103c1401541c40c0c10540e00c5e10801411805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429968615 1250 429967365 429967379
    0x212190b04030905060310150e01080f0a0b04110c010e070e01030f0c03140a1b0602030901030504050f0703031101180b0a4b020a0c0803100e0c03010501080f090304 72
    0x10310003400c2501006510800402c0c0e035181c00001794002d0f04901c8404940510300682c4a201500d00d801c00410003442040f0a00c050b03a0112000e41c210490b1400d442007512034200e408000c0005038041c0e5041070610200e65080d0305040e000e0582134407480c00910842c0550810b4035218078280c010300d8400852000140b01042c0c01e0641e45411501c01c2c0303408103100d40c9a440303180c00d5449080800c500c8c0ea0000c40304008100c0c0c50041c000c411210420600101800d004010351240030354000301e4101640c1c0c10005051020400c80482940d0f41d0384c068401c001d8403400e0040c1488008200058658240f807030301001c0d0346021040510f900c0d00a00c0c00c903070076180ca020040140c0132141d801c00500030203401c540c013002e00044240344640c0c032056400c00c142d1110812261035611019103003c10a1040c002d8668580d000a4810f083c1036003c030082c0d6895441c1c0c102c400021505070880c0c0c129042920801c0b00710903a120013141a158240c82d48846983c50402c42c8042c1c00741101c401c00281c0061004100c4c139 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429969865 1250 429968615 429968633
    0x1e0a17030402221103101707060210020705100f020406110604030f030519050c0307110102090a0b0702010c1e060e210a03180506041e0807081602040216021219 70
    0x6218048000328408806110b00c0c0d0080d0026501e4041400029100f0072000a11f1440f20384422055005000c0c040e10b0000040e4131031204089440d0200e400007861002c20106100c0141b40b900100010880aa002c1420708020f410a0141401080352080084001c00c40040e00b507100b654140da601026000d120310841c003801d40608042c000321050b100300700c01030101e1301a65101e08800e034000c03a1607242450b002040c040c02c0340416440c5900c10455887c0710780721001c441c01510480521595180700b41d200480d9089101c1b0000f512040301c07041a84c03880f0320f032403480c85420f074051141480104070417081c09403141c0b20b641c3d028142011618084103440039240140244038264200000c682080007002d031911482c0341c7e0100c91580001c1304000400c26000011845600c05440c0801000d100d940c0c1d5543c0c51241c9080a07215800c0030480c50039078820300c0d402d940040e6000d4425502c0c4d0710900004002800303000d00072031003044d0204a442010b040000c0b606490616107816007140c481b580c440c0c49017 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429971115 1250 429969865 429969919
    0x30d06060903201807080619030f0b0603120a081e06030c0f121e15090601120c18021305030c0a0504090c081f0b090106050f0c1e0a17030402 62
    0x14a01040481d9066104c0641610610464503215039615000042007050508603180c40d5240c200040b060000c6040070142000d01944039926001035142d000019141112128004200050008908808a6002d201030f40201030030701d0040c1ca80c000310400ac0441c00021510a038240c0d021342c0c111566850030403554920700b0300240c08801d145061010580c1812070640d0918030104034400080c8030701800f001001104601c4000420103818007207400c5803070f030300184955040c41c052000c0b0102440f120300981c400600d00080740d1b04841180781104406904a00422a00c4003c01c070000900d03410085141d0100740802070000d41c041c4d040c1420403000382400301c0b0540d442d0340c082c500416440400c1081412200300400100100d40b4200000c0c0240c4410b200a41c0c010304c528401003084540060070b0f240e460103100041c50b02c802c4800c402900e0904242100b41c2e014003030360b401c10001030b0081045841c00307014424042400c444289195110310003503074000e4021590200c4400b88034040d07004501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429972365 1250 429971115 429971119
    0x30f0a0807090f06031a03071a0304030203041d1f06020606060708090303030c07050610050f04090501090507061809020c03070231060501080601030b0d030e0a0302090108030d0606090320 82
    0x2149522090340d5454120b440d088040846d40e01c01d09600c018a55140300500d1640c101c0c0101380c018240421194030366510403082c9041c0c10044003080c02c05000b03005440140ca584003415601003c070101d400700070001502c03141c034039803250301d04184441c2c5040503400075140180c0042507943c490380d003403003045c0e404101c054421035420310824200340e409100035409850900c000035154141f40c102039041200c00342025034140e40242c01000584c80340016000c4240d41201c1c0050903010703a081540c050000e05000406034004c1c200007143d01500515142c00c004055103c0030350040e191010f00c0103c1c81950403400f802d134410f118110051a1156440062104500151500c04205803099080c00d4290320502c8507117884031000c7c0069640b20200c0e6602036000d18060160b0001c3c10007241c103180415030098100440c82030f40c0c05250302c425034040c00550740585003443e15030f921110284c4036044280310001160038260006081c40c8101122025079802c84590102d8900382541c03800782103403100040ccc1d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429973615 1250 429972365 429972377
    0x28091503111b1507021002090a0302031f060f12062307050c01140720010b1c0605060108060307060503150607031106010e010b0d0207060e0a0c030506010602030f0a0807 74
    0x1c500c024080504806402440b08001000c914410315040c12070540a007041041c101080018542d4002202c03c9080c44542c00143d941c001480400c24081c1c641e003020390907203d00340b210007a0200b40c242c02610f44148000400020362a26095402400140f140d102800d0503283c107000030a0140e27001c8025410042038103941222890f02403010303400200d414030082100483d0583c4114402e01907210300d00340c83c1240a503540340c090006003001c28221004500c03404074101c51085000254800c02f240c01000340010300c1c05000c100d2000200c190000704851040c10440462019402050700c03d0240c0c00c0200a404407500700101180c040d00000c090341501c540520b001d04454071840e00600c0240c0c001c3d42e4080340d40304290f00300c500d0f01c00c060340207a203c040642c3c01081150380f40c900f41d55010412074400360ba43c042c0c50600801900500c0c00403a01805241c00b40700c20800082103040441e40b01ea410f4034080e0713a8440041c0e0700c1c1d004409084500103000c21514074003610641c04140d010340582042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429974865 1250 429973615 429973631
    0x7020d051305040c0908060108160605090117270705030d0503041106030106030207061404080a0f02010f141006030b0a15110d020102090102071403070e0c190528091503 74
    0x103402c0e113034410030361000b10b0303480002800158003e110050242c0141c2000380070800c9001156082041e4603c51001040004602244030b030303100e40306140c907104088c2c1300c02005091401c80d2007483c80b06508800c040c01001818400d0034040400d0384008c540005014220070750080c601615980c0c0024000c030b071901c10983c1c00400f141e81d0103020f18040d01d05170b0750041c5c0321119860b14000b00c50350101e0f0b101403c40f0060400c000076030003800303e40f520312091820401400741d001d008d902420405041042c4103081803000074240c180c070101350303120384240c0c400030640e199075400c03e074210b0303040802403504141c01580902c10800c840000411071011854021221810246840d040120643d18080181d40005015010350303810007500300a0242403410f881405203c20000e903803a503030f5104031b41c80302c2d0500c40010380203843d410544604801c541c020b042c00c0d00501c40000c4c42540112050400090404007808900c2c194001081c0a484103840d91504241041070581c101046200c008041540360446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429976115 1250 429974865 429974869
    0x50606040f0e041208040209011a091f0e1e09070512070f110d2001021b0d09120f020103050a1104081c030504051c050d06060e040e010507020d051305 66
    0x80724000b448a40072500c041e00b41480c003c10500f400000c00760401c5004802c0c480580d07956188141128120104890307109030718a074804283c06500c81d4607900c1001440d1003d000782d00303000460710501304ca544251103002d0010030440002c50014540603104981c4081c1c209a0030b140440035004403003420f0950408d018003014000c1c0050445103540010414664941c480341c0240200585e4590301000e407004868040d0010200315581e230407002c10700c0000e075020032854820341c100e480182d03100d40c400c031405040455965656451340070b4000096030036500042d0981d01c2442c0b0404640c0c1c800022100c0c00200e400440c06054060103d458980c3c2e0b030f844070352240c846100203100401c1e4210140196200304a010640c0407458800201890304000030000040c8010521111454008a03c2e044000303400008460728000d41090090a0b8a8000d0106a01e6040023030761900b070000b150144507400c03400901034265042620742c040945e100c4025105210300800285c03106d1284004010182955500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429977365 1250 429976115 429976139
    0x30b0a030311010c020601050310090c030c06020303070e03030a0c020409060f0608010c080903090306061c0203031309200405010e06090603040b0115030e0601142e02070504060e01030605060604 85
    0x100c01c0700032900e0805a40c03500c010a01546820301100d002074007140d03241002080d200c080d6a800d6040721641d4403000341c00c100c40449003201564100f03082c1c2607001c0d00c4040c040e40d01d0384240c5a50001c140340c443c0c0d08a8501c2c00000700c61051805036640307104a030359542400060140c02a048031080c0c0c40c0c15551210400714880c0c03030010040000086003082211002070a40344000d800b10400c0d42080000c1c420744c0d100001c0050700410103950030091000701c031640c5485580c10000095050000103854012220342c0780101094a008880401521082c8090482d6504401c400800e40c0c91050108110540c05110315014a02d03001d4602031502d80340e00000b414a07031040701c0446180c01c4400041c48610b094a655003103e081d030382810804868656025a5118014490f55004092840c44060b103915020794044030700003400c1160003118160b403810f0288488072307a40f003401071140580001d03203480c0ca0b01500c000c8424004450000e42d0944d280c00c005070000031711042e0000020440080c40c050015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429978615 1250 429977365 429977369
    0xa1208040620011e150f0506090a0905090a0c21120908190c1e050402090d08071410150902090406030804080304050405010b0901210f0e060609070f02070312030b0a 72
    0x40342a1440308491004030f0105c0b0030b104400008144c200e041408065030901107103081d29400c441054480e03084400140300f42407250410180f0390f080074140800c0d07020018807000b00700c0c0315040d5070034425214800c40600c1010011084d0400e19a042e20030017103440a0311a0307060380d5040c50b1030b220081d1070b200079500d0b143c140d81d0302030710b40003c40191809208501c0b054a025001e036002c0d0002a00035100102803980060041500c1145d0000e2940415901c0c180840c00f40b60f03000b42825240c54141c01c04024940c1020202c030414000d0782c1407204440102d00c500303900e01d020140d0211880f030800755110025005800a143c00694801c004008907022030040d0004040160055950324280b030280b01c107503801a840300110400a01005007103a82140c03000241c1045c980b0000d40a421550054020b402c0b0075001e40c0c00d80d440e06688500c408004643d0510a160650700e1400585442d0300c1101e002440801ea900141c0003c4006d000040e90710740468000d04844c0350109000e9110800a00e21003029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429979865 1250 429978615 429978641
    0x203012d0e060c1207051308060402040f0e2d0303010e01090c09030804030206070320010605030c0f010e090a140a0c02010f090c12060603140307020a120804062001 72
    0x4088040103014002a6000c00c40103410b060401000c040010700030001003101c0c50000c140022403c1307100b0002d40700e40000044080f981103994100c05611a201954142d01460401862850402c40750040701002c5034114001c0011440368022035003101c0a2103805400000c3c40c16240032512401c00c041d6000e04011000c3d00429490070740b000d01200c0c8218035020034441b0441d000c1000c104101d00b83e0b42280e4040d01d416075104501c3c5801c440d04008100075490000101200b00350030380d41540a002034078010fa0485410586150800c058414010301c903d00081011103008102c0c140340e400282c00c030700502c201040b408450f07040202400001c458100b0002d550f902800303150766090280c810710020f49102000285c09540700c140d050b5405010f10b40030303051404a00b43c00c120309a400368009503007140b80d4a880e00602d03003030796440358000c4009911902c000040801c44101c4424925889544404500d240a240020035158400030480507030040980c0c02c0c11110390b890070301880c4135400320 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429981115 1250 429979865 429979931
    0xa0e0c090a0e010501020601090b011e050406020c0904050337020c0109170607030b030304090f02070b010f080d0309030507211103160204091103030a090302030d1407020409020301 79
    0x3005041c49001c440940c0111107141d40100104000e980106603203042d01c4982c00041a15420f50b0b0044e620440c59041000d251141039025203c07499000d00540151a519402d0381d400c1c1c1c01040c2049800a026540940150820000c1881042400d0340c02c2c80c00064209122070a803511b203d0489010501d50503a03409a044541100c5181d03900280d40ca0181400c03c1a84a501d080c4a0009580e07140090501090550741c0300948034075a01007042d9001024010411f1010041020703151004e0b40144004440c0180804008105502422503010950702c1c0700c2d0081c02440c440d294100d01902d864a07040c3c050010820600f00403588008003c0304961200f040c524a4200c0d0400007002504010810301d240e030400c0c880da00000241c00e5018143c0f6404603804142c0c0c800c41e040c07421040000c9074801d0741c14840000c5081000d5040198070088034000c80648440402000040d90456220054000c407540200310040041c0b805500081c220381c006800003c03441310404480b048009440301031014404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429982365 1250 429981115 429981127
    0x90a020d0507210f0b0c2208010e0c03030a120605121c0509310203070c03021005010608011e05041d0606040b220209030304031203140105011d0a0e0c 66
    0xa03c03d540b10308001c1e070304040040300c030a4442c2410f0141c1072138010308003003040010804546000058425500c01c1c04101e0000b460120400010504184a80c41c482e5080c1691100349120100b156540c02e000500a50f1030205206400c840300503007202441021551080040303680d403544007110040005103070040207030310007409140c03020312562000700c0d013000b604004001d05030301c07000d13904009920f407800da51110320020b144a1032009006410302041038030100c200040c0b2031f40302c82d80c00c110a00940a850b030807101103c000c4240c0d2424020390740440c118034010440c41c080780c60440d0b00340752000440030b0001d44503400141580c2c0506441002080641c0b0324212100d130a01015800040c202e50030044801400702181c940c405580b01080a1f00051003105103524a40e0100d4403c11801004c0c0d81e40daa4517450b06501c0340450303140c00300003e840c0061500074030400e600481e0589105031a0002c0b0b10f0107458901e08801900301007181c10102c5084000391146113521803d0040098100d101e45841e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429983615 1250 429982365 429982379
    0x180c0e06090c090d03050c062d0906010e04050c0306160314090a0602090a030b010f09140912091c080702090c0a0e0105090d050d0305090c0a050117090a020d0507 71
    0x1140640624030401e03540080c004000001011681d50903003da5564070b0b00d4501d400c00b51954000c4850745402402030808108504c0091405102c00545113004911030194115140180140c1201e07051941d622900060021103143c20480f644584998219148600000d0200e400d0881c1524103d0a0107078403003020800b0b94050242001c00c00300044e0b86c5200c3e103401c2044a41e1818207101c05040c041d40051103122a031280084032000c6c41d008140b02c01e40d0359540e074010307590051500c00c1d00c0245203007850001c40c10524284040c01031a04030000e14208400b1040551280d2102d03c503a0703808010100e0000c894404401c001c000c0a004581080e25203142d801800322111000380000300301c01040046050b441e80049240612400a10300b480e1034003086401b0586882c11807030050000c2c804d902024000960640169210b1205071040d01c241e01e12507001e000441d5594064280860201c0ca11410100030a40c0d11036030004505007115003204064010a42c00000d0b03103000d840302e80200000348849 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429984865 1250 429983615 429983639
    0x6190206070203090607020d1e080304020112020301081f0e150402030f01021914091c05160617221a090303071d0a15020a0b01080c09160201180c 64
    0x201001d0300296107807100d030000141d0b072071268000003885906003100010500482051410301a1014001c1004040c414181000690030841e004c900292400b0301d46040c120310b60007a01e04071441da800410310310121418080e0607041440f0202d03441070340d80e022000019420130201d00742004020304500e07542414014541806a1407000080d540c2c01000716001030111001c0c410340e03400c3c00e8517142c80801510740e500c0c9128030880c814580c0c000810300c0100c014904076500245218070030303000c58209402040d0981d400308114030861010407650000c8040e1400c100c00c44942c020003a440052091501c2400072801d80564002500e000c0f40c1480c90380ca102c60705000d155000740582c0021401d520f0030240c000c2059002c124043e202c0104520022100e8448040507406485003c00c82e03e030003010000000d641da0904101551011204d100005010f40c0104044240d424080c2807800156580000354038541e03d941b07030840c1150f45e582d0700014101d0038071800c0c00845100c0c0003800849443c1c2000000c030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429986115 1250 429984865 429984871
    0x2033405030706082202030a0605010617070e01050703110109050705130b090103060902030c040603080c010612020907110f0610060f0206070c14070b03040c09200403021e06190206 79
    0x2903110207403d0052981084e040d81d44005074030f01d080ba142d45500003d485200f104200250944504c01001042040a070482070503030f07203665284416610010038408094100b6510540810880303520310701594842c000a0070f4a901a080a0444561808030142158140b410503950303a000580c080c0900d203444402d00c00c0c0600351000c144442c2d000b090000760640010b10004207000d0381e6089440454806010001005800900401c456681e07030611541d281c0c080114617520354a131181c08250032003901490701c07009801805036065503503900030a4505000091141c4c00612031603083d050715803030030017500c0c0c07040891203000111145080710142081b01003100010540d08181d0422645039402060340012a0300404400c42031500c05100d1070070f01406400a51601200000700028044074880d03010884960410802084150102c0d90601d02c504101031060054200000c101515041d0100002c800e10074140043d6200300400080c0c1c56400082d00c020384440c000540000c0e1070301800a194 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429987365 1250 429986115 429986119
    0x30902120706112e061706040303060611190c0f0308090a0905010608070c0606050d030309051207080417150430120213080d020a0b060a0315020702033405 68
    0x40c6852040b4810130b000303030616448150455103031540c40c0b400201c64205c0002807803c14a1021144450020507403501e03000c5905401013400c00d00c000911612480c04800301601960140c1b440006404c084801c041c002c00c02a1798098000002045a4019a403d03400952183c078070b40d59030740305c254103100300c000003a4000c2c1003d510b032900400c1443c0d0425402d55015040d46007072444030002d86004802801c3e10f41003e6003080681d041c1c00c080603055406482c40760b000710100c3d440f002d40b41b50000818031880344000d000840600c0200189502c40751032812403846030003603540d450100c92400e014004111340944040c41c4035245540d03600d0040c3c0080f894074408029094400f4a10a40907014071040c01420940d03d0b40043c0d045000c1c0c4d0201890000b0b0701d201c5041d100180c400b070000035078400700704034191010403c60300800d150f0310f006429032084a512040b5240c01c01c98003075244009402c49001a43c040c001c1e010061080400302006c14845038500c54001341a110420202c840c0b469280c02441c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429988615 1250 429987365 429987373
    0xc040e010f0f030b061305280606020c060705010603172206080606090103110d050403090b0316030207152408240705070501050a0621120f03090212070611 68
    0x101a10b51007800b5001504d4000b0311074103503a12041c0109820f1843d0320141c00c0c145140109204001c0c0440120380c000b940f2883c1403081111076806440c0c100c901c14403030070000d03a03c10789880549003002c0303014001c02401013000040c2c8075601d8a030341e40080e003a182a140150790008400e45105240301d006000e00e070303444601e54002c41c104007001e0201b841c040c1c01079200c2c81d00803440100c0350380301e078015450710310305000d2844d10b6040540c030702c0001c1e1005441c100c02180d4501c0700410691000b400fa00c1c820b107261085e00c903260840ba88298001d40c8040f6059030301481209a5000001344da000340201c2c058001040022801c0c0070703154000d104482c0c0c000c10345a4100e040740421080703a604845118000e075950f1211991120103007510301c0e12811100078841e508003001c12848c02c103280e0029046498070040c00446200601c0340009040080600801e0782d2001d82c0a00a030034441c1e400c0b074511080d241000100c0e002d094000841600d040002c00000d94868501481010751004207481c014140700010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429989865 1250 429988615 429988619
    0x20303010f060819050a0f0e060a18080409050c091906180303170601020a0209130b10080a170904060e062e2601030f0b0117031606090503030c040e010f 67
    0x13a00c4c950b2800740f41c400c407107850b040450848000355001140c192038154081004400c04a412522030b5800c9403000c0c0581d10301585903580c021880f10b000b00e11580405d2240c9441e0820000700001c002c0038001c04d1282c2c00074049007825071210411110b04e01c20354a4001009440e0040090903800c00d23005984103c0d101e030b40c01300006a04104601c80b45844030480180c0360740c40d000100c0c44e14201c41c0c0065030004048082c064a6150440d4070700355980601d500c03000582d07500040c52608801803180d900551300003546140421070340da484103c0304c02201085031800d480c400c0080c050b1900c0307402c658000880d24041c4a903a141c940303048640000311400001052070851003600c03401082c4801002888003000e418be11015012030b0804910702d81030103403002544c5074100500354029030801281c40390340384800410350092034a0104e080122040c002c510705030301206c00800340440c420085503030340c5d100c0c9001c000048083c800340d44100c100038445a282d81c54000c2c0126008bc06034008d204004c907403801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429991115 1250 429989865 429989881
    0x4171608010c051b030f0406090305011103040f02011115070215100503150a0603020406030609031d090106030e1509060906070f0509210106030b01050102010b04050105030717070b0a020303010f0608 87
    0x40d9101e50040403d0b141c0000113908400d801c500ca0b180c0c0c3c0198465000a004c145c15400075042d8050300c0c02003008015071202400e0350030061000740ea000d450090000e580780e0040d8401c0b49200f03803444034001070b298000d02101e6042c3d401c0900b50740301c1d00940c1204034054110452805e0a035842011030801c04031862030440481d071548100c1c02500d1882007400000b0f084000c0a410803401503502400c01c1100e11b640b400e010005004403442140080ca941405e07818040b804078041110400c018003110041e4640391081d0000d0a02060100381360091001c01980c40501d45d200c1881078098001030a100e02d803110525080c624002c009206101a5559a8280c581d000054a040013015510a00c03c00035a400d0301d032002c6000c850951003523003043e10120800c092758507142c2c1242c00a800070301002c080300c4200020f0755024050310750540e0042c00700300074079220940106448448d0000756807030203481d0340504100da032200d5013001c090b0380004010081c481c0e4000724800141b001c1e01c0c0c401c0b0181040d42ca = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429992365 1250 429991115 429991117
    0x14010b0f0d0c050105030c0c0a0602070b01120b0604021305031c2303040b060d02040903020c091803030a05250201050610050703050306040c140a020601031e0203060a0903020304171608010c05 84
    0x10f00e410410048001410034103420100e42c150005c52080b52000a0146040000380d03010890850b411f40070301c0c00004002e00341c0c90507607030f02903408105020140d807a482400f0080d04411030407864010403040005050300c0c1032000851224940d110700001c04035040010b44000001ca20000340301e070076044a81a40920351080c0e035000303035225050724160f88440000400c0358541e0303080650700a14140b8000d00b01a000a201c6035950815503c0704a65900c41d040154460b80d02421200f56400400000f5048000e0b9071066038040d0b030b044507081030010f2101030f124a400b815010680980c2d9624140000c600d8008543c1d80c100b00c040c030300146003040c2550010071303600000d0001801070352105048203a0301e01400d00881c0741840c500302a62105184240255282130078401580d034071402c003c14050340048600740c200c0c1c0c16000b6008107070340c0e01e43c40b010000515404001b501140428400418a49120304c06081c09080c0200205070001e0098503085048040742c2c005030541e8904002c000505400c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429993615 1250 429992365 429992369
    0x20315060d080c07051f1701050f0d0813030804180209060a030c11010c030209090603010908030408071104091202060f0601020d122019020a05030306150714010b0f0d0c 74
    0x52034054441100880d903515105070354209503030080c070280d103064158401415006c40c0002603619903115007007410303040740e07152001c0c0101500a12401c440351202d08008180da25070602c10850240380c03403084644c01417880004d402c1141c10711000a0200580b0001c0045274100881c850001c51801c00804005102c038410362080009040d200c441d02e21880e800360440420703c2100800074010344444100080096000841d000c0c81482c500c4089403403401c0500c98036200c5980940c81c00c0c41d6490b10b498411258004004c04c0301e112141a0840c0c00c1615107000c1c8150140c03060840f40c0485542c410040d0404500030001d901d40c4101808018682c1e900148144908429003440040d05000d40c0484c800342c240c41008604074a078224106508030251802030a1400091740c03015070642d09560102d0312038201c44e0700540964814408121a8504082909110603002041a20f0000756989504d050354103900d050350145d44d110460764940c10140c88501e2280300032a45020601030680d29405e42000f14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429994865 1250 429993615 429993623
    0x1c020102250303021b0c04111e0f0403050706020601150516140a140a0b0c0304110402031513092d0b1e040506040606091416140f0403020315060d 64
    0xc070401400d0500a904468103008040850118032030703180141079030360041d05480c0d0302551904d00c1c00300400d0000c80a48030302415540b0792118140f1a02420304150300121304442c584e5070100030010024108100b18001483d254003d8007080d0301d030400c40c0c40c10030042013007001070260801550300842e1110003030403074056110311140200c400c0002c5a80c41c00702c1d030311801401019501c610501003003001841c500344902c1500c06841950f07900c08210400e0105036070041590b030500b040392800c0e11b803540141d54070030487e08500b08a24001c000044103c18000c0d0050130aa80d2810881c2c00c0c030440c44083c14011061071460068803051a01c00d100315400c030030303000d048085010b0105095105103a00c404c00e02c3d4403100c2100b217500b03040c10015100d40c41a00c08803281032506000048502a034050150700032000d60717690103140d880b0307141102c1401030b6503111700800c48040c2001c40314980140c0a0410f080006000c1903c0c1c0781144141840c0010111001c210b504500081009980e504665003080c6540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429996115 1250 429994865 429994927
    0xc18090a020f160c081504030e0609061b1c0c17070501050c0a030e0c09130f170d060503010b030a0807060b0a170d0e09062e021c020102 60
    0x51880c804000d0145400d02c00c054000042c80340c03066801031a81d60b408900400301d81403041c0d500d4190640e10150356026140c55000c680020340407c4c000d403c80b002011001d400c1c5450440c40b000021015404450f0410440548098114a00030208680c1d91051140706181c00d061002c800060700c07509450400800c000c112680f60700e038620075042a5034205601000a0099003071500c3c0f250300d2030b000040c03000000f0340f0308500741052403c0081c11001c1004060100401c0b41ca0300b861a4090b03040110060300c511206002090004440c07040040440c5000100c00d0380742d1801d8076203c03094a82e03a0348820300c684e0411b03e4001c0c0c03580c1c000c40c1744e0382481ea020943c25a1241686407039000b5058481d4881c2e0b02c5850060b00080000788a2001400c29054406544d083c1001000075244041205000e40d00002a070300043c507681881c1209640c4080d0245a111290762030705000c80402d0f40d50031004005811200030301c64402115404142030040e2030000354100040c00100d0f408040311507803240704100d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429997365 1250 429996115 429996121
    0x90402130c02123c190509120606010e061312140105010602210a0c03030b040608010e1005071407060b360a0b13020309151602060c1809 60
    0x20080040b4850082e207070564645036101031000100c003032121144038180c9030305000d41000c84006000da9400180502034480c1c10512000203030b0a05202121041051000c100511f070f01640e901c0a2065602500400400c810b24140b0001454800031182030740c0900d9061010746203403007504200c1c00680761240007602d040e0505003003400c01101009a076034115447e00002142540c0d01040d100d0300c40816212410f1300004aa032210b10601c20003400f000007400202119000a10a4105100842004001103220381d05c1e0329901e0b0854a045465400341e81c0310502a160a040358020294402041d040003411455450400c26280c800d94170002c04055441010f08074580e1010b054089150140c5204070300c0d0440280b40f440c14080c1e000031a807449585100007500e84a050060001c8000080c041420700c40c04202440081c0d0405801c070070450045040301185845240c020b144035a0794130f03000044500b049000681002c1c4082c01c0d03d48601420088000001010b04a900760b0300310556007181b5580d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429998615 1250 429997365 429997367
    0x6090106090e1c05090604180b121c0e0a0f0e0603060103021e01050d0c0804141218040902040504050607180308040e04032c03010501151e020118150b090402130c 71
    0x1721038030b800298030600200e800326038803907078201c0404c030a408038200f004400e40030f4003001490340d4600a00d4409511811030441d03820700c00007482c1c8039200e060034001c004410f14000156988419001041d00c4104008200010202c1c1e408498000009030702030401541035401041a0001c900a0100550101180114a640b10703008644910321071450030401902e1201004020040548042e101b031811400200d000c0b005c04114082ca40c020380d040b103480c0510344251840707144800034031282c1c040d559980260242c3c495004203442644110040c01452429000103800c03029101c4403180f90502c900014400114001c0403601600c5000c12440d4240e03071285011107480c0c500d40c841d90300c00b140d440107000301d03042c076400e0745400054102c00a10041e03032100b00211811400d8207080b80021a0101180094464045040c5000702d062002283c0d0800c1c1d0080366401402c860000c407001205032514030481401072142d0407a05100315031388541810b26800003020180c203200841d00e00d0341c3d02c00360f10f5500303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429999865 1250 429998615 429998617
    0x301030b010e1f03030c02100201060e0a24030c03021305131424091005190b191d01060c0f030e030c0a03080c0d090b040e0705041706090106090e1c05 66
    0xb560008181c02060f07205e00d8002c10440741e07548100e0007500c400440698450042c0a184142e401d0700740781d882c05942e072700302c54400780001081880550503102c10320824401d1903844400654010340414842a18500c1409072020030040035044045c0f40105004a00110025160f20b454008010a01091540d24810b092041d407080e0150307001c000100a11107041d90140d401c0c070514801050344c17040c0c51130400301802d81c2c3c4c0448001701c0c800005010b81900103420341c00942a000c4c0030f0400150203101c50b800c48000341413034100c03003d07580d90048401d210405820410b80507200a180050f5200e2096880200b1901d00b00170003002d1004030a0380f801981c404214901e00490000c001550030742e82c0c2e00f00007400350f101840b03001c0036000c0c2141040c5d2083c0100007040441c2c0d905c1105a24051414842c81d45403130014040e8010041d0400000582442c8817034002082e000900140160303007051004030f400c40e0403591159034107a0420754496005040031880240769064000340a2200100c50411110b03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430001115 1250 429999865 429999901
    0x1807140a080f0c0102060901091707030302210103150209010c0201031d030f0903070e040b07230408030a1e1202090324041101141803070305120711060301030b010e 72
    0x741c4522096428801000508501c1c04007081c3c080d180d5030717115074580900b46d450608016242d95440d0700303217080380d114002c028003419001c0d00d001420441c402c0c000001110003c882014032000390307401807060060709101101e80c4600c1020440c6851214400600b000f0368030b08010341415684da0010489540b100c0413003803103000841c25240d5034145079a07440e4103904809017040c044c0c0304a03a00800c002d12183d1100780140e800588110440d503664404441c1d1201c468620b0500220f14580d1460650000340900f002c1e2005802950b106d40200b04002e08a160b44e412030582d07a4050a100d4004941022512005071128180541e480c48107101081c50704103200d204003d180441018411010f40b03020010307008a12a0010ba1040d801100046405d84d042c1d00b070405245d030b000c03c42d05e541e0003207003052800d0048002e401e42e444560b9a0701ca65050600c4107002c07110021000401e0403c00008041581c40c41004a503c0350443d41581c0700c20b0400b220501800d200300044c400815400b0100c01d00f07190b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430002365 1250 430001115 430001129
    0x304110301020f0a0908030406090e0c040801110d0f0614120a020315190203040510020d15150f09120f020a12060b09010806041221090809091807140a 66
    0x5035480c4906a40410f6510011041e8005410110042a9030102000322001c944080d80d80ba0140c9003400401c000c2500c02801c3d10134103035010480010500000e000705454442807a000701d44550302014207009480310352413113948140c03802006000240c0384034040d41c00c40006035000109900019801441c2031600f400207980343c40f51401d4002e188006160140c402d0000310101d489403118040b458080c1d0000b50b4005142d50010a850710301d500d1980c0c05015143e070030711804180c4120b602c003a41408e940d281c0290b04207480f1400d0588174250016400d040314505850a100c55074a0701d080b40500703c0d0a031400500060400301c454055582d00c001820113807d507408800510034035442d00300000c0c211100104d000781013290000410f1080887c4541c811500001c0c08074070031a14117400c548088030640c114000c0071000c20240c141158900c241c1100b40d100310041781c0d503100024204016140000e102005000d40200c241c4210400440e100c0215203864880d005100042c100142414003070340c005403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430003615 1250 430002365 430002367
    0xb150d06050f15011b0303050406090f060912020703020a030b07051c2304081606021903050108010b1002071e0302060705030306040c05190e031c020a0b07050a14030411030102 77
    0x40b600703034042c002038068921841d821241c80100da006441200030004001c021545903156000803901035085298014480d0100050801c51170b501c1c42c44030501c0513003e580c080d6946048000300560341e4151b01d00c88580b0700003050700320f03e10b81c0051581c8055000050050480301c01040e0010700600980c0e000d890701e600850002c054040f00e1800400c603c802e0300e6016800076200f401300c1c1d94030307000090060790031151252a0615001541139400d01103c130855001c2d03404c0180e0b215451018904550190b115135011510b540f602400c5400d480400070f60521440d42c002c1e600c0c280580000740e000498001d00c0c92617429107003919890480105c1c6500294005400084440400c000840154403688046400708030741c4204410441d440e0081c0002008604001c000004080e0700455200c0c20142c00241190081e082031141c0c4115248400410340159000511140c00c10920302141548408189801ca0804140c2180103140c600c20b0300030241036003c004007007024005012604108258040d00079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430004865 1250 430003615 430003621
    0x3130309050909190c0503061f06030510150c0b01090e010f02180d0f05030714010507030b010936020a020d0806100e1306030b10141e0d0606062003070b150d0605 71
    0x441d40d0030711000c460004c290127010100d4254000c0c811a8010b407881201c6015950030a00c107100f140d05800c04127400c0c028034802c240e00203001208034501034a40c200001c41c0b8220a1a82a406d55800c030110044041c01440800210400e00e050540f1040d000c031030803120340c0f449050485040d06010401b60944c00002942340502000820400c4810508002007026035183e4030104c1c01c891240110500140d500b003010080d11200203881d01c5025540aa040e604051030b180150031410003080700c03600c054022030701c0b4105603011311038540c41c1001d9043c129024034001c0006284080c80c0c228600a000702c500c084421600c6402e0100c04880389401c0400c110b940781c5c00c2440300c1c007104490112208442d01000b0510080001e0600c1e0003500c0035240e6590407020183c110781a4280722020781d0020060f528140104031203000b0300c0c0081000d515400840b100742001d44881e05051811480c0c140e00c104050800103070395071580c0d0b038011001c0ba40300304411048000620048051074010300315600701ba0074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430006115 1250 430004865 430004881
    0x1e220203060a090507270503010509010b030d0504030c09110c0a0507080d0507050a0b090c06040f05090a050405061b090301020409060e0108010c050d0509100203130309050909190c050306 82
    0x3540202812210401c2280c0e83c2d080079400c1c0c032000c84038403001a01c040940c0c1c280c4905055601420319240920310846a2100040f03400c4034001c40b00c482e92a912a60000301500f03040c85503402120382444c0c49840c03d400d41c0c552540f03d07041441a100015070314000389905020314000d4a10740c1c04900103035080c04445080143e43c510f8030380580300e114040c1450490805001d0030440d26100c0d800009003142480c2c0340c8079a04101401030000000340100000c240d2242d07500002000909040800301c1001402c1000380444010f004100c00102031a0505204c041000080c403198400341042c440e01c0b40001c0400f02d40c42e103020b2201e40d2605503001290102e034800c240e40201040d2800c1564882040ea6904007060070b0350006013008011034010046190446140e4100da64401c1c02c0310202d0b40342d520034094800c200d90045600c0a000350300040001c08155000141800400701203030000c541e030070706030b480540f61204042d04024644000c943c00d010041140b80d040d001741030050070b442c1d082c03402c696 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430007365 1250 430006115 430006117
    0x1107050d1a06060418020c07050a0b030411091302040b03012a0e0d11010809070e07081f0b09040b01170403031e1401050907031401080d020706020c1e2202 68
    0x12498400d01d0349a8002003070780c1845410f880031a00503804d458102c00c00044064025031015400c0c4030540500e40c004500b0b510746a5810001b0800c280c49140d480c940390070301d0300d012003400604520401e4440d0034091400c0458181c000c842c4e804450000b500b07040c6000282c0140402d141c400e40e0116048400103040b07a61030014540348102d07855005450181004100c052254280002e05407518003040728448e5104140036540441c061040750345483c1c0b602803041d02c00004682d1103002804410821109008000c04290481e9000408c4600142840c10404460140c800e08030b00660b5510940c00c6680c0c0b00e441c11503a85603000030b50984a00f45800c1c01006040c0b8400341d0040401c50001d164001443c52185510303510071041018096401c0904001009401526400816403641c0b10030380180b251281e258001d25481e4000e151418071200013a081ca01c0c941d01407030070f54106400c90202ea45407800011030110101403450442080c1c1c1000421848500d8156100814000121401c9188a0f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430008615 1250 430007365 430007393
    0x91e0c040f0605030606030109091e080d0e03090a0b030606070f060b010e0108100320130917070302151807060e180103020112091115030402090a02191107050d 70
    0x142040c00c126101c040c243c0303080c13000342c0700d946d0014001c20041100031829401081c085100746c000091000d00c8022021202d414580d090b41c0c00540050203d9464185100301030751403040c00701541c01d018605c00003569100303407482440c102c01c800000080580c1c0d0307007808481c0d1031903002c4807007841558203040800080104407025804102040400185903020f821145d10880c5148100710070142199a0068400c0d00c031a00d0164040950348100b40ba0b6440c1c130302203405080841d000140b54021400c0003400020302982d00d074021181040101c002c42d9000c10940c9103001c1507585160140c803200707801080700c040400d012519010b00380002c00e0f010f50003841e00c517100c1e41c2114a061040b07002e40c10801d18030001e101c000d0108040144001c0c99166581200c40428003a410708440c6d9001480451003000b88021381d030094000c004200400c41c50a1160150483c440e85130450800c00b2240c041c28140c0b900800c500c00f03004d02d40d040a02c3d0820300b00055409090050a44802d03d40c0d1803424121107882d034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430009865 1250 430008615 430008629
    0x510020106081e1e01090f1103010f0e10090c050307060f030b190608071403010b09010212120417040810091103061b0d0e030408030a0801080d05040302091e0c04 71
    0x305910026100a07030380841c1c00e500c00c1004d4030521030100d031008001d96042c1e0030344406540340d0f6844004280b481c2d52101c00e490140d40041503296076602010f00711400302c03000345042407804203844103407900081d215110250501000455050b1802d03e001070420a61295078148160140802e201d0f0340421340d0254684580c40500c00040f80c1d80801070b40c4814031501c0d030500d41601100300301c0584102c0003503801c0441414541c540029480c2d0104580d4000d820014100200003103109840d42e0400080e040c2c0502c1c0f1a007141480c080c0421600c2801001d4030290480140d10808200e040009040710f0081c00048105c2e11082e211481010150a04110544402c03820b28041102410b010480e503200703030240754034131a00c01e0404aa07203025800c621403e48100741d80c0c00490120440030801400a000c010380119243c0c0075008004000030b205820681d26030700044040e1600719082025a41541d0303048540c40041d80e24107103c885520168000262080101c034180001031030064010b006a4410f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430011115 1250 430009865 430009873
    0x102031008060f010b03070305060103021303210804050307020d05100f05010e060915060309010f0203100e060a0b030c09010519080103030f0905010c060c0314070503100f1d040c051002010608 84
    0x12011683c8141800b4814500f002c0e40820014110512030341c0300c0c9070310180c141001800c0030712680000080719455001100d42442d071070f8540541542d841514a0410090700d003400e4240790607a202602c9029041000f4001d0b100d04c3e5030142000811310042d105402880303010030104c140d00310b110000d04403e104400710000c00c4800706145c1d00306850aa403099201d000e00d001401c16403c01d0141650009010076415562070010111150303880c0001c500400c001c0880013035071800d008001c481c20a001d070045c0d200c3e1014001c2046200da000d02507030342c072040041e030b03454552000c000103984d80e224209840003000c0d0521803101620f5008146603040e280660b0300e441500c0740946040d29081510b000b070b680820b00c1c40003040e0000326250452a0441418600859084646000d4a07540881680c0301404038001200300800d440341c1703500318401000c030306000094031440c203e524404d8a420840020b086400c07500000c3c00e05c030001c82a00c3c020003001e444c02002d041503180c000e000344035a020f00e080c2405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430012365 1250 430011115 430011121
    0x120c0304030e0d021f021c030b0f0315010311040906020307020a050d03021303080306040213080708010e120306010305090c030d0302120f06011e02160603060501023901030905010203100806 83
    0x91501c40741d03003a5580500404078400310036115800601c102c5c0c21110451007241e400941102040920300e1200180f910302007054a80601040381c4401d4201d8554001d900c9a08081c10780f82c03031551103a0444e03401001c80f480707042618000c00d015000030b00e0042c1c8424000418084059400501c0c1380403280a013050b200c0503001a58114203920030f0b0983c24000c225060307400d0021540d00c0c0019500514010801440c0c51907140c80d040c0122100c0e0301002994010010400040a082c00f0300c10080310403402400304080708441c84661408040c01e1941095a140f0019668003c200310003901000c0003000c4405040001c84010040d50105000140c00300221010499040c114488503002e244141c481c03403170110040025180100c0311040100440c42026400591280c0020f002c00140405a60214405080c44c00280c50304d51220450b16004003c1c40010511500130300d00d44003030003000048c40f0113504403900103c014160104019040d94070000c00c1c4540d40303008040040440c0d100c4029100035503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430013615 1250 430012365 430012369
    0x7020f0a030804090f021303050f0f03031b07061401091a0303090901090c090f0b0703110303070e0135010e060111030a05031003050a0c030c0b0715020a05120c0304030e 74
    0xa00c503444028a80401804103204028041d04130056001c1ca024005082400e2801c1072102d280b4107a00076901c94100402c41031030003409001c802c02410003040214514200f00c01c02d040c0d0f0100400309100030b48008a0f808003045185e0700034201784003000030311030400c3d6147c2c443e6000401001e48813003100850700c145070009003400300a85055660081140d105a0320345407401d00a041c02044460410001e46030104110442c0e20b20035001e4041401c079191118004d10380542203071000c801000d140c0e8800e004101c911684803030480d290311002c0c41e1083c451a40d2265000c480715051700001d641f000c1340141000782d00340a240a07412036050000000180c2c85000055400044401c4a24503541080016070070340c0d40503000a6400c01001008070319070555940312542450110042100d10f215040010014016240c0603540540b040a035000e04e001402e50b510120160200070490f80240c01280307404c040d9004506880c20014102144541440d040c44904660360048604402140030150707880300c54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430014865 1250 430013615 430013629
    0x309010c080d2307180b0904091703011e030f020f01090f09091506080304090b031507050a02060709060507320a0311071a03061201020c01020a170c04060807020f1207020f 75
    0x32404a0f1817484a1030905800c001c16502c00a82c0c55000364941a8a03c002740250200200001c0e00c407510075182e504048101e10303020207443c0542410405c19000744007049c0401c00c960301041e4100e603038284500046c40160703010300c010350001c03c076100c5d00c0c0000142e44249030000700b080d611070400c1e0f6034540ca01001e000221012030245540c00d506c1400140030043c046e91005005030002802c48041511011015028820803640b6000044010450751a450b03010408160490414200190b800382030140081990250b94000b034521003541086894a51049640f40d0410400d418130810001c9034080250b07440200800450004442a114209850020400340281da44400844803808509080d8030415000501900e50204079145101e103808401d04c000c05003541880005a02c50340c0c0310b0006000060f868007044c012545071000c0203420314581d4100c5080c0e8016081020072912141d5080b407400581c0b40c032008180c421252030443d80409400540041c0740b0845010080c40d810801344009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430016115 1250 430014865 430014887
    0x11b081003080a0f03022206080f0702030306010c0c0509043e120f10151d0708070c0b040c140f15030a09060203100303020601050108090309010c080d2307 68
    0x1101e0900c1000f074118882d80303c0b0903410f11140381c094240b210070481d09045107803d00c24224a119991003c0054503040f4003c0c55004001090314600f506e00f00001940341c0c8401080c480c104018160018204103c0001d21310180134082c00300d0345d86203001e1400d030400d440e141140040950112b6220151006201c1c290b010641e0240c001c00003800140c41400380d12110400a1b44403401404503000a40504124040405039100d074040382d50400000e00e000040c4080d08110b03045101d103075007228204581902542c01c8a11840d05042e10342d141c002c202c880c407408902c010103540e246014841400202c840544c280c500e0b598004070901c011004200e8050100d151194218410a030308a60391109400074580c040e10016001c02c0382c0510742c0e908000c0b64030841e062500255103507002d0041c1a41001890301500080c00c109d030043c1041000b0390f40d079001e02c0c1d02e880d041080035040c0b1010005000305503005c622034803a05000300b180c2081034400004080c844080c200f42d02200060b0064072902c44110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430017365 1250 430016115 430016123
    0x70e030a052e18061b020717160801050603011503050d1809020a1701060e06030a020d0b120c0420120a021b1501050103020405061206040905011b081003 67
    0x40d880ca901d44003450b1500030003040304040b900184040d1036104a5025000c2c0950f81800c0403403080003586440400ca403d2400840e21406280c800b54051a07000110390381034036106501c01910200410440d071030104600028000603802c0f6100003002001504005c0c0942c070210000e0016059655041100e5185444003403c50b5000c105c06141c441d01072400d41c29201d020316800d0346c43c0c40e15942e02105030b030b116806500000c0c18400d1480018083c0304046805880c09103480c40d035004a8200140190001400180015600154641d5104980d0788941d060f60030107000c81d141c408219184c00d840f4030600c00ca0901450804e06000280024100c40a40720024440707498100780e000c2c0041500b480d401001c16000e99401c0289001e044640703203179102008101d4004001000040d51450041030040c5e200d54141070040c4420302c41030f074400c0141c4901c0400101d64081c5551a000024044d1441c0700010704a9403070300340c840c0c110002070700800542300724a840340c0c0f806840d20544188200781c1c502c000f070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430018615 1250 430017365 430017373
    0x204020c03160c05100f1107050907020c03150609160c050a060f0b1503070e010905060d06030c0b0313080901020c040e07060f051602190b03011e1205150c0706060e070e030a05 77
    0x4600f450113000c0c042c7c51310400c00100c800741615000402c001100555a0740c02581c401c01c00e0003c14070f01045400c40b041302441800c40c1c0c60410f030000c2072002c3d20191890050301041c1c0c5126900610072080501c400f50407004640e00b003c004d05000004101d9011070a00a80c10441c9000d91424003030785506040d8201a50545903646100e011520684038444076030401000500025480e5107200c09040202c5200307000007201c4d89176240c4158450b01d6075200c050115028410084000d00c190501100544c11041443c0d0b0f54142d03400407400c0c4441c5074029903209240071000d00f020500003074488166a400d858603000441e02002c10b546500a6105140007901c1c44003900c001070a041405441c11103000d5900701e030081c1ca8040200303042e00243c1240460750410300c038100300b040004503004000c10014000d19a2400240c662680b200341c0d07000d003044445020004106600b4200d41250181904004100029a202c1c00380c0641000290707048000103228050314446032401160043d0385c00c1d8810010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430019865 1250 430018615 430018637
    0xa0e070f03020309030f03041104060509131709031903030e0a1112190602030906070e130b01020c1302070b06011b060902030316030e01022b05070204020c03160c0510 73
    0x1c030065840106803048502090202d000100560005140a24403445002004c48103820502044912a911491244880600344240d8403101120600c1250700803c9035034001c58005d516900a00c9031902450b09445034010f00482c104040140f2a80c1034070a0b94188650542440b82c00e903500c4140102800100c2c2a0640c5c40302458100814146060301106076014442d0750700402c68103054284041e03801c0c680020802c8445503061205982c40903150814101e0345071181d000c40d03014418004480640759607400d00030640c0e03008000c800016000201403500340a600321854020750082c0b00c04450703180028000c41c3c2198021111780c50081c3c102c0302c450312201130940703c10340030b003405213800c2e600b42c002044140440c2c50318421041c42d482c003d407039010039031a40c0c0d4002450116515480400e50207a200341d2842d1203010040f010102d101c61410b103441e01d400b0b000040092148000580061100007901c0d41c00225400388042c41c0303401041c11084a580c2e41d4140b000104c403050480000512806103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430021115 1250 430019865 430019867
    0x10110f1606030221010617130308150a1502030715020f070314070813150804051c0908010501080d090f050108010b0f0c0601090e010e011a060f13060e0a0e070f 70
    0x9030490003605410b00c2d4004468040d04205004c0a804c0200081c00640820a11241900d80680c102c614101c0c03200107501d158034018146040503180341000c04010900d00e11a6a555860401910356540f44d01040704041d6006981c0b40c0c01094100c6181100e0042001c14200b18402d85450914480075545030080340e5034200c2e03040683d00e0b07004034060428409203001c9440b0301c016000c0250703465a0101e859007040e5403941c84d91616070014007048110002c204c002039020501500159000798001d90800e0704c120280ca50342c1281e0420502e40d8138100000179aa01d000501d5500010345480d020745103605c80d0340000800b0824054580400d007058010080380d9508401440d104803904034031410f200d014200c590804d1800c1e07028807115034503130b28541d01200d028130504010b42d49420081080e180c034481c0001c4480c180524041c0316640202d8a8052600c14000300c07560f445044901002490300e61601800307207010080c0050250504e01804aa58441000b809009828544924442e5600068 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430022365 1250 430021115 430021117
    0x140403080709090527160b0f0915030115050c1b042403060605040b0a050f040e0a0302060106021c0e19090905010204140a1802030405030910110f16060302 68
    0x441c6204121030450002a2411a0301c1202c2c001d50740340402e04525665100300b9000102c00020910305034200c054602000c4417404041c404660f01c3c140115140c00305400b00c0d10850280201e03094201d001181e10700e1054000000450694030b440000c2c48456401c00d1003250b85024281180003581d201d440034607615545c840018a20302c00083c030101d805130314404100142800941920400300480340180108030660007424082c21059404105041c0803800165400700b0784e10996014008d11412204280c070340c0d4000030800001e080407221090400d1500944d2a4003d00c1600c0041c000c18041c40204d481c04400781f021003581d0740c1d0321800c1e03101000c1001482d40e00d94070f410011b90991000010140b0b5107000700c14403540144001a1580d142480b044071104050640c0b510032625068188400418040502c401c503030710390350050300ca507034a01c0d10b00d1440c81400400d1b907001220001e6002283c0d032000842c044240c9031016908000c4411940540d80c2d41c4017401c0e070203059080c48041c094284a58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430023615 1250 430022365 430022371
    0xc05031036020a030302030a081501020d050c0a08040b070311030f0304020f0a0306050c041e0b030403120b090f070e0a1a0a0c06020a03020912060108070303030b030f0d03050601030f14040308 84
    0x700c0082015240d41d0008000540c513500c1203000d0782000c5146540c464100716096403007518000c10042035400000000d4680d599210f15a080c81004521149680c41c00c200080700c0030f40c002e070034955490f11159201c3e06a000300308224009507400c01102461100071013924104480010741600316240c41e0301f00854a02c0701c0c40840d80152000c28000081101ca00466004a080145413565181001c0170312241e11000380d018424000074510820200d000c40040340e83c840c0d05442e00705100aa0503e1000290894062a603413142c500c9050080e40c690900301540103034107584034140b100c0c0b036140501c40300345036911402d0715407065000700b141c2000b0103100820100003d407074140400360550382e40341c080341c121f4032400c00025408502d2250a0a000d440580c1094000c8004c1165600d0030207801d542e2440760000404240d220381000780c03075440402c1288008038108080c1c6103a411848401402404119065030009003000801221660940700d4110031040301c0c0c130340d815155560b40382500d03044405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430024865 1250 430023615 430023701
    0x11091e1c08180303120f090d0507050601030b0c04030501150e2a0903030904090c03020f120304091805010f1e06230a03050f060f01060302030708060d080906070c050310 74
    0x400681c04261000d01c171982c480c0c812000d0104d02c0c0e0a128008030314110310452034030184001008058042080000c030107046070b80c8a950501c441da42c0d041555418010741c0c0c4010300b25804c00503d80300b0a0100d134019401d617003400306008030903503611000341000380a091280c100da03294161644c080000400082003031a10180451b031910400c3c20104045036031034042038440c074024030010310441c6409021520041001c540d040d40c807407021203c90340c03244075500c501003a0b682e841c044004640f544113440c10710550424000c01131004009884000340903150100d094581d0f0b40c60304180c520000307100308415104485901d0300f04200c44100105200c0c070101200360f211120500000000c5c034100301c45034900c00c402019069070700304041406030246042e00404207060042c02000421980080700d42d80c021402c48031001d4038009420301c8200d42c82402c000e2074210100240107021b12188441c03140443d401a01116103181c80c14817094101d4803200494601e484024074603621706240000c0100080c840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430026115 1250 430024865 430024867
    0x32206020f070f140c01050406180e040602310902030a1b0c0b06010f141c0e01021c050708010302060705070b0712080708100911091e1c08180303 64
    0xc90401c01d81074101850807200c21a140c1c0b00042009281a140818448840000d1050900f2800060080d02690103110100501c01c5490100490340c1d2404800509103940382c4001821303c4d040c46400b940c003110940568110742c00400d120205803410000c090b59060440c040031034240710360000079500142c11300c42d41a80381c07c5096403400420f40c00164460392074940013000036481ca040010171a00800c1c4506000b21000c820303055070b411807590080b0b417468220081e5207400c8519071000100509039920070036803030f112501900110550043c03424009c4c80c20107900c0f0748004103091083d1041140d0140c000b0f042e100041005040220142054500c034006881c1540d031203042844c00da41040700c0945155516070b03d42201e46030002402908443d00380b4040341e03c2d1401d0f9004800d8000c1c87c1c407503140c003a561a141c1a0312211a0310540e0314085004124680c603001159128500c3c1c440c00b40910b00c80c905581c07901c0d2007540c601900001c00341d440448242400012800b510500d10300403d400e0701800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430027365 1250 430026115 430026127
    0x405070b0f040f0b0306010f0e0306070804080c011b11120f0c121815071106130302041508010e070807140d06022a03041409040c08030f0a08070503220602 68
    0x480030f01a009008801d100070f4592800000042480388003010010501046481c18142c07520041640c6502a0306410854600d4030340d0300d40480c0074071441782209201e51030524116040b0031400c201c0260070f002d550741c44402516040c103854850207142d5105001560400c56025118a0400540342c08917060054800344485508513080950018400010224a04841c5c0c0040e00e02824505900c2c0348030549030b41407648641d58081004600000c1e184505001b081e08401a0155080500603680c050000d00503880c040500c0c0b14003e5441c019140c1c01c0d42451091425030800260700700440b840c190003080454584450284003049400c1816003181c0c003100341402246190000300240d007000000714003170301514140d000c049002e010100125401c00c010400a01b0700b0921040d4045400b1540180961030b070f440c11500181c070a40c480344942c0408101650001c1409001d4100d5256030b85501c07202e5076038600704503101c3c070040b0384420500f50b0010540d00200780401104038140e100b000c00514100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430028615 1250 430027365 430027379
    0x30b040206070210050a080709080c040b210c04180302071503140f06030706020705011d04021209330403050304060b130b03071221030f1b170405070b0f04 68
    0x511044e81d1408640c00080300907a0503400003000394003a0191410204841c1070214203600c80c4054102144110f8444034a590103070386016540490005c0101c0501100780d02c084080e486020f030b141c025104524102012001e20203004070015183d81c07603409003c2090030304009a40c54103030344d4000740815a440ea940014142c21548076406402850780341f27401e510707214041518040c0c103070304010110341100b41d0404c040d9800248a44a21100c0c401c2c00034a03210b0340300490f0003030003007003181005030a44034240030300c02d00301007100c1d611524652101088030b40000450348a20b084280414005042c140000d4080b0b440760019641080c810f44010442e0320100c0c2c0054826000e148101c048940e0355a88007119160811910009200100c0c00211a610075101c0c0070000e18410072125042203400e1152049a1003a40051110b4141e54004c11480d0a5062f41070058000e01d0404c50210301f0441800c0700c600b5280d50017501c1070360302200400816080203c407280c690440c3c0c050004404043c0000314140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430029865 1250 430028615 430028629
    0x12030f020307030624120209010212071a01090504080909060d240e0f0c0114040902070b0f061c0305160c17150c070204110d0906090201020106051801030b0402060702 73
    0x80c090301ea5004c681c003420180c8000c101074088407000c824a10815901c443c0a82080c013840003d0071450005845210310b0700142e00b0b1540020300c0003c00180091200100301c03550030110903064405030290a5607807100802c5088990991300035007000403e018110302458001d0f03140364401800343c039482c0300c0c43e0340b980c2d52114008522400b2800c4100f03103058040c0340b107262051000c01c5000d48020001480b603010050b4860101c0b0203901e04000e01211000361010503081264000c0061040455840c0e10604000902c1c503016601c4911013a142400b04255103400451143e99000e04180051000798aaa01742d0f201d611034010f160500d0036188001000c1002d0001c498002e055490010f10b05460780b048043c107040c03040180e1020210240c0600c401d4406220546000642c192000101c0504003000a4544e015140502d02428146540034041185c59045071800364402e80003486040d45650030092a407114905c001c071000444401080031600c0c4100c916003142c00a42241e1529100c3d80115680c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430031115 1250 430029865 430029871
    0x150702031312170c0a0b2a03060607080d06080c0111060624071a0702010606050a0807090e04201c06090204020405150a0e010c120305060102010e16030203070b0405060712030f0203 79
    0x500e400c4124a041480485890951302c050301901d28107c03c0c2d1a10184501c40b007000502010403d0b000c00007a40c40e441d40c04c100c40c602900101642d1301d49450001d06c501500c1540104140b90280b0136408215500840720b0030740d11820755002e40250b550380d0061000f07512051280100d0301c0004944440c0d034001d1100102007081c0124996061005105126808800040d00001c116072410104118003a840800d94075040224070f825002600da050302103810301d00b940c1003e012803c0c650188010800c1c5801e203110f412102e1202000b0300c9142d4003c11010030754652140c082003122010840024582d0381c402030201d03200078401400c00f5201c402188400381044400b50b41d00c04005000f02c03246030050100c101e440700918243d41c09442e00d036036205010480005c1401031540310404a00c01340e0003034110542003d049022250040301101101c0e10340d0015100582c028001c042d030100f40380382c80604031410390f0f1000e0300c2d5a10300f4420b030751000f044a407100400000c040c3c0e185181c20b507140c014002580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430032365 1250 430031115 430031137
    0x9010903081617191b051b031b01090504180f030503040b010803040b0f1b0d030204150804080a08271b0105030601020601060f050403021215070203131217 68
    0x3140b407510b140050b0200101e086031000e00344180207110400403030381c0e0b01204103200c07490036240c140c80900c803045980309501802003c40c01180c00410b1100e0014100d40d081d180c007181200c0d205404040c081100d03802c60008240000d030b00c3d01d000d00c00c030b080a420000c40740c07440c20800c44501811392141c2d0300307070050f40700c0440000300700000b40400d221036410080d015141d03640c0034610703140c68050400443d1246200803ea00320021404a41c400c6910011107012010101134400c42d010840000b40254404e00840600703211506110307451501c294030a51150b64000c0841d4034100215009880d26640106101454540d088204240e4803040c407210082440303450041c40c80000f20305420b00c40b82d008003150f03410004107108121079a070b4002804e074110740d150306000456100918040780c00744075680002e90406844030700c07048079803400100e84203a40021150600e107626200e030100c3e1244595001c82c042203c01c41740c10300540d030040070030702e2070980b0880d0b0f883c0104060020b01c804507000f00c02821 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430033615 1250 430032365 430032397
    0xa08010e070507060510140a12060515030102070311060702160320031c090603111b0c061201090b0f131a0409060c020114061503040f08070507080f120a050901090308 73
    0x40b02c1401c108a03103d20540c1180c601c00c2281c109408082275450906024002030749680121b03103401c0303160301d85e826502405802035684040504001d00f540c40d14600c842007501c034000000d4001071000ca4868035807504000e005654a01d9610b600c039501410303c1c4900395186842e064000c2e10342d002c1103003040b2608a4420199013603800c0c803010380300150382d901510515050000c40e1007070a07084c0d412681c040e048490300b2008071400190b01c40c034040800d8404c1c0c0d000340c0c00145844082030720710f00d45412200841c40910251004000340001d030340c583c041d001d400122001c110803000880c1c0e0000c0a0020561071000239520700e900010301903c0740c02c0020386149954031020000c40768280141c0c141c01c040401c00003080c1c1403841c0070400651408290300346410020010908000110b41d5072011030fa000042c0300d840d4103150070b015803940000c4c45103c40a100f4041c403110f5012011401e01c20154030300c1071440c2401d000d20001e0760543c1c44041818108440b845010001661000250045180340c041d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430034865 1250 430033615 430033619
    0xf03020c191506081605011209050718050105030a1106030a090203030307120b04050415021806040b0a09080a05190206120c090f2e201c050a08010e070507060510 71
    0x1000894040350013119a0380c0066a40001080f080c410084c111031007860321002840c00030100400621070080d00030316901802c0b1000a661b80107010354590b10b01c080e6800c01183c0d0341c80c402c2595400182c2001081901e050712202198038100000e550b001d00c200f0350200300c2490315070010f0700319842203902e01d0100798400c000782800c150314440c031240365500756401c221a09083e1a0b5428407440004503e564039000a14501e14014045032451840c1000c0c0c19503803140d84441501c61142c11403118440003a0640000185d14480015410550b82c4c20a018000d80e220f102c1a1200500c5400410b92700b02900300100c030041000408140c1c03140080c61646038550441500300100100703190070991145090007804595428104c5c0101400c18103a410701c1b607800090801664210141c0e482030620b00003c2a00c41010980454080c6140004454840792500780c24016141c60003124542c40c0019840c00044c002000030080098200300c4070b090540c280621641e0702400c2da502142c0c00d5041606170790302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430035971 1106 430034865 430034903
    0x3020405040e0706080702060103030e0922030c0210020705060d0f1b020c0406170d030e1e01090506070309050615041401060507020901050405070f03020c19 69
    0x20a002421020109039150449032007100c005c90003981c00201180d06c00f0402c0c9042e070b94992511814102e007142845100d10f03008000c40301c80b2058030070025801902100d40010340703102c0ea0f40c0400380e250a10502002440694106095500c41070341400140d9850703040d40d02c0c0036600c40000030106040aa29000b0f03003160440741c400045099016507240d86d021446011202041cbd4051082c00c0e0740d100040303102c6081102040c403036085080d404011500c00e82000b520568980100c0352840e01c01da030b039200c144900c400303039a030a0380d0340c0c2600c1410800d042c458684c0c0a41d850a04100c031030340300c3c2c66081d10341c07400414185601503003201d8840541d03241d900002209040c01c54420066848113070250055101040981c0b140b580c2c480000f075a440c1602616100302440c1d079450500c80c13107503032007600690881000810345006101c10081411030380b00c55030100600485039245140d1200d16 = true := by decide +kernel

theorem cover : BRFrame.Cov 429856115 430035971 := by
  have h0 := BRFrame.cov_init 429856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 429856115 ≤ n) (h2 : n < 430035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
