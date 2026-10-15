-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:02:00.597992+00:00
-- url     : https://prove2.me/submissions/6eb493b6-50e6-4919-be4f-cba69f34e4a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987589928 ≤ n < 987769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987591178 1250 987589928 987589943
    0xc050a0507051309050303151809060912090102060601030e0118110909071815030b040f1112070b1e1b060a1107030c031202030702030d051006170414060103 69
    0x204002d0511000f445040544440d041000039410344686890f448000c040c80c100c1450800c244805548a101c044082c0d041103181034950700e400f6002507558941903179111200d00c0b800000344140c00505d4202c03000c42206901a1025855502c01500501404d65010400f5500c40d000c40070700d0302c41710040c40c40c1d8a0054080d00448942d0f001448201c603409080c40001d5008507405101c8200306001040f50154130b60170001d100f000042444100c0c01c00e5410044c41000220306201c10300121800e40c4007042d008041c0001303100c51140c01c1106902c000400c0d1034486c1c110100030082070441002070098809000700380300764207940da1110110f550005400030391081400c0e01401240b04c1c100034440e03104422500401418074115441c04140c010048010100b00c074110002e07080500c580141c030041460800255100d003400080070303440f070300700340303000003066141c01c002403c90700803000000105c40460b00c0d0014150484401c7c032407600c0c0018001d035000f0560113070803921038004104282c02507005912 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987592428 1250 987591178 987591193
    0x30e0d0507150c0f0c0c0305031801080a0519020c0c03030708040e07050412230a06051f05210a14060106120b09061002010f090c1703030f01060804030c050a05 70
    0x18078240c45240ca070b101e0b10b6003c1c540150441d103140c00080d02501d0102c9070411002c402c1151600104800701d030f40000b4198040410114400c03a892100a11880c9003601c8101c5280d481082aa040344c5048441180c208204c040604215482e03900400d200140715045d2000c40f601240030a00c2c40d4050305084851020004040120418110b0150781007809071400610b0039141401544000f1280c4002603c0780721000d1486540118040030171801e80c165000b030300c9020105003000070083c4002c86120010b4044c0090242e02003207116120b2040c0c400090a94501207e07410a06100ca403540340c10013517078440e2070411000718070850018001400003100400307842d0f041190080101c4a84840000b000d0b04041318915280d42e642c84043c8d0148055981d0300110a5210f0b04a01400c0082280301d005482e0030100414450045c0c2c200080c1c0d12400c51194050a50250140e0340b03100407260b4500484040c40148100d5115609003030b04240a403525031404c5607241c440909081c00f030300701160107621410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987593678 1250 987592428 987592433
    0xa2103020f06010b0d021303060f09020f0103020403051f060e09100b0603040201020a0b07020309190302040507020319030e1c1d15040501030f09081b0c0418030e01030e0d0507 77
    0x31161448820780380180290f540340c0510300b0800c1c01104041040c803038010811290440342440c2c068002c40c0c0004040c00300000c01e1040100424100c0c03016070042080124400c0b455001b402180c003120f40c00030040c4150048186441d02030903404003200200b6845520009808100d200341c82d010300c1000c006010301c240052180011130f07a09010300e60041e0720034010003000d40c0e000f040c0d440100d9001214519107030b40b0342c50100c2c154440c03044a689e101001850000034040a80c0103042502d109841c100808e496956040c0d03540e0099290000c0080810110081c0d00c83c032070380111407010325036401c42d09020b09050551041903015402c07000001c2d11400c25050500000c00f0b5855040c40c00d50300e032014043ca451400a2034400c40c05428141600d40c02e01240001c9a03a000b0781205800c070304800c1d2103034096484091424980b180054181c4103d500010b800d141c00d20a6070040c03e016616220003d81c15602542d103100310301c2c1441d05048e99803d1011060324207118240c403040d01c0390354895a8502d00e2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987594928 1250 987593678 987593683
    0x15061c022403070207050109060e190807081b04110405060d11030708041b03081b030d110702090114090403080a15240507150207050f0f012c060402010503060a210302 73
    0x29031020f1f04000034030030100580d80d007040a2124680003a183c940c0550b1640515004440c3d10b640681034134400c1c0040003a0030000460491074514410005452101d071800030481980e640401c4011080c00401041006240042c02420705c210343c1280454030031522405500aa0400c49026000c43c0340c0404220412840d0110740342189054400903404a0454a070b411003809030200103600c00004201c0449a22810002c1d00c1c2182c0400400340321410314814903102a0700301020890158107040c00104e5186a0003180c041c40f06005051611a41d485840032502e16801405c01141e0f16a41d80c0420b007502c8400520001a001c840e44200b030b800c88266406406825400366203041140a03c44403001884d507641c0580983c00c400c4000d84c03202620b007051414000300d060902210b12490801c45290503040d0172130380c1d496203807114100c003200007404000e21007441030180701c050781c10510010380158012809141c2011020f41000c10f19515040d01c10219000c2c45400702c11a40c1c199000000c15904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987596178 1250 987594928 987594943
    0x1150c0c0b0a05070b090a0f12030905120408060907061205040f02060313030e060a081b0c03040f5d08030402030c0303070b011a0708030a0e15061c0224030702 70
    0x45c2000b040007074602d44400901c1c2109010040c009c3e1940202490483d2081c0c004285c415000000e4ac0e440210805104055070b00038403812119014079000284824004101441115503545a0b00c503045a100400c1008100080046484060214028015071aa0000340d0321403030041517400d00014040c2005000b069400c0d800713a1003400c0402051030180d030b00200e055041500ca25070703c0c507102d2010404903428050418505030903c004100010f00021280d400822220724214240b202c282c103520404881c10034503403844160001c450807000407164a40030400304c11607241c588110707030302940f202c41d0144101d02c1e041d10310b140d000c014482035181c14000d034400c9180c11002949001d580740c0c6c83c002c2c0107405100384504514400d51038640400340c0381c120703178000390b000403903590700d1401150313a00007000b00400b0b0408920802d0101c030071110382e04006502030000103001c0d01e0050010b200c2d50500640e0f4100480e000b1060b010300303201441c1c02040082c1254540f2035000c5d140c0c985400000c2c503109a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987597428 1250 987596178 987596191
    0x6091b030f051e1b0313061505011403060a05030d11100b0f01081e0f01030b090a0b0604020c12030114011206050105090d05010e0d021f020301150c0c0b0a05070b 71
    0x3600060203c40f01103401d120891200340c0e00101d1550f607a00c610750703c85150344d101e10482800000100414828988518001c1c0c500c52101049504140402e13100e01c4501c501485002c02c80c1401100c40c1203203401c01641c1e00031070040041a0b0191181c021900b400c0c03c02080c0c0000c541e40c0390300c00034541802c0c0000115149815000c021008102c0c00054100308031001403410b02c000180442c240c03195501c03a00e00c545045403101005410141c00c0c104071701800344000d0b900000d0000204802d10404100035503110303003100f6851f10a441e0101004001c1d4851481c040301845403035140403401020b600510f0003810500034030900ba20440002411102001c0350305218249010414005c60b1b80203020743daa40081601c51481008140c0703400e81c0186007201c4030003c3c0d8401c0c000c403440403071f030b0001c0c3e007400b0702d030425400710310080007060400141c0c04203000355801c1d1008100580e4840d44658007201075503014032100034109030349842400c6a644900300d42d0000810000c5c501b81440300d84415181c0141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987598678 1250 987597428 987597431
    0x16032603161103071e021305070c23010e01020c12070f110d151a04060f03022e030504050d0822050f0106180b0a08031c06091b030f 58
    0x103800714034034081400c64422801071010380030100111010400660340341d20381c482804480c000c090800c0400030000000c0803440b60f00c800468641d007494a0041500840003521000c40000c05035036a50004180c15040601170a91008034561040c030074082c01d2803d071454400141e40c1c101c1da60347d96007490f21000c220a1780315000c0140c0030010700d046008400454000420804e1070800354009094040c1001e0082c04201010280e83c2e8094110350050b080d141010841c44047d00120042c4419994548686284140882c0d41040542003c1390001c015540c03508144a400e800340491400e554903080784480081c0d515000c000412204114109140483d41407000c902c0c0303085030304c1c00580003115009207400600703544001c04020003044881c1107252290000c1c0481c81d141c2d1035000c009800c54180c030324030310300700b40c1ca02c01d040c28002e040030182d0700c0a602843c179005403502440081031000f100203850594900001a101d11588100594042c848106030139030f4080340340080c1a03a4203c0440d51285 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987599928 1250 987598678 987598681
    0x20f03030f0f190f0915091802091011030a23070f11180712061502010b0103060b09031203040f0f080904050f010f12020f090f0912040617060316032603 67
    0x99002805d0900300c0d103004944a451460480d03084a07845229404004003070100b544002c4040c101d03030003828032010140d440c3c1c221800480411149005840c00b041c0ca5600204280701c0264440c144000702c404a440701c291080804c840d410040307a0004000707840b1888010301d68000c0106103400e49103c0c0d04125400c8012660b000c041b00341002001e003012090241d1405c1c80078100e180794110400800d141c510507070b40f0482008001c0e0180074100030340b500003407400c031011441c0c1c401101956903600b00a001460b0075400e610304540c5507800603106a41e10342e911124400010946501201e400e445000c020f900e80002400f88000d40f10040c000f12903c03210000140440e1b60715800c464200c40214010808100345070011502c044001e4131426000810441000300501ca2000c10601901070441269100d903401a4095040d010720700405000400600c00c20080e18500700202e904610011b0aa40b00c442750180030014411a0b07610444804201f0000c44461816501d00320405150078101280303103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987601178 1250 987599928 987599957
    0xf0603070b130608070c0f030e130e03040506070c03080d02250308060f12010212062706220c120b010e13090303060803040b04051912020f03030f0f19 66
    0x2d60a280507040800102000007101c00e40b29118409080344c10a95150700500a820001e012803411082d0380d01a8011184c00044503000d0b200e0004604a000040c504203402d100400143d980100401c1d42c411481c8140407020603034800003080c110001d41ca0040e65241503441c028680360020036290503003800c20145401080e00617034a02d500100440d0180d00e007010000000b0f0440000071b0a03200c3e01e61012a08a03a06154000710074001c030011640d002d010b00380e60402c4000500c1d428603502c01c4410040214000741495818040c40b5001704001801035507040842108546241e116030000444146184501424510800d00408000e19040390001a02008a15020030b04038002c40710541c1c58003041c09044c86580884040c09240b801d4903a40c0303a503501c3c2d9903000d8200307000b458481c00016044c42c1c1d00006031100c801c109c1d00102200800f00300709408110f40b10014102c8560140020895000d8617503020008021341d6017542480c1d070b121403404040e1090064440518003d11005c00c4d1048074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987602428 1250 987601178 987601207
    0x1a07110d030501030209060604180902040e0708010905060603030304030f030504150f0504060b0415170a050f0307060c020715031a100306081009022101150e01031505220c05090f0603070b 82
    0x103030000c8452b020514070b070b0a20101d8018180300c1c80070403881c003c043d0040384441d010340244407028001d8040b50340680303882d000c00d81c40e40f1060380c00401060303d0322030202c0f6a030300036044a81e03c0707805000d03905a90441404104252000c01c4541410284c0e103004000c00c2002502c20101050001e840400c00d40b604a101c001000895004a0740c844910840c111550981044441c14003503204043c0c41c8054154003c2c90b50341e402c011801c54015040903c2034112910000f941d03005c581c1d00421180d07140c803106200342c1c000d04586014040c0301c403100710382c0400c90319803800c2c10804c40c00d0b139980021950b00d06a402800c0020040005100c01d084c4035240c809031f07554158210242c086a90481200d8886002c0d0b240188888510581d0010ba00c0d080065882291042d15040ba4002c01d580e880d141081c03c0e641080740d104030b40301014141e43c07080100040344144e00fa11364981c42000d25454107030b1110001a2903080c101c4944010382c140808120702c500b424019074000f04001201c65040c610308100d42217 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987603678 1250 987602428 987602459
    0x9090a020913021f020a03120b030c100519081902090303070b1906090903030c21050703110d06030c0515040b030408070b04030e1504031a07110d030501030209060604 73
    0x80c1d0342e4003409111000c0d0350b0b400701003d403002c031101094440300240100c042d4440d0041c2c802600402d014408981413010b4500440354000001406000c0d5944140c042116040340007050b07004105061002c81140581042250081041a1610ba0306840e02d02654200440e450303103080440c0e130040c030134403195440000554221a9100c401644c40fa5140024110010502240d068126042100010b42c40030f10394010446036010b65000d00421500800075907840710101030382103844600d11500300d052101c035804580c00c54428a004640712110010090241e040112004180d5541e60b1082040140c201c2c1c2040040000740c170400d1640c200460342d5030040c0641d01c18034484040c008001810803031404100e0710842c4d0302200c07404960809082c000c00103122400340c58002c44000595480424008e015a0120f0307600c44d201051005c0d0441d480d40c1d9807035000d0040b0082c061010f07401c110340e10041c882010040d01941d0700003025859401046441040982468060803003080180088080d000c0001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987604928 1250 987603678 987603691
    0x305031804020f030403050409180203030904240e01090c020d0c081303021305040c14060f3a151a0304170c070f0b0307020a030c0c0905100509090a0209 67
    0x800030850000030030060301c9800071454a10030004204010513400c1400340060743d1503020700300100301c00d02c181c4011123140007101a40c154014420350203a0300c3c0035005407011b1b484641c2c81d641d21000d140c070014100c0c80140c000b5003121410100521010120b031140a144c241c05200509682d49131920182403000c40701c0b4080c00820000580f6000309002c00d02c4d2100856020f80140703d04510b08600384002d000c02d0b1022181c511300030400291503d0548121003444100508e054030b008400180b0882d40d13801b49081e4400300c4045a43d41018000d04000843c042940203110498040f08418040440701000c0041050100703d031001c1c408225403c00c050155118801c089035207441e41e0610a074007982003080d9a500d9403002407a40c031600030129003182224021600b0880079034030b584d001c1209001c122801001a4071400884001c28403404011080a001d80f65104965440d41e100030156201160b003000840076108042145042c1390030559405149080500a0b400540d8001059100c014155 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987606178 1250 987604928 987604957
    0x40e0c0a0c17221d040b0105130e030c010903090806010f0603020c010e0714040c0825090e0708040311190b060f060408072904090c03020c0d0207030b10030503 70
    0x41c1102d10901500b1a0b9400440d00030094140c9407195203104207140901840e20401a040c0a481c4a440a07000c464015131703200c40803994603805c01d028492010013184050158a850b522441e400c08414402881945494000400c0100c814100500441701c283c4c4031411380e41c04034004000ea481900703102c9003590704515000d80ea8140010031a4054415440b218642d409090800110441c51041c05145c444055800348a0324503620341c1569a001c6c215000514200f101c105822841c00790488582e0864071414514013461301c510342510302c608200d41040c08546250144028940c1025448401000c120001e1603111403001e64142e50b030104540084c1003a280c5404100c5a0b65003d44140707031044042c200036280d503600c032100b544d100f20310720401c4480c02125640d0500650300054489480d40b0486005143c903240084442c0202062010b1101701903083c007106508010901160240d0302e001d034001e101c2c0d01d00b10708000704082c074060304016007a00101e20800004001205030380c02410740b10302 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987607428 1250 987606178 987606203
    0xd0219020609180709060f0e04020d06080303190f0b01020a020103150503030708031012080a110c0a030f0b060105031303080408040b070c0612092a03020301020f040e0c0a0c 76
    0x401c0150050400c415803048071003030101103500720002128030680c01a40c68000daa035079600706a84455200394000e00142c80201c0e0402c05040036001820020844500011117560f41e007610307411034000780d60740d009080c840b10042486410b140a65400844101c20401800d00c0920010b550b5030b400400003810300da220f10b025074468044004100041c04041c0039a541c6090502d0f006815620485005001084a2801003079410b0380c985605e042c035070f2115050b13140481c40c5c1c00595a40303c40030230542007489035440030011504d5510014000314881d4071064014805494080c00004004011504000041c030030840d2144802000c8104180c0505200d940e58031141000d0442e0b2040350030144c0300910015151b0f00b00b03d01c1c2c40c1408110342d400da44041c05000051488000d4032254000500400ca114000c081500703030f5210a070500d0034015500c0c00310f0580e26400f080c00e98001400d00c0c6000d0034040f904024062802c2c09103580704003c40d0b580c80c60318107030440203448203e0202020b07000707481444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987608678 1250 987607428 987607433
    0x9040b030109080a020d0914010c080309010b130608010b010f120b01020708120a0906020f07140418111008040b0a0203062704021002030c1519050f180d0219 69
    0x5010b00840798001c00e41e55070b20405100042e5951000d483c0d20707400144221800150210240500228440142c3d12052180f82c903803a001c0c030382c0e000a0320b1101c040d50388031480261a910209034000d07000441c0e43c0171818074a0a00d1503400c44000c1c0307010310f05102c840c640d00224035030700803441080c1101c1c4200009402c2140e00041b8a0300000390440703010382c4140c8011080c48102e000c058552035083e80e032148005500d030030040b600c981d0442d0300011998041c0d20103010041c400c8500c03900750708020b0400920314000c401003c08541314441d0985a00e984a008640d8605001c540c1589144071400d0510440c01c295482c510084002402c2c00081540480428007990b0390b21008010407100d00b881e9082802500b46400780c80743d00703840803881440b8518a0300d20060000c4240e54072003500b24040c0080c0241d00e920040c0045004103d01c6002e50100c00244201050f88203850241042030900708842c40c245440e840000c0c4000400302107680245251091a070707001905103031103023486035160305540051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987609928 1250 987608678 987608681
    0x1816050103020d1e0b10020a050c09151c0302010b12100c03110d02030a0609052a090d080309060601050403081e120a0c0e06040602070308070203210a180b09040b0301 73
    0x4c844550f03910340600e2502a4440c9140c001100d018401c807100b50080c0180c0c2c1e402c0e6500c400d440702c000e00c0c1d500407422a1455180860819502c0b007020000340d00075040480008042d90300100c180f07048040d1551703040c030074181d092240c90b4100c070068410051301c14180360820f507201f42400c080c0300c5290311084075508031031082e080108098007a61010f034580c00d801c40d11602035041181c145050924040000074000341e280541d9008440620310950b44035003054160886408600801140020400410300316880d01040487c10358051001242c0320300f0403159043c00c05001038030707040c10004140400e001007503020301101d00150704000486c02c9106904001d41850184041c0030090f20700300820410054856001040701000c0c65658400d41e0340680c0800220380258000d070001a4403604007800081c50781c0d401001004d00080450b8902c8240b107810000c2c2e840708856155140c80042960040c5c0c1c2d0308a0450250b0302c0803011004440c074141034640403d40100400c09110700e4880708030f41e404d92000e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987611178 1250 987609928 987609941
    0xd020d090e1504051611151617090c040509031207050a09030210172503230a24080303281104050f04060b070b07050c0a05061816050103020d 62
    0x10f8801e01c160b02e0130009001c17040c080b601c080c0011032114090305202c10004034007400c0b40380301507400c25115111806c0b0540c11074190b00004081c08194503032406155041400f00d44030790320540060480707040000501c4151031010300b005034150b0003130003040c2c1200030764030040f50703c40c52030b2410b070351203039000c50040380c0c3c81c4160750019421001703410640d0011a84007181006200e9036188222035a12081d4501100a401000704a60449403200e100001c40c0b00e50014220220502c032404250101410706a809032030680300c040c60b0554403000d03a0341d140200980d422039948005c00080007030b440e104120342c40e884002c0c00001c1c0c0503a083d04c00805145031120b2940107007a07000c0c0c100301c0710007880d101800315801400b415100b480000300904a901c0c09004107810344c1e1a0070001c40c240004d40d40c0d00141058080c0c070f01024450305200703000c000c1c0d2081121140071800340c001042581450402c24880006042c0c1da00c0c00340e0040709812040c4005841d21800b02d4000b881d006964600e11403006000303218 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987612428 1250 987611178 987611221
    0xd080606030604051e0c130506091f1202030f01050a08060403080f0433050a09030915051e031b03090a0308093f120a11040506030106030207050d020d090e 68
    0x141402805020306d00c0901401d0000c010f031030010410b50325801081402d014080240741e00180706078184e00da0500301c3d0000042a160381c280200c20000c1d00e2400380c141d80003143c0081181103410300401235407500b040c03400010000480542040d06040c0c03030040803044001c00700b519070510f10003c141001005a0305100e1100202072000203d51905000400c070312a0300760441825080c000856900c0d4810300c10340c10300301d6050301c1e003840d030074503000d03580700307032030b509420340e07414003209200380800e2800b00f246144111050400341c958902c2c241c0c6188030b031110692907101041d0300a004101c1e142070005900301c001509400c104415584a014940c6458403a4405095a0074107403c5207801d000801c041490010303586100000302e21034002d030b0301018040c0b00e4100300340400d05004108500080e500040340045901001c601e0151281c010440541c0280c0c0a0b0000950010f0110288075007482110b10840e171600c0500242c00540c0c4000b04888800c1c040d003006400542c02054543e00c04507400c2e1002d94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987613678 1250 987612428 987612481
    0x307200a050106051c03030e0102040302040207030906120213030b0402040b04151409070f120905030307091e0f0b0f0c0d02030408120307080c07020609040f0b030d08060603060405 79
    0x204212503900c0c0d5000000c1118650300780303100400c103880d190b8402140491444001059040c1e075840403800f0384124134200002d558204000710150329a4001842c03080d01a0321101c1e045450a000144141201617031072020031301c1444111204105280504201c980019104c13400f42c42d18000100286120030f11107038010b1078041c40c00c01d04985050600c04075880350b400440984551000c1c400c600b501251000e0000e0b0903c9440350324940142800311036600c10032400144e82d17039030742e07503442c40d503407058556901088400300200b00d4108001491200e6020400040c1c4280b89007988906035910240542c801c0c1c004041780a0800351800f07001e9a01030144101169030740910303014065180e90007802500c003140180204211200d9000d0700716070041c8000d5a80540550310400107d5803600204000ca0b0b00a900300511011a580c07070003040c0001c0c0040800113000d42010b810140741556100802c030a200a01003001000e59031032040d240e1105082d5070200f01030b51061005481800c80d0440c092410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987614928 1250 987613678 987613727
    0x109020a1d0612070e040f0f0e0318040504030c05010504031e020d1d060705010f052203021207020d1202070816060507140f0a050c0405060406260102090d03020a05060c040f09020307 80
    0xc3c02e5a0450000d2342c1410f0400c11000035400c0b4442d45920400081c080805c0b600544200581826801140d11130f010b4a8407841840c4030303580d00c03400d440040e42c05500003000e4000519030018145051011240781d40010400c40031080303400b50894002140406851090407002003554485000319603030268800006c10903051481140720041c082500c0e1015400c4480c0014810301c26541c81d042030064040d001809080c494070f0790342c0b2590b440b400d0120b8024088175895800a4407132203d40003440e410f034000d40300460620b02603520b1700c03418075050300880580d800104081e5420004403010a50000c000304500d61002e083c0f980f030140c16007600c00d40e41c0b0030002c02d082804004141aa40c0c2c00003250240b065803118000c200540302d1a0282181c241c00c00c407200361002090b50600c171952980c7d200058181218030000400f55440010290050b03009140716004001c0240040c40d07001550104c808e04003801c03e0744d0a06415618014542e40581c000049a01b242c0540035071032076a4040003090045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987616178 1250 987614928 987614951
    0x105101d0a080d1d0105120c0f09060706140a061a0918010b22050a060305071106100905010e010f1203020c09070314090c061611090109020a1d0612070e04 68
    0x110684d680d81e849568150046076051580305100f2514440c00000048659448038405e8038a50f80c0f110b14420300c5003004008124090306c40c440a02382e080d0050500083c50118042c02c0a45a840241800c2e078440c9442801e0240302d07019841450051110541c2580391072080e1301160a145540a003840e40000e024000038110010f48024400c2031480095494100e044413210311109045004241c0c0c0104a40428000b861003a0312103076002d01c3d6403418122101d42030400a042c00019604000032903140c00c3e0901a8070124010740d40100500888014103600d0300b10300c045489214000e42074010400035004052503c00c002e86014004010b14402c41800c1594018000300010015103a03404145000076205440c0424140c0d801c040c0601107030314261255148512900400f1000c80740d1040c1c3c044000b61075103582000398081c05085100582d1400c21450160800d1142c5d4841c002e05110101c01c202c164542d04103840300448411000314468940100941d6910340c00e5555903040380c684803100d00c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987617428 1250 987616178 987616187
    0x603070c0f021e030d0302040b030106350a11071101200304060f17040507170f0601080a2a12030318030306030204060b040e0f041106070510050105101d0a080d 70
    0x150014110205c0700308240c0c00c1c200750242d00403072066145501003030004003d0940103a641410782c5102c550080900150b6000300103003699219071403c1030320052020411081001d108840400d440000d810342001815600d9102c1100c1d488a210304004541c9420301d0b104030300c007204554111540c1c0c146c0391241d8640c6001851420f02c070b118500012401e41c800d80100c46c0b4100240c0c0141e0300300002e41840c07400c2282191000300250701e200010b108026031810100700502c6024064050000580a40b000d10306080340f01a005400e030540e006102800c0c0b02c0906006180c0d5002c884000d068170030b20401c141401e0b0000d120b10b51000d0483d14420105004060745a030058058034422201044a5603c0d00d1400c00c1600a5005010307030601e4a10204121502401d05685e100b0710070200c224403c0c0d08007001c6444c0c0d070002c80b41280c0c40d45c00704448100309900c9010310340c0501410340f807031003101c0084000241440c0d100d107650b40c00c5600120f1036070010b45500401c20081c042c0c0c00d00719051160450b01c02027 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987618678 1250 987617428 987617479
    0x8030f2503110c0108010b031612020403030e0f030c4b03010c0302090102100902030f012405100f110f160306050c030c09130618060e150603070c0f02 66
    0x500c0f4000c1041d140d40941c01101a036040e02e0310381010504558030312009001408021480406105d040256500d840155000030806184a82e5036400200100802d0040b2031070680744480c42600704074400c1185071034501c80070690100380354800c90101c1c0c031041c10448004009002c400a0024003103101750f280b94004109000f440c083c1c008211800040360104c0c201c0c007809001500680004500c0c040220b01e9400c503500090000b07058504043c6103802712802c43e6003141501040404c60f920014500402d0b201c81001030400f910049041c00c0c02c1304000304422484c1d9259000e01c4110005019483d804108010592408104a68030440341000700700b001e10440c4404c54909003050b0012b4181d01e0f400302500c0c080c100d1112080d0824180e5010080304415071500100c2c0b0594507003000441c3c00341c3c5210184c40f802803403c00690641480c41610484030000d080907280855001410501e446100890361b124203540703410f00300e80b11286031044080d400c8484c044e5020410b02d08481d182c2100c014080e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987619928 1250 987618678 987618707
    0x70804240f08010f0b0c030c0712022b031d10030209031615050c0f010c1d040b0d1101030e330415020a0c020619090f08030f2503 57
    0x42021000840222030b180001d0040c1c407020407050700100481e245500140c03900311405401d07030f42011092400780745070184540c40126046c0c2c40d01000d00c15824030344030348400118440e400703024401304154030014040500310000c003004110300c11901d0084a12801440a5070001c0c8810140c510740b180c0240a9004010b0461082c0640482162490000d030074803c01c40d10020340700a40110400c03401c0e2015001081c91440e140240b018001d0b4003c230a201d41c000e174403855146c4e02c6681c500940798404000d010f074000313802030b0300c2d041c0d04022560341c8090302403856078840c0c4005018140400100c0103403103080400c01a0f445401850302c081c144851701000b00c112003144003504900d40c0380d41210144003d4a003d40006141380004c10148000c0e002030102d03115030f0800302004c050030390101da1140d01c91030001881c541d44020710343e2141d60040b082002000300c01c1a0103050ba050201c0a512446040c15040758180001003034129480d01c11180300b00619000100040b20361a4207010b014800c010f80c42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987621178 1250 987619928 987619937
    0x1030b060d020f040203090a0f0c090c080121031b060603140607080a0507021204060804150608100506040605180106170f0109051e010b270f0607080424 67
    0x90124100500110700301c0e50002e2a115194841c401800003d40c0007514160450291000ca040070840001003914000c0c41546c0c1c01c1003091500710124100c5401000000030049054010083d0b01c11203080000e41c1d48140d407e9515000503480c0c01c3d43d10441140080c08410910120f04080c0102070b44a40d045a015605500314440300350b0991f510b50108407020310108604c0030102e0700c9d00c410307948103980c03100050044424a0035503040400d2540c000e640302a00084181c01080200401030103515445603082800384100da041141d200d48071100320002e02d00443d0340701d0004006948a40244000701800303003001c0904610f8841070743c0c0b400000d000e81c10114041201c0200e01c8600045401c2c82000d900b00c148045900b068041d101420014026207242812810b204c40032081e518803060013802c04200f42640c581c4510103540701c015145c000034203e200f41d5411305202c0c8d101e040c11000609000c6031801d41e94003407441c003040c5a020b15000303120320203082508005070002200b940355186040d03864 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987622428 1250 987621178 987621181
    0x20a02071202061605010608060a09020f0a051f0e0901060903021507110d030320030604060503031939020405151e060d0e0a211707090b1201030b 64
    0x88600040d034a800009421900130451a00c60961251a030800e5034854400401c01079a00c4081610302a800d231030a0a440e55034041040462411448401c03040c14280c0300c0703503c000d01e40b00008260850420004200b038040346810500140301f00c55545121000814100d55541c450300c3c024042c14043c04101e001c0d08150080c041150030400988180d582e01001c0aa005410f801c04d21000700c0249d2422014035847c0e1451440c040342549241c0d00405a020202d80c480c5840d4040100340c600b6030f40002d02a40040100d107034284000a110802e609035800c11125800400c00d4100c000f50114443e15805102090010010061a00220f480e2802101c0a03c4141c541700300c03142d030a40c05500c410383d0114011500c1540d200664922559500d8002d14180c00c3ca0100c0b5140001c1e50040003844165410550302c02d002c000e0000440104a00110b0760103180540c030344400380001c00305181c0c00030030310045070001d02c5543c41480c3c80c201403d00084556207c0201ea102c840140b082804112b9140440d0b80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987623678 1250 987622428 987622439
    0x30f06150305100e041709030d3f021308070803030109050a0b0105070308060f1306030b090d0f0e031e030a09050f0a2c07110c0d0b01062d0201020a0207 67
    0x760282994419213031444641c650b5a03c000d482c84503600043e00e01c84060100b80c0595030144420072004220b0348501c880b8080c40c180804400600d903040c0d10307404d1030903940340070509a80904551000c2e44540016911340c0c2503843c0c401d40c54a10381c0003201c0c0d44034005004c00c000d10044003070b50480f8481041400b00d074aa4020440079560381e00e01c064009103041c04020082071003964400e07044180a000109005081c01c0441c5044055001c4801d02c2500c4110410400006281503948481d5a038040c00c15200354120080a842c01e078840c22040040324404104a41d4091008030848100a001e41d50300c03d00001c06103850b500064015000305401000000b45814651203942d0009402001011040c1c1403c20507a050300007007000002c0e40c2210782d15030540c030b0501f454039400303274100b42c4036856216072a4a41502c1d01504a003118040c00718544804c00081c4000700c080c2c15128a41840308000003074105483c40080c500c00108800c1d1a0400781e081826010341c01048501040d45c01d03560402d4864 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987624928 1250 987623678 987623701
    0x60f031404020d0201030c0e13060608240d0305090d063306050d1e050609071805040207140d08100f21140a120e0306040c06050a030f06150305 63
    0x71100a90058504040d440041d80720303900c221010400c0741408404400d11b030380400c4881003035420390100556a050280400d0743c00400c0c540d84500d0413440803003001d07146400c9454603145201c020740030303140a580745010140144140d0f6802030010b44081200c1006041400c0034024002901c12100028001d840003000c081c490300200c503000c041400c0d9043d1a01c42c2c01c0703819034015001e2803200c9030746080012071100c41a09034a4a001851800300d00c82c00d010040024200000d804001840728004180030000c050f640c08804680342110300603120312090810440303401c90381501916a01484070f003200b43c107812030703c41030103408851001140d294844891540c0d0120a000304004100b02000603005041105c850415030340c03180c800c8219002072000c40c0e0307240aa4041c0f04840000c0311070700800815901600741c0752440300c102d005010505064a9280700317603800f80034000800c54001405442d160107074014514141d8208000c0002981d14411040484103270f000760400642400041883e08454 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987626178 1250 987624928 987624931
    0x12150f040911090603010905070f0e0f090c09070c0b0412031a0603040f0f020901080d0f2111090a06080405011b0f0f031e0218033d0501060f0314 64
    0x49400c00b04104000300300558008010441030b41903484918002c00640305000200080000142540e502800e10ba10b10a011200600c1c0000c0400f5074400c22002540000e5100241c64065605000549548004540c1724215450207850403185800740020004c00305042c1c24100c403190740803c00340c1c08014450b02c541701c241d0701c007690003001400881c0210b041da1000c038120903c50070744030054100b40d901092003c50240d1040d600782c0c20034658602080e400500c3c0c1d80c03031001c0d0703403501e03910310381301e071091500c2c040281c01031250b10755500d148984005092008a55007440002c00318441c490380d0b281c00070101c10048404032455400c142050315031400c00940b80c0c980c0c202c50303143c2d0b0100691846084a00141418a4400b0180c0b21151000c400c0131140442c000d02d05404000341c1d6403030620340707a41c00c200c030030543d040d000368442c1480d240c00c1d00e60000c40741401966100011040f00340311070f03180003a4074000d0712080b80e40d103008000100da60b000b11041d2700316210340c0c505009040d4003a1220005490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987627428 1250 987626178 987626183
    0x130504231e0d0c060b0f1929030708060111120405130501030c0302101206330509040207020a3606050a0513090f05060711010b030c01030e0312150f0409 67
    0x2800340d500c000144243c0c1003c9075019001d00301a000421b11030025a0a403941c055400304007030a103006208101c0c42941b041421014104200120b500940303160f21144001000c43c1c003001944008250568400c40c03440c0d10403e40b150484109819440c1e00381019840f91103028461002c035007416103050b085018241c100ea4000b01424681480d5409002c1c80140b0000c4081c1001000b03110350b0f4402001d40b05a00150010300c00720b01307254411480d1140b4414103001030f43d1051024401d00b501d0150720100b100c3d40c410b400d80e800368481080b40302041e002d4000d50400c0c04030424130f913042283c3e01000400242d00e01c40004005002022990000080b5900c0c0d000d000d400400851083c000c0d4103044800440346000075000003450320403919007102c040c2c80703045d04542d1a0888000c0c084c0c5154040303c002105e0500e0b00c002c20032500300000190356441389136072490505885030103152082c00180b0039244225448400c2e001d06140964040030548000035486215409111200c401400c182c0700700021f10707a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987628678 1250 987627428 987627437
    0xc0e0a2d090503120c03180f100e0a05060a05100f0f0902091f0207080c0102010b0d1502071527020942030d020606130504231e0d 57
    0x90400c2110261620003815506480100805451060b103492014070a080f0641025100c1c10012000c25444c584001e051009a20241103e41c008130041095240c8a680703440001d085045015190b0a2031000034001e041401028204003a0b42d2854006078070071403512150651040d00c0d180d5083c4910304500402002c0b00740300d80103010304079840d40101120b101c01040c0700c0d200b03500c00d05881c0740c203880c140c9050010380009070100a103060070080c00040a80900082c40101d401e4408241002e4410b03a02600100100082c0c20b151000c640c101c400340f80c1c1101c083c000c1805043c030b0040142410300c222819180443c90101003022072411400941c030307801000d80005480312011450f4000d0140c854000c0e814070075107500303555281c90f076000c0c160102c0b44800200040c015000c00d424074410300901e8080d03401c85401c1004a40d24040300c034404c500d0159000846440c1c50402c55644142e150707144840354040303500d52103521400201904c020382c10301e91300100d15004419803510380306042a5080440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987629928 1250 987628678 987628751
    0x6020a030507140703022706090c120a2c0f011415011206060c0209011d01030206031801050103111e060a120b1c050d0207240c0c0e0a 59
    0xc00c43d240310b00000ea41c03401111191500d82d000102400b800c0060701b00311841c501c0f92240201c2200e00543da214908603005c503100e140c41c00301c160451244140c1054002960350008002c0310075540310058806100450300d103030b10703440c95096181c1b00c52007a000840348610304490417848014001d51101c40040010a4801c0e20748003050b1100e907100d0410342d4144000c421a070040e14500380310303a20041c0300940d24200c2c01681801406007121044c3c024416804804920141342901c1d07400c4541180c0c0e040c1d039016030b03d556105141e000f080054410741515400c1c071000106010001801c80c6191030116440301254400d0710704241003110079403540d80c0000060042844442c000c9102100440100b40007060092205000841054803404040700c440c00852100c1b00b4003108000916095640380011305070107040480c1c126042810300131240b0090711141d50720b074465105200400c1e145500440c0040940c1d205e00d011198800100c0708034002c82e1505200900080c4503101e1820300888201e01c54801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987631178 1250 987629928 987629933
    0xf010c05120618040501150f080a020609060d0203040c0302091e2205070b07120507080f0f091215090a1a1005120106090f0b130b13090309050a06020a030507 69
    0x1034200c010102c0f544054690000710340708044905007481288640d000007494151020004200d44aa400001d0081060181445020390000348894415011550030351100d09410010b142d521580c00c8800c030360b900100a0108011408204000340ca100b101d0bc0840e581d244100000760b514000089500038403000003052078080c101050504003903000311004402090703030712070500c0d1249650150080e071000017a283d050005402100c40000d20742d1074000d01e020b8203030316080d4080c002c1c803d4803200810001340842707402a00004440903618040c1c09d026044006900c0c40341c80740300c5907c500d03035000120307400901c0c1c69102260100440c1e501459144020180c070004d1200303524000c14000f180d50708620045903541e1138403400310f0000d82440c00861014146803407a400d0340c800f400341035480e0382804400034071551508818440c80312842000260740340071a000903034941c840c8a104503400c0c5041d1900050540c0940d0703076016540155642d90960342c0d5034000b01c1ea100710f03d180c054005030303050081c0d100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987632428 1250 987631178 987631207
    0x304060f0e04054507030b0115080121060c180509220804030f081b1501030602070c030b0c090a0f12080703090e1009050610020d030b0406090f050106020f010c05 71
    0x40303407404d1103c2c0044003001400340541010150b8000c035040d07881103004100b044541000140582440c20140c081307041498030191000d80180202212044401c1503030b0f00c5c001007402c1d4664026017101d014032495552250281484903048c040c004002c07001030300440c0d2400e01c0b00e000340c001d000b1070891412456001000c180d1036000070108448201d02008000082807900c110a0060b9005801080d9500d105002c1100421041080961181c004c070300c1c1d03810401d207400701050449420007000360ba07906452410010580140e0030003081d5038000000c0c01410166040902040d000c00d94503640e0311500c3d00f00a0386141818401c252000e62540706c070703600240115010380181c5119090913010703951284002d030003804080310742171a44819804104502c500d03c0c010150804016200c06a01600d1488000d495503d58482d01083c50340320004803043c2d464650000700246440750007002403603100c0340604043d000038462000184180c3e00d20a91101040c03160300c40141d459144c2c2890603100300c1c80d650 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987633678 1250 987632428 987632491
    0x80f070806220c0e07110c0102061b07141b0105040e0402060c0a051005060405180a08130b070501090219120213061502010c0f02031c1503050304060f0e0405 69
    0x208851140ca080c100241d40c0140f20809840301506070b004a00c4c0035140100150a101c030015140e50164620316075990b004038000b41c001f4084040318901e0030a41540311182d124404004040b43d03d0400200d03090701e0042007841c080d51a550324480700038000c030011034050280303000d4501e0125a42e004500180303002c800074200c0c914400c003914075192160f12068140000c41c1c41041401c2c2e21041003000074036051081a034810041965640c508c00901c0050360b9902505800402e43d0200040c1203a6990f0707503400840040c00004a075a42d075440300e00e480da001e0020490b0032030248188070b21000c0481988820035094901608040d4050380040d02004014104401c1544180d0341d510b4010034203115a071094040c0001039000071420210380540140ba00313500000c28421034000748403552412511090460220107035903404107605651200c0080300c0302d40b6610042143c0f00c0007a000503515041004540c4035220b80d00c0d424420341000f824801910340869203d400b482c0680700c2166224501800e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987634928 1250 987633678 987633721
    0xd020606011b031710050a03060506040b121c0905100e030f031c0b0411180a08061504200c0f0c011d0111100608010207060e150609040515010303030204080f070806 72
    0x12070b01c0311b9a54000c2490300e541c0c0d8005460b04c644030420400c45041c18010b9500d4264240d4003080050900010580c0341c504500102d60400c2d2500500920103105003521030240c400100169080c840c1c02c40060180c80d00031855a010b40251400b0b16040c50002c002d44800080d214100c2c0302401e004c08142e8028200c2d601005e922980e28402141020000c1010702003036411280c4070918421000e042152091241c0e1012500c0c0d400101046003442c101140808407200540700420040051012042c01c500c000c411400c48003001319100151400018937075416041d203034150307a0301c02c41da50011185072040c0000b80510910840318907032103500c1080800c11202d00700d01941e0303803001c4082e1400d040e560709070300000a070f82d000b082250a020080c4282d841d00c0075000c0003407807040c4c0e080e04946080140108124424003c0e20002002e100043c0329405a1003035042d00c0d107003e50785900d00900250402c1c061001540304040d00c110180000080120a03504031100401161b640c0400e0301c08492507003c04c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987636178 1250 987634928 987634951
    0x1b02060c0a0212040e01030614070e0409020a1a090109120c0302010f0302090307060908010b040203010e01090b121f180c0b0c1f0207050c01140412020d02030d020606011b0317 77
    0x207200d003442030040c00140032011340c05c110079490b40c200b160a0b103000c06c1005585040c0b00c130a00c020160841c441003000d1009440128140b1080e00010b03003510000d5020700d00c4100c2c00080300b0200c5440d00000c100500e002d032280d18880341c540030300d420200e440010041c070441d550b8a0500141d8060b107070314100180c091070050b1034641c1d1840032a05002c1540e0080d40070030300f40c42c0d09120001c001e015001d0b8200c03098408604640c509403083e00070000600ca403c5030b55640d00008802522500c1d000c0c140e0f10352071400c89000040340103d034030840c0010380c080c3c07409500c0e00c1040003440803031002000784039400c018020720fa070341400c1020b0500ea03c00703840d445003442a03800c8034040724200341c042000000070707840050301c0c5e140034100103007406010015241005041c61541e00312401c800140c40c01d941c5c8010031030103400d80510204034841d048400182d414450007101c80903803540020340e03a12441003a40c03010450181100c25030500d030351385480100428101e003000300900000b4541c2031f6000b031103072a8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987637428 1250 987636178 987636193
    0x105040e1509150f01031b032f21100212040212011b0e10080103020105071209050a06030501140415140a180c0f0e010c0b06030a0b010806101a22090e070501031b02060c0a02 76
    0xa01c3c01cad401e0f64000030215400b840c0d20028010030300004032a4034020744190700c1c05c5810740803c6000350300107000a104205040d400c83c0010030940c410902c0ea6500842c0903a000407002001d4018040000041e00c100d40599811401c0d44c804c4001f81d041366810303100c0c5410504548e9554116880d00c100c042d003009071038100040c1d6a65844d003c040102401d8500007001e50500211050f8100c07420860750103070741480c6440fa4101d00f100e0030780048400c000b50242900300d1b03540001c0d88418182d0700c071520126030102c40100d040e03050ba00500301c07050140c4070054450035124007562001d030410f2985020405403c140004600000300c01c40c1d0000c00201995100c241c2c50b9503c1c0c0c620002a000340d4155480441084100307d0019015006050030001e0307880c68041d800392031405840b0301c81c1c0d408a501081f00504405101c41c401d0f00b4064103810710188100724001010320780d164160711a2a0000e4281044e03041a0104500d0001d80c948180e40075054660f40c441003005070380c3c0081d016200f140324071107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987638678 1250 987637428 987637523
    0x16060c09270b130f0e011401060507050c0607061b0806212112070801150f030b0409050d121812050705070603060e0105040e1509150f01031b03 63
    0x1d080010603826503100203041004d41c040502110340818900e50035a1401024540c2d003103140f54041c3c1101d9207846c0690b41c944d5140381080c2050111044150001e002051440400986070018100d000c00d611280003038180340001201e5802040d02c083e500220004480000045c89000314070130142c00b00102c0344401254400c3c45d4904020b01c1401a4441001c1481110707992640400b58006025180441031755051005215117001d0142e0481d0610161141b0790031024040e80000c408a040188104810801c60620765103901d5071003c094000361446c40740e5180e01c1c103184901503002d030103194034110010840c1d8907035100050045c0c68405008040c0304150000f0700401c44a40030b480b00f682c012030301d40d00d800c1410303003c0d1030107170843ca2140c1e05285041c42015030000b000310440100f40c059a0f000e40307070303003d809040902803c148500101c2c00c0e001c010360b640c600700d051790480344540301c00d0702e0704100744114a84680c20ba0100030280000c006d0007091102c0685a02e2062848282e44005081e5905 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987639928 1250 987638678 987638689
    0xd1106132a14030c06030910020a032d05090d120e0703170703080a0207030507031808011401080f0d021504150c030905010507030510052416060c09270b 67
    0x703600c1444558a0b42a14400314101030108010341e0030250b517490300f9030500c1c5409648492800c0302c200d03505a4041101d0000c103200b6001107842821103481c202a01c60f100340e0031281d812045901c07122050070840424101c840026004030385c5c0c080e82e40c480d031030108413403c120050006041d080905105000010001c9542c2c03819142001d0503140c2880c1d6a0121460050300e40c1c41300814960780c840c814001100426080004c139088180d0603d04590340300c82502842e10446500d820003040c641c40c01003055040640d070204503050b90414000c4840010070020581d86e2441d401e840200180c200e0091012414500402d0a8200388182c0c0300c1100030041714501400c40b031082c240340c00003a8a5104280a029084c4101d940014485c0343c20f108a10f002d0200140ca00f005100c0c50b802400c000c1034803c0e540901486540c0034908218043d81d03241e142034084050401d1030030003964000e01c0d007140404800d0040c00c60703c0c1258004003a58012421841c40c070940d001c1d0781e031148000c05840c0c0900b900c003076491 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 987641178 1250 987639928 987640013
    0x190503011e0e030306060409051e071218030c08030705071205210907050d020d080307021c050a0e01050901020a050105040b0a06090b03120310030609050d110613 71
    0x1030401d40325200c40092455800d581c40c401c0b40e2001508104148010f42d181c400442d010f481e90b04101003030031340300c428403a460032246a000f119100444020b00a00a600041c550b1451902c0c0c941800b042c080c0c1d00b801d030b06501808030b004021540e0403005100264000c4051036110400d4201907090030070f1500c4510035680030310000000640c0001e1003000d41c1007005130f0021040c80d0b4950304d200901c0c040c0e0005a48a2140c0120787c841c014100e112011541c0f01403941c0c0c00180d00c904019100d003040103000e0340c0e074040301040640b4003030714040100c64907210318280c030f0007003000b50b540b41c0c3c2e08480700c0015074044d4020a642da045014195140300821400d02075180928440c80c0030b0740c1c0380d180c144a80c0c0c0c11540b480d008000c25500340b0359071054680c2d001403040c840c0d06203103501c01c0c0d0701c0c3c4420703881111003105580002c0085007003005036004d000010905006422194a980d201c1d0303002c00404ca902d6610441341c117005440d0342207411021440e001c02c040744c40501a001c031003c0300d030846c141407400b020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 987642428 1250 987641178 987641201
    0x90907112835090301180c0603140709090911061c110c1f060807060c0501230f040326060307050f0d0b150d060b092419050301 56
    0xc0303512a80e0100700402c40e0882c0300c141e00e0745800ba20551089003601010403002ea180c0b4a0010110340180503035030a41c044440034a00c0300d6881c102e040a0319104039004454412000400d20305a1040701e00362402411178820415646c0380c0000302d007442c850400801c04494107640d045204d494441d0b240d100c9500601080202018400003840b104603020140d80c1c001900122401080c0806002c4180c00611050003900650b5185040103403042c26000920781a0710884191142010005805802440710811503010303200070300035040702c800c1110003000450807440100700400d0016240f08201910150000c0c1f00346014400d04064200604200751583ca0800016114005000d034903d010414080100400d80d8003510f03860100000550ba9040c404010380b121031043c00003080c1101030080741d5401c0f5001403500c07201c9511418000000c00c440d050701030190242030003242c2c8015948015450130b0224000c05000951610b051040c0f1070714212582011924040c2e0210b0641da00b8055400c0000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 987643678 1250 987642428 987642493
    0x11203021009032d090e220b042a061d060c071701090b06090c0d0203011503050f01030804060c081b03070b160801060f1704080d0e0309090711 63
    0x30110f888201d6003080c03865804c1c1d40c3c988101c0d2800158100c1012403c980350300e42c3c1d070310040e610410954100405110300764600b10061030345030200304419400c903008501441d95003c9000da08040054010302220940c0902c2d084c4180400c4a107114400c4100c0c50782c1112640c0390140c1c004000304507107070001c507000c000039000110300340018020036810300f0340104070500903c030312015500e50205004000d0105800b460b0f1440c0003802c03130316081c011503103e24030481c0c04550360360b5541254440103101d07000510000b4204008501440403412084d8140c03504250f24902d8946000401d07200541d10140c1111074240074441100c1011540c6040f6844208400207141e5030106454100d83ca064014481c403a184c04010740a06a0350f4407015190550f002c03402c00014180c031110341076818524100e0701404440c040000c00040101400150000100030302c800e001d007210030345020b81c0301c4c002d400510b40c0007201c4500045210340301d000b084802c1500c8030241c030904051001e008101d105149010840740 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 987644928 1250 987643678 987643697
    0x301021b0d030b0316030b09030c07030501060e0711060705090a030803010b0a0e0a06080f0a0e1b1309051f180b1909032c03030c010f0f02030f01120302100903 70
    0x1c54150280f0704036a0004c9003d041c003c1d090f042801042e40e003034003000d080e030030981000480d501030400880e400c0040c1d203030486003600c1d543d1600601900d014001c4202c201e06550200714142d004e02c007080399090300100541a03998414600301e61940000c41d86640c080408080000401c86c02402107003c0c00f50404d503183d40c0c6c0c2ca041c20181000d000503401500807003244408005590b0311100c07058000942004400a40e290920054060810001c54032054007400e0300d02c408141c1b1210f0341600102c0c06481c0da946030311402c801a01195428a030180c055002124ae070304074801c841ca00709001c40202e040002d00c1e58102d400c00d280b490300b4036108075131030102c680078000c1240d404008060510740700e08060040c1030440ea00100b0b0000c8a100c24182c030030300b8114010594440c880001d82080d0050100da468070040500303140170b0f120035560342c2c1080b440d100b0503480c080094021607100c0d4044600700c0c943e1303902e090940410071507000001c0e0214040c002407900c0510950141000c0b060099a84038400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 987646178 1250 987644928 987644953
    0x7140622090906091109090607120b0402031e010603061d0417040303020d1218080304060e06150a0e07021c12050403080402040b2e021c03020c0609160506090301021b 73
    0x10020250303686c0c81807102c0e000b000107404d80065041c0c0c3c01440f614101c45100d44004884015191812800307500500100c200280c4080c0d022103001d14036442481468183d076903c606034111015401000c40d0201d0021000340d4140c04905031540040c4103541c1c4100c441c6004c510700713901c0c0d0031642040380143c10a0560f500c100c0c1d8441015041c010a070358040160301c88441450300c044490480c010221000440001c05002899000c10000030380b030000d4030010b2070103400b42816210780718542440b403a003004004c60401c00d0079640b40c1c440e0000d03400400c0e118540b410341d01001000000c0307a070200180745a4400004c5c1d40d41c01034034017075071080d128010301c1c1c1064810001582e51000314a4054050300241d070038100c3c1e110340380c104501c507036101c40148504135030400ca081400c4409190f4001d44000380106603294141d000740040c4a9840a0b2005034684042454035241a0640050282283c0784107004902c0c1140080c584150001c00052502440318082240740e1880c0d80348070307417035007004080211 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 987647428 1250 987646178 987646193
    0x30106030e070927110d0303021902060405072106060e060103110306150f04080a11090601020708060604111b0a0204061a07080c03091305090714062209090609 70
    0x34144a03801840007403903550b40b1203000403483c198203400c1c07681002d41d10288462259400c40559010744050700744446d60401501942c440c1745001d039030403082103000400f24404201980100c2e4001c01030908189400c1c4110808a40b40c110402e404c05a41c2c00c00c0c0008045201e07500042a111118040a1074203000243c104c0d03058491a4402c40070420420079295207403a0030042540003120100e8035008500d0030070829010f1a08001003520415140740107010380d000f0096500c103c01c481203009940c0d4170004980302c811a01c1150010340c001408078038241303800c3d0800210180c154003117900300395214800c0400000c807200001882c0e00544904403d48c24140510f5004e807106603506c400c41c0304140d9115101c5d10a11501801c0d0803c0801e82140c02c40040c4122545803500816030183c0c20501101140100410340d0750711410303ca804400034510120300d03120000100300030501424248041c0c41010300c00344c500c401c1d4509090254012580003258810702c0d607034501454000030180010303d428075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 987648678 1250 987647428 987647443
    0x140f07090b0f0a0c080f0406050711040e0601121104110307031506020d12090b0708250503160908371e030c0c0e09060a051006030b010c020303030106030e 68
    0x10500721040000c8549000311400311100300100e4603246203104141d0610301c2e01d41c0950900300070028070002c0c2c005000b030351040151145501aa680800c40c2c6104005c100440f10000e0740c0030226001040100a290b0300c04804403031190103030000400044404000078111001c004400511300c4000c400d02c00007a5040c41181002c000b200c406a2201d0300309040603586601065034142041a980c0d4400c01400301c41d000b44280c245d00008050240c188140044c1012408035100080c8007098810102d10328072042021401d54a152511841d546900d4850220148030300290000c1c02105000010040410007002c40d00d60159202c001031014184114a4804038026031855460103950036240030841600c0303c126000324000350510001c0c544d103815a0081e4100b040605020b221160001d1141c2081ea4254031445103082a6079155541443c6641190010703142101c0e0000700600900ca20340c0283d2012869001c1410031140d5150300d54002459548260010740009844140e811812041080b00e0b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 987649928 1250 987648678 987648689
    0xc06120e01060e01290a0819050606040303050903161e0602150c2506090c0603200c030c06131109070f030c050c010f0902010e240a03140f0709 63
    0x2031009500d410394503c59920f0600412540c039440c040e0b07240708100862080c0040300d2140c41145e850302407a54001d02107d070101c650380c40800754155454441c028900c140c42c841c0400401d15824207045407411035003600305c00c10998261288405038075260140c403070400000c12034254441a4203041090310f071050310007540a00295400141200f0f000c45a01100741d80c40440b0111254075140000480050b900c9180c1614600c80078650311403082c04029001004030901500c40e00400ca1303030300c60040302101c80003111404010100c50424901001000092030340c0744040c070440e0300340500a0707451400c3c05015200c959901c01c0d5044204100400550031001010044400344014078003420090100340c2006415410560746154001c02d9034001e005665458406900802500301e500c1045002810304000980c04a00e81d195203600a280404041149020009605400209140603100990406007444091580341c014031408400c0a208462103201c500c0311440007401c18240241a00b21641c210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 987651178 1250 987649928 987649931
    0x80109050c0f0f06071209050d050309030d05031510020f1e011503021806010c0b01120311010c2a080c060708010e0c03180c0301020d0212010b090a210c06120e01 71
    0x90700781c5940c508081c2c0d42940e4000d0680d88005007001811280f110440d08230030340c0945440040010b0100010290a40c51026422501544508003045d074607400122010b2002c1441e0b20b0722000d1506248042c0b826600440c01160310b03590444110506140b044901c001d5040014a10700007205000d00a00f42140d289e03260304000f0a00312340208040070b543d00d50129003e250315000c103500782d00c51000c07039110981081a203005542c551000c400c00765207201082c0e00083e01c1521841c00340e003040c454092880c83c2900c0f10b40200d081c41c144403048251000c1914452510384d200d9001140c0c0300001002e891620340c014152524040700b0241c503410040c1c114000b41c900702400c1040040d06642125084a00901d11001c03049909070f80d140340c0040c41e0300d129010750000c601d40030b800382240c01a242d40350329959029550380e02e490601015010740e004e51a4040c3c403100e030400a070580719486c6405120280880440c44400b40c68032652000743d940a0700018102c49030108040c02e00f03204000700200d00070b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 987652428 1250 987651178 987651199
    0x106050f0a050d11040f05090c0415050d0804080f250b032202100206090d1b0611130b0a080c1914161202060912041401030204080109050c0f 62
    0x32400400c500e0285038014103d41200c002070142110121404020050040c4002d0b0b44601500015087c01c0d1902500341c418443c40d03d0841ca4540548156110000d40d8249030a14081c10041c2c00090b050054401413010030002c95006418046254043c41a0005001603060025032030030307074001c60b0400085050032070700070300c0f20041d04004c6039000313868100415a112a1100820299099920000d41c0f04000884050b203041d00811198400c03055034054540040400d2400d89200c4103102c1c04208007840d08135400005120b583c01012518502d0000c2810301c8042018182d00003000e4011015404c0082440214160700607005603101c511016810b040845441490705651b044150003000c0c080120000e1071454840800e582c040741c1c40c0d009402c1001d026060500e0280c1031a910103006004106c0080e850500014030250381104c1520780528091400c1200b20811080702d4806040503020040003604450034050b0410050050028107500d44103c000c0000c01c44844a580d801074103c0c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 987653678 1250 987652428 987652459
    0xf120b07080c0f18040203072705010e1003140906090c04020c0d0e0424081005070215090c100e030c030111070308040609060213032a03150f020309010905010605 71
    0x83e911000425000161070703910006204001c0f9501c05981a0400c2c404810041c0b0a9401070082e170192501e518004000000301c010309411030000c1c0a0980410461520078603c0d080902000c9100d81c950b1500061500d05901c900d50340c900c00b9501388810340e008805025150b0010322511021714000c64085191034144054180c5501d103150325a402d00020744540c20003621245c11010400d8454680903400da10600a1414400924040c94005219003005014040d465103e07880c0580c00d10b40041c017002162504a00318004018a262654001c032040e60419440b100307440f56072141c035a12002c1101c070306034050502c0c11105200312442681051010043d100440045880035505071810425598860805a01502c040c50004102520001d250604000008000d000b900c0c81401002c40214100c160801c0e1400301c0c41c884502000321000c00c2000540080142140004815000c1403030490b401c502c0c4c0480e04104c070040e05a945600315a01000420301c81d500242a040382d03904490b84841 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 987654928 1250 987653678 987653701
    0x608010f030b09071809050139021f02030901150e16020109020a1202010801060507020a090902040e060709060207050102060405100c18080c131e0c090f120b0708 71
    0x901c0041e21032194040030825080d41400280080c200c1c800241448100d42c9000030020040c2203000e96035546094085454452005c00c841c15a4039082d41d04000c2c0840c011410303400138000b1450f10150710030280a004600310140d50072104a418803801600e07481c1103101142500d1018440e2801c1c120040c00500003103a419040d03d4210031040541c05016004c207901368010301c50042c0103948400012000a10903024100d40340145100303988854080c0d98031801910711340a40c40000358816078001c0c0c24000c5140582c07140e446203000600109a0081c1d0246141c00d0200070f0310790a000940450782404010303010004030000b82001c2c80244014641a100c0b03c0e1980280815000c510740c94140d400c001d580b28080d0302d4260f0000001e24900d0070342d907112040e038a800440225018015602200141d800343d8071403100b80c0d1b030701c521620041040c05643e0b03400806204405070140041204045107601ca881200341c06001d20800c0c1141c00d440701d041818090b50020001d80420500104100704c41010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 987656178 1250 987654928 987654959
    0xc0c05160509070c021e04060b0301080d090f06020c040f2409050c0a09090c0203131508010501050c0d081008070b0301080c040207031407050327040608031908061c030c0c060801 78
    0x1c03046c40c151000100c03001034080c10300c41c0d011500c12480400041031540d00440c8000c0320108541361094441c1e5a1240c640000420b80304403c0541c124281164050074a03400060100c44040e10003da0210403c800c0d40f9410003401c0800610b030011a02840b01540d1442095017001c500b0b404c0c40d081050900e8010002c1590b405110380c01500d0381c1c01450442c0c003c0054603500f210000044002c1a11000c007000f406011024810024060900010710341d4021421a80185910300c00340410140d10001524501000307805000d05143c0504006000c1900740100c101900000b6032203a5a07500d05080c25252505c10740d015032140f0310400100b000a40c2000f40524600d00842c007160711144242000b80c15030151028901e1a0810a0f010800040d0103002d4010014011102040084d071103101483e928000c00c0c0d850144c0a401290801903113011b001b480381c0c02400200000351101000904d0b0f42d000c2c040d0241200407034129142682044208100c41001d006107217012502e941c50030302c0e072101c004503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 987657428 1250 987656178 987656209
    0x6010b070204110f0c15010b0a0c080915041d15030c150c0a030306061106040c120204020c0d02010213080607050304110402160b0105030f011b030c0c05160509070c02 73
    0x60350310104140a1481c0309607010f002d0504503443c5c85421911105071902d00c10f12104848000c0c0d0b01c0080f0f0702d0b5034408160741140400380c3e20340400b0102580c07825440d42c2b00300c983c40d80c800440790303842c007110360300030002c03c081d0a1040c0d80d03401182c5480c05a04090710054402c072403948503600c00c1141610002280510740e5000c44201e041110303401c80030744942c450107400405c00e010708c40c43c441c00d140c0c164010804840007652040d01000d01031541030744070b48066900a0035554000720800a020452160b1600c00340001c2c00180b40c41c20940d051403501302c00d0191000035075000301c2e40341503540503c5109070013404000c01034116460001c3d0028007a220040005000005021410b051516554107841817000a6405c0384865807080c2003900c4a40000d00c112803181c030030081651106481801350111002045606203048401e140d0243c02030441c0400001c1044030f0280c0d150089801040888213101010a00c2180e03242004180300300310b42c0050500341444881b101180041c0c4421402c587c0741003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 987658678 1250 987657428 987657431
    0xc1e14070f033305151018050114040905010f0f0605070b040803040609020306042303070f12142d0406020303191b050d06050d05190323090a0806010b070204 69
    0x101000b18043c2c050107161500c0c03049280100308030304106843d0844032511011100f00904209810b0202c940d000c0a8540031030400c407000f410003140d4003c40b0b07101c10b0f6103041882c2c0745c1000d4945403c1c0302202c00903031222000300f161800c100100500c1c8407986024091134a050303440c0c07601c681c6500032003081c0584001c8c88984000002424400b1030752005040e20f5004003a50340314242401c00070041d00c1c0d90201406840c04803680300418040000890760030590015000384200c1581d100c00b03004a00504010052080303034160b50115000803c010025401041d8240a501d41500084141c03468103c0f10500049402c220a000242e000019203911046600c0030500801e0405100340c0030b0400340f0080b801d5040e01003901001507410102804461218541c00c00c961a582e008000f00c0d210030710006030598004d50102503c2c412409201d180050107400c1a610030030b0109903160501e103a598031181d0004000c0340254483c5042e40c000001468500c0081c005941001c4030856544907011000b8480da = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 987659928 1250 987658678 987658733
    0x20a0308190902040c1e030b030d0302030901020903070f06090509070909090515090a02090a02040b0f2d030403080f10210204050c03010e0f0106020307030c1e14070f03 74
    0x10580b90000448194058010f2080480c500c0000c0c2c110300c81c0c3c85684680c082c41064004401d0310030721400e00d034000c0081c000c04600801c00340c150300035070002d000d10314035540070850329206413001c10010000308861041e02c9510361424034014607064980d080b251040b0306030014003d0312a8066400380c1a600886000112000e603860010b141c00080044000c512514208120808601117aa02c0d070b02802903c210700280c0e81d04601808921990043d641d1021702401741e4410010502c0c040c000d05500184241d9405802071480031200824101002c280c1c0c0d00001000101135215109641001c0711410f85400c9082009040981107454060a602d40380c03541500307114440807a03821054281c0261041126003408000100340d42d200340200c0c0d580c003a080340403407584900311000a04840455010394144851130b03030100d415021103c005d480d142d90900c40001020411a0706005e850301c2044200d00e154048002a0304181c2c05510000000407580810000315000c1d102800403413036001c0c404e0995 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 987661178 1250 987659928 987659971
    0x4210512012304050f1801020f0d022b0504021c02030c010509061c020714030408070e06060c0f100c1b060e070b0304060b0a3c08030c0616020a0308 65
    0x3801c214441c8540c01404e08003484a010040030015008900403502091039841901d0081d00b82e00c240c100911071180d0030411402c520318540d019045000280c0c0c841c0b01007039045000c0101c96000c02205102003503480061004528150600140d0b003010848140d82e05401c5800180c1c0355800307003000e02e051100000e0214120b0f5144021543d20043d2200410507160740c5006220094111110441c1c10320760004801c180790070008192401c40ba0100001c0ca552030900400e02000351f4007510103500a5028002c1c3c4406d1003090120800310401c20004041403000c80d494038054911b000ea0010501c0b5542c40c4401100d50140f0045001c0340d04908041380440380700001510340b00c080e034031200d2812004010f000c10007079a5006503403101b004680050100b80c45944c0f0a0010344405080c642c04204c0d038200c0e218488003102000e0503043c40b0360805600c031ba59a05802e055521030100400c0a8110780108510f0120901054808404070310003000401440d5030042d181c4040505009105400c4903126181d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 987662428 1250 987661178 987661229
    0x50402130f3201050415060e03070315020a080f01080d1d03060f010e0c16060e0f03030126070e221e0303050601020a0213090c030b0421051201 63
    0x50002880c00b200350000906100030b1800180d880c000c92045103003000002e103443d00c1d028401c1406205246c100640303281440c1541e8031046c1d07601140e0980a43d00303001003c14402d07524151149032040780941d40d00c6001d00c0080040e00018a012039035606040180f0002e80c00140fa64251702403810031003c050103904334560301c40404500e4991500c194400c20500c8601031b13181c18101c0f850446001c0349130f100da41c08150b0074051017501c40b400d403540c1103598011071000e03000702c0d80c0380041c20103450803110f204403240d0039030f40f09802024040f046500b00000200032041002880445000642685401d2210510f40c220010700030158174040d0141d42041c82c1403001080c000035502031401e080400103004804581c5c881041e059001c28a40800240c40794008580c1101c050fa000f454038014159255640d402804070b00c0d4151040218110003000182e686c01d1900c0c00344c0d0103048001c3c000d0118112440510301003d451108105060007207030600c1c0c0b0551480c0d4191418034000d4042884503040560 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 987663678 1250 987662428 987662441
    0xd0c030e0604090902030f0d230d060e070207210212100509060703050f1003080a030e16170d0c0809040209030a0609020906060a02030324030a0602030a050a050402130f 74
    0x60740711074001000101c0ca1860360002c05424400e5040c2c0d02010710441c03003603450355070b43d48140000c40c1000c806005407849415088039146001c41ca49410044c410500c402201c40b1a00040c803410720803410b00c180036070100440d00041c02c54000c070034851010301008144c4006c0d0000000d011304032a4146e068620f0040c460071640c0d103150b91040000346840c1980c25a588000d60b800780c0403070b2506011034092030410900380e01c038010800141500342d00c3d5940344895540b040d814201096500d40118407a200248400c4680c610220420400a03037000c0e03204982081040042031240d100207102c0c0d0109400c11071004030190000c0c0465100c1c00c00e0f1011070003901c5980226a0b0601600040c102000500d9001c5d1a10500944900100740d03140800c1c403000340700e02010300300581d0052000450b00d196000c0320203c00302d1109070320140782064034086494500781d0b400403100e20382c0100802154840030312815921107441c80042c0311a04080c1c0128008440b094074060306a500d03204900800302d415003025 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 987664928 1250 987663678 987663707
    0x90603030e1c0f03031a0d050606010807020337020c010804081c0504080d0b010221070501061509031a070c15090b1302010801080102070506130c090603080a0806120d0c03 75
    0x5100183e894001c0c01000301c80040c2d0b2103044c120600f014030341403078417041c0034440d400002003059445203001074416103801410341c0218071042110316a42240702e1100b144090b1000070b000c1c505d01641c5860303413a04100c1212031003194024880032201d45e9110700c42d41d802603007144140d0707580d009540e4200070410400900801c100d0901090100304040100200000c0101d01410012400083d004903103502c04203110b4807504034030081c003041c0303201d2030340007403010b14850400001c8543d0703140b80c0a50400007101c3c0c2d40010800420040051016101402440e480b035402c0040c001e15029002504445801c00f001c0c080c03103007202d2155a000d0450780102c04280c2c21400c256a1440d0407000803200b8682101304900180902c8000550004140242c8500c0d682c00f0000d800c0c6a0b443c07004a400e0120714203816a07400410040001d99050f5038802d8a01450154200c1071380c0c1e41342020041e05c42d0300090312182c0a100c0104030343c18505808142c0148000d80e6141680d59280103040484d00e07400e581550 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 987666178 1250 987664928 987664943
    0x91f020c01081801181a0f18030702040608010c0807020a0203030d0e01290102070e0c03040f03050706140a06050d03020d080703150e06010206130804060c0f0501020a0305090601090603030e1c 84
    0x15405114a005d0903881061b1283d20309442d000c040c8010030300749070421f44d01c107104584200082030491038840000d6000301000d6046070b00f011500d0b000542610282e500200349030350b55201310b101c3e45500982c4030b5480350190008158101459000c651360380306108031051007130b40d02d11115442c20301c00c2d0880c4c280c4000854051400f4400382856401d45140541080d000d0302c20030700300207150090412200d100d064003034002c509540e0380f500c80e0302c0d511040240450811000704900400076901e40b04260070b0140d8070741e00100918019000300c0c1183c0150304007502c035280c1d2054540002e5400101c680130900c3c249851095501c03480d0003030b40904190440030b00e8140e055100483c2c806503c000591107654260b086440b5a101c00425211001040d1005841da00e000c0000740121030240154400151140c80c0715260101d80d900c9850072a0041246240007076140c506205080780c0401a89001d0f104428041181c985542d401418550802c03041e0340c003e0032410603040362582615803051403682c00a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 987667428 1250 987666178 987666191
    0x30605090c01030e010b01020a20090708041e0803160e0a09020c010c08010b07080a020312040501090b0106020c031b0607020d0b180a080306011d100203091f020c01081801 75
    0xc02a00c03403600e1101540000c1c6884492006030105000b21621240180c01500e412081c91321014448403e018902c04080b00190704440d0945501070b1591141c1030561b0746800c1410149000c010000c440f41842c170915100307100c83c002003006202140c0d04964101480000420001c0042d200128080c000703a901c40d002e00304c005031690540d00240888080e45000b003021034000b45003540c03204002e009000400760148401400107550b40b0040c92450f0450040724103016440c0c0348840c50b604119002c490a0351942e1240d4200400f03401c6040c00740044d400506200400000420741e984525541314520000248120720703c0e4480c075084803903458001d400c80002c2c044a0030007020050b4280d030030810760a0210303850940b011000c00c0d0403240340d5005604a1940d1031f800b004550550004420462445500b03043c152039075030304c0303a54100303c4100741c0155880f68059810082189135280502501d6000e041c4c254031015400304030301c400820242040b0500e6101c1d50781c0c440d1040301c88103481140c0c0d0719041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 987668678 1250 987667428 987667441
    0x1a03010b090d1b15111b2103040b0a030e01140a020d0b060304080c06070f142a060a0605010801053024091c0806061204080904050c0f1e04030605 64
    0x914641c2d2413001e0711100c9442850b60f450f5941c40d1804840c444400b40f521400042600d4200c0e2804441c0c0f0071455031000700000e2008460031070f4025400000d00d040002030010605d50180240c401c699444002001002408500c5076880c01e4010103807020940e00107400d1200c00c5055200c40e100500103080642c49180c145480d803401e900c040b0300c4000902c00c440024402d10f102c0d80204030351000e555210000290b00c00340c01e15180d000201080e800e040c1130008441c40c80310072600d5504031100c0707100403e40c1d400e0000c44101243c1139500040c1c100300e2440014440d40c0c03150398681d000744a24200b94002e81c0307140c1d84c030085a4080b103904004503005070501b6a404004104540e10344d02c01c0d0150400440d220180800d65480003001000d20300040d4a088504690150141903031103a0302032701c039070300e050030f14040c0c00c2d80e0042c1146d08590405000c207103081d00e410315120b12a48480041d00072850140c4580542c120383c01030181842c45154007542d9800c000d80e1650a40b802554028000d02c098140207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 987669928 1250 987668678 987668699
    0x3120513030b1803072f09040b01060f02070b090d05011d06040302011d0a02190f08031209011515090b070602120726130b09071a03010b090d1b 63
    0x1d4403481012450614010041e038800b10480345e9040d400361315880c4c02005801003907800b000c058416040500810722070020743d251450b28a2099218081d03c940790f41c1060400307009903581031604001c65008003c01c1c025102400e00300d41001e40e0465412001c1400c5241442c0506900c1051100c450046507102c40c021500203401d81c0103c4c0310303400078080750250b1920882020b1401c0c020380025440040318502600b004851902004109009820100d0f10b4200740b6040c2145580202e0302c540c0000780400100d00a00e8030140c02002d06002130207010044000911251080e00030f1401c20180d03450304035a4503016888400040501e401c90541761106400c0c520300035000040f4402d4008074200015405a00c40d128142210303040281e000e18010300c410542861100041442c1038100d40701c1ca908010030300f48000039200388000b500422505007069a100080489615034102e900c1040c00103114083d202001d5500c403200c20f840c40101030340d40341458000c00f001d403524160141b401c024040780d8130032070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 987671178 1250 987669928 987669931
    0x603030d150b07080a02070501170c0a0306150203040501031407021509030c1902030d03110f181c05120403211205070e1207080d0c1406090328080103120513030b 71
    0x1075020351f1646030380e0340015a070f4405003010801505030780500188082400310b0140c83c8155280c68000b9089031624070305000e48010400c54400741e4800b1800f040039603454050410b0200c0046801c41550400c50b001070b60350001c0c5121294200391880004036201c1003003065034401d501e90001c81c2c1c072001030902e90003081d01c490f0170140d02900440038550311460003402006018800c2d00c40c81450007001045900c04d0b1303000794801d192240902100c0b189507566815102c13808082a9079503207580d140500d4240c4c9030010400001101d07a00910080000c10003c1c031048a204280d405040c3e45940c01481c11038500003a00d810140252901050221082d401070142e1003200b41903440c02000051042d40d00d50341e070741318484c101c2154000300c3c0c100ca5852050b100c907050796200b00341b80040300810350405414160100c03103c22040d072003c2201880a14802ca0469054142800c05940c07880b580d007000340b400170140406041c0018226145140c148031ba82121140f400d1815007503d280c4c7c50307241520b0307074450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 987672428 1250 987671178 987671197
    0x1b1a091c0f1b080c010c080d14041109010e040503030406090201051215010e0d0c05130b1f020d1715240403202407080307020303040c08060603030d150b0708 69
    0x118200031650f0a4009010103442105849280000e0469500c00c5a154005a9a03044607510b84003000c42d45010301a000b4066841010024000400c0d402030041000d0140d002108000d814400c1c040418004021030b60841e40000c004101c3e43e81e20300050341c040c4200c4401000140317040c01082107001c1c1a04040c1286d0500f41d8600050f4070001d8100007070350039006c01c050001d680c0c0748010091071902c0f1041840c900b540e03d1001c681a070546001481d0100c980440001d07028110542002103607050201010041043c180702c08030710400e4406140c601c100816050205900d0b02254529a039407845402014040344d01241c45801002440c0b002904032344070445071000a9502884000a86403e03241c0e0341d00d000d00340c03003410f8100c50000d50941c01d1054044a85201c00c1261001003015032000f58403814194008503682c0c1801e2400c80300d01c00f419448a10582c01c40b0f000e100299402000303c4d844055154004507805030441e404a9260206502c00d401c1c4c0c4000080b8171040089403006000700a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 987673678 1250 987672428 987672473
    0x90319050909090304051008091002120a0b0108010e1825050102300708090d060b1f120b0102010f2307020c03060610020102161b1a091c0f 61
    0x21609071001d0f40c0c078000ca006d0f050748803900c1c18484d0040752041c1300d0b1643c0086180112101036402c0c0b0f805c0d03401c0342c0c4860620304110048104119055803a40900c454400c0207181103c0558035000445070700760000781210307240068154401c2d0300c0601c00c001507428144203402202416900c40b03881040d0b00b00b203120b220b0245c007504410000c05055900c80360034035aa165850300e9003e10050280083c0d80c131000b07088030350400c00c1c400c0d01b8030313901c038031003000115480350b103002030340e40840d0081200c80c00c1c0301e9003980c00912070540c040e80003650214040c000003410000104540c03d5050040c0c0c00f40804180410f411490029021940c207034407100d4403030324104150703400b04c1c680b103005003241c03903616015a254160b405400802c1c0c050520010002041c00300f0300c001410060280e0a144c0c5161220f031080e10f80300c890222400b0750b50107400030380004010300000e0610300c0d50030311450182c0d8022900c40501c10744c2220f107480d600c80000c604c05a0465030110042e446940546084458101303120342003c030b40b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 987674928 1250 987673678 987673681
    0xb040911070804061b05030309010b2115070306030209190b1c030c020604030503030a0b030f16030803090f06070513050109060c0b041704030602120f01031a090319050909 75
    0x2255001c850321140c00a096034540340c01c05400b6110380e101505904850241013000d130020801c14409140285a5413002040035040e1f40c080041e40c4100451003184814239002c0c01409500009404540e401e00c0ba00440040e07031003202c04e90040a490780082c1d0000d0300b110401005480900c441035251241160801100c0072403801e201c00005250b0942d155008445014000b00c1e0040c1c1c0c10078242803009018070314140d01d030742c0c443e03055402c10340c1c02c03404103034840b4608078442c035040c8940d411564001005040745100c2002d00344100925101c06460301c1000400304080c14030601004141a1b8501e08513401403c1030031000f0304a5004058140100421840c0800c00f580324801620448040d03544040d0036280036202c5030101e001c041c008035070f01682020a04060b582d048090b000075800b80100588034480384122490050004000d00312241d5a0700041c00001e40ca007134401001188080840170399614041d941d46548110500c0c90f208900381c19040400301d40c00301c01040e10840550304403120b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 987676178 1250 987674928 987674951
    0x1080f0601031b03020304150e100203060303161202060a1a1c020d120e0609011218201810170c03070f03061401030203120c0c15070c120203070302040908090a0b0409 73
    0x21a00c5202700c4250a4102c5480518224a19000ba6400501c000d050342e161002c0000da1440f41ca5440b6030844002c11007210042c0c0d074903011720070164030102c40d0005103c241c42072440801242d070b034070114030711512010802941042c1610034545503603038080c1ca4401c5019441c00e02000f180404000500028031054541406080900660f101c07648182c554800300c41c040701b14070010b03104104008002c20021003111010a0f503400000c84000e1568802080c0c0002080c20302486440c001c030340280a0003100140421207041c0d4498004452164002080ca03c0b00c50903038030304280005480551601c240000032601000000c540021240f1a282c20030010061000e44420b0010074403010398140c0204003c5800800c00c0030091401c540c1c02d8040e20050703404400050700c00444070000f6059020b01045610810580c02c0c41c142c042c04940081c0c2c6e603140400d50003c0c0e07480e80140002400386440e508d66804101c0c80303206441138184018071070030420b0b44032000820b10750420b20904e9103103428687e00c00034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 987677428 1250 987676178 987676181
    0xb241b0c0a0819030e010c0605010f05040b3319051c0c02070501030b0a08060f060906030601030804030f210c050d05120c031003080a0207060f08010501080f0601031b0302030415 78
    0xa0342108401010b0141c883c5480590b600780c4c59138a418144241e03005608000b44a51041d14041c08410b002d12030b05500302000c0c0b0003240c1030040b02ea4010002c2440c0c0e01030448000c400c0d000102e1049113060b0101d24881d2003401e080c0144c24019062940301c4140b81c994a0304100036009400c507204694250a000c020180182d0304544145000360b000042d00744042c1d4403d0f0080c1d0500741c0c0c043c081402c19582c45d00681e05c0c0203c100c941281c02c55060003803012603d801d49010b500000110010400c550462315114400d1185100c024014903980403c1d03400c06c2010005403d0301c068481003444114110103009c2d0100318004412a0103029030402c4501c024004e5050790100700901d41007100304c2d501c044c014001540003505040599040b40c00002c001480e000090651030794541c003a0200c9031900d40f01901c0d50800004110510941400610484e644001c1483c0c1c0b001030f51011b1000e40d07d0b10350042c0c00801da0303c2021203d0081e4201409140d5405400031401140709084100104048c0b045100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 987678678 1250 987677428 987677443
    0x110d051c0e0114031305212d040603090203100e0606120609120d0204031b1802040509070804060e060a09030e040e070b0d0b0a090b130b241b0c0a08 65
    0x8190b41840414005904041c000403040e200d10308541103100f14071003d605519122400c2c202d03032400001c0c01400301a1041144d0348010084501400454184066103040c0c0900c0c054001013364605000c1c1c195541041602094181c0b60000c0107403d114925581e01c0340e00842d0860300901c00150000c00301000040d589100d6080003000d4203036142000403060f050350052201c028a0b5800f80070102c0801e5401a07000d54104203007814400251804007070085203241c2e080f030b001c01c00e0300c1400104050340b00c02003201e50000c2d65141c1180d682eaa00d00c0c0c004010196409011100c2c0b14410402c0b400841d03e40c00000c44d50b000341c40d02c40302d1104030010081912007000b00c1200582094004000d51200071015002c68140c0080108881400b1030110314880c88681c04464020303103a94940a590615440d601410071010809004140740315000c111000540700341201004525847c01c29210003510540e83c0d8400b0600d15440808104034a199554110600d12031007440030980019100c41c0006110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 987679928 1250 987678678 987678707
    0x1c020703080f070e241e03010f0608040f0b19060b1b0604210210020c011e15051011060a020a02070b03160f09121208070507050604110d051c0e01 64
    0x103211030f506442c0c11800c2400600049204407a00b4021604840c1240540100030001b241e220ba03125854526409644051940000203004090040c40f02284c4200810540303541c024404041d06c0c0c940c0280b0290f01c1c21507004021515203080750106074108030b80f000b48440b2007171101000c002100c181100e610307031000303481c010318030142d100111003140c54441e0304021390301d11070060360121000040b0303450603a48107450315101651340e840070b20000c00c00c01c65914440c4600711401c021661501d21969080c0c5224010039101c0c200480d208c6280900c5034514140e424030780c0003070364000d0030f005844402035080b4a408901502039030002051103170124040d00d02c11510009100c60f001c2d600ca0301520303100b41186204003008814000851120341c3c2000c0d071a40f003480798070201c40b1010707054001410301c480902a1b2040101c100701f810007184d4006026500290000c84641c4007401030000141d02c10810b00d4018040e02813102030200d402ca591465076050040c5455240e0658860001199000c400d400e14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 987681178 1250 987679928 987679939
    0xc02030909040201051e071a1524040603050405060f0606030708042603040c0602031306030b06041d0403020f0c0a0306090f0215090307090b0a0b1c020703080f070e 72
    0x200305245441c240440d040350040c10f0092038134507030302c0c07000607030f10320054440f44540c1c4002401010003070546030400307013505003503042d150a00341000030400907000840c01e00e1040d040d404a4001c100d600e03405040c201c0c0c540f1143c2503a942d5681601074045d20048a0030f65803405500009171410a048107070501c90800280228a1540c5500042d16007050161040c0d5100c1c0800407908031902c0021800e03090b950850041070b0310b030b140600c0d1030180d03107101d604400c0c215081408220900740000d24040d0580d80d040c280803548140c8a40411107030300440d40002610110200b401d05191072001da02070103075000c0d900365942ca17425401c059658a114580440c0c001c220383c402000807600a6122789e49843c425100801c1c0d0400e60340019003159079060121801150005180384640717020003015000704040001803048007030328800034040d444188200c0d4003425001a90300555034220508104011a4080440d00c44006040081c0344070f404071102244849d007140811010b034081e080405c40481c00624 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 987682428 1250 987681178 987681187
    0x1090e01052b151a0103060b091e300102031005040e0c031c0f0c0f08220b04050f010503060d060c031d0a02012c1909050703050103020909010c0203 65
    0x14507801c01090100da082c15616500601c0c0b0001d40084140d0441405441c1c01284211424122180d030100c034801d40b03418146400030030020885c1c610107807800c051003125414010054a01a101d414203da00940d84c4040380750001c40d80441c0458483c2c48031906200703034400c901d18401d1002d00300e01c41524009000d008020b810030180c5041c3c5c002d0b006042501065950707041610021a103003c100b060000c8425910301000d0b00702d20780c00100c2c8140584145000302c0101c88640b0740c0f211143e1a65406002c41d500020380b170158050703080358048800300b6204d98800050303542c00781d030079942c00038024944188414008905590301c144c00342d03070045200030004840b5012980d100300042a40007035460506441c2d124a80701e00b842404103075285030010001d000c02d00540e100040c003002290035030b90b8520300c6d44001d101d44803072071000da84030303d4100303585402c2074408803003910700003010030384c005004a0706280810220303e07855004981200d00c2652103140c41c4d280c8103501800c3e10302c081c0403140140d00610 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 987683678 1250 987682428 987682459
    0x1091a090609030c0c15071208011701111603020c030303071d0406081c021e07051804051b0a090504030201200a0215040837020304030209070f021c0e01090e0105 71
    0x1250b60151204500c0087d1070105107680e00840c5028104004002c90115001040030320301d6407040102c07000c2528000c10040c901e0140c0b02240d03018140d5421562002001c602003018001c21400b459820000c0072a5120b20304603200522460500780c50300101602583c1d400624106400341c4000e480402001e014080c510f01000342071142c6a0b0114011072281c00941d00404000a824414507020040501825400c000501c180540d844102403000460074040002092020664621020103424020100c5040a000810541d980d0700320302c0d5158900400c7c8000c140d0154001c008020199003048021220350103052313018001c0189101c00f58012115606044c0d09202a240e4807511607414207052884d038245400c01d00301c00500802c1450a10a02441c030036118281840e1079203080d1004525090856010030a101c00c090181410300c1078452500308114000d00851005d0010300c0016580a0b02d804c034010b103039071440d0110340d01040c03108001088806d40c00007075605903403010f0b2024000f07040c0e54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 987684928 1250 987683678 987683689
    0x91104020a030b060a0f030b0a1a180907050324031b010507080403062412030e03011b1d0d0503030106080403121b140703170901091a090609030c0c 65
    0x10103003442090343e01d100d001d000356180c1c009030285031121341d01d207459108965001b82c101d5031080e0b200b41c440d82c0700040810205804c1c416a0342920310b0300001c56203c515511030352081d0b107459480d007684071152408101e54680d0140103940300f040c60311541000c103d03024411100c008030030398900d600b64020344103c14403001195103103413002c00189011341c5021026143c0710100c2c2c2180d08100c48243d142d00007102d00070400032074150051100740c00b040d00d03d441c1c810030b000b1801d8601001000c4c0550451200450b5400b9840b8002c15a4400f504200c816a40000104010314581408404082da44201e82090804c0100c07a20301560200c029803940c0d0800c10300b81c0340e10f80028000c80030046c14400e03810181100c0c0c0181c0719003010f803a101042007000c0c010f014050104488071819030001c14400100800c4d4804c00a0038008050b80341c200080c0ca0700d00c1d12501520714604080c0c1420b02d881d2142ca07000301000da00d280305140490030f581031a15106c403113645a02c01d06104401d1a845090108001e1412 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 987686178 1250 987684928 987684937
    0xa0519211a0d050d02010e031804181b030b090d0e0411041503050109050a1103070804020f0616050f240601020a061802040c2309060f070f05070909110402 68
    0x2030081d0360604808960020342220301c225011074490f088020082c002070340900030320701000c41e00c1001d07505185038410700e1860304aa400040b0320070342d21014101000f80d200b01086030788582042a4000700d440210012400c210240301c11116002800b0000f004180049064100c0001b907560f5081c070403841d04104409464980c0e14982d030036100704800146840c020f01403100420300c54901240d190314002001048490003040180e0346030400c0b028840c100904811a0ba000e20142054049900d450010803ca8540343c0740046e00000c0000d00c90134502d90074400c0051807485030003226036041d08400c000d41c5402160f04041c100040b000d6408800f0341d8800846030340182c2c1071040b030308010103980390300b13040d00c01c0502402203052444034a03000790b08250055011031100c07070600000b011500c00200c3c4005400280c0995509008110810159078400c100e40084640c144c01d140c88140d5400c00c0444810722820407241c80c03242050020780c3c04524003542e441c43341c100340080710161910041c44040d500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 987687428 1250 987686178 987686201
    0x1e0f0708070507150c06062913080f15060d050303010302130f02121905040305030105060d0b122b020706050903010f0903020309030d0806090c130b0a051921 69
    0x2c040f4045001222000741c0010710840c0d9440c0d81921900c2c0c2040c0381221110307080184040000c011010003101101c1d2a00340b50021000d10b00da84001c91001c40500d0615504180b820b402050f08141110310b00003101d210b90b402a0f00e81188a4540d2401c002d9001100000140590410b200400151410030058202c88600080120354a00340403042e5040f41c3c8000d8a1411418540080c80201410700d040000034000a0b0350800842c10240c8000d426804148a81c42c07140780c0c0091f1211116582e60440c5880c800060803260450200007081d680b105040840d00c040800424244080c0038220800036001170401d40180c102a410254212481c2e070009454603010340d21421a1003102c0d141344200c0c103440b4001c1d800b031519020341c22700b014240581c8134841d0040220400a01207147d4a2034050341c0c10640050541c3d40c0c6001c00a8203401c00322469005401c04c0c0d002256056000d0b03000310041010f100094040c1000b8404080d041e41c001d50050a40800c1c00ca0b0006070310003544042d40402c45204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 987688678 1250 987687428 987687433
    0x305070804081605090f01090c090e010e06121b0108040309080f0a0203010c0c02090c0a1713020a050d030806041d030c011d0d080c0a0504090504081e0f07080705 71
    0x886034542411030380c019888400c46500074560301001c2c41034104008003410301250913180606061100c11001c45043c0169000903660300d4000451600801011009094180c02c168440d07a4881c20000c0340842142c8040c000c0c228480d400c2c07620740010078004400314400c2c3c421050103411034011160300c40e0042086003846461040030640301c0041104643d008103c50007001000103510506003034036815290102800411100d8400603030300d4940c1158070203100c240150f00c8091b0202c04a940c030351070103c044007000d4141e05012b418041c00c4038800015000b0345004803451380c0c5001344101c060b0308480240c0054011408141c4900d400d42100c2030240c6442e5284011000c40165141141e222122040b40c680d910b0b800a48240b22401e4000d44c00e400800240020340a204800741c101040140f00c2907502000245c005412030080050768050031101904002515003403401030035691100c0019200786000840d160300c540414400c46081680c00b0402c0c5090a000b55103c00d4103410002c000c44207030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 987689928 1250 987688678 987688687
    0x20a030b130606122a050d0602070b0106020a050c060333060d0c1b020105030c070c1a0307110f0309010e0609041a09090102161202011b020f12040815040305 69
    0x80c0ea54000c0b24080c280002098032541c0c400e10b805202e0001010b105c482c3e090161000e01c1c404070b5681c0c040011518295644200707242d542c54a00002c0c41100d2000308030986801c0081107103039000400c0400030b4412000c40b28a50000b4041201a00088600194900f04100554507440c4140c060024020f11101c0550715240c0b02e02c001002034102c1c01ea6a4010750b80c0391a001c000c2503121400d0090440c20800c100d00c8000950002031282c40018080d245c500d60004041082003030542c90800141030040b039016510126404a072119442520440001804610814004800820905074480000008500d1f0104d90001520340107043d00810341d00200510848029898a0081804a6640ba010404e105001d03604200101002403e100702a80c0b042c84420485d1502801901410f40c1014541d1099040120100e0150800d49032000f1a40b540c0c0c409141c5950300041d040301d142c1041c42c242e405149803030070440024021441a20b40303580c04407100071113034089000307681e41040c06031800e07903c0c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 987691178 1250 987689928 987689933
    0x50924062b0803070e06070f02060304020a0b160204050903120601231801110a03020601180b041e050a110306060c070806010f0f09090206072d0f02041107020a030b13 73
    0xc40da01e0a40c1a51910750000c208100c181d03200d443c0c00040041110014102860303030703c03880120840038500a0041e40000b02141c250341d1003c4146c4020064960219510510420b45032215100004100d0185003420b002c18581d410200c207880103480c4004107802d40c1c3d0b50352401102c40f99040307c00551a04500071030801280c149600810180040b118101032551150b030004002072403050100e01c103900611030b0325001a074045881c2e8111421042045498414008040003d04050040ba80d0243c41d0150034030860707075543e801c8031103101c1c01c8038100a680e603005155000e84050101c6421900b100700005039481c50600041d10800d40d0030002c40c0c6a887c0c840c800103280034800c4c0c02c80800180b10003000c01c81a480542001d028161181041c8400c0c912640840d9941c040e40200a010000040d4506081032543d2130207404d42007d90119411030a00d41840040c1e0b40f940036050f4001c5081500d5a01031007442e40c2159101540503020307542092854490300e88198028041101d80c095140040c0c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 987692428 1250 987691178 987691249
    0xa030c11030706180902030c1909120609230a0305030a14040f0506070e130e120a170c030103050a030f030b031002030106020c030d05180a0f030605092406 68
    0xb803c1c013074035840340d1320101581e10010322a103688164215801041002103c4c1040c4081d034440442c2034094540c10540385034165103410458000031107940b4804070140a202c41c607005411414020403003083c2d40c0c23003045d09d900301480c00d20701902c0480e8048641d090020303100f00002c40d40462401c9002032940341c0b0340c0c10555182400d4805458000005031040c052000038454550820410f003030501c405501d0f2004144200e1064159200090b580c070908042040c040c80301401c081d102500107035803251100c90182c90b20172050344041c1d40039858130014600305c0c1d11400b00d0303060302e40060041c51002d03d143c0c1d0854400c140b4a00150805460b02c0c0403031000e4608000c0d1907014012828090b0f1650b041490003440c000c0504c5540d4402c1d84075900d03000600750440700300c3e40e0030030682c246070701d4045840d80810b80340c1140381d100301140d02e42c441c00001800000e50110703008041300826a290b00c0000080c3c1000e40d4404a1000b046a50303070000f249003490009074030300c10182d50400b1410707801e810807010312 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 987693678 1250 987692428 987692443
    0x30c0f092409261b030c06030414010509010510090e030d090c0e010b090103050610201905010207020f060406091e09050f07080702341208070606060806030a030c1103 73
    0x4003032514040343c02c0d02d050140a1000c8441100101e00c40340444200041d98034540c00180c0c502500000010809104000414048003000c1400074041c90601500e4a03000300002c95074084a503c10520100b11448180602c2407940c0c0d52000541c2030101c10034002000b0040c110007295a0f14552200107404003510f01031714000d1481150481e03c909908001400350b0300010582845440380580010141d41c0040c6108a5200104400d4004962218002740750160090002000c0c40c20501950100031054000b00a207a100751669900705407041709000aa0045000d41401301f0380c1d0200600981400006d44d1118000754094808050398880e41d43c401c0318001e40e0601c2d1005044010400403641100d10b4540004540c07009202c0980544040c0501c1001a03040708009030911243c884d4001c01102c961000d00b0262840041000c9186800c203055401500d08844050501c213000800394000c2d48514482c040103409030000c40d0721903400b25951210100120b6000402201601d2243c07010080c58 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 987694928 1250 987693678 987693719
    0x1406100306031a19020309060711070807030503030604111c02090612010303110d1d1201110f041d010f05010302090a09380321070f03030c0f092409 65
    0xf4419080128a0000c0d42ca1840507941d4010b0042090014440c0001403265001c200e13841c1200001d80585a4582490300a40c800720041c80341d81004028420080003c40c0a0041141c0401c080d0380f0841c230690305409080c000202003004c40805242c200c04540041008100042c255481c0c400840a001000202a042500001c002220004000c001048403000c075402500704000c00a01001e0400040c142001b0500d0081d03101924456072418250000300e4503011201c0c2e82d5860361503c5815121b50f07040380c418108100b050383c1c0b914074445032070012a416503060070030f24000541814010340203544141c5015420119200c0f00040b6200075218000c007122144020b510041c0031101440e9035030a078200203000d03284054480f00402d91700040c6080036054210030f400401d00790580c0d135002d07a000b140005420200b6510003801003660587c00009000c0e815110450013130a280740c2262804400d014048612070a004580d648440b003440d001041800341ca0825299a05c03003a0714018101210f00c00b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 987696178 1250 987694928 987694973
    0xa140a170c0d0305010f0603020d0204150c120908030706050705090a0603062c010e040201110616110a0231021b19050718110a1110140610030603 64
    0x20400841d400380b00707102c9458910300d030522043d414240c0da42100800e903c17990082c1a40040c20800307102c0b180d0107903401480080d000380034425400c28040c040b501070740800c85d07030494030801d0040d42d54000c1480e4000c3c1d80e41d00b0000c606208c110350301c40c0000c1030302800c04810f001c0240856482540c5070300064000c0c110b1660040b4040b481c1c1203100c40030341d0340e8050303000c00f0a106494100c21018007180c1c0f1340c11035100c548403804a0711240010390b11301000b038562041c14005c1c40104554200e40140c1c03440b60f80c01c55a41d0040c02d4000e0204c441d02c8580c8203600079480400c4401c108501040207510521180304291750711803812000100b0703012a44405803042c080d06410f400c040b44141d05000c0fa0309100c0c0f0742c800301640c3c10b00390b69510340c8807500e41c021441030403004800400c202107554420240b0b4402403490039034138110048081c185100070b4009122902c21441d8029141c1c816000329044014848201c040c1600d4410800c64150703450f0720070000300341d034412002011420044200030101c03000a107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 987697428 1250 987696178 987696187
    0x3060108330a060e0303160303201206040507020604120318060504061a060a260112050c1e24040f090c090308041503060305060a020d0e0106080a140a17 67
    0x42c000540741a5002505100312403000c0b050319100842110030f104a0481500506801403905130000c0564518061540e00c2d20741c0780c08480000c5100a029074420142da002c1d890f6140003c11041e01c2044a0450042e00244049000226000395500001d4418100410a611038a11003e14500c81c808c00740c034219101e20130302c01408170600c14265a000700e241c05d180c107141107030007081c007500c20445080c081100034400e2410b02e40c40542c03860801210304580384102e580d520b009920343c001002c000c7c1d078075026a9a1074600e034900341e00b000100a03140600003009541308410081c03100340022100741086054641000b0340910307040100050b042c51140702040c241048991401c80c0c034103074020014880403100a101042c1c10300c0a440499801010340490301d550400704078003800403548020712a00c507031001e0149240300c64016011b40f854588081120f4042c00381d00e0750903550644928000d640101840c80042104001c4200000280100319440b004032507843c48160704120440080b074002c0841c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 987698678 1250 987697428 987697531
    0xd06020f0d060807031a0405030415050a0f031e09051e0604031e0801030809040b100f0e0117040303200c01271a150307080a111503060108 61
    0xc6a1400b8181c1d02c1c00801545045da507408882c07a0140b40340842140024001a04010042003103c1c060080008000701c01c145000c4040d1154000741c103001c0114804048000c3c26900c00c2c4600e4243c10302030f640e406880c41000254000405208100303481341d0049008920303800700001c223a5240c00100d00000c210070f15044c1002480b0508004960100c000c0380068910b80b00e03408030000b419250015006941c0781c5100d00020018480301c0780c8580c03c0008a40c1c034119258000c03800c45d03031200f465210f540350720280c60011200704466050401a019400d4003140c040303442070707003d070030041e51003000100810706140c044103550b0031000542d880c0382c0d1503090321500303108114070308450283c050480045a800650f502402e000e966205544c038412601c00007660001509200c28003940042c081e2081c0c0d6403100c00c034688540b0101ca0035209000301c002100c40d00c1c1001048100d003a520140a58210340701c4400440740e0b1000035100440c0301e0307405a2030040100000042c1c491140da04040307520700c801d088 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 987699928 1250 987698678 987698681
    0x705071d010f1d0a091202010c020f190b0604060f0b07020f0f0612061906030501090e0d0c030311091c0302010c020d1b06020d0203070c06060b0307120b0d06020f0d 72
    0x16000385003000306030b0310704000015511641d0040c152003a469403641c0c1d51005520340050481e0b10001d80031200e0b44070180c0d401d98041d03012282c8050541d00742c3e10121801986c5599811555168200c405000c4180001044030003e5043d00308500500115a9a980c0c090344400380207143c000c8811480c1c0021130000714a0101e0030383c0d20300c190664440d403003a50013400103819030044031400016a42900001030040e43e8101d0312138112880c00d00e8810440f03454080003001400240500c0c0c0c942d5140c1451b025405d80c00060a403101d424a81d94180442074980e0100c01508180c41c0c0340d65001814401c00b1596581c1d44a568000104880160010156410000d00b0b441c00c5ca8ac0c04015500a08400c8428076030085903603d0050085a00d45c4da09105072030260000d2080c03400d15441ca43c40401480341c2168001102065280255401c1c0706d1745860fa8010308891005840410101c3d140000c03502140c2100c0d04001141c5d80020b00c26215400d694503071000703036403181000559070760001402040c0d42c000d6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 987701178 1250 987699928 987699931
    0x31205010603060f0e070212030c04050a14210c0d060903030b090f0109200304050f07060216051309020a03030e01030e060613270b100e09070b0c030705071d 69
    0xe20703062092130314040702540202d01d0f60003a40350348008000080d541600070041c8000c9103101840440c1c2d40c3c541248841140d40043c0a03441c800c2c945d01c007000402c031118013a4480d175408010541c00b03424440d820905900d1448201c0307407030302e03000740700000008c0d035211940c2040e03e50141001140201d03052400404a4000030307100c43c071400d80d4030141b10410000c2607006066032561400000c41c0c649031182414840d400c018900c040490002c200810803001051480d83c40030082d04a441080c3c646009a03250000d09201d0814201444420480d502e04800310f000305044101c0009030303054a81e00844d148006c00d800550204000318001985075030b15100708004020300d6009042203081000c000341090300d150348107502480d1220050440095006503010704d1541014241110006900c0c05545503d01165401030481508000190511840f440c8520070130348440646400740c02c00c0340540f4a42c10000d44400d03248814094200000d40070044040a00780b2001c805902d400d011700401c101520 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 987702428 1250 987701178 987701189
    0x1206031507030c141e03090a0c0305010606090e36100e07050109030b0f04140f0d0e0d030f0c0819090807050406030c0612091a1006021b0105070611040303120501 71
    0x10030010110b1485c42c1502076507105800c819590760f00e44803c01d0302c07071070040c24880103001c80d0481c10b8008100041540406c00f1900300b0303201c802c00590703280c041440c000070490f88410101d40030002d1a149081c820742c0c8072406900c1040c8521910000c0d0321b1a0324107103500310759603c880d03a500d0390a00681d00c10014000144000d01c1c0c05c1a84504594880d00e207150060241000d000a020201d42003289154a120f60924540102d44048084c2e40d48a030344d0b079200d00782c80d0340891014440744685040c0400d80d0658660107880e11100818034001c110381010f201c0c64140c0302d0f0042848a810410710700a25168501c070140c1e602c001c104d080203a2075003002510f50200d44100e140003c108001460a4900002c81d0350350b0400740c1e0030048806c03409001d89041e80c402081d03e208080e00070301210f2146280c41c040c40d40102390343c1c2600c0c0c9a0500340c0e40d500f2042c0c280489111011034100103980320743c008051042c41004041403001f4000c0c00c0c420960481d03001100031480c03c0640884000b128444c0c58010b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 987703678 1250 987702428 987702467
    0xa0902060d0e1506060a20030919030c06050304020904030f020f030a0201090c0503071401120f020a050a030f050609011e03140c0123090d030201090b1f05040905031206031507030c 79
    0x4c440031009001c4102d01f11580f510b1100c01c006425002c9028800c0e0340d10400068011008140c4110841c00c0c10091400116020840303c000801c1d40341c4581306036840740e40d0180400480b138455032002e944170294040110114800c550010702000b40a20141c210450705400124035190786241c001c0d501030303007074001034002e50001c14204821070715143c803068258020f080c01400c1e0034681000b00003400b0032842c3c1410070f5000162070058203512000a02e02c61880f035600708915041911140b084c1ca034280e80582d48282c16800600000b5001900d114280449000182005030b036603594000041281100029980100e402c00e02075581050b02c2c22016a400c1010340d80030304180241402e280111641d1501442c000d03918402018001d6000030719858001c00140d5031440c04070500c201c01c2c620402c17070820103a401c0c100059682070501850416603072100c051400c0c0b96081e40c41107451200109050790500c150340d202405090b00c04151400351074580d5001c40c031f044d2600740240940c02144801403210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 987704928 1250 987703678 987703687
    0x6080c0d050a120909090302060604180b04060b0604051f1e0801061211030f19020a1202090409021305090106050901080c1011010e0304090b09010b030a0902060d0e150606 75
    0x1540454021034282c0d000c0c0c265000e01c0a107000450380c00313442d50401c0d0119807804140509158000450a01c103141c100d6090201c4100c0c04901d00d000c000d0920010070060354a8080340004030301e0b0304958015003001d4002c2c1d052036130310b00000c2c1540b038491b0710180000e40c0b041d43d940700c0103902407a40710110072204004600a2400c6900600c21300052042c1000c1004080e226442803500341c01c04589101e0405030942c80b81008441504580360a544015030115030344d080c078100c1a2140290b4444005588984810400c800100c101a60145501d02d9100c0c0e0f440000d04016a035100404401d8400004d00044515008502a01319840c1c1c0d0449031140c1c00c414010403403040d0018800c481c07803006031440711041030031750001d807514215100300d40c41035401c02000c5001e0f03107030005c098411125a00b60920403d01100c01340100030400380102c40c042c45041000410f00003083d00445002403011300020701d0314400b0000981221861a02504030340c00c559880d000900c01d450809400c0007040700c505180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 987706178 1250 987704928 987704933
    0x132003010812030901020d0903180f061b020f0d05100e011b1d0a120c09061202100509030714090601022d12030a0905060a02041d0603010207140106080c0d 68
    0x342c0090491880c82140000300003410120207406903404070204c0350701848808002c0c41d0250103818492409032a1300b5000c2c100050b0318610f0000c6c40704a50b21522041c485040c5c84641500310b031a8a2000c0c0d130082c1c4006500800d545640c0e161115184c0904060000c0c1200c5041c41002e646c01803a00d103440703a0400000c3c0c807400c0403002503d1b2030715005080440000d0106449060381c1a48422200c0e408180903200040700c105000c4000801807103046048072407602c41d90000d0495102d402040b100004212003a0018103040d022203941920b00c2c1000c41c1011107032000a40b601080d504444a15000e91b01010824188942003030b81144090020f84100500210010340044031401c1442061107081004505004140085030b5204104410b81d80d83c4c4c0361610707881026020b8144111241d2241d18006640a4643d109542c143c81801c1d2290078a040014040c552016028012a82c0741d50300700003607400290075400302c2201038441c100100360940b03866801030410342031074020f0f8002d80038034401000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 987707428 1250 987706178 987706183
    0x1a03091b06030f060f04090c0515040f121a0115030e010212040b0a0f050f2a040302090a0f050a0903020c030705061e040512010b0a1a0a0305151320030108 68
    0x3e00c501e01c82000d1101d55184400144800111000e158000e0303d000786507001d011640041c681991741c00d03616a640f200403c015114584143d100e541c045a0b100c144c240502c10815031000841070080081403030007400c180e065a8404000c0c3d02200c00460320016103c00e0319058041c685106610340d0003141032034443c81001c0254040100f0080c2040d00440015008060301c0d480b0300c0c4045460001003040e803908010300c1500c0c02c0280c51180800b20380e40c40c100d00341a4003034601840400c0140314641041c1c5103034280100c2d1803010700000c5580d911800c90700c010320814400d81d4032801c03581c1400709480d0450b007000fa04200300780ca00b245c0240c00150b000c2c00180c55150450b000084410003842010111003015055809240c200c5075024401c40d03c106c0715020705411501c40384000f26000c200855440080004c600200741c1c0500d42d40c6d10134003e6801c1c42d0b020742e1080c2e503c890410891240040d610f000903082da0b0075883c08901ca20b40d503d42111080994618600003072014415041c82c650400301840d9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 987708678 1250 987707428 987707431
    0xe0a06080309040b0109080d081005100f03020f071e02040c0e06070312060e04210f08071b05031b1204030203031213020a090c110109020112090c1a03091b0603 70
    0x24040c5481d80740c40a40c0d1792180b10395100a10046042c0c44210b1041a001801a001500c000810402d512004038951400711018403110142d030b210b041d8002078444040d4041e400070203241d0800c020601130b0301c0200d6000952480d802d01c100d14540903201141c8108030440b00928010010041c000c22001c040751907507000c440c40079406041c00c85000e2540f4055501030405a00300846606400040c4010041805030045003400780b4038460310f00d04140c40d4101c0700703d5407000c807460000b000760001c10071590142141074440c100e4420003615504282d110079203580e106040344030050460320b42c140f00c9101d051100300116000c6007400d40c5428910b400083d03803400340c00194404040c0040100344568480300445076125805402d00000303513030326000440182804081e000100e14503c021001c100818403405542035416190031071b02c0013000c44814002c0c44242001c481c52168000003280016482c005030444021b4080c0c00b5549142403004c007414805c0c1c03580444000021820450415514442502e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 987709928 1250 987708678 987708697
    0x50907061b080a051306050304020121021b160611070314160602070509060418061a040f1a0a230f04090b06091003050703110409080d060e0a060803 65
    0x10400945946044061507503a5100200668400201000d440b0f030000081c0030301e00366401e078115400717903500420340e098402124000c0c0003651740f400300d00c4030f050800d083c9040018904001401c046441484403d4208100c0c1829801c1c3d00c6480c240d004400010214009000700b441c000c4c1e00905c140301c0342d40d5601464040240b01c3d01c0c00743e101e2542c03803208112024031111041d0311032086981d41c0c07101039201c0c0140e024290007000c0c00b100094040c10f10740a01010034884241e01c2e00d0200300d6440c2c1d10000c02e5000441e850300090107040d036050303588900071482588000000011100140e41c02c802a041c848403403207018034046807003000000e15590a0b0640d04074442816058292208009421300075881c00d805d034010314001200003413044c12a00c95100d014180d8003104540c076aa80300740480c5c006440000e021344d01c250028000112040008515803001502c08190a1940d07524201c10f604041003c040a9583e000e0801074401700210980d0450b2541c1c1c002c111042c100701c0c050b5180e2003a507203035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 987711178 1250 987709928 987709937
    0xa1406090d111906080c190e01050c01060b040906060314071206170f070501030204150c060f110a02010b0603060f0f0a081617120307140405090414010507020105090706 74
    0x510522402ca004001c1d189401402401200c1c15001800d0701412280260000a400c4000040c590001c0000300c8600d526081c0f44102248440202281e29020481c04141006001e103e0003106038001d000d604003400359901800d49460821041d841202d45650228040506000580c04400c0108600d507811004134503240120090341000c4101500041d400401040b010900c1d0340501e07200801c520345020030741401da8007220b590790011070036070003103000c0d001c0c1001032802c182c10000e004d40c1400301940d11800000c907200e03445000b200700b1100401003100e000c0350009400344403141d082c403444100110440e07615045007090008924078102044240d402101d140d002000305a46040841d001406040c0c11100000101c401125580c0682c1c4111a81c5281010f804140c0c203401240c81030100c85040d0400307040d51303646501142ca08000c44c40224007000e0800001c40c140e115203187c40d100d140520044140c22005182103030840b07100400823011a4588000d000d0005408030b960703811034256180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 987712428 1250 987711178 987711199
    0x5010906080c120f060f01170109020c071203020a021314130204090f080c0d0e2b14030405090a14060f18010e04020a05030708030f03130209040c03020a140609 70
    0xb011003d108004507590548251000c0048240d0744000c450b105480556a402d0030289100c015078011802c00c044411010a0000601001d8425030140000f42400011100340c0c80d0703034a805100600500c0c01c241d0068001240d0401541810980451485120b0030204501b1229070607d080c502d02c05007074062601400c1580728190b5031030350024000c40da0404088000418146000c40d81c99104400d0740000340582459040310138029005c004042c0d001401c455844001c80710707034245068241602c400c2008440160b0404101d88484106084581d80025690340b42030000308032850100401081851b03040440c80360b80100f0b070014264001d0002c0c0c42d140141c8541c0e03800211280300d0700b101060241d48a400015440c05040250f90003180291640d540c010349803020306491701d51038052044550710030001624401d002c54004d40d4000001c501e188048000c0c2d03030005074541c4054a050300c46811102090042d89009003820b00244402c0c01e030f0f0000a0745107c08030342140904a25940305440058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 987713678 1250 987712428 987712441
    0xd03020a11060a0501081902060d02030702010e0616030605092215090b040611070c0e070509060708091f091806090e0f061f0e070908010e01240501090608 68
    0x400c1e451018419400360b0b42c0c24a410030403507008210900c03c00082e44602c40305107900c2c091041800c4030301600580514509400d61003440b010f54000b4140d001150f60320000544011014400c86001d600e002a410311500d4a1a400409803060ba400c114803412241c018005901c00c07140010020310000c4c44800c0b0031418a060060380396158141c0300010074100b00a6908003c44646142d110b00d100307000401c41543c03030340007000903401404801000361000540c05c0c400c00c0d1004041390382c0481d1906d091071401c8064004141c0075001139030109c44401010492078180d00d00305007084040044611240c90300008a80000c00091051144202244002c040d228405410313030400c60150040303410500184034802c104982c0c5420240d5600c80c43d02a84020410603200381604e80d40d45800944075100540c105840f090105001410003010b0150b00e010004203a2002e0145e00005040100000b0301c2940440d510081e4940b190403240601c40350200620181e070b04014100240c407190303c1c210806a031202c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 987714928 1250 987713678 987713687
    0x4032604061d07090207060f09080f0304050f01022106010f120c03020c191b0311010302220f060905010305040b07030b06040e0a09140a020915030312100e0f090d03020a 74
    0x21545001c0c24000e060f804500a803454005003035051159408010210480001004603100800000c0801d6002c00821441c040007a015540107401142669899000404002d089030302c04860454043c50684490390b420301e60350241680280c007820100c964a90142005040180c009501c464643d03a03039040104052195040e2160300d4a000101c6e0b40030000500c004022504012080b90013900da91104022090b521100ea011603500a11f0711156000140055010350006a5480f03010401c055114101250308030300c080042c002000451030b00c5d828911300a281c003445421860625090005020024540c8070038164014220301e800180c45100300c000507101d1046600c142c541d170004405018641d0103d074850504144121020802980300381c64081e01d4001c03680010b540209014005007502071004010740301e07210001e09491803c00f881000e10f5040c14180c46a82d2003010341c0d24240301c2e0f811000c25080c0c20407a003801c500c0c903920381800e03400d40e506e03030581c940c10401d40c01041c0b03a410b140c040d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 987716178 1250 987714928 987714971
    0x180f120a031b020d0f23033f04020a050f181b040b0406090f030b07031109060a0804050d0e0306150607140d03110901020d050903160602060403260406 66
    0x50004e02c080c0403038186075000700600c00b02500d1203520210840124901c207184c0c80f803080c1c01c5402841c1040303d4000744002888800081d040745e60b5580310650000407621401840410603d1403170b0205082070300611000d44099001180035581c0d4490041c520340c0d408410000d03103004850f89500d590b2b81c4502107007401c980d100300d09821581c00b040c04104d10900402400c00d0351180d0340c9040c000b81d40c42c051210384c103466100207001d00c0c64000c0485c45041c42500166940d20100c07041c540381040410218040360f011584480001302544c0a120401205200c10f848006c45c40c98800103516001c0002500c0301c4001d8080002c0072070a0800440a0f1101402e40c1c803941e400000c6030308081c07043c2c00201d4840302c0d2125444002484c200040d512811504141c990600d010f900501d0308000f01c0000396400d40c1316540c401d0381840343c45040d0100c2e100c085114005411950302600b06801c1034980a0b0a800c400030048410886030350511111500c080b02c071690140e0040c3c0701064451783c2c02c040e000c810b1072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 987717428 1250 987716178 987716183
    0xb03030c01050c04092a08060409080408150a021216020a06140114100e010e03420403080402060304110d05071a0f0301090209030f03180f120a031b 65
    0x2440104003005078100054021036001071420b011940301d0300810306c4035100c0500c19030700003840b499010140c6886010000d9200d00e003e4800116410703075459110440d00b1550119a45038003940003210120030800900b60081e035045c10540c145280c81c003030640b402030004c0c0b41c006242d240c000b000942d68400c101040f101600f19508000c0300043c0005450300e00024001d0082c01112500f201c1041d051014114941c0b0b0300f15130b5914103101001c00111040b101e0202900c0c0d140c4541d01c25070003044880c0810b40a150305072041015040c46a482034145540c901c00245c1c20700081e4003c120100e40c0141c03240d948554101e0303c0c0c1c0e41c1ca0740d0b1482e007030f44608903200010b500600d200c100174040141c0040d070a81900c242c1c02c0c0550030041c0544a000c0584544011103882242c00e100400c20312003150050a03800d10002c0c00e90320914140e00c4c5ea1403031508010240b84101481d18103642490901802268100e0303400d5034103405940c0102c0300030303584004840b0300600300f10350041e544641281820801c81c5259 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 987718678 1250 987717428 987717431
    0x161107120f0602030c0901260f06060403052a0a0f0e0408120412080603010c020c0904050703080309031801050a1b02150c0615030609060412030b060304030f0e19090b03030c01 77
    0x104084480f6080d0843d0b10047d0100780f00b035584200f81d01d40b0410b225140d0313010340c08402c2c180e031704c1032000707100c0c0000948580d81101003884041b0001c1c106000c55542000c404100c081d603035900030708030850400c1e0240024001c00c2980d00902c4000c0b2403a001505583d003110031720380c0c1d940311864804d00c01d108604c0c40e070003003540c480c090004002c28a880c40e00c01b6030003582c0c0c80f10251180010035088450040c0050056404407207540140d0915680180d030142c0504c0039030304216a283c44003410f9034011a6260b00175000060701c0a0307a040381a82c100c6d0010030a00c3d10300e0400996840203460718507954811007940404181d40c50841d510300c03292400b00348020122645410200d2451692141c0549510050700c2081d84154240d0074001409031107502c107840104444d40310341c0c4401c0f00200c045e4041c081055115241401035882c2c1600850007507120b541e99184048110400801034101020f144e4803560402401c8844401c0207101001a14124580001c070440c034040080d1551041b001d100100c2d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987719928 1250 987718678 987718681
    0x60b060d020a05131a0904090f050d0f11070f05040207020d120c0c091503080f0d110406080a0608070b0c010b180f0106050304030c030c0f05070e161107120f060203 72
    0x6a40300c009031900440013030441080b01d0b01c80c0d5500800f18415410050220b9040c4203c5040d4a4980c0080c504103010707621403070515502d52a01810030200020842c003180c42040c82034407003503208104583c880c2000d0b001d0300300c581c00c0c418108090303a1644503540c8525008103502c001e41da150313140c01c20034030360100c0d001c19103205030f203006801c0074004030b025190110848000070b05d00003107000300e011100c0c4100700a005203045a46805843d0044190030001d1307034040c0140300241c083d6115000c400b032182e03116541c1741d603d403540042041d0070040040c601c007414031104100012000450f08151030030004040d4541d01024005030062400b40100c0b13034080c0e84c156108131035480c040070340d501410030b4011000e556a06e9010607561440146e40c01030001d422401410b0101e0310404081000d80e106140f80d01c641a500d8603058544000b542042c0f0348259080248070012101042c103036250041800c2c400005a0507030344442d120141403242c103031903082030180d010400005282c4112038592022045403203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987721178 1250 987719928 987719947
    0x1206010e210c01020703050303070c0c0306050103060902040b03010c0c120201092111030c0a151814010606020c011205070e090106050d0b2b021225050f060403060b060d02 75
    0xa461804071010301e0240300740b010b50310f5202164030300c2920b030030200551031030f10742980132140c02044076010340300c400c50b1078400b0000444900849000f0760040d4408105243c0f540104000c607030800621038480d0385018045032201c1c1c0c101c4c44c0700308216004180924214407442c016400b40c83c20140c0141341000f621a103060981c9105800004c8a0b50b6640d008030a82807c00700700e030380b845038103070038a21580810610340c0002c1e1000f42481c01c4001954001c20207404161280940000b6910708940301d038021484a40c00c4c031024800c0100030030043c80140300400c003900018141d020011044210740303445100140c80a40100d04c000403c0300701415000d090740e51081e00401c250011450400050b05000f680c2c0110700e0000f0402000c114518882d40303071112400c04440140246200898000901030702001c0c0c0c0c840144543d1045050024464140c80070004865040c040150445481400c130b280c110349051703d5100503078080c2c1c0c1e4030000000f0101180300002d40c4901034000300141e804d00020b0310031803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987722428 1250 987721178 987721219
    0x6160201020903100e0d020102040b0f0c0a060c0f1202090604091a09040f15050c091012020f1309050f131403070c031e020609060a03060306020c07031a0c1206010e 72
    0x202440e0179019620b407600e107030000700c1c283d105a100c3d08040d8641845800443d000c14402855044200b004540301030050b5130303400080d40d454801000103c0e94051003c10b58680290b50100c0f2040c401c10110300e04401e150005103d4040e0b4003c00810a40d03c02c40c1a900880400032078051100c000c0c0350f015140b03403d01e0f00b5459465540412200c04103c440c003e00d011720240036507402100041d5209040103410424065445c40003801e1600b084400004004c20052a02c010180c00c03140c240c03c00c3c0e81d01c549861030b2410f11a1680424815841d000c10080080600799009401c526000b00c021804521802c0c0944910030b4400d00303150a0000046030010440c80060540c220391103002c007001007440202c202150340022600203500950204510741d981e01c3c0143c0100714000640c200000d90544903105d01e0100d801001020015620952042c000d00076085100d0300800300042c8803840d01d1a003003480d9007242c000c010301c408048030a5008141c1c1c5a025846d00c44441c1809000940341c2404140c8405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987723678 1250 987722428 987722441
    0xf0801180213030c18020403030801030b062d0109080610120c091803201e03120408040302090c130e070c0f0b010e15091b16210c02030616020102090310 67
    0x40041e41d4480e6902032445c8980251021280c154842c03605a038a1a150854050b20083c569540070405040940c0950007081400b401e54502001141c66000211700150062035543c221a50a9015004004402808100d00025a40c070604001c00c4080c080c07602030054001a000200e16a00b07051000540ca030603040e000c440e940c0203541d91100b60402c8183e41d1160301040c010406550854543c64000c5200100124101d1003090204e070720f400721681c41050114001e0394225091a0009020420344c5090320b0078581141104668070328000c401c5081d098050303118410743d1250030411000a203920300075243c031481240c2041078140503001500d8400c01c260802d004100d05003c0ca40c000c6a44040c5007400f0744807007180030b04034101940724020380c1c0000c4441241d5041a0b01e20801c00d001d6059811002080d00b1485031a080707011008003da81901d1007072080e030001c200300507280c038a400359600140300c2ea0448170a0103051200c4c01c2588080740a841a018829018482c40548032411421035010070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987724928 1250 987723678 987723689
    0x130b0d05040c0f0b18030c041a1e0a12030e040203010303032003010501020a150912020d09050105090109090903020109020405100e0f04030905010f05130320010f0801180213030c 78
    0x82e1035846001000103075a490085100302c4c2400d00600d20f03001c401c0e69190603d00402000c84610003140c4002400740c5114150f0804100394150600300c041c100b0080d001c18042600b070b000103000c0c1a10021403070b4071140d441591900244a1004d1050502a5607030720802c40000d0000d640d00e40e141d05026010780401050f69100420741060400200f03d0181a02d058a60590280452002503160100b4250400c01ea40740a42d80d1841500002658520800200c0380150060000455003410180c8020842d500c0241480800c1120b0f0465aa02100081c2500c586140000354a00039007022401007500700d20081d0424a00000e21021819070007440046480844500c1c0c2199201a5803080816081c0d40c020007242c3d41030018841d03903010f900000c41c1c504281c40d086042140444298224824552003980c0310502609080c2c42502682c4030071505807000e0900380c1d203181120000501c00c2a05100e4402030011510030300f818094143c046408501c001c1d0a100c0340c854990130011a29001446003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987726178 1250 987724928 987724943
    0x60f0d050a1e050108071208040504020301060225030201091214011119030908030c0304140d0c12020a021005031308041e0608010b0a080c09120a0c09021e130b0d0504 73
    0x20b15000d80030f0b080c140d51440700540421444c000c240c2450003407488003101e46078010b00000c54503072900d00c091802401079074010125040707840000c0d008407d040320308480d0219100002c0c03000d030b6001421170b4110703906000f091001c840030342407850600078004a175441d55401c01075905030020100c000342c054900301007040d10400da48000300b94119080c82e140189014414000111803d00d41c0e405543c2c0a40100762742c00a00c104c1412403410031060400342c001154800840b1030500407200b01c0581100400d0008200414041d000600180482d0004408208000000030254011141100b084640c0681d4442d201c2e41c490f626455030895a13514120030042400c0d00294040c4030b480c3e01c50484000140251030182100b0040341e9401006048649047c410444c0d80e1070340d154980701e8980700f0111000303082d02800300d244c0850b5101b940e5210b0807000f801032091030104945500540d55071071103400c0c0c5940d02d040b00ca400c40350a00301031740038010100022802c411848080d03040140314502c150362 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987727428 1250 987726178 987726221
    0xf02010507080d092109050d06090f1703011a07110f03010e0f030c0606010201020a0903030c02060702131e0e0c0418061506080c072d050615030c0d030806060f0d050a 73
    0x1106ca44910740308082d446410b0303810300004525240c0c800c03023009002c5c6000c45c1802907a42c5503400d5900152240320840b0394008010006002071390070005115020600051401d0a241c4501c2d000500000140703101e071149a011955545c1d095001ca8403004103801910f00e4a001e00800d02e03100e42014881c102c136401a500083d40f80d6206100f22120007921707403200805607040d030b1421a00b41175001800c070782001d010013803c00965181410060114050540462200111000f0503010050643c0c0c0c1442181020280c00f03460901003800003c0000c25200012203180c2468590101e06120300058842c0340ba1010381843c007a0419803440503a82e59032156030190b258000400782a103c0c03071038090452050109031044030130a07286003417403080443c02000015415516520308009013542e0710700c1500d04c090090740300ba040a010080c00e101003142c3d09040d4080396100608042c038004c183c0c0d480ba07000000d2003010101d4600584215492425040000b4900107540b20010031483c0081014a6000791 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987728678 1250 987727428 987727493
    0x90c0305091903140903011508010c2d02071802041e0803030a05090f0f0708100b1c02120f150c03041a0903040503030708030f010807030f02010507080d09 68
    0x5042c2811098421551454881e644003100c180507040b6003240c94800070844650304e564240100060007541950860645141031001c0d401c450105103503c040c0078001b2007524886594102400c0748154020b50401941420303542241040101d41001100c00c07407801130300c552030000d5030160058450142c0120b40c07044988007401c100122911038081c25910400000b034905119402a07a044006141107440380f425588400303040c484807502030101580310020401421500b005500ca01d0f800d010410000551341c1000b01b403184401d14000b03142d0380010302c074060440d241e0007050940d162a882c01c3d01c0c0c0340074403060b20f02d80f1032143c2c40c00009544401c102003404c13401a603044a000d40d0744280e2000d0448245480d0999507440200f600e041800144130000c1e55031024401000820300c640141c650304c0ca000c2586628604041c0c015003420b60040c10280005005400000d12064090909540720420703890328000c184a02050b44007001d050030541001c21120800d504e107142c2c600401a8402c40d010f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987729928 1250 987728678 987728683
    0x816170408210a032c0a0606090b0102100e0316080a020706051215030f0d0305240102030f090f1002030d0c1806110102040f060207090b0406060c020906120601090c030509 75
    0x140380d042c448104003a12a09002e54811000ca00c2c2e00001202c6000c02d0f00e01c42010b01640088002d000c1c0c1000444504120180c41032501030620200200412543d0500003035580a0405030301000310b503944256108505d04200ba540d01d070950030b41c0c0201c40803451900780020f4005020481c05882403001c003066a501800648003c144489500c400e03e07500d5070712210703046040b00003451705405541c2449021801c280314110a010031a140429642003160403070b40e441c150301c00f840602d614440d5050740300c1e0f82c1c080100c82c160350100c000503864204400014514a005100d8640d22803101711042000c1600803000e0992410700c80307401c000031400382d03c080d51200700714220001c02c0d001403a014001c0a0142c01143c2c240d26043d0700050a041e101d110580800009401c050050b9000c0a0b0402c40c560b0140a00200190b007544c0034040d00345086e501401e200300d0440024411210350340001d00c00d84500200000000700302c8111503441d6135034142e0710000e00182c0c01d140d0000b81414006200ba0100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987731178 1250 987729928 987729973
    0x542030109030c08210c0711030307033c08040b0a110d09140a0b01030506100f050d080c07090b01180b040608041506152a0816170408 59
    0x10384907006001c00070307654200540c1c0081c01008040c004072145e088441040022580f0074045210040d0b5101100c1c10b0840000445118161081e8820001d100000c0d41c407110035009042e18150300304003880c06803401e040c0d410000d01e403a0003004074034011001740c6a201d900b03180078174090707240c584042c1c40b00e081e08030550349141c8400305281000c02c03411440e01c078a035000c0c0b0100da00411b084c01c440d47c10f0301442410555001029240e072103104c0b00501c20700030148101c94000c150700b101f001c001071504281c0200402e0600c04c181c0b00d90399940c5502d0501071a00d08a500860710302c8207035950706880d04103e1000384002c16031240003407900145807004510040440081e0340921150606142c58007074101c84030071006108403400da002c00c04501c80c10710540107140241c081d6404803041c049003840020621100c1074003854054002103148051100c800030300b003404580000f03405a940809082400c04e500000d03500402035050043e456010105e024094070503a000502030303e40c01660443c984050a0b40f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987732428 1250 987731178 987731183
    0xe070216080303160e0609060313061112130f02060d050a0f0204050f0418080a0e011713172b0c08010501270b04032913060542030109 59
    0x21004501e078192805a0100d841d2200300411487c6016501408100c05070829a81c026009002181310020402c0c14040c181c01c102444a1391030a021a8404003a0f0182c4043c02010024240054410600c02d140310092000c03a00138184642d40c07005401c00b6801045c00302e484462142c90f00302d0409802e545070007104e0450704004d14030311404109804010080620445d002c030045500d60b007010006524034007030240d6491927290700401100e2b4a002416007511140d44202a044071410040801c0859010002c1580c10a5081c812441d042d64004611b108512400091030a00610300b41a8070300c20120010039007002c80306101050b51003001740c4030003000307000d243c0c080783c400200400300071400c4c0201c40c2c000c80000045114142e032024180d10303d50040d081642c9000c064900f0300041c04000403c0c3c0c40401c030f000070096507442e11040000225480c3c40c0f009050a450380c01103104000394541c0f0701c44200c00d000d49840c240d880d4507041404000269403d5001800b2042d00310024501031103082c240300e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987733678 1250 987732428 987732451
    0x1b050307050d0b101a04060f0905060a0804050a0213230f16020304030204050a0f050f0108072612130b0408030414040912030b130e250e070216080303 66
    0x602c2e40d6034a01000a00814003450200744140025526003100c01e10f044031466182400d5450f800d241e4018a0200707401d00e940107210310308004020f281c41d40b008031900005a0b02e4a0320481c0c41d20f00c0c0c91070a116241c1c2003c3d50000c03188404070f0516045610502e0842c81070b00305059003a04019110744800c0c81141e40340300588050001844641c000410309003560018819a40391986071360019044035400c0d00c2d101d2001d82c0d501c0212024041c1485019001001c1c0a5081c4a962610306403660b1a5154000c45a2000ca080105107012400003000e03107601084401b52601d02002c07054030b4000c6c0d000008406924087c010340062840c0007a01110117690903100654a41805c001000b031800a0058000360000da460355810042561003a03050b83c8000c15a4001c1007420814007008030720700c00241040d040510b4100300d2006200c0c00100c20401d50703c00d081c415180085598082a0000150b105080064000e810085032560210b690704100b80044603449800d0b442d0107095940e40012a02c600422 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987734928 1250 987733678 987733699
    0x10612050a0f020d050604061e1503020402090406180b011b0b27100e1606050403110a0810050f070f0509010324030f122a110d1b05030705 61
    0x40c00402c0040505400501a111002590f130750302031030030000b01e9007518215910008450060b055801c0401c5030007100701c0910801c0710b04013105050040610000744203542c000b40ca009992119003100000302402c108103038004040384510780207001407050640c00a0100c0b903151144441c100031054500d6007144100329039a1380c9200408405103072419144804140e02003580d04490300b009682014080c1000205a1000045405160401c00c0c20740d94980e02d01e00300d090280607846415038085a0304a000c41c07816000310408204600041c0c0c02c0321301036005030400030388260019080503000380500039201c0b21695410804417003888801a0340b0001031420006c082041d8400d400541c20100e022401207041c501184189001c80c10607401211a0454030341040c06110604061401032121410300c02c2104030010495440d880c825004c4140c0120550000018000c61080a00c84a0006010816642610709042c1c5005071240701e944040c111079400031955090100d621030403180003400c0e400d0704 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987736178 1250 987734928 987734933
    0x1b0705030715150e07140a2609030a030f02070506010b04140409020901092c0d0801090506030601050d03050c0a030903120e100507030c170a1205010602070314010b090414010612050a 80
    0x281007000d0704103400c01100d00c2d103400301034402000070808070456403140350481c100400c2c01e103006104520a03108e2040f80008019400d4008402c0700c00001c060700e40011030409483c00b80009015082010303041c1e124a00010629032041402041901c03e231030140c04011100301c3c104004ea5401190082d0400c0307a0000401030089a034011344960030500e1400c0409084d40b104260507003100d8208000f65911017080741000ca41c114081c5409460f0350701e0b09019519010000c00e54945041c8140790003a041c120300030b000d00d84240c0640e40060301e49001c1d56003000b00c41c240201020780500003983c2588030326607510183c9010741550008544040c2003014440f150b074006464a8210400c00d030144016074007030800040d54004020106c0100342510340c1c80f031003002d40080030301a011154400c92031070715005100194000a2040880358090b06461124021064503809095040c8009800c16480d0003403004000040b0a4041c6140c05200200304da569240d0141281c0500a1000380481c0c0200390000007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987737428 1250 987736178 987736199
    0x50301211e060902041407180e062e030c0f110a0b0603150a0f05060901030507030605280e060a060e010302060307112406010801050105121b070503071515 68
    0xa06034000c00d0b0000d0111055004078054510140b07803503980401c103004001c8410f400144000005104824080f481401c2401c0ea80e07080101415803445510240702d004d41d40c2c40c029040307403030701c3c038012040224150211030f019024048403150755001c0b5058082180945100e01c800814540006008126040f015160f0030044580644202c1e0940a610840d55004001d4400103000d0200c46400207641c0300c030310400c00704544020b408584500c0046004001141c40000d403402500d410100c009000e03201c0e500141d0030503d00907800052071404011000000c0074a511a207511a03070582030721011360b00e5000e0402220150301074009250b042200601c050705159014562260403401c050042074080556103103460980000c0fa4500300f5490082e91a00000e031144540000080c20f00c02500d5040c40000ba055010704a84454488122400030b9000b00000707881c810002c1411400c0d55480116052641d01c0f5400900e05640d41034000c500e41b40070380000d00c111600015528650041e06041c044240c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987738678 1250 987737428 987737483
    0x60a2609031b0115120b091f0c1e0f09090b150f040801050f1e31080c01060305010e1204030f0609082109060403050307111c05030121 59
    0x285940d642e114901c00843c58060320720291817205140d020304c503820728200c010b0034002003618005402540b60b0908102e60151441c441c00c850380408242c40c480d400301110000514109440002c1020404c0c58055030401c0400c2e2401c00c0d96507410f00c0c0300c0e48861041080c0d8025840280c0c0002c00f001180c1e242d0b148000103400c0852119612610700395035000024251002a00c3c05040d40f03030000148198140e4610741920b03c0004910030368440e2600c00c500c100c60004080081c00c2415407010340c0c030b0603c1803856200001903030040f1581d403690162a542c90091000f80000c96180d032034903a600d10b809000107903505401d0b50030300e62546040d0455582c0c9000880c10400ac4075102d03240c07002000001c0d00030001d45485911140035030f5104c1a445a0320035034600c0030700a500180c01034028807022941c440300f12940301c05d1504143d42444000e641103450f092846011030941d405003140c10900791340c04001141258004059039180745050302c0d411800d100801001441d52109036900b041c41215101c002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987739928 1250 987738678 987738727
    0x905060c07020406170c010207060206040201020304091d0f031b01060e06120f010204031a060105070b1609080609060907170607030b0a0b0c010506030d0c05100209040b060a260903 79
    0x108442e80d49044903110624404017100c11a00000079034225540d04121002c01800188000c1c0894141031300040d4880c401c60154120064988000e0082914480c140100c80c1e8001412104003103808880c4903125000f500320310101031860080ca00081005009601c15a4400c0289451984880003000000d0001c0b0707108012a004807c13040c50040400c1c40a40015030081c0036070b4106507007c0340c04007c1e02c00004c0c40c46041c408240702040c0404c03042c514041c0d04c80b25070366010b01030303088118041e01c40c085903600001e0544152400c001c8401d50104640d402411035004840c030b015200c9400c440d01c901c80381f1240d01035030710200000e8801442500702c0c00343c10b500a03001d48203c41c0c0340c0e800540c0c19032200c42e291049a446605100a40c01c00300000007a031000381c0780810128034503540700e9031220a03c1c103100c44003030340224514483c0d03036460340030000400c00181210350394110750350083d011110740c41c108a180c4903510900c078031b0240301400c1c4911540d40c140c0618504450807010461074029903000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987741178 1250 987739928 987739931
    0x20c0402090f0a0f030b0f070503130203030d06030c1a070203030d0c090b0403120807030b01020a06050901020405060309060405060622090c050a090204050a090b0d030c06140c0903060a0905060c070204 88
    0x2c103492502c610040d00302030981c1090340b9200a0860603d038030603480c040c1910040c0c940745020008021745c02000e50f50080c1e00c481d040c204010316400000d1446c007031002101c0303041d03142000000821010b078001c5811500112418141ca03a010310014044e80144400179405400801624807200709a0b4002e05078014a410080b2980e07071512261003150700180c0041352041014100080300e0f80c0c0020740c0c0395110383e82d407406011401c80d041c0000d4449011050040034151075401082e10300707000b0340685000d080d01a00d16500c0f491300b1440039507030b00802e4405480728001c42d000300f08036003042c12000005095070884101d0744c80d0082c00302c0f001001601c105640c0c02070f401501043c19591003440c20001c041d01b00000d0b840303900f41001c0007800d01c202d6224214592400c683c0c030085d03823a14092040c2c01f0740c05080c520a00405402c007440500002c580038061240c031013040086980740c030b80c09002e04034826004c6402c145d5823081c007401110307041003001d04264800c400140580c10000014800300707101030130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987742428 1250 987741178 987741199
    0x30f060c03090a0b01030809090609011a070804050316030b070f21021608040f05031c140d060303020a060b0d261308070303140f0301090231090516020c040209 70
    0xb03614084c04420313002110020f600054041403850505010342e00148120782c14134540d40340c185c02031800d40b0a665a0380010401098141c140101c0c0c0040d10300410000d0140c40b80c4112a07800091407450a0000300c0705c0d00e600c0d5020072401032203264201044904c80d2109030708900420710000c55508085010b014071602081031890200c11030400100385445440c11640791410100c0705000c01c1450307003205000c1d03449500c00440720442018022082c01003800d00030008116100400218400d0084175204181807410003c10075500080201045005060800007a0202c908104642440c00740240c22805003803c0d003034001c22500c0d4410345a1050742c001ca032402450410003070300c04402d1f50041d42c1a421440e003c02c04d15400540101115135102c5001e4502007008282080f580018081d03e0074255001c40c10b10fa240c41145091a07c16202c800c1214403410890710745071035030595004030b0070380740c0c02c140100384511440e6194948500c007a03000b902d45032141a05000094000c407102a034444e400e400f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987743678 1250 987742428 987742433
    0x10f0308280806030d020a21030b03030301060503070f09082a18060306060f060726031603060503010c0905061303230f0312040b0915160e030f060c03090a 68
    0x1003000007021080d44800c4028a441c208040c24200004001d40554010003c0d000002c2d030b401d44816400a40140c201c0059401081c2c2103008218602c8070b41d030503100000010410a40007030146214850030b03030311034001d0380b04603c040340c0d06041071054481e503038001e6414008211200e4a0401d0b03040100720030313034908140a4000380b101d50350b4003a0b080544411030184491390906220656211000340c41e980c00751450000455818030440388090311520700291309a01d014440390b00710b6035400c00e5000e101e40b81d080180d003920600b02207081c440042498101e000440e030030b060149501d11000ca44a00b6845441d1009104107688400070000002c8000c004c0400050207d40300051400115240e0044154000c0c6105141056000255010f50b00500103482c41e03807404090190b0080d80030855404c40e455915855140040d04022564854910b808010190740038080c80020502e05031b6541d100041d11f8020300d511100d80508441060b00720300c001803040d640c500e000b9500010a40102e4482c14003d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987744928 1250 987743678 987743737
    0x3040c151e0e060a030e0609071d070207030615090c020f0d03240e040b0c091302091f030b010e2b020117150a0b09130f0608070f0603050f010f0308 65
    0x134034030001199880c00340300115102000b030140d000260f14028201320b418034441c043c0202c0100c0301c0c011030490010004491610034042c0c1c00c021640b140b400d0101c43d2000c000311044010a000e00d1031890306c2c1c20b410b502d549100140081e207400d022000b50217858455481140905151002603092030b240c5101d1841c0d428071141108000c0080c1c190302400303130509182024644101410150b29180d0038003011403148e448030020485001180300041c1c0e01c141c071001160040a000c4103e02d20401c2c0000c0c3c42c0300550305504142d1110200b6a215012101c2d1501003102c00b40b1038110358043e00c09400e2560f0f40300e4810352010000b050050400d045170418080c940700c41c03058202c505824220120303481e107000b401c0c591a840007402001030024140307500072010442501c180d010031801e075525210300380401ca042c1e1f44510050f11288055450858464240d500481d40307605c90340f00004e1400001546008082c2c4c10181aa0000c00b4039048092458548a285420541c262042c03030660340a00004080d08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987746178 1250 987744928 987744937
    0x10e060d020307171504050a060b030a150501050c100c0c12090f0b0906070b150315040b10030c031403040e132d060203131703040c151e0e06 62
    0x942101680e40d190500005145100c882038080e8000e03d003109021708042d0340761100c0f1400134266000503c03640c1d0f240559000d01101ea0007585805000824000b030000150440e0b40c0c0020100c140f4600c640c2d46030700450340c078400e010311001141c0144600d518000c000390002c2c10b031207802d40b50000c082ca0154450301c0f000c1c0c1e41407509030040707175000404114108886698000400c84020070600f4a4200004a40f2070b2241c1c0c0801024001c00b5030006061052a00f2501c1102d500039085030140710020103910000c074000d80341911000c64502c0011400c5200e820302e04141d03030b4000445902d49142d1354031004c0d40d0809904c81c0c1c006010910000c1070b030b40c021944041c40382030102c1d07240b840a80117082c0311020010705000c1210505040441030b4003141308102180d80c95074460401a643d030782e680100100f400c8071101c0105480402d40002c01d59000200203580202d004540c4862619524400804000040700107000418800a440301d0110300e100a09600e882c01410b00011414a1800180703072a0f10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987747428 1250 987746178 987746197
    0xb03031b061f0b090a03060e0f060109020306150a031e060303170c0423060705030319050405060712020c0a0b16051314030a0c09090b0a05040b06040b010e06 69
    0x100c0c40380303590a90020864190007010102004a01c01ca009070310b115039200754010b0700c200b82d1001510150680b10311780c010000b940c05c03000c100043d2840300000c9490703e18240b04030240c1d2148100204800c455403084034000e10b00240258401340c5030000221250b0440d14804051503076440520140b440d9020304040100010800042c88a0852601902081c3c0119004442c5a403150402002c1840c000440702510b4034040001ca842000e4091091010420707466182c004401084440422000001440c003904515110f02000782e4180c1c0d0580c00c452085401801d694016400b060049001d07121020750032064074005850461490310b1180b42c00390303411044502280381d038200200c10b52142500c1c10a9003403860490b107072410b03241209455540ba07001d42c0c82c0802c000e00001d05c0da5501080103004103039000c80d00f0319025590314201c200800752074405550300c0d002040003403001c441910900c0d1003240d21691101417034548105000040100d800143d051003600300304c424843d50748030041d204840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987748678 1250 987747428 987747457
    0x60907140d0f0b0712020313031103070f0b07030b030d020c0103021c09030e030f07120813172518050910060803070c090e060a02070c170c030601061b02060d0b0303 72
    0x20190742c0203152002804170950b0b07142c41801404004811a203400000c59010325246038003c4003416401d0a40c8510f100023080310b00c030980321808000d0813001d014814400d07510200003072240030051540318100243d40400580200d000c411956010340e0141c0000039450403001c640352000301e070346011640c00391401e801081c03504000302d0322483c04000030082c0f003480002502c40d480c5050500b40c1d0680c03504d140107000000c00f04a80c005103c48081800090408080a42e001c0c2c007c180d1103904e174444007040c46009480888019102c1481002aa04680c59015503036003510b50141440018040500420418011201400d040c00c1e0319010b03200140c0100c901175940c0e07a8251800880d4100941d03c803200c0641420300c15080c41c440403483c15406414100c02503070320003d034642070350300e03011b41d070403089003071810380c10403e9460f500040140141400760222484d43c1d0b00c83c4019a0600124500000420847d00045005041c518050002101d60b040c3c00f0a401c008140028107603044010303170130b0106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987749928 1250 987748678 987748681
    0x405040f380d020d06091a01060c0809010f090b04060201021803061315021201171e060c07020d06060b130b0c0d08042901140102060907140d0f0b 64
    0x51115070a030400290008500d1615074402449854200303008989a40b003055450091000d5446140e40182a503520a01c10032007031040e072070725100d09440e00c415604000b030740070008105c0303038000d00f8600002c40d048080d081c1071003060301c01106e6000c00e05c5000e908024015900040c402a40c00150000e02680d40002d41c0f1040102d800840d0603401b8500036101c1c0d4405030030b201c0340c00d0711200b481401d0b81e00501d002013081a60915440644903490354003541034444000018034000ca405a0002d0111400079200800701191041e4803014210381c4030089504044082414000c00380018001548080c09009603100c0a458070002c8800340d5200c16550b101c0004c10140c0c48003c024544090440d0300012400c020504c01e2007541c2c0c940040d01e0f00c5c10300c1844000b080030b0103070003680c1454211407503904a403100e000380751286415100b80300d001da90500c0e862188010358000300f171a6125016090082410520b0042100c102411140003a1703045403001c0510004501c0c2c0300d0041805070b00410948005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987751178 1250 987749928 987749951
    0x14281416080c06040e06060708120702030d230f06040f1109030f03041d040f0803130507050409020303030c070303060807081b0607110d03030b2d0907050703050c01020405040f 77
    0x2000340c2d85100c42e00c60a0104400e01400050101030360300503106440319a141c8042d45040c540510581000311405100c100070444065800001880442d031004014070040d02010742c20301c0904030f40d03e21286194411307030000751888c07400070100b50f01180041000c107140d004011580308568141c090640c12010000d20803180d0f0804011410044034290004c6262600e44503540046010000707000b18856180350205040c000c01100b90760009411505080d0359080c0340004101120190307208a030030340140440010585081d02c1456612034000d0055485c42d81c0e0000e0701b040940c001d07881101403694800002c074241c14100400340103404058001d0040c911030024100054034400c14003489070504002480c000303400504240d81200c8107940c000002c2240340740507405483c180080c0c82e0040340c0c0c00e9041c000f0741c02034020b4288000440a050004d42802414003445400880d03418010034400c211807400a44030304001c100c08000c10b0001810300c3c0e20741c8000742c15035600155225000c4c0d140c2e0380d00e40a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987752428 1250 987751178 987751183
    0x20f3114060315010b0f2506060f060f0806030f0109030f09090c09031101021c050405150702060715090c0312030b03070302010909110d02030109091428141608 70
    0x208079004a0040501c0400c201c00a0034034041401007016000c0042480200c070441d04058564003041c0c0203141401c40c1c401c8118100c0d80a8644080d03e20900744000091102090301300c1c1310a40303003a90703900361030590f0702030040d17030811000752180d60948900070070001d6010080c80790305030b13a6111341c1d202070401030b2042c1c008013024a990044101d4514041000c040c0f0b980214005084a0740841004050f04503a00141d0610010700411044800ca8800844482c0e52102c01007054070001c607442400086651502552802800002900f0040c100300303503000703e60340702c0f48844c0c805800722012400d2413496a400c01d41c046a5441101d41c0220301d2070306002e07240c2601038806001c0041d4020300d08540f03160002028801c052082000042c0e0702c0c4034150006035100d007101d5520072000000e540d0b950792407803180d0092840c500141c5040c4a96032030440d00f100041880c0041940c01d0b40d29002000750600a4001c28118800450702031800d02040e10b1400f0042c030001001264032000714031030910b030060950 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987753678 1250 987752428 987752431
    0x6110c041e0c0509031501181b0c0303090c1e090506030d080402030f0318090f04050c060f090402040f06230f031510080402040c020a051506030139030207020f3114 72
    0x441003407d0407548080115840b070001c2710040c05142602840d0402d080a40c014002e0303080c05080040e0b03c02c00418031001d0000e112901800b20540034081c40d81d5011640111a030990b800c513130540011041c03000c1c6511034004550894001004e03140844d46070300069181d0303401042551018005003d00c2a1b00e0301c2c060100d5980041901c0746c41c605441c1641e034858030340c1e0910441d01c2c80f41c0000702d400001c0001003030a90f000c47d00d01610440d0382d652501840070000015210300c000048003481c04142c00c0400107410708203c0075008802d420400b500d040035405400080040c000603001c03607002d03451540c5042c10140d0400807515002c005040c240140f000759040c46802400b90740c4108031050002d04001801502004400101d0f0590707290040001c1c0134088480991a4800020300c001010f20310b06002c00300061590f40502480d0000c588083d0103034060003e019500050b02800c3e09541d007030602036807040508848003034441c00100101500e440305460042d806281e59094840e2040c170b65424400d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987754928 1250 987753678 987753719
    0x906030b01050d0201120c121a1504050607060c0210022a0c0117061207230d030903020618060301080d0e030109022b020a06110c041e0c0509031501 65
    0x750f0021500f40c0020706000440b07080c540100e580c50410300d8000e48100e141e0482c54a40020074040e00011103d040e0304000700100007031090b1114603145004008031412a8102d0364094030150400c01d003503c80c1c01c003c2c03007600011000e45c00388010b04042c2d92010f100a0083c040c90044054100304020291420034082100e50401c40d40480a4140f80340e8118109031107e0f0072513100160356668010100f841c1403000c1c4040170003403203000d402280743c01000f81e040c40039002c1070740100000c2600030104130500c001205c014001c502945018405400c000c5c0050010411001c22800f2a50300c410200d07455074000d03030144429802940c400030403154400e9140000100c1140244006545900020040204203ca2403042e1910401e0086040b0b44404068083c036002400300c0b00e600c0d542c010150a901f14140d000403903018201002415280c140700c1c20b5040012080c2403400842400c510600500405040d80c09000e800d0210204581e020422040380c0c0300c0001e04218503500d008420a0b0700c480c5520b90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987756178 1250 987754928 987754939
    0x280c080a150b040b091503160215040308041401150308090a0e1e1911130e040c03032703110312070503030403030207080909070e03060901022d0c070906030b0105 71
    0x10001c00c14a001070703d05503034451929698513000c0740b000030401c061411113414441000300c20800c1c074510380c40380f0041c8103078280c013541c1c1616411008120051400c0714000c0c0451314070400304011454034400300342c80040c580000160244107000c04090250254030480380c16000140c00c09040c2030081094009021030000c1601d02e06114450464040000f44005040801040020310380b01d084052011000d1072800100700100003a100300d0304039844601c0c4226003c50384400051800d001d000440e10668004102e4000181966421107214803d4001d03840c1680c42d048030403041c4c8140d0a5254002c501c41e0003000700c045001c00926080c543d0b980c00c8521540414003803600420404011a07074455454a80142d42d4801031403c500a806500003603034210301c50343c08100050b6001203010540440071002c440306036036008102402d03445052050b600d0380203007410225039400e0442c107580389401d004800d141400341504049280c55882d5001e01c00254440900704184000ca1301464003400090b1034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987757428 1250 987756178 987756221
    0x60b091906091a0d031404180b090103110d020118060201140901180b090a0f080c070e150f0a120c0e0c0a08040f0303060b040f0e061008280c080a 64
    0xd00c0f0070f290079862103c1d004a02c0d0790b0282040600c0fa00c0c0444144041e48074594a554640102100c00601408900c00e460700c0c1503101c10081c034100718a24100d80e40f0850030f0f98a4510402409900c0700c14a908134107109804a00d502031400c0c4d012400090021035000040400d030040c3c0844d56140050702d041b0076030745001c04890403006400c900300c2541d0381054040845444400800e0314040ea4150040c02600c1d08014000c1084102401800040c14120071141d9090b01c81c1c01d481c1049206484200490003100144041420300c03090307003140e0200c02401e00c0c0c1d04c1039581012a1500c83c00400c2210400126501808030381caa02640300d4011049161940c10006490405081060007500103015400c00070110070825100f600201301505100f82c10b144c6499888413802a180e07903a0160b0320354038124600040d45030400000303a0201d0709156403a2505078842005070a00c0b508499a000d50301803006c041e5070403040e00d9004030042d00e2103d5a8807140d5281c1b01107032404843d0f14003410100402882c0313 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987758678 1250 987757428 987757451
    0x6050a120c0503010e0c04121208070f1e020a06050a0905060f010303050d1d0106060801050a0b090f0d1509120e040504110906011b060203040311030a050a0507060b09190609 76
    0x580b8107540d0b045c4031442840d10307680082049402190310143c80031141d2a42c00081040141989078901060f40b10740c0600c1d2196070f01503e4040d42c5200d103000156084050010700e40c03040d40d920008039031600640c0c40314030440d11005c0945504641000c42d403074880e458030080220030403445520003800d10400c3c001e941941c0d401020307889500d48541141e51507103022084142c0054070f120120104100030482a6910480a813100780244501407103403000c41000a4500220022102c1d8020014000b019010030032040000c10414440140c1d90510103005283d20456a0321030441050300480c1c0c401c1b020f0030001801460051040c52079400390381400240000240d08020a090020048030840d2566a514004948405029524050060f52610a0000c0c09038035402903028070700a555041c00200c1d48240e241d56442400a0100082c20400004280b28401d038094000d15104d41303008500c00300654005143c8013030546881005100d410402c402d070411500c01d030b100138002c0c01d80134030000318070340c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987759928 1250 987758678 987758687
    0x1205030f06010c0c120b09070b1608070602090a08010227010c06051b1b01110906030f0c07080408030c060906010f2705010e090c0102030913090c03020a06050a120c 72
    0xa80103906120703603c814102088440a5554080c1034510f22141c0c00c4459030a12800c0e0720000e07079014240e8090b070386001c100c40a5141c00c480c1e060540754000204080c2940c2c45140302c0d4040001910200d41c00d10080602d9590160301600a0010b40c00140e25003034401c030903540310b90302055154004a0f1501040030705907003103e0040d90082e00034500003120f035100e50802e414400081c080141d0380701c0c009200b00007003180040710240c01104a000b0032880b091030440c0c141900c02c000c0580e070b01c040d081c070014504443e90603115a0004103960f46505101096544140b01e8100d074100144903000811082c6070180c0401c9140d500400d040010301040d450406c8208030310310345020f81e44003200360780c00f28070f24040c81c1d061150307002d00510000c00496035600480000e8442c182c50300112030040010340b2490390b00c0001603d084810041501c10003800303171420003006110080c021204ca01031000300002513074600d5480340041541d6103500740d60354101007008200456011000030128684040c080c42c06500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987761178 1250 987759928 987759931
    0xe0a0501140a020a0215070303150602060c030901020d0f022214040b01180e0714040f0918050d020d11070b03010501030203090a0b09240609041e05060a091205030f 72
    0x310741c29965240a80c1e00300d00b08a4090800b81d00b00058500e101044a040001018164001d6408006e00c0030210144002d02c15a8402d110047e40b020000c00d0b901c4105400460300001d010000501c0c14240b4100b03c020b07115080507024211b640485e012488101403020f200300515030f42c40f1605420304140b80041d42d00004030301d090146e591003580c1c0c0c41c85d900401c2c4c2c10000d01142500702c402c46950750314468810200310f402c0000030344029004508440004152810354010700e0040038bd035414400302400174130800c4c0f210691180c0e5260f500020403420b0017150b1040c002540a80103051100d0382c0a403039200103218000c96540058010001d000652050382e0640300246000f5a0320380f100c4015030310380030001c40040d20a180090602110403000a9440080b4030341c0901e048030a203020080d06003c00c0b088909035002000c1c00c0c000340c0014038080740803d030090b084804844845a0340c480340c0c0350034811103060030b2039550b61000c2c10a04c0040d24144207044014904140756150441d10043d10320300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987762428 1250 987761178 987761207
    0x507050a090b180915040b060a080f0c041211030601050f090103150204030b10030204050705030402100f12020a0206180102070503072603040f0c1a0405150c030a020a030e0a0501 78
    0x800714650000b01111043d904121400500c8581d02c0d0030950b5020110108880c40305129524080811141c0c0c2001c0044e9410604541c659540554480c6070880c05071100a00d106410081000f02240a00342100d42e100d0050103040301804d8a031800c4141032500006802040c403407400030a06283c199200f04070203065940c05240c4100c20401c2c51004400780c02a50402442e0441e0a010080107001514030801140e000300c13024441ca03140e80d43d0584040c40709840c06900700c5091b0100340c580e50b02a090400c42002c051419001d80c81da03200b0090b00300c0e0001c10000005800002c01e00918111140c2c2c188200c1e02920021031a0004603556141c0d00e216110006040c0000c000014031204c20040c2d149441150521016030340749400d24021390f10001d0000c0440e4400d83d000d03004120384216010060f440d0321011032003031030141003404100c1050f40c0703000900c404e80b00c10071880c0301c001c40510242449240d140c0042843c2082454090900c2c0017125620f8040e10042d501001180c1c0e00040038070803245c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987763678 1250 987762428 987762449
    0x708030c1216020604081c17040602030403020c0901142119050f160501180e1314010e0c03071a031506091537050a1b05100507050a09 59
    0x54034507960380d012100b0003401079800300e800701d0002040800400c1c80d0300c107003544046490000a4070b0409880b0b542c80b075000000b8012180b000140050382d96802150428001d004a41d065451400001c0186034243c104205c0e08400030303828840d50600d05000350542d407000d03640310981172844c58840c0e81ea0b110200103006c0000506100f500b80001031054100684514003031328030300304070034005080040c020b1203051700240030b016271580e14040304900d01c015211a540c0680b0992a04417090640784441e800030368107200c00301d01c4455030720024801c84120400e01800703082102c28031000c15080c02500c1e444002e03150141091082010346540031650310000284420840104010101b5aa4019040040d4102e4401c2490368803404c56030001d800e85044a0007158406400c1d240088840402e4810a052003a89034104411041c0507101030000d0610364580070080c030581200c4081d614800800650300e50b04100c1e1282c294500f60301860b54024480d0a05514209034203070001c00c80ca80c00d01c504460319 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987764928 1250 987763678 987763687
    0x14070b070c0b01081606020a1a0703060e0f0601022a0d170c250b090d02040b031005090c01030b0907030e0705060a120501050103270c0b0309030a020708030c12 70
    0x880c0111100020590410b50409442d03848410b20303569001036813080d45004d14a00710026405100041c410102ca41c043c80b010444038442c450307405481d1000e06840d041c19100c400c0454030400941d0290f210310f0b0b600d5500c5503941094800682041440c12031095501280d000040800404007800c80c040842514000300b04c00c01410150752400241003c0c1c1500400001e2201e14204002264100006840020648110034202c90050303507155124050303990406000500c214504001f10300440790001d80b0108000202c00300103801d082020444c091602d030f0382d0b018441c02034070810180b9104002824104175020f03041d00000c000c01c00040c40b000c101358880c40b203804410801e0000c0d800408010740803940322818020054000001c000c50300909501d8440000344030740c801e018140300e40101d40007003640105012058003c0081c0d2602c29070b50820658000549031941000541c4941620009151580b090030802801e01c00517a0185003654400d0000c1c5c12a10f1002c1900c0c0b010f00a4443c256954 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987766178 1250 987764928 987764941
    0x30d0228121d0d05010b030d0216060503060616050307031101090308160201090b27011803050f160f0209180303070507030c1208010e010e090a12020c04050c09010f14070b 75
    0x100c0e20505102d80c0048509001d0401c010b0b054108240504085003074510040d0b40c40002c0740c0d1482880386500c80000848070400180340288010752700141c0240c00d0914089291880205020700351030202e465034000a04941030503800141000b00c0441c0b000240040c0c8101e860090038210081c040303010300c041450070760201c40d001354440c030746d01607019a035504645001c038001e1180361000c41080081d4a00c200101302c0409041c032564101c5841d07001c1c000000101a2011103294000c182401c2042c1003c01004141001c0c0c03c60080c0c400740b141d00410010141b620500113000c4c0f0207006203011a4401c01001c041c0350010041e258094450b150650b12612541000c440f01c480944014110702d0100700a1468140d11640c0c19058801c0c8265a003056640c90910b90a9524122500503480e0001c45104002400d141107001c0000130b288121740d2210040b000090483e44d0a0301c450300641da0006010b4641e58011070720000c40105401d1000c1100306189285000384200741c401090100c81c100024032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987767428 1250 987766178 987766217
    0xb0912130b21160e030c0307030b040f0b011202040608030313150f02070b0703140903070f031205270304050d080307020f1507030516051c0605030d022812 68
    0x40c0c2c80d420107100b0580e007440802140c90100d4201c80c9800208049034082050500155805450703001038010400c041c270b0350b1100e442040c40500b00725020580e1071620700128003061500750203401c0b8002814180c5003144100011681903a000d46c2c1c0383e820500070330141010350014011040e0300b00e18000c1c0c0501540321090024407190409024092000c40e00c0006d11600c02c810030701c00c5c0c0094034100f05120414048507032800080720340411130b920400040f40000c0307109005030038081c4642030a01e61404241c0140d0305441e011100401e0407141030520790f8031554807003550702c4a02c81d0100654070301818003006c9100400381183c00381900b48004040341314140300f00001002418000e00b0b44421500c01d003004a03130f0348816a18000000c2c14240400c0741d440d1204107010f15400181c40b0b440c071307010580b01c03584c104001402c642c4030781c03698138007001511b0b80302401301d01c1143c0d6503903000e410040403280c06003d07804280290f0b07004002641c0300368030024104083d224040c0e40746040082e8089540701c1401c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987768678 1250 987767428 987767467
    0x1b120601030e07030302150a020405150904060905040b160906020c061606330b070f050109150c090f050a0501051c060b0316030902030309040b15070b0912130b 70
    0x2c0c51442100c8001080c50f50109118012281e19141040c80b03840b180c0010099004038040d080d448120b4a03100d00142c681c11008100f1010041c0001c64142d070b561501408843c0b0445080d6034420460040001d54100c0881360700021700c8074248806400c1c00d09000959411814039440d00030300000444c0005480126500070081e82d100106102410071020040b4440c011480303850464034029000031250b100e10b203900d005403881d03a11103e06203843c40d00c0e00900c416415106480b04e559a001031800718404120f241500f00388290f010030031a00380c82c002807060142d0341c04060400805031003031001d03907030710300f0325008945c000d107013154403035141496080b95502985a0f50520300c1c0381c00d6000514020b0310000d0342c8240f43c901c000134071214008034154103484002d4002941078004001e904030303624107948604554800030b805041210285981c200c0158080300040ea1407100380c40800c0722001e0308006401100290f41c1d40c05041c0168680920005c5c99035010b100c04850004c6a45240d045071000c1c00c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987769784 1106 987768678 987768701
    0x12030106051818070203250510200c100501081501090f090501051e070906232109010f060e01120305070507030c08061b12060103 57
    0x2c8010602003090a500c121520f001111419420010700d100f010550029503450b08000300d2a0003110b40010b0404031180d000c0d0004001034000304070308490740580d000c0420640d0070100c981542a52400d20a000c503140491350300540140094040201800b8610400a590303c48914544514007001500d645a0504004001500320740c2e01404204041010015061031283d440c0b90035a601511003a508541c411800841c84100220035500030341e00341040c00c0c3c540c0c981b01024141001c048900d04004511049800001030036004036895150401d0b640c4044c0341140c0c0b800181c100007550a076078298600100c02070034000380c0c0305440a46503662240c000b00d038a005600001d1a401c101c0031802c108041c07240348002002004400701451103140821a0a8100300380130f441c00c1001000c030102501440480540110740c5411603d0100d90780d80c540481e17a64401c01640540032040e0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 987589928 987769784 := by
  have h0 := BRFrame.cov_init 987589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987589928 ≤ n) (h2 : n < 987769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
