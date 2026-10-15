-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:46:19.989811+00:00
-- url     : https://prove2.me/submissions/cecbea1f-3e78-49a8-b7b2-fdd9d0718fe0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 749820143 ≤ n < 750000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 749821393 1250 749820143 749820191
    0x70f0f060b1c08070308071704030206011d09030405010e030a1505060114070c050f0f03011d010606050a05030a1127120705150d060b03100612020a050d0b13 69
    0x3056103540d001e020040c19480b004805601101c800c0c6415016a41960303450401000282442640c011600300042c40050b84c80c82540300364064038056044c07a0b0a030506480030014960040d1900b4100000403400000310380594800b4204555800c40d4000040e00c0c08000304401416541c107000702c1880300c1240d070051405800262100035a00070a2038a02c412402a00c1010300346403d002c60030060341c20506d01c05421402c015003e80000640c1d00c0202c2d003907a502800c890408400d000118204078020312800b0080c1800d1701d001d17860604240c0c0c004000780400f41828400035a5070f40c0001640071030030112890814a40902d03140d00000304505401c070b040b5030003824002c07502103250a01d80c1e0301c0071030707807400703441d001070a02d080410509804200350b0008065014595514280810414200c40240d0312620140000b40c2c01d46e400d0001c01804400d9071041c800070f40f40184501480d1580002c280e94143e1020000050611410340001e0355a00d103a000c03140c071552070890388044c402d00c40c841c1a6a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 749822643 1250 749821393 749821399
    0x6081f0b01080613090203010e030703050918010e01030b06040b0423010b03102c1003030f050f040506030901061509091d03030402120f011a010206160e010302070f0f060b 75
    0x60100d6040055840201c220b4103990f00540002c450340e0350382429400312403558006000061207072081e400d0b0303038556800082e003903000c80c07008640c001c550314044243e09500e403400c808140c0b442d40341c494041d44101c0103020003094486000300140054031075500440c1d000c3c50080c810720130314401030880354986a41d00a00741c086c1c6c0010001107151071855040302d02030f11271000102c194515003440201007829800f441c901d80c01c2d00e543c0010500c401c1510150165403590b80b89450b551031442c0c00340400e91175542485c00d0050501069040b90b405800343d80481e2805c1d28465540d07564140850700411072a0083c01800c803000510100c0c3c10b030f00820341020b45601441c1040213003c404242850418005140411a4410400140142012503171840341c03250f810100c4107c2d0303030100e0a440c01c2d0303514580040d030200380c9480040318943c1c1c10010350b5045204040700d0f643e11041303204014090001480018107060b0002445030402a80305020301900d0303041444031159810a24144016103200da500b02e00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 749823893 1250 749822643 749822651
    0x7240204091503021c060b06040b0a0912021c0201020c1003020a09091104091d070306021c150b1303140f1e0703030804060e0105040f140f100e0106081f 67
    0xb492404019018040da9001031040641410307808880c600240001012545240c4a4024032815111100500090201400704540720010794a005140c0d8241d5030161032150042540304001d0313100e07400301003908002c8800002c0350594600040c0d140021314000550000d145140248000c0d0341a03001c3d10541c403403661030310a1a6030704e800f1030f03003039584005041440b08030401003007041c2000b9500c00c40056110f40000b02c8902c0d81115034030b04096260344241c0d0910b40005e625403081e56401c0c2d0008600403c46010400030380b41090180807183e16008216032408002211286181c0121590000b55441212100080b128900c800d480707480c400ca9500d503500ca290000b118801880d0405c000d007112501c004e0855915580f01110368a00c046c0080c0c600070b60711800c0322510402801102d100324001c802c5e010302c60b415860401c40c4400b0075803481d00741e504501500c0d01ca04d440824607c03400810800b0124500032111802401041158451445440341500000000c00360041101940d8101c0134108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 749825143 1250 749823893 749823911
    0x10506090d080706091e051f06031b1508040f03080402010e03071706070504031707390b030702030403020d020a05030607120f060510051c020a05121e0c0724020409 72
    0x1c4410406e217500141181c0050703107440034000c40414045080000b8002c04101c03141c1e651141c0b075055135090310515035194544800e2107800c85100707410300304a03018075008000f441d194482c0141450303080d40050801c80c2003c08141075a01c12003848912040003802d030743d41c161b542c0303240b1070007103021200f6a0003500607407000480c914010b50580f07084036003180a03190461440501d5240c0303988100b10848485080700c100042103c1d0490b80d4040d40703640800c1d42c44100c2180c90f21410083d8450b032204150354070400070840c0140e40841036800b2240d0645281c09285100e1001903c1c1c00a0341e086184c051042c84100141c00751301c4429078a03800d0804608101460801801c84259002c41c050706401019862261030345e80e1090f802440f10007512014000180707456010001a130b8030010b0080b00040c00864171050b1ba20f4010440b40c1c014402c54440d40c80c90018000b00c1c9881180101705c20a01003001c241c0100f0f01c10200403d4995080c9000316240248400428400030341241c01a0038002c3d203401055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 749826393 1250 749825143 749825183
    0x219030b1305070e0903040902070606080f070f0614070203060a0501030201110a0309052107080d021005010e01030f02061216081311040f020d02030a140c070b010506090d08070609 79
    0x807410301ca4100000c0c0101c54100b4076440c80d11200a80b024141c1e21041200198170100d51001d0031700c0c01d05c030342030115031513260500192402e0041860074440e07801540e030802c41c289c1d0442d00e95040300d800341003400d041a40200f54207064044c4000194040c007617101003003e0311005a1200c2c2c1a04d100340c994000980450710010760703480d0411001004155800d03414011864501c0010ba56000c02c44000441004001035007400c00c4040d911202841d4814041d03c0102c5405100d42e84804070300f00310402081d890904041c0d200c0d0b5041c84064948018412601c05540380e440c1103408008007a0101c80e031358145201d4410b48160f05e40c1c2400d0000d00c0c00710110740d44080e800814640030360008461103071103a01074100700013000d0708001400455820403004182c90741c03a00240d0301c611045140001c221800000c01740d60304000800402c010355042066400240304010101e054030415101d0320303200d0752038002042c14000300000140000e080841c105003000803640000018034030682d12003820048250321 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 749827643 1250 749826393 749826421
    0x603060a0c03061208030106021203010e27010e060601091a0409020702040b06030712050124030515030d20120d020a02030f1c0b04020901120b1f120507020a150f06030219030b 77
    0x44901200210303003c5031803242a86e000c2181201c0c241c2c000074060804c3b5182c0380c01c5581d030442e075030301d250408402c001e07842d80c20502c0c5030300401c12401c0c01042d5203c009400040340c459401101d50181e40400c0b88015501e0301d5200d00303040c103400f4199a54906060101901841038036a16403549030a010012501d200c8903060140c500e0300b4903442c03204081292600341c0c0030342402130403008003020071411880d050341e00300000040e0790002d40340d040c03040c070b07000344000ca880011030080c480a0340135440120341d81400c04200d584540301c10600580b07803420440201e0440c0300b0548014003d000100c2d0b60b6040c1d0170f000790704450140100c502085070b041250309020076070052400c054081400401103120038922030300201e0103698010007840e07010b05a408030110507914125030b44000307840071400c00b10003083c0384100c5400070001c1c0010314004129585040011903020403802c080354407500c2c01c040e5018190010340c040d582c020001004409071405a51045100c0d1000742c2c0d00c20707215008130302c4005003000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 749828893 1250 749827643 749827649
    0xf081c0207030f0305091f09030b06100e0907090b0d1a090c0306040b0d0f060b091b04062006090c010f050301030c05060a200102041d0603060a0c0306120803010602120301 75
    0x48100d202d8044d10240c5458002204d0030ba04a01002d613680c1c81e29000341e1284080043c20307129000c0050440c00c0c905040303400104064010355001e0031001d007150b0450452011200200c5180c485603640342c0e07045070f5810482c5c1c001023101c0c1c00440d080400d0302c21600851494004d804c4030307a01c0c0401100070003a184109595003a203d00080000c60003500342600400c1800401034503030002c03400d9560f102803020035204000c2d209a9510803a8502500d004240c454100744c0b40c8030381c0428136420b5001450b4034800c912400d8103120349806aa240320b00d01d81101140d032001c00042d60307080e16182610320f488001810901e40000c4c1d4140904010b140980700303a034142e80c0c004084101c0340d420242481020b51120040105109400310322543c5644101c1e08140c45445240001d41c58602d00181d10140d4054503402e000d14100542c01c001c802c1d180000c496900c1884484003044806c1c00503400d40c001c0a168000105008800d01e441c4107102c6844011070480302258201c0e41900200300a80046000c280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 749830143 1250 749828893 749828903
    0x8090303160c0312020a110108070e031203040b01051009062f070906170c0d0f0b070c11090613090204060b0c011a01020106150e0102240402210304050411040f081c020703 75
    0x52140f1207d0352184050540c400158104241c41c00c0d0f5041c0000d01d80a454408014110310000c104420003036181c0380316004040a8805411024a42c0c80242036840c0c90f00600c0200310590b140000070544803030144240c0201d503040c841400c190041c41c2ea85a9955005810010b4249080054003203070400da480c801d820668040c290803600281003180c200301c2c4d810702740d442d10b00301062400443e8a00081501038120340d01d0319202c2211614049000d2404910b00a01c01e0300c0100800c501922556803803820020f542c1d00005551105200140c02010150442000c90344046014140440158000f03d041a4a0803880d440f0b104184012820395441c0e000b81a84203a42c03039240101c4d00c0c0030b405881c1c00c8103414016904094083c06008048500c5c18084202020302c0b0014130055040140399022441c400360909040142529016650784c450351280c1030140e60759050052981007620184e03009004090327900583c00d66070b50402a580d60099600001e41420b01408982090002844508490f07003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 749831393 1250 749830143 749830163
    0x60807020c09061011070906060f031a181306050115030510081e250608090109240204030b090d090f0f0e360d0305060a0308090303160c0312020a 64
    0x40008850704040c17500c1444941c8181d84c0c000c50451034a004140140020b0f60b01d0f004000d013940310080c207036040895042c28001e1034503c4d0404070380351001c0300220b41c41c110000080301d031a04886a4035804903c54003900d02440c00c4004141201c10400174500e24816650a0001d030325031000c41c0034110402e103c0c8150079409120400c4080002014591002d21504103a030500340c5002c40010007000390500c1d04414000300101842020740000d201900075402d28001c0000300c003a0303541d2a0740b44100340404494411000b56691118034950101c3c3d0295602c07075100d15460801001d880d5a4400380740200f0040303100001c020504021510308a400c0b034074001c0c0600340d040d181407920407045401909500382c0030147d028400c2d065000e01c201c0001010030a101a610440c000c11003404c0c02c006208140805d401c103018010b0503910b003443d030780a5035008010f243c0e036030640a000a00e94030a61404440d07007440500031405001da40011041120b02035080c91217264402030040b81c0b58180320720300505040721 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 749832643 1250 749831393 749831419
    0xf030504062703171201080706110c01021f1112010e0f15010f1b03020f071e0306020307051318052d0402150f03180a0c12030c020604060807020c0906 66
    0x594000b80c13100042c070303862030303860440c5c580c070b88100e0038030f00340c12075400b035442002c00700304484e8082034140034245540050f008026506000030b4039001c1001c1026508400b0050384d444025099110414846070445083e540d940d41340300b9541d0843e0300348180100c003519000000e84c40c103140c8104501c150302c500e000300a208074080054441d03c1c81c28050380c040151101c400611007220804480b10b4500030b8005080c40301000710a10f15005c01904042c258420318181905000b5105582d5000d50340d00250140e200da07952001181c1710302603041c4041200d600c507000002c4589000c155881d0706060030704103014a6480d1000910300d103c100301d40e054444500003204144a420507260340c1c1040c402412089485500030180003030360066541840d45042c0001400400502a000c100d1425200e0000d003c2322001d0b51610460a0324038801e18510881940103801054850303032a40c1e41c50f07540100200d8031a911801e00400ea040c08072001c40141c4510440290f2a1900585131445003200610f914980c0c45 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 749833893 1250 749832643 749832653
    0xe0307120f021824221413030206070813020f040b040f0209040501150804080c101401030b0f010b0409020a200a051510120f0f030504062703 62
    0x4403000140c601c42090700a40005079503014540500c2d44500010a100b420400b01c9441103082c00e0421103c124403040d0404155101c0c0c10807500081003c50201e8413142d4941d441070080d1035080704040942c01001c0803c0314441006c10031240490080d0b0031105a0342e1600d0003900d13030000550307010040818110040c001850803800701d40c500c201c00b600200d0004000340205094840541c4500083c503004103211a00b810144552401800c03218505024840d45d040003418100c4054270180c24084006503104030020108980140b031055904200002e030907541007408680c07028001101c3c036a0040d80400d00f0340f091200b41e24142d806800040d0300e07152600846100950040500310280240c042100200f11070580280f03441d03145610141503040c032940f60450401c500c41c4003c00e0b082c002e80e0b051000c9660014040c40a841da1a00d065403051010b040248074808060070081500806035000c104260b0b2100140c0203c40054541401001e819024103088000d00800d4050a8806003400c00200d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 749835143 1250 749833893 749833919
    0xb1201030f03170705190201060e180f06040c0e06040c2a02040f0b1002060403080105041107060507020708070f060c02041802030a110907030b090f0a1523010e0307 72
    0x502c02d0410200540c3e2481980440036021581c00001c5140800d210240a240510035041010139200030002c07503060000c44000c8510151a41824a600a41c41c4016078000c0044010007562481114803520707282c81c00c59400c1e0300300d00401a807050700001250036070800d80549408002151901c40309000c0c025103410500064a1920300b003404140b1325034015859911811819044480000c20144403540c2404900c1481886080c00c43d440081008007103070340b010301581507a00440300130402410701030b2001e00038014440c019121a1812090042f0942c00144042c01c482d00d07102030b10b00250380c900c07200003001d1051140030081003107a1041001440d050340b007003120301d023640183e00c01a003c0f030300484c3ca0900035000c1100c15200c03490002209203031101c2c405500c0401440c0900c1203440c6100400d401b0702e00a0290f294026500010030076007100354000230754500b060a003e2014ce50746001d40b80e0b82d40600004441405240c45c80260254800d903c101c40b032402c080c000380110380c909090b0180704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 749836393 1250 749835143 749835173
    0x10809100c0504030b1b030109050a1b0806010801050f0127090e0f0606240714032b02070b07051b0102120105040e06070905060711030f06040c0b120103 67
    0x1500036164203508081051041d01c60008180d90b071541c4803030131403800362425500030340820100120720300d051000c0c203507181c00c4906454406d0030114042d1500803c01001c0c0c001d03201c0a02680c40324403412040164450355582c0300c0e080c260303980c1c2190390b611001d02801040040003c0e0020320300c0036400f05402161020940428401202004c810b42e86914940c00c0b1854155580087d4000464403401e0400810580350020030440e07002c181d4075844000c42e448a44c12038002d40c25100302040351001d02078007140c0c1c90396000e80384055954580840e00003081d80316044021a0040b01c100d0342c0c2141404481c03083e90204c1c0c0d4040d402900d203482e041c5080d200b50700807910110811140c2c0a00300a201400e0002d4401d034656041d99120079410f010070401a40e003012a0041b0f241e11032001c00198680c48007502d0100c40040e82c0055962859003421b011502d41e601007642c1510a80b0301d1008602c000150700c0e0b00c980d00501c00841079989501030060179104407149092580305400041c004036410200e05141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 749837643 1250 749836393 749836411
    0x1215030c010e06031609170f06070e011209030c14010b040609090b01030f0f0f0b0a05090c0f060307090819020108100303020703023a031d010804080c0c0a2310020307020108 76
    0x1b04a84d28030001542080c005c0d1f02d460180c114800c04402180c0030411543c0104080c289248d40840c00d46c00204003640e200c0020207101d031102005010315002d03000d0381c110a60440c506084010020700303000e0281000102981c0207038602800001e01c12428440c1c1d4040719480600c120950340780d6150f807140c1c000d00141c25a006080c50b89440c00240c3c400881e19100e92051502c2c450518003c01007004803140240588600e0304a0301007411107568010381c1c02482c240844185440340c803800740883d4103c2040c1c004001c42d01c14004041403648020403048640c0c2d00c00da885111640d20782c15030204080340d9100081c05640039550a00c0180ba00320300704483c10740c012500307860b400c0d03041c0f2824032841d85a450040643d1031140d51034040c142d0140d4241d5180510084148007400d200b00024034045009101804056021462051000003405194500c0c00c0041009000c19100c8880440341d4000380c441841401d80e41200032400c0c00c09000f84840030599802440c04c00c401c980040d103d4480c01071a1481c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 749838893 1250 749837643 749837657
    0x503041b051806031b01170a0605040f09050705040615030c121a032a01030b0609030a0c17011503060c020c091618050f1003021215030c010e060316 65
    0x14151580241042682c02401d010516070402c00c05250800c07582c0b2655820582c1c0060340c5000598019a020014191038030260304207036241e028a10052640e40c1007141c0c0181000c1c0074070510001c0d9003200303900c1401201513840da0b5558208001c2100c4032842002c404d40c05240351480b0441c0a5806030400001c0e0341062802c060081c069542129100302c0c0d01020380035140315600c043e0604001020014005903000d45d40f4540c41a0b00e11004d0351000340150401d902c0b41903408180c3c1341d04c42600d0b5421005030484800e2281403405203141e01c003034000c1c281c801b0784a0001000c015014001c1d110f904101414045007a03003140c4540b00540040010301c015481882c007100300c0c40e06c40d00c1c825442031b0040e004d140380f00d400d404802000c182c00a10303e0604004003c1d002c1c007d694815000f000303c4941101ea0388051108541c0c1a07002e401210320710119074441004101c1c00c02d000320f0f08a1315210044050380c00550b403010064440c0000489a65040310085c0001001411800030388010010340e803d29071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 749840143 1250 749838893 749838899
    0xe01050d080309010f11120a0e07090b060403060e0c090c04030b0c180901060809120705070e0603160605031909050607050c010e01051807060c030206040803070e031b0901090c0503041b 81
    0x101991b5541c6d083d00d064817400545000d401050310201500014844800d220b10429116180d070740e410540101440c40b540c40071428480c0e902d2a088500441d40140180007070400340f0341c001d4683d0340c4085554003d60400e000202c4d030704d07aa41c0480b01941c0c1d020b5903070102610740307681031001e0343c00c0000c004040007110401141c46a0b12004418002d101507581d043c042d152440b0001d00b86030403080b15403410340061100e500040d8010030705c40160f8502c0c411010b0342c1d039260000280342c224010312004141b0140b00020030240d9000c002503200d5088100403401c90040c042c101d408031207161001400640241000c2a0305600c05c50040186900a900204400c1440c00010382164020748401c0c41000c00040d0303902d40c1d440140281030003400c041c10442e4803404c05840c061745942d40144000c145070000400500c5440c0682210f001aa40143c2118000c400c240c2d0490b440b0882220898441c0100d84000180d404860203000b602c162030b1390b1040d00391745035079440407594188101c4262025254003008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 749841393 1250 749840143 749840171
    0x31b0b0f1b07050c010f05130e04030302131e0611031209070f0806060f04022d0d112101080a02040f0f0c0915020d0f083601060e01050d08030901 64
    0x6441d800d0b00a030050041305400c00700150205109171a103400740482444240156207200c200e9400311001c0e066410500c0c4d0b910300e0202d00038803540d2011608034800300004a110342c7c540700f50001c15012402c44e00c20fa5034491000b07540415000c07064042c140d10810041e03070621002580c1503005580c030f0b805c4420058662008146803a266040001154044c1c010403185140130813250520300c1e801d48045207050b01d07400e080d140c041c1c07000450f07400700c110305030b00d4000320756080e4126107800003400010032507110440c0b0800d18035403003802014812a030001c00384200498456420313048030411001003041d04601d6003440301512a00c0160300c031180c0d507845003454030281801400e0103004280d9541c0100b030b04041c690b185688110100c9401c66002190900b1441d4010505010070100782c02c10100304e030381d1205031007801e50703039200340128010410280440e203001c000750464285600400900640751519030346180c001c1c00b403182951082c521400c10f00881d20b40001184c001082c00e0020401001e25038074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 749842643 1250 749841393 749841397
    0xb220e0c040f0b01120908071211010f0903080a0c08060f0420041e032418150c031b03150b0c07060306140d1101030212090604031b0b0f1b 61
    0x8082d640ea62a42601e180d5907034015008480902801d41c04c12a452054558040501074154020056a510003040022602480c80b0041001c1408000e02400f103004000d14050090b960084003c500954003040c00c0110501860425070780300c0d502d000076543c85004001d10041050079054100740ea138140103049001c40700c0c9864008004c010810303030750751514200383c0701060081d2880d980c0040186003030001800021410700c0c0c4a213004404821800d07801210001001604040c0200000f528804001c01c6040305010300c030840b4005042110b00d08482c0190151002620042c10b1304032161400c03031025020b0b5000c030841503d04840c44d42010744510082c40264050320349448180d00541d000c020555050142c0e5000d03014034690043d11500322004103c0e10802e540c001051101000c11004850348280c1c140d5542c0841c070007401d0245d0a00c802503946070704040c1d40c2a40000c00080c1e20804040440162107041a40072080403030343e60301c401c200b0840310000303400c0074000d4040c40010700c903100d40342d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 749843893 1250 749842643 749842661
    0xc15060f060c010e0c060421081606051009020403080708030919050a26090f0f13020705013206010c0b0406021201091a0f130e0604060b220e0c04 64
    0x100018640940640842c03401903045c901500c03d000030042072100d04c3d13180240c541800100301e02000d41a505141100944c000c403d041641d90b08000c40303040a001d038a4010a008100e400c0604200c4c40c3c4465100d4203a12440c0070241111108000c400002035500380103507403048100041c3c40e200403040c044a0081c2c002440182d5155100e0f114441c1449034a000d6190a03115881f83c0c66120900320840c180729008080c80c0030320031062442ca4100d0b98032490400714010304001d10489403480c5000440000750481c07001a41c183d843c00d501c0c800c40180401c6480d07443e82c420031f0800321220700044c3c210410750b0002d200c03504019000e284c900c0001c000512a0340154858200540c9036800c200c070741034034140142e00246240e4204042c0d5084602ca0303407211030b003440b8244c0d081d5903003083c40004546180304100586c11460300d0304404900b250b801007151800b5520500b010b0281c410401c041003074000c0d40b1f503040d2158ac260048000044100c0c0d40c060b4402c5d0303001009580300d0303112541c002011500410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 749845143 1250 749843893 749843917
    0x150903030c030d0b060a0c0b060a08010518102d060306090602071415160e0613060f1d041d010c05180a0312080601090f03050a0b010b0c15060f06 64
    0x414030b8900e10020380500c1315280e0069030054104240c2c0140207000400c4500054400d62100b400b2600544582c541c5001802030706000b40100d00782140401c104411402c1300030402d0190340e40302000c0d064280518007200c3c110056620310741c104c015110400d1202070b0309500500d56034810001c00100140103445000380030b01001600c40426040030002501106089071941c0c120b805121a0740e11a01c0890750002036050301400040c54141c02582d0340f070000c02c1c91035480080031403c0100700101c0900502992065500d40b001c1c90314500741174803000d401000800c140e02644a204e0100d042c5581f01c0000003680f52a580b80e4110001d0a9508441050110b0b500181000640302c42600320b2406880d071645040e030b6011085c5145843c1c0300d5204a242c107020040042c03400c0400c03201e80c0304400c002d0203080114109010103a881c90032556410442c80101ca00302c41e00390000034210720700c1058400c540400b00140a84090303c450810454100400c2c0980c84510042d1a41d003d44420025140d881002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 749846393 1250 749845143 749845147
    0x20f04030507031b1e300c060f050c0d0c061e0b09070c0201020606130603080a030606020c0603090d0f09091a1f0f0e010e1302090a08030406020c150903030c03 70
    0x2140c10310b0695585034000c040244400c8a018518400c2d002c01001141e108a031a03004403041a014a03c00562040c06c50840c505543c41050611210141100072541d00d515041c0003000e0301c20040d205805031017208522500a1000031450702e0099042c1038020303210308800100501c5101e980c0155103280d1f41004207455580703c1904075070901c40e601365044103041c100610607469076030000356520b60040040340200f185000c6d4034524001f0303400540155510040350340d201d0000c120020010300c0c05104020040c42803060240b810b0401000f100d01420b028000343c000c488000741c05035410b104d07030614030301044510000042d021a1501c03822840c1103f2420840c060082842000180d40140d40d0500d00342c10210b200d07054042c0c00100341c1c1101c1070241842403107170b110a00141c034110240010641c102d1030043e0f411028100641c020090340c2e908940c480307140d585403008666640568040da1025a101510003841842e113440100141040c60542030b1600602d003020a096801c0f000720440d0355440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 749847643 1250 749846393 749846423
    0x51306051305060c1b1201020a0215010e0103020603070513080319080105040218270703050609070c1709190f060807050f0307030509150103140d031a04020f0403050703 74
    0x11441440002d02c0202ca909051036060f61155850f004500740301d084880c2003001c04000360700c60b4145a00c050b22028002c5445443c1070001a4a0f00070f8070114074255142c00c800411010110b41c000740c107807600501050f04580d6410415501540004040ca8101200321800102000104010054045902c8400702a144204005007508e00c068008a1140b0300500018554500922810f010050b0071a9406001a0101120440040780c480c6181c0c8081100040081254040e00492b020715804c0e100900d0642d02c000e82215040602c2d00020040010b81c0b00840b80c00602902030520910010403003408603200340c0442058502991140702c0302c59408008000c0c0741c1d004258a54003c1c91420701900d0010705004c640c140b840b00600305010b2555a40c0443e003411810448007090701c44c2c2e04000845541c40e414a82030b02240c0081640d42031149030b60382001d5912900811400550200c044102410318008000194001e410b018038400802d1200001050f82040707028010f50192800c0c242070300c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 749848893 1250 749847643 749847667
    0x30604090c18140903090607150507091d1303080604140f04050d0206160804240f0506010f0503130f0807030e03120a050d0506010e040c031a040c02190305130605 71
    0x20b4610b0201d5640443c207010440d9001e000300c01c56814540c1101c426980e42101c0c0b402e4045101c5a60002d040d040c5041c080001594119008105a540c40b02c0742044845c14a00d0f1080d000a04444460340d00c4509841040000e0155041c1508010010302c0442c02c0507103810300c18030407501200d03201003000d403000034402400000c1c070015814500d5880940090301d824031307074140261074043c00716007003007141c4002030140040601d5180303555401000030038055064207661400b40c2070724982030b00902d14000c0402c8040d80245044030300026261112400c5980e210318403240c4801441c42685c0207030450700d50310000340d1958010f040c0f10f0f02c01e4891084403c1c01005241c617103812900409049041000b04400182d080001c0c2c4800104807080851145c1e118001200d13a01400700816070041d040c07001d481d04054268102c8010002400c00c1c2801c642081c070200000d0b2000c0180708005604242d9298240c0b00603103005074023150107030802c1441c04001401118800401e54410301c0020783c041020b0384030725 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749850143 1250 749848893 749848901
    0x13180b032d01020d0b0a050a03080a0c030e04050103030c020f0123031003140f120304020d080a0201090204020d090308060406120b0a020f1204020f090c0f070c0f062003030903070206030604090c18 86
    0x1f140c00d842e445002402d6075a5500507215400c030305403d100030850003404151141c84014491035001d001480130b940e4920303000c0d28040e004441280301d07205c20b800070300301c0b540b09810031a8841c111000010b00702121344010302c01503001800c14038041400000100224002003000ca845100c0903000b0f1410740c190b030300a5401c0110001040000e000c0c00c02c24000541c0c0c4040d810001107820280c00307552408898010b900400c07181000a4000e030000c25130402d20a4150301c0105414020b480d1170380503554040400086405901801c40e900d260140342c0408195004500f5a01c00d9108600614040b081c001106d00c0e90441105504d200300d24108100071030510300d0a85031406410345441c40d4500b48084a102a80120703100c51407a52000300324034040c00204c0c107000004104103110b1500da55102d6400a20101011800f05400e414459040c1c512079000011240318441000c00b0f9030408641e0380c00c00c00984d1001e80004d500c0364495502602207400341d072104008100c00d07010112445103080f200402e40e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 749851393 1250 749850143 749850149
    0x521090f01050105031228030606171b0f07061803110a03080622090b0a06290a090510031b02011a09090a0813180b032d01020d0b0a 58
    0xa90602c0010842614002003140304800480b100d40e40301e4000d56541425040b49807a1661340d107170348406140b207007501540311070142d82e41d944d0ba248440d8060b14610b10800c00c19521110f0f0b82102e078a0b84440c600c0d0030070250025448064056103010440d0325464141d078006513500302e080d0410044c40d010035400c03800d10404c0c04411700140902201d15140030700b448900503c1d4074003440c0300d0200c0746103c3c1001608140769000205041010042c923040100402d407084500110740391609101050048040c11210825a012010b4210840b03103102409040c1c1c00c203c142d07509211550744003003210f9481110110469445d5900044c500c140c1d036200c0300c4251007100a550542e450499030f4a500d40840842c00c0a4600c25141c130011a02e403400a20324200c80c80d240a45101c4021940c00e140d0340340c3c0e0312010304941d01525240000070310f010704001141c090840c03407035043e03000320700c1c0040540030f4100f48a400110102c8200c80c000d141c0c1105030a9070300101000700d150344d44002c0c8080b0340c03900540340005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 749852643 1250 749851393 749851423
    0x211a0a2408040f06110d0e061e060603010605090102011e020c01050a020309030a030509030f0c0610081506213c19050c0a060c0506090d050415052109 66
    0xc40c180394407000c03000715420f1806001103868038800d0441c0b149a1003142e0081482501c00c00a0094001441341c841c902581d2a000444006661550f4840702d9840503000c0c203801032850707240d64071b4240d098899500518105041d95210108402100013a1480c105210421000540d84110600300c070303821100000c3c0b4903421184103005100f44488000203594032003005060000f501d0b00d400d10b030940b0714001c41c40020f01d40c0e003000038080c0d40d808000c0b4242e4001c107800d40c0c0790440c0517203c0e00e0180c0c27541000e41c14100003143c0c18000850500e05003120006103035054460391100e0480d0b40c105803e01002c44440245058101d0107058400550300300304079295080c20a0f101c95412500b20903840f00da03d040d8000b080d10303c802903041400014003c484405c2c5004040c81440350380c0307580c003520900d43c060701a5030f41c0c01542c001400781071000c503c04010441d56502c45107001d040c4410003290760203114102c130412034180881c0c5c515a205042400c2c0308000404c07046081c0c0f03005000f0034901807400d80c10b004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 749853893 1250 749852643 749852657
    0x280b100e0601020a03120c0314041a0108240c090306240d110105030621010f0e0105040b04080d1103010e06040c02030a0c0204050a0f05071d01211a0a24 67
    0x201180c0d01031b141c048145509800496269000070040300030f80040086814900d00aa0501007004151400301c0c441c0003071402211030603039990160715100c0120221a180d4000040a18081038a0340d11362690700a01b6440454106161200031030324000c012100316104110006060b107180031000546880c9030300407102c0100c2d111840c2d481c55020440c082105040c007401202103200303540c0d40300c480d00d00704981403c002c041c409402040b81c007a00c90200c0d01100b06240408000e0b03c540306000740c9101d5a0000c1070900e042d10755603140507165010600105006584900e46100c1d858000d00460091100300a880b03042e00748881040102c40345000c6000940d0700402c0701c5807409030005400880700c2c0c0c048070b000401e507880c100c41c5409003200c050a00e00c0f0b14a4a400c1201c2ca64100b810001c103040581c840c40c03000e00c801e0b001543c0c0e448140600600600b10111072800950051b0090384100150a10365060700e40108041080c0448680008040c8a18007201c2c41c900302860300c000c10308801038a0416 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 749855143 1250 749853893 749853913
    0xa052206020f0c030726030f03070306090204080c010e0f03070f080d0c050d080a0212070f03061a0403020613031202070612200c0f1207110a08280b100e060102 70
    0x42d5a070340c150301c04c1c05002070a40c1c071201000c80003820000c6c034100c140c9040e41d0741d038503920a051805500c1260100007281c580384011502070868800e680a0b2005039004100e60311421380152881050603c505034080318890300f501580d00c060145100510079002c010008505110721a818510035640745c0c0c00b0010340340b403800003245000072440501840307410064580e45401004001078810b034800005410040001d108102e5445100302055182564040085e152201c41240c00d0042c05441a05414024881800036180c50300082030780511080080c42d0459036a95094081080c4480e0b803405130308807240030050141c000101406200207100104110030400006526500610020800208010030f01e40d854070410800d150b01070790b044c1c00302c0e842940c004101c40880d0b1b00c10380049800c1403955003092883d091030342c081015150808040c1c0440150300c0072221400c000007502c501e407400c030716401001282c0030081d0580100c031f50308035a001190501400d025090301c040c141c1030455000a44007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 749856393 1250 749855143 749855149
    0x60503010b06041e03050d080901231506120103081e04050306180a060e0102030106030e030c0a030810031218241d0406080109050f070f09020a052206020f0c 69
    0xf2400d58556500240200352258800e410608068200808602c12650306e48002c0f41c000d1149485048007000038000f205102012204620344114992071691185c80460b005164071186615080009412941070400e00d0801c021100801c0e40252488000040c428030b1902104c480c140c00b1001c6044401d2603e40f82c6004a42d0307902c070050582a181200900342280303480b0901810300390036041a4280654030721800501e000f584203105280111345444401c456008011041c0c4045950340000b070300d00c41416480654000c68020241400010503900c084009088403040c11500d544075518070300d403441000070940d61065141c01c814004040e26041f09209980c1d40404004060a40740c10b44111078929800b55070381c0740070144540e209081040108141d00c0560110031a40d000e8011a540140c5600e100b0780ca65071140910102607075a0541407001e0300d01e540041035103d0007031500a00e0f108106a5840d009101ca103407000d550750745e10b6130030498540d0403c030252064607882c020f064410002c03000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 749857643 1250 749856393 749856397
    0x10140c0310030201210c110c0d03021b011b030203040509010e01030503180102010609060e090607030501060f030b1918050906060102330124020309010c021903080c070306060503010b06 81
    0x2c000e04100501c000c036010858000441024511030f0380e0140000110504003510b80800f225807400244a002400c00301c41c640700d8980607600d90540c001d0203030102050144d080707030501d450400e0706004110201c05400c0b82031861355000316000c3e80c05103803134509080400070601e02c10780c407070142c031001d1400520204c0c401000300c401000421a20b402c042c219600181e0142c03035242d2190708194034103000002c02501074201350b803040d0b541c0429140c6568802c403040d0215042801a10300003510440a030000e140649e00c01c10010100410f401e40b08548004000c4212166410040000300050003800405405010305904801220050285460140d000035901c0750507085e1485185941e9a40020f09c0d403c0755001042c080c8441004042076031a20001c44460343ca001d00380c1140c203400d1002c3c204403480413095540c80d15059460303162001c03079502004440c0900381e5071a014801c046000200045034803006240001007140a40045480d5081040866440e64000c5000780d04092840c0c86550300c1d801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 749858893 1250 749857643 749857649
    0x302150c040b16020111031b0f2b0201020c070b0c0d03050606090d0212060c090a0e04030c2a030c091802090f090a06020f0d18031e050c10140c0310 65
    0x3ca0381440200c035000484601450022401490000041c17400d1685100740442c0c001300d01403011214140c404882d0580c1d00c00404c5140314101c0d410042600038401c008100c9030700e00000f4400035091180c5492007505003002e45d80710381c3c4000350000304461130b5030040c804070740315440e1401c0c00c008520b040c1010540d14400c50490b00d2007642802c207071000b15615002e031602000e1400d0115012460801000b0710103503c5202054400c0341c1c001000030302030922740012031141c0c3e45550764441c521160b81c1d90611f624007040c0540d054100c45c20380081955111805480150300841303408845924201c1908112001d800409080842102c07100b005a12002c0f2011340005d0b05030000103803641c469001e5070a04102e0140200300e5400040c5c0d1404000c44c040207000c400b43d11070020404a485428004440a17074204014007040700108084508502d8110400c4042581d040c0507142c5183c2c04100c03401c1110f110f40c80e5081903502c2075140b0f907440c820b511250b4444652480e8519500700060540c031950100c0c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 749860143 1250 749858893 749858917
    0xe0d120e0109171011160507060e12031606020c0d020c13290d020a0e0109051303080423070f1d13060e01020904020c0a022b0b04020607020307030302150c040b 70
    0x1517884031040b403244003114014940e9043c50011101c280c82e01c56240c1d011482120000307200c501201d085490310b01c80b11121200800c009620704048140240c2c0b40c240c03490001d680c85503007032051108045c801d11141203510800d901400c0502e056200300118449508600d42520346005c0d590050010722200e54210304000e00904103400c240540010803041f4040c1c0000c3d045802c8036170014144009660803070503650902020311007a5551089034826144140300940007906160118011545890b40c400600014001c460f07607000b4004145854104680d0018804280740318003040030984500d50345e0440080f1b240395040500784502c0b040d48002c040980a820035541c2d00100703001c030398250304a40c0800c0010f0025500d480640d1611a101d45403210140d02450b2998100d01c02c100c0c220240c564405003036041c408461103e51035985400d02c0082c81260800070802541c005a0345c200546001180b00750300404858a00050800310b4981c0501f07030a035246002d106c144040e00d0703042c00792028010300d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 749861393 1250 749860143 749860151
    0xe0a021f1b0503040f270c080609060a03062415020a02060f1c0c0f0e01120e030c01050c041d01030b070e04180602091801150e0d120e01091710 63
    0x82c10702c035040d40704d80c0c0e02c00a418800c1c0c640014108260b541d04104a00c451468003050ba5101043e64040e9501182e8040000c1c030303100c000443c3c5180100169401410203040002c145440780e54040c121520030140f200e40160950359a035688881300c7c600000b80c10908810483c2c19104a406580e541711250024400c80340825400d02c1034113944151080450012a00320007015502d00240007403105480190004000c0c4118020041c05980440544801039452024100e650003102c8001c015034104a0140d00041000c503183c0c0c0c0c001d002e841e00503501900302c55a034601d000c0c400014040c003818044113451007800100003141030744440781d50061490030000000710351200090f0040513404590301030645c0070300c11841400310300d03405031040003800d8980f28020501d801c143d00c1e0300c0500341310320741c80480300800704100c0d6440b4002003174102c0006054400c000f0015aa010100c29040030228001075141132a04220b41c2e112010f000186281e0a2040e134429124000710703110290403941900060319 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 749862643 1250 749861393 749861447
    0x309010806122521030e03030702030304030b010e061005070b0a0b0d12020712080d090512070501050403031107050a06091103120306030c0402131202010e040e0a021f 73
    0xc1c150704070020740815410307104990b016910240c0c5203c14600996224040403501080034103a221914080f07103511201c002c43ea0301c1950b0115078050200041d00c1d01408103019010040e2010000341c409103110b85455102da41c10004881803c9200038441845007a540d0851500150800c003100c0c101b40d000000702089564551070500a000f13420072054000e480c0c03450843c1840f1b5145143c002601c1142d003030303d540f03554495001c0071040702e1001c0900318000c1004034400419495000e10b03065482002075a500b94005004081140c00c458810769050751034034100001c040e4948261441d00300912011400d1480303e4490340e6a515080100a00060707a5031070030400e1002c0703440c5405001000908540805100d0340741251550010340d2000d000c1c1c45004107000c0e10345814001d4640000c00c820980340300c03d03d0508e0148100c25580c0c4140c0c144542800c4c6c0280c2502d0382d010354a0481d000c04000d1403004050300c1400400d001c10044180040e010011042003030740d01c03002c00e990b0078200000ca0000442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 749863893 1250 749862643 749862649
    0x130201031104171209010c14070515190224040c050616050f211b06131a160f0504120804030b0619060f0e040f0c021011250501090b0109060f080309010806 68
    0xb012b074010340c3e88480445c1c0b12031980221034005203000707282020902451605008266aa090040400d820300d8a4400d000510012a100f045034450700071002800782030b5403140800c889030304c601803180394403403508100014408200000e0310076141860040282d400c00f02c2c0300d5003503044500d421202c20000013850500c1d03404400901d40d07507034842e081914103505240c0c0300c4880810900c0c0d0121050000c680d20301040811640f5030070304c9044a4040e0304001803502c10215109070709064002d00348901840080b03000321500b0034919429215660095445046003004a0803120003014244100d6000101c81c007c2d50004140d501114140d0501103661213003400162414600307803095942280c0340240040c014052900482a00b004607000e031020441000e00c8001564241c40300c030080d1101c01c0040751051030000380319a54415912004a00c900c0c0155600c600355080400c1c10307584076900c0001440790030b0540c490400100760603500c41c1d24030383c501000346403203000e181d0300213050000c075400280d4035172 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 749865143 1250 749863893 749863903
    0xf07050f07240b2d0307081006031a10050f04060b0705030a09061419110615031e060a020706091202150c070b130201031104171209010c14 61
    0x540d11422207004550900d007481c42c010401940c0c07044007420441c0c81540707403c20003440410400281c034003110001c4485003070944d24040580325500341c03240080c0041c85850900483c080d05401501c013003425880c604101c40e50400baa88001c008130680024002a014203540d10421180306903501007510031030600240040009522103544441c00081000401401000078013420b848c035214120f140ba115202114070304100c0706594040141084a1050028040b2102100e03920744c0c902080856003030400d0a003041406d461815a203006891002d4891400b4007100301808000300c52703010b01c4010349181d03550301d40c3d018005107005540010850144001c87e00540241600000080050308143d03200a5441084d050118843c0f540500031400f00da07102003c40328456084001c000b441d454106c921b19407804002d104905055440c81041455012500900010451000903029100201c50000e08216481c0d0100004c100100401502e503a001003120b02e61a41051450400c2e01607504198a08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 749866393 1250 749865143 749865157
    0x81e0a0e030703030b0312030105130509070b0a0c020307080d0504091a06070c030b0a0b09040209073b060301030c060f022e0b03060126161401170f07050f 68
    0x103000c0001c000b820b042d055000070405440503411250110049455071115010071702800d80c0c440e440f41d2100359404581d401ca1600102c4181c1954240f40e5291446007065000e041c014002c140101001000e501d000e00009004181e0800541752100c0c119100511501c66800340131483c0d41d8551070241c81034801c1c12015103003a409003c0e59a5089942005080c1f0300680c072007100c1340d1000000085004d9402c0c0152000350340050440c1c011625198200440300ba0018034580800200340301c0410f0380c0100e40380311440003000e8080c0d20f200007109264195418002c19049006038000c200400025011424840c200d40c110700d403001d18901400022402e001c0203001c01f1081802114030184000010740d011564040c050a0400044c0c9045d01815120f0100740320760201e0140001c0a5003132507008805000e4544922402e9821420314095600241a015009068540300c1d114601e41c071541c00803c071b00b0702d4a015405020361450f10700d041140544000345690300b08100410b070350707002c0c0c00208165106 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 749867643 1250 749866393 749866421
    0x6070f0e030a14060a020a0507030c03170c0a031409030702210610170c03060712020f04031a132001200604020406090e030306040b0a0e0f0412081e0a 66
    0x42c180403410884003c0924081c60f0801e07020707203c085100f01205208840342c4103d15110541096001d440079074402c050511706805100f218a1030041c280f03140300020f4810100854080e40390641c01500808840c1d02000701c0444190f29020300981c85400420f540301a80c0c1158059048141240c01001c10701002c1006183c52250500b404034900d03203900c015084d00c601d011480b400f0040003646035580d008148005400d900500041880148261000309140d01454000761900c0d840051201c805c1d84a54402da60840c101c400009a403200e0070704442c1c0205240809190700844d90301c410f4482e40924150840124500b584952283d001c0c054240500c418038462410300071903210041c0c1c90340e9086808070302ca28a010000b145c100014800c0050b0704039860300039411503441c641408002c10004003d00c0d40310750440310005540e08050302440c0300310060f40e07061615083c913103405a5a441c40c41000024000100f0400008941d0841004040600c07140c4250403078a0b19819034004241543c51510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 749868893 1250 749867643 749867653
    0x112180f0b060f06090d03030f02040513061401170a09050c0901090b010f110721060908040608100308030406050711060907240507080c0c0607030809010c1106070f0e03 74
    0x920541d0030009200c0c25041c0c03a400c80c0794100108105643c460440c041c1d81c45441807001401103072080c1d1001e400c90400f070600618242d10760300019091540526a503032225242c0409101c410a803003c006000403080c2845610941d10041d0801da042e4014114140550385030840c1051100820401000e100060141696561944224006000603206090101c0c5541100220389881503007114450320460010341500d0341801c4801401c1000280c1c5c41030490a15485100410154401d00440a224400c11607031246401340c007418204000b0104451048004c1d010070100b00010103c90788150701c028005120b55038038100340c40ea05000000304155201e100e04100c010440012a1401d56980303551030f500300c08100b40c140d80e4900d01c0300003420018600344080400581c401e80580310f605030003002c0d11703019012580031510310307002034034264002098242442802e0500384501580b0301018940030007650410810700da551400035200c0c41c04c20006c0e04407841403512070f801c146800030004095503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 749870143 1250 749868893 749868923
    0x141c020301092c0304050d080f0a2106030b040b0424060501030e01060f0b0c1c02100c020a050a030e06090901090e0c0a210c08030304050114090c011218 67
    0x200410189030f4151100c0010a5146440b038040158012069114002107182c1401d010030f0100d503610101d0201d44161052008001c07003071240024051140da0365854605001c862001800c584091400040501d031410a0510100e041c03050301a43c407039089452007501f500c482c41c3c4010f049201445c04211401c14072040c88245046411440855038240e800380007001450a04500301c41c0f681c4501500001e03652410410b50750000d000c1e04004036040c007600d819125803080d000400f60700740c0d00c60006801029052100d41994415407a88140d688014400030b034031650b81030b07a5504d603008060b051000b40407140707540743c2d220411a40c8010014200c03403441e50356070074800080c022001f031075489409031052400c42070600003840741c21144212910704440484003403182d160040820107a4280c4091807001c10303aa14100300440c040c601c240c00020742e0300b214147c4c1c050306582c003420740c10068004940d20384e02a0380c4548072851300e291a00e400100046841c0303815842004404e40149042c85400780c0c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 749871393 1250 749870143 749870159
    0xa0f0e0d0f061104050d021311031e070c0302030a0e0a09090614010e0f0a0209060d14161103040911160807110303030408031603150f060e030c01141c020301 69
    0x8038508910030003092240b15503140e0140380c0c3e800350b40141c40d042640301002c06c0c0945460401c16204a040107000584000101003001e15940304440704842100020030000390740207200700c4903a0200e00f500d8100940d03011645d000352248110300303c20040000442a04105a80c0d114a40c1300a1101c46006c0101c0066480c040002c0c00103a18640800c2d12250000a05403003030031061842a080100b04181ca03548464080e0020f40240c8042608a80148008601c5100ca8810b00c801100d2980300300c5801d00e0b0180c1500d242030b054600b44010005c0c1c9100310ba1042d0f400100703031410b0304e00c0d01c100440d41c00040441e0030b50601a20701107a4282081718040c1051000304001801720350b0054100311980f06940c0c080c95a24402a10001c00c60a004c0001403865503a2260b00b400f10040d900e0301103201141c00800c044c4010399034120187d00c6190003010007080350803181c00e00d0008026030140160000203030001c2e021314940c0c82e140b044108005401000313a480e5001c0000c01494540b003c54072541c4a05803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 749872643 1250 749871393 749871413
    0x10903031107050901260a020d08030c090a0f03060f0b090705091201140907120c06050f07050114060f09060a12080d1104090c0c260412080721050a0f0e0d 68
    0xc040d2550204c04886c0450b00c2001c503002000039006811582c0202059940c060b80d0b610050107005914000d0040c5006540c0301c9407254004c0900f03400740107070b1600354245407040700d00402100c00300c546404118505074903000c000680c044440d0804a4595100d040418406461805074204c036520345000a03140e42c4061468a003d2104102190301443d200e088442c4030f910140005046210062010071011744140010f201526406c0e10060520400b1340d15a820348202c0c0c0403110303140a1410030081c20741041020f8a841c100200e90440756800c00902040c0c1800da54041d00b4069a4258041400c1c88003210446a00c03d20f10355040044800d080c0030004950031500465030f105060500f1a00621300c44c140e0796014541001c0060032444070119507606800043c2c2e50314209190038000004c0050218a1209410f0b008002c001d9884a40e41380140d0046c5480035610300164841803203c404551000a035620b02d001ca080c040540d01c5400d005803502c440b01c5041581c08a134640b500c404120b400c0c20703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 749873893 1250 749872643 749872679
    0xf02090c0904182105030c0a03060509070306061101090b060d02010519050409150e0a0b01030f110d14010b0a08130807060f050606031612090609141b010903031107050901 75
    0x104c5040050200340c22108003101507020500000c0f0184041022165a82c0003440b04001d24103000400c27598840c0420314801040705c1800209a40e5103080203c560400321420040344460006c00c4462800d0390340c034201c600080d00e80c5029500811280c4116401601204d443d074010000740c428511558134000d0541e441400354405807810700d00181284004100c0580541e03c0160038980726a641410450007484c40c2c0c4012410140c48178212240000c9921449200b289048480b982c2c91901d540720034240c0d01c04a07441e0710b03200032010040100008a405480d5214241c1c40c000e0201d03107500d100400951082a0301804090b0009206401c203c1c072030740415644185240240b000340d86850401405004c100d5178541d500d040d0446008805105508281100e003804a001800d003916840741011203485140c1154101314104003294060003c0250030204002c520303e55560002c2c81c030008010351142d10004040c400240b04902241805008500142001801c2200c0d15a9190b207032281500800c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 749875143 1250 749873893 749873903
    0x4030339110409020901060503060a0b03090f1b060403150609110901030e012d060806090c150301030807080d140a0b011403013006180605010605070f02090c090418 72
    0x1660318030090419000703450605400030176000706030b841c2001c20755141d032008118581c032100070600403808814010103140107030b40c1d84c4c0040c4480c000d01c0101d00d240c41c9001640b8011885485182800e555030901218284e80d4003024034510020310011480280c01150040c3d00c6107400d00f55254565036440025107603080003641d052100c2441002154200c1d0b80e203003080c40031000d40114103404007008888444d40501c500100050445c0e4401440e414118103954040340340e00712035a0020140381008d81c0c41c1c2220002c24860b8039551565440346c0d001c1c451801c0081c485040031607003010140f06948098922003410150cd10b0525040928500034500c104245000c100c8000c0c00b110100c1440c000d9034141c41d8100b8600700400020021540800c10766100100002001800c0c0c2c400515680103912881e200044460300080701890a02d0554005030040e004000c4140000e00100c1d00140d52084584d0301a5510501501c91040010f044d00c107081c02c0682050410707004c14001c64007202002c8103d8012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 749876393 1250 749875143 749875163
    0x4050c100c051f0b041b03020a09080a1202060705030709050d020d0b1504051b0904020304060b0a060315090e0a0b150a030f0506060609060d0509030d1e050610020304030339 76
    0xc41080225011916040d2000046011b000001c0b40aa40201000303141c504001c81c074160369018207071030085e541c441140c0220502408042c1581c0401c607464020029041040c01d41c54034420041c5405884c0c4038240c840c68861100b41e043d0345510044100003031300461000c00600c0d180a000300d201c0304150445020b00c0c40d250004000b517025042981d01100d50602d282d18100441e01004080d41000e401540d00c0baa4072003422030743d40e46203a40c090091040d41c50126080e00d090001c007100700301d181d000d5800c0904101d200d4280c500041400c94041d0b620429014854842010345107440c4042d10441d40c00c090840008028010f08500c03a0718101d00c150211f40081ea508818000b8a01a034081c0b150810401c0c0b10b5992800c69a8109562003648141102d0503c0080544d90080e115000e2510300301841c205002c0c14522400e000d080d6210009644142181030600002903aa114620000e001c1021181c0d0500d12242e5003e00003060301c0c07109030924600c1c0b03c069607030380a035020b030784007201e500303010b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 749877643 1250 749876393 749876411
    0xa0804030e0303040b0703200708100b010f05030a020703090b0408010e0601080a0c150e090a0209090702070f140609130c080a061203050307030b100809070e04050c100c051f 76
    0x8460036a90034984141c00c00566550548010414240d950320f0002048c0344a8103441d020000c6000a108210080c00d80100c4500d08000301d1f21907480f43c504110000c440c07004004c2d00a400c40c2c0e003000e969100103a80d56030904048a031105180c001303000b00d510009001990607030540150100c0616103040d19016641c5d8407015030784407401d141c0106800c0c407840040022602807036030144070552030304102c994849094005000b101080341d503544042d901241c1e860187c10065159540500f0600040402d5804c00714100c0ad80c0e503041c81010400e0a0824185001c0e44903c010307100ba800014001e1061000d411034460081c0c81149081e00010340c5000004220110f1400303820112118a40342c6003501c40d05840c12101940018014000e040d25030a5810301511f94a5100107480b104e5900c83c4464107001c0515800c221880d40b06c9401030041c1014040880c0c40460f0000d0351301d4044440750909460240d041d03510020030350014205010b024884400a00345006031903800700c041d102044440c00c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 749878893 1250 749877643 749877649
    0x302060f222333030109090b0702010b0f040510122a06050f0d020405090406050925120c03021509010f090e060904020402091504051302030618040c0b0a0804030e 71
    0xd03411074420340c070411080b506040f00d86114420344110029140682c030b090910b24000701d8591003030f808000c07101da8500c841d60502c4180c00129070404d034144028001406050001851809010ac0042c801c580e00d0b00840c0e81c55000c03e0800c2c000f8a1032074291006950282055070100d11011922042c40d40c80c040d883e11100e42c104580016a14203441341802c0c031a10b40b2003140c0715000904451000c960800001c50a969084001071059214400201e4646490300c0b440d41061001101060040710300150b00351103000b00c000340003d4501122451064103003074141444003018603030003e034210140d0103e41910084400c01014102d40030703201c005041c00481e070103c600078042d209540c0e5200c01c51012a030039142c6403900e1508540018000340c01e1460220000309405034070000174000760700c00030301004a410701d61440c5205065440c0c00318150314001005c134a60202c80c640c0f01c401c1c030740e000c400034041040e04910840640300100750750341c480c1c4400700094041c400a0b01d040c1c01007151808103401501e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 749880143 1250 749878893 749878949
    0xf340318090e03030a020d0609090f0501060603060b0f09060d0908040806070503070804030305060d0c060509091308040b0322030c110306090d0f1b0309030209090f03040302060f22 79
    0x5581c907000314655500c051a4100a4100c1f6015403030203a2900e50006100d00c0b0b6000780c1a946001c0c40c5400002030f024035006084402c140d011509243c104081048900c0007070098038070413604003001a81c2c9005400000d8518418441045032030380c03510514070184141c020180041d6000030702140c001d900c0d241c604dda0309000443c0c444000406000004000a101c0c0d008160007400242c407401c40f40c1c03100e944885210b8100e801860000e2404107607031401e464191542d9421503003640c05000c1002464031840901e00c200e001d903040e4000d0000100744030200d80280507010b460800122000089545001000d45400d40c0064650343d001182d00c440928010911071700403d188002001d41d0300401800750b98101c070b203501c804248210107601c4034801c0240c024401e007051190307651020850a40c0b041000031213019005e00403640c03241000800022000040f0303420707260100c5601d0b440304610111000244109461009441060b80b00103031220180304071502940c0700804418401c3ca01c50454203958 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 749881393 1250 749880143 749880161
    0xd0c02030309041812020f01060902030c0703050a180803130603020a0f1d030f01200403030503010323030c0607022415010201090b011212050f34031809 67
    0x95001001898040c0c602a4441c03004c4c1c0d021044500003038255a100c0c818104001582030025800c0310080c8050300ca4203110b003001402240a0860031814001c1c4050810302138440000d007400000100c003d40c0d503004044001194a001301e26907a41c40d00c81d524262a5000005e53741800003540d0f00200e8485c2c080e000b92503000c5101d640b0701665038008541211201d010803036522070645042154800c03a28180900300440e0030240010680a91640240c4800032012800c400315110600040c00085d0740602241d04680c0c2049000b4450052085030000c903401740898403005120018901480e561b012035000c1c0301b1a465001e1b03401110103421400401140d01c0690031003807811600140c1848046030407004610010710000401c10159903545007044400c0c0c1005804603080e840890411071022000b9960f0481850709505011000442c0c8005009561403080c4c80098035044407204403a0511840f41e49040c00b00c40480341256041c080c0804005004040740000d8619003c00d924885002e04910 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 749882643 1250 749881393 749881399
    0x152203231612180b120c1603050c0d020c01050d020a090f060c0c170c060c011103010f0311060a08060f031609230103050a0b0a151412010b090a0c0306050a12050d0c02 73
    0x207020030503081e0580404000b070200350402407e0110303001c074045240c030b02561103100b51102a560010710038207925004a500d1503008541c48032508502590344002600c000054a000c05612081e00c90340039a44a00c132a080380380391a007050800030381d990303114500b221000d0003209800051525040f081d00001d80311840907030f03943c1c0400a07015403820200c1c01080c5407900b0400020b10401e0740104008144d20a911201030904061400e2003030000b0400454240078044824914040c103004014100d60001040035201e0a00707046540d00546040c050680b040c940703070b0401b001964440682400400c05000c4840d1401c11109201e81060201c0c00c5075070581c1c3e0844000e00030513043c0ea44a1505c01c07802024180c8080c0c076031242420110b13101507804060260b41d500c5614081075a401c4c0044040601072507080c0740c2c10200740040544031085020b40002d403d42c1c0c0404c41002c203110580240c2020ba000c43d030406510314002074070707441c0c0c6120f16a20a100d40309883d14032884060131034060503201d44c0030b58 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 749883893 1250 749882643 749882647
    0xc04090b0108012607031a10062d180e1501050418020901050d050c030106110c0a05010f020f0708010c1106100b0702040905152203231612180b 63
    0x12846402605000d108084c1404444035180c507540c0e04114200d141441071881c41c0c1c5070b028050280d0780d10020030701401040c5458164070030040e617000500c1500020340150400c4040190010510440b14400b401071103240d0710f1411551858408902002106c10383c4a8286180c54500d4661180084804503040b4621034645400c207241c1d100000d6001007200c0d030520004005400d0a0307002030080310322600c64542041d40765858220054217041030454424010f0b0800000c00c0394603900d20403c001558003e18041c0480d00c0c03821000da01d411061078515550384aa001c0010b8000070542048192a84d00c0c3d940e600d000c5040c885035586c600f4169088501d04a0500c420702c079000c5200060500580000c002107011030b85074030780c42c0c1028845040b00d44051044e400f082110001030380030310b179025042004100d4010403524018880d141c8000d00600038035803021901c0503201c0041c16200c102e050700c140709041c2c083c2d901d42848030a0b4004d2070a0045529043c401d9100940e42c1000d402b180e403c040098 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 749885143 1250 749883893 749883929
    0x15060f070b0a0603050f010906150312030507030e0f07050f040603170c0316050a1109060609010e040b090906040c091503020d0f06020d0e1209030c0907020a0b0c04090b010801 77
    0x1046074038010010348a142c1d0340c07240000411810010000450f1840f000024440c111f814001e003528010009121050b00c02c2400b000050381c4008030414511103403900251644651a080700903140448240d015480350300103192444002040c40d0341128822140f15549100e10400d03c401e4401c9884080e0004030030841c800200e010420003051514407040c20749203070030040c82c41058060100c500680346984260100010402c019007080c210640c1104c03241010318100e400280c4901c52880c10b0750412103405116041c0380c4071504900f580070320041c0302603203e103480540070307507209402c40c3c0a4502103090f0400080c000020311600508901c0721a5829586043d034081c040c1040f4010822104c800481003040c001c0383c042c0c8060520342001d0040840c0d0512a00000c9103402c0100289202201d400c0004101c40daa00060040d02480d0540e040c0046941d042401d1f4144030aa140203814140c4000402140032100001403055405500040100c0e0344200c00440d00c45c07209001c2c9902c0406091440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 749886393 1250 749885143 749885153
    0xc04090b130f020301090803160309050606010e1309260a171e07050301050f010201050606120c120106390b09070902040b0d0c1704152315060f07 64
    0x1007035085002c1d00d00480c0c85016540420308480e0912425a0101303008403d0042d10014031000320140c000c4d0703180500803a803013a02c03483c0e180c13500a0070f07640c144030140300c02c000c0e5921052001056629008420002d00350b040c20122006901107101d0300c08146540203030111101940e068a03011f00e02c0307079150011048150302d001d14004c070103455100310158006c0c00d101c60710100d0900a2050301e16a0350350f43c0f00e500d06030038014440803901d003103419641400104003140c1c031064141c64112001c10144140c54560b20f010f0702982c400d0f56004510352510400110740e803601b200145001561000030b400c0c250448070041e0070415018456195010092a26000130683c10041d070764005240609489005030b0b00d17015101280c0c03103981f003600d0807400850042c1c126001d034030030f00980c50f03041c1c14a2482c00046810100f003414004100800b003104010042130019010362125880c005035241d4622084202d00d6110303e03196040350203052030518449000034034104030741a66807101c01d9001003030600340702d59070b8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 749887643 1250 749886393 749886421
    0x6090e07050a030f0c110c041103220b04030c0c140306070e060903070e010e090d0504030f11090411100f020c01050304020d02030303010f080105010b0a091e17030c0c04090b 76
    0xb40010161a00840ca94000c803030f05c5442103200407900c8154094810703081c21410a840d80008131700c43c901d48191001c00b03020000072244d20804c070030000b42e14102940a668007007200820050503c4a00200300030416820083d00300189003d0340b880301159980380004420b00c8500b410682d05904840701003440d0178020309a4440c8500d00620550922640a010a103007040d01e612603004e00450600400c041d0440c14140fa03004228103000c0d01280f010540040c006114a1000034483c0300240c0010081c00213004410319482c0740104240c01d01d0409041000341c00c004e610240e841102868911003c503070040c8070100e0101025006420710310003100c01960990001041030ba0440c141110140c010381e8103000950180c00b02603103040d441c13400c2c025620308681058000205500d800c00249101c2c0790040460000c0f981c02c1030030410309030040600b41c43c6c0c2907c01d504c248034000c8080900100c03498003001800ca004507920450725400c600c04200815515200340160100d0203207000729411070b410041c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 749888893 1250 749887643 749887657
    0xd05160509010f0e09070e0f040204031a0a09120906030e0706120f0b0307150914010e040f1e0b1c0c0b0a0c080a08010e13031e120f020901020706090e0705 68
    0x18405603c4e14543c01013182c0030012526a07001034400c00b0003100d60b141140303210f4010700040c0d8045040500350380c0d401d2248059102182c00c41c90303001002551a00c8035420540e80964012841805820401c0020705040035a00680340840e0410700404ae00c0d50002400c40101d580a42d90104060b0000b034810005044101100d0213141e194401200c5640b82003285e04014201c035084454008100301000388405480c0d009501700d0003410340c00300000d030b0b4032031900400c079441101e0003c0c8a549001180009010f190a006240303041d024408104a943c3e50000046890a035520004290407000c060019100c0e02c034010034002c0449424002c00320080c01520124005080c800112038444c0c4501001d074010080003800a08a40700500c5001c0e41088a20b41218080781042200d0700c0326a0050401841a4400f1480031440040d00300120f125601086104444140401007901e45d420b10201070344c01f10031850b001d4420903400103141031140500d031084072101402420152609041100c403680f01d10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 749890143 1250 749888893 749888897
    0x4240209040204030f020108010b03070c02040b010c0b070903060c03020a05030406022203080d0c0c1208060301061701050117060103200604050a080303090c010f0c230102040b0d05160509010f 84
    0x80001685900d0700c0c8014000303140210207000b075038a5a0300c00146185016006160400303030034014071a8050700500302c840b080da41103502050b844802c1d40121a070103512140503041c0c042c1d442c280540d4a82054454082c4c0e40505410b00c81c48030141070075800c0c0d129101c221000a10200000340114000354060300b032422100e4009981c8548841c03c980030300d6400c1c0c009a50f41240003822103000c01440c8202054041681031012510380191103505d4406c01c605800014480100c0004070036903000e5102c1c4000c1c14018948d5003100246480550080109014a070380c202d0001d82c0b100c1c95104000713180c0381203d07401045441544441c00c11301001d03842c203042240d00084280300201d011b03070700c801010015103440c07001180c80e840c2021f00310f440c203140449100d0520401c01300700900b6591043c0005080c40c0c001ca1020122031a00588048042c5a07490800a40d480841d004c201d84011100070095591042001c0c0101e440d0324140c05083c140c0c001e21040071450802034602c07994021141101040028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 749891393 1250 749890143 749890147
    0x10c0308190212011403060415020d0f02040801090b090105060901060f0504150e04050a0b01091e050306100e0702031c050a020c0d020606033c0a0c030605010f0e042402 74
    0x400101010390300a440700d0354000324103400610185c400d22160512040084004104608142d142c00d44032070301c81c03d640a800c5400141c81040403034a90040c500c0f21f00d08030390465846a5500c1c500c0d00a0981c18001c1344c1c10304030480070406001c4140100c40c0039038001003140e0b84a9103001c0045c0d50300d01c0000c0703150003401824400044d0700c20001159004a18482e1114851071140c00108011600020f00d00b00d9032a00c0d0400300055a607201007040142d8844003401000d0503000500d81c80c03052042d501c81e540c14071400c400c000c0000d501080b242d04503250030741285216102c02da8144c0c0c0f00c0c0104502c084105600c942180b60b40e08142e0000c0340c00c03001062005103009940e0000508058a02c0b0540c00540e00443c1842803900702008115100341c249100008545084000c0070000c200740740c0010507000e0103000b04c410045040c801c0801069006100b002e000380e903407926074040c100c00d10610030408444180021601c0804d40e019210325400080c6007414440c0300c104060500d200180e5032a42682 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 749892643 1250 749891393 749891431
    0x3150403091a211005121906150807080309090601030603020d032703050705060a0302040e010305210309060a050714070c1e1809150606230405010c0308 67
    0x401940740084070100d60300556180540744118080715007000207240c1000f00102002071000d0090b50003401c0c1c500880b00044501c800c0c4082c00d00e041980380e0314241c41c24135480c24908002d0130340d1041105038413000d80d00001a80c0d80c2856900c40d00d540c410844036400c00c2202d0100707031a001150651003101410002412500d03034000c00c3d0701a007541004c40100b403a0f400c84440407001c0c20b038140e0032126599000200745081d0b60b9110f4441038035100380c0c1d00862021440340380b001d0094056601400199150203030a44c5c0d130b0306010b6550045003c0c011201e4242041001400e054801180e02c0b40f1a5480200b05c0c2ea203c440c0c0c041c0c01460010441c504000c0c0190100d40c181d085030000304260b80c02070908c02e04880c20848010700309500900f9640c1d0750500c81c0810005412580020781481190490004804009081145414543c0d000b0038404919102004c604e06400ca200012840c48045d90b0500000d01c0c400c1044041c803681c055240400c46c40400c240c0080d114803074250b07020500038040004094 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 749893893 1250 749892643 749892659
    0x806060d020d0207030305102d1505070308090313030b060f030f0a020117061018030c030605012904271503121412071b0507140603060315040309 64
    0x1402c2000301c6140c00045490030b060741030040355008055078040b003065614004000c3c0d442e80048504c505045001c10581941e40000b2800c900106844020041c061100c1040100298020b40c4201c2c007050700c01000ca21000400000d440040044030b2508202c1425a1118621600028003056100c038104c04000000c0d2402e100042c01e022000004020f510b0080c070001d0010405141c400a108880c1d00030440c490307555501c54102d0104904003400e000750541e0b003070200c0c40c107590400740c01803000c208000304110840d8000341c101d440300200b4028918091807040054140300429182c104000e0100780100040b050015100300080e0340c0c0c2c100d00642c10005001542c1c14201b101c4070026030003204005120b102c0c5200500071030300c0c0c54206807050802c48441d0320b81c0034495030058a21400c50005a8035806800c80901c0f20b000c8841280800200b0314003107071b4075000742c001d041c0c400a00d85111441410006c1c1900e010f000e004005d8100c0003881010004032010080041d01003041036440020402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 749895143 1250 749893893 749893897
    0x60706020c1f06080102030f0402090612060f1b030402030c011202090d1a091501140a0e041112030a0503011208040b0d0605030c06070f031112160507060c0308070806060d02 76
    0xc0d9400d101c0c4045031032202c2050086404603442103000e0790040041002c2c0e44071391140c480d030042d130465040c4116158040070039069242418544094030400d41401413011802820b41e10035020300c0700d607440144004807a41d88501003038400940641c01000b42c041c0c29805148071100340c400c8084014180f0f010703c0b00041e0f5080a00707005540b15010004100c0ba503040c1b521031503600c00d0b0500000d00100d403141d400e600043c40305224030b0110388080d00d00086543e0303859001000400c40d584006084c1c0c01e090400180f680c0c0d08191307013480f5030010080c618003c207000c030a0390086c403903070f46886080d81c2c40d200c1015a1182d44030812207061000f0000032806040690280840044080d8006030346414901454902010030704003a120700d2080c04500d002401c981c2c001c1d41c1c50760b403510700740041d684c900c04841e00c3e0288186109030310501c042201480030040690020700c0a00440c01c48030b5450780e8100581d152000e4080140000b0400780007e0821070040b071500b89c000c0b0010300024a080c1c80818010226 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 749896393 1250 749895143 749895163
    0x30305040f06031404060203100b070b060102061b120a06091d0c0d211107150905100e06070f02030109080a030506040b130e07030f0503070c08010b060306060706020c 73
    0x1059020030103125005101040c0805400c442c28100501c0100303601d0118030f01002440204001c3d0004005481d9081c80c040c131000500030480f4035a103408070b03440e007101c40c03500c115002c900501c00d01000501e0725000e0104110f07015074a4641a2400000040848094000a02c5540d80e662941400a0059a10b10501404070601d00003000501e0340c4440071400c0845c0c0700c3d41207106280c008042070100d546100203802000404120900011717840c0c0080e5011805107607005000d0090760000500c0c420441e05908000486a9480e0102511002080f02400e1080d1600300042c001952520050410340010b01e00c2a00034010726403190101d070300003425610727110001c80706c0050202e140000a40c0501859402402c1190f090009294080201e0360f1003290460030740340a0344415070001d50680034000c800256421a6800015164030304090741d480d132065604450205291100082011040c411500c601038001c080901e107449002c10441c80b40c0003084191649582004400e900c105c08114032200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 749897643 1250 749896393 749896397
    0x712090611031f2309040609020a08010501060219150e0703060609020a03050a09030806010509010c020a0308071707120e3c0109030804090e03070807080325050a140c070303 76
    0xc07124007800f165029010325400041c10004502da034107001043d000d901380501c40103665610031995075090000240c8580c04010350031000e028804661803a040d044141030750b0a0b0380851b0800700c1110121401c00c440001d0141140d52140c0400200c1e01c010703080b40d1000b207480d0741155202a2241c840408031060380e40200781c0154001000c00300386800d03010701c65005002642c1003245a040361405821390b04020199410080001800f14450303001740107640b247c0b03401400051703030306441e8a80105982e005030300c10341e19101d1000001c1e00349040c0a00329041154481080304540c131884400f9034411011741da880740e1100100c896544009100c00c4a9000310064000500b072241d20248540e078101c8c4d24000d240d04100d8820b03404d0000c9104041242c0866144400015290075100c00e803d01303502440e42e004000f0702000400e0400e0013300c0c005180980184080800505101d244011003403000c0442240407032024001c00c20210701881c0c0c100040c0140d841d0040c503140300071081d81e0600401c0e800c2100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 749898893 1250 749897643 749897671
    0x141602100c1415070504030201020619150806010f171005130f030201050612061e0405010608010204030f0c090c0f0c0615180509011119020a080406050918071209061103 74
    0x84603d101c071144030f4000d151400c0c2079240c542582c00003910b80c00c0c01031410300130030810f412008400c801070b4400d040fa1041003503500e413440d03200d00015896403000e20a1200002c490302000c550402811041d07405480d6000040ca804000c050500002d008000c0c80150801010002e11001c00c01000b04010200e10076400019907290603000c10100c08007245042c81254450f2080180c102c101d07011440080d03141007081300c4140c2d1249402c90241c545a002010326500220f000070410140c200c4408034240f1400d1000b5410b9111046031040f5000d095a510000300409500c0c00c6503405140c2c0e1080185c015040894640c00d5440c05851824407a80103400203500060291801e201900c910341d00012300100a100c0c5940e028040e0307102e8001c0000c03000400b030303e0104805d002c40c0204812000254043e8902d51625540d200203446078010035030701401102c0031760601c1d40c0030110f888901e1242003191592065821554000c07401001c544000701c4496035101522514542c00070040c40c410310900640003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749900143 1250 749898893 749898913
    0x603080d020307170c0427020a050909150105160201030905070f05030f0606090c0307090807260a0201021218061b1501030302030a030903051603020a03141602100c14 73
    0x284049110500700ca10303045844140029591800200c4045501005042c400c80d81810400c04104d8107d0701c03000f010610015401070007907000805404468400c4030020300036580c10368102e0512180504503400036000300407511916071007034090402a4010f141c000b403080480d54880d464481541c20101d010000342d20204001c0c50100001c0642c031090350040c084c1800c141000c190301500181c04688040004000070759190b20950082c002083c2900448100e030307a642001d00d1845410407401c2d042403006a22101050307400040244106174183d00402880c7c01d054400c018a4001d40300000500c040e60300102001c1d51050081c05c040fa140341000f503012402d14142c0362820000c001c4113152155010700400100c0d402006950030111242000305801c1d40c90f217000c542e2440f401e035010811100380e001d92014154000f605400091198450004020214514a401e07008031a10400c0c2d05542e40d030010010308003041e02400160040c289080400c0450750340c60b119003428404940c0d9030744003036511 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749901393 1250 749900143 749900147
    0x8180d090f090605061803150406050f0c0c37051b0a0f091e0903020f060703050108070501030e07080d0507110a03030f0309110616051c05120a0603080d020307 70
    0xa04010114000c040182c0c51800001c51a03a00a0300c405a046c2d0a84456100c0c0e152410301a05082000d00107840406144c50b241c090028041a114045a2900d141c001001c0c0c80881007140e0342c58410100601d506080000c02154100f0800e0708500e4003040014080a103040222000603401e02ca50003138100b080d000c016251840c1d066110302d030700c2460758007c01c00c0341d000c0030b00c024002d4441d00000401c4642640c40c1d201c050207445880110081d16008078603060550200781d0541081004080d102261680390088090312002c1c0242c11054000c454100a80d60107580845c541516403003c0e0754520740d59000f51414810080321140100d600091200304115544610444451007143c9104405046403001014681c0040d003400c1419500c01440051005083c2c00759003107000204916510300130041101c141c4c00380c00c80102c54500c14501c000100b84202e403040c0041003081d0342d0706418514814481e903c215006019040e000350b0381c400120125400c43d0080114030300b040000359880c1081400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749902643 1250 749901393 749901419
    0xf01060b0a020f011109010c141c0e09040c170703050613120f0e0f0d051f0608150a1d0715090503060f16020f030318150c0a08180d09 59
    0x1103c407099160941d881802c01d10303031040d1107603107600b03107010f5580b0ba4042c500138240b281c102d00000200d11825079040c61146150400d402c114080d660764054040d400340500070409015034008242d500c0d00c603000d101c035040711920420300d8600d90048400f41c1e683c94480c0340c20101c05440005040c0341c501000020b1080c0d004880c0303490f07185072a00440385840100c008012008051100d44954881c03885a2080d5448220307450420b034010b070944020080074401074031040140c10010005a00305100003c0021001c00d2881c0c0032108142c0d29001c07950b035070780000c0040c9464558060020f1101c903a5441c003680401200001c0c05682d000ca01c2000d0601c000501650f02580c4024400d82c80081000314004074040c41d42e402c420340741103000b00c0a8610314240e007032186000c500030080c030003c000c000c04204103d4070035031a1152071096444113600346400c03c540f140111421000e03c6030800001102300c1c824003a17554484082e100c00811541c140113954207112249841800203088020184851842225 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749903893 1250 749902643 749902663
    0x30c060207030b011a072a2c04050a0f080705160501021b011b15060f050303031305010b090c130b090a0302090c071403040603110304030813050f01060b0a02 69
    0xc20101d46140d68034081030f801401212020380f004c0954640c0d102c100c2d02660300c5a03500c03104000301d01e1312907800c40c0c03003150000d50146035013510080300041040d03130030360004020603440c0742d0450b000031052980e2503040d0025201312142c0c0315070041903010544420008842e94070480c03180390b0304c42140c1050b07450403840d0a48031001d04d0000ca010041d80ea000516001d4100621482c5174820000b500103990369040b541c040c0d40d8520912014108120b4100d080305000c9281e0507081040780e441d410384d40c0450040d80100c0307401da402000410160850301810040d000e1007080085a28400100031514083c001c0c0d1b564480c1000104018101d44250b541b090090160001120b051092140000340116400d21019000740803150101d0300c60f00c004022629400d421101e48007800d03e0011495640c1d5010b48280c00000b882d042081001e494808201c80c011783d055540c2c980c468030781c0c1002c2a03050070000703021101072156900b0142e60690070b005440003000350314071068496400c00f20290411400b24 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749905143 1250 749903893 749903897
    0x1116050d1115060d060615030b0a090603050c060309030405101d01230c0f012309060c040b090f030f010c03061a040905180a0c03060b06030402090406052e030c06 71
    0x7100002c2e412900401090780000c0c21a000d0780c0700c51150402c00d00414141d000000038800c000d13031500340d02d03406811500c901c200a43c1c45041e8503a48042c1e0004032941e9000003001170704890000b0300b45140c200091504081d075013087c1c0e1b242c15030b10b90010f8204400c0f8207115010810038603207084450581103021a20000a0a14045510300801040751640140c142c60900301c20103e442c2d036501800304100d0041d07040d104001c100081c4013403c030001e00d03650145c41c40d04085041000900d1014045841d42c014074484c4180350425082c181d40400507003045011035040684142003ca041da41008407180c14004c4600000d00c01049402c028181d9400c0d070086000200d07400f0500c841c0f605540210303422940115070001d440d80f5090504101521402c889810910500307045805100360391110404580c0306210401c01d0700260001e000c1c2d02d00045502079402240a4000780c0854100d4100d5a40b241004a003480003495010040c401d14828050000c401e40401501380108400414800081c107518 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749906393 1250 749905143 749905153
    0xc081009330507020c09010807050901080d0e2119140106180c0c0506070210050f1e0a11180909010506130c0c0b1f091e1116050d11 58
    0x140540780d401c1440c040c0e0701c5119680e500e0014841c1c601c00d102960001d0001000783c1c485503529408144d40d520a801481e2041c0f94613400011822400141c0310f0303030f603031075911400f1819400b0010455018404c554000c00214689000480c02c030043c40111640601c1c0030f94481c1241c217a0070310030001d0340c403005c145100782c1c0341c118207200343c00c041101403400000c030500109544660381000c5480e5840782c00001c01030300c07c420602414035004110700f0030b612680142008580e07512000d4070b540b03480590782c01c0f0744c5050701e000c801d00f40002610b80c00d6100d03000e19808105007008141c061f02e59840b42c010441c070200a4841035903107181c21251a900300394804028000784c1407040005407000380308116990400d03510355540382180d0090720702510aa410100e14141c5280c40c10010001c0c1460b40b086019040c0744a101181c0c1c4082882141610740c03507110007442d0364a000d14544010040300d440030162287c00d00c10800424000007880c800706100318003620b00d030a41c46401429041110110702c00c240c203d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749907643 1250 749906393 749906453
    0x20a0914091b0307050d06150e1503011107080a090e090f071208041502070e101d09061f1a04050a17030708073e15030a02070c081009 59
    0x13140004e03180221a030040c001054585400204100507100039036080340c0c04c0004000302100106841590007288090891801e074013098200c401d900606080143d0074092040440e0410015040000c16810090061929401c4038a400301040301c03850f4055010040100300b4000500160008049080071507405a24540d07421b1414000c0c0d000700130300229514031009481d4800c0040070020000b110108596041c6030603004130090590250b1007141e6034425a60014043c541280f522520420010746940d407250020000b07224880034102440d00360408000c14491040890895180380c06480c0c075560314904014062000216448030102640000510313800e190003204540d025540250b100b070f81c4011601e440d5044040e00b1041c401d8082820b440440161000d0700e83c0c0c02c1054800150801c042200f004004440310b07801d9007420080e1003031001c40c07502c101036005802540d2080002c00c4619803540070f901e1528194100960840b131b120400c1406108080030800041103022040c80c1c0c035000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749908893 1250 749907643 749907649
    0x114060310020901052203020907020c0127030812040b07020f100c050f0c0606030111160f111906030b15092e090315050403020613020a0914091b 64
    0x807100c0d030152207898000550101982c400c0c2c1c2100e00880303c450700020002c2c10701d94801445060780c08200c1c0540c80c1c06001c02c00181c00080c888158920581d1044a52200c110080e8050080c150809404400c1590b0210000304424040c0980a800403106c00062500f0308260011312005403824055404c42c804d0250b042802154070244140e4100004c51640d00500e0112024405d84004c420f80060106e071001c828000403e200d80540000c070020301000c000801c00180c90300c40c0e14480641810b5041d020400100c00f01310605000d8000c1014004c0e88a810000c206503a400b0f0004010756401345d8003d0004d150148903031066000d0a0354a03002e08110030f102400f0b40c0c4034171079040e8881c003040c2c0040300115080c00740f10300c070b440301c00703500340c11849201900a440b484060000f10340c1010b08000b00d14102c2420300c142840b55425900402c4142c442c0c50096640381c42030382060381c220034180310100301c2880301e019101c180c07030099103801d4007450a680040d0504101c561a0046042d5009041046036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749910143 1250 749908893 749908903
    0x801090506100b161b090b01020d0525080714160f0b0d020c0a0510020403110d050304030305070f0501051e1006120b01020312130312050f0c091801140301140603 71
    0x8200c8085040c80404d0728242003a1030000d440b80c12020034942840070071940c50a40281219085c00e030202c48003072181090641e054001c42210000300e2005650b184241e4034564981c50880c0e0140d1203151800103a034492a144595544016407070350700c8a9100c074500501c48d203141004005c0809041c20310390403c0501c201c00e104084800b0a01130700400c0c5403428280501c600e800155025040f04e00c6031448414020194005204c265011006404445424102105480101a80328026518050846d0b4040c1d4580c0c010000c140e9030058070b5200c2d02c00041c401d114160103030140400b40111601c0c030300c0010380c9c03656004001004a9400c0001000b10039048001c0c003064040410300411072011a6004034070314010b404180c002e40000d0014800311008a07028800c01a00a41da0090502415083d000a6034020b03110b640780c02000c400041c200c2484c03100a80004040240350a00ca40701c440030421000600303811032403100200b140145031914013442003903200d02514a41070003034503240000980360 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749911393 1250 749910143 749910157
    0x3c020d02041703041d0411191703070210050f041d04060c03360605010b0309070f1208031306050a060519140607050f06070e01090603020403020907120b030102040801090506100b 78
    0x1050700d54042801c010f100c240b10148200301400d40d8648c01129211120b4411152054100c501209071028031000000300480b4200c0340c02510444401110840448095001d002400e00d10380c0c0600c004152a06617851011640e25103140d00701c1a810181440e004403406001040107142c517040c071050031140d4114841080246008001d404414940342008400c168568000c0141b45010000300768440b04038044c40c0a41900700440301115200c181d2070341380d0f40039405900340b404411500440018001402503a0151815480c1d800440032640d4001c01e2300d1060300d030348803041d8035620140094184204d410658042c0343c5c2e00440628901450415138880304006180108000503800050000c1000580d04007074119003240e000d440c004800800d840c000d81c68280c002510448001040d910a0080c6c030706880d0000d0030348401d0780b290f00040d140c84442015043d40d50385c84400380c00c01d0795000c2c0702500c02002010004102904640ba0241c28901b00400064003190014000d1042c0c41d42c5200795226 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749912643 1250 749911393 749911439
    0x50d0b070908120408120408061f03080414040b0114040501032a0f02100204060e0127080706030b060307080c0d0f0908040602103c020d0204170304 65
    0xa031200c10084a0941c102d03040740c801031144084509407601c0d140010401c1300d0344882074510344c5410400300b02080c8514032901d4207076070041c00400c50609849003002a50200403400400c02d507a2a950100c1c9a04181d0000b0708030101401002c40605240c041c00500d0542440e04407140031600b80300180c1030040b40191410107960314007403070b03281c1c108203600018030041a01551071500300410040c5007403416a07000005001e801c103c44c00001c214000d90701910425101c605c85111948011507084000d607003003000300c5420445040484860241800140001c000900041c60515402400b550091079100740203040c03c00401c405241d00000b500d8006c81d20120b0300e0f580b08180c4e162072001c0c2240680c130000a902c5e10841c0307802c20800000901c100c6e8015000da500000c01611480101c1d000007040100748425840c08400070b0300018094a040b5080c0d410f621310f10340b89000600200e801030000e808441c1d60000c0c0521040c107440515404c8445003200a52816040107180c00007220a1951441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749913893 1250 749912643 749912663
    0x80c1501061b0f02060313021002150a0929160c0b01060309080c0f100c170414070914010303140703021b040902040e0a150c09032607060b030d09050d 66
    0x10041200f8a071803110303400420342d540300d0400448103210101d40c441c04900c50880c01401155007400030642c400d08080156407164103503181200742e4050304610108448030046034003e100c424a080c88512901204010042b10034684040419104040c01d04443c0c00c0c8410740349e0403000207290b034400d503040d919a0310340446c9440041c03504c586c0074014540f105503c0c2c000c00005203802e050000f001121054944001d005440f0544000d86803c2d0003d200c0c0003001c0008000200407807080085010b01c0d180b01c40032101c40607035500b0341804076280358074030000d40e031041d400400c285548050007021940c4289106454050143c0c4c004c0d43e00c1460050120005640c82d8442d101a6620b5000006c040e401403c06e000341c0784001c3e141500c07000c0120b4200d0b040284941d80072081d0959104070521042a51120b000240c19612200510000c2418103e05044840002c24041019201800e50f1a20800c808904007001b40105030410b08004800e008010110f01d00b000305661300900302c514035811540c0c0031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749915143 1250 749913893 749913947
    0xf0f03080c0309030a08031006032703120e0c12010c0503150f090f0403120b100e060409090f150506060304021201060515120f06030309130605030604080c150106 71
    0x1a065005410780182c4c94010090500180408440214850040e42c3c1000c4282e6480309405d404881070407885680540001d920034011714a4445000d1240d800713401d10751007280441a61000740d40302028511200d40059040ca211401d115810007100001c0384003e110700000181d008201d80002411000b0740e0004d100a480c850b03c0e0160441c1e41c10705d026040c41664900695550008901903900b100007a005507103920140c012442014150900104086058003501800300c4a845001d2180c80d032011040000088004661041901451243c8121504034450341040c41600381c0484200c40150305110400c492550303150201c1c4c1d4010390440d1081d90441c0902901c80c0140f2450700400e4001003895000b040544a80000c2c11081880303100405099032110800200e0050603a000c94065006000b413110703e02c0e0010550460389030441e00019200e80d644000b074905901a1000d81301d5417000034801203a541e05020003800c5c0b044032002c0651951420310020041122038040a4445074104a22 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749916393 1250 749915143 749915167
    0x60703230405130e0c2e0e030610050102060f2715010f170c131821120b03120309030408030d0c0f0206040b150d050a12090f0f0308 58
    0x148016210140001d5000d140f60300c6048000e14201c140025648203404a000480c649680007450041006c40c03000c12109840c036039603401d140f01d0010041880342d08010303048503840801665119039031801041e4003082c5401c0029080c03100180a00754031344400b80411890a0b042e402c1840011035540b460b503140d0a941c2c403441e0803d49900170000240254000006480807104409811345030f40c1080810b140c21110100365031441c0502040b5006a502d40800354580d03019030002901c0c60b00980c411001c40030680d150007140310704400c000c0d5901d841410642c584d030381c4001a9014034030091002c00c070f502c00c01e6000a659540c1885d0084400304004001022700030300303205540080140c141188c4d1100842000c00010704102100480003c2070324081d540200d1001401c640140e4100d03400301256243c2180030f05400d1400c81080e5048240c40d4400000107500308400700015009040800191100e003034001c0410100e039200400d02e0412000030702c104d02c8040728103402c8960103203e00760303076288500b26 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749917643 1250 749916393 749916397
    0x22b111603050f0c0f1c0302040807172e0f0506010516080d140402030111040f150302090d0308060306101d09010e0303010815060d03090603020904140c070c0506070323 74
    0x10302005001707101d031024800d5400100f407014610b000c09100b2150301484401c81c00ca0103984903c0046031700c80b072010016250450440f00740c40f901c1c03c2c1500c8010900800a04c00c4071001c461880d03d80c40940860010b0100901c680c4500c2d101c10101170015090810008000340540300003003643d40107418600d02000803150860303c5001c40d841007800020070078181d102d402c5030115003d0b8082c1d404c00300c200703680c1a48107044a054406611610019506107000d000e0755135407004281060507401c1021629582d40c0520301840f16104c5d544414043c6040c000789802e160000d0450700014000308400d002e035a4480e90004401c0032061807900d61540d401c6801030140c443c6580c0206503000000c00800e0303802d80813480301c5088141860b20742c035030344440003403012101d042140500051950308044c041148a9001803804020081012841041c15481d002c51040152540a4090000110b8104018988800c08001c09040b40c8140c2810455200a804280034485114180e040504508030080031041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749918893 1250 749917643 749917657
    0x40203060f12032107090612090606090209030c0a0807060507021f0206061801060c03030e1f020a1b02060301050402030c0c011b0e030604020a18022b111603050f 71
    0xc2c0b01c0c096090200c41c0b522a44101c81158400e003030a10130b02c031071041d01c0da01c0601900103603807100e881c146001011039159101901c84078600e91200c0d880808036100d4041d100180001c41c10040e42d440c0468100340c13a0001100020f0301030b207905403003044030580c045981c1e0700303d030f0007401d00fa035481d600d91000440c00281c0d02003441d00d840c17061052501d000e46c0052050311404080d01c540f131340310101c0c0318a42c2c80017800b4481c040000d21264034040019100382c0182c680580d00c24110740b603806001da154401003541c40325107900700b90702003840364102d50303c2038942c406001c103005640740e480c0c000d801081207031005008142c001c40d0000003141c55103042400301c1d4019102103000b004407406a40c280e91543d00c442203118009a01e80000403407525000c9845401954001d103603407000e030301e04080b08504080d4114015800d607400d200d04c0310348184c907100172107910004180c25418950000541003c540100283c0341d0307403980620002e05851501112006840e030142042c5403291180316081d022072183e04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749920143 1250 749918893 749918899
    0xb0a020705060c0109171801031d06070c05071a090f0a0b220b0a12050405010b030a060e01110a02070303141c0b120606060d0b03030c07031407061d040203060f 70
    0x14508001841075100000851180e117050303407072050a40031b4004900512207568841c0d1410340e003500e00e941c000d81c40300c4190780419140701400c1202c0030540342050011503401d8089007918114000704203042c845280904034180010b0425070030080250554041c44200c0c900680c146100c40209076201549440140003100701c1c155283c000040140210aa420003107091860a690114500200305c00340c50000489581e03440c4803054496148001d000d000d0b100350b40e00d540e03801d172400303071900e05104c803c0311140242d5003c2440e0704003035052b070b00b1214020709480340e40400740720040b00d00b81d004c1044400c0341d0700b510f403000d00312440207201c41c045e02c101c903aa2500b229661611200000701c603040390301110400c80d080c0c00e00e4510743c00c8441d12a07004446044e80101c042281402c0e100c115803240c0c4c0c60203006030072641002c100086062400e0350070703041504c1900380c40e542200039800401c9400040c00552038460348107061201c2c150460001c406009100382e4010000075455150912001a484801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749921393 1250 749920143 749920147
    0x120608070f030c1202060f091f021509060702030a05031506040311030c090c0d1107021e1f0206280c090602070501080c030c0913050405011a01020105100b0a02070506 73
    0x3801880c1d9101001c0d1000b250f00304840b0304002183d8042c1c00700001466000b0703000b549000c0411018488640c0240c04c0180d00c11451103190600348840f40081d2018031031900100302e03440710380600c1c4c11400300c002d01102c1207500010810060b03030790220907100d2042d405e007822610ba840309034000b00c10030050b0002541000c0049000000d00103030020880440c2d0080d81a04c0c0803442c60070901165040c2100c0803514207008011070034940240f030f400b14000c864442802d0b4202011680025140c0c24140d60200307110b02c81a81f42e04440ca0010300f8040910214000c141900840345c0d006074485100400040da01002d4480d0800040c03030b01d07050440c100f480b0b00f80c10420004207400c080c00c01c40907805550010b06c10460040391759401062028050202c0c0c0c0e84550840c0d030703006d010010340e5010121041d0458194401410754040ba4014036020b24810030010400008880707007000422000c1c524181168141414000301482110022040d2162000c410340e40e1482000180c4c60202550f200715001400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749922643 1250 749921393 749921399
    0xd0b04260d0507020d09050f06070c03110f1e01080403140d091106040f03020f0a170a060b06030601080a09050c10020304051003020a17072a02010807030e070612060807 74
    0x1002008500103584080015849043c2c0480e5101403510a04001c9030050f0403c1c04503261801d0701c3d20202c0c070700030f106c5443c1c882c00d035560100d0b240441d481121080c400a04c580d015107040c0c0820005041d007581c11142c0d510342030618034036a80302d0989c0641880b1051010405051040c070300c040d2590a407218043c0d035142c10070f441300c004007800d4100351510110f980e440e05d024a0024111022924450340200d07609055408001a80c2c4100410583c88400c81e200010844800300c3c21840180040340640341110b41030500130151080914600d101e41c50130410401507030b801c242d140da049914040300041c8201c0c0743c0f50245c50301301030108550340000102414400039134008014015141c0549010b00740492550b004e905a0107041c40b0400420030554101540584000c200e641c0b001d582d141121505404540342c0e007100c051006071007800c0b2140348025041d5604a40002d410010900c1d007001108220101c164994541b40904800c008a004124048000a80140c00504030020a5030b400640d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749923893 1250 749922643 749922713
    0x602040b0c161e0b1812070f0501020303070804150b06030c070204061d07080712020a03060306050618070f0216090504050d0c05060601052206050d0f0203060d0b04 72
    0x18102d481504801c2e5651001c030300c607424004803c90701940c0850412145052001c0c1a141d508001c010490380e124441a946143e9104a120700c03408a200020308012400c104800b01d0400458004905542c010402d00c01c140b603004407aa03070301542000101c00701191003904030015007104c2c604154000703004030a1180380c20402d00100f8119100b20750410240390355007400d0300444440039460303517509518000216140d00811100340e1110b01890101c10201a00441404a810a0100c0c00c0000e982c1c4109008002d03040c852550441c0045400322404d604059103203003040d0005048104001003034060f0403086000300900251010f119010b51100340d155502c14000b401c00704e80c151031034400c00302d800035903d005101c0c03800c401d5000300250001d641d42000541e0b003540034108a0981410605500e410460360100c842c02070700b0150f4460340e03200030100452003520044c550a0b100a481041071016558400840b510400c2d40038501c0106a07499007801140f0700c100301c481040c0b00780740e10703200d240000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749925143 1250 749923893 749923903
    0x80604241104080c030f030702120f03070b1b07150c0203090a0801140c0a080f0709151e11100b040209120705040c0314132105030421020d0305040602040b0c 69
    0x51080d0040700c10010042d810175946409994050b081604100040c1000d410b00500c1550b128089a00303c508000c6010351607480c0d0f07407004c801564009076420030f00c0082908a22a1152a003c8070441d90500c400c6842d10548110713803440c000e600913075079500407910a00a1065500710070700281641c0000b90741e180124046c103820302140c4491080500000c0540071040c0641e110200e050b070703070800c0903039a00c80c0c840c13485a005072080d402c1c49100c00c03000a1074416515824041c00043d9502d499004002200100307102c0c00c04099024821404171403142c4c0d640000e0300f58881e01c101c600118640d401407020038020300c1000ca0003500a40c06442040c1d56110000700038040710001c1d40d00708103003107251200310211070312180e0084801c04510013148942d618440c204481900500503481280c14100b1618015400d401c0c0e10008208007000b040140000c81c0e4500840071500c95080c0100b07010103200944502d40d9010a1041c181d0b20b40100342480880d5050f00c024005008515580b451b442901507903803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749926393 1250 749925143 749925149
    0x612052d071e050904080f03060102101b0801060819020f0c0a1410140103110102010e030415080903070804050108041a0a0f201c1401060e0a060207080604241104 71
    0x7100c0c03503640c00100c6007088105a4030586d00080041c1c1000c0c00000b006041d80d1000c1c0c0402d0440c03164880c1d1624107070700d922031891400c804140455641c17051150181816030140d1181c0c0a0019540070001244070300351840c048207002c0180107075100070300c10625401340030f480e69030f118070320440159004121f0060466048401c00000310b03480d901c80440b004040d01c2000b40c9508955005400420018626000040074410140004545007520a40244ca9034000758403101011004100e0f00d0381042d0000701c4145c110360a071001d149040041d4541e004503211321f1164504002c4800f0008050080d01001d8420700c50100704110b41904201c000d020250009205001100b850618404a044a01d0851890a01018603401e060051a1b684030b41094028140401480d803125484010f40581000150103802a51220080d441d0150140508051260072800940d44411000e0000341e10010340031350b0260780b240c4400920441c00c10b110306c01081c0d443d01188401d09081d10216010001000340040d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749927643 1250 749926393 749926439
    0x705011d1509010b0d0602070602162301020304050607180b040f170a050c041e050f01030b07050705060c0901030228030c032708091e040612052d07 65
    0x160340b01d00c03980718200ea104502c0030743c2c80130b00591010001030154002c1c003070040c0101d40050078620a445045034040000c0b4084645a1210784401c41c003608070b000c0c0816170030b000c0e0021070441c0b4050f60303101c2c4d039034601030030a00c288615011940e0a1030609181480980407041c03055480700c0d603509851840c514140900005603c41d962101c1e200800050700000b46504040104072241000b07007840b00518000300300300082c005140c100b440d405117601845004442040600d60a98554101050100c20281280e01008000c200150110300d0000320f00b600148225290350381c1c0c610050040e802845114004c86845400c015080310300c00c2503011844503c181603e0178000c00e01403150440498540c408007410000c20682d815065101500124074124070a090781440c15500200007403a4600c60003444800e0407441c0346005ca0b1b401c0900945000346078183c1e809100d9a016170301c1d16166048a48050110909840d50303032000a81081714290b4002040141d03038105854035181480c440380c03140d601d46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749928893 1250 749927643 749927683
    0x180501090615050712120603051b010306050d11010512010e100e090d0809030f43110d0b070203090102011a09040f0804080d08010305010c03090312020705011d 70
    0x540ca915103066185850b640d555242d15080d803680d60441c2c007011704603200307040007044030700c0819041c243c1c482c44c0041d40c020030003401040c10308504c4c89481800140224105070070101c080100f6254618038400d80c9601401d06012004200d00490b81c2e4050003804130000010200002000c0c03c41400b081d0098404007a0006480c1c1c980b602294040d60948000c50360358002025011030a00c9040c5032900310317002000b501e28060b200d22009030180c1100b48400c220440d100e01400380c448041d180c4884014696091510320b8404000c0b2860ba680005e002034640d1940c148501195130f900d00c0d007810383c1a070080481040742400308000f5900d40101840601661a0144200000402c500355004006004010490359aa035a40790b200e0301c111084121901c807020710000c0f664074014041d01c003030801140d0310041e080d895800d1103404c0d00c26600710401418a03011401d80401d83c00320b2207201c0030018402c0503a8400c00c52900070300600b000303200c500c00765520081d0340303107103800c00b181c06800710100d210000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749930143 1250 749928893 749928899
    0x606120902010e0f150403030e013902060c0d050307031d071502030712020303100e04121803020301020c06070f11060402100504050d0c0501020d02070f0308030c041805010906 77
    0x6048880d0200d010380400d900200900c0306180c0030100c4c6030289000340440c00000301200f034a500300d030042c0d00110302140004410800030f5038070036080311f880c4202156003c101080e1210000036968041d00390542d004010041c0000e5480740c804980b09604203004071109010f9070100100783d50001d4440c140040e0a059605203402c0c41ca000081043d00d110f0042d20640e0b00d07000304000d441458403c4070080d808180000000b06103205500240c50303100781c0245a1b240b80c4205118903181d15a000308002610450034007010804601c1d161920b0300460070400350002c1d81107112446c0c40d5481c0e00c02903256000081e2556401e201243c01030041100f500c1e034101441c01518256503500800c061441c569029400003005403074109020152001d003070034803e1805890301c0c0440c1603580c0402e8151040f0401060422180d40e040010040441651000d48446070034481c030189000030383c1c07001402504010002ca2900e5030064216001010181c4a11640714044840c10703020744400d10036001d00038a814000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749931393 1250 749930143 749930177
    0x3010c030b0612090a05030a020705090109020c0c0d02040f090809090c0a141804240602070605040302010c050304050316151d010c1b09021206041104150c020a090606 73
    0xc1c5800010080c41c403401c001000200e20b20480c801442022107108140f01100031610070f20052203244202d5018241c09410402800441e810680c0305c604250310401c01100a1400421090301c809000c81e0030b05000000d9000150241a01e111b0258400d868091000b040005901c01410806c1007507a007061f0759a2418054034450140b410311802007240b800c900f140340051107008022803a10010580340a102100100c1c00b26085480000740841d4800c0720039800c2840301c0c440380002c1c5190710003004000d04048004109020b9440000c0c14042c0c0039900740700300141801500d0107424041d040350b0245404681e507450400051080711003079031000480d001c040c2d11400300d001622080c0404200191041d100440d40c00f40c4101c800d5030940ca40700e0800c420300804540c100000c110310680980ca5103451f03c0c3d0740c10030840180c030700d82c40b49203030109062000070000d040c0c0381140c54203845082008440e440c181c0d428445100000d511850348880403c040c4800d51002003510241c0e6950041c140c1c1007995 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749932643 1250 749931393 749931401
    0xe04050106112104061404410f010e0103140a090213060503030318010f110c010b0d0f03080c0c070305150c070320011d030d0c09030f060209060c030d0b03010c03 71
    0x20f4034926010401042c00218000c2d101c1c8a4155402074006140c9650381d4400e40c6140410315000101d00240c0c905001001031280f041d200c452100200f60207000c252030001491200e00841c0c00e41401000102800035278020341c0216450203540c09040b8561918487c154004c020318042244182000c41203a0703c810994421441503900140081d403a6444003450f201900c1410428600315640718145542104e82c10300868182c2e208210707000d511002990100c9e0309660b50740107114043e6240c2a41d00000c207da000c9156082c0307070141445441625500f00244070741c4500000312a142c03103100000400c01c20001080d480b4100c0d0f103d2040c81c9510340c0001990f051007010009000956500a140c1460003c0f590301d0010300c0380c3e44000145522940e40c00d414690581121038419000405e049070240300d05d0191104100140c94000c0c612805c1d03594a00d017448e40c182029154943c08a0a04407603241e5604480b20003041408407900d0b100b8003101030025004011303a95000b542440c424545007070103805 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749933893 1250 749932643 749932693
    0x303100501020f07060f0e0409020d030e12010e030304060231090501061d01031e0c090f062102180a08010903030b033d18060506010503040f030806010e0405010611 72
    0x3468101c00100c1c101b0803104407e014802e47c0d4060743c1c07400307c00010ba071002c038203403582032094071040045115803003001502c090752491008140d04040b03101e15103400c04003c495105521500040c1c4810003010405403031030004000c10b410b41444005a65071520800f940b03011980d0f100c07410302c640da072a800d00b21102c42e003100726984d98003411096201b0306d600940010315070200d0000091340d40e140c2c200c0c00e20280c0b054201c04e04045895000140004240410070f134000d032501d400d00400c0082c042840815a400d01d140b80d12202e540070801c1c060303907010712118a83c1c18000070803030031035103031070740101802804005d604601182c501000101c0508020800d900c0103042035411804440d411584807900c0d013003481c2040400408150410741b41001031003250210301c1c54140700c4a00c00c40034a0f1060807540081d09035414002c0030f10070040000c00d2603a00c40c601583c9482d00c0c0c0e5031502d4a00c0142c80210b400c05090340d10908041c0003003030040e400301c844111014110126650800d10101754900500b003e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749935143 1250 749933893 749933897
    0x7080a0b06130b07031103040b040f0801020f040e0a0623040e01090206030a020a0203040803070f1e080f090d0b0f090c01050f07170d0c17060906030703030e0d050303100501020f0706 80
    0xb901042045903040150000a01904100d90040b91100d02c440c2103501c02d8110703010403500440c0c01e12403c0c2c01c41603208054804400218900460784902c1c02c8640118803589014031111400245000c5603504100001d014001c440c190421400409200c0d000d0a44003413802149042c150300f02c02c072414000e403403055401600b00d031310b1900d80348590343c00b9500130040101984030810000900f401e00700014080c580c050310070190f40e68024607198082c008100300c6080c030200e15500502c0030444d048202c400c4685a1410650740342e415501084c244420040041d200d09110700401140341880c0c06c0451060080206480d0702c1d00c0c5200c01955503004003008009940800d01034200024103042031501c41008a00005e4100f01c0c150300d80000361985000c1950001c6d454662000204414040d003903046001140e0040d83e074505000400ea41d4525840040e00300858990031480d1768940c45c001c01c42d425040700a60b44d403490304407100107079010719115083c0148103842e542490b80e03002042e10000c2d40d10f84d0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749936393 1250 749935143 749935177
    0x703020d111506270103080a030e0f060a0b0f1c02040b040e03030c0a020106080a0c180501120f02131127010801150215070f0206010f0617040f02060307080a0b06 71
    0x208084c01034044110000b84200a103031401603031002002e80b4080d008501c9000c0007941c60501c1400203007035030036808401c240c1341d210000000e681c00d008141c030766102d40d0055001548603017400c00520b200b8a109440c5c0d030070142d05000c1c0440b02c080c925248400038000c2c0d5080c4413542d6618240000c441c0030f400c2103141900709102003006c001c01c481c010110490301d480003180781c03034480c400541442d0044404076401e1803c1c1d0b40810600076460342c846e01040404508005962406080741e120a08101004090312038200480085603507083d41c0344030850b0300950400c0040107148440310983c3c8800c3c4030383c00194001c00c64200c0d984a01c107035100300c000c040e50340554a920f45116014107844000ba007001b9070103480d520014155403031104c58420886540c44072600d4140080203814a1010b810400302032100c0d90741071104681280243c3c3e60000420304c00720340360b900c80c10415051642400b000b5032000000003070007184c660060b06140103da071840200640c2810108204d8130380300e522030782d0307403600c02e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749937643 1250 749936393 749936401
    0x60d0807060e0726073c120201020606040903051b070302040c1d090c0f0a030b03030a053703020c0a02030709052d06090702030c030703020d1115 64
    0x1010000c0d1110034498103022411800c0d000540f41446240e400c60100d1466050441620b561044a041000c1c203504010b000400c0c11300c0c101800701c1c008002221014a00701c5080d180510201c13008404000324020000d20441d02c9140000d404602d200d07050380148100004a401490507100e5030702d0302641a11050b10b0001d05d8021031001c4a203940360a000780c000d006001026071035602484a412400750b4910300980c0b00c01488a01c0300b0411300160b4000c0d0115410842d890814101307ca00c01c8000008031038480c808211300710060805140165014000800c009607001e03041009011142100c02601c9194090700d1078140c2050b1845500791084000a081c8942c680d0007640200340700f150407810b484a140303d940202e403405000b035000034115651a410400032208900c14080604003c00304d483c4c1d20294031100e0b45161001a18a910548001d030114040b1802042100e00114602058079210141400c01035103501200c03841c80082801104520844200881c41e8800c0590b556030343e43c05138031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749938893 1250 749937643 749937653
    0x250e060901120c030f0803060a0603020a020a0204020904060305100911060a020d35070908031809060a0807030503031f23040f0f06140102010207030801140d0602190f0206060d 77
    0x204030300c0944100c1e404042c08000700303000c440c082c903c05006e0045540d403030400c01e003402042ca8844d800082014410b00c074000b64164042104c2d28110340440c0c015131031300041c1000a00600050b400100b05104000485c0360801d00f41d0820984e05000e040c05020103600b0005010151051021080058002c0410b05801900642d400d5003500d02d00c991305074100104000044042045030707060078810519008000036103074029520700151041802440c10080c001d410703584029444000140f080e440007000442507100e45182000600f4050200c40d20f41d070b07807070a00c20b4036540240c400901150000e000880302d07600181650048a41501080150382881c2d00811000740c14003503001c0d8491b4440c48152004d4811b4003418070b941d10850390009241d0314200a81c04040d052079219410340e4018031a01000c00e8211664604564040307141009000c41c402c00aa010281030b040208800d101003106c4000c545181c1c0c1710344562000ba210b90004820b1190241d0b610a401c40e07100f5030001550b2050701c0010b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749940143 1250 749938893 749938919
    0xf0402132904140c0a0210111e0f0d090203150708070315030c171204060e210c06160602040909050d08010f0614091c150e030d0b12250e060901 63
    0x1140300d1044c1c402d18450407500200741d60481c4c9105064000c0880c65100e10088031084101c1d40012980481c2b03000d40068000e2814083e00b0603034502c1070b50b18211041591818810405640a940c5884802c2d162401c0c0c0a4406d140c15104980003d1074600e205009a1800c00031a040d65000001958018603011540142c0c00720070000c0e281c540030340380803c2105014a406480500015140e00f1003000f10b406c1800055408aa0304443d0a0b045550100148a0110394810803d130b05442c201ea48010108121101401403080204010700c0002d0024102c55290b0040d81191310503015101481d100c40c000b1030711000300780900054003054082c100122402503100411400741d20743c1043c1082d1820b8002600480d04150b0b50348012031807001c0404000203202d240c111034000d2881084101040e1819a82c0e900072880e00302611340da204ea40c06a56915500d00d485006000c0c012640440300c1c403825070a01d83c1c2c01e520240b50708100040003140342c000c0407500038840c80016124a80507881d01074460440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749941393 1250 749940143 749940157
    0x302090f010f060305060d120e1504170a080a141201030c0609050108090706081e0405160506071203020307030f0912020d0f0c0809220903020717060f0402132904140c 73
    0x271152800d8940003079140c401c8a80210a02c2d900ca00d032316245000c0340c40941c600114400c410680002840200040c0d1050950342c4a80c42e0740f4020a49003400c900100c020702c1159012000314100d18000003c010b0840c0c00142680c1403652074110b415950401504c0c17008042d129220103800c00b40c0244207013032140c40c49503449002c5242c40304c160403401d00b6010032032201b55000e41d0140c000241c02006440400610801001c0690b00c191501015441c2c41d4180704482e40a00101500003021501786d0340b20341c01010f01c42010803420040f50285183c074807440b1000300782400143c003803240e42140c0d07a40142040c4030b13011456100c0f013074030300b540b0340d20f15026522103d52990312013041e9000c502e00041d0041c03110802c9440103400569171001f810040d00c1e10290303500c285000c04203160007054240307020443d180c1149100310b0740c12080c5c486200007809610032091025600303180c04007000e840741d002544c0d0104103016401c006c1d016205201030006482891072946034059401000c1240300c1c00300342c001c0040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749942643 1250 749941393 749941397
    0x801090501110f09090403051b0304091b08070e0a091e05071b230118050712080d051005030d0203040906090c1e0201020d050f04030f0f140f040302090f010f060305060d12 75
    0x50305240d001c0b55031422803081d800781c6940d0700122f01885103250604c108682e1441008028207158140c4800800d001d10042401080250400f90210107881f0400b50b60090a0060014421141180310031070283d0403140058000c0390801010941c2140908011428400d0301500000c080704240c443da204403a00e00090f0700c511000401c10807820705c0071b100d101910703c0c03036404010207002c0d02e05005180c503940740c0000c1002405682c5000010f504042210071591148402040c40e80d111600103c40002640c0180d03054020745000c000b000f6404802070040d20402402082096110100f47e011030703168070203500100d088209003030061405100070300240c801c1ca00c0058584002c840862050300c01c01d031920408800424144001c15400c50074402e0200741c146404003c0010601d4000c02c2c01800d00c2041c014001c0c000b840d0116080020202c401840c2c01a024001a00b005041a1810030b0240300d00f030910a011540450418424068a4020400204048441c0c03401e45c650300d0355403100c5004941 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749943893 1250 749942643 749942647
    0x151c0503070606080c0909011109042406030608190506041e12050a030c1806050309280c0b04060f032304060b0a051c060504031403010801090501110f0909040305 71
    0x14064000c00024103644c0014001d40d41901051101005003d045064142d0502101d018020425010b5a4100c0001c5501090f84d490f0a0684001286a034614444035200c84c940800d85940540040701140e40200031194580c81c0c00ca0311402c03403002040b0003022908010041004628045134020404425080c155014991980d40141c0059041542804502c0c040b84200519805120b004005c2c0c82509020021030344080703c8510400303140c01000c09012000c00414182c0c00300300010710301001e003206941040001c00900000d4891100000c844141c5403000205205507004261011203860341c4542c00d102e240e582082c0c004d03000d41200c61100d14114600003141c104502d071154000c50007030000184a03040300040c0f060782e0b45150082402043c07190342091420340f44e001c960034101d40210000440c6e480b207240403661400c1c02c078240c02d82c01002100119828078194060070304c252168008110b5110307103058000a5015683c8900c41d150b83c10300608040d0308041c0b004590051180c0752240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749945143 1250 749943893 749943907
    0x18020108062211130e150a3515010e100f09051b03130605090102030108030f18100207090c020c100513090204060c06060902030c091311160b151c0503 66
    0x1120f411007a402585081d04030003d1101b412284000000018001c1e100e01114906000700080c11402000c02c48507094010314924400b0345105020310740e00758494080c2e518861001c0c144100e808000e01030850061100c5010031258280c5003007a804075200d89541003405803900b02c6070402000024120560f03001c94401c64a02d03138414400940c4166141103411000f0700043c01c00b201103810040c640c143c981e104200500c07080a00106540c22249a00305e001c1e503034a03048070004503c85100c40001c0c0c101060003402ca03021500420010295060000c0c01c201144040c44120f83e02e4884036102504201d04c0d981c0c0c00c5150f80b00d0001041c20b68000002da008070380d0b581d543d03075049034481e51045c0000383c3c0441d1a0420020f150050f05c0007080004802c1d07095040800700311101e4403603441018455403c4c4074000706080020f4110001c40d00400000980780d240708001c646414007404400c4646400b00170018140030404801c0e0039a100015200a0fa040b0900c0d50a044a140c031007016529807000780561 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749946393 1250 749945143 749945167
    0x1020616020a170315011409060f0d0903020102030906070f1706030a0b16030b040b0901290a0203070c06030e061801060b03010b0a030c0503250c020418020108062211 73
    0x43e0082000c041003075500d1405030503071071501128003012410409203000c00c11490180b02e06454581c403003102d4076032351041c1c041a200018030039548420710007400e10030135209058066014502c20340c0b1580644041f9540e882084800e03101c4411010b0209441030701c5152090080c07050780c0e80c03041c00038044404010b1070742c0380c1c01001070040310703400c20b1018081002a000e035407500400329021420354091208440800c00226082c0e814012918500c0080d81c8104c03e400301100c440c01c810400c084242c3e6522000340009442c0c1d0700246003601c11404c40c003000903401e0302c030780301da001003801005c0030703017140d4a41c0d940780301c61b000048403211101d45d00d0b41004038507098035800640c000c00960301c03450341d5058144c4000c1c003a240e40031034890600c0024010444074042415106d68441c040c41d131080880250070300103841d0700c2380c0c010000e5003181c40c284584030b0080034501842c000034000d8031500403560b540c101b0000490f19400c01c900031b00d0b00c64148100080c02641120300c072440b60340581810714071000b00f1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749947643 1250 749946393 749946413
    0xd0f1211010f0b0118080c090622020901090b070f060e0304051503090f0d020a0f240e011d100b041808120c0405010c08090d1e1e0201020616020a 64
    0xc004002d035100c4020f00c4030f45c3c012504411441e0641c0001d01141d24203a81191200b080c55075246c020003000313000038221340d1803c100c2d01c1c2901985501c1d03d26564507039040c000075040003a910740880c0b030400c404100c03021035a082d600f000c3e5100200001c000d049a56a034064604600305c41024030090001040b5035480b5131801584500c6001007503107038503104444520b0141242d440c000c03281c02c09600300e5501c2c1d5010032458109900328000c0c0c4040e040c94640050081000041c0701d01000741d08160303011600311904041c4100c0001c800038465644074100d010003c0101c2c5a01912650101000201e903400e680c024400a800c024000110441c440c00f03680740d81000400704540c201c80c0011001100290004950b411050700c0d94158142800c0800180022000c038001420a07072001c10801c25035601c003059140c200350302c84414402498000301c1c1844605641100325030003050035960220407003041c200003140300d40590042507261039881c41c3c1c0c880c410b6019001401c40c02410950340205850100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749948893 1250 749947643 749947661
    0xe010c05070914060f031c0c05010219020c0102150703090609120201020307080906040203030f0708160830010b0903070305150604140403210e0109110f0d0f121101 72
    0x2c000714403010301440101041000910080c8110303440202860039440020769134000543c1704d1000780001800700002d664102c90014002c2c065800000c81340248207001000e021244500d40880c0d0340103001c8001640c843c0301404203101c40c0107008001440d50b6101c0d401900f445402000006105080ea4407944203840030a890180940c0d000001e0018096002d4245503018500c0400307000d050a050b0300280c0c491161808038283c403100416075405010100e022101121301960400101034480c1c0750200b4641c01c51003100c107201d44400600c00e10700000100c1101e100c034010700d13813021581c201500510584c11010116415104021010001481c20441040341100078104046a440d00794108000c0e91500b40c07000c0c240310920824400020742080740c1a000b03480617240e200d80700100074240c80080021180c071518641c01c1020344818400e0540508070782d10801c1d52100c076000419820f0200440701418000d0800d40380c2000c9c0b070042003110305000b50349540d618210600c10200074083d030a4a14000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749950143 1250 749948893 749948909
    0xc01020c06010e09070f14060c340602100e01020909010308030f0c0721110a030302120105030303190504110a080303060a47070c14031b010e010c0507 66
    0x1078014010340c0081d4515540c060060001030942d41e0401c00558821001441182031071b250004038a034240c6e031103800b0340304000310b07007402c441780f1854244403182624208401e0504201d241e8890b16850415030041e04180d4540b40c00820110301444866001001e01d840d10039815582441804002d03074480408500840c01902a1610380c1031004001406c04405003100784101000c216940004280c0c4030000510b005409241c2504450100165000c41d10240070700f006014244c0c003d4109a01603014119140c012001c042e6640c3e22a400d0595a00c401d417040021440c3c0f5840d40c044c7c1e0f002540140740e000e44561588a012400303100401c4142c107054000b1a15a040801001004e003400849903009159a20040300f981c050b080070220540f07010342240c10081001d0313402c0720526189200d0b0b00c8061820460141d0f645040d424003265803c0ca601a80c00b0410030003004251629000486a40710070010202807062902c0900543c3c6109003100402c1c1400160032021012030014010200145554 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749951393 1250 749950143 749950153
    0x40608040c0602010507270b0307050c3007052a03061303140d0e03160c08030403031e0e1906030f020c0c010e03030d24050301020a0e10050c01020c 65
    0x1803401c040e403051640c02c054110380c50501007208450303000c41e03e07455000a00d0088109503103100d40c203c4411410b40c0084450000000c203120f5200d600900038081c140f010400d40c0d200c0682c4205000040d400e903c041c0210742580c680001d00c0d210101d00070310000d40300c1c5048030481032050240c0e491000220b80c841c113240e00ba00164001c41d080038040a68811410701c0218540002c6a401400e01c80c03c49194004802011600b02084001640b01002c0805504100c82e25454041c441c0e04002140040c2201d90380d022402c0007480e0f00000007514281c0b0341c1a20f0704207003000e240002440359450307200d0f404d04100d01401281010b440d00d0020361900c803645000000114281007015054a80c03046854200794410815444600c00c0404c02d034440b03070424a4050200c2403010002851030044424030000c02d8500040740c905203403001000c1c114010301d00701c0240c2e816034800405080b0b02480c01500c2c0411069981c440c4a444c0c610f039140c90304815414081e0030030003002885070881c0c00005c031106096100b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749952643 1250 749951393 749951401
    0x50f060108090d1d040908040306020409141302010e0f0603090a26071104091704030309060c05100c02070b0c031e0a170a090f0b0f07110c06090411040608 68
    0x880a80d40b98010030900003088034103901d1200070900c6048105030007000d43c40b50302d400c2c9103680c1c45c0c108040042c4c00000c480e4940e5101d0406100035030103482454462803030840e103104a010000c056601c110010920817050314101d40040d070b00d0701810300640b03900c440740e0385403c0120341d50440550b00074800d02c0300911398240740c4d24120005580d15012002c1040030034410300340348052001150f9805131312288403d52540e0890104000d0101c00000801c110091529020030071001400f400490b8000e6960030b040a51b0b902c0f054540c0407a00300e01910580011085107915074881d0041c0310740914074811a00344503034070422041142c22564046065030000a43d01000c1c4016012100e811414030240a180040c8001e0141040301d082c20920005100c1c10b0011f0442ca02541c4011000d6410914561f040318040c5020003211100f00d40461540c4103410105580c10b1081a4a40503001d0396801001007040d1541004215040009803550260b102c662401860303150034043e00040105889000003410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749953893 1250 749952643 749952647
    0x1c1e03030e0d0e0f01030f0e0105090d180501050301150c0b0c07053a0903060204090209091509150d0204020409090209090f1b041b0203091c0c0504021c050f0601 71
    0x8040c41440400640c03103c81030096540c860b9442204009007000a1020300c104620000b500c0c10704504002d41d46803508100c0070b044045015580540e040d134840804182d03d100294210017140269400603a01b030005111001c8a195102c0107101982001d40609460b47c0d903200c0e071a80111074010400c00041140c41c00c003e41000003011803c140165000704182d80d0b0034150b10a00444501d15000c2106019801c0c1e4a008914007005150001015035545480e200070030080c0d8480210640a0f5a1480010f02000d8400c0d0700c5642d203640013441202551211201d4250310b0003100003455004619040d8000141e48030300c02040101100400480c0d0f40c5498010080c26036001403881e2025000200450205900401e228511a146001c41c4d1502c0100501040041010010703010040c180c1d0022840c259130000301801ca41d8000710740e5600b00c4140d95240c540000d81c8684020204481c010781401945081c1d00a050541514070f00160a889013141040644070240e40840e40100c102090003841e513 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749955143 1250 749953893 749953903
    0x51504061a03123c04030b1f060e010e060415090b070c050904110910050406080307080313081606050a050a0216030c05160828021c1e03030e 62
    0x8040b00600001c4140c64039908041c071540300c00b000c0044081444c218407180d00910150000781044000300440303c86612400b444c2d2042c08151094003440000035000300200f10300010840002c05020882450103006403032000c000d0008078140f100e0150804059200c50003e40000c0c17102440d074004a0241a8010301f107400d00d81c000c5a0000317810040031020413080408101150030a690640da1950f89081581e103802d001c2c0820f0364001820000e010b1501100744400c02500c1c002c850406c01d0710b0f5070340c221564a200c0d0319402080c492041c000100f4204504039110740c5280503240c418138144802c00b2400040d403140000721000b5a0b50018440101e00901c1744590004411104515155101ca40c205e6900151480202080bc521801c8001c11405004082c10181d1000d10040070035210a440e640b2000c46640e000c90f03a410313149040c80c07641002d9a2030000c0b0398020b00844040d0810fa4082c1c02c0640405e0002c0e43c214000c05030071100601096802910b40e40a65400a48442c0f8560494145 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749956393 1250 749955143 749955191
    0x9020f041401141b010609050f04030207141005090d080c10150e0a021c0c0c03080a1103060904030c020d0c060815030601090207060b10170c19050705150406 69
    0x2100e140d2101183c01c03d808222902c494550440c0c164140700342d0009405001e4907000490000d00745805e00c0034038805030b0b130b10390b0046110782c00b42d5400da92182000f03c2513101449407254021010310140d0075442c010740c0240300d80e1002400300d0b004244952640b8099900c14100310304245d11411010141c04901d11841850030080043d0540503443d040340d680c410440a002000356076400590506240b01c164840b2014403c0003500b400001007d01c0060b00c441103010046d40450075100c0012644d120b14030030005512401d8000340c2c1981c895100340134000c800103004074148a201c2c00b40ca00035070307100d00d4030f20001441020b54490039414414002d190440103064101c000c5404400340645550220380c0314113490001100584480b00c904061001e440c0f81c0a001d6000b035140d030b0104240542c881d65a060013040800b0b00c9100d500c5944604104e81301d074027541d0b11020304200d011045144980002c1c43d030395024108a90500c010b03840501c1c0c1c0f00e081501d003150520754170742042c00040811410040c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749957643 1250 749956393 749956397
    0x31101020a050a05030901150305100b01210b01020f01050901021903090203150703090f0c05100801030507031b030813080706140913092306060f010e040903030609020f041401 77
    0x301014241c02908034058070444005001c00407001403009a82540215040b00d00e40003015021603603810070a480b03250340904400c145041c102e0480541d40035420741124049500c812181c64008815010000e000c2407803618114061381706140c4070684240116170242d2400c03400140d44400041c820700e0102b40c456140c60515040860303901c0565400700f0180c2d5907c18280d102c641c2562607110880061590f450020304d49208807100000340000c0100c0e241c103403441038030703400041810b48109503102203007480300809a41c0401e5007400025410740b0705146540c1c0007908101103a8480e07641c0d585a801c1070110b1011443c0b0507108100c40001041140002c10306428911007030000028900350074801e00002a004035000a03805d0042c80340359000310780e4150080501c1984416441e802200215601d40561544c40348401081c0d0600d4000c1d074102403c41305840702c15400b07244c40288805085410700a0307052654074031000860001030300081011844a40ba500d90b11386c02c001084601340c4182c444281 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749958893 1250 749957643 749957647
    0x5060a020304140906181f1706010b030c0403060b061c0b03120a051e04050307030503030403030b190e0601030e0d020f0610121e05070b090405092a0f0d0305030403110102 75
    0xd001d03292030340010850b00c220352148941f036482915082e1000b481e040b80d61a02c241315a80090314030b081540b4508400c3e00070080d1a0a6640d42c2d07d45451808282c07800404c0400030001000082c8140d400841c0d410b80c041d0100c4d09040803000408511002030080350b900396142c1e09030340101d02d4184101c458010420070014140301c511840282940a1b11502001007488101e4001092040c00e090340c0041c2801421122025180e01d059600d03074006403802c4002c01c0c03e20400700c1982c50070b815012003481e2036498031000c441c600001c5001140f40540158141644c50388510944072061042c84203480b00ea8004100d580400c20301c0c2440c0c518000c05070701946814510030311014102244080c03201ea0803000d00c02405185045190303600e0f041003001005403161110000f10202400042c00038030318100d8040207107956240580c0e0701c8681400290b02040300d0440762040301014500300501c5110040c0200c0300c0340d2002c401007901d040b1042e0054000c100c01104100802d6030150400c0b101c1e00c80b10300258 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749960143 1250 749958893 749958901
    0x60221071d010c050d0e0112060501020c010c080d0510060f090e2e090506040c020a02030a021c021c060c09080607080c190f08010f140d02060405060a0203041409 71
    0xd00409045051190301d40e1045184800c5070301c540c00100c1c080742c100055684814000c0c9000d0020b0700f208080601081d40750840c0601c55110b40316984c111201a00a045e0a03418403004680084104030103c4003e1018019140b50910034440c0901c6101c03c3c00c0114001070030010b02038a0f81d408414450100514486c003031000e40382040c646600141403c0c038906801810703140030741d105006405149219a05210005285449a0425405114203540400052288500407a02c0d50780000c00650154801e070300980c0141040d1411484d1021840b034820340c03255480c2c0c005400340d44824060300c1d07402c0039054020280b10552041d2030902c0003a0074040c480758900422035846a500909020500c0301c1400000c440300201c004450400050803928041c0a030170b00c101402c03006100b00b6200004800000100b0004800b02110043c2c5011090300309072840405c081000007012050201d800c2003051000044a03200e840141140901503009075445904040840000440074080503100741c1c1030200f40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749961393 1250 749960143 749960147
    0x150d050c090403020c0909060f13110f060d020d020405040e0a0c1403011d24010b1b03090306040f060f050601210603080c16301e06022107 61
    0xc04180c5106440d80800c50ba2641401da0600384040107040e045401c80003008004c80703010030740e0340c41030511b50f01d02141c0b9150b80110741c000e50002180201410318003c4c1d44540b0b464401c0c599809901c00404252402c103e821007032088c0e8100300346c0350800035008a4280030b140741902415540346000c034014010130071a41c6032a00b01204a2090201100302c0d64842483c81d1802e41103600e80c000058017200a1a0801d40a00d40c2e410a06c04203180700c0030081090b60502000882040c1202c26981d499414409412114540d81c54299000d00e10fa200421961071a07441c2480414800c5004404121002c0d895081c100c059403d10f002d1251058038141c20071100d80e0704520507075442d491061140c24040c1043d49200014245500040e11513000410162402c0d000010340c890000745400e140c6172002d03614200c2e00c000700e984055070420800c125080102040c0c10801c0380b0344980c0501941883c0d200c084003001d09403221030b18155880e60300007800d44800c9084000d1201c982c0c210703980280d03151a00c9800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749962643 1250 749961393 749961403
    0x23030a0209070905030a080a08090f0d12140702010b03190c03060f180803061201150504020c10020408010204031703040b1603020f0f0909010b0a080c131706150d05 72
    0x244550a4080842c18031845458803d002e040041d0461b03404120714200925550003500d21040044c0c40c01000a010400224446110840190003003241301101a01540c04400c901002c1c1500340d560104c0c414114441000c503401035070141c000195220451041c9070034501011035000c900c00e24000508c00040180052004981e0001e0b80024011300007800704018014082c008841610b1100103401030040c0f42009501490080320300d6000d512004c800d00e42600d0000c8128016540700c12010005401c154009210b0403c82506507003203c8800c4400f14203e8105810100c0641e602003001d004000f440500c88117900c0c030034144103046142c907030b54500c2d2442009000c4c42c007502c245502c0c8901e00317020740c041d50700141d650b500329900c0e00c0b94855484110b4120003001c9215002c1d02000003081482d0004403030700089550b440071301d40da0310340103180e00c981d102c040e03d003802c40d003200000a000d04c1840140d4a0218245011305500e083c0b0302c060b0345c5141c80350702d0110310030981100040c00041c00021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749963893 1250 749962643 749962663
    0x8030609060a0324050901060501020606131d030d06093b01140402040c0801081002070f020a0b1c0b01090302010e0f04050f0a0e01020310091d0f072303 67
    0x60100d9455848101046600301d0303d034001880c02c0f420f6405150401640c1d4081c1d03074904100c100030011541c1d4013054900b82e507103a208240c0981c024401141107414604d2510900d1041c4007404607686004d2035080702c4090f8682c080c02502c0e00081041c00107844107000b100020080c4508c1400f501191801918803409a8882c8454845102410604000d9542000107111080c04001c03ca10004501801c40d982001c980491045e0f260405e07404026001e5001107059070210002000c00032001c64024000390301211080da0088c49202e1001c0040c1c0d26020400081c1103045a041e450707007920507070010040c441d24800075265060072a408000e0741d0085450044039024a80742040c2c000300000b14448581c1132464540042c00d107810000b000070004140c0d4050492103c0400400d81d41d500c846080703000507038002003610188502008000510f402403a18108600c545105590314902c5551038070305c0038103800b9030b01c0c1c10500c0104145403118940c10f030249203284d140f6616141640010391074102d100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749965143 1250 749963893 749963899
    0x10b0f180a060f080321040503040b03040c1203050c060a050c0d1e060303110609070609052b030807020c010230130906320918100c080c07080306 64
    0xc03000881918080d00070400800030040c810010684074469aa2030b036108031103a117070f1071090041080300980400714262156800c40301550415007400b88207482a8405401620141014103021406469000703100100f14401c0d03c03000e988050141d515810079200a21941145107441c2c00c012007608000100d81c440b020460000035000b1084804141101d440d032500000c180c506280407003007540025441c4000c05517070b403c680d416035030021096074a1101740140d41c0000c07036030318042080d402e11880d00d40e211002c200b64642c46a0b0341407a090303d54101c4600030760006045600b0712013807940500ca4144021420302c094481160b204de128425030040e24007407030314000c10011510030403084a0076a06442e4140008002042d40c074500d0314054103e0707000300c810341d00071420b05440c081d0f4480b00c1003000425078407031300016011f41030410a4161b0001e0210280c101604109480110b050084041400005400180d1100c400381d00a026003002010700c05890310800001000c51a4030040c0c0303a20031811 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749966393 1250 749965143 749965189
    0xb1f08071704050d0206010b04150c021c0303092006071e150f0605060306011d01020c190f0905091522030206062e0e0402070b090f010b0f 61
    0x41044a00c41e1108140940c4040c898060008000b008120244084915400c464060b601d13291590520f100d58030503485440e004c0360840c0022406503610240c40b0740000c0c20a0005c89080300b020352040320350041200000c0e60ba44180c0e04110305580601c0c0001c1c805000d21501d550300102181580c03040e400c001d815041c80d4801c3d40901d151111255550a6001800941c1e5003a400c80200281c582901c0b08400c43d414403402090b01c2c01d0400c1034911820050350b440820f0104041500d1424410b204a1030441c0100b040103166900c1f4200019481c201c1441c08003c0a85001601d00b80314140d60000e8030001d080c0020700c50b91510000311400d6125000741c900110b9100c440c50321103520100d2041d106064104000036050607004034806208000030307039140c401d010001100d45039103940342c202040140140c40e0300c641700503c240e05241118401420041c90035440b5101e01c00782d800d0840300c180e41503008401d1030740314120030300880c2a001025650300c803e0740320040c000b0b401b000b4280e13032409404000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749967643 1250 749966393 749966401
    0xd060e071b17040608071b0c0e1005061617030103031e0e03010f050402120609060a020f09040204120c060e0f0904030c14060610140a030c2601090b1f08 67
    0x125000382d240048420b4540d55030380381c0d0340001a00c860f8007219880042080c0480009000f1428030000c080ba41d070015104d0f50244c105a81c0d41003800000d009003207910521207000c070320754890400a1660025030011180d0049043c686031041180c0c1000c9020b0007031041c4010400a42c1059a003c0c42d001c16640c0c1d0005202d40c280c0440705c69000310705095040d800c141c2100103800182d402240104e000355049000d0b504282c0311503544038002c2e00c0a44ca1075105a00103802030007294041d28074240e1952030360b4074101c40500080c017a030700107030013542010404010b18020403103035140d188018100c90031310000042c2201c000032600d454810030103016106940001e000c25102c0d03038601d800d0a138010000d1a2004011945590321441110f82c103005544d4800d40400903401034007044ca1000480121510b80192410124064100c280e4620280701010100300300725003000024201c528110125040c05614000394501a9064409054000d005588a20281e6900c2c00c0440810000d1070070904401c0d21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749968893 1250 749967643 749967653
    0x60111030d020414130b010f05030601110304030c06030e0a1a0c040302040e010c021b0607020f0a051e041505100305250806090609090d080c1e0d060e071b 68
    0x46140007000c1514800100401c0050000c04406021102651000f464401c0b0700341c0c0301d00b145d00c11030314603001c20008e6445510080c8034800840d400403042c50144070305181580341c6032454100750070031122541015000d20420740e1520403504003040d80d00081c1554201522008410800c22840e585844410343c0041c030030440d01d0003100c005580c058400c110700e00040d903010340245084010000140565190403201d80c10302500500c86910080905103010015400c2045060800c058139811401003a07000503a0303696001509541c04003040c010301e00300d4011042004885040b1b0305204c04590b100d10900050306d80d1103044107403035050308000406441d40d02804940441d01074070100880c80507a070240324654084c8a06016803019504054152601030400154600841e8051106c1e40940036007c080b9209045140e000f0714588506458200c403010b02110701d1003171885941c410203001440d586c2114091003480020860b0111003603007400d20320b60080c05e0080ba070b8000c1c03c003155150300c0300303042c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749970143 1250 749968893 749968897
    0xd0c0c0f080d0605090106050a1101020406091206110703090303020609070b04091a190e0a0b100f0c08040303110606040504150e1203010e0f0a0b03030a0305070203120711120c0606011103 82
    0x4c60010400b0400750780d81d400003481030703001100c414002032400c0a071040e52481402540c0c02d0310b407142c56604540741041c0e040f40d5401904501620078070b4451035400c01034908039000b0b0502e18065540d1080c094114140a460109c1c080c00200a6070312000040000481881c00d840030b80c0c500c0c503808500ca401200d8102c1c075041c1600c14a95000203440e503118035290040035580121350b00c0244500c1940d840b0000740f8102c407040b000c820b40210905400205c01ca00c503800e0481a404181001e0410f869541c80311803440d006a04101c011070b05084c0c00c0390840d001003001c1688200221010300280c60310b07549550400c084110750b00030b02500c40491717a043c10750078403080032100500d140c810b48030f60b5a83c40100c01408255000761440c0c000c00085160242d01b40a02c458202001d0001c6140a404180072401440010151002c41c0814440d0883d000021000ca502400b519522560703d104280103007410021030304600058503d00300503021068801146031313580803200b4200818201d80c100c013958194 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749971393 1250 749970143 749970149
    0x30e01030e0a020a23010c1707030909090b0f0114100e120105041203270f0f0501050702060103060e0102340803090322060e1306080a0501020d0c0c0f080d06 69
    0x41043d400c4003051740015240c00302c441d000e01c845240c0c07003640c0401c01950510807900d0045c24094900c3d20a000031805c000041400500c6480c0c284403042e51034850404960645008031020983d130014420064620a000e50140448084030b0250b940c4c0000007070205030611030080d0502003c6008040c02d59030b0380d80d0000c44e441258009102d03900d41403070840040c032821020180442d00d8580e001d0880c000f03504901320040c030503840022841840761282180c0075140082100c4410139145008002074003800341d61302072101a001131826505500c0c0000540300e02e2000b035180c40e0705c188001011300b030b01e80b24015007251030350300030002c000e02c90001d0200300d070010744010709148400002d0010001d0000b00070a01800f9016414102004560158140202a11602001809003c541c09c414a401e01c680429000015000580c0701d546e5003285050401505090b6044e035400f048440030740c903480c066010484400d103031982c4820303501c0d034680201034600c45024207650404603500c2c20100103607000b1005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749972643 1250 749971393 749971399
    0x61e031d01060305010e0307020108010303120906110d14060616050c06070b04032705040e0c09101e0302090c030405070306050f0108160b030c0f07060c111504030e01030e0a02 77
    0x8003000010303540a0519440225415880e001c20480040c5e0b000c800d5445840c4d0503900d643c15a46141c804076102d02c03041031407840d01c035501c105d41d0000601502c1340600d407441f003041480d101e511541d0b00c03908036185040f101c0de0356100081082075680eaa101101e800441c0040d070720344880020b0602c00e00d042e40c21095160400c600181c3c0e10184100a0000c1b0300c228801e503500c0400c10b2503058500400b403a00ca007a0900310142141c1805145010381080070510500b04c200c1c0c45400f00c0000091030000b0a4940f07584910107950248562200030080c040c001a0308070700040c078589540d010516108005051034080440800884d08020f4103020000003548c00280900450401032148103401c4c4081c031901c000b0344544100c4280e440030f0100074100700d41d9804000e40c110b40e031722403081c0c1881c0d00a00e0b070308020345c0d000c05c80d41001030114444e004100905545240100c0a8030b20303030919141c184404c20110018940401c40080d61160759410291020320740030030040320b03481c41549819849940258 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749973893 1250 749972643 749972681
    0x11030a080a0c06061e170316030c050a170a090522200705060a0b0306150603070c05010e030d0b01020f0d0525050114011719030915030902031006061e03 67
    0x6102080c112100036100c6e408403c41c1810004001a41d403031003802e080403203c0d440418050b001c039000d02c141285e994000c03006d031000001d19a40b0408036645480315081c0340b0310049519900c56920583d54000745c107059801d255601c140813510301c8019a4076242c0e8801d103459030038a01c070241018000c000da000003111300c1919501240307045911403100b1a20400103902c0d01b070101649180014021340180d0555208149808642082c012160300c001c00c41010700c190301300b5180009100744110b03d900944000650380300c120b8510044242c80080c0409030465001e40c1421002010106d803080782d04945003851596484d01c40a144104000092058001c2c0e81e241085001e00c101904032100b404800702d0700500c6a030702c3d440d815201c0d0318906001d000fa580071109001c0f0200244201c000d41034042d050800035a9560b0000900e420050085900080c1d1140a10340c11410200401400048040c90612405041c142d0003480e00001c141ba100e41000c41c1808155564040e90100c09000f40c0d803c010f003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749975143 1250 749973893 749973929
    0x3050c1801031b0f090c02061b090f04020f040303080103050c1203030c030a06050907030b091b25050628060e2404060915090c1b0302010e06100311030a080a0c0606 72
    0xb0032500542d00e0140c040c5800149c440c90341e60700c0d4126102c0c0f0166030307141000301d850107004104161150309504036030308000500320a664074010304000c6200380d6540904d5815880c0c0f15042114031000d4a0240080004040380c0701c0c00442900c0d030007602d50070034980300ea6900c0a03007000390006a2060341c10901036010b02098680c1a0041c80351004240c0d901c10aa488150820b604002c50091115403003c00384003440c810714042d000700d11100e030380b00b16486240f50140c0307440b81005000c0d9460360154a0000c096040041100c1d9140b54404039040f040103100e1501d211080c040000070081c43c00381541c032806400403c10b8480340409920094410072030345448441c0c0c80b0003031640026048dc4002003907030001d5400c0e00f03401402e0300c4140b41c1e5110681c481502c0001e040b180c40c20501241503540310421048000020000644100c503520703030b003503212869818540301d80c1d0400d28800f4040d40000e504100403841d010200c600444251034190038100c0e55003481002444190812445a62298031807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749976393 1250 749975143 749975159
    0xd1b09050a0506031f020a032316050901020d0e030f0105070e040f110a110712110f0102010e1e190c140307060e0402070602090d030903050c1801031b0f 67
    0x40c510034141c8607410001a20f880c8209035440b0341446417428032020307500365005012800e402601c0b40d4074060501040e4210342d002420212070b1201c0400049500e031904011190740e8250280740e0f48551801d029152600d2200000e49928251035680c040c81100e42d5861a0307624200514100e466016000b007100d0700705010002c1c0440d1455045074811810b00014100c2c05848e40705001d0610700a9103142d16010100100f6240d985a10145066501448c5000181d0007802070791300c3c0c403191080400740c050700c4a140c100500404602d0800e811a0f24003408104040400503101152003000030415076090b04d00c112035403504400801480b85039500c1c103002004c00540300c0510b400d075840161165034001c10032040c5940c503030080c0300d1200042c101445150f01818154000d100c14ad0045501600d413500001c046440519034140490006102c14810001d02c1814882240d00c0035084030b0041a602920040030b0300044180400f5107040c0c01c41580540404644003d08010a254034841c020700e90750303c0c0c01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749977643 1250 749976393 749976401
    0x30f060a081203061003060e041109010b070503092116080601060206090a0609030e15030603010608032b1b17010e06060403060b0d210e0607110d1b09 66
    0x198000c2422100224002002007a05402600d5540400d41166118070401078040000c00c102410306903500c40c04148401c460343d51134130407030080c1c0354141c83d07009135018000c030100164030007809024180511b0000800c04411506d00250446400320780b80042e2501c414120130441802d4411300c280c0410808240d00d1403008012144d80e1802d6503030507a40c444090340c80c1c540450741c5200c150442d140c40c8002030490740c41041c08600902c0c20300c12006a84011802d0192040c050080000001c41000346600d801d001d20405400720034007460038411250b02411004500b1242260002d00c443c5410715020759030341c01522049168450060200000c400c040d0002001d204030800656070b030b20022880842140c1c1c1d66004800141600745443d2468031a0710080c5203184420303a020025111041c0032548544802240305514a074502103038540032805000040302c1600d00707011310010b005035000b05e014085e4031195408261240b10a01440c0d14114100c08401004e1141d4500b43c040041801006544 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749978893 1250 749977643 749977651
    0x4051003030e040902091b0c060a0207150603080a0c080f0706151a0f0307021f0c18210311010f09110306060307140d081b010b0105030f16050708030f 66
    0x11811850340460041c0f00655202d0760004c4e4021505002007040355a50103005204104119140c60901000040150820701c09561600119802241c41018000300724600740201240a604100d054559070304c000349406281403100074000100b13680740501c080740c0110391081c01118082603980103540707071900c002c040c1c034030070707001000508040840c0c0401a0b2000046240e85208003034200700801188800b2548000c00341e17401c5010302020b0358040c4100000000d5031610200000c0340a203030031a4010002440040100150005401c08000a000703d006a01c85108190303a0b40141089a050075648929041700e0700116602c1d082e070b808040002e951280807450310402c1300350540b0914004250366030701c0c01d0740c3c2c2a070b1542141008005190003c0d5514000c21001740021a40c0c01180d1101d600b40e400030040101c40700380b4060310000c0c3c03030820301c180070314000c090a00c1800d60900d105802e0400100400394000d0f2102440a106800e002e03178244c541da04d500041c6d440e520724050640c5654180d09035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749980143 1250 749978893 749978897
    0xb07060f0b1e040207030306080114071202090d020d140a150501060503090c091f0608100b031b0f040b0f0a0206420409081b0c0a03020d060b0405100303 67
    0x10089141d82d241c02c038404a07400509800244001d0079140030000254007401040b03050581e606800590214207000d21240701005c1149a0f15a1030011030240885540324009010248104294001c50b5174903038a50060341d030181d40f49034100c2402e01e021007080c68802000791152041c0c601c402e0411210a00520314046146018403080e6a120001e490394001a6003001003074003c58103410160600c41d56490313000c0710f01c50110502018600301700c0c8a511482e00b11400051103401000b00c00e4050a00001c028031070040300c6071a510300100f80d1180625100200c00702c0380c50004406540481940681d005450300d400303600c1d928183c2101412407544015004000345c00f800d0001019111048001c02c0c61701000380c240c0030b40038010701d481c143c11260304040340d01c02107030721059082544881c400c002c1618481c0703a515a07900e0401c40c5920980105a00003203030340d0300ca208086295100c602c06502140e42c1a10070303852000305481c0c090040e182014400b81c00038500403c2040e100340307103044181203900175 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749981393 1250 749980143 749980151
    0x1305030f031902030103080a030e01060e0106111507080712060f12020108060102072105010204090f020c07080d020d032c0105011802070804030b0402030a0f050a0b010626060a0b07060f 81
    0x20002d640582c0070921019100711410700041b607045010760002c40c000074030b030703c00011013507111100c0340e8007210282c0007540060000104033200751820094200b600b4120f105041c5149029100181070301c500070140000c00449121509a40e80d041e04444040d1909140b60044262248a8603401d00003840c0141e000405560104806500204147d01034481c0e82c89000c0000c02000e02100e41e52190603000c80b00307991b00f0000010a8a4213105101c10301c0641725026941d01402800c1c02c0c6000d140e42c00a020640104401285c0c668001a2202c08000b860a0120b14030740110034182036112202d03c41c5018080d03000c0e50003084481907010300d043e5000303840c4851001c12000c4241c0100d01a8070001001620304000c14008a070720300c05210b0f80f2030b100804494081c0442d070b603001c40c4103c1300ca100701c841c4da001040d10401c1081c4030a40358007401e080d28003018075096a0325088031640c41c40704401d080280035004034295817644640e00019055604080e0707510314184c40c068008050101c0c403400c0c0c062074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749982643 1250 749981393 749981431
    0x2010908070e0403270302010e03071d160906080718032913030e090619030b10050904021e030709091a01090207081c09020901060201021e03060102070e1305030f03 72
    0x100482915980905c5d030860f00d0b019003594019141d110507511455810b1080b540000f9445590184803170f60203074908034400450500c014094410940e0b64021001e01000940c00d100342c0341d01c5001203600400500d48600e54440c04c03128107e02c05c42a80000d400e02012603241c500d4600c001152002008480b01c0108c01a65485441c1081c00d00c1c08000030000303081c51490b20020700d0100d04080d000340f8000c0c003200001c0010049644030404c036510850f0480750b42000c101e40381900e04803580003080b0944180029140680c00a07044509900b026050075401c5100d91035151010001500500841d0008001030080303800c1241d14801081c000c0d912520300d1030000320350041117000351000568091007e904005107401901030342003800c43c0c5a0b2019644a01e0000541d444040440c003d000c13507000181d840c00c1061000b100201120700340300c04400c0400c00d00c166668001000c03070894080c982d80a4203622160030f0152441800840a0007900c00810b07050000d40315200154050404031101c900d450103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749983893 1250 749982643 749982677
    0x6090e0d0f0912230f071404110904021c0f1a0a03020d0305030910140402010818100b0d0b27120d0c020313060e1302131202010908070e0403 62
    0x42c99000741210044400084000035003045103070009900151060100c440e05281c1140c80c00006040786030040d400032100700315450750b45200e500030700003d0741c0c10300500042d4400808103118500200b4010f031b45c00110208140d404401e40c06e1440c010304030601ca00b005001103000030308803503894012040c040b0340d15126540380a00300c003802c513036001d0081c086100c070035103007a502d54100400320411401108000c0100104510403003200d00303d00c1e143c03c4850b04090000411241c0c00a1141d02d2800c0c10b1030820784103d100041840a9001c42100030500d07620b4400410284251414014800340c45401030080c104005001d0072a5201e945050b603c400070720306500c2d075503241074280b0a2100402004440790020454004001c0090103004680c9040c28140040000700303100e5101e200000c1800c19581c40900d0450102d0303a181038015000d50509581c590114070301a003d2081d010101d00100d0003034110390240c060b2800a20a12042e582032a0351158080600304080360201c0005010801c1a04484 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749985143 1250 749983893 749983907
    0xd0b091801140906040209130f0b07030c030e0c1c0c0e06030c090c0d2706060608071d040b0a1a0a0e01051204110604180e07090203090d080a06090e0d0f 67
    0xf4a0704020007003900c0d5a000e000341014098002140d01e2803500c21140031400141d15100300e0342c40380b400c0081e40c0c50b061750001d08480b40030b4510b904140c141844180c2c800c1c4001081c5407140c0e01142c11004004c00300c20150708403004400001e21000c1040b01c0055000c605030101d40c4034100685c2504c00380b04d403004c2003105203c030031101c543c880041072010040074501c644c0210040c0050300100d5110308030194285604051002d001c4071019226402807041951141d10381c2d0f04034000d8140000c1c1c40c0385024102d2000c0b00d1861030540641d1707807214600c41c03036916691070320001e0038480c2c840d440740040300802807000c1e48103240300c501040c05001141c9140d44210111842c0b02101030849940c3d848507622015800c1380d4609465000e5418400450305034100c1e4010030011114038800622049401c500c0740c1001503c3c0d002c0e20070710340f0600c100301c100c08022070b041103402d16501e411615969a0444107008041580001042d280f070082440d00c010000903800c8040b07003080e105c3d800d150200b2001140d00c1c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749986393 1250 749985143 749985151
    0xf020705070605250c0e271f0e07050a0605030103110f0901171507020705120a0b340507150614060a0504080d0816030612080d0b09180114 61
    0x540c141c504d0080c291481003520a440c28820145282d585a848801d020159030640d00070502050003021032004440b848038074580b0030944009081241c007045070581d41c101c1e0300d141900503252504802e2400c0c0c8400d00984014000c01004c6c080709a813542e4000702186c2003400b00321100180b40e0f104103054500611a2108030500a003201582ea003824141e0080c10311100c281a00c600c038143d1120391200d2103140c0700b8415912a4001c1803101e00d80f608000c0101d0b00703801440041c1c1c0000700000c01003103e1040c000e0b4441058103100555142c042c0b0700581d803c45424940c00424000c0b82c103c0c450716404030007020000d00640360318002c41d820014580448400d882440c0e55820b041680794407a0900d9006451079075021b04005003820707511070555042408640782c080015036948104149529900e00449a25030589003c01c0154100b0141200134032182002510962001c81c0c001e52031140c9400051002c100030700032400f0790800100104032810320750101d600359403c1080c0013095034100c81ca11481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749987643 1250 749986393 749986417
    0xe010605030405120d090c03050c0f09060a06030507020a0c09050f090309030d211103010305060f070219080d02180109120c03021c05030a0f02060f2509090f020705070605 75
    0x4007808813001800c13075502155050b01841d458090100100b415008110f006602840c050700580b0381c13500400000c000525a002d128526074800c3c004103840324142d540c01e552080c00e000810344c880100591505480031342c024202000500042920b441c40e802c21030182c182d422120031705445185101e03482c0d00442d6122030301980900040c4010030701c506441020b540818000e00c4172a04501200d4094402c030a8807504039480001c010420040c080220b240e1003a0f00107541c170b851f03081c02d6030025161041c01c500401052900d03141d00f42403105160846490420305242103503100a480414045082c407141c03101d021900720714000640703506414080601c142d00c0809010464216400c000d0380824060f02840c4a41984d02c8000018030700b000240340d0983c044d00c440400c0c41d0304200003860001d00402803040c001c00541400542d1702c803103404444c0c244540c8600060546a91011201e406069011010315824003040c82c034150600d80c01060600d00510560395026101e038000e641900c610700300011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749988893 1250 749987643 749987653
    0x3090515191d1215131703060f0603070e13062117030c031803040302010804030518031902130b010503010b1602090c0d1a09160c0506100e010605030405 67
    0x2080070b108244802000140003090040300c00750001245980202120300800c541c03103488000c4100800d4120b990307200b20003452074207117901a07a540460394a40c00c2032000e982000803011560303a65498040754074410000d441ca83d101e240c4480c00501c0d014038006a28015007100070b101c00c10b94070070b00404064a00700e6160718485004008185072044072440f054807080541c071514104800154021801a0002c80381c1d207450341441440580f940090465a212540c402c10003000140d8001c0e00441d8059018103000ba110910300300c10f0070400b103072281455418001c1710400d40e4074015111b50113180302e000b40e8480340742030b0300c40b4090300c2120311000f29030380460320601c01041030010f0000240b10428224a40c5241c40340c156000c00c0c4a442c0c159000901c5d1040411494488990382c07058140716180d040c0c941c070325001404d010030074143c00134100c404240b80c0140b07550240c44c0200180c0c5c40681c0e12508440c0b141c41c08002c0001c0841c070500403045031101e5407000140326880b07001681c0c000e40e00000609 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749990143 1250 749988893 749988937
    0x20f04050c0901110a0c030506010e01060c2d1211010c02190b0c07060e01020a030b0303070213110f0d0e0c090906060103050415020d090b100e0402060702030a0f03090515 75
    0x514184c0c00008440140e101e40f41d04400058600000c13280254880c500070940340d41005180340140c141600300408011480500c00c01085005801c950200203050031900000c4d015078502003415500c0b0400317040404859000e5610715401f10020403503549023002005109e90350b410481e202c20268040450142944c1051400f00d4004402590030060840c1940d1030601300307940380d00580d901e244c40702246950120395250b84a8050003400d003c02c1e81280510710304030304c2d42d000071615035090404080441e0380d0209210b041424204880b0403000303280300301e92581c0c11048160302612145803c40e07414003440c1c03001d8941c2e0405000c3c043c010941c00c2c000c4c1106544450044005000041058075442c100000101a040e511310091018444420b070100f02c0d050541000c48400c44d020341008001034420b002042850032070000103400641c1103441c15555241400068980000760401804e00c0c106c000c002c104054200000c842200d80c01e41c3c003c0c44115504045004a0041800603191800510255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749991393 1250 749990143 749990147
    0x509030c0f0103090506071e090b03150a05120a0c0503031c0c030b090108210c07030809151209060a0506010f080406240320010f120209090a0504020f04050c0901 71
    0x500c4070181890000780400045c0c4815107082000e03201940411996581070301a1aa240d04214441c0d0701c03030404034802407410750402814800180045010b054030b0341541c145641e01111880102401813400d642900100e41e2251261842642213400e1100e5910005141c1008000d81c0d0003411540014189101c0e1266402c0190140c01d0302030301055038561410b071141d6101a4102e010b020340c040200101003181c1c00b02d122140c5001013440740d40e5010321171004461000914441a654013014894440700124046184038008081c8420f040e4800b040c0c410a10358100041407045000d80c040302c1081d00c8909081045400c1900c503d400104403a002c896581e000b840310641141c4100000034070000780d410b84481050551001a21030360040404005100d00c60b5150b050b44d0030b034a065103050aa13280e00103414038820403000390034402ea9104c28007041c4410781c180d8280c8d0f01c000d0701c6040603181c00355003c0024074003154128420343d000d00003006642484e2043c51f210300c5030002180e00c1e1100c441c1c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749992643 1250 749991393 749991409
    0x70e1203280c021311030115110114130317010b03100f0f0b25150e060f0a09030207080f0d031a010c0204110412110a150c150e0d0f0306060509030c 65
    0x40d0130440c036150303200a0000c1c1e20910055008049080070340b44081c400b07240040c1400d555903c0c0308007c0c5c0c10892020750740d80c00000c40382c0d04905410744c0244079901515081d601c2803180f5004005210320080006025004140218840c640701109000415103d54600381c44180701e0081c8040c564a0900c240300c4052400300400b0607130081c0710420820341513855050101c00030004100c8222840e00c4940c2d60141050041c0d4002207101c40140455141c54040306001610041c101100d554a0745031850a141c028800200500b04110542d109460003480f06550740c82c40e00035500c000b9107003000d115006115420801c401c90416500c4100a14003602000098110039003092078407401004001440d0030083c40e00c01e14184a0124002140c40807010445051001e5000b680d40c000d1440084007000d40c419030020800768030a955040403142a4868030080001c04070040c0f00c0d100380d0b000702e09681c1c5c002076280800422607a0038010603031120811105401405001078066101d00138078015032412400b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749993893 1250 749992643 749992669
    0xf08060d0f02030303151e090f04082106090f0919110d200402041214070b0a0c051606020d030b040221070207120b0609070e1203280c02 60
    0x10440600c80c1c2c2d00002d0031070307000780c0340160721000c480b220031a9410008071020081c48110b0400301d000080350003182c000d00008020349502202c0380001810840e41006960245c2c41600d10a40350f81e411100100c0c1c4a8821b0300e940d40320f158040006102c1007504200c651280f04540007a02c0b02c40c0b440301c016030401b280944100c44039486000a01513603207c4400440c9094040e0008030001d50503803017400d00441d156502e0078000c6004000a000c17641d03002c1944030100b41c3c0000000781440c4c8131416642400c61542108c50392010000e4079101c0c041c0d010b0b03000244140190191464103444440303031454100c20b4441d02c170150b0000e03154454903034060362040303c0e0000c0191001d8030f00540030903040c0e81d45448096410341809114103110070310b03a0404c8002c0c06407020003801c5030b486e1a40d444641610754010701d080e1046103041d00103117550384107070070380314400c50080c10440b400315084480c82e417680c05c90207038490f0000340c0c2000000596100d9203950034a50060316102040c0403127409203d10060012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749995143 1250 749993893 749993903
    0xa03080903070b0c0313080c0102070303120e0a0308090d02011e021804020706060e0f010608010b07020102011e1b0e13181e0b010b27040e01180b01060f08060d 70
    0x2e10000e0180100402001000c601001071595008001d1400d02c61070750b550030415459101d10711001c2c603070342c0014200f000d807a058100381486400b076410038006800c0d150114591b6006040c02402010380106c03425000e0707240e5209650030a9113002d812801c0b50b5034800020b40005100324501c0d00215550300400d641344018080203031034151000820142c3e40140700454400755034a5040140001c00d022654110b40c0d90030060055524110000701944418000c4440184000881d80c04580c001d610038501848404044102c419903020042d004040701c107107401c030f50392405c2d6030744420300d100741e0312000b82c0070b00207090710204c050310140c5900800c00c2c00032040a50740020402800700780b110348241c03188a010707005103414100a1400c0130100fa0183e0100081c48004e000c0340300c08003c0c02142d421a040a2590040c03148642c00004002d1326080d2006000355103070002e050a8104061507a00c1e005000c0c05920140342d0340c0d000210740f1440390460300c000082181011443d940380440e100e9044500070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749996393 1250 749995143 749995153
    0x1c11041806051009060b0a05071106071a0a0e191203180605190504030e04270b06040c02150a0e07090c1d010201020903190c03080f1c02090a03080903 66
    0x1a5a00c0341121020f880303610b003443c8083d40c20003058100d80141c0c0050a82d010302141050a80340015200340141d040040441524600800c556200c90083c1c031009030f0802c035110300010406018190b94003040d40d58410349420250881c03516880010324205010001c0701d04020a141501c40c101d0901d21074800404140d00c400401108100c04421b02c10307503c2c011079000425013088a034140301c141814569411090402042201007600a1365401e440e800645003c946044024071640d07005d4805001101092403007460071040c000c1280000f03114441c2a41e0030004107410100581e07031900081c1520240c0368030180003a4002cac0d010340040c60103000080440d0f034000c0c1c03a0360844054900800303000b0001b0711454050f100401301003401d802c1544017030008500e0a071480000c40d4584550510b2a48e80f00701c0d0024060400202800d00d078020350700400e402e502c0c0c403240c400d19601070380301c505030b50b00380078104a21001e545401e100701c81c03000200404a5064501e19074880c006500441d100607410300403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749997643 1250 749996393 749996441
    0xe010c05161b060216080d09030f03020f0304060c050105010504140c0c07090c080402090709150e0d020a06050903060a05130b0402060d05040c0f08010e030904110d0c0c021c1104 78
    0x2c202403501400140d0082c0c0106404180c032450a8401d950110200307a002c0800b6401c059001040b203416139800800451500c60b0908003039180200d5140154801e20001400007642c2c2d602403641240144150000e00041e645d40c0d08105c291110051180102816000802c14080707855004200b0014260292100c1e40d66414868007142d90003454600455460744c2003000314540244021f500c8500341c28404901c42c10140b20300c940fa020b00d0071940910150305500c6c000c44d582d0b824824a61507008240c158641d454040c010010340100103041c0c002e1044c078010400368402e601a0354441c0a011000c1171010600f500c442c081c0d0000034005980159081000710080c005900480f03100d80e0044018075041c034585800d1030f10481d030650040301d669252020304207020b04040200c070a00d031003c5402017240310820014000f0703070bc944035a92001914000f0b1007003c20b41c005400e204d0f030500071512401e1030500200e4942651062000082484155000d5290301e4a0954030814000701507600782014280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749998893 1250 749997643 749997683
    0x71421043c030f022704060c090f080106061403090c0d061d0105011a090a05100e0a08100f1404150615030e0d0f0801030b04050a0618060e010c0516 65
    0x146504280c443c0d0701803011003000c0d03003060f5003529a080c10b156a003c4c0a00901400315294040184c0010001ca88550050250500c61100e01c0090040c20b01510031403035403500c60314000c00080c07058602003012103400364960989007094900c070383d0040000e0944d0007880f104120814100000071145103998240180e0184c1043c205400d1000c25100009425410001c8458403c01141c4600031110020490902d29458480000c01124030542d03040c0680e07842e107102650107060010355150000003174500004c120380001900c2400c1c01050000300b151402114001c2d00303a03070400c4241d4081840c02c0c404900020f03040d070088048180f00610002d030741901e808907840c00c0e24950103004006529003d00710320000040c001408010920305003100b00c440c200c2ca004d04441014480a001c00140b10000b034140302007400010106a4000c0c1c0400a511905440031040354a03094141c030031a1820050740c1846005109480c10b8820640b05c141c10442545143da20306091214204e070989000300030041d40710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750000000 1107 749998893 749999009
    0x821090a15021c0504031a06120708070602060109140609070309081902190506160908010204030308061201050c0a1407142104 56
    0x10110100011286021580225140d90300041e00140441d40420070801450014070381103030760080d01c14100e480340607600004214240301e03c5402c031505601070020b031b44020700a101c05d43d104021000c0900784105a4000c000d40d500082c4140021901800403a02410b45840100800038854403445078418025108500460141003c110014400e4014001c00368109045583d40c02102c4400c0c040039558041040041c011030000300070b4903062114220342075420000801c0c40c0e4940c00320414501d10010384603000d000c1c44a0000400d4407007800500015030003900c6003a01c82ca0b11400740a10003541d0304030b169459260404000100c0c03240425030300c1c410154501407200710003c285002e4148503580000c2c0920b04118032007003091320002b54840c0c09040781d0307004031000c0d4140241d40c1d000340994007d8460b605444102114003148000f4901000c0c40d00c000e5851840001e4000d0400361 = true := by decide +kernel

theorem cover : BRFrame.Cov 749820143 750000000 := by
  have h0 := BRFrame.cov_init 749820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 749820143 ≤ n) (h2 : n < 750000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
