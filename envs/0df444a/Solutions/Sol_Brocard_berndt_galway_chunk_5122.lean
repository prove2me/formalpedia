-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:57.869675+00:00
-- url     : https://prove2.me/submissions/4cd11557-eeca-4f00-a47f-b462fd749827

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921043165 ≤ n < 921223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921044415 1250 921043165 921043181
    0xc011a0310270f1103150c03091c021e07051503060301020f0c06010e0a02030c03011203020f0102030109020a020c06040321090509040f02030d110d0e04090b0a0203040312 75
    0x14014000d0003110318400005003400181c21540d881d080c2807141600e1080d840c0441c00740e02c6414101001050f904104440c503980100c028400c0d004070410944848440760800d42010072000401d0713481e1921844c00340b820000c81c05040d5521091545605000d0b004a80d900341c01964203c0c00b51915121200f071a1200441d0044903030000c0000b090600c8050160044c690041c400303000141f030300052205c162495001041041c240b9888400184030580781302c1e1a0701d03000241c8040541c21030400c0821156140414052420021800ae08a1003898820040034aa064403600215541e5841d1446900a54010103030301000d485191582e001c207051501c2101c1c03c403070f0042c0120325032004280c503007a540d41d0045900010008a0300303010820382d58811946000d6072180306085c03940c26152060508200e100c807030010500201c2510420441c0000c81d41850381c4081e8603002c4001204480014010800130300302401220b1034a08102c0c80640355402180030b030703000b41c0325110f004541840c0c61060307800c94 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921045665 1250 921044415 921044419
    0xd020a090903030b150c0d02010603080f180d03030506011b0b0c03101809170903060604050a1503050c0a0e0702030d0f09051f0f06031106090609030706050c011a 71
    0x12090412442080d0340c01561035610a00d804160b5094010000e1660300030810840c0b00030000041c40c03258801c0c100301d81401420761740000c0c0013179451500c4094003806072480003051000c00181400981d1000c40e1155040c0c00010804110701410b402d004008040440c0d61130301040301603540ba60b034a0503001080000c2913014130101e40b6940d501e28500d900390001303450707202c040000c881c01003542100402c1103030b141031850030002000410350030000d1401600c4403c689041004100d024840d0f200414165401078083d5008205920303800d520900030540f5101030030b0540400d503404020004041100c4003102c8040318072903842e9440c0d40c1107001005040c3d81e020050f034020808512040c50581100e0b1440d202005d001a5030005d070b4484900b012201c41008a0103800c1c014250b203820454440c00708140400303a010000a4199134841c286c62002e402c0303e602c140004690000d069032590210f0b041000003400f52491156100720103020398000e10b107050515420300703824026910044103005519400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921046915 1250 921045665 921045679
    0x6042606090c150d2a0201050f071709030d1a18070504091e0c0324060e01030f02041d090c10080f0613020a0c020117010503060105090c04320d02 64
    0x344140c1c240b4254071090110341c0e001d8860700708604034034013080c0b21103985c5071000441c031112207129002400c40311300404408180e8103000c240600d1560190303003034060030301c0140162001d89403039a101e883d6018212030541102d0030105108218481c4ca41201d6004000b501c0745041506280b428a000050032a04003001a02c02d2104009900c0c1d42d800002400b00d001280351100901604050281c03185083d252011075241d0001490b0310b03042400002401c0046010100c0783c0703091003401880c50600c02c0300c00d410181c803410403144818540d030441d40280030b00c101a503034141c0c5000b1040030410044880d4002405010400d00311400c14600050000e030b4965a03881090740d80c840500304e03440d8017400d83d07504540e1010703a0142e6404148003c00c2010350740c3e110024920301c28400100b03445040144a41110f074060010002501e00158080c15120b08035552074440ea6400030280403809954800000a00c0c1c0c0b4044411000c010121f00c22024a0701100c51400c190f8030090101018003000000d40001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921048165 1250 921046915 921046939
    0xf04090609063203030d050126100c09090903020a03170907030305030c0d050103050714150a0e180703090c0b030f010b0d09020d080d150609060e06042606090c 70
    0x2000f4001441080f5107000001c0d40d140790022914642000c80c039006095928401031020358110500041800c1007402c3c1d003000200e01c0024a43c8620703401d400700c00041d844002061030745000340c0a4601500000404000d080036130f04009680700c43d0803200b42c000c01c201ca005507603030b00021036101d882000407000411841e440c1d0340e0103c5055100401d40041c1c0c890500009a0700c0c3c1403402540e00847c080d000400b4000d040c40d640711902c0c518844014031450840c003aaa89090056081d15003c091038140014900498070200d03552080000c0102900e5034004100607055806a008000c00d50107001d40a20740358071610280710074402075524103840a164001046103041200081c1305091600c0c5000c1140c00d220b1b400b192203580f404c031045503210300200309035551206a104010b041218034280c10821b03890940c000d00f0032072203030090b00c003009100b070418042600d80300c084400a140c49a62014140c2c00140c022140394100901c1e1780d03080c004c1030049050503c002594404105004000b692224 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921049415 1250 921048165 921048209
    0x5010f05040312030b0405040b010e01150c11031608030c100204060203160215040603020315090105010912080403150207030215060a0e04060b040e0307050115060e01031505060f0409060906 83
    0x50100d61240c1016110b55203031700c03183c4684c040c86000c1c82c8074827040011035040101c0e8440405051b001440c0d4070724809001d61510383d1102000e5884e64001481100710303002080030a0500e44210502c8880002c80c035400078018000000074600c2807244e07402d0b216100a0b004440090b4442d0340301d8a030060b80140a140c0011003803444480590b0b00c0103281647c0031841403030504881c0c0050f0b0009011943c0441040740a270848080205070b18000c0318051107a6061078000ba00090340d43c010209220000d00d00441040034000c11078000d1500030741b04907c4100c041094101039800041f007103006000b40741940a4920742d10520301d0180c00001d002c2c0d00414100350942581580040060b83d42ca0345403100200307181c41d10301c90310001f102140c015641d6076010381062400e440151510704044d0002c0d90040010a51109094000242c24600424102c00210003d40840d04a80159038441000100c80b8407180708200140100c810610091042c00c0c0e984030300c41c04855052203008550f84840c03013030ba000c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921050665 1250 921049415 921049433
    0x31205190203071703090705100c02090f01030b0c03040f0b1519033306030506010509011e09020703110d02030901030e1b0411040b0f09041a130c11240105010f050403 73
    0x12040c0d10480b4007c1da07840c2e0019006015903411000400d46200b81c41096041ca0341c2c0c0313a68071039801d254042c040d514654906005a000601e0000d140748007001107010004815400303200d058019007090502d0801510103000c0e80c045201e01031259045449051185000c1e051031002c0326007240c1c0c001000a4448030b02d030b0304600000004207200c44082c803200c113200c0030b500c030f100091030040006068a40c10802485605407040e00813610300d020b40c82c924400c14150307801c00d00a880c40c583c400360311680e00c0d10f02a90b4921402d503503900d590080c09500c2d100d940c0e0000150013898400d0b0380c28407505901c0701c601619130701d00b1002c800d4007440094003a256424550401d045513650580032514040c0c1d02c0710520416040142089950500042c54441c5460140148010540a0003000a180307410800040c0c1c01181c20b07804003200394807240c5a1003c140600d8621906200b100141c606402c42d2a0010100d6410a140d20800006582c0007040951064140c03c101184030303100c41c3e24082c11a2110307030076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921051915 1250 921050665 921050671
    0x50f060f041107290702190201050f0d05090d0e0f0108041101020a080d0b0109050a0503030a0e1c0f0501061a120a060b07110307050108060d0605040804031205190203071703 76
    0x2408000c0025100244c1d1036004504080340b644500200e0380c0c85903c0d04611414060583c000f1903100c01c210500e41c40d000d5040c40d8035198242085071755205080000701c0700c0c2c098009078206403481c01040000c81000450042002d2243e80d580944803603110302080404101c051000f40001c0c401400100000d50140200d01000c00500403141e8003039131a03458081070345c004c003d400d82040c9c49031440714041d6000310f10b0b50040c1c402101c0303c400043c1482d000c03a0b03036400b80301d02d1300b010451011000e5109031241c4011544a0b1a11180290300b140c003400c0900314882e00d400f080f00c10f0340c82c1c840c0006080c0003513003420850401c070b20b048624100990f5081181020003800074030355a56120707800120004600c00030b00d1694410841000c144295404050402c502a4400350501a4200400c44242d850080b404003003580200c0c000b82585950078278000038091900011b14040c2c10740c00d0000d0f265004405040d0035248180000501002c003070b804c070703101e000d4074000421401c0c000c40d005400400150155074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921053165 1250 921051915 921051941
    0x5150a030f020d050403110d020a080306091503010c09050a0902040e040305030406061527050603060d14010c050903160602060604020304023111040b0906030903071a0a050f060f04 79
    0xf0900c0200c081a80c100d507801d0350110080341d64982c041b11090014484201c8036180e80c0003130031100c001038481515a101c020801481610301e240040c4038a01c02c0c1195814001020703000700030340c5a00d004090080c0907a4003c503485000a01d030000348081241c000c40c0c0079a500d05010001c1398540b83e500307a80c6500068000c40780183c84242c0415040d00402100c1c8500e0710a540300120621402d81c1400c07200e10202400c54407d807443c4052109844000469400c00801d0300d00d00b201400a0501107000450541030301055400d1030703120a0040c1e03000010300207041c0100c050b511030004091024903000240e10600c0c0c0941c01847c00128680340c5079010b10b5101d8006000a20160032035a855072000300c01c100c0d100c5081d011500d44854a110074403d210b4415070710040b00745013a00b02005a1254042c0801d0300340309007000000150400018400d880507558001e0280082d91001ca64088034a06c08a40350030040e494100011f03481d0b80001a118001c207405001184d00c00035100501c0003401d24001710322 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921054415 1250 921053165 921053167
    0x100b130b13090f140610060f02010f0f06051c0c0b030a0905030c01050916030201090b0714030f04030203010c03140f061f05030f0c03010303090e09010f060305030702010905150a030f02 81
    0x11800380ca8a001d841074851040343e000b49030f0522894503007100100394902400d0340e8004401c0101c6480807000e1700741601d249082c1001a8001c2940403800340c4600d00d0810705050a100c40c1e1002c1212076003091003562000c032406000942c2c5400d5001c410b480502c4090030f01d020041c410801100014000d41e0026503d190204620350503488071031459101c2003481c0700b160b5581c0c041004441051041d5103102c1540301d8072802e0301d0314540000f0041c06590040b4250303040005004410003801c00d0081e5800c1c480b9000b80e85e110340b20fa01000e200b80e0424401603000f0350800d074110150910030f00c00d8034074811000702c070000961034400b002c0700b0036000213100c40e411042e50380d0090440c0f20790003c2503c0482680d0790741c1d07a0368601114240b80180001e00b501420000034401840042d8004038820261f403c902e0b0018820350f6110000c90251112218043c2c3c01d83c075049020081c000044020718045000ba00e03804c250130f80c1ca400307014010300480b00b81c4242c0039040c071100c800288179811141c0c803007030110742c05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921055665 1250 921054415 921054439
    0x50f01060c060212010b1206220203150312130f0b0f090102120d1a041112041a07090e0708150d05071e081005131106070f0b0603100b130b 61
    0x4d210342403e07007061703181c42c00c0440c401b181c005001100d240d00100030384000c0c00716001440d260165509504c44041c1c0c0c65008000107802c403100c0c1c1d00340d801150005046803444101c420009981e136200001300004900c0c0d25001080004480405004540410201b54a006c114080c00d032981e800c9107402038110b00400b00da07c51034010600150400d50068480051480c0d00c064141221040000c0350f40d000c2c60400d443c480700d141c0340c001030f1342602c40341420000781ca503903902d1300c4141440c3c2c02060700079041c1c81c20103101c0016440300106094070350200d06a151911100019108180708071054aa500d10a00741031045003000220100e00070311800840b9441501c83d02d0700c00c0990321224014450210010082012540c208520821040390706420031030740c140004042c84c001d4803108d0181001c40c0200703460020742c445034229541250021494010200d4230300d0b20b04405401601c80901c0303841210412440e00c103062103014203140c0020030701d408140f0810a03000c00b80c80900200c5078440a007501d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921056915 1250 921055665 921055687
    0x12240606050415020c2b08030103030f080703140c0c070e09030d15060804080f0d0f0518071d13051506090703050c18120703050f0c04050f01060c0602 66
    0x2400054120341d240c642e1540d081c482c0e5804640200c95500b0308550200e00140781c0e0340c03101c0300d410440782070030090303900241d5004014421007190040010072244001000009040c0c0c08a007010301004150b44030300150312804401c4003074070007000b5a100c16071503650114948524038030082c0070314003038481612411661400d040c02e80000480e00c0d00c0300e507000091000842c500c5403180e088440301d0794070640368090628100400c540402400203020b100d00191030680f01ca4118280c8250b1141c960f010301005000d610a40050b20b41076900d5000c04080707170702c2943c651001103225803c0da103024524541c8004e400c0681c000d102c502602ea150900305c843c03150800f1610074884003000407030382c14441502c2e00703006c014050031110051a503000c00d4a048188410010040121042100c05820b500e44000801d00095640740382d516125101d0310910b00000f08114020a8103081c0703510310f13400e5511034102081031006541d02105d0f109010519140144801e500400000081078051407006061104000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921058165 1250 921056915 921056921
    0x3220203011503030e0a060314010303030c03020f0a111b010210020306151b0c0105090f04020a171302041107260403020a091b0c0b0c0f0729090105011224 68
    0x40c4c0000d401181c118440e401e0503e45980146540c0c602000410440e10000341d0821040c00020101910b8201c11031010744240c0655080303010803448266030b00300100000d81070210b1980c4050766400b0700b07211001d241409030010700b400b40c01070300030b80280c61a516807440258030080006900104840489202c48002d9000d00071848064030f0320103191490000051910503141b512904012080026920903121800640040364081c0e50140e01c6030800e035401d440a9443d1a2a54606180001040f100740301d0000280801030007943d081054114100f0898410702c250b11002d45060030072107a005507c104144051020207000d100f903810b1030b840b68005a07141003e42c2c8441460341d11005250301041d00e5122900c0c03000b149080c40160382826541d44410400f0003050459040380209180c580b4200e040c0c1210070a940c0304c0c1c24510382e00c4000d00c00450a908940145021842180000ba0031403814401c003416514184600003244030595249a02209644d0305a1000c0d50036001010448a50340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921059415 1250 921058165 921058169
    0x424140106020a152007030e03010510050a050a23010908010e07051203070221011e320a0906090506040c0614120f0c070f1a010b032202030115 63
    0x1d400f4000b921810300300844160a1084100c24a03407924a46010107500e03800031010581c203080d0700780c0c0c0360501e0313081c1035132182c0d007034a4a150194240420000c00f03240c4131300103805880040f669032507029100c1003402031200d405e00030078034503403046501000380c426801e000800c01030051600c0072140d902d41c103200f42910030040c450300d42ca5001502c28015460680d0401c01e203c40410011405c0c45c41d1303a0000b41804051444002541603d10120302243c03e080d08032483e841c00c00c0c0c3c15034030094054030902004001c15201403000c407a080b88548c041c440ca5008440300300800d949041802d0703c445103464014000d1100c00c440807a51340e02e0b010f000074800d0040c18440e600070701518076103916100000d05190700d0300007081c898060801401804800543c507a03500042483c1d40711100e942c0d000c035440241d20070044040c00c071203801500c0c4401c1121443d000218125080f14000311079a850b81c6240141c003050751640d0f200c0624008150b2840807800546680c640010000b003039180307403801000b242d41d00036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921060665 1250 921059415 921059417
    0x70b07020405070c0803040b06150a0810050d0515060d1a040b07110714130501230604360f0e1213051c0c0b0a0f080424140106 56
    0x8260081940703094030900d54018044c0c00d00f114514001e0703a40e80b03000e00c0020030041100c540c07180070035955107a0144080d030940e049004a5600d00640030060902c000032112501c007800e816802280c00e0518007a110000c44e40013004000d01e8841d60401c807460040200000c0e000307c5440102030100c1d0a04c40001c01c011024580c0741118107050400742d850001c0102400117120f0100744503100f8410010341201107980d429500b6441040f110001000c1e50b100110b80c004041c240310000c225a1010707044c8030a40041c580300352603441440c1003805118015445804846080280f86400103024070001a4810018040d50184400042c21140c215100f115025400325aa56004604040304001c1040700007031168541e81001c0760342522595102c900c3c01000c2c0184014043c0035951080c0c904443c4901c1d9100e100d581106480300c010181d04d400c000a0100000c01220b440089140070349003450155411141d1046d03144c8000041d120310800c4071441152440ea2400340500800d01461168003070051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921061915 1250 921060665 921060667
    0xa03050a18060909090201091e0e18030d0c02010e0d03150905010b0403060b181f15140306190b07020a210b06010c050d0c03081e0406091103070b 64
    0x20450091080d0360700d803264010840380e028244065504a0315210890300341d120003043c05e10803071004a80e00b000e00d03032040908c2c40103a905650721841d10200d0000780d039440c40041a1a5903202000c00b000c180007041d11181d41c1041201e400070603140d4120754451041c03800080b805040c4048110b140085543d0500d0001c3e6032003a0b42440d422060450100034103071008140103950410072014114030441c480100226581c08081c41c05454018000540c0f0560100c1d4818900d800e410000c2c110b92140c1d100c004d80110f46401182d10390002088121907616039540c07961180c00e681e004d920b0341e480507004030303444624103040141c40004910740c64050000e4240413501c2e0b1103240f0600c00714911580003010690304211b03540c1c0b460b04503603558414068100c1c10884454545200698007074031180006081030090014584000b5003118022840f14840d56405060750344804d400090951403495600c15200b41d20045008100d4a030070003003040d0300071180c42c4940174101000900d061031540c015800030390 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921063165 1250 921061915 921061927
    0x212162c1215040c0b0a1710120c03120c0510091103030c0c03100c0807120b060d0504021009080a030e030f0106080d0905040b0108130c0b0f1215060304150e0a0305 72
    0x1001024080c000d00003c0d03580c5086c0245080043c040c60050396071981035104250014050024000000d0024043c1c1d03003162244100d242880c2c01c80032614007045d03508101100701d0300300c01886007484c00c02082d000405040140003030078a90014200b942416a00000000300d501403964080c00104500308100c0e0090000c40b40c210241414036010a100840c81407502c894010044e800038846544038415150545051010003603800c006d0400c1c0680300d811a0000c200e181a41d0200c1c2e0002d40228000c8410140945203888100c0e691401c60188620640002c1c4070b107000a0f0090b2042c0740c0d2024020162a113820703240181c00c0c219105640b2030b5070a0781c44002038584054001041c032010b00720a55060020154070130000e400d05c6c070040c00b0811074181204204051100146994010f0324040e031009540300c04084d0a480b494101c02182e110141640e00490744000d4404564001602c1c054804c60a550b01d030f803200041221031002c0384540135101d108440940c001400040042c500c242c4405031112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921064415 1250 921063165 921063173
    0x1c061d0115080f070e070807121811041b0c0609021801050a1502070b090102010f0e011a041803030c050c190b1602060a020f07060212162c121504 64
    0x81491118a1513412444d420b01940b92400c01e4180e002400c0e003496001515024411202d410350703a030824080e81c1c58a081029001008005907512038054109404981d07a800100700c07c2755074042c9050800020aa80e149629028001302d00c031843c0207089c00610401e0b07c0e00403d9941401072145101c105441c8014000e510702540e14401902c0340c80c0140200c2030042074046c0d40c1b02d00314000c0b10882403011400070f17000e80c07003500b00f11078002e5800014044100a149514080e00c4082c080d04030540d1140720b480d80300c3c1801d101e042c8003000036406498134880710b0b850989c020400b46407000c3c01c2080c10000c142004004004a051000c0500c85480d854a03217802c1405031030002801000b980c3e0b0f0709114800c4076560000710150008112200141d440c071092407016414440c41030300800c500d0001c07549040071462104070901c00c1c100c0c0c052a24818864400850703800e40f00100448034034441482c949100145001c2c180c000002c0a4900d0305101d035400086498401004d4442d05001d106e2401c02c0104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921065665 1250 921064415 921064423
    0x9030801080f060a1128120209090a05070504050d03020c0102100b101215090b120c060406140912030a0306050306090d03020705010b15181c061d011508 67
    0x100005030181400c904601d604689448018011090507502c5d2003c250082c0694000c071240c6e501c0d0700d010000c019401803100c5441d01c0032401c03e80013182c4c003088040485d540e603000f19148100010210805559511019002050040c2c081001c003e014000828283c071000303030003404c043c026001800c42e601880e0009142c0180301d003101542c181861042c1c40d6a440d02180c0d00368155180c1004400844d0f240412002441c00400c00c1c4002c03000281c0000c0e403940c0e140c0c040f00501030306803a0700c0b464030b01099a0079500c01e0031350314098111000308420481984510080e50100814003012442c120542d80054601969809803034220b8000198041e02a82c06202d044014032003603000d0001d03441c0002007251503041806800e0b040c10380006400c0104002980022803000340188480702c0300c44102b40d5a04035070480c2a1030002022004041d00442c540b082d51200625851210070500307001d11b0b0f50301c0d0050801940002c3c2c50b078194008140340008207004040e00d94800d04030b4441c003249000742e01850 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921066915 1250 921065665 921065669
    0x13032001020c06160320070f050102041403120403050c09071206030803060f10020d0507080c1603020109090b150903150a0f18080d0b0a0e070503040c061e080c1c09030801 75
    0x14585803c06e48032204408007940d00d122004c4950180c1c6a000d00c4c02e00c1000300e601c03900300901d1948005008155000d0006052084840641c112084680d91180da20418030450101909960115061891903d0225180786c0d00000c90702d082003103804001519800e51f44a0b4000b15207848005c030802503070341003e03407000115050484400054962051000e0f40b20403d003464803041010001e141e03c07d011031882102c81586c2080200d031080a61490040300354411408203e0016620807000182e00019024801000c07100a001c000300c6801001d002d07520303038403030025030341c041c003e110003e00c0100c030640b903881c81480480c40214010003040c80803021235820000c0301130f016280c000c0a00c003051a02050f04c189c8034000300d00141d904481c0e00002e00302e40302d95101c08211070200041110040d0701c60040c0d4080d0b031107006c0340000039840e4101034440700210996104c0312907900ca025a41c45100325455500700410040f682c0ca0440d140003070303580105041d15010394113602c400180307080580c032801040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921068165 1250 921066915 921066917
    0x3070e040212010b0a05040807090911011107060509210601090c0908030f0f090904080c010c1b0b07050c03040b0c0c1518010915120b0913032001020c0616 68
    0x100d05030314038048012140307044c000c61641040100b5100303022802001110054042d0000300c41060f913403215400040d080000b006c5506071107a254440c440c3d401446203401d41000c10001c0c0c03880720b041c0907085a4640042c0981a4419081c00d013625982044280c1b075100b4090b0310340940007560400407100140d03005500c21804110402c00c0030030001d80080141c5894058000540742da4070403d4085071414003035131100700d5202c0e0061081c40104034800000344060000c200080c454480c2003601a9400000703d07001c054014110605000020701003110039070b00c040207040681c1420308032204180b5581050300124100500001c0e59401200304000032030362407808440154045e109007102001500681c02c2e80034440d0003941d0740108603030180140f10b0140400b80c007240010001510003c0000c1e081154084010307203032100d000c4c05400c0622207988103041e0a00303100e488640541d002c589501d000403056403120b002c1701c1c000c80c00d179500b80000c01c050b248600040102e8100090000d4104420740c907000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921069415 1250 921068165 921068167
    0xc030c090f0f0909140313060e06162a060507020108310f0b070804210e0d030903150912020601051509190f1d060f1005120702010203070e0402 63
    0x46000d84580c0e04100b40d032005140490700042c45e28056140080080c01424140404224400d0840c0040c07d25030848281da030322200310181c6031081c030102c0d125000020400c5007118200c400480c8152030a822032203070103071040c0491640d6858040d207513400780d003118001840c005200c84c290342e400b08005d03811071200700700d943c044030b16404107032194211614401c000e070228a03a581d0502100186044403203401501c04406480c1218000706000400c4504540c904100442807403408091454040800280c0c1c0b1007440403a144001c100c2030a0414608134204200040040300044650381c0c41501000031060110f0010031070715200b00e08411714220302c1c08542c030501c01001550359141020103405246041d040d541e4505c0000714140d200c1406000c01400a41d401c00a000d420070200c450448042d18074a842c0408030401c03042e1103640030768980350711002d100d001001740d140804803520b13460740702c1c141940340403500306100ca50500221110750240c1d502000f040380c031a0308480328ac2d02c0103108a03011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921070665 1250 921069415 921069419
    0x1080d05030f0103020d03050f0a0305010f080a02100e1903060b0f09100302041a030f0c040f0c1403070c0506150102061b0d1d0a060b0411090a060e01020309040c030c090f 75
    0x2c480035207014407010b841401c80b449900c040c10f006408a62142d000700c8841c50b9580355030b14010380a4082881403410011801e600080c1d14203000c54100c8589a005001c1c0f00e41024616044a414240c8207035654090b05071440c02c03012400c10001400254400c1d500860f80c2410a8101301c500c4200007000341c0102410b004000b401502842e203101566812100003c0c6c1e42041194550072194804100e501032042c807602c0000307444000340c0c180c01100304440900000b2a4138007504250b4803107007090303400f081103080e21101d05000003002c1c42d40a00c0c0d500c0c2900c85620180c80b03042c98804181c4101103181242c48051103156418480e480d4000d80d81c2480a594040e0f02105030904d00c40c04660401003659000c8241c07002d0384118080c04a2845001120040009810030b00020110a40c219104074070704001f40036010300310b105075066201d00a1460150a00c1c0080541e40304403441102c6046002c01c00400c607081c2da4500c5500b035a488184d50006140645030301c05007801c501500290042d094040f02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921071915 1250 921070665 921070681
    0x10b0a03050a2d0312020910020f010f200d02131205010c0503130807020315070914040c02070b1309020f1213020306011e0803041d13030e0904081605010501080d0503 73
    0x1c2040c0761035162170302940300c000c02030708100203010f03021025502404d02601c441c0200ea0000d842c0400c024040c000300040d0b0480ba95141c21201c12004695015030305541201074110418041e003242000c4d0140135180181c40e1050050000c1c06030006104504081701e40801e00c0003d00c500348410100f42061441c500703140318003480c00c00c030381d500041c411200050484115101408204880202c88200d52191300300428041d26a44c03040c007406902d14076038081c0490030702d01b81c040e070240108aa00980011170811200030100d038480d040c8070424484400c000200c0d10041d00c020058203002040654a40b42c1d01039514845103000391a609540fa030076201c000250307a022481c981180d001881e644e0000300b07075180b041080b030040e51164089020201e00000c207412029081107402070034060b00f60711a601c003200380c00400b50000d030103000183c0f01c00f11a0400e0410011241d0024050b010b06070070034420304203a0156081404048070140d440c2c03001000112400c00c44402031540c10304240e0300b18540014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921073165 1250 921071915 921071993
    0x90801020f041205030c0129040b0619050c100c0801090b090a020d0605030f07031a0c1c09080d06150e03030f0d09020d0f0c060c11090603010b0a03050a 67
    0x1242d03000001000c60f0340800c00704000f01c03440006110001d0144000c060340b10650307801d03c003c0d0881008603404c0c0e00080c03458244695502d03040000c242c40e040c01816403411010f48810700d001c00500508010304003030ba110820041c071761800c0046001c2043c01401300020420501079118000303c50620300751030003075611004104e5105d07001400040e140c40a80030804040d0000e03a0000c2d070140076035221400c02500100b491010759015444840445040c2118007a103a94108e0700907a0b00c07001803120ba00f11900ca4007803080c10b0a8050404950402c854540c820250b02c0040d40c0100160f9900b001c10040b40f000c81041180c9045040c00015005000302094880c800c0c1e81c050004140001491507550446034056100941c000c0c00c64541c10f105490b04005180c1080300646000949103800100c0b5445085034a20840c0e020380c2c0c17134842c284c1c003000f840390100001d400c05a043d5240d40d01800980c442c103110b000218040e1005050a41e03070b80c1808041e0030743c4194040031440038801e44503d00e0354421 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921074415 1250 921073165 921073169
    0x1f0e092103180c0a060c02090c030402010f110c060a02011b031503020d4407030507060b012003040609080705010e061308010513050f07050916230a090801020f04 71
    0x601e82c08500740e810005582008960101a81e0041303c110b40415841e40c40807072020102d1007030f0381134401519a030100c3e1200d0700080300c0080c0020440c04080030b003988246e4603a141c4040e8681150401c10140b400510280c012100040050790b40d12648013039100d0242810701c5140c0141404c21141c08105440d01901c01e8600021f07001d2140207454000700402d07034001d003034041108221610122800604803020020a4020140440312840002038006914080b05c10702c0380d250304c49600e030036015501d40024001040307405041c01901207540030303604001c0340785006546050380516640e50030024040d00354a101c0d08900c12395401010f003401203036009040e014102d8411641c8903200c0e182282c5401880b025500100c03069424102844160300d040c03002d00031841d200f6402e41c1c14500481c0f14240e0707904c08070f1007241d40c48081000031954040041e0742c0301c600f400280c47e0201e4007480d00400030032100210414502800b00006403c020190f01c01d0404005d014010025490450480d1400f80306000758 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921075665 1250 921074415 921074431
    0x5100e07090203040f12170406050613050f090f150a05091e0102040302130905070501050c102a0c080315041b03200a171f0e092103 58
    0x40414512a2104000400c02000501000e42d524035082ca0922a11901c03103400b1503591030300201c140c0c0e14130701407004a1814072812071107840983c2c0c0c03616000301800b000380046030000440a0030205020442c080c05208035403c064001003400d040d02030600d000b8944c00003000382c4d00a24480d00c040b5084800c440e80200d5074041c00f180c16118031400750b041c040c9412004045c03000152820421600c190040c4c42124000c48480b0240350004116100341e8012410040075500f200074144095030040c0007410015495a0480ba06000c000074490101d40ca500d62580043c2f4926410000713689070006840c0d6040e403a460040e40022160f80c44103152301018000c14000c1c0d42c1c4149260083d141c66000c100c0700d9100395500342c1e0240207510080c00400c0311102090304400c0300c15100c6919003031401141c003101c0b49555103a080140f60310400401c00405411849294070030b4a28440e00b004032140321010702215a0603440300c0c00e000c0307200341c0b4100c414482c1172a0074415813190355500b04e009050700d0380507102c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921076915 1250 921075665 921075671
    0x20030607020c09041401140a0f0c0302040303210b0a08060f0601050c1504020f040c121515081308032401020610060e01090807080f100b060403031101020c2a0901030510 74
    0x785e500d0b020702424600c0c02061000d44030004202c020102e50300b003002921950b030803c10990003800b0b0110264402d50002901140465000c20704000d0000ea103030300d04100308240040c45032002070011b0b2202c1c1250f80f04142590000c02400700070071082012a40100c07003420000e00c0c02008241a03034039001c50005015201e801c0000103405d54445214040c1340500007801002001c18410b002352901ca0856690801e142c9000040d9110b0100000309000b6184003040c5070f2030000318444101c5214034000c0900480081d118440c10004c5d107254090b500034a040c4920008058202481040010800010504543c0904107103c1c1c461004502c0c4002c0c2c428030b10f012514010303c4001038034950280d0b40080250320445100040e42a000b103003100303269249905070380380b9941100d0309505440701c000049501a130100020400240107000c00001c080d880000035080100c081e661500f000785d01000d10302007803440041c0b00e11403004a007d01d22203840484041e0555411501d0302592940444114454695 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921078165 1250 921076915 921076943
    0x80703020d1212050c0c061e160302090303040801020405030d09030f0803060d0507080d0f0216050603040311070806060a08012a03020405040e0f07080f060c070c0320030607020c0904 80
    0x40f0a8520300390305260782c14103000c2d50905044081c0710b03034849040c0113018050400410350005421014004050100c4091802da8541d141c3d001c0248098885034810326a08101c44401614140060402801c6800c0016103179032919041c10709010084000004101002205200180104030301030034054120030002c0e01c90392080c01246100661180c090a44d1203401800241404000350021044003540d81d099510700d08141300740e03034030320440c1c035800c51042c01e00e44c09020344d00f0100091580070b1300030306d80a141c00c081c076050a1704114150b0461590f68012004110190401d00c014030020203086c0b0007084003510f109500d800c8503d800d51400109580c840e003400c3c480344245c05881c09040001c04c02c00c00705401d081c060380e95110282034076446000b0a280000c11410114021015065440290510f95074040c40450654014842180e03002c0701c101d00031000c94040c02c00004641040400e010481429100b0103207004002480042158001c0f00b0070301d5961a10036103182c110343d2041344070030800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921079415 1250 921078165 921078167
    0x501060306140408340f0309150c0b15060c0d0f051206131d03030105041526120409051e010810090c0306110a17040b1311190807080703020d12 63
    0xc1d5140421101150b03176600c0b803010b200e1a101d00001300ea20a413034030005a40e07940440c0043c440001c4000c000304a01f102c260010442150f096640680500810071424070b0800c001600c5820104107100140d10090410184907000202051142850b0a00c24200904802018100c850080449015441e403c802403a001c44a030000d180c131410300a05815240308003d00d1a0f5242c000340f250a20070303800c2141c1100c2c244801074202096030f00442600000c0303007001909003056014100404c05078410340104152650900015001070885c02001040314200035140342000c402007920900d20744050001003014003c00517000424400328000890307404682d041412444400c1c3c1e1001d0318081c1042618128281c81d04d00514664405842c0c50998a0030b0700710600c85450201c03002030a0f254454042440d4421140712080301c00d01c1121960034004205001c1441034880704581c9507070810f910340600404805101c1c0c1c4015099042c01040d07500d18540002d00340028113000a4000501d446c40f0603049 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921080665 1250 921079415 921079477
    0x603190b031e0115081207030203090306150f040e06130501060b0a080106080109020309060130030e3c0a0f030317061f0e0d02030a0501060306140408 66
    0x145002015500c140c541c1e10301d81c65600d5012020300b4607a51034181c01c00400d194942400042e905100014010020340195052040d404032074241d05620051245034400c3d40c080009910540d9400596003e01c0c000f02c092129155405607450311660514190f001d800c1c2000481c0c551200709440c2074495400350382044c90040072a03030010502c42000107166829076030803c40840c12034402c0e56031207030030b603903070b0380f90341b8224041510041000c0e00600b004005062000d50391000c2031080350740016150900b40c0494409100d105001c03070104044894000c4145040e0711201c2a0f141e07600869032031030781d1a0010300c81c0800d40e803d0304c0411118000441c050fa440d41c00001c1c01609103040e02c0c007241038883c01c0103040e4040c5040403801d494400070004550707040c1005011540e02d1101c4441d0b031440e01103002580d11382e0801c04101d4000c1c0700c0b8802007003d0394041191030100381c016000050007a0441c104a410340d82002e0341a0400c0d5112414040081c482d04202d944040b2010901c1c01031401c0d20100d1203403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921081915 1250 921080665 921080681
    0x20606091506030a06170703030903081e03042a0e130303090b0f040203011b0c03440a0c050f2b0b0307050301180b040f0f050d14040302060319 63
    0x61030110412400590710383c008400d90369948441d05541c801c0f542200d0f9148001c5c0001400507403540ac01b0400034035418007030014088805955629a482030284003526007080b02c094407103003400350446007001a00f94120311120b8100011150481c107104001951203c0a0a011904580082c01c5010f0502c2030380700742c03032440d40552300e28130600b032000ca0800101c1c804e0314141d20039460921000495070306008801b000030407a4440105540158405071001008424041850843c184100c50011403807080b141d5440d80d211618450940c03000c54098052100610420f4141d10300035084001a81000c10303101400c3c8404040b03540c17114078000130b840300044114449046101c05020743c0c06403140f5003090b8110f04003901114030090b6503004050aa4200c4121862030b0585402c02c440480c8030781c101507500074016070038007031240b9980d56400c940d110117074819243c9402c002042e40b140356106010301d983c41c00d1407100c5400d00e400d40d00000c00c50b02c0080c01c0644194030b40700061920000903004505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921083165 1250 921081915 921081919
    0x5040e01090c1418090a02030321072a170313063b010213060906020d08010510050a020a0b0a050f0f0c0a2d020313080a080a0f05120103080d0b0f010206060915 70
    0x7486509820f208100112b1140e240040f44000d00b00143c84a84107022070b0705c003000d01c030b0f00e0002200303507075100003d21f840702d1002603841c20210701151094010310002180603200120001e10302c00c9450400724115140c01404c07146840103003c0c0c248120044105050603c400c0d039080d419100c1c5004400c1e4024400d801d00e03545410709402001420542240128084034485d8003a5040b00c01c0101044030b000000740100c0364020f84803804001d009100b00c0180444503418011202000155124152840380c11204121442d4584003041000c00f5190101c07034015125007400030351800c01030b6800c03916008403400300c0c080012003c4a03400c40500280c0600785003110802420072140c0c40c20b8000c2d00d1758030010b56000c00b5414100000303601c01001a560460642228100342081600e10301201c088400d81c44070000c2240a200c0d500d5001c025264484c021442449402daa8401891090040d030742590030340d51003020034560f004043e90b00801d03482c0d0b104a0032107148030301c0d503607006c143c0e000071080c0c044035a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921084415 1250 921083165 921083167
    0x90f1806100501031a030d050a0507063306020604031b06020d052203050d0c02031201060c0b06041103180106081f060f030503040e0a020405040e01090c1418090a020303 74
    0x111890004074400002d07103034282e030140205143c07280d031000d00c0128404010313007660045041c10460780c42040681034200c4145070003440c24040380ca0704000d903a02d1149205040c0340100600c20402d29054440801c80d030700c01c4c540100a4a002c0000e9140c5c8401403010702400403501d0300112025800c910001c0c801d90101d000c540301c06c84c1001034001420200d0b26141032414141c001d0041c000d41c0c81c0c0c60242964035668552528a031250200050311a0301c0c21082940310603c00c2e000100007441f03640c0d02a01e4540d0303890f4000010381c00c1038400f142025144602442c503010031044407400742000c0340c1d40241d110143c0400510580c2e41c060040407145e02c104c940c3d0080043c0d080d12500d440c094002c90700808081400081d4540c0c07504415403032148070090540d8400c0104010300d03907500c1205503214140e290010305042e41c4001007019035107000b0319086982d40d905c450b0b9003040070100b6144040c8c400700000035441c5001d807020514681d5a0a00300c0350f0300c1c56650000d40705100400000a0035980138042d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921085665 1250 921084415 921084421
    0xb0c031003020a0b0d051005030309060708070b010e040c0f0e01051212181201050606090d06060305031b010f0b03190809061801120c0903030c1b08060613020702090f1806 75
    0x610a00e03080104900b417024146000f14107021014991002603480007401fa40c41c018148040000d564040442150388c02000e102c0d400200e0802111507000b84864007100c00c15180a203403101c8500c0f080e0b0042d0b0886018900103004044401e4181d5041d95019110050b41207503030030081d031411000c44503000640308002003100c4003082d491040701c19148141c41900c61035000d0400b15081e2901211f031340d50814002d0122803403525265000710700b43e038080d10700001c2c030326201c0d107503241150312601030050b20303185d1400c00c5c80a00c1030034429680c035000d121070200b141e46851000a5141d0f066003003000d2460307192250480074085c0481c02c807521031100400e4143c2e141c1c5038250628034074000145403808200d4040d00140000d00c2805001c01101441e907942e91802d04680d010340f1040061941500c6c0361404420522060400b0080340029020010007854289080c10400204e03418034881c1900440c0148640001610396104954000c9050100c5030f506035107800e280503500f920380d00c02014522500ac24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921086915 1250 921085665 921085679
    0x30f06020c0d1206091e110c0a03031b0201090302060a051027060614070f03090909050c0a050a080604120516030c170304020607021519031b0305040b0c031003020a 72
    0x60070f800000805414000300d40d80e812124100c8610404218160b101d5101100400300264004807042d03500f0b840b040d0414600700c0301c0506d41019041e0440200703545025003030b031180380d071446000c980032a44000c2c80f40480655000f52522001750402c8010780c2c8034404203405002e03004c2c000020b06038a02c405510b520354800d04c4000001d88a803035a442900d0700c0004140310b482546d5100e0700d00a0205a179140c25829640d005070a019468160100001c005000c1403000c01806441016030061004203840088242001340040791507110b103105250301c840400203080c0110311541c1c815080501c0701041000201d00b581d03d84560440c141c41c0310b12070410b00042680004000c529540201d00092074000701c8407218050b4481030790080d41c800b0091128400600c0d192010090b01c9503620500c6041c0725001c01e4007000644403d982d5004640c950071075100c8503400410442d00303200c151500744224109511803000407a0041c00241e203110002002402c0101004600b400440d40680350a90855a60785 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921088165 1250 921086915 921086927
    0x5030c01080910090b0415140408071a0f090f0c0112180206070b0108060604090314031902030a0204172805030915370e13050f09061f030f06020c0d 65
    0x40444603071f50380e181b0040f11132880e8030552138119800c90643c0c40035280ea485100e180d03040400d04640f1101e001c8141800544001c1000703010380503540752030056040500406003094031a1600f40300c16070000c1c01c078204c3d5a900028850750004010746c001a00410034105024500d85840042e400c260001400320400244000c200d049800000c241c030030703907291202000151046890042c00040c2400c2035070700700e0901d8000860304201c082040e500c414004021090a903007003281e4020546a000c6020040e25008103988800340d240107024125001e007004003100c0850141c1804400542841465001c0040400031140200801011000966504004900e040d480041d503246c41c94400c0f0483d030f1807820401d4402c4140b01004848000400f40b03680c089803172981c0254840d40c000d66405c1e0702c8101074420310919000390b1020703400c00c00d9850000240d624005010300b202060011070882400400b66008800d0192a800700116154580e01c1c140304020740070301d40070880341d400bc8450b8034030003a420003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921089415 1250 921088165 921088171
    0x50307080604210c060203090c040501060e01120501210203070905090318010f17060415030c03030905090c030408340c090608071e0b04090c03140105030c01080910090b 74
    0x38007103d2460050091041400d0301c0806004007003000442c607040000e02a4000e03550101210781165404201c04d17000509076282a4000b40100e04408100e001550b48000071a40d010340041c014011545003d10760a03040358401005501310814054420455801703112810040903680424401401c040c01c100d0b03240d0340540c020f080c07500f0f002520f0001d694001c0c03038040d0300304031035440300d0f403003000ca8a201c840350100003058103071710617a10000740c0b00d83d13441c2d251440c014500810b48500c90605514003e0070940c00e54000074030071444401040542481c180407070390301584c044551501c45944014140c858804038041c10000448050942218800c40016580d264022452500f455940d2000041120740718065240190070242c0284403e0b00e180f04441103440d006940c0f511000d41c1c0b04040e41c20780c0c0103504490b01c000e444400702e01403d507040c014520350030102c007030381d048075450040029650540c40e191a4184a0f81100040c1d58860620070140404140c49062080300702e00d1500d41d000070307422 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921090665 1250 921089415 921089423
    0xc100b04111315110d0e01020705060a090e072109170403050a06061a2d030f0106030506030c1806040e01050702010e060c07020102070b0313054305010513050307080604 74
    0x3c00c031841014420aa0102040b4000c0044c0c03102002c12401115010514200d00c2d0641c4100740300000c032500d03985c00803d81140b05680b024591810b0103120300e4481005400402003201409840c40700b680900e0040440700800e000024114402c1c0c94252452103008041149114020500009000d004503281c0742031071140804200270340d00d40208480f04200c280b5425044003090040089800c040800203074920060790b20030f2130300118010b0901c590b50044602014555600d00100101074044c003c203074111804501a02c3d00c2070b0b2035004101304800780028403000d00c0416002c1622034403654001614084444000c1c0014a000100640640340100030300d083c070302c5050005141802d020040e0345415030305a0180030302d0b40c680007281c41c440d04060411601113544060450006404010f55500c115500104000070701d02c180810001078001118402034625240c6440a1405103440680a0f1882400d00ca921421529040c0d401d04e4081e801094051244180200d20320000140441c451845 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921091915 1250 921090665 921090689
    0xa081b1009051f2d2414040b031b090705030603061603090c06030e0c0a03020306130312050907051203120712180605041e03080c070201031413030f0201020c100b041113 74
    0x18881030002120404150380c500c5d44000c0428003032a09149150800316100030404100c41031010006424000001403a040003d800100225641030041c565640149582019401e40c501070001c84c4d21800000d0011500d12150847c05241c1c1d8080d50003d00310076003120005c00280d0b21154050f00600c141d00120055108042c011090744c9401b404640940740d000e4080c000e19107501c81c03c810321100511080301803000c181110300b050304152089510501c1e070200100b500610b444140702c02d0070781d0f0584900700da0b0030400c0a01e41078030240341c60503084000da04c0d04100038002000c100006144000a0f40c00d09180b20608009120803034010500a60042c50211450100489500700050300c0080003000300d024140040d1218040c4005030500da4011b040204800d070038501d81d2200e10000702c590126000700c1006480505500110815452010723000031403400c41d0032500380b6529105c404041c000c05442d42031204180e1074a8000751041e00b40c2c21040b42c1c986542c20711200b0008210301480c002c90407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921093165 1250 921091915 921091931
    0x1f090303080a0603080403060f1808071e030e0108042603010905070504060f181203030504150b0f0f12010e1c0c150e0a081b1009051f2d 60
    0x2607503c659800c0f07070b9014440314074091030360765004046c085014404010079a9442c983c10750425900742d00c0d0482d41325094403030b0384184c7d41c0743c0b0181404134403840421101c0c98a0246000903080080e01200401c2403d00410540c0d40785800000c42c00003903403280310203c0b41660440340d0358620740954140d40b00301509015a03640e2031021039107802a0320903400003403509100108480d02600f88045200c0241168404480e114a001a030495442d00201c0c00203a80e1020030080c000501c07418010a05a07040c1804a4000f02d400190f02c100287c40c024410008024009040e550315240c0648564081000b0320800500030703105525640341005400500760014003685903e480b40c03a08001ca80c0c0c4c0642400c9080c1c09685400004014a2940e400103104100420020409da54098010010710400301d0311f0f000000704030ba03420101c4502c2003402c40c504001920b00040c00219241444101a01d115001003065201c080090081200c411625407011289404007014103803288072640908a401d0260003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921094415 1250 921093165 921093181
    0x6020f0c030703140715050a031a0303030612010e0a2105031009020313051b1c08030c0a0c170a030501140a06051b2a09040f0b04021f09030308 63
    0xca0030115680e415004a03a0a0000070850f01c0910b1042c50840200d6811a44643c080d440f068020401e04010520104112410940c107000308695184a070014014046102000c00d6407404040e01c814422180008581060301c42540026100e02a510032551458101e052107501d0303c015042c0b0340d00c850700d07010b038143e4400c3c05007003268054400c603030078504001d140a00301070003500064400000f00101881e098082903080041420011881a04540b06c4040108102d40050b0403071242140309007005941000c070fa20801501d81c0941c541d8265036503107848030401c50702c883d14120024049150980d211403024800c8001c0c1c10700c01038985040100b40d80341c5070002e8800111420155002240340c2c000d201036807042c0090407800405030609000da01643c0700440c104041c5040c0c5111040e04c1c9050f0341c0003840c6d901202c401c03028091b10290300c00d003019124600315070080f40c03000d00b02c1c41c54540820b086484d011402074810410400c860440c0c0c2d0032800003850704100f40300923000070f0250360100c0c001c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921095665 1250 921094415 921094423
    0x603150b18060906010e03030a0807080108070605040b0a090f030503190314340503060a0b041505030910020301120309050f030a0b0406060504061d091518010906110406020f 76
    0x41880c1d0340342035031140d454000304216414010106070401024070440030540d20208090700c3c50300c002c2d0322820b03282d00d0040001000050168082c03141039020721420000703142c0010403075098812910101c2d03952480403000340d8014200c0c1e80408250300f080c540000910074088041e01c503550410094041410500d1800c5058a07628050200030303020480100781502d252034010740d00841c0c1034400101a201303040d00a00d1509100c81501b02080001080007a545070084d45140500100300c84141094100001c11400108401d4001d09002d40080072880c544410420b4100b00c0042a80942d500e60710b4110312151a01d140300c00304e02003042c1980c0810726107401a01341c03403013030340242c0200310821817a1074203500140c0c0548169821503944030040307110740b514000c40340900b5903802405513902c9111b22103511300304020a16a201e801213902441034052802040d1741005001c107039000b11a20300d02d00c1900416000d10001d18440c50880f03115206000b40c0c4c040c1c81210303480e40945001448202c416616 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921096915 1250 921095665 921095689
    0x20d02010b0f131d10060f0b03010e07080405120a030b010305100828021801030b0708070c03050c0c0a1403010e12030f090f060903070c06030c0f0e03100603150b 71
    0x302c6101100d12040480032130307200e0b04070030740e91501609406050310b00c0c1c5400c040741031448201c1241c540ca01070028500c00324000d4010540c0d824214078543c5451058086400060b0440c410880e0003000300b000d10000b0000c1e81520520711441c640d40d80070801003d0018000340204901003804c0000158448120b980080115001f07000a400140b40c030052003021600214501d14004140700d01d1130001da12030b0940004e0410604000408039411414005c45501c0001e0028042003803800402c40b8095201049528950741418500e1711824500d218506107110580b1b43c80c0c201020301e200003005c06426841803400070b01a0020808130401e1040305440d030b414105040030315030003000440c0d40c01d04028201940b00d0146c90607034203202c0901000d01e040c6a029982c1a01562010407650306202a00c03910354020300b2141006c00080c10b00c030304050135040c2c405900809000d01101078894a45080c0320950414055030010840d582d26440c1c0072010b50380100c0c0300c01011386403018203206810072400d0058 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921098165 1250 921096915 921096919
    0x80a0209090402060a090915030b130c0e0c12070905150c1905030906030109020a02100e060711010b270606071a060a030204020f0a021606140f1306020d02010b0f 71
    0x1680c0c0c0d07030240708041d0704c1580c80780100305902c180068841d40710320881085910840c03c07107800d2071450070822b1800d0009800200014048070b030b1303080014221403991048450003c8940034517a1940c00001182c040c0041e00c81c600d0b00107004200c0d407940d0100f401815030320100c42030b5020603040e0b000d0320064003130b00c00405890350100f060758800050003640c0303150192151040f286440e01d00404244150002e9015443d0543c001c20b031100c420360140b0403100c24200601080044100450500341c0c1c610003d0b003481d080c4080d594001c000c4507801e4221580c00b02d4064003406045543c0101c1c18901501c2070015403138200c2800c0070502d00d160003011101d00982000030361104406054440250640240a030340d400600703280b0000050f152030019001038226000d20355103c8000500190070000c0c500f0345151a00124041481065000031082c0d080003600800c050715030317403080100c00301880b030045c40001104640d1340c0028544d074002210902004240d0090000700c0e0309000340034440c844e5103220380d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921099415 1250 921098165 921098179
    0x6041407060e06030604020c0307050709060905160f0905150405150901050a050d09170309010b151c150f0f170c0621010f09060806060d06150f15080a0209 68
    0x264252a103c800346403c030900400045c81c00c04608000303031665102c00c2003241c4079044410300b0009400715125220050240c041c0901c50351806842c61344010340500140018020412140b148052241142ca40603000203400428921b205258201d00340e0040d04c9800d12440e140d03000c108268100c0400c0c4c0320385030f0060b141c032401c01000501c00c1e60f040d000a05064690b6a4640c005804200c60500c40c03010040a004071943e80e04148882070b00b92986080b0700c600410a030051885104035040449052003601c507282c403003400b01c8031100c03070260081014401e005940180e005c5111000070403910304480d100200d1607851961202d003d8010040d82aa05e1015044036203020910308005005201e8680340e0852007000c0d14030b08984141c4c1010a8101d51120b10207070500380082c144910910014048550040805160040c0010f00100076128000c2c09907469503c4c8c010300000f608980406400c040000d000701a0301c414201c515140c842081b88002030101c80031418600a6208691020402a1a01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921100665 1250 921099415 921099437
    0x50114031b01110f0d09090608151803090901080105060102010b0a03030f0c03030f1a0a05061204020f010912141507230412050109121e0e0402120106020604140706 72
    0x41d00c2e8070030390303c00054140c000d100101c0c1000400384640048601c4076281c40c01e106007020590000c03140ea40d00507103920740c486a8804181000340718144e43c8407500740c40320741c400100a2201e508500a0301c07162904021140d001141e01041034012910665085e40200100031a9804011800c0c82e18480940410103014a40b4401c520400c14040444c4c040e060200341e024580551100b21101800c021805d9510340000400625041030300d8001007200320360490800f408001c9540007540c0c082d01c001d20070a507822140e0340a900540f0301c3c00041186165106074000582884089810081c41d40d0b406c600030a02c480b0920b0701603110301d074081c1400b40d444c051110400300c200e0821018495203501c0d51070081c400062000c5100342d400e03031401d1080c000890494200d02d00080031009000c41354083c089102494a41c0d11810b409145040825191440c012030807000400c00030b2040e0380091070380d221407c0c000314a803500001c3d000d0140e8495001c00c59006200d48034507403185c030039004140014000e0074003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 921101915 1250 921100665 921100667
    0x20c1813110d02180403030e01021c02210f09240a18050d021e0c0d08131806060e03060601091217030115080106030b0604050d0305070213050114031b01 67
    0x10000d600390060b01185980c003490b00018040e10016200c082d80800600c100410107505018801c6800794541c000e6081c20014000c900303840b40c4001401c0b800f030344e02048015a01481007001c0d0200c20302840c01e400c490030040e04c420050304040711381030f10700e108a040da02e0214841440c9201d00c0304840c40028056201c1000c0b06000e000e11001d8802c151400040800c08941d091100091f007042c0d5800034503020280702040044075594110b103520641020380441d4440d1260840305496642c0030703a0581c1d6403202c200190002c8151508989031340c590118440f5000b221991001d000e40701c03035444002c0d2100c400d208240d50b425049840302d000804450301040105d641d030180780b650a01c04c10303091401c000c1030144030800c1d40003648002e0031050000f540300001c90700820f0880c0504268902881003540b001c0100c2d5262045208036401060080c21803001d1604c584152046246d0091480e0190b11a10b213001c40540801c5c011100540c1403000481c00d0340c40c00041c0c1c0d02605a9030038080010b80c28040c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 921103165 1250 921101915 921101933
    0x3030403020f0705030709022d03160c0203030f0a050408010c02150f04021e0307080102070506100e04030f120605030102160b010f081b0d02120d0207050405040305090d051606020c1813 81
    0x41c100c19240c0c49d0b82c3c014159500c2507100307100d40c1c062075034085840c0d162201c45c0000c5103452003040f034113220b846c0207200090385012003110200ba00d2003069998a4490b2001103070244690303800f10785954a0301c0e60130001d00e980400d240040403807500c0c851105403200400b20714003001c00d0f42e000f98418052400d82900e4102405290704900d0001e042e20f55050342c4027083c900b640d202b108115541d0300041c1c00c1110138080c10f181c1030007805506100d100941341580d00688002641000c407001d200081c03d10056500003604680301400c005002903444540da0342c0d424543c01c070482c0048410380e00c408008152900a102c80c13208903103000c0c0080c00075080c10143d8003007050340055510307003014074205107801588554a0b01078181d00003600406000c0481c10009017011801d40065100300e01746000d00000c250700134145c80e02c0c0c19088901c0309000002c0e00e00245001c92603400503401e01480180000d07681e40124284030000310a030342c64580e410555101034040078084640c004c1c000004c040740c1022900b040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 921104415 1250 921103165 921103177
    0x306030d0c03020c060a05030f010f060c150b1503041a07090b1602060f070c050603070c140723091602060123030105013002010e01180306020c03030403020f070503070902 75
    0x300661304c04e0350010010a4041c0c5c891241c000214000106100c90250031041440c010074219000c002000c1c20b02d400101030f0703150010081c14441a80f200d0401c0001c10758810b511140b001403a85508101015106071a42c0085a003556510000d032020402480b610708014402c90307140d952404c2490900790b000d2400e070806010701c265071103450300d0300c401619500b0003803916156002205440d440c142c03801000e206010b40040d80211030078010710070341a410001540030203500c185203140f2032525084a80c606403507644040d000304101d034480c3d44120038020f40042100d200303895001c142c1e503c0b48080c40c0103071a02e0103030500590000004100301090340200800340606104607405009800c1b0001e4251182a0007981403601054440802003894041c19802a0a0300000554022107900040c00e4568401c440302e040c0880ca00307000c0500800d43c00413001442d40054119140c500ba00308041c1e5941088504401600c62a0380c81c1c0050100082c0f02c01c105c640050007010240d0400304860081d4000c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 921105665 1250 921104415 921104417
    0x1e0a15090b040f0305120f0913090203100213051c060e03040f060302120711152206061a0301031e02040902030d030903030b1c0f03111c140306030d0c03 67
    0x9410040744601c01880100001d060031240b18040c0c03411820310b0b9050141c0c1000c82600c1502c00c002e25070821800c80103954005200f212100881d4820324105d0b40600790354032000390315001d10500034400000da68050800b113003210404155040c1c4070000e00440489064400800a50640589000802d541c0001204080d03950640341004d036118942900d1010681100340420b40110304021028004820103174040368900e000ca003400f0740300c01d8090300c40c80221804410410544001000082c0807030700c00414611034441c0035180d86040c1032002c02060a805070341941c401c0f4900030001180b10f003064074140e1350044009408160454a0101420521082240c1082c1c69a6207140942d40038803a407006444c3da51008038036003410b4900201180c02c0002818810443d2885c0c0c0707079400250600105041703501c02001c1803444036500b41078403e1030a0703101103020b074894110f6122a4034070f050003013040c0310301316202d0540c00d204030100c106a601003102c0c2541c0561004403880708071840342d07002945060003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 921106915 1250 921105665 921105677
    0xb010c0f0b0603011503030507050637060f1706010e090d0305060307120809150f04060c080d09050f060a02091020031b0c030f0705091b181e0a15 64
    0x8208007558200403944c6c0260086640840c6280901c2018402c1c0c0d580001201481d002015400904171009940c1244c00440c0189020213076140601903403020014041004656071003598038103000a0301c4030f0706000c440040c0940000003410420105c4c0b01801004501c0c09442c00d0001041c04030003c090041003aa418402c030b90b0006440c040480a9034400d501a0a19540d42e0341c914040c0b240c401c140e03481158681c9400c2040801403001d0105481c01d5503907600e400084181d0368240721405014007204c0031461441d100b14a41040030000355a12401e512405a078056960007415030124010178075469040091b030b010349401c0901c5001b04505e0a003040c45200c0710f03204031407462842e54221801c410500039101c802415940030800940c601004120014003940c5110380c8169212004d622446000303c0050740800d2641c0c240e10310400400390400e44154841640d951880d510f00404681640203c403528190704440001599110403803e0243c501b400151134005131a00e041031444510040201e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 921108165 1250 921106915 921106931
    0x501061e030b060d0f0c1419020708150f0c18101806091a032514071b0506070b060609061605030d06060504080c010c0c08060f0a0b010c0f0b060301 65
    0x2554101600220001c0d00c400120000c144400400f101c00d102e4140062147c21103114065044000480b0800d24880d501802c00030303408a0142d1600c103045c0c21403070050040030708858150301800e078050721642d001800302005491ba072001c0b40b030521803000141c42007186e2140103221400c1c02c0101000701d0985280030310680000b500d60742c051050540001000801e0340504101024040500700c86100408003040d2450030703c44850a501c600c42d1044045d001d0000341c003084118020817076000c004c0044880075980d4070080c03130400c2504034001c8421110a450600c04034040c00e00b04190752000341c2c414460103007600d0304002c111030368020900c059401501085a40c6800200011700e9140c02d10602c010358440f82000d1000040d0707221038009004002c4240000c0004000024441660802c21b00385010b400e5402d040650181140b0b411030500c0c2e215001c2403100321900c40764103038441c0d039000404014403112000110354440c0d903810040c1908280500420100c0e1603a88410341140006000252240f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 921109415 1250 921108165 921108169
    0x1050405040515032a04050c0c06150307060c03051e04092f030f040f051002030c0a030e060112061812080907060219080307170a060906090501061e030b 67
    0x1e81c2c03c40704080001074a10070100b150070104000007081c0302e104810903225801040c4008040907440f0707a41d203d40c0e19078021504407580e900494072400c80c01e00550301c1078506480100089000c8885560084c440c4400018140d80300e00040643d599156890724034001c401d000706460079010440000118804000001c0c0458035031041d101d0400f058034010100c8103001c6080500048286d0301e0054035039080040240c0310745e03662115a8084d5100340d010440d0000c1381021445d1401c6c03200d800d00d4140c0700006000c01c03465080090140690141c2d410700c02441e5403005252101400c0c0304034607034900f40356080c1c000611560800b45001c5400030b90390b1400d522503155078041c08403980c814004511b40e5000e04c20004004d110481c05080c541c00245640890900c446001c07600c03c1c5800b8103050000310124105074400c04804076084d1003106100c1250424918080040c13489102c0c4e586885d203404000a191001d6025140c105c2d036080e1034001d926014658030703161205140f541d900c209079464600c18115 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 921110665 1250 921109415 921109421
    0x607141c0f060603141e0901020712350c0c0a05060403080709080d020a290711070e0609130305070b0415110304022101180b041e030e0f0105040504 65
    0x306074180c0c022403094a803c0c1e014048620201841c0d220b14a500100708442c3c0d42100e0307038039504000280d140da260341c800848500a01419034000d0410410381581091180e00043c0503501c44204003501401e02841c50ba00501100110001d24140e0182230000e011811080c020380003501d02d440c103440d106840c1d0341c0d0700c60405030200c80071808221140c0c01d1000c01e591051442e07010340780c080000c5c03210b0726107044040e40d42c0c0c4080030700400408103400103480f008480081c0400742d148401d032407442410481e50190200e010700c0d41240c2507208030382000501031441c2e07500d54001c88015000c9209a1104100880e010a841c3c509805010b0104055000180d4000002c0d120301c2c00742c070401c00c1c4803803101041401d0301c50400d030f1280044410b0040c440580c5c0c80081101004c5d0500b0b40403902c0120740d4030100e01402081e400340828005144050050046040c5e2051250744504025421100e81558440300c2c1a4400009400035071040c41030115814043c664a14540050500c0f43c20207540340f00107130607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 921111915 1250 921110665 921110681
    0xf0112050a1401080d120c030e031309112b020c100204031a0105061206031c02010b0a0807080717011b022505010509040f110c030c0f0607141c 63
    0x6041e990121207100300100d90b892030142c0308890140440d07000c1600c00500300d031a49804044060380d170742c45a8100901a500010f8465010303025030303032039681c4001c0700401c2140521403035070f9807810030400c250910099011129100b40c040c8802c080d1044440c442d00d50b440c64550098000ca50800090030100c0e820087c0c002c0f9640501c00144c4c0d41d50942c50210803403c0703090007003605016040018480c65888809542001c05d40214000d0300c0c1c5e54070070000740b0740503003040640c0410311043c1010b00d03250341c1034000411040c01907a2050f451940c0300d41099681d8a58403030b150880e002030078140240c41c00b01c40d0b50340540c640d841c000701d030a03d41c0a184603a40950780b203481d00540e00c14410705e440c80010b0901c8402c0c070034010300310303400c0545414006070040c495900c149106540da52401708105030254032414940007000b2181d81c4416080401d40d0b503d034000818200648104081c103007203c40005031442c800c00f625070b160b2041c5d80d1902240c801d5508003e403d103020340360a00c0f0141702c1c410f09101d8124 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 921113165 1250 921111915 921111931
    0x40303120b030715020d08010e0f06040605060406030209011d09010e04050c090c03010510083903040f0c09091e03030b1228050c0d03020a0b2503020c0c0f011205 71
    0x54801d030300410286ca0080d01e0324080b0140104d50b401000410030030080e5660203d55403005401e00d544000c0010300401c582d4001640c4030401080116615a044d400360412050a0300c0da250045410711405103861980396605074001ea0540050145004409540d508a8801c0e401ca4440340f50f10030002e0481c1da41201c58401014000c0010003061914004800c0500140d00b03045045041c524101104070784203425401d04031086110350310b01800084100200e214448074a50b4490420b80340c49880c25031034410550340c8034804000403844c10f032140308802c03c0c0b95101150300740d90a0304802c802d03807820852105500703040c0e07035a4042c03180d51501052003178044151409441220310708003060440001390148400b5412107842c0c94400101d00190f0102843c1c0200c0341c4150340c009034581240380000c8820000c15a81000d010710005c0b07003660600111200610b000002500c490a00c118224064400d80c10019440900e0148490511102500d01404185400c40d030340c044100b10142920307400c2d00c40c44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 921114415 1250 921113165 921113189
    0x130906060509090606070b0c03090307063e1818040f021201141b16050307420e030f090a0b04060f05030c0d090b1911040303120b0307 59
    0x1400d1604226035540300c0b070100d42ca50b080040544940c040e08070010108d0400c0da400201141c4460420030a849980b42e000100344043d600348010102210041030340c2034070420101d407200b90383c07111008540480d03140e80f0580c0c2e414022200f0103101c0824100d110700d904551095100e02010705500c840a12580c01107684081c811042e2050140720aa5800c0280c50b60345020303048034007110b0039440590025a2501001c04000c079411a0280714406c070032103414140c0307003681d50000f005000f10180200b03e003d40001e402c900116000c0c007860070800c002c510100c004d040e060a0142c10441d030284100e03c2c4103c4005100e001100040c0d240d43e000c908400c45d03041000c1030419031071500d481280050401508134508061500c00040c0c48100e00100e610140800800018400316841c005d907038001c900d1100c02c0c02800c0441c100410525815035206a800c00309001c0785031750029a00640400a000040403440c103481c64404036014151000c84000c183e40315a58131480d6074080003811301400c00c01c0510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 921115665 1250 921114415 921114427
    0x14010506090f010b0d1a040e0a0501060806010e042604170c03030a170702281104110406050a02070f03051c080603060a050601021006081b0414010306021309060605 72
    0x101e14400000c00342e00603407900000500152000409a604901c8030080c040340c02c80244280c52407030041c104540b078019241c9507010314101000200031100502440003003101035120208151500303002d028410020201001180001d8091000c40480f00d5215407000c682444108500c2d00720350080c0d01c01164901c0d1788e000021701c0c074010320038100703a4002100150706d042c02c8a00080c240442c6d20b030421145c5110180003580481c020b0008440398030134100d8804509030500182c03080d83c0341c6400265641800c640402c40c807424980b00d20b005c03526100403541d06041c41c0100403501d03984807010000c1140111000080c2101c0f403800050040d520900251040c0103e810410f820040c110140d8420002c0c22000d00409072800300301c290b001034031000042800d40d41d420040c1d161249111200b58400c1c540700e800a56450040b50039602010040800448594044100800c2c0c54041028401d1040c18000410010b12194014001e0082002840b0011990b40061104039140c3da884103012803000956 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 921116915 1250 921115665 921115669
    0x8070602014a0102043003090302060f04050303040305070302010212181c0803090d3e1f021911190303020d0c031a0306010b0a0e0d14010506 62
    0x2007114010044050001a111241000d05042006a41d030010702050841c41c071601d41000d28034007000b064420096546a0b40c504004c4001c000f42c6108180c08461164a00c50741c02c3e01104050312150151707284000702d400e603000c11485038030090305d0380e503604000c0000003059101440138000442c0035401402060b4918000a410201540705100030110200024815590700000c210107520054400610703001c5c2441d800b00340304c010000c0141204c00c0200402044d001c0c000b0300649041c0b4943d40340c0c0e04104440d484001c942030012002080c1c0010f00ca1403041c9030702ca00d00d0340700788502c04100f1160310040e807150100e48a0000b141c0300c00140c0d00081c185048080000c80d540f440581890200c40940140c4500c58941c01c0e00c484490b0140442d04c40710090603c02e030140c441d1b8800c0b6880801c980b613221200034004041140c0d80c000003240410b2940f4075850003068440c103c4903c1c00400f481c2102c0008201c1e4030022040c05250310202180583c80071400010f03000c0e04204400b80005024100141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 921118165 1250 921116915 921116921
    0x60314010509010c12020706151211041e02072909010c02060402060702091f0807031e050303161107030305091207052803061503150504050c01081e010807060201 71
    0x922003d80c100811402e1440d071091556442c40341e030010058841420b483c1410140000760140e4002a401d4800400c0b62410b52001e40d02c0340c0e10036170b01030100d141920148030640b090781070010040900002c54014400d0303e80c00401000d40f080d111101824494200c0c10814115a404180c035516407404000c2061000d00ca49075551380d260004000c280752560000d038161040190080c094a1041d0220300321020111003409000c80d009800016a6103402c0300580e240c1741071000741e48404d5200880d10685da240d00ca201a41038021020314656521000507599480300e50109400304082c11b82060110102072150308040e40c032a0747c0341e50b46c4480f04820428040411b9618244641044c030302003225680e08840f400d01542c20b222640b0005054a0321051041600d6001030001828082000741d0b48102d0401c090a4070703c541c0c2c01d0504d030303035490400c503040b03c0040350010610b9222100b0341c14190b000310f10385640102e0b00e2094114800240042c8004000d081c1c1c404001e030f9201500c14484a50280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 921119415 1250 921118165 921118171
    0x60c0602040506031f1a09123405060310030f020a0b0d2c0a06051f0f050108010b070b0402043207020c060c0c0d02040b0a0b09010e0f0310050601020c03010603140105 73
    0x18280380080e81840b0b0922a03a80718002042d0f11902384051b0101c07100c3d80138442c5022003106500764143ca01c1e2a6a01d182e811030442084203841415a40c01242615040c0700f13030ba0040d142000d252120a0440e542c64052100d2a44140d90001008600003170200e4240c0c014441001c003800c0109044140b9001c00f44003100c2c00780c117040346140102e800410a040014100081c507008503010406454000403014507101c040620350a4035014140800c81c41038402c6d180d4100d60080c4d8800c035060780d9945c20860700d400f4040c030040c0300c1c001441c0031801514207a08507192180005080f00c0d25080701c0e2240c445020318440c2640c101e040a5001c100c80c0c01e8050005c5521894107403580c40c90002070340d0f0419160851440c1162140040813440019500c49901c24210072101a05283c1020b0300e4122010303c50b0484000c03140082c1107007121010303606240000440545014000702a040d2100c61030b60041d140c01440c240c1140b0a41d4031144007a5000d029030720046000300303d00c52104001140c0700d802c0d51402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 921120665 1250 921119415 921119429
    0x30109020a060e101d0d061b0809120f16020f130e010509010e0c09040c0905040803011e03030801061b020a181406030a0b070c1a07180f060c0602040506031f 69
    0x400c1081e98280203002c0c240c4205d042115204030300110340c9800402440b0301c4e5410408000b40c007603000b03480303608504418083c00c031040854410003400200d40080d40300300c24000d40f2980044c4140d0b400340d0301402406090900c014084001c1d90410300109103102c00003020071100c16121494141501c20a02c1510380240424000b4050b0b48000340b58242d0711103214804502402a020010b03003440501606500a00394101c4248903d0030241050000e5810038050825aa0500385c2c40310407a003910384410041740e40c1501c0701051a0300c5d0803010341303000f1300004581075074410701004000160798034142c000c0034102d925141500302c00004015003c1354030841c2c21055400d03a0070f051103c1950700082000700c09034041000c203240c2d40c88a0b03080f101c005004000500580200c000440c100b5481945103116180b00d60341c86404a03148840780c41c2c51981c1d0b21640d22070000030202449528482c103018083c1d01d020b180054900b5584d00d0102e0303602e502c00c0f40d241c40e0511301d003d22020b110191440710b20040c070403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 921121915 1250 921120665 921120677
    0xe040c08070801121103060a060e100e01090c0516050d090609030b060405090313080604030e01020a0b07030203060307031b0f05121b0418030905031e06010311030109020a060e10 78
    0x1206901628241c0113005524500b04030014aa0070007020306020003008501a0503280541424034191001e42411b0107401c029425100000e4050303044150902d046400c5414900d05076464034011030010020600c60000f0840c080118940c440001440401d03a240300d20300a0031560202c1500030300340389907034001c00b0410040640810101d20b87d4140301d0b0304030004940c00649511016007041c07662043c2015488080c8046c0800200fa441c00b01c3d059110344d0194a0b0f10350016070381c100490b1107101d0050010305140d521000b24000500c0781d40590f40c80301c006004c41c1d00e11501da88401c8100704202107140c1e0500b01800051000800f184482e00c010402aa0301084506044481070344400e082c44048039203c1d41207203404059610740d00f01e52036210541c1300504400708503041c0180022100d0040318000e105040c3c12800d800c039088100b9000402c3c02001e030a5a9085a4404443c000c0c1d070b08440f5407540d01d822565015030390b10131810b07004111a40f10482002c044806000700f40e00c0b040d40000a101e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 921123165 1250 921121915 921121921
    0x120a230111041809170705010b0907021e030c162c0109020d090804170607050a020d0c0503040e010620030306011416121116060509010507030201060b0a0e040c08 71
    0x501c031400d81d0203656040d102c0c0f0300070020034156031000b802c20303041c0506101114014090043e0301a0020602c41e80110001d206800c0c1070f00620101c54815280b5400686c000c290252100000c1d04214841044400940b460500c102148514003900b40d0a49899a1055001000b400092591041e40c002d02c001d01441c030340714406450f8100110502c515103150784c000406890003917103940726805040c0d104003000e40750781d180c04200c04c0c0803042c6c2c560031599100340000300e034201d400740f002d40d0703031503580c0d0f03401407150001102e4225045848002d0807100d030312083c4004510280000c0c07825010303043e01d90b20961349000b040d1310100806a40001256290020402d000300740e40d00c121100543c43c0064007081d038420a24130010103846070254064542a0800141700c07040e81d1000c10002d0340740c2003800704c6072007250b0310344201c881802912071000410000c101d2646c855001324090600d0034080e000004106a407401c04240c00e90001c00c43c0c40000790100304075441480c0610130030361412a03074034018074140703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 921124415 1250 921123165 921123191
    0x4021e0a03022104080a05281d090408191b060b101d09070e0d0501021806090a0e180f100f0c200106050a0b03040c06110604030509120a2301 62
    0xc0b2070300c8151401c0003000142c8503800c00f41031100d8007121408103048d10102d80344900080c03054842504118000403c0c6da1b00403070324a00f40c074809000f07607000182c00e886c142c0048080070209110072840c200380440e009825100c1d141074400d0545a40c054800400d0b590307810340400c840c000081c07228038240007804a000c81c00820364050801e050314162520342c03240c0c4602d04180d40315122102600d074800c07141e10111042000c190040c0107010702100072031103108031103420040f1a0240340b41054002da081b880801c1084002c044107a040003a90b00000c01e50f140c450b984600b4103010003500c02050b8070428000450440d648900d14a08840800802101d440020024400c0c030f90180d5018003005044e0381e00031449401c0d03000034000c0000610160880741d40da002101c29030000c0f036040e0f4007080c4012000079103900802080c0c941e1050000605165500d03540c2c2a90380d9009039030000d0b00103409404074404080100301c0181100c0c0500305007940e11180516044103400d81c0050348840c0e0b418030040c00844 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 921125665 1250 921124415 921124417
    0x30209040b040501093804090201120f20090f040c170429010303080601080a02210907080f0304090e031204030512090c0607032604030507060501140f04021e0a0302210408 75
    0x7407030107c4021030410020b00040303e95a500d80300000c2401c3c9040e9200905150030b502c440c06043c0b13007100072520350440140428260046c5c0000c80d810146c0b0001c1c0c28524075141c1e005203210912410001194614040c0281034108122001c075410b00010441442ca1444c103e0300d04512052003080701115030556a00808403403025040714140000790001c168290341d2a015a000749250041c544840740e8140e220107038000c420755056080d800360400201c0c030703d00e021803849111300c401c0f001545413610f030110560040180c10b00704441e900090043d940000b01185e6000d006602030380d9850f031941882c0d10004407400002c1e040c0b81c00d80d404000703a1315840c0c58090039580e00e1074050802c81c200d5145815500c40d900a440f000908842c4100100b204141e01321000e04022030003003804000c80ea032190300b000d00c65045c00c907041e58008031303405485d001898945c004002036264410915a00e130a900300c40700c0c140d04661100c2c0c0100b5008181c150303130342c1d60400c0200c05a0308104030351041400c01e40c5a001803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 921126915 1250 921125665 921125771
    0x6040b071e062903030a091203030f0212010e090a0b0601110102070210090323030f0f0717041707120602070c0b0a0306031505040c06030209040b04050109 68
    0x40c41544034480003105040210103429160804400e12400e000910f015008601083c030301d408000c0c1e0200b071400d1904001094543c0c14000d6280c21588900308500c9040c3d15200680c00c80030103448a05280e018a068000740c0b00d4141520000f200d80d5041041000080f1070090940c200c0d5130080006501242107403400c1c41d00141d00b070030001c6000985a0000d4003912071400007a42007200b860100c0b800e140e01082c11400c0364055418404003007442c80180343c92030990b00044140e98400e000840c8100b9212005001d46100880d403079242c102c0f40e5440c40040391101a40f040360800c0810100030030701580f40500c0c000c01201003e03054040c10403009180c07a80d24114054001a800300b100b100300084404908090f040820849483d981c001e0001005080c440c00121842d07444003442200645003130040c0c40c01a86c0c001c0e41c04000340e09100c0214000c4d004012165032141d1030f4100c140d402e4075a4440c0d180038141080000c200c0400c2100c9040180501d0800c2141100f000b41085d654511a00c8400340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 921128165 1250 921126915 921126923
    0x31a0315070305062b0302061e07080601030e0105090f120702130e070305031c150b030f0910020c030d0605180112230c10050a143a060506040b07 64
    0x3c02e03481c0c3d240818550030350740d820390b0f45554911841e1a240e1000b141003103005482503003150142e50303490360f804800c084064421014601d030349010035500b900641a42c0d50041042c03400184085c00040c1c254250f405c1511140340c590441e89546500d40707010f02c11401c18000141d01b0619001140e40402c013003400011516443c203595107111342c1d002c00e003801500f00440e0080200c030340b6403540030350f100c1b02c1ca486620031203201858040c01c110084a00c3c098201110510000507040d9941c2500c85180c6220081c84101340d030145020302c0c00c8443e081e1000e085a100404000c585441280b8a00001c8481580003203208401d00038440703e140d4007075445281541d81c024613000450743d161529108806c012900c101d41c50040e5901e084603100d002a850741280d000711650254a0b18080c0240c450740b02da59105d0001950b028500159810304800030303c1d803d000e601001c4003100da101c00c0d9840d4070713820744281108455806814003079204a80910317005080b0031105280b038640341020800c014441c0e0b1350010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 921129415 1250 921128165 921128171
    0x90601051305060d0e0604120e031b090405161e0b122809030314060931020d03020a030f030c020a0314070c090204090e150117031306031a03150703 65
    0x542644c100c1e08076541e41140c03074040f06d11509007407034900c0120108101c042c00181c64000c11807402d180004860707180c14038407501c6541200154052001c500b400030802e0314240301c1d0f6500112010f40005000f00203001480a9075207014074060000030a916030b51000b542d41c5014483d0f0a84c1d004044110741c1c0002040039142e0702d550392258540c440030454040c401c58245408100350074140c01d50040c048d038900c030003924441680e0751b004000a10600780c1e0308031100c02013a0480c42d02c40310b41320700460342580741d0001c0d21300c8440d01c1c2d8002005654044030850058225145080425030815100c4a280100c0c1c01c0601c054090020000d540b1703807481034064100031035200e035a10404101d00446401c01d0b0016143c0000584404808020350310500c5600c2d60b191800100c074001d84c001054180c0340044100c58650280d203044050200712003407924125050104100e024a20450324491038000c104a882c0400c08121410400942803c1d4150980c0242c116010703081c41f42c0000c3c4540c90f80410141000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 921130665 1250 921129415 921129427
    0x303091807020f010c21050415050612070b210702030316121503030806150301330306080c010804261606020705010f150e04050307080301120209060105130506 70
    0x100e1603c3c00b007480030021075103481500802c1507446039484e44141c1a50003081907031135034442d4a504454046030003600c0390304190044002160180c12aa410020052043c440038481e0708006080001d5075101041c5990009120b4131b00d8280c24544407041c01c4103260f002440e20348440082d480780302c0200407054058a9420584145014107078045a1103c007500070081002400b000c16014921800150080350740400007402078684040c1005198071401660b03070459181c0703905100c207010485102c03441822590000b08507034011211220083c0c603a030703034041110f1380307404400e904180300900f00504001c819020040841c0d8482041c0d0510003245810700840c0849011840303690250541201884038081400d0f0300f40302c05500a004c2080c081c20003001440103180c1c04504540920080c210a402124010060154140c6545a02502031410307030b458054203544d10b200e02c0d4000d03000890b845035404401e90035800c01c3c1040c180d2107102804c00600c1c201e8803a40202e0180780610a040c031840f00001c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 921131915 1250 921130665 921130667
    0xb040504110403081c230a0501090b030c01030b04060e04030c110f061b1629030402010905011b1b090e12190c0203060705090118030b13020d0507230303091807 70
    0x400d211400c00728070420740310b5241c0c0e054002d10318103031401f5008508100004c9415400c602c0ba00183d8003000f0010300103803502d400150007419540428640c800d41c1d40500140a80744c1c488030500c46d5100c0d0351000070102c2c040c03606480c032110102e01180150041c01b00307801c0c4c50b1164011143d1010305c0540c1c0721210080aa0f0451030807820050600e01c1c00f02519000a013145032020609e03c0140c04440e600d144071006080f003610780421140a0300085201c8001c100c103502421b510301c402c07044100c101400050716101e8001042c90425011869550342c1000c01020780640b10310a1004038001c080e2980308080c110010701402020700b600c070000c4800c11201e40d481c1c028024410525405001d442c0b02d80703884600a00b1a41103000410b0110781d0b00394000c5500041148000103403644401888413503201c0440340720180c451408100d801101c10510040070501c100010130080560101804d00300718603140221072404900410340c082d502c2484000d0150b969017100f1890a40f08030b030a600140c1c0c4800c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 921133165 1250 921131915 921131921
    0x602070501050f1b10051012050307020d080412030909060b161421090103110a0207090c20011a0d110405072a0203070e0c0a0819060b040504110403081c 67
    0x810304c405214141d04515904180e41001c0c1c0703d002d04038040014540c0e14803a145150049000050481c2c200300000380051411002d9958214020107086003026100c252454450010110540c0800c840e040d0420000c0c1d0300c0e0144074080c10760014070605181c2d91040b6403114035441c41005054400201c20310328030b02c00800c040300c10802c11900382018240b0300036106c08168000081c0c2ca00107804d049040501d4807009044512206066000303228461070301c050000149000200401001100c040c80c43e20340e5020109103101c1c2117140c0000400f00e522000c0004507041800c0305a000c0c898014807a40424110720906109610a95010406660f444012549100e0151151a8607244100d002012640c0c0e02840b00c10140300358101e908081d21281c0d400300092040340c2da1741c4610000c000c046409885500e110346c00552031000506000c592548440955030150820380854401080c204414a4540036140c0c9171120884400d01d454115120088070f13206030901d0f83c034505030f060a50441100258 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 921134415 1250 921133165 921133207
    0x20a060b06090406030803190b100807090f06020609010e0105070c110a050d120e030a080a0e240a02060a020c03072d0b010305160509070c05010207050f030c070602070501050f 77
    0x24001c1244e107849140c032071340d41e410a5a24130100580038a004138000d09500c90003182e50360003000d42074000505034040b181c405008004004214103180001801d0391921960809840246c0290255240c2401040d00312100d8101c04840d580c102018005010f40109400c181103404c4000711080014900114050200c194040d51300410098a20014040c890f001802260403560314269041500b20400d5502c10704a000909152010444205054028100880c12103c00380520724030000d901c0d01d80e0f90048229006254118001404072000c541c1408020340c00300e0300c0c86086003804a0a4111940c03030054200c014086a018181901d002081500d030074608001e800001d41e180b0b081e4900300b40308000a00c000c40c0c151081710f004140c04a82c001c0180c3c25540040c04088803070b503070a501100c08230124001682c083d5805c01010000c5903040c8072100c68200078800031903480c0200a030f85480c000707842c1d108404640101d1f0041c04240c0e88002100c0e03800c20506005a143c141203046400000084 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 921135665 1250 921134415 921134419
    0x5011d030d091e0b16240c020f03040f090513150207110f030c01031e021b06070c050706051b0d02070e0c130b0a02070312020f011a01020a060b0609 65
    0x1000c441c212455019882d203003a98043c504840407000e80c2050ba5a03004402d00070192488401c1c060803000920304144260b045004071421010644140e40d44101e4039040c00c1d0003c50740347c0307a007056810217404009900360301844600440c581b5103040300d205a811000c0c0650481030b070715000420100031448981d900281c6e00142d400f141a031108103404001d501140f002c82d01c0c0170701080300700c0c1c803450804a80d2000503005005003440f0747c4207900450040450255410f0003031000042c804076842c9a2010b440c407203000c0003003a00c100c1042c00c001c0e4034044009103105c1c100305100c42017100252012550008440709401c06545601030301303060500050b94071640307e04074810b00e1811a4400e0f80000c4c0303c0c1c200c2e110603a50001c180c854002c0302030b241c4036100d0300040710055030004000d41007441c00208a146240c2c41520400703070f100e0751030740c142e20300010a9000680c06010000c012000a129402201e043c0d5400c1d00c03514000e046c0040d4403000140d4001d001c0c0c0c1e594200980707031516510121030a074000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 921136915 1250 921135665 921135673
    0x3090c03101b0f050d3201030b010e040201091205030708030703020a0305240f0a2120010804020913060501120611030c0f030405010e01180b09070f05011d03 69
    0x10546100e0000d01d101c80c900d0007030b000c0080c1004a40c0e8099500b90600c0fa4641d55550f1404213140b41c00c402800c0b45403001c5e640550802c00903042144100911540c01d040d0056040180d45582410043d1401c1038004d940c000b01c290060000503a0007003207110485030034807441c0300341108a0401d113045004144018000310800000c000b00327168540d0041a0b035100a84041202e600c804548424040755046844600003c221301030b0010b02d003038014080d481c1001000b0249117619074052420381c40d08440c00b5103141c0604801182081500400c00411a003449a42e44500c18a000003d00003200640082e0180300c084020920200d2072009889116400031b0050000d56034951502d9860b450350b850680d400303450020341c040368020150840740a900d60b044414206241c0c1e804c0d41c1580c1c1c1c40500215240c1d961654010f84028081c05000d150200203031485801242500341031900700b0004145450f00d0300400e20a005551040140c0c0c0190785080c070300310940c8014009212051818406155030505c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 921138165 1250 921136915 921136933
    0xc0f221206020901180303122c03091302120601260702070602071a25050a06290a0b0a02030909011206060605030c0a0c0f1e11060412060203090c03 65
    0x7001d600140559075003a80c6028a0810800030348034610030030f01000340090703a0544540c200080a8000e1140851031340d00012000d41d00042104140e90409105401600003184454440c5020100d2000030f50011106600d0b001c4031601c0401c002c80020011414084100e04031040080c640074420140680e01040b0300d06400c1050000c1e543d40598803543c2c00520510a0104202d10181b0b41c1080d442600e0700d4080c207221507000c00c24414800194a10118210100c503a404100104400403100340603540c0004c1e0019090700301c601c8403101084030b081c6102c07680c1103002c00ba01c5003180c400c00c0301d040c420055119094038070201d00310b100d0307458a5644094030000100f00e05924020aa40705842a1400c001181d60b4a00c02d03101c3e400204c0c4e0241c00c20340188406203080b8000c103070409095100341c00c492030010b45e91796040214005083c221100e03d0b51806150100400b1506020001c50216803103806e0602c1c0c10030303451018003142e030000c18184e004408107a0001e0200003076443d054001b011307192907070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 921139415 1250 921138165 921138173
    0xb09370f0516120b0112031e0905151204030806041b02100b190e060a09110c15060310020f0d020406050c060a06150309030905041d060c0f2212 63
    0x1080c1c0424081484056000160300c035401d0203503d101d076038004180d6449031710b0045a003070a8982c00506405000c600481c05003402a49025485a000d40c0e0310f66500031824001031021802d02c0400014500104100f58090244042c940c1e41e17125526103000249a55200045005420a42c80e640c414140000f03103840803035004580405880d140900801040441d18208521501e5003042c0c42548100ca003806e2041861804256a1008000c3c20b10520b1603915a90310040301c460075222003051101181010403404240700b80822184ca20300c40e4501c605004000036190490350040540c00c0d41d0005207001141051400d844113000714510854881d580c840f4090000d85c800124100035008000c00222000c01d07a00c251002e450038070b0703621046e04006210641c000c01d0800019001c0c404082c00000d080d81e03543c02030401c13210880754240d104c41000303003c003880d14101911070881c5c05024000b5451011440e0159800e141400610a0611076414410550001a82c004004454412405030144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 921140665 1250 921139415 921139423
    0x60c0307051204090612351615110715090803011401080a0509030f0702010207030c0e040c2304271101090902040b0f1e031003020a060e13020c0c0307090501030b09370f05 75
    0x110f4010840040d0458070f010f409c4080391040c01c8461240282480004049180000700391091110608006280340d06501d4140842c1c009034004000705180310050348081d68003001041d004140ca040c1400f46041011000e520390203144140110680041003000c11b581c404c000d10703802150030403041c4203041c0e00da900c608504501164203a50b0100c281c1000548020031340c0484210b016212507545001d401030041202900d042d0020f0801140305406c1c01c2500145c58100079421440760381e20b6001c074488140054825401356001c10b020a1040c0000c100c042e40c120300718bc40081a803001180e440711014138a40340003505000c0002881c0703001c0100880b44041c04000f0043c1ea00031500314040355a0b560007220003812251209401c01c0d40b900500d6404100c580140c00c014002c0d0b0b044d614001c2d0084080392600010742c2c805c5030015141c400400500825001c1244c000a0301000307407540742030f5201d96054180701e0240202120081103400100e001d004030006000c40d44c40301100d103881101c0d003403065503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 921141915 1250 921140665 921140707
    0x30b060d0e0609011b021b220b1c0f0215040314070306060504060315150918020901082d0c04050901020909010501090f05060c030705120409061235 65
    0x7640d071034600f210002c03000d049035940c0c042109500030083c07001141f180100300c40e403905840303400c0191442942261000a4145a524142003600082c400d40b51001c000f05c4006420000c819001d4407040007010030b0320518284000c54040d2800e00c80f0103150740da042c3c0f1500c6603034005400305010f444010314407500030900f50304607405018284400e0341c661741000200d42031440300070203220554043d5003890009401104140044403860188140c2d240700170f405a4411401503e02d28080444080c11494a40691400f40095100410a100c00c240990104081442c641d908108003000e41090740e990170032603116a00c03400b50083c42641040d010700c9003c0c0d00300030b00ca1032044044200100da217511a08058086800648010107500d02d00303028400990305c800360a0040e0302080000d240400e03800c020321360012890060396541c940c40c284036842203904a40000e1284074900401c0004294188146450004c0c0380d059030095851009144803820b410040c10500e0366800305040c12032000302607403841c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 921143165 1250 921141915 921141931
    0xf0708040e09240609060103110a020a03030f090320030c0a0c0303110d0801051e0d03081008010b0906040f090b0c0a02070f1d04080d11180d12030b060d0e06 69
    0x1d03103090708007007100c41010070407602440c3d0503010000c0c940d0700e0a040450b0300a80181000115401000d40114440e070050706164007507400350190108040e8148100f0050011500d02040941841d54004002042d04800315000c006444100b030084c0d04c0500403955400c0c50740e4200c544140c07580c40c050140c00220b2000354045201c15081588880c2c4c007144000300380040c3d0380d884045a00307100801101d891009600c044030f24501c1c66241207a1281a0035512041c0282c60382d101031301d407050703c2215190300341c1c000181a0b41401c0c040c030141d440d848a10740c0c1050701200d01050052075511114001e1440ba60054134000707000c414000c00031007801c000c00c2c1c0b2841550035038481c2ca459402c0300d400300103c0d11956800c0b2041d845c4000b400401c154030f058102c6d1240a4440c0740c074600d540c10358281d40c550507070b440c1c0144000503801c00b6802c005103100d040c06001da501800744411612109a49918180240c040c540c8a1000003260340d034040803105d200003203c00811441303040c007401a40c0e0343e4003168109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 921144415 1250 921143165 921143173
    0x8040504112203121701030213060e10050418081602040207060903030b013504081210050a120f170c160e07050712050a030b060703030203070212090f060f0708040e09 73
    0x10307030341074451400340c11540c8110b2076000305c2e64690f50038807085544c41c0f01d5080110342e81d0180825030765074200c6414040d000084030103010034180b008010403121041949940484174080301c00002c0c0c540070680702c103804000c0181341c84510310b0002c50003903c506400200f800c0d1501075944c08160301a400f41c0f403c000280da030200d8100c1d4241d000040001440c00344000310b003010003018400004c0c07428182d0312511480c1c0442c00c01e0103071301c00f402d030b000820b03211102c0b0030540c40414032190a00040c0013004103003220600115143d41e88a600d0700340c0c0c0c1003901a000c0d890042a58014040c1c401c12184030103025002c58210050940300c007000b010860189010011071040850b00c4248a14140c03403041d508030038000c0c52510040780070343e41e03640481181c006041e21484245103c1ea20b44020f024000c1c06610056501d01c0c222000900345250800e244805007018060810b0a03243c80c3c1910319200b005541541da50a40c44040e04518014408000c10a49000a004c50301d510381c203802c40d003c0e0991600321 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 921145665 1250 921144415 921144443
    0x102030a0615050f090301151503051605160302070e07200a03052505120c0d020105041716061b2303070e060d050405070609050d08040504112203 64
    0x4640c0c80511507030b02c2c000032014000d20101d034007070030020070682c0d100030000584001422061161824241d100900c3c0800744403c0000c1c89816008143e030000003403080ea0041800000c0203891401a03020303020324180d0320701c80d603070426001700102000f40440c5c1d01c001c0d8051800f0440100a09500203600c0d60f0783d12105a0b4210b1030000081e102c10440e4107407955400d2488040700e01f520408264035000d06008110381c41004984180000c641e880f2806040a5848131000f034035915040c6050070100841e0b02d00002c0001040c4c8840780514003400e09028a030307540d030300c010724030704860701069024005603d814880201422030228404400010352900d03400c1204000e940d4044009000940091300e03020000100c500d80714080c01244001d0086c0450b0030409200c0e10b500454804560803142503120440902605401ca080c25008200440e454001c2001750b07941c2e40d00f0382c0a24412240101e4882880c01303080760b10301c2c0036211302c494481d00065175200160b01560080c0729601c02510b4500d00c4001c0c2c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 921146915 1250 921145665 921145679
    0x90f0705060c1e030d0203090d26010905090c031b0103050c0307080a1d1903080c070507170c130212010f0e04230a0b1017150403090e01080102030a06 66
    0xa54006803402d40c007504940d6441c0001e41c501c1c100840d081d03001c600007080305807400f6031184080c42c00b0340540c0004222030034401c14040c1540b030b403030b04102e052044140001003050100107211070540300b003000003003103503200d540800745010ba00c80b4856071705005e108452055405640c1641c030f0200380c02d0b03130180480d860f28080081284020340340040061013600008040d24a103410986071042e8816954035484661100d80f07040c507083c0001c2c1e0b80260702c18070300101850351100c2d8054000b599285414507020096503030741e548400c2440f5281c1e2a41d001442d4141142c024448038030003103009014404140c014206c100001c0d808004075100d0b81d05c2d540700100d805603099101e242520200035003141c15803259250180e00080c13110400d6424000c0038940a0180c0040c06003000b11032190403480e443d400c1514041702d220780302e44c002042c116080c0d5200201100001032402e038405e0801039106154642d410f003107500c503200e50040d4100036441d030f00003d03d2880560045201d0b21040c04100002c47d203480e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 921148165 1250 921146915 921146917
    0x40503060610030608240711030d0207020105040308162d0308091903090e100308091e21060a0507051e070503070b07020f0d1e11070f0627030308090f06090f070506 72
    0x10303230301c00e250b0f100f0b10000c080c46c101580101038046c01410f10905007981c3c3c5c0c1d19200d041d80111026008502032045490400007600310000b0201800c1001000300d425507854500004240d00d80582008150000320f221040f0074088011403e260400c203c0d40300380c4d941400340124845101e07100e40e2541b0758000a90b450f12882a0030709030380e84821001c0c2f801100e81e041008075108000d001c042d000c1350111140c4079540d401d028400c1400c045c81210001e01c1341003072072070a01f8001007804001606040030003041e130358004120b91000050785080c60b0006210307441282180500c0c10010222301c0000b80800900c40950302075481030009900320340000b0132229226844031114100d40012034140704000d0344002d1501e92244441040749813220f07004075004091854500d550303000b0030660a0341201031081c207600c4050b5071150814400620360b01150061072100d05416803001404021100011a81c541f000f8055000b51050060403110f25050920302d80b0380714400060340d50410301c00d6000001d000d04140d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 921149415 1250 921148165 921148187
    0x50f04030c03230f0d0f02010f1a13090f020415091a09010b121503010e070308070b0c04031509030509060d15080714151306050405150405030606100306082407 70
    0x39011700110742004209803a401000746015055540f620f07840c5a680340e81d441105099a00401029050600b45041c001c0c84850b1040180816003040084c60100720201d01c180d602c0399051340c0c000b80781c40d0a00300f0381700c0c52401c542000e0143d0f4102110414403c580d40356100c40031004843c80500ca9903202800d10340d910039102003603264003044c0c00084540c5603070b42400752140b1000d000030441d4440403030ba00d41051001e400448000707402081c624140030010000550080384180d085241030709546801420034609101d804100c0d443e00c504c10205841a0f05680d00200c0207003000c0d4803100e10300705607030243c030b40ea00c07c901d0b48100810000554050010700082114405194020f03105405024801c100c5c040704030729082804200010b06108011020580003808683d0301d940d219800c06007004010a0f94500441c0c284205000130701180e41e022646580000040b500314482061200c401d4015088c290301c1032410303000d5440f10104010440d001c1704000091481803052603514101d00303640f00d40e004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 921150665 1250 921149415 921149443
    0x70210030624031d060f060f01020a29041202060f0c0d0e07050a0303050417070b030109021c050a0209032a1302121305010e010605090601050f04030c0323 68
    0x2c2c03404200c0842c0c000030301035001c02861a0100b00411000000b0110541803504424150b02410400c90720003100e00f100c0350418800c0310f101580342ca00000003507503040c00000142802120741c000c5c0044510070325814910100700c100c1100300b8074260804904020b0440001809030050b440003e4921091103080b92240906500359400e00c1c210841260003090b904803c4802c1c0d100d0001c000c00c1c5a942c00c00c000300114420344d00e80c3d60350350514a41142d40d9590b20451800d039071024100740a02c502010680b4152002143d0042e156400c40805003080c0c1d01001501c10070307501d040c082c0101010190001c2103804425400c44111400d0b10944001818666150501011324150854403604c2c7c826220b0300f115400c5900541013020394010203c00c07002c1501d040f80c01d82c42c81c1d002039003000070030700a50003184240e20007081424a803e02259076501c004100c541000300002d00040a40d4100c015a17000d180c015000403601c540b02c1c60000e809041c0038617000d40303643c0c443e4107042d0309400000328803c0305045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 921151915 1250 921150665 921150689
    0x50405100518271f15140102031b241e041104090f120f110604150f020c0303010b04051908030a0305070c05060f01030b070318080a0c080f0702100306 66
    0x241018100280a000c440e84004e02a8069149070251858084200c40d96412000603100481d5000102d0810456103d614404108003c240307a9a070040159005c592410502d038400c220402902e506140c3c2110000d41804900f19000e00100c002011241c800c141c0200c001810348280d0034130400d0324808450041682c0e005400000071404e141e00b00c5101288290002c2c00c4000c20fa5546821444030352179000005240c445001001991020000a1581440c4081c0015040940310a10026981100047c8084e211881d0b992541216812680a000d0000a4039120750b1182c0c03440989600921030f85200d0b40c244070010080c0f41c0e400c02001b0031074290b50011031038a180c40c4415405050b000f85004240444400160b02155040c404107208944910703c04009604500d8160202c0343e014001908040c81d100000c00d50910301c00c10703441c8140e0461f81c89511090081011a0504888400108883e40200707800024180346400b400000d842218220080032412004800300c1e44039100e40311a4602c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 921153165 1250 921151915 921151951
    0x14010c0f1d06162f040b060702010309140a03050408060a02041203080a0209060c03120a1b12060b040e0405010c0e0a051903020301050106020a0c09060e0601080a0204050405100518 79
    0x1d0b01c2d0000301118004128000103455003a150b100003c000c50511003002c1d101d291303500000034400f0741c00c1c16281c0000c680411031703900b18202080c0a4000c00f07000030306141d5504002c1040c0880d0001c4428800ca10300f04a4000030002e250041194210f4414494140300c1c180100b00c00d42c54030300a403015034085d41c41c4071004041c240c4045a50301d101525400b603680d400c00c9004140d0720740b00c0042580c15244c0c0002d5650b6410000200000000201122800b82c505080942c002c08100340e989019402c0e858580782079042c1c241c4510091000364082c1541880000303000500c42000d1002e688250b001d0300c0208242d030040b4005941c0e030100d0300b2000364844581c5006118034a0203070415810070103012401010540c6982c0800e086070790a03003110300544d0007210407408116400304d140000d0046040d082c08038601d800401008200c014040d6814040800b000802c680800d5040d80c00a1070010700c140504d0404801503040c2c4003680c080c40d401003910f1030000040a0003030307102c140a80e45585151102c58 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 921154415 1250 921153165 921153169
    0x3010e04051e010b03122d070c060e01020d0306150e060903102c0705010f030e1006090f0b0603040609020d06060f06110102180f010c05010f0b09160212090d14010c0f1d 74
    0x40d1f08000c4498420014091140800c03030011148015006a4680030303600010203001900d412004107a010415007440030900c4114103095500001d040c2c00d04040c00e0b03a8803810000341c110f000302203001e030300f620601303500c80001459034101110340c0302c6c19541480702409a050310002036241c4668080c0b1507100740400c120320f511a814440074040949030004003c11a400c84e03d061250807401c1440722512910180811106440b403850400d9550740100b204644bc0c00100b121800010005400c00e950b444015055458801d04003400951040e81080b405494400b081c0c04040e15004050000e1b020040400800d071051085511402c034698044034a042100c0030014141004030341c00d8100166920441c00250342405501c2c22500145400f184680502d014880c069a004048901c110070050020000c203401003580b004580356100310719a1090404003180140780080741c0103104066618180c2c80e29070041d800951213116640d928400258244011558a81001207984010b0745020038042e080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 921155665 1250 921154415 921154477
    0x906010f050d03170c090d1208060a03020f0907050f0705070608150f100201020d020a030911030d0c030305060a1a030601080612030f1b06040305180402040b03010e04051e010b0312 79
    0x404985d564151030b00c103400003c91004242c80070208c0c0c818006034120207800d07400805966104400b500c0c0503117500d15540014109541403c06903009268000119025620650844140c081510a00c640d0361303c4524240c0d0f41d460341e80c0f1844002601c100081149204001990400201c2c010040342202e072030502005a920035141001c800e41d9800c00c00d5070b029801d10b001500000e80300e80c030001561050b505084d90704819844165109030000008504590b8014805010f9140c041c50005055900d010210741b820000740c10826820030100c1c95801808078000095100790001e07652030141361904030502c09011680011403200ba0030610004503801c02e03e402401c070300440b50b02a0003c41a0900c0300605210341034400b0f5002503000250107088680011034521140c1056504500c0c03c0e1610020340b0f1980010701881d042030340c8900114082c02020004815140e410451b402c0400d007586000900034a42121003c3c0a4010303c114524201c9182086c0c0300e072034020b40c00000c0c0703410120050042c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 921156915 1250 921155665 921155671
    0x901030605061f2706021e010e0a0605040317010e011a16260405090a0f0f110316081b07031704080721020c06160b0906010f050d0317 59
    0x24168040403105145842030040440100ea02d4543c100244460452030164501303004002c4140e8403501080000e5002514420f02841e00720215001c17002605001e0251441c0401910184034905544040c8126640b220f0300540c4252280b040c908401c0180a001010911480183d8a6010300406c415102c2e01111120001441d820b2482c2c400c0d416112410140310403000e40320f1080c0c40c148000624085c5c0ca8649011045c1f03d140c504040c60030000529000e002131407034090685502000d01c540c0e50a810880100000d0340040c003600190108580031500200c915201440d070000300310341414000e1080600801144c58411054500e2a6000d881c035403282c035085041021050032900c40c8280c86070064056072058105655510850800300300b120f0f40440c94040d0b0400c46280321210580000b46207011590541d8825118600c103181d003034400d40b5800b00a0484d0840e1000c200d00c100340403503021306aa449002c0076002030b4885c2c0600810140d040320040c049415410440e502e10350562080e54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 921158165 1250 921156915 921156919
    0x30807050f0301350a020f0a091e060b0a020a02040b150d0b030d0e0f010c1104180b0c04030c0e131a040203011410030b1003140703030e01090302090103060506 70
    0x201e003400c82000151154402d90054109040c0184101c404400b0700100031240046804003c1c494010900b02076100d94101500900c101211640460651900400140102180441000b1041d400c80a010425203244420340c9100d14000300400c0001c02c210995105591640c01800500340076820b00004007100741a03503034008201c800b8a52084100c0c0e0090400344512540410b02d12034190078146480308259907001405030260341154192202c4003041307034104092178540d1000400f42000e40312000c440344041d030032609203401e0f00b030703160b0030007000c0c80006216000340d03071032542d4684c0d090351030740142d00004146021515040bc0002c0c00300403d20f40003084405280c801c1c10507a0b450014500803031400c0da890407a81020002580303030a101d06965260000d8100c0400d14144c00700980243c00c03400300800c00307140b040203d20440700790800c0d00042c5503c50780707440d4503c100180312699040980300440005201d800440190352103195081d0449174060550080d503403c3d0b680b004043e0400803c50382d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 921159415 1250 921158165 921158167
    0xf040225060905010222050904170304030e092e0e04020d06060915030b1003020f19030c06090e100305150c07020d12020c0409050a02011112041d07020c0d03080705 72
    0x40342e42071004052007900343e075406c0702109a03400180c048100796440b240c0b2403000601000003242ca68204a000410360341811640da6907645002d4030148243c00400e50013420140c01c1044800b040c940101c82c1c40428400030103034401d10403d0031000701060184a904001a10208006040803070300000440d00c101804900c154a074a150f0040343d480001c1603000c11510310040082c03000c44003809800c010034691121066003180c021030381c400003550030310380a226407100c604010240d2035801c1005d90382c000c1c05480c1c860b94402c0020041016400341004881c0d10714042402c8104202c410700807030754032034040c0c03070440640c181444411100811140800b1000c00143c00180d07140841c1d00c84003846415001084000c84000915010752401c0c41030086180982880c00b25a0000707208640c0d5609180015129408020aa081c0750700d10401080303584020501140c198991107402500f0300d1450b007001c580c0e130741e40c00c0100d80e100d025005c0580c0041c4440d00a001081c411800c061b8818800e0a1607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 921160665 1250 921159415 921159431
    0x3161401022a1e03071e050901180b03071404020f0d0e0f1605010509191508010e0606120730021309090c0b0918090a020f04022506 58
    0x81d521010a10700350052941d0702001101041c03a240100b0382c442650603a2060022140b0808255600c905e4040c204c0240c40030011001c207418840b50381c201400005d466000656503407165005041c2821500f021120305144060400341400200e04c2d003112508082c05134281c02c0001840000d62103000c0e480d04083d42001a141c000741107004000806001d1001880a0340c55132604900b40030180074240412003403080104050380e408410b03100082400c40d82101d071102c2c09484002941003961042e05915134007040c00743e8490700030b00c50350b0489285103c0c06c04142d40c0c000030005a44100e541ea00d00d610350b07850204000c81d00c02d0941c102e070041c103c0d042041c03060601c80d0002d821442d64101107082a00001c0c1601c1d00c1c60784802500041c105008140f0a4102c5a07842d1a408a118014242400c401040140040e950190700b400110050081e16009042847d00300b074031418089400d81c01005030f8400051941044e10803107030340325040c1414141c540045400a40322000d20403046c3c0c0c80715151103003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 921161915 1250 921160665 921160693
    0x909020103060905011d01090b030d1b0b011d0903030615030702010e0601090905070b040f12031205040f0308091b120c060a0504060216050a0605090d05010606030b030c0316140102 79
    0x1c4174041c1080200b8400c0d001038100d880441c188058003c007003028141901d0900c00e440011b00401c0e24541820048804811000490340d28000c210740905000b031010000600e40145a4580f21101d1402581100661740d0001c000c1c2d880c0710958140b50410301c43c50749101048000c9000d5600001544008138039210b107800c0c018503102d030a070442910203a48003070b504100305007004103d0042010400c800c0c1072924002022240d6003c5204008000c2030f55030b44641014415001c8500003196910100041c2c1041c0c14402c2c20030044410403030105a614001c1040c282c40020719410b5038022941e0724400045450a0006890100515031803a126003000e1541e40d95819001e003400d101c1503900e840d01c45140c000000d142c106030016081c1c907052401014000f0f80c4880d4401001d84000f0309040b565451204007040c00115801400780c06546003c82c0801d2040d07264020031465401242100e03041c107135030001c044c1c4964100550a55540c041e04041010501080b00e40002c002c050054503130446070b01c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 921163165 1250 921161915 921161921
    0x509030c030114091006120b190504061a040504170a0c05060411010f05071a0601050412380a1109060a080f18030a030b060904020f0306120606060409090201030609 72
    0x203080e0f11090300c1c01c010408098800c1250405401007a0320601c5540d10f044608094150500380c00740c0410380c1c10000404a603e00b04500c0342c0b201c8256010811842c3c1030500750000d202803001c1d20f1000c40000b407180030781d203064000d00c2c0c0115048a01c80740b03901c8602c0c2c0d040300b0a1707010042540c01c1c0300c1c4070825800401c00502009104502440c5040d2100c5001000182004142d14240080c040c041c00144c003c540041840800740c408070701001c1c4207072642c80068480c0c5c041d940c40103002c09002c0800c2410804412480e094112030b4207100c1003002c48950174090b40d0b4501000100c07240c0d8030480081c0700b210864120310000c50115030b80906d810f000c8404603055920803401072012400d40010300071070340080501306920007030800c3c4203c1c4c0741c03400e0240c1640340d101c2c1e500c2034010180c4600e03d1181942d00c400c1221086074009200715a107030f4a41e001451103400440c6c4042c416003405003a0300001c0c2010495a114100c010401840d20781003c900030014060321000303a04041da20b11001c40c18000900c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 921164415 1250 921163165 921163181
    0x3060d110a0f030b0108010212041e17070b0a05070210050c09041104140607030914010909060602010e0601151418030304030c091a010e0f1201050a06170601150509030c0301 76
    0x141c0e61842e181103003406803a202060784480610780c0704218001c041e1107a0302020b504240c0c00814008008000f160400030b100c40851701502d0845040d11000b00e440e4508020041d451040203810b807a60b03200e10500c2c0c01c41e0300848050001da000031003281183d10003503010f268810300350464141007501d95000b140454082c01e0569014240000d0140030282c0b1140c0c02a00a050440d6043e107411000d603001413900740c480c4103048032440104026581a8011481e00c0d002e00056001044680ea4031800280600000703003050342140206400071031078992406408085014548030481002d1300f902d0f6010050340034203810b80704c100280d0481d5110766070900c010001140a528144403050620000c3c608403848122100040038460f0b0301c051140c1d0704a00c403400050310488809950410074008a000c003102d24600041e40e5180004004c80c940280c1d0044041d43d125411103070030a40c03900c0d40e440c5c5c1c4502c28011030070544144030b987c00940703104800600c04080068269000303c3c0d00c0001290a4a08030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 921165665 1250 921164415 921164429
    0x180f0507021509060c0702060c0a0b090d201c02070f030b0f0703050f0402040c0201090501150314342312030405010c110301020c070e1902030c03060d110a 68
    0x308140442d010b0450048a8020f000311002d41220b041840c00781c00d01d84941e9000900615001c03401d00d1008078140840503816800c4004a4041d01c0c02c0508191100170f40c6000c00003181c42d0002043d0340802d50f8202c00242d0303810320020146000c2e5400103042641b03501403040218400c800c000701d460f0202044d4000150310550400440b1700f4034004007080b1a6000b4649400c061800d03040001c0728007030340c50494000341c069a00143c4544aa0310890140070034042c05001e560a210014644088004050301101c0c02806410826961100e4450f02c4002501101c04207003c49200306800704000350181400076120007041c99815505c1e24044d91440440c64441900b0300c138040c40200034100741c130903640313100301c00c030301943c40c081c1048000707048013440d45805400c4503110001084983c41c25030465680c0000704080b00c4015655095880c4041c00c110f0765802c418105c804080c0070859603009403806810300e002c6280c11a91b42d8401d2100084680d07400359800040c41701003060030349030b8203c00b002504507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 921166915 1250 921165665 921165673
    0xb070b1513060602010c110c2b0f05010c0201020a2c0a080303150a1503150306020f0307020c0f090705090d08030a0c1407022409040c050c1c09180f050702 68
    0x1d481c1004e400c4500c442808428400151000b5034804804510a5883c280c1283c14242e00e102d01070315060012002520701a410f0451600c0b1001c0c41011030006c00d00510402c001c2c04041407d00089080c1d003e180f0910000c25031b9503850158894460850504074101513947c1c1c04803024030b0000031500c051036401a400f5400020500210300001103001041080c1a200d000c101481c0c00168410040e0b101510800c16a8540021384404003030680ca10045420640564075025010b2844416510a807007410252003046600000c80c20582c81c0141d070702c0002041c01c2450b13a140b103015600e941c043c00700300f5032058010b0003610000e040c500145008403806103000650249500380074003121100445c094500105010910069a5650700c004100200c4414104010b1600c3c0c1c1c4060940070b00b1108580c000d041401001d0100d5100028046040b44501110808010200c40801c40c440004003040010b54188043c411001c07401344151905a500e84002080340c06c6908003400c071070050f1441401070308 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 921168165 1250 921166915 921166919
    0x80d0b0316090b030c01080a1806060801050603070f030b010b0a0c020d14120403080906370813030c1205041a030403022127190312090b070b151306 65
    0x1c180708950000f03005a004010041254001a01c04038004004000150b211400000422840c000e07074844258080c4003070001e07503200d0144c1c50107858111007030390203407080f4800040d640c0c484030341c0b882c120385e0000010011079081c0921580c0c558003510038001031080408501340161900d542130040c450054030000e21b50204040b1841c00e000e516040c00503080b40c140320038030225010f5000c40d510f1344002c0b41c18550b2145200900c9180748401c100c4907030100c0d4a40301030b45000950503480d03c0c903c0b0540d51021590f40d200b68081140b030054080143c000380c8080d0840300003500e40900c0c03232103407150750801c42e0415564001c01c004401c0350280c1c0c001d001c04003009000070160100074603124110314400003101c0700c4004180800070701a40c81e18080035072030102481040c0c5201c0f03c0e500154a0060b00c100c0c42250317051740c00b2110424501c42216401c1100c01001172003840758140d40d0a564004114a192143c0382e250901895400380000d105060300c1180348005a807502006040a000d9213000b062040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 921169415 1250 921168165 921168179
    0x5120114010b0705060f09071703092d010804080c0d0903110f09040b0402220b0328021e030105070f11120d0504140304090e010e0712080d0b0316 64
    0x10040c0c0c4910b142980c1448180002500884c03070b1070f48884644410a140e560b90301e00c40e490401c49921000721354008030aa60034025000c4001c20b001c03c819205080c1d034141c401ca800f03101d9039950108949200ba40034020490358401d4400d2904140107806142c00c0601540341035041c40601d4140d5004201c2000c810800c05ca041e54558002080840d19601400e40c0c450114014600060004001e040186d0001c2c0c115a16002401c088204590080c020169154040c00091040d001c10390b20901c10310143c40d20b0741417501c01030402c00000c084030800d49113640c1d0900c0f400d605003109241c400d05032200903000940302441510702c00c217450381c2c0c0c100309040340c4980513104046a10b407101054200b008015800a45081151807600b12854009021713541d5090481c080d11030400d1a03061400006000581030352240c104c02e200c130f41000000c1002000e0038241e2903540b8040e1048460401140e901c403c08201154040c204800320314002142c080c02490009081c4844401e1803403142c10355403001e120103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 921170665 1250 921169415 921169451
    0x20f011e060905040c1503020f18010215071e110102030c030612010606080112021206071808030903060c0a350c16060b0a1a0304060e0307080a18051201 67
    0x1041440030800481c213142e1108004c11245004e01100e4541032426189841d1003641142e2740b01c2c1f603264000f522000d0343d044112254010502460043c481c501a050f02d200c40703081124018441e0b526044124211810906450a6000141800c1c0131419400b15100b0800780010752054541010150342c03841c0520411150003480015a4450b82c5084801d0000031340101c4100d05640303034240301100080c003910009580f080341c1210108580550024800042d40244840004803129203d600e42503440b95130b501e64a01840e10400d40c5a0700400200342c1c00e051340701c02881030341403626190406141003800700b2840f040024501e804070000c103014204800304220742c0354101491081c4213250644c200002c410f850304680c00036009555030741c031000301550765510200041807003a42c190001d48129050b030701c6c1900100c509550003401e2a02a280c3c2c400044110f515a035840940581494190481215280b00001c1c060001e002c0c0141c000c14242d990603460f0848485010001c03c19024078400d500e04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 921171915 1250 921170665 921170669
    0xb180a080f1e0709050c091903050d0806061b060a0b1c260a0f020d0804030c17090a0b0d0c0903030f18090207050a0c050109140f0d080a050c19021807020f011e06 71
    0x23040006520610020710049448183c40d030440c5021003441d01c404000407204d1007240201d40a00c1c00300030540960b01700104820307100303103034424040180f101040d05215020302a0310f080d080c070000320014100040c50b0044c0726130b80c04800c0c140052100b8050861903500350b00112a540c0401c1001090004840c0e0420404110030742d6442d1900503403e00e6a0050048001c0803030052031840000c0e58920002c01c013006607152020020414000640d40b0402c404080d40300c1309400b1012800c0528407071007580205d502c03108403a4035550b407031003126594900b1a0b00301650070180c035214002550014124010340060401d146c00380c8040d201666852a0103003001045030b2009040c02100030f030030028070400c404412842c00060b907980c00b00f50403110000ea807054001400400142001c0f031061601680300010b803844000010480d201801d0100103040081703401031000350721800409505803c0400d1042c080d80200c814011105041c50f5000123a0a403808400c08000c0403c102e030305205100d4581c081c980c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 921173165 1250 921171915 921171949
    0x120f1506180f0d2f030c090615071b0e09060c03010501030e010b03100b0907141903090f03030507270302060309070b180a080f1e0709050c09 62
    0x40750400002003954100c02014141d803140e10070400d821000e403200703084510a1a03001d003000301c0040400803200403c01c50015901e8000501309400e82c0c0340d04000440d0841c0d040010b04124159a1b00c00810021540c10052969851b01c00e0106000242c5401d41451550400c0c1d42d13088141400c01e003000301d00d41d800400c0814180c3c40381061201c500302e940e080b20305494081c0382c0030412000803201c882c094450280302c19018400e1a49445c80d1482980c0b1040f004081251400080d484c0c0343e40440300d40d0196a50313840c1c001010000c241440d072401d9090710b1011200e0502141c4907480d40c4072140348101c2050150042038a44041020301d80d4048031003000c2030710400c15025008605421282c1c40049804000d014920000c0821600f0004001401c028070050360425941d84118400c041a114982440d80c01590880004119980701184180760124403c00400305503500d074010600c01c1ca50080b400c110f40c029068007040b0b00744503000300c5101d080e08004a503030b01d80d0841c09200e8045d2000c14081d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 921174415 1250 921173165 921173167
    0xd0c050a1d0906060c070305060f090705090108070b18060a080702010608070605030103120e060403050102070c091e09080f0703020102041e050112051f1e050402040503030d11120f1506 81
    0x2071001d580345009070340c100d0310903a01c035901c2c0c008140c1c6540c030304112900094141c0c4508400c001051801d034190390301c038600800a48082c0b50707503441030099800c4203001c0c0c0b039401e4008003000d0048140c03a0340503145132080c1c2c018480ca0045d03d071000c15503e07440811120002402c070300400149076024080c00e4024158400105001450844000c04030701042c00020100901224010b41c00307031081c0400d5030444c01c01810256982da69103001c1c0e0003580301c0e1504540e108040c0c41e0000341c0c54654440c0d02040f55030455540d04070644500c0360001402d010500b1944001c060004601c000c88240103000c0080c4603800060f41c4508126140d4515111088241034006400f04180640e0f613000b484a0400c0410b50804101503c035070f0744241c03411413150100c1116484003600000c2c0040039104402e003480b04641a112800e45440a0100380d10640c01030640640c41007000000d028034a504c0203115824442144c1e007048002052020860800d8500000c02d08100c800c0c044110b507000ea041c1c00c0038034116070003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 921175665 1250 921174415 921174467
    0x10b040609180e06010608040605071b0f0201030f0c050d1811060c01090f0c0611010c092c09070806130b070c0f0b010b030703060b09031c050d0c050a 66
    0x40074110240504401e0702d011212003420742c03040c0d800080500508900780d852540c2c440c000100300403000c403002c0e1496401c14000ca00712a01480e00390b11048041031071964400c91503107500310a21540c803401c07030405640301c410381d06908151050200900242e55240d40c0c031200d07405c50f0b005031210b0040f5400700502e009800000280e11078403030035100f4801c0d541c2544903100000140d0050200050181804001078040c1040092200a40090700c40703d44a5074040031040614a00722131040402c440480c1e401b0405000c480380c40540741c140700b0b000c2140c800900300240080c0d82540b401b6100300c0780d50ba108000c2400081400d001c0703140e104480e590032990103011501d03040309894010340800b01b40a841020307502440b44081c00180e00c1034001030b01d4480340d60746950f4030180e54011503009002a141080200e400740c8243c0c02c84441100040040203e124045a03400492320102752100521404116402c21030519000350041c04071162201030301c3d40e5500101600707007820380c14503403080702030a058 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 921176915 1250 921175665 921175667
    0x803090a051f0e061201031a0702150414100f0c080912041503061d01030506070c0503271914040e101121010f06020d05030106050a0311041d010b0406 66
    0x101c00b4055820b03162080e400390003400852001d01c6607410380031201010343c3c004000d00080220754103c0201c000c1f05481580e0340c490080f030301c40c038040c0500c90440341d114000c44d0105100782c0020101d241002e00f03071081d0030203404064003111a0340e496915a10b40f5810a090002c6d00010055800640c00c00a030600000c4450700462610075030103079850628601c011211200d12961103040a85251001303140da05210300b900c040e410009120444075842003c0010f024588207202450601d54000c00560400a59001d48071a00d9084001c82d9038001d091000021540e4482c100f1014400e00209142d0391542040300c038600858142101c180964202104906c0b44078001520030400c412207040001c2520185540350518071403c0e804191244160f4407440d135221503031030351504a4400a0803001c1081c4c0e1103a0a903241c40050190001151040c4010082e441c0210010121407550b40350024440c9250700c060007a903002a0004054503050070720202d0001c210305100c03070240035140310769030429103480c034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 921178165 1250 921176915 921176959
    0x40c0908032b05010909020f0f01050d0e12040f080105061e13200921250b04150305060409020303030109090804030c030501200a0f0819060803090a05 66
    0x3034410046100c20b40001070a481d012107421580700120800c2c009541d44160b24400b40c000c102c02a440341c1c800790307004400d900d03100040f1030f1030400684400c1d082ca0b40524a0100500b011740880e0380f240035900204040c20200c0d00180090040d42020003407440c10464007600315400140a46c2c0241071041440c0d5210182c90306d0b2040b240740882d4140075000311644000c0c05401518000c40100800f000608602c404540203410954016600040d08548000781080040c60046907102a40c1144840b510151f90200d8107000102c02e00e01c0d503552841d0f40d0581740c00f09920607403100084181c080c1e03505604036418014a50003600071101030018446540000b030b140e1006100e80e00c00c65580714000f90400030b50740c0580d40219002010143c00300e0740c034201640a01064001d0441d80c104000d48140e0074499a02541d000702400c0e95001400602803000f5030350824003500001740d080fa5081e0021811a80d401030401074801080990345540002c020b021741c0486070f0308014800c030010f800309620490307402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 921179415 1250 921178165 921178177
    0x438031e0105180a030c15021c060614040f0b07050f03120105040b0f03070b09010224010603050c281b030c0201020f07030812130c06020106060e040608190206090a0e010302040c090803 81
    0x140703507c10b41d401115808024441c690b50040c40765000c00218030007410a6100740e0450750f00f610784403100406202231400f544107a004054258108890038045444118040c0c1100d5101c1c000b181e0000d41a4000c00707286401041080030f420700900014003560070240140280303040306485505040d0920710020b621100306006014a225011503401040d84c420040f000800d01107050b0b18550601b425542030706d01c0424062040424281004a0343d003d0608040f01d455044001c621041c03205219800034010001c032902800300301d409102c542c00b0030412401d489085101c1c2d02c400b8011441c9200280c01d0004140100a094004410820100c0c0309038044862030307108045448116a580c1d0305805611500600c00781c000c0c0b8400d000410f555070154080016500d45071601c0c000d481d4a0002c11040e1940e90248030f038079801c903481070f040c0c600891003019203080c40240380c9401d0030400008200c0c0310395503500c030400d01c094a400410a500341803080d0540c080851030207a0307000381041980740d80c1e44900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921180665 1250 921179415 921179423
    0x3100504080a0c2102063702030709030b09010c0f031506140f0c060a0b03070b0910030b040e0a1527030302070b13020438031e0105180a030c 62
    0x45101c41e4100982e4414901013441d00710307016400b9650400d0000d649030002c80e49504003100f0540b101a030780c0d85648003a40f100409400f1071481088488400010f5003010f4111028403000d82d00c04800141f84840e2203200d0110440002500e00039000c2c001c04100540380c800b024503160000c0c55003901700307100c0d01500780c80342d50401e4514089007610300b8080b84118080032201a0011031800320020010842d40d000705801e00e014403070010290105621601c8500c280c01d03200404000c40300c0c036811b00501c41e000100300341c10001651080f210215080e10207011840d802900104040420080320100020300072540000801448280580c0c0318035070180f8500d40005001141503100402d4402c2c0c04481c655544450090024101102110451900014100c0c8141e04000c2100350b90950000120302e55800c4100895242000520200210b045002200d4240c0610002d01040719008144030703503001071020000506217040090342c049200303e24100c45003a003080502c0b1001c2079124009900903a00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921181915 1250 921180665 921180677
    0xa0312030510230a05040c020708120903030414061e03190e1203090a0501060807030b180c12010b031c080c07080405010813020405070206060108100501020604061104030b0a0b03100504080a 83
    0x80b070005034600d04c2560241c0d60160500c2c502100b604c0e03011407441b013202c03214821210294503c42c04244a4002d1940494042c1e0080c0002c0207200107007070b25500c10041c017a110070700d402104c40032000428070f85800c40003204000020710142401c00712080c00060307051482000b11040070154603440d1011290000600c481c0880401e640b008207100b80310b990399020707000704180d0740d942201039240c04942c802510200002000100043c600b112841d0904140304081e20001c04400108060302444407070107800b6650b40c165400321a1000c201101a842044500550418612400408806006182c1c818080b003d00c02d03000021000c1080d03600762002403c084070345645040b540c58940040f43e001039441400d002c00d2090341500480c40c00c0c0110004e0740c84400175503c48004004070321803131084500590241000a000c10700c25400055100e000c40342580c6025a01d0f2a4a164000191600d6001035074070318040c1202d00c1c3c104010302c007400c101e8006114607e801d03115025940142c00d500c03014440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921183165 1250 921181915 921181979
    0x609061d04061d040215030c0304061e0f0f0c030209030703170f120f07180e0c0d060803040f120f060f0e0709090203100504050d18050a0312030510 65
    0x1407150032003809000581c3c5036004600d400340380c00b000c4000565003a80280c80e054240010303160807004030f0b0b200d402da0040207461078440780d40d13000041c00d00d81031125200e03110b568004050007036806426524a00d030300340410802020111581240d00144410081c1881040f803842240c90100d8a9422a60400d502d0f4825518140a0380b40d188940e140c40c82c8820b1000825003c03030b50764208501d0040075902c0d0089034640e0340c08001d6490200240341c140982c0c03d040002c0000307400b51030740107910542c081c00540c1000c9030b602c104000e642094000300c80c0b80c0c0001c1802e0045120080c0d2110080c000140c2c00c006080c0c05440307600d0b800c4036840000d001301e5200c0d08001808503003500701c40071a8083c030741160030b0603654040100c011f00328080100c0c0329018080c501c2c1a281203074007515000d245c018002d401351400c1401d09840d60035542c1a000c020b040c40a0303000525540d94071060b8011801414108000c2d000050001c00f218001070101c500c0720a0100107020f80c0300300d58007000b040000840c070511041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921184415 1250 921183165 921183169
    0x3070302070c06050711090103020a0b1b0613050d03050c0a080a24062007050d02030703060e1606030203070207090c050f0714010c0507050303150d02060309070303090609061d 77
    0x32103840c002402d05000028009501d940c042c00500fa030901030a2407900c0c08a40700c1c1002030342e400a00c0043c0d8441403c41c03050000c81894401425002c04140613404000c90b0340d8200307400e0036011202001008904800b85041c070005101d50032680140380340811035454a1480740b0a02d01400c0182c0d000c0103c54030000301402c101f6403007007203500d0341c103a80c01c140c16003038443c40d200030034480c0241000176680c124a01c0442102c1561004062840070182800a04007024800007904a2405990600c02c014000011a42d584520b01c00070750b000000c1c00d1195140c1102050b00c500c40d03030014081620402c10040402d501240441c10703140180c0c404030707940c184054111414000c0c2541045a20000603035141000b800c142c10b81c120000683c0280310040074407100b902e030380c00b4040019150f03030020800104548031048608180390001482c0b00011000384e000300e2880d42040301e411285901c020014001c0c95000142c4000030440c51410420890500b00018000200380d169000003c1f4000d03644900e42d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921185665 1250 921184415 921184417
    0x304150c0528020d05031e101d16030b03060402040f0b0d080304060506010e030c01081f0b030624160f0c03060b03070e0108120f0d020f0a03150302061b0a02101701080a03080c03070302 81
    0x2010302e000b44090795040107103907411219040c1c0d419200a0000c60310350012b030303020313025840348424002c0c060800d03603441c0e4080c00080c0960058801c0e0255403052440305503a1800e94001060f801020070310340b82d1505241c060700712500a403045040c05142c1072401129076001901d521010001e00c0d03c1c2c000d40d10350f11302420613102100070708000c031400440045003039050700020f10705c180703012151411034030040e5440c85000741c1c090f8100002c26100b08810401c15040390b4a0f40105481203c0c2071401d507509480e4080c03a08281d070402c80b500307901e443d00c004c0b85142c10172205024021081c00e41c507295141420296442c405003401c080c1c00034000c121807005843d0f00c401c0d503483c0722010500355520b070480b085140e410703844280c4110110746804c00c40c5401500c0d607401e690076240c1c003400e80340c42c1224904003001016903003012204503210700090000142c44040070745840601c1c6845882400d00c6080c021003017000140c00808055120190b60404682d01c000d05075040380c2211459596526032400460103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921186915 1250 921185665 921185669
    0x30209010c0501050a0b090a0c1e020304030b1009050f101a070f0b010510020319111024050f0d030c0302120301030804030c0504020304150c0528020d05031e10 70
    0x940d440d060805c001046541c01c1036003140001c8070301946a42d14040e4031400c171400d1901800011781e8402d00109035500c180025404c0600a004880c10302c2d17601e55504a200d40c08440e0400d11200d4440c0800c01e0550358001c3c2d64014400f400d43e006c56180c000281151303c181449080640c0045031110580040b00c0e000b00c036441c54105c41c0c624204900303070800c602070f1071081c442c03030703015140010345a070140f480841a108511210f00c0d4802850ba012807048501540300c140c0e10a213801012405010280240700c2e80317203c14a102c149115142e170701040c3c1010b001d56a804540518040074020103190384042503018000e605041959143c140703420201d150001c02c0c0c00c9011003120000c0044180280c3c4005042101c1c0700b0741c801c0c400151140c050100b07a0106441c0101040ca80c1c0b500310003648034503040035514184503e0703c0350900a51001c400e0b00704e00d0103100c40b075107003002c0235003909859070600503011b51400e14141a459130829148400a9000301c071800100a100380700840d240c40031000c0c2c2400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921188165 1250 921186915 921186923
    0x9081c020f0708120a030621050f16170c060a0804020901051203071401020c07241704061806020a0f02010e07080a0618140d0207090209090403030209010c 68
    0x510092000904190180910000507204100c00880c400d50009824015035421101901008010740d55450b55034101c50030000a01d525500049a0882c1e11105a0350043c0d4a8012001c0100320f810942d081c0301c0e00249160b540c0d0015007030250fa101251000e203088441095209140f101100c1c2d015081060400c505d40d0700c10400074a2808a0340c0c4a0035080c040c500844040740c069a03214100321b80790348252300e20714a0b90824000c1c4404221101509080180414000351908c0c8560440318104055030b08103040504040d0202e403860400d00e60302c841d1014090400050ba01c20010200076003c4005000070302d03190304c6081420440000b0140310035500d80c00b100c29503c5450384c20014001040c5003010400542c030744881344441041c001001000c84109501502c04070480d500e45401421015050100c441c03030a200b00b030000b4150000c80c2c42d0032207245001c1d1440314440d0704000e0602815500010010f4010300140e00c26603190f0102d00d07001a07150900584d00d2030346100680b6a144d04102c0a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921189415 1250 921188165 921188173
    0x60904090b04030905040c0905060a02070807120b09070e13110d0602040e1003023f0703030801080c0f01030c030902090907210b060d05030412121b1709010908 70
    0x401c1110300c40c400741c02540700e502c0d012142500d880030301c81280c12a00880c0c002a45100c0100610b0602000411070140035205a035881500d84d40d00134074200269000082c1c5e118800c4010061001e0640616045001e00c00a0101039142216404000e14064003400e40c190b40d041011040020700440210725080c0a0316006d29008942080b0b00250400e104503544240c00d000050264050300d800d034070035281c1c01032550842c0356140081006030295070b0110421449142c2500c0030310002c09080d00c0541c40144000e2405a00703500e4003c1c1180410380c030511071a8440c111000542d5600e103400d80010b2028600003811014205089002e054407800107504001e00c0301c11701c0051003000c1440c00680760100c280b20a181d5012401e0000101050000b038003c911801c0810300614008a803910514040c6040302d003000c0c0c4568000e082064a0041100e04020980002c2400c80d004086041c1540b41c2800b01740d000c0f881c039281d90f80070f040283d44581100d81d0000300305801743c0c041d81040d409040103030203c3d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921190665 1250 921189415 921189431
    0x50c01050906040c06170f2725120f06140a0f0515150c030c032122030f021608010608070e041e06090614041505010f14060904 56
    0x24070703159001950f0590b2044240440072a629000d80b009070410310381083c46072101e507100c01d10822014000b030612048071030700f112200d404802c1590510121004d4a0150070010313042c05401004410440c1c44d59101050b82c80100080780800c0c00708501540c011543c0e1620b15a03030324001009150380610b00642c3c0c0f64020034094507895a41c00255803248507003003045a600c0e224104001110642c0000c0d5000d141c100c40c611114a120340544107031030405044900300360f0204080740c1181c1060100c2a10000a030075440046940700108603009001c02100071b02400750300380c42c1c0703005261140c4040e05000401c103202034264420000025203150307080d03050b4040340d10b50000901809981c803d9203490702c04e0744004940713240500b00c040d00070341e840941d201896450000c2c0094442e1894026030b04c640d62061000c02045160245c80d0a4035a4500c81c9903075880c01d442c0c4007805d02e02803881200b00a01d01070042c410500b00c00800c03015100e5144d5201043c0c2d943c500000d025100b4151000d40050815000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921191915 1250 921190665 921190681
    0x190f060f05210a06020a03060e150a081204060e0f1c0c0f03082203080a110c0402031501080c041a07050d0e03100b030304120c150f0801060c020d02091603110702030c0f01050c0105 79
    0x1000c654031100326070030890bc581d103158003640d4015400007640c44003000c02040003c00e01030a2240c0d15420082c1119501592000014250344041c0c0740142400d80408480020031021008a4019001622800d0202411a203034250f8600440d01046079541c0d103600380004d4000c02c0c01c041c00003590700a280e25a20b110313030000201181f0100307161344c8040c405d401c01030005150500a403403042c2803100e4180344c075002920045603103000113004e00440b0001000b0108269000c5461903414240422041355035080500d07044c5d01d80180ca01843c0d081101c078120b4030415a03030205800c4001030709450013241075803054000a080d4070981d44030700c40c11800107500208002d4201c0c0b080045500e0a00440ca01100c24081034410900b1000320100040702d442c01400450300070f0801d07051213800039000100108040d0b002caa0040c205888602d2004840310000040070341c18016408103041c4a5120b506180302070740817a56405140301da561080c00300d11000082c030b0748030300262140d0b1141c1e50028403103410600e030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921193165 1250 921191915 921191941
    0x2070503090a03030f030e060f040b0718091a1804170d09050f0105060a060807034205150403020405090114040308070e1206190f060f05210a06020a03060e 68
    0x80d40c00200c2d00341401f01d414880e0100d0304602c11004800d90b01d6066460b50f549030205a401040d4006200031080c10381d4180c040420300c480038062100300010300110700090890303412405120389101d90881d00740d10810145890406400590042e5450011060b81000c0b200d02d02807070b10344c0300089252000900900c0b0300001c80325030001e03114000308450340b203000a00c604507006004800114200c10701140800744aa03021707400500080182400f409a040c5180b0050b42c0c500050901003190751141c00c04030900804080001d00c2c1c120785581709004180324841150080d444017070312940d9079800203554030b1003e40102e51009903488001600740340c14900645156000d070740340700001d54814444026801c02224880800031003400901403035407040300428111148220080742d00d80c6480e00d410340c0b5081405204080d0510418002000f820b0006220008a035036480d001180031b0b41c41c40030081000800c245090640010015903211808401900500055480881f180c40e1410030000c0d400b0300b00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921194415 1250 921193165 921193187
    0x303061815120c060a20032a0c130911240304020d0b0903070605010509060d2006040602011d01091a0403030213301e030314010803040501110a0b070302070503090a0303 74
    0x3000f401700c1d200341c1c3c1c00c07065a02d002d85603456002e008400112100e0b800e09101740030b4100006011109270b8104180415019404280100c0c0c0c480d07200c01c5264204050b941e80000b030900b059450b0b00c04d00194154082048035560b100c4070308a0710000c0400c00759180e007042022015004049030a180c206041c04c203607245d01020f0f06035070191400c8004a011b00c0d044d0101e50060f04010050300800c9400d4a89501e08400441c0003c0ba040c04c0706609542c2c1d807208005000148903580000941d91400043e50031140c1e00d14008111591400c940403000a001031399001030303204101c11560b11030740c2d00d140c190003d100340070144094403100f41c8000f600e0a5000d1710005809000712851041d0400841d40c2802d50071a00c000405103a83d400042c2e40740c40040707420741c00b118024130380030915254480b064800400207030441842c2d44c1002800b4429035800c0150107184e0340c0e900c80289801030345030b12400d80b003980160101c0201030300040c007102484006c106903042c144d001801d40078116902e207400b0740718500e58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921195665 1250 921194415 921194447
    0xd020d0c0e100806010504091805011b0f050408121b19170304200d0f0c1401180510030b030d02060708010b0a0c120903140303061815120c060a 63
    0x18000210450f2140c2e454602445040c2c541900301801c00e8040d078054254030800a200b8442141914080b078403d0180344140000440c0e070002d4092f00000007401807100d140c043c000c1c03040402041204107030004101501c2212400041d07204c1985100c6099840c00d400240c100c1441500c141503017113045e640c07003400158803441040c81e44446260440109020458005e416200a2441107241500c5d041c254040490010000c5120098a03900c00300d254015110560785844a000706010074ad010a264813003010090901a2909810b0f00c40000c1d20b5181b8011b85002d2180c924010b08214001d412000d0304480042c1950010403000d4002540c40e98201c0780100003400078800001e03c8080c06040740c00114160b5204650081c09450b028100a40a0b80d010308001c0500c50010200340c0c0b12280e03c1040e43d10701c1c0035695074105041003144c4034035050356041e040e030304050034032100c01c042d03420b011520141540c169502d0400102114204021841c0403500200009000346006500035072203c0e2104070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921196915 1250 921195665 921195679
    0xd0c1401092304110f090319020a060c02030a080c0d121107030305130b1305013b0a08040b0a1b02060a120f06120203060711120d020d0c0e 61
    0x8584011240400184500349180400d0140c1c0d495081d042d00c51841e18880191000c2109181146440c99603840300c6042100343c04041038505652400b4005a41002c500100300c40c0c90b0240781d0009003090b0694070402d0300344030701e5070241821900d007400202d10440d0440a1980c8803150707a80304c0340c0c0b10030030050080c00040740d9550500101d0402d12581718444003105e80c00d402c024683d43e0560081001600f600c2e50300c00f41425940005500f82d100c0b52007413100c1c80d03075203944081c9841e1071420740761040301c00e403c2d100004170074207248280480a03e148814034046030304030019504410707050030380120001d007910701e002a01041c0d41c14844020000c0702c0c042d070b607100c0801e5000311440341242c2c40309800940c480300800043c200c80b4410a904105212003030400950300004a000b881215140d0344140c011452505124081d4079042c003100764072a44038240021040200e04041d030700e5000443c07104030a4140440c4c075803414895581502d425080300700c01001200c00032103002d00345480c860399051181c0c0d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921198165 1250 921196915 921196949
    0x31b132715110901030e060f0109200a030e070f030b130311010f0e0d020109080406030504080408192901030b0702071e0305071a0d091a1f0801020901050f0a09050d0c 73
    0x91b000034040e2080d02c00314200010307a402e00000f00d01412503200c1660a41603580c90700394025140e07100502044102d920001221030500c5c0d001810700f6125807102068841086040011030464000aa8065400002190f0320320b074616041d11840c4007240241c110750f10305030001044110a80c00300d81072501c070308110f41e12403000040c12030907a82481e2006003040d10500007045a00d01a41180c1c2d002481111607a04103615405c105280c0011800110b000100301c0c4d4580051000148114498501042c0710003204401c2000412038a04107120003000080e10800159a451091140d00c001d4501201c0111020f46d10001035000c25082e0f010680c0c2c07a0242c00c40024a00c1d07003900401c1003080ca1508154249030740054040000c1c44200410340d00b0905031030600c0c3c180c1c0c1d16080c500d4481c0b1000d0b03400300c0740b111280405241c0303901c2c5a04603c48603841049284c030103a0300034042e41d00440019600c15580c01000070100d60b10a900e9102e2504a03214070542e0040000e801604000c3d550703200361001c0c03404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921199415 1250 921198165 921198191
    0xc0b042409020d060e03090d06020301091d0c01080402010504050d081c14010e04061b18061107031b080a120f0801030206030a1505031b13271511090103 67
    0x14441c1900254040d442c522060300050385508144400030000041d0307402c011521010a03035401d9a0441100c8155000006200842c3c06106003800303085807008010b9004c3c42c40c0050b582e80c0b16a9441141444200b8000404580c4294201c40141c48040c1450520b646d042c40c0404083c0c00c40038806104480544c0300a86210321803086040c1140541d02442003a480e2504807092040068800d0769090744866081100c03103003580b03507040d00c100c3c160790701d10001d00c00c1c2400703095001c00c81e04080104100c0302d0340b00140c190000b585000785c0750400c0a40301c0c014200c00030001119015070103000c15018499800050000c143e02c006a81d400365180c0c0b0203e84800c0404840c3e84909000080d48403006101107015000c995200b0a0a1b00d20652500c074403503100c0b0002440c25040e840c4060030010610f802403404c3c00c040d036104012920b655018095003520401d10140303002803003131004a01e14220304400501c503030812003280c60b45c1d640b58104404c0000300e01c16002a448a00e007240400c1c1419a018060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921200665 1250 921199415 921199421
    0xb0a0b09030613020a1503150f030209060a060906111606030b01111c03020315031b03011409060c09241236070b04120b0105010f0c0209070c0b0424 65
    0x440d0313005010512490409030044081c003480d400307100070141d4510713030940c5104180c501741c1d0141501001c0c0c910f806107540704100340040004c19050103914801d10800010350811500c1042e0307400e0b0304000820303000d00e0b60a14600b92075440c260446d00400170000510f45d80550015038007a90070303621800d14101c80000140d850018802d0198066000c207608245a840ba50103550041451981d0001c60b200b0070700007a03d40f190207102e4a81d818603407814404c580c6001d01c07520140c400c040e01141c1451800040044e10f803a0001e02084000070000b461149581d103ca081c00054241a01201c2099001b00d01d05080d41d0041c80552118002d0600400d8900101d0b600c0040b1401c040307a151881c0c9110160800c6540008407100a050720681e040880d418003c440a0320152580c108444c01c09902c50419140c07840040c5e01c070605005410700d00c1800d40780c2c810028250a41c06071900030182d02e540c1c50071601c501703480d0f1002d841c2c0940802400200541c0e0344100349034a82c1c01c008400c000110b0b1103c4011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921201915 1250 921200665 921200701
    0x90409080904111206150c150105040f0c021b0604080d030c0210020c0a110a26060604140703051f1401080703021c0e010b19081203060d030509040b0a0b090306 70
    0x704080180011511b107003036401c240700e076107048482c41e0400d607818208510f0400c003c0c030962042c1c1000d1005111030b08052041b500c03803080186d0f052120312003003107002e500c3d007e031409126499004541104245d484d1501241c00905c005003c80e580d0045400c40240241442c1c840d1000500407200d0744589103186001b603a40040c52100940342c0f681455507205005455580d00f00e400000e0100005008031500322449065820b4280140c195284603d0050400e94018040c911075460710b03000da40f420356030121440c1d0000381d034100003426407225648040c808250320041e01134803000c82c00219032210318080190610074280c07249019078440d01c2050b4240e0141003050012220301e455811441106034000404040c11040001600d040760408078664010b4407080000c41c007000d03101084117000c104007004c00390380001030250079800c000c1c0004940320f01c2d21002808002e0b000c6400710780f82d500c5910a03810b200c801042c10b5111b903550028034016400400465119000e09000212241c0b003950014031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921203165 1250 921201915 921201937
    0x90a05090417031e0c0a090b090315092b050724050429010605090411130b0301260a230d020619230712021813020702010f031109040908090411 63
    0x1c90301d0b04241523000e0f40d4119908031a414401d01100301e90b0034022503e414044e4812101809050b9154001d010b100d4600c168080c003a8641d503040d24017003030340c482d040c0c0700b4043d0b001045403001d9242d20100140902c1c40c921030415185030606200400000031000c00c5c0307003200002c074001484545809428451024420800440d00c200542c0641c1d1419500041e000c103544902d10b410a0a958150042c0380c15036008180c24440000050001a1440c04c9514031916841010011706484440d1035403110f1102c038006003c0d6040841c034081d4040125107594543c40e12004403004075010758402036503903038190703803807480d4400450a00042d50303002d014060740d840d24120190017420704580d0303458070b011004054404004402c40c040341c3d400f81900040080d8151b0b000380410320040b0600700040031500f4088143d4092041003d100180d821801e401c507400d1081c04c0c0040d080342d03cac4e01a52181c0c450b00064991192920002c04204001540a881110b0007660704201012035140108801d10400d40c1c104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921204415 1250 921203165 921203177
    0x106030f02031e0705070b010906170f0a02040f0b090a0b0f01022805010b060c01090b01050402040321030f0c0521090a0602031005210c0105090a05090417031e0c0a 72
    0xc1c03002d43c5070203c02d600452a4502149055020348038030780043e0081e040b05003202c1c0c0f81c01040050414801072a0000c0305860040d10454480031040c41da225907144009008503203c100c21003400503a0340c001405400040c100100c913280402d0340f800240440030101d807080005142d48049544005a140c003044003821200d0050340b100d00d81600c50701c11440c8202e5a40d921906041e040d0b80322803000c1d00b55000103000100341c12803e80b42014503d14160000d5028034030500080010800800f11200c0007849090544108041d0036030480c050302c000104080300c81e040071440c015071544000101303692203940b80c20002066020f049120142c5c03041c0e03110100f0f542f1030003014011650369402190405030901c85084103645d21804a908000788804980c59030a401c1c080c074145460a0040c0c0d81001c0c000d02e84285024801c0001494801f03450107568018494040000c08000c0d041d5200c51b41907940c20159030312031802e510101303520b082c0759142d44010710341c07000441d1202e052101660210141a2140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921205665 1250 921204415 921204451
    0xe160504050408190909050a0506060306010e03161d0a0b0312180907050304060e060103031d0406031406010510020a120804051504051c02070b0d180503040e0106030f0203 75
    0x400a040050401e541030f200801034104105070b0404941100021521040c0e00e0350720b03000f0035800700c0c0c20013407091584c541000104103540c1e56040850b23a020750309003418244001e0480201380340c0a10450403074107107a05a8000b09200525001c1b21544001d0040b68105960f5540004016201500c610700d425034440b0520f0303107203004000081c15480f0710b0340d01500407074103c000001d14a0b03041940e038240031507400401d11041c4009805480d015040040c001c01c00d55140d564018541035805441c0442400c00c51544141951990880b0004581041c2c071504506d0071000426244c50081c42910310880500000c022000d002041455402d81c000300b080c4014140b02c18256924900200201c0c1c0d80c1c09216884148000500300180c080c030f01034401054410780c2408119400c005001442c4250f5101c0701c1d04009900f01300c4225102c1806141d0081401180d8800d0440315a428100c002c2040c0008134010590100b0b254071141211965603080c01b200b04070003210710072840181c802c44058881c1d00c1c0710b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921206915 1250 921205665 921205669
    0x1081b060f030603101404060f0e0705010809030408070b0408060f040b040f021203070506060a0b040f0b09011103071a1806042004060306090c0509010e1504020d0509030d0e1605 78
    0x30710b0703010708060283c0b124a020814407204a46c071184e40c0f0a2500d4540d003d210134880184035003c03018520700010040d1224a00e40141d980f0450700c203850421810400142250506109443c0109982c1c41220071994840d20100101d4000e40151000c03441346c2d60001d440c040c0360030031f400c0c002c42d003100c10741e5030648907610ba040a090212900ba030308022402c5ea20310003810100018445540160050080c0c1d0030078804210110302c041d40f14410345502070200f4001e1000d10355034401140c1c2d440d5500c035610740703c410068500252580e1a040c4034040400c1e05020f001ca041060700042c0041c40a50000c0d90318071400700c1c4100000a01c4060603401100058005001044004100c03014440128004071003a400203007521034a40013250742c0c1e03840704020800c00c82080203050280070115005605981081c2d0b0500103100002c001020514815801142c0e43d22a90304031008008000e03424055480c11822003a525440140c00300100c030f00e0481d040345c6880c0040346000345840035070f000b40c40280c60842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921208165 1250 921206915 921206917
    0x8100306090303271406310c0f140109060c0b0a0b04050a0906050112030e15070b0106030501060e240715060f080d0c0c03020d0f150501081b060f 64
    0x380c100c083c15034038543c2c11a5800c848149000c0900c00316500b10031404240781500c0d9041040e4074028a5502c68014030607001d0150326000c040001c0007150740a0003407210007103402c4412506000c0c00e8070342c3d0402c020440000001074241600c0b9840350030380b88007500c8001107941c1150b5105030000076100143c59030006c3d017004c8030150881e07800800495000e4a85000408948095600d85a0541d65204203803c20180380207032130041800920403880d0050741d0f10b0141070402d0501c202ca03c6040280c150240d01e409090076500d945400c00c000000075038560f00e010300104000e01501010901020f034002c120326103004080480f01004040b42130358110b0b012203801680229100f120100700703c01540043e140720380300e1080209a400301d824445c519240c000740c140001d80704030b401040075860010005c140c4400001046a81c150340c025800174650411114000e86000b00414a06403415013040070712244d080641600d60303000548030f0300640441c1d00072a80d16035003110340d000101440f0b000d0780042500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921209415 1250 921208165 921208181
    0x1090510180b0901030c2109030912030c0605330406050631080d050706020906190f11060f04140f01051e040209060904032705040c08100306 62
    0x104080c1541107a9006020000c0c40a0704407034540680411011800e40e4075000d04448201d050800000d41c1408003080820300480c60545004280c0303c55841003018416500070b0010403030800e02107181714240c40d00410244c1c0b00c2d081511200c5c1040c1c082003401120f4005410b8011141d40d0680301400c200003075010b9000c0d9011400e501a42d0340400003010b40305c400c0205500400c048050031500280c442c00561184c03410750010b917081c0303071030018056003400041004201040d410700c41d0f12079540f0715017030020344101008940c0210002c40e00780c500c0700c2c0c1000901401c01c1113485188809101540450b01003e40c0611142141e001501090078901c0c48404103402c42d01841c03c4107584101400003c1c607080c6240404003040e0354520401154840317040d500c01942500c1621020141041d40002c3c00c5c0304070141c40a441a1700708004501050b006806940c1008080b4500c411240c612351100c01007107030719110740c501450606146404891042580d607115102490b1240d1210741141c50b4440103200b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921210665 1250 921209415 921209417
    0x14010f09120c090e12070822030b060102060a02090a05041e0c110f011e0c230702040b0f09011208040e0c0a020f01150b07150606080412020c01090510 66
    0x9030350085140c8010300d0a00d0001c5002e005000521854503001e002102c400102c180e11300d8201c0346108850780c0d0280b080f0383c0c0c40c58000224584410450f11031098080044a01d03403200741e8286070020400c1b036880b203031512a0100760241d81c119a20b900081069103e1390700c019502ca00c281c40c0900403880e05601400f0381420b07090802703d0b10340609030b120301210b00b0b80c143d03540400c07400c0b107600e850664200100d4a8400d0178400a01445008840191150411031b0b100c05003542c17145841076403180306807240350b00d015620314202c040b030410060880c0769900c0240103a000d541002c1c142031141c00e0182c403642c01c500b000b4215503996841e0014140e000e85d02c4141c1120482010000002d9030403626500c180502c0d100101c1c682c2c0e401d500311010f4500b000078116040e440c3d051808860a0880140700c0c44204c5920150540d550102c0f4581120640c04603040070006511344400491007a601402c80340c410f501c99036011080d4804040180c0e40d6840c8128107e0004054240a000900300f0340e802d465603040c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921211915 1250 921210665 921210677
    0x60b0d0906021b070503060714040e15100e2b03050c100923061005040c0315030f030e03030301230609122b080136091101080114010f 59
    0x3542c3c1c0307500d04600c544016012648451400d2016140c284107040e04024581040c1a2409440d02031103400d0040d44501140c0116503000502d071f8400c8040585600c1780000c0c00321810a844035000384c51102d00c40c00544c0500c81c0030040d58840440c0e000c2e40306140640140341715800065a0307040714558011621104c8500a00e08d080b6a880d0f2140666a503c82c4541051101c6120800450070030202011009031560b00c1802484030340b840743c5010a003503d4003501c01045945014500703802821003003200c10038207960124000203004040c088501d003c0e21036540e040580ba004010545c0d02d000070b00070040688003848803203070740015031074150703114041c00f500b51401c010040d4001808490304c0d00840c0080c0d000b01c0b000c00c00c201040540c2017000c40c0961411003880044803002001e1040c14001d9184800111251a440c024001121751030b104182a20595049006c2c106001404100b45d040354402c8201180000540c020f5050f075060f40c80e0420201ca149034088011690102d08101c401c041c040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921213165 1250 921211915 921211927
    0xa030207050d2906101b20031b030709060501080a23160206060102010c210f020f07060c08010608040615051512090601080a0b070306050415030203060a060b0d090602 73
    0xf0f08544030f40340c0d100050051030035242900502c50610b2a000410b820454148808440d0342402401c2c404c0c1c41c3e4211500303500c152030b021108901d100c00e034005039034035110300000003d116042c01c2e060f030b46e9002c0940655090b5551290b0712803d4640500501e80410078030800101c0da00c81c15844030580c108032040c0c404141c180044450101002038451ba10405601060604055010000d203a000070f028802005980ca000348020b00040b5060789801c091400004410031080700c035001301020745c0040500315036070341c0c0e882c610310740a5110004c1110500e04000900c614203002c1c1c004d290490354036854a51460ba5248d07a4800200401c054981c3e2810491601040c0b0351560400c402c0440c080e2200305603942d1002c00001565000284280d00580c01072005124510001c5050b060503a80652500c50742c1d00c918205501610b1981c0106030800e29103520901c1e04481405180101ca00a805031303441916803654210994840e070080e0754500004100c17883c0c4149a603845109035900410006090407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921214415 1250 921213165 921213203
    0x307031104090b010f0c05062701140412090807090207080d06180f060f0605130e041208011e030314041a03063604170c010c020f0a030207050d 63
    0x60042c0d0005010b0315940c0c01900340030f58200d00017010540c0d0500304200c50b2081c4d60303280c0d0745c1d5510090020002818080d01220a54020350384c10141041c404000d100c03514044010103400783c0304442c01c0d1840c000303000140c41c405000781400000e0b03070900710180c00e07503074100880750010754480c2030110303004207041007040c0303208680d40304400241003082c914803800030466103c43c0550703614034421080780e4640441008100354a00111084600c0303800c24030386034402018500e000078003035070247c04400801800c20040010071b4403c1120040303191241c0b041641c031406880c80901056601c590350007680f210900c046030060318058582d04080c1d481c2883d160326410881281540c0c480d0001c03003c403011013072080500d4154074040512600200020825442101c201c3d2440318800c1c1801700803100c2c4000c1002d020845400754407203c05d01e07401568441500c403007240241078442e071540060003402869211503201080300d1110b10340580c0107182c00e42c20001000280300b0080c0c0d00b03c03002100804019804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921215665 1250 921214415 921214417
    0x403020714060c160905070e0a050f0a0308030106110d1b030804061e061a0720030a0609151401080a08030901062d0b040303141b030f0903120901080c03070311 70
    0xa0000c440c00a0817031030110b04009450000d4942c009100c6100b080309076903218203540d64105c5004032040c050fa6074a01000c07480c2c0c1201a04081c08602c0004004540300707400940324064060544200e07038000006210480c0c50340d2601030108030b903226103240381000c80d2040b031449800902a1500281c0383c6540030801101d150000104c1c0480c64554004000101d174000d81c080708402c219403810b00d8104180d96030944201e00404000007940401d015203080c1d1820015070300401d620020402c02030040d0700b800040f140941d613071103103124200a0071030407602c0b07001c003158100c45604006000d4090709035076840103074000404400b135542d62810006002e80c428400c1c3d00d90180e1038a003280d050214030704036207086c1c00c00390070078400f00c4420401007001a5000344611010b51500400b03a44481242d40160940108050014000d104c04900c62510031442001881180401c504071040000390b00300c2400750b80680f0706c90a0100703d0078000070381101d00d4000207540c0181d09180000340101d41c2490744c065 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921216915 1250 921215665 921215683
    0x616060e0609010b011b030e0904050a080307121d061b090d0f12180504180f110a050909120306180108010207060c031a01030b0102030d05010e0702070605030403020714060c 76
    0xd030345440484c8602d507045501c001c3c0350342d400701c4c041c00c1003c0d003500c01034001030808146030b0007801c809000078203005007800f400e138501d03512584481d40c0742070200c001000e4052045043c41e50320314081c00c107140d4240395000300840d125050040c01855035445070007150b40d51503080c884c00c0300c28100b220f5882640c1750443c9484841c03040458100400076400e01d071441c0103031a07032003c043c03104100400440c0340c000f591103030458004030340102e003400c0c0024800c80b0a1810940081642409880603403c10030140f882400b40082a03a480b0540c9070780d0f00030000404020361788280d0035003002740b5481050498000465004c0d80107410b08410012101d01e6002c406000d9010f0074040e58041655810400030340a400f04021062506000003486078866158140c60024160b060560381c8000755502d90091003076030200050103d003041550381d01c039401081100c0845400b030040c0104040418103901540a80780600d8041d8010817030750741008441240d46180030032052f403100d070501a421481c0800c00942e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921218165 1250 921216915 921216931
    0x110c0603193204030c081b010c0309030e0d030503010506090f030703571703070203062a030a020d1802120f0d0302090607050706110d0c020616060e06 66
    0x1800101c4112482d01c041103011540310020310038040c4004240d200c9498481c450704103500715544c1001c40007941c0c0c0415803882d085029400d0512940c8807030303010303805003440c94060303104c0f0300c0040510420002c3d034020881008003c11000d10060141e0b04003400034000c050000340026030000344132000249000c0c0c681e07104035040a070400c40d5036140a08580340b51200351210352021072802401c0400c020800130b2120f08108582c5540c20303e00090f00400f248001071042c8990108881411200644c495004080581c040e106d1080850410384024810701c2c100780c03490348440c0d0001188400d0480360b0340080c1c20a0700c01a02442006070501c51031107441d0b00c8002640c224140319900744107008104c000070040e0649900702e040078628400b0b011030103011204540c5001640c411013900040ca0070f0182082c090254421000c01084040c0c015105060000714427084070b41e43e44e081c2c5401c03100d4079074080000307400c070324180b003091310a2070f42e13070100c0c44400d1158801042e120008610207150000c122826a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921219415 1250 921218165 921218201
    0xd0f0603060627060b0409090c05040c0c0c1a031602010209040501120203010c02010608060c09030715020f071406040315090615060912112b05160501110c060319 71
    0x21076418003c41105070440407011041c450070349003902006407402980b04004a0940701d500305c0c2c0c2000705101801c0003400c001031040090005c1d4440080400c1d2101c0c1d01146c000c07103c41e8012034040c141190705500060614009031959481d5a11700d0b07a02111280743c1d106641d0244003a07042543c40d4000d50f030191103001418103880d60b213801018251010031005006691507c10240015980402c0f4940d104020341804d1360781e502d03444c0c042844d0001e207600000d02c40761222100d20743c265005c02d2048081101c1f0040f500090f8450400e91403032402440140d0348004200b0040000804000c0e50302400c000e02e04000a401c2d4040d2130f110180d600c00b4502c90301041040e1381c20700900781c0299401000c3e00c8041d02403100c03003481d50f484604035a580c1407524820014480380c81d01400310000400c0f0303505129044014110064a0015a219080d0860340e15048503048045219403180018441200d031810050210503407000c28041030b64000f500d40e81e901e50305c5803940e0050002d54000c2145140b1400925 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921220665 1250 921219415 921219449
    0x507080624010806010206011413060b03100806090703121407060f0e0a0b0114040e0d020c0307050f061c02041208070b070809030a0e010c022d0102030a050d0f06030606 74
    0x580700c1c0101280074941440344110038030031a42d03400900b080c15135410f1000c018161603503a0010340c5541d28901019105804c03e100414089146401703140218440034040600d151039603c0541c072060100d4103d0f41d103910160003000824aa40b100382e41c0780709181081104080c0554012030150320441081d02c03a40d48030251691b11201500c01e250140c803601003c0c140c5100a40d80f003d00c2c41c101031280c40c1c0c83c003000c00d050035000c0d51550710010840003c9400c8415981c80124007035121894440414442c0c040d4031800501410b06040a0017081d00c003d100718a480b00d528150161940303015a0a03020035800c0c04080b882c080d0002504481c94002c04000d5240c0b04a850681c01201c0c1c001d00b1241040580003d21000302000416155054040d0610303200c00031940004840c200c003131450282d4000524008003101c2d5840c05142c4c80f1864880e8000e4520205a9006a07906d01c100900c82001800410140b4903441003a03100c0c0c2c4600343d410710003140c955500d0311640d05031141d03078019918040201e0030b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921221915 1250 921220665 921220711
    0xc0321130e0f1005030d0507140102070c17030f070605040615170106080118120e042306041a15130605090306220308060103021201030b06100e091305070806 69
    0x20040e48407200107100c2c602c082c04c1402107500c030413a480d410b209006020400e101008030201040c0c6001c2c41d908002c540302d183c0ea041c1424100d03820311544040c46603800341c0c1500d000010003207481c1e003104540740b107141c600c55540700401044018419510f156580d0748481040705007082d000d001b0712140460b003145401000f040c03421180340d94004140c030780c54500c0c0c4404822540c0c0350481c0f0150000110062401c03401070581d008280b0211595000c0d18000b0690b0031117000001002400f004078240c45002e0b40c0c1e01c030034402107521041420000d00900900c403021480c2c1440410480d0b074401d58030324180210b18100124108880d00f00703101081c0080f400c066982810000326a100d030080e00c4080e16480000103c00007010340d010040d0800a0795030024101e0390203901210a11031648001260643e03481c00c046d4001c0100b9500203202e04030151070840300504c1503604a003400402000c1c0d0b820f9440c1c050155280969014044503d030003a16400a0811401d1010034071803058004040e0521000c1c940c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921223021 1106 921221915 921221941
    0x3110105071206060203030f0a0e012702040b1915031b09061d03070b0a020f0a03030c02100c0813062d0506030c0321130e 54
    0x284116180d102e84404180901c100082000b2030300c0d0102242c07240b006407040303801030425101049540036507901854540303d5240000409102442110001c0c04090100c0c031030030b600d83e86e80c99065003020701550070107100440d01d200f01e5040c0b580680b20b424400c0e00640300c600038100e08011602c0d000c0e500c0b80c616004480980c0f4488111060001e10515081c083d8038000385560001d012130000b114607000c1c040300018050800ca5045c5070544100c5c0d0020000e040442c440c2d84060701c544c600078401c4504060003541c000c12004011040070b0301d08006076901040e038074a0000c1241e504d40c0c0c0080301c1504807084000b14510781c0b2007404c1c00d07009013002e948040000c2c0131140994421405010f141343e2110600c0300123119070380c1c405040548441900341d0720354054024402c56038290007000e400c1001e1001e181c01e5503040611411038080c0302d24098202c0800c07501544248100d0030032441d = true := by decide +kernel

theorem cover : BRFrame.Cov 921043165 921223021 := by
  have h0 := BRFrame.cov_init 921043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921043165 ≤ n) (h2 : n < 921223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
