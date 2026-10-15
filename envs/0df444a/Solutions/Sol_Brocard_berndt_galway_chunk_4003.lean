-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:12.92599+00:00
-- url     : https://prove2.me/submissions/d612308d-ba27-4a5d-87b7-dd097eb73620

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719784172 ≤ n < 719964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719785422 1250 719784172 719784187
    0xd020702100e0a120203100c021605010201021c0f06030b0f010e0c070b01141f051c05150105030405010209041b030c08070f0f051309140903070201120e010e1506030c010801030503 79
    0x444034107240e0140d925100b481014081d05245000b2540c40070f80369802b80199941c88030003011440e0720f54000906690040c000180340d6038052aa0040e1b00d4665500800c8901c0f901c00440c00801d01900302501c04103802080006005607c4a41c604881000c006010590750307203481c0711680d0207002e500400401010300100105644500082075aa030000e05000c00021119500340c541c003d244071107004144017040c5280724110600c0301e2040707201e0818003400b061501081c6103156500d00d03180e581c1440bc020000c00c0034400258166030805070040c00030000c40e50901e0500742c41d128201c81c4070300000d0030640c110102c11300c1091000e0261040c1e840d00d180742d00d8400000d0702d00035110002c90342005001d10442d00c283c0307415110400103050010780002c0600324904610244440103100e045a503000700500700040c4d03440b540c91009070062510000d90109500b007103d002d410030f007040d04c03d188034103c41c045449410303c11550044c50110200c500b110300120055810342e03006d1101801c40c0c0c1042c04140f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719786672 1250 719785422 719785439
    0xe070e06030d0c051906051603021c150306241d0c0309030705060408030604110a02101509051e1003110402070309050a0e1e33060d020702100e0a 64
    0x100b59500c01e400765002d04801713800f40000d44c8a1848103407406030b03c503c28004184004268202600b615241c1546015214943c0ea818601d00e40c60704a0107590701d0120040d9044403405032005582c1c0010144081d5000c1d10300c106800442c42c1190f440c0c0602d80100052036810b103014585520b00c042c510b5500e50740c8410f1100d10030f0700020000d03c07450000b0403032200003501c1446024400c80c03091440d591a42070403000d002c00c65018583c80b003000a010840382821540001d0b0000b84800c0c1d241e404602c10304005d50422203071307401e903002044980c03c000c240040c160703000d01c5c0ea11005941d03240298241d03540b5004140385407040e00c000b5010700a42c42140e81982015002415006c4c00703403d10500040e82c07600400d131103192642c08840c807a1142000d000c05134a1800d2201d010517158121648942004c07001202c1a800b01200d42c04d04103040718143e07101c0282c0d50200d040e200c05c01420540c856190403500006540452001c80c4a01003c4410000c1e01c2d0198410000b41080905505036050509264 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719787922 1250 719786672 719786687
    0x314150d030e04020f07200123160b0c3106030e07121406011d06040509070b0f0913180f060912110d080606030c0912030705010e070e06030d 62
    0x1c0b542054080008503c0a01c1e0200103003d01744c4074161a00402d034403a0b481804080145d02490304100307510091105851010705da2012140c0c02d03030a0b0b02d5550003581060042d00f80030210050480704a07a003004100c42008002c1c00700a2030000603e00c2001c1c2461065400121540540724055544c02090220b00d01c66841400c04ca00128110780b056074480707414140040108108481000c0e0089908403460800d101040c014944842c0b42c070312006890218403d8007400400481c02940d840000031004002003201d4070080604a014a0b83c03005d40c180030101702d03406162607500901c582da41070100440c007841041c08402e501d1106c6140c140295a88420361012003c040d00c0d01a1038071019408902c0d001100c0c80c0740115a1a0000c1102145080d1418003010001c51710a1246100030000c0c03e440d16012268018100401390f540c94040e80b0006d03541505021319024144804134464040040540c011701d02009110121600559030344241500036008481c00d1b60907800c0347d44545c4103503005016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719789172 1250 719787922 719787947
    0x301060f030b0d06051803030405030304170909161d150f0708030f0609090102120708060307031704030605090d09090b01091d070305060f1c020f0307060314150d03 72
    0x20007007a104056030015542c24101c0a0540311300c0e44c1c0d401030005144003180c1422900305068040c60440c94036884041c0caa0000500141c00b000c16420303c1041040c5280445503062001064400f05042440032030511444d5103c0c6000840c2002c001e8414461010605440c29100246646170f50100c030504c000040d00314400f4100e407000144810f0001072034500166200e10300e0499401c005213003910400004203406080b080301039104005042f000380381c1c00e81240c0c0c02090b03030522010544035600880d10301100c5900250195501c0c02d1440303c900c0c1c40300d00420480f4001d0100340142c0e11400340f0b143c2c4404e0245481c0f030105840c44001c1001100c2500080440b140c1410704010301c0c0c0e618113000c5a10a8000300010047d1351a508001c0c406806100e42a044030003918610300440341030300801c0e0004a8102e12980c005845500304d0210350340c81c030800e51002d40c0a0260ba4180d560380fa8060054020403074a102b0501b000030000318149a608039141c50f10400509902520300ca5480a0750141500392 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719790422 1250 719789172 719789177
    0x723030a170f0406050a14041211030c0d050102070203010b030f03030f0718090b01031a0f1306120503040608010602061303050c0a06150608010f270b03070e070e04060305030301060f 80
    0x31120282c0c0700501800c024000d5440741d03541c0e080708080c018800050614000d40400041c801804140155150204402d030701a10f0000030100e42c400180c0361041013070003194040c42c4032002508200064019080d001e10070b50083c4180030000382019201c0750803021505803075105100080e001d943d40070190750440040d08001546004540803004016aa9003040029039103e2460191075649442001c01302c3d0202006000c1c0760008100040f84284c40031401c900c10051101c1400c041442035212200070400d03440240200703d201d103802d41c1c0342c1d00b0610400c00880c1002000107855400420542d204070031103681e21118038000e0740d0a0300c1c0c9400500042a86d0301c40e101c642400100b292007502002e404200035107944074039140c3c005102c4001604071030384e8443d90407010031021110f6000f1404a18034039180e8a481a425110a801080c015030001d1f403510a55500080d030750390000a20340a840159201c0080e11280011310041c1d90007448001c4c420ba00810042008500c956429100c451031032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719791672 1250 719790422 719790427
    0x10e090f24180603061609150203210103050708150606031312020f0f0a12050702030a060203010902040e0a090506012106050a02031008070308040909060f050403020723030a17 77
    0x40031412010741003000030340d82154401480881d1030200117203540b02c0c600c003150820402d04280f00800c4e070a0303244180d42c982000105114600c500034425180030848042200d0b01d0400c803154803411a403820720080c1c81038080d42c01c01141100c00819101849490115648800c0e2203810a0150a80c001020280c1c10402080100c00107080301c01e1520f000c600740e5000780b010621103000b0f1401d04440d003d8950403a0700884e88030340042d00300311441c0c40040c004e051554070f90542c1d002113400d011804d400100302500c0000003244849040d07000d4000c1c0c4034240c490036815698900d07404103c61241101030115400940100702441201200460340c1c3c4a014030104809282d41e14402036072029204c10341d55517000300811110b00100c4145400400c4c1c40001814014550303181c400140c8036030b004444415848900341c900f0302045030010003032004660010406032505080081d02c5058900038503090140025544030308100a00c03039025400130050280001d80c4d0300355980c80c40708440307440040c04620103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719792922 1250 719791672 719791741
    0x60f1f150309120f1209170d021e070803150a090f020c0c060310180908070605040510020f0d020d0f020a170610050901050a1e02010b010e090f 63
    0x940c000c10001044503240864000301924148080700040510001000400b5828000503a4090030440c05503280150005040c00d075400c1800c018001100301c0224000001024143c00105034001c21810b0810700701407030352084140b16011941309500c0007410b000c03400d1012031a003200c00c18224020020052120303084503a220000340954071180c41c0303456100e81c0030400b090824414800701c101c07400c080301d29520b14940034126800c06e04040c0a0f142d00c8010003110414121140d030f2103018481c2d0010900da868038103a203400f002900c0300f15011038060159076501d410080c518000d450b03246200052041c2031200e00a04040203400501b040c1c0300340d5031944810032408a580c8028203810b03290740c5d510725030358007640c0514000c00005000e45002d078140c018403042d1940e101c016262040000d10340980c1e1401070b42c0381261241e404201c0c1801d6140e901c80d003400200d1301580b00c21080ca1003070301d403100f98401000801030707191070441d02d900007410203800140580e0b6400c201a0282d41d0442c018400c1c0902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719794172 1250 719792922 719792939
    0x110a050619063c03021302190804020f0f0d0602030108060403080c0a08150607051c121506030c0c1202070501080a3b1c030b0102060f1f 60
    0x3041c1c0d14503800d14500668407803850032a00078080544080d4102140c0064200101942040b000d01107100041143c0c0c1c0310180c01020311503020045400801d503e00e25820544480c009522a805100324040401c80e61490707540940f0f59144600e8004020140400313031441401411108400507a502c074400c08003010000d036044c406107000c0c107e0740c801044545407900e03002d40542c10140001000038400d00c414000e01e58800036080d0f204510320380f440340a1a01e400821010b00507444000d046008048507202c0a1860307079070712100c0101c99076039107082c441e4201109040303c1b4040c0c6030240c060241c0109000e0240660011209d1031800e1402032180c0d1441c0d11070803081c00c40e0005880050b001450100919a030010116400110307518081043c40d213416000c000301029030030318106078081c1c4c40a00181d100b0418100e920010381d20256410007404000030040018940d0080b000b00789081454000c0b9440028110303c903e10040ca804800d0b01c61101c7d500c0c0070103001c0c514a502072401c12000c5107144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719795422 1250 719794172 719794183
    0x111010e0105130209010803071509061803020c0405011d04061a030d180b040803030a09030203190206040521040b13050a0303020d03110f0d021308010c0816180501110a05 75
    0x700c6410410f412241d0910400c10003c2040c5c0c4001d0065109022060100e025428050103000e8050300016540d41585040b002825640c445860416881e100c090280f5802150b1002070b118201da003000740b40e03200c034110300003a0032248403034038050040c400060001d010b42c0d20400c803000703020302036000c141d006d14002032804014642c0080050305254003000302c4403185000c007029115281e410f074141428482515501e02000748041803058944000b42c1c1494020320440d664490200201c403114140402e020b540c4c1d07001594222103603c45c0300390000544104043c0564603d20901115160a10b4201c0d40b1400c3c4d0000454000c4205031500c00013001e0b61190a00d2000314400c0c0c010b0544a141c002015084400400589e1607244c41041901c18901d4814119a00302141603401611400c140030041000303800c3d50070502c519031a1a00d1005078070780001c20036100d00b0000100c159860038055089900700104449002c043c10700305414030003980120044204111000100c4510980603140d00e403408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719796672 1250 719795422 719795431
    0x70609230d09080307080711010e1201060f080c0a030b150603042001090f0504150f170f032502030321090114060a03060203090f01140a0b0d0c050111010e0105 70
    0x154051114180c1d000d401510100007850002d0140d0b040a03103540390345802d48600040144018054500050168000d50510708418000b1f050111042011182d007802080c0b030380183d100f0f81080c15000102080700007800c204200b000342c68008014030b59501c0703240f00e106c06032400b444020300b1070b09610740761100b002035842240201945036074540440403075410240076240c0d15041080e00b4200b448000c040c54452030407500300f43c8001510802054161fa013102041d0440f40042c03079040400143c0135070418401c1000c00c1040141c45668080702440340c0c0d030340720b55103101c03d1a8803284400c102100000a04013103090005d029a440e0070000503411310080031710a100c4070841000c1050060f80d002c244030356822000c00c858400c144d03050500024210041d50303c03008242c60b4000000840c02c050502068a280c400ca100a0001c03a01420080784400800c881c5002158600300001151749041848500500c1d0008001d0310b1840c00c0070011510418440c102c21025900c58440c800c0d064000d1241e284103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719797922 1250 719796672 719796743
    0xa0518101212080708060915040f020706090c05061312080d02031816230d0b0f0609100b0d0c201606030204150c060b04050c0904150b070609 62
    0x41c00108030020304010f0b00500074208004104c801c100e150348802506941140d0705401c0c0380b40760803445002801403e0340368001c0e1036031350004c240c403070401045410010205100d10701c2c0c0d11255890f0402d110050207406040d06004404880030001400c4054000400a00880d00c0341e00d4250400440c5003643d0054910030b41c040c558069480e2005030500c48420101d40c00d40404000611b444103c49030446040345181c41c00518185010751562010f49024110f40d0220a802c040e02d0014500c5044000c21603d843c010301020f400903030307040809241c1400303540806a15604cc014a084802c00034140f42d010308007032150030031515a0203090f01d5003000c8903140c14002054100c0702c5042d0008800b546502c50307400c1c9401840b00b03001c41c0103a43c40f1140e5541c6039281014101f8014244031001d40724101610303411034608003d00c041d2002945c02009280030503138040c4240c0c0c01074159400c400080e481044907841c0c05110701c000080150b001601c0c806c2c0560a1b50000040940040b0524921561101e10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719799172 1250 719797922 719797943
    0xc150c0c0301020a12051911040816050d03260c0d0e0606010903030c051c0801060e010215060d0c05040f27080307080c1b07060e0a05181012 62
    0x4054108111100030400254001d41c01c21000c0a0041c0c92100300d02c003207007441c03903d42001900031740d8190300190f0f41c0568a242072000503884811480541d020b03010ba10303120700030b0304072400f810010340d400c400c00c540014140744030018880c0c40464582c049020000d2145510510119a00d03600341d5506015081441810340d0703c000d6444d81c841162480604000103400c44800c001903030380c01900e10400c40b030f05420482642d00c19450454106100b068000e0801c800f030040c20300d440713503001c2c60960503100d040e21103000001c280740059039a0044070412148070314013640001e03c40c1c200b1560640d801445803500c2074115840f100000e094900040580c0d03643c0d59115005081040c066a00e000400307606044110346034601c0e1190b504030300c00248601d082c0120080400c1c9441014411200000380f03600340c80401500f0b44103190780300c10035403103401d000403140701d070112840c9004001d04044601c01442410748030707002101c18481c20b000404465100440d00b000140c00701414030304851862044c03101d500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719800422 1250 719799172 719799187
    0xf270b2802030c010606030b100e010c0c14131b030b030307080d020d182d0515010312020f0303040f0c0317040f0b03090a030c14250603051311030c15 66
    0x6013160a1030344110708040c20880c6501c1d03181c60f81d00100c9d054109924100d01c90b00d0020006940004190f03c009101c6003600a00040035804144000d66000046502903025507001c0100320036900100984030701c182c03240a0074000c00d8001d9001c0701c0c00d064058192420050240c5406500340c02026040540c140c001a14101691481c0710f007455542c000f00000d41c01c403400e07469007241d040c14082a880e440d40c00e05550a03007584980f408001c05d6a019007102d501c4901ca48001c149280700f0311084604019201c140c599107400805d50031a000f01d064015811030b0384035104c4000e4900c8460050b500d44114140200c003003002450806904050380610651300c52a141d0748860420362076000c882408030900600c04801d0010450b40a00c94040c64041803c1e000c90030401410f505074400303960144195040d0047d8082003400d03807000c030282044801c010555520007138050321400c8034049150490014000e000801500c1d01100000c0040c00311906141070101140c200c0c9501030000741e050502140c0c90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719801672 1250 719800422 719800447
    0x70f030b0f07020f070306020f07060207051515011b0204020c0706180605030f0a200d0c090801110f070501060801050a021210140f01030902100f270b280203 69
    0x40e81018241c070044c20310080e00d0741d41c5500c03041d071804002d22568000400003480e910314412394180d40d4225100b1556840c851400c1c1c0c0d900c0040d43d07150031304800d80c1c0d00001c0c4464509006800d04c200180c440841c441031007000c585540310180001c80e48194240452031070000200a0000540400e449101002e280400c00c61040d8071603611080030484208200003006201800d41e40d0014600d440202d494408603c40c0f41000415078000808480f004c2009202c250190300010f40714070305521002e800545481040c1c0c01d032a407507000c400410300b04100182403150300f02c00030b0400d90b024600001e0025202c40505094803002d83d02e004c81290045101d4910f403820030000c1e904810107030068035105207400c081075038410501100610460700004088800e9000e90080c1203004c0d8010005515003140007c045c1c409030510040d2000100003000711501c0d60100380c10b2603c1c074000025994080c500e0400030065035400040b10107850390902e4007400b1a10b00418444a001200d42c0145031581500c4650 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719802922 1250 719801672 719801701
    0x27060e060c070c0e0403050c10050126030f0c0f1b01110c010c080f07350301030f0209072105090c150909041a01030b040510022a070f030b 61
    0x50044041c01000403400083e40030346814200d660b02105040959928203043d207890080b0092104240162620720700c289020b41e015506840502c02410300c080348945418551001035074851140d81d1041000c20b05000710040982643c8040b581201d01203070100f442e0a0410b4030411801d039115112420410a56801031200142111850024001c180f94500000e1415130078840182c9818400100c8006015280e401c80d000c11b500020504000e4008221000400c410016230451fa0501540c40401c03020048084074101c981115217695942156000c0101c00040a0a01018060506007070920700700342410849102520403400503440c074010b54943d06250544c01158072030110105111210304c0d5510640c0d081c1107064074420004e40d10340c5030104854031001707429034031004103034000420000f40050580c070640c8214141c4000e034501050550990282d1200310010048080f401021096080314142c02e1900ba0300413600610358511001c0310024140d0000d4840065210800c5902c0c1c141e0401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719804172 1250 719802922 719802931
    0x10e10050402090f0a0608010606090312020a02090c09130603060207120207210c09051311060406170402030111030705091509031c030207021e040b04061827060e06 72
    0x405108030300e0242e00098034a0070007040032078420001000700d5110015603001601919403e0000c004040d250a0086c3c81ca091901c401c841d051600000e41d41030740e101140c2a1070180d805400701c030054803959005102900b1041d0203640212100d0000310300311700d2a0003030500440c0a0328006a458885060003405459403420580a55000280800c401c0841c2c0103480414540c0d000301c3c8440300414a8001500e1002d6480001040c1c02e003030510940e0000440c0c1900035910501a0f0b000c9401d44e54140103280c0a94890f01c0049503011300104440340403604a02d5001e8401000083c1c10032040c00701c980710b90000c2c2c6040d000280003007087c032a141000101c0700314031000701d1345107400c0410410001c0c0e5034800c001a01084051201304290307986000e40c040d94502507004288018202c060345000240c802c01c00320445c42242040b120041c43c0c00d052081c10151104000c52103020307204200c00c10050032400300c0c418181000007101e6003006e0804200c03809424401d14002c101c19404042c00c500e0494082e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719805422 1250 719804172 719804203
    0x1503030e040b010503061e0907020312010f0501090614120709050f010305060609040902030715020604110913022b050304061e0e0d0227061903022805060c010e 70
    0x42d5204030b0760703000003d8070780c095030403940b01d4580c1300081c5182c0a000c455200d0540c01003000740a100d070040e00480584100b001000d100c0c44142c1c3d03100b41c000800101485098080344a40c407050003568810b01117500305400045034203160030105010300881100490310f02c40080e202a006001c079240c004012400a00b003407038140000e041400014140f8030816035041d01c40c50340c130903611045403002d05c202d90081c0b552032244020f000c0d0794400651551000c84040326107401605813104246803041b4203a019070b004a41d001c1c10384241d036003405104c041012100103d005215600c400180201d080d20300061b10460182d500c6906d01840502070500d901c1007040c150091109212a0740c0c0d01c0909032a84007421181c4840c1c0c02c40c58004102107000b00c5070821181c1f0b80c07928002042c07407090000c1601401041e16840309402d4504113074500156a400020350201d40780940900c9510b221461415254000c140441c0c296901d0001503801e0f8015035100840341d44840f0300400c0190144031912200030030740c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719806672 1250 719805422 719805431
    0x40e030f1b0c0904050a020f0418030309081303030513060c021c02040b0904051e210c010b0a1502061b0304060f0f1802090a0204060f1d041503030e04 66
    0x1503881005a0148a0180710741814440c00840301460810441d86204400f070203100460916040240d1104683c000c1640104854101030400d400d26106c0d42040094040d0720305a8031105a8080f0301038100d030002a141480d05000801b80038040e006250000d6200f902c406a8915012502c615540065844001171245503070900c40580c551014403c0781d10408401c1c0d00f201c1d0000c0c40020000d008101c4215001000d010400042010001d030b599843e10003095a01c19a00389032441030350344e070f0902082c5007203d480c843e03120b50071030300d14009801d115401c07d0002c0b40b5607113031f00e0108406206070360114882464841040d103056405012070307a003103107034014801203408881000610911010300000c10140c0d950042601c804801d40c8000d103000d00c140750501001010419441c55030721a41d5080e071207443c1d010081207103c44680b0859044a81c0c4da1070349018003811030f03000d03207884c0601c004040c5410160010b0511690b51031182c5240c05150410240c090b0742903060003880d50844100e5140550f142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719807922 1250 719806672 719806687
    0x406094e1e050714150d090b0106030920010f4506031a06030a0f0908030a0c05030907051002160b1806090f1c0b0406020c060f0f04080306060f0d0b040e03 68
    0x3c4003517481c04c40031103000d056075603d0310b07498040041100c0c0c000076104640600000c20580d501d50800344c155030040c0342d8a14400b104010410079074441030442800306555080a85030310f8081c060018103002c480c1c001d1800710100e22050600d4141200d0204c1301d02c5c22a0390007a04074102003d40d08040d11a62408220074500c8100342c8542071900d80719a44150004400508200103981010060702000b000602c003c1d0824078001415410580361000c4150400f10440100351264066034486c80c5840000d00d501c0b4500010300269510000b410f504600030603540f4800390f50150030440081100151003507440281c864411400340c0180812807003141d04102c043d065545000120405003070032640514000d0280105804120706002c008100658480400c410b202d4181c4c042d140001c1c0c40c100303a072070039940d480c42800410070465103450843c1030f030000b0502007410a4040d640c005009451070b0300e003041103500c2c4e880940001010445040d02d40d6410241ca00b014040c541003003003044001e50030000c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719809172 1250 719807922 719807929
    0x200301110a090e040807031805030d0c140c1c080f0a0f0e0a080a120513030507080c090103050d080403030209040207110a05121209060f0406094e1e050714 68
    0x243c20b4091f0400c41c1048400e80f901c48020b010100504000b0100d4840202c0088058103100b030904047ea0a00a401d5001c24031000210b854003401000412031a10800d56030320050041d45244819a050f1a080c820f40070340201d0340004001d0351046440e2428107100c94400200764000041241d80203a016420422001100046107400a94819010f5440d071710300c040112182e0040084180149030b881d0800820b10401044050590b03024800b030300d400724110400d00c50862403c2c4070003003e236401380c5a04030b0403a109000310303508a813007841d0140c0b070b00c0f00a40c0010180c0c0c20201e4246c034503148280c6c2c0e1505a280c40100d02e002000181e48285903040703410201074070b030150000e0015480384009510561b03541c440040700c1400800f141616241c2d0f484250003007100d101c90081c098407101c1c0016412038002048a00d04541c00006488058050000d100010344412410090380d503140c101031003400614440c1810604290031358194024110034180a441d018465001010380c80550240751113984 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719810422 1250 719809172 719809177
    0x30f060b1b01052a0d11031e0f1b03040611040e070806030a0c090903170a02030907060c0804050609190306021e04121707061509060b0a0c200301110a090e0408 70
    0x411107900551145c40c1d288060001c2c0448600103d641040001084110410341018010000d222071106e80c4580d10400c9410415070265000c0000c0086094291580d9030303030400550b803091050f40f020078810703076144c1c0c0341c03540d5000740c2c21003036410f0040410401c203e40d0061000c0d40c0b0a40480080c00000e015456080401d0410b0154540d140c0e11031554009050241c862500c20104850345580c2914003030345090001d400c1580e000d015401000740024149115000e50108280c016605030711300341c541801c10415500400301d15411000030791940820180c145a04030046005480160356103609044001c0f8607020104c44011094050000740a00d012050901c181d81e64442c1102c2c0c00001320580907500e17402910001030900342400e203a5032484070710340e801800700c0b040700703d007804a261a0b0009131000d001d0032401b02d0005003402c001741c1c0400c2001100d00100805d0020b520340100040000c6070a45600501c0c202e0024000602c0c00305081e032010740d11005102d8100d20042a0615507516406032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719811672 1250 719810422 719810491
    0xf02011a06090109081509010c0504030503030a1d0f0a050c0a140909010902060714070e07170c0f070602070b0906040203100c02070e090a0309081c030f060b1b0105 72
    0x3068003080b2945541d00510003100901a06003c486501d4200c544c6040c03008401c42d00d181c90365003441c03a5044803500034400e9400f520b50000185055607111000d000040204003810340860813080008400745c80b0601000100c3e03910700e000750142180500700f840c9800c442d4100300340036505448041004900c0c0c201e40f150320603c109c50304882c603181c0c0740c03c050250030b80c41001b9500000c0082c0f03240030400c004120f074800202d07203402d41e1005652002c0c00700c04100c0848a1401040c80e0720306100f404154030320015403090481180c28100072042038031004540041d05d04540310b9500144d6041802910240e40b6403200018004000e20314190380400e40700e25500340041d0000b5111091912024000c0c4000f4000d00890740700e42c4410725040c1c40a60b61507103160070070340101c0d003215008546040b0118280e0996111510741028440088900720003c11440b42c0c080229a55000f000c50061f07440e0b80205400c1d0318641d500b504e02c1420308102821144054409019042c911070b104142d10401400880c25 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719812922 1250 719811672 719811679
    0x60604050a060c081b0d0206160e042406200a05190c03080a03020301091506020c0f031002040f08150910020705010b0d140d080603070302120f010218010f02011a 71
    0x4500807450904d01034003c24050f541340151402c98040500781c000381840001503503608480b8180c540141042862a600c0c90840016061246601c000d0600d1f0300100c1060700c0c0e00648a2404803070300380505850000740c0109000a0f11900d400c1203241e00030480310400344c05000600045030b880d6890b40c0d9280c0036100103071044c200035030b0f620051040803d000c20003140c010450b281c0c0c1d21110200180250b0007402a03a0605140650001c178047e098051038054804c10380051094410400c20030601c802d52114490389441004409601a4620f0014000818504800c1d0b070580c0d02304205942480039803484500049005000c03c06164000917040c40ca030903c10600682d520f10714149503000d88401242c1075001030705500d4420810402e120490f054164079420344500e0944030100303c0c1c00c034006840c22581940640814009031408080000b8154204012a44180071622801c0c0c20383c0c12007000007400c20a040072103801541c1104010000307031214402045540c1c66030303401075055000703170008030b02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719814172 1250 719812922 719812937
    0x90304060f09030f0c0609060512061e03070306150b03070f0302030a020c0a0302151608010302040203100509010b0d05070e011b020102030c0102120a0b10020a080a02011b0c0b060604050a06 83
    0x1054055048240595000200282914450b0030301c070601c0c0649111b9000020185000000c0c11427041084d13400c60071503402d0031001c0ea00c0c3c120811442e06880040c1c0035808440c104c8134a042c2c0e50400c50b22005510030754020a251000c00b607600c4441101d640182c2101c3c40800402842d00da11042003040804203040048e2a921410113200c024004c0c01c008183d60300ca540c10000c2815000105040d50000480e0721580e07559810000c9a0b003ca000815800461032000060005240940203598000c6807604201c401540d0740002880b801002c1c0d10100c4c5011000805c064600c10741d000e4954000c0c2031f03007031154018407241d000820b21415910700c0d0b0040040500300004580c801c0c01200c0d560500d0380c0c025915080b03986205503a00005840000b050f45c6008400c1c661414211086c03800c000c100d401600c500b070915186c80946900c02c1d101c0000319542e549480800d01c55000050900001c995125005a00c103881d10164201014041320700c24201840104003669a50540d4426213105190004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719815422 1250 719814172 719814197
    0x7020a17031306020f0d0302040b090d060923010c0306050a1511010501090608011803020303010b03040f0803010312121406010513050d0602090a120236161709030406 73
    0x303046001e050b5042c2202c42421400140b56940003d0b001251144c903000e54101003103d201c25012440303284502041c0c01d106108014551505200d2072040c5c6004c0c82c1c0c0462540f00a9480c0c10742113816050280c8004802c55990b510083c092054909540c07403400e08016407810000012005140d911030407054000b55074203400c240d0320034540d503005444600000e20480d40c45002c840050441805100741540c0303414071822000001e414540c101719099005189103900380440100c45603c014400d0f00d864080315603040014119000450007235002d1840705000e031004a80003481c2184e9228400b21682c02e12440c11266640c00c0710281d0041806d0078415034510a40b106001031040c00c0d4001503000d1958044e1a050014903001007050007001c0713035441d450a8a60b1a01c0b11450b000c1540690060050340c0b500130b0300b0580601040c0f894500000c0000d00b039180c2d580030f0070048811911281481040c01020b200540c00c001003081020354170380c80c400c0ca441d150854a030b40e8000c07031041e602004140920304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719816672 1250 719815422 719815469
    0xb0114091b07021e120102041401111c03050103150207120318020a08060610180b090a030209190e0304080c371508011d0702070519080c0607020a 64
    0x2501042d9002c1c0c01d0101000c800e41168070344c9022405040c3c00f07991010f01c062003810f41882142c040e03030f4071000c404801d2110900111584c001d00c05040c41c09110f202d180c00121110340809030200d00003568080780b40d60440c603100d05c2c2d040640d1840d6903e01d005024100024210080001d001e4140b40f40005030401400d0030790b0120501c0c2c3c1000b035001350b01c800c00490007060100710710303100707036400c0d50340c2c402d001201001100c09c19082081841d420f01421403d21a04a5542c01048155030080c80c08118030307285c1c1c00007000d50b5401d1368502c07a00d20707500306440c05500160044039941a075440145052600d0031880b00d403282c100221041c850004004030001518403840d48000d05480014001011805e8001c03030580c4846d640200c00306488030310320f262a4284103004090680d2050f00d541da41400c080051140e4500b07020304241c00798042c1c00c0010a454540c6022685041004801642e4403490b10107554200020a21028007a881c20025080540c403024480000c880100d5429000038201c020031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719817922 1250 719816672 719816677
    0x2130b0103020918150303032403010204030b0906150405010b07030509060f0304030f030501050406051011010e190c09051b160510050411010206012d0b13030b0114091b 74
    0x30f480e801503a04c048001c0c80c00039920414842d80d4250303001407100214000b0981d81e408121358883c3d003440c0c114803605c085546400380c0404d088000d0000340c00e080c0c4998811030606003ca58044040e0f02c85010001010b1a00304038041d880380945040080b541080088500d034820350001078140600020003d4a90b25507804444110b25403440301522800e0900d03000300ba4055503010040028242000032036546824813400d011a50000d003110308030104100c0c2a1a4280c84c64039201095580d5404010b0b0700c882484201219960070076619050f032400d10380f010743c40c4403075004214610b182c441013103410703601700d502d040780c0001580c3c03090386428804110000d01010030b00000c00074012040250302c91011a0442c0d40503520460400305a009030300b00480c0c1c0c0701824442c04901400b466003202200c50342c651911288210042d1207040303103860b08068891584203034201005486084420028040b0b0848620701624200718280100d0091000060340601c01402a02c0c15002c45010f20340d40c040348004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719819172 1250 719817922 719817937
    0x609060c12090a0e01050d020f04090f030f0f090807060e24030f161e0e06040308040f06050f2b0e0a0c091413080c0610060e01030902130b010302 64
    0x4488204059900401940c1c000301c0c4120f028001090002c6420408601441d05a88000d01842c0c401d05041d020001e41403c1c4040958006540700c40c948081030303c0a00800172180a03441c0e07208600c004910003440780c0c0d2904030603000c2000c4140c007800112000304615088510a1a244880056800001e080c00e071030107061248514a59182802000d400b8001c2c0d0b108190500c3c0e804010703a1a50a44020280355003903400000341d603c10a03d10045240c0f010801043d0945441d8070302204a00c00b090203a030003900251144000401c040140c10800c181c40b00c041c200c070345405030034100440c4a69403240204000c1c120300003e0340c84410250080d034000007444010044052000720036040c1040d40358006507006517010b9000040204161103d40111400814240301c85115592070341c0111411016080044841c0321080140c00c6014008201d41030142017103541c01c82100d1301d007000280401000e84200e41c18581400920340169681882c000740c651000880400e10013082c40040340240705840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 719820422 1250 719819172 719819197
    0x8150c04081603060605010c020d031103090a0602100f0b1309060b0a060c05160f090510030203010507020625090306050a06170106030203070f050d02120f010204060c030e010906020c060906 83
    0x1005050202c1e24040342142d0107294108002e580307030350044843d50075151019401c20b40c00503c40c4002840b480d0b40598510f0b540040d40d091418205c0000c08610b042d03482800182c1c030088000621943c03d00c541d49034800381070070801c001d5442d00e010601c007464004046103035694966900c4248000e54011900c02d450091410029584944010308541c5506a09440c90702c280300048a410342440d49420540d20600880030800780360002403000740100424200510745000800801a1400d0041c41d014841e641c018140510304245400039040d420150750b07142403802c0c221040115089011070b001e5035082407012646984c1d82000002800b520351203034480c100c100c02d000d80081419842041900c1c0b00728107403588a9901c180d001c050b030304907029460344003100300d500303000501d0200a18014107402e0011349000c0c8283c81429800c9070855803028001c181aa0380c19010103601084c0c444107100242400522282000c0c1d0081d92400e2145005008160008400940e9a1510141c40d410200340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 719821672 1250 719820422 719820433
    0x304030e12101b080a060807090e0307050111041a03040305030406050a0b090a02041a03041109040c030c030507091d07171e0705030c2b0804120c03050f0708150c0408 73
    0xf00e000e03806041c03a10700107500244048010030302c060654020340d000c42d004080103203c11420641c084009001016400905100070000c400000d0428014602040c0404182c9a00c85181c07981401a03002d403000741102601c0104104400681c01030207490f0000d810403400030f41580c030415205c005160b2002d03919405082c0d4810400c030520180c00901c1078451080302c20034024400c040c517030020b004c1079900131301d4004202c0b60203549080c0000c0641e0b0003400f645248040d00d6032900d45101c05002a0001d03901d941014009000f2408180030765a41c040800d4005c101760b003203802c85aa01c66600c0c1c0181c03041000802c2d0316440c1000e04100980a044100c0c1e4805a00110344034038a554602c01d10070030f80240176641078815a46800d00381c1c288040b00481122204421110242d4151880307144c0880700d0b844240f1000c10044050b421a0703100c030f4880e4a503100c3d80c0e4194104603103007001c51400000168001d94003170002000c0442c1c515808050302211600b5500c800382c000020f07004942000c0b2841c81103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 719822922 1250 719821672 719821691
    0x12090803180d09030312050403050f03040602071b0e0a0f1e02040905070212040b03061f050d2004050f0418050d0e03150609130618060b060304030e1210 67
    0x54450740e0218480300001c075a10304141440a03a600f007601d10018001c0b072000e01c2044480d481e2074000c1c80c4d2080c42032030014030b00b0300b40200c0805150800d440664446030301046103410444401c010010f208900d2040045403444c0410103604c0d00d00003019071140b075480d62003184014403117422080d01d800000480c0c01c4180c041512010007500f080c0b145100103424079010030b00250010450351a044030031401280391500380700200c0324550001d01090f4110408240d07603403900407500d0a0100c0d4084540e203256490320200100001d0303802d080008802020745801b503003483c46a2404139070455405071441c1402e1003202c00040d000341990190341211040c0c0030420810440c0208901c009242c80da122080d016010300c0506a64042c1c1c0360104981c560740c40b000c20003138a01403586540c40010f0964840e19a0855900c00050f60211080d914125a0444d030403c00c000c0d83d80a210170859040d2084c50441c901601e0003080026100901400f44038800d0740321600c0601444a00c0e00c02c0d0a02c04140305a021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 719824172 1250 719822922 719822941
    0xf0b06030a140a180f05150a06080c0f010e0114090405100305102c1906020406020706050f03060906010909090836060310090615020708030a080712090803 68
    0x10200440740582d40c05000a40310500522404141c0004080b440b211083c25990703119207002e4002094079103200f030b034002003440c2000b1079229100e5101c1050101da81d616081240d450440090040c510407004400068100d90b8050039848504d402440d00310341001400c650910244105d0b98205c0d0802e09140800c800d00c1d580c1401541220f22402c01c9038034403020450440d0845034036095810381c03068001081c03010240219600ea13000f951881c142ea500000c81d2407082a00a500c01044400b40d4010a00304200e5806000b44401010f080c10982e00d480e4100c00d025500d44401040c4074440c1da451008550241d1080d0382d044040c200c010420019400700c1c0c2011045a00700300c0042080f0a5000c89442c1e100c03441045080310401c1d41e02d88901180f801c0010040540c0008050b07040002d40d02400003a40c200a0180100a10700c0010b41c91099644c2c0e10b0003400d0a0f007070340040881c2d82c170421421707826039801050b0aa100c9a0b52408600100d41101040060648100003500300040441842070204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 719825422 1250 719824172 719824181
    0x10212250f02090c0a0516021804060c0305012711070c0b04080607031b0804060e0316050c150d09020a0302060307050d060503060705041403070807062006100501030f0b06030a 77
    0x18003c4603541950f5644803071540c41c911880303c040740000c03018000c0b51000340c45c0900b0100d4051005244d2003500320f4144000603408401c85054941540760b4822140c0c0ca5050710800d0301516442c0c5592801c021420340c40424a00c031409540d2409940341c6101c4a000d010100351540c135507201c411a074015564020a64250b0046e00880183e0f0090f413011070b0a15011380304a4200254111080f171031340c50002d00c150340c2914014803d4400680350380c3c0800740710340c0c1072008003412010504002511845402c2980c03501951072040c0c0d01071000c0383c04c5015844050002c0c4c07140c994642d0f13000302e883c0741503101094401210341d10007500b002000c801d020040350400040c1c00d02d10a0f086c0301b08203142d51007040517500c40d800d40d81440801c40c10002400004040451840500400303030490740c24a540321030f21444c00e1803c0d4403220000d2402da039604c441d12010011011740c1e00420000b0b100a04015480c00840d0720517205d440c0c140350350b0308078414900d649038000114040004103403235101c0c640341c04001c0141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 719826672 1250 719825422 719825453
    0x50702032e06080703170903070e1e01050f06030f04030c02040c0e100c02090a090813240203090a0b0306120601170c190b0714070605091c0201021225 66
    0x4908040c000700e4100030002d050130880e6004410000001c085001d0a20300c0c6c0d21901c8030a8050040290202c1d5200b514254180540c4600601c5611210031080403481d00700d041c1c00161141d2442d07001c3d0305881e903d00003070781c0c1c010384841d402881c26200c0d403405943d09203600390020341241c00c007510042c040da04003e0300340c6040010b031080303002448003031411130b14100804c2000b0341c400c2652012440d10700c0d440d4800070900d8131550480b40740140e0607001b8a1441c0700340d8050260107240c2480c011178042441580161445103000175400c0030000c60000e222800c0600490b604554044000303420f81c1d0742c0d2142c5803012082d000940b160b03075840c1c0d020111100d03041d028200b03880c0710f050000074040c18201c0c0c1002d610303010704184450550074150b44010903409070206a034600201102d144040805025060060650b51159030340c030070700d110038402000302c40141810b0b5003410506070701c09030740c022602c02182d0700700140c216074400620031030f8182841e201507400d50500c8482c08600030403541d2816524003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 719827922 1250 719826672 719826763
    0x4060501080f0a03080603010603080f041a030112060915020a0e090c040305060c070503120c07030314061f051b0601180203010f0303031509291c0305070203 69
    0x980c0c8070980c80b541d80c09402411102d940c031040f01c51021034402d0640982100b0300400104409540c1d48070a102e03500025800040e000c40028204030610340c000d110110000c1c0c800b905400d541c94200031245610040d5070207441613440362164802c03c8480303440780e4088400342c0411500c403040c034003006105030300d1030301d410340a42807640225003280840d0042d10304881e486402468941e4494608c40695001030a08449601c024003108200061001d4000d2084840e95040780d12454035090007410b81d6010030701600c1359040141032240b0368031030704c000140d07a190a007508030f170302964540200c0f054032407408100c580c540c44c110b01508a0b00017280d07090407501e1242d5000700340c2c030380040b910040303210078801d01490020314581000004d00030342121b9084504009048030f481c1c0e075001000c040d0340c0025040c10310079180d4100502d00d101d8003d45800001c2040c0c071071801d00f0384586c0181246030081e00c00581070000c04250181150b40401083d00c09140d0311082c034550880585911f1400c0b21010000001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 719829172 1250 719827922 719827931
    0x221b0305012003160311090d05061f0308090409030e060d0603033c02010f0f060314011b0e030304030602070605090607141b010b03070303120c1704060c110a0b0406 72
    0xd8540300d001624021201920451a2141e444c001580209405202108490020702c07840513076669018421480501801c00f400d03851800220400c041d15078914400c1c460080c12070140007240b00d400517039500c2c1006030f4001903820311504007610b1005440041c56448140000e9200304030506130055021680700f0f8807048850480c0c1914492940c540c6000541c004d180e04c015200d40c200364010980c003800341c0e4000002c0c8a0300344a0a001583d8002d92100d10640c2c07558800c10070480510040150180640c0c000c000c000800181480b20302c4030072040c0002c0052000207500ca668041c0300f2240110741c880e40c03c42d5144501d14110000e400111001c0e01d03140181343c001200c190207980070944051962240038600b00160801d031403680c2c00a5441000da65854203905d903079480c1013080c24003035402a2507500f141c1c0d040300345050545140c000c041c8100200002d03070f8890104074003491900b10f80d0242010800c6403201ca01129841115980002c42d840340003c0c4005100c03c2c0c44410740141e014600900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 719830422 1250 719829172 719829221
    0xe0d030b0603040b07030902061b0c1203070c17030408060a0b0f0d05070b0a0306090e060a05010603060b04050420070c081504030f080603070f030515010e221b030501 73
    0x1441c0403c44000d010f20136080001140b841c806e5000381180c910041010707007020050450342c0e2a00003414a5070038168089404403e442c40c040315181c420801c000c00a600d030000c169030794501243c8038481c200c102201c190180c241410b051060710701070044071088404600d00075280c80d02411000d000c050186040c61100403160602d0039109034801d03044802411a185480001603071076000500402c10103030745920101e421405406115407540f08503000303190b141000e0144208864041e8410001d03d4609241040b180b10f1070401e4808480c402c840c001000e441040c840440b001401101c1c0c41c5400c00002c0074000c0020804000041d03440300000c640c04900003107113000c000e5000741d50140100e200c0d000c104000c9445988130950040300542a20111a03850055410b804617039002200e4035003015030101c880c403045c003c01e40d0041c03821250080031414500c030b102d24503581c0d640c1d1558601c420104860b0078481c0e06a008070499600d881924071080c3d80303080141c02485000c0740000e0304d1a1551104c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 719831672 1250 719830422 719830429
    0x70606140415060f09210525030b100b0415090605090609041a1002251208220303030906050f070813050c03030d090209010b0703080c090609040e0d030b 67
    0x700e0b1000201400c0200c90501c07a0a0301c00b4440c031558481000401500070584c084600719810030050300d20002d03400541c152600034148850b940c0345220300030a40c84100c4c1569020400752044903080350820b0a2a00c400300410030f1101550000c00356900009030005002c0e40011105146440580e50510703259151030080360740e441841030700d1340d00020030303c00d00b60a40343c0341d845480d007e01c1c620100041200d40d40081000440040f10800158000542490b0842c10340b070f5034030f0b600c0c45008643c91401424501c0440e200c10280d5000384c50000007042001ca06542e40c25800b82c03a1005000c42441c40d070b81e07840c00401415446400700c81b203070305080220301c0040031000c202d070240c541502c0302001507803812540c880361440700d1401e071905d05c40c840e8805c1c803a0700c0a0005000e07110445c080440e2180b481e005200480c001a40103940306c010420002003c203520403001c1c0c0c0c21050060710541e54041200c00a04d040c080d158646034010b04c0d0511203408018001808046624a920103015050000d400c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 719832922 1250 719831672 719831681
    0xa0308090607090e01091107060e030306040b0306060907030207030215040f0c06080f06060915070c0f0503120a120e030d060620100b01020106030b180714030316080c01020706061404 80
    0x80004130002c2900521000c1c009400c00f862031900000c5a6050610903240d46050b14544020341099400000c00c2c0002824036004081e91801c0540083c6010b040007000302e4160130380180003208041e8007241d51010075109000d240c56035000007100007114106818003500d200d0942c03604480c0c0c413a2100002841c82e000350100340c480e08440c0d815142070307a110300c103201ea5507200c00b0703c81e86c1c803200000740d0100310310208010b0500756010b40310350f606050905602450144054000c0c5101c2d40c400300c401d0401800303a104a034240340aa240960b0001e418448020181c005242d0645003800041040224514154014011140ba680d03a5800124000f00c1582e441c00082190004541251220448035902a002001c2d4040103200000350140d4a440c3d45034040b0081e40d052a9400d40c4d80796000c03808ac01040304134080d2079201c4e131100c0002c50f0000000d03528484d1802d010040410515184c0c1031140403810f031174550700d010f4000d40d91681e15150180041c852030244048c07100001c600300225040c144034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 719834172 1250 719832922 719832929
    0xa050d1707020a0f0203030d0e01090204180b0a09020409060525030b0604090e031308160f0506072907050c06012414160602120a0504120f020109050a030809060709 72
    0x2d42846061030311200b20b0b51030644d030b00703a800d1701c0b0401040b540a0710520804298071700344030002030f40500300d20400c819609817100880041c43c0c4101001d001c289502d55054000348856400105d071003552000c03a010340411036010b80000e2601007040b4404039607100d03080034051400c525003101000c1103c107408440502034802d400c00002e01050007804450780c804942050840100c9080c0701e4a542c41c110b05000b107401550300c540142146011843d0100304a0b40902a007480d03c1c001c8a003403801003607650080b2040034000a1320b039040c80100d00c0d10910880d00000e40000c1030000c40c41e2900010f016030703004200b101c0e014412000002840b8000d2800c0d0303001c01c10759504d00d074141c81014500300c80342590141120343c030001c100014032000100c120a461201c2c410040541c58403448074020768040001840c1509a608200c1000001044000c0041c202c03256030a05103026481e80c50102e004010b001c60060991161111010a041d0031a00303040c41030105000b01d9a1075924100d044825440e01e20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 719835422 1250 719834172 719834177
    0x602090123030c0c030c07030321020906340605150108040b040204320a05070c02030703060218090f010807150c030f1b0b01050405091207060c090302030a050d1707 72
    0x4045070000001e4401413900c05440303012a41040140c211890070001944d004401003003401680192070303d400d48040e501d2007154a421820320940102081c032900c651f032401000d142d80c103c2040e01039010403010100700085000c0c52012159070b840c000b8000c103c01c0c1c81c100245e40c0554a081c0070303036229040c8070344503aa00040c58034075620342c1e42c00e0001605a4101e2041c9080c20710700300d009401031009241001058031041e07040c80e801c1c9903540d00121200a46240100144400c07400056140010300000310796215400582e40e580c00360b02c01041407204c040700d0343d10503540001d000d4041c1d01d0320103450580fa020800e48010303503603900340005050383c03003141d660101d0702890094022074018100082481041d09062a8000c2d050b2008008200021800c661409492005110074101803140f5540982c0c950f0003000e5180c0c1201d41c000302409515001443c0300d0311581030444941c4202050001160301400312503442c3d1480c50300b96101c2500030001340005d8412203106c141c4581c80760303a0a0090070b164 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 719836672 1250 719835422 719835427
    0x609150f010c0803102603090616021002030307170702060f07030f060602030c0d081918020405041a090705030a06050a11041203080708010b041401020c091311060f0a1214040602090123 81
    0x1020711003190450f0018801c00210b40c441d420158560301ccc210454560554069560791a0403040980a0307101d09041c4444542000c04002e21030307400042480d0003c1c5c0800225181d076903030080c00c8026000d00210b0303402990501000003902600040602031820140050380c000301c0d0f42c1c1e00100c402e558202d8655103080c180110710700700c45040d58040340c40c08000364104242007505402003000d80300260713030440d400790385224207090182c0c01c107242079001003040029094040c98000002e503541300c0300034047c0c02d440c1d0b81c03004903440c2c00e03880d40640140d4104446c00c036180e0765100c02208201d44080015004907113054001100c0b03600c14074065040c4d03100c890320f00703041030304192201500d450401407071030540c070807940720304e030b085e41c03404041c920407466055185403006007464504684846007200c1030140c0303410300c058001441c444c002d40c1c110180e10700d1704203811070562104070082c0c000711900e0804d010041d0700b44010f206a030740040400340001c1e05d42c4001c0f00c3c64068030400b040d541a070940d1810006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 719837922 1250 719836672 719836687
    0xc0f0d0e010c030207120b0f160f1b020d081b01020301050105390106090b0415030201081e010e01230102070510050705030315090609150f010c0803102603 68
    0x19070340703074600034002e10445d10900e448110484606240740c9080d0780c242c135000c0030803008803c581489a400741031046010350056048001500303002040f00c800b001c2c0320349441c0070f00c0719a805450408015400800c09001001c0d42c0c01d00c15102d82c494031241202c40e0101e1a0218030110500842c0c3c107e440681d5058a0540301404200f0710390040340310b58000c404041c0032044140d4800c8e0510200c1c0c19004000511300b4036221086085440200036903001758200804c6d103008140484d44002100e40a00b4100a59502c00d5001e940000700341480c00b00101c454000071403034044841c040340c181c0c0d040005918005008200341c0354250b1841c3d00050040c0c0c1700420500250400428401c08003001d801d040381080d42550b1181e0030768208aa201c207903000c210802d050300d0724045c401d0940002050f50130704034038241000c06548150301150398a014500030030107454580d200c0c0c0940c02c080382c0c00810f0703103403a8240a0500c0810300300b030344290860b030048010700404c510030108012613803443d8000118170b403520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 719839172 1250 719837922 719837927
    0xf060203030417041203090801050619030f0309080a0f0c0f051003111c2f0f1e04060804051e0d0311040b12041b0f0530030c0f0d0e01 59
    0x108a0f08030002c0c42052000154081d81c15524000d26446911088015800c082c400d50840b41d00408980c0305503200e000889255841c14550001d403070300142031840c1217030507050a44030010141d000340c100740304d066103800904c18002e150000070f5104400141996554015015800724180a070300e611407a0041c12146150290740090030135100314243c58282000b2444140007840c008034500f400b20707101d10050f1048100c8503141d02c04020040c042d19a044484030b01e00206010761020000ca00500061a080380420b11029070039014003044804c0d42c9988440700140107240c2540c007210781d032180e101d400c400114003000d821081c20290b001460044c903a00b204401030076941450700ca180d40c04200100f40e0304920380c001c00f1401c2030720410700c425007094a8040b402d5006d6480c81065245200e000348030610307840b050740c8100d07282224204010a0048041405034031070700f00d842003a04010b4440e400701680030019041c8000c1310b10584400450422070940c40c2e01ca101d022030005554080c26202560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 719840422 1250 719839172 719839193
    0x501031406090406090c0605130b040b19090315090b060d05061b040e01091d03040503030a032406021b1804021c0b090c0a0605120114040906060b03040302070f0602030304 75
    0x1800360b18089248171640e29006c0701158140c1118000410010b00702000103000c0410b00c0041c4821002189081e181c2506201d0500071481c1c3c101d885030451510320700d0b9a21800c0110055508200352800c412140c28082004082c0e000c8110b64010700440064080e24243c00741c0c1d140e054008010301055603a4a030b825568403c6c00c1255250410148404125444030f104075038007801c1d1007280090614044401801000103040300345c0c1c0b10b54000c00c010300c02510040162548440c080c00c01154101c003411035403507208200c0d0400856102041000151140e0018241c0139102c04440500100d80c406004d01c586080c400d941070010b0074582c1c5c08038005080048180d48100303c1b658000e807403682d40c0c1d92144128a800e681d90492944041d29a0400b441d1084168008100500300140b07890320032a540300c0c203a0014403580d404418103807401d007800e0320385402c04030300d20b60300c11810441d41c1c0c0c950112000a400a9030180d006105071100800e020303c1c0c13010a01c0a40d20b040d001103046540d00e030344030000390 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 719841672 1250 719840422 719840431
    0x512060907030f050a06080f120a031a060703020a2d1119030321050f0f0c040b0c011d0313170304350105150f0d021c0606050103140609 60
    0x150b442901c0c0300c42e440300d03101d250b004100c68003012906d240740c511601e14040210300078281c02d0700000e0107003d00112030303800c50b0680c060038140410545200c000e1621100c400c4802c0c942c0206000692600301503020820411040c07040e801c01c2040c0d00302d080070300744c2c0300c24490b08000c038a100b031260341c0082101c5e6040f5400700e0000400c3c0b0b070350541c3c05070f0171040c0000590b40201c001c00d21100310307180103100d0121441140d402200c805c004500d03182070110418100030b0107144880101001041603040800211405440c41c00045035503201d01144603802003140350901300c8070041080c0d45d03021a41002c0700700c030004044008201103e505001010f04140c2102410036000c0c8410040050010003c40704024000e01c22292103581c04840c0384a1141150007001524440e40b410080060320442d00c4846198540181c5050159020340c1c808a00212a04c0c28003951182281064013592800e6011307a892007485a04140145542c440054050320040c0e8481d29040c040c0000050b26800c11055141c3e10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 719842922 1250 719841672 719841677
    0x1110a08040e161707030b0a0b0307020f01050105030313061404090c030e1510060507030311031f08011505040b03030706050f0619030804120c0e130b070512060907 72
    0x911015911032000d80d21940c00110401030403400c02100084030314044010f003e503420240402100c03038a5007605460002c00a00c1899a1441040b106454000d6104d000e000c20440c181d540b800e0064010f5603c688000b142100d96003070000201d00b504007c0251014554004605014507007041d0080d1900b120750605403085410511001411107500d0084624252240e180091942508000d50b401c0200c10310314600b8031260300d4244815100802021802c5540c503290182c1c40d1500c82c03400f100601040b90301495009408014801d0400040c0410007a2603920915051007907610350042d82aa080c13142c26043c400b0151008201034246a00109110000101524500005a500c000c00c9446c180d0346003519141d001c003080201d061003210720038054a80f02d10342d001d0918583d1155407600c502e0081203948020404404204008548a440600b501080d00030a9107004c0001060040c55004160340c400d4110020462160080d8203e40c9403041c21000480039a541c941408418000500302004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 719844172 1250 719842922 719842933
    0x501022d1905071509060f020c0d0e19080601170708151305010c03240506090d021c120315050f0d050f011a10020f0a060509120409050a05160e0111 65
    0x501000c881014a0040131400120182c05003007101c111100b0081d070141d0310b481000084082d10300000c819030196401d2800e07005001600000c00c0002030a010101030f90b01ca5550045910140421554180e50055828840b40401d45401694074404c41c0b040d0806a00702403d8800724104050b005944480c04803415510030b6587d90b1001d0840d02c01c82c008500191b61000360055522203040101050884030302c481d190306003044000380d0148a0040c00511039501d0581e41000c54a94000c1c2c541c2ca1080408c250315010034030304040d4040002e803110000003c2c41c10304048503456690306c1c0f2506645000e0805400d103104070043c48501c80591409031044d1050b9120070401500074080d5143e50b070444100c0c0c49074020b4840c01e000324081d015100b5010b6400280c0c00c24409600060310031405904210049800d40722459010304003400d00b8811840c0c0c443c002804600082d143d00300c1c5004401c2c50100b041140d43d0307000b0035180049803080c01d20003d100d00070600c00071741c404c0c01461540321401041c1e82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 719845422 1250 719844172 719844187
    0x10203131106091f020105090d022a0402040609090e01020301030b180f10060501020106090e0c09130203010615020c0307050319111915050f1b0f0a0501022d1905 71
    0xe81d049007a1030103034440801c0d141c4d06050260f0a0042070340001c419401450003004460001e92242c01500154030380010713003c030b0f650000c14010030710186480c01900443da9140c031444010b0a5905600a503c0024104010018140014804c81c0d040302d40140e0502c20be07454030740703080210841d882c10b00b9070b8034401c440b0740f120100024004a40ca00a101100103600f40c640000a803c3d610341c3e42c4000c40326071034043e981001c1800440c400c2200c00d0100c0c0e10a64035031b034002c0721505101c0c41c100042e400d5032828070042001114200100305511a540840398032140040c2019510f841e18080d0a8041c2c00030301a0400b0300409000e03001116128084021254003210302055402001d600303900b1101903000c1d0100a4078003040d05510800b022440c20f00d2030080724a5001c8080c3c810325043d01502c0640325461090680b0600845d1018289241581c0070100300c0c0c00e00320f010750800c1e105051125100101524815150300c00190814a680c0391142000340380f806241d06410a18207070b00a0010422800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 719846672 1250 719845422 719845429
    0x2070611101d340803040605131508072d03051005040905060417031506071a150306151f020a1e031d010c0f02030c0411030402100201020313110609 65
    0x24005101e10040f2058603000300c4071800e5690b0602c820844001c480402c1c24801640e01200f12410f8903c00d04105540f50410081c101c2882c5055101000b2400c4103410b41020741d50001c0120700500c0c2c01e541d103640c00225040418024421996116150541d0b00c86402104e4060b41240d0381c0124030840b5904820340d24004981030b1020314000711010382100d402c0004101c44100b15140a01142002038110310f851780c01c490407516a400503138440c0e01e001c104401002560041e040e805034080c00204101c0c20400008079040c0d1400d43c021b407003800b503100090300c03240c0c5281d0000304031076000b400000c031034505111007901c5080014001c81140035000004020403aa03d6035014a46e60f8001c0703448001c60b041c200103041441941d0349403090000e08014000c03e81e8426079185801e500044614070210140c80060f2420b02c90844054103c1d003000c01d2001e10b540751034041d611550003510081112440c60004130b00700d00c81203655503419028006154003084a0054005600d64040c1005280c5010840003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 719847922 1250 719846672 719846683
    0x60906030c3003121b02031923030a0608010e10050106081e10150f090504020909010b0703090b0d020415090305120c100c09030302070611101d 63
    0x15607014803400010402209642140030402c1e0885280010380092080c186050440b0140c01808002a085000c1407000542d8842e01c5040a20b02d54141c00342e20005010f034594121102281801628001c203c0507240120105407280d6002e05911131100c4800701c3c2031007d904054100b011b0700b43d035030750003182c002400d01c201d1540c80c580034014080048080700c12819100140c0206c1d0401a08006001c56404030f140c410000c0c10326031281c05000c1e561081040704032000c0398000d040350344c1c000210140090700b0081c1d5500b451025552004540e40f20028002039102e1a500035402412140c01040703030304140000b42090324030900e005816980d4425009056402c0700d0249d005480c1e0004082108801003284255103549a08280f20094a55183d49403541c80c000d4803204104000128180c440c0400d0001d0075000c00c1031041048013030741c03280c0000d1640301540412030140c4038444012031098012092485d131120600002c1c103a4480514000c0060040384130b050050080b10035526900304024850f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 719849172 1250 719847922 719847929
    0xc0c17071b0302010207030201031d07060807091e09021b03030a0b0a090c0f05161a0106030608030c1225060921020705121905250503061504060906 65
    0x100030385404890070200d01041d031003800c040048219680c1040142d8010911004032034090030001815824006141c90040f42083c0008045c01055400700d0b5403a0841d40d440cac010740055440d0000907849003004100314152400c400b003014842e00c01046a041942c0080c40ca0b80811842d040c10440940c0c0c0e418070f903070402d071031501c00d003030311440319225900b44612408000e00403441e0038400142c805102800c0b948505042404011000501840c0f410b41c0d5508000115807050441000c6680305c1d0f86904001828014600042e04040c0000707446100003095804801810300580300d031000e07a40803a43c640d441402d4000561000750300c071460180f004a00820f2142c0500302c042811070051a10000d60600100050a95800300c07581c400c0966000a240007921400d031001d2860041405000d482e002d40c00c1c1b2101c1c1400031580c030070700801801190540300041004c01250f02810100203a0b5440d0005010300c6c0d4043e4040c800195010165039055100d071140030f400001c1041c1c9030309810b0140c0e5110340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 719850422 1250 719849172 719849213
    0x60c1c02060103120503040f0318081029010f120f02040816060521040c09090317070c0b0415060315060303021203010b16050f0601230910090c0c 64
    0x4009018021141110b5252030740380c951321b10314113580d80d408040035540303002d400c1010380d4811400d840c004400c2c2801524040d011a4400250060140050711003180d400c08043d100040c0c80640d41c00c0019000440c2034141c40718159105400c41c102e030395000100d29040038a864500101c1221110310080c406020040042c1200003082c610855008030b480e840741e01041010068140a0301e08080d07628070403482215010115100e6080640710500542c00120095251108400c101340c0c01c01101c1000d1042d0225403046e03035549000030f07141c13100c02e241c0c007410010740c4e500040c0c0011604030044880d006030745400160309449403a010380e8043c1000300807181903500d139414408c0c1a01000306054142c201c44060345158140781000543e400303161900021050380c100000204074007800101e08003210304040b15029039494102d1940b0f8400b900200c40103010305039094030981000300352184a06402c002019401e440c01d81c400000b40704444180303080040e204c0e0200d0000f9092540d081d04403417000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 719851672 1250 719850422 719850433
    0x40501030c0321050d0c0c0501050705120109051902030402040e06010803270619050708121608040209010e2d0f0c0c070317070204020c010515041505060c1c02 70
    0x5240039094a1940300c50148583d140c1500c0310b61082e0b00c40116040380080391404902400300341c2e415141c420320f00c08010300f0b550a080070001c480754444050080000407082e000b8807642e0ba405038004039502940e0141c0c0c1c550f00c0c183e0705140d81b000c81d0011a00710f8400383c0002030500c165000142814003c1c0c00070403e0381c00000b03020003e501164a41610180e41040505452440030001405441240030200c2401e0001c003090314502d0003401030b1507a894104031903540c0c07240510440b0f40c182c0803c50702000340c40400e51b02208442e01c154400d6214550181c000302080e400c1030001040c00c031004068880110040220802c480c806480c40c20340740d4400003076417846040002e94120104001011410514020b220f4040c00080001d840001c894210807542a151081c07098904103108403140039401c1400061070000b2440154409442000703102c5200c000d01d540f100401c4295813070b150281d5000c0c86545e01c1070160346084d0005040319030015003140d10781c00c401d40d203030b14207080386214510140c1c109 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 719852922 1250 719851672 719851679
    0x7140604060b040b1806040507020708071e091107020d1509050c0f030d08010e07050915030a0b0a0f030b0a2408060f0705030a0504110a080d110a0f0f050a02040501030c 74
    0xd025401c134404040ba086065005c046618064005004005510560300d80c0c0115140f24000c0c0082c5028000460136280c0311900c883c12030404455840d0b4107282116101c1001405400300c5c0701c0c1c8011280700510951420055800b0041d8039401918150344103030400540031440b006511500010311701c00d10241400c0500d030410010000c1f12003d8840c020303086a42d0b5800c145a21140310740c151030102540f19203680300c512040344c244c000c10142c41d03081900110512800d80240d40910b1050000c0c0b0814880b88100e0001d0108428040c440e003020210140c1c01480040c2003d40c816902c00c84400000915040303405a4201e45564804510f0713540300100400e00500606004030369000b5001c1000300c5140c180702c0783c0140380740b0000380040380c80c80c2d661000c5130400c10340141e041a0000c6c003c00a05041f0f0302c1e00724054458100050780c20200340805c131100b00d00702d0003143c40c00c0c0c03150b0000c444800c0e1381c4403601d44074824021100704440c1801414140d000583c0e85d44100340c069801210142d031518103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 719854172 1250 719852922 719852929
    0xe19080d0e04111218240a18050c010f0215011d0f1302040b0d05060a0204080c0f0f0120010903020a1101031a010e0102010207050708160e160507140604060b 69
    0x20040300011404608011804c010380d403528090340c1010105907a45200b8810104d4141824260243c2540d240c1da4003200d00c900b02940341030780b806485c02080c10007001c0d944012124000110840080103600300b07504104943d80609503d0102d05914019100d4400380c5043c0c8003203a0030240c000000d140e03100042c018588070012481603000340c1240c0d2405070fa0828820100418150407002441140c640a030000141c54008031411000d80c0141126403a0034481005070180d00540501d008a01c110340e006091840c000c40c2c0501074010103464079074040b00080045401403190f0060140b0514440301180c1040c40c24400c440e0014002e82c090700720500c446c50708030343d200c88003a00d0300d04041c201030840c101440c09001c050100002400d1046030702a00070b0050b40a4003440001803c01d019646001038103150109010032001c40804c0540107894985110f00c5c41c886041d03a10b288107100420f240005180140004e140e08c901030381d80c2c031403032a403100c11043c6444411a0121622030721011450854103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 719855422 1250 719854172 719854181
    0x5100e0d080d0c0c08040e252a0b0c09031204061e03140f041110080402090f040305040e19022b0b01020a021905210d0f0e19080d0e04 59
    0x3030640c031308520318585a466994290045005580d1440c01034004a200410301d0b80f079007001c030707162440720b40000100044083c04141c507103043c05008031a070f058212803048030b40c511210038aa00488501032500d64084080b101d0301320000032070b05803040300c1070a02603584200241004107000e5132201601c15860300885514400e20009806250400740a2074490782800241903024403443c01e200b0465640341230508072143e10b08900c94100c5075107d00000b40c5540300300181e114034002c1d509001e56884110202d003050104980c0500000c0060100b804525030350346059030422611000300300598101030a13142281d1007040c81c5403001c08403081c4c1e401200c03c06a60350131070f1103c8080c00c105007804840003070340311a070100c0001e00c44c40103092202c0401c41824204005040040c1c0a17200764460f030401300001190485811216200d0a80d82100d054461110b8411041c0d11381d0ba04402d46841d0018418044145080003010201031000810104000c001d1140390348041e40d10995003105090a000c1141c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 719856672 1250 719855422 719855441
    0x1e01080d02070e1303050c150112060605100905010f020708030a05180102160911160b060306130c0b0306130c03052208070803043e0102011505100e0d080d 68
    0x803143c401c12400326020660644683d0300350810650301e0701002da5050808500b41409900c03a80043c0010400003498810030041d5445a0b4040000c0c50711030301040421290041240001208e512041c04103509ca8a4405800e00050045400c1e1a840740241070a50b000910140c00180c4c022401420a07840c400b20a00030100c00e00180244500c54480b545201e4803c1c02844045a2184104285101194111a0700140303c0601c56005000e0b85130010042c10240c0b00a07101e4898000031170b031842140314040c41600e81c030000c207540c120310300109800c2940004240d99482460114032010524840c040c10619115a80e4001050301c1c2450010281c2110010b001690300880f01c80d20300001c240404495045400001d50703a125995854a118101800c40c1280c1007220920301c28404000040c102008060000802c003030b040400b000124204c40e503d0258507040703080a24104400d003400721030a01c0e100d280e450107204011402c0045035182044000444d000600081d9081c0d64a40358030580017103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 719857922 1250 719856672 719856689
    0xc090b0340060c2607050c0a080a0207051905010f030b060a08040b0108030a1704020a0f0801060f0e040b060d02040b18041202030306091f0e150a0602030c03070b1e01080d0207 77
    0x2901354403650390054595440d41a468640b250313001c200818081d2060312035404409003290540812860010401d4022800810261144a00100c0e142c40d00b9000c1001c007001800c110400c261420004407110f140e2140034006150342c4024400c00c540703800004100049958864041900309458482c0079584142e100b4122a00180038506840d0340c0a03100304440d001e9400c480700c894481e400016600764042c0e01c0b90155100844000408000640052080322940c540b9020281c0d545e240c01c0604400c00c13100200018800750001310a490208a0078540d240050300004200c44e000002c200403040b40c07d0b03500c07a074010160070841044140500c8020307620b035920286040d0300705040480c920500242200001d24403c20740915808000341000c4020415075003500b0312410036021402c07070000e4010b11030b4014004103001280c12030001080b15050181c0d0402075140c40c52948610300300c02e40103000c00380c40185848140000c0058480214041e201e944007503c00c1811500c0041e207802c02c9540300006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 719859172 1250 719857922 719857937
    0xb090909030c07030b220521040302180a2c1b01090308031b040b090130020f130314071205030906030a1d070503010c090b0340060c 58
    0x500c1c02c0400d000b02220b600080d042c20030348a840c2d222803841503400c41e8920742c20f0b80400c55401d000c2e00081103400c1440c6c03000740c0c00c000305941448030110310840c00041d400042204000750040401d030341c1103610191001c0300080b541d04996145001102d454184200d001007018480d1600c0000d00c00d1040070b103090b1000580c103086000000e803c0450034440038001e0400030000505004600c2d0301c90a0041280007040d81c0c42d0749603049020507402c804d450600040c69007011940c0003141003412205e0007207000710112410085c0b40002c011703601c50344103000c14010521008181d51154500140550310402c410040340f458030b030300985061000d502406100814a10034400300b00040100d030303108807040da1501d660340e9070b22070408082c03c6492141d084807512008000b800640100300c000c140c2c0c0d070440003444010281c4004844814140c0903100c09d2071010008540031070002d61142c0c464540b4115421680940c042804600c0000d802c0e13480b001d4910540380070300300a405d100741c02c5402e1441c1440c06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 719860422 1250 719859172 719859187
    0x5030411010f1106090a170a090905060105090901120b1e07050906071209031704050f04020a030e0604150617100f0b030d0c1a0106050d050606070c0b09090903 70
    0x303140301003121032410b0184502058034480e201d40c845180310b0300758104030303100c2d0f05107411195507800c0f048105440001c072840004200101000c2259405141a61030321401400c1c0343c0341c40c00501c1c02501c018103110f0200031121403a02ca403e03a460080c0100b0203402e01c0c00da458100140040c100500311002400a2481100103d00e040440b0741c101e14240340c01903c0f40d0700c0b5004900c1c0ba1051120182144001d031059040075035016143c001603034404d56000c0d0396a13a80e444144243d01880c064564481d0340d000e25103c00f410140d0150035544010320340415100111800c0302d05001c02511b0648244011200c1c0d80700f40c4801d8001d0400400407180741c500941c0700041030039280e45404228420250f02e0740d1400381040d510f03030041d00c14070000806880c1c01c1500404060507003082c0420840382c004a91600680c245030340c03460740d4106c506980f5618075024048013140c00030400104115841507081c0005400f14070700c1d804c460040d040c4400695943c908210812064450003040003989a01c00c02150f07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 719861672 1250 719860422 719860433
    0x60c041505180a09050402030d02030301080a02191509060906021212420d02030303040201120213030812090109110d0501020405190f06080708041e0f11040c050304 72
    0x101041419107003160301c90903104040d0110000200c861580f280c1c0d0030601040e0007110ba800399004138801c804079121401c480209a0701c0340001d2080c0700030b58008103000313005401d00c4046c00c1c2d00801d00200b10040251141c01030344060404542c68000a1030902c81030007002d402100300c80140c10b0900082110a41544a000d01341c44bc0142081c4520301040c00b20b00101c3d0704055223600104a1120080d140c00c507a6241c0c000d001d110b03401030b02248001003c0091307904100040d6421190042c02a41c138543e00c5800541e49002180d1204020035420003090443c1244161290091031244461507a00c008102025604280241209104d81d01d8940c0260004a84812a6030414400c1c0e59002800b5000d0030154024065648156006040c08084924403009101c0c100e0584140178040d001d038584800c411920603d08886c0140071856400100c0d02140040c0c030b00400e404440c40e000b002c01c4003981c2c0e420900d1546094211000840d00300840c400b0300e400d00a43d59400c01c1d40c07900d81d0861505031901c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 719862922 1250 719861672 719861699
    0x90803040f050d03030207120302130e0903030a0203041412071505090c0f190e09010c0c05031804060305030a11060a0c0e12070f1202101110050c0d060b0309060c04 72
    0x40a00ca00d404250f00700406010b80c055034040e94204c115407840c2401e44c0c02c003a0180d48482e001001036040c0180100d242403c021050b40500255002103003555600e0004100030f41c8003400a4429044c4103040401400c4204800d0580001c40007240780c9502113813401e8003801440c4141d07286000c2c18001004041e0300b0000702c0c255681b1084511000d240e24180108002e00107036414002240c00d4850b000c14071a00450300107005003200c90003002004680c0c18202c0302100b9001c001403054008100e1b203d01d00c0402c1000c8408150020700002d2565503039a65586103030f22403450350001c2800701031b0490000c801130104541c004040d1805010440021000030300843c4001d0002d1321446003443c00b00d400036020400341003d010f1070000a0080b40d221800190030881103607049100e42c110071000000c081c86100c0c9081d00103140c1004005030011a50407402510004004a80d80503091019450500c820300841005140c14803406903a420045e07400c6080000007803920b2a01030b0304010070860700d203900c1d01c3c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 719864172 1250 719862922 719862929
    0xb03070f140d1212110c01061508040b04141608010e0705090903040303180e0415060b1c0207050c03100b011704030f080c040b18031b0321070c090507090803040f 71
    0x5080e0607007200c4040104c000e061000541c80000c201296000075807005500c050162050550300c5c0781400c030680411200c00700c2c110f0f0024a07010704070010900040caa507040f081d00e07c281105a400780a00115040c131741380110780c0b000340c20769159203072040203030824484040682002c0d290f120191030121301440d500d00c501c1c40700604200340c2500301e02da000c1200c554400078002c2d03403100740c0d10f0f41800e0a0240903103402a65110049280403400241c2107514012201031078090241e01c03201108400d03041009401240c4240d40031f010303489020207256000d00490f8000310620034001148681240018940e42c0645c900e4144002e0700c8062101007904401b461010071a02d15005105a5841000707260320b01480c0d103c1c4400d440301040e840c0c1c40521500d4954880d007401d50845412190407818444036a03105a040c1e600341c2c00c940c00d4030940072500703c0501c100000c07000180385001410303034450200704c1d036691000802c1d0786e603001801070442d0302090050090075000015411309041c104070110000741e610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 719865422 1250 719864172 719864177
    0x50105040b0d060e010f050a06030203130f15060605031504020304080d0513141f051005040e071d01150f1b0f060e06160302130311040b03070f140d12 66
    0x10181c0550105403c400c1c040d1500c4620380c001541d640d24110261811805028401c0720b41c4480880d1483c800c0c401e40348a4001000b4080c1c2d410040d49841e50825908402500c400081c8001c91000d04001d006590017450280e0308e040d501e2404070210b5003446081c1050702c3c4103900400038440412074080613207084040c84040001c0c281c40342d1940001b0740a404400518441d43d072180702801705000f00e00c200d0380d40d041c00559100900280c0e007c1c0122807040b1141c0f141701034407003424042070400d507000b11301da0780d5031508490781142c84211081100700c246942525088291005011040c5180310b2650000c0d064180f000e543c1e0000074010f4201804041d2036001480c80440c075005100c080f0b490303c10460742141080042c20080c094143e11006c1c21141300807813409540b2004071080c881c0c821910003150f6440d031055028295074810011020401c400b590083d11400001e400d540d0a004c031030002c1075001407500c41503140c00050118460689030039881140400e80b4500844c00c2e80112500700d000c2803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 719866672 1250 719865422 719865427
    0xe13170a0c140c0a08011a0f130f060b041e060309080d02070c090509010905151009020306030304050a1212050708030609130b0a090201023c0c04090614060a050105040b 74
    0x2d00300c0d03807820300c0c0c43c46015030181e42441c0004201c0313810741c84205020074410812082400d5a418080e03001d030920b500c250003100c0ea001600c8404601d5001c0c04903030580001c08142d16958070211a105d42007a040003a0001030b00d01505026403103440c1410007032880f41401c1c4032415047d22034204a0151820024513140c0000303858040020b107080380c00c050117a412080007542440305505000b0889800200c0312486811034514441900c40d40583c410b042c400e84d500c4415040599980c0a5080506041c0d0184030505c40070542e507a981c803441002c0c0110144900c581d9003207003000c000c1106065545428058100458804100030a040b81c0d030141c0c054030381b98441c0e00c8030364943d401d0102d14580500507628040078407280705625000102264005d03401c0750000241100410012112504892144641f405003600141100c50107071b4468904002a43c4032460240042001d80c1c40008044540b6030b560000c4e03a2807a03401d503c00315002350040d908100301608290001c0c0951003580111000103001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 719867922 1250 719866672 719866703
    0x30612030717030103060e070528360204050d020405070c14010c020c15030a11070b010602060105011d03060f1003021503071715090c040e13170a0c 65
    0x800c1100c0c40e8691040107000200ca228606542c542c0007808229111820304038090303070300b020009860042c0d650041c00003a0b0341c11501031842c200c0c1a4010b8901440440c110700041800c2c0c3d100c400c0602c40f1844d410003c81070508449842075070785600c0d071051450300c14401800f00d03442d0801640c0740310381e041c3c0e40081c880d2101d08086c3c0700d0b213107880742c01003501c50000e156400c45901900000d200f4030716502140c02241300c00b000c00004c00480065a11032450900000d0303500041c036000011403c50645005107001c00e40c2c0c40d80700039280c0981184000da4030580040160356407204030040c001d1249044000054020400642c9696016003102101400307080420b010b15965270008004607030080088002009015404580d90002c5484d0004694070402d0300100c101c0c10303004207220704034803200c44100160200070804164800742200c00b45440c144004200c5803e03109299024004201280c00a090b8626003007841c00816111746a80060901000c51241d0300b240784540c805da40130000980150300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 719869172 1250 719867922 719867959
    0x50306090403031d100c0914190b070c08060c040806160323090709090503070b0a0f0204080606120d1407051908120f071202091207141e03030306 64
    0x11100500d1202c40120ba004075044e0500092210041d50844820310006060000540d2903540c039104a1118844406540c038007454100c51080740100c1602203131100301c0c0c58090000c8960403640c1c04440c002c0d80400c040c030450400b0843d5035880300550210500d41820b080540c1c2d00c13641c3c040c00d000410080d441540042900a0f04076400981d05050b00c40d4004802840c4100d4511085ea40e40d012070080305030106290086004908400b50048021450180d41d0390b42d03041040c40080c0350500c4a42d1350500742d031009009000600040c6a00001403031142441b004010380c49485944024455014124100340150009054540348862100050f05ca444504081e410003040e10541044948140d00c0001080041406041c0300800d0080c02485a0780b8940b203018610340c2501c030386020030b01c11080002403200c10b400401c54114080d0014503444000041b05260005581041f2595002c0001600030f900b031810004000c040c130f60454003424207034107011071786910000d84407d00070010346008541581 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 719870422 1250 719869172 719869181
    0x903030121061e060f08030c070b07080d050c070302240105010f050c120406080109060617060f030703152703050306030304030c060203040501090602010b090601030203100801050a0b030f060705030609040303 91
    0x100c4083d015034074a8540710101c0000c0c1071a0180700d0200901000c0407607120400410340e84100300c00d200504415040280320f0781c007a0130107001156582c00c100205403481e03240b0301445018101c400142510b614941c50081d0411400507211f06540501c05495203402c07000008181c1120004c2c00e01980d0031940081c2203402e44204910b4240c240304001e04225401100002003085507015600c0241d281d88403103040f01950564882ca10003d0a4802644866806a032000b034000e28003c003002485940c610110341485255482611044018124491034015901400c02d403194103030317040a00d01500d4844001282d20300c80002d400c000001c00007410546082084070042c581005101c5030742e56894078000d540f9071080c0100c0f40040c202d800d0001d051401409050f03120318009018191580e20301c0c0046000b074200030665030003401800ea000800020038407596000348042c800208095503194141450b10309880c05071049039011130100105c461340a01601c0d0400011600e549040e00c450071300300c0140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 719871672 1250 719870422 719870441
    0xa1a03010911120313091503230613080409050705210601021009110409030212040320060903070e0a09211707050a050c190b0f090303012106 62
    0x19841c20990105001e880e10041d60b114004440354107071542030081c01e03074a90042804192011002c24014007440e41640c100140443c6da0180c01d0f1002d5a90352102c10000711503803800090344a01070340d1700c0e00348041804101c5d4440c3ca131143d140d481e01d89c20f540e282031612440c441d845285030741d540440c0d5a2840b0f2011a810740c1030b10320300d000c41d1010600704114030304000e544850151017103200d84001608075014840426810041d903400c100101c01c2880041e100541c021411802004c1c159110311075480d02500141d030080d51642c800c0d00300101d150450344e424450603841110140692400c42e50006401d03002d42e10030003e0901640c403040004001781001c103200130240e4030ba030440074034207030703500458803a803003505680c1c0340c0510000b020b12181196080e58003400007031040141ca000c0301e02580060504404c0d1204036001c01e010702882a6045aa0500c1260040006d906005c00a01d002c40103a0b00034086078061442c40d490082805080b03818541c0700030590001c41507a0041c416590701c0070056 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 719872922 1250 719871672 719871679
    0x809070f030c17010506100e01090506130801060f05091b0906040303120c090614071b0816080303090723030d111005010302060a110f0304080703060b090403080a1a 72
    0x80e80780c0c5411000ba03803076402007014103001481d038091814014004d0501401d409003072450034103030300c8108a072108904520581800f580101c001220b031155001441251002030035807500301d003442060b50940e00282d00403600c400781c41006001c16512250200e80241844045e803d401c1c1d4040c40c18800c1b80103550040307070300010111b030001c24583c020032451100c243d4144d0402c162900c0f1802a43d003e001402000b000500c10890100340d040030720000c28020b400703400700f203e130a1558054040650aa0f8010381c49540000f01a01c2c20308880b0f00c0900003400c2610040c0d070943c03900410b02541c2e42e03100e208100b9080d036a103012603000c00b495000448241c20190965202c0c441001020b0081250f40b0041c0e003140c4100c01441c41801d100e0300c81d680c1079130745c01852540b4280c41940c080315801d044101e408200d000d50440204121001c2005000500d040e0f0301902c1c61500e141005000c03280103641701c1d405440300100300030019510603006503001c0d841c503800144000c42030081e040030298a040c010b82 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 719874172 1250 719872922 719872949
    0xf0310030f111804051506010201180507080d110c06030a18030f1209080906030403090f030b01080607090b03271212060604050328020607030507111f080907 69
    0x50020b49004810301d204181c91009200c00110a090490041218007038135680113082d441001000c0600c0c4e107030f00702e5014400441c9601e0780446070a01d0f191503038421070320f0354848901000f81d030ba41482542e4a40181e41050300082c02051420364403400c140c0d0310300340320b503d0000c0042c0c6210a154401082c0500421400400ba00f0514010740040c00c4040d8900c017250b0340340508041001d1901a80c40c00a80c803412540c02d00c1d6243e01030118a80000e0400c41c00d0040c05007011502c0440711440000860003080030146c0795140540885c00d141000d01468108918408180f0100e00c11340200c1c1d800454404002045d1074401c10906103c403400c0100c0c1ca6240550340c00e09140d8100d54014040940c91030008400f1030302d905007040070501c181d1059940680100c6c9045005c6005007540e00450722441e5440649045141d001440c1313a403103030500302c0c080f40003c1b074040d0901504003d6400070703400c16504100d9244034541130201039403181f444d800c1040081c80c0000c0000000340040c0c8028a2040528007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 719875422 1250 719874172 719874203
    0x171303200c03010f020c030f0f0f070f030f0503042003010f020c16050a0530010504080c100501030803010911040509040f0b103b07030c0f080402060f031003 69
    0x1c0e10380a400210a21075070a05406a030010304900c00c841502e180318004510f0450750186403250380c0c010b403450506420051088440500d80d000081050034032502d20590100c1880c80d000c0c0505101c1c4285004104c1d0030f108100c00a41c41c604182c0c800b28041e0070080d0884d1007000001c0c007401c0c03005006001580080344402d010703200014140c841d1070075001210500c81c0c5583c00c0c0840d075942c1e845803070740c071000e150300341c0c10300340141c110710344070041003441c0100e01c00f00c0c403e80a800d6920a840440d1180e2000403240c492000c280800030660510000600030b0f5451134944c1d85045c0410700030003401079030324400d00448132140c4007210001c0c90040c0980d03815280a003001d504d59006694242d03400d1000b640001c2e1071030200c03283c86090703c100108400ca846481d014454123044403101044c013401a60040007031034824020308910030030482d40d0110342d010710104000c00800007004050103010b2507c090000598541e01583e0b18454502d41e21900c1c0d9407100746003603609a20354405450070801482c0c80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 719876672 1250 719875422 719875487
    0x60f0d021801080c040e0318010212030c07020a15080403110a050105010f050a1502070311010905030a0c230105030f0a0908040801020a020705103624171303 69
    0x114103d4440d20162409000c0e2042844290344800122207415081080f8042c142084200d020005401c1131040300c40c0665081040c1c0119401600c000c15540c1c40858100c0442c50070003c0034020304910f00102c000313a5280380c005000b180c4003a01c02024490300c142c0e50300b040b401c00c2105110b40741e0440c00030b0003296541d84404c00c070003106000c0e260245101c1900458a16824007244050504a90003407560516503114080b41d0480100700c24100084440009240d035001c0204a40c078501515007100018541a02c141d603c500c405038841e135000c1398809802c02c0341c0e01306080d40d81c000440d1516818aa03151100d040003000c0240d001095240b0201d00400c40101c1540603000603042602196601e03070316402002480c1c200701ea180ca0000301511000c031100150025002361410301e12000b0004141c3c0d8003044500421143c01940410a4981582005c800e00c20b2a4008285a6040402200c0d085080035411880001d010014000102072040d041501c0b80b800b043c000f004100d03400d0000c0100300c00306d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 719877922 1250 719876672 719876719
    0x303070b06040c0f09060f0203042d1401050d0207110d0803070809060f0c0d0f0204080a020306010e251e080105011709031b160308071e0b060f0d02 65
    0x1d0080340f0300603214200900400300564000c02c0c90b154007604510741401110321072410024601140010b000c00070700303c0c18040541c41408660440e110025400802c10f1030280301980c010a8076803482c400d018003d91b0040101c480e900344001c005a503031003017810580e01550f100d010b1107400404541c515424400030f00041d60055880350780b00002501c0b1b80000309c1e07607040c041c1e440c2c540c6c80b002ca00114004801e11002000ea6619801009c186003d405501d0341c12608a581b20603102d801c83c0d181041145000e01c06240500015083d10340b217424032802c100707074244000241d0040306a00c10840301c07005005150040e00740340c240e00326a40b074080c1504010b14234036080c4101d5012942034043e2204610300310050030f12521041c002507041c0b04035464000040b02401580c69114046c8010107102d030390250b21400083e41c0104c268039074400b403078a069129a0081c9500e80307101c641e01a0740c64009010301c658142c1246045621980140c2c688001900480c0d000320000d42c4a84402c58040ca20010611b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 719879172 1250 719877922 719877931
    0x5090613030b01080d260c07140d0801050a0b120a150e1e09010519021e12040b0609040302070302130b0402030a06140102030702060d1a10030b0901090c23090303070b 73
    0xd03000e842480070700058000f40e486c1018060120a8040012983c0e6203030310290403554011104940342170003a128042c24110006240030000700c0c4a001800a8281050080700070710080100c1858012701d0b01c2c41d44500f0300003030500103d581c1c40f04081300015100c002d040002e40890705807403102d0b0070b084140c00309c1d19090a0140b2100181d0800054040380180700d80c910a0396400894172138600c0104041009601014403562805a20b005450101c80301001500013481c044149800c2800d142c10b0818000f8401480d1034410410901000006680400d00d481100d070f0644000c4110800305140c072001e844072450261300903101100b045114246c82e0002002c58206075464410300c00c030f0200498881c841d001010703400c02c0007000b040701680095401110800410400142c945c2c40365000680304100001501d40060f0312003680325a9460030750040c034010300342d43c0c1c0200020090303000054501d40301c807124160120720510702c0703c4aa56802c000c8806680004054a6031820305140040c11140241c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 719880422 1250 719879172 719879177
    0x10506010f08010303051806160b0906090c030a08030709180c0e01030606090308030a0b1801081c09060807180b0c1b060702060a2a0b07080705090613030b01080d 71
    0x48001c0d6070140034100c07450603a03405503245440d06202e0310303c2807505401e0b8100c0d140c0100c01008081c03a1406c00c8003c50104606c242c002c5259414501000303880d040b00030f084ca01032a008603604580d581d9001991040c0ea0754441d040301e03204c2c1c1e03641005441002c85607001c003c0103648420210b108201d190b01103d00c03101d80b07483d51442d1500e600011812100d403802440c01041041c081403000c120f00d02e01459214401c4980410180032650100390388001e01c01ca21203c2200240040c0140c040030300026506582a0449200b80480d405008052000b54031880b020720054102140003640700d010300180e40002000c40300c0e00103984640c0100c80e45d014200403030300b60003420074a00100d00c0303030012000c4111005201d241001a241c08010300fa50202c0c071304505000c1c2040f441c4810840c074016107019002c104c1540d01400240e803c1814164000a00301003c0118110400c0b84280e00002594154401601d00c01c0e21007212401004c0440001e0700b0150448003400c0002900c1c18001071880c003858101d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 719881672 1250 719880422 719880437
    0x60114090a110a030b0a0312031e050601140c0a0516080c011407141011040603050c070203070e0c1c060f0b070b04080304020d0602120702010c0228030504150201050601 74
    0x5001038200c0c2c03101d810034004042d040007402c00c500d110f900320845540005015401140e500c0d600c6e1104010040030b01c401298070b0b1840800154242c3d194a0014180035405010a1900380c00091140c140031451540510b40401e0391038994000300305070600300341d01001721030190a5426020f460402c82d44a004018400c05140e41174651103241c26680c0c0c8448000d400e03040c0000c580d11000c1c1c440c08000c180c04244142d00b00114444164014031200c07100c0c00708402d036034a0621000405441c0c00904406840000b00b2000c0c0040c0c5000921004a0389003841488503501d9041c00c4031400c2c400c1c0c1401e40c50303000c81096180715446066020074121900100200903507503490400021034014528042c3c103032446030001a0100c0d8044000355440b034030040c00d5a400303a005655503000c0360841e0b070009060000350410411130f01d80901c40d45003080e02c01e0009115912810010110400301c0791501401c00115149180415008206071406880d18281c220307002c48040394001e00a0008a65050002c2c2d00c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 719882922 1250 719881672 719881681
    0x8072907060f06270906140a0f110f1905091203040509160804080c0309040e0a0201080a110702060d0e0d020607021203040803011202012a1401060b031b070506011409 73
    0x18108000c0c2441042070000c40c0341d908030380c80c40d0000e10200c0170a82c2d501d034841119040c682c041182c130910582569400003444984603004808442140b400c1d000d8004c0b00300213203000a006c62040d14006094078501c8046640d20303001c100c07414007a0b8014650030980142005058200120150050f076000361800810342c1e85a4150050300b06591142c2070103d4070481c04503010411101c020550850014101c034a01032030003020030200c0d0170b030b00c008001c2a002040e003030085607030003c526a00140420410b01401c0f0a40c00040554803840300020700c04c02d40040c02d103100c5162a00030440b83c1400700e0a61701d80c8120140060340715607007100c41e0801805040c90000c140315042e0141c0f402160041c1801d81180e00348482d40704010700422099061040d100c0440400400404c4a842203043c4000107110b1007045251290461170103852412069041940c02e11544030208180c030783c420340540c0c0f20213142c0d640c85081c901c640f04240c030141503401090b00105007500d0103a51040e000000b9030304041e241e6038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 719884172 1250 719882922 719882939
    0xb03010207080a0f0c0506180607020105010b04090b0a0e0405010e12070c06030b06070f060617010b030c06070314121905040b07050f040b12091608072907060f06 71
    0x114103005081c81d5081c410fa5000e40e100340b50258064907241410520b001e03507901c91600e40102201e64100c00700a6225049021f101070180b2508081130340020301503035041c400e91074040d0241740102c11244d6511080e8201541d12050900c004001c1044002d8076800c0070304016010301050f188840c0c1603c0340e00c20f68110700004078110381c1c98540020310910481d0a00104034040e0015455030b60703001005119070030200314140306207602d06100744c80020321146071440c034040c0081641d58001041c2d00d481c0c5282c070f1540f0003089455a681048510680c2d41c0c0030740c40c040c0d40401f880c015000310340d540811269a80034481d040640582101b003245102459402c4543d0b094607801c41c1c00034110040803000c14140c6004030081e26905554610741810b2030389600c0c034034901d500b1815492400501c1c0105101c032020090004c50820203840d2484000b030381c200414540d13188014421082c00401350f03011601c02c1d0902c0ba102c010341041d50016244c1e50555400c046029250101107403c4040c40d24000051041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 719885422 1250 719884172 719884177
    0x1b0602130807030f11060702040c09060809150a0e010905151012120c03050c030a092112080705090a060c061a131121010611120702060a0c020a0b0d0b030102 69
    0x21307403010401c0e25130202039a4130685000d0a0b50b0040e0022001e000090050b80c0d030b4050703030002d09000d9880540ca117203890030003000284c0241111816402136440c000c2c030050031005032540b100e03140d0f41c040703000c0fa04194031a005101c1038201822138001c403d00344045915402050380074440c400c00c294803198580701c0618000350300c10b500174040c0306403031a00000c044c01040c0340b46019010341095030400400c01d98841c01c50f4440c14840c800200b200c001400b140706148581c0c4002c9510040c3c80c1d4000d151030f680c4450b00c110207500d030b030103100b4a0f10000300c056204004541c5840c001514135441c1030344d00c1c0d002400004c2404070440e0494109081200f640028500c0e400548000800401c0e0448041d4502c0c0300801c6120b19076583c0c018200b111224001030081d600c0d0240000b09042000c0e903161070002007004600c10782445c903070382000072104404255101035405d00d40e0100d44040e5600c04804083e01e0000c0a010001d42200360707000009002781d81800034104843c4010818007207007100208045c202d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 719886672 1250 719885422 719885429
    0x111121216030c0f0f020c060d0e0615062d0406031a0f0a05040903050705070f030201020f0d0f110f060a1b02010b0a060c0c0f0b072018071b0602130807 67
    0x140494101303040355200e14aa804290500c1c01540c06088070b00012031415802110038140c13454803487c42500c9000100103030ba502c6403201c40b2100c948904500020b101c1c3c07182640c0041030f50061142030040d848540820300381c80f1041e24842c0c0d81c5075607450380900508000b03024000102d5414103000f40c18140401c80d800b004800401c405490341c00e04040000501e5106020780400074240b04407000074030100a0003014114030005004800d1461000916208092a0300c0002d83c22400c0c1c914001d41d0004603880c0c102459040403012105030441a42c40e003800c030360b03d0b12010710030310007404244401c1d50310060803114640ba4100d102c1e0742441c0b080e8262005000e529400102c500300401c16a8410000340180360302c02c42e29280b1107682d42403000c2450702c540d00b246002504c0062070000300a034403540e6008401034010000c11001a410000e0302c1400304503066400d8800c0f0346d0000340000e100308040015540039012003484480d407070614030001e401c20072840d075022421050209400c17400180e03c1044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 719887922 1250 719886672 719886677
    0xb1905010b04140607020a03291320010c0b0a181a01060504080706030b0117070809100e03030a0b031203041505010f150e2d0a060806061c0207020d080903011a0f0111121216030c 78
    0x40700aa54ee0b101800340020701d41c010090ba18030840c080181240d03801180300340030f03240001d102d00c42014080100b40042e40200305215082000b00704045010038807408455007800c0000c1d4021085005884582c4100d603144020542c40702040002034101c01c009001d203003071108550076400000603803001c560384545659040d6100b440028220307070840e00030452082001d0b082e505031344c4c038542c400000c94200790703012218090088e40c5162401d0003441580d005003100700d0078082ea185494030108014514010f4401000441c505c03844082c1c03503182c1140c1d0394683d44000381c18141c10101d400080c95182a16545c0b01d10303903a01e00042c04c0c0d031240e030b0500d028110040c81113142c641800d030306c400b0b0608402685d1351413a4091140c00c01596500b50180c081f00d0044001c5903403440c01404250848000302c83c00a01160061000700e00c0751500d04000c100c0382e600b802d0040010806680441c60308240380002c2d03450000001d4800341002c0c1d56110707640114031030f828114940341ca0340e10a600355031203c22540d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 719889172 1250 719887922 719887937
    0x3080a0513110d0803072a0803010e04030c050f070518090d2d03050114030105041e0501110301061809180b1905010b04140607020a0329132001 63
    0x800e508400008003100c2c01042080c40321403950b58201c1a0300200c2c0c2d40804540083c0d240308850340f40c4882030144000c2c41d8440000d0680903a00c003080c0c0e00060044214243e00100003604050151140c4800305130008211070400c0500070300242c0e121507500030741e80150b100111402d020100100c3c01c07801441050058603100c0241c0300d0407540c00c1c4000c0c0c0c49601900014020ba00c03800c6102c242034110340b11569000c1803079810b100c0c070340080a440c83c140c980260f01d4042004080740c1b110705441c0c01181060842c03904402c1c0ca04207180506064050a161070728000000610640c209113244161000d6aa545411a44d200108011603003010f407080c240945c1d000c680c1c030015200100171588070202460b107000f2501d82516660490f142600003460310140000c0910100c080c100c01d0700701005040318050b00e012500d5000c207201c0c60061000402070201ca80541c080f4250b5402912400c0c100140070201c90302d00010340c451510003d4405880a04103111251081d080d00c1e16405090300f8107131507146 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 719890422 1250 719889172 719889211
    0x40e0606060a051c06050a081c0e0406030602040e1803120a050711011503020321040b07140a110a09180b04060608030c150106022a040b0a0b0703080a05 67
    0x1480c0e0b000d4101181080341c00c0024a4801035035000b05181120070400004426050405101c416806c0380c00c4000283c0c0054444814512441586c111b020074a203400308581c2228408240039003c1c68000401c401d00210740484c40751001e156a52040c00d10441125905a03101c01841e104c1c8034000514600c0306041001072022034140d0000e03a00412a454000800a8101030040c00c48503645000c1d1420203100d0001c00075440e0400c42101d07100c0d42420103603050011002000c030248a240b283d000300440c0850304206000c2d140c4452400341c118a0255241200c840c6004522410b8010103544980d984e81b80109a920f603d206140100c18504001004121035072030f5480b02c2c1c1802082164201c4d210b0b03002140d440c0c000d00c00303401d001010300001c05103031801c0c0e01e4001202e00160010011940a4400400060b0001c001c50040d03001400c2c940c2848030318000810040c140c050426a04030190100015401c900d0038010f10f4218020790700e00c100d6449105000c03003038071015078003450000c901c040c188 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 719891672 1250 719890422 719890429
    0x501241d040221060717013512040810051603021c06060203070b0f041115040b072a030308160504080a11010207061b080c19150605040e0606 62
    0x81d0028002403450040001c111901c0034108001041d81c0103d0304400f042c80b2000b5042144c0c0d001c002c0c60384c1c285030309940c1000d0800d883c05507451107404c8254020003000f08050050202c4a000e80c00150645c1d129091148aa4070181c2c420720510803240300b44941c2c118040042d110311030203905a03881036008136030b48401c00c4000c2c0d0041100c4089a0524140320702c8404000e120302c1d00285803a401440d280c1a103410071013502d1500804082e00891058104000140c140650612012080b0b540100042c3d80c2c440030819800746d40c200d68803110000487c24188541325900d0395043c0c0303030401400356804100c5c008401d51001c030303c8001c0c081031454000c5101001c7e88004640c4484c0185400781c281907a8900300e030300c0c2003100141502d030f01107050101d21055034180080c4000c1e00581c14081507503401c03122101282d800e80702d00030345030703034808202e080801200b072002c2d1501d0520100c400007115603505120900c440d81c0d0400c1400149000400140d600f480d0040b50407030746c060030140140b1703600c15060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 719892922 1250 719891672 719891729
    0x60a0f030309051003140106030c03062103030507020f060f040209151302090612130203011d031c0924050612030906090402070f0b040b0606031909080405030703050124 74
    0xa000915440d400038803d40007411a01031f00030b0040d80e4001c981e40802c1200503003200c4864001c01840d01014052200d412504038140c641c81d41d00d840c0c0002c40b603448910881c00c05000c8900315015018070818810000b10324006036004c0c2d40200c0e02c00034a40c841c01500c0b140c588040700f45a03005607010101101d50285070b03000c2c0c500001e0141c4668940102002e1000d4400d00845d49881d000c0c600300c03542001c0d07040c00d2180094142c50500303801c00702d60040306c91942e68007c040c1d820000082c410482202e102c07580e0440b80456070f0010307400300040d242c8041d03c9035a090003080301e41410310300070000b0881d1605003810014034012a01452608190a080c0b040b0340c1d101802094102d0b0b0204134000010700100e0004228500810090080d41414074203200070210280110703114820a005005401150940c031491000e80321030f0008000c0101c1c64407031001d010f01d5100c5641801802000024044190416003025481902d0b00c1490040b0050070001100e140c05000a0400c0b11000d040d0001c4c0e80141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 719894172 1250 719892922 719892949
    0x90708041101080c0c0d052109070e06060d09081207030b0a0e10170f100b011403040c23270711070f0f0e070c08030a09110603040b060a0f03030905 65
    0x104c06142c01451001c0524000508401c00c0004800290040704000c9100041d0154150203100e00c2403414a00d19850b074940c010b0042c07903113503201c00c17010a04d6980c0c0c45040701c06d41d0202040074016402c00e0308251025070001402c1c003d06d101403400181d0014440d1260120919006051002c280d040c8103506a02c020010400b0f0912020205d0100e1034221020301e1000b00c102d03003402440701e0909501307003c0c100784502140d00002400c1004d002d0440e82c1201d8200c1c0410011418580c883c0c0d00e0341000315014402d944a40f0848610300000b00003500032041405c000807094501c444200c44c01c9411005009000c401452089078942c0411412031040d403213510005400f400b203a40d095110b54551000c0f1059030b00038138200c120703880c040001d0054400c0040c1d106009041c0310410414039125151103100c028403a0311181d9039684808100020094400e000c141d000c0c1c401c544a103403514084c007100b4000d9902521030100040c00040701801028400152a81030750f80140c607900c1c0c90107020010440c0309 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 719895422 1250 719894172 719894191
    0xd09020406090e211303030c034a0d0605070c1202031c020a0e0103020306010c0c0e010801110f160f210809030901052a070f0509070804110108 63
    0x4000103400e040b94011000c1842680d0702500c1101004030301ca81400070105805030aa810a0240c00188811090311070b003200d82509082c8a02c003068902292285060381c26608401012098032011a01c110031003480b45103825250b400c0480380c95040e030031000208060039030048410402134002501c0790810f0741c21032003d0400201c0300d14a590b03107140c004580c181c8072005034004284041c0c041304500749941c603000c002504515090003480003c12075594402d4883c1415000804201c40303902c1403aa4200840c1c014070028032264840030030890580003031103840210b6007460315003e02403041328100c0b8406003a8542261901c06451020840801d03a1141540c000044040d240003040d509d2011614034156403044642010f01180041c1036050050710102050b4010711610600c0d9030018211150b006403110652001c81c5103d1a5058903038042c00c00004a0142220000745a60008018000e640003203802c902d0641d04c0d60380440300900b0869025261042002d20107682d54003070450f15030801a1310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 719896672 1250 719895422 719895431
    0x1b060306060c01020f0c0102070b0a06080c041505041d12042706090f02120f1017120a09060f050f0a081e091615020d050d0e0a060c1d060d090204 64
    0x81c445c1d40300c1ca4010b901031100c03694000a401c020004061040c9600c441c0e600401c0142c107003000400c41c1c0d1070424183c06400f0319620110b001820340114100700c01080003c1080c007948c02d12200007404070f0700c05103683c8110700c652403076010140460016941074a44040305010410b40310b00402e40404009030f40a03181583d03c02011500611070f000d200e1801c00c01080c05030355071403c00c10440e09a00300604142d82594044140140140e83c4500c402c03c8507140224038103809090040d450070b0134070305040c0d0809001c00040c1025400d0b000290031080b1513254440c07ca5400e0345070f900f0b0320300d8418608000c403e08010014142540c8c0500d4120b03400c4110f40c544000d00d084110300152000700141c0d09464140e100404c1480300d110860061805040080ea085025481707911010355a80c0e088084502404030200c0d4440505e1100d510556000644104070f489100a9060010040200240320000643e003488090321546007050034a001d0800a480145400030400d41a0020140110220384c859140e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 719897922 1250 719896672 719896687
    0xe060d060801151401360807030302010516030203010605121f0b27031e0a121d032b050f0408031926131a07021b060306060c0102 57
    0x34440c940c03c0c00380c0e01d1a09080c0d182000c000f0746020071900156810040449440900128413540e40e03040c14842d14503036242d401c00490b01c4c009564140d00800d4451007600c50000c01d2642c150002170207034030204c40046507005148000c906a1009004040118034100400e01034443c0050a13254851000012031000d600800c0400042c880e0591105030710900200e80c80071080c1004400c41e0142031007070f03000c1a41c040442e02003034481c10304080d080c00ca919010002d06010b0414012120482d500626120188020b09006084c0c40105011700001215400541040e8200007076509d01e021880d041c406052030b040300c54898000801c0341e40504103d41440056001c048510141024007180b0011755280d0308120b0f01c5004202940d03d0100402ca83c451102403a02c11040104005036105031340700501d513840e050821047c0c0c2d800e040081c018404801c1384650000c04d80401c90144845a084e40c2641003601510b02d031040409801c0b41d4080d01c00c0000c039400e8600003004210b001031310000541068070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 719899172 1250 719897922 719897939
    0xa05040905100515070c0308090103062601112a19032309100804050c0a0303030518070602030922050f1905070806010309020414181c0e060d06 63
    0x6a42c02d4040004038071040c041803074010104003030580c12505080c10106943c441004002092001500c03000c0009110011079210f034020070090002d102030782c001030414480d01c851105200c01c1000065103407543c0da1100d400f482c0219000808090cc0803110640c4c01c0811010344060240c048030644502680d680c88143c0041140a0b000d00070385a40641d02d44404900d41e102c82d00120101128004005081056582d90564504d00f0117903c1c00d00a156114034003545004018240b140d0300c804413450010425030302d074111903c2007903127034030038080700303003030001c000d99551041c080c0e0000750f00306010001c0d5a00307000b110b01c0000f0800c426461001d0fa51411807500b252029110300ea03061020204120b070601411102d402d0410405100700f00311719290340000d14003900078121604040c0c461445406641d15508a000d00900d07001e00040b441c184100580d2101e0200490f4000381d00909003a914074101d0004208121039564555a01481c807050800ac410391105000b00521640c0d104041440c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719900422 1250 719899172 719899181
    0x30a060f0b0d06080118031206050d0c031103011b0f0507021002060708090c060d111b030a110c0d030f11100b0406090e1510051e01030501060804050604080a050409 72
    0x44101c40e501c0da100c69440940c010340320103420802e2142c0c10861742049503640401c0205180c4d4051900300d1200903c0410500a00800d600c4a644004013150344028055203010f10422681308040c0b020300d01c1d401c0c4040c18240d1f100300001c840340b0651848001206805048040c0d40c40030380340341aa00e8032000c3e40c000390340310801e40340b805e0041c4c0c440402c07c2480341c1c210316241c1d00850301e000102010001000010305500c16040407030f490035103840b0028050000346c0b0540d00901c0010484000419611150b03583c0c0780c10072140c88000821144012103c41c2001c00e40301c0c0f0500000d4110b0400040c913072815201804000d01e400200080d101003084440d805011440d48090100004910b0590240400c400c0d40d116412410010345000445204400700140d01e5807008240122074110783c0d00c0303078413240c1003156541c0101d41100d05180300f0001c3c0529404031130300d000c400741c0302002240d8940008442c01d03801120000c100d90f1002000c1004130f090b00c0c01900d070500180c9881482c3c65161300c07101007900c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719901672 1250 719900422 719900429
    0xd080f092b1803121209120e130605030304030f110607030c050607090b091201020d0e012703170a150e070206010b161e17070c0f030b0a02030a060f 65
    0x211070041c45081c099601c01408100c0c2848003007014219419a00c403820b41c010402500014003400003052840544560002c540040e049462040b00c01c0d00300c0c102505444058020314403a0b5444100301180e00b8241c070039041a0342010300290b040600715076943c40b10707145007802550780340d07556001644146d94100041590300d10039510b036022000d107480c00b10b14254000c3d00340d0081c01b4085409110040c0c828040e240b420700200c03203c5500f0b8580602480c0248518100006a2820700004c00088481500810a011085034100d41a403004185c4e4140c0b450040c480280014105808400761811102c200c1d600511400c800195a0300212510304070070410b07a0101c011a0201c00400c0b00058050040714010052161001e103020f03c002c07038041c0b140301007010050141e44142d100d10181c011400803401c4003070f4042e405281541e0808942c0c3d006810103441240c1030380f07043c200801d011000e141c2c0780d4210b90740008150515103402d100e21029400090183d8000c81c2d44200000e130f9160410040c0006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719902922 1250 719901672 719901733
    0x1605160f090e0703230d0e0906040c21020a020616052a0304090501090b030f1e0f01020a0c3014070c090e0d1e030c051308100e0d080f09 60
    0x10b1600000007070f41406c548204010074030040058040b06620b0350181660300040840d000912a1000301c030940704010300030b049410f902181035150076405201c0d4000c010100e03107602100c06940ea5540c002034410780351500400060000d01111900281c03118820180540106103041080010410145190015805500070b00c0d210001041151041c0c820302242c00e006038080c00580c001c007003075503641d80c010a00d88520100d207480c040071102c90610000300c038120100c00a40d520149402c000340f24846c8860709480400e8020004921015041c00d003242000b06a10004084d9044640603a000208000c92804505042280400088880c03043c40082c03e9420400141d102404486525010b1b1001c5410180001c0f60034003102400045944070001d045443c01103104d10722440c00300e6190081d01c0180700000c01400000c1010100440e0070442e01280070001c00041719003180c682d0b0f840005e0380d07502c1c01190b0240086908810b2500c040d0750301050201c00c4464a13508030b21011150f040542c510410b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719904172 1250 719902922 719902973
    0xd09173c0a0c14060a0f09170a020c0a0305060105100206011410050c060916150210020702060403020a080616050306100c021c080306090f090d03020706060b1605160f090e0703 77
    0x1141e51140c1b1030b41032800c2c1011070800040305035680d035069802108001d21032402d0f000c00c40c800700500c2007080d0407182c5405081180829500d28107181d56003002c0c05441d00c5000340c1101041c0072071001601c0c5040741d4490240380300400044e814040c0051800804200b0047c040260f518803807030412079a401a100d210003411941c021642000007100c098004044180e105000e100e00c00b54001580a540310046800595800c1e01d440050014442c7d640001d4000c150030304001100c3d0004910745101e84241805050010f2000b5011075240c0300403100e4990112100180c1d0036118415408076061502c040c2c1485060900e4480801e00303107000301e408131150f030030000c05c1241d94200400c41035042482070384034085a090101e0f52a88030040e20852400305a804a64003090105d250441c200900000c005031385e41da2400034080c03000c482d06000541d410f00c101d0754990000d150110b8445d089440c4d02d40c0c0001c0450500c484040649400314202c42d092003210804008505901003403030781a8a400144031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719905422 1250 719904172 719904181
    0x1050a08070f1e0f180803091c020d0c231e03010f112a070614120a0516080f01090207030e0402190908010908030c0d09173c0a0c1406 59
    0x85c8603007000c0c4030f42601070000420410000d940002a9201010304031042d5081034203030000112a4240380c07801039804088854030b0401c0c0007001e41140c0654040c1c1d140e000061010040e01003141581440c5903400c80040640800410320002e5010f0803150300500200e00d04580f0031a4105444402c1002804403400151141c44412981c000d00039003411200d04040c1011660083c9458101600c581d4041c0107030301a051501c0190300d4101c03403603000d8074120f119050602195900041504403980d44030340c2c00b01d030040b0042034002c142c0c451042c8600d101d41c1541d0780c20500d000c4065000743c40c0032400d001a40744c00c152a80d5480c0050450180701729070280201581d440010001241c5a00221050b49002580c1c004181101308803a4046000d03c10940e0310b0300c012030341e400242a80300002d0407410307116401d0401c410844006000128000041c0a500d440016044614501001c0c00f050708042500022018002d00350191440021a003440316030b512a58407071000001e5840c003482c1054100c0d40400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719906672 1250 719905422 719905427
    0x30e0d030f1101140106030b03030c0a0609060515092d010b03061f020703060c0e1905190501022d030304050601030302010f090213110d0e0a060b01050a08070f1e0f 72
    0x6446241410340207211801d1040f240716503031801070003910b04141c4c4400580d02305480070003c442008491800300d542e240642c0c20810014840b041003254a241010040341c21310158000e06d2500002c01440703d9221b80f981c42c5601722400324101c0790030300c4415040c1c8404c80140c0310010f0070300810b8200c1e401da9072460040d0401041c41280d1030b60014900400450040d26507001401009a81e40300e44006541181c040b0152031080d001d20000d1381c40b8504032030000c0d503050048a65021100141d46140e04031418075525100b50300f00e0b00803a801a448281031545d841c07000c1844481e28580301d141241d00700a607205690869000300d03002d41d01da90000004208143c0e092107000441d00d42d204080000d250503130700059607129040c031001a1035841c1c201000040074000100c4034000303101030301041500c030030f480981d8491044000a55816151465004203540114100c4d81200302e19aa40c64041e5200c076020783c0d203007144d0f250354010008801c1901003040405600842c6050403511855030009110703000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719907922 1250 719906672 719906687
    0x2701090f0825030b040f02041b0c20030d0c0c0504020f0a1205060d03200105091b061206060a020708030a080a230117011b1e080f01050d030e0d030f 65
    0x90500c002d48440100041243c001e201070304554000d2001d0740400701400041c001d465424140e20380340c5004001c2055154220050800c214414602d6a1101c1440d9a0141d449411443ca0704d416400581c2e500b120f040c400d0603c801c00030b1146808003030b00780d2558003140481c0c102c641640d240ca140064140e0016401c0002d0655040c42001c00313025038035140d404a0190284018018140648051400e58410354141511080c40410008111601d822b9418941d182d040c03080c2c0094004111001c3d040302c0c01d2600032110106843d0032a03590075202e80d024001d642e400020910118040c030040810a082c0c188020a4046895070380e030302d880d040148010701110000305040000303a801141401001859599103411038640054990108015034002c5000d0411003602010158015288107085600851464603400800c514032180002061040d500c0003004d846480c9100358900c010001464240025030b000c1d40320303181200f1800502408980da1414124040340030680c0d081e0340204041d840000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719909172 1250 719907922 719907973
    0x50a050d18081903120c090513060803041a04030812161e0e0d14030304030206101a03100306021303050d0c1e0212060108011407052701090f08 63
    0x120748015514101c0384030354038901c100140d10b42d5242c240b00c18040c10b006204804040c00c50401c207202000280d0b41c01801c0625500407184104000c3e041e0000d41002c0d48611415140000001c616043c02c10304680200490940403184824007000044002000100605010000403c900c1c00c14104002500030445900c00d00c0790812451803100002c51040c1007007030a80113020b00b00f25915403207080c0415021130009001502001d060218003455510002c01140f25034069800d90754191584000c02c81c801000b0302c074660301840c2d42c1442090080004000b5074010400340280c1c100785580e9601d030030583e0003801c2c0d80d010b0407560039000c01c20310a080c0045041010f0510700f03a0744100351030384c40004800c44d0148600e0242d20045e000703001c5441307061410700f65520102c1110715542c1c1d40e0009501138040441507494964003940411101805401901c2c0902e001122103120480741c15540b900441c2c0d042c1d0b14a0411441e244006004112905004090965a0007a102c1804072a6529011803107800b0f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719910422 1250 719909172 719909207
    0x1005040c051203030406091401020711120f150703150923060a030b090c06031006030b150a05032a070507240c03030b03060f0601080f1b07020607050a050d 68
    0x54601c11903400c080700f1685c0c001c0c0e01030700004201d0340a081c06038441c1c400801d450302540c400101202801a90042c1040320a001c8821100020100002d1901c8143e5a19428200c3e441550302c02600e10000c811640c4c0702c482483c0c0001c0d00c4078030540d102c2c08190554400c2c0307100ca55882540140f54404085400403091070360460426041500c08501500d001c0d12002d485183c1c0180031408444081c0100303000039200030006030300c0742002103120426214610690010914200f2050000d042c0074091049180c446c030380301420701aa04005443c654402000444850080c0f00d1640e43c0181102d55095049000c0d400706031591072903d003030740c50407a0f550461495514980c0320343e6000b040c07001c0000744800322440c1200c002e034491b18098019010381c030815585400f61804001124201403419071249500742c0c0d0f010741585680684d1280c0070010b40300304064030b01c0d15400c2044007600c680100a850710141c007444c9009a5911110f0074941500e20881d400e42066015030304d03081c1e1200340356207a5107008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719911672 1250 719910422 719910439
    0x2010c020606031b0118090e0d020c030a0609031106070807020d0e31020315100c02030a0b0705071502030a05070504080709200a11060a020a1709030c1005040c05 71
    0x298000f903611245441c0c40019900c0407a01142d8591188000748032001c403103560f541001d512441c04202401d8440054442481581204613040d440010000c01c140e0028000e0464848151600405403151080035002e1007400d500d41420342c032041004900c10034081da20140315044c000002070170003800789119401c1200402c18102d0640c1c62502c410760b0312800b2810100311030666002003d0300050075103820a841c0c03000c8204055000e03030243e0201e0404080b262824030071118002a01c81c02d0200c41c000c1c4d0035501240c40b02d8002085c1004e031a03000f14a90400c1d508000840e0741d8045021002e411914000d034000c8240545040745024081d00002c0c242400b03410141002c402030b40e2451240b2030a603c07151a411071440008034a4050f83c4600242d95019070355007031140300a4210b020540b0714148912070140000c1c00540b10740b00b5699000140c0c1d44402002d401c00300243c5115030302401c001c0240c0400c11808440030410051a1303100b01d030401c000b03e5107161074180162406c10503403000c0e0041e00c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719912922 1250 719911672 719911681
    0xb0315071e051606151502070e0114090702031b030d050702070602031e04170d0e0a12140118032a03050d0c030902060a030f15030302071206020d09030f02010c0206 72
    0x240680341030540f010f107030740360540843c180307480503004000481094442c450300200d40b00301e2103280f1901c800803a40072140711382d0b500c01d0001c0b4030f10390034411804035010104c4028a1883c221b142d0540140051048a09140c40c200201701048841760580030907a000040000714860a8060958020110300142454900d04040a91203101d01c0d001d100d0052842c202e100c161506031004d44000c2c1ca90801441e001e0301100c00e9036540ca151041c907120110700250700f03108482c5880c014400030b540721711a0030341e03c0421581e1a01e140c06441c0c034a101c000c0d520380000500180322140e08010103400f0340d83c0c5403c213801d81a110850051011006c2191001250314000420340240c00c41d1017080900c000040c031404070401c00c400800481200a6101d000058505201d0b5415000905560a072030300401c18010000181e4a2014517440024096001007504008420310502d0101009004543c0903280408048144048a5010302c00710042502040b8200589509228841102c0a00c0c0010405802d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719914172 1250 719912922 719912927
    0x60b0408061509130c180203010305010e01060305030901050f091903031d0102031206030a02030d031d0c0a120c030507030305030103031119083103050f03120a09060b0315071e 77
    0x200188441c021041580700901040307005d00b6580002d191040c1e02200310246603001c10f0195001b807206454543c00c0403450035284906104542c01c50354003500071490312400000641e06a04000c00c8a03960080c1480000c0c0c013078998600e0000c00f68004040c10300182d00750b25016200100300c40c007108107800300c0705440d00683d8001007200e10140a0102c40042e6a48610001745888860480250140220391040c424070380c154000600700141c240640701c40310350a01100383c2d03643c01151405c0c3c3c03100d500c8008201c1d20762a8885020300d1406000c40c3c10b03005450751142c0c1c1c9840d0480c1c0c000c07000a840000100141540302421062404803c0040c0020842c0251000050002c3c0300e0050280c2d440080d410081503200c007008002c41c2446408014521040600c2050800c4503200a403924001ca0240e2810010040107c50501d11200c0e1580e42c41c3d11801d450b000100044c102c00c9030119a90340721100559000c0008410703880b407150340c0032254641214018030030380140042c80785140000d824400c1468 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719915422 1250 719914172 719914189
    0x7050304091b050d0f06080f0607140c070312030e07060c06060603020301120b0a0f151412060a1e060b07170306010c03030902030312040c0e100b030103111201060b04080615 76
    0x200c0f4004d01049152500310b0310f4008150b1540081418440c00303201e241e88401c003140040c4151540e0711290064001400b00212a01c603c044000a90300306450a00010340454008820072100d4500041c1d269031b108140c4e4600703409904010042500c507108038007001468014007029150b10b240940c115403506514690056a1140041c07150000200149001240c0c3d4028500e02c00490002d012032844012119042c03c29800740101100c00450701e0041414524220412207611200420b8035648190204008100e0329044070501c040b144440b00011000e402120041c2290b44105580c80c03c040c50041a22403160b500450040d10a1040000c00e0b81c10851081030b96416080100307000b071640c0f0010307003148036107a4055012007a1b0020302c8244101c1400c0704065818045a030321385500d400340c0701d10860320b5601c50b00d00c002c24200014400669490301c0c0300c0612801408210300302d03510350811402e503042ea8000401420001c07900300300c0d0748410000c40340c00020b002a0710b103c61505401041c0c2c0324 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719916672 1250 719915422 719915437
    0x5090f061c050c0406110d050307080c040504020d0b011209110631031505060f131409010b0f0613060e060f0a0309210f110309030307050304091b05 65
    0x10000400c5800607034455080312480240c18140400052401e414422402e81140c0107880000d101c034120550f484000289480b1060780548030395065545400046600302d0006102d86003020050000081d5500d50b0300180101242411000c41c1080010000421540c401042d503030200d420000a0700110300004200b030000001502c8440d40c0e5000c0c40022a00c00d001c001811424613580c100244c0320300c60000342102a02c0c0301e840000c400c1002802680b040c1c038400c0e502990310941d42035848540e441c00b101035000c4c85a0208001c240084403d101c4840c0480858182007140d4440c800c070700c0c5030300d8043d0b9a14001c00f01258000d05010300d100b640101105c85014250500c02e5150213070700950b0b03030f003010303580728075a44840310769501416000100544200b03171003120079016660031010100b4402c01c0341124020150345040340703075038603140c1102c00c451614070880d1180401c02c103200b2981c40074002060028003500042d5070b900d1070000d00004503040d4000038030031900e42d803d010340d80c16885412141d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719917922 1250 719916672 719916679
    0x40f1a1302120a020d030333060e27041a04051f1a150c16030309150807120b310b060307030b0f040207030c020901060306060e0603090f0d050c0c0105090f 68
    0x141c01910001d4816200d2007020307610814080070811401a14a223444810f840c0a40d07100c4050007001c805002d01162003105904071100f82c400c254003180c41c044a0310b5849805020800d010280ca4420281110015903054036140c000c80c112000901ca40900718442c50814001046603442c2c071a500001c1e44001002071b481000d282c641d1035018038400043c1d581c0b02481c40152203900c180c1c0280610015030303604c02103020608042c0c00180b40300b100c207842280a1916203400880d0350740c40d8012292802c0c0d002c1140c1c80c15507200d843c0811a200c0c0310306010748a07814400601204614013000302d44a03154200040314900f40300c803001098449800b900d421414500300429500003050000302118041e02d04941c00c64030210300a800d040d806035010940600964106400c0d988a45046081c0e035001d008000100b04400360b0400070f8104000159441640001a02e601d0380c01c4052190510540b8403195000030b0b400318640210540501522020038000d0070110701d40304440003c14070707058214402030310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719919172 1250 719917922 719917931
    0x30b180c21100509270615011403060607030c20010809010203090a0209090a1a191415060c1902190f2310020304080c0402070b040f1a1302120a020d0303 67
    0x440c09002c5e805041110007204046900510500440d03514003040f183d02c5c1c01440c40001c84411540106c82030201ca0380407000c2c5e1072650341c1340310500c451580f003803804904000602450002141e40783d40728981d26142421001c0c036540c00c400c001000c082c005440301e941030b40b04105000c440080080c08040c2c5a0341540d4458041d903c461101d824041c2e1200c010b071002c07640d01c85c80d42c48a002c803858503101d00c0385181c1c06030984145c5040f031801c4a1780754650044400b00800459803072004101c005441ea02c0003407081d4907007408004c0c460f007003203074101002e1903441800e06414214504902e0200075188941c180000707849c606818450303d03901034841d072011801c2e072000181c402c90200340164031111016029a090340036aa4000b07551398410f00c241e118034012074800d01120b2820b402254001504020b800b919900c483d282c1503242d0b2030700c0b202100c0011626104e0041441421030241c410185110403c1d10081c49006200c1840301094011045401090807600160356000709010400d030035150016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719920422 1250 719919172 719919181
    0x10932060f0307020105041e030f050f0f0705071d1902300a0e01020a05071e050d08090607080c0d1a13020c121306030b180c21100509 59
    0x240d45100e41924445601400020480070640540200c0d0065200310001001342c905800c40b40002c1240c800d00400040040103c040307064031400282c01aa01031010941c030b0001c10b0022700b480c030350114200704d82c1504012410403c181c080c5406c1c0b20810441c144c4180700b490f040d5810144040c0544c2c1d181c860903400300b185034130140e030501c40c280c1c0c01406511009044224072141030001c8007c58829940f182080c1407850009010b0090380c240c0312880d200d0f9410a242075450f034000c2c629103031031095141c24162146002c528204a402d40282044c0c07954076803401e01400c0103080040c001c040c1c00c00e00c021803042c440351501c5a41214080d544560000070510340311030a0703490280003910f0703480c1e22241c5000812039200060340103100d1301400008641e2086407050701c000d454084c0c00440300c680d403040d0740e003003201c0307800b80c1c00084a0f08002490310340307149070708840c81d440ca0800350380040d2074440105440240d14109055441448202c0e1503c504a20b082d03545242c54101e14020b0390f00030b05a840205 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719921672 1250 719920422 719920429
    0x10e031c09030213140a021312020d0b070c2a090e0a080f0a080114030d08040303020c030a09140a0b0d0c11030a2a020d06180c0f05010932 61
    0x1c20155900810340c1c81e5a0008142d1036010b006024221006070742c00c44007040e00d1408902c212040c02500c0c001c5034034620714202000c818014603890981c0c1000925015100140d120301c03081d4030076032158441d850312101c44d040080010001001c1c0c10f400110007400e0810481e41c120f4072000320f40a9082c08100002e011140c3c038207052092900410703401010591840101c15440545409010742ea41c07036106aa0f143c442d40504201c03110915019004154900c840174031600306554041d000e030401500e4001c01c08081851503010303800d40b9001030240c00c401d10001451081c030390700189086403a07450302805d020280c10f0510803032080c01c80d183e660340b80b000300303450041001d40c2a080c0020141d90b1107106111014202000440010701000a4014503003095031203440001c1e5029005040d01501030210f1380d400d030080403200d5042c0041c62b00d5040620004039a040c105014001c0b040700e0080f068981000503000c03041c40c2c2c108001300300000710741c42031030021840000e01c803000d0940d141c0300c85810700010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719922922 1250 719921672 719921687
    0x24010e0c0c0a0b19090209040b042117010b0307021c020a05010f201905090a33020120070305040f03050d1403070e0d1106041d0105010e031c 62
    0x2405060151400030301c1400301d01040648610307103442d15255502c020603e003001700c950081000b07510561800108020980103a0040d034020310400c80e55007400540070052012000801c07141c400100d108401c205103d10380d5107101d004201e116a4036066040c43d0704041d41310541010941e040d028942100742c44244200018a0743d02e4101c0003c000c0c0503590071414000d00120340310540740350020403554203082c000104a50560b0000901c0544a01324000200c5055101001e9981e0015442c1e01c003060603e5840306000404055087c405c2040e1468110000403c0c0720b041c00c6010f691420005480800c1e0f4100640d44101030005803546c0c4a1a5160a13122402190030030703130031400320500100c100540016203070309101040c0c88564001012401040c110b210854582c8009a8000b040040c51f04049001d5250940329004d130745000720b80100442d1103900715030300c40303200c003131040e19040b20001020200d68003501081c64001902401e501c042540c80340304a80480c03075a0310320121184460312403c034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719924172 1250 719922922 719922937
    0x1c1b0c05010f05212a07020315090703060b21060601030e0c01020717160b04030303050f01120609030e03030d09020f09090d0f021011030405160503060a1116120224010e0c 75
    0x458074a0700924280d03e05058006040480c064851035180400145145403150f20980c202c60080c444180cc40d42c46ca005003000550107500082a00e400c01485c0c0701200115091004c607000401c01e1389800000101074810306c0c4000040c03600300044c10744150360301042007805d640f070007141c1c1008441c522404a16042109001001901055001013070200c404801041103d001e940c0900c016102d120302c8115882c420b11440209440310b01c02c17200080c0700c1e504002036041c002d040c001c20508440700401c2c2103901c0030150010455842d145e070070031031500500c1c0c881d0304c00302a00c0d40c00c02072a0500020b5590072402c0d070b940e003e2100c4d03090307402119413003080211502490901c080c003280003204884841030300300355411a0346010305244804840703000c1000e0300c11250010300038009070302d58420160080920401410100f001000183c0b008010000642c00c0c00740b007070700c44102240311250003c0c2450f000d403c1005218260014015840950001d05c86c1560360003242c141761916030205076200b521680d01d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719925422 1250 719924172 719924221
    0x616030203040302030f0c100504120314092e090305030703231903050601020f07090f091a040302010e0a0b070e1f030b040b121c1b0c05010f0521 64
    0x11481c200c1c440d007c503005ca8015000e0318120441c8101c4102501d07135003c0c50017400f400d01a4510444017107071203440381c1000001c18268442c42d00c040000424a0019a03007500e14403503903140444aa05281c2148503118100316190603030001d81941d80c0d8648078440c484001e01002940102c826400329222070b804580850018210f6941121000d902140c0e4540148030003c00c1c44c05000075540c1d400840c520008058042c0030f000141e0400403000b005205800318881100c1d65651041d0001c0c90b0151011528101d10003254401c1c03800f40360003825a030020b00c94403600c3d00303c0f07034164000070380180256030005e105041c141c48807981e076000b00742003800d042880c82c0908a094548605641c15900c440f007444000d84080c80803071584018008401025280c01c00c02e0b9002d001c00e545083da0100c1030510b02c1d0312610b820420f400001e060107202d0083c0d8070f0156007190010808200c29a00704442030406410342c20454186081c029442403404c5c00b041d00c0a04030340c00f03240012008416030401c82091801075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719926672 1250 719925422 719925433
    0x100e0102060a050c1c0b0301050115080a0c021906091e030507080d23041a06010210021308010608030d050a05010b0702090403121b090b040f260712021e061603020304030203 76
    0x10785d904050035007050058001d510f840c0001c01c405000d48058400500300d0307140d15110781c503000080e01c020030740c500008086000b815980b1401c01492210030341e07000d014501c00b084d000f140d41007030000c0541103144a80b60003100321081002039040402d541081d500035940c251190440d60144000e045044003010741d80082c00010b140454020002c280a1800341e40494405158041d2031a44060140d85490160f0f000346842c090104064000302080c00020583c1c101059031005000e0035036046030414002030f04041100b03d0b011119200e0740344e21a100711800d0026515050b500b141d039114081010340107800e030034005410b0500580b00c02600e408880400c000720710b540c640d000e2141c041c0000b16030004040d0750001a03a84100350541e400d844e41c80500b5182903207000d940851a0b00c540c0e203c424040d11950444250301c5040c800000201642286d030510150280b041001c0c0951201e4241c0c400e5402d9034094030147c4490003a61b1030300202080000e1f401d00141026451070013130b0b610007985032049 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719927922 1250 719926672 719926717
    0x10303030906050a05060f100c05190311030a0c0f320c010509360f01050906060a09061b08040807090b030a1a07120e0606100e0102060a050c 62
    0x641c80501041c0c000e050402c099101d80a00340c2c20b5510959070030750300c200708800552072031414a0b4004121800b60600703d030709204950b10309081805042c122004104184003901c14150401003802903008080080d62034807030300d0798001e40851824100607002d00f0a110300e0b08100207407404d40140702410480401d0121080840c020401d038460000320303105000e2042070714002c1d4000c1c4261101c0150052400d1b400041c0228940c00312500354452421086030006100e150704c02c980400360041c210380c003e00c0d0303203036040400f070190016000d480f031802110100000d024003580b200d084030030346029182c80d0743c2012003441b101c0e03400e200250015000d550002030028541c0c2c0700060301c5044a071745040502802c8981020152511038210700074100701c00c40c0d505821152400c060b41c0394081d480e820710000080c182c69040b011103411349e2020303680781e20100a02c01e6a00d411119140480290b10b0110080000280000d44806029114154040e03d82000c104031160380307000c2c2e13015480d010004d64490b800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719929172 1250 719927922 719927927
    0x430050708070809062a030a08060d031403040c0510080106020a120201060b1804150b0712030f020d1d060114011d0405040b15090c030403080a09021203120c090d080f040509010303 79
    0x1051410003c030250051000015100044107450b030b20781141c9c884080c613913140814401a86c1c140c0108408201c84080d14001807480d02024602503400b41e00900010b600341401e00c24588051320b400001c0c804184010440c06a000500c01d40381a88803c0713410000c080c1a800340d0150950f50400340ca60007003c690760500503200d001080304094202d8052041500302c041030076140c0294025a513000030f04001030804036070203462841c50340b00300c0d10340012030710195088041240c000c56064281c2c0754540d02e508428503400030300b006002240001604980d4034048074042c0e01ca91400005050010101c805105070200419040162001800611052815180815070803030100c0c0c40d1140c89545c40244445801e01964480c4122080c03031516207075442d40d4030192900300c1c0c01030001c1c610b6603c526501c40181c4070364900044440100005540f5091010054484480e00030241d07040a141405010040e030780301803014410b60380009400f50b45054205560300684500e400003601f240403036000100b0540d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719930422 1250 719929172 719929207
    0xa1707050a17010302030703081e0706020406020f16061b060504031e02120304032f100b040b0f01180e151002010b10050904060e043005070807080906 66
    0xa040d651402e1003034000c1d90748150060303800e010180d090340c0440300c18000200c5a074010a24008a4041c1c0000110605010a000e0340060007ca076442d4000c82c08100441d010001a017050a0b0400900b8034a00c0c2d4628100780c0305e20342d100300c0e4200401c1c020000d520312112500b83d540b031a00000140030354942070802515080394520b25148218041c101d91030a24070129030704143c00e0b2444410351640d01c540c1c908a6071110300c9820307a403000030a50070100200010040065045031060040d00e00d204401c100401102d84042c41c0302c0c00b46040601c4500250b9404082c44e0a0381000d0808130301c1400055040c8803200c0e100c1d00040d1541c80c1c2d54080c40300e00381c144240f400b0400c60071100152003070103900b0100d0985121000c02a080610102c0e00301e20a401a0b02406130031101078000684a41d440005102d8140190f8044d90020f98060364804c000303000310101200d8070426225440da5009081d4001c090348504000904480804200c0808010346801202c0680c0c000500e12615030072400034104848 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719931672 1250 719930422 719930437
    0xf040807050315011401050c030d0b0307051909052518060302041508060102120a09030b100f15200609010f0c0e060f07020307031b09061a0a170705 65
    0x91180c0c0500040c5450001009245801c3c041401c000607407911640a110824140728181404000d00803070304000d0007007002c1c2640ea000c0c1c0c2c0c0045004d14213035051508188040d000680242c061000c840d50600c0c8250b84078044500a000000d440d6542100704020844110b800043e21180b03414000107940c2d107c00c0b0010031010141007007112541d54001541284281e1203040b50600c2844080b461890150003020742c4590180140c6009140c05180345800341c0c424119100443c918140c24002e00c02039018990348040c012900d41040c508042d004a800c0780244a100a10400342080c1900d55229802040c214090300c00d020b4010900070b040382c1c0d21410101c80b80e811561900d11801c252410314040c2c58847c3c4d8030780e210a24802d030311130f0500c0b4480e401080c250402030010800e420060700c003000804002e5010b02c07094260000c0a103440341c28a140c580c00310b042d56040c6801488074094280400c1040e402d095802070352590880410317988100003100f4801c0003452241017040d40e0350840018040c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719932922 1250 719931672 719931689
    0x402041805070c150914100c1107030c180603020604140118030209062404381605011e0203150a080d0809070b070c03020907083303030f04 61
    0x50740d82d8040b08540d04548288080c1110f01c101c0410400010079500c01080180980841000008030f9149189482c1001880b61151a80c41c1c10411075254001e0304412a100301e5000381045a165031190070311100c040c000d000c41c4c502d10441e50220010703194030040003181e01030006500d69607240b03800102882c1e080e4400d808510b01054004480350415005026290300504140b11900e98000748aa82e40d1010302d0500039080c1400b20803407011140e0060310041c040c525002421150702e0600080c1488050a400e0600624469480441d071800e01a00d840c00002d21000e40c1c0b2107903505140c0c4c05020200308440c2c03141c0ca00744091050b2451500210b1240303141008103411400064107110980d400340c889c2c0b01c92500018144440144958103a0b42c000d0081c80444001d5a1200d008596039400f010003120900440181002103090541039180d204019003032140d29840c0003c80c0400720550500040c0d00c8000b12411200281946900d070b0080400103021661540820f9002d0996680907008070380c3c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719934172 1250 719932922 719932931
    0x815150a080d02030d06060c05070e0c0c07090e0f061902030c04120c05010905060a0e120a05190308070f0c0f02010210090c0317090102030703030f0b060304050d031103060f0f0f04020418 82
    0x90803805050504007441d444001802b00901d42032100e10103000140c202ca0752500708000a6a072000d04110540181c40d0403000001c8403003c100e013043c5403800d40800340c1c0b9150450f81c01c000c0c203246041c00091980607010b03809a0740c0d03901c0ca0450300482c403894110801908078400c821007403149200171001610002c2e22150111030315401002114050317000e0035000145c0d049000e1140781400b140b4101d4407070700300c4100ca40d001d4541d80e07440d05100c280c40942c0078440114074010141a03100c1507241c0c010035241403400b01d40f212042c005001e1180344002820b404040e22582045920801c1180c00405000a003000703000941d20784150034541c00d102c1600c0b85000701c2042c2c0410184a4103e41d83c640c0160001c5182c41c84030f9506030701030106480300c140e00c5680d4000000711516000d005620451290703018240c0301240b010042d0880340c0c54000e5034403c90080c010404503031a40d51641d00350200c11501604411555000a07588820222005820600110f40068441040320103800c01000100080c0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719935422 1250 719934172 719934179
    0x30b01020c031009020a03021c060c0816050309070b16020109080111070f0f050d03020a020d0305060f0d0c1a07020907050a14030411030616090815150a080d02030d06 73
    0x2030396074102038000c03540340d0488056040d410b1615400100b45038406403200e84005d0b6a500040c0704020718501c81c86200d417044103c10100b00c8a88034580103444582062a083c0c01d20302c900d040d40302c841a468006021001000c911440b03001c0203141c0013041c2a111542e614407400700d0041c03605001d404128040f80080c94045141c480600524031800281d1464500b00030b216100c0e82092101c0f83d105482c0b4041404071903011a105101043c848400d546015983d1342c03c03c0c3c0300074604500100340c0d40c10545060244911a503c2030039511480b44100c6403200d6a10203030401c000700318096880140342caa40e2086202218500034082c0c0f9696001f15200d02a03507988003001d4409100308030803070700020b1000e116240303104002c801a54105024541e40a41c21807444080791514405507004100384081c0b0101d10700d0030f40e0008241c000340810340080c203a100da0810380010f4465014009810350280000c1c5a030302a200c040350a0001c0ca14901143c0001c00c0c040c0019483e07600102e10308512030f04014021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719936672 1250 719935422 719935427
    0x6120b03070f053303041403030c180f0d06020f090d0b010f0b030c0f130902070b0f01080d020a02060c1609060e0604060302030c040c090b210609070507060504021807050307030b01 79
    0x946000c22802d80111a008104080100c0c0d1004100700d170071fa105903071018100c00c1c1c1000903500c02c03004003802c503594040c2080756191098104e614184a8815803c0810f05ca80350100542c0701541d0090300540c44480b010b2005005020350a816508180045003410a0000c1104030038101c4000c000c904001c151901300005540c80b00322460091a00200035205c1c00c9503014004007401c04030642c2c040301d07454032a02d6440903a032050005488a2034100203010103400b4a119031070040c40400d000300350400c00010081d450342c0058101910030640402d000703002c0d41c414046080850105050101d8458490080c80000d20b5940101d0f01d034240480c0c0002d250341054454030068030380040040c1515880841088040c0c0040c1011008001c40f940c00010340b0354400010309540c801c0b5611070428a101c1403090814500010000d1f4441c004860a0052185e004801c580842e80c021102191035616030002ca000c4171020490a000b1254007801c001c100c03a030050185004a2456034103002e07410494004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719937922 1250 719936672 719936719
    0x4051804030f080601200a05160807120c050d1a0f07051204060f0606050403170906070b09010908030412020615030601091d07091b0302120106120b03070f05 69
    0x7004500d02601c440d8060707001e20300c800c1d4080e005140031505014a1300c0d58191104071881c10720810360041001e00b041080900c85a4504049511140700440c903000170295110618442c0000c24400140030500340700e0350741c001c40003400e40a440b48440a00619000742d550403040b041d084c1c01284140421a94940b881c0400e0142c07540d03546103810310381c459043c02c0740c840b0060f104903181540d54203503840d07011a5000710002001c0c151111501c56196040481204540d208035110141c1e0030490086255a91000e4400b0144c12000301d0101d540c3c0d9189060060104070b5014256240c04000c110820441c0d000c00d20300d8124607401c2d03900548805498105c0480e0081e0900d9060700240f005201c20502c43d8000078020301c60038542e20040c141c41e259142403083c3d54200103642c945501206280f50245c050806c000364107031404601d4541078500f8248220018000c0d402040711480d8910f0395464103401480c0c40c80401405e95a41c0c59642c400010300c45e40601c10540140c0490742c00e0340c00c19032800784 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719939172 1250 719937922 719937931
    0x1707150f12050c09010e030319050d0e010618090f05100f0614090403180b0d0c020708160308071a0a05060103050c070c0306090201091502070503010b10020a030c02120a08040518 78
    0x1800380c1001031380710041d203411003001400382d01448103102c0455a940251400c900d446410381760f043d5140745150504c07055032020703040c403d1a80c0c1090001c1080341c0101240c200c04440c1102c00184001041c03070a80c1441140040141c0b4910070b05404000791003165110110070307501034030100b001c03a54a0700c1c50350022941814003540040c520000074046805603400038148071403210080401ca48481c070041075900a0881070007407590320021002c0e811b0301004020b001c2e00c510300060400f82c5150003214020314003800b008048850200b048070810041002c808048000a641d00180d490034051032001407200311810350029040501003400030040c1d5048a4282e0f410070800341100c2c0c21611088042c5c440078200b05d0406c000820000b500e4812249011825600e985c06001e2080c5410308250960f104408641d100f141c4590602a4840e000603060307845660604020711801c0c010300000703086e1520391240350003034003c84034200c1c20000107034014010b0b9441210741341c40544130a04078072075401c01141d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719940422 1250 719939172 719939191
    0x712030504260c0a0602101a0a0b030a06090e1f0f020d020c07050a061205060d05060907090e16061116060f080129070501090609120e09101707150f1205 67
    0x1d007d02100159601b09050f44024956170000898048020560031041688116a940c0010060241307441443c0031b01d400810014070140409045490320646910301940d00340306444840404183c03140315908451040d80c00218119100e14400c045a0080d5000d00070784a028081c9035000708062400c0c25034503041c1c1e042c03560381101c03103540c078601c0c403000f070402920781540003004034980c40005604010301885070b810800a0100540303426114415540d4000102080c0c0d0018104480b4005402d01a0021a0b00c50300c0d06402003c1c094202c5803d00f81c00c00c1a0340942c40f403620010445942010b60301049007002d54800039281e0b80c881c400051180888442890080090896452524040085c1140c42d02804c00010750f00803075900c21040f104000c10848074101e01e21084104ae641184004404038401e49540c140f500e0062043c3c01094a1401080048034518111506417501048220041e22407101d118402d0a4130040260880c0510429040043c601c18a003e4202c0d60324003625000700b1012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719941672 1250 719940422 719940433
    0x40f0302061e070309060b040606033620030d0809070506040b0a050c190f02040f14010e0c12040501020d050105031b100c08030f0708070903050712030504260c0a0602 73
    0x10200320302920074848155166a20f94600540c10b0385c0709d00c1680700a10341d80e200001c0c22400314901007030800c2c200303440803a5052120445882041d002400100082c2d0001c24141100c5800000c03164441c000c032800c80e054800d41404800c560f030072240d1580105400000c880c1410307916000c0050601c01ca0107500b00f44030040c800d00352080e0084003d886904299800d4405806640754150308070b4905031402e8460150349030102d0203504052080a61004e041c1105200b0100e9000303030740003140d006200301030100e00114001408c042200081d030f00140c0740850541d000d41000c3c200140030307401c9042a455084c0c54080001010701e400200a0802c4070461128810300f018401081440c801d840d0307242c01842600c16005000a02071070045115109100d10f2020508103030f003001302a100d00a1004090201400b0148046040082c00a085481e03e0780d07050094000da182c11a840d000300c0d40f09030116521508408000481ea900c0c03480200c5000c412561805170301c908005400a046c401d410141c0c021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719942922 1250 719941672 719941681
    0x2107120b03100f3c0207021807021f0209100806031b01050403080c0a0302100519110f0406021c17240604180e03030402280806040f0302061e 62
    0x11904044610311070100005240190320468029010b0084e10000340c1c00c0c2e5042c5a030b00c030000001d003c501d2800301d42d4802c50800b04075034049900e09041c140381c2007480d82c007100014003241c800c01c0f1000015910000a80d4118032505e891001f80d0007030103105100c2c4070412080410317903108070507140c4075003402030040410907644200c010f010040b0302c10441c1000030811000c808600c0301070041036242e00b10001800d03c1041428000d0401d0400c49a02294504280a111800212204816446e004400001003540081452804a1082c81042000c0000c04180007555640106800d1036080b00226403213109440c01c40202c0c3c01100303946502c62a1010240450140c6003050051038660003035510707029010400c1e10000f500c5070419400005180098160b00554000d02e0040d40d43d6403038484001c0d402e41c14540e000589105500041c00d002c2403800000b9402c0c0c0000452083c000c140703a4003510980c0c00e140c1046c070410794124038180c1c017512a00c00415401c030b0401000d00082e200d041103504481c0c44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719944172 1250 719942922 719942953
    0x60903050f0f1c180b0301080118032007031b0e0f0f04120e09041b05011716140c06010303110c0a15110303130c0501080c0702040504082107120b03 65
    0x10704aa10b50811882590f507050300c40390f684c25034000d408100e40b41900d940c5051640ca084d42ca00072040100413041c2524180000e0b0040c200c8034440c00300084480d580a440c803d924038111855002400c0e420718240782e90282c00011201905a9030384100300490303543c810411001c2c01e1000d81c1d1403400300600b0070001e804501350414000d0007003141d280c40c8205444842c0012440c0c10151819141d103044e803881c031b42114090002c078070b00402081c20181e0f0b0032080c000c034142e81040010400300f02c03a1200707c08003414500c203004008903400c01c01100b544a8413090001550340c5000d0104130045020400b15a14001c000a0742e000b00d00002410a00d40c81c6c10101d0440d090002c0d00d544400380140c0710030001c1e1003281400610b01c11240d0b0740f45507201c00031508103d0090b0015038825414058548140210040ca207011101c60ba0780541d800304a03a180d038501400f1500c100c2140540d4680780a14405610880e01c00c040d0082145e6680d8826030090a001c2c2005c45c3c40e1000300607415807000083c21080c0d41c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719945422 1250 719944172 719944213
    0xb0903010b1905130f0e15010f1a03150a03060906060b070f0201030b0301021c05041a161421060f0a050d060b06070215030103060c03110a030b1504060903050f0f 71
    0x84000d001203003004031150740c24240c50744400380402c3c6800030400182c07482c247d0903801e4014076182c0c8100005a280c05400c00c02e1880310321100d400018000300141030941c130340105000c800001b4008481030303982e9040c0070009182d18002102c41505103200001d00541c010300340c4559035000080071100440320f40c0190b00801300d6082854146d5000d0000742c02c0082503104540103201c8219000c681881c1c41c0c0b0700004418a092030b01040442d101c01030080c2910160410030f110141410702000d2002c0b2007004001a025004114005100e000350844402c110000e071140210020740712844051844400c20039001001d0003165004543c1030038034004220f46410600d075180c0041c4c00349140c000d141d00424480002c01e05800315442c400001001040341511411b0705134090f07071a0410064400d04049613040c414a42c00c2020142c80d00d060751596078a246980045082e0700c442030b6546c0d6030382c40001d8140c629070712080ea0fa5005160034400b5244000c40c2d401801e10101018180c5c111b01d003c030161501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719946672 1250 719945422 719945449
    0xc1509020f041a040501080d020a0f0f020303040f0e09010c02030a180509090606090a050f15120706020d320f0f12060906010f02070605030a020d060b0903010b1905 72
    0x21800760300000380c0300d80c407a9072060000048004000c075001010b0106641040c0d0080c4840e0303100768141d2540f02d5000c02d4031200350b68051100290306a0500341515840041400658540030000b030001d6149220b21400049944090f51038140744d442030550f500700c0e0003108013500075810030400a040c2600c40c1c10b6440003004248000005191158040380540da0202c86006542e8083ca042c400540b4020048660102094005001511701204d030041d0450b809440f0000303003800503900b031201c0d41d00c03154451072005003c421540c500e503440c480259138001c40461440400c04194a019101000a000c120518485003010b020f02071004100b807041d034000712401d224103e0034050300d444401c4040013041484003010000703c550400f00200a00707076001512040c140045410b0a11050b500410700c24211030440c1032407520307641d485514034064071403000c0742e4868616100c404510303132409030081c0101c542c05030001c104058002d01403101c0c00c5054040084128064001081f4510f000354010468 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719947922 1250 719946672 719946679
    0x50a06050111120c0f0109050a0302160f062a050a0b060d1a0901060b0c01020901120c080402010f120c0c05011b020a0f060f022a030319020d06030f0c090506010c150902 74
    0x174003a2020100b0b003155000d0b2800c43d480d4100030a418141541001000c0140003003180c503540c418507101c19050b141e0361074400d0780c00340311040888003418070544502c41d900d900d10101c00300588c42e007460000c0d107854600f201182c6480409000c10002c0c20300e00385144200d603000f03a07041100401040780c5c45110380d0082c5800411340d00c8020200381059480007805d40c0e154484009030b200c00143d0000351401c0c10300c08118001c01d1410320f180500380c0e80301545580042d02801d0980c4000c5110307804540007640762103008142c40c02c0407070246040740d200001d081d80c01c0c0554000c00109030548800c1282d80f0103c114440164444890000400c1040107843d03107140c403840000a0003c0c110380038600766045400c49419250000050505401000c070040703c0c0d043e4100c02840ca1071821103480e0f200c542001c21646040ca60109046000075410341c0500091600001c6400b035070310440c5030001c40030049000d00e811140c10407000c0b81c201e50040300c114024550002d0383c02180140104000020404180180da2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719949172 1250 719947922 719947933
    0x1106060607031b0f030f030b060901090e061203030705040501030e0604020306040b130c090b01020f0a0c120c081c0f02070b030402040c020c19080c0904080306060705120d050a06050111120c 83
    0x300720880808130385100ea19403282d2841c10361005030413604003001003030140740d04000380c08041c3e0b44800102c0603590000d25040b515190310b00400d000b15110301040d0100e100010620000681040c0940b040340c80980e0f0511100342d160410940300d83d400d49000303401d03070f006101050005601c1d1080d2036115042448103100316205403254550383e0b903258000516241d03144081d0b01c655905000c0b500c010482c10005251300305080d503031030704810a24850a0a89841c4c03c44040800c84941c000d04010103411701190809001000c8040300c0c00300c12543c1d080800c10342d0354001181800810004100c40d401d002442c21599075800b840090300380780c41e0200841c051038031840440c1e80c520b248901c50403945110b10300100d04051416141403500c031650340c0724407890000c01001580d204d048aa000c08280e541c40d454203800e10348145445041140101d50600c0407812112050301030f401184a18602c01040c81031503511401501c0440101405c10782c90f40145d910003410301200001010000103001c11941d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719950422 1250 719949172 719949227
    0x110903060f09101b09050409030e060d0b041a01030b090705070206070f020306160306141c050a1a041b140405040c260f010c170c07140a03110606060703 67
    0x498240380c84c01019200a404090802980900300f400506810781742003213004d0780d5440140100e410641490b20031a0f002607003002c09811500014600d140180080c014400d04401c0c10720111803801549002919110310442075180a007607031340c004c02c6982c8519162400d50380034404941c0c440082030741c0b00007000a0600c01610308002c4070344180c46400c42d581003140c0780100242600c4072030b40300d9031003a200254003621656606c00e0107a40c030040d08014184c0e440c0c851902a040c4021507601500c4003020344000090080f2400b2410f101e0351042d40b421b00040641c0c041645a5051400f0711200d010400e00d00c000b2500700b640c1b200341c01c14082c0b60b4500451740c0c0d46061284d01d0703103590143c02d12000b000c1004d002c196010801c80c0d080ca40d840b002401038441200303008000c0a01c800b040005000510013041111001e107080300d0701c1e0b03600003852002400941e800709507503030b0b503100c0200c1c00a4640c000c00d100d50704022584500404001b4074007854a090354900303e51079080c0c00d2401141984d4001c014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719951672 1250 719950422 719950453
    0x40618140303041b0f0e0a06150c050f06010f0603021804020c010b03161401080c0d0c09151d0d1e050d020613170f0c07031401110903060f09 62
    0x48200005004680d00c1c50185412034000035585044d030148010078809110b100302040503442a50501c00300410716544841000c1d020700a1a03109c42d03511700c03908450350019a44425649080d0380030b00c00302d844081c50300b42141d40d02d04092007591a105009076042c8036851280d00100411440400718045841c0503600141c12a4010b6880c02e030907a40d5040b03409081d0405100c0c01d40000c5601c019044800d00c2d1100054207400185000d504110103d40042c0709410b0103c207941c180e501c9810100301c64824410701030030740a0a400f4070170110520160080e552881001c2c0303c0c04101418203030024803099203080c440103404071101218040c108005611020b01c1200b5082d80c00e9000d030004201c0611095006400c024000e000000070181c42507402c030100d14200132400c95113105251540c0c0c6c0e14203039544a150750240c10b52100c05405440d5001082c0b0079202c0300c4480c519055070003007111841e00c00400c58548a055490b64058101c0f40020720502c140700c01d8a0340c001c0c00f40003540c1100a669022 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719952922 1250 719951672 719951693
    0xb0306090f330109061a09030a03050307050c15070314060307050f0102070503100203010510020f06060108130b0a090b060303210405031c1a01050c030712090503010f0b090903040608040618 83
    0x24044c950780300c004000c1041010250741240b01061403491402e424100400d45a000e254002340c2804000030104854920520443d49110b806e40c00b41c40b10703000d006003581c103103600680b00003000170f041c1007034003400b070050551550041c0001030092106514290500c100c0c182490784440c10f40c0642e000000b41c54a0900c00143c1501c0c4007140141e80c4d40c10710003000500180c140710041154480c40b0410f03002000080c03242d4000f103090034600f01e6560307444c072102080e414042c0300500400c0800c0c1400035400e503a4100d1f00783c0e1071050001c1c610b80d82d190400d1690301d004100e10191541041c603811100480508440c0350010b000c6e0702500c0ca0003104861544000f030020310100604c0b50359400720030091003030740c0c800c52180c6000d1070901d18101601e20400e41d031b40101440035086070084062004c005000f607402c075006000240080c401403802c050060002d01c001e1100a0140c501480020741e155000b00c112002e454032500c80c0c01054895403661001800c0600c4841d00d1648400030800110b44407010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719954172 1250 719952922 719952929
    0x810210813090f1a0a09050c0904061707060e010c08030a060b0319050603070e010902090d060f140f040c1a0702041406130e1e010f09060b0306090f3301 67
    0xc2c0801d200344040340c4a4125003d1501c14403042107081800751a5544900307100040f0f0b9064503021500d9110400c042c0c60911a04d072050b07600501d032040c001124180b00d070301c0801c2e50111030181d81540d41e88840c141c411000804416001414a80e107000015610b030004d142c010400000010311540c4940704100603620546a2a0751040c0c0e024111504035014001c8550021041c1c000d4006c0364a80361000c01c4400e0b0600800202a802041180594440d0000000748513080382041c0499110036001c0c0e40141442c1400740200314050b8000741c0e0140442aa140c0590790100d44145403a01d0008107010312403000304205c4041c0003c0181802680d01c0c1c0c00f40034440d0100050034441342c203120302003081d03112044034070161160410141040901000c1410080364800030346c09401200d13165100c034014005032010314060f62900608005214140d8019443c4c203c0903400c03103000c1c0c1c985950040ea00c2c03842036407244242c0c0c410500d0418603402c0030300d07040c20080c0d030f0801071b60b40c1010441c44001c2548240c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719955422 1250 719954172 719954189
    0x3180b04092318240406090203011e05060a060507110f010c050d051206030607020a17041205010f0518100902121b0a1a04140f0d060506010810210813 66
    0xd20081d1401401000104059134000c41c0d0b2034243c910304070240784402000540000c1e5030b07483c903400f551401c1d00202468100f2030f0020b954010101c1a480062000361203550003001d040300c000c5011802803084951980e0840116440070100008105510404136903440c1000b0710ba42204001900420a044102e00d00c3e4440329150a100100c100580070000e00070780c0f20380d000d00107001d42583c000c0f405060f419002620600d031510060a003010510031a0b0110040c1200034585405000065020b80180701100a06106a0b00c0c0d59030720511a05100900703040710f40101049039645286d0354010111144080c02160000c000070000900f01b81c20030074180d4030100c01904940d014605070260740007400180350820219131070082c00030b05500890017040d011541c113409a07091650345403400700765030000900028803004a4a0504041c01d002d41d00107000c141000041810304070303903007104000e41d10001030444488110740c0c000e102500c0782100a80c0c00c02d804004401c0201c45151403580500f5425 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719956672 1250 719955422 719955451
    0x120c0319030815130f0204080712051915020a03180b09060726220302030c010c0801140f0409060213170604080f0a090f060c03180b040923 61
    0x50402600c2c1c440014803400c440d2550601c0394500d07030340d40a25034204c00384030034002852810340d8102d01c009125a400c401c00c40e10550800142801245a000005600c102c081c0c60321600360455000e07503103242c1c1c440104542c1d15030418100c58480c550213041420418540030580c0a03c205840001c4086100c027039070002c0c1c62404000d4114400c0200715040b12661402a000d800700c2d08401c0e03406d04440e480032120300c002e01e021480c42105400c000020040244085100401524029680e41c0c0400c44204082d400c01c043d00540c1c1b4001d0480340c5c102c034448038a403000c40c4000000c0143c2c1c26100403200c0d42c030507034540d17001011031403034401342943c01c0480000c038103d5420445a2a05d44c84101031250003940640d0401000920040580304090310018015444092050055030051601e40000301c0340c1e21803640005015071300c20b50f080d241902a460320380d03414415240320030705c81d41140030310030784e410040000304039295241c0d000c2d11296440030f007401182031261000c00f54054003a6601141050394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719957922 1250 719956672 719956723
    0x1903120804050f0a05060613090206030112031d010210050c0d0e032104022b08130608061e0f0a0e2703041d0c0c0d02010c090b040f0302120c03 63
    0xb0000100c12204580013002d001c1000d6580c295549030040c61103001d41c002280104a0000941203052201d80c002d0603175841e50303161f5a01104034080c402d01540000d860194000c2d4002030f0511160b00f00e00103170301401070039640005440140102409212003c4400c0000040c0103005104408815140e1070140d0350301c0e4201c001c0080c41410030903c02c03c030910540180300059840026103000001c654030003580d82c0e481141161b241d4000800c000e8400d403000120386048644103040b0200741c1e1a40d854611080d02c503201482a0240a48400c5041c0c0b1200d0811000070300e00420400000e0038014034801a003038680c84a56000b40c0e0665003084a03401c4507120842842400c882074001403d008000c605061408146800d40f045141141c2d001056040c007040b4000d498030219031035000300310105c1d4010b54007204028028150415185c002812222011400340c24610407141100c1b18404000c00c080e0440d020008450001d03845650b251182008468407510184250a452000c601c490b51140c01c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719959172 1250 719957922 719957933
    0x160305070b0f0313030c170304030314061806041805010509070519060509190608060f032a0f030609070f0f03020a09230c0c010609050705091903120804 67
    0x14180c0240860601c2445000000780701d000560f0341c41445a4148070510516040550b0f0f800041140505086005900a41d0f44940d6800640c0a20710030340d400c1002c20308020107030307030001c0082c4c03500b40c1d2210441c1c2d0080201100317451225001800100009001c0404010200205003d0001100c140c0d4441c810032400d54014411840101340548000b042040d141c8680c0030481010300500040c068089071003803040d19002c118031008000c5099920500746c590030064a44401118141c1c890204488040e409080216020b20111121680c00700c01003041d49600700740d00001d00350190081000c1b115181c141da020011a0b0180b070112001e849260b003010b800c40700c5141e594010440100c01401c0820050300e40350703408030032581c000ea00010041c40a000042c080e580a4484a001c440c4550512401410080c018500989520001c05c80d4650b22640002520011074058011601c24009025641025612590184c001110661010b92aa035032100e60712412940040021070584c100803c000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719960422 1250 719959172 719959183
    0xb060d2d060e19080f12010b07020909011401260304260c010f030f0905010504030f0f0c0f0b0403050c0303010f210c062303010311010e0907050304081b160305 70
    0xb141c0409010180042003403daa104144000140f404600242c086800705091068600c0e46100d800a5042075030f59444500c0a03800064007688180c28000c007092607034105201ea100195200b40300485260b280042e0030800f94030740c5449814402c40b1600d4104a0700080c0001c0c405054074219080b49802499080c0801381d5900700804500e50140c0d20f0f0040980e00034006142a11140c50046521400c0c0030301c41300030b8051804018043d44c04c007402e001c10580c00a0560309040c1e4681d50b42c0d00031704412103080b00c00641401d405440b9990031481c01d0007003640e500510358000e000341401032900081f80c1c4100c1c65540b090b030100c018069170f03110601550084d00380800e4a102c0070903440381c0c00c41407a143c00200c0d441c0c620445051121502c00c2005c0318426002c400d0801c480d02c911141c40790b070749041c415080841d20142034006541b42d04480d0052030a00700c1540070380131550b2002d040d035a403940c80b01c3c2c00f64041078030042c03a07094881146405610070011002d084558070001c496442c55482d019103803c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719961672 1250 719960422 719960441
    0x91201020a09120825120f020c0609090402060f1c06030203071521150803040e0a02030708070c020402091f090f150c0602070b0f0118090b060d2d06 65
    0x140c21807820280420f81d8401602c0c905100032520000da450740b080540d00c15041544010b10206d800015240000c5e0815008180a41030b03030295110480e07050108500e500c41d50003071030303440301011000c0b17400341c20500007a0042100600344240ba04400303065404032459868203148071685c46800510443c1001e0001c0001449602001c0302080c120a074080c0c607000140031040448055981c8410001c041f94200066460000c039502500648400c050b44e126031003401440500406400410038010726403084034400c40155449044648404c042159801e440c0402a07074006d07000d10660829689841000303145009020700c00c0c140f104038240103401ea0313210751701502c3c4001d0040360401c8505140746641c20744288a00d0b103604160018604040240940c0901415400040741042240c40e0406221816180305840d42d084a085040b040810b5a41c4490020400c0c0c144d6000700352242003e4421100a42c803030680c203c402c00b44000142451400d16034009440c2e843d001c00881808203e02c980400c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719962922 1250 719961672 719961689
    0xf0c17070515120403020c0a151107030b01030b280e0c0307080714270105030f01060308090f03100c020313061d21061f091a04050a02091201020a09 65
    0x1150814034190303030140280745203044499030f000d0003c1d08062080c0419441e4040007000c1015031071701ca0300e80e20b03141155080303030b1400b042040c524030501d500300043d001c0440b40d1203035401200b44e0a59880d01240311000e07103002210a0350750486042a000c6590801c0e207410f01e440b0000300089003034495803034009120030080c041d0300203c80030b00c003841300481c2c4201031307950075143d003003020188101090541c3c09062140300698804450040c401d04854043ca040321421000c0314000031003050f80f14200d68540c40001c0c9021000c00c403002d800e017800c01581c965a48010b081c1c03450f48050350102400d40350200c1039080160070010b929603403a02848181c40c040d040384d18044940e09141c0303850708086d00e513076100c60388a540c2d0086802202c80c1c00030707002c0c96112010010f070b40c150b00300f6000142c035101041c000c0e00b55507842c00002094900c96485180340c560740c104a501c898100200134071005100280c070500c8002d800304400305060b110010541c194420003000140c0d00d1161140040070920203130011540c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719964028 1106 719962922 719962939
    0x1050705060406090c0e09151e190f060b04090504050304052101060b030705030402010e0301150605030103050d0509011706031c230a0f0305040f0c170705 68
    0x28a0748220b10b8031807803070f40741d8400c140c081b0030442d80b10501d944040c1d0350284000f00b1004854000d1003a8414006043c1102c0030001344e440222420344101055030a008007a5519100340090503621010400516050510500f0144100e01c00e0780344041c0c80e00003241c14401d00380212030050a005150340c3d1502c1003051000300b0f00401305881003140d483d2486c000f038440c4007401241d1040355103075690b62440d59150f0040d20540740c0000c08681542d40e03103030221095061407401002400741a00c60300d8503503141d41341140c0303403840780300807001040000c0c001c0b00340590f04911501c5002008001d403198656500002c249410424860101c0701e5000c10030210400ba0007265280c0146c006008603211247e0ba11040c000d94844c882d03100d0b0000d1a612900c444081c8281e01264100e4428186044031000350f0300e800d5081d41041d0040b003041c0101024203801c8100811102d030040c0810b590006 = true := by decide +kernel

theorem cover : BRFrame.Cov 719784172 719964028 := by
  have h0 := BRFrame.cov_init 719784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719784172 ≤ n) (h2 : n < 719964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
