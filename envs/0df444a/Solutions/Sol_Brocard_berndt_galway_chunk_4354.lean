-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:21:12.492002+00:00
-- url     : https://prove2.me/submissions/ca7a0ec2-38ff-4ec8-a0c8-447f89888a20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782913669 ≤ n < 783093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782914919 1250 782913669 782913671
    0x50a230a05090f12060f0403030e160510020609031c0902060301030803090706021b01081e010308030a0b01020109080904180602030124031a0906060c24010803120a02070303090204 79
    0xe6903148026040b0b40c0086101c038410003060070751403441c1c0380c048062510000706801411182c1c6403000310340c404950140c0210b05154580c3c03141d0700d60740d004010200d0041740c40b9038100c060a1514042c00888400409400e003190000030410204050000459503410130000c000024414120f605400400942d40c009500900000000041c40940805580912a600140d0b22a5070351040140e035100141e40390074403a041c60140310b009a6018010281d4840b80841010f0ba17440601650074441712800d800c1261b8070700c800710600a1200151141000e59034080c0000c008101c0c40c1c0c0c03103051a6015505c0824488c544031450403106040700450034001c0c540c412029500e03561142c10f4032100c001e0451180c500381d91000803641603617200303024299260350320b5680710800c1182c11040c0403840c0e40080285410006c10040b00b0013244042000300b41082005072581074034540e82d120142c1412041c2e101800f1944180900c481c0c01c001c1805558000d0403603040103a070f600c032070329007074014000f0554065802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782916169 1250 782914919 782914927
    0x5150616051c170f010b0304141c1211030109020f12070c0b070f120e0304080a1b0815010905060a0b0403110f310b0a03050d0f0906050a23 61
    0x111030701c000c04280c902c0880d20703103052501006010f24500101115440c500050a00040280b107800f00d0043d030b002030142104460080200d0780311840c0a1124406c0d0703450004a40e5240b041c568441c0600080300f40e002c50901c01454a69003034551404180103245800d5400200030483c2200c00045843c40c8101500054a9252003000507040c16020300c020b4484028a00019402600c544850488034420f034555410b0801441c0980d0000e04d07102118036007621040102040140e400c11045645510400050b20b0985415203080d642c03807542c5e800b141c1c660388415840d4141140f0f000d81c55041d80d007507080004450340c48200054028100703138441e440c024070000e80442030005c51000c0c40078180056070400030110036281400440708150b0000c80341075030f00d601101c02002000f84020000d50341c8040110f1150b00a2002542404e5550f00c100c481d5841801c540070085e03001803002c204040c9605001d81d040f490080007a28600c41e03010311004000b2b84804c50840304511106081070501d80380c40c000e4803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782917419 1250 782916169 782916193
    0x1050c0a03050f190e0a061814060108120a090f030c090c0e0a05040209040f0f0b030d02010506210312070504061d0a03020103022d040302130515061605 67
    0x540d40c03080e100e03100028104400106100c91002c6418082c0b404c0c2008442c8207000200480d008195210000007540940d800c0440810030701d02078406030b800d42c12000b8414410520305440c2c00500703888078102036004600100035000c03005c50200041400c41690541d0380c0d0711504100c1d084101500010030b0f0201361800441030201500071407080c0c4012120030042e81c0d1107844141d689181081580e40e1114440a0901450800340c000d0690201301500c00704000602c844400c06403040135682e1100586e46804020035071404000c3e0300c0c1407051500003000340382010000304031910307240c0341e202c4c0110300e45040e0b000c0107540400072149a4410b071251641f25003410880140b240e4454416600010403906e800036420054030700324000d00000502104515140d60f0065029400c10a4070a051040c5002d0045214410f448103141e001401d00d6050b0f511070441c81082a903034910340054a00303a10300410045203446a026501c0e40c50000c440c0c1903210b8910303061000d00012820781c01081405268650700c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782918669 1250 782917419 782917441
    0xb0309151f060206060d031d13020706050c030f011a0d0903021011042706030804080d030c1403181213170303040302070b09031501060f0306082a030a02030105 70
    0x180064440a01c8a80341d640c48200d9541c1010340e400c070352040409032828002030280540040e04180e440c0c01d40c6201240038006042c00c85030054062140307400003000f40c00c0103058840e1581c090074940019080d42031500b00c844081b00140100b194982040801c030515034400e009550320b0440d01e43c01403044d007805140c003c1d1202e500c009205922400c0c09800103100320f1000c203417019242407401d032540300603104c0012030103610320300b1301d5500c4a036070303001d0100100e44000e0080014005060080281c020302c4140101102e030400032910810034841c0400b48207e10140440340c002201900200030392165044040c06e142c64070710840c150b10400180c04540e12400c92760342c403c5070340341d00c0540c01400e864402503882e8031040390010010303000208148008808240545108600502121000c8254840004169000303800110128018003604640582d16004000140c41e003c1c000e01016040901d0707003034002443c00c2001401540c07000d8502e0046d04d0400c916030840760014020712081c24100b078041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782919919 1250 782918669 782918701
    0x201030f0216020a1a090d021f0f0f020d050a03020a09180e0f0a05031e12070908010b1806041116060621050c0607051606030b030c0109080303010b030915 68
    0x280154500340c1d000403c15141020150005170025442c0c0c54403080c4010071a0220403a40102d0348038400194003003101c00355040b40e0500180544a5489031089280050280c0d248480710350115400020030080703003544070050307a0b01d8900904000da02c1d0b4282003800e4415200c1500005030440d401d0103506175400440e000b9040e03004d0041c0507a414142d46901a580380c80e240b8101078601ea0080040c0f0f0a030000f48100c1c9104402031041d001d0810f8041205401d00351800c2d95100300050f4502c1c400d1222179401e01c0380d0a9005821a848103100c0c040d1510b002448030010080c5116a5449560545020101080341d40580c20113115250000f00d03032406c40c00501c2d59000d4440003403016941c80201214120782041080c0e040f070300a1040200540401903a030b800f0301c1048800f40529403054284121000650300500300f5a180072400d03039080001e00d49882c0c08003203468100700918034208005000482200c0c1910341000c0c120b507407940c500040500d814484a05403502000040400c54481e900511803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782921169 1250 782919919 782919923
    0x302011d0d2a0b060310020d0b0103050601022103090f0106090e01061a0414011103030f1b07030503150a15030207060f0515040903030b04060f05030f0d1b0201030f0216 74
    0x551280740c0e6141541c0d0b000003180d000141400e100d80e10010809000c2019032000c4010101c803079040340e0356100d801703036041113001c105071680b11242004150380500440368061030038402808120405804155084099000300c0c05100e0000007241d0b12071010b20a800c0c4065048000f804580e0b9191306c214010704047c1041215542f03407110214100380c00c041d20b43c0d41e0400301100c090900d414503101d40c0c81c0380d44d481d60305810b218007801c240c044548280702452103031155402488040c03800d50780b902209a40072400c5801414100903801c0066044419a90050070b103480212150300d1010204d101d1f024290801584031b00e001207003924499140d001404150310800d0180600000780c243c603815540180c80040714410301c2009051a0b0030075602c1401001d000780b501041301c014a0012030300719103d07a040145500c3e280d071820301180c28100090746590040f10001c1083c2c03104060000d0a07890985d589a8201100000348420b40e071094104004514210008642c0d8803410f440b41e00068500ca101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782922419 1250 782921169 782921177
    0x204180f1707170c0c0d080309010609020306030304061b060204080f2a040c090e182b1809060b0c160513090645020a120302011d0d 58
    0x303190041e004010350b1441a07015a030b421820140141d40d06040d00a408900c4e901e00c40c012614842d81e440701040c00b6464010498680c0d01d080144000e402d40c0c40359000f00407071074010810300510342c40010444007101c105251042601922940c0081903042c0843c0c054240750000c40c001c12403c2c0c000c142240c05c1d1034220222a1102406030724454880704030b9801d280c0440d0982c0368001c6905040c0c201c0110301900d480c014801c3e9489003140321429606540d01711011824200b600c0c170b1400104031039502008407034804285042045070307841015512244240c1041100358075401e8002900c0880805840c2004041c81000c1e100c3c03801c604180c0080300c004044e4803d10380c03424004002c054a020030341720050b20224222038010074000141c8400714040f94442c1d6101040304004070700f241074010303030740565422403070782d600d0231100200e2032054111111a16491403065030040e660790707420800700e44110004003206400790405030300500c00303070b100283c2c01203406035509001c11003c1603d184806140d10307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782923669 1250 782922419 782922443
    0x1136060a060f170c07050a03020708160f170307081810030e060609061c08030609100e01060c080405090f070f050924070c0605120a050f070c0204180f 66
    0x1c0c201e40201080310104007181d10f000201d002c00f0b18410304903034003a5504c0c800d54508003465a9151414401040c1030300142c10100041c415050203020055800102c3c01002549908112030700d10341840c14401c0c2041c1c841e11441c0450300c0f107400d100f500c19407500b04480349e07200c03404000c0c81c40501081d1b00748584603489840314150040d00074444d0030000c1400100400e102e9130781c0400e00150b8600039156960050340060014101100d2145003d00300d4030a96280e516420100144100440080e01140084c09c100d6002d008191040008a0441d00c0034580304020341d2050901c6980ca1003140c200d10340003640503003084001c08140c4041c6d07014041554900d10204902c19007111280251130685a00801000d030a01540107001440f54081c24001c0d072403403a000160741c61103102d03203040c1e000d0800300d240414844655806d07107051541c42001d03410180310740d01d44030a044039001c90082c408024003041c0308141043d903c4035800010001104c40041e2018841c038141145080c0860000300c030a035078444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782924919 1250 782923669 782923679
    0xd150f0305010b090c070302190302030f040f080d02030f0d090c0306020c1f02250204020f0a020a1103030901090605031503061503011a0604151101050a0903021006031136060a 77
    0x80c5c2120901e580540c080e01540702d01c18101c07040c8054500b03080d002c6200030701040a80407040001000101115184041414581a00b650a20610841c08404d64005000d200504185502140c51000c08407100080a200031f24040c2e4034072071190009024107102180700001c040340000c0c000800744403121000e81e09841c0b0307981a8141d10507001c800011405060442100800c3c1d02c00390381c01148000e001600344820203101a248be008000a03100503072080b180303001400490315103840710400a4001d18a06503422001800d10106807151804004000000425440c2040405140c515009040d21075a0601001c3d42900750068030040d0312a5203044600105a0400c500b002c005e540050300490a2514181c030520200000f0301107030301404185800c104040c02c080c07296521800400e040012000540e080092520f9100c00c00b41e02c1140c601001803002c9102240039100494044803004803101c1c0010981c000d11404a0000c003402201202c0d030064942d031506903074803035041607070700c00c9185540d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782926169 1250 782924919 782924941
    0x4060e030c0d11010509010c0605280c0815060d240b1201060503130611031b03060d240207060203061009140103090614040f06110702060d150f0305010b09 68
    0x303040040c401500040c01943c5540104050900c020050405c610012520f45860040d5803003200c2801080300d4035444d15100e100e0140d080b0745003401c003a004024042c202130b000307098040c0140106419103070035140d41b05207544a400303d0388200c0030240300340911402c81b103c03992001c59419000c1092100b210340070414141440a4920034804040058280d928045050300c50341c0c0041c240441c004007440380b0b00086401c034054855504824280c2c00c0d90392a200c81a080600d04070041c4100d047d80400a002c059910200c0340e551264201e6241a0800d071626039901c0d00c0c8020142058400b8004150f100034041542c0c0903500c0368400759208605041710003230444458000e40283d8100000040d60044c0300c1d40b10b5800021a244030b8080080d81c841d089404d8100d42c401150110780c42403240204a04004c2140940404554001251230801c00d450380040c007e402403030400c1200d10380ea1b40c0c401409010744040f40e0014102110100641a12814584c0c040c205441c10fa40c02034068101040c00741c0f450f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782927419 1250 782926169 782926189
    0x403051c081b0904021803060108032203050607080621061b1603270311100809100504111512090c0d080c100513020a1703030412021204060e030c 64
    0x805548540f070043c5440800000f07401c032001d2621004040404220192810040710b406445280c0c025602c42409881640e01f81e400807603034003c0d90041900400001d03800003821500081d05040075001540c541000c5100385601940480c4481d5103480019100f003030110303440e0f004003000401c40c4d444040d00b496a0501c3d1003460100703030402805c10309400100e0b20410b201ca803050b003c0c02825501e0701000001034040c0340c02e90007e40f1107111040c3c401203c0d1030800a508480c4205050a0f84280f4085280e00d031201e106251032081c11351284005020040100c05124105400a141c0c0e00c40a000001501254015030b0850b100900c4060203c0d6180c00001040d424604004024580c0402140d8036200c443c1c12506074032100b8031980c0966010100c0c503000e4244200e07403148070105948480c1c0100284003034107501240c4a0741e07000c00001c04501e004011a5402900100302150501041e02c049142c600038418284901002140200d29140d2040d46000b052104408445540016904102e09050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782928669 1250 782927419 782927461
    0xc021c0e0307050306220804090501090606031508060106050702040b0307060503040b0c09031b0402211014030307020108070207030c03081806091806191202011713030c080403051c08 80
    0x8410008401c0e483c0506c1d00c0c0102d118070079490107003442c1d0343e0124031098410a030844910380303440700d8062040540c94491a400740d6090388044811514102d0a140c581006010303001c02c101000038003100755241c0c0d801c1844401d501408607882ea607a21000104030350001d9404071500e081c9800072034960340c265400d0310007050004014198809680c04001c1030b84900043c0190403a8007030108903415405410744080a032420754844800b0324241e085003400e241660801000b4102d440d4540e001911700205403000240d080c04c1a000d1601c0c0d008081e0318092650388001c19034003c03041c010081205d500e000e050152450b01c09540d05800c41e01c100103560154011090300441c15260440315500d0041201f80c004c1005480c030170a0400200d00c49041403402d800c490841c001e241605800c65134402414544000900122906070420024841d1403040311000501000820032020042c414810100c83c004e42d40042142c80e01ca000c00340d1511421101d0245101049100d07001854944040482101080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782929919 1250 782928669 782928691
    0xf161106070c0b0a09080f061f14040213080a03020318010e010c030c03091205011e050402060f0d110a0e0120100515101206090b0f040c021c0e0307050306 68
    0xb0741403200c00718058004410090820108001c0061040d00a00100031810460005809149001000701100e0410101b25030f44404003048100002180c200351040039000c119400f5030b039200174000c6012282065004000d1902400da5081d08040d00003000b4a40100b00e4002c3d001114903800054440020f40300704140030481181d1003800191140608840c020720030b061420170103886028170210011140700403200c0e607545619480003509920f00c01c0890619400040c490ba141c5030b40403c490b4043c600001c2c00d0103038041100801c03003105401c004d6501c10420740a03a225181c108000303061544c401d0009000c505c04c05401950144440214800b00c0707800801048002640c120346070080100422010315610007001a040d0380da503003500c6075144092941e641e030320b085010100c44200c07000c541c4540c1c9002d01d003060070032031905c03610350080c4501412140042c0800307030304000f83d080000c0120707540c40981c5200c880c011400c3d0450f2544111500076401c0754015500c0c0e505066683d0f60603103109500e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782931169 1250 782929919 782929943
    0x170d0f030519180303050901021318060b070b01050906030f1c11060703090506010806010303170916090519020c060411030a060c020102090f03030a0906140f16110607 73
    0x124020340100340c01a50501d03108210704003030224042215203c014420841c0402c1c0071040500d0b038940581a00091064021843c4c100c00c3c0c40032007035000d2a48211030545c0e00c02c141c0382d07201d0401e41d80700d600107003c403040241c2d54040034a400704045009024031446400d81d0310201e0680d0800060b0f414003106508010421010f0102e40e103006682048203200c1000040c0c002c55220300c4041c0851800b440e1503403800f203041c000314074160f810903405070440e80c403e902440041000c40c0e80940c80c50342804041ca44242952203a01d0400e050200340c00c20810441c01040300003600c3d840e2913010300d100707020710022151400122081d1a0580c8500003900b08254094000300300403c5501036004d40303100c4000c1c12030f02d0040c616503540003a00c05402038280580d5010451001c1800d005a0000315040110040c514240d0407400c0504000c0c1580500010010140b0300f54850417038403000c031900d820b081c82c030a42d168159005c1301c107030350300001c0b40480e01c8203180c4045006d103051034401e461140741e20074071120103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782932419 1250 782931169 782931197
    0x140411041104050604140a17060402040f0b0415091113140127030506070c03020d18170a020411090a0b0705030d0501031101020606060301060207090b0301021210170d 73
    0x5480d181c00411114072003008000303011340e20040204000c00001c1c00c0110480508010005540300302d03070050704000c00588500b4034070b1b0b0010070703000c1c3e0203503040f100002e00307003010b115100c01000c0c6080b0154004e858510702d80040c0c0100c405050444005000c14001188150160002c1e80210700c2c000c2112155403d00b0300904448802d8880304810602d80302850484c003442500e0811041c100101c043e0110036030500a00c00c0a11141c0d40c09601420b20b0036501c2915a8001c2d5610104a030240070030000d9560008103d654007120030040a042c00030b150f440308000c3c00241c85840c081c1c2c0c01ca00c0745281007401c03240b51100340c084d615510341c01040c880300c05180c00c03a41060341d4401c1d60b0442d12408204070f844001c0c0024415140a98041c5405003004c42c450f01c00689404070240480c3c0c0700740000c3c030040040560000c0d034441500c0f820400030440745601d10110f40a0700a942d43e420b0310900385010400700c0940310305901d003200c0300b00800200d035681400c040ca40321041c0401c100000380e002208903030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782933669 1250 782932419 782932421
    0x70b040315090204020301121506050f01050a091e1d1e040305160b0603190503040504090302160617010f0602060606070f02030706030c020c010813240c09030614041104 74
    0x1000720701500340441c0400b05640050100d80c001d0b002030603429241d804c03003402d001006044403441400003000300b140504141c000303000e041c0c1400f2894104400010003451440c45203071075800074001c04030010000801d00800c840320300e0541c001c0c214026801d040966086424106081c007402407410b00d001e000080105504078134a0040003582840010000e2503603400070301d00c42e007040502074003101e4030710305280c0201418549840000036100d00f02d00c0091000c2800030040350100c840c103c0300000e40b1041440c0c182d040401c40b800e81030b201d8011003c0092400d42001c400c041e0052400d040c4035003030380c07a071004042c1c0c0005405000016800440007031a1410110000d00341c1c90f01413035003807114401c1d50340040d14040e02038108000182d01d6050010300b20740c041045034840202401e00910524110003c100c8840a03007030040c000b2207001c01c0c90710032200040112031100b0b90740d402c14055140d800344080c0800b121407004a800d0361600010400804a10440c0c43c040d5901074100c1140d03543d031700d00b008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782934919 1250 782933669 782933693
    0x31e02120a0c0c0b030403091401080f0c0c1f020301050406050a12170d0c0e0f011b0f030302120906090c0a060f0305181005010e0a05010b0f03090a02040501030f14070b0403 76
    0x41e89403e0a09002c104060f00300007443c822032190f55514541c40c01c1903c0046010700c501c11082c14070801509000510810800084d44800d00c0e80d00c0584552800d640d941c076200381c00b10075441c2e08a0580c4500480a1160000e50507280309850038000e069843c424443c4503280303480340c40d008280601e04500010001589085401c19004083d0300342201c1e8003606080324554004d000102c1d1848228005a0502c4510841c10b040c0900340098110360100803035000081226000340003800c1c42642d04100360080e810f403094060705010b40314540c54a00025980d03203134191462900c40c469a00585410300c0c000020f1000d481d250b0b070fa0070343c4082e21107a06a002d00000343c2a07501c44130091707259003071086040025140c122444c0c60007080e80d502d07012114580390000303040248a5800c0c1030041c480d050004d8122100303041180300142e520b9541d00003550420300480c10082d845404c1070700000601581d00c20101c52140203058440c04540d401c00415594100c0d803180d0301c2d010390300380f10800c0460010841c0c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782936169 1250 782934919 782934923
    0xf0e030a0206131b09050a0f020405010e190308040806040c0803090105092716030b030703021c1506090504210801330c1203090209010e0a02070f031e02120a0c 70
    0x1026a04c4070b42e031802d01e07103200365005544825076400c00c2056001d014083c41d00341a0354034600310314050030300d00001c1c1091072855409000b102d141a141e81307840c3c0303109a2200159005583c890726a43c44d2103116440b02d00c2a81c06403260550315401003903805001c07040310070801c4142c490a02d009110801e00003200c0507403c9007001049550707240f1504100d1035100e54820f00600503402442040e9041c0070f412038011403070311802075210050610041e100d021400c1d194084111052162a0f2640303811a111700d09031840388141400d05000017082005500051f004c3c510402441c034041e0b1102c01d01c0a03584000c00310200c00603005c2c80c0100813829414510078500240c0020341d1110b400d840104517111a122501d100c00039400c0700000c1d041c0f0110b10200081c00700c20345410702010030039400007402454107005412024044070081118510305a04541704590f109011014a8140d8200603108001c03404840284240b41110003006038804140051103000c0d4006960a0408114040342c40390700817042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782937419 1250 782936169 782936183
    0x804020904031b050c100c020a03061113030b07090506090a140103020f04170607021609110c162409030b180616031a060702131107060f0e030a020613 66
    0x20b0030100d003940c0802c8003190f80c02030300108000d150a005100002c10900f003144c04000d6503010200060782d4407207079141102d4000d44d021804204081240a00c1d110b04031020f0140000707440c0000801000c820010312a004a03100c2e07080302550760703043c02500d1103a0b40b04194024001501880001040ca000d001180c0301894010306281d020034080d5041d41c445c2c0c00c281d282500ea8910f00140f10010492150700400d00d2015140722040200140480328032070090350b40c16629207411700c0049000728282c404a03404c0004542410210090411189625000d14002003c601070303004400311585040410078207403a603611502901d142c440c42a01d007805440d524004c005c4c40140d1240381030400031140104180c40106410b003082000160850740b08040c040e0b02100303a100043c1d290755800c0300740c8640f903405840c003554851004c49000000e25107010b002080c41c40100305402170002c0341d0b002000b9015038450400c5809101910b0a680b4010700311000c005a01290005025184808281e80203600c9060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782938669 1250 782937419 782937437
    0x7050c0112020f0c0703060c0f0c26040e090c060f0906030a0e1e010b010e100e040608010f090201020f06040b04081605060f04060b0a06050409020717130510030606080402090403 78
    0x91441542c05506080045d5000c2c8805100b800054414980041c14030b0414580c100440c1c00050801c0200c0c02d0040c0c1080034480402005540c2a84120f41d04001101090380c2d5546420340207503c400c0c152070180452142d8171080c0c00a04051b0110780d0346100c13000700241002d5045c0f0030410b151b40b00500ea00d95140d199282e41c40111401c000d0803440d00a00301c0340710030f0341022034803007400c40302b4954901e0b040003440000001507484000100c50072800034a80345142034420b03800705001e0403da60100103150702c0e080d086d120380c0030303958016100103100764260b4204020341a0b9095130380c9802d44000d01048100700210740041c80850041100340603004c104450b102c219100c80303041c028110f0700c61500c06011410001040544d12441c014404200c9000300481d05124008106006074020510810341c00501c100a010301c0c408001081074020040e903986520001984601210a00c00c0030300541108000c3ca03040e6020740194416503409030b449520304c1c0c1c0c0c0c1303408000c44100007034001d07018080406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782939919 1250 782938669 782938687
    0x4060c020d094e1203150e040809030d0e03070e040c12032006011701090f030e0f0d080d14070e01120207120314060a03031b17030703090302070b07050c011202 70
    0x528000164020030b0343c118a10300b00d6042c280c01e5000000400310405260000101c0030700c2d2101140c800751220a00e0100107035a83e4074001440b03110f0b10780f400b0f40c98401c5080e40340a20b54801103a2402c282c00b0b400b0f5503030075075a0303000b0740344ea0300e0040d02c00418082c03520906100032003d00441d29021070181c60500b2400310061134840f6032031840e1003102d43c15000003005002d03402c50340c070344020074541260003080141c0d11616120200400f90b803000f0200070103003240da08140e80340c41d007503a4103400003485a0b0192841d40340c000c12980c02031640400841c181022008069921040180b059402c0e8032041e115170344072401150b01180c404125014103609005050108520040c00071010455843c0007075401400d608003924404000c100c3c03071046403000b03028400a44e1008184401c1d07080c000003180301d184245050151512940d0005c010140048204010b0a5264001c035100c54065000d03244e1041d21b50506062034454610082c0c210350107502407000d203501c0341900004161010700010700f07106020b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782941169 1250 782939919 782940029
    0xa051515030609060a1a031609030308130c0906090b100c020a030f020316140102013b0a0f0308042108010b1b060a1401140d0b0703090204020304060c020d09 69
    0x300b40c1c00064031004020020000f02c120304042005232a82000740c2503e03e50b54006140c06001459a00704c616045086c504000303207540d00c0c43c050070201d030052141039110040f480003008040c00942c4104042141c211f4805d01501007250030b9900502422407050464803800e003460840b10049825110b02c07051000304128208041010302107603180410307607c000900080c25034000500b246000c109010200410050b568540a0003140c140e43c0e00030425a4a003c0504001d00b4070409090103009560940401d0b40c440d44252080d031080610301c0e00c501e02110324001c480104010600420100e40050010300f510401034815a04068803940514140002280c2400415520001c1c026118806240c0b490010f440c46805000e034440d1500c41002e41300c0c002043d0400c0264094142881d0201042c0098480d41180d429141c016205560700e0800b0704d000401490402c0401c00140100e1800440c0144560660002c0381d450410030103d208410208803050030504040000310664032032008005410707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782942419 1250 782941169 782941199
    0x1202010c150f09020306102d050603150a09050601020709020903030720040c030b0901120804080d050d0b01020a2a120b0a1d19030c0b0a051515030609060a 68
    0x48144040f840c180341d8410b251170100d020705480d0b00810403032400d00c0100d8900101d468503840580650144540721840c0002107c2960000ba811103070000800c85840c030290250b025815041d9068007075143d5400f0504211038013a43c041e40141c010007800c00c000c80213600680703243c1000030305407440c0007040ea650421b482e13602c40800c40032880340c00c0d2540087c580342c818421159454102032080071021000a0607040c4140504000c03050050440003e02500d002074501401c0e80314126100c42c140d465020708141c1000d00a61805400c02e49002c099510115190b0400c660288184000c2004500042e162150f15400340000c850a8000040c0013030410003226170160050340c0c04441410080713030f1038060325801d043c00015252040001c4074004030006881e107100c400108400000b04051034100c45442c41880054500f0001005010701c001c1c0360342c02280100c043c0c0e240e0f020300080c1c031428090400101003982800c0f07501400010300c0b03820404a41580400000c203103450351170b1164030b10160408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782943669 1250 782942419 782942441
    0xf030402060c0a030f1d180907150305160905060304020f12100f0c18060f0e0406080c012307080f0c0a0b0109050714181201060801020a12061202010c15 67
    0x145200040980c001941e542c090702e24a02c6e0640074190300000c1031041400385050704150020000044a040040c840180034101e200703c60549500041c4000340a4281622100b543e0700c828102915014054401d84080350800b81c50b41d829952107400308140c0760240142c10350818032215224a026005010000440c440303c0800035060006c90b010608460300740c0c1c40382040c018541c41c45110340c403071013890100b1100e0600c0c10191380000f0b0034081750810b50b040503c80c1c025040120108004202245000380c030082030342e4000d55000070000704107200c2661050425002e03004c00c2150b001c030749804000c00841c002a207149281c00e01844000d80750201e015402da4418a06c40014440140c1d07600500360400b0300e525003011503026283c0503006521800d10843c0200000a4181d407045d2030300078079502080d401c6070007000b81c549d490050f036001c0d5110800303900004205030220328030700240e8491541640c44d022103800c607901c125070040d20207201004003076032007609a15501c40c0a1440c3e0299401d061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782944919 1250 782943669 782943677
    0xa020a021f0e030604020d020904080403061d0f1f180c090501080f0c0105030a0b04140106050d060602030c37050c01110c180621010608060c070302030f030402060c0a03 74
    0x2180c1c0100c001d2128100b001d8091180d0404424800943e4802c1c041c031b0000f80e0121800446622580b904107104c3c815a0300c02895203041024100c500039040031194040704805060b20304400a203451692183c8004c55468039154562004603c40b8120350f1001c0030700406091000b02403500b41d12024840402603000c0d407103840d02e031300041c0402c0c042400400c2c02c44048100070302d80d010003107001078200c0c04000e180010050313480602c90b201e550746402c0000d00c80d070742c250355040c41d503103c440081c0b040c0d02107062500040d041000002d003581c400411904425211009030585141c03070000d90020920f85d41e80a90640442d0354880c0062003520802410310344104020441e090a020016085071419a114030325a081400c0303116440c0c40b55001d40083c188a81075003a01c0f0f0f03941c00c2c006440f00035039510211200300341d400c0d03203125958154020b40c01c1c2c2e00c0d0700040395031555818401d840071344a200c0d4014010b800c14030044108003c00005150070a01c02405182440500340d0914600601c9002c180d00107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782946169 1250 782944919 782944969
    0x6110f0316140715180b0d0b01020606030c0310050a0b09070908062206090204110c0f0708030f0d020a12020d1410080c01050d0f0204241805060a020a02 67
    0x10400409602c64200c00001a00c1c2d01440c01c00c1500b260351103d2210320500070303480e0400c1e207010320f00088003004d07080e002240341d01c400d008a0044020601c41c0b02c05405842a88081012483d00080c04c0110681c010003c2c407071602644848009050050100000070b504c4482407045940ca0405c090301c5080c0e0b6030340707815080d0300d0014218035241000e0000c2c6108070300c0340c5800d01134004069008005a40050300403415a00c2c920108005004002003003c23180b002040400036107801041c1c52254a0511084030800c43d00c80e40160303224450010015210b1004011001c5c48402d140c000d004d0010702c07420880502c4040740381e242d007aa0720a0030220b01243e41c403c2d4026a1000c8603d906400c250702600000c2c0f81c604198940755610650300d00241030050200c0d4500c42320081e038204544020f0486815520f0780e944000301e001440c00082015004c01107490b158041512403214510500c80d41c004000c121403a24051016903072100404004500860709e0550258031102d00c0240000c000449000a07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782947419 1250 782946169 782946173
    0x618040b1005130e06090105040902030c0a06030b090108010234170703080a09081e04030c030b0709080109020315130605090705032b080709030605010e040b0a020c0706110f0316 78
    0x203c000b01c0d40162400054400078481c454840032071060545c5c0055800145400c0a8000a132500d00da008074103501c500d012802041c26035041d081800c41c01e000b038800d10700998880300c0c81400c4c2e00a012030ba0b402480d028050411506000400840c2100c043d2039056010940740c403800c0043c18800181c03094864009020030415501c0254140d100022007030070001c1070a07039510085248200703c003a20b4128050080d0300c1c3e82c403401134101c070015688074120203490b81c0d913403410b010b0704202102c41001084080707400244c1d040c41070184180c0c3d15802009080b030030241c001d00c80e0151078090300600c10800c803004281d001a0171442428010504100109061890482054a01032803484201c03010005445d100e15964507000c58184060f0031810002140d96580d50b003154241850351010707200d9420003000241d92105003568501440c000c01e007400d556620b00d00100c5c107910608190400a13408102c0801016101300c2c9020560403080c4107a85002c891145124690340111034001601c10041d01c1c4071003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782948669 1250 782947419 782947447
    0xa0806130b0618070305190e010b0108010b0f09060a050c0a03080f01080f15070c0c06030608280303050c0f2a070f06030c0203040f09050709140618040b1005 69
    0xe80300208440300f08030040e031204010302400010304031a050544610200d20000500840b10814200010041100c04403043c0e0943c0a085940740d114082800b074400442c002440404443d01200c178008040d190001030707024400e09900801c1001304200c001d00a129813800140240d8510f14040da880a0460400462406600c81c040c0d21441440d0700034100025007003000300c1c8030010505a2400301c00203689803036054030300d010600340040c018868034502280e8140c26034007000a070b40400040b922070805e98081c1c2c1003132003010004094100da0007007250b400280700c0e030040c650000000e080d00341044003480f00c041240c0c00100c08181c240000f1004070201c0050038a00c080b044000c1001044118640080b181a03200c10b0b00490781055102c413040d0400c94000c0048400401e0b50b07030003040b01a66078103080c200504080d83c0840c00243d032010000713440c0180f2084440700041c014109032414000030084415a1f1080c400e054000780c480c1101c040650390000d403403280d00c81c01e0b182c0c59a1204841c00c500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782949919 1250 782948669 782948671
    0x30b090a1e02160602130b0f120903030105180702010617010903030b180601200a141b09150a0308030106020f1510030f0303241802030103020d0b04020a0806130b 71
    0x41c06191041c0b00215621014182041d03966811680040e980c021850081100707001c070b41c000c90010351002501821400c2850024081d104240245141644400030091380345e12083c0715482c2d04c952001444882051000d034204d8001c2124000050403aa036108107240880c0035041056050350f4a450301130515405008008010388203e0f040100350034850030034040140060301c1d080c10400d00941c40b10703942c1c041c030080c0a8130f2a40541100c04840710b5252401e4600c421820b0001c6500035188010f0a641c40041d00c2c2604600040c44800c00b81da0b8201110801c4540e0700249038000320581000000c550032000850203004594003401e048410320089500e06066240c3c0c024034503605004101001090001d078400b41d07580b105907050810343c142400c401400900c950300011029a90301d444140043c3d650b180111401c1140c042c0380204656464000c90109220194000785800010740000300f940342e049034030a00c000c04103c00c07107484804075071405008540c520703441e485803240c480521500c44078407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782951169 1250 782949919 782949971
    0x20417010506131d150a060608061f03091403091804050c0913050105071107090e100507170415060f060e09071e0c0c0602010b010519030b090a 63
    0x900080c108100840d0403034012075071030f0150b00d40c0c50440988480c1d2050411351058060300407100316881e98240c0f1050020240d49003000d040c40d000e00000c455000305640c81c4600d00c020100380c01007030580445c00c9002c4244014408242d626406100021582240c0c01c0411028100a60301c501124060090301d520140d20150340d0820807003040000b1344c1c00282c0742d1484800f036425a61780d8070f40c0700310b03281d44900ca400002c116500f41000c20a80961082c01c1702c0503824800704a42e400c83c1c0e40d403101000c4801c000c0c0181501c1d0040c0070301c0c0d4280503840e0460360f0000280d20b82140c04061814081000a070f081d0350403101810380340225021400c80d0300441019200348211504c40c2e902c0c0800250100310f408400d180aa6590000604003d00070741040f1800403c00550510003000e00d07000030881c1b0352035481201e4030b50b2042c40100320b1074414440c481c4034400684a880c41c5c107410341c40e0300d00000f901100c20401c05440f944003105c2c0d521108500742c0501407522004c201a80200d1401100700d400c1e0201d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782952419 1250 782951169 782951171
    0xb0c0304050a060c02070506070b06010305182a030303070504170705060904050403030f0e0a03081609060507050a05010f0207031b02010503190212040b22020f01031e0e0102041701 79
    0x140004650301090280c0b1855201e5030000e045003542000343d082c01c0d0541d120560002c004110102442201d010031480382c003090381c0401c405e5441a0b080905001801031800480c1d10034400290054070040301c80ca01d105a246443c216000c414000074036540c000c64800c40000c1e0702040030000d05441c0b40001e00700306486805065480d0a10020898134001c90701440c1c41079440700040740615002e40d000352041d10310548188581d00c40b041186030380754007081d004c0700021503100010780e50041c4841c10710310483c030f1030f80d61007451403a148044610b40c101800c03d440c0c1b8040e080e140800a002445500d00b10034009002503107500c41c90a003d044404480d248074582038621840c00e0050707910004036a0b0114411040d40303801c41000c90340348024011010f501e0081c004290500c0240302d8054429403150300840b996031401840d4120700002c040c1420030080d04240d41c2d10440244c1d600a41048520401061401050a0f28503c50100b691907103055003e46941c005403e100b1640c909080c80084800307000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782953669 1250 782952419 782952421
    0xa0512130806010605030c0307030b0d0b011806231215010e01120302071e0b0310090e0a050604060f0902100f02010501060f020613080f1201180c080a27030503040b0c03 74
    0x100174107036200041480248240010000e05014000e510041c103148018125171803200b4a403074456a204400c1c010070229440100e00d104010000e40940c00c05e80e00900c20711482120b03c241d48640395148072035a00e0740981c1c2003802c0d9640680802920707a80c5190311880c0440e95242c111200380000042e00442031419039240241c000c00d800150f083d04950740307075001e202c1c1a10000101c50408445070009000c045d800014450329020800344070050340d00c020420803101204400709503480f40c903a50000d055070002c40010340820020780c41401d181c02001c0c4041241005507001400c04007242d01c245000c1101c0c5122580d0840c0d0910401d40500607601303001440c41d0101101030b58901d8000c121482c03052546003140108a11401030b10040799011024035200c034007500744400107213024003512004d440c05004d08072100c21140106031000e40680c448016613142c0c801c030b1501401e85201c2c2e0035640c0340c2612022071000c95160360541c01c6802907440701d8072401c013854040c40001020b05241e942001c248 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782954919 1250 782953669 782953679
    0x209060d0b040221030f090307050a030c0902030601030219021b010905030a0b0c0d0203101a0a080f040507170102090a152106080a030c060b01020105041707050a051213080601 77
    0x20303007803600643c04980043d80420a880c034441070b0141480c0103006404045000208111000003600f04803504809a810f0703251124144015130b012403002602d01810180b04124108461303005641141040c0b402514010b0f5560814404151510204c030040c4c6c80607681c0301d1030640e040d18013813040009107000801d007071901000994030b1084d00406080040408003203607154941004540c0100c001200c255102d15012511441d1141c80f441080c0c60480440d0003d0081ca6030301c2c080380e82440c400c0e210700b4401d44648800c0c0280039401031045810b031140c108086001e4021105148229144200142e5540c4a120038000c0781c079642d600c09148045041807605699400442d00c20000c1307851201032040754007400750341020300902c1e4424071032400f65103004030a056014030f00094441c00341300c051102e401c030b07070004a003281c0342224050510380001400d21a8082c8840c01003400602031380131500c20400c5904c91508004441415202940d000648070324411816800a401052094007408032076140c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782956169 1250 782954919 782954933
    0x40618020f041107050a03171614090123031512100209130c050a090b030609010302041d03340809011b1209063e0109020d06090209060d 60
    0x40310803031080da1180a070380700700381060b0141c91045404c217084841c02810f6050181c40c81c00c4004205101005c501c0c00560149480308103028141810b43c4c03454035a0032082c0656050b600446012410003110b402e02184400031122104055900303087c545640c0c4c144403030074180c0711486116450040145001d4903203480700104045c3c2d2071880410000d40d0302d0449800064010320300c002d01c80c8016245c84482081143c3c00800703000c1108040d100e44201d03d40f1144480c130075010031102ca940c0706078804010700060801c2d0300042018400c1070090500c00c01c1004550f07065412580e8507103c001e0140350190b11040c2580c5016550f4490303005005200c60380f0b5140ea000c03034498001c009041c440c034049003250001e41c080c6280391003a000300b07842d000b80541c1207009048600c24406c05000400c401c42803500d0340030750500140562090407500a10f001010035402c1e42140540036000365540c0c0314a14030150701c039012a5a5a01e200f040e00207442015071040151029001c0c00c00390250601007481c20005c0d02d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782957419 1250 782956169 782956189
    0xb06030109051320040f05010503061920090f09010f0326120906010501110a150b100c0606060216030828123e190804061802 55
    0xc1c005011886a40b044102c10262030720102c010b002000c0e0000d0748410340c084000300405803000319410700401026004140a40e07000703020b078940c1074001c0e002180100354500346c4000040b001e86000b01d98210782480c41403d600219900c58003400f0700080005081c6002e81318040040801c5940e081e4950604c40c100c016980346001c0180031950004001ca40790460b0f8019090713075110f10010303640c0c81002940c80c908a030001d44001c07c10b4441d040000c0340c02d6000b8020030040c10140300003000c0c042c4c1c1c0d80d02c130940e00c65441c41a203e0040d948429814298a80f407120071410740796a03c81001c54926460034208071042076000000315000760f810001c01c03038101c291000403250082c45058403030300c0c112890340c0d0703420781c00a441290001030440c5800e41c98002c0752856186040c3d141c20421400f8019050b1107101d034031114801c408444008400c80b00401074100603003211015045401e02072034405000380f010080b1070200224a032642004100081400b036641c00e060b1403440d003103034623800754007258118207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782958669 1250 782957419 782957429
    0x918060c0c06012102040c3516031d0708060106020601080309120309031b1903020612091501030b011502010b0f0f190902120112080d0b010e03100c02010e010b060301 73
    0x15051813250300c4030341003050581500d50018404c002041c1c2c043d0002d0010000c0b20b03010074800701c0046c1c02d210008289a2040b1a070082c2d00c503481c10f2036135201380060304032602d0200002403581d584c400104481d00e45003400001c0358108010a18541040b006510b00741059112104552060f401801a03050100507110040002d840c11580300e401e49c1c013280d0841c041c48003241d07014850562120400158030619010303489090740c1e00400c0780d06078229a503000300c09000c0650070440400a9a080850070440c2a50100c600019205985030400c1c0043c0b2102007079005a80c580181c2c0010f000005210347d1403c0e131403007075000820481d00b469000c0380d1181e082c1d2034880d2140380d200b02240010f03101c55400c42c450080c4940154286515000710300000d4102c0e401c10440000d02c6400413800b800341c00b4100b00c41c10740001c0c1d8582005030f604810006050f0403c50f4078100039075015240d0032b039203040290040340c076007007100030030301d508910700007800c64520b8407080c0c2541c2c0c188406034900d13807608400c507030560b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782959919 1250 782958669 782958689
    0x905031b031e0a09080f0a03030c0c02061614060403030c1d1012020f0406110d180b0904021b010209040b090621030f04030804061704110913020918060c0c0601 70
    0x681030241a038661301654401880c1d805061076000c4c2500b00401d058840c1d41c4251010044002c031020b0846a185104400941046080080441d200421481d04221304c1c40b03412000c2c42008625800c43c200941550b0480c0400e4a80446010581e040116440d030350962100010110b0b035a00000b03800f0950f90900b034006c1c80b03602500501e450040e501100c10180b4040503503990307075071717280f000038521005220b440c07a00d40150741400d04402c4c482d8444003140c040140150580c1400e02c40e0840d4183d0091b088030703600503400c200009480800748111418400f000740016160303c80c1805010544061a240d90f00c140404810440180d0f039032455a07c0c54101c0140c050410108071607007520b9441440006514284080b40000170401c140c4024015110300d80c0e250601c080a01040d00c4407d10240c0d0020000451103104070f0160510b02002d56000c1280c50030401c3e0900a600411000c01054441100d00b00c44032400c504000000c2000d035802c01e400190303140c0f811682d42c074455260403040c01801c10308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782961169 1250 782959919 782959927
    0x121515070c09050c0403050f0c0306011502190b1503070509070509040b0a0e071803080a0e01020c0a151b080d090312020d0501060806040b09040305030a0f0905031b031e 74
    0x220840704150005000144410030840c200441600b105402074401284c45115400e4030402001001c40c050100400c0600100640c0c3d00b8001a9240e402e040d0a402045100f00c2c03402d043c03440c0052200e201502c0c0208101803040c2060401c6001440c80001120b000f60700040c01007016031a000083d540c081580e241c00358031081940d001602801401c055650300c4480040d01140c07010300580f24600460700c80e15010304007c0c5591101a089040d448003034030040d4148098400140909a111003813241481038442c0d1014480c00240800b1568202e07201c0c0e0101c8451a088050b08152448180c41e040c1c5038146540c00c80f581c9440c2980706103448101d850740c98116441c2014040c0e050b101142440c41c000795100c80e444004c00d40105424443c0d94000780c0e9a17804140f0300d00745031151500b10140a00366400aa580b900c041d0342640c000b800c42d40c0a0303552440400c03606080ca20400188910403805903035245111840d0303420241a80715645090b0f081000380d42140810101b9040d01e611108d4482500c0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782962419 1250 782961169 782961173
    0x8090a030305150d11032506080a0f0e070e0105041806020c01020c1c0e010e0d031d0607030206090c2706030115030b06100203040609060c15090812151507 68
    0x1103461800990809070307104c00c107420845160089050701800740c0c211949005d0000e070500b00c001080362806186440171000344070980c031464000f58810401c51011425110300c3e142a0112020503a202c01140c1011005011003442c0303082c2c076801400c0c2218184107490420b0031210074070b0411880180303000d90001e0180c080b04000c2d01664128820002600e5804461070112007285807100354520015000880100813503014442a031085500a00800c0e072403026070760162200c519803a0440d0f8000456107000c0c24513a43d0400400701648a03901611141c00e20441940c81d00203210fa080d80b03d05500900c05902010b80100088400131810302d5052545070103010034010b14064920308082c03130441c04040103021031000280d000d030308240c4400c10071643c1420200d8481c043c500031a0000740000307108004903445010070b030302c2c40d40c007039414900e54007000c030941802c0b180000340445d42c0100204403141c1d4681c01e800c0850344010a004180b025001c54000503580503003c0c480d0a00408000c01c403641 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782963669 1250 782962419 782962441
    0x706030f060806130b31050c03030a030c080105040e030702092e0e0601080610030b0609060a031d16050d0320061906030209040f022809060608090a030305 68
    0x4010200b06040e0b80543c104104043c0080a103610107032021021140494203010b6045034511160034030701e0008a2101080c41a07114941c0d4030401a1564130981d516101103aa09100a16200d0704986000555009038680640b6006050340820b10581c500003500b0350403000803040703032034181e8100c0c4c0325241941c4003146080800c80381000ca922200051035104114403d12140c4420385400e441d400049a8400004480c000d500320b5a03103030044005052254103d010390401c0c0310888004210350300b0418034001180b4a900283c0d40200007980701d03080013041b00c44200102203000400740140c1200c10344118005a2035055104844c041c80c00301e017040301410310a0541e103620341c26402e210b03440305405560651317139000f0a403242d4610080170441581c206455200d440c04407035003d0310b41c1300742da43c0d141c0f1090003c8c80b080c00145c1c4c10080b81030b205448452940002c01c0c2e81c1d552050b810740ca050501c40b00700111481c2d504201c1c2809960018440701d0940040c540300265814500401c00e40c5c1c54042c0d240e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782964919 1250 782963669 782963681
    0x80601030b040c09092907121d0114150619050a09120308010302040501050d020d020f04021612140711040f20031e0705040e04020a0e0414010507020f0706030f 70
    0x41c11444c1500d8403040101010404264039030307031b041450f581441d6110a9100c441e0603a40700020400e07040d8500c19401283d0401d5250907000b038503000118102000043c02d4406401017800713510792500070040c0c00d1510000380c0c1d1040340191280350070301c0403a100da5001310300b0030808603007070040125040b002c82e48070701042c6000e80301c111070100c10300d070b501e2502074400e0a081c0400c9204a082c40000f241300c1c24401d1170380c2502c58000f418400c20788656028068290040d00382c1c56003040d000c0080400010361042c1148166111b0840300c0c1001c651600f000341103920680c8208070580c0100840c00c080f800510130390902c02d03000c85000541c0b90441c4080801005285140c0d48848100d440001c035030b4103014003940c4903215420b40c0021148c520030400312101c0c0b08031101d6002c00d00038002400084035800303019611510260241c82041d440d81d0941c80e07004402c0703600b201c0e0b4006110400a400c0000e00807160050002d00060500b5245940603d4690003d030082c101010303543c10080b17606c0c24080d0840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782966169 1250 782964919 782964929
    0xf1f030c080a060b03011a04020f0d05010e0403030b01030b010807110a150609240317070c030b010503100e06010b070317100f150503060d081e1c0501080601030b040c 73
    0x12041035a512040c09480300050042941c11600c0c1c075114034641e04060055280d4003240c1031640c180211000100802900000f4910040e180b0a028001584181d40700e0f0a0103007110107400700ca24600784ca00141910140782307a0b07904040c02c2072044507582e60404441c44e040300301d605003240108403680341b00d032404100340405000740b00341144ca0381d101400359200b04152940c80c3d03401d101200504034125040c000d82c40b084403202040c840c01b007000c902010380c0c078007054041d030040e030b898110b05445040c021310040d0429104a0840c03030041025144c20800803440340240030040c401d180703100424544078841446001040240000c102c01010310910b4050600d290f12098181c1c20b007044070f4203040325142c5000f0400d00395100c0e00040745a4030031a40000d1928000c0e83d032a45075079148400c2c0034000100d03000884030724500b031244000c00c204005000101c40003001c151a1202c2503000ca08000c030b00441d0903110080e20b0400107000c09c03c00400c106066070b403c8024503405884a00c0e001c01180016400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782967419 1250 782966169 782966183
    0x702010621082206111c030e030403052406041503060c0309020306011e06021209100e061c0b04150306021308073209060d0215040f030c0e0f1f03 64
    0x142070500c400c07100380f055480e1035442120000c02d4010641d9502c0c100c2d410051080044000c01c450030307119030440490031280009a82c1010340d00d03550246001025038584001c101440e0b054641c9440c074451055103d0400c071002e00000c0c2203070440305888a4140070152003ea02c5246402400d40240c001010080c0e014007140c40941c2e645200d4030b80480101c00404940e922484005413062000035205840100c0c9505203103415000701c20414008412000c8506005884c410b000309581c907500900703030110301007407072108412000610340119810043d40900c0746142c8181c414202e000e0031459420b40f903001c1001a0307603103040780e181c02c584c51b0a6030100d40c1920492201048000180210000000001222445010500c0001c12450b403806084517044035007200014070314600800c8101c1e0090029141000030044040281c08503403086d001100750081790742080080003c2e0907044401000100036210040c205000890040007020701070091344594400c40707121005005011030015035202c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782968669 1250 782967419 782967457
    0xf060f10140f040f150503060307061b150b04052202041109030708030c0f010c170a060902180118060f080a06080a06050403030b10051b010b0405090a0b070201062108 73
    0x20080000e600c03801071201e51175140c8001d110b40f6000f072054a0182e00000c004c0c2480c079080000031a038020500030503600130400205074201044040c9020210f942ca00b05011030248602800d02c001c3c1c0704094990480e0103c610500b03440e55480c4c001588200354101d9001c07c02500d82074140440b80188030025070715008503c0c001884250000040900c0d60069042d50107081160310130b182241c200d0030280b0301281800348500240e160600030658400e4644030000f071015200c954040898004141f100d1304415403050740c1c0007641c0c10503450007018100c4000b1384803481c1040300082804807100341107024031950002055541e01d094000d81c0c040e240c0f400403107411318090308040d0081e2000703070f900380c0102c0c2c6001c400c0c803001d0501000000c1c02d0f00032500c801d40f0f401d20041042800130580d0090300b5095503a407035071070119034950050a01441c0b41c1ca0060070441000c0c1000703030702d00b0b402070a190250380c58680c081203108200c1500010a101004c06041e222050303080624142c4908509003140d410254 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782969919 1250 782968669 782968679
    0x1514070602040f0513060b12060402130f06020f0a0c05012001090f1a061513210c0b0a080118090503071a01090c05030a09020d050709050f060f10140f04 67
    0xf940c03000b110350031545101030000d01c01c1604200c40c860300132003ca4260800c800300c07000c071a0600054000001900040c90a074041549010790902c68000025040c40712104200c0b55604100a92464401e8800b9011140e61a41c5031500c0c0310350b61050505007d104000c010140800b0710010750500c101ca4001d20000d40300780703002e0280845513142226403480703010401c0170921001100d00c1c81000c018080800c0c1191404141c2c0c0603401818a9000e800000700000c6802c0c40d0300c4070004c1d90b6003000c030110740c015800c51070455100e0501da00142e40d03048003402408007441c0d2004c50941102c00c01050b43c0703c0740c50040c082601420082d00054084c0c840014550200040b524081400a141c0c406510a0340d0300c0e900f400e41a0b81c96411100c0000c0c80500100e12503001641c40180f9446c8000e00c00342042c01c0c00d5680300e080c0115913000d090300341d6423201046990305000d80071982c0450304071082094050717140006580d000702540f400c010800140f910082d042482021100d40341c580c010700c2502c507581d076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782971169 1250 782969919 782969939
    0x3010227120d020312240d020f060f07110613030305071b080f0705010311120c04030203070806070305070c120507030210050a061a0f1606180327151407060204 70
    0x80540c2e540c00b64645c0300140d000c140c1c9070f006041c00d1070305200700c10003204540100a0191105071060f07900c0f42c0060b1907440d070f0340c2e2003800920000e04840c50792921030480342881d4280c01104100740e800361604200b5920245501078060b4242d0340d050401e20740310440c50600400c1c616120020070340300b1030f00e800041012017000032100c0d8038000c1d1008540070240c941d4011802d880c030910790080d802000f4810114030100301c038a00d43d404440800101c0c00c00f030740ca400080c0b42c015035520030704254101c0f0b030620801542c0342c0507981d0302681c1401c150800400c1680c420515120000454080040c0802c00108151003404080c18103002c1a100f4082810040640300c01440315100d003000c4021000701c40005101407005460740e41c07041214050a0202240f4078150070101c40000f1a0303080c2d034031101c981d034a003280c0121300017a90095580703540207001c0c0e00500400355190f1549107040741b2103aa0402c1140b440c1d904107402c40d9101d240032100d00004440001d507a00856000070800390000c0780200e82c500d02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782972419 1250 782971169 782971177
    0x1707030509100c080601030b0619090512010c05040311130e0313230415030c091b0509101d0d05060906130305090f2b0201090503010227120d0203 64
    0x1050142c4001d812612440c0c800c0f41c4940014a000c5120301c2c001400d2980030368855441001c010340744629201d0b01808054800c0002000240810b920f01000d11140c2403100c0921903002c1810b008201000064202a00a02444c03000400c2d19000c80fa40120948031480d2140c44800000410f001161007021180e44036080702240407001800c03006c0004200711400d400501c50300c514403c450454210300c05000140002a0000c50b0507040ca0600200159a40010200910071918001034031610324001038920303000d203402c1004104051041929071ba44115810600c0d03481030a22405400000780034003843d42554100300d9004000e21a0741050110224250740700716400025030b84140e465041100e03144204038400780018005014011035400c001c807400c00210001404d81b0112030003503104000003150103d220000f150761910000841d6003103030001c00503000131402503040011009107250400000d042c40038441c8116001c0248075103d142c01200c1103d915400d9401c1000e41c080049d40d6a40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782973669 1250 782972419 782972431
    0x7240c020106170c0d021314090d0905040605060901030e0c03031602040c080108060c0a0909060303050705010c0504210f021519020c090403180b13030510060803070803040317070305 80
    0xc1d41001003401c3c03070404501042d07098801489034008510540034041c20310341c00200180c03a10798801c0c0159a08070b0360231010f0310a900b03c2d4020448102c0d03011000304150038560002d030149003040300611280d03a440003a02c104032000e10b400505511402c82e040c2c60072000001c011380500000840302c00741e2140085044245000f91403d01500c55001c0c03040f00c5007042442500900d40040d0045001040940700070f216094891070200d030010345401144088406682c81140400c40001d40300f803c002080c003036001c03440d0403414014101841d082c103121101404400560000c542c4480c030504010350207904076290741d0068142280d03090f48c0400051140c0c4500d003100c1c03a04507413580d501d1040e84001aa060f240501820003000c0e5103940c0d8040c0d494510380c5240c0d0a4212146c0740214500d4806405410f2000100403800f400d079203103061040c140074001c2400b48185041c64014041d5010010440c0c600c540d0006905640395203c0c14100c9803c400b402e120343c020801d040901ca181c641c1500b10500400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782974919 1250 782973669 782973689
    0x170f011b110c092e06200a050601060c1a0f070c050102190e2103090d02041e0c0311040b12060d140610050102010b03100e071d091204060507240c020106 67
    0x75842500703100c4c510b0050b10071880003880000113229086042d002802c48a525030044510a4286555107410f08000360002c80004400d15003540074011600c810803160781280c45d481303a80741000034420411400052825090092410f82c0c142008025070494a9584943d000f50040d08450303000240841c402c030b05850710511b05041c289280c00340300302c19001c895203130070000c1d4506102241440a6034860300c40c00e90384155584400c038600360703043c80e05540310400503000080e908411a0701804480756580741e00710102d0107000c140100c2006000725402507111740110f240341d0755480300040c01069841d80c01003084480440c136201c00040040e8040c001c018800f0781400b201d4a5070012070880e203601c03000d00d5055002d00c000d10006442548400080c0660409a6800c1c60b1580e5030184648640c040c18900d80142c20704009459501f40604043c25881030f100c9440d091600b500140280030b900e0700541031082d8900b000c10308100c8100310398800d1424400c20300c06100b5464000e40241001e202e904029 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782976169 1250 782974919 782974981
    0xf03031503070e1005150c0307050114070309020105030c0f0405060408070911181002010e010c020c090c0703120f1d010b0f0f030d0c1b170f011b110c09 67
    0x980d00d0b2142c95803083c1e003403180b04e0350b8881c5400e003048a8010400c0c81c982521604206201540340140024100309000d1b000114009460042400c03c80d50004c003600c0405181020150050783e2001c122078002640071092074803150701020f080c095102311342c05103904ca103000500048411010404404440324a0410800c464100d480c0114510403004d03241c0a44509583c020b201303203801d510341c010f80d50741d0348000695180121442c07800c45070400d1900c0056408848021403a1800f82c0c2c6c410740c03140c18030320014100302041e50060b05d20f0543c6141103500326104d02c0690721510040c3d2103407680d99030074840e036052800c240052900800c0b10707244490051003a11000021428207c0e4045130700344000e001040d11440d01c490888110b642000101e900c48015002640d05649880c882d5010f0300302c07408002c1c1800d20500c5150701d04240402c158110f03034100005404d02144203003200c0d00c0302e02c990a1141c2000d050407042414138550541d11584112500b00380300319800602401c001ca8071203030501c0049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782977419 1250 782976169 782976179
    0x30908030a090303031a03012315090412030908040e09010b0d031b03030612080c0d0206040b01030201030c12060312020c030a020616150501030b0a180c03030e030f0303150307 77
    0x360700c1428000c4002c100381800400019202c0e07401549038120491381540c9041200c0c0000f409d50302d41e50445040b49803085011071040401665642d04240320311007400004101102080d2036200040c03001d4446a1300c1c0d03e60118540c065088000700b00e601004c000d544a841d0704003580d80500690751100c0795841c1246400c25070910320000131016401d9261254040c001603240c602510758034808808141d19024001103d290700d400003401544960100d5854000c004180703440d2008800543c021540b0050902000c940c0804002e03041d01e80a280100359040400300039070715010305500ca04829460b0010000a200c060305618105414a40c00d907040700f04500201551040d4180010303600c52010428025088030300580301072883d10582c4510741803844240207100300da10036131082d1503094601d4104000c0070580e110301e0f40d5042940d071554202d818241c482c0c003d01034450100038280600380c45600b009507010483d00424002c1e983c1140e90301d140061200403240004a04203009214809012407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782978669 1250 782977419 782977423
    0x907030b0f2202150f0d0f020406180605030a0c090b0a0906030b032d0c03030a1d040e0a0b180d230406020607120b0604120309170c1302090319030908 66
    0x20002e500103000340d0011105111145869100d500380e014640700421140140243c1801074070050b40e0300310001612985000c2000d0140f103a03030140400410865201400b0311a040010740740c00940502001802110405064540030a0313a007162050314408601c90064940c0000c11340d06488150341d040c804220b00105250340c41c50210108017040c1c1c0d20014400d42c203100da1148103120f80941013183d080308040e402107411940b00c10f146100044500000706001102141144210310043d241045808900d98100d82c89000411005181e1030b1098040f03284a50540004200e080c103010903552000701d003100c0601401c651002c82d0300c0201c2000c502c11540f8841e01d05440450700300c0e070041e050a170723101e90b000c55030403040300c191805955807800100c100351990720203080544681c035250602005507007009002d2070016440b000000c42040054070310b5502c0410201d0b442c4406843e0352140602a05604020340034588000340c0600c100e40403051500c07104007035000003074081c0c0c48901035203440700c80440d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782979919 1250 782978669 782978731
    0x180b090c19050a2114090604111005120603150a0b1302070b0f070c060c08180c0604120c051f1209051b0607200f01020615090907030b0f 60
    0xf00102e41680e0340303407651421801c005070710040c14000c0013443d005600c203e07208400c002e440859a6901c107004010401980100a0710005801c889400709410710480090080c80f4107940344800b8034903603004c11802c1d1020880c0d240e001841c3c88800c10342e0301c1d04400000081121127101ca20511500060031030f42122403080304c0d007581e0480f41007080d40da03c89888100101029000c4401c2100c480c51540214035a44074075000c221241ea2002943d00700140f00b1075041410900f6044030760810490175403640d9030442114222035040310b000c1c03802104d41c248902e8044070303588416001400c03900602c80c0060345019100c0ca05038291240c00010200c048290202e03944a41e0040040d4004600c50303100031012416581c1c5444010422460a07256940f1142c1e03082e0004456110050180d400c6074640c500580078860421082c4000c290600d410001d002171680ca2080d0140207000180c0400e450400030702c8600b02039504031a4603d214200240c941202c407508880f0100468091000c81b80341c414104070781c1f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782981169 1250 782979919 782979937
    0x3010b04151202060403170403020a1502100c03020904091214070b0708280e070911030112020a120c140616030311130305150906070207180b090c1905 66
    0x8860780c82c2002042280b0045000b07007aa401001400000300140d6026404612404203201050701e03503185105000554031640c20228864040040e00540c4603130001d000c4440080c4c140002c40d0380c1c0c40e06d44054000b88a0144c0c001e40241c10b014401081c840b002c0c3c01c59010040d20f6980c1c50b251304d00c2401c921068012003500038440c2d5813000221707801c03900c9002c100390048a103001410012449000840d07407018100c900340c1c0c0458880c05141c070905020300142c0000c2c40550000d00c00d500c994040c100341ea101c1401000d95041074105420b0542d140c043d4136202401d100c2091008030360301400d20324072030000d510940c00c800d2040c44016031036041105c00e9075038031411000f0301e48280b03250f80e40603000b030440070241d44a06801440400035800c80d04c1c0e10303000154040e2015110250882c0071001c0495401001a683d40d0710020600208950025060046482c018248030400e5a0070034a1000f500780034145a030b000c26400c0500c800010000c00405483c00c80c031151035094046100d00359002d001307018174 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782982419 1250 782981169 782981201
    0x30e07090207150606021c090504090f0c08190b04110303030108150a0b0a0303030b0114161e030c0b0a0204030516090c020c060306190801060305030903240c0721030b03010b04 77
    0x111003041482c5404845422410080d0000742c0341d00101d001c48400b22f800b6140751201c080110107000310042024060001c48000d0008500d08421010301d07010040b070010150240e0741300080074020034121190080c00d001702a29a2940e60396510f0343d60b0101002e800380c1c40c0708d07a040826034001c000d105041580c10003400c141401859a18144d004003a11240b40b41888004c003408281d0410300c8005204a018040d4549607100003402e003001481c0411044040c140b86000341400420b40180351010401c1d480202c045007a035480013a80d000c0d0003107134001480d0b44103038542c013100f2850180041083d03861001c0d0400ca1800c05000072642c84c03950b5045250401d00400c041507050402070301750000010b0394029404040ea0300d41000d03007152202d51060361a070300b000c2a0141035160501021425008201c107d250840c0c64290b142d00d9140c0c0500410702c0c030f000001d000d40422550400d01070f0312140581c00701c09209002c500241c0600400160b0520a52901100000c02c0c9081d00c1441600012800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782983669 1250 782982419 782982433
    0x3090310020f130303021f0917090105070515060f030a2607021203070b061504062609150903040f170111042c0606070b07030e0709020715060602 64
    0x840600075804a07607042c1800c0001c000302042c4400c0b6500c410700130361007580104081c0000380040310020541d00044842c1d98205941ca0000c5081624040c0e22002a002c0c0d241d600c40351880180e98510401c070006069004007040b00c50070340041c1080903c1010103840002411403039104040e111780300b52400a00030500031200400c2e4910b411803484480441c03814452900d1031540001c0d21280d00c150021660303034000907407c070800031825141038000c034068808500d1020f446040700b841c1d0045000300810400d500c000d6030b20700420184c00305001c0710b07448110011802c002e01c0c0c8548070003c2c518052600c40402003c9408000000219411201040f001100c0a802d00c4440b0103038a44045800200c0d64980120a030300c005000c00a1006101c43c800c9010902511016107404132040d61640411740c0c0b07220704103c0f80303132035000451b003485034081940142992503160540080c00364014184da94401c034031010800200981c01003424500800d41110100c0103a001c01051b140c19005240050b00281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782984919 1250 782983669 782983693
    0x231e1612090314040e01090c030227010915031406060306011d061b0f120310060c05010f0f0e0606091b030a0e1006090c0c0b0112051504140f030903 65
    0x640310810051180c507050b140319400f4544034840e41c202d908070300e00f10070101e0010018443c02c1c0c410300a006d881c6040030b5007061a4400e8455014101e032225040d810349d2000c540d14160b02c140215000b03404403a0006d000380c020b070f100060080107509040700400248502241062034040700384c07403103a20140d481000615081d5416848020400c1c12076800c001d017801045000e607800c3c030a00050a003214001e201c0c0d00c2d840c856082c0b03801c1c160450b90140800400034401002d001c0d180250a980385030030307c2610302c03400d894064010300c0341c44510054940303803884040c07aa100c160400c0b06030602000c1111400c3c0c0762541080060b040c1a180d560740000141d200709002c15402000d941d005241d20380000301c48a03030300040c50409100d4204121155030300c400500a40030720b849910848803c2e4940030701d616030507684980320041c0600a40601144940c144420488100600703001c080c2180b042035464105440c0200e40607070b8841200686004110b4108900000002641c22555000380140703100e03003242c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782986169 1250 782984919 782984921
    0x9031e06011208090607050a021f09060f020a0b09060717090307112b030306061106180106050307090204030c082407030603020d03021f0204050a0306231e1612 70
    0x142070110f40c0b01806100c02e02c0c040c1d44d240d0140581e24024005005020694410054821642024401804014502d440406605c0f003c60700980303415082403666400c0451069181a4a54000a2002d04508104211301c42c0100318a40a00c04907128510003084105083c4104202169515615481030201c0d1010612041d2039041420024086c503103c0030f07e0510742100c03460710611000781000a01410000c040c0e0510600c0d00410040c42d2548031081550720301e0b42c80710005051801c2221000d1922000f283e02940305100500d030003421200c1c0d41d641c0c0c00c5070101035001440142e0388450790040020f04c02c200480c0d020010120020800079207048100800c6000b031010f001c5104240d6104404070050b21141c0782e8000c5170b8060380041980d18104000c0c441c01007061000c064060b80103020070040d170b480e4250b0340f2095a501000118603000c00c0401c0d40faa2804000d034044005c0150410300880c03000f2054401c1039003000050030b131a29940d80c4109601f070f40f681d200c0740000449800300c4084000203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782987419 1250 782986169 782986199
    0xe04020702180405010204030219031119180e0712020a2d0306021b0d020c2e0908070b0f090f01120f0c0207080705060a270b09031e0601 60
    0x801000c04070142950b451942da42881100d08480c0c6070340c0001c040c000d62038054504100d0903052650f001880d81555210601c0250710301d296409070240440521012038803049600281030005081300c22910f802444e03201500c0640c01007915070041c0e00740411600c04905640b0b8490f500034105142d0a4503001c540c0964102403c1c1d5081008842c64035500c0d84200000b1080096001d10800350320b403a1401d102010300217904c68030b00765990100702c1e20300c1d0031900400e151004030011038615040e10340c0300106054129800389036400d48001c04a880c140990042031040035182c2010031102550745881324a09036100c2c2900f8902c9490040c060403580f40303072800001e68400418901000c1c20240e801150741901c7c020003152a201c2c5d01e60541d10907060307040122800414042c0020000c040c505800700303005c3d10900e0001000c100041c001c0004104d4440ca1113140a2001480741c012642d94080501c680c2d0499603902e4801d0103205a0005000301f010101c41f6551203000107408641d203004138510303c03540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782988669 1250 782987419 782987423
    0x1030b070503100b03190509060702060109090c080d090326030105060a1b140d051e2a0a060c0206071709010b060d0204051c0b0a090c081b040c09060e040207 69
    0x900c9a0700420090743c041e000d98010501d10004806c0c001514501105907840108801d5179503100004000c0c8081c0c1c0002c1e400e044541c80400014039030784038240300001c418260401c00c282e1041c0c4a2141d840c42e803010300d0600f200d006d900302551388100c080f901608002e43d1020045640300510040c0030a24094000340340d501164242500440388005400b881400f40c8142601c1b0600095a600c500c11414803030020f02e10313a40d103040c5242c800b40d0090a0142c40600c0301e0040030100200c1c298002400083d044150000302d10b550344001031107211041e80e540c4502100326400c0d4100b90382682520f00018041e401032015850f41b4801141e0101c1c40001d00740002d160030142d43d02d0700da450314243c0301c01004210004001c40056540d608201c01e00442030480601c07841d42031804520711010859005c20715030401000c810126043c40a402d00b0801c03026a50003c42c141e001d8000d0039505100c02c4501c2c040d44180aa41c1405240791292091f168803006119a1000c21050001c03004145001e83c0100101c074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782989919 1250 782988669 782988691
    0xc3309070509180d0c0203120406080c03041a01080a030f1d10090b0703020c0f0307062a06050c070308070f0507080c0a060c0f12020301030206040e070e13060f0b0301030b070503 78
    0x110500126500d080501000c44c40803d500c1000c89082d03040034441c2d504001040140c1525081c58803100510103c401001c03c804000044041000c2080e42a140f028044040ea030f09803155840b0b4400c00d403181d2403090101d02060347c0441c0f0517600d5010b200c11400c2d42c50f00500d041a881030010602411403181c401000401c00f0a40001c81c540980c4005000c501d40a0ba0003011150000d01c1403026031507030b1a40c000d00c03980c4200d1081100d41d60145025003e840300000204440075000d8203c000078800e080003c01c06030810b4100302eaa0381c4014040e081c0e160003641c9911554071000030a840712484400180000b601c1006402c0108171114010110308400ca0300b202e02044e11074a9890884132021410740000e82180c04071101e0a9010001d0016000310000c21441d552460f400210140320f40d10802810002043c0040c1c00319006441250101c0c00c042c02c098420010701d40107e00901103809076250001c0c4848011071040d4028054074141d136400301c403400c2180c490302011b560540008203150024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782991169 1250 782989919 782989951
    0x80f070c051504080f030f09010c0302210d0f0c080604150b040608010e070509030a2a0801020918130308040c03140c2b0312020c3309070509 62
    0x142c0358940041000107481c80100d4032142402c5100c0d080c5482209040c170940c0c420b000002c1c0f24907101044500b09002424215818801494183d00b40100780c2c003113595000d80241d1700210702c180000103106034041580100405081c021402040b50080c100d0303140060070900000e007441c00c2070791040b50202011031450030401d42c0e918251303c855110f0382240b40003640420040000c04c00380104241c0004590500c1c03401d04201d800480d940700e40035034028000707030750044c0204103c0e0040c0d0700c22039041404004408907280c55070b2405020f5070207048018091089021180c100704440c1c503903940100404081301d400256261002c841c0520f014000781c904194142c80000001d4240c0e10791011a91803001420006007038500300a440c1c8001c0000442c48040c0c2c010f24611001300d80039400d001603041c181060150b0034031020000034046c0c5240003183d4032600b0301f400909050780c031080f803541d480c0f885115071800d50519068210042542e441c0400c0c0c5c802d0f00f0034031a034604040c0150303021110740c00740840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782992419 1250 782991169 782991179
    0x313060e06090d0503180d0816080f030405010902131e09170a030c020d0807170702120409020301080c06040b0d1a0d060509120a0f0e030111030f1909080f070c 70
    0x810f030340000044400d540b00242c4038140e450355144d803e8410b03408407240c0044403030701e855a01c1d26100b41c00640e01c00036200b420060402c0a1202521004a01c4000f40c035140d04e4103183c40341c02003000050580c4a4902d602552000404500648407045070740c006003648030b2107825a140241410a00455180040c2c14442c5d01110b440740151000c5078240d507010492248a650190070308035500300341020801440c1c208001e030b54200c040c8400011320000c001845641d24542281481c50324000c8041440000400007840e42c01a00903605030f030000402d49060407919010002c20384201e104000350305078180481c00040d90350341d0040d040010309851800c1204014000110031030040361003220b01a40d50414032100c00300c2000018244000c9004e09403401590310b1020300701d000c480070600100800141d051250b51001e400c01d14400c441c100015032a030074224030b401c50701041201c07040d02e0a000c0c000d030034400721518080c2d80d821a8210b00f0680c502900170f018100c02d603001ba0b10640d051405d007403002030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782993669 1250 782992419 782992429
    0x1806050303030408430606053d02190609021c03020d1403062202180907030212060d0615090f0f060e01060507020a03080a050301030c080313060e0609 66
    0x71040d4032034280ca903980c00040d41c88280302c50445d031740200700c41280b9041c0c082c0c90713040c91044c040b513403c00c01c90b100c085c8000c3d1500388090a041c3e0480354225034042d0440050200031015401500888040060145006c1c020700500907201e007103120051303024144001c03c03110000d01c0c080c000c1d801100c0101e403068094011813034101e682002c40314864924005034050560601107414034001c1407811000107080e205c241f010601019200c0340c400c0300900b010b1400f62034012600f0000c030802a00c10f54a400b015007030b91030340f10404c10b1100c1c019205034001420640c403a03c00c0703030b4928501a00003501a01c03000140200f18110304c4c03084901a0791017441240e00c524442c1c41000a002203400030801b481440985000d95024285410782d140c05e0841c18802e080c0d0740b84050307054031070b903203020b585440c1d440c00000e5650301182d10107001034000150200c2120382c070000a6043e6409040d0702c984003036840b0003169591184c42e02004041132124000d005052250106000e0303054020207071401c0c0101500026 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782994919 1250 782993669 782993671
    0x6090a0e0f0106080a02041a010c02152a060106050c03030703050c07051009051029062110240e0604090e251802030703020d0612060f0c0207180605030303 68
    0x220b266171250512008519040c003d00820144004400d80243c14034000a4054203c03000000c2c441d0401c40302001c500c004c0031042c1c0f246280110010400400404206250040c10141088443c0241c2001081c46400780c001c4500380c1d40340700001c5240d80d84d0098100c0007081d01074010305141e44200030160101d0400c0040c11b0311998600000545020907280c8545841245800c00c4000c80c105900985e14028902070151080000c200a880020112001861610a03210805c25814031000d410110440100040d8407444011620304c4aa944a00644103426080144620540069030600200520401c089015034401403d01030030251164140c078150780e40e81c0348d24000e51344245040040e804c1943c0c8071428180c01c0d26040c80540e03003864848024080804e4501101c1d94000021805261090341190510503942c6000c000d415102d059501c007230b404021080e40c0030b60034044200310000032881800c4103103065030000d264282c50f00c0388043da031a0f081e1b001e07182603e0340c40c800090b582c0c805100031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782996169 1250 782994919 782994929
    0x60f110c1b10090324110406080124200708030a090b090603011e050901060e04050702010b1e060408010c1e08090c011202090d05101406090a0e0f0106 66
    0x18056014007207081584085280599500c40e4003041250303000d00350403803668000d07644c21698010344007020f01305105d05600041e000580c000e00d440084184203d910300a00b041d100a03560301801d69076110071044e1001c0201d56110490003641c05900003290080a64030502c0c0d0401c8000c010005c00342c4012800c0100325441200316403c005440104264400640405080e1508100d82480c7c40800030445900050007011120308880d10101e440c6d030326a038040d0000b00b600030b0210500b50317110000100100403194505006c0d50a080103c0c03111b5006014507110303440060103040d40d40d5840c0710341c91001400c5c4c080c8550131540401000c100d108003030046522032007a1f501d8000e00c850303800c2c1c001400300c01084025000c104880082c890850070101e5480c0343e1500c2440c08401d615103200c2940020f22031641c040c0c0d1b2144000a40200f040000309802c0401c1e4242c1c0c1b170400180420396000102400119a2250f00104c1c540000300c541c4038542c400242060a1411251220031010f45242101c00603080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782997419 1250 782996169 782996173
    0x203062409040b1c080c120c1609180809011b1209050102070e0f0c0d02271009090207050a020a0b04230d030f050d06121b080a060f110c 60
    0x7929500b0035004481c80d04405440f00410005a0440c4011140100318000c01c80c0e03000103007000383d82c0005c1068a0010f0050000c42c1d0742c80b84581c81550f518003070f04039204a1006034000000f400c5005104014030810500003514031a01c071035840c4106a413000660034103005818403952441c80c0f822100c00c180500c1101001c0c6041c0c80c1ca40c02400d841c010344d00c114110b40c880142070080150303120810b03400c4080303561707100b01a40318000301ca01d950080c000501070b468404500c54000c030881c070b0100a0000b840010500c0d5220000090001c020024803510002c0b03010010100442502d5074004e0a84902460940302800b20550001d0302c1c0c0b00159104081611011801340030004c41a803e0795841c00303685100515014100e4003045030310b1183c4d00e020703080c049401c180c072061600540c00c40d911005810701c1004a42d40b14101c401300170400381420b480c0204000e0241403449130b0110f024017510406401019030fa0f10310f6131240f01400031030702d0005440383c9940c00850006c4013080580b14507250400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782998669 1250 782997419 782997427
    0x10111b01060302040e3708220f2106020403060c050715050403140a0c0b0703061a04060c14070506162a18060e040606080706020601051302030624 64
    0x1004261490f107828840703580c01502103480d044a08007095020201020304d0040c0f0a06c003a419014403a0400e20041d1141c2c50024560131030821200d600c6000006a0000c030713420780d44404c489240c0d090140100ca00025103140007140f8908624a04001c15100b00d2026251540781e65440301540c0b040b25106010460104804c4200540b000680808840026003004a4500381e1001060f191418035030314140800092003241462091510b000002d80044000f006420304286c01801401a449905d580603201c2e0300203800807942004403800c42d000e83d600c3c91602d0307403680c4800102c41d00c1e02400a402c0d101d071104c0001c858640202030030003000e0947e8044050740e070504015200d50070101c0c2540d060524a4004d08144c1518000d18040c2c0380d90a0894500315800e02c18030340100025000948001c00c0c0c4400c0204001998000d401501d80860a5402056440500b40cce581c107000e004d4a83d21414000c0d00420034207203640595400040200b07140c0d9240da13060307100c1200c0c8903e1000d004414134005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782999919 1250 782998669 782998673
    0x705150402100c020307120303090b010f0f081f0c1b1a0604021e030901020c12040602070f060804200d2001020a0209040b040201020c130911100210111b010603 70
    0x49040d03140c0b1403820b040f200e680140d030000c0d849001301e00540c100f00703201034005010b062007a07018125580c0d1040c00380c04a9610303a4052111042e1a00c262002401e058401203251031000c160100600030044c0300701d0111101a42000181030051201c008200743c52001142109040003030712180f502840f43d18007120064426a1084000241414041c60041043d4a24907201c2c6144400d07220b0203841850300d0361242d50300e0703901a10500d1000da0040c4189990f490003010403c0040c8120751050302125042c2d03a840700c0200c0045611b1041c100881e40050015000c03030003103a110010b144122a03036220a40b408800036541c9080524142c1e1401813a0400800582e221440d40002c2c1c50240010004010a0350002d48404402403008107207003031050200d02164020802d800520748001c201c0100090407507503480042080341d07410384001c9007540e5040da45041414a510b842c40580d80a411082107880780d28000d0444008080049401002000d100d1280010141caa1114810020401e14614 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783001169 1250 782999919 782999929
    0x20120706022a0a02010305100f0305030309010c080403020613030c080a031508070f06180801022719030b1b0d0608101103060d141f0509300705150402 66
    0x190302104000018864600301042c0022400d014550900c1c0106042da0f4100800d02c11500075441020b10f090711500c04000c011002c0003441c40345208038001c019122801c13a045a4001c400c2d50050b016800190110b15a5244c0e0700003103001034020f00f80141120b02541e2007603401d5100502d87c0c000245e440b90000300d45040001c0b004010500c0b5002400f501e0704040e40c610441c86940301700301c02e01c46540048525601c0c811414801004210001c40d142c500400d03201500d003030600c0881900c50401c1d01c2c0b848144c90716480c0d00c40006218000040141d081d40d807a44c0d101140034115a0700050030324000b000c4003501d03800401281c1048903003c1902e51030800f80610b021241d020030b06101d810311500d8440b0005c10300a0745e0307024500701c03004403c10036582001c80f140200e40420550b240181e10220f40b64100d06143c0400d5604411410440c1d9074401036481e440b034550703644001800405808410300f69a00340c1c0040c100e00305c1c801280d0303d031001543d40c46181542c6106504440d15201040105528007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783002419 1250 783001169 783001207
    0x610050108160212181302040501090e1006080a020c0105010b0c0139053006010804030807030b30011d12180d050703020f010509012012070602 63
    0x4480c0e0440718606600b01c0652224256220a80c000030045610100074240903801442e10b80060008482080c60f0300e008006540030b070140d00d01050010000007800c0c010326007980d104020071900030b03401c641000811912924080d008003100341c0c00303000c20b19040200f0300caa14020803646904540e107003440002c85096820140303035461003600c016851002c583c03212103070049001183d40780030001000780344156014010710103075002c0007035140100c032010f0514020340030194401c4400740c26180c3d075030001150303440c00443d0001e001840e0340c400303e01c2d82c9000381c010300f600340401003498001e200d00300c90031405003850840d04540301c0c100d101440c960f010203110b40f03089800c008032086144090590365035602d04c100240c00110113800607050799a40c2c1c420030f0180d4005401442001c9895040c10015a00c0e220303070205134402e00e0144800e2003598001c608980040e44103865000030f245000e52010703c06d50301e43c084a82036014070070460151900042c0148255841a80c0c0162244a103100045070149 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783003669 1250 783002419 783002431
    0x10b010518090703060807090b1306060c14030405030f011401080105060105070f08250312051012020409060908070606060206011a0d2702091b0714010e0610050108 72
    0xc810440041000340303155514903484015039881400740c549090480c0100656400b05049020f06100890750160350342150302c55100490780d2804001c0b00300c440204441c803c3c49039002003440211880c0016503200c03000d4202810203000e89040c0f0b6564408607091003125010342c0203d9560341035000030a84c108030710a014000381d0b07000b0001460b200c4000303401445510000b41107540090106001c11030024100c030444442c015804801c03090b0390380c9181c0b291240d01e0081f004151b2003011300c900c82d4054402c040c0710740b07100d45c45c0081291900741e10302d00b40b540c900e43c1640c0150b12910b625000c94401c0c014480f03041d01c00ca007280e907142614203064007210202c0e004541150489401000f00040c0b0002c07442190070004041956070803a109204010801c0115603c102042c440701400e907103200d29031120b40613000b525804c906503030301c078902e014407040a0f03a110441030b002d00c41500490b004007504140d014072940002040c84011254a2405408a48e003908419055000b4416968860b803841d070004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783004919 1250 783003669 783003677
    0xa031b030b010812120c04120803010e150915030307020603100e0117030706022802010c02070803070f0305070c27060504020c2a060408010b01030c050c062403150405010b01 76
    0x80d00c41011550344145034114009055650114221031106d1046400138401c03000000741c18001c0303241c0032609130024891504000442c10000c1c42103d13504000c1c4a070321a00904408981c1e81d010300510b41c000070388126035014407091280d0401a100c10b00250302660301c22001d00c028134a0800181d02c40b601c140c04c2000d251861440c0c1043d074032400030549a1442d84100d026844045410021584c03c61079014103101d851401ca0000c940c540650000c2ca510607582c0c29107030b07410344030303814190b0360702c9104002020b005d21070b0890300200b0300c6203002d00520303071281c282142c003159115140c0d080c0000b08035282c400d000d42061000c008001d58402c24005040546c1e00354240075035504410340340c0e4a010a10440803000380c1c111b01501c201030b01288501e003070003060302ea151038680407568000c054500c1400d0106c0c0c0b40c01415040c89014000799070071020316030000c10329039681d002c6100111142008800e1809100d00710903030350f82c1e414440c118000001814200652505040040c29100c001c05018180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783006169 1250 783004919 783004933
    0x705130e09300702010507080702031504050106050316290414010e0d150903050c0102120103050c060f030a0209030319050703031401080c041a040912020d081e060a031b030b0108 78
    0x1034550340c1503c50707044d0242411383d01e4a1090410b04418031039400c00940c94003688500003519400c98100900403400303030b00200452920b51081c9562140c18507040d8060000321001049007907100c00290241024061342c00034070803100000550150456005101e84500c1c003103a25100303591010128900f5001207410343c00101b1151111802c880d400710319600340743d844002e54014907006004640080e28194000c641d10222500030084402d404e0000711028054901808030310301d402c00c261002040451101841d60b1140b40d503000c0203500440100d90075000520101d61118101c018400d60700e015500c9803950f4030000c0ca0000d007150650542c0c044d03d40c00d508014005454005046151480150340000b4229044070092401079044100c1d15400790034040224104070700e0407594103c01c40560221807101b12a26000e5410620898038080e0004904007800c41c000e0380f13501155080306001c1c3c80407824644948620300080789030140400c0030300305a94104100440a8070076401405064058010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783007419 1250 783006169 783006253
    0x120f05040e06040e0f03031e06030705090c0d060503070b0403030f020a05031602060f04090c0f0519141c05010f080307020a030303020a09350607080705130e09 70
    0x381c00e03009401c01d80210740d140541689000100800c014014501048035202e1401449502c0d001460f8131154031400440d00118503d800c000600c0019900c00405010481d40c80c4100303002d2030303040400070b100c900b1b07101c10000510f500d0030300c808070142008001c455611821405d010f4802100040d800086500c2100c00e40041407000c825502d00b0b0044990f101040b4185000050a03800303461b01020f10280001000101c0c0d007030a0384905c52a00c800d44410312112505242039956000c1c035000c2d075a4030032260043c620303284d219120082c215145105014104807601c48040c182c4004035010f4000c0544d900c0043c007405120f105500010a54000118030308501d43d03001c51080000f52000034203254000c61103c28550140c3c0d1804080c0603040c1c00f0b040703040185041e9451294441d1001c54240e441040f041001560200b1211f224003050303250191951110300d011545d652004940c8624040182c502003144840001c00c071340921481c400500c00207204001c03907034000002d4440000403e1580b00084a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783008669 1250 783007419 783007439
    0xb070f02160504050c04051905090702070608040809010519090609050a050d08090f030f0a0b0601050c0327100908060c190c03020c0a09020a0809070f0509130f120f0504 74
    0xe070344050300c01213100d40312921400e1890003039800003580180c1c1c40e92005003155070050810201d0f0800c85110209848010050f40c0311a0180101d1002400fa0400140460080401011401c5c01858401d2514140611041c0d0010304102c04000294080ea0200805640480300c800608802c03900400e0080c582000680c0c02c80b80040700030060072010404800c256a0415448945000030701076a0404131001d000329121142c8040c204c0c1c04142c0100420ba45510900c00d494119103d00300540c5080c0910402c40d900c0c1c4d400c03140b000001c03100341144180c40d0b10340084403544601d4944440b07085508044003207003440c1300100364443d4081c080c0101c4000e10300540c3c0800c40c00742c5a00b080e0801d41d406007022801c01c44015502e5401103502e240004d2112829070003020003071260707070325140c09803503c001c880d0b10341c40903114504031b814044d2814032a41c50f0640c5266000b4034100102d0060301a10f07619100038600c2c8000649280c0751400f20751144d25000075481400c015240b45ca140b4207030038030f01115 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783009919 1250 783008669 783008713
    0x10905210c060903250f0807090c0c02150304020307180e010501050d080406230a110d0e030d051605010903090317070201090e09030d060803030a0f15121b030b070f02 73
    0x300c070048980201c01a50203017440b1210150201880c04486241c4480040b07070380310740c94419502500d03d1309807118241da1007008004211940104503038100758109000f014260000790060b03078980582a0b00180403201161107460000005402203845201440d0250031140305902181c05544c0014581000035140002c40d015180141001e5040d5000d1002103139103c5950300003003107074060016103010540c0d04581516400780280c0300300e0b00c041c81144000c0341d221202108040d0564011040c01104601501c00b40204248901c0c0c61134003045151034250039201010029004200d12039000c2c400d11001c1c11902000300030504202c2e1803c003269000030035411151044c0c0100311180c81c04203030030b48018011114042c2d002c0805001c120f40f05e85009807a64001c0c0c2c4c4120000d8540206210180c0d4a4001d0035a080b6203800243c480e903162946e00c40e000c00070480e0464015030303000d0440110340703001c8030b248010318015000300c41d15180910700641100100b4104000b55405800e03820000641c40e100a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783011169 1250 783009919 783009943
    0xe0d030e0f060f310606050a06050901091511190b060a030f060207030309320109080d0f0b130213120503031503010b1806090f2202010905210c060903 66
    0x1031542007011004c806900000c1003080405190303003034510810301c00240c2051080d15800c0301c20140c5682d580c1001d40b04c0d4070a0062090110b50741410800240c03404e4006404003403042c0c00d00c03030f10040d9451511810f0240044042006258502030f49083c840c00c0800d203a07004400340c5140350060709549a03520070744032240d401460140c0014011040501c02d0b0000e1242c10342c400155a0141c05440c000d2034540070540c04180c000020915140e003000050040a00c00354002d01285d140250020b42c05006d0304c0b014008030380268440303984003081c1c0c03140d42c88103242c2c1044501c01030322a00b801fa030200350080c07945e01680e81e5003030144111000c600040116604031a02c6150b8036507848100c4042409040c040e5015503012504030b654842c0501a458081d110303000032108180aa0764141d48a0102e150640e0318480320007507455480807428500c0b0800541d01c0c01410070b503020070f50762000984400070f0305060882c0c6003000140d05503604010840c1c3e00c0c26590440d001800c4c00701013008203030b903031080c002d41d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783012419 1250 783011169 783011191
    0x105070503070507320c03011b09030615051909050606070c090c090b032e030b04030c0510020f04080c010c080d090212010507081e010b09060304060e0d030e0f060f 72
    0x1540215600642c411042e05d80d001c030f840000312003414181c81d2101e00c100ca10f61300039400e1180c2845005003e00d29508200201e0b110400a2415601c62000a0482d416100100d001511001c43c09540304025100d661018159900d5217900780843c03981070360710107000c442c0507540512170540040e501c0040c00c41a1103a5040008240c40340b540212400c142d203512401c0311000000c180300d8410401400d540c10101110024190745441341c00c12410040c0c144006050a02c000c0082000280f2480f81e036218540030300200d81c42e4550191800c0103e03070282284004421000904000503242400300f00c010b05003d003006d2200914507101d11007640310fa540700d00c8140c0d594401000031540d0b0601070b85195a92070000b007040c0d10740003101900c03600c0d090782d072102e140b070301d075114060200b02c81541607040e103244400b1181050355117014452241c00180c0221082ca0706d07149614042c040811000f024044540d9000c074041404000e014100340a042440c003003904210100500e024140d10340350740006c541c03e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783013669 1250 783012419 783012443
    0x30915030601030b10050406090f08060f04031808071511250305250b16080d0212070801060305070e011e050913060509060f09180c0319050105070503070507 69
    0x100d00070b00020b13020300e9006225100c940301c910350000140c415a8007070380b2090f05007a00c4071001342e295012449416800c0d400701000900510015040e650010b06c40e04002c19200345203203600216050b0340c0c2108819601002080000842010301401c04c0c509a0405180f515605100b00b42c0750800300502c41a0038218145100d542d0395100b09a0000716080b1007500c80d0075078130341c2e80c0d401d1102c610000607500c8001450b001ca001501201100c05c41982c4145180e9442802c0e5501b000903040a41ca0844013a42403105000c0f582200e001627110b146295034240c115810100c020303007100d20217000c00041250031124901c059800c10041c20a4009010448011000f070520807078192280070461a0070880f19400c0c100010f105400c070344161042102c0390705a5503640700030300510648184040381c1c0312000d600450814002106600000180403041d941902181c10100344cc0c1b828485501c2003903280e100821092000a04c10941c2001c0c0f245002403071414600380040450185420107460296884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783014919 1250 783013669 783013681
    0x6031a0d0201110d0302190201020c0a15090c15030f05160c080c0f0a03030f050621010f0e100b040501060801180e0601170607020c060415050f03160f0203091503 71
    0x1900c10b8145268100700c800041988400901940250541010301f41000159941c114018006d80310b142d5210030060042000c0b81e1200319043c0ca103d0a1103a5803a5624150030200300344014640c060041c0d100d54540001b9021b03001000c0384d854214500701149000184005442d0f802081002c1d98400d00e0035254a8a0609100a80c0e01c03c0442405041c8203004091422400100c0d8081c101400303903c2c00c004901109200c0c60980e501125020b502000c2c441984000500c646c80c19032210b0782541c00001e07003002e407901c84c45c115807800d0140c0d07040b507000d00c0000707081141900480311599411760707081c040c40d450508040c00742c0c0c03418081c1000c1e5005200d1040001e519a81c00b640340c80041c0c004840403541d48044020050901403501001409545c000800f203500000741e100f040103024105914051418044214012440c010701e001c0010420003064000006409140070387c1070203c25242e48070480d48060710f070344400000b810954005000701809980c440d04095001035083c3c4070039a0700d175620 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783016169 1250 783014919 783014927
    0xc0606090b0f042d0b10110f0307080a03110c12030123031002030c120c07060501090e1b0102030408120c0606031207020915100305040c05010306120206090d08031e0106031a0d0201 79
    0x40701d1904501500711100050b0362103400c7c0b1040c00c1800b402e64060745100e0300883e4681c4a0b0401c041c0050904100a5188500c603900c00100140114440d505001c15080d10394100140d00c00e918560035804801070107030344400c172070302090f03202100c0b01d541d040100500070a40398903103000146c0ca000d80c00b000044d0238400c0e00d01200c04011801c442c3c0c050500d0000c2e01e01849402c41ca400380c804a20300400481c0b078500034031601d89201c40081c010440595038141500c8800110b0071603e0450000307010001300300b0410011480d05091100942c1c1c6c031450484a001d2810b0802012144a640f0007440d40b004001340c00100d134180c17a010b403404800c50b982d54030b8055020b001232080640040d55242040c5d00c03240d1551015000c0c52003014201c405554507401107080e00d480340601030388c46160203203810061810100612410101400d1400088203d896240640e002100c1a0140500c400e0b0051000c0e80d400f90624090f00660408101c18510b040c1c0030a10921380155140c0141e480c11020000d580c06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783017419 1250 783016169 783016181
    0x703020712020d0f0303060317030105031e1e0c1509151e0406210c12020715110a0305010501050a0e09100b0a0504061e0f08070c0606090b0f042d 64
    0x1094206104005103170007001007440c1c0c401609c85401c01e001001c0450015402c8a040300e00c01001800c88060b004009402c1c0c1c01d203001015076522407008443e1781141d140c0c1c0040085003000000c1c00000350200c05008036031510812240611004003c654015504c116001c003ea41382c15045c2d40d298021000c0551341512031500390013502c4000300d070010300b1aa2010082d42d007091000034980c60649000d00c0740068442c81c80358403011502400c40010300c60455409041710300d00903000d003450030701ea40611008840424600c41803044000030002402e0b5054010140108006c0ca07026151210305180200700c1100a42c6861288040101003087c03c1440a9800060030a0f21101035803064042d4000d4940d43c040e118000110340c0e1038454103e40c1384a40c103d0b400d00308031f0b9266140080782102040311030100040c000414011515502408103600f40f01e1000030b000301c000300003100b8080c8800c100302d0b00301c0488000d1156003400c4988141d400c076002d0300d000001d81344155032842e024403100003001e404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783018669 1250 783017419 783017423
    0x307050304140a11240307050903070510080609070e09060409020409060c080108070e01140d0f1704030605180d050307140c280c03020d0807080d0516050703020712020d 74
    0xc1000e850301d0078001d804d41c40c101500400c95800e0b001200c440c0c0911282c500400700440207603424400200d01c98010320042035802c6004055841c0e56071640005910a81c60b4803580c0006208101001640e046c054111a0403480c01c1c10b00360103d41400d400559942c00c000c200d14081c1c5c0e2207111240c110745403900b00360142a40404280030038121214020704099007482591914826034000003039040c0c1c20492389050f036501d0820380c14662001d0b000d00c92450041c1c501166122003822444c008110103072030050780d1102810866a4580ca9420a1003d684015150b00ea00e001d04100c24900c1711030001d00c0b03100148c1e9508019032241d80301c95064030300c0207400c45406412032001a03014100d440100e140da1107030840300312421041c80e2081e507240c1745544103540140005a9100103001510309403c1405000e0f01c42d40d01c0701e103083c02603600c42c140d0b50098030791034501c1c035140d10601c190001c9111810a0b80c002c186042424001b030ba4600035601d821611843c6e07250000001003109645603000b0ba5a0384035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783019919 1250 783018669 783018673
    0xf1e0f120c020f1b0109090e0a21091706060405090304050406061709030a080a0506040b0409050d090611030f0912030a0c1109040c03031b020901060e09060411030705030414 76
    0x800380c00c1c8042c0d00c0311180c1941e40410300940325844030410030550284010241a503030034010504140880000b41403212880e0090703c0b4450007040054940303003618040d02d01c1c40c00c801081e03410384c0e9405040c1080d103402030404000b03072042030f0601080020f40c46501c12070450307001c90710382c981c80c21490440c811a040700d5041828803c000c030b0155004094130507005034130103008006603940e83c2e4083e01c1c0c5c042c4400c000c0020f114500070620440700ca0308016000070b0000c00000703e100000000404988908008a48a40161400070034081c0c21051500c020a201d081c458039044074001c28a449200c0e1403a100e400030300205001c0b0ba940c031802d8151050048100c2220364901c20000043c0c0fa80207050400c56416200c45401c1d046d0f800c1904150340600e038000d03010f0f600641103640540c0c444480c05c88050b410400051014050f030740c0d5000d594000e01054440c98038101500041c4401c4800081501d800b0704e050440c1c0102011418003120791180300f80c40c01d1030301d94850b071401128016035064554068 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783021169 1250 783019919 783019931
    0x90309030b090a0c09050105010c170d021201180e190f020d06021c1506030c180e1006020102070206180a030803040b07030e0a0309090209010e19060f1e0f12 69
    0x4041c0000300d84814a01840080c0880d1796120940c00541e0400d0142a00140c0413028000014a507840650020380400c011541084001020b0800302d8011081c4065000204030042045402c0050603071084840c1c07850034014440c08441203039a42581b0411000d510420016000030700540004d48561141c4c020440d0544030410308080d00030b5041000350340d17010281c841901319000350610072080c00c50b80748000006120f240030410303402000c0701d100c2c0006008544810144051060310204c015114242001c1c500e4203064420200017200d64102c001036a204000440140c0d8517002a41c0440c0300c03a2605542c14150302000c01d003460321036840200303041c20120503c0200a42c079031445200e615151381c200840f440e02c0340d4040e5185219680a008500a95410710007048150010031584038107060a141c03200e649004960b101c501085c005100746085d01e0180003c640c0002c00c00007440c400c0ca420607881490b1014001a5050b40c0c800d142848600c1c1100480c0e18002c50500f203800030341003001c10003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783022419 1250 783021169 783021181
    0x2030a090b1006080c2a0d11070e040f060605060f0304050c0607500d390206070b0f07080903091c0c12060e030306060904090309030b 59
    0x2914100c4821902000301c0030000d060032000407504421640c0c141c0d1640d6183d203d15010043c15448424204081c01c501540280d0068034480602258002080209071a1640281c01480184850401c03881600800c108010440041c42c5d100e8109801c00b4038000b1882e100c0c078003040140b10590005800035408211010010a020081c5100314015000d44600c1461002003000c24412060300074541c1c1d0800c540045800c2c02c50984c0c01412412100740c0028045051259240030402d0300381c00350380342030301d0301403e1981000c4c4400000b9240741d051680c13222540e4030072031040d034a01c4100c05181030352840f40500d0f011f0440488611841e0007600705a604c40b201d0600302520b0310111000340b6003400d040040b0301c2e0f203481050390324440c0e60380ca000b45080c01007030000c00a000c400002c800d04c80c1038821059101103070040104d14000d04020003480f0259440d8501901a00c000d15180c480390b401c14003c00c1100d4a40d00100d80600000312800a0150194902590380721720380d40000e815101c0010811079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783023669 1250 783022419 783022421
    0x40f20070606050d02100809010b03100c030b0a03030921061103070206060d05030a180306050106050912030a080103030305061908100e1c0807050c0d05040609080c0d081c02030a 78
    0x103098001c09040c0120360700d50b03080c0700340064990402074011400f90a4941d42c0c038814088030360048511000840d42d0007000300002d00d442140d000301c1c0d40766903480d500f00700540c0d014411110b2151086d01d4954481e880d60300d0150403403000313120307400c003800003520844020b003032100b114680d490380264108210065100300385900c2d0822030704a009845000e012542d503103131240c2c8541c4516403087c000d511307020080d4001c8554800e480c8541380b90a51094000c03000508a0060b030f406844103550b05d03910742c080207080140e1210800c040f85410307041040049503040d44003080c281501c1d01410701003120340300c0308080780070040000314032000c50400500c003180d5804041049403007181100001e0000e4118140e5050b2a1503d603c18031420110290300b040003c0c0c0600441c036405034075400c140341040f01040d28603040c030516017030300b00c00100002814095280c008140e007016203601c0006040406000c000b088503180d00100103003000340045640000ca1010104010121401003803d42d01c904188241c80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783024919 1250 783023669 783023677
    0x70f080c010e01180302060f0903120d060e0106080a1e02160b01090b030a06091103030703030b010216230316141807080a0506010e0d1b0602031305040f20 68
    0x141c0001d1810a11030080c2d88150340d000e0a0701c10b144083d00d0a0340c696800c110180e4001c0403000e000c0107060100c1e010310f0b901230105003401d0b60302403061955140c4076080c060498410750045448a0300c01d8006002041c0e21141255200d102c110700003602006440f030038000c5802415111085c0d5000288040d0541d0480149a988520400425070966215125a403e480c040244c0d203825910488024020506130340261210b10702442c1d2010342d40000d0b401081c11540580400e5020075290f140300041035904100300c80306c20b10741c00b81c0c20440300c1c01e04003a1b2440004034294900220b1042c00d411703140383c1d018003901c10002e942817401594190781302d0302d2982d54900219603e206403070500311440c0c4040f00344026441a0130994440040d80c0d582d04420008000140c1407504100808000d5026030700c44462440c41c086c051090b4801d8400c41412480b4950304179009a070454106100d2500c1103e520707001a81551760450700810510000541540100840706003000c3c0b01c900c902c180485c024141c4014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783026169 1250 783024919 783024943
    0x60e0106020312090628020d020f1305011e1d040c11061503060f0a0b0303030c1207020c0a05061b01021603020f06070210180f111e0f0d05070f08 64
    0xb1071541d180501607858207012035a2404d02044042e4a565201409015000c06c0400c103070018180045000c200c3e00300d0b00300c012810880b0303000080741e100800f0814841230003404246031240300c80d0b04815003031064180034060701041c44148440d44241200228103803640000c0a071042008518289008200080b14100145203001b04404100e000c0e040d2020203125800240041103076441c0c9003810105030300010301d03081d489a51381e40103102503502440298040c84030b0100081d00c4408181390404005000760109055500401c0f00d2003440d19842800700864808488850300c4a1100c03060203458090402c50304038a510000b4000102c0b0b900164038a203080c002e600711802c00110350001030b511038041e1a5500560300050f0402d01401d8a50030210386502510300d810305182c030907612900031000551003191481c3d4008200504c90074500300c034100c0490450400e01c2c0c9140580d000c24018160318015502400146c0c40103414890200700e842c005103019052202c265540305495601c0d88262740309 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783027419 1250 783026169 783026197
    0x1e161412010c050a1b1a091006080706170f0106030f09020619110d12050c0702030a06050601080901061404020a0c02090c0405091b1b010f1103040507090c21060e01060203 75
    0x614a2808202038000301c02130743c4602086c00081803108120700c0342d0001801c42d800351046c1c0b5101100d100840c0a030030001c01c2080001d247d1581010805803500032100c4441c520403103248200844052100140d80c1100c11604000410801d0684032a0241c04424030294101c140051070003402c0a84080303a818181055582852071041054840d4484154001036000245126080c00022107250b0005811810401744d003490000302c0c3e03000c01e00b04090100c0a4508a549400704022940c21498140d070180a50008004160234030298104c0e071a04c80041600980d80411159101c0380214820f4502a4004149210501c1c003401000120b900c140a41070180ca100f80202e070040c546042c1c02c0c40d0003080d009455040c942403580c5500b0404002d0305294003503485201c180302e00c00141c89507440303140094031460368038505030030000c0c070b0224070741d0021b640e0750321b001c41c0c076810550b1120756044490407810300162610301b0625240007900c8160490076444441c1c000001e100303500000200110911000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783028669 1250 783027419 783027437
    0x14010807080a021e0105040513050a0b0a050d08090d060219020c0904020a03120927060b09090c030c130605090909011506030221091e161412010c050a 66
    0x12025100c2d0110400250810760043d0380b4041c400c1d8400c500c06002d07030103140a60409907503200051171040c0ca0086808020740da08140b040f5403515001e02ca8031540240d680407001868240416210079043d0307006401654041150039040c0d40d40031902c550180c00140554032203407404112107104020203010740241c81140884403035428601c035183d2003960014205003100d403239501c3d48604c09260b04620802c000100c030001c80c03108440d44020007030070f4800c0340d83c050100c2030340401d1089803180c0d0041142d4613001c0c00301400c0c2c1d5403214074040c1e00c002c6545615490340c8500f003a0b01c0b082e015020340010307078059144d004505558008090541c1c81802ca60441030b684914017510700721150000740101c501100c000511003d03001c3d40040c101800c510303102d0450905115400b04d840d4000b1341c2c800b0201c1e001028034010001000102108401c10640944002038034150810400c40740d620482030103030151181108135980301e400c84031285100350000d00401004040050003940030040d07080210303c90751 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783029919 1250 783028669 783028679
    0x20405060c072d030201050c030d060e06181b07020303120901090c0e0609010b0309030c120a0201061a04050d1403030f190605030a110a15092301121a0414010807 71
    0x24080600402144580c402c0c1c81c19a001100c048e0700040465025100403c082481501030b48101002040702da10141414101441042941e01e81c0320b02203c4001c000d03106014031b00007003000c039100780034500041955130b040c0341c8040f0703046001c1c44400d07002d1450a5020040ca540040d044200c04510860030191002d0301c62030a007840f84000e803003864008980034010b11480300488015500401550116402c0c00a80008076103091590b03802c23140c40d902c000c66041943d03602405079002400008a110301603504811170942d80c0e000303e03c1003e2290703030805d00e540203101e6140b040c0221000402c0603a0750b03078940f10345240c41c0c081090312040c403030f801051103411103039000c2c2c820f043c02d90b80010701624581100ba2030360103c0c50300401605510005000e0000380000341c40300d8070542e40810340c0310012000e141800d01c2200c0094122540101c4680c47e1524040740c2e8010017114a16072103c00c0041d80c4c03003a07903420202080c00d6245041d04907140090702c41c01c43c4812500c2c1c038106d43c0050105c41e8407646030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783031169 1250 783029919 783029969
    0x80304060510170604020f040f0f0603020f01050339160c15020d031a060408150a060b03010501030c030b03010e0309030c0d0305190215070801090513030504060e04020405060c07 78
    0x9003020b807403544c10a10124005180420078216590401040030402c4080013401c08102c0380f501c4001103005030788072410421402d280c0070102640c0c1d02420020b0551034909d60070715440200f2103100400411110007025121916000a251020350904164503000c0e018001c0507641f80e041030a48030710001c007800003045c418004150924441c0d43d4041e00d040c03008030301d0940c0984480b910006071240102136188c042d45942000d40010306c1c20000030310395050b0000c01c0c0c064a50703018040d01e08203420104103100210010080340d04441c0d00386400600384880400c21001007100d08a950750550030056140d440c0300001003d48141002181038842c416800e408002c20312183c2003008010840500c00040c01100114031019903907100d0054074290140d07218a0009510102d5250022904003001444010428802c1a80c00403006404141411a40d00d0140c030501440c880c6404211020484224a4840740c058038028203001d40581d8551901d04042522580a4010300100c0002c50010a807020b0b62 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783032419 1250 783031169 783031199
    0x304080d05040c050f09160c030e030105040503090a1d07051803010e1e0f07060f050705070e0a060905190b031e010501030b0c040f05060310030b09010c080603150f13080304060510 79
    0x4402c54210b00380c1c7c000c54094a41d100c2a034425014050744040200440c0c0302070190034451407142000c0c6945602c410100000c0c6099034004030058501a41041240300074031014940044a9042c10707511983c000c0c040a591141d42100ca68140d403c10044180e01103001401c1c0401046004000b186180d0300d1600b195501c0c100301c03410b05190300607107041011a0003051800d007007140e14a08149022950b8981902e0014558440300014140d07100b00070b501044d921811000d48185001030003242056118040861905400c1074020f5950f0541141155410000c0070995480b00d5000011f059910310300754020304092006030b40d025009400240c0c9510301d40c00311001c0e41c002001c3c900c0e20f1800c080500034982c00081c842c5c01840d0fa4100c0110114000b108013a2140b0548000401c0d03520304900c00618152000d04030070700075031012645c180d02e2411031084070b43c015840500e42040380d44095240c11900078520000d0030803070b000401d020078000c0c990840340c8244408110707040055596810a100810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783033669 1250 783032419 783032431
    0xf0f011805280b0f0411010e030604022e0c050f011401120512030a02310b09061e0a0f0c2415060f0305010f050f060304080d05040c050f09 61
    0xca07003840c081d411040b0944403070311101d401d0505295034040e00703c1800e44000c402c409a440801c000c000d180c00b03485aa103003082c42d11401150500c00032035990200500002d20800141310880b07030806040194039080394007175000c7d03000e00c0b000d0700c000740a00ca038009040c1c8150282e0604004000740c14010040d10600600b010b05031070f0b113441034143c0ea0b0419041c0071035142c024501c0004900019801460190700400c40040e03171880319408180080e00c0d22048000f51244103003005030f082c204c0d9100340781120f00c100c0b101e40d5504624400100144a1000140f49a240083c1c0e51018910407101925020840b038444034a0f550007403c081d1131f903005591004000c95080c0c0f690800110b04680e11070050350440e00e011804001c20241c0800044481c0c100c0400104461078480c1502c0e41401080d005090451420030700609200110707000a41d10b002c20b5025402c000b0100301001195012174080100ca003008000d181068035000c89286110b128a600c02c0c000740c00d50304150303d010106180180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783034919 1250 783033669 783033673
    0x24050604030b090a1a0a0c020105060a180905060114130b031209180a020d0c1b020402030c07060e0a0b010803160210020705040e010e0d14070605060609030f0f011805 73
    0xd8a1a41c4401d94200002c0210307103240104181c901c00601030000c0c0030013044050750010900e180941060b0100c035600e0090008580c14481406080d80315110071034141c4107000781a072a205a054510800352501c400010481e118640c00060313511034078038606290201c01c0342c101c4000091485c588040e503001c140d907194185c0025800d03c070311425070300c01464803840191112194050b40383d0a4403c00324110303000d00e03034103030001402c0680c00900d2040003803400b56030034041c890161007400d8880600a451000b4041c50b400000310b951191090305a032030349980f01c04144005180c51f40419100c100210302101c0b4101c11100201d065413011040d1001c0c0e641c4242c6942149485408100145084100b01c40a6020700c050100d0680c5440c044c03c00c0450300003002140c80c00d40010114036021002c8203170401c024010300c02e15914030214080381d0006801402c080b8517505d0310b2000034510722481036030b03560520408a842c1c01d941800b08a03c040003130003038000c01245014102109202907540c000030135907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783036169 1250 783034919 783034927
    0x1203050f13050301050405060a0609090302070e1f06050703080f1e0c0d090c05120a02031b060d0f1a040209100813050a0c17011512020d08030109240506 67
    0x3180e080080d00c00c00c54104821081039030b840000c6400c403138050341c094559410200800520404c00d0080100a00d2044400c00480310b0913100251a49128003596484a51640100c0e03c1d070403400547d900c2c501209809112055607402d0040d0055000e000d00320082918840081c40d030750001c1c0c01c0701d4490030505146480320301100390140304180c401030003004a090140811001d2040e18440c400c00a4400d06100034803a0400040001020040ca0b0101e403e030b000203031600041e1000b00300781c03500c0010066840c2d405030304400041c9840c081c000d101c8601074540310301c042140001d80c00601008411104010020f02c075003045c04142c1c41150b40c22500034a032a4204c20060b80f14540716071f03010080c00b0710000200150b07607500e0300f00842804243e41600b4541ea081c080e225482c10b8841d0501e004c84000c024240b0030317022060300085988540444001e0b0740440300d0554813001c1c015440b180d800706d0950f40e290b8440310308500a11442110321203541c20303041800c04241007200008190ba1004140c80e0070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783037419 1250 783036169 783036187
    0xb070c08151f08060a0f0b0306010b0a0c11090a0c0f090302061c11040807050108150904060b1c0602040f06030204180b24031905040c2c130507120305 66
    0x104481a07000c003a9149a003040008a580007070004d940591a0104041103070507400782508203031048074104c1d51080d001840100141c2c1503810460b240c4401500788288880d0040c00c0110f0060200607109401c040e0070000c1001c41d0300b20ba48115840031182e200c400190784074440c1101c1c01800380c000290891030070000d50480441f1a44202104240d540000c564014401ea03428015000355000d0030440d44609000c1c4029a0801203050384090301141c124810101c0000060711004041c00150032240d49d038040c1c0c011600d43c2c144001401414440c075840050642c0b4010000358007512880380d611242004c0811514803900803541254488412100c141c4401a2404000c02d00e020700c09a00c411259694240c848841103111214400c409804c0c1c3c0701c0c80c1240a90325a04a41d046132251103141c803081200003840c040c02c1d08141ca01c031900e1450000844008a00240c030090103081c280208402040646052505aa0f40d0345210b08142c60f251035584400d01c45e00d500516005011900034400c000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783038669 1250 783037419 783037441
    0x5060106030e16030f030201050601140f03100305061602061810020a05090d030e030705040216030f020c0604030c031e170a05090a091a030d0f05090301020d060b070c0815 75
    0x4500c520350260350b81012a02000c04500b15544e20442c0c504071220f05020a00d83c0a12485078400e801703081000c41c0710414406045148074003802c058050002101180440d12074441c0c2030b01031a402021200182840e00742c0110500207170909500510414000400045000301c1031722200610b030000b0440c00b1a0740c4e0b1040060b4011090f003504200f41401309503243d58940708801d082d9800b81e1602460007280100341410a10385d45c000500031401085101007045041075071444103601485e180c3c0d80c0980b420412400c0c07200011626500c80d0000c81d010052080f1010000f003180e2203410504003550103409060f00400f13002101a001c69011070000900e0002d00b0b006225500082c0790407440c2c5505400060792060b8543c001000300d554440107480f10b03000509854914000450007404a922a05001402c0500c0c08400f402080408264060b007500c0940540304503005119040c001301c0e48808595520380c02900081d6040c805c0d200002402110104500050110600701810f16a8814070b60b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783039919 1250 783038669 783038681
    0x5091e04090b0106080403020706030c0c0b04031413170c0102210c1203151e060915030c031e0103050a020f060c0105070315050a08030307031d0a050604060c0c0506010603 75
    0x240d002516003040d4000241d08080c468003a001c240c40e14042030a2505000b464080690043d07014140340071038104140d6005901c18403202c0e8001091119665103140417100600c4401440601101c08115240008208900001611204440819005208001da0369107092003261103001d40c00c0341103244405015080582c00d08100e8511861409159003e41482c3c1040e991214501401c00300500c5031209c04000b01d0400104101c4503202c1c2008100d0101c1060320116001511804000440005645462201401802c2c900c42d4094591400030000005544100d812401100201e844a4091440c50000d039050321380207001031003140c540c0e600f802003080044144550101c410710140f075181100340900e6209074900c3d980440e074003881150101c0703002013036082503122707000004061103005000025a54050b80c1882c000c02c801e000c0d510b0300c00000f01094503031400c50040c500f02c0c1c0c0a12500064140c052441640c08016000a0040454040000030001045a00141d0040100500c02d130464 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783041169 1250 783039919 783039979
    0xc0c0c0303133309090c05070b0a020a020709110703031401030803010b0304060207080703020c03062a220b0702091510200106030b010503070b1218030409020409050a0c0509 76
    0x10407480580d04030b01880410300f2968000000360505018001030720b040c0100c2801c041c0d40d0601904264a030754403400c1894008111007419a0301007a5121014401c02091000340b032058002c010822450340310300040c0d841f030340d42500480d040807400c4e0b041d040f090700118101c03500110980c0c20759090075400000759001400c10b03200c0c16001d0045001060002c00144111071094009040c0c41740e44d04145800d0500c01060311022003441c0701000c090301c41201d0400195208100856591031030460543c1c18043c04200c0b80704400031250000c0b071000440d0000304509402200e01e1502950748800e11111500c000e45920340041030090100085070040898000c40d1902480203900702003841052421154694410765503440d07503600401a90400f440740700c0c050082003503c42c0c94103111052a4030140c001406200c401803d203a1242401d03942402a01e010b4041a070082d03580d940d449405001a040a035048440d0a2a11070b0a070300c194020000c03100d802d40050408000c1d00c018009070012a043c0f4800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783042419 1250 783041169 783041219
    0xb0c0304030b060f120c010e09060d020405091606110105010f060f12060e07020c1e01020c060a030f2c1b0d060e3403020a0e1e0c0c0c030313 62
    0x52501307541d42d4856034903419000c03403004040141080000622150902061a005401e5801440f20729150489400d060036010b4a01203010b0701d1320311035945440056242d0851890390307100e002c141664403c00782c6040d107100344024031259132110582240e1800c40d11074580410791009a445420380118160081c0c1da45020000881d2070b95292103c02912003260041300581100e21400124600a501c88030307110440e02140511240400010350b491400710b800c10f08c6814042228103003180709401603010101e4080c014045100401818484812041c00070b510040100c42d4020b190f05000071501030890321400d120a84580e20810302104e2407101c5010368503c0c2e01c500c2510749205040001e14540c0540300654044880c0081d00b0000e0340f21511601200702e14039120800c050780c0c40d0910201510102c55541e44142c4130701c450000700745280e84c07604004d1030045c1d08014040c80401e01514000c2c030700c507080c1e0703c2000441080503264401c602c808039103601803140502c01c2c0e05804a60002034648400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783043669 1250 783042419 783042439
    0x30a08070e0a0e01081204051c0219030515060108040327080a05160509010e07050f09030610080706030608030304150e150604150b07120e100809070b0c0304030b06 72
    0x11038041d1a00f80c12503c482039045004129600382081945550183d02d411581890b080600140c203035142414103000303220306151450195550216400401c04450302e18800c00d541e6850310540300c10398040158407010303600e0000f80c00765000300c03a100c0c822513040d99000711003a201300c080d440f44844031b07113201c0f1483c041da407002c1180c0404011032503d0034040c80003881c00268180c03c59204540c0da03007160707009011781c800400c200164907100c0390300205541131954448203c0c090140d0719004029030700d6450702c42d400038451844c0110125405451099040e5141035448500540a440192007080425401000002c02080d50781c81e946420342c109071000b0400144007a5494038110304000700d0826070700054248070047c68035200311010b0200340710030310001501d03002e0b40c4036082c0125240640b40129108261000c64412007400c800f0300d00052448050354101c1000405180c42120702681ca0301c04d000e070205a00c0d0b00d86050310350340d0100c94000c62420b8213543c4c1d0044100400340c80c898001404d03407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783044919 1250 783043669 783043697
    0x1050915240c15010b070201080c070609080f0a080702010c0e0105160c15020d02120d0e0709060803090a0906050d02120304090617150601080c090f100203071b0503030a0807 76
    0x1100600c0d441200e6802403c5584111000030000b45041c1e02c40070301c08600b0045000180d070000c3d24a5805022000030640351046404c2080181c01c051800605040002500c80c1910340c1c0398001d88034030146541c40c444c1e1650340c0310090b42269507104589020070702c410f5400c0c40940c80340c0c0041040d043c44070340d059070914203656880b090045039040184034485020381902502d80c1004884447c0e142e600c010b0018594040328022640300d00624035503415100d061400c40304004100480092114110030030000d40d550081030303200e2700300c0d120141c8940c6c030581000883c004240146026076400500b0424000c00541c00c01c01c0c0310307a20b1056250a40410b100003d01c00b41039104441c02040b0000900d40c11040c4162068200070310b04088a07400b403544414000c050368850021a8009030030424156203e0115001840460b80c6c1103400341c0c080d1840d200b076801c0316404005051140c1c803412150450040b402401d40c0420811300034140c00d0781c0b052200d600030074440c0440b00d4000e441807c10005a040742 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783046169 1250 783044919 783044989
    0x120106082a0a1806031407020106030803010e040809031203100b0306030d0809070906060c060c080f01030602090a030c030f050105061206040f020a0e0f04030e041802060703020712050a060501050915 87
    0x3548440017103951044284c1d03040750300c0c10140340d100d441c82c8020084070703003143c3d5140c00c3c41c001130140c442c4280319000003404100005e01194070582c3d009040341d481040c4800f03800003a0703004954091581c400b038440051201054001c0d41d00540009001d01403062503010300325030516000b0004405803081d900001264500c0c4d210380304c068034140ea1440d601d2110741c248902034844100100e01003003030741000c000706d6500c4460010b042d01d5000c280035a448201c40005008901241c0000d0440820003800200b0808000e01da41c1d09203124074020f01480c1c2e1100c08021075500d40c5130071503e054100c403001400055140d802035212901c010009107000351250040800389004440e1000d07042c01e0f0900f13010a154105103204c42028080302c080c0424002000d060341404501031009000790008110801014020f01481001e0309040c00000060022402d000d07545520078074081e102c043c0350900110322414410859440f074094001482007081c0c1103000d1252604c0501080c0c0c1080d03001c280400e82d00389803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783047419 1250 783046169 783046217
    0x70b07030504030c0605070618030f120609020a0801180905060112020301061212030b0a061b060b19060e0a050a05120c0613030215090d0b0a02040b120106082a0a 71
    0x5290307519521f800403071800a00302c17000d028035900040706143e0f840d000a42d01c00201030b444c41041c54660340082c034140038480505015041424901e0011030345140c91948010380504a41850050400310140721002b94120742074400040c00603008a0014440c006000301007059592001e000040c0880d904c4500750410316070305004070341c995014039189440d5a0316000300c43c2c0c0d04070101c94281d0f0707040c1750841c0505405841403120102040c040e202c13005000d0250f01101075600080e040046812011815003414086405001d022604004103001a41032840c00c0000f40c60300500381086181c24402000b2440001d281034510314420380902d0029074481078042c012042c840c5499050380c6045204205c030102c02080b45c4d000380d240621521400d40d540004040320180c210240c00d24a480d0b404209020b071050341c0290400c1e800c000f481c1000311240c0081a8101c802035640c9040588945500151594008000c01c104650009000f500044000018071081200b41000c0300d85180d00b40301d031024400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783048669 1250 783047419 783047429
    0x1f090e12070503041230020c120a0506270c10050702060706090b15040e0a020f12060c120604020a0c031d040906061703070305180621180708070b07030504030c 70
    0x410303c80007a0030b105c04000316100c40540d84d546c4101a45c2e851000755600b6240040354400c840720040741c0044481480b6114500341c1003c141d40680c41c104410305280008400c0c00591405030f1000c4010409003c2051020340b44020072030301c1425203901c4215040c4d003100d01c00307a900074810894800007403410701c5030649041c401c1400503401e203002c007100489440c2041405010320300b002c1c0a007004072808a480c0521a40c1210605480310b04030010500c1d4410000000d203082c482da80502c20341d04a00780140040044085094403150741c0e04090100342c4c00f65100e08400f0983c0450740000280c040c2c0450040c01d001c9004882c6c4005102000406550301c010056a0550340c03624240016811103400c0301141d82c0c544019458110f442d0f0b802001e6224100309492003c60018a801a580d214021503c5c7c14040d00042a9580c6c030041612204940036115001b041c8101200c141c0000f43c0072990402721014a40a0072150389000b0000760720340d0004408900f044820000800003451040b0001d002d09 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783049919 1250 783048669 783048683
    0x606090203100f05010201020a1215030821100308120406020c2a0108240a090207050318091b0306030f03120403080f13020f0102010e03031f090e120705030412 70
    0x19150129020b00b04003e0b42155046900400118090980007161140c1ca40c01d8808009004805a06180d5030040c00f60001019818001601c8412002d07801c0c80d0481c3d44d0100c801d9a090ba201c400446011085610004000100074050a00b03641284006198828010000546044a0f2003511805c1641d0f500039003003009042e801d0503079003054030055034054460a00744007100b0b040884001c060741d031452454080c60201e9100140250319844019001041e410406640f166000c0c0f40094030398006030124039480390360b6904500ca0340351a95a081c040c038008002e600101c025698081681c3d031008014a82510445119501402c8200014030101c00ca03007400d0035050030b1520b0f00500d110000b42520301c01c0640c800078403181130310740c0c10030307006265040741c42c40440100302d00140c1c050415041c0ca608903000c04000c0200c1d039010002800c100044040f1007000c22500c0c2ca48007012206182000d50560b40480c6501e98a984120002c0c00811b000f501244d0400b9691015510300070707980001242c0e0b103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783051169 1250 783049919 783049951
    0x30c03050a0c290f07091211060301030609110103050c0d1805060a2405100f3b15041a0d050910060503210f0d051501020c060c0c0105070606090203 65
    0x10100003da06504110140c403104424203020b44001c051400b28083c030781910804c1500e0f0002c00c401c02c070400200c4000545102e40301d682d40d0900030300410503844240c45111800b00000c0c0b5540c86880349510514450b20114207140c2e40d005050001c084282c0010300b240049440d074000315400f0818148550904900450035500c8401241c08140b0000305040003512480300603c801d6030b42021050603010207181c1044058080c2408840c5007413901d079000d1089480c001c040490701d60301c51045898850007100e1130781148070881400300601c86011070390040348040c0028005d440002c0d881c1602c501d103008500d401c2090354072001088076000d8506942c0c0760b00c40c02c0e5071591066030b405510003d0004601502020148408000d0b1804642001604050b000109240f05d2140c0c0019a02c000b070f01d9040400c500e141c0704131001c3d43e0000c202003082c09881500042041c0349054411a504000b01002074038a081c07021005441d03d40040b40704903465501eaa80101785a4001d03c050f5120303201326444c40f805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783052419 1250 783051169 783051233
    0x30403051f14040302030a140f03040609061a09130201050c0d0302030103051b0d06151505040f09050c0f031306090605060111010c0203090f031606080403080a0603030c03050a0c 78
    0xb200e81001402000b40b41140400001c660048261103180340181010a008444000c44109610410714060040003010090006128103a0302c400c211703600c13501e0b00300a0000148800d00545900744413055101d035841002520303003079000b13103c0f0380d0039441070501a0401c2d1050107500c0c2003a92100d45980060f9012004205026017000400060300c01050394488000e44400410032001d1200c80241059484890074039506220b001c21800070321843e080c180462001d14002001c039845845403c240f10a0b004001ca25614a48169409039031408101c601d4070910101c42d1000b5040204600152401c11a4041c0420841c5c09512505880f4800002d81071811200140c030b100e03c6a0082c928a031b24020b400032806400004840300c8030801c492900d18111644002880c000c0d540060003150303805a00c0010345030f03070001c0d1900d019610944a00605a03101d0403554220780503440301a0000321008070310000719001d00000c000b50f85a500d0101c45010490f150442c51081c109000101820170102d0145 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783053669 1250 783052419 783052421
    0x120b09012306070308061c02192607061b0c0e190b03030306120f10020405100e030303010b091207060e010f080f01030b09250609050103090b0406020c030403051f 71
    0x448100c01c42e049400c181c040d8070000d0020000400c1c450190008502c99180504010013032140c0e00d900134441408944c2581d800200b030748591051031000d0035103a03a11100c0c18640103210980040ca50700900d8034911b080340403188147c0441e080001c00e401910301e04081488400b50384090081950031958074140003408588016405807a04103003450400c05800d03da0f40401101c3e080b0100701e07000e518141021107090f06111641c1081e0503288280c01118504110382d4002d003041310002c0300d0314207000d4080d590075252422607840c2241e15810400040c000d043d04040035081c5034001030190441800ea40781d5407840c02045c1d03000b1f40301107040300481d00899a1720584240217942d4914206a9906040500450746141800020310340c640e42c100040101804000390800000403140902411580161158003610b543c010400016001940418154000c0c055008041d910006540c40343d034854581000940107a030045405000c208000000700b40c0400500004c04003112400c0b0020200100b054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783054919 1250 783053669 783053729
    0xc080d0c090e13020a1823160804121b0206070f020306070903050307020f010e091e0a05071e142a0601030f0b0447010510120b0901 58
    0x50f84001d10f103d01c10b4010307242d8036000c0d401c4842d450392466036403040d9110341c0080d1003200c26000d84410b00b859029441c0c451121400d01a50710400c0040d402003405900b2503503403d0859000d4012140c558100d000342d44507400c4656251455002c5c0d01a0400c2ea90010350300742d02036003082c0c50880051040105500d401e008140d0030413418100745030020f155507500c5d07072640207580003c0d02c164201c0009604a901905649000390402040d40341a071400c61411021960400101d0707030344510308000a8440c84003445014050869505d807200001c40078440342290070860201042041104412030150882c0d440c040c04400700c2109007544508200d040d0b94030000034021005525030302850040001c12406041c0c1d0701d00c580c0110034102e16680c3c0782440201d60410758050300504000301f062502e02c41405200c01070201080241c403c2100701c90503081c054000030302070294802e0021502060880c001c0d0700300e0784000383c50400881c00041460014540d050709030b020101030821642c018035210703a140712030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783056169 1250 783054919 783054931
    0x17030f0f0c09010e0112020f04030b09101104031b0e01060302040e0c0414010807050f030a060305010f0b0108070e03070f06050a021515010c050a020a0312021e0604030c080d0c090e 79
    0x90b82450b41c40e000007843d103401a00300c4d42c10701c0780100c0d11030b8041d1580d030101c030b0400b01e016014980d1140d5914000da0b114000319810348150080742e5000d50380803940d005580e0005e80318207642d82030600f15115070402558120741c0d401c035841c1450000511002801d803071030081100381c4006845078507140b00742c4c408a20003000800482c10403c020300030b030400204100441107003840d2903005a41c40c03010135603d40c81207440f000d410880c080100f02003444a0341100d026248560028001c048120f174100c41a1074040c102503001c26a81e030001985107104d8515030014401c010216145241e48201c0d69000304040c3d081080010710000306000880c6d0100b02030030039400340c900035401501e0002d21151100080040545c1040000c03101141444402c00c03c0c000310310340091030085d80590303c3c980070b000b0300402ca0703241002d40240050703071543c503202510305d030849241000544401d641d9030390b0403101c08464000450705401c00307100e8031540840a200e80301004545890b8061614180050720070009001440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783057419 1250 783056169 783056191
    0x2010e1501080d031107060608030d0b09090a02090a0908030a060f05060a090b1b0607090303030b060705030d0b01030636180f03031b030f0c0906080c0717030f0f 71
    0x1003085202c00105500186060310380085c84001e0703058010034510400710f01071b100a04200780401c240c0e001100504074401e200d0030400103990761000303101113103508850a0040303800103034802001d420700401059010348620b0b00020682035903556108070780c0054034110301a540c0c40303105002d510b44000700b82001d030404862040c281b4070420b00044c007182140c00380c0e00c0841c0002c03458901d420308000801c6045548c1c81c00381c03009451300035401011404984421340020341070003803201272800c00b80304503800c003500304000d940780c551072003502000741c00442c0440d41015955600002c0f806404a100e4404142140c02c0d04d079280462241c1e4905e6101c00c12525820505c1c00036401154054903044102850340a043c01c0346e140c18a04045c0d005084c42d11080d06202c0a1351442003110380e01d80e115440850b00d03420b04101c00e02c880201224500980c0c0141004610f0507004640c882c101d150190040034410f4201150342c0324440310f12503182d0001d0b15281c0d241190300040c0000c040c910781d00e081d404165400b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783058669 1250 783057419 783057421
    0x105011814040314130902030907060e06091c050f03071b0e070e0a03080a0c02190311151c05162d1101060303020c030f060609010e13050d02010e15 65
    0x2044980c441c0900300406110341e840e80d84804d034005006941401040a9024074615550411a000f13544112402c510500410501266071030280c030801e180c2050140980c0d0500b0b580c0401d1101d191080b03e00e418241d07481c0f004003000200304100301c1d0615080c240141d0f44954180c51300c0354003010968074600400c40d00c802d05008240c4030b14000d950003061403408078600e900c0d03807010544010107504041e01104001448881d9142c20443c03030400a07200340c1711250401800016444a054035000c01010f0411a0800461501e040f4460011601c205191541751000c01154000030320080b134201e40d5603580f43d00c1000b103098440c14245401c0303041824070b00400800540103564407158080704080003c0f6042d45244034078400d174112007500544000800646841e400c01940e41c80d600c81c18107100380f0400041ea01c02850100300c8a003d03440180c8212200e9080141d031100b0000b00602404140716203100050111f182042203589850058000082040300e0741d400c3e909018812100c0980c03c51050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783059919 1250 783058669 783058691
    0x910050c150c030a090f0b010305010507021515010f140d050609011205120d0e0f0c091e01090b06090d060b0f220b040b030d030e1e031803100e01050118 67
    0x2c1c11658407418220000441e81c10030310b44910240702d140d1018080e0f5a060001004211781588190300070780d0386808484001c18410700403108040120f80840784110154845600c0d9400b60860f910032110030b00f807550309074145d403808068580011107162806625034013402050b042101307503240980702c505884000c8000300d0b126266204003070200003d1036a4005a000f00032035035a409640c4000341030301500c0c0440c020102035595480011010f07403083c00c242000c506010b40300b01250303600b0741e07985102101c079a1a2000c504028461407035400d070000703002c01140c02d159488010800c4840c0c421100021101100b00600039440d0f0400340340350165807400480d854035401d03465400101801d0080c0410340049405c0450003508030030121076010f119008000c0805601600f101d0802034400b4115819020034402da041c00805c00300c501d048541041003800441828181e101108410160440701c49456012020049400510200e513861355a00010310420910080c8100c540c0700302074040c0a140c1a003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783061169 1250 783059919 783059941
    0xf125115060e09040606051903172a011b05030403020f0607050d0f061205061e06130903170703020717251106190e30030910050c15 58
    0x11038442c503c240740d020001400c001654121001900e00030f0b0400401c03c43d403246800c0007880d140000c5480500c0c1c5200c00b000418640c0940c2c0c12000c1651500c4400840e010100341c00c0d12040340340c030000d9500c50908242e01c0300d0040610904056030755a4660364545402c0080c00d0081615080b82c50780c0004c0c060100555102083d1240111000c60001c0c4218540466000800365640402030116410070554103200010031441d00c0f8250700e42da0f50040c0d40c0d1200c8040c0f0600c00484002c0c0d804124400e040a50b0809940107007420ba109040009804481301e0145045250484480000a03000038410040141e0091a000c0d182400c031034041c2440b04000075440c05214040c0e200d45020006905641072021905044140c000b01a15582d40c5050b540e05d140c449030040c0707c00b0004551810103110444c14803421070b00d028100180100c000d00340b00b0070940c020494520b82603142d480140040f21040c1d60f0070401c294078600716182d050360b0715011aa224280007800d1f80400341d010469040141c00c1401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783062419 1250 783061169 783061187
    0x4060908300903030403120206010303080f090615030a0c08030a0210060b040302060f0d090c030c061d09130b01170c1905011206120b010f12511506 65
    0x5818400ca071502d24220102c1d1450081b54005411481081109a19150042101416a40a607492001075540c0302e0810201c2c1c0010348040000fa4020030001d125001424014400038a000b8180ea005003502c1e2550034400e21390f40c01042254000094503c20541c040100114401c10114107100f90740c6001c04883c59801140f10182c081c00d40084c00b0350448140c0011070f01404038212081000e02042e0800300140c2149010407226543d282e800420424001d242d40700d182c00b01880196214103444e02401251040500070300c618950141c502d500141404866034040c1110f141042c5080c000b24100b5490084008500c1e0700844511601d00c0207558503540c188140c80c0213007801401c410f110204440100001d501030a140344000d1f0b0804100280c281c125412a10f1016111080390303112a17a9101c0714941d058001c03c03e09139904a0761703e94914002100d08041ca20700c1e02d0200e141411f00a426569040d090070040d0518520120700d01081481740c880d0f1190040c142c2e56a85040c03038005850025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783063669 1250 783062419 783062503
    0x30b030a02091e180c12030d0f02250620030103030804080f040308071101031802040e011404030c0c080a121d04110414090f0c0a1404060908 62
    0x1070b6400029284048601c0081802c0d0070a240d58401031412854a40c0c025401840f001c005004860300e80b1810314011425402000108003e9440c0c56000c540e050000d05020400803802034080c001400c011030030b000300702003030408560041040c1a4914112007190320b42c1d51009020708000619285100d01201628107480c3d141c18071a40070384460800035090700803104180045600005c0100400000c2c10142032501d110f6400f03590310041010064054464805842119518031720b0f1000240c40c1c2900200300c9006440000148038181e0742c201c0d48152000c9038158003240b03410030141c0812406403c050f0007410840c0162128607015a58140344c4510504c85604202d083c0c200100c00389007005404580b42001802009800b41074054800c060701709100d1108107081e00881d18403c5c1c00c003403888034411400340b003171070503151b48500c16004507070400242c034807c011000600645551314000244040c0140c0d8070340715640c910b007001c83c03803410b0902a0203402c3e0048040a000ca40a04512038200a80d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783064919 1250 783063669 783063679
    0x12080702090702011404030e120c1507060207050a0b1e040201020c0108040302010b091612180303051308040e180c010c0611120c03090d0f1d01050c010510080d030b030a02 75
    0x2e02d840c079089024142046000a0f8080200140020180c0003501425095025142c04031500d0800710703500d44581d01d441c000c681101d03944116911003401940100a1a80b04400044c00c007080380d2502840e0804000049032a101a06d040c0320700c1c8800b05030f00d54427002280821a00781d20701540000c1d224001c03003035860b0511443e0408541014000c0d00844c491800140010240707241c03a241c0da490b010089113110300424514860380008030558002e072110602c20640301080030b6140e5904800230017008103034903c031000800c884400100e40e40000c200a0641d03180d050b500381015a005152198078210114aa501c1100303034001b282d8014800401c0640c10030000190314001070442e40980c4502046040800b9443c010000c0d040c0c3c500e0301460084c15410201c50101003451415291003110204090100743c00020101154040500e5945460340616050b41003618079401582500d06c06d4415180d01c140301001400499030402c500d0500e80d003507180a00003aa50b00300803035141c09510101038014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783066169 1250 783064919 783064921
    0x605100c03120902040f0b0406060f050f0a181805070e0117060616030309050c0f060403080306060d1d15011404051815010f0518060103090f0605100504061208070209 73
    0x200b015804400c034180c0117002481203e03507207040724005004006a90b031190780b41500104400384242e81944600303250340c4a06203040494814546640c105c00c980408010305085050208911190440000c10f01d210009544541c5e858010050715001040c8400700070082c9201000d50b82d02c450009050b24111b001c9903055201c20020440f14440c03c62b0702c04480149101500030594554424014180210181c600070140c04040101d44400c038010503500c42e409020600200d45034900071070304190000c02141c03070240b4404001007692400c1c4501120007031302c1103081c641008103006500c03801c1e0a0f185411000d41c14031103102c0005094041c0c150040c0e90322000158a2941c14903050b02c1403030150f0444088507000140c24070005401d01550494400c40311000a0500305805410054050450001040d5aa9600450041c020311100f42c480301c0d00c1041036800f040e101c0c0728040c0250303010648805003130700b4a0f0074001600d0039a40a1138840c00120003400115680d002641c161560440c0c2c14442c13 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783067419 1250 783066169 783066197
    0x100b0f010e240706060f030b04030809150a0c0f020d022a300d050a0c030c06051005010f020c0307092408070905090610031415010f050102010605100c03 67
    0x400007125182c02d001203960103402401c1c850a405032900c07030704c2080140040b540300d0290003040c1d00c9511004140c119140081800203009441c9154402c000d03000320341c00480001c00c0e07100c3c0644251020001c0d5543c4d83c159140559000301c441c2e840b10080e00050500d0411454025901c0302d1541d0182d03040844c00c00d10507407180840001071600d1500402c2d07180300c1c0c2c001c001495550382080d4442440554140e48509005c3e0003c00e40e40003c0aa40d100d59040603500e2400b96117100c001d907000c03020041079100450000e00c962040d18001e44401403030900e2603040000240034409200c452606562103c00d0842c0d2580e00003030b00805407640250041880002e446810061460042102e4106900c1c242c0104c0c0040002826500329201c2080601c561744034480e0f03058460000703882c40c0d031241803135a030103001087d41420070078100b00c9204200c0e411a03818001c0310741681400e0300808007020707180d1010849582d090041601401c4110b609040380c04000401515500f41e054006003488528480501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783068669 1250 783067419 783067429
    0x1c0210090b040b1201060c0c030b040c0b070f0303050c0c0735101d0607200a051c0305070813063b0f1015050301060f0602100b0f010e 59
    0x4010922807060036200d6403070310440c481c580c12a11444c4140c0180c54000202140720301c1200e4620350b041440d140c2442e0841c0c4032588010401002624180d80124000807407901d15401098081d01030440903101c181103103070040c02d942000c4d090350350200c0180803441c010346c008941c0d4800c4500d050020086080d000d84848407001803844001d03066010034101d0241030002180000c0e40c1480d0007030400c01e440c2c10780d00340a4031403110080d520b0349500682c0059000c900032402c13000758450044891f06070451a8510620780303a074040c000c035507603000502800b400d6081107000682013550f9040a100f64900b00d04d004003045402809158001e0204029a080c4029584082a040c07941040808c44413060341c810040045840704421498405070ba100101c003c0100f40f010407070000c0d50240c00600e900f640035070064500c3c074004001c6826003942c002a5135409200702001440280101c0140c2d40c98500c0181c101141140d40410481c14026400c03440da4a0300c030150b81005090814164500c01c0e0000f040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783069919 1250 783068669 783068687
    0x605030108120d111b06010504060b0405090702010b060c0106081002030403020d0c0311060103060e0f0705061c0b060a080402120d0804152c0c0103060e010b091903031205061c0210 79
    0x102c20320000003110001d017904e4a0030b075009001c030541105c6c82070340d071401804102e8030607100709120310700b080c070081c8482d1401502254100b0340910010889400001c0060355a50105400c011581e540301400c0022a80602000c0c03503681013500300314254500307910080e4444844464078010021450008400c050203030804000b00c022400840386150303120700d40b040091110204d8007000e4070aa12040c214008000340c08401d50701301400b09402c00d60b5490006500020000150360b01c2c6450307420728031880c1c907541d01801405200c3e42d10110181050300510920141003138000071642c0207040c44444a50304804055005a480501102541180e61980004203048503004120440300404070103c107508907440c044541c40c0303005448000304ca400054080700c100348070f210504124180104194180070000d888992000f80c106000d040d4440218601d00e5a40d030001c074041452004c0d8003620296611030254440e0080c2d8102000f41c60442d10385a0010048100074441d14024500146052203030402c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783071169 1250 783069919 783069941
    0x50c01020313031407030f08191a090606070f23010c021501060203042d0b0703020a1e110415080d0522150e030c10030509070605030108120d 62
    0x21512070410350540c002c51511210250005042c40c0401c1c000c5200c1c110494049030b40c1602c84406128656030284c484800040c0342280140050310002d17070091482c01520341c2c5e282c1d100c4296031003169175000c11100310009801c0a0068200b413080d10006216900c003280c02076044125540c499031210400d05529900ea05803103025400c2ca0310041c11b068001940340909120300f140807140f0382c0c031b56108a039039004600c1075000c01c40300c040081304000c01c100d900c200301030f83d5401ca03021513545842d00101181c0c0490821401644031035016030030700410148003901000041d48603080e1110300e8440580b160100c14039588250395a80c4813203801c1d030080b5010300042c40e0400644050341e548a0011f8032941040c080c1d241c801c1030a0169000720341e802d480150a0700c101c54600c00038040c629400303c0303520842c215816094414044800d50b103665140c0c410403c0100d039900030400f40b82a4070014100300c0039a2120050210500041c0440c80c00800d8040610a8202406480e80c5612101d0b00107085900d0786 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783072419 1250 783071169 783071171
    0x20402040315020309060a0c0c030813050609070807080304050916031d03120a020306010912080d140a0f0603081e0403021f02070807150815041e0b0406030b011401050c01 75
    0x200000b0341089030042c610501003041628460b603103461408054034800c54903030300010100405d0800103406884500d0300058880c600900c1514103568903407808200f03030b40405140d4070190f020010707030a040084001400140d40510b08180ca40b03408984001d502038000040341d01c0005061558030310a602084030031800d201b0111100c040d920100b0303140d901ca841025101601c0e50b00142100d0b032140201c07409014180c2d0f8502e01180f4190400404d00402d400c1155002020003240003400100e001c1c5014481040c60a943d0b0350030140c0c00b29048410800c0611056800c20383c041012943e190240c40100d5400b42c4404500d072040d0100010601c0780350402035200c1e41c0386001d03482030840003a808a0f00b01081d02111412910782c0d00641e80c5095500c02c03a2901d003518140c0710403042c0700743c000ca900400c49003100105211188009403d0302d0721009002c0c1294414401c03502e01840d6070194400691041d14200005419900c910401c08814020354494124420082c0f4240c1d03c180d0880d0300e15155400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783073669 1250 783072419 783072443
    0x50706110c150105032404060b060c01020327060403200c03030c01061a0f0304031809180201021e060105060903240a060f053a061b09080a0305070204020403 69
    0x1108000c2083c0240c600074498466444441000b0446103c01b8040301001811300c0d617183d40c4c038032018204400c0e04030741059007484881c40180c2d090000e58091408a00003202d2401412650845100c1451040250360b010405100200c0d4203c040301d43c0c0148a5004001580343c01c2081302d02d0140220450391b050300c40005e0900100f40190300110a948081c1c010600c0300190381100c071441c8c010301d90cc0e81401d074400c04c08500020300803c9100041040503102022061342c80350314404446010051620880070f00040a0840d80d040c031080e0074000006c8048039034200602c0783c3c03e640d0801401002c1c012440010403000996040003050208407a20b402c600c1c0036140c0071f0f54114407140a0385d1650130981407600114040603d8419039098079030207407021420340ca44a1031412002c05180c0403882c49002d01486191270000c44a40141d014020b0001041c145000401d030b0814040c004220b83c100001c5450501c41004041280c41c3d202c1c0d094504980c68035441c0c00094000e2095600080c10520485 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783074919 1250 783073669 783073693
    0x8060a05030a0507090612081813050106030903030509012706141014040612060510050406060c0b010906380703090302040e1b1203070b0a02120c0406050706110c 71
    0x80c0e19040d05c00301c0d1030500c026599034a000d040f680d030f40c100080800e1018081114582442d8654103051040200062850214003009100b100d43c01c1c0c200f07800180d00e41080030b007030503003601a00d508041518000c1010b2229502003814036403000304201070030308410f14013005002807500007040448400c01d112009003480b00341007025403481d2050110382080c401818003145400c1c0b288804a80c01e01d0f2101c107203842c041d0f840b03100a20b0020030224407101700400101d0561204d1041002a0003162039001100c2c40300c0c00c003d502d600050f4040041c02d1f00b0a10140300c11101403c18403101018514884d03144e8170181030500141c180308040c45541341000c50130206241d80400c0c0c601c120781c001d460400400c05180086511380940051102d0464041c8100c00840d0408004c03840c041401602900c1c2032011590b038802d68075a06458a528541c0c0100c0c1040d00b00c2c4070031b8411908000d1922126261521f8104090800e02409a000d030603142d81d4402c2407004102c04007201c0d00304001c4000d441040c1070348 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783076169 1250 783074919 783074923
    0x15150a03090302160b030c071406040507230607080906040806100509070e030a110f0a03150605030a1a15132a0e06130308030c12160f08060a05030a05 66
    0x20010750052040b001d00719120000d1010340c1c426205a091246e00c1d40d91501c0ca641e2043d84001d00840b0a0382600100103811f13401130121038000d510032070141c072a80e803400d03507030307207003086600c140c001c0104185001159503a40304403c0710140d41e40301e04c046441d26a02c0300020828080c40e8490412409400c0800028101c1c030101c0006460080303034034150036200c1100480303040480740d0f000c80d0950300c48504840451a1800590328120000300000314241c400004103008120a90007100c0c82c02e194550300e1103003034060041f00003825050307004003200ca9450f1200d80514820300080892180e07100003203100841030030008003059101410512101007010010401005030031041c08100011480c404140305140358110f07005002a69000d44400d8000c0800611703502c04201044034a2504100000042d0713400d0180d4812450017902030786076129041d00b0030550070000d1441001600f8070805500c0da941003003603d03104001c58504174035140c2c2c43c100440c100903034a4110640c14410f105202040103c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783077419 1250 783076169 783076181
    0x30b150304030216030201020a0b04062423010c0b090a0605040807260405090a0f0c05040812120f0403020c03012903070602060f130204020d0207050c0f060315150a03 73
    0x10075030850b0355210407003481303541820a5000080c01030b088402e004000c6064a030320142c0190041000240d29402e0252102032078020000d01614490503140070843c030109080d09400740c041c000300a691151070800000c2c003103d400d402c014001c983c9813001c620400d00070408004200d502400c10001800c1c2030800b0415a007000c1412161501c0000303071101008003154849510480c00540241494140020800003540040c41c018902e680c400c01301c418080c40307000d24011a130554843e9640c86007800b507040e040c2428440c000c502002c00f080b060001106036285954000c01d10703c08400c164a4510b01241040f0098203815070641c2050040d420740e0226258200040228201100000c4840d1080c140c80310454801d0f140541c201500062044680007440c40d44502d006400101107551940083c2c100d0700310042030030758590b01040340b01c00c0080404c13060307020280071074100c03501d9039011000a51920005213090200d0b54041c00f6203140f6100c010b01d403182c819601c0300050b12160011401001815 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783078669 1250 783077419 783077423
    0xa0503040b09010603080f1809010f0302090a020426010b030d05040f081f0504030c1509112d01030f0504060e01050c1c0c090509040605061e0f0d03030b150304 70
    0x190110115031401c005100d04c40032a40e101c11070f141004400c031410015500100001616100f07485081041075403034440e03140c06001c1508a10505a086005001505000403c2c20107110305c1080140407000100c04c10440741c0394a4608649204c0c807001002d805041d462401035010b21031403074480d4100340c1000191007a50703c91044411690740d1491760035583c03288d41074281e0300030342071040c40c44180c1029041641d00c54040d0902e8403400c403969650744540c3c8006001c4da10407554400c1c02204001c001100d07502c030104111941c010380507003442d0070319030300701d15104007403a03421000c070884404d034000e800600c0c1801080b842046545060309105004c0d00300d41d4284401035282c00c00144080b411001501d0038480c1840c4100d825400e4800c512005088006030582800f200c00f60018040e83c6000d0240d03c121b1041d10003254500b8040280072207c84681c0413949601d03c0384406908640b60090801c401c0002112a0180301180e07050035401001c0241441c2d420102085001c0179024080d002580118 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783079919 1250 783078669 783078683
    0x1e07053c071401020307110f0a08030415090909080901120f0e030403060c030207150f0b0d08091f0c1e050f0616030203040c030f0204110c0f120c1f110a050304 70
    0xd0341c0ba500498807841742880040201602d00c80045040c2031442140307000400281140124503211101c01d032854200c0d61140b444910340b4000401802c4d03214103101300402004e070003441305104554480c1c019003c0d45142a0400000d81c084041030200707030f000002c01240e500b0081100c100c0c0d0b100e84648950040c0011b403144c1c1e0802108400480c131038800c07190400d4100b1000e00030b04640c44001005080444200640715403160500c10ba02d541c0c100d8000a03042c0315140c2c00c0d42e5550300d103090011403035031408083e179401c0b03a1110620030b0a4102d0101041142d0003880c03062402e104400010310314000e03003006046813043ca8050119440c0000c1d51a01495a0341c821000c1030700d64000c120141e200440f030040ca4600d40c10700420004080703d1502d07861070304c01040820340003c443c400c6000d9070494a803500310755000700c0c1c0c104104417050050340144011074940c24904003800500c541c0e40c42c04100c08003040420303244410001c140d151301441103007520320555a0756040c100001802501b00383c1d0305807410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783081169 1250 783079919 783079949
    0xf030e03030609161103031e0a050c09010c14060915130201091703210601030623090c070804060f090506120a020a0c0c09021e07053c07 60
    0x110001080c1d0b84620001441044250303180034611005500c00c4403050144408204045a00c0600f40b014601c04d004000c0d862003d01e9004111545560020b003001c4441d92510b024010880080800c072031100000b824030f03640310400342c07528011625052400e01c860340602400e0108400b008151040c0000a46425002c3e0b030301d49542c1c2d00c1c4d00d40294a40203001c00d101403c200007100c03090800c5042801d03038805030390505000607900110850140070700e0a80a9010080080540c4c241c80b6407000381a0315680041c055010066544040c0202c0312903600c01c520100001e03001c442c0c008100c03440285d011200903100c564620004c1c1809988804600c04504000c0001c1268200340702554851001000c8007006a16240d842000a6204118074001c0181401c1e00030085280c03030000400429001c440147c1c0ca2804200200c521418403c00981e80b507000c0080070049040082c1100202d600c42940100e070700441c4101d01035112441d05250030002500d1840000500049104000c6a060708180005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783082419 1250 783081169 783081191
    0x370f02120412082209150b07060b03011d03120106110307170d06171209030307030e0102030715050f07140d0f020c0a0c09110f07060b0406150f03 64
    0xc4410410303249121000500c4108145084800080c09a07806440442e1501c07035406650180a00f001294804131075150b001041541028802e901c2600da12601c1014401e007041d03802441c902c01c416024000c140c40e1b0410f000c041d51300b1340c000c134015000d450b6040c200030b020b09a00368894103d04a0044180400c100001d036042c040c40c010090366941d8805140b0303020076a031359001900300b240480d01c012082030000c076210000901c1980090043c213194184d2045290001501d0008601d075038a0a00d00140017900554034008192280c40d07070301d8140403409202c5080100e00d180107800002e02100f81c0c6805c012050f1005a020724020004d11010420781d66403071400b40c4040400903c00c0c0b1200c44104148802d8010540c840016464800400340c42c0491101c0c0452234086186025120b01c82082000c00c0103459622a0260f00c02c01104454104030078410040718a002d000805450340380c6400710301502e036450342d12881c0070305901c1135840300004680c1c000030010400418840c012038681700007640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783083669 1250 783082419 783082423
    0x90606090914040f0816080f0403140d050a0f0302130e0402010e03060402010e0d02030a080c070503061e06040504081201090c120b030a020f0d0c0902091003021608370f02 75
    0x80f01d81d070030035101c0341041d5140d03030352084560140d00b01652110401d030907007000030a040300400c01c6010380701e64591194103604103020345016114400303e1503800350105251190f040130580711040c402d41803e1014031406441030f00644a444070180745142c1010001c80d07030214000c00075008134001c0c1e03a56595801842c050560f20841a42c1c060302140403000b040311540381c0500314040880c0f02405070340b80c64205580341c2d009031b0040044910150080002403003541020040d450b800f070703120b109084898030108940001540c0183c0854025611040081d0030710840340300700d805107200c00309103607029a580e4030040b005194114415001840141d480e518a10640c010711004100007000340500c80c05607820041415800d91142d604070080d200601c0c00304651800c0000206071138074025a94031455000c0091000d0482622028148140a403c0481e100b080d9150542a80b014219a8590f51000402840d1240c0310010342c46406032004143e900b08001410b590341981ca40701d0146c8122544000d90f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783084919 1250 783083669 783083671
    0x3091606050a120b0d052b0804080304060b2d0301110403050705090a27020f0603010305061302010e1c060b0d121d1e01090e090304030813090606090914 67
    0x48001142c3d5004203154101d10380c0310f20071a0400422480c03412040b562282d003040c01071b144684203501001c0511004c449422171554034081589800750007807805645426803800081e0000e001c50340d5588a611441e21a032a02110340f07000312480b107842c02090b0386074410614141261602a5007000c074400800001c020a0fa01a80e5018020f490554100300502402100040010760304d0354076100035069031b600300183c0680c40d009141c42c805101c00d0324018000c079080f6110003c0c1c013540c400c000400101d80e0104100b600501c04440000f403940e000d00040300e0464043d80c01c964000c40b40c1e0101411003c6002041408900c910002d114602815040103200310007004041d0000c0c030b001584000301c62207007145801418032440c11071211a05100812070144044441c1507650300c1200b0f00005560f0045126001068442540403003403504c880120b46a019921004007115000300703013150b0940c2d00c808048060a5a03c100f0007045544510007040340742c0078803030081c0051514000c50400400b410f025 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783086169 1250 783084919 783084937
    0x50c030c0f0d020a09060b030a1803090e0403110303011d0604200a0504081f18020a0b070212033103020307030201080a0207060c0807020124090c020709020309160605 73
    0x1c80d0800e0229003845038180072100704982c04015103001080005181c42404007405407041d00716224600707010050103e900c842e1511113032440035209400025840044036068840310f00c0311082c1d03500e80f440c043d11180c0060502444a020100c0007280d60607501128051407010031340601915201c42052100702d4048a00d24170303090450320446515040080006d01000e8801d03c0d1503494169181d641904203840c911154005000802290002d00201e02851303610f030000c0700c01d5082c0030080d5400900501940d02c2250b9112101050410941d958070442e89403e290003c01e5035514240f50030b0311400c8465107000520013011010700300400007020a40c050035a54080c0041002c4c604580040d07454180061411b83d01c0381c0c00704030b041c0c00100c5501840d00000c4150b212243e40707050800d40a400d495030346c117003601c148910015001041100d2522002124030080b80040d03903400e00b0104034100b003540d4015004081c000014006a1240000d0350302205080d41043e105194803244121210b00c076280c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783087419 1250 783086169 783086179
    0x18050319050c03040e062407020112050610080a0f1404030f4b020106050a140108041502120903090a1a030402191206050a0e1507111513050c030c 64
    0x600c0f00b0403200c16101d1300048010712100c101f2514800d070011020310311155030807400010507290115600039103e51034100d44440d050041e46021800704444400c51300ba00c00400c1110008031302482c1041d4082c444c0310020311402d01075100e447c0b08060080e54103460840000310360b5005c1800303442c4030700c6c50410004081a905000a480b040100d080f160540c86807140092420542d41d032007040543c000405404150008590285040c003040110324481d48640c1c040301034000c294009aa10010280d0b201d9031000710100080d19000e00e07900240600c211000741c5044c1074017441a21803001000c1c08103154102c4800003000e48404141400000d00c80036488d0042c82030011600614180c4000c3d03804001d03604007064020b55403040144484100c40c019104103036544103002c01d190950084640003091440180b04105400d40d0095800400a1201003007140049040d401c1810503c41c4d6980082c4040041489003810042d058000100c658111007a00c00c95001d480503080216140001100c0184 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783088669 1250 783087419 783087427
    0x6090e0a1e0203030714071203030e0f07060f080c0702100c201e0d05030a0504050a05060a02190503040503060115080f0601090b07320601090b0a03021318050319050c03 74
    0x952aa480c240c0206ca2607218081c0c09004100c0d6500000b0500c240340c00703a03401044480d403410042d41002c05a140141882d001100140480b40e04450803c545003010b1070400840e40e00c5030001062400f400c48020740c004034009203a807020b648004c2c0582100d00a500c0c50701d441d039030030700910941c0600310380e902d1f002880100702ca03402c10020004036561745000740c14030070162203aa44160559009001e07600c0443d00205007400f07036007802401500501420f5456601e042d08011003c3e6480351907032076020445000742e07090010488140103850050501400302c0f4441e584899241205159510072100081c041c0b0002032818001c4081c2c0c140198010307140d4845c2c6905101100709194810101552075040e20760030a10049039000404c85910080015041d00307103980c01e4a50f0820406030300c03006045d81041c9640007155111b40411046a50488007414903068680c0000c000d005044800c8507101000385282e0103006000c4018142400d00b945c1004405052980c15680c500440c1c0e03540c20290700a01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783089919 1250 783088669 783088673
    0xa060918150b0a0e0405091b032a060d0f050105040e031305011b0209010e040308010b04210314180f04060b1623010c021204180c0306090e0a1e02030307 67
    0x98020315000e0f40902d802c0e00c00b01e042c0320128094400c140c401d00059841030014803050a200d200b5035080b204c0031805040086001d682c0400500c1525a003c00040714809110300c0c2c1d40daa500031100c1080e070785541070003200c00054903403000b46402d1080b18021424501003410460012040f00d82c400154410480b955042800466641c482a0501000710000c04007031009aa241c8041038002c0120300c0c11803449103451318008042e48010391254000140902080c000180841021100100c800900c240b4440c01400c084030f0648082807030b00d01c8170400280f9000c2d40501c80c200000c00e080280d0314410345d80b036070b0014001211894801c413000b0300010b00c00b4610b00400c030a1100c0001c1d024a070710f2018400b510140148103400c8198654407a0b541e030001c0c41209406010900908202804e2241010b2412030a0741852401c00a407000700303541c50003480e03150342c007030f50040380940102e032010040c9030b0141c0d55441d6100b00b50f030f0054071004900e0070100d0001d51f4442055000950280203581440265 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783091169 1250 783089919 783089939
    0x10902041d060112110c1c172503090203010c050c07030605040602070206030106181202130e1203010b0a0215041e050a02090708160c031d0d020a06091815 68
    0x25007890304004e2114034080181180d400760b55942c1800c00c50440e40c503484813010a29200c21079820411032000f10340c0c0c40e0140b5400400800300010307440c082e034550340daa018003400c03403600c89401440807410031604031801d558180d0100c200300e4402d4000300f1507410110401c3c2e525000e1008506029441110140300248054008580040c4a100090304160f983d50005171250400d0b00031100007891145450b00b4452103540d8040106a0007115040105403500031070b8404290302d0303041100d103407034000b5010713030041c200040a44a40070b501c80c151256114001c0c01820b44c40810000011710a044041c3e0324a6401c0440354012903000d82d4500d0710f00074184581c0c000010802094441c2c0c01161002805030301c40001e0300b0f100754100d60315180c9614001424019074421001500100f0220540220000c0d81021031100319195004901c100c2e0007910000401d0255074000003034028402e17080002e1b406800120b01c1059926800400107000301c10b8981a08803000c002d040249180380380c0c0e04103c42d03816 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783092419 1250 783091169 783091171
    0x611151b0d090303021c0506060f0703020a050703050f010e070806070f05130326090f06090409050304090e0105012405070201050409090b06120a03020705120c0307080102030f010902041d 82
    0x24110314642489211080704040303644112040d00400d4000450308000328400a0403c880d00c1484000c00071400c1050114810340a01140d440a2000020304002494020404008042d0340039040350b2081e52249403e60700c81c104880c1e020565805c10100761a40754020900c1003d07150340c0e10050030306a0f2903803002c40d83d00c1c0c0429658018494200402000c0b0030415401101640c06100443d01c98031490388940c508003900d000d40b452805090003101103560703441c02218800e03002142e810340c5076180180010b00a06035400018054030001900195140c0a5084400b40c0c02201c0c000f002660b82c4d648480038a62946e1135031800020380d036040801d805001d00058004180189492410987c4489104045074000c170001e0300c0d8042d0010030880c00c0e1a0402d0b030300080000510140000468540c0c1c0a9690b00242c0610f45c881c441202200049400030404480d048030024112500555280c1c0a18001e510070b490322248103802c8400899417817298000c80b0300b150f03950142440b41400a140800240380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783093525 1106 783092419 783092461
    0x709061407051b130c0215090f211605030d0606020d0e060705010b0301020310030b01120b04080903070308040f1409060609060f1c06061115 62
    0x32020510b01001012503110040c10042140000c0800107102d58044c401450400540c01155001070503001e80e842d141c20b038626945440141a4907808541c0115403039611600001422080b0780c10121412010400514180810500746881081ca08402607459600c0414228400b030407a116901c000c00a50008000c5070805050280c014004032045905c1800042008001d1003829013013220040e0700200219074074681190300700d4000a080c0411f851988001c4008240300580800340e1403101d400901c070519964803540c0e1648641e11041d42d66030035004410002000607142c2c0c003d04081c204180d03402482500b4006406c800c00518483e0502c03139010078007401465207840f41102d5042105840e01a03881c48841d2a100381e911840212507d5403c2001c076078680342103980e100d10140c4a0541d0750789201054104015a52031810f130110b40e40b880f038030740800c6502d0b040040b000341d24130b = true := by decide +kernel

theorem cover : BRFrame.Cov 782913669 783093525 := by
  have h0 := BRFrame.cov_init 782913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782913669 ≤ n) (h2 : n < 783093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
