-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0863
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:14:23.857466+00:00
-- url     : https://prove2.me/submissions/fe5f907a-fce4-497b-a5d3-07656e0a3de9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155035971 ≤ n < 155215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155037221 1250 155035971 155035981
    0xf07080a021b0a15020702090a090203010209060304050a0c060c0803180f1203010306060506040e130602071a0601090902090a031407050402030c130509070507061a06210a1503030503 80
    0x901c10b468014100300711801010081000100e074640415008090305074a0110306901c250507481a010000d501916070400134510389010740c00b00c0c0600c0e001900042c00c0214071404a04254400e82e015200c0e86d22a4000000b00100b03600c0010107889c0c1480d154800a40070ba0340c086090002a0030b8050481040400c21003003002004070300014038a10701101c00c81c010300140b100c0c85a100780010b07a041ca05010020a290810008071011070364821312400c102d0f510b00b81c461241c0f415029044510030340070002c6801140d50f1380710070407503912201c2491809050080001d085003095038072141c2001e0040c0803160b090787d101d100480c11207800c10040e010450740b046c282800c015098000503401880402030000c0498070310081c20950b545115000c022a45650400803d0442241d0b030704000752003000407400043d100c1d001651a1907000c00302d001c038445040c00140d1103800118150b540211000b4030f0621a0401d0b092131608809200402c20150318800c1c006c10b80207801c1d02018051000c004040b40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155038471 1250 155037221 155037241
    0x50d0f020907030c030e010b0604150908010c05040501020c03060402010206010b0702040e1002030402151206010e060d0516032301060c1502070818040c21060909060507030e03030f0708 81
    0x15005a40108240c00500c2c0000c0080c0c01441c540403502e0009180c030030303401201d40e0144078a5200d08001400300d800c00303240c0040196200407440405082060302c1000081e000401d0060141140d1251900e54480303061100083c900340450b18000e00c207601030710501000d40d801098160644042040780e40da07814060000c1400b0b81504805c0060610440c0220340b100c08480c4d000e10b00035442110990311400e840341890a80c2d00403544d52031080e400040c08511517600600a100005002602040c24450202d414a044680172107803101c8514a12103441030a5a0610036210f0005181d416180c00715800c10301441c2100c014000c000900c05051041014404007555620b40c1d45400201959241d410f80782c50300c1c42c0d400400c4000b046030903c100001091405010b00e0342e1408441e6034080c05541c1c0a00f0b07507041510610b4030381955660728072010039150424064100d02d00d00810000c2580d0401c11700c010300b20b807191946100650018400d10000150340c919081e0000c0389880c0103001d03521650114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155039721 1250 155038471 155038493
    0x6142d0a090206070b090c0904050d0f03060b070303090308010f0605120604140711010c0e0306190b0312120f0402180601021216111905061c060f15051201050d 70
    0x20394085404202031042064401000c6c0c0f0070b1003000c041c0c5140300d880700107000b0303c54425100103107035402000c90b049140b441220b03440d400e00640d25001c80c52030f075208e44401c60b661041500b540080c0c0c407050f40d00141900b0055003401803481241285a5a1902074010501e0240840c03440340d150030712001c9002079a0395006281c004180c0e0b0394110792402c0c2001c000d030944000307220341180c039402e05441c40901e40c040c1c51419020b500140141000e61740d402014600c03154860031400c140e5640724a4240d65842c100040c14003080060310003580c07034454148044410400a0080c02c1c8020184200401a01e60b0440c1068410700d51400d540c454a500380140d0500c810f0070031300600c01c05c0c0802c40d200b014440d003a036404814000c4208441030230041043c0f20b0709030305c000410b003801c840b000780401081c1070071030041248464100703881c1c80c101c13108000c4209492240c0d00001d403465503004148480700c1c943e142c1c40703a40090f0341401c52401c1d102108014003e0014401c00c2d00c158a204402d1040c4061036640c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155040971 1250 155039721 155039723
    0xd020313020913050d0504030c05090910051003030905030303010b0703050f070203150403030b0f03061305010e03040f06021903120e010b090408031008030f030c0318010906142d0a09 80
    0x41e02910301e00058a030021642c004025100345c8900340300d079488140250211001c0d2074000c1d80f00d0313030511300f40300512508185c00342c4a000e60703100340389013545c105009114540c021180140c040c10841d145040042c07001541e0741129100e60010401042034400c11401c0b9003202e035150802689402d0001c1d4900034078003c00710083d4060181c1d080300d04400c01d01c5505c0c50310851003900c04011071030409003070100100c0713003000f00c85d0160310030804924030030240c2002030700c058840d80000c118410581e03805030542d0003960060040380a01041440800d8062055030350300280c1d01c010350240011078034014034060603041100c40450352200901e10409080d0001503400c0c402400700360b25402c091500702c0701c56100f181d6503101418100b0f0082401d00d808011648801c801c1c4002e42d0031a11140c0494500d80d00c0540b038008100c00232010b251180c40c0030b0048041a48c003c1a0015035040c0841403000c1c8400c0003000c01071103032800804032031120182c189042440000d40ca041226940300e5038900014410804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155042221 1250 155040971 155040979
    0x31e07020a05013b1b04060f0f080f0f0606040b04020c01230a0e0c040506010c051204140f060a080901060f0b0c0106060305070903030c030c0206030702030306010f0905060d02031302 80
    0x50f801c42c10b07448242441e94070342c1c1080d00010360318640c44c446a00c8400c88001104054010030b1081c02034540c0d00025000c0254000e000040d1981e41d00800148606140d2140c0b1044101d120308208240b4180498481028508007074885610300000c1140c540700c008020500c40c1d03541d40901300030364440358183c1d10090b21800c020401241204800106003198090040c040402174000030340d035000e030f800f400015000800003060300808000810000e480d00600c0c66040041000d18000820000c0011006d4980c00703416265581e414005c2054800d421441b406000b00003096040e00f041d01e0781c02c00c85020034042e10303100010380c481907049800340420390300110f060039a0481c040796807944c01d4014042d1904440c000c02c42540c0e14030081d416074004540040100d40220300c10004680945000280c0c0c601c03038686000c0380541a070000ea40ca8000707451010050303101004100003541c200d48100203a42d42410b01411541ca0f10300000d400c0d00c10f494114400c03503008804070b00310030a0001e2281007154024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155043471 1250 155042221 155042231
    0xc06050c0a12050711010203040602070e04170a0f022505040207150c1107090605240408030a0c02030c0901260c030102040e07141603080606130905100605031e07020a0501 75
    0xd9002442900003840949031417641130b03100381417580008200d07806c072a0241c0181000c203140c040a247d80c1440148107545210b0500c80414045000c0001050b205541c2e80303801c1e054511410000f031800c820400409580d514a6000344000d0200510404c21120101d4015a50384420f181c462089124914400760ba20f0500e941c000d1642e802548a0141041c0c0f081201d281e103581d00300003c1950782c81c0c8541034004894051510010204d0b908031504040603070001072410307075170b100390310b01c0c590141c40d0700310003d0007100c0c94804510b402d00103141403110465200c2c070f15505040102c100f46107059602139450303032210a80e1120240900101c00b030a0b1004000b1515541d9803950720620440171a10304002410510141190780500415140c40751125401103070b0b40301039a0343c00d40703c0540151000c5e40c0500284000c00780c00851010300030242c007000001180740d007410b000c0124186451340111080c03140907c20041e181041603110000300440a811789100d403200070050f070801d51011701c040d280354205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155044721 1250 155043471 155043503
    0x190510050702060a0c080f010b0a05130905220210051305090f0906090703050d0e04061205010b012c270a1e020c1b0a0b070b090c030a0c06050c0a 64
    0x1c1206403051340100030500003226804030881d40e0785011101041010400c41c0184070005088000d01180303442420300602d0b0041d4220586d4604e08584d006203195506c0710304100041306001c28140c40c0d14030410164000c644c55900050340344012020300c000300500401c4e45902e00004520004c0240805001841582000203402d40006000c60303544105216150100340103110018101d8100d030381003070140003a0b41c40e0503011900c50001c414241c3e40161510004a81c518104000e600f00c02d00c250000030b21201e8a0001405031a840e06040550b500d544081c030401107446000880c83c4581201d881a0840703501c4c0c1602107140d441c440b00c1010380010030400940706042d601420712205e0300c0d82c0780007211141008040507446103000c0a8801d030840514981f4040041070048080140103042812403910340103c100c445d003041c4001d0722100005420300061620920130210310a01c25400b41294003541d403103001c03c1d07103d10b06c5a01c040000c0002c41c0794035080d007840050451548802c3d408585030750 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155045971 1250 155044721 155044723
    0x40204060e0f010f0219030504090e010f0f0501050a170a14060f01121a0601090923011e03020d0f05010501060309020906040608060a091104060306140c0c190510050702 74
    0x108a038603070060b2841c1d4203900180d03016042da0611201194000c0503141006c02c2c1e803c19824100794110140700e010b020100d440b8075180220980404440b00000d90700031800001402e541e144013600c40028503180041c403054503003907084400d80301012001d181c2c012001a20030303e04000d406001d803180c3c0038401c0001c40b011021400324011034a6290102c0c840e6260140d588584400d4a4000d014680c00c003a56610341200c540f103035910000504241c500e40f03565040920584422105c0003040399a0600c6d64680301da235040c04280580b00504000300078070038030628050021030724000684512a0103840c00d04200f81c0920200d03d0076030040c0240300c0c1d940c0d6600060054409840c0c124401c10401000a000b030a0a00c6100d01b1160310200919058507007603070400041c0b0014805542c4030000d40120f01c129110340c05640002c5108103c00120000700070506640240044c10f001040d1608010f08050b006000030031580c2051960036a0880d413400e07117800b82ca02051516a019031504020402c40510b030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155047221 1250 155045971 155045987
    0x2070305030313140105010e0f060d0f030f030f0e0d11031b0c01080601080f1b040b1206010e1f140d050a060611030405030a0f0311030d02030901060504060302100e030c04020406 78
    0x403140001c502c1141031081c41a01b80c0d03400b401440d5003010302d14000b801e401803040c070701900321002800c50351620485450390020500c0040064000c600c07100080134a09905114419202900b1942000704085801d240c1344c841c03400130000d00c104a041c0308141088030040c01200d044d400540a40c0d15883e41c0d102d4030300d440d440a079480da40858581400036406502804145101d00b40480c28420940e1300c242100503070311864000e1844140040c0000b041215610001709001c0e0007104000ca21460714000050100100481e5203014441c1c0042ca80801405070f2103c0e04a00b02c2070410b40355034031545005140c140141c03112000040c1c1424280200030303846501c5042a1206030340c810211a00060302142d40c0e12a6201e150b4250740190850383c04603000003800410315200c1e1806640d84d04001c00d8a40ca10707001440c82104840d400014440080303001d1044400a00c01070301c09001e80303403131900000d002d00c08500460080c032030345d00c0560044d540c041c0200340c0c3d1200010821074651707444160080c9242 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155048471 1250 155047221 155047223
    0x60503030a020d0906141b010f0e060420060d0c03020904062403050c120c0c0708061006140d02090f0603010924050906060a02010e01142e1502070305030313 69
    0x100440000b185c076030702c55051565032409100840385082c0d44a2600001c144c5845c0c41c0031025543c440642026000030300404100c0c40c1034800401450500e8240f00c240e0402d06000070302201500303003da25103038407240255850722002d5070b000150044030890a40c041c0c1b190030021940603103001c001003001c400b207a2011711a01020610b11117400c201c0e800a03001c0316020b0340c85081411b4140522904403039042c000d15070083d2084101030074980110700c0786240c0021a0008045600710004008490500c071014500900c00c03490004802900900c46160b00c0c031444201504031900002c0304c0380552940c1e1042404000050803d6640e5a0745400726801000303000710f00110f13140c141581c000d110129001139810340f0001070140506032070380d5041002c140e200100030429552a40c00001e02d5050a209003a00c03900c070307030144081a10307003000c200314001110821600e1406140c0c10008600c103083c4007000507501148079544c90b00c91106020703483c01c1881e6000a000d4400001000035001603110003242c21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155049721 1250 155048471 155048477
    0xf0609061404080d090816060207050f160501030b0303091f030f060f0b03060d0804090606080a09050601060e0310050c04080d020a200d05030d1a120a02100201060503030a020d 77
    0x80d140320440c1205080141c5010344041d80501130030103d84290351200010f14850142c00c3c0c0b4000c014180a00d03200d0300a00300391503e540c04246d04090001c1840f8160a101c4808080d00803807102c12841c00700101c245c02a54105a030301c1c84103254503102042101c40c0701c02d0040401860303c1d60440002d4000310316000c2c0000080c145412445500c14501805083c0d4482c804100181402c124070320410760070051400742d00a4005d10817001003241e8600610281555910115001d81088009050b5003030240051070514a07059051002c15008900c49040d90503034a03111403102200350001c1c1c50480130400d01e501c0c0a01e00b60620280d540518000c00403100603038250361f124501c01205a860780c9071008090171810081150b80301144d41c811040204481c02000308001001c035458072851900310480240c40c05685040301c0302d10310707107240380c0c2c1140040841c1c420a0200030b010740c0ba500e400d16004001e0280040c1ca0350078080d58000e402c1403000d008041e040307070b0320f48201c1d1070000d544600042c03141000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155050971 1250 155049721 155049731
    0x9030b0a090516030b01031403070f0c0504060f050906040506152d19050702011701030f02040f0b0d03050f0c120a080c090a030305180a120c0e0618130f060906 70
    0x40c046441411402c99410201c0100c41d0fa28603108c600d680f88180c828514180400c008200001d1b1103592a91004c501070000e0104103424441031204030381090b04042c00001302c1110801503592040f0820b5406081510041101e03142d40d400f0581440c1c814060710b240c200301260721090b02c41c594164a040044006c100c03204030407113103104505407142da600050f40c0b0f000c204a000c44207001d48021b101144c41032601070480000d1100d1780c0c801550070b8200b16030107200350034441c06514042c05000c0c089242c00030b0410218010400150010740c0c21307000203042c01004a030100f15107070341e40d055651011003141506c16280001501ca480c40d0f101103a048040b41c5c682c0041408441401c0c143c03169030030042c01e03000381141140c905840503004084410401900898840015251050010024080d010700300501c0c21151500100c3e502058102180c102c0d1460204a400c3d0fa498418007078000c3c0121885a0580f5498080d540d036596100000d0201841c0d0003203201007124650081c02214014102000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155052221 1250 155050971 155050993
    0x6050409030503060123031801050a0608070513060317091905030703150912020c0f1503070503041505090312091c030e03091e0a08060c0d0207020109030b0a0905 71
    0x4503000d032140a00010300038000141c0c50b500605206c1086940e136150900034410009000713109a01c200d4080360844502c03217682c0c410304000d00030950010740c180010710189061a0480b551080035214843c03240781c450301c200e40f03418041d038407280103140c02881c00d110503948020100455804051942d0084012020359201307941e0240c594002d44000030054251146107445200d00031100c0d12819443d16a00c4502d240000e10762810b00070107060a03000ba100d83c0c0f89080c00c0001c0c03640b2940496014034030200400c41c9010700c040442c2da10010600704640c4a03103840c2807901d141289582c800c100580350006100f00c00720000f01410700c003501c1c0900000240d96202c0980e840701d5501d20a106441e800400280c00240a50060440341d0501011641890b0046000a40f00300b85484844050001c000342c80b2010b08004100e030000d4200780c0d0082145051416078650741f4070400481d544065404980103045a200d0040d1000441e0450340c540c0090801004003002000b0407102151641301306800d041d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155053471 1250 155052221 155052229
    0x90a0806061003110405030a0f290105130b12300d0e120c030405090a02040b0921120405090c040b0301091109060f090901080c130e01180803070f02070b0d0b010201270203010605 78
    0xc0c591001652b14100340d00c0c12051008032201021040c4003903858030101d103159161103900d1680f8000c104018411031010b812041041c9188100000100300c019032294140340f00c2c0710445440e00810f80d800510f101c00e0811883c01c10074105003810408000295080100358000702030030940c0ca084602100e0f540380e600d8028101d00c034a2048070141e000900650301c8030314000101201303000710702a8840305854090000c03030419506004d10f00325000d010400380124100003949940c005030711000f03c2e1800c0c1c204003f141150205104042c4004e03115040303004451010300039074000400203001e454a40d80c00160340d280701e411000d4030f40d02944d038420000403404000505a00e59103009401a8a04401c52008901070101411004c0e0950b403905410b4603c0319045180510710b9000341c480756140c0c10030300300050514160b140f6040c11540640c4003440a4008001150b20002002c0e5000a50307115040c0142d01400726110410f0041c0041c450b41e680022001c00480c0e07038a80b086000b005081c0c0c5a40c200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155054721 1250 155053471 155053523
    0x6050a030f11040b0301290a0302091602070306021305182a13060c020a0801060e071d030a05010e0f060c03010b090111030708090a0806061003110405030a0f 69
    0x10340760020007141c1c0c034041030862184400c082405800810310340c0192012900b074403084240807500045541d030a10384092081130f40701c0341402c102c680380e2030f142c84c41e000500c0b10b0101a0072003103038080383d40b0100d41c018020044030b002154060425912030601d6100c2180c034610302c0c844e49003d03a00c2c03450000610300c00d0b8010340788910b03003601030000000e807040500d9410b8041c5e4000c810801000b00100c0c4800a6144070301401031030a0354400445c2030491040c454007164130790007594560704242082c00f117401404c03c51a8005403e00c4d04d4800c480000c84041111011290810303010301900103400c090100640002120892020440b12940e50301340c0044e5480e201100c555201000c14001449004920700007012017880514043c4481c041c1d00710940d0469000f401c04440280001501440d941000301241009003e18805040140340150115801640c420086ea04155460304038065140b110701c103907800b524000d03044a461668a14047c0320150f1084401e1342c400207180d010914142001c4a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155055971 1250 155054721 155054723
    0x108010e1e060102010e0105090102030402040b12030703121b020d021c081501140406080a05010f0605090d0204060803070302010e010b031f0c120504050610170a170706110d06050a03 80
    0x41000032030008a000d015049000e44441c3c119500c0b1129008848400d005080c05803244100050b901c1c101071040004441040301b00d01d009510015850790001004026203070f0440d05402d00c03680350320794500103100804214240500c0104009071204c1555400248101c4400e010f4086a541541c1070b50445040c4101d6109034000a0304107001881171003480e03091a030427100605020900c404960300300c03082c5800c15000540002c040c642007001d000c03060b010b140d0040c50074050005065090100050507071044080160040c064490054110b440d540c0c0046d00030400001034945038501031070000c0c060034810346018030a42c01c0c507400300d1061a010070409040e8055070440501e64003808444005040d44d0030b00c800c18810304820031341c0c500d0554000c0c180b01c0c52095020304944d2404003410800c14045400030b4078141e80c0800402d00e2190009124010203402110007110490041302c400c416104500d00140507c0c00c100e152a8180d801c0c0c000382130b0000c02403c00344815a1250284104520342c0d200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155057221 1250 155055971 155055991
    0x2010b0d0201180b040b0a09150c0803090a0507080c031005060901050918010f0902090a11091e0d0602030f07080c040902030603011d0c0a09061a0c0a060e0105060108010e 75
    0x8003000158050103100031a403100c180c011840319a5424140f41c00c0d001740c1c0c415418940300207105010507a000c1c036030b50080c0c503298402011800c00214000c0c40d03010306050051802e5000400300e9002d88040002521680d032040464855036261003441c0d8840780c510038024081d200b0f5820300960480c6078080d0034030845c4007400d449120780ca01820400c2100014012a203002c8000d451086410300030300840108003a100b43c0414100818070612961060040c20015410301d00145a5200303541c000c111030f40c60404031050320548a40d90003076400d205000000d03917803000c1a0403008040048a4020303502c201c001004400c400e698800007a9903005d4200d0700044114001c01060207040707980d601854018030040e00000d2142c1c0140c25110810000f12562a07141d440400c11100c50f1401480e0100502826142072116500c0d1803d494804042001d2808170030101040000040104000c403007a8203400242c180305c403519000c5075a009080555005002520400c00400c00994110741c850207200145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155058471 1250 155057221 155057239
    0x51204062d06050901080606010e010c05150402100e010c12020c130f0509060f04030f1403041a0a02090a0306020f07020a090c031b080708040201050c030c1b03150f0601051306050c010c02010b 84
    0x8d401111880d900890180c103126074854203001046040091013020088100c034190241800d00400058103c8500d0b244100b2411140020942c0d070304c442c440034070325806a401e04031a00c0c401e00507801e026420420079040303150010246141d42140d08800c841c001220b42c00c000c0761f201c0b003c0c8a51545c02c121940490302e50010003190000e445080c00c42c3d0410700910b00000c44141102c60411541c1c4240c505941c2401a528159052160b010142c0c0d04181c60315002c600d4108a400440c03d80d81007403002420042d804a281e02e1554048800c60344482e41c01407542c611075895001d210300130681510800300082c0750200c803554007000f090b81c460942e101512201510340e2190803c6507140030041c012410000103010700e031800f00e4204060841400c46c080500118400788041000303030b00b208503000d4400d5004201c0c03807408540c50446190048050311441c6107542c6c0d14030040e5414841d0340c24404030310350481c5000400560241c05000401032120003804002c2407400c0490907203e0410f59076a20090603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155059721 1250 155058471 155058481
    0x906020a080c010906020c1f1503140c040e280c05061e030702010204080f0607080103150902030a06050402010f0e03031c090b0907050312030106051204062d060509010806 75
    0x640282181c0202e500c0081620445580c1d84c80507038006859800c696400b402455640c0c0043e2814906000050f5904002420002451501140140c440640f05030007081001e410520b0510508440b07000c054400c0c0040c110400e4019520036081c05c2c107034401508410f00510003014044625652134200c9001940300c1e0130001003100d20b5200001808a50f0032818402d40d803a070600b4084c5124401c0c81d00016101d0f0300d040b80c158140000b06003c18403580240b8104010142c00100007415a81c000417052980310900c1c2d08000289032000d4080e5142c40340480c607408011403508034521491003a030301c41c910000003a00660302d007000050007030b9054106002850400d00c001d01600420328002d440170441c075696844602054009a50b103886a411000d4140f0040c2010025058900900000145903614192006125010b01155a0340d85401304020405101d5140c010f43e0413640440f1004103071340580e04002220090400018484909001000440e4641202954100c6803440017030100390341e0f2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155060971 1250 155059721 155059733
    0x30d0f0503060f040902040504060e010c09050d06090512030a0203160518090c0f13051203070b0609040311030a031505011407060203071e0f0e0d0f1401061d0114010906020a 76
    0x650307041c1c0f940003540e80c054a0050b0b900c5014550082c3c2c015600064844031144940c0d0030345110001c40424000c1188080107a92200550124019000400010510550b03d45035081c080084800c510b00d890100c180000e40c1d0503640111f000310b00041d6182d0f91403101100a07105805114100c00000343c807070b02c0038155130600240880e480802030141d06e10b0582c0039020111f03d9080700140c03a515006001c401d00841c2007003400420000c60800c010745c00e1038030b155513199040b08003c03c0f0600450400010808041c005c070520f80321258054296034561200f02d00041c02865031044d98451030a21850001c1d00794001c4040c0b20008007090390491030b00310f441d01c420029520143c2040704001c111415041444d80b15802c020a41c00da079603c0700800c1040040c01004880d0390340e0802d01c07880350302c0c0c00800020025018418295440906d01480402c803a010074014401c1f0340c0a0b003170304514041c1c1e0343c1c80c2c408298001d42c181e0701410348250351251080c0044402c5d24960040b100540d1041c0108808590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155062221 1250 155060971 155060989
    0x4050d030504111c0c050607081b0304050d120905221503061104060206010b090a05040c17090703030912080306090c040305010c0c060b1005040b09040e0703030e030d0f050306 77
    0x1001c1c0103669543d00907400420007032215000242d0070010403840610402c021510b22400030b20040798103605101e5592506400362088110184d40c0e80c0f03100f030005109001c14000e85000700030090a41c04041003600701038074400c050902c0300e40041c4040d00d02150350325010203503030208452450121502120881c098006000e000d400e1804000600300020003d20740d030151074200d040c13010030641c5440c41c0c424060b282c03440680281c12213030020b0014a541c0c0d106c0b00d0100003142c50856010030340c0c480244080d620360500e41003050030168600100040c4440000318141140e2296a0341d211030b99443e2102d601c21441a00e0040c00d401040001c0f81161400780b600613006441030240d0341c941680d03a030b140d60031980d14102100c0400c0003143c005041c041d0b00d00c20301100c2441520340358601081306d40300900a201c0c0d0b00030003202c594041b0711020580c42c1e40c0d01c0014900e0303148044030750440e282e0030080c00e25081c4800c0c0038868441c03420501c07a001e100341c289000d0f290040d2142425500c40d0f10400040503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155063471 1250 155062221 155062223
    0xd091503090204090c030302030c060c0c0d3203071d0a030204050910090b06090a0b01080a1e0203090c09100305120702040e1c0f0c020a051504080703060507030605010804050d030504 80
    0x5031100c62884c0494043c600403801944039030000d542d14010706545900b8801c0c000c01b807215205003400484403561010654a5014a56107040c4071f82d20a020703094040003140310085079070302c174445011301080f403039201c002c40c01260075840b070222055406089518509443ca40f050b0070130506c0c070b0108010b05041d000300b9003044100c0700b81c03801052580e6860080b81c01022007a604071001e04144400d80c200141000d8018000c40e500780034400c501400680a4100079150031100e0b95104564480c0301c041e05100000314020407400e40d40d908002d00f40c1c0b40e0303461034505018402c1c0304400c0403580d41d561000e00310040b41d6000028000c1051900c680034815001854141e0704203131540345890b0118000d2002e2a1784022000351a0070607a0104801021080c40101e003505210b55441e4040240c2d031001580c070b003110821980e1504025651055020600172a8009a03040c41141030101c20040380342c204601c54919580c0030080c040c0e454004507262a0f0583c0c002d451900022001c0171654426004a41d00c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155064721 1250 155063471 155063479
    0x6030201020106080c06180127050405070519080702031e030a0f090f060b01200f15011a03060411070b01031a0121030e190801050907240c02030d0804050d0915030902 73
    0x42c09c10013480c441106010a002e0030003442030420b00c881c0c50a882403a40145080c62b0a501701000200301c80800750300d00032071505100e00710300000d4045208008541c00500d9004041c0702071800c080151209030800c2d609a8011070421205600d800c50911581e01c010b0342100036890447d0803501ca20300202a001405410481d10030044088081c555034020039100b8004020300c8442404902d003810440b02c01c000505a80c2980b004004141d0001850042512042c12159981e04c603180024000c140040038002c00000105000c418410280c500504a0303001d007401003456110311340e40001d076440900914141c6484c032415100303008000c1c14a034109078031905003200040300020002e6401000c294040801004c048000d100340c580030b018490f04000c0c028000c0c080740d03040040720f0381002d078009a4020301d14540260761035440d200340080307a100d50b009800d4420191422500401e0304070100d60a82c1c403072103940204010f80f840b50350a441112480c0856080b00c800180c401c602500450300141c1c4e01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155065971 1250 155064721 155064737
    0x11010203070504031203061d0103021002120d15030506010803030105030616120b040905060c1801020a050c0f06190507030905030a030e09060a030203101401060801031208040602190306030201020106080c061801 92
    0x350031505a050740034182000108c1c003940c51841007080703a684c2510100304540242001c40303810829841907946008441d100459100301c0091034003103c6a0320340c00a0020300c105c0c0c000080482001c001076041e00c9040e4140c4000d42d0f036101d40d6a0390009160901000600480003206407032a43c1da100040340c960052005c140c0d0001c5449551420300f041e0303030700500a000000d100251001040d01404024001c0c009404076500e103881d12502c4140c4884850300400714100c646015035108000c071400348203403038410010000e01060080c2150041030b021004580080c4003c2102d01e4001030700c04105515035900031a07100036800b40040f00c3d001903c3d0540050134140003000503a02405284e02611002000066140c021502e400c0b0003841a80500d0a000040c00184040b400040d00c00041125605000c4c800351107629005009201b210b9200e400c1d41c070a0280100c0c0168107402950480c2d000340e00901c0f40a407610b05543d141c2e0150011203a018400f0490801610000d000d44600d0410505040312 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155067221 1250 155065971 155065979
    0x9030b0c070516050f0a05090402040203060d080c010507090911030613020c010603080304020f0906090127061706070810140303040b040f0e090a08071b0b0408030a1101020307050403120306 83
    0xb28018650720807015464042405100c40d00304400c001420040c125108401b8910708404500041c4000e04064003072a00000062032030340300d100056001c10361000b100c69690342548095402010240c607201c0006203580e60008883d0141d01500503401c0c03a500d40103107141c940e40704000488140100380036000f502030290b100c1200003841090001c0d80100c0c0c8d150390740d103480d01c10001d4582d000c2c4070961040100000340209070320f07254000c9041d01c1c01c40340070624460f01150380000f403039000744100091504000b0b011600607000d40e031081021100408842c06521a1401a601c01d402210141f0304012404410010081c04410944400788084d00f60b078500703030301e403a0040d03666800f5401154555458100420002d5849490598003146403c041c0c40c29000c19a610180c0744690a8041e00003409a14905100c2c1c1e00c640744000100745880c0959696503455030a10b889400000b03c01000c0f030000c07140c04000132418000c036441020982e61341071a10741180e40d04046800c80d010111308155540f1004a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155068471 1250 155067221 155067223
    0x3240114121513020409050a020f0a081f1205010c0f0807051c0615020d08090307020d06180308060307060e0f04050c301521030918041b0609030b0c0705 67
    0x14600f40c12040f000f581e5607040c4081e1406036040a060307000c50718410080c40101d07201c683d080d01c172180483d01d001403003030b00c80500c000f25800005900d6041001d15803000240030003000030702e50110f84180c009100e0841c4041c002c6d1111080d680d040d0700410304040004a1140c403440080840014148142c8010b4804102e4441112816041028142c90b050014503500c0e80400c074a006c0390000d03150907900b9152910f00c0d0b503202c0c010100024040c01c64079181c4c0c42000f9458208100c280102c20160754585c0c030b18100149010402e41701103009001d48803003c542c080c401c0d2003400d02d200c405001c60b25518600300910005040041402440d103100f80140d01802c01201410801c510a04074400b05440310004803004980303010300b40500d108040048031866440e208489038020050540d0701000c50340700081e180c15841400d280740c0c0d100e0742c4040324100c0c40341e0b0b1415850144d030190740502c10500b507080c00007992185500801c03010030601c190400c0040c8415084e19401164004900d080c2003981d540c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155069721 1250 155068471 155068489
    0xf0c060218190311061309020706050403111501120f02030d0c03030c0509090a0e0f01020d090c17120706110309011a04021303110f06032401141215 65
    0x74040804091009401a2030302c9070326007040c10180c0180b824864990303500c130114149003100c050f019090119001c07444611782c004000050600c03400640d030740c415929200300104070885003240810030104038440c1038440024120406003039111502d240364204461600e01c10400d2008031602c00e618040000182c40601a0601400701c61b19403440308083c40c54081c040e81c852440007000c001c800d02007501140d071100407407504240040790000c3c00009080c4c00380e040c03403403c2400d2891036000084800b0400c2c0c1550010720001d0042201480181e2030701e1203070003283e1064a00604540c4000082d5082031702d608001c0041a01c60000042c41240c002113034002a00211489201650340e408890810210b0500071050500122404c51030180000c1d242000c03000c6500001d019401d40082c00e03496915141c0c503090041d10000c000b02d0322450140101d5014004c2c130600c0e0707016018030810302e03c1caa50050000c0c14a100031101c2040c204441990b002d245940c0080080c0e19241107141c405e0b000d901d50400ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155070971 1250 155069721 155069737
    0xb15030a380c0702010c0605010f090b0411031803160305031816090c02160f061218080304020d1209050406170d03110c030a05040609090b0307060f0c0602 68
    0xc0c00c0d50907414001c05400100d21040c00004104901c210000d2035400c26000340e90110b2480000d0b600e80d401400100c400782c0c46944007c2185150800104042c2099802c0c0c1d0708840d4044801e0103466481410721041d01c81c489001c0311841d20900124654814140860298580390400c407030400c0464440c003030404040001c140c01080c400806c1c8200d00302c0c40781002c0e440c41000001000920031107110565841014490707540c20303079980d508d02601148288044000c4852040e04e46c0b42d5035413984115481495503110300008542c000744525402a100d02660700134589140005c441c2803c252180c1c11507a1000300100d1784064003414000004140030b158a403030020707594891110600b0300c02808100c80441d00800b842c442c241c1583d01c184040060459040e441d0745c9008140307408583e0070544240a019050881404041a0048200da118014000711010341c3c3c1d801001a5880301132004840d030800300c0f180c00d42c0042c402442440d0080445000c0101c452606500f4070350141c8a800c12a08407140e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155072221 1250 155070971 155070983
    0xb0f06012102070b0105090f0c03090a02040504110901060f050a0e010903021305100603200d060806011205010f0908090d110402040b0c060c09130c0e100e040f020a0c0b15030a 77
    0x10b00c810134008075000544c0502015117030345c6c905003000a1132150f05440240204031942e400000505184070602c41500d4056014000b4000d80c1000c2c60603240c81043c644030140120481c6000003a41481418010911655900c550b446c240c8004404c0342c1c21070215080a05200c84100000016111006800d54030051901e00003001d04140190401002143e8840000c1500f45016078000c00406e00030940280206400c913603980c1d15800245001c0e02090b0700c070488902070b4500028440ca081d0140180141c03050000308044c3d40300081e06401c445840b400a045540e0600003440c3e1801c10400c2014a903008003d11200d000030480000c00303030ba0050300920840b41c2c01189034080b00c802000059085844030781190b0070308500002061541c07000c05030646001d6201c400440945000d017000d08924a00905204c1200c40e0031900509005d00420180b80541e10701043e41071250710038420358121419a60383c102701801140c0311030119500c00341800c00d410751043e03031a5000e56010419003942030700c112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155073471 1250 155072221 155072227
    0x3121508030c0f03040b0f0904061d04120c030c0b041b151704110d110d030504030201110606130b01030209030114070f0c08040504020c012c070501030204030b0f06012102 75
    0x50b4424201002c028003a0b500342d0051200384000444581610814089200801d4035440e60704000f03000f500f00c0341e00c0b85ca800b2860708040350141412103401da1099010b150420500410058200da500300d000d06c0290018603106c114000190000c80c038903400ca401803404a0042d40910000aa0314082da4041204a0790801501c07441e04d8200c6180ca000485150701c0a4841c5000c1d2a410120f040d442d01d00ca2240890f03840380c20800100344600454000d01505041036986145000f4116502901040e0f000ca20b9a030801080c901c0c00103800c62050002610707561248a541b138140015100c0860752606164091004044030f480910442000d401180c0190480b410001d60281c80c031030504400d4010030810401000c003064065003110112002907070300595903064501c503980100302c0400c9980f03c118604040d240150500f11b441000fa56100c0c3c251422aa9038030015802c030b119500c0024030300f6074a800069041805004981c0c1d00070010b040c18520100344d403001850f4a64200e440b08a1241c0c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155074721 1250 155073471 155073487
    0xa0903060f1d072c040f0c0b0403061a030604050c06092407060b010c0c0608040c0302040e06150301090302300f03090c010309051b060c0703050609011b09030312150803 74
    0x5003090140200c0700300e201243c0d02003120b400801500c010406800024091004010400c5503103811004214801c230700342d00c480d10f070b180510242204a09240d52009260428007052401080007400b55901c007000380030b42c440000a02215410402c0c01c0d45d4450340f448074404030411191120f00300e84040d08005551002686800c02c01c880401009604111985330b4903400101c602d00c00909982c12810302c540d136640e5928002d07402142c503410080d04141800340c071201101c000508a070051494055200c000c405c11021f1500300c0305441c90180059000510049003507604c0e0308a102244401501c00da14102032030b035590010b0b403050707404282d01c207400010408652401e01144149001c240ba0500200e041516400e6554129041540700c80f14201c042c04011307503c40c021030382c6c441c40d44001e0b6403400c0c0d502d0400544500040314112501d50034550300302e40c1503941003581c0454a294ad02c8805180e419501c084401100340042c072000142c5d01d1100740c0d481c0740300c0c0b001c02c0010a0002c005590315020f03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155075971 1250 155074721 155074739
    0xf03040b090601122d030507120302091302160803070f03110406080a020a111906110705120c0f01021303020f010305010605190e04020708070201140a0903060f1d07 72
    0x10040100049420110040c000550440c144d82d840703940101d5032050f5800f91141ca4080050340a05041e05180030428460405400002610005008030000c83e81d891140c60305505034401d220b001540004441804540130354a41e01500700110550300d00c0c8102012695004201c0c0d0041c1c500202103908110044402645405240503002c80b00c01e42c14203240c5071910180c00175101a040070504d1b5008180294006d01c01c1e0b03420a44180745008641c801101919038001804c869441581c40c241890704004040850704111040f007a80b2000034840180e000210240d1500075030840c01803800792404000c501c4030240081c205034501c4c410b254a4180c618810000c1907003a403490a41490f08207001040099040400c0e40c266070320002424002c600041310888189140066146d0300901c040742c25814018600040e10b046071007030302c4164005024442081b81c07400b5052011002414610b81840012441c1e000b044000c0204500803404655604010b0061005690032310507030340c8010010041e141c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155077221 1250 155075971 155075993
    0x709090b010b0f0708210f180109020a0b0c07090603051b0d0b2205010e0709060b070b070507030509120616110c09100b03010909030e0405091e030405060f0304 70
    0x120038000285803064403600f8104038050501c029110450115141d403c26211003824248095501244000c07031030034500a00e801801543ea080081a00c280700032200032051007460340040d0000c051452607031030804005500e621001030303c401360050590004282c595801060051442030015007a01e1040122204903140440742c07003482840d1b5403800801003410000c246070031200141c0401c0600100c0b413008040c0b4210104000c11642c61b1a818a820020200e80c50060724901c0e001840143e03601c084002a5000326103010f485280701e0f00116940c5030240d001440c0d0300f8400c6c10494100400070001500e250300800c98403281e42c1006003000008080e050307400e0040c11081c100582d040100702d50303080d80c0b01425068503008070f04440110706400d541f803100c2c4000b4240c1003d9559250f844195031406420741ca40100d01050500b0381c0c1c000c042c500f0b800791a2044050708001c0440d101a52131984640121008440c00340c00708000201c0d03c2d0f22514000e203425101540306a0b52800e080c40d000403c14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155078471 1250 155077221 155077229
    0x20708120909040f02061c060509100605040b09010c0614040c0b0f07030e0f0a030c080f03030c16020a05040609150801090201080402120f01050114090a0b0907050a050c0709090b01 79
    0x100c04011044199482ca41e400b50403541155105079903559600c00310b000c606c0360b911050360a212240c103d4003691090b404c15410750b081a1180c20b5240c0b100c40030040c2d190f00d10f02849007c10b01c07d0200307106a050b4500a07100300c4d00c051406c100003404030740341c0301d003201c200550218072800840108406d002490360780c81e00174801c0891651814512007004910360188480041c10080a181501200d503960380c5400120700c4000c0c0f881c08299541d26005050640c2c0340f20380d500a01401c11000d2004070301006980c4038140d102011841c00490034606060588003102c120380c025808100030455480d80d00c0b078400a080340700b00014880940050041c0801d6061340410143d030704240c081c00050364000049a0429030544507084140c5d0840500c1c1e0610608043c000030b9903207032800000d02003203891651032408105690460480e00c480b5100c02c00d41d00501360003500300e120030001ca031400e807041c0020415500c16240803410701550302c602a0520b1140c2e800f5208140d250000003050004401e1142c1c014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155079721 1250 155078471 155078503
    0xb0a030b16080606091e04050f070f05090108070806030a060c080117070503030901031e020309011e050601020d081003050610050312070c1206020c150406060915030f061506020708 79
    0x83ca8100e0010310310b8801ca002c0d50303004110040d1507040303d442c0c0b40481d0003180300013042444985821510300902d00c1c3d084500000091401710700c0d0041c54000c41c100d43c02c001042c0d503081d01c1d42d0b486010595940801411082d01442941007000125645124000d001c04c859a41c0450551401044d038144040c81d0241d00741c560002c010810a030ba90000844010035801c4c2408103142e081d203c0100700500e10880c0a900050001040200c60788040d8403200703104595090310750440c100c2d0340f05641103074001c607400b40c0540d0000007058107180c0110714495018820982045000b9265611a418100c082c5c4244c5a04680d0320418400743c50240007261000f481d242d446810700c0c02640781c0c103400203a04d1050141080156802e1130600c8101c0d0125081084000e085035848546a0081c0300403140c00c039020b40c0d00b586400300c0411034072250301a030800803a030a150002c0c11411610350078030011000b0300446907169a5180070b909984417410b0100280517070b40260000d00d1a00c02e0f030f81e00701114484040c4c82 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155080971 1250 155079721 155079737
    0x4050601030b0610021b0303040f060306090f0915110c03040303021c03090305030118060302060a0224090c090c070606060c1401140a0213091802130612080c010b0a030b16 75
    0x4402c0c5c1c002520f0702c50201030440e01003c1d8602d8000320303042d8400d5401c0017071044080440030402640627003010302120807800702004441a4183d00b00d045450003400180038002c880c0714603101c48017a4001e11000b8119002c0203183c402011b2140749142e2140d80201c2c0036800618142041402c0841090880d070342c1410280028042550000c0c124441401900c0765800007450301c1d8107903901541300b0300180d50302510b0156a180045400303980d8001030358007120250066083e0040400b603109845000d0951440103160b086008010820040e1009085621850041c080341d80410441d00542d4010420fa40382c01c040310600e0704268207840c68141203e840c0c1d1f0b06190300480f41400c1c240e80d60741c0c0300d0215180103031500d0003503800d8484c0080325807000003000d00344118504410b2542264070071580c401c0343c00e030110100c000000300a4071041e1103000404021500d0a6012030204401440029103420001640b0740c1c5403000222000c40d240c100341c030100a04c204010100b0055400d24142d240d182c2080e4038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155082221 1250 155080971 155080999
    0x6090c030d110c06030a0509011803020d0f0e040207061409010c230c0f100f0e0a1e0b01090506010f030b03120f12010b0a030605010512010504050c1204050601030b06 73
    0x20392007051903000c508100d0049044012000e040c0f00c25640c1c0c0d034004000e595681002c02c0782101418040e61002c10551814039a943c46018000b000a803040d41074002d400c1222600009031604401210180d00f40100b01000e50380d1665644010700250b480740c04c000550f840d01e061190050703400241040d2060b03142410302d2030b105411100348401e241d0841958208021212040b4020380208007103030140c0c2c0b00d4428003269000000c0740040499031415410000c00d0300c03c81c07103441524141d0301007401039040781c4107400102e104250110145400c0c070f8040034048006a0314507040b14826031000410590310380900c0501e41c1c4c000c0010080c1249482d0520824071400c0020762942c400300e180a090b10400102d10940100060a941944202c40091742040d03940301b540c4151b40d0700850100d40040d14100c00464558003c40c1030f140c03000011240440240e00300b4040c4801810080c040700b592540501002d0100000d89140c14452480713040070300025491460009443c07100038085511407007032001e03111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155083471 1250 155082221 155082223
    0x201050c0f030f070c0f0b0f130b06060a050702100c0c0b03010602060a1d0109110907030e07030602070302072315040506160c0b04080607091e03020607050106050402030a06050306090c03 82
    0x3e411501d800200c10481d1600c0e80b040c0d8401c1103640c8001c24110340070781c60304203105c0303d00f1083e071044d281d07041d0500030f03603668800d010f03418103602c80c2c002e00b9040c1c0080800c1190030031801038070781414141403551404905400013030203040d04a034140c000850440141c8100072403440e4070401031454140f240c3c11541040e070043d40365400182141070380f6070b903108031462500c030061001c503a9040b010002c00c00300c0414200300550910100c803240c042c12450f0081290544644900c610030100301e0048c002041c20340d59000082e510410050f0114400d07030f80003140c00c4404111038001c02e510300b0040b01c42110144180010101d68810581c03001106010402180d11000210f9040c00e5403240e0b51546400c1c00d00d080300c5e00ca00540c10040e60481e000c00d002c509941d00050440c0641c0345c50701c420440d20340d10288924140080e0001c0360504007d0305d03003000182888400780c44010301c84c40000c66034036140c074049012a04202e030414003c64031920100300d41d007010b1040c240c00c509084060f04580305028040703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155084721 1250 155083471 155083477
    0x110102040f090b13020d0603030815090408070804030c0e1e0c09060d0603050d0e010207121205031e0403030f0c0201050c040b0307120f060302040b0d02130e19120201050c0f 76
    0x2c0040d054850b01c0e1079000381c0e11000d400c401021030310700440d11403905600d6200200010300003180443c1040010402011503421030340c02c02c01000f88102400d03692660740007919041583e04840d103a9051001000250003280300c54050f10409840308004d16041030221102034695442051860110040c0400380b001c0808403008000103030303102c0303586022188111008100307a0340b0250040c043c05810030f0002d64041c02100c600c160980c2103c0c02e0a07158484801d0120142c1002030080c18070103c040b49881c010000703140c2c4203041541441c1035003601024590114000c84048001943d2441d540480c03030814420104418480e1008004614015103140c2d45841a805000c3c85880040300003464984079940c01c26100b001603405100c900003c02141002c0d10785400100e00c601e0401d140700700704d81040065603c120703030000c140b030300062000c0b48003000420941c108002c81e4003c0000e00070305a9540410344100382c1c0b08203100c2d250048a120000c1c00c6503005804028060707810030034295604424002d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155085971 1250 155084721 155084729
    0x30709050111030c150103020108060603130f03030b090f010806090c0109051201021c02030a06142206080a03110114010323070e09030307020c0105130905150619110102040f 76
    0x3200c0580802c1c00c1c1214038601074000804502d01c1078003024025401ea5645c0c1c54100ca00c01c1e04c542c0d415071169000c101e0b039404115610744940c50420016000300d180144540a00c0d402801c0c0091080054004100c031800f00303d4002c2140224100100328541c801c00029610440d088040c01150b508500001d05180e601c0c031845e441002c5903607000081c40402e5040b01d42039008525444c8000c5408a441c002a410480320084034624000c00062a0710a4000c95000c1d00310041c541d0341303000101407180010340001402c1d0201c444c0e60348800b1450040800c0b8268416019443c0d200d40303c400440060700792500e2030320034800807101c0801040001d407546a145101203865980404034120354000501d002c1480d44201c400341c840c00c050000178280880218010b1160381d080c1e0f0400c81c00d440054949203d0f8032085007416600341401c0060032015880f0580003031044e07a00d2554036100c100001c202e604000e181000c45404d5901400c0c055401101030242c0c2107101000798141450890003c40511403449 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155087221 1250 155085971 155085977
    0x1103061006120f060806011401090b0901030513151505190303050f0f04061d030105040c091805010c0f0f02072402160b04090605040e0712080714150a020307090501 72
    0xc0c1501115266041100003c0381a0b008016a640d41c000c5155914003e200b00d40d200750880e03054100f20b5215503252410340b0480203225140c0742031040110000c0800410020641041011600000342c00481052007094098008520310462000340e440344140b55100e10311848501418080a001d075807075201c210b9405052058545040103c00d04951062600d1030040400000e03010031800e400090740200540203881c900603001a400a1500f2a00d00380d5016000c460702c21810403d10805402410200c04021202d06800b0340f41e554050a4440010011000c28a920f084451283c2e01804803204440a840200611450145040b0403040c403450154040c40c80c1310a00b4006500800038400741803603a04400b0b4400c0c0d5541064412a08640150048541080300001702490580920700c144034012014203685840c1a6503070101802c84542103415950503c1600049000d030321602852841510140c0a040c0400821968928004004090701da2040c0103005405501c01007902c00e42d44282 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155088471 1250 155087221 155087237
    0x30705151207051b0f0717120d020304051501031205030a0b0603070210060b040f0b090f0d051c03110703110c060a0e030c0f010c060c03140901091103061006 69
    0x40022003080c407406942016403001502440342c8140c0c40320080c031540700300c100b060b02d0b4580740c1c20519032110380b040340b00c296544c000c100a1220340d00d9103441c0b0200100041c200c50700c5c00b44010b10300d00182c1021960005040e4040204000c1c014140040c0b0130718040d41d07212224a60540d640d415115503122011420040044009506601e5640c000045450010300301d940301d250407003000f9601c10b90f007031921000508140300013403800c00117426101034415902803c14458100042210341e034114406184c5d12694a1851783d0498803046200c209103401503000e0003461448040b002c8650f40741d0040704041500d00071503120942451415101071560620307040008400b1066401c2c40c0c11113044810b540002c00254464090340c0001e12104070b045e069003560480c040d51010040314045e210340090110b8a910325800029510750701910710a1440d08000031541d01c5004040602d1104039030600b00d507952403c0b0030083c071540702e41051854208030014401480c10010409214245104a4040c001c6031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155089721 1250 155088471 155088499
    0xb09120d0206041e080706090c080607020c01050f0427050c040605040b0304060b030d0e01020601050613060f021c0305070e0f0f0402090301091203060302180c03071d19170c030705 79
    0x262441005800040c001d80346e101d1810314800504080c0022507081030200d400003280d940105040d0300c9000c15401810300301c0305480054900354080ca11051a40310b0800c4082840f041c2054020002c002d546441c0c0000001002d052048520140408444d000180000c01480b40d214080b00c080d00d2800f07505540700d0300d880c6010005000102d0407a5818041c0145421842d9401300d0035001a4030300b6401c0b83c0b0266a107401303025441c898500ca02d40c1041d41544103014050140c521482c03110118411190410045122203182d80c1d800851000026215404d1003500c550001c03d07100401d0045944201000004c4001406e6902c8041024061500403d25500035174080d807041d019540c010340020459110114000c0051070b00c1c0c00202d104000300030600c000b031600d421910784201000441c2900c0e5446020098039107000701c1903070300300c44022202c41d400e031a212801102d804610084296010f5401d00900540e1141602c3ca2881d1640c020800c00e1500d81e00000c640c0d04a034400d60313031a1004945 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155090971 1250 155089721 155089763
    0x3040c08011509020702130504080c0111030903030a0207260301030b090c010c170405040e030a0f0c0c062d110c0d05060112030e061303110604140111070f0b09120d020604 75
    0xa0200c400c1f8100d140c101084280300d106002441c0c002c5401703008004100c0f1500c0c100220740001c1e5104029a881403001883c114030f00c2e4018200759000e2500000310b030442d01208041c81c81c030a8200c1c421840044010010066241102d030340244594014100000c031081c0004c0088280c5800900303d6554161400c8076550040100c801811001d407050083c0300c0c07080c80c01a52540644440d000044004030451007032807050141c3d1081c0fa030300c60340390320380c280c40c0c0744081318460002d11020480e0641c1818006800ca0054518000c1500369158051a0002c1d01f0741c3c5030500700008105401030044043c10303070000c2d9011500e9030542c0c1d07955000c00344000d420b08040701c0600207000c034240c100342c000841e18101103000c2d0030882164441c0d200c118402c804181030008900a82c801c02e03013000d54101c0d02d4140c0b5030041480c00281e2142008807900c1d9640c030707651500801c41e15071001c0d0204100041c010400d0a06080c10100c2d0060100205202034040c0c00083d5540c03002400070303009100f0200711014182d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155092221 1250 155090971 155090989
    0x50a030c1401061403060f0403080f0a0b09040506070e01050a050f0d0905030408030301030c09092112060906081903080601080703060b030c030106081e130c03021503040c08011509020702 82
    0x1070600810070716403918a24081031541400407880381c403071080000c1960b0803034109075104640c580c1c0d5150040d107404a0f4070501c0d1401428400d08039031603454051031500c98100440c800e5000b85e000300b40504042c8000b03860a070b034600000d810807804101106078550000115000b00d58441c0342160344104281c1a20300425180f44000d0840c0000100080c8402c0c0c004003440c184c0c0c0c09080e01c81c655942d00e4042200b00e800183c8010300b210000c140d40c0c0c011390103000c030703a084018060411117480b110f170056290442e005500101001541c809050000711001c00211543e280843d18207803440d40103403801303004c1510060405040101c0382001501861007034114070010060203252541760b042c11468501701d0b404c24010702e03001030725820014480a0080088850698403840304210035141d000e985a1500c2c16100e06990f5101034510000040e01c031b003852504429440034055440b070a25281c0308100d06003650125896030f040c464050848041e0364400c008840003158016a16240c03840801c590710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155093471 1250 155092221 155092253
    0x110414090c10110f010c0207060906120b0d0b0109200306060d0b01020709230a230a0209090108071703030f150d05100603060b03030703050318010e0f10050a09050a030c 74
    0x1300400c3c1400400c81815081000216a1502501d082c2e5480d000c0c1250260a43e21450000a81c40172841400844c2d40e400300c0b92608014200270408a102e0301d8946c80e01c00700707900010409984002c140c102d81d08012100c010030003081102403842c02d10742e00260a0380501c00103c0c100c0d980d9850001482d038000c010040040c007000c002070100c0106c0c5180c524105e2486400300d4007001c0000b0001d207440e0201d10a03c2c142d41c4c0780300c5a651039205448180180d1a8008200e10388069007003150000c207030342f21243c0034020410200140112410802200440910707200880e90542c424018003c4c4034540b0580d032580704a0814401c50300d0243d45e00021300b5000502c80262481c0558170410399040e0b041e03000201620300500e800e0001e200210305059a0303200700ca401400041090020030150601c51890306a407402c060004680c009010403441d0400614004d004c035aa404400c0780380000c1c0030f0f401504c6e031000f40184108054456038480c4d035110034003100004c0401150035401407c1160840e8040710213 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155094721 1250 155093471 155093473
    0x3080304151407021b0603010815071209080c011a0a18090206041203080c0307050f090307050603010e15060405010806010e0102070806100e0f0606041208040e04110414090c1011 78
    0x82c0c100a07001945a21680b00c1708410459a141c4c1ca01c1c0758104242102e040740c41d840020031132200c004400701118000580207104110341c1540000d0b10b01303094001d80340e0040c003a4200c10b6941ca0309100b4a800c4607420030300c0f090034409100d18a2620b607141c3c10700c0d004440303008003401044140c641c0608018030f84020000d62005000c24040b500c405103280403030344103220351035021464651086803000f40c0404c6841000051081180314520703101a40500304424000d000c86004980340c000098694009820040407400681d041001030713420300c02100d0781c0c03a00030384000d407400741000002000301d0001400c51341030003420105109640d00c00c211240081c065081611000e050010903450803800c04e1050840a6000d000480c1000c04e003102454041c013002460300b4545490b000c001c003403490011105039440388051000090180c418a4080c0c8103038410002c542d42c0e01000c0301048100d80a0381d140c00c0081007100c042101001d80011208216070084a09169014214600320303081d0026041c92485 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155095971 1250 155094721 155094761
    0xc100c0c080703140f0307080f0c04061103070f03021f06030201050702040b06120106030605100e0a05010e010c050102040b04061106090706050903010e030d0213051206070c0309090e071a040308030415 88
    0x1017240c4000c0594010200340e0340f00000c607114600c201800350710588205d50141c0c800c1000b0841d050040c1040f40714441ea50054a0501410f0340350745451084000c0180e01607008a0018580c4c94600c1e00042c40342c2d404000c0421140d42103030002030960058850090090360f0ba5021001d1590300c00040e1548640181480c0e50150307141c0c070004010301220700c070301801598100f8071074042600440c3e09a080c800301911401903079207018011240440c032a01554103100c0d0321a541c41c0860001c0c0020000390030010780c1d10303907103514101c0000c2800c5104184031405410800c24031400d0403011440c4402c444103480d100303481f01d50707a070000781c0100091030100751188000250001c9a20181c1c0140c109400300d901d186244903683c00510a0f07a208445140b20150804c2340040c2501d0b020703101d6100c0d490b000b40b0b0100041610350502004450302c0c003500c1400d0781d10104080000c49140c91071074141e42c0700188618101459540c50f041705002c0500001d001c030100748803141420145502844c0801030406007248 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155097221 1250 155095971 155095987
    0x10915030f060e0712020d02040c030212130203060c03010e150a08030a02070302090c0c0703200a06081009021603030905150c07050c0d02130902011809020c100c0c08070314 76
    0x10090620070391140d03c5014550303001502d803401c0544078825580141010007908103d608100c0100003061400c1c4c117055082c0682c5e082d52901400d00303807003404486d48802511a95004151030014014410005014100018400340f103482e5116034001c40c00e642d0045030b20301c20070b000544c00620381c0c10035115403002144046985900040d0003085a00965221200c1d8031581d00007402d80c4500b40441c070301c682c0150001c000066242c0d18200d4401c211064a1400303d201100156580425503c8400080c00e04414421200522404d0000400e00b001c411880c0440003400c48507003a10310b0002500745903692040009004092187e0b0f400540b07820340c071508910341540c80041e2a0050517040e100e034810b1004490340e600b13100207046405600201584440c1000041c1070f030107414208422410006a0b100c18105890030219007400342148550258031060300c12003403480e000381181e04400c1d203800d12041c4076405401906007142e4607013200e99681d4a20180c20151412b403802007000380f00c1040020418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155098471 1250 155097221 155097233
    0x203311b0501030e15040f0609121d030c0a140109030611041a0705030d020c010e0106030302061e0c09010f180305010207030f210e0a17030103050708030a0206010915030f 75
    0x22060350003d8800308103880500039407903520303110075110720801d8202c40c0c0494007041e042141c40d0026880780b0b0011403181c03c10303900c0104c05003140400101003440c02c8414109040350a1014010000a60003042c04660180008040d041640720310304c00c442d1043c2c90300509074841d4030344d034010b1900290140070400c200200c0c413100398480d01c2840000c281d1040340c650303400d1542c022106010341140003141030005280c2e0b0305000f0350001650008940d0b0b5510f043c0310f910340070301410009501980103088140307020340010954000d1841003400c0070741d001d010080c10b2203840083d694445070a203011804090b0400045d600000d0040c4a0580c654420317100004000c01500140f06041c42541c2d9013090981030007013900e0340e10260407040c0346041c0f004d06448003008560302402504560104403940d12106132622400c0181c5c05044041d4140004014000c1c0701d0304001100003445210019440c00e411000300945812040c099002c035a502c1d018020006204d0844200246070040c0c00c10300500240d140003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155099721 1250 155098471 155098523
    0x1e0509032503020a05030d170a020d09060501030204050c0a0503040803070903050a08041508010819020a15030501140109230102120f180111100b03010908070503040810020331 77
    0x301d20540c4c0c0100302103054140030805003043d01e6541c40c1c28101101c1d01030394212410000305043c21969082c08601c010700800d00a46004a00440c0006603650450040c081a54001016880300c13041c2044034000b007962201c00c90394401d82042100e40c890b03c445900300d508a0583d40050914480c41000c001405294002003045602d005282450f1501c0100e0503990310009102781220f0f5000840320010030340d0f1550750082080d20003860700600d00e8840d00c1d40780601071103c5502000136034450040c000b680d05c100d0f1101188500342840d080c218074142030a00707004203035414691250320740c19801411b80d008028040700d440ae0008010340707a040762409610f058010400910002c000814108036550140d031000b4440d005407805001c1781c54210344060003502400403d95090366035502d142d00400d6019002e010308510a101640e070741c625240e60240703004104594000b4081c810800c3c002000301004190351001e402c0865001e0034500303210350000d500030020000c1c00e03c0c0c074039294a4031010046401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 155100971 1250 155099721 155099723
    0x509010e0a05151902010b0f0d02131b02010b030102072409021c0b0a140a0903051b010605030d1d040c0302090315101202031e160303050306040605011e0509032503 72
    0x880e503c03010401074105d00b03a5610001f4607410402450010480c0d003030519441020a0000d0103042d5002d88a0f04103008a46036085011000194095070a94242c0e080c01040c03a1024210000d50804100e0303161086103410140720343c6200f2040c0030144e1a103000c00d407c01075000d9002010203141c00d01031460148200c40c004c101300e07000440300e000031340510302c14801c2d44010103850f1000745099441c00c5114004015000064050200c103018065100d00f034402c00e066a100b10a0020824914100c141032802c201103115034144411007010300c01088910140300c2181c41d0032100414034103824a01600240300ba003a90b580c00d4011442c0c450309140d41d07a030000d0301849100c9001250745903111071948103d401d00c1d40081d850341182c02352542041406c01502d80d514051400d444001b01d121036504100360541d40104c001c0340c1d001c0100700080c58544500d10003030500703007000050001d081007107d41c0e031041c900d10fa0b010b204010918810f44d0300c0c00c000c008040760a041656078050f0029400b0401c0041500c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 155102221 1250 155100971 155100997
    0x4080301051503090703080a0c0204050c0c060f0f070e1302030406090b0105030109050307060c1704061b0804080a12020405040e070905011703030f0915011d160509010e0a0515 77
    0x1445610b925140301100e110300300d10300250001c00d0560f03840389103507846204140100003d40e0028400344c0d583e40718803070161201142c1e0964540401c1d8415042c810001c210b401140392440802c035072843c60908603903118035907103480c0f0300c64000c010004407400100316842c242c8a1001c401c010401c21a640040c03a0740703002d440010001c2c1e036600100750a0b00c08942d001413140e08103015020000b203050300040c800d08100e08103c14601c40400100748001c50450f015500c4984442c3c007018401c0180c440680550041d15000d49140380544444c8080d2003000129800c210582d044290b140d00c0c0365059134041c0c03030f0040041c000d001881494a40c0d074026805000c0000d8034100000861150710440c0d100580420b41c00f45003155100c030b120070090103004012190318020209c0142c18200c005159074041c007110b408260884803403150745100014000c185105600b1200444008a0707080000e039040c8a8003460f0280044007040d0110710b00b0041c552280da048071000c0800624101004040c1c2007030380f0206 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 155103471 1250 155102221 155102239
    0x1709030d0e0d1409100c08070b2715010303080a0e01060f08011103070c24051003050105061002030f0c0703080c07180207080d0c020f0708160f08100b0312030408030105 74
    0x1654002c054070a4000c0194014550071034405d50501400b280c1040d540110b40b058104080743d00c0302c0101d40001c40b04120413420a2520b451700e24100c000007200e803041c80d1b00030581c0c0180c0d0300303450f240c1c0340041c04050180000c508c006403042e60300790484800d0203e42030017400320965549400c0e03468550340c010f500081d401c0003401228101603600b941d100303c20a41ea00980c10038151601c1801e04080283c4003044041c045030402c441c13290b800344a018421115014036080e2550620a08550000e0f01c001c2c031412848821031481c1e9800000d4504004c1a01100e0703035a051840e100f5481c5c19a15480100005004550003c00c01e1021a0340030072502028031140c0003440c0903604808034443c040307005000c46414040c40d44905c80d01e511841c0082024011030301c90b0080b001c80c0c2890004a98086500c603400205400d232a2620074030404000e00d11a10601c5070349040c50f08080e01d0f120700c2120210400c1c2d40300f5500003e0f0f90104800200003000101c00b5a036800e05081144a0798000d0203501d014404c4030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 155104721 1250 155103471 155103497
    0x603060d050a052a100f530402010f0c0f0804030c050303190503040f080c0a111206040b09070f03061b05070305030402010e010e0a0603050a1401061709030d0e0d 71
    0x1085070b041c000100401c0400c0c03a0100285c1a9101744440c07000f001080081d14400e94180c98a0b003c00d400060a003c940000c2044a20b5002c4464410104109545c01c0940356070141c00704458a583c1080e424200a0b55208013200c049440e002102030103001102c401c4442000d2049034002441074a0107001503400103915072007459940e100d0030400340d0181c400850340c4034a0600c01d002a540040c440c032010303510705405444109140d0000c00c620b0390f5a4008841c502c04001c01e00700f508100a1054070803109003000380e005181c90380e400400141103c42c001c03002a800040504c00c040150407461500e620103512420580001c240c1c00b0007140d050000158291101e9010702c5c2640c0b0713030300c0c0d25966680c5955220350045840421a0030b40f64140b00110105108599a00007000c01604040e07130001103d107010817914081d40d0801441c02545903601c0d00501003079900c90540740c035211076440700000039100c1c641620714500c62041041c2550b071a04036041440309011864641d50840e40d030302e981346c1d4084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 155105971 1250 155104721 155104783
    0x3030e0717070306090510020307180603051b1606020c16060203040b0f0c010902060c0d020c040902030304050616020d0b19060f06030f2306090a050601020c0603060d050a05 76
    0x1c1d038004084203034000701c0e0030800181c0c40e4005440f064426800c1d40c0107124842c1c0010705a800c2074030100007040c1401d0030110041e00e06120000108600e1504ac842410401940c03860440004402d5001d0b042c0050443c0d0340e4000742d4418a0380b02d9115404641d5480c0c10100b43c2d403281c072010388034a1a090300c2000044c1d03051001003601c0030f0320615a00e032480c101c3d1012065030741d0b92088101a1082d5215001c050160f0346410140040e443e081001d0080d502c00c481e0001d00340899442d82d640300314500380c10003025880001c00c1d1410369405940482e607803081d45e0440b204081c800b1100a5104000070130600030880c080f511107000345145a00e42d07542208600e65901502c42c1402080c100c0d0159600400c01c15119410400c40f45480c81c0000520030300c03510b48403010182c041308000318040c00c01e05100130740c1004240d00341c0c0f06241010030030050600d600000c2d02c5528a80400b842140d011011582c00d941d04260f5080351a8002e040b9200321603249051070302c03440c0740420394001c808032507007013030101c0d50b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 155107221 1250 155105971 155105999
    0x507030c17030a0e060901030e0604060c0e0108012313020c1501050402070b15190b0a02060108030403050a060c050d090c0801051303140c24090706091503050c0d02040303030e07 78
    0x8096250301311032071109402d200b41600401d5000b8101604d5081042d180941404980c1c01a4010710740403507046c2404101410440391620f01b1810489400c0c010003030a9003611054a440c10f036100441ea0601455000800303800003400c807d0002d510008840d522035030300041c680300039440b2800080740c0b40c0c4e80c2c804200c00c0b070184407805001c9081400c00034084210f40c516540007580c00402c508084041901c5080d010f1304950003413048000001307020700c81c1507010024103005040110007140f50600f19a912900c030058000024031064603001055601030141c1d050f20380300e90050741d08000541260902d4080120b10380b154807a40c1d4038113000709451452503818036420542589540c6400040c00c4044d642d03503801204074070003602500d901d00002010074090602c40c0c0f103050740e000f042818101c0240c0e0400b201d9034452030611807038100c100300d00305804054101819181c200086d05950701481c1d08074920a24031030000b0f6510005011082642650200310380004810884101c00c0d101c08210394110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 155108471 1250 155107221 155107237
    0x4061407080d0f0e10060e010e040f03030b03011d0a0b01090509211213050d090e06090402180703140f0105180a1b0807030e0127020307030507030c1703 67
    0x400204401d2110802035003103011607055002c07001a20034000c00311582000c140040417621152a01420440c802d043c4117514003502244e48039064504107640c50003100c1120340f400409243c0c44040c0300081c4c1ea400c0d84101d6100e400603c085201800e0b5042c81c03a210300b40c000301102c00c1e20014001140329503051043c6449085403000a290929030351040454805004003d1030400b0000c219251201d422502d00b580500190701201500c070103545010342c10900300c10549010400030400c100f042d01c0e028002c1d9a0029002da51940050312103001003401400300803110000302001030b061040155242d407140420b0102a1035061081d00c441c803605001e00c10070b03c10039030300c25906484030810509245480303410910203080000c0e42001000c105008040c1040d6000114a103a0208015190180181ca982c040100020010701c1c0350814000d4001c0c1d010311140e0400580a505802151810042e0030301851f004001c032050a540c0b494200c85d59a1a4040c2c1000140011040c603441100007058507a05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 155109721 1250 155108471 155108483
    0x2011b0f050904020f0c0c120a02060d110d0603050606030714060d020310082b02010504030f0807090905090a02010905010206090303010b281107050f0603180c1504061407 75
    0x190031003104840c103400084249901c00e0782009250410701c07005008041d0303010444040d141d1110313540200424514a2622210290440580300c3c00513070b5600104c50055046c01000540858000100f00d0315000d454100004c00c5c0c60140080700344030b00080e4403442241e045088600d00790311104801c80075a1a050b47c07580009040c49516040003040c1c014680c001c04902d01400300c5603540100a251862400400c203800056481541581c60a580b0340101c02002d03000078070840c1025500240740300303000e82940c410450004041409503100740b03400e0300102841b00c020701c002d04000440540321021100104e020401d284000141540040303540c41c8902180c802450a682c40c101e000712451703201c0300250705d03c0d210500c081e0403035846800d914120000d85564151000b00d40403565441e0400d03980006101d600c418a00009a981ea413044a40c40300d0000c5040049551800a4a1a11060503503007030b800080201c00c42c8039100b031800a041160000c1d614a0b8207803c201c50040214811600c0180003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 155110971 1250 155109721 155109737
    0x1050403081e1602040f05011401080603032a150405120708161a060306060d0f0804050312030406051b040303031e051305061e1906051005030702011b 66
    0x104903114094440880380a400402e98104690b41c050598412021140942c100c0801c3c0c40560500c0d1242100d042c031518010000d55041543c080c8010000f004014100040313034000600781d031418000d4941d8450301014041340c558040d03618495218502903032240501c50303101400e241165014806005a4000c40a03118206540c40001d829620441701640c0c140707002c00c00d079005482c005580350f43c068020b090300c1c40c0c80b40e241203e43c07d812002410f0940701351b100000f8000984d030b821085021441d80b200d440741e80940c10b4a01303401c1034020f81c0d0009500d070040f1012003030011003410045100ba80b04580811503030380e0390078220b400c41e503903401c012030500428801880001d02070383c054443c0c0300c03441c0e0010b240700c03031984041c205035101110305142c0b502010720f50004110040000365000b0944000c04d4010501d031201610a01c11f000701911190900c05c0e4944134035680380c0c0d00a601400024180085c0c2d00e001400260542d40195507600c015031810f1f0354200d40c01444d51034600880c0741c903130712294 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 155112221 1250 155110971 155110973
    0x902150703110309090f18031306080702010c0203030604020a090902040905010302180103051e0f06090106080717210708030a05040308130c0303031505060301030f0327030602070812040506041103030901050403 92
    0x682009207c50b09a98070b503a00d81f000040200060200220065200e8204606010740146028070141440302075a040c0601d04800540100c2071705d80c010380a5a0040c2c8a11800070100c07007603c525408800030b54400100810702c0c5940303400c07841c10703203000340e4440c880442e050030b140c060070100b448064a55002a80138041c1c083d070070752030440c0215240080b01c03010b0510410150608405542c000c0e002d0795100c604000f103020034031810006040d08035809190051840c00203850f11f151454048132a08020711a5040700d41410a448400717401003003081c0c491406800303e000070001501c00b903010502ea00c6c0008e000d0300c1c4d202801514264080b111080c550324690b03080c1c004d002000c1c80c1e6209501d0800c0c01040546030407024500960040c05000650031207030070701502080700a801c058001d94a402408600c014901002040347d5000100603a550943d044c030360400d004000340b0440c00b48000301032205000000500b240100d004603422132a03c101807080503664401d441020380843c1060100300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 155113471 1250 155112221 155112241
    0x30f0a0203220b011d0c03043e030c030a03090902090d0f08071a01050609010f0e040c0e090f130f0515070302130605091008220317070302040b0d090303090215070311030909 76
    0x2a1400004d144100072000d09e010f4288559059240c0420780c00459100344c0080c070f010888241c0d54071095002d001010100c3d20010309403c20783c09000360030b07a0000380c0c01c0500d444a030301408425030041c001c40200b100c6450002901d80c0304a00940300781c1d8040281030a88171080790442c1c12640020300403840c14580100650f0094840342d40f070f0080c4030850701d240010780ca46000342202010150f90354003042c2c0d80700c0104104100050148040300c1011010401d1203110407080208540c0c114032950b408228518041c0d00c0c081e070f11444002c03c0c561040502ca409034141d006440e54078581e15090200c140c650108498901540305007950007a010450900124050000030360020040300520010190b80d840c1054420611a01200040e00308000f0250340200805403940100700c51509500d00740c038010500c4800d015101000307030003a0740e401e01c02c1d003058001c0d8445e54000e90302a02c0541c00880000c1d4547c625004440182d010501801d80841032450101c221a0b102e100201940400e03181c8030044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 155114721 1250 155113471 155113493
    0x106050a05100e0a1e06030e0a02010e060f0c10021801032d0608010507050c060708040c1a120109020a030e030306060301090c090801090606090c05030f0a0203220b011d0c0304 77
    0x41350000416040810800c89a0b0304411726903010001c0c00c002e0500d0000d000341180ca40d00004001a080003203003600503a408003510820490443d00203460b03650004901d2514865440302107080e1049103003081002080740c000d01400c0300045840e40048000074015030540f2240101494480c5200c0c81440b4201c4034803d40d520362407402c00f000180c85803981200d80c2100c0051b85d29801144020403c490311010400403e0381c0150940384c1001d1a040c580e640d140d11010300e026261050144085a5a9003100002555051400c1843c50005940e690055000961020860704006410810b0724141d071b9800100f160b00810000e804140f4507860896844c00402900d0380380d0027000403056001460304004d00642440328022200060b10a281075500402c4a0b840ca100ca0140f08003401000700c04e0203128030090f44258104030150390391b40e407a880382c603800c03400224a00442e8450031804050000d5000e0281c142c0d4041440a02c000c911005d1030f40b4408070458a0310f24480c03042001400007041c0c1110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 155115971 1250 155114721 155114747
    0x15090c04030204020d020706061d070c0602070204090c050312181302040305060f06130501050f010f09080f0303010e0907050604060c1e050f25050409020a170f0106050a0510 76
    0xa680d040589075400101a40d020002c00e81d049600421200d003445401c0c841d00004106c01c4804000e5285010409691034000402903000c0c08001d42c0e491040c08440e40440381a0703640200104090903580c9025000e10341d040c02050701911440c21401050504c42c000c0311070340c0003141850711941c2d4201c0d00704403603065040c0080c001181c00707000c0080025001c1140c94064451f0480b40c2070240340c004140b245054609006061482c107000c01044a0780792040e42c00381110083c0b074207081080c01044250380010303056002030002c0c4075610b204404040040007031810390340501000d5000340c45d0405000e941d940180201c540c00002000104801801083c915140a02c650f81800c0c40b65483c402500c14038a6181056030310390031203051a0350701c00d028400c2c0100038294007080040321951352403405d41c00555001380e6004554a8800b00103545d038002d001d10003404560307000c488404211160a031200c40346100c02c1c50641c2400c0c004505441d107078400000f1760324040e01300c3c800100340f1102110300c0603050301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 155117221 1250 155115971 155115991
    0x6031b0d0c080d020a1109060901050409050a0c170f0a2a08060403090e09060708180a05100b0a0b07050a030f0302070507060f020d09150503041b0806070e091509 71
    0x1000140500c000c1c004500100f00c9600508001042400c01c0f13001c0301c0e498140f41d84244803620800480c0c0d0b603108181c5042d0b40341994009681e05517840c3c2545004054a00a4801c0c8100d004c0080c0789800041095005003c08040d21004030841e05102c1e90f8100c95240200461030424841100c05102c028049032000005001c070400ca0f941d0b026603007014401d0fa41940007c0c1c0d820000d20801e402c1040c21a0040e41c1e043c0140030514102c10018400a8040c0803550800300c02070004815000c100080c100c842d8114003030710403807c4003000749801804003000d054064001c101e4005001000e0a00b070b0341c815500b060241105000a9500b22108028800c8000a0681c240000c0020520401103200907000e26250942c4410548001a00d07202c10000c0b0345003040140c0c542400036210081c0103405100c150309007292692102d15000340031008920842c0300528015800050440001400c5802400191501c103402c0c014502844a6201c08070b801c0e03c400f0803da0700380381444c10411079050b0f03c502580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 155118471 1250 155117221 155117243
    0x120306010903241a03060c0901030204030827120d0305310506010b1e0703021203100e0c0a0e0906010e060406020c03061018200412050606031b0d 64
    0x43d590b1503c0801d00c980c00c596142e80c90340444110380c40c41c881c070300b41d40704100040c00c1081140b40000b50745074001030071040701150108240482c0d9000342c042c1c401035544609010f483d104101101e0035200c0c0d40003503407490003400c61102e0181e8180502070601958945001d025204803d4109802030440500a41c800407001024030001c4100344007141e419100c43d00e079160301300040f420080d10300b02060f0040381d1090020450b201e0403c2115116407c0054014001034999020742403d9040c012150b143c020038401c00800c00c01d880b070b8206001426a41c00b904010450b0701c440781034100b58051b442550000c51000d8a81140038600414001e5200005241c40c01c24002d0600106241da0403652201c1d01692214003200345500e020b0081540c01040c903ca00c86a183c58081203030302c2461100f200c0c0b4a1156102443d0b02d01e85581c0c0020007800300d9540038a551180d03100b40e040c0c444801e140c0700362803500481b4049810340c5004503500c04018030380c5111803440c0c0c450908200300d002c88150304542c090319030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 155119721 1250 155118471 155118473
    0xa0b0402150403140708010c0203121005030105250c02010509130e010e0a05071205030304120201020408190210030608070b0a170a091a01030b011a0d141503060108120306010903 78
    0x4500200041c51144da11a50301001c5a18803500d040401c0c0c00c007082d50b9040c0004001d06a07800020b640b01144803800402281d200c1c0c141030585410990400d54041d400c110400000d11003400406d82c1d408180e403903000d00d1003a040404c40d03002c81203840007800100200480000c601d050307003e580d154002000c002690341c150b078181c4c07421034048252541d41c0740c000e810541c1c140801442040c5c01840b41d60450200ca004070790b540c507203174840104003c209150702ca461201480c0f00b58142e4014014240c21507410903841003425442d034034000d00803403084807800d441854040c030a0041d481143d01800051040904004010b41c42e500b005584030304205e0420b0b000c0340c81d00612012207004500380d07880069203143e581803e00d5508000008090001042801000040c0401c00e41c00d04403495414031408140851546140d140b164916040303203141401c004103a0155000c03841e82c007502007040301281060300a402c0c540c840c0340c24802d51550b50070840301800800440401983d0182c2d05140c01c0d0041512 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 155120971 1250 155119721 155119759
    0x30204090204020d2f07120c0f050d0c110d030f1101090209010b030105041b090302101e020c0108071404090207030c080a050403060f05090a020112060f060e04060909050a0b0402 78
    0x70f50096803c0301084d0156008041021780036400000309030000c15458000e036a00e8056030482c02054003002c000c0280105010f1200c1000c0104c11294400b0a84100049000c80102816441c00082d104a079a1101461031441c000707030070000b80380d031503101e20100515688050300e100051000b88007140d502c0c0c2c176203e0b00581d0742c4404180a800002c444640700c7d410007080c4406c581d040c61500c0c80c050b1150b861014090740140b104c00840341d049424208102c42e681d011a400b0000c0d041502044884c03814100c2103607000704000c600c0100a0743c40400c3c42d91080340407a001d5000c1fa0810032081403c01090044001c1c0c1e070020000c00d4000d040940302d555082d40c0741c1c1c905602c444800300009a020800b401040307010f01074403405211110080c42141403104640f03855101d6844004d050004002d095012000e070340e0803000081c00d1520610407403039511a00901010b00c0d45150502c00d5145c4140818211060321a1403800c035009130040201020680d14010403620240060303a100e40403000c11541200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 155122221 1250 155120971 155120981
    0xc030e1207080d111605060d0c02150a020a02010e0d050f0c0f0a0b01030b0c070206030106030c1202180a08030f0909090f0715031d100c1b0b04050601140a030204090204020d 76
    0x41036515001d2100311114205e00b80101d480400074a108440c100300f10300d5940c402a00d8580181c40000641c01c152074005074909484480004d0400742d0381d8013000030750b00d420b50245c104941290003e100e11039200b20070b251103160341614580400d409001d1172908000780c00280c8101040001180c13403994203401164601300400308100c5820b0290801402080380d012030040d004101c40300103232304100c21a40000c04d5800140a04030070941d940308200e45c020303c968518400c11080803401c6540302e1070380c0700d0010526140051705005000c052000510ba20001003103488101c100200142480c0c9820f04002030070002a00355590351040c403024044000c2e0501c14003006180880130003102d5094240c02409507440440000203c0c0c0181150002c0c03450003044600b5640c000d00b0000030440003642c2c094482c0071030390340c0001413015120005800c0000042a40e4000c0c0e0160045a509a9850b1014a280c4440b0041290442255801007006007004e8002011980c4000c0016040010785140c0f202150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 155123471 1250 155122221 155122243
    0x305010302132019020d0c0f080304020118080d09061409041d0609010f0e03090306010605030a1409030309011107120c1401151401030b0109031103030408030a18060c030e120708 78
    0x94148112100a50100b21070300c4d42d080d0b1340c1006c1c40040c0486d00c13450342c1e40b610018040c00c0004004008bc0c11688924003901744d144206001c446020f454450550360380c518400302001180c820400890390b180203840654a15203a03031040391800000300140000f810105c280021400300700e6060290f00542400803370310800c683c00c000038540045540c141c080c2d8807d8160b0203d550010420000c083e00c011a0f002d06682e140c0c10019520f0301c40444444c000c200c621906100350045105202000d40017100031406011040001d01c1a000c0720000d07088940f140e808010051408440544001030240020390181809070440c0c6401041080707440d400d4408849007604030082a00f0b040c09541003500c1c0307604840302c080c601080140c141c04006400b215440c0000740a030481c0b4118401d02ea0340801c212000b801055054030745401a81202a01c1014074210324031400800c64000301d00c45d4850414602030a4240e52062140c100310000d10801603e00c00403e1994002c081010480703490800c01d9038950 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 155124721 1250 155123471 155123497
    0x30201020a02120415030e0c030a080d15120308091c030c0f030213050402031009020a0909050a0b0d08090109030b0c04030b0109050106080106120b0901060908010c03050103021320 79
    0x100560740e002030a1a070f54012030442c0c040c0600062003043c00300c10094a074002c00c1d0400007940480451300c03d1520700c8900031103a061149400900130050f0030700c0503000300c40d114030303050040520651282041c01030030b00030318034803a000c0c00407400801d10880400da0401c0c07010f0183e40203007090301904c2c2d00c22060101000080b13a110408d030102581e05c1194250a001c4502c0c00314200f01c0b20043c0618001102e228807442560080003103124084503d031440000c9ca0900811540d49004003009440040c0074450000380b1888c20000581c520050300810b65000e90040803c60014429958840d05070842c0050b40d04106d0501404400a400864141c0c0908155040c0d244c0302e5145180c51091044140c002c0c8d8075090030000100021170300000b18905440960920025101d0b900000c000107000fa1a03207940c2c070a808100004116400c40c0142080d103801a00134091281403000507802d640b42848005c3d08a810f040f240c80207100d0940c4002002c8150000214103040c0200440d6142d80000010604c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 155125971 1250 155124721 155124727
    0x812010e04030e0f010e0d02010e100206060108010b1207030507030e12043b06060705100518031306080a060e04061b02160e0a0219090501020d0504050a031403070b0403020102 77
    0x245078100560301e048100c103c0c4c1c1000303080407210000300070720030141c042c1c1d005904e10b640600c00c6a00030720900c1d00c1c020026204030001174240a009503240b00c10b071442030200c4c0f9840004504130440c6400c40703800c6030215503a8000780d106d00300200c0040400500003010141c3d00c03485882c0c80c079000d2001140504020107010b0b1141c0c206144107801850711800f5105580704040821308051140c0e62800c1100d040c0303500d4490a995480100302244126200203000b0301032a01508c1200c00c242d48811300454013200c0b00c580384051030b00450b580e0712031102e4611440da1089401c009403031048100d198400d014000100b03080e9581c2000d4246010107030fa003118a45d03201c903004c0c010000e000071010003102c3d003440100b0140c0030b50704003000e5811482c0500b000150610002841c50452501201c00300020368600c403036000349440c0014051211401894018050b15580c400624032074401d44098490003002000e815146d5501e54a20f2003240c20410080e00007030103551f000c500300341000c92081c0d0003900003581d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 155127221 1250 155125971 155125973
    0x1b0b370804062702060702061603030c0f2c010306090f021e161124071502180402070501090501021b0106050618011211040b120603010902010c0f0812010e04 69
    0x2a142400001c148000c1492810500d43c41c00504003030003580c0503140c040e607400701800880c0c41c912890001c4001c00769511420b40c00c0544c5076210710000c0c3d14aa444510100c501d503001c42c0e1501c066058441326a01c4189000c2d44100402c00c281c041e03079014100014150758a01d1004113a449680100d2103840d8045558400500c1c405803240340260307450f1010303103808a2443c0d0b242810741c0c00100500b040400106244491303c421419960940301400403500300100340034079100703940c0001c03821944840700085000003d011402501c0c040d524004c1c95a05200e07010080c00000d400075002034070503640b1608200e011035028802001094000810000d8403a50304825500b51841070344400d000e0181004112407040200d141710031003440c24a0411040d8154514a80140c4404003000c1d1008000007800208842220000e0180710125405030500d07a5658041602326820080082c0c08170716284000303070000b140140712400c0707103219440c5541060b0707104840311704000c0c003600708420742c03203120041c1304c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 155128471 1250 155127221 155127233
    0x207030f030e0c15091f0219030507020307030c08150f070e0411040603051f06020a110f09010902090102100e07031b1701020405090108030a12020a020f0a050a1b0b370804 75
    0x702031b100b80c0003c40707a240d1b000030002d40d581c0107586e521078130300004a268001c1522850032111400e030010b04898405071a81040c0801c1990b0344980c0d1181e1094407042c2c1203200942c090244900c1c050320001c0d199070348961054844202c1079040030340c4a540d0310301c0d690303070030201c100503201804403560000303550315201903240c086541c0c0d4158a0040d01d10100100662940010072884c0d0b2a0300400c2110000c0508001c80c0c0540c2c0c08441065000e40e0710300002c114642947c1c0a0040c44800f42d08071040c0d100318050400446030003080505042d044100d041c00403408000074000c030070a481c181e196803280d64402200603c01c1540b94841030381d40000e0100f080e80703041003606000d040c0c64400b070742c541810b00030080e042020b14000402e500303802043d0081400e00a10400300000043d1040e11100b000318070307016403201c50600303080b5a211b00c00c1c2000b240c0e003000d080b241025a00760030340390352601c90349640188038040b030500d101c6030003135204980c40c0c50144000103031f00941d81d00341c03642c0c0d49a04040c9086 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 155129721 1250 155128471 155128489
    0x909040f0210050310090207080c030d092001090e18061e0a06050319020a12030e09090303010518040c03020a09090c051002120d06030f0f050c040207030f030e0c1509 73
    0x2d0040100500511082244801241c41111514140103a0f503c40602c0c05551900a080c00d6081500000c11164a8000150003124110344940500d00c1c001003010b1041180c032540001ca42e001403c3c621082c1311041c050b050032600140108102d80456041d04401403500c1011038041d074500504140003002d42d10341c0c071106600140c0c0c44400740070190601002c02ea4410425000c0100608003090410640d100c0e200800b0180c1512201c2c3c01c0c4008040c1409400c820307000340e100c0e0041d2054000102c0f049004000e580c140c0b0401403240c0c80c401440e298107000040c003d002511969034102c00000181d0b6990400d40c01040041c401080344c01081c2030000c00c4501c2036100500450034016400c029550101d0308000c1c0c194074001803502e52003280c03000700040c40c1c190001000600791010312403d004949400b40300940c8100120b40340e20071440244800e90082803c000c001c510f200302c4810800e8001c0c0c2103004c00c4001e02c1e040300c1e0380c031401c100010303000c5400844428804030000340030f002d42e042078000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 155130971 1250 155129721 155129749
    0x1413030c03031d0f0d14101a040603030f05070501020c0303150111070b09100306091109120102090108060603041121010b030a0c0b0a020703080a09093c020909040f02 73
    0xc2c4450340f5034600204003070070314070040644600c1c0b003214604104846a460541008404003c50710380481c1c4d505188002d0100e031400e080342c0c85e500301041030245402d016032402d41c1d82c1a81c456480e8440d01340180c40c1030b04811400c568a54007800030302c281c400700700080e5215010804540256848520001d4804550b03003200c1c0c0941c2d0400601132008107480000c46400e1701065804000141056100302e000304001c2c1c00c15441c0078107000904500866440261000705002c880814818155a11042c00c0780314090181d0701045031900010a1840c00c0030195502ca8007900d02511001c0004001500c04988012600314001904107445281035091048400301b0400340c00902a000941d2106d03401c0740100e1140401c0b0500018040301254070a0103004025540302400725143d10344c815001e044044c00d800381186461400c403507005052800056240c000c001d461108045590b518100030312101780d5000940ca00317800b00004403070b0741c546001c42846107000e04802c080038191441001000c90031945 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 155132221 1250 155130971 155131007
    0x3050403110d0f030e030102041a090a150c0f060b0904060f060b0f030412031107030801140114090f0105271c02100c0c0510020609070605040602030702011413030c0303 74
    0x4002d000142e0300c1d075030140610703094206401000d954100080c0644216000340525003910504100c1c2ca0068201400104008561a00005442c1c08084a1180c8542d0200e80080c441000d603601150103941c00c9590b4034010b00000c240c0e22502c4010500d500350a890031a40603541c0e52036402220310922805006d8821509410b01d49001c0c000e0030040c60102800c0544a0f41c2c0e0112440901030099100305181c11540078255110740c1681800350040c8401d110795081e040714031184900c158032035040c160800407500b07041e9082200740c0c0c0601005a82e291802418480c003000011441d00c05105810207425182032100c5582c4021014405d122250100010b80440c800b409440165580d40c8280640401450703d183c51a081c0c0c01c052a502806900164000030071144440d1440c2e0b012440c54441c0c5081d100301d41807d59515401c4499120300c2c440e5400603001400307150015071160019902182c141c480749418040898000005c45800b0b60003201c0503421030300c040041540124440c07000c100b50380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 155133471 1250 155132221 155132239
    0xd0219021c0e13020d060305030a080a0b06030a09060e07181406011b06270b070804020625050f031c050906040b07110d081801021c050403020f0a0305040311 69
    0x1d10042c21503510003004500c10800c1000c0240501c0450b07060381d07a8604c0d0342c2c9007846100d940342417003501d9511145017600099011400100e100510b03020f002034412001d8082481c5aa4442c444802440d1260080baa22601d0b040003180250003009528003804180c4448a01c480c80907402c0c0084030407102114132034449010410607aa0b801c841249039001904001800703190852070f004005004000700042c40c00b0782c403001400600c105804200099210382d6116585031600b04041d51148070032600258405410400c0a11144040e41d2203032401c03224184103180003030559603540c10a41010302050301a400860400440182d4100d1030070425010101007040b0b0501106554944500800203030204000c5400703c2d030708034070418801075000c80d02e5064132145005480014680c03181914001c2c000042e0201d00f680700081071080780d111b00410b0700c4d00c0c3c550741c072400f2006006d03100c014000d4066028409800030094404c0c05204041e0b8840c0d0f962039650350440c03600480f988003000082d40209514 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 155134721 1250 155133471 155133523
    0x1805060a2a0f0c0803010605120612060c0901021f0e1507140f070807110109140102150402030705030307030807080a090b0a0f020f04032108040b0f04080d021902 71
    0x140144000ca1600c0d40000d052403005035100210f0702d100402c41540040000761141d4000050060061203e030406069150300040101c14401503203111140e42120000c0707030103134045900030300d40d807001801621880c10002000c840e40c074042410500e042c584410b1200c4012205020790b05001c140e620015000e400e07d10b000810000310200b212a81c0c0400007541e0700c8210f540019104070940c08000903940c0c2146280240882200c0494a4042450700c4070201e400328004505030f04440d01a03004000e101040c8118081c5454003810998150213485008100c0d504d061008007101402920b405078035007130580d00248500d0740100a200d0b1540f074201c00740d000031829181c0c280c01074110040481c2c148407603d00d6000070321400d0b03440020100001400010846002640400354140c02604120b040c40080c094504290403a002040884a207001407600000c01500b5604907002d80d03107d038246045201800101d91181050014665130001d80c0d4000c10781c100250415114520b0013101c090500d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 155135971 1250 155134721 155134781
    0x90e060601140d02070813060c060e0607210f09030815030a030c06020306010e030712020103050f01050f06070f050a030815031f09020607020901030b01051221070203011805060a 78
    0x240c454910f508a4000414500f844010402d40f1b4070184010642600a80d4500d00030744007c070a1442106c200f814a001c01c8846c0c0404503070184200010740350a0310141c3c00050301408a0442c540030340d40e0b9075031105280a002c3d21445030703c3c4101c1c829100c00003a0b04100c0c004030180560310407800c3c40b03580000e03c218000307a0701061311081c00b81e0208025889440d2200141c0d10008280034140c4c06116200340080c440e0b441c88469000755000fa201042140c594840803070680409000d400d030049a094030f4156a418860028622140180300d51240da642541d500da08001d030507401070303001540d007800384800340c201c40b84909990341c4c08800903c00b08055948150074a14203841c00c144041d9aa11140255141c00080720030309a40200602c13015a12468048201071081c003c3c80c2c06034017100290421082c000819841c0c08000404607001c21400751400b02041e40509400ca0300b40d501c80443c459003980d41d40e54500d01c01d226a002d41900d142080c11042140e185204601111044034468000048 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 155137221 1250 155135971 155135977
    0x30f010f2301120b101805040605060a1b06020d0c0801050108040201080612070f0b0a02121206090a0906021908060f0d120513060504030c0509010b12060a0f090e06060114 75
    0x7007800c1003903580c8030000c40352000340151120301d500070a00403694516560b003e070f0341c9019003e9140d4548466500d941c20b1000300d030100c0c050160040e90401c20100011300a4507a1203030481e103070f0080d4403103810541d20007041c2c2e00a203131002d54003500d8204040000390040c50040c0900020301c0c00c10240c3c030701034000a0003580090542c0f801075681c0282c07081406401d200010180007014803049000c0e40c0d6030510300c200da00001e083c10042c010030341c041d0083d5004204030750005080d03440722011601d68004200f4504800b810390600260b4904079000000d9650015025541300c0d903000b0800c1c1c9100140142070607100826a6104803407814224026075240d0701481c07560354000f1006c95014440c11400e8a00e48190307102c0304103101036000005146a4040700520999200300c92101d6125079030341c107020008000b8050304800540038405a0040d51032443e1441e4000d0006100100d00e9956610030320320404e45400005445403160301c81c148090041003480c2c1c0045080c07801004140504032141e0b8070740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 155138471 1250 155137221 155137289
    0x100902011706060d0207150501060906020703030807052106010801050a080712020f04060e22200406170309040501080303150907090305060c070302150c030c070602040b030f010f 78
    0x114403072020032403036200c40b800d03103030200b03000a021540d50003a4108450004031301c609805146040c90004254103100e401d0940489100750001c0003014156038041c0c4420f04000d2221040142c24044e5001c60b10801080740342c42810401c80181c6401c0c040001403281d4416002640101c410f040d0811030303200001500402c88600c9298000c2c00203803480060594000000d080307070702c5810043c001c44d10701c03285200d035402072181c10082d81440070070450514024400010180200744e13900c403042034078034400214138a1131200800004d07020f03803036a0303400840360b098000b1b58820f640003290200440c1018481c040c003514180c0021400c61600c0c00f00360398005842d113041401a18680003003075629011703003d403901540c3c0c40b4050ba5134030314140442c411250400030096005100783c1e038a6454090000c007416000303060f048081480c540d82d07246007101d5603000940482d94039500304400210340c5441c00c00f55002d24000b0b29104184e5140c903001540241b225000070002e16001d105845a24501c030180506070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 155139721 1250 155138471 155138507
    0x309031103010c09140402040302092503110904050c120403030501080d0c0507120c0801110a031a1008130602031503010b0306012709020d050c04050a0e0a1b15020f10090201 76
    0x40030785e04007140c007034000c941c002034100c1d01000078414162580c100030172441d241d04520f282d40100b07811040302a588010001113191108004000440c1800c0d0007040d8003650390750001d45064400011084142812642034002030b5507800103021074441403254030240c1d81c0f540b800c6400d0300d107291249500c55410780b0962010491a0f890032042062032810f007402000710304000c1040085a0500d840581c0c051a80c10000a1400c03190b4140c0d0454900a000344030001783c0307000c030000808401a10940780180049080103241003100c030001e40c8600095100314001004031180180010a0509581d0b00d41d10b400d219070058030041c01000c1d02c1140b044154032a06800c03920b80d4100a40d140000c080541e0040d4000c0c40004200c0c050100c00111612001e400b0341301084642e44a1014000300da4842c1c21010454010400748404210305600f84c0c03034298201500c02080c035a460050091000d4502680d6000d6040039900301031901c030910100c24a82c448010500120140343e00081c04002c030078074104c1c20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 155140971 1250 155139721 155139749
    0x5060601021501090c1806020616050315041a030102280f1e050d050f070e06040f090e070f120302010501090209060a0c050a0506131b030b06010809011103040309031103010c09 77
    0x4010311506d10621420070500000282e03e440e684000e440d88011100004ac000ba6000c1005500d44904103ca1161903040400b40b0007480302e504100c09000c0780603c4104201d00d00050010343d640030310061030220a0180000d54500d40021070240800841c8101810312282002c051122500540c0c409507910b420401c281c501030340514140c945020b401d0030400014900010803a03800d0510315018029020303900c0b0480d90010743c0d4200300c05880350740141440888401c004022030179103034201e40700c045180026900c142d80c559105245005003136000c1c52a01491010f90414150288105405010001410341c40c080c01c41000c80c090707100c0c1c3c0c89210300b0403006107007410600000b80018a5501d40c440242c400070706041d5a010b062515072103098039a40400007038040c4c80c110b12143c0170100c0e64414002d0980f661031200649002c0402841002555210b441d16941c489044000f0b601c1540b1035258051914110f04100c01900c02c10004180243e143c0442e6030300e15134102500703404548820380c0580d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 155142221 1250 155140971 155140991
    0x210d11070302070e092e0e0106050a0621020c031210120201120e0d02010b1206060d080310080303070302032d0406200301090c02120406080c07020d1a040506060102150109 75
    0x314000e06042c0d43d103134110301e01080d04030b2446d100e00304500d040808a8240181c400301209036003220352511825501503646102003042c14060415902783c2c050a03d80c2590144040d8220300c142d03407181c3c8009a841d0000a900c4c920300c0904222190028103801641854a08150803280e550350b52103030103414021a0b400110700c410480c2c200c2c00c0720080000540d22080203103500a8041c2241200b154854001c40c9030345003d1410010b0124850760700140136038006c000c1c85d01e9500059001400c1d511003d95403450118480508000540c0100031b15a001640e0f45422048000c503400500c0e5214408e40303048a04a01100c21000810342041d00100001942c504140304103045116014110702d9240c4017100002e08124590b00402c10f130702c401d40a48400001c0c0d40d81d62100c9100d64010407001c1903803600450003030024034019014152014228256405003622400c54020040c8d001805018a503400c01041120903c5100e41101081c0010700c81d80d88004040c0c00403002c140900030ba0b095680c09250 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 155143471 1250 155142221 155142223
    0x20f0c01090c031101050a09140105120f01060e0904080d05070908190212070602070b07060b04090b0901060605091012090c08030304030201050105100c080309210d11070302070e09 79
    0x1420916420008019401c40c0b850406000006880305480b05032902c480d100a55004030100c680d00c02540d5690b46d06103040034a41580b0812194806040060621400d4a525010140c4c14091005490b90f0202589032910040c4107140c494440c40c051020761080c040000c880784280d5458030300c8a100030401f41c0c1e07100b00c1100d240e0380b15071200810b031150381e07100240743c0552200d0001c201c2c000e48400d071b80d035101030100507a1000c043c0b0448006a218280822030107141202810707c1510031103002c42d10114078000034003a034001000c10b0368036010304010300213180c1091060200803c41400c0072400c118090340052100101e4800201c10702004144800a4040c0d56100605881d40080c50f604403540711208260b0721b41045900700c1c055803030000040303194909a040714510b0445640d070000c240c841c030340c4c50b051240c00281102d070f29407044038102428101b040704000900071010b0b11050312a00c6100300342041e6019484003411aa44c03c00204c000310b07601141c0c040540304880300c48011030702e4040e029 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 155144721 1250 155143471 155143477
    0xf0303074103060d0b16030e191223040618030b0a0e190302060601020f0601031101050a110106094703030714010c091e060f030902060c070503071a0904020f 69
    0x106041d170394808021600c0c5502c000040d510f03906980c100315401d03100384001d43d42c408000901401809690704040010036404030f1440704003140c13405240c0d07524001102e2840c0c1c0d900c2481440718101c08102446003540c420010740c02403014a0442c0195855030b181c81c01d155002400540b03a4540303070101008501c50800000e10030284e02c3c0241c0080314410f040080d1a41c0d016165240107025154500408590014855061ba6080100f15502c14800b070700651f2b1680c07200881900303000060305080c0c920402807140500510900601180520410450700c5074524030f2880c0f8050005001541c00f800c000310310039154500c0c20a01d418013003020b107000081c0703503004002004110304203401c2c10458a44064020b101002030031303140c503082c403616802c170707118201076485007800c0381a409003041050340e218900011510f1964140000c6000264012400d541c0c0715010940d09584026420025420200054002081a04002a041001c0313404c0d09425215200440c1e21031a000f04000400700d664001f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 155145971 1250 155144721 155144723
    0x306190e0a05070806010e0606030712270c03023109020a0b0d1e0e0a0308070323010f08010b03030a0e030c04050103050a0c0b0a05070f050f0303074103060d 69
    0x326200315a44d566440e40d00d802c2401200c61040a41011640078105441980d010300b03030030b840b4074400d240b803403d4120052550800303d08100141c0b010050708120503003a00d108003030103042501c084a0850040c002c0d9411104401080b08200800072600b000300050408407010803444003148107401030001540301425500302c0480400d00042c03210402215510070054014840c2501d44800c8000070007104550141c03c10406907001070101030300080c030525184da4015400c0c00d00040c1d038100c2d0607000202d803a401504510b80d5030300301d00600c141e9485000000042c610100203016140d08800441d0300d90081c240403070280090010032601c183d400384075900b0340340d001902c10004e542c5e403410248d40d604130450094a00c6003841d0b01c0480c0151000e01203818091840e160203207403004a41d03070300d0304c81e0145580582c1d55001d150b0003d0022074092000714010f018035a211012441130b20304c035480100743d4650a025803001c510b1010115500311880d00322a441e85150386031241d540c1d1006c0b4a0350030203c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 155147221 1250 155145971 155145973
    0xc0112022109010c0c0b040602071410020c07050324091c09090c0e1c03020106080105161b0f12051c1506051206060318010204030606060e0306190e0a05 67
    0x1c0003001102640e41107500c10003a20000b403100304010b18013902c00780105040505007034034540c005004107210703400901009100300880c2c2d0100050012190a10410a010340c043c1c42e000505018886820008280034141c203c000c1d0142919001c111415041950b1084051148032000110259800d0001040c0340503100c1d04001e41198079003005100c521103004200960740340c40c1c8026841482990f0030110f528000c5c04102010030f070814449050038020b03404500f15900d480001c05d26482c02c1c00b0306401194000b044800580540f580645005d0700d02040811802c235668031000070981107401500c0780c87e00310b40c0c800010002000c0445640c441c0510718541ca1a000c8210407048869912500d104035102c07207202c10380c076200c54081310648a203a00c848844042c0101203091450403200940d0040303100e1a103503000b60f400503403050aa800c80d0707000359a00781d0385100c20800356070011b0000e51078982c100c028140520b80404030f042e41c0c003500d1340c102c40390369a141c01507604500100700748030038150404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 155148471 1250 155147221 155147257
    0x80d06060e04050a05070206041e1e11180604090204090b1003060b041a040c0521060108010509091908091504170a03020d050d06030204020a0c0b0601110c011202 71
    0x500094507a4080c4041140581c0c60032001441d101c032588100c902403c05903000d0b264075140d6450703000307090520405090032522a05480d0340007a00d034484940701c01e82030407102c03c191662410403840d611420049a4000c91407c84110400014401c0e550760154003124000341d044110b0010500a01c0007100080143c0b07100003d02c0501c0310482c0e2904c00700e80c4101000e1090900400602c010303503c0044412a01c00c13100b44281c85a4a09900405d0034220079241c4030381050582008060105090803101010b001400107004a03940d2060f4002d000d4038041d00d008440c2c0c105000d144d03540b40340703200c001d05808821076000c0301000f89110840d0b40711000102021180c20449040725256441031281e1100c0502003000106040e034003203200d4010a4058000d842107036101d00084ea2154803580c420a80e4507a951800320050b5030b107101a0643c44103c1d9641c0052610b9850007404150010b04a01c1c184071182030f4400e18100009040d941515081ca05005129501481e040181c05554002080701c01d80f1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 155149721 1250 155148471 155148479
    0x10050a020309010e011a010804060f150e010b0a050f0a020a060f020c060907050306010e0c04090c0e0306060d0b01090b03010e0303130309090e060a02070f0b01030302030d06052704080d06 82
    0x603006107004031820002003185600d04101c4908032a0a080c140c41e49003543d0f80300800b00c7d0302400c10960320501455000c14055904019601140c040d00010490391101c01d0042c046c595000c00036134050310f005c4142c54544001150054058000c00c4048900254002a0800c00340d10a02048001e96400300051042150884007140607402c030040c800d00780e106210014a40c0c010020b40d14080725005400b4108503404d100b00c146071000c00508800c2140c00822000501000b030307200300080f11040d981c9030f95100840204140c140030f40913100314400d102e4441c0d8440170075040c104150454004040010b080442c000c0881d01512044511410070300002c0b003000f10640c03160300000000d40c031950f1340744442c0740c03528001402c907288015103a0341c42c0e200d42c0008010344600c2c0c0c010041d2038000c910502408030035079a80b05003c9803d0b00101c0050700041040840014180a110058401203d204c9018007000702c140d44084031540c022907d03604540041020701c07440030111003821480c2c1b04140aa07e480d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 155150971 1250 155149721 155149741
    0x516080c150109200703180305030307090f060815061c0207050c0907020f03030103062703090609060e03060a110c030301090203060906060c1c0504080d09050a050a0509010909051005 80
    0x2440b440e415182010b02e08044c80c4148590030307400d8612102400d08120042d01c00302c3e4005c1551034640ca072000380c6400400442d00800140d0311504d035603520345841030300b080c6000c0c030400c1d420b074090130a0100b2007041c80080240a24090660030080d2042c0d03444080c040706020071880c4120381c22200718400980001889008113a40010010039251403986445110003280e407414100c1256030716070005d1005000280c10313900000c883c0c3c1204c6041001005040d10807044a000b40c0d9003c8012844481d400c02c0b03000d80026003140141450308100d54445085404640c40762402011115481d84e80d202c051416040782d42510034141c66001120344a6031111441c9000394003d90350640b15071802d8001444624015003110f41c001c1c140006444d0310580707a480e884103d006c1d96448400e21805002c00700c0c10400170481a80e19040c10f50714040900d00e001d0a0008001d03094022600441d1030741024000307072302e4000d540d03811180d2801c4000f40020031420224102901c0405054403542007100744889554 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 155152221 1250 155150971 155151013
    0x7030204050a080a0c0b0301121104020403080a08070f0e0d030806030a140a03080a150e1503010513021f020715020106080304151709100e070302030633010516080c 72
    0x403156200c01c1c1d55544640806c07016000034810030100080c102002c100040c00100e111052200240c000344c1420b40300d42d244403e903080201d0200004001c101000a01d6520501c4440310140e113081000c5458041c901240c50300507015409814400c1290100310551401c00c40841781d190000824029411100060f64440100f4002900000d10941c049121520540300e80150480e1840c1c99080c036524200e9030300309580c0010f207100c0c01c0d20080d030408035032902c007801407034403c1c22480072003241d0140910400483c44805400300b00c074114015640e001c0e040c0c00045400548640403e0b004105c40d000703200324007400d12a00f00841500010a000460f0540514000703000090760b20751200c04c88014080c1c0c141a04101d8180b14285d10032480380c40320310802d610802141c02400300b522000c5440c0c0d00802e00c2d08006545445484003411090180d000c140c0d6406200303408048080e500e081d201d100001c040c1e0069454000c44000810144c070100241a403c90b250030a00b04e05889881e203100d106006406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 155153471 1250 155152221 155152223
    0x30305030103140f071202030a0c090c02010609020f0405150d0903031a010c0b0403050f0702030f070614160201080c070b18010606090e010e0a09051b2707030507030204050a080a 78
    0x4400100c0f0190000c80858084a501441c4d00100301580c500320312400510071408060360940184822500030904022014024004523071000c2400802404002e007120016806403030001e20501c8444003c102000131101125022294403d104104229428491190096068106280c0f40c0f04400f0150141c000300001a90041c08800911282005454a02c8030400081410580e88001000a0701032005003034142d44140140781098210b60101c0d28220051112a03003581c82079104120080c0e00480d100420564400843c0c02c0a49407951380080c17030b815400083c14400b40350f0002e503040d2000310583d607040b604031303034648810705040c00094600030654080304455420315101144e030500800c1c0700300490b51490700710852a80f81c042c1d460703000388014045400720b07500e800090f0003103482003001052a0005441c04001141030718100600a00070f0764002500e480110b103c22529080440c0c0594060300380d02380401c040d0b40c1d828080b4001c1c070032a00803542c4455115004a1302c1403000074540303812 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 155154721 1250 155153471 155153483
    0xb06070b060f2e050c030a12060902090915010311070b0619080d03020f090a031208090706050403030c020315011203030e01110304030507030207050d060f0b040506030c190f030305030103 82
    0x84980042c414803011204410701080c40b00e034403d810140440b80c0101c0d200c059442c0040c1000302007501d25003503030300c08216440050302c4485010000c05540c400c010091480c0344046280c1081200490080781c802002e8020340610a074003101603034040c0d00306074100c00c004041c0c039030b40b40708a14103040c2c05032059400b540100a0030351020b6648204c14211026a40200c0090451243c01c040c04ca011358043c500341c107803140c0d05004a804c2d50b11410803c4019502c220400c0d48420901d490081c12200010810122039101140c01c04c520354000c1d086406a039007503e05001100d60341e00200c1d14180c0da001800030003d0110000040100f000100905010f210b650240000e280791100c090903144103400c4800b19000400c04100000d001e00010f01c03046100c0d00503600306658407800642040310703284080d21126141d0714283d80d030020b40d03c140b084105d4111703000c2015090a81c0030035139070405d2640450186000d03c00c2c0c0c0c80700c0c03202c01074204000c01c1988000065039860749801000354100b03100499030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 155155971 1250 155154721 155154739
    0x2040e01140d05031b19050304240503010605030c0c0607110d081006080910050130150f020409060b07050d0230250c060207050904080703030b06070b06 67
    0xc1e140c4000d0030b01c0303090b80003c0154200302c0d4056641c0c00d140c1030120841e415110b071030852186071810030306100d08a1300510103141c50b00d160021000c2040040c40c24184950f880390030007240180c1180075a07044d00c8852902589a81d907003071104000d4810303650b200b40144035000404c50348990046d05a40c032006180251231511002c46010344440c44103403002c0f801c4490200050110500c84d18880340c0c88078515040741c40c031604122640040b2070080e0800e200001d00d403410b00c0740451080501e0f4482d40c4c02c06000901031065034580f05010b03d104080c0c0c29034a600c404501d403050110303405032805030034203490402c059641c40c3c6040c0c000394010f031001c0310907016030101e02e42c51600224100e41850000048448920180f2010780c0b0410b103140c2c01e680500303400303026001c050b0050755001c00529404240150a004003030074914101c4089034410710441d130108d0010701090301c5d0740300100d8203e580f214061f503ca4585207403d034041d1184406103500104085400c05c01c0c00b0581ca47e00340600790a6881c001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 155157221 1250 155155971 155156009
    0x130b1c060f0308040b0703021603050109110a141002010b060a091404090b010b090303071403070203010e01060602030a1b0b0415050a0603020622030b0a020d0501080a0203150c070602040e01 83
    0xc030140c40b407101405010050000704500140750000707040d100d201744190b500206500d1500c5030015025041501d5580d5510f044008021040d100782801c0d000c115104102946400a50101041c455030741600804541c1d4411034603d000b50000307400d41000810144c0c485590620042030400c003449966030714890b400154590742018490b6640a170340003c880303010f503801c4c00d00c01d5800340c1c804140c603600740c0300400940f004a0305640411503c25800301c06143c1d41c400384d004260a40d401b55020114903413525604101264000040307485002c003504014110f9400310000324032300a0b00300c0c40500600c103030004000070022001c81400900140a808000755268071140341d08480321400001d4000104100807001ca500307903800804a40c600b20b204000040c0c42c2d40e41c02004140a0340e003005c4040d00822400c0c081c89103406850301402c2180001d01840300745400195660120100d0342020981c0e40d40420705001e000e50841301c1054100ca0159070305c65030b0700b42420041c842441403210300080e88031901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 155158471 1250 155157221 155157239
    0x2307170c01030f090206070f0f05070923060102061803070615060221040311120f100e0115060c0305041e0302100201020a0c08090607050a060e0d0809070605130b1c06 73
    0x80e40c1030f174010700842d0407d45c40b075481031140d1003100416980c01041484480000d00208800c44c060440b001020030b40c80c07050710ba00081161003170803a40101b096041002241d980c00617969510a41070045102c440415509890651250060140c4000e0400c2c444d2748502020600501c2110013540c01c461201550058048100c903c0741114990b10b07004000030800b24611444400c80050002d00025865026a001a00e00b20b0301802680140c6c00c003201c0000554100d10800d581500c0502c024800042917800700200010a8001c200074002c000c101d07a420b240c880c8080c1c43c081c02408140c00740001004a0b00079195483c0c3c40124071034541002c482c1c40007403060090343c20107200c0c0c0d1182c908003926075641da0700c030750020b6800710341209042c0541c8001c00d0040080c00640c41c004d900004801456004481c01c20301308558940500440205000d2042d400003070034000ca41b0140341c490b03110418504080f10070729682d880000851030115040c5080181090503840c100b000d0f400070003810390303290206 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 155159721 1250 155158471 155158481
    0x306041113060e150f03180307351b0c09010609032001121109060a080a110301050306040f030201060b0f18100212091302030f040309050108042307170c01030f 70
    0x60307002e1220034440c1210702054900034542203080e080340c0e10090047c0c903030f411345141c21001d0103645217214280f600c840c40841c5000701807484c40c0f10717211a000621340000f0080c64810030b6082941c0070f50700b40300424207800503c010101174400034250603a40d40d40f074800512440d940d00082d103517603510308500c0c0261040d20003840409841a114286d2800c05401c0210007411200e4101c00411005c101d44080b55648400404010015071140c228904003450081e045640c00580c54540300700400042c03000b03a40018180d6402a400300d010380019040d03150490260440b580040d91454011800c6114030760b07044060007040d100420420700b030b44142010400d804264142c0040176030000c0c0e07110302d2603150300c000400f03180f840540110185036a291488003240d0044400020000c02d407408c0c00304241c1d0022142006000074039044070503041a4890040800200400c81d046040440d80c000070b2010602c42c800050548c422410b1b482500301f800340d5155a800c2d0140742c000f0385000d0400007118024811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 155160971 1250 155159721 155159749
    0xe0f0f060318060c07030905040e0a0f1106070f110f09160311030405030a08010b0f0301150c0510020408010b060324120f010603020f010804050a080306041113060e 72
    0x881201aa00018030200e80d0000d00980c090b60381881025032008001c0003018081d24642a006686000c203040081c43c0d0900340d0070103845a4142042e000780142c000400d002180e410103517000215025107440000c004c8884016508030a010540300c0078000b0702080104000d00801603202c1818001e4204402807010381301b015403044444000c2240c12503035558109003052a401d0015400180034090030854004a03021a896480041c3c035400243d40464040e00504901104906001c10300c200428a8001401520365102212034040e445901c6020700c411956007003401e6407009440b15000c43c010f0740c400d010b4282c0542c00d14154250504246c001c40b445a00c10500142c1d0400c204195001904010f04009a00c0108103160500a56051101101010060b800090a141b451060040080390803040342e041c4941e010400010031008120820140d505c50003181c0d5a941c0d0300300090042030554200002001d0200b00c801c0228a03c0c000f80e02074403456120b4100c002444401c01001c2440458 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 155162221 1250 155160971 155160979
    0x50a060905060307060807050904050c091801230121060f0506040602190c240306050103020a0c02010e2d0a0905040236041113020903150604020405030a03020a030e0f 73
    0x21304001740d51042c00c465800c100d951900600d0b10307001d400000e054031b40958003030351b45600000300b1601c00c0c681988008140341c02146c101c03540c1c1d0324000c0e221005c03070464500700e400b819081c44409480d0b1303c1070141002491340780c81491801c0904190803001032083d4000c1a00306121b06c1004035441c58403a05940c12600e09a0041500b480c140c4e907100d19814207068121f5031190848008038040e0184c0d01c0745c00c020003081068503000c00300c1c55001419190503600482c140b42c810800002d100c0d5008848001854080c2800510690450045001146002c0ca42040c500740c026940b421a090380c6242c252003181110401c001c9611070004030212502664001e50103001009140d4582c075100c0c04100e20b5180f000550f10040c0078502d000f800a013021201240d240000c40340e100b4052815280d0542c00c400742d6101182440d40c810046591807100a03280000200000005159590345130101ea014000103020340355240b00720f16001e95030b0701140a00f10702080141c5200040c074180229100e8034a0f500030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 155163471 1250 155162221 155162233
    0xc0906060d021303080406080f06010c03090902030709080d050c0f1216050304090228090510030209030a02040213081002070503070b04060f060e1807030515070c050709050a0609050603 81
    0x158001d070096114903100e200d08400c954000012603101d4020300004c01131a01d5002c010314083d908840780c00402403146d41402840490040825072045900c3e094650690005940781c84550007980c242070320b6801801544203012180d992580d03c0406006d80d841300d10100e603290040103800ca40c039200c25482a1721080c9080c002c1c400404040f4420400c4103000d03a0540e40b5180c0c840d00c20100780e82c04501c00c0011081c00c075806100e19921406411400d06c07161400c046203a08090018981a40304110340c400c0603000706011045a9080c0a00031000d58010421980c4024032440c00342074400521404115010b0411b0484d9018002e00840300d003140d001c0051403903da0659904086a80060300503101c1a1380c45009503030f10340262042102601c03031300c81000c8180c132301040c400050701400c4c14503005e19004410104001500010b40c14103104100b841402a551060004c9820380b040504c050b003503110320080080c101e00c0f564041402200c0b0100180010381d1641006010340b1002d840468240d0710031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 155164721 1250 155163471 155163487
    0x80a12111806070803010609031502160b07021513030e06031005040f111602030706020313090c050c15091b010e010e060f0d050a05090106030309060c05030d0608010e0c090606 77
    0x9040c0d0214081c0109800d08140b29926900c40c10b810036040700001c5030111078240140302040e11070100d0152494025072404c08265484140c0358240d28000f881d41030b500300425813140c024088595840340c60b100b4078405150582110681421864064012499440008170345040000840380704d03000000138190204c7c84d280071303c8010700c0c0108144400f1f980d6804e0304010040380100a011241005905907180b9a04d40101810015144c1c414001c0d580b08000c0c0c0b403558110905041c0844a84081c0010514003c0c0f905407204d11605504500a0241c40391411050941003282401001000129145440d02e003002c41049a0285841ea01042d4000c09004170f03584190401c1e102e03010302404160610505144804258101c003400480302502d41c01000300360036640c4035403035002100600030b1100605d1503c0281c0800002d010349010803524171013100c1400390030800c03105000001542009042c0e5980000c5008045246010706203020b01e00366071001c1e20703142d01d2131307030003000c1c018241460f00c1e4030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 155165971 1250 155164721 155164747
    0x30304080a051201270b150d1b0504030b070e090c03100f08100f0912050717030f011809120e040b0424091104030f021309080a1211 58
    0x1407260604020040022080204055540703600034001c6001c82120401c041c4540d501c4a040c1d01c0302c030840640707868040b041a0f81d41c004107044884501a04654030607502d596080074001c1c108500c0d010842e1000d41d0005550300c0030041003103e0088d4404161501c4601c411111001c40000302c83c2c0c046c50040225600c1003c1f0002141c11210030709070b000c402d5030b0358914816a0491584403040c25008554811441903031805101c010015428082100702c45507074510034802612200c03102000404250300c020081e00e40e40032818941c06081c05a141d250602141114100c240038900802d05542c040d100c06550f075000307180303020340d00110643e41034406250445d000b490300851541c1c010b85038440d0540d5a12144550756200c982035a08210001f03110f145410204e01d0359010310000d0789801007184240c1407100039201944e6009800c42c8007007525000081c100070207003802d500b030545816001000c0103e11001002c1ca170000e03403541c00ea40030104a41d00300711030120b200748a41d01020002104c116103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 155167221 1250 155165971 155165977
    0x6040203060f100816050f0a050c16030b0106030c020d0f0f0903060908030f0105010c050c0d0212010513060507090806150a080f0607030f0225060608010903050319050103020303030408 81
    0x15002c0c10b0a50440d0000001030301d00480c610040c3c01040c865000e00801200300c081c010180011030510525241a01d0580d8500340300e12001001000000701708010640010f200f0704818981040f00a0011a00c0f42031000444100303109220102c0d04c0c004c890225607002082250003851940c48200585880d004c080c0e0f4214102a41d04040001410004c000a8814443c60b440c841c05032242d00e4603850301c103840c210041c0068100b2414002202c900c08000303900020741810682050340c08190a41c007a01c00b01e40c40300ca1180c500b400650910701000412020b91004c00c140314003c01040c0700b9515a0b520a070350041c05401814900e800138030000b10800b07900000b00300400006000c20322440e59621545082c03986006105200d034001605022001d40c0c1802403541d09140e0350002c6292a4400a2009041f0200000c0042c00e8000790b25250034405168444801001c0220007442004100e240c02800c690040f907212054010107a0508407411a601c1894181ca5019000f140345031965298403410750 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 155168471 1250 155167221 155167231
    0x228230304020d140313030c081603080a0302040b0705060723040509130501051015021b010c0204060e0106020106030201140703080721091a091209041505030a1a100e06040203 77
    0x1421810a03210070310000c20050030001c101b02e80f120b00441c111300c0e2203a19101e0580c40f524080c4d0000c1c030b41000040c10603041d4070440c0c0e800b60700240d0720140d001c0142c0107402031b588401014400440c0003000d0110200300180701d6146540e40c120b03141521801010102c0306c0d02450240550180818442da0401c02240c2d40c00602400102000f1f0083d55140c90a55804982c85001b44201e26010400802d0380461840848505d002420f00191004160521480311040740b6042000301c04c032580540d01c541e0300c00780181031040300c100032130368543c03030040e0103813010744270032800264070445c5040d1060000c001d5500c0c17554103513600f001507102c010b0308507020403a494001301103415103134102e251711106102e00e480461023010615400c00301d07040c0d11000d0180041c481c401d0707604441c0c02c0c040c0020b000c400712070141070103d600040040030701001903c4440b10782c018030703018415503900c0014041003101964034211482c0c0400469135802c102c243c2c10715081d2281c50855407a21011440070729140d00134682c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 155169721 1250 155168471 155168483
    0xc17070f0e150403123b18040c0503250b031e04150b06071106031801060b130506070b0601050d0b2e020d0203040909060228230304020d 60
    0x40510b2800c651140d4041c1e03008403110a00d4020183d0f02c0303504818076242507000d980c0320a4092510521144100520103004841d61071508820185603032a9141141c440c01c0f00344007440b40346031070b1034000d80c00d003c18000d1611901c1400c0400c0085025000d807251007072900d42c1c2009800d842c1040c41ca442e40c00c003a10001090041020401d8410b01d84004140f0950240b51401c0c50710b0043d00d8500221103c4a0569000e5401001800d011072803ca8212288103005d07280780760340f5943d894130305610141c0001e1081042d400c0000001d13072405403401801c620310f20000820125582c3c1ea00300419841011030050105903500c0015000e5801840582000c00c103070311003c1045c00c04240011240d04141120300400c610505880044880700e1218480304101400206030000003800c019550740035a2244c003400c5a00e648800e01044100c0d0103948803554460703409503004440002c06900302400300c0a80c40000e0a5495201c1c0803119141080312142e40003039031900d540c0361138083c4461040003c009943c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 155170971 1250 155169721 155169739
    0x606040b0708031902190f1b0507151e0e03031b030703080a1e0b130c0203120708060108190603021c020a1203080708090c090a0c17070f0e 61
    0x329000c00d500a11640340300b981030a9480c40c090300011a524600f40b407400520f403060000d2000314030340642c040494503050528100b0600c5002045071544800503807421240c4100b640b49003080400aa418141d0309500030200101501c00001c0b1f07085910f007920064480000d29101501c54010800000b4a03500076080d0782c1380807000c810b0080441140d03410800b9170340c80090f00f10103040e03025580070f4111102a41c14000086194030f501400c03840c0b0a9002c80155403000c19403e55554581a400150703a4584c0502000816450294a0303401040ca54a4030280820000350243d1261209902c500703016140c640807612000c4a10080890450840c0b188903030b1580c020025a44084004401407400c2d202101035131200c1c81071002503220b035030000c540c020100341a000040e03004149554040d002d854590010340d100c03400b89241500c02801a40c002010400f40300405146400c0140a82460b40302c000c203000c1150103445000900316080f6000440b4007910200c140d00c1040c9a00000c1402044080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 155172221 1250 155170971 155170979
    0x1b0c030304030f03020f030a05040510090312030c0c0b0a0b1002060f04030503130b1503010b090906010e04020a0b070303051014030c04020a02030904050a0b010201050721110d02070308100f050a0905060604 90
    0x21031944230610881c04580042030401c100c5c517000c0320200b40e6212a24120490398a15a9410160b0744102d00c1d42041c16201c104a080142c0300d00800a4081c7d00040981928204420b03240e001780414201d00e8081c40c20302c00c80c2c8981c00e0000405602800c154240d078010b90783e96840454207504003806070750000c60060101800b1a1500d06c925004000310020728440d250400100f5085480010317496009211207400c00681c00c001054040c1102d815250300500d46d600c0c0c0c400100b043c0d01c681c106075910440402c14000381030f4140d00c9644100a1405007011064907136050042141410b1000c691580c040001880e0500b4250081c0049070120f0048a0900782c200c0001000c0d02e00071a00380d4503095032207030034010640e4240034090b009107440c10218424201c1d590324440118090880303020040d16101c5800950007408116030204540407811520b80340c1d5850002c3c441d510a0f40e0310551724514034408034a031390242e03520030100e9400401c07403180303949000c1c22600a400010070860717008106100003e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 155173471 1250 155172221 155172223
    0x90807060605031011090609010905120307030305010504020909060d0201050c150a1b23090405010e0f01050405010518130503030108030d060602030301060c030c050a14031b0c030304030f03020f 85
    0x11a04500c40c20020032114141002d0610784000e2500c0856110300b0200c50407815240c200454142401c1544e03001d541e84000c070300684400002d80d1181d0380000d4217800001c000314010003d481054840c0e40c00f403003540da1340e9007008103030700031120815480b1307031004003082092811041d002c48041c81070529505202c40c610f005802e140030008565250540c05003001210301c4240714000d0a90854420100d1b0b032420501c000700345102e18924403081c0c0f16a201135107501e103310420f031038148074024030a006540e1122003249c16840c0c1a500740d800950024004035103031800340622410303524054240b003560f1000d445c602c28a01c0f005421011800c01c4240701002244007800110b01900000380250341d00c0341006101001c48501c0d90001c01190024070040c0065948070b00c80c15010f0790075141120ba500c0031030070a81c2c140345050744020f041d0300c00400042c00200003c0083d21050700b1503072901448441d810b80e815125920401c80700e515400030082032002914034000200b101c0d000b481110008d81c6142c040d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 155174721 1250 155173471 155173477
    0xb07061410030308100e040308251d0306071b0f05070603051602010501050d03030906020d1e0b010e130c090e0a06030c140d030f030b13050f060d240908 67
    0x1040a424201200b44141a0400302143d0006002c0136100d146030b01e080314541380040050001010401c81501180420199000855030241506114164400c4c41d040c05458034805140c64400d820f540402c60b0003610f40800c201e8841e480507160031034130804a048543c94440c1560b002c4a9198441c4c000d2000f043c1e040140f1130240c05180c900240368140912041007901580c40c0580031a810500184003603159885044d5046905081c081076400703042c68828042c1c040e070080303003440601e0002079200c0c0c0b4065000d410701a282142081203035020b880011940d01d00c0b811041d641001030000746100c040d000c0d83c0b0410700044c06107880412203840342d480402e003600503107070b2003146600c03294144144101100210020200c410f2240c482c01c1c4941d01040d00d480d80341c90042c081c490840c3c41ca20250740a81c000c00c800401c001d0408480b022282443c0000300801d40d50547d03942c94000009042d420504400d0740f60a0300300303030000054090400304a1001010304200c0c0900790315036100b180010488406 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 155175971 1250 155174721 155174731
    0x1501050103020c460503091306090c080a06060201141501020a0f030507110121050703181401270809040603021815030303060a0302040e0f030309070807060512010b070614 75
    0x3403c001c0b43d80d504850074100100c0030010440c9100075003c0d130028000000b1108850f030140c0f005050680610014030090086a002c441014107009414807002d03031103480c5c9882119450010041c407a200c6400304d0132140c0822000c1d200390741a20110b031080070340b210245903041c814411600c1c40b18495403000c3d100c01c070b140750880124001142c4a0200210403040c056859001e190110700314901c032030004d01341e50205503e0310610b80c1c3d4070301240071603120f900004003950644400404a850b540b40080500c40ca10719004444d510b00484080c2e03105182c902d00102444601101e141141035485140356a070140d080d807584a96035800c0040180c0700e680500340140c3c42c1100489161a028000001c0100385041140c0f0941040003007188550f00c041c0050192a0182e800244074081e0081d400d2034a488124480c0e9903100120030801001000925042610040c00664400c0e50781d030101920580103400ea07954100e8001d0700103111034510707a0050a42c1034003817680803c01015041c1150b0342c400f81030320313 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 155177221 1250 155175971 155176033
    0x3060402220f060f080117010902040c050c0f160b21010314191520030903040f060504030305040608070201021e03150105030f0612030c0f070501111501050103020c 72
    0x210801500c1c0a4603040d000034907250908141c01131407504002c02d1030805018400400000041c90b07000c65509502460301d00354003500803c100002c00e40c0240c5980c00500c0c0d50b8096104500440d001c540c3c8c080f1f4550300c04100140701c116a5410140c900480e6000a03800b031030703240c199031000c10501a04900007802140140d401d02d045a001e200c4441c10603801d5503440803c083c140c4820000a012100100b500540d289400181d1002d10110701c0340c200054508048009408802d00541d41c50110041c4212005240e013480d000d90384032410768079400b961002801040b8107110400007107008000d0198004418800145006094120310092841c01c0c03189001c982c5003c010400755016140070801000400d0a084d403e500e09180070480d0b58600815940c016920b0012b550b4032400200300f50f80710b820282064601844c2c5540e54259200824032079940050f00e4000105e050000c00710302c03045041c0c0e4229049945a081000540c065405158035011610410782d001d0303d00a0440c44000750184000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 155178471 1250 155177221 155177287
    0x3120403050909090f07090c141b0105060a030b041509051516050403080409020702030c0d0501050703050f041101140f0a03020408010f0e030d0f06030605010914090706020c010503060402 82
    0x60503c0943d400082c458821a03104407161501e402000400e002103401503030020564030790f0342800300c03016004410280c2801c4800b0528002308111004407081e40d04100e00208483d6480e00c0c100f00613403207a4400940a0680c800119011030020307007128070801c0c510340c804109003031141c0d612803420980024440c42c00071107105200b071804001c50041c24207891407814504140c1140c980200030b105910484c519590300141c22001c6441c00c0c00050304500c0c0003081c2c5070f00050103041c11782c040e00d021901c2900291800000914046010300306902030b640041000003921003000044d18017002c0550005030801c003c1c0042d05450007010010310503054140c1c2d0150700d80780b811f88140e0070740340285119241c590070094010464580042581e60318100305401007900c1448090b0340c4001d04075900042e200d0383c201000824075482503002a01c01e00c2c814460902c0541d5421422074550145004002c0140c1001c0c6a10741250302c50805150030047c02040145000792058080e0304003002d00c4104441d402d080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 155179721 1250 155178471 155178487
    0x3050307260903030621030f130f12050f01050c07021306090203090a0209060a0308190c0609060603110910141f030605030d110c090405010f0c080109060504150501030b01020312040305 81
    0x2041013150560031b440504081882903520341e174603805441038610040710045200380341d58181c41c80a100410070b4492042c03440c2d1320748103443c54a10454a0a49051203903046074801d15a05110380b1b48190001c0303103540d041078110703800c2260304565911714001807500d550b00841c80385201c0c40154004c003c0c0c02c0080c08004c446105104059000070015031141462100410200c0c06c50ac0c200c802c01000881c0c4110043c0c101501a41c1c0c6180591000d0640c600c1c160b41c0384101b1000e070b0700c080305484c094226400080f8036981003200c40c83c8200c3d2250b000241e042c100b00a40382d40b203000580c550100901882da07030010700c0c0e006110303e6110003d0400183d107170002000a810180710704403010032035151002c40800b0203803400380e03615541070400d40106458800241031007801e40c8101183d5014007400d02c0039100d02440205940000c0c083c2113100b0b440c002c2c0c0000d0500d003034070420a1900143d0322140d0607519000c0158010300018007410f055000410042e04150816000640304510a0700d8150300e540c0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155180971 1250 155179721 155179729
    0x20312181011070b06030a0b0403020106180b0f010503060a03080327120304030f0c14011a060a020a0b040611030901060303020c01080405190501110414040f050103030503072609030306 81
    0xd60310100006502d0706402c281d044891000b221102e5400144541040d290f400100385840d4000d40c010701480c4403041440101641900010110740b40ca0003885403001c0603800c0c06084414801b049584510729036500340b41e55004a010756401000144a038249950342d85071440c2940c400c0311122140c900160962404100f00c2c403062315540101001411001d0400502600500c4050710107814054500443d84415104070741c22040b0070351019103d5880822103000501901d02e0101018154040e51803403982820110156000c1106550042c109030001f51035108910344080d100b55881900c4a01c20381300d2100e18002940200286000002c8807481c604000741000750001c2a541009085800d10000c1000010050a407520144100d84410340c58038043d40108500304815412120201d400200904881c100752001c030030a03117062102d178a68020050845c0d40c02d000007030101c1d400740089211603103e45410000c00366000ba0100d1036010717565444500e00780454540d10150f00000421569040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155182221 1250 155180971 155180983
    0x1207120617190f060b03010b1305040c080f0a060b06090406060801080c040b0f040b01020f07090b09010815161814040e06040302030d0b21070305060c040b0a03020a02031218 76
    0x45030100b40400030640d5034440300c0c1c004514050490f0740c59104071452130340c0a5104c5200c0c81d0005101190f42000a0101809000100c0301541da42e00c1300c410000709c59002007800c414290010b800b030002c000550fa01c0d0002008071000c4150002d070103100c0300700c0b0b80e03c0368031a1802070091612901c61540c5848465440c001040380607500072400c1442c0d00c003c58441000c0d4800c0c0c0c50b0225808076014400c0c0300100d250851210038520350f481140300024041180350712401c26000f05036141c08880c0c1e200c802030755403110204843d6030607a900100146034411403140140c08040310380b50a43c09901248004111000c4913001450341c203a07000c941c1822880c00f845488448580c0300094019440d00e5100a03440b4050407140070b25003030301c07001c079003041d591107141052030b44440d44940b000e0000380742091641c8403d0740c00100c03042d101d51004a00000f00d40000d940c11030f08a002614601000c03100c0880c060341004284005511051001e580c040b04103da005110b0810090040c807549410258145440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155183471 1250 155182221 155182243
    0xc020105092a030f0f100b01020c1203070b012903040b040f03140c0105160e0904110109031502070303271104060306050a0b040605040204050108130519030825051207120617 76
    0x61400e0301f040d8032642c02080b14030754920202c031500342c180710540d2404e043d80304001c0300604c10030a80b80041303500480310322220380300b0076180300000100450707400481f000d10066130050300030f00c0f1070302c0042d000422485412035a503109240c00b20304018200462252034002c000d4000c402d9444900700841c00880001c03085181880707242c951000c40018011500503800604094016840108a0345042e40203c00d00401181c0c031039800b03000c08030322020002c003e42010700d0403000641046481c000e84402c0407078829007c07525000550003041c05540e80300507000c1c2c2000700ea80003034981000001041071449014800e0100040220721032486000704011201030703800c071798401c0d807040c00140210790780f0400c0540d114407150313180200c0d100b143c100070786440302a2041c3c401441085031400201035000c81c0c218041d016682294038101140c081810243c1c2100c2d01b241e0000b01d0070305c0b82d86444041001101e030051820b08240d80350402040a00040e981142c0110720005004003c08104910402c5850101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155184721 1250 155183471 155183503
    0x506070905010c11060c0307210809150406090206031e010501030e070504050907150f0305090303061e19080a1506060e0d17030103060f0c020105092a030f0f 69
    0x2460078140082d0245003a510080e00001c860496902d05458a00031a482c10700403404032600c640192404501d6104c0d8103003c40441c184c0b08032401c45140c0030300f902c540922600340203089003109001c00c0350a001d40c020f2054404039210010500942c550000135801403c40c0130003500480790120100c80000411383c0400d040502c0c1411100c4c4032800424007405490044501040380d486006103646440c0c5c951300041d80303c0c42d900c00012812608143d600142005944052149945130316040380c890201301d464641058422490031400744403103c04151409005041036003002c0c00220904212469812243c042d501483d0942c003400b02140d820b0511144102c410320606040c000000c01140c020100280298414070b0f104080040c071005110310b4503d061a807988942c0d5900b80b803009040022070800440345031105080e501032040c050300e84901da6810050600c480200b1210000d0240303000c04002ca4854429628007175135050010a900c2a0464010031244100c0913606040c01c412020304116 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155185971 1250 155184721 155184737
    0x11e06170a030504060e060f0d0b01081302060406050d1b0503010501021504021e0d050d030c03060b0703080103030e0d020a0e040605130b01091d100e0c041505040b0a0b1204050607 79
    0x1070f50201c21101502e121b8546a0800d101d000041603c601039a4001e60183c14003044180c40b0311078590041d4540c4001b640c4000960b00c03000c8100290020080020b50411403c00c4240a601d0180d8020324060742d4421000903030080c0340382c11048030001202d00d440003940000041180b584c4c10000222054052007a242c1c0c10300b440d42c0011000e0b480d5a07001e080103004030264008584e5100c81c3c001c2d0380c5803c0801d40c0e0594119410090050200c400b49902007032415001041031540d50059070011980340d00d81112503421518240c60041c20200030720743c0981100748160068441da00500010300c0031040412180c18645040415614020001c5e05105194100000460071082c0c41904451b940000003a0002807031800810304c901c031070b00c285080d2140b01d41050000480c0d0740409101007a07001666a000000001c00040d07600c0c1204400c42e5159882d0240a035141c20f80c0220340c00b520007480b0400c3c8a640e03600d9000290440824010400d1041c000c110a1050911041350b000e4110318103c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155187221 1250 155185971 155185973
    0x905090a050718060903030212030108030a0309051e0c0a08060c0304060b01200d021501081e070305160f050f15090a030212070602330405011e06170a 66
    0xa50850020300200303046840e4070128841c0d42c040c5084072256240210504501603d40c10050880c0e07585100803401441000aa0a12001a4401d132410ba071a000c1c080c40c0303080d029807400c4001d040245416079407030007107400c80c000c00900942207080030004080500a14a41c50341000303207256165001c00c405801420400c00382008003411650312030f40c04032002035074041d20001201e4a000b1441c1e4840700000504d0280b0031903900040662074400e040d800c076541c502e80c2120400c00c00600388960320460b07120051074140d401d452680300610b5080c5108a0742155038030313207440786095440c144d80c02280c00380040c10301440394080c3ca050050101566011101c152040c045088586040088410010003103860b2180795905a0b03040d00941c0c0045c405c0d441d50101422058490689200302c00241c400d000d400d01c0128030010450380e4159041e000000101c0d20034001c580e0300790005008540c1d41d56140180283e14007000c900f40c08110b60000001081420b060040304403986800c407641d03881d03102d100c001d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155188471 1250 155187221 155187229
    0x10030606020f030a3005010306050610090602060c0f0c031902101415030309130b030c010305060607030804031707050d060e040b0105060a090e0f0603010510060c080f041e050f010905 80
    0x1c1c101da1140084460faa40d00c07129003210a0419080345c41c0c0d94104030001080c820707182c2149002d031038111000401000c403001c082e04ca01d2140d00c50381c00540c00410020b110030720005d0261030115845103c1601e860b17000c10310141154820301a080b940b29520381c420382c0c46a410020240030312240c1408111000040c0c0c0c1d000800480108007216140c607110440085032001d01c165a4004805004414002e1003605003c004c2c0500040c2c02c2d00138801d80868840640c0300f4004e15020301800b50685161000584040b5201d40d0010402d40c20701c45507200e2942e0300391892003028071521450b40e80340e40b205111a41178054440d168440340c0d00810f920300340030219171501903485c116801184c1c600e58070701c1b950a09a516801640c0003000080581c02001910200010681d1080d0801c0300208055941c050740d0400295080c00380c40c0c0002c10000c0030b84001034a960040c440e16900054140c10241c0d40c4040e920090301d24109903021070782c000c404001900b401000001074031000d00f08411a2404e000100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155189721 1250 155188471 155188487
    0x102040320062503111f0f0b09150402160b0f010603060602100905070513090605090703050d0809011404032003030618040c091d0601060201110307030b0f10030606020f030a 76
    0x8980c0c1e10440f64803800c05028501086400007a1001d0390a42164003605c2c205004100c41040c2d1103604044000000e92102d2041d070400c48001403002d641500d5442c601d48440c3c0712009a140c20aa0811076803082c5003450f07103c1030905109156846061900650719480e081040c0d0241003030508025060100d950017149802209092040005000c411400c0c0710307141440644c0b00c603800000a12143c20003d03603903084148618000c40041c000f030348840e42039a564a565200c0640160404d0b10b00d1210a44200321b4150010b41e924004200300f81004e10a0740e01007800c1d5001c8010480030000303641504400061108040c0d0408055401c0d41f41a402150a43d4020441511009050800542003252090543c4003a100ca00000c102021250302c0104415580070070180c15481460000240c1d00d1050150706441c1c004411020f0071500c0f060000d0b000b5052110500d0b5102c0b655106000032070b11600300031030800069980202e402858044040d01346420f00b006101680c108004404520340c018001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155190971 1250 155189721 155189767
    0x6010903080702040f060f1703030105010504050909280308102106021b0a0c0806010b0403110d140d090605130614040305010f050a0f02070203101805010204032006 72
    0x207410780c0c40129100040c000e040300684560001c3c0740c01c8000c10b0342c0b581003148070300343c035125111018003601c00c011241d601d0200b4441c85001842c100b00900c400c2c02c141c0e92054100c031425046500c8215034400141d418121240c280c908814503200702d00916610100c0950803107a5012000d5045003071407000400c00303210017001c0d40e0088140c03114004000c07813541146c2e00c10340000385103d4460700d03181006454441800e4299800b491141010a03a45404600795048442c02016a85050703c2e41e076401007902080d6070016070000014401b40049141d080c94080c02d609010082d2a00d554001406400754040d60020802c012050080e2040342d06810202c0c41612031a05058080e403400da4070401240c4280d4000030415420501c000750300d80f01d550411b501074040711000380808284084044228014104d02940c150300401c0c10b149807a2542d807001c1805800034443c1400d020854075030341d003680d106500444484220b0200f80310b02440710024810114070031203510b40342802d103481c0c03801203040d2404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155192221 1250 155190971 155190983
    0x3190e090714181e04050f0c0306010e060904021305031b28170312160f0f02030d02040b0c07090903020a200a0e0711010209030a0f14060f04030f0806010903 69
    0x140c4100b0f0f0b000c01c8000311000400c02041c0034030f100440b1240c02d41031001d91204d64012030038040400d00c40188081c00394454903840f40c149056540307070070046401c85140702ca01500030804210608c0c1580326400104118210188850103031840c00d030a040c9000882201110f01109103a640a100d51f666100c805500941514003042040c0c0007030300302c501702c1e590340c0311810280ea801483d0002d04404005040303404d15400e500d20071070340c03124038060907008500e141d02d000956a0f1541e80d26036000d0380e0302002d0151a8811681070640c0140354404036070058109000d4100c0c045820b024000041081c0f401400c2d1100050044500c1568080e6450103c04802040710174100301b00f80303044a05800b00e01481e4402004401c003540d42d50384c420700d580b43c20b450000c00212611141c015098050003222910038002e402010040c2d401d4a690960035001d40003210418641d011590101c0820803c2c2d078040c003a903042806890420345006040e00308121040c0c0e042c17200b0042001210381e00301010320b0480b90814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155193471 1250 155192221 155192227
    0xc030f03120a0b060c0d030608010501150503040302120c0a050c1509060304031b0614070903020a1a0c010213081509071703130801060f0b19140c03190e090714 70
    0x60b50405422005003454202c80042450505500e00040003002c00226480820580e0b4554098509881d0240280300000702000a43c83e80c40d440f070001103510038040d10540d01c0d03210b020748040c00140e02000304041107a10000c4000e003404000c4c0540031402c1d008a034806010b1503481c1240c2824041d071540c862280708048006024140141034401e000148051040c00702c81313941c9402c2d0002c0410507441c3c0340751000000000c00e0a4040d1000b00280c0e80c000303040e40c48040c9007c00750820200081e00000389580c0500000761422005d002800c2c521100403e011041c50504015030320f00040c401c0390345550000c02040c045800382c085880d41c152804080d4401180c400c0102c0d851440c422590200114a8a900001030b004019803100040d100a82481440f107a0f036100c84512601640f0703d4194800c0d4401e600c10b045c503004480105540a201000a0070803506000060660300030f41d50f00d00e1094209221041c0196114084402c00442260302c0e0290b8100030000800c01030043e01c200b44482000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155194721 1250 155193471 155193481
    0x1003030c0f051009170304030e040b04060f08031b070b04180623010813021e010c0512040e011a1909080d110c0604032001051207020c030c030f0312 65
    0x8101c1c60044103802804484440c0c1c0c4078404040103000890056a401119060889030701984c1c0c0b0449000d150036559041c0c1c0b1001781000c001c001e184010b84a80d0103607032804001032190300c0c08039903802000c07090b0140d42c40c0e440303200402c60401c075003405803803030394012010a03c204413050081d182034034040d030384840801c03105c1c00000c8020800303504010040080c0a25103040318110f20354808041800f0f03600d088a640350032a0780d41180400340d20095020345001400400203180c1000b100345010140742201301c0440d41d44070f180c00d000c5c0000b1181400000000d050081c800c11100c2240104041483c904c0d508401100740102c80c00f568241e010000210345018500604c5803c01c080034100440a07510b0000140d0405040700490540400850151026001d01c07480c0074000c0e5002c0b02d4002e403070343c04079900d18030000e080020755544541c1404014041240005c944200c1c151107001a0380040000c29000d004240c036224185540b54480d40c01203001c1282c100c0080305440382400002600c050710740318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155195971 1250 155194721 155194733
    0x9270602040515090f092e0e07050c0c01180303180506040605070209060d020f060a1101020a0c2f01030209040b04090c0f14031b061b0c0a0803031003030c 68
    0x12980590380c400160307040d08054a0802c0001c24607401e08803900080145c40303800f4002142d0088840c007604803604011440f0f484015140c01e0103025055079038001440d195401e605074180103864110018070003003000c824101c000c1004a15503242400c00c1c0311000000c0c8403410051204c2e000040030090002c0300d101d15131424240b423070058040200040c1d16035803620303001003168200c1e48007a84100104004540e550500c240c815441c280c019244114403880b010a0005d513502c80c2c01e0304020030050360150740c03103004c3c01e10141218030b0081c0e80340403160034103003008025038803614001007a0350101807914968880020840c085a002801c000d07071a44840400034004085020220b40c2140c00e01225408100d46811180140c0f40d0403803801c00d280744c90702c103d07000e204100151142c00d81c0c0001420304a80807540080810141d004010310318042c40003202c0f0240540c00c82c42020250b128140070100c0d07141c2504400c016004540040d42145041d880303500118055200140034014540c00c00818002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155197221 1250 155195971 155195977
    0x8070b030a0b0f031507030c0e06040902090121020a090905240109080601080c011b0c03030315080313080d0c0f2603010b0a030b010903050a02041a1e0301050109270602 74
    0x10140c1ea031405e03120300000c540b40012101c00700021f140c1202c1c0580107005004460300080c02600c1c0600302401c19409000a52004500a0601151110010703c504c281a0918a001c0714840f0268940007904409840010b06030481c4040c24105070420089005c42012400402040384041c5280c80c0e00500588802c8202e40014100703000780400807a401c50000b4511034070030f2080e80c82650200e0003001d00300102c05002001082051010303020170100e4820313088404191282580607010036a40c1c1c1d4803510b554000320a50b841c0310366005080110013400d222040f040b00c12424100981d40640c4d032040c0b1440081d00005220f840300380c0c02a65a240036808040c80780c4404100b09507a9612850300010680140024100090030b00180c25419445813200d40200c0b0340c07110040518220640c01c00003c1c04020b020000c0f41c110403c10940140d844150005626009098981e500000c05003032500791801600000720080c100044d09140c02c040c0040314901c04041da251a04416440c500800a44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155198471 1250 155197221 155197249
    0x3040605041e080405030708030a0503010311190e06041a0d0b041703011712120c07031e0f080903030606270409080d050703110a0f0512130c08070b030a0b 68
    0x40a9040030008100c0000001c20170741e6001c404a4030005e81e03914240395248208100c05000034800c5c801000002d0b00c500345a03c094030024103047c455002d000c10710144070815400b5100726000b410a2082604103031181c072007000000320754211002c5d4203e0100d40d612a607480014085104000000e06100d42c8440c00d41d081800d104203299203582d00d1021140c401a10042071205009014551840100c114110b070100301c01081c0c88100c44e40d03075a000e5032607030300040400d500380201d514841140320b01181801441030302c2501c0c1c03100d902c0d091a0004001c02c00040021f80b0b1644100203000351031751418190b450030741c21034850400d04102e170706c3c8aa11400c8007400650304a42071140c2e032001c010780b21b8060007403031100040400940c1d1b103c032400c40c1550080c0841c100f008404020000c0312503c40d81d0602e0101c00c0ca420650700d843c031034158003c03c80804559041e40c0e1002c42101100f001480d1601360024942d660040500d181000011100c1c0c6c8005041040401c3c0d940c4400d12042d201c2204000341d00e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155199721 1250 155198471 155198513
    0x509010c14011509050f070f02160803130501090f05100512070e01030e0d0f050904060e0115030b010f120b18090d0e0406060912060b060304140d03020702060304060504 74
    0x120301c1c0715480350103803812090240240da69500041428181d5100301441501c0e040c03d40641c40e21400d00030307a0480c0c0d18807903403400c5024000c071045400302c2140b002402003003107800950350340c0401030708000a440d441d00001e04000ba007182c01c00c003401450144000380d80049402c7c0b1400c141540e0266850f10032003000320440c81c075460400107100e0704a40d182403015001c0e20305005030b030022078850751110031450290021400107000c0b0300300d05200700003074042000041c00c0000d1450721240c0b1034150309800d0f4440c4400c4143c00d0403d103803250740b42c05034102040082c01d140080e6040740d0400340001007080b82c035003501607680c1141c014a60b5100c03641d41c201d007402403803102141001504140c03145107a070502000b280381e40102c408903003042c0c42441c0490705107668044500d410100008215090140160740c0349441c1d01c2c00c01c48a40d07803000218015441124500c3c501008030a4680c20107040e4070303014042c14414800b1402684594048a5001d54031150004072540d071490030b010b82900c0c0d41c0d40541a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155200971 1250 155199721 155199743
    0x102091003020d0501091814030903030c010902131103071b06020301080102070204060e0903070609050f060f070f1707120e1e12030c0a05030405120a03020d0e0606100509010c 77
    0x150750150b00070b00b203620304980e0912960f0b032180c1c1c08606a403002d12008007810400008071010600c14600007a1003c0c6a006691505845034006880c5812101d0544426550341360060110318055a0762506442c0502060100181503c01c02005000c010049403d20203506012000c2400d1385003018003c0d035008108545a5031031300b9885000b500700910480c0030310b02c2d02c5d4010802140044040f403042141324011483d10030389a070360300c0151401d550112124802c080074604400401c1c480540714030040701d5002c1880c5030030f82006015400c021195424400d01c0302200c284140025010342c0c0c020303400c1c10005c0c02900700000000c0100b4003002c8070030782c90244080c00899070600121144201031341c0f008444840b5400c100d00e060a01c0290b0311804042410000710213102c3c015000745500c00e005009544100c00081c550003495400341048400107030f40003541600201440c070501044d080c3c03500c01044c0c03a1501101141c0c90064045107041800004230300f40115a00c280180740038258002d10b2001c13 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155202221 1250 155200971 155200999
    0x30405130c1b05032106040b0a150e0609040c0f021b0916022b09080304050f0f130504210c020f01031a0409050304060305010b031b0a050403060e25050312090102010209 74
    0x9800c03800d8501b0b0384581e040213034115051418060207000c2c0c405080450240e0705914070203803240e20328800f09079004003041c00340989a60f030b2441400c40800b540c0c6c503070180d5092058030007400c4c048d08c8041b400c00d04611264103c0e0546070303241019800184040ca0b05080e240c81c0c1300903403410781c0300585e1103248606921030401c14400d550030005051324030f0315002c040035210100300e506d900581c060207801c00800d000c07906071858214640748200001030300c281c0014031001081c6050302e8040b141961269610b10100d2250307020035600081c0040f0502d041002120b455001800d4105500302c003504041e00c03200c111368041c5061000036008075008004200b84002e92800315180d0304548900d2001c245080000280314104034100e81c0700f14141001e2000505400e1101d4903035030040d400382400c000301400003000040d40c40c49203502c083d42c0b5400600100040c005840781c4180103090300c91b000d07006080100300a0f113000540e0030811f258103281c2c6071a41d00710310040b40240a4100c0c202d90114941904403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155203471 1250 155202221 155202277
    0xc12200f04020d090c0605430f110d02010e040b0a0f08060405010e03040b0409090804050406061d01050a12200f03010303270e06040617030405130c1b0503 68
    0x40c00744c5200300200c1000b541d65840c00c1c2d406000e29918004d80d0103540700f4504110300d8400c50f15003040c0d0520034041c1d02211441a2520620503150200da1100425078a0021b100f0245e00070094003000325110034501c9641ea00007401c0c050907110043c0038130f4a0704e0030803110342d484400f2080544240f001400b800740c1d0303510100356207600954045d50300f5440e007400c01c02c0e4541c2c044119819240c11001080c0b40501c0c200341c2200501d007411003581c05200900001c64a6504e6000c5c1c100107003c03550b00c0d24107688010070368454107804800351a041c81020845d25200603000728800b400c89040f03040c0050182417040243d0030310100c0c48540c40c0d040c017000805485071010070010710b050360b010359035444800390100640c415420005240100045140000b00444640721103e554044400fa1000c550640d8401400c02c2c50b01e072041a00d805600040ba00340041d091002980e07441000080b010f1201c64101100070b01540c80b029107034401c3c2204103140d4424098200121089101420200c41425141c59030308 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155204721 1250 155203471 155203481
    0x150504020f131d060402030622120309050c040507020c2407031e0201050f011716240302040b07120215070206060405070807080705160812040c12200f04020d 69
    0x544582c1d08900780c4001c03e2200240680c49194080c005081613201c1c0180341c540c0c64110030812200120f070f54070000004004061094024170341351808200c841251030442d05101c2c011514600503481c0400f0060126400648210401d0081d15000e2004002d10982c240d0054020144003822400150700e41c101640010409804014075400c0b01030313140f4000d0200c1c240c17081601c030480d12a03080001800b41401140102001c11f07507078001c0360110440d107074010386440070b143c0c0306041060080c09490854001d03112405002c0d141d40c68110720309070920308036400701d002d41348028040c00c00c0341d03a41d80e580c280200440000b010140079130b0074052a1001c1c00039920001151444d002e24100004500850301461140d03004090985503c09250742d42072085441c2d8026a002081c41e00a4035000c002265504004203202d9240b0510505549002d0404030040c520961104250b010015600d1b030109441d1110700300c074800b0102c0c19003404254100082d030613a410140745d507441480041e00c041410301c29402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155205971 1250 155204721 155204741
    0x160b040302010e120604120c05150105090a0606090911042303010f020f1204061808070c0b030702031c09060615020c01110316082b05090a150504020f13 67
    0x1a03e01c803c5088043c07000044040d2025030b00d5034050b801040002d002481110401c1e130031480c0907091031041d621042d282c0103152043da004c03c0312010051041c1e007003031004158440b5a0001c280080740c13400b42d000303140c4d9000c0c0c85118144c994603018240c103010a5000c49004140050030700c1c002002c00f05a40102c1050001058425860038406170b07140c81150007501c015103144500f660070401010b05010230044003c1048804507521300c15407042c11400030030710101398041c03034111780c031581607152085001a4075002208180c4062080040460340002102d400b403c0c12961304000d1440e4502c1c0d20060f114112004000608041000c280071881c0302e00c502d5000c00716400c545170414210019200b1940c180c4100d42c5a030000c1000202055411b50701c0510765226a08031442c09910500c412117180010107103489051800a04000d603048500445c0d0b082000d40d4013515964051383e94102c20400d498505181032034941c0d000500355030341c11004142c0007401404030100b03808001564401002c900f08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155207221 1250 155205971 155205977
    0x1401080c030c0f010503150603010603020a090e04050606130b0301050a1a0a050f0d0f0501020c060105150301080a060b0112320105030c0d05100c09060818070603020903160b04030201 80
    0x352002051500080a094007071000e040c400d0010040c070011122035100401011b00620041c28080007500c0f104002d5000f08020707a001615040b0050300100700011a0b889028444611800d0201184004c566960068802c44100074056100c0f0010300140c0b00440743c0aa2552030f041c100100b520b41b507040040d01c0844074000816a1814408100707400b041c900a2a0f005515000d00c88564204620103114490042100500314101c2c1d6440b142a41c4c00008494005d030441401000142001c041421800034003803e003606640c1089201d640d26130440030301030841c079102d01c1d800e51940d004041780384101e83e02c41c2c41803207a003c0c8808100300b00c00c4840100d0005036020601c603040503010000f1281600c0c002805010881014420404a03441b4080c00f500ea81c003400818180180c8184944c0303511180326110390310711500d0540090107a6030700910024500b480b211040c4050b031804240d42c1c0c1900c005040042e107614590000c24980100340400d41c601400390780020801700d03181005001200d00c00d913 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155208471 1250 155207221 155207233
    0x702040509370f0614010f180c09030209100602120702220204180b0307051206040209040503090607110423040f080f0a030911030105090d0e1201140108 67
    0x201e003a6958803007105408000c050303a1120b507200d2007016040640302c11142202da403450031064070f80d40302100450204445466541341c01c0940c582101d00c4860040402c00d0006010034505129034002c08140d4940b040c00b0b40d03941c01030659150090b0201c2000e190040c0c690a110318044080000c1c0c071440d03014440140c4a04000740f02480030383c0003154a0a0750141c400c2e660903044000e503070f1040682543c242a100d400384404071380901a002c1540034180040c1021070382082d51414141440744a030403250017680e440748049004240046c07080d4000da419101c24600780d40c3c0e800d0450840c010050f580b40c1c00a000122081408800402d10001b000100c8007003180c0b02803035001c8e0705002c4c0d4030612000ba801340c0b50000b8000c03401000c0000390150041d0121031030f2191664200d08160301010041e00071940e034040722400c0c014004801603203003400f500201701c9410000348030b84c2da80c003000b42c0d04403c00610704000851a11010f0000c4444c002c004000e110100d554801c045000900340100d91040c8110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155209721 1250 155208471 155208481
    0x70b0711011d0a03031202040b07050a0b0702390405181509070b0d0e030714010c03060807050607031b05010902191a09010c12020c0a0f031a100305060c07020405 71
    0x241410302c0d510a80203284410003451907400707464032103a40c140d200116a00380700000d061071484006016291182c0c002c0c04c01c002e2145000d0720340000c0644080c08661050444076501006480b454020711010010800740400c8444d49001030826604200e400c82d060074284058404404644805a0b00304401c7d00c9291103102520303412000126801a1143c0c040c4200b00515201580205811590070341c011409200b0480310501d035920a0350101c0f40401a0300c00c0c54942c2030288a4007003642c565180507c4070615000c0c0044c2e4400c00703030160500c02d8500086220405014501c462144000320008004103500740c00c01c03c0c02084210002d034001c200e550510380d4003064007096501540c200100615800c1e4072200c841d80c1741e401845809061180f100130310b00c0820400030244882e980f15500404a10060400384a075800781d5071700112100e10401424400140e0085107584524074412802085070b0303c03900703803c80e0310b661988081c0550051400344075030845180c00030010b6600035107050020b5203403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155210971 1250 155209721 155209757
    0x30b0108010e06061c170f1b06090709050603210403050d050a1d011b150e010b090402060d090f0614070503150d03231806160305030603070b071101 65
    0xf02c07202c40c1d1041da82114544040f40820105e003042d4040d80d009405048190071a40d013681c84511f545803002404143c0c4240002c05080324600d030084034024020314105040495900c0f1402d0092640391601c071000100e054400300600c40c0c008091402900210100c13001c0140b841d030040c00241ca050048183c29152a8003407011189c0e0f644d066512080300001c0751400040c0790500c0380b42a810041854408403d0544071000b22010034004d101016205060040910445101610162070f690401088481690303030070b440303030f640550180c800a546030800c1140340c005024007030707009010f41c2007801480c05100f0340d944081003a10680c0038265071519140010b40e020700088400c440050b1001c0c80022180c00c0244641400c60312a0500201c02843e0700460345140d4941c07550407440a0002c1040c01400000480614422505495880c80d0980f01c0c000d81c030b1140d10500015052040000c04501580c40800c03c0b140240644000b0700d48890440c0b13485401039859410450001e406c00702c014200001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155212221 1250 155210971 155210983
    0xf06090605030a051506070503030906011a121519031e081b1c02010c120504030207061d0306040804050f120d0311070b07020c03060a02030601020304030609060e07030b0108010e 78
    0x1644841e030850341c41480003c0500343c01000046603102400d00c1c445030b43c403180041c0101500c0740340074544926010a00c03d103003800c164407a4003070610602d64000c5c0c15408400706c8400d06c01400e89139031107030f0303c0c6800c0340041d101c0342c55815003140c2030640b00c82071250503d035003005603032048400100001600800c4024000c0c2040041c0c07141008000c2e08000944803d0042c4190b200035094894001402c00c0c40700c0b00c40c440c0380f120700150b5110b107006c0030b0b40c0e42c0c002e01c094050780c0692801c000a04150b180295500d40ca07000d00300601c409108815008201405a1100e00c08000c04842d85840d1500d08a0315540046c46807a0280c2414000d00c081071500c0f256909451400000800152402102c21170107002071303c02002d01da580400c42c4602160207158a81c2c4070f0170294001300b00783e02c102d43c141850018002c2026000d58418000c0c815240c6c0d02104440440323810440200d019001810254000c04080e40d40c504944100d032000001c103c1001240b504944a040003002600301e01c03040c2941317a017 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155213471 1250 155212221 155212229
    0x10303020a140d141c05010b09030132060105040e01090b12011e1d010629040f030f0201030204180c020f07120803040606150513050a0b09040c030b03010f02040f0609 73
    0xe43d13aa081d400201c6584e902416031a0303411000a01c204480044072803c8810030303000401c404800003850141810f0074045c2078400d905a1105624402d07201800ca40031044408100070110340607804281c16a22410580e4090a1414001c00c041e5948107100310040c098681298001d2102c0040d5a4101c0d01c1031041d15115003604d07500100f50b003801060b030402400082c4958162900040d0422542070302446000040c02c190000500c00007005501c000305060030115480c90400200310034030004c500304c03030f40000322036000106102040452005a0190041707400403a14003c51460194144601e40c0002c0c41e01c410540a4031008040e00150310703103c5619020f0108003290108010002411200c015680710f40106000603c654550700c0c4040808150724904000940c0801d13040d00c280d0b0701142040040c0400c4446004841c03500782072030414091282800e00c035a81da17104d4007083e40d009070003c03204140018004c00a031801c2142030b8000b904a806006030031034a4400110303415003e0703542d1030b05076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155214721 1250 155213471 155213477
    0xa050403200d03080901110a0305060a0e06060703030b04091e0314040807051201060902070803071e090302010309060b0a0b0714190807050307020301020a0503040b1e070c0c0806010303020a140d 85
    0x440b0701038400791101d001c0a007089040b51f58864020010300d1000300a041e15555940d8003056030b041680c104030807200d95407c000c81e072801107000d03c400fa44d180c2003200d144170f0340f60401048603446803000600074110740d48040c08640c07071040405600306000c0a070001e01882030321081c10124508800000318052401003115a503c24a003d000628122a1811050300750100100b041a1503022440c01c1e0381100d00f0443e0b00030400320901c800c41750880640041544000d12198200300da9900042204800e41300190526507a007207008107101c4541c002d2103140d580030f08005111a80d032030442e0300d15407003004161108c0c04101d07442030380080040360054103104c4103d100d410198241c1c41c1c141c234030307130110f0011503003840100250030045c1c5007030010f08204002074030303080d80380c0c40c260904800c94a401000300031303100311507a041c0f8100130401e00c42541105240c940f052000700c20f841c02c0c00d05520150400c4949208000001040540c0018031a100c103216140c10a07058a0354002c480d511659440c140000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155215827 1106 155214721 155214739
    0xd02040618080a0201080601080a0f0608060106021204120b13150501030c06020309010c170f030a050405010b0a060203030103060c050904020309010e010510140405070509060a05040320 81
    0x200a0b84001e00041c03966580020b0145000809440c1407182082c003081003d600303540010180407800004000c226120558641c0c0d40000b4801c0200501c00d07002c0310f20a61021006030390450300f028100300b4414101e5503a15004030ba000741000c2200301c002c111203000c500e51142000003d107007501d0001e059419401d10a4111032039412440640d4010820f00b80b40e070b41c0c01580e985956402c00c021002110900b1141c0c403640c41000c0340c0d0104036802005004120116601c0340e80a5445400200049110700003401003c08440c499000582c000f8001000801c08a412040300305810b032406510340b04550700054102e03041a54113641c980c1d519041c09180000910400f03030040e42d0040c048036101c0c94002040450b10384d86c240315000716150001308001030300650070345d0985003000b0a26600e07100710303001c01401ca400c20710050b9058504080380014003c08865145007001c005400020 = true := by decide +kernel

theorem cover : BRFrame.Cov 155035971 155215827 := by
  have h0 := BRFrame.cov_init 155035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155035971 ≤ n) (h2 : n < 155215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
