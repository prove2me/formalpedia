-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4988
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:22:43.926473+00:00
-- url     : https://prove2.me/submissions/db432e18-8fa4-420b-bafb-5131b1f3efe4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896942446 ≤ n < 897122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896943696 1250 896942446 896942489
    0x7050c0603040f0308060901050d082d180411030402100203041d180a1709010e0904030f180f0e04031106090607030609050405060a020708120a15050301090c 69
    0x84522965019401106001c14003c1a41802c99518800c1e00c8111040c0c0703800080101c029024441c40b540030b0100c1c01002c0005c0e0f07003a006090b00000072190400801e1300004407507149603003081d0940700030401180e081c2007100c900400051103002901c0412080c001c1340f140318414480140040d00818280030b408803d28820822200141618480c54480740d0003c080e0103440ea03c01d81301c1007a10b1807120601c40744014080340309002194080f18880000c1c264800d030584c0da401c1500034234180002001e1540203a118140c01c6840b9030f00c00c0d903c02c0c0e4062135409014040d883c2c0b0880d0340d80d00d956044c00030b220003401c032140142911020220100c0690791417604039507800540352060100c7c05080c0500582c00e400040300c60190303d882d10280308030380d110401c071400c2300c6040ba0b01519550240d8003041c10000140d00400445e8000c0316014034118103644c01c401c404105440700c8405550362075544a1240ac41c000e00400f81a04400a1225000980b64130b0301000890084001410300d914244985 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896944946 1250 896943696 896943703
    0xd060507110f03040609050909060a0f09140106030b130c030f0f080d0e0f241314061e0c030412090f0b0712050f0a14070221010b100c03050705 63
    0x64071448412034400c4070412803901d031640c00c42e1145c800403501e400400701d014038040315074a1041444000410701b035940d80315203001030180316800c4035003580e03103a4203038000c03515940c007054800d0341e80c00000c15190301c0c0d49800c10414100800114500d0b40035a41d140000d040040b03c0780031250090b0200101503007031304280c0c0c00f80c40100b100034400310340000e0b1030205810a401c0310400810716010b403051000c4000c4101d44604964004c407181448400700b800c0381842d00d4424541203038882e0404041e0310440d5840006110300c8542d6464203a0004017081105084010f000d101904131074481d64007030070401c0c00e82c880c0c2c0c00050b0008081c48c554015503049584226a500001c0010301016003c0d00d41e0b07080080c20b96030207000d094500502c0310f041084198059000c496611460952103442c05d802444129005030408800300d0002d0001c00c800e0f800750380c66000503041d02402d1003d00e119000b9104c522801c55010303c2842e40200e8010250042003900144807110b000d03058148103035146441d1801604 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896946196 1250 896944946 896944967
    0x11040b070c050a03061d340504060e0a0e030702100804020f04050106050a0e0d03081906262505040b06070534030b06060c03090d08190302090d060507 66
    0x8214410f4400002030180680054840d00045000c000304800c0c89100191981d013042006070801080441c40d11400000701c12400d0014684e1f030a0700780f4035807035100040c19140c9a50018203440c41030010f1210b01400c6205000c08070105200441c031f441915404144010035141340d03002849034840000303066440d03500d804071503201c0051007002030303685400d00640741c1e4001c0d940c81340016335851421392090034404a000d010f10740645901c0065561400356032128608201c10070182a01c8400020f902c12120740c00c46162218004100c074682c01c840b01c13441c60501044444001c0e500034143d4411039599603005031081d18819139003c51040d2038100414580d01c901030f001000c40c40b40c561401c400c2c00641214056140e6400f076a940d602180308408a034168a40c00041d05100100d000710380c0c14940b000007030620b52441c00903681070885a00001c0d050509506040c4c0385910001440070a1f104003d402d0403c034907040c2401c43c2021070303010100b8050130403a00c005009580c1c41000c50403960046480a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896947446 1250 896946196 896946199
    0x7021c3903080c16050904081b011b0806092a040803030c130b071a181b0a0b0f090609030106050d03030e10051e0a0b131b0311040b070c05 61
    0x4034495580e1030491102da02c18124198240038a5440602c1c503010000d18a044400003440d103500b9841c4d03922452025400f40c6400c6e40c2001450044a821141c280158034041c2006224549040c02d91040138003100002400d2078130a401440070040c1040320703980c4050228210f07501c201d12806c24420408191f10681d00084042d110102c208500e8010b900001c020301c03171207001d01c4039042e035462100030b0780c078010300100500b00f1080180001c0107210310200d85511003200000f900904000c0c10031142070400f01940f04901c03401d14040501d490501490f0f4000a01180141e646010070404c0484d50398000c0001340c42c030030304000848070015682500420041d2500404040b01215a0310340a0700400319403004c80750030702480d00c0d600c0342c0308603d02c103040c0304600030f03c2403079030a03035810400c3d540ca40001019180320f5690303070784968865204c801a4038034030803a21200160051120204040c1c2e1401001c00030201420b040c0b8022880310b4039019242242c0700000e540380c44603a24942405c005041c1e4201a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896948696 1250 896947446 896947553
    0xe1806010f1e030b0a1805060418080304120306090507030b0f0108070905010809030706052a0406080f09070f1502160609030b070201060b0a05070201120b0a05100e100507021c 77
    0x1010024140d0b000c1c7e4003447d4111010040081100500c14941701c607040d002e01008010701c002004a42032203c40b0104120342c0c50000f800503101e4071400c04560007a00d92030006660390074851a9414240380d9500f1068090905503a180b410700c4008148031034078040e003410032100c14040398100000308107a900352688410207002d246002102c1250109180d81800c1c0001d05558071003180c2241c1d0000c603000d6503d0740c2da40714403d64651925a40c844030103000e00c0c101d84110700001481040c410a54005060908203030104031001410081c900340303025090f1280c10744d95440400015400c0111b2008581d400075010010390b42d84a000e9006002c03c1e88441404640080e030305080d60350100003005003510036220302c8025002a2854011128805112908054420b005100300e1402c98000010703c0258a416907849182001081828082c42108004a100450284111701d010340392010070f00c452214603101192203407560b001403509c013045501e4208080119401d0b12402c41d000f40365031042d0a100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896949946 1250 896948696 896948729
    0xa0b0c031c090b2d04030e10052d07020904052806050f070207090e030c19111e01050d1b0207080606040213030209070e1806010f1e030b0a 61
    0x500d0068942c11000312603c03402c0c1e02c0060603505040300044035250441030a400d00050460600e042e0003c0500281c0a03c001480601907a40d80d42421489401c8555281602d170354994050b122955000c0403110074481414841a9802448100380c803000d980440c0c8001170360300d480c14064103203801c071070403140390481c01a80c450405803805080341302d2502c1000d08020b0b642d034051184c100701704151411801038206580030001c0c6052074100b0400d08081d14203403440c00001c005081d00d00741c9030801d00b00184000d04407000521482c4864030344c0040c01034824660044500b029688071071a2050f0440c14070402041c507800040e02980701620300303400240b24905044c032042e0043d41d20000c51041c42d0491003600c0001d0b5072030510340243c3c0d6400302c0e01c8844414881c01c2d58200b1040c0f9000620180c1001204202c5449a9035000e40c40d0340c03400082030016202c0d003080400180b0b0300f00103d8405040c0004a1410b103091102080c4094885c090f915000500000400000701c14402c01c1d44502d02c6101440b80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896951196 1250 896949946 896949997
    0x1050d02030c16061e0e0607081b0a110c0d05030a080c0405120307110f032a03070b12060306040c03151d030c210304030809071206020a021b0a0b0c03 66
    0x160b104a58200c1c643c0b80c185c004c4080d00d041c0c801301c10044020341c1000c0d0110300b07014040c0c0342c4640c0000328540755418101e00301034045000d8220584c00c0b80094040c0c1035140d1500001c0c0328089200760300b602c04601e080015181c40c3d40e68400c1103407150412a505002460407801c00b01684c01a0500a000804c26008a00581e03600c2c0c0081c00d055861403001a40040d0902c2c150880b06441e075000790140034103114101527109030000348020407000900d4800540c216070307024441e00000e00f8040da2400d0b1501e01c003000314041e4400050440d8013940c480014000800c1d15032450300704903980f0050004203080c41048002c06422514051060360305014007424031014044042c01060721514120364200d60160041007075202d0b02c1d146030000031010130200e00032a104080c2203510070101c0f0116503000b91356040c41c8810020340c102c282c03840d680c041901d842c1240d040c40600c0b941002000403030f880d500382d100000c0c86c041c40c510a50a5154002880d150b60610620a1301c1401e0100303107901a80c20385560 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896952446 1250 896951196 896951201
    0x6120606092117280f0324060f08090c09010315020d05010e01170601031703070c0515010311062812020c0319050a0c030f110a120f03090201050d02030c1606 69
    0x8001038400b4600182e03000e0110004e02c046500d18015514640c03403071203411701540107140d46880d4105095241081005ea4001484000c009041955132495a0b4a282d08000c01c62107002d07013250459008001001203641e00c0c0329080703054035049900d20b414500f0f1052504001c0c491842c801d2440c608000001820500029070755040303890880300d8055054949207980d0700c4a0703090000601c000c42c840b202d0389802280070050340d130054450425520505454640b40d140480d07011001859481440c010300c1000100d50507944808001c0c0c0c1d070182000c0011a4250000043d03000c60b8a000c44035902e010741301c512a026a40b82095400e20466568020052003500d03640245207100b100090b9040003109188280300310b5103144403642e0f540001407101c0d50222580d170240c0165804028448144c2c0319800c8040c040c4040703540c0f280940503121140c0c0c0c5406070043c05488500c40c28113203001c0c400805071340c000040390001c00003183d0041e82c1c2e80e1500300003001030050226010106c0e2600c20071a08009096 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896953696 1250 896952446 896952457
    0xf050c0118140f060f0a0b030708010b030d030b1c03020c0a0306060504060b040f09020a090518090105010f12170c030f03150a0b16020d14010606120606092117 70
    0x1106010741e0000102d41c05960f6010b103000e00c2000780c1c403210006800c0c000c0380c03024075001002c0413008901c04a140000a261559941008c12a655030f40714094107440e0402201c03903840c071303241801e0000b01000c20026000e04040b45500d0512152801d051041520900c0040760f01c80e0001c080300b51154403818440c004103018041e0728025841c01ca80420800044000d072411501220480d102d00b0b400e08040d84082c0d003180310150244005000c0c00b00c0c050b03450f420b41c2440022000ea05002c80d180c4042103500b5540182c1c03000340400b11416061000240740c02400c042c072500500c0c0369103015807605462400d4420210512038500002c1022100010303803500031406a030010b2094a56803c4002c02c01400c0d44c0c1500c507014030144100403c0024141e10f4110340041c900007420402120b623661134203440c3da44a0320655102c0d9640d40014401c603900312004d00c01105a03510200240b50900c0e070050320925181c001e480c0c10341c0c0c0c2140705824928921041c440e801c2e51101000151b8184208040940c0e0080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896954946 1250 896953696 896953703
    0x11802010201050109050c04030f11090a0203040501180302030354030a0509010c06180819020c030316020307082401080309010f0e0a0e0f1e040c03030f050c0118 71
    0xc2a000240c0035a040c01440d001c3c1d1187c0540d103140a14550b20300c0004000c40400310b03000c03004030b60041020b64402107400c2c8038500c2c0785009a034a250501d000c40c04c5031247d042d00603100d44c09181e4100420f50010640b640048400d0441c0d03482405c41c40c1840c0d0461200e4190180c0403400c413612004c0c06036259004220700304080d0114038021114002030b89a014000000c4e001880c1803101e031004d5031003665404200d034015000019008070040c68002c0c854074000040d10f10721030000b0040003180c0e00c41091100c1e080b49201900781400382000280d10b80c403031404014212164040003909640e0240a5640100403003001c640650719890701e200305041e2200c07041650103410900025250300080704507060b03884165a00320030424003a500b030721040100b921040d004050343e080840e090381c0b05e0784118010701504064a084c0c1c5402c81c146c0002151180051800c80d000c00288800108019079000540e0781c582411240d07020944000c80705401030703110151441d0300741010030105062201010a80501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896956196 1250 896954946 896954951
    0x301020c0c1c0b040201050703090909060903081005090103080309010621051606080f072c0901060306080703110414130c150207120830010e0105010905010c14011802010201 76
    0x40300780e228192082c4100028140d08000400100190b1240d030041c2016071103800c18606c2c558503040e10b182280d4030200212841580da5412000781904180c1059208208802c448005402c200c04584d01c0d05040c400240304000220229001c0c82080d0003a44c0500030200c0c0f4100d0540144036004105c03901904255058091090035112100d0310516010a0340c5103a120108a40c44103207200c0460301004001c0e00412001550b201413802c00c120700801e0000d1483d03100d901200c0307543c04005082e00c060340990706062070040100950b03400450701d241202d800488503002c2040c4000468050104042a0341c000140c10007003000da20381048080355003901451964540316100c40035140000029064000581e203c24020003c1c4116190301c0c40c40d01c0d1048150380d05105802c4d01d07100459007041000308001502082e4052031600c0d65140c83d0040140089540703c03540741c0400a07280350004c0c040c6504002c010b8003003005124409a02c4032003a039851008000d8072901c03121070244032440c00e000300d00550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896957446 1250 896956196 896956219
    0x100e010b09062a1014060316030b151f02010f0504150c051e0408060702070303170601030209100201020918042001020a140703210c020105030a06050301020c0c 70
    0xc00080e644400d002410382490a21041040c0382005012a540c000d100c055241c038400c1c0d01c03018003071070403114032000340403590009010340c00c034013508020000c40c0640d10124207100000440c0902c601143c0c1c0102c20a0159102d010b514800b8001168165401500c910340f0816400450b120046640c85280e00800c80aa00c0c00c0c60755040e00c0c01540c02038080340302007102440120b8654072030460341043d81402850f02c0c02031140c0040161207901d0102100001040401001500384242c591282051010b4180325083d40da010306074089030314020030742100319400520b09900980c109c51030404000c149500102104200901030350020031102c0c0655010010480035210300c0c500c560040794805c4016450b010b0500b8501046140300789a54114030401c2c02d1036021600071340721910001200000750411505508080800241407409030130f00e41580b035815000640d000e0503000303186509107000b035540e40341c08041402628468000c0c136890352000840c2c0c0d510010001d0f000803070303000c113451450000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896958696 1250 896957446 896957459
    0xa03210b031c2c013e0c0d050c0a1203081b04031a06040f02090f06030a15030b090706050a050a0c0312060801050406050c0316030c050d0c02060f09030301051c05070509100e01 77
    0x13850b21845c2401801c0307030f0440100b4600d90145080aa56201408860304a0b44031000141045c0d982e0b43c00395000d0b0070958545900d800e01240950140c0048070341d0003000d807001c0d54000c107040c1000340303118554480584140107d42e404401c1705c0c0103640056500705100030710348080100b201c003584e100c0d125510f08069804484114020b41340c40050081042d003000c044041032002da540300070403076440150703501c60300c880c014114401003028601440c000c09061904c80f8603e40780400c1d54001030300744101800b00c144510303841411180038044614200b813050400d494259426500b07580c51040c05820035201080302e082c1507001c5c52040b4081c3c981803101f5250b90004440c5407000b55a4501032003120000c000c4040d0203600581402019441c0040c035260030810800d08903250b40d0050b00060b00282c00b44103119548070302d00754102030000042c600d10352500c0005407030780d6002d081800c02d281804501a0038014288074140007440c01405c3c85103a807400707025010366801d060103007681c0410018004940c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896959946 1250 896958696 896958737
    0x140403081e19020f0915070c1a0405040e1e0c09100b16080f030705041e2402030409060603240e0a0902040207050a03210b031c2c01 58
    0x40244189442c1405151440c6001070740c410041c031100d4120400c5820016125650b100346000f205110759500e9201c2840c04105c0b02c90395070300008400c2001c99803c0c00011260084078211102100d00040b44511350100d00e04042441c051320000080d04071481c0100c0c180420300000f80c0700304035010119a598058129480b003101e000e04c1100120138080c070013984580019840b101801155580d0030501f0700002c3d4600c6610854600d000524045403c00c4006403054081054105948000300c1403420003140f0a409112003c1108000076910b0031024854001d004036805003082c202c1c02c1c042c084c5c5489029000d861250480416111014107402810325034404041c240ca4140d107020030180c8404503000098891280c0907a40300333608100c1017000030810401682c585203e17031209215a540d04101801d101c410f544c1b070440382c40c1440d0440030944e03800f10340140240c41c05c02108001280429044030030040f43c03a4010700000d00d50000e030180034403074000d854094a09070b03507074048004c104100104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896961196 1250 896959946 896959951
    0x306090612120f1b05010c03050c120c09040b060d0b0102070503120a0e010e0904120305010819080706090f0b06040f060605090f1c0b0a150e0f0604140403081e 70
    0x820400240502c8252184424003039801092410140b60f41c032a41458039941d2141900701c6041c0e5480017003000b451b8050003036030390000c807a03007c403820203c00d020b46404549000306056202ca0740000c608007a540e42d58812665148050020358071141841ea20700000d02821000c40c4c09440ba40c0340010385450300041c840c1050780e10110041c20000c2041d01690000000c100c0281486848613405909482d044c0d0f58602c038900502084542c2590040c01804481d4181c11002c0030f50440d003d04810944020000060154041c81855aa403001e04080004182007030000b4140e10302c0450000902c03040386801c0d400340d8021141001034445404c00c202c00c8030303898421030f00860b00900400340b080c034114040d9410448007422100000c00b003006941042c0080d01c40440745111200e080c403040800701d10071000701400c905401d40155040c10b80f00350707503410020242c003000300202c40081c0d12500c89070843c104003a54034050410f242400c0c60081c00104080328440450341c5104409071002c0d10654400b0b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896962446 1250 896961196 896961203
    0x161a0a051e04081204030314090316020d06090c080d0807020d0e060a1101060b07050708060103080405190509040b0414010c050d0911030f07030b090a110409150c0306090612 76
    0x100a9030000000759158402030054a00340d5003132250b8656801c0d11300d00d07580704030300c0303a600000c0500008142c01d04e404800303051020503503c00d10841c483c10081d001c080b00301a80445200000031814540b00c2c01034612010004c1071000020800a000b6000003031245901c00b240d11000a103680e000030403695403050100c1e100010350010800340c02c905000300208103050b82031800d40307282d015401d500340c02e452450340500c03a04140065010107112042c0f103004042c01c4010050803065140d51603d02030b0f80a82c1c042c55101d05407484500c2842c91402103000c004220240c10a403c40c900380c1008a800340040b0360035915118000300c14640f031750041c0f00300f410710081512401d0821900741c005000078240c4140441da44283c40781c014400da44e04000b1650049030100040c641e039070461901c148008405000b181241e8080407401d00090400310f40010701075402da4000548505500b0850001303202248018803c61405500050066041d0061001e843c88400c09102d415a200d2100c1c070340380310303043d40503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896963696 1250 896962446 896962471
    0xf05090306130f0506090f07051807031508010e0d11030720060d0e031e04140f0a050603040c05120d1d0114030a02130e01120f0602161a0a05 62
    0x180c04510210b039840c6940340a0400e1001107100d0355212450b0040c192072a852076407005c0060741d400d8404001d09409044c0541c0c20a690240d5182c9541440c04007801c01400c1c1512444006110025418071000500c45030000340003a0850008690325080c2c800b451500013840c00110800b504800001c0700c07040c0c0c4c1d12208400701c03c100d80390307090282c4440c0c000300f1764010410048211007003494001c0d1203980fa902c8015545d101400300d0702c9244500024464034441c00144810400b619042c0045803410b54260341c50240e2242c1100001c4800302c0d140c110310760102001c02132005110030060943d00344caa06882d0031140710000304442d680c9503080801c0d100000d4660303002c5580107403903001d038440035001818100d402c68044040303081d07107400441e80c05d10040d9000c624003991440c021280c030020581c00d02031021a5040101401c07100401d444003030074120351100044108415581120b43c1c00c28010080f01100300c0c20725140c642e42d082448400038080507080410040c4895110301801a08490300e207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896964946 1250 896963696 896963701
    0x170403120605060406030e100b1008090106090507020d030609060b041701020c07180c0e0a0b130b0a03292107030b191b0f05091c060504030f05090306 66
    0x840d10340d090802218511a1542000680c41e00c2e07100261010b00000d0300c1c00704084141141c04e900d8072441092071203085041c025600c100d40c49020f0800001404c0e490480f0542c1e441d1101c207405451550b00c001003d40c0b6083c100011103134007040446d4107242c00d580a1180c950368106650540c6d9913400750220529041008011012003078058004078056440050b08000034a200365041003282e60107418000c0209a1024003c081440341020303640c40d81c1041b00c100d441130702c042075a40d0124050300480140c00148204c0d94151006800000c10742e01090b81d6940001c05e40080140c03400002d0500e9800344652540f4142d092801043d81441c00501141c41061024050960809540e44580f145016410000c4042040d03110140c4c804c140d0940305e04040880329480d6012541c481d82944900c0d6060008415210340c404001c0d50340d9034251610b5034840d5a40c000041204184214460f64102903035090f104200054007c684181c0c040d444e20ba1481a20540948a41c03042e1501240e060300003100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896966196 1250 896964946 896964953
    0x6080303061306090203090312011e050405130606141002010203010b09012304140f0301020a17060a080a050a03021905070501031a04390503180a0813090c1704 70
    0x2d41c001840b44445010441a6035444030500b26403066452402503080010a149820440d012a86c014141c1030b410004800e0820246440400103000d00b52240c1d84800c003054216041a9030700c11040c0d080b030002c0010aa6481580407071940c10034409005910350102e910b0402d006200742d038101c41b8183c014034900801003004407260700981640b01d045056a01203000598494400303440900000e260500c080540d28003044144042c0c0756110340f10f680104106031203223601184000c402d8040d07031055400b5807241f10018402d055540c01c00c5400b4403170104000244000018281803140c0a034003583d06621014040001110000c080501164800c0e4420412540300741c0c0410501076445252100d194100b100140646c7c010f02610061400c41b084007001914140090642c030f02240c1d080b459001d010030301d02030700500004140204d4010a03482e40481b0650904ca0510f00c0c0707a0104209664203101206842a03c110f030240b82c03601880d05d000178840600442803030084150754980a20699195903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896967446 1250 896966196 896966209
    0x105090a050d08192c010c1502090409030314090109020109060f03020f0a051c0c09030b0c041706181914100f0207260405060d1104060816030608030306 67
    0x1c6080310020400c20403600c8070a80d16802e00101041c5503074178000c0c0840141411082c00450030810600c400f241084a0683e800901304102d5943c0071b64825048101002140c000b4050320644542142c1012a01c004040e81036110b00c0c040d1250751491070340e6494034003015080b16504c890007800b00d014600305102503405240c10000011107450098500b00120b002c11407603402c00b0902601150000c00d0320500741815201d40e03440f11110017030800c050042d881c001000c51210744009001ca44105c00416140c0c54040704036005044000780c912071480307001b1451070762410220352499040f071011914145503030012418161070881140321740341002c2d86845070f1124480030b40e4065114820f050116500b142c2e54047c607440c0c2e922000c40140c5440481c14410100761090a1082c0500070100c400808510104140d40c16164186c3d022900c607a041070780100100005104250051004600060a0b9030300c5200d062080b8004000f404845c40d008106805a0f8414000c0100d681c00500001c0c9007070510b407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896968696 1250 896967446 896967469
    0x40803040503090d08030402090a0c2c040c0507120f0c120201090516080c01020303010b04030f0c090906020a11031603081f0e0a0b15040302011803210e0105090a05 72
    0x1101501c0c5014201800130782410b9407000c0460340c40001104000039407419500307040d4040d003001c8040c0500e100e0340308010900e0300b82d10065080d28071085650b1400a050b0740480c043c0c0030000c3d10030403194942a8000d080b5410142c0e0803103040b42e00d00b00d140b4059201d12b80b010702206254070790010312001613507880340c04010341c000007085642e26880d41000c62001c005402142c1c0914003081d08960814509500b0200c420000c14155401080100040c281060445040b29040780d038030014544580b0b41500c003140c00b0352010344007030b0410300007400b44081a4000e05270b981c15a02c50591954075060707585c1d124010112a9041214140700801c0802e000d0003d180d84100c0348500350030307412242e0291140c00041c90f08125441c000000400c00a080544650514039004440d2080c041c1e01c800c1030081c4510890100a04001c8a40e480900004080703906c00c020795803203401103100170821060124000400c03400c440020700c4155806c845940190100c030741e160000b81c4000d00f01828078060020460b8403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896969946 1250 896968696 896968703
    0xc08061b0f040620011a030c04091e0812040302160609061b0203070b0a050c1e07230d05060411043e0403050a2f010c05010603020a151206060804080304 67
    0x8041181c804c503020700c2055400881c0403a1400c42907244400c0c5403070f2241811590380107a213003c003000049040b00c100041c40b00710402c41c0c102402d144e4503000f8120b00408a00003243d94112040c482055000714522100707611050040343e4869a94000301c0d8880f0013441544041030b5030307403280a4056074403803000d1010f60000d81225046903407002c034a40785601c000d00d200005500429428001d01046c031030240d800e4801c20759640420342ca250019103d03541e9114020b1300200581300c0440e03030081c9013000c0b0040355000f0319480100c189030411903142c0c5c3c42100c0445e0b200d0305400d446260b505e05842500000702404030b80488032410380f503484002e107480307481c540310036080e24202c424003094140041011f548a4000340410380c1d00c92506c3c3d03542d0b801300080210b840d20360301400d03d8400012020354501c84400d2910410050705400c0c013500518040c2c001070740085e01000c0c041540386044400c00b060030b0150741c501c040e0f1241e40154404032000d5014001c0007a0448020034082900c078805903070881d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896971196 1250 896969946 896969987
    0x204090203070803041413020a0e1002070503100e0f0f2a0604030507030507090b0d110f030a0606050f01050c0309040b130905010f0c082e030c08061b0f0406 69
    0x303c0302101440d50b00280e005800740c0104080007a030340d040081c50302600388880c00040d801c0006008015011400c405800e40c0911150807507103801c0b03482005902c0042c84050162802603081604000c05020003514009444c4900001c00d546103c2c0000e5284841003818050840036201960003090a80034081134510704008071443c8081e80c1d6100d0091006500c00d100504400c1e00d1403134100d04000e00c6031310069115180544460507921f80300c00c0001c00c2b03640310808451031a481000100b44032032002c142d640610940304850100140759000c0c5080e101d00f2141c0c500d43e507189400445041c0301d440c1801e0b6003030308140807020715814141c0004a1649005007100c01e00f80d00e8280000c100da4010f001552660b4492203031040d803a082d48a4054102d09602c1c015000c3d01d0091030344480c00e01380400114148915014440f40c1110032040c1034051580440d05440c1141e03141300c403070307a10030040d906855007040f10400708500d40800c2c012111075020740c403a003904162070240140c0f07615070b0303080f216046035a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896972446 1250 896971196 896971199
    0x1a0405030105010816050303030c0f030705041e450902030d0c1b080c0d030e042904140703021309290a051507020d0b040b040b0f0f0103020409020307 66
    0x36000e00500c3d0180001038010003202e82000745407111811285d020324040c0e08200305102d44802104200c1e0101003c0460f00d81c0d50380c0310018115860f118644c4608464141c120091071f20f09103c074141c404864002c0603a8642c16010001c40516a074907200032044002c00c1540004200d00103000414042261000013846101c170303030080790400d06088402000180503603224800c008a04000c3c440405810b0713104030143e400c02c01910b50700c04000660510801e03411492000709440f400103000d22031400b030000d00807038862400c8207020300310f0841d05a40f00f42c0307000706003140340c2403134421440486540d86400b030054071090303425030003584103800803c075605000710302241120315801001490746520301d120794441d4090b00c2000ca4800c6000c4600e20504081008000c1c61341e41796242d481c6080d1304490243c0d074446510008600300b00c0000010f0807150901e082109200c41040340305c1c4524082c080c0309982d42d848c0c3c003103d900e00100b1a408580c5680400050025040607400820b41070310140803608040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896973696 1250 896972446 896972449
    0x30d140d051003080a0504030b10050f0f0d06020409230402011725050904050a0b011e030608070306020c0609160e0726100501020f0307081c050702161706011a0405 72
    0x185d12400a03030010407800201042000580c04071154004075410042c1103c80c1000001808900f024111501c1021800304541c120368036445107040c0e090340141c0c215038072580c80c070241b4090408035107000140c09020b100b001d00d0307200b042200751043ea4140d45800240c0c0703102d0b20403074203100050700c1041900c4140d02201c251500e0081c80da8000f2805803111130712000201d0801085c0c48000b80094141824a810240c01703982041c0d409010b07088544e003628080140110480042140d984444128030509100006100560b4000c0292109010039589566100e0749859070340c4014104014940780c0e8201d08100c540007034100765400000d030f40b23440c4819000641f103e240301c00000300340021202040081c4801e441c000c5100b040102028000747c020156070f8200c194580c0100c11b0094008a000038580c2084c00c51110703420403c8210a01c204582c1c20324440095840b810200c2c1e04900b0b0442c13100200311001207442e0a91410200c500030200b6030300b4910303000c11401d4000b031503001c0c0220601c000b0480307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896974946 1250 896973696 896973713
    0x6053405030703090e01060507020a03120507060912140304050d0f03020d09060510051017150307080303011802030c16030207090e032d040605070f06050403030902030d140d051003 79
    0x84500a544240605041a00c1032401c160181c0c0300751f091007020414440140c50701d00540d400c0782c2c1c0140382c0c0c4203442c80c41030094800d407146400042800340740000c0701081221106402c60388c1ca2071640c50842e4805120400d405504c020b0302c2c068030a51200c1c62400b201441207281c986001828a00075041000d074010050a4440c03140085440640311003c01441d02d82240c170f503900410040301c504200800d000ca010b0440d02080c0c801d03a045000c040300250700040e441414001464010341118117041d0f4030046a0340702d170000e00415411264410300070000c11003c2c001c1d20301403810200901d2904c0b18481c1b68110341e600c4904124254001d00c0030018000342e061040e41c1e0300402400165a440385a9143da442e0184000080410302243c4500f03d480d600c051004d0b10161550740c10701584d1802d017414901c1300740c4800748004207034030b04041c10002056815002003c3d950300c02e0341142d042100c41c5c6015200000c1c054200c031400c0505000075201704206401194004808203541c42c2010345903100e4484 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896976196 1250 896974946 896974957
    0x2030a1202030a06172407050a03090503040302060a0f09080c092701110403021305070813060609110424050d0f2012150906041a0a1502070605340503 66
    0x2183c014081b10000d00140700003542c00e41900d82d021040c070303162401c80a05180070701050a000c15641d84840800c202042040314040d43d0010720058940351150300041109501d40d10400c00581c0c2d00000182c1c1080014500f07484200c02010246560350303195501040010780c00045007007421804502102c1d890a210390b41030b40d4020301445a50714190300500c14a202c0744082c16801b13614000c00c01600540c0020510380090350134a01c0841d44980d0304240000c0d080715000b14050514080c00c1d03401546503035008104031102c1ca0419415200741c2e050784c00c1c0d50040e80980e0f41c00300d0710812050b082034040c1e900c410385541c0d00c00c400054401e40407210880d0781821a40b8400c0842002841701c02c821520911250f000500c03641d00201c4005c0000072804e40c0b40b015160074000d40d10b8007002100f403182e8202e01118940050150441c05a07200d00758014442c00355000c10140c0200c0c980420804c0c0f140c001c0305e8158101e0040b252061181d8201c0d1801300d040e00c41241e42043e402105c503000070300c0610007080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896977446 1250 896976196 896976239
    0x20f0a030e060d1d0d0903020901050904021305010f0e061210050c0403081201030b060306011202040c1205191505030a0210090509191d0c010804140d0c050d02030a1202030a06 77
    0x40e1035240c20806505c2c1480482ca110b040c000c080c1c0301000165184ea180328155074080e50007020b651504d1001c50110100001c400041c941044000710b2a001160a801c04590307404040c03020030340b204000d00c1000c1280b04d240e20803a0b0400200382d5202181508050f808c1042c02c00c140d0710b082d550f52980354254018035003540104410000410504c082c0100f400c0c2c00040c02c602030880c5524000580305100c2a030000280074a4960300020741d8503001b0140b02125058a107010300540c50002c000038628018010350444480c54044104500c1d030146d2843e1041c1d0318003400801800001360204003865404450703a0040050254010072240c60301c20519026504604900e4248408075240c241035442c00c01e0b4032965000300b01c02c0c52619900010305500c0a4801307081014090300c40c0c0c01c0c42d11690900584111981c420480c40194080d480844810058050343c2696405170244c48100c1c0c0768450300d004034000400c80345c1d000d026030070140e00854200144540000380d00e0b0b030315071024903020006580341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896978696 1250 896977446 896977481
    0xe0301150801060918060b011412060102010c030b0a0b07020607080a110709090f0201050c120f0a09080c10120e071202010e0f0a0b18041b020d020f0a030e060d 70
    0x700812202401000301401c080501440140968012a10722400505020b0000341e01d5902c1c2ca2040c0e4013a424185010700710b11880c540c1c46181252181515805840e443e005620f0058156102c511038410007680c980300030134038070074507180042101464100e1031090340c1c448000c00065000540703840c010100741105072592200c0903407444003181049803d5001c6035401c1c3c108031960700011a4000c030400c0d83c139030900700152115113861216282210181c0c00c001e1000c000149501080b5440c6c010300004100f80e501c1d03c040c203884051098881a8054055401501c2003485031405400b40011514003410450005840744820818502e0600c03c1c0d4071512070314440110703050a40d41d202c800c140b4072007026500301072840038540102c3c0d6070b40304911448880400204030380c0e404c0340e0b80c50022041050014414041180301030034a0240c002c045403a08098460360561444160000c14120682c0b609076000d004000c3c0d15441c2074454404188074598082c00c100300d00480c181262142c00320313010046201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896979946 1250 896978696 896978699
    0x90711011d0105160f02030405060d02071b17012a1707050d0c030515040b0102193203030411040b030d02100e0703050a110103020717030a050a02120a09030e030115 72
    0x880d44c074075103505058400c10003061220480580c0020443d01110340503245666644c8101040d50024056580002c2c0124154000303200c4035400e44050409940b00e1415021000340c2d010440c9080700e8010581c48000030f51200808003951440d001c240682640b8105040044503000a00c902c00d11b084500f20b003c203130301140403804c1c040700c1c1c40b41d00280d40c6d040c2410881818001000071158610501040c400c907191000461b60764424030241c41c100340030600c265040c00081c50000610644110040c0002c000300f0b6082001c41001c00446078021f10030f078080c40c0341d5111904c0704103944480164172500241c6407005441f09440400c283c08200e41243d000c2c0400f0039609004d138044e115603800246442d886100c050011800106001000d90341c0004080100d41401006030041d01444802401d8911300c400140e02c40466400254464800054100503a40e250030500c4100d00136110a0703100b8064940014510703801c0707079001800b420300a0a160f02900c800d03400007801d40304c03034206a80f5000c104c4c440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896981196 1250 896979946 896979961
    0x70302030d050c1213080c0f030301050f011404060302070501020f0c1c0f02251e03030816051218010c0215130203120d180c23090711011d0105 63
    0x401d03070098000d0703a1580c42c101500002c0e5081c0c1c513024003400709a1010810040c200302d0300300100d40c10300300d21006446142012000443c1c50340c10900c50f45020714000c4484040e2933208400b0001da0042c0780e110141090b041203012402134110f0700084805650030400203002403030000203089800c280340028407076a04003400c00e03405040342c203040c40103001001c0404540c064021890000013240e681c0110030003100720f44400c1c00b2408540c80419003102c04c0c12403142c04441c10b41040d0a5a0194881015646581c2d94540e00301078052400380010b5021301c0100944401320081503040780140c0d41c24401910018a1142114035900e004000340e4400600d10086c111005162540125021800580ca00b41900401d466000e44508043da501c4001032007030b40c00080703601528003000c01c0000e041c01d840d200d240c0301c290500c1500a8268602c0c0c44802c006110b1480e840d2420921005003040e40207464080382030344e00c5180c038003181c1c00e0b6540314151f0401581888030314088080241e8004140381c00c2119 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896982446 1250 896981196 896981201
    0x120c0b070b070e090c0d0c030b0a060905010f1e0f05090a09050105040605031f02070201020a050d2316110f040e150105180609130203010903020708071202010e24070302030d 76
    0x41903c0d01030188901004844005c010585440d04404900415450109007084000b414030741c0301030382d20243c421804100e2076400710b10312040c1d410030b0301c0d000041d42c0911400d6800010110610103041c1c02486020103042c41074410000355016420b00c4d50034108000000380081c407a980101250076940e60040007035107810b02036600180300035000781c8407480e5130111000e40d02000040080700c082d0002034482c21644200a0080001d8125003514490560380c0001050301204100c030541c0c4540c40704196004401a00445c2d201440a00e1010204c01265a410310071142c4404040d520600650b003000580d1120300400c42d000c01d18070090700d80038500c50015945e90030306800084c0200481860b0030100702000c0319403604a03104490b1203a0903643c40c48526a00510319034025055420148200304154002888000b0740e208030302560340081e16082c20042203a2040c030302038005030341d0040f600102c1c00c01804074104d0120500303e100290703920681103049a48860000c9005030310001d8505080d03520751 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896983696 1250 896982446 896982467
    0x190c26070b1f0b0c030301030839010c0f08060922050c030d0e09010915051806040e030a0f20030f250b010b09010e2706040510120c0b070b07 62
    0x5182d013400c0c034a02c1c45205030b0324001408018845000013842c4810000122007007480807004a0041c0ca20402441212106031030803580e001d9a0341c07e02e1403001009018810010500401d90348528980e987d002c1003104094019000300c2c00070a4600c010307080581c440d205c560040340198003e0240c1100842410710f403d80600b507d004200070011f15a24590310140c507981181c1c500c488c04039402000c855502e40c141000c0d8003240d80600008036012104c89480c3d180362003540b08840401c0004c0ca028080c4d070704c03440343c20100e50009000203d111002800341c08240084031841181a0f25a0344040e40e440c0f640d48290040c05034000d01198103544448030514000003003e10500c0c0705002c000a079210410703103006015036124003802080d40320042e441802c040b119504002e145a1142905031a408120484140c2003540038030b0180c001a02030429014440c0113892211107600d01031f03c1c2401c0303400c10524800e41118804245500020000d000ca0040e01181d402040c6110792404c0074100a46050b02d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896984946 1250 896983696 896983709
    0x5040e090c0907050a0201020c0102390c1e0d231902060904020702210c01180501030e0708010501080624010c03080c040803030903190c26070b1f 64
    0x18007445403090715940c41258000b10b42c1c0c01c01030780f540c0500f18160b000e80186c2411258541c4041035440b1034001e0107000495950310502400902c92901e00354121414450400c1c543d1a03020482900641c01c0100b0020020b484c4a90301c5100003174000001003012540d400700b034031a40390320b51b4034941041010340744112140c0c05000401c1c2c620703000984804c41d049511406407023800040f9112606488a40469140d6540206120044810343c1c2203110790000303c0042560a02c15007180c00c02c40d5010b045039002001c9885280709889240c43c0044026116412140400340071f140c20000b4001024069640038140d1302010305907601c0d10000002c1a14010414054100d580d0191b140e9aa42c020a011000d01d03054a02800c240ea514040c1c8030461003135612032415072000004000c451100403001d0054100310b00c40c44403046550040858090309000d038060861142d03034052890785101c8001080c0a901032048003428104c203070310f5011270380000300c50011804202c0c001e13410480381c0340d401c200003800c0c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896986196 1250 896984946 896984953
    0xc011d180a0c08040b01030f030e03160e060303041a21160e0603070f08090118060618051e0402032b090605040b0a0305040602090306011d0903070b07050a180605040e09 74
    0xd0030b8550110305e41062002820010b000e841d90803c1c5442181d0200842ea00502143da043e00400d100c0285080715208001c234008410021070b003580383c040120b0b02254050b14240310384407a40203408000741d02001e10455802c1c04403a0192032103090030112440307030140d83c0c56080d440040d210068801007051281c0d80c4180c0f001c000700122135401412181c041c81c502e1400c451030750fa840110500415140000010b115800d036421410131540f40c004000b0b07101090803d80c1c0c49141135080c1401d607402a80e12f000004103c460400fa0a5003520850b940301d4001411509030b009562040c42d5034003481d4503c10726042944084003000ca0b00041c0050007024903107001d52515180003103060131402410300c1c2c0f00030036495801050920849405849081c0c1d001800d0b0f4400703513501d41205a00da00c0f01c0042036126400403002a0040c5400f0040c1c6902c140c100204c455640c8e20028110303015130004002d4400d000d5031094541032800083d43c1c1c4000340c42180c89a60341c85081042c0780800c00d0300100070490070390 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896987446 1250 896986196 896986201
    0x10606090608070503100b031009060b071e0302070306020d050f15011b0206070206041e061809110c0703050705120a170901051b011b0c050c011d180a0c08 68
    0x5a10030b1502d6442030040c5040f81e100c3d04e0307090320504000003d502145408a010083c00322440071014001d0440f40306140400100303036580c0c41450030740101c1401030040411400800d952542c21610710089038420702c1542c813400d03100d641e48800c913004101c10714215960742d0200500c0c400308016180d000307550905c81c00b01614184000034450035014551071001050b0956050844d01e03180141c07046540d00401c1e550720303542c6405a5800d400950402400c0c6401c2ea0240000c1c0180900315140c403140103480310034038060424580c00058054036040681d58241080080980e90b000e002c91030240d8410f43c00703014542d103884100540a103005031056215040614084c0004140e600074255407070001001e01c1d01d40142074010780b91130042d5180641641400d910001c8401419400401d401c0041c8000c00c03007400dc581d00440b032042e0350860040040d4000e00f04030b2600d40c081e066608140c01181c0c0345a150a42d02800300d16000e021001e1600ca00d0a00c006001d40076981e8001c0242507017440c0713000c0b034051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896988696 1250 896987446 896987459
    0x628020d1d090c210910050c04062703060f0902131109040e031207020c010f051213020a1a0d0506190306020a0219032708120d06050d0b010801060609 66
    0x100c1c00a00b01e83c040c05030020700c00401540c1070300380d00d4100b650071122900d24075007810700300d445007015818002c1e4903141c00009600f04450138107680650305640d0782e80fa041c10b8845c0029680c01000030b0340ca04904c025140010019050380202d03428409501d001040003a81c40c030501c003000b07038042c3d4180304003810102d40165041c03400041c3c60900e2400c54010803c103e034036003268114801c50103406813442e400320410458580016541600010030303a03c890390b81000c81000c80701801504852a2040d0724a00400c84485800c2141070440740010800c28406503a091a485011542d01c20002d0051011408200b145035510501c2d902440c00d84505c4208405c18400341d2500e00b86001c028029030303002c9800c4a00c54801c201402ca00b0a1240d610315029405003800f6048400203c440521004403091752503110009610b420f04480d07030600189484c038141c0304c1c50703001d540254031800c1085541d5603000074244d80b240481d4240d5400b4070001c1000707504040781207003954481e40108080c0503600c0420000d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896989946 1250 896988696 896988709
    0x42301020c030322032a0e0c030a05061206070e0f030114011a0d0f0902031e1c0c082a011b03020f0715050a0b040b0307050628020d1d 59
    0x120a4490801601d1320021000410781c0c3c40c041d040a010712015960700003601c280d0381d100c084040141010115920358071802285c03940c5049802080c1c8031028800b003000d1403500d40041340c02c00c07002401c448031005d1b04415180b400e0011191500025800080d0201d541009200b100d40c1c2803055000380b0010164184841c0a604107100d1088026141c242108045501800750b030308900b14003209101c107541c0c0701c20200c00782c00110400e80c440d0054403c1c590100450494944444000001500c54107800f421402e200040855444e000c2c05070b03111401e40020080d000500c19036000e0b00c40d00f0700e0007100100f444022480d80c54107021a0780341c008c580416101000c0703072545880c024903002d0381d9400c010603424524090784900400f0341c21807404140503001282c020500c00c5940190070000d0503a110100f00c1a500e05056094142d0030415040c49182000c4000300710783e240c640c803840b107012882070301c501c41d003541c0814110040e00040c211401d901e074800344020a003007501444101124803c40060304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896991196 1250 896989946 896989957
    0x1104050a12020d1205071406010e0a090203060c03070516140d050406021504021f0807030e12190302090d03180b0c101d03040612050c160b07020a0206042301020c0303 73
    0x80c8034940313094504503101d0400c035820968094001041184104501e5556210030b010b03605014031035400103150b0014503c903034200a034008004182a40702d464000e81c03284c3c00501000c1c10014100010050300042452080c00e4621403000c3c110f40c4000ca13025241071100c83c51001042240801042202e82ea0000e056001e01462342d002d0a66501c65100013008100700b03041d1000b541d4110b2032840301482e0490326841c400ca0054400303100240f42c00d0040c649031542c4000252070b04005021700c66076881c00c000700c041004010300b401480c0071410340005503160032140d012000600c500d10701c9242a8400c5a4500c0103141d00b1550b00e00b044000c0c90003030b4850300c4440c401c250b21955101c881c40e82c40d80140c1810000c046841c02d49a0302d544503200280f078021200121408a800c04000c6504403c03180e044841d0407490b940030060f40c44682d40e07000410040901070804603c15109203601680e2903200420083c1401420120502d8030658440000e81e850318900381507401003280f20340f03079407400701c210b40f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896992446 1250 896991196 896991203
    0x4060b130e270102030a11090102070603050c12090f150f01030f0501110a02010c17010303090b030408190309061d0606042a02010c1803020a0e0c07061104050a12020d 73
    0x41d40d911000078404202070820035040b504509040c5900ca07100c10350046019400e0340e1001d101503c51100e00f00501e100fa403810030300503442418100101842944042e8012100c215038a103803100e00d02c43d8408002c002c4d14021071070f400040c807401003000c0400c1490004124506102c03894a80741450061058051101400e4900c40211200800c00c003075100714165440c0b81900d0b600c0305004c90000f4020039040c030b01e07800852924080b0504800080e0015812a5410760b111400e0905000c43c42d40700b50000360044803440320130b2141c501da181098036100610503165400048181300c5045c59001e65102505a815405a015008202c50004501c1550002041e1000310700d02c2d040d072504551030801c2c4000881781843c80e06040300300381d5044d00300507004410b59594403543d010340303a8040f00ca003100d03200080d4010052001004240300300900c10341c0c000400002142000490740321042940d070142130303940d112100060140f110707142402c6040b015000b050181c08080c00c036540868040384a0404c0a03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896993696 1250 896992446 896992469
    0x90506190603020d02270f011403011a060c100c051309090309050f0d0501090b070822021011030d140a0e03030408220609090b041107020103050402010306050a0e010504060b13 77
    0x100700314080c40e001b85d88009160f0046c10642d00d041950b820401c03100303000c0c8041c00c0401c03200241c6a031405014007408000c0490784205000c42410410586500454880e406030180f0101c0c5101c0c00d01e548200a044030150b102c1903a584030000000b081051150405017550b450000c540c8080b0b94012050300030b40b0010340314286840307910b0000501300f216920008090390309200704e10003080110b04c0400c1c000c1205486005403a180e078200d031140040c0d07001c490001441d00900c00c50245c0343c01c054a039010129810219841d660301c02d502420340d4001081c5d1404d01da12a248184408002e0303124650046a0756801c001c0d42c2800e40310b55440b440b01505c0a044d000021172290050040c13a00400c0300a07079980307401e0810950721100134002e03101c240b02d100200c1d0f00d442c01014040c02c2501480302c89803031080e0818035001e043e60042d80201030192069040681e10f04c4007180d513449180102028101c0042a0020340d031400041006544550308148803540047c022582d038814007400800c103031000700a44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896994946 1250 896993696 896993719
    0x1c08013002090703020f07060603110427170c0c150c0d050d14072118030f03110307030b04231b092d0a03030f1809090506190603020d02 60
    0x45020707001b52030b070014040b103000900c0010451541c0c0000212841002ca84c0040c2a1a0041000722410038038036030030081012f103003040301c94040b45020340c4462195011a5009201035000c148039080340c1c48402c5558071044000c4d0181c5440141c2d00314058001c1900c0f880e01c0d0740d80403101d4441c40c0b8a0094420700c02e000c00c1e9004101c01e150001e0001d0309180300640075a00c5e10740001050300010602d241010548515602085180e60040b008214a060840508402c180e9021614048003024210815903a5003210b07400146100c002c5020300825079020171b10f20a00c0c0d0400c8100c40c10554401445070f0340c00f00d02c4c1804e450365a419a0300000740e44000030301c200f59200008861103160310031503004c0740c03400c4410100c201a529141d040c1800302030f444a00c51490003444095262408042d000c0340300c01210591080c4a48001e00280e1a030301c419000480c0c0c0d4611313071815035141c3c4404903455000141040640182e104442c296410100d100380030461558010421841e0404800781c01055241365 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896996196 1250 896994946 896994961
    0x50a1514130c05040216080706050402091305340b0d0c0801050d06020f0d020703180b09090f18030c0f010b1e0f01170f010303020d0c081602031c0801300209 69
    0xa643c0241b40e08501c8450b0384000700d150040c003d08044404034441e50000700840e074590303086451459101d9000e001012101d1a01c05000c0d9010305040c107101e10400c1440500740002030027550f41000f4510a00b01c140c803904c2c990020f03429941c6e240455002c20040030300401c40c6a544140390300d9003541003d001030b03a54a188800d81190303c203842c607108005000141100c02c06901c81034507000c1e41d185001401520780c807803031402d00d00e11803a0050303648181548085007180401711850768100a9945841c8001202a0320040c2580c1280c40482e0094010183d52001c5410a0141c0700d1503500071956401c14104852403404d8407406000000c0c0601c801c1e020780c4001764020071422801c85850b0b164a40146800880c41d0340e81d20003400114010701800004041e81c1d4040d181005110380d01c01c4210f401c101004c3c081c00c4c074144e8030719410ba0380743c4200700c410181001140d2001048200303540e54902e50f1342c103002903c41d40021120024400c180c00060700b40d254100700341581e0100e5030480b64040540c68054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896997446 1250 896996196 896996227
    0x20102061f2d050409020d03082715070216171e011d012306060d1515080f0711011e0e07050910060507050a1514130c050402 55
    0x401081d40110030042d0305440b00d440c9008075804141c880701c10381c03940d6200e07400d02065402c0034000a402401040b51000040d02540b41903034030a88190020000440f20b112440c01900b000350480e05e5a01301d2421883c1e40e600c0401426881500b41c0014070345409007880740f1000358071b42d00c2000844c01c00c100c4046c10107503050081d040c01a0303020300d50310130341d0000360029070081c001602d2552107203102d00100000100e042c00b0706007031207901141982010102d11131030b4118a0f8000c0c45a80c3c0000c1c1084881d0410085104601510b65405040740c1d0413401c0842850710454207121090601c0000010003062800c0600d03e554013847e5071801080f0a24034049590140003a000e00c01c075400b041011240000c42240d000c059034100310400c403000f40da034070340911043c1d2030150391000550641d00818040b050003030f0000c00c0701c10711401c03c0701d03070000c115190302d00210912001c080c806501e8900840c0f04440c0d40c040321303411800f0542c0f402180803565440c19100e12003849124043c640119400c102e021080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896998696 1250 896997446 896997449
    0x80307031d100503010e150109090209120a11100804081c0e0601061119080a03020a05070c09020406030f02090a14190b0d0e03040e0a111c0515010507020102061f 71
    0x5000810b1001c402e07240507201d900309000f0002058240000500c0b1040e0325004580c810300103031140d07641c25080c003491001a501000c0740075001024026110210b00007040011001809198245d8840742c1407402c0141c040801110002001090018040800c070301d07504840079213000580f1994008071403038904020b40003a04041c100b03401b0380740002414035046885d04131502e504c0801e4a4540ca804001c5000c1a20805401f0f44610824031004040d140241c0c02043c0b035495900f00300303041c074a155580034242071103a040b0b01041c41d0041000c00225815004595221940c45001c3d420400c207003020490515040c4201601c000c041756440519480740c0140320b4000c0402c40c2c07070081c00340d120b081070006070b400641d14030130b890720303080e800742e4000e42c00700c02d0f0f81c02d480d0680003245c000e89401001e500034260000c80c0300c07901c1c4820010001c1140003400c100394894006100468240780041d10310380340c01440303881281445010021040142e03800704807a6804481000b2500090a2901f44e142007125507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896999946 1250 896998696 896998699
    0x30702280f14061e0c0c010219030b010914061815070b0f010609051e0427050c0a18110c0a1407060201020406140a0e0913021306080307031d 62
    0x10441603030180304407120150b1103808100c040f540705460f24550b807594525000c0324480c64a84200200d82c0904540e0010401c8150000002d801c04090245c469500c03000068491b000c2941c0e04101102075821803414401805500015441c50512901080c43d600c26882440c8c0030304040c8bea076508030f5545030f105e101d02c001d00700340e029100c1034a803a054540c2d55081e02c81042c8800c00c00c00000b0824421040b160a40310094000740c01c800f00e49401d80450a014012564010b88074010124143e4003a00321117540092015000d070340c44500c0c1421401e0040c21a03056000f200d41d00020b00c0420360b481000756180c0841350780081c118501c091030f413800d4040ca00b604200c03805100c95400038000344d1001c40966100100c1a0340c11950b80e1401a401c07407056100710404101c000882c103e1207103111014050b0301015080c00d0040000c42c1d80014074101088030100d07803100d500f04c040015030030704a40200d14a5414001005101c1c20400d2003035490080c11401001c00903050f031100c44114070502d40700c036076140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897001196 1250 896999946 896999963
    0x15091e02030a090c08060408090d031b0812060909031605011e0506010906031e1a0a080706030f020c0601141f031a0607021008060102070816030201021203070228 71
    0x301501c062001c1c0283d2002551666507000000c580120040341050107143c1c0151a507103000c1c030080c1400320134400700606a042c0075900c00f010800c0034110102000c014450b03000c16590380300d002d10103840d01708040d01c91406003000f034040200c41c51001007180d1a08a080340319840211a52804034090726425505400c20505000c504200c80c41035009180190800d0f00c68040301a15520300f01c080341c0c0d002c03885104409082c039000d49840502e41c000034202c1403540300c092440707550b80042682c000301c50703002020711b903c454004c02185502d445540c0702c0181a000542c509010307800032035a200018004e00340c0a4001c1d1070840c04d196035545150030901d03035072140d1030784801118102030000c1140b55030b2080d6130341d040406a0207030f2400c1401c0300c000c0b6500801c0307000d05440ba014200d032440390041205055100c2c40307401051203001044184000741e59042036815481c10f40c4002400e2522449040800e8030040c424864100e802088165040380f0440040c0385840800d01c0b03020007031100030340103880d058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897002446 1250 897001196 897001201
    0x60c0c0a0b0a02150c040306090c031406060118051503070207180c09050114180609030a0609170a14090d060903051e09060906090301271515091e0203 66
    0x40401001d011142d1494003910b0342c0304409240a5814203044902c104003d20030403092000684a5116141c0c0300e02800c8007008294403aa200c0c019400581c5030b1101c1c3c0c0d40400200512907a200b12408043c5802a40c3c0d00107c914010108008030210b40c0c40359074045d004000144110700c00c00180c1c0003080450007102e120007800027840000c100c0d130000500010107445010a1650040c0c1d140b110b4201a004043e150203d05441d03c5210b09114808651113542004280c80725036041201c11341480c001c030703c00a5610340c1d614011041088160348002c00300e6090141206064000c1000a04605400002903030349a40702e00140e1300400c600340c0100000e181c4030600051503800005071108102c1588138030750303a42d0345072013980140c000c10501d90340c8044100452641810101c000d4000480058004140320601444c101d9504402c00802010584210300410174041c1405407c4078010504800f085110002000400d8440040c0100001035846d010703243d4584200c0b00610703041e010060411901ca0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897003696 1250 897002446 897002459
    0x204090203060c0c160f090f060b03181b01080708091203010b0a030c020a02031209060d09030302300103020105090315160e04060e010314030706020c032505070302060c0c0a 76
    0x13500015100a0701d40706000c280ca00040200450000350f460300129204040e1030408864080c0c86141121002d050308c8550005d04003012030050743c000d039110640c0788070b090000b0604a180c0007403080a0314001100c07a06412250f604409a6074004440d03141036421a5980001c40713140072000200d07580300c4680000000748018030700018100340c0134242d03000d00caa485080703c1282e803800d80c001d001c2e5254020752201000007091500500350300c0c101420543c10441981c2c0d00c502110031030710f81171380480d40000302000300b408102c400400040d050740e41081c2d244000700c11900d2460301400003d06100001500c44800e0390104603850342c1280c1d420000b0400d00e04054646000113540003030001003540d2042e07048040ca003500445007950410511100f26a2840d210b1b05410914000b0705003c0f804200318000201d06640010543d0b042184000d55448800c10141241d0b040390b2803c007005840010105c1c0e0018101281e15000c0b00c2c0c04468031901da12a000c1c0241c1400b0070400c951354800b00517070740002e89 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897004946 1250 897003696 897003721
    0xa0503070605062d0a0801060806041a0405030a0c0f06150806070f021507090e100f05060703021f02131205010c08060a060c11060307120605120a020d020409020306 72
    0xc612500701803100b40c680d4010b0003640425482004452a1035205601c0309410040b08040c0d550001420040303c180d8442c02c081c2104c40030b400c01600c40d04418108414081c1010040ca6100c2e500440056585440e80301c880e12401403040440410403505409014880c492120007a0250030041c208180e210f0030f0000300490005210390180ca008080005490900900154041c02c030300c4d402415007030980080042000c0c81c020f0162042c07047c0c8c0d10001c1000e4084401c514801d550003045240030a061408481c80081603610052255008015520000c0e50104540c8005a4550041d010307940b1812940b0000c3d01440c5410400b55002c50000188070300e000d4a41c081c102e014100801c00c0b001410b804560366101290701b80c1d0009400c410400c4458800c0124000d030710f0140d0a0103200c08080b0300042c1e00c503403003518881c0001e104c2c484001d928208070b200d502d006080171190040d07803030091542035858454180019100f42c00d21450300c019501c9940103a00700990085c01d661a40c074042004400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897006196 1250 897004946 897004957
    0x120309010206010b03070f0c081b060a0b0a06050d0203060f100203091201090b0711030c011a0f22090602132c060105030f07020c04060b0a030c02010212060d140a0503 73
    0x14481d902c0001400c0c001c581c112070107a91b09980d0041c10f45c981150550303040540b0802203078842010480d50203402c503540540b001c0307403490001900e624141045448180c6007052012803046103032500401c54550000102c40c95040a9400540c0782d581e07410000c3c281800054403141c1094854503001c00c1036034040000c10306546c0860303409024a541040840c2241d05095004141110320808250700074084c07018200318030001002c40785044100c0340420709684059034009004800c400b030302c401034a010000100780e40700550303059400400e04c3c025100400107601000005681c0c6940d61024807020b038044481400c0c0030780c451210300c1d03500c003101e00c403140700400b02200300ea81000d01c1001ca40103140203540103d405948042c1903841d075500b80740e920b007c00350090081d40310303072051002a41c503607014480080904116007030310340100450140c20b80310107480c0d80d011644101f2100c46c1c0341d2100d08182c0c0d001402a1040c042c0f0700707118641714610303d4035014441c1e04c40c414600f401c401c10000000520 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897007446 1250 897006196 897006199
    0x2040e0c03100b06180d05010c020a0b0106020105070212030c04050d0507051f09030b0c190c0302070f1a0703090b040b030603010b09151216060903060506061e0a050405120309 77
    0x314018440000c5a040f6400708402c1544114208500c029800320180070b90060310000b0030005520350b060f51142d003121100c403210800768214000020034030812a000d5030040807540000e01c114602040f0094a402d407283c0f04030a99900403020480380d0b010740c8103a0f000303010084d0030700003000f0143c10a2903840b001031203614443c411000c03245129000c1030380d6540540d441900d0300801141035a0340c4030405640104094103a000038070005008440c00c80100490031a261100581080103040c0241090860303040040f0303e5554502c2000f0070180543c584000300012109140c07608058501102d03604126400a4540f20000c9004151b04000e0b00c02540119001c03070080195450210074056460300854851034000358107120060b560510000252208414900780c1c1d0400c0d1500c0c200426401c4240c01c450001103c46c01c080c82080340714030480d40c021404440e004c0c20490041034043c201184d40c1100e1a1082003c10305031500b601134401d82c4e0240500504080c1003100003107595607680c10000005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897008696 1250 897007446 897007453
    0x5041a040c1a0d230c031e1e0a0e150a090b0c03160212121f14010e0906030604021e06030406240e060d020612090d140c07091802040e0c03 61
    0x182007510000b00d50b0200004c0c0e1111122890340d60380700c01d039507980000b0000c01c14030003054042c89030340c030340e510f00223101c0c0001200c8003948403a01c003003503c4041c0000b4089500c45140c90405540d00703000269410b003880103000e00004a40d10f01c1e1000c0701510007490003c0c0f04c00d000304203009050340010040c6200f018409000b2a1103060001c080340c1d548a1910706440002c007c1181d0011181010001680f0002695501344025040e603107107a58010940d020140514004030914129a032001941140b05070885034441030b4100b400020340c0354280a00001e1140000d62468402c04884c04c80d20500e0b14401805a5203a107428201038010f0240ea01c1340010406420850102401116402c8000e985402541d84420f82e00d01c0c080c080e54a10740c04090340c0c40380081c0403203d4020104171503d4400c07802da07000380814921148014200170540c00c09101c084105000081ca18400003c101080f201c1c10340e80810661101801e03940d51244481000c0e40180c2040100b0005103070015155030300f404180c048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897009946 1250 897008696 897008711
    0x115050102121801050a0201020c070303030f0b09010f050607030c0c0e06011e0909151a09101e0e0d1505040c050d02010912050106210209010905041a040c1a0d 70
    0x2070700e42c0c1d1240b2040041c07030448641e0155415480781c4050550381c0c80350b000040c40d04541305d040519184d1168012000281c44a20095115446000b01d50b000c0505a81445240d4101100000c43c1c88040c001d09000700710100e40348091600c1041100c0300c0c2500445104140b47c0c8500140301e07031400c212030060209155802c42000d070401104207052903591542c0f50b86090381410b82d103101030701c080f03540411003001c50800411500720a00c0c811030341051042ca495034905418048c032285854034110701060100800d02400300c0c6580741102100301d0000d01d01509240e00300760004200a900407000313010207213132000c00007045020364000d5002c2c80c050881c04814a9030b075420020302d103c603e44000c0c0040c00360402080051000350001800c14495400868066141d4140c41711012000c10001021f0b000b0200e26015404c000301c0e2140034000a1405001030328113601c0d12240341040c0c510954159414000090a20120701c85d25406015202e513003151445480400c00300a402400a60303400a241c15003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897011196 1250 897009946 897009973
    0x230607080f01030302190302010608030c01050a1802101101060906061205010512030a05340c120c1403010b100306050312071a0c0c01150303300f0e0115050102 70
    0x801d54101c0e940b5500409450030b850410a1810f0f131965001c074155922600302080014090014208801000e000020980307840820901900e0b03107000d800f90001a08560f0f07401503110303d803e6080510301424030b20746400e00d00141900615107a48222040c5107401000701b0030340d43c4040c00c0e0003500022142030101e81d880b44104080503030070101200043c1c0c0104100018940100c000d0280c210118071031510340c0c0c90300d1b54922a41001240f4901c5101d85061440c410824201c40d00009002040c10710f400e1320400c1d580d50283c00040f4000c4500d512500f0440300d036166000d404c80c1418610252090400d40e48044002e0040d1400303020340d42c800d000b40b016190b01002c1160a59111642100c03d801d00310007500b5900c980d03c00c002e8a26940c034281004500c241d8030007402601c840540740c0340480350440c81e505000b4401c010b2080d0401c096440d40f2000c030515624040d02d000c0e5040e5001002800000b2802200020810340c152000d8550138020079541811210354840c00f1120700380c0070384008216500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897012446 1250 897011196 897011221
    0x509090a050906160c0b040503041503060b1b0a0f0311010f0513080a0c240605032410050424081212070c0f110f010e0609040923060708 60
    0x458900099011000140722031440141d601340b00209800c01c06038040058a0b06003100c101181e00791042d5100203020001418502026644443c8514040241d903003013006242c480d01c00c1c03100302c04c50041c1000341030f0b4000d81c0c14040c4291659120b00003800d812690310340070b054203040c4840218113500c0c0481c08070106040d0f0107454810700040c00c5400c1001c1c920341d2203c060b504100c61080401290010b1100041c003007619101c1c07006080740000001214042040b020f40d021608003038040d0300100c01000b402812403c03c000c2624445410201a544080604500742c6140e4004c0354000c0c104440390704051000b000c041f058404624501950544030001c55644400d041d034002c2c0203e804020610074808050312454018280e031038103007600c000c03941341c043c2081c3c3c40e07290569643d100701c1800080e92400403183c03042d804083c2000020b469441001400e0b034040c2c02072180c022510f60800c80204044156442500100c14071503a0120303001d134042c50398800c2d048aa8801061018011841285c4c0c0007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897013696 1250 897012446 897012451
    0x402540f150613030b0405010e06010b0c060a090f061a060403031e0f08040b1e07030515090c0703051e0a0f03060b09090105040b010309050d020c030606040504050d05071707030509090a05 82
    0x66000f104d10716a10700510510081059440d55624020040407035400d010301c47c020101a281c140d00c44076040c1d01c40341040c40280c40103001c6480c1c4040d07640050a125010406a0f410280c002001488001001c40c4c4500c0e804005501c280f001901204245d00070a01981e59100300c5c50241b109030140009507407050f043d01224004c59541400100040c030402c030490f0713200750010f0000c000c104e00c41c007032002100e9050390f48602083d2a442040f003440328595100400c9401100e07204a10700780400300b840c007889840005810448e00090702601032281c24500d03400d5003000e00260b56200d107858002010f00310324400610000341083c80009411141d10709840e2070a80c000d0814140d64a000200703c010104100303000c0c141520784410b4030200f00140b0520742414001d40151241400690806090110003050b0a210f1841c0c46d0610021420000380c11030319402c14103040c2d5071a0103030300702000a140040e460115001002451350100b6a2141c0030b8000e186095460103580d03210342c0018019101e04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897014946 1250 897013696 897013717
    0x2e05070206130813180c0e090a1a030f01020406021e0d0c0201020118050c0a171c0c0b01080d09060c170a0c060906050402540f1506 58
    0x12902040d841c1d400d02c24075108180c824840c02d480c0442c0ca488600c034480e600d500c00303405000e03c0c10394010031042600450115081c180b401143e5103401600207400b520002d00180e201c60790700d09400d1084000050044a440002021560600603103990207020b503016000f010014020703440400c5400d601d41d1100928201e00e500640407406079950b01322124031540030260304664842d042034208003c803800e264800c50046c00503200c0c1030001c030140260440c40d5071048040c0d002240f1a89101e060101e2021041c09003c0fa403c00749400c1000102e40061803484060461007824000051034000055489c00d5147c980e220043c1d0310f0396545003034a6074054040050040106008a480c0012044005000b00071103070034000040c9074141c44010403505003450840399250381d40240310940c41d00003020804504c01c0192107083c141540c403192940b0f424a01401c91000b0900044201120201c09200b020014000392030010715000480c0300c64040103441c1c0c0180d00030344420504490815004558070030300b6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897016196 1250 897014946 897014953
    0x806090d050a05121005040506010507080706020306010c050d0503010f0e063d0203031b030c18040908030a0507140a0215040602040e0f15030114040b0601020a052e050702 75
    0x200c09000d64036a0302142ca482c082200030449a0f582c1e80103580d0284c020b150300e401022060f82814107010441d1405042c5074180b000900908000558910484013165807101001d0b850303482d041e0043c0c0d80c808018100621902072a0f0324004415401400f45040b01c40f4200014035456607003031022021308007500e030290062180f00c0e041c001c0b43c200303655980d0312800c150140e01910560360300e0b07025110180b2100200507000001408000044124440300d0072284040d164503505101d07081c100ea03407242d400d2000082c4140790310310600380e80701c0d44405529038201d00d03410341c0d929000c084135000300401c9440c5404260301c0328500f0318003000e20301035640d00e060680003000840c10302c0e250201307102c900620460f0002c2d000c02001c07403a10050010540540d003007907080d1300e00e400c00580003041c00804045a0340641c0c54421070a80044034248102d4000d070304502c2141c030039126440100e0a081c0d440c03601500c184111840411494680011001900c40080801406807001c0101c5800d80342e090b15443c0045e403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897017446 1250 897016196 897016213
    0x33081b071520030c0406110c03070e0c0f072301050408040504110403080c0105101707030303020a0e03060108030a020c0a030f1e060e01150501020a1a061206090313080609 75
    0xa00c1d41d80080d10140e51220498112150750200b03180a50045074040c0244101150820803141c12240c01c0c0100f000761000b1b01705007090040840d50326202d038491038081e602d964001c181c0b074801010441c0c1c243c0020200f000c0e65444541000303020b1060780030300b14403881080041c002d042030062103a940250b034000310141c60585002c08001c003412403000b00080050b000c1200000080f8030600038075200e094880086081d01d001c0c1e0916680c0d000310380c0283c51542582c0c0c02c1d40ca001401046c803000740d039854200140c4401444070125550180030840e40e4140c0b16042c00801d140c1c00000c06000c0150710381d402c039420800040240042204d075440000c14030800c0c6c500c0d900005810750705100c01d41c038954400500ca03409640310300b0255681004043e41996403500d160b2241007920351000007910080c00100004c1e1842d0342e400c0f000700301c000428040c5081743e2012884598810074001a0742140c8011205241844640e480c2c81e40d0001b1440c000c49000340030005245400416868840c0254401402c07420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897018696 1250 897017446 897017483
    0x26010524010905090a09021c050715140a020f01050601210c03020903030a030603030f09030b190605040f0b1f12020a050405100f0305010602031333081b07 68
    0x519940c20034a0501100d1900881c0c5620b405415501c181c101380c60128800b0294014003407031364040c800381940144c24960304400700b00300090351012508900380000e468100242c084450318600c150340c03021300c1000680250301c10360000b00e070426011100d00030811034079500700650346420344141d080381705005616900400d80f40c41d406800c854078907003409031410b8940700c0041d081d64002030840c00403a40ea190309006042e8041c240000d40501030400101c4d490540c0c541d01030701c1c10001c251042c843e03c05c0c01c4021005145410880080c00042c1042c071205042803180c102909901010361300440c0c81c442c03c1c40a2428038003040380c0030007a546500d20321007008003102011f03511000d541c2c01404020400010fa544415844000001d0580d4424540401d0313490010140d510607408801150302c1404504811400078180004440c0300c039080c3c1c18010014016210f203030342075541160807034125250110909400443c0705111305482114150001e12013030790010309010b01e0034050300c0114010f41d2103990 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897019946 1250 897018696 897018751
    0x521151303080a1503060e01090c0321080c120712060602010605190b04030206031003020904121b050d0507140d2708060103020d020d050706110d0903110405041a01260105 75
    0x2a07e007035000114485181d03880b00446164540d204890b000b0013034035241012044034070300040ba1111490103804a05080c600e280300b030302403980100118900000468503003809041100000c1c000000300340000c6903103c0001e8024001841118003841140c0c04500d01e1514980840341641daa40511500f80303401c5400744002504014403480001c071038a42c01201507035801880c07a10852140c050b10240e180c00e00002820400403902c80d11000064080840008002086045a085c10f516080d51103c1b200e081c82c0c880b180b81c41e0300c4e0041c03c0c010624071588003540008048481c1051005d540e010740c1d28601d120180f2074103845144100d4112000500061a042c1e02141c4c0540c0000c142906207407003904d89905002e0035505c18400b00f60b004140c00000102030009140d200c1c003a040c92072465145440b500d500101d551400c0b44910b6403040080c0401280345400d010090b041034441030550384607201d600551140448154105840049850841c101400f456104141c01d02c0110035001400355480d11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897021196 1250 897019946 897019961
    0xf1112060f2806120314090d030f031410030b1003050709050705091e0a050a031e03031803120f020406020307031103041d1e010521151303080a150306 66
    0x1652602d01d6101d000c00101ea004410240190504203803401d6114503000d40383c5404884130b04c41410301800441d900b5036900591400544d014140302c2110b409821089004000a613040c401c2040464103001491f0005c840c07140a50388600c0103580d103a201c0d00161130001d451440010440e500885d01408807002c185c0005410141d81d0034090b05020700000000d9080d98030b01c90a03541124012000340c1036103000d00c0c0003002800705417004881107095403128900c00301c2d190b52401056451640c040b0416100e80c1c0401d410001c6003400c0c1c4101d081c1407400400110844000041d03050074882d80d0202109280708441c00c03034020350001c1d4236102040d40d05407015040d004200c84a80803d01c0002840e00180d00780d00003050303041e84000c1300307454a00801c0c18a12000d0404080c02420000103110540320300c0c440d1094540016082d140d41c007242c11001c0d00e084107802c40c2d98102c43c00d040a10101c503442e840c514005a11a4035540d400d0394544c03008508072a02000d042e501011421020400320b11540e0200d00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897022446 1250 897021196 897021241
    0xf030c1c0210050c03270d080606070602042606010509040210030f0e010e0f030a0807080c0c010f02030f150a06030905121b060106080705250f1112060f 67
    0x80c02c02808807030420403140200c440100310384001003000440690411100500c4e2001c141c81000d0142179880e02c5d41d80c00381002c042c4144842c4802240341540d5213030a0350030440d4041403d40d034454440d0840d09002c40003000c1c019045100c00c000704004500401c0c018165840a84034444548e115001c00010400d10380101d01031568840585221076030324010305a59598090000c01d1b103506903060280b4101d0300c04500000d43d00240500d1060300d80c03040c202c9070448400d18155940d40c565a1740051a4415002d403140c0c250300c3c1c40600309006440750084e40c800c9880464501032544c8402c60103050403446140d0746e60100504006000d00c0e030003030740306045940c000c104030381c40c210849000c078030304c0d80c84107450000c00700c4003500c10802c0000800110b030241910745415509402d00d824054420700845251200f14607804082c403113000e02140740311042c5608010080b4051495042041d00346000024035402000b0007458020070b44000154180541e210031400104e5540b600007582d1452070782038220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897023696 1250 897022446 897022453
    0x5060403032c0c0a0b1c02090114070b01050901090504050709020c0f010603050601030b071103030412050c150a0608070515221805012c06010e0a170f030c1c02 70
    0x300380d42141002c840070341c00880401402c3d051006020000c1444083d4011440b9540410000600e1010400e0182040e20ba024026071a81114001a01e02c5d40c000d0088035440c0c2c43c00b049400601140e801013a048600585999105988801c01403050b01d40441d00540740703600409040240705803070b80c0142144081d80d0700ba10301c400c1c40d8291060940300720360300595a50340f00350010700900c2007400e0300da508400075080c00803080d6202c0032455140c1c000104050001d18103048003810302400f410840d941064060180c0f24100700e034014503021800c1c00c0e01c0c0746d1070681c90010040380c0782c80c00203000f4050311402010303141c000c80e00102191041e4403000c0e4103c1007080fa03014582c100c0c24a01c1850010b0b08090300c42e800d00ca0f1030300b80c8001c111141684a04040060340194050a60340750740c52000b00d144e000c003103101d0741c0e4564005031015445017140700e0704502c00101c00580c00f2240e020540c980c5840600303036403003088003800c60341e5607008180d490b150680202100a0094404a00d4503c5441260068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897024946 1250 897023696 897023741
    0x4050c0405100518270a06050703020c06071413090f06090b0f2e020a0b0618010e1807061d0910051903060912021509250f06030c02190506040303 64
    0x505c2d401d514010b030046580c0c0c0321452443c10800503016507580703c00140340450500d040c8091055407540043c08100038004c200100300803048003c1c040b5100e0700c940b4481e03034640c2d0359a80115401000c2d510b840407102494404007007101441d5020b810308030603000b88240c540308161320401c40020500c801913100102c0383c40902d60324003205e900c074a49031440d58000d001429082d0510103c000c00090130503204555070040000c241804c01811819035030a002c2c5014241d07100101d000040d141600600300511070200c0c0000d03225404114a07450003013420070311103000702800501c022001d090382c21041c5291103c4080c00b46042c1101018881000c41141190b2295651186000c07501c0440e000d4501961000024a9041c0c0410801c0162480441524000d01c1d0840006841c0e00c0103419280e20b1a1000441c01500301c09498107030003801c040750600350503a69400c03010f40245000103000015020380c2c0200003000c10f0403a1101c0001e0740000162455030b40c0e0b0342d011001890041c1c80500b040e40d00228 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897026196 1250 897024946 897024991
    0x15030c16060504032102070201120e01020c01052a18040b03030409050f06120d0c080a0212031014030a0f0f0218040507170f030405041d0604050c0405100518 69
    0x2510f0f018030300035210f48031900e940082101216411390301c00141240100080d80042c0d07441182d1b0007880201d4200091003000d50000980a8854980d120351150b0a2401340078480d00216000980725000340da242c0001030002d8009040c500941d040101030381516046031145080a410a101d20003004042e41c2c5040d407070380071520440d54151000e403042c1c540703e0108505030900380340034107120b8140002403c040e0700c5144010301c5038200300402024410013090301203400c0e0003081229605001c100d8156185c3c50801001070a0350240d104a8040814134800c01005040c00b00d690360446400407100c0c0040301d80368a405200c003410345000c9800107648017442d01e480f030400035098001c80c40341018011661411b56021981914507121005942080c8910000e0740c00000c100c501f210750036203001c03400d03074102130321561144002d04101141c1e001e444200010084046451089403608a03002c01c0140c03074945002280c00c82600403190480070050102002c2c0809000e0268841481e0401d0346800c126200c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897027446 1250 897026196 897026201
    0x70b0304020d170702150304020f0d06061d060a06030e122203061506020127080d09081213030f03052a131703030106120b1c02010e15030c1606 63
    0x1c05012420f001240c100d007145095620b4011401032203020743d09604080e000103070502410b0718114032992103240603401f04032098108d44000c00300a80d1180d10180d0380c0240d00c0c5081c40c100d48062040948001c081031080c0030344900c85c0312007150802001070760019520307040c030355021080c0c500c8104003040050741c0350480202c040c8055803003a20f02080010038240900c00c4101945c100b901564144075100700004000c01142010a80980304104043c1c03540c180080e10344100c1002d070005c0c0781044444024000c1110042100502e02c410b8900380356100658408804400d10006000601d803915401c0c50506c642c02c8103412404040024a0100100040300301d80012081590b810000215254401d8000d02410380001c101d0001c1002d08422082401d98032480305001e89018803030b0740403540482000b60340c00f90000d488050100360003031214000000300c1c100c0f281401ca0028031540074140707590500300e400321080c0e00310569581c2191500c0c4450040c0783c10440c90707035902150040048000c24142d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897028696 1250 897027446 897027473
    0x10e090a0b13060f0e12160b070e090f04080a080414060732040b030928140a02010c02040b0d060f0501061107060f0e0402040305012a030608070b0304020d 68
    0xa0b0781041c0d81503081d00d020340542d21070328441c00c030041c94001065146000801c00c6120002c01c0380c0e42c00c2d074481d031011070b5100301181c181c00034000441301400c111003181c008180c806400c80848628000d81e845925250300b4040c2114010000002032150b0301d8903a002d031183d1a00f03e071281c60b0442c000b13903104501914064048549034006891a500b404510a021f101080710624880c0e000a6800f0060b26004840c812403140729034030070300000024108901446203100752a040a050300002c1111140c209620301e03241001e50b581d03803d041440d1003103180054034500b41503040c0c58402040002c0e400b048000c10703c0303c00d01900042560100b02c0010070030702c0380c000302c070340c900000203803550602c8001002d05a0160103030080307a029a030180f080c1c03a00720200d400c3d0001c0d1403428222028201c00445c000e40640e9100401e19805d2000400c039064108001c100725041e2400d07041c00802610800710305903141c034442c40c5070640000d0003d0010030840d20045a100740080e00300b01c000c421607a40c0c17442c00c8020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897029946 1250 897028696 897028711
    0x30209130c060c03020601150302040806010b09190608060d03020f1e061e0f0c090619030c09050f0f0301020f131706070f030f0e0609071a12010e090a0b 67
    0x206041103080003410080000a001e403450403140e521200e03540a940c07640103010700b042045146181421861180d0103c41c050043c1c1015580956515858941d0b6030f08150140d51169010032220040140410340c904110381459444410070380341c0d9800c0c800d0310740b040301c015021030048034081017040c03d0130840341142500d055014a0805044042039051840c0500f90344600318000c0302040c1d1400c40300c00c0f0507420132090441c0c1c00e986d0300c881c103007088240b01e031980d1725400c05000b02c0c0240c04107900000500310038050307803014007091042a0084898821901170680d01400e203c16425103400c00d160030110a000107000145031900458114602d90413808021070180a0214288154030044d6054074209400314001c00880c00c2500300a058445016203641c201542c562204c0c2a500ba907030020141da00500d000c0c2d91443c1028030302280c50703c40b1800340f01c0241c403109a110f1210f030060b50894145248a1441d030540340d00707103107006d14445c0000d46004814824803641d0404a5800710156014016 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897031196 1250 897029946 897029971
    0x60e101109040e0102030c310e150102010b010210090804090f0e0d0c020108011406070f0b070e120604020103110c0f03210702071a1c02091503010605090603040c030209 74
    0xd01000300401d0303942690904a082c0d0050081c80304a60749103007517900342d0702d48004e2802d911810070400714410208440c0201642368400000500e4034038005243c6c000c45d000126000fa201c0c0c10f00041e401c0c1d44203001490b006078094500c6031030104c001d520640c401d41c41a1040361400d81c0d54004035064400c610344042a1656075000010f41260400244d080305403c0e0400d4049291140c0010784115014822103840c03440c8126400c6540c1e481c3c1d0f003203402070303680000015501001402c14805003c0e040399004e020440c60001c1400500e402d94103440d070902400002c2c452541c5170303030046002c2d10122405507050081404020042c2d4028000c25612440e480f00954880c03000c881c148001841550313400030603800c00f03004e100303c0c5640810a2000c0d900c1418a40c4118191092010aa4421030000444182d844000e10309500c80303d400805003e20129201030194141242d40c40040c8000c0c0b00f82800304d94108000001810004051544507000e403c485081543d03d4010a8182c0c078221703803c0c079034000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897032446 1250 897031196 897031207
    0x9040210050f0d0b0306091513030c061a190503030f0a1404060201140a0b10080613060320030607050a0f17090102032e06030b0409050a030503100905070804060e1011 73
    0x6040206e1035005403441c0003010440ca801c0c0901c0012400905025140c840004000080c14059040a90030a601040421041c0c0701c0781c03000000c800002c880107201d441c01414a10b080c1c80250708040c10780b034005018500e807084c0d101c02403d080d402008000203100d00608444481c0c0c2400000c0c0c0300414090b0000f04800c3c00e0401a501c1c443c10050680030614508850b400140d2a04400032141259605100003030303807a021300007030810240c80c0d1160129820010003100f00241e0300c0c40c400d0b199001120000d4000c4400d41019215542102c8c44030000301e083c021410f04030301c502141000c0c00b80318200480c1044185610480d4107000311180245070b074002091010b507224090081120740c540d07000c0354503a801010100109407001c0d1081c2c000301a120700c40142d190b580c9500c604021944041150030f000000d280141007900100c6450300c04081d1807000103129241806524030401c1c1503643c0ea001540d0342e40e41e00b001091480180d1070184a03040030040c80020364841c000d114000c1d50b07030850301e95 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897033696 1250 897032446 897032449
    0x41503051501082d07090e012304050606150702030318010f0306080d1d0d0506040b090303011203080c210a150b04050f0303070614040c050d0209040210050f0d0b 71
    0x41d041c3c2c04441d660b4404400d0744452050b1341400c2040700e0000000d40643d03081e100c03005180c14a95003151700902e16106646d1084201540000390201a02850542880c100c1e22255040311040360081c1c0160048000103845140040314044035000c00350105060601d15000710b8656001606000c4407408850400360b465078101c402700340003503a213190501c810b0f403c00b00c0301c6440c1c000c40c0c034120301801080d905240e03d850723180c4210300d03820700301402480d8142c00e035040c5207a6031a002c0d10141c032000c0c1044041094000c012040728140d8010713401d2a0880211a5812500c0007c01001c04615036814052840311062031032070300080c0008010300c50460b041000c8010102c81039030b5020700080d119408108070510222050720110351080307070082c2c10103d408010038154030540c08020505c62900e140e44503110009803519000768080d40740c0a2141d6240d00c1480411404220060341c0100c9181c001401031a1000195403442341c1e9151403400c01c00c5141d210007032908941d44084102c0c1d01c810030300d0040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897034946 1250 897033696 897033733
    0x150f020d0608061311010201020702190e0705040e01031709100c140708100e0c0604090603200102030d15080f0604021801060903080a05090603010e0901111c090204150305 75
    0x42c0503082c000d8a080e0901000e4441c00e040291402000d11215480064580c0e0003036069568103500540441111203202c08427540c07200490040074201c4d002440400e40321b034844c8080e039003942c2c034202c24504164295290013800410b460010381c40d61038100402c07100c035210138040b251064115210303851500b40c0c0c0c3c90246c66015004681c0d68180c2d00c860001c101138100011301c1908400750300300010700c5054080049050040300045140c00040010300050303141400da0010303044901413100410f1900840001c07031802118000c21038010303401072000c101c6140c0e080c0d0140c91214210341006c10101c0c0e880d0540c80c04c043c6010f03058941c0e90010002c000940c01d1841e070711038000e548028075102c2d56041010161a5046502000e4140740307002c80c0c592982c034003440c1200c1003100700410f031588031343c0e40e110200300c007010840d014440c65090102410104e901c401c2034880071001c036125a406c0c1e481032821a4000d00c01510107aa0003519002c05000c2e128011604101960050010740174007112794184084 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897036196 1250 897034946 897034949
    0x11130612020f210105010e030a3002100b010c1a100e071d190e1308040f091407080105040e070e13030915090603020c030d111801020c090402060304150f020d06 70
    0x1408007452417200180c1d004601003030080e07808010800801d034462b0a40b444c0b51010313810a08040702600c0303c034011640005090015507070001c818009008008011904543c0c5103100a205060320014032941c52051411103070301480490010701c0c03181ea500100040007100b03445488c04198603014117081c00c1d10034104144101c00a60354001e891840f50184090025140b00f400c42e51321042c03010450341541000b4046182da0060051034480c1d4031420b180a0042d8180f0030361024514200d4030546041c61a00441c4c8100c8030741c0c40d00d400c2c50b8a001d0074400909000618a07035203008002000c1014040b107141c0e68060401c0802540340b5030b100340b8020300710021070307000002880742c3e14100c030901546c041d411105a540b070b45005a00c504540400500d54010386005040d1141401d5011071200c80d0b860103009405450000d40d800c420002005a0f11100450381c4207400106840004000d41003080080d500903108480b0000845000076030a01140c10111611300c0c00d50300080e03c0c289106650003800d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897037446 1250 897036196 897036199
    0x618020403020f010806031510211101110a0206040902030624091c050f0d09091e0c02150c0d1a01050304060f110f0d11130612020f210105 61
    0x40c0360a0640c0c00140307910000c078200604202ea4900052000c3d2424443e41c013140312900c90950740e42c00c2801c00b907880055180a80c808800c10042542452803000a046000c203401c10a401c50700c0c5003400c01111140c01c6145190520321812010400680f41e2500910003852141c80050301d07820020200000ca003441c1000c00d006603c0151204400c030101c0080302c002800c115641e20081802000f103141e003002c0140040d040f40104103c2c4c805007040481c410ba40c001c01075482d407004a1b00c95402d8400c440c032091b0044032084115000742031141166010360b40030b5490380100c0e20b01440f00252084030007011034240d00d400b03001081728110145e00307025420380040c2800008940100c4240001c145000060001d04407585030324019501c14180d40c80900007005158604d9a580000b60b540d4402c6d921040740c0456480c41d004516941c61805c4055540e28045c201801e0306080c5000030440d111025140c1030147d04e5800c100348001404500c008040d1207035588621908080c15091490142c0d805030b02c05c5c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897038696 1250 897037446 897037451
    0x604051501090b0a1403130b06041b0c0c0b0f040f05030111580b0315090312010f060305070905061b07081b0316050a030602030c090a06030618 63
    0x3104180c1c0c010351500203841d108038001d900c3d1307410050201c1d910464240d40c0c44a4460010500c9202560707109101d9215028400c840000e0f1105002e02c001c8444231048c0e01600075600d080990500d1042d0b90010585010301c0e4008402c42e00c521100e512a880714061100203900002c0c100b1000070b00d40c03015001800f00324000c2019030a4182000c6d25881031503c1d890920054031040f141084003e00c4603a0b00c0482420140d010803035807021883d11582c0314200c00700300d0a00010b191101c0445003d0441d4800016000d440d0130780b501c0036201e82c210030140c8441c0850009003c6203001403e000090b0b070003001c22110a100851030814040c1c1100c101800d40d00401040110a0042c0e858078821990b07000c442e041d4030411280260890380c10b2801c1a049501680105801c0850503c14a810510b1004d4103e054030824410070f801d00307002d41924812942c107c0100c81040012a80903805540c1c080700d00750000740382c2901d206c00208450429044400425510601840b040401040070703450961800403c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897039946 1250 897038696 897038731
    0x7110105070906030b0d060e010204060e060c1b03030c0a0b040c081c300b031606080f060a12030804030207050d0c0509090307020a0306060e240d02190e060405 70
    0x10305038a0140200f205042d05c41c5810121516182c100454440d0859010845862000f0070315000c1d500c41c0c440c0c2c3c03000811110940c1054a4094125104c00300c1d00030040032088641e200c051182c091001040394140001d1043c015280300501c0018a4103114034030a95807442c091501408010858105865030b500209180508050f90fa13081d42c001d043c030307050191030f89041c0d06020307010304840107201c1a039107030120452280032040d4014001c0740d80210300380c2d500040c440501c908485174501c550303000507880a0100e0310b07542c0d001020a40014000e071503c0e007443d459449200310055005011000a60f90400300700170b1689c1800301d82d01400d0120385681c0401c01e6511010340f1070300355001d1207228aa101c0040ba18136074081040700c10655015140074030442d540e003445002010180300d6a100c00140c100000c0c0c403000300700080b4202448a1201c8980c08440c2018060039447100e10f400ca030003004501c10a03641303036500f010850042c41e064030541d0261521501340000d03140301074500010070110010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897041196 1250 897039946 897039961
    0xd0804030815030f070e011409040f0b0405150405030d201b010e120d06080c090406021c0e07030309080f031c0204030c0f030b0714091017010e07110105 67
    0x2946401c115030542c162450044000000c0c14441c4500101805119000c40002c0100d181408141200d1180182864030282035081c0002500111401050b60608804910000f100720320400c0c0c0103405074045581a44543c800441c00c000152400d4529501c04218010306482e14020011100c1d811203543c09517034825804405507020b28000540324072078007d1448415035095002041001016040340c00d00c070001c42400d9101d034860142003890504040d400300395400300049082510f140501200e07050f56460719120005e4100d81030340c0d250003003544204114807116014140a0311200406482c580e40740d03160183c420a010b0b4806101134001c0240001039207008420303a030b0161700e00da40003020800c41160341f000a125a80005122856210002c940840d400003004140c9203e58094809520345070b5094452120200c0d03500300c446070420042002d42441441c0c05408407841c181140a0110507006c000c010500740c01051002e4160000c10111540c000200081c00303407004001c0107241001c0c2c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897042446 1250 897041196 897041207
    0x30a05030f090613032105090f060a0c0b040b10240305100f0308040e010902130519180e12030408040524031503070504021204062403060605030d080403 67
    0x1003081400e4400858121410f84402046a5640d002c010b40d01100d90b4683c034010030a44a41920040280602402c0d9600d2502440868038040c10041c4010f00001d101020410940c0c000c403031440c10003400c141114002480c252040c0d001c5c520400420240349400115042d000d18250720840d40c48400300b034508001880c079024400c14000600c0c0200d0039644500320b06161902690118441d520118000014004450090401d40d502204c50a56990b030782d00710181640075908003115041040c210400039440c04000c4d200f082d014544460000a58a03a0030058400c07a9500b801122900d4030503568141030144403a00c0020150b048440c21801c040c2c8848006010b44c5c044c89004450101048403500c01c02462a468074507121340681c0d41e8a003031400d6214040d001c4145501901c60030802091a02c0d2074002c0d1074403081c40981c104280c7e607494980d400548840d11450029010721600106a822640c01040c003540c041e86001c140305142c070f014075150003040c0000300c0c10051440240400a0382c4013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897043696 1250 897042446 897042457
    0x141902040e0c0604091e060b0d15080d02101104030312110432030f030d0f091b1401080f0103120311031003050613031704080c0109150b030a0503 64
    0x16100052060080d50101c2d1030504a00855603111201090004180e140ca4100c0c00b500841100240c0c0c6034848004200150382ca58094044120014892214441c8061340020300520a01240415069035400f807203080070303c001c4480380180c202580c0d080b40b802c2140100180150403d05d40c0345000e117140c5008100c00b950700c01d8a602203480700c64143c00421100180e4010380140500326440303100d01300003810141c611081d140e04514443c42000b80f6442d022801d03909000c1001c0281d8602600440030800502181e405079045135990315130f0700049500c54601c84030b05940d030140020151306052035120b40f250003030b0426041200800070130002c90801c1440d80e0440364804400c1490700704080d4264003070020401c40c0189028048104194070748048880c80c11a4010000e070b401e00c1e215060746c03500810f46c1e80b4018005c18081801d007121601c00f103c086d94024081c01c41107090503041c0c0101401e5402060040d107042c400c00c5022210130300984200e003102401200108540c800ca40e44194890244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897044946 1250 897043696 897043699
    0x120907050907050a05070b0c090f010c020f0409021203030c0c06010f081b0f180a06080a0f0b09160915150212090d0602120103060b03030a0207051003060918141902 72
    0x86100041c44d4010300c1070b0350801f54000892032852800c40c0c03001f50540c012504c2c407886004200c5080c0721550090380f15944185e0040d0801851030045010303c005806869800c0f0b1300200c002c0e00304070190300f040c400b07140901c610300c001668803001903000340e2074400d043c0c00901d45038035500c2e0100f04910300080d0030600d0000b00c00c640c00c2c0b04541000040c00400c444040b454021003e40a840365480c19400014812050200704202150b114152207a071290744074401007031003201c440008082210382c40b001c5e80c0102d0810031110080101c0704c4204c9100203d600022016803110344152200350950002030280000d04013541090481d80340083d920b040b116070f0040000710024010000b80c03142c00d00c480305035422407002c1d075542e228901d408038034030024031054900c9458008000f400d881d000c4212060001c846d40200a1a401e10f0208003418090704100b1050598035400003a25105501036600e149440041d540342d000c61905081a4084200c10080302c66040303112a82e000020ba07040403420140c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897046196 1250 897044946 897044957
    0xd020303130309050907030b0108090102160b1b1b0c30010e011a04180c0603050601030207020a080a03020c2d2103180402070f0f26120907050907 64
    0x1042c18240e41c8800f458014a070042a03103400c010111b50140c03c095101442030b13a070a9a245d035048206401c030300844504a103403044002a410100c1c0102400075000419032080d00980c2901402d05041da41c00003036802500036500e001803980c00414000c03010010f1003955000c154130102c3c10425461400d101c2d03c61002c18040300c12406041c42503010036540b083c201d000b000a40a070070560b041c9444601c0c1d0b880c0c2f04508020003140025000c616070b2200c1944061000b440c0390401c1811340c0500002001a41090750920601c000340c0d0310f2200c81802041c4460241010800c0390800030304028071004508c1c05003100c008400c91a81c008000e051402e0040c03512800c51084500c00552500d0442d0f12218510300c0c198002e03a070041022004044081c52403000078200c00270386d4184401c0c3d00441b54003402e07044180c0b02000200d036140011054007031003442c000c4014186407140340108207403c0182c03c1035102c0880d851083c0d1010705142900502d25200408c1924582070010700c0c0744100034644001c114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897047446 1250 897046196 897046231
    0xf040e0703050f07030c050a06020d0804031202040e040201080601020c01020616090312020304170a33150501141608370905060a02070303050912060a0c030506030d020303 75
    0x680620482001d55480340036100010510b14580d56186201d00045c0c40d0040540c000007003919100d9118000c99007140c024282d1000d01d90b04c141e4401c1c400400903414003442800c41c4420002610051005c5e0006ca1480340060a0600004082c40030007400c0b079041d58070416045031140c3e000100264000c80711042445103404092046451042c20342c0b0080200041d0741c0c0c0140000c0c0c02101a0003542c2030302c9010358800030140d65813070365491074034009007040e0600c4a007104c2c1152802204045644000c200001c80180c00d440c0408440d02c00109c5404080c1080e0140129a8003002d01d0140100c0101054205818403080c04418101c8000c024003690000400c82840000c5030742d940048400c64001260500d410100b50013000041000a800142656408201c3d441c00001f9240c1c03040c5681e0041c41052b00b543d07420f40d411350210704980d89c0310340001c200d005141d804000140c40740c07640c1c4001044403e4488009001d5800c00b4013291300c02d0304103002d960310b115800411747c1c0e4000c1c103144004c10b440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897048696 1250 897047446 897047471
    0xd0f1202070b0114150d050702010c021f050a02160b161d090603010b0d030c02091015210614120109031403272a010e0f13020307200c0f04 61
    0x6500c0f005c0c112000d10070218028000c2c964503031200d80304007000d4000340954540380c0022600c90801c0c0c449a00700424241444441e100030350b001580c080000f84005291684411f107201540c841d17400100c5110410303500704060f09440c041440072403203440c201104045891440c0c1c41000396400491401003100c1070025003540d909400880000340003900120004000c0d05009107540303001c580a03401880c101c0089403070b0281c048928002c891042c081030141c40d1214030102c80710001004041d4081d241201c000c01840c1c0c0a12842c0010660b0b004c01d090019849001d200c81800e103400900c0050b4034002c0c00001003070300034480c11402003848541682e00d955250100e003181c201c40b00c2e800c0718119600171201503000700064000110b110311007200c00010408041400b02d9a0b6051b2080c00114040e550b41c481d401d04040b844c0f9030fa00300a0451045032140d51020040b600201c0701c4000043e0a80303412202d030098141104c1d034030b19155002d000703082c510101007541040c40c1c01c0414007031581c0b10b1001080f07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897049946 1250 897048696 897048709
    0x11802180603010e0702010c020a030f0f0c0b150a05060a050a08220605070813030e010c0f1203021c0b220209040e010c09122102030c0d0f1202070b0114 67
    0x1540c034010039007500d03940c4a9803c180c00b45021281c0c0b501541c070703024840c041d0034000107540082036416074480c0c0011510b28021603a100540095000340040d0280c01000101072411451180d21103100103400089a0420405c0c80c0e02503611150003440704101a40c2b080f503115084419401b11410541d596445000d003442040c0b074012011069045001d0005041000a8000350300454003640d03007035150788034640c601c54503800900004001c6075510320b03d81215405400c20018040c02403004103018012510b42e002802c0102189100192340005d4042c801810250104600c9000c0e100800c00c0e07c4443c00403070805103d0301c40549620f240d078101c4a0b107a060b69012074085030300c0a001800a0a441c0d03030130b54007815400325000302068103840080784041025220000007500301c403076400d000e585411401002070000c02c42030110302081100507440181042411800c4490380c3d0703007114000d1b030828014400c1c001c2d0184504114010010640400c0103d003102c0d05641b680c81d0716840d1030502c0701c0014036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897051196 1250 897049946 897049987
    0x1407051801410a2310030f09051606051c02160204090609020103110c03040915051009031a0705031f090f1d03030f131704080a060c08011802 62
    0x1401c06901e400d03442800c06000052150140a50b038032085151203802196030300b403a86071300f410010700320403429083d4038016124105484050400085c8111001d02c110265540414151506d512503120903105008a0f040303100103142c10300e0941d003094040801d004101000100340490640c011460001900f84030b1600046141d0041c42085602944c0c40d003d80503144c101e00c181d010034038060441444401c40d5040703503080350818000d98585814210000001c05102d400038200d41c02210b40030402d5100c02078202e610344100c2c1c8404048030700d945403201080c949400519100404c1e02c05120050760400140e0b03400100340701c29184901c0941e50040c0f034001056002c020207a051a921982d5001c2c1a031244101c580f02400e070a01000306a01160340c1c80c0303c19180001e8000001c000201c42d099004000301100748600810342551078008030404050304550003401d810b4020042400030444907100300300e041a02824599000d42c58501c0810890548030156041c850b00054402d4040b07400304070546 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897052446 1250 897051196 897051269
    0x120405070f0303021516020d081509040b09060604060522090507060e03150402060403020d1e201005030a0c03020408010509011514060702060702040906091407051801 73
    0x815203540e428000d50305d00d4440514960140b0660105030130003c20305507529002029001882c000411050440d40384600510380c0c3d05411072203006000580c1c8903142c0b54051400707240e4a01f11401c11080d11405d045001c0d148510039403a1841c01c01c45611621008240400198400b80381c111050841708054000b10500601074000d480001c0340d00c41e00042144401c03103064040307810540668413803004c440c40603280a544200e082c03004000615104800c0d4025920501109031540d4821180003000800d0306021501c0f4070800c1a418003242c00c2c5104140d140800700d800300c0c0140c1003440c3c040c0180c44090300e000710700ca40f16964118440d00a4040303e004102e124000c111600e0541704035802481c20700840065003001402c006100d5407508840c00c00280c00400c0301340b60942c1d6030b003000400d40c0203000c00c0b6007280c0c450340f0150200da083c0c8200d140c140c1c0240b00c0c81020b603030200707030244c20a0130301d81259200c1c030b40b01c140c0043ca1230180304400e810744640d412030070086121503e81004030542c0c0c0d80c0e0785 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897053696 1250 897052446 897052469
    0x9081e0c120304080c071e0602011104090e0304080307110112090201090308181c02011106090c0121021c0612050c300a11040515010309080d020c150f0c12040507 71
    0xa42c440004503461912000601f4404840c5c3e02e81c40203d00766000b6403944138070020b003440706100f0300220354446003e2888038801c49103441d607902403403800c1d41c1290708107036101d1500781d000030320650b0003200c01044606050420031549540d580042e206084ca800301505e007010202d260706120184802e20380700c1500051142450303219400140041c0d00c40310000f2030010b141c0b43c00f0342c08030003000180e0320700801c0744101401003441c83c007004441d4400c4180300314030b20b00c0d00100341c00602e0b0500d20042c41c01100d1490759009204c442e04000702940c1c455400803194503801d0429802251000c6000c00d00180304499020f0a09040c4c105d41e00446a0030490541c20001c00c85010b1481d0300006001c0c5107180315035440b04c40100c0d000f0802c41110011580a00400100702d00c0ca11035602c00c0e44540c00842c070883c849420800310014100c101d03004113001900c039034006144501803807500300042d40c0c0081e030f8a000c0741c00d43c98485003c140d82e00036020b40c0c0c441c040e850400328040080034800307900988540d6105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897054946 1250 897053696 897053699
    0x20d110109090e251a0304020409060618140106050f0f04080102160302070504090209190f050a06170303151e090f04031106010501091a040302030109081e0c120304080c07 75
    0x7080d2100203c4c4131032074440c101e2411501900d018040040300700c070090400240702d220300c1803552600c1c0c1d200900490744181da0b10f012a00007410382c8510000fa120307410b41c5d420f00020900111040f6004c034041070500c828000d00400103236520908442c1980750554141d5243c4a958a40c030503540966000900703207500100d6007852543c65442c4011456000e41d0840d0181ca07520320920040320601600650000c0383e5900064051550b0b6020800b40103503424000350a078804101c1c038040b204191800001191101010091301041200111511180002452441c10b0500c50300c03e1a5814801c0301e4000d034101c03100c003040480f8080940004040c06048500e880c03901131a12103d0200c11581100440c0801c001002c9100700000c030503060354010717107402024504044490051455507028840c004100300008001602d0038090303924a6440356010640b50744420070722610406034010206641c15050241c000e90780f00000e0380c000303807040b04400c09940f0388880c144020144144145658503200d540c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897056196 1250 897054946 897054971
    0x7060203041a04080f16020d0c06120b0901120512030a1b050903060f2a0417060c190309020d140c0d050715180b09030613020d11010909 60
    0x941c82180700e000d007007441c465081900100b088040e540a405a407050004004a0014400608581050a48940d9075031041c1d4001842003010310b07000c907450010404100491500300c1070745690b11451f01c105100d16080c2c01e0218100090502c201c9000c1a68203031090148002440000080d04c0c1a000155030381c030380101c2d03401c041e01c40182c280b50404172480c1460341d02c0c0c0c802e0742503c07080c081c001c02130302c143d440d0852071104542c4040c2454500d01c25110001c0841301c082e8803011261802068442c0e1624034244407010709000c440000710803600064100200011103d04803070314554100300007880f81c4201c6408400604500000035080300d0010340c003101b0f0010708407004004c6e8488030200c440a100b4074041c00001402801c0007885030740820b406101c400e008441c0303120501c20a1070720101a4400c0c081c150169415980002d904032000070b01506030b8142807210591040001c029001200c1580e40810151031100801400b9880a503d82007616803090154000902c1000c4042c09200710510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897057446 1250 897056196 897056201
    0x80307030606120501081e030d0e010f06090b06040306051f08150912041a0f07140f120a0e0f060d062318041a152706060a050403080706 60
    0x80c240031402420460450444501445040e17aa00c18060115001070581f00d0719005402c1259000c030b0b00040c00148924040361142442c0307504071400104012242070301200440703003c3e4118116060a010850701c4a4450300f04a40840303600040014442ea03034406610482c200c401220038003000c0401d00081d0b040e100103040b19200b85044800c02503174880442e1255203485168403160428003e1104100c1c10346000031140010000201040c034205292070f0072410342c0d01c9108111002d0041086007401110104074504401264900404140724a04075a1100d4055180030900300031062a05034819182d0040340701119001601c0c40f80c49079445c44651010f030080d4043c0c1d65824040020355440310011181b00018040054000560103d20300c0c41d81608182c0204184c0e11101d82500b030205c440400e82146215102008101009143c1d040c10020303d07400a00a01060301e0302c1c1c0d403e08690340701c1206000e41052084400950324a0104c800f0740b1103028503400900030f80e10210b00380c4180101074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897058696 1250 897057446 897057449
    0x103080c0a020a060f080a0501060f0c151d06090d2c0a091a0d15051b0c0304171c180b070b0a0c0203040305060a0906021207020d030c020304031a040f0803070306 71
    0x1d44540300c6c0c603a50714a046085803030901c1442c000402d82c2040ea541c80d80124101c1d81c4d80342c083c6480044201c45171900c80c0c195001e5444c0060040140174050f031700100c052002c590800882d101410b511550b0b500024440046101c90b19a9140c0e1103042408101901c203402426a9015001d6aa05661003440b90000e200342115108040702e103c030307401c055181c034840c1c0fa040e840d441030961802000803002c42004110080001c080072400205941e2881d203101c1c00381003c00d000c6002541c0d62810905501d2140c0c0d400c0c4c08112081d0b2001041c0720001d01c52400c030b0003c203285458841d607543c00740c401124601034070b60300c90700300c0341c100241500a109900310404d00c1039000c408280101c4150761422641c920a51002800c650420004121400010740110074000e00503c0c015003880c801c420007009507401070302c0f1240940d02c100106000183c040c0540010304603640003a5040a10710703203520060f82d030440f1905420b998403000080c1002001500c4521300c0384c200e95282e8036483d040358040c0003040503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897059946 1250 897058696 897058727
    0x20d09140609010b010c1203020f0d150b040e0435090315010e041509021203030402030706050412171306020a0b060904030e06031902130509010e01050102060103080c0a020a06 77
    0x100d07000600719003014090104843e006030340d0608a40b41039101c002021074802c070a001015005c00c25100703078007551006040f070404a1340000418100c5a5208003154010b41d20a40e01c9200500042003a40f01008126501a8105410707060034442c400011314100c14000c0040d00032420f0200c01c608550445000d0705400300180c0442e800f81070003c02c0503c10203424840c2d024220441400030b00002c1522408444040e401f07000030401c2c01e82540025a12139958040500542c0040304000546c030f01085a00001c1c0b45a00346240340c40e040440320401d080303004402602c04144c002911000485800441e03004120b449030190030a80c5441009440b81d4014000b07a661032610b0001c9480e03440c0c4505141e0240741d25071220443c00c1420410710031150001403d440c8907045003904110707446814001003c000707000e829205540b07420002000303034424040e041411410010001030210b640c0014416041d01e4100c2c0301030740c8850400e513000d0b1903c4007420000b5000260601c00085807034024402e8803441c0e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897061196 1250 897059946 897059953
    0x602010b0f040f0b0307063c20150a0506010e2404030f06060f090506060d050603031201080601050a210b041b090203060f03030a0c11040e0303130c0e16050904020d0914 74
    0x26081c08c40c407640201c001c03000d40c0b003500d180d11390941a01070710380c02000c2d010065075540031041d2158007908103180d003072055503080100010003e02c0741e041d1107003a51185090815071210680c0300003003840010081c000c0040f1031040b070f0103000011224015900115404082135101c84203919010700030b05401d104800b081001e80c8004900d06210b0701940d403068602401c07841c180206008048042c2c00c0152410b9050300003003180c1c03c107420542d40c41d48d0103404c10000070a03840d4502400d00140c6030181c2e00699011010b4000b01c500301d844040c072221419009146007285480314240100b000c0380901d121044a41102800502030000f50080e42c89080122145a201004903050584a11501e0750303990005581614050000340c0f08101e24040c113a000e0300005603c20030602c040d15590040d11082d80b51042d00344460104041d401c210405408010400482402d00c0f00102d084040d2101004003480f0001c10f19200070307281d60b03054a8481910040501c00e4522504107010194640c1010b04910301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897062446 1250 897061196 897061247
    0xc0c1009051618090201050f0309010c11030f0708030601030e030d090210110c041d030c07150203040b0307120f050106080703051b0f0306030a020301090c0f0602010b0f040f0b030706 80
    0x81100d5503102c101c41c284944003601803121426080200010002241841010b000000ea0a007200d8040c500c6503080d1400043d500314801c5014010114621050910340c0c402c0000d117200000030001d55038443d90060302c00b603d9450302c00068002e0810101e00006c3c030b04c00812041540078540d00316502090013641ca11510418074901103d40080462101100e80e2000d02c80074007506003035001c44880b0148401600000c1014184d2a045901c940d01d5164140d122a03803d105000040705103000001b844e0008624092500000300070500000300f02c101071013240720021340d0704021604000d40407400c100b0308000b950f849100141040d2000d56400b00040d181000040545001204180d041c00351000c0300703801c0c20442a10f0710b909074001800181c041c02003810b00c40060714240580300603035100700f640e030310241c2c20018031005c45d00d11a4000021a81400800400c9458641d800c280011085d01d0100c2c11031808102d810142c03400307402e00ca40500c40c528001400e641e0010900c3c919000b8101c2002c00c2c103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897063696 1250 897062446 897062473
    0x7050d210203090d020d020310020f090103140f0718080a0c14010f0509041812081801090308010b0d02130803090109080307050706030510030b010e07110f12030c0c100905 75
    0x7400b401c4641d5400001d070030240d0015181646c0c5600381c841c8003e0495201d000100d1408041e41c001030795042ca001000302d52030f200c03582c050158403040d031012071400c1018602101c1c2000343c09006008001400701c1c0000056605c0410640e01019012040407203001d0b501c503190554180c1e403a441b40340806000750b10b05003a07640c0310780038049a4000a0340c40e01d00b80500c1108105c001c21031040300d00401910002e421000501d40d01494a20550300d445078016450050340d00d000f8400503e50b0701e403603a454982c5c0440003e810040b500e043d136120300c44480e02e0b52a0968040000d00c9041d540d83c0140418110004020000100505254100380d803901120395444250381e07503d000b584402480c03074000060071f02206100c3d91045902c0f0822500000c0001c0d0749031030700c1c15a4002030304070003260300c1c10000300505150844001040c81101d4070043c004072000118084c3c030f03004503072018055102c0001c080f549901c200f800391000d07690704200742c03011a0113191702c50008281d50b950440b5140101c03ca5807810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897064946 1250 897063696 897063703
    0x60b090102070b180316080606120a1707060e07140109030b0606070204021603020d080c04060206190615090806070503070f051e03040b1905130204020c07050d2102 72
    0x148241070300181001c50500304010815041940b48002c090110300720140c1980d401c00045803e240f80e40a040c0c001401c0610450421600800581c05110180188115180006811002c468115100702c0c0c2c42a660b807020503192240d98406010f140c2003425801524001003484821140107000d2484451205070040d00c0031030942c80082d1526010000040f52410090003d108141c0300400051810b04821200190408a1402038005900004201103d2900301e1401a000380d68441143c0c1800d01e040c4000399101d03402030490301c807503001e03040c42040d14946030406c2d00a08007900303ca410005000340c0c002c1c69204180302d1408a803003000c0224007146d0181c2e00f142e00640c030a45da0003048080948081d9440e900045091340c44542602e0301d9080c0344011406180624414100746409082c0036800e1030ba2a0240b01d0f080c4a80c0740b401c3c0a01c07a00f001c043d030314a00702d03590684002d6201e1010070003c50400030381c1e40c4540e030002d428244d030008000400192003600d844a03a41c3d070000c00e003680000c0307a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897066196 1250 897064946 897064957
    0x708060606040603180203070b04091a0904080901140f0c060a060521210703020d03060f050d0c08070e070f09060206010e180106080708211b0f0303100603060b 70
    0x41001c1c0800041c030226100e07030415081c00c081c125524400a40950101c0c1c80d0485a0307000c050140c1740401c1c103008040c0103005456614002c3c48203030484a110500040c005880604024004000010320203000c0c0d0003914600c4080c4030301d480058075402920903041042d4072050070000580102000242035443e0b0340324240a660002e400c0c02c48503074080d0041c0c14203c82d4003010203602d116010b01e504421000700786803413621108114080d00ca00542c50060f00d4600704050340c40506080000500410715680c10b06400c0364000c4074400865102c50821050f87c0440e41c002c3c0e4841c4c0250324005c41c08800c1d40100d140126200c0e0b94001001e500741200300e540411500035000182c10920040009507806003500e03410220701c9058840600108036200d00312205070f4072001190304500e0040008080c2030006110014807083c1c81e111800c0059200c12045c41110400031a1a24025009181c241c08000d0201f0100c141411281c0d20700f86048e04101418103072041c880000c2c203264020804400c03620a494 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897067446 1250 897066196 897066199
    0x40503010609150b0c0f0105041217040b0c0f0708040b0a081b07060f0b031626060a02160f080304150605063a050108160b041701110706020c07080606 66
    0xb030400440c44c001c3d501017031049551380301e00c0003200e81410702071103140c1c0698455440d00c603110f90b4400d0b0140c000170100441002a94034a801c000100f04081c0d03550b5885a802101c046c3d40340d22007510542c25014007000a0445007000c9000300c1c02e4950580100120800b40d103510889541d440c1000002071810620100110742c24464000002c403950071185130b0615410700420155030070b070086403601c440141010003d0700009400c0000b1460f419000310a142000c103040e0550200070700b03060343e488010740084020750380050403680000d80013040c0d40c00d141e0b0280c00c82c1c40b400c6032401d0005190f04240c1c1e0555031181c0c070519030341c0e411071244104000c40b140a04464102401500503071480c210680f600d801345181082072010050b180808046504803008000485504040256180c200411485040c80c290090140905410078081e00c0480ba2076850420380c1c0040703103501c9409024050030103074400c40003041c120100607168000c0c0010840b101c0844920a80d102900b40d17944405940c0907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897068696 1250 897067446 897067481
    0xb010906171507140d0506090a0c0219020d061508010e011b0c060e010c030905010b0d2613060e011d0a1403030c191a06060406110f1002040503010609 66
    0x180b050300c0c14910b000d58086041d05140400b000c501540c0340315680724a46410000d40d86030100040751500034581604010031810410180c1d40304040a995020800c185242034090920b900e800c40d034400b0a82e40070b543d4040801d02c9018010055048040709500a6206035400d0108090321480140700e884000600d0050303d040b4041554420341c1d179120401c60a46480f526000b000500c03010034011080f29402c90317a00000e4040450408508461030310002922500e05c88030544085264610400c007080c85100301e5400c1c00020b503080803020303c6840325403a940103140030005a101c1e04603620703075282c40342030301c581d500084040d0000801800541c24190f010901300b100f0b11207004500800d19031000b01808491411380000442e80c03078483c3e096507030108001419410790410055041c18884642000c200312041e0030043c000420a00031030040c1400c03c40c80c6049005a4401003000720380d03815044082e540c2900400e2602c001a44c81805840d001c0c2d17083c07007000110000a8800d03a072500021300d090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897069946 1250 897068696 897068713
    0x1d0f030f030c131e140604062d05030402091e041202030708040902090a06050c030702090a2a1407030c060b01031e02190503092d0a0b01090617 63
    0x141810740001d0051440800b0500c01404142e46406825018040d407906800c004d00005016443c95001e82d04064111002c1004e00c21103502d0354010f440070b0350540e0401031240342c1c04030070302c196000c42a0041400c0d100d071000702d18942034000005600543c000c2d80c50303000355a01e0460307034603042041101000d104800100000c000c00c000a144c217050000a1054038a01b820703c1e252004190819005a070009600081c9031880e0724200d15800010314040c00c0c50b82c2030004286078070751203016a04000e40900031910000d180341d40143e005402850102403915450700b421804008110703022041040445c1c101180750001e81d40c1407055845255055603100e00034101581c603180034198004110b03061640b11191a40d4080c2400a40d01c0d2000e0880001a25447d0410020fa058107046d40c40c0c4091000c200140603145c00045008030040c10304d540e1101014500c1c0c24aa01c400c1c4100003090700034041d00c0002130070000d0380100141210346684080c000a601c50001c0c031154961007031556074540c0054035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897071196 1250 897069946 897069967
    0xd06060302040f1b0c1416080106050312181f020c0102060702070f062a0f1707020d0f03140c030703080c040b041e0f0b0c0613150911131d0f03 63
    0x5102400521031b440544030f08111185480c507044d000101030f001301c079294200f031240300002d100300340090034210020000c01d42c0e40c3d04c14075185e00c0703513000d4224440c84401144a140e103c03180300100140701c0b0984401411180b5000a40b1000e46510355401401503002041c2e40e00e01c0081d00d1025036409000080c042442d015007038450035900810309591107032540e42c0e4030502c03c0c26003919807c2c038001c404c2000101900d14003000c000104e4400c0c40242d04007442401c016884250754041c603150302c0800c80240a00c64102030703c20384000c0d801c0c1d5000c40c00000d0080700a00c004006040228402d85522a490315080412030042c02103000310345070500b0074001040546950240c01a040405086c81c40d42c00da200c04442c610072450781c20400d04a030700020f804803002000c100031a13211021080c50400303908036548078404540e2003032600400684a4128109110102c50840074032503000345059800030011040c0d0000d417500e958002c020a505400071260b028010898444440040c1e001e903260100c0e111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897072446 1250 897071196 897071207
    0x6030a090c090e03040503060a023a09081c0e0d180806010602060717041109070e060c0607030612052505060c07170c13020d0b0d06060302040f1b 64
    0xd410307100d14541c000c00003450441407291144031000d85019503038841c10309050521303000001d4882d40c4007920420125540148079090045030085131160500d403184c40112922034400c0480d8002025454920103404204000d0b0042c00841008110b0550000c540c0640400300c035241c55081e000ea82161140135052882102030f40c0c0012150600b0038015512040c2140c6040c4003600000302580c400414812070540040d03464401e40c04035150310000340317070039a034000741d03210712003001805500281d000c40d800070b02070190007244a4002e44015210603202040c40e603211410f440c0440460b14092012a8461080a020340000e400000070801c2e40b00c0308080c0c01d000d104440032086030054009020407140d681c600201780803402000107088060402c140100d4151001020107403075401250395050644031180e130600c10240113180180c13295884200000a00855081c44e030b4044130f100e10000810115a1040d400e40c0d00175941004003103140d2280000b2900f03210401c480302c00e6880149480d407440380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897073696 1250 897072446 897072461
    0x7030b180606070804170d0207090b1320070c140d0218090c0409030507020906190e060d0507030b07170126010b06030a09111e06220f0611070506030a 66
    0x8112040ca010740e51404240c0c45900038408006d03503044181c529002039030410000d0082c01300e15608012001f804400643d01801c9180c0283c007140c3c5481c218044020700413061101e45a080356581d90360101480d242c4c0820303d00b405002c81290308003140042c2d50426400e80001e1744d0b030243c221086882c800c3e4099455003001030000400d44184210541e054640b030141ca6a214840d0701da0580341c0c06581304003d07500100911260050304804001c000d080300d00c2c040b020880346c0d0009000c0a80c1c440c40e001c504503011616018210340314a40b0004100b0142d0603c092045145556036a010440b43ca00803410701400c0c07085c0b000c1241d070070101f81080320b040315125085c1070302d50000280c4c55200300c0110301079400403a00c80110a641d01202014000102540700c100b2800311907840141d80c02e9900c200560a0035000c40340503203030108070000180c21007401d41b441c8102081143c00030ba0741d202030a08200180c0c1c0288000550000b2280200080008006d4252440103011500790395aa001c040002c000d003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897074946 1250 897073696 897073703
    0x20a08030f0f16020a0306140a05090c040c020f06040b01030506010b09060a0806011205010e01090b030a150b1c06021b150105010311090604090b10081317040801050f07030b18060607 80
    0x6050f8900c00590314421381d280118401d20002c0399407819001c0001650900421801e0b040b41490104401c0b04030200741c403140000e003128001360078404440c00300d103440c0c86c42482804510429042c0001d200f40c0d082e509040700e1107803044500c2a85c9070945c01c40325001c2d450704140c0101040c85421001402420b21382c2d8020018074203408400880c54001d030643d1030a90044510681d1400103001c3e801d45801401201303c000c0d4000e10020403d5600c9a41c1140700d480003030155559042000426501c4521950031161203d000c21390b04209814030704c000307600c00c8240c002d0001004800380f12188000c580c080f8801c001d180c1480c0103a2030040150041d01403030300c0819004104114030076296030340c1c0d0058400350140c9000014a0a213910a114121104608a00a2003500400c000b12108019030800215038131142d1141110385481c40c84c8658001d80d000b40040d54241802c0148400c80d07200d60621813001d0f41d405114082c0000c1c02e01411a41c8103400d4140000800001402c030f003400303001030103542c7c031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897076196 1250 897074946 897074977
    0x80a050c0a030c02040c030209150f0c03030403090603052d0a06270c05030105031c0201090b010602010e070603051504051b0c06070801051509010806030721020a08030f0f 75
    0x24003a92180c1032641884088020403090b155040660800d48aa0002083d942c201149007808000018001075400c2035100b4026000140b0a130340c60300003100303031600f03201180102d130745a00341440c001e400100c2e14040d01d80001c0c42c1c080080d14443c0f0b41400c400c0d10703014210b80141c400f686140e80c14600740f402010340c041180c40d030100244e045003240100005140c14600011690f02210289059800141c050010811b050005002c1030351301090070302c51401583c0a80d8442441003034241d01400c400c0002400180e203c400008009806420000045c1070740000d80d00042c0e02c400741a8101d4005841c1e10740d410000074440b04a80c201035008a420516551502c04004d09054185840c0e0307104040641030740d00502e06010089400000a501401084a40300c1c00102d04003044181805201140d0781003100c1d1102117108c0341c8051240a014184024440486429145240c44101c0324114100d01409511700000340f0081c010041c0c0c0d03a2036840c0340c0950b140c244020082150b641103a403e503403200e44d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897077446 1250 897076196 897076207
    0x71b03050f0708060c031519090615110d1d030f07060e011b0b0412031d031905030f0402150415031e050610110c04020403150501120b04080a05 63
    0x2001001a400610001002005143d040a40b0141440f001410741078030072600b03005200701c1800c0108000e184030b000340c440b48010b140c0ca1107040520003083e0f2024141c54036050010408401411040c0103038403c90711031404040c05907810f61303940d11044510744009540c11440c00361220710083e01c01583c40307009084030b1141c0106481c25007004e4503680710710080713842902045802e5030404213020020190300c0c103030110203030305445840b40f4041c01080104100d40c880502c2041c2802079104454860101d25110303600400745000d00e541ba800340b14149449110b406203016198030450480748100c01c0d11a10300740b0303611294248a072482c0307030052914100c0000d01010801e5103841083c501d0710300075554042082c401c2d144011601110840701c0c501c8840c2000208845525118a00014654070f41707042d0302c100d031110603841d041080d8542d0701588507000090000a10211060001030000c1104080020f43d03600d034603404007800c2d01c8400810409002002038045240c850150040b40f03002c0c00c2107451318 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897078696 1250 897077446 897077453
    0x110112020d0b030705060f040905060d1406010503210f070302010221040b070809030a0e0f1201150b070c090209040b0d0f15060f09020706180b040512040b071b03 71
    0x240c02420722900c0311030755405000701510f07040000d4030040200f912071a03c0c11a100c030310f502284c41203000e40c210050300c40c00403801035200d04c02201d1310680c0207468200c1c2c030314072910510b44a80081c442c5611a1050018402d9550802030840e000d9540044c042c40c60300d90303144030350740090b00524015029035601740000007112100401c0607100e0007110740e0f0400e4500e0a4902a105030320050030450402c8204000c000f108c52000080f03408011450404c0b9401424490000301c056600d10212600803c04e5044c0c0c0100c4a0150800c0951841941c0c844002640f07940d2100b141f13000c0d54038003403c000d680c0708080102c280240e00402d035116003c0c2000c5030389000c26022a4120002c440704403440301038601c003030040c840d240001307824404201c1000c0c8080c0d4a4030400c154601c40701d005145000b513000070104200885680708104104042003402c05c00002d43c01c00d0345101c081114280c50b94064010404409451842113505030f4940501190515140d40c5507140e00d0380080071003031480c0c8416000403010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897079946 1250 897078696 897078701
    0x601080a02012a0b09100b1e0a24020c060a051603090807060504030219080c01050901020709140103020118080706200616020f0111190504092307051204110112 70
    0x1409001e0a1005042030403000e40352611806d4503250840c905a40c04034180c7d00c00c01c51143e24502c21000c00c100107122400609019480d030300c5501500100140d000d0030f40580400860200e40503025a0540048481441068403d02c3d00003000690300304990f85d10fa00c0540b00d2010741500a103403000c241500c032a20145404e002e90081c401041c4041010011171811010041c2c1c03d00c007400880001e03d190001980d640c041c425281410b224003c5240d003480e900c01c0211b200241080070040c8010400300ba50591401020301040c1d0010b040e1141c0d040801051100b810116180c6000420405207009001c032402c0003903603483c2024000d4481c0c90902c5001c02c000640c0503240119a200c078026114074042d141141b03942d1295410f905203c3c2c1c150007d4100e4041d101200300c140c0508510751060f041c102c3c0da41c480c5412541509142101c0414102c0c11200c4c2241f00a901c401009100c0c1c0b2001026100d5002e591000c900c80d04080c03000500051102d400240d4000c0181007998640d02d810b25030606 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897081196 1250 897079946 897080027
    0x8070303120b1903030305060f04050406051605040f1a07080706050a06081b0603070225030201120e0a15110a08040605070c0314031b0c16080601080a0201 68
    0xa004000c0140d6801060300c2510641c00e8101e840c001c0d0f00c426040c0318040d0109030700c00a010315540d6000114640c17540d001c1e000c00004001c0c0100030a01d003d240c0000148002d03103007102840402d40f0030429160059080b10281da04d56026000c00758074107a02c030b052034402e20050f0300b29040c044c00b2220004410700007405200b84150804142454002051021500694002c0031580d03c004a60481c4410b100c00c2e000c207040d01a101ca55403030307480b45801d070718150000280441111110341281200b421003998842628400d80e07031070440c3c0f401c00802209407409100c07050342e180c01c00c081083c0050500c0580c0c00c0016941c0342c1c003090410300320030641420b820100486002c503ca0700704202c10480e1501c074056001c481801c7c1303000c6007419501c0c018800743c0d0f60100720400000002c00305186824645031121079240c41c0b10700c1581c8180c4111001c0e11201d0f040e41941c0300d0500d50308041801c00002c074a441c180c501c164003c060101d483c1e001110042240d030344612080c0c041d0002108441182d8001d01c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897082446 1250 897081196 897081203
    0x1218010506011b1a04050309131a13060806090f0c0306060901060818100e070b0c06040201260c07061a0f0415050901170607020307020a090c0516062f040618080703 72
    0x1030304c800810f01400042143d010180d4603140c580150690f1540041c58401c2c2c15060540d0140003120020302f0340c000405994018030314601c6644200500c1d0320b030014006039041c07240810348024080601c10f055a49009a4040e68401d4a110052001c14410126076500a0100c5d00740b0340d040d00c0b414206400c14090043c2004100d41311402521452010407030f02004002c07031400d80c4d14200701030503841d440702c8004d4002070411840d560010b80c1e21503c14044400070070400710b0840d0718144040d1000182e071114008443d42070820000d403807418207880c407803104501c1c068001c8034031140d03100401006080881d0500000d681e130710340100e02d07900d401d01c0c02e5000e4005988030030031402007800660300e4803034000c00c82d0086600c00c00282005840381d0140008407800c1c0000801c1244441005407114010f01c210641e072940203010321004d101c02ca4220500100b00b5495901405008041c1d801012000c101c3c0103c10580401040082c0c0303204204440341010440d01d603180c025195a4001d0800c511544140d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897083696 1250 897082446 897082453
    0x120f090c130e070b040305030a0809100501180b181501030905150106170c09040c050705061e010603200702030a051614010c020f1e061218010506011b1a0405 69
    0x2e108104103e4a03004d44280340940d424540f45503540d139601d01c1030540c00300401c58a500410042c41040144211070310560f40148281c1da11381c984400c54a80c42d0f070240c588a41001481200390074512103101e180c5072521007100ca26501c00e104c00c03616000c0920464109660703020341c0d4001c550103020540900303550441680d02540740400c01044e43c554442d1400b285400c2c0802d0101803507180c42202c6902e003050b1408035280c19900015103a9000f032004c090321902641007000b014022084000011402164420031a40d0300c17500101c0803912444607203060b00d000500120442c00c85030b006030209078802011150f081100741d0f02d950800b0100800720039184003108040c400780c0ca80700840e10000c4820310340342e00b00860316000901c800c07005010240c0201e403c000d510302442d601d048181e0070010003070401540d0303108151074680e0350300c41210a03241d40d0b09491403010142c8810301030280076023016075600e0204d501d0f5128224001094020488203d02e46035030031900b80148841d400d00c82c901a1025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897084946 1250 897083696 897083711
    0x10f3009050c09060a0e04141606081b13031b03020301110a020f01090b07050d0b060c030418060e0414030c0109030504030b090c130216062f120f090c13 67
    0x2400f00302e10003c4c120070312803000c0c24401c1c00300c522031340340d429400b0fa0004c02c24210a2800c039445428145030008000c1e8000800c07402040b1180c00180050107401d58030000c1241c0030081c00c15100c24026100e01081c90140c6141c100301040804032032484030f01001034032000c0d0903a00d81c0040d0854916603c004100e41000c28414220354050152a1003100100c00911403801d00d03568461016800400034001d0060100d50210041c803a9488940a850041c188a41c1d5451010303400c0c0da00d800070301c40d60030500d050801102c2180240d005940031900d540b543c644c1c640e102d56840194106191240604620090155204d0580c00b4081c08180600030b48500343c2e503d0450800e620f014100401c0804550701c03182565450b912041c03040c040c259240480148c0b200101d150b2000f9030f00560602601c154103201c00b64512410706501c015504c000c01040c40044c0103111a000c02c28001e8851070301d070300140c90000512505000c003981e03502441c1c2e8001d443c181c540100001d03400ea403c0c2c1210b520015982c515 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897086196 1250 897084946 897084949
    0x40803030a0603140f06060915042f04180e0a06020d02070b0a0209030615041d010f050105030d09030303020706060905041b050609061b030424020705010f3009050c 72
    0x541c8502e1342d000001030f22014070b1485945070784160107804a40200010400641020b90112190b107a81c24024824480d40003200c100d02881c03604c00c9503181601c40040c12401d0110320f100116011501065400b6050f020305d00c014100400a040700300c1414043c3c603050900058252005194454028000584540413804c2c411010907000300820002841048014000d550025a0f154082003040800045107064808100604500c016100608035010940b1049140640004034000400780c020000f03030307076074500b010f81c0e401401032110007046001d0000c0c80403e20039001003506038000c0f040072460940e1040c00d042140e004603030680b540c0860b91422080202c442c0b0b000001004200c170301c0390034202e210380001e4052050000000070f2072444003408045182c24800d490041c07001050101280b10f4a1440340d942c14641003c1500501a0303e1010800390b0240780a070303070504180d0741c0c3c40410041e100744111000c1e00d41403456880d80000b641450301d2004500a260030940f03e18040c1804081940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897087446 1250 897086196 897086213
    0x70e0903043606050306060f04110a0e0306070306030320150c19020d2703050109201008180c0a060522030215180303270405040308061203040803030a0603 68
    0x14503286143c1440020842d0f560000b076055007080c02141d58040703d880f010300050080509101b513095000300407400d40e42c11a0808001c2c0da08007000c0e0f041d00c20581e41d101046088030340901005000c00c24084e10321155048192580000384259811102c03000c5074403440354040c010865003903032143c0d400218504071056150010009505600041151b0103072030002401c001b50480750251251a10318072000f458405400410081d50020001c10180c066820700101690015000c1c04443d019401c181041e03007050300c82107601100a54a03084a81c4510140c0900b500001c04039100750311a590002c2d00d55690141500014010381d16043c0d0b640021048070003804030403041a07124211098030410158481e409031a0126001c4e105840e039651702d4801d4840c00500c0d20301501d0301031102081c03501103c3e4494044854600c010721854501000145c10030091751800c480040001c0d0118001c87d0142c200303515014145c0841c5001e807400c00340c40301c038180c2c0782d0b42040307541150681e1a00010030910503043c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897088696 1250 897087446 897087539
    0x3120706152606010819030201020906120915010303140a0c15020c070501110307030509010203070c1202040e0115051507020d15150f0308211008061305070e090304 72
    0xb4060200b82d80b40a0025072240c142240a001030200000010304062003941100c0d58000c0052111f51103022100d442550428200c0f00481c003842041d80045800c25070030b11850499903d5640c8445114110004030078503005403401e1320134041c2035402ea5001a9240c2000401003079042d01c01a00c40240c1199641b601040740d01c0300d4180092506401d00c50b44020003120082c43c1c05050460b9a5801c400040f032441c40b5400b0054106889100003140c0e007258055401440e6000311800e10240c01c2844600b802c0ba0101841d485222042c05410403490401d10f00e203407002004001c0103070038420240c0100c2d02d03140c010282101c3c2007403040001c1d0341c90303821486851400c01071108240c9204d4106903010070100907601018102040100300c0d501003040030002d80c20302a40041200d08a828003010411a42c801d50050701c51900401e03002a8103c8160391801d4107454004009019551419820110078400a0245800c600040002007281e89600561103002da05250b040f1041d0304130000124402c4210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897089946 1250 897088696 897088769
    0x7050f160609060203030103060e07050909010204030b150f040507020717100c02161403030d1a01020d050f041202030a02030f0d1202030f0105010e030f060a0c08060a050312070615 79
    0x500d02c040c8000341d400015a4190303030f440000002c0c000c200c0040c651801ca280e40c44964000306420070059030110640161044922400c6030008a40b51b9618003112031102d480e0303da402414140e0207144c103140079000140c01840f54019105059100c44c0c1b03115000794903103010328a6074400d502c412040c086511490700015070610180c084a170144016650414041c85a07804000e204c06013030103156403d1085907100400f00300c0800c403620071410300201240140504901600503500c604000502403022510900c40c4009203030302e8141082168034400c403082e0b005903090300c07807a030081c401620201b080c8804403410700d00070070640d0b0f0b0f1040000e2107000c4800940c02964014001d000079442080750702819917500b42020024003e0400c0405c2c0781505034000403520b071150206105190604d0781c0138031041d60446c0c0c2c481003140e403518288200c00145128140e0158054501c0074130001000002d441118855003020504000c4203034500c1c190307040c1d5013001a00c2100e006e0101c0041011440503411502c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897091196 1250 897089946 897089957
    0x150f1b0e01030f15141f1101060e01180b0f0136080102310e090a0506040b150103060f0e061804080a0314040c0611030d180c060507052107050f1606 65
    0xd55910200ba406508142c03942401521401c10400c0311f42908a00054219540482c1081d03944a00d4a24002021010104002d141c40c0440754281803d44401c08400410f8558240e11001c010146075580c040001d2034010f80700301200804014400c004410080c454540050707214040320000c0d01101c6c0e00e01c030345500103440c2030340b040702100340d6424104100c50b0600441115952809a481d00b4000751101c01400c50080f40104002c02080c54a2a4010307020303802c4a5843d0519800154101c405030b001e41050410020b400b0440c1090310780e1841c6e84004003a00d2031602c0c4071030307107200c03e40c01c001510b080703c800c20042581111540d01d0300c140c60f0800301c81a0010281d00701134a9242c06c28a80340034010801044042c0f160010b030003041100c101d4481c0c0e00080201c0350100c200045040303109a4100d6001e0355002c00002c80e140701e007007a42c00641d000b07400b07441c94514009a0a03190b00049105010015090141402060302840703907400d9200740320040c1c200400401c6000e21402d4640d04080d05010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897092446 1250 897091196 897091219
    0x30c04050a15120209061603080708090d0c2a0b0705010f0504081911030a020604150504080d020c070e0702030a18060c030c0609060504150f1b0e01030f1514 69
    0x241d2000d074030f0301d040e1041e1500680e1641e0210120baa43d1041c0001e40006100140c0c7d14800c00d0381c0241050300c291798642d20740c0071a89807018030315280e4201c0380170040080c02c0248100c010900d01100c0f149161511500d82030820490b0008410030700c000d1340052050308012414006020080c01200b402e050120400c00891409030b079034450380c0c000d0501480d1041441c18444100e6030180e5a0034041c1010401100e072150f00101c0002e6440781c0440341110403003a040e58204d2800618012240501d0b07003c28150b050084007412038000790801c1d0410310541c402d0340e4000401512504034140240803513800b42da40e42c50100300140c1404840044440c02c5481040d003044650b40c0460511004c80d13061819000041d20303811b05802619008001500300c0b4608000e2108009030089080345a01c08848144000d075601e5007600111040c41d92030b8089014851000102d0500c624190742c2104414100000d865003402c502400301c940116540705402c103011b10512082c40c51034503e01d17101800b10340c104104e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897093696 1250 897092446 897092489
    0x30712020a050a081f09020d0e0c010801060c03020c1f1b11011b08031005091f050f060d0501090b040605040605100c0f050604061b0e0f13060b030c04050a 68
    0x148100d10009080103440d20100780441072050070803170324182131003102c2c00c21501c403250788000350b110750b110a003071501d8400f251008400105180c0d04009050319451116864170109880d90f00d000b0400b20214018010408040e90315450310107044030000c0140c000380c0002d00c0c002703070031700880520024a0481c8051001c1c0001d0707040d00000556607013864050000100c941d4440c61250903104005e00740030011080291050020780180e0454a048940d011541c546403441185190400e00d284900f0307003007010a0010307003006d400c00807010750054649854094481c10440c01c480b82a0002c0024a4613042c48008602c2d041c0541d41c042c18046a0070084d407071419000a00c182d0700c8070481c03010b120b141005030702404400b59000e8502a00718003998103501e85840c04200516502d03e0100041103c8440080e0703085c07040d404010004009000d03445542c01450800c0200c081c18004185255220000850310b0040000a03500403001040d0054907030342410f04003c0c118103160021310008904074a03c0282 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897094946 1250 897093696 897093707
    0x7080414030c060a0f0e011a010912050a1e05030d061509060203120c1905030106140f03180c0a1806360f090b06130605030c1201061208030712020a 65
    0x301c010304200290b40000054064064580c41100c1007087d403030020301400c0000e2000d44c1d0310310090266503c20281c0d841e2010000c0071049880d000e4100c0d80464040d800003001540166030784c0900840e2545440110383da6203180d50b0003003800c4007207d41c8582d81003081c030109201c4880740c80c00504240303070b00d182045002503690192240c581842080e50000c1485030707025204442c60f01040800300c0080014010003c6c00940c02032040c84000760350080700d102400a40801d0311001580130a9062071912615400d0f9500680400400514006c0300f540b40d840c0d43d10182c20314005c00e01c4600e004805440c0000301403c40f003d551115400c03210181244e00d000000b0030807001c00004080b034509038215000b4070345c401800009002354205240c103002e503051000481c0c3c04d07403082c10112023030494040d560640c03100399051842040d07059405000030700464948050889070005117000001030040e501c40d012007641003921019596a80d00206000f01d00f82e10500512206061401c01c0d0b14101c0006c800510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897096196 1250 897094946 897094951
    0xa05090904020a151e0e060703180b131e05030a140a06060608041b14060f0903070e06010f08010e0a2304060605010e09010e010905100e07080414030c06 67
    0xc2010300000250031541d4019a56000e0824411408284203a5a10103880d04180c040400e4030103403296102c030b100318400c2c41e00c2c2c030210801528440c00c140442d40c06035000c3d058482d0501e400e204081e4040b903004880700c05055101402944c4a00d00d6181548194500c2d01d030079038111895100034420300c501e4800107060300030300764000f5521200c0c4240342d500300e0a29079220801040641004400101c1c40c4d40000300e5401180207526650007100c20700c180129400d1184941e00c41c1c5442c1e15062041c51030050302920725105000d001524010780c00000900f003500d150440d0810080d002c0c04c1c0446541e01c0840035844c0c2e105810a108994189058420b28901c020f20564007643c442010380d4200140301c00a005075403a240c0c890110b802c2500c0c020b00500043d00540d400101400710301e03011031420752400d0703048950f000c4036440c3e141d0034180c581003e460300500e042c16040305100009845030340342000c14421490769440c0b05560426190411404902900350203050f4820310280c00101c002040b80d54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897097446 1250 897096196 897096199
    0x260a050c0127150c0602030702061b03090c15040b0d020d0605060307050304110409320304050a09090807081b0c010e060d0506030f07091409010c050a050c01110403050a12050a0509 79
    0x2810350349000743c00c848410b9040c0005003890b0000c024030411580004800d8002c1000901085603e0150340600c4414007046605040952091003403940d9402c001c4012400440c107030590354901500c0b1200d482842e441200c05101680e030003e0200600342c0a0700c20b0364041d00301100c3c072501d141400385000380603010240001d80700c5820041c1c0c1100644e11680203689481c1d00200c801c05031040d40461805020419190a40301c44c81c4140211200d1804400c07281602c01c014041941d09060025040c0140007520044400030410020000816100c030060600701540400c101100a020388045061140242410b0b05004465404c9080c560302c620541d22114540c1100068030b544602c00680703815480d900750140c0e030043e070401142014039038000c2c0b590300407400100300c91502d40800305400c80f41e000c1d104000042083c045000c407184500c00501c8200307044000841d000c10031101091543d80554800c071a9a40510003600400c40b80d5454910148542c0c10142c0c00d20942210140c118403810350384a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897098696 1250 897097446 897097469
    0xb090f0f25050406150816091712030c070c050901030209040305070c0b03090c040b100504120c0503120405130902060405060d060806040f1e0c260a050c0127 69
    0x301440003495500800401c030060007880030345d40d265482440111044040c00000b00d4007800600580303100c0c0c44009406480f5900c118816140040506036221a4640c05c440350040c540407841c01c21180010390b028202c03205405a03102507034585400000c5441e032010780520f03220401040580d4a0011460b800b90305801c4c8180d58007000e113002d1400000766000800400030120074044198030024801d149298191420016810b0200c01c10207117421034640d000001b10100818045140c1a549040246110704840107030f1680f5000020300301180d807038801c4c0c0c031204045030400503441c0501d1074101481c01c9040c10808602d40b500419102d100c0e5024136030140700300084808400445600ca10b00a1651000340c030800d00740f9290610765002c1c8207a0039500e020a0002c1112a4201c1d6012041400e40c01140d10394a94981a10403800305007c01c0f401140054100b40c5a000e0700e010b0204503c0306e4070400142280e04000e9001400d0350500c0d40c2e0f0f0920a2500810b20043d005541c18404169860180074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897099946 1250 897098696 897098743
    0x6010f09050c0c06010f05040b030c09070f0c05061312181a04050303040b090a06020601060c0b070e030d12060f12020411040f030c030203070515030a0b0105160b090f0f 74
    0x10280c1503c18a01200e502d48120800000c800e401c03c4901301c1a2002180c050041c004030104150361460005440c1c0c0e03201070100301103280d490080903138016201c001d081610407500c503502e9050801100b103d038603130030300d41c000800c00402c20407000002002e0030314200500041c40038015004580d183d802810644501c07030040d9449440f00c0390650b001420001c003105e50752902d4004004954001510700ca00903680c284010030503500124485042e22101e030b6940065564944961800510180600e010301c108122556642d45040c070001c0c01034001c50321801807147c80d481d1400c0840d030b00c40e80400540aa420418008550002c1a003c99603404030780c0490801c070480041b12080c801c5600801040780c0c8107000108000152464a04490084080d51246e079562401d0005c20200d0606004150034100300155015403198800c0c2c808280600d4405d04108200066001301080d4500588000c1034004c1080810001006140c002071aa44040d00c07407030020800c0c02c0d5031911852546031211008454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 897101196 1250 897099946 897099961
    0x150e12121302130c02010e010c020106030503030a110706180c05090610030509013b06040b13050a0b130c17030a0815100c02030d08010f05130b0901081c0206010f0905 73
    0x18105543c51400c00c081003000010b0398043d00030101c05030740441c20b500303000c00030803024018425001140c0d004030256196961743d0010900820200c3c1c00310f050500d00f48090000b1549a20458140c0c0e00ba031105045521418145255907083c10703400030b4444d4544000700605038858141d00003d500f540c1c20089451386076248020302628005500c800071017050502d008011600d509240808070881c4090100c045c030b41c16081d91510402c880182c48030b070b282c1c8007207440114407800d800c070014014803d84902c402540e1344d40c06034140903604042e441120b00c101a0038810740d011000c00400f910740b024195a6482e0007465100e00400000d00203120304040043ca034440341c00300302e200c1c40000030000c011640600030040d22407042000164000d01c1808540010765006403509070582e000c4020000703d6900d07080400c110100342400c0b9941c00b035222001c0e098180c0368070250301e0180c54104054201c05140e2407800e0100d500c0c0d8460202190301c690300400200840c0c1c611141910408200840c59503110310 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 897102446 1250 897101196 897101209
    0x120f06020708030126101e14010612020901050406050d0b10030605040f0209030a06021b030c0102120906100b0a0c0f08070209130c0e06010504150e01031107030801150309150e12121302 81
    0x1580400c0321360400c4032200c8d03990400c03401c3ca416100302c2e40b02c0021201909000c80100c0c054150524003140003000305101c02c1d030003003024040700c15680d80003140b40b501703007400716928443e50030124010a4a43c8801c0c4807a2500340150041800c59000440c113000d118000240d46249841303001c7d014690000d01030190090f0300c448410703080013410440e66145400003809000394807201000c01203801c11030200f00f140d00049800b5006101f12101c191941e070401c031500c0d40c2c552009a032101030080816540c4001490400000c5080d405502420386410160040c40807070b80d00242418682003401c1040301c001025036040c00165219401061200d03610f1200683d01c1d48541d0b00a05c50945c2c9041c20484820b501c4000aa1180740a07603040c4140d00c0305a0106807613019900005020601c114018045241010f800000781500c034600424181000d8491500c504154203035240000c0d02c17410700c0340d8443d1040140d890303462810070001d407a00b01e02815001903c0c40280203100c403151480c501d2000d654500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 897103696 1250 897102446 897102491
    0x302042708070c15020f060610020a031206081608010606031509050603190809030c06090130020a080103121b11010309020a0636120f0602070803012610 67
    0x290928240c10800400180d13845201b0340512003030740300d0140001c1081c00c1040302582034160359002040f08010682d01134400721a1000054156a500c04000500020402044e0540c5000c8000149510304110350380e429070300f0030703000941407500308118448800c000c25100c2049402c1b1140004072034443c100024100111320207901d41401d02c0c4d00302c0c4000d0106030340080c03050b071000f201140c104e4282402444a180284107905022955018808180c3c2c042149292412590f203000c205864803c09100b10481c0c1100ba081c0001425140040c000c0023801c2811400641903410155000c0c2c1c07941c164015041c00d50b000080503401c07000c0c2c101c18143d020350020054194002e0040b0351032520703500000d01c424004540001444502d80c2c0c0320005426440d01410441a01c10300e140f4170310f041c0803102c101d2010340d00d000c6950b10700c1100b54001180c2644080c1400610980403d80d0381e52402c03d561002e2001400010b40c0c40600d2103e030a1a0038000a12466126840e040031903010645c9652416a0048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 897104946 1250 897103696 897103709
    0xf071d090c1c030c05060c0d0506010804080d0c140a03060602160f18092a05040504020303070224031006030617060105240c03072a031104020706020c06010302042708070c 75
    0x50b141840045000c11f00900007143d120700007003080307a984200448400f841901e02500802d410404044801c4550300303ca0300101050602c0c10856883e6004010b880d48000d9180300040d075507800070b010299050040c50700c40c000c24501640e032207040c03005500c076440052142140d080a0302400140300d00c21600034092564211030301110006c0c100c442010300d00507501d400201540c2011000c1410b00e0f103403280a00450300600154204062a400d1089046103501140c40c0c0500d00c0203103105840000c0e000b1840f40740c0300300c3d01c1201a0300d0000042d003a613035560400c40220310860b0a0b0310040000040c41c90449508550700d4804491014940c04444011f035801650018000303642101d285000008000c1c00c0d01c0b40840070805164003021650001405001c40e2aa219a01040000c568a0301e000007000c40014001468400607550748070813030348414602e0341c1d51b400c81d000400c02e520701445410111122068504c0c403040404071485069059071313a009010368400b103190418000c80b649004060200c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 897106196 1250 897104946 897104953
    0x81609230d0309030b2d10030b0702010e1501030f0b0a020d02160506181b1f020c01090f0b04270c090e0a0c0504030f02030f071d090c1c030c05 63
    0x2590030001c2c48041d480c041904e6021740d4502040c9960420034503e6000040e8031703403c0f00851000a00c28240050241c4540041400c051002c000305501019a9000d00b9241c4c000040800c41195440d05160034840e0000329000030340700400100e8032540541c1c0d02e0301d81c882206031072691140e4200d8001e01a0f9480024000d1000c9100d40d200200c0050f4a0b000174041c00c103d601c1a40e45951403040d2100c9181e4054443c0c00489030054090320780c0e408920303052402443c0b080c904541c40042c00ca4840b00c03081440040c0d00407440352695580000780d04000e48450014001c03101d052011110752071059100ea0f40f0707884d1084251074600007071103003440c2040c501e16100b4080d000003503000401d22120b5000d103106d80c000840100d0f00f0500b5600c01c100170144207441d0030b070805245031104c8003c1e09500c04d003640c1601072240e4000510206000c1c1c40d028050a003800c40c420b00c481448080155001051105154003000f1220340a950700b9801c18003d07900401c07800050310751440c007144c20000c4564000d00030310 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 897107446 1250 897106196 897106219
    0x124030b1206070513050f0d020915130605040c080c04060c031b03110f010e1c0513090e0c01020c031506060c0102030a092d030e060702120c0108160923 67
    0x2e621000500c00c1c02c1105d581455a20745035020000e0007109041d140c5c0e80a517002d80054014240004610340c0800fa03040819160300f940004120007034040b0500000340c0380e650000344250b151038450700318210345915003000545001414164144101e004000a01100c056040c0030144600703a000240e407684224034042504521340500a02c030307204050300d114004c540240d9544a8144143c0032105100b00041900300b030042c1c100e0080c4070084880340f0801c030041060440594800904030001c105208002070f02d2181c04100508164070650458115040094408819640000c958402c030102e00c805480c1030319101c00040c41489500d00340c003100d50003c07040150b0080b1940c0004e60040c042c951203d10304a0b01c0920051000001c80c1c0c010205444a1100c40481d01c5002c0c0114480c0001e021185491803540002c0d103020401c00b5100c03500e50011540c00c40d9940c1c03180200b1b81002c04510044144201c0e1000031f080401c440c0500c08c45d96003203c0e0020030301150706191207003412029095582e402e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 897108696 1250 897107446 897107461
    0x603020a170c090d05010507022404122d080a0608030f0a0c0f2108040506190b1e12060106021b0303131d0c04080c0111030409050106170124030b1206 66
    0x202012280d08c0050300903000e04460f102c401501e02c0181a540e41c800c10100d554644d29000d10404c0e80c203d000c00c10000711180200a17074048003241e004011401c00f1820404003241c002c16240e03000303003c5645103040170010400c07020000240d41405c0b42c0001a62344542071584120303540d500d4000081c2182d074004a0318000c3c09000d06107440358480f8082080440102d40009842e04007042e0b40042150b4001c000180210030207034805c280c3d41011031004130f4446080000511342d407820300000c2800240001e022551840c0c10707072190440345151005003010358504a0003a44401100c0481d250312844403107085899a810300846201307840300211782d001c040e21a81c0b140c07200c0640c210340d607020700c3c0b400c00820344450078072041d60221090f42005005800101004554004180c0c00d9450180f00c1844085290350150103820f0181415a95881d004251122190703620001070340104081c6d0962256030451400b1405074440082d1141000f14907000200301080788595101084401400383c138041c080c84 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 897109946 1250 897108696 897108701
    0x10f0207121712010906090225020d061505032a090c07150c020606180114032b0f262206022703030702010f12050403180603020a170c090d0501 63
    0x1a04c840c11006c1041540b034075441d83c01c9114810b6007820410160080c824096034032658000003070301c090036a240c0d41845070b41d00815140c1039449600c100c02900302c05c0c800341c00c0810030004034075001221610740c82a482e00b0401003840800f038150050303079076200249011000c2c2c4100d450007075004100a0240d0300c5c0268003c01003550003040c2c0018013a80000c545c4620700750030342d0202000c1074400a00740b41d10f86079a60030081c81812165400d802440590201500e1500080000416481940402003520304009060b401640000c6c0c0c01d0010303100c8034143d24080d020f580314040110b00480301082c0c40d5000399089614603250000402c00d00000c120b4200803154010f44003519580e4001103c603081107290305496a401d098040d056071080c420b10000d503226500f415480e00382d81c01c0481a020403100f244080d13900450b015030110342c00c1c207400f01c4c0b409d000b00c4084000b00030300e24003103042c005040c000070800c08549a10706c0702c5d52500004240d00190030421148440001007840306922030500d407982c007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 897111196 1250 897109946 897109949
    0x1051c1d0c420307030c030212280e0a110a081203060103021b010b010e030c130b0613060e01090608130f020310090b0a0f0c0f030903021e03070b06010f020712171201 73
    0x20701b46048483c2c110f000b4001d5501c803135060075800c03c41b070740d981d0022010b01210320120350341c88071510400403034080c140c4503480c2d062405502405e0701c1a03840c28054000200f02c1d60103401400c04400401040d4000b2445405449460281681e2a110040100d0181c0200d5004246020104500d0100c09070154480714114000782ca40441c080b200d0010103465040b600403903a0046522801d02048500c40c0e440280385500060045013403003c1d03490308120800158100002207000142003417040c1d80c020300c81c280141624901459985803982104214041c0301000030301200d160403090701195418031041c90810000b400c100480300290410701c0700300c402960701100070ac0c50a280d410046130240079601c1d8811181e1106030320401d030140f044009250042d002c2e001c42c00749056022880b10b401e0300c0f41c1200d0000e03400940e01c2d4030b01420003800c1400040d0105041c00302240030b0400c00d90300032034050101e660702d032000c071040e5580c0e007008560061020440c5245a00000e40c1c5a19601402400b03070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 897112446 1250 897111196 897111211
    0x30f041505150a170c090a090602131a1905030a0f0c02010b12010b15030c0403081204050d02010603050601060c03020c06030c040806010605040605030c0901051c1d0c4203 75
    0x180d4290b03891080d61044500850507813500d03040040c04081c80e0802c10380603501308103200000600d008494459038200e820002c614125400a12010468404002c001b140c106010914591170006035030400d20400407240c040e2018001d001c400181100403d40c801010306043c2c0c0700030320259100300002070007031900008461050148480443c5000014820302469030b40c09014021401000490100309410051142880d507000b00400300001d00030360003030302110340e00b40c0050042d810185021030401424212007011a132409408101044002035600d0465600781040702c0c01343d0941c142241018103d14000d90040c0c00001400f0482403214018030844a071202a280c10766201e02d0201c40714451842540d0001d0760034030100b045840404002c280d180c005040581c03400110300f1014601c00d440407030b4a4a015911504a0700941c101001140710341d00780b20150108001c030a00040382c078542030710100125400000c20b0740b00c5d20010100b80b2800032110b080540601c0c0464081c3c801c6504c00c880d00d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 897113696 1250 897112446 897112459
    0x150921071217031f12020a14010c020f010201090515071806020307060b0f210c10020a0609050a15060906050f06120702030418150e0c030f04150515 65
    0x54541c940307260001c0000e81c070541200030410311030501e00b425000079000310003a04ea03203004003180d614a41841c00040501c50314550b43d590349801044003440c4e4607445100009030594010382c0d6680d11840c0c9d80c440c0c583c110350480440110000407401020444001482e038071038100c602240d0f41c042182d1612483d11075541210901200b070f40010b40700b00c103115100150f0720134403801002407007541140300c06007070140c42c082000c1c030b181c1c00240c0c02c444d400c0c0d41e80001d4450304a888071500e41c1070045118404043e2800c103614041800e009541e800c80440281c0701507550251401040802c0c48044002234020000000c0034040340060001444544074802446160650000d442d00303018100360000e40c8018a01b604228480b100f00480031001041c40c800c40c0030400001c50240c0b05030060080501041d5030004205074014a190604245500300203c543c50a10400542e40811000ca903400940d450381112180c07038910308020781c3c1800c4081c0e070045034241810080b20f00c2801c04030300f03200391341240c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 897114946 1250 897113696 897113699
    0x102003090f030d09170307061407030e0f0a06050a0e121324050703020c0411040504060914041203111204060b0117071b05010207081c150515092107 65
    0x405a03640c0c076400b26200410204007080041c1740e044150307902c40da0b2041c0c050300d28040380c542d100421a4000040c8000e4054000144101d555052245281d042c900500504004c030600082e50759412811000404c55900c0e03400041c0ca102503500b000769a034050004860660300c0201e20303421a40c0006044602842c0f00740400035001c501d00303000480c250516003904850914415046520382e00800003913040d4403404006c1ca0342038880b0b00c80c2c0d06226542a4000381c40750700700020441a03d150703500ca0781180b410450070a807049010141035812590108a079030b288035920a00707401030111540f0707400710010040b503480d025070130302e5140500c9030348a14006c01c010051100151244d1000f4010802c901d5840c0000651713a5014a121610b00015194440741c40c1115949942c2039a00c2510704480480012817910315000c03100d42c07648034041101000f4810550080194a4840700d01d06c0f45501c10f94454041e58030b11511401110f104020190840caa0a401300380c1c2110020311b010105c0380c480c891100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 897116196 1250 897114946 897114949
    0x90e0109141b0f0a0e031b130b030d0e0d0605010e011503020703140c010b0d080a11030412020603130807060504050c030d17071b03020c03010b040207020d02102003090f 74
    0x280c61a003880c60240703141480752120200301c00c1d804c081000c0c0148010a07180f4040b5940410003006001d103c1d50340c2e50b03034480c400d00501000b000140243c020786810300316114035650b8049681c1c20030114524100906408e0580040d041a071514800b0704103d203803034008035614282c6044071f0705036258101c2da90540c0118442c110300300d1040420150015403038181a194a5444100800b0040202c00000c2561346100d00090305030400c0c031104440070440042c1907000c075608a84600d1004810720050b43c18540381180c07010408001c01d800038820400000090b9090040c13010392000140c01510981c1c544980e460328070f006080969003514035118400001c151450300042c20000030301c550342c8031a64511068040705000340068810b0043c04048460b40b40c0704144014160b4520b4026801030000d848030100303150846c4e4040c0b02040c05a8010003070800503803503841000141300e506807030200301a0340c1e09000b1202c142c0380340c51003c104102c01e9442d1b41c038a0310001c043c100148c81290340800e440249030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 897117446 1250 897116196 897116221
    0xb09030c060f091306080d020a1b0602330103030c05010e06100e06120d0c0623010b0a09030c0603020403020405100509041e08040e180d05090f01090e010914 69
    0x802076000018100a1100d0300d0804c0c80803811070f481c40110120f502c680324036540781406103045075100142e00150020f401e110040c544c4049603e100e000008000303091880013500d0300e02c041c2070b050340036102400d860b00e440901004000840800003100405503107038500241000840001071358a0760034920304141c1c01c140414800d0243d54000c3c40400410b180011000c0110030040c800c1e980309102d1040c4030080305c0c0500c0500080c204c00c0e81c8019103110b00c0d18044007210070342c07141349210850160301c000880304040400c0d41912480c0a4541e2201c82c0d450085518011b6030300010a0508108000544240c043d00600700707891084030700744003999076505460303183c0070381e803180301d5010245002207004503c0c5186e50412203201400c0e200030000c400d80302e100b107517030242d4003080307548000001300f000046280b01d0405106412102800b00103103500c1c802041d500810003820300c156428419499180e000740e0310280144540b0b412032000e5a5200a94030090015440e007484076210000003d01181000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 897118696 1250 897117446 897117457
    0x2705030a0c081e1c03020928080307050303040f2102030a1103070203030a0c032a0314030f010303031104080f010b0307080d08012319080f0d090519030b010b09030c06 73
    0x7035008011900501620380c4c960381202044900b81982001400d513542c0782d41022000000540b180f0520a03400000c0558209500f54041c41c0f040e001480090000f41000c4202d90b041500070b031440b541c42920381032060400801c54200020000e01d000b03080e1215801001618a504894540081d11040301058a0700d0b8030883d80020340c50b400403c2200f402e28040c0200030700d014000d10f070001300303010450022140b880c2031083c000d01e14052085000e080503031192203046440c03010784907030307041d070905214401c3e180e04180002024140ca8000703103a10b0b98008030a980040910300100c5603564030009000c0e008104810800d4000e0107400c1000c12201c1d030004d414450040603594401b01a0f1a02141e1608504450b42d5804007048400303c00b81c845c1c1c0d030030001c201c41044c08050387c00031600c0d00c1a510714102004d020500150000c606010401c1c1c1c10101c480d040318015203000201418124107030f00d208900e9040142021034440c000307e00e84010300050104040c0035002c5450000d245010042c0700e000c0c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 897119946 1250 897118696 897118753
    0x1050601030908040504020f64020c041d010c090602060412020307231b0d032d0c0b060d0c0b070204200a120603032705030a0c08 57
    0x40104005c03d0400354000c000b140e2660700320030308102c150b0340038070019010002c2c244204101039044005808455601001c48982144c1a01c81107410780d0703030b1844a000303014440036100300701d440d01510310b0300900c4840c440d000001c2040001c26507040c1c170146100ca01c03607840981580303040310030580e05018100c81c0060758810340007040c180d9101d40d80c86075000c0e003400e81da100f14013003400540001002036420921444891218000e81d4051007091071500e10071281c4114810a0702004081d2629800800085030b50113180040c008440e601c04000391041141e8000ea00503e0842441c54040d8450b090103030013841000055805d0300c030b03c000c12500347c400c004050600c6481410420118205030000c0025602c00384c13003c80c01c10b6109086c0d807002c0d002000282c0f01550001011850a42d01c41421202002984000c10000b0309544008208810105e091000ca15400101c07000030075001045030001e20740107007120041c08a919010381c43d18503d2185050a21601c080405840580e00914248160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 897121196 1250 897119946 897119963
    0x1103010b060322080d0c1209120c03023c03070302060105010c1118011a070c0603090206040b2803090512220b040312091a07060b040f0905010506010309 67
    0x5520b030218058250302c441000e10f004201d500c050001c2c0c00a005401d1100120400250602c819207025000528070007004801c14540007108002400800750340082c0320707442c43d240395103000500e4240d00e0481074050301503065401b80110f150848040400760003a101008103110282102c801c400d649010703203200200076803c080c006120a5120b503c03804403640c01020003440d003c5500300412545c00e6141c1030005135a02040c0180f01c400940510713290640c5c09e005c1084d10707148554840c104400103a00400041540f50a114800d564800e0107031405400710000d181d940750111002c19030a140c04090b40c0c01d81d07114404841c3c000c00e00034031644030302607002406800c4d60b0140001803d510750010703501d20054040c85403134203071813204620302e00094115810307100e54403425030070040221030740c18030410100f0800510900c400d8920f0740c41d030500010310a6200351562510300e48032010f440c00e20710a03030b0000d1621025182c040d034180c10018800b8014070003040710f51140801102540d20307614001d0103158 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 897122302 1106 897121196 897121201
    0x3150510051903020a120201120c02030f04080303040308060603090a0f080f1b060124080a060306090f0b25050f07060606050a08090312040303020c0708191103010b0603 74
    0x4800403203020650f1255000a09d040c0400c201545815180c1340c4030120b5600030000e4031003120040e002c098a0301d4031307400a180c2d83d0b0012203041c1c000803030341e1000c00d072181401c000b00d90186000c0c07000340040c50034a459058003030084110844400300d007007229640700303114500a4002080c0780c044901c241d8214060091400301c1c103800800300d8412120803002c45642c0b0b400130040b2424281400f07502c65a039440640e00410b815030000c0e005070305100c0a4410410b0f5031101e40d1016100f061840201c0d1680c280d40300c1109290a403104681c89a0107400c0003060003503029081075004c0c0c100700c3c0e103043d005e9aa05020389211341e00c1040401e10100c0c10090b00e94000f04066400459200158104004031403550701c042c001a1000c0c0078140d000658549000042c4031100c090003540e411280100c03040e0800b480300445688058490a15088540d4040c0c60107004031646a140100b0041c15034 = true := by decide +kernel

theorem cover : BRFrame.Cov 896942446 897122302 := by
  have h0 := BRFrame.cov_init 896942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896942446 ≤ n) (h2 : n < 897122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
