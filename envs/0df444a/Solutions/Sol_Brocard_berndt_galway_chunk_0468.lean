-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:57:54.057203+00:00
-- url     : https://prove2.me/submissions/686cd6b8-4d3c-4273-a8f5-4069932985dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83992807 ≤ n < 84172663 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83994057 1250 83992807 83992819
    0x10908090d1106030406060f09050601050a0e010203070b090d170c030402010c030c05030d020d0605030a02100e01090308030103061b050f0a0503130206191409010503040f05031e03090106090b 84
    0x10440610700302481c00145030107140c10011186800000468944c012181220304940d075403003d10000e100501c80002400b0201400c0055082050000e02035006011000040092840702c0051a134400e0003a02d00c2944e10052502d05c90605e01d4046481e192105090f800051840a064013034240d84800c6d13034012644000480d18546a503001100c5051001200fa001e1080e00803032813002890410041007442c40d0220010f860710400c0c944082980c400c4e90080c2d101390300c43c15884015980d01c2d48002031541e10790a03d04103042690740140c0e0901940d17800070301548404800003040c0821a00442d5800401a5403041c82e200035102c156071a01501c02c0f40754483c0c07010704c04a050b0a0003000215040800204403c000d45001d90001e50594810071003504003800da004124400758101e43d00141000030005100d0074001c0581c002880c6000003040500146019502c1109004081c000c40707072490b417004669140c1e08280d80303050303071240d0023a2a250a55071819a00140d105683c3c400c000180c08020f0070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83995307 1250 83994057 83994067
    0x115050f04020408160f0e070f080a0f090501020d05070305010e0106030903021507021014010501140d060305150f101d06040b061c0b0d0816031b0b18010908 69
    0x502804800400e9150740080e070810000c1a0780070100714000d8000c0c56500e010542c2401c00c40c18204650a551240c4a841031140070f00501680140300e55886000a2501c2c0c00c1a5a0301c00e441c00c046c00c90311000441c410b20b0041e002c0148038040d001071806000a4070140115140c80e88210308941c0c00340300d0144500c00d030000500020b4407a4000f105690b000344100c0700c2484203011000e4004030161503481c0964070052004d12006014000c8000307030b242d0f24130440314640c900300018091041400c00740a4501000600300003002582d40214003071900b000454085120805030389480703801c26500c524909400b07400298032698860340380f10650b100801844000d111a1026145c10413000e407510b036000f1b4030b802c03e41ea0700d03403150009020a4458004000e803201c01c020100012036a5030440340c0d0007480852860700c0494088003c840845200328080004000a81001c444038110140854034004540c03242d03106101c801c2c910140585105402414203100b5103910500320341d05010010801001408 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83996557 1250 83995307 83995309
    0xa08211312050106081501060807030b0604090e15010e0f010f080d052b021b03090a1203050d020c0309040c020f07050f010e09010305010c030c09060504120807020d05100509011505 79
    0x8080700100c1d11402c00826030741c0d202e070302e00e500704030000c50303980840089140100403c43e8000b4403140c100156050070414051018046030040c421401040e151507154156000309580410400e124007072008410511944c6447c1c8188411905031480b00b030840700d0000205113142c2218101c01242d00340d00090210300100038054505400800c400940d04480b200d41e030501400d0a80b10403880d030901d140043c0d55500190b5100d0310f0f0301501d85400c086078010300c000607882c2c40e00000d59041c1c4000d40346604d6462410726007100c0760f109030f4004011050000c030b1100780d4540c0c000041c180100f000c0f68180104081820120b94a03810b04021031181e031301404e020002400c002425051544061600340d01380d0303442d080450900d040a91003151607a6455001c0080160b0500c900c0301c60790002c1c41c1c2084264078060005081c1d000d5401100c1580411229034030030421280c003240d02159002d00f03540c2072a05981020f1341c560000c1d00c00400d07001d04240014801c050103100c0c22441d40e51b54120f1014507405c1c44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83997807 1250 83996557 83996579
    0x40b1506040f0e09160b120c040e0f040b070f140c010e10020403030f0507021e0301110a0206010312080c030a0c0c02100f0905150f1b03041203170c031302030703020a082113 76
    0x3914184080b94100070104ad01c0c10b41003c400c2c400d003015080000a814a0300e030481d02c502c0700600c01010400140442007255900c55090f80c10855140c00254950312040c03410f070300500030112210218412408207103218070058000e4011039000751078203403082c0c08010080d15030b445580c40003588011100600c0001100702031600e949100050300004841d42c156103040c0b2270754041103640016038828001001008090341d803d03401ca40c8140390000190800e8501210b0500002d00310035002d0740c44101c542040791040900d0800203030000d01c100444016043d0190000f00941011000910544408615410441c204030a0100c0f035903410340c90410301a00074079943c0c00001c92941e420009090915200b41d0400280016102c03104246000300030519019200c048501c0f00342440225090030065403051240c1581c2e4401003e0705200007903d03003440084d08150640d04000d41c0841000d80205085d40c0c00940b86e1010440c24840000d0403c2e821449005405a86c2425050901e4604148204100c40c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83999057 1250 83997807 83997811
    0xc04030206180402130810020f12250c0311010507050405010c0c0e04140d0c020a05090402060d0e0102030601091202030c06090d120203070614040b1506040f0e09160b12 74
    0x101c41c14141102e1264006010799101c5c02100e0f8940b00001c0d001d000344d180620101c0300340b01000c1401c6242202c104501c2e0301501480140d503051402c190009600c0c104008100040c041c0301e0004e0014003042c056015140320007140c000e5000513900903c4010000c814443d0304e0054069440350f0341460301c0d00d001142c200b0b0041d50b007150041074400340000e110220360307041401244161b450384081c9440d00e409614042c0410845c9041010b40340100300580c4803100010142c40080e1a00b203542c1c1d980f400403074101d103e040f4000d03508034603101c20300c400d45606502550048c0826030b1191013150350b500304182c0607056000040e51540144841104900d0030a000700f121702da001d003150b080b45502da26003084440e8040107460250300006005010490030384640c104600c4581d54400d00f40c180341c2c40da00b4208000500100107130b03141d03164110b419030325142038030000c0000a454862080d2141601c084610058a5580780307489444c13051944003c1d2140d007002914108605681804211005003243e4080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84000307 1250 83999057 83999077
    0x10c02120f1b010c02012403080a0509030a0303090302071a0f220e01030201140c0a030305070318060b0306090304030b13020604030f0501050609060303250507080d021c05030c04030206 81
    0x1c02c00c0c0141403120350084400d0407000800011207541c142d0029007500c544468003400591045030480e90480c85150150959400681c216201c041c0b2810559040c492410265414840c031220f043c201a41a0001c1c14018400d03829220780320b590b00b01c16000b810041b2450158142c050005c40c0c0c040910310003400c01044a032491440d4042550603040707180c0d501da04641001d054600c01031055580140b0740c0091483e140d5010f0340b40c0f0b070f0721080c05520303205e585c28001c1c20540c45602098115100341c0080c881d240c152054224102c0103464005c0041c0500c0780b846000c0e00031140050340c9507601005807400c99803c101081c1e115591250744140c1d032241238100f00e0b4011028440440414110844000424450310002615082603c10000c007034400400c440c1c070a50041010400d8009686045000f0503c49651024900024a842d90524145400507000b07441401e00a0f055580d0014441c1040034041c0c15050861108840c1120075100c1100c4ca21540f4004000030001404c2850082007000b00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84001557 1250 84000307 84000337
    0x1021f06031209140105030114060703020c060c0c04060503010b030309010c03020a0602031905060a030213020912011503030f02010203060f0d2909010f091203090c090504120e0102010c0212 83
    0x601c0790b465910414000354010001200301106000c000c4032454925800790090038000c2c11503143c046480b40b5002c520440b51b0251201140403004c00d4020021270f410140b00500c0d40b40c440075888036035580c84460000280c403407820004001014101881400e60300300000e4003862034581c0c0360340152213100311006e048086114509800c00410301620155003e02c008000849513a40703c000c3c0c3c4404d8540241845210700120441000140d03240c003c0c10205541c43c071400768442e5842000100900e602180300c1c0415401e04d07a03110342e9a8210000003080d2886521041d007250304030b030030032400c0340811a50f82e500902e00071140c10b02440c101074080034491044076003ca455980300076252a0031003044a00c003070b03000300030184a0f1291003070142041c108101201000403500e0b9440d0082025105000380c0c042c1030352440c50711706009100c6c0b0700030090058508203201c00c0c201880c03ca040307030740701c440a280083c0c7c0d05203218003a58410b01a0140b480c1e400d5000b40443c90754a0505141d5620101d0340d00300f004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84002807 1250 84001557 84001559
    0x10308032217030106030c020303060d060e010902190f0605070c030201030f1d0703020909150604020c12030c0306090a061409151203030a2007030e010905130902030c0a0501021f06 79
    0x30b0002c2100c0911a04800b949501c951500802805880da421a440290342040c8100041d586652900c241d1071508448041850107201051078010311040f00c001e50081ea0008410a010800c0500e00e0111050944507a03c02952036004480c076000703859004040e4002204108007541c800d4008503110880d102c0c0000f100b10100002404064404048001070303004080c041095150280209034040030420107403220b104054003d0030071074070040c0194030403980404d1414a1210800001c40c001d4136003101542d5070300741180c982405400448045100364240381c0011240205809118110f4601a8071902d4000b40d5030100721029800801803020000c1c0d07041140d026070340d844400c802804480c005195207081c081c0340002a62860001c0b55428000f104805a4240382c1d001101e40c603941516001c4d0a44d049400101d070b03204410341c802a4020b840e49400440344000e07510000b85188205c08550200d040b00044c80282622407180a0158003d800101d074900c4010741c0c8002d6031482000005042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84004057 1250 84002807 84002813
    0x203070c0b130b2a010c02070801050907060315080d0216090216081b010f1a0a1428170d09060f030b0607020d14060a09230c0d06020c0c090103080322 66
    0x311001c15412a240d079150f40380490382071f405014001c06800400000e000702d02e4a40d101c1d958480306840b4000030580d5071210820820b55011900d406043e02000b0794000d10f041c2040296990041d8001349080d8041c1c600018440d40707107200702c0302c4840c2c0700003d031001103a458503a0049038100103900096008821020303402d40e0740038400c0c48078070107134660009080c544c8800000100303403040ca1f201e4040c885854040c486d445481e2044a42c5c101c04940d0b003083c01e550701c800c074688078003141c0c1e036180410861000403440d504015003034240d5049127022a030080c04c407000110348490041c420000030418070660346041900c84d4114840052014041500d48000e65001c52580f943c0c511054920010701600031a504c01d061140700d8010760119420f100c81c02103a228980c6401e00040150702c1c03241a8845a0b0764200140715104c0003140003444c0b002400e00c1c03820b01402070343c02005009143d000360070110086140c0890120f042c3c0741c0008074182190740e10003100d5410030200128540307126526040c1400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84005307 1250 84004057 84004117
    0x106110c030d03020a170c04050405061f0c110402030708011a0c030415090b04060e0405040c03050109050c0405100f0b0a0c050d1106010909050a030815030307030203070c0b130b 78
    0xb42d5400b55401030f0340e80c5503030394003c4c8122101540c01c01503440394414804c0304000ba90548045d5201241c0004240d206c103000902c0740203189081c40b199802c0d03980c06004058110ac445480c1c03c3c011803602d040c001d49281048224030003100c4250219030300310014440c1001149549032040d0070079800b1441e05020b5003d41e0301d142c1040d80124141d11380f915011540d903a01c400f450b00103000101102e801c140c200030b4007034000001400740078081c6503600c00040a11034407602040c000c6420000802002c501824102d8a501c8103101c170b00d00841c00e20011030038080358250700000702d0700b0048119040c42c0c00c2c0b5880f955140c0c8104141020070030042005008140280b00041c042c4146859045c8102014003225003413030300580c0155651850041c0603000b00b80041541c0b00c1c9240c0c54179192010350f507407444241c158034070104140d0301440082219401c01d50000001e25007640520700c0701c00c3c1103a0380d088901540c400c04401441032200500208100d502c582c002d4a8007a2074404244540400520b08500c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84006557 1250 84005307 84005323
    0x2a05040812090316080a0f0c05041109100912020105070f060617010c17040212070312030207021306050a170c0306240d0c050d050f0d0305160c03080106110c03 70
    0x188100001a1001c1103140c104a02c0ca242048100c82100c01440c01005c02c0d00ca004060021380644241c4583c038080002c402e80540c003a01e00104100308904001c45c001080342c110f804514042da4504c0e101840d071501641c9403000321001c60800c200e00c00060313401100d4075046100d0458400640240d2030700010a50300038040505822900b0054a10b6000419400e43e0440b02050040c003202c1000180400e243e421040d40c45a0140c90000c142c1d030b142c4140900d0708000d5031025000c52103581c030009032987e140c1c009201d0b09000721441c3e001100740d910f006c4104d94080c410317154000c03880501004480d801c41c85006542e4003901c2541d80000c6004013090030042c040b58044044100d882807888132041040c011a400c9109a82070440c01e0504d82d28124042c0c03c9015441c03042c0c003c020300108010701000180c070a8501041950000007940c0006000341400b80d490465008010040140c17141c881e00491001642580d00c503605a40b0702030041d1114600c40b99001c04901508450300c034107481c2008000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84007807 1250 84006557 84006583
    0xe030102030702150106090f05040903020a02030601090f061a16020303040e011805091c05090d060204030804080f0f0c040504140d18080c18060d0b0103080306040f2a050408 76
    0x218020180162411603104c0580005052191890080c045d802c0c0000300380e400c2c0d0710240c0d0300040600355800c080e40350041c200402545032003024004101c1e50101e400c05280242101020b2100c0e03034940c0e60141144445911030901c692090041d66410060000c0008410f4000307401c0d60719083d1034450340c1240c1c2c54240c1140d494115690384405a06d5007038882e07958810f070840c3c090300c3c00c1c00d03424501040b480e030b580000310301300000803490070110340c0e507103036115459907000d58110750340d139544d15160f102900b080c804c0e0180c40c018141409a40715010510a04031000080070b0b00071843c0e90801c1000428003d042503440c1c40c907688602501013030400c80b4a03109040750300c0356421001e6200d8820701c0d220054001c4400c940051001805a45036082c08038840306c400e1035000380640c0c0b94000300704100550f4034050300030100c1c18000024860100c0065018040689090241d03174981c00c0981d041c0c4241025035164200c0d01443c94174110b000e410b103c41070701c40b14036009140540d070300f803041d1030b00f000c6407000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84009057 1250 84007807 84007813
    0x4060c0e0d030509031207050d08040201030f0e060a0b0406050105070b0411060705030903100b01140d020d1805070b090d06150509161805030d050c0304050a0609090b0103050c18010e030102030702 86
    0x184010302e41082080c1540d8102004181f419401e81c3da801d03120b011141a5905100f01c0c040410210380c060b820444851420a104100d1000014921541c40e44244c2d0708a820b5480d000c0b410000d41450b01681e41500c1042e103c0c00c0c85c00603a551070a502500080050700c40b24051484240150b94400092a2140c0150019922040520b00f0181001c08280c94003004500d001d04020745a60010303040c2c1d031039a00081c0c02545900e03550700b403100130b880707501c61408006c0d190650000f039a00703040203040415070048044170071003600d824540c00b15210b5440001c0d80300052000a200040458102c00c002015010704031941540d580040f48248030160f81020400d1050500f5a0781641d018070500c0c07a00344031b038602e41d01052038180481d45600b8840f601d1001c1000010b60070352100c204004071401004041d09920b40b165944500800800b11406000e46403030802e40030800642c8a4042c0c64003449441c408a407070f140747c00141c80b01c0c507500e50b8a150b042c8110320407a40030940e02031021310b1040f0015009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84010307 1250 84009057 84009067
    0x1d090a0204052706060c030706090302070608090708060c0a05221a0906070201030b0d1505070e0303070c0b0921071508090304060f140d0f06090605030604060c0e0d0305 74
    0x7040b16000040d0b10941c224404440e8540400034200390320360b0800f03820b9442075607400390986d8803421072040d41350141801e4103052041d410154001740398400c8421640d1345030413640324280c1d40c03a1141d505110f805a07036880030010817840118880240180d42c8070b8244076280807503401d2000300c0d40e1401441c551105a04500030001c032034030100342050141010034510314041003040000c1d664054a50060b0405d903035880c40350802e88034113002e0784015400060b00e03030f5101c98400c0d0010180104032041c01c001000b04840c59490700f000801d592131307181d100c44005181800d040c1c002103030381c2000d03c0c415841a00c03524504103140340301164401c420300940291040904160020480100050200080040388010000002c5d00441541c06441580c80d18611035065454125011840c0b042c1d440d9400178001520707030600340c4030760002d40307400c40c0b410088c803d1035520503442040f00e800d032003900e8060f008580010005000c651180b900001c5509102881610380c1740810007240e44407000320003240000038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84011557 1250 84010307 84010309
    0x727020705010519110a02071703040e0a020903010f060308030403030504030504150c0212030a05040b070218150102060106050a0207090f020c0111040918020a030f1a070314060901030b071d090a020405 88
    0x703120170a02e0341c280402d10704416018000d5461800c0d12403800b140c100390032000c070340d045c040c021074008003040f0703c5664040c1810581d00340250301049075184030350318002c601d6030001183d00500d81141c1c0c000000905681d12074400750090240200f08404000701048049070540300b0040c20391246c2c0660f50340d0459002d0610501140720a110100d00c580e50050140e4012580e0001c00c86054490101c44540ca0303401a2002c18244111072003904407600f60007041200528122505880000d400d07402c54a9030399072a00107032110f1080000b0f940040e00600c105200302c2c2c7d0f05421203c050411428010700d05016040c0d0542140e000088208005070005030801080d0f00c54060300480c902e01060b50021800207a0000302d156415100042c00340c000c0483c024140616084895140c9807070103003c1680b85030418004001705100301005215000640100e001c0342410807900e41601d50042408560780c95070070055600340c036644c1801901d40508003c86246450300ca800701e0041118260150316541808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84012807 1250 84011557 84011561
    0xa0306051e0f0c03010b071415060301051608150307080d080403090905060303160312090b012105030328091113021e0d020c03030108060609090727020705010519 71
    0x1a01540090082c4010f20014401100859044400180c1042d60741c04c4a0325180c004803191410702c5005004d40588140c000c007800c10030030300c40c10f41140200b005030f0720b00010580108036548013100090481c00010955184102a03a021800c010100e8803407956030541607142c01d1a407811100025408024842003640010002010b090501d50500c8140340c0a4007182d42c0b401120844e0010324004c862013010316000c0d4a0010350030880f0102800001c941d42020400d0800c03e04c250400c1d00907448480f21074800d400b40c041d44032a403000185207181c980300c41d44040c2001800048996103031107561424030180601c51107015074407030107418084801010401c00914611412165046d004102070441c0340c89030560441c0c5004d80d0780465403a5002183c5c02c8000b40144410402c0912000001117020940065440e100740c00c01c4031745041503a98880041d448501c40e12032280c198400720807510760f14a9100d80b40c0c0307401c4a0a0030050801116813215401d4070300540300441103644440001541d58514 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84014057 1250 84012807 84012811
    0x9090507050904030c082a01090b060f0f0f0109120515070c03080f1f0801020c0c0d0f03080903190c11010f0e01050c01141f050a0b040308090a0306051e 67
    0x100d0b80036040c0c1c6003544001e807044070143e030010500300000800d986a1300110540300340e01380312500e90610801a04c41901c2c0288028902501c5e00354880c2e0015045141c840300c0d11000c2000034241c859004074450501203200403884c01181030025914010075034010303401c105101c84e8009c1d002080c3c0340861051980c020200580306904110b86800701c8004245c000c40d100c5d0704940030b414014001d0b41c99450040d000c2b003075590041c9020702c0780300000400c580c05401400c03040003800140c2d0303004c0c203024007000603c4000d010020500e0b00003140420119010b84072a56100c44102c050303a203840d41d00c102d4880303c1702078220188085040c0c201038205020003902c011000410a007014106011400c0024102194015441c1e041181c0010038543e102000c0d0070480c500e21104d1500d04003400c06030404a1011031001c1c2d64034585610000005051030300020306400c441c1c442240928081c01c607265a212540300b8402d064211500e01000000505140309080c45040c0d01c805042071421454005004a100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84015307 1250 84014057 84014059
    0x60c061906050402040605220b0a0f1101020405031f0b0d0f060b0906060d1d01060605190905090703090f020306010305100c1d10090e0c0a1b03020a060b03070f0909050705 75
    0x4c10f00050088076040001c950360a0111441a510054031a07003002004030700c0e030400e41e4030076800301d100541580c000c50380e64003510700b84d05c0e6040280440da0b5224208d00851042ca030741580962121621007031240c0031010050031103940410402007050110300038940c0408122401c07000448010b083c45007501c5103040c4900308071169070007400e042c0e00059141c00303141c5144041c0c076524203a180d41011901100360b850140c4000038400981e075484050041d0b0480c080c003c89000d0b021000e01810b074840c5440900340c0f44000c0c03000009442c0c070300046004141c03c01088594490080350400980d800700400c0380250300c81c0009040045055080d0000c0d9641a04201e09100da13850024005c0080980400ca1640003030b87c810a41585600c81181c142a055024aaa401101c01400700712280000100040c503480e80b19113615000c08000d00d401002800c0019005070004005000021300541101c0101c0000604882500e500c0ba049903620b40b005038044d10545135030309903850400c20207010790740c02028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84016557 1250 84015307 84015311
    0x3040e070804020d11010c0b040c1e0b040306021605010212011802090f060c01140f060f15031612141e0103021513030c0b070b0114010f050702060c0619060504 70
    0x2c00750b010030310700040200d004103014542c00c6003812a0f40300e986151500f0b0340104805c00300e410281031110008409010b1902d510b07091300c40d030000c1d40d01440821011688206501440c081c038540320b900c020340016864112a00d10710070f500d00800c0c024000340c08c8d911010314240556502d4482e5542c0407100984c2d0328452213005000c200302d69941d000000d03041d1a01035440c960f40741001042c181c01481c1030300f01c0307050b03444c1c0c2c010a003c903c8000b0040703680b003460140c0c2d003100c020f80841c041140c1011201000c01d0310380b0f0200009041342d10032481e440602000c6090042c0007140108000041d10011242e211212001500b040421500400e10a5080c269924203110365419500030a208042805030748083d0200041c1d0003410203011021140110341288140512a031501550607641e400703414169001c42d4400000b05032294206603203114890144c40c0c624000f480f041e01980e945d0801c1c2070030b82c0e00000a10401e903c131901807021901c1a5038001c00ba054404444142404030380e40d075000700c1d000314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84017807 1250 84016557 84016561
    0x60e070602120a030b04060f030515060d120e131d0106050d0816030c06090b190e1c020f010507080603100c02031b01021308030a020d0201090804030813090e03040e0708 74
    0x51a0b0500701c03800c0070428680800c454240002080c00741c00390340e02c0030844601e03c0d1000000d210300800c00c0302c0140c1078503462100a40740c1c1001c01104d0001c0c00c90181c600c0c1c2e0003021010100d809000b40440211014007141d220340601c004600444004806c075002001302514040441c510030b109103c0036010407201c07504161021740b03400150740107110000300c0c400c201f0402801410701808072115102d900460a00c10700c64646010700c11000e007954102c1c5101e10581c20003402d10414003505980741541c00007000d148130b90301050b0322a8035280800c0000d5004035030030106c8820082c001c0b54840c8600341c0707a4401c5c85c1800030925140c042c2c0040c00c00c20440c0f030505440107140d4084102c0e0001903d4002c010210155031845900902c01c842103d81c64400e1030400240d000b5010024094540240c1c09403007080c4100708050342070b240c5107100148203590400090000070a110003a240024521600c0c003055138881201c032084034039000700355580b980045010007000d199410a0b55010302c162130420054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84019057 1250 84017807 84017833
    0x30103050a0303021303050a0606090b0d0231020c01050f061203160c0e090a02040609091a04030201020405120a12030b0904200a0303030608070e16050c010b060403060e070602 77
    0x4407040c070002400c02d0340004911400d0708161090001543e004029941a14101c0c81c200006001920803140c000d0b080045020380c0c0e140c01201d60780103680140c007a03040f80820b2501034559504400c11941e9442c07488000c0040000d0f50310280070504800800050a4204994260b00d1380b50002c0c01d4920030307601c01171840c1c01500e01100340d82d800030740c080c081d0307100d031883e480c0140d540c81d06504182c0380c850040c410480c80321800140c030f211081c02510100081521280410309076601490041c109640003850300c001c00152050199116000744001802c0035115030010300c0c800707811a091400381d403090702100b062024181810b00414000d050401080f00807001142d096000104080e01c603141404000c6002c603c502c0d04002e5414004150007500380e00c034500603000f401d250181081a115026001c0b600e0039907403101c20f0080300d40c29000170b0403900e00ca108440c10742c40012006c0840d501da102c44940d503107a10000e003000e140328100101e904d41150010030714003400da42c0481e0841d400100c2d94120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84020307 1250 84019057 84019063
    0x8040b0f0403020307091b030506060706020a0302130504060819020a0b04081b010507120509011101060b1b070803070209090a020315040b060409080d020f1903020a0908031305060a020c09090303091203010305 91
    0x1b907e8950501041940c0c1d02000204980281c4101500d140e0000038180c0c58580d150b40100824a41c4861000c03803070307881e83c06200444030240200740180c1d02c10600303c0c2110661114000b04544000c1c1908000e5441e40340300005900b043e40150041d17030091440c0d501c003e120f820b00c0b00c802c010030300e041810040c1d5615585001c0f202141d000d01401000500804241d1060b031041b501851440b00a03c109548d0b0a81034840798440301161241e1440d003c80c9004080300444d074602240c200c14000c1d4100ac05907000c0291007900508030341414802d04480d100140c50902031005030303002021501110345000d081c02a107001c03006000b507201c0c074a8030450200040c0c01006407248500344503001a02e80388003084104440c4100c88820740d1488249601d481c919516400900007101280d0721111790075a5a8051642d81c0944424282c1000c034100040c007190501c0c501500f81c100d15441210007000200780450b003006001d50704c0f14000e4200004002c1c0d0a90108820443c03080b00c40405840c41d891a1690350f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84021557 1250 84020307 84020351
    0x121f020c0118050c090a1517010905011514030f070b03070207090c0e01031406030604140c0405040b0601140f0702011812030e09070215040618020a0906060f0302030115080408040b0f040302030709 86
    0x3011240d403d580c02235110095004a99040d801802003014140343d920020b6901c0092140319144949081480030741e007030115100b0a401b802c100285071481c00c0440c0a130b05a000180280214400c2a100040050590140d4140d4150617294000007944000005042e1030304401d14490703160301c4c2003c0c4080e91300c0000d01d00d64015080b01313481d190441c809085070300f010059003141c0c0d800303401c213002c0c003040c0000034901d01d000e4003007600d50110401c5240072809280c01030003d0112030180c10320505025502802c2241240e20159484140e12500c40420b041403403031003c030680004d1441c0720481058100f00e9409500301080d1700041542011040c0440140b8200400040c00e00e9142c01031980025900c82d03810310250b50040c2013148141c0c03900c10760401080d140c81424005241c0c544c0d1440154007038800c032811703903541491812440e03007540000c0c0c3c1d0507040a44220b945503010000040c500c016100640407038041119510340e640d00d140100f616118580d0858420301d172420300d441c004160b54080d184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84022807 1250 84021557 84021569
    0x30b040c021507050f0a02100b030d02060412050f030108030a0908030405030d031505031203070801050103090201050a180b16020411030f0103140a020301051302121f020c0118050c090a15 82
    0x80303816940d100e0b0441c0c6600560105d1175035588003080c4420340907004140c500d8000d403120707400c014414401040642d641c244504540241e00142d01240c04100744200c002048091418498607061854081040c0e6034805d9205d20312a03040481d04884842d407240034400108542c0c0d00441c181400c0c00c00007038a6050610040d0f080c580e6030800200141e03641c206080041c1300043c03d035103080340703481c006582031743c0100c0d070460001e25440000700e6150f009110300450213406030b4405017400742280c2c065905600000035a10800301c1d0000005040c400754004120070f8208944000d81d0038418410300c0284c4001c0b050482c1c0512080c07041000e5590114200d41c11242c01c064100501c6a42c1008c0904000441b64043c7d019400c040820a010480c0a4241d140360701c00c3d85d524110350010000c1341d48030202c00390081d030304400b01c050a105e90241600a4194000700e0b10002440f20315100c0b00942c6003a0f41a0103d51540011103c3c0089280c00301c0762550000803401d0500c0401e1400d20a50200002c9004807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84024057 1250 84022807 84022843
    0x4060810091b06170108120901030f14161101061404020901142106010c020906041a0d06050f0c0304030905130f0207050a02090603010e07210209070e01030b040c02 72
    0x2a051006603480400001100b50311005003a40750103000b409141800c5000c01d000508100015440200280020304400110349880c101800000110041d0000200f15014640c903403426001c140d100c211401e005809840740c650019480c02c04c050010050007080098907490600c04000ca100000520201450f044400596502600005841d0900d0030aa0b541d1394000108200340440c030a443e0b18240c030381e442c080454941d07455000454507110000c0b0000d400000c0c490109880703082c00d81080e414400504000e8080e0300b000000b051044010241c141c8145882c1d4050001c680d0003031812a8014013403031449440c601e07264802600c07101003482254000e03c01300c6070800c0102e20b2507000a568a40602c8107559a080e141441070799040200c0381684103e5221021607403501e4148200d9204003040f40141c44054641169910507094040025084c16500c0e200040140c0d2001c208600c96100e40e01e5007000301c1460800181199286410300d4003981c40c1050080340d040d0002450180b02c55803003a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84025307 1250 84024057 84024071
    0x18010b070c0807090603021305090318040608010c0c1a010b040308071e030f0206090303011802030406020c0d02070602010b030619020a02010b031b01080a05010b030f0c07150501031104060810 84
    0x11140803000258080b44490107194000f1600c4034403a0400d40841c7d000300c903507134505001079901c40122070003940e603d0f06030f900c01c100d504075210300300302282090440103000107012a940c40e240c50a40f40303400b40440c0011000003150042040d00081a603100a06800080b60b03981800030300e0000f07101c2d501001d041c040010904508200c1c00996014080d0030346408900e18545d00c0c5000f030941e1088541e4200075004400c00280103880000030b490403075500c07110350503070504000c1c101d000940c0007a2055861a8080242001c40d840030001c4442100c490340c0208282e03480e02d40d000f800c568080c2d11092080c4c001c3c500307000c400d440024552881c1c0d45194401a070b110242036041e4010021029940c1c2c16020300701c02d11007030404c15000300c1d6048000385c0b030f000200c0d940c0324001002c84209009070380c01d0242c2480420410180120441c1d4802680ca4071240b4100c0303d621070902d00c0b0026100c1020540d22640180108044010482004501910141f001c1c605004810b91034075062118500e80e9541c94031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84026557 1250 84025307 84025313
    0x408040e04110d0b04021e0f01030213030818030706020c06070803090109020a0b030a06080a0c0605090a0e0f01150507030c030e01200609060c0f04150507060e01061418010b07 77
    0x202c08080c02c07401082c401c0010300f18a0503000001046030709030300c034034614a0b002c804411141d450b052010401000e02048142500c0194000d4201404608038050350400120019400500415840b0b0f50500c000c1b10018004081602d0100c0303c3d000241150000d400c2d05226495010079a401558800c1180ea140c0d07940170841da00501580c0310195100d40c00a40000d05000d0f520015400f50a00107018002c0c00e80300d0b01c04030b07500d11500344003c01c1440250700410009101c0c101030f24070341c04001c2161310020399034040040070901c1924804480312a031001004010000010760303e400d501c505003039007068001c0d100600380d2515010007605010340e40d6400d04441c2c0c416030201c1c0400c0b085102900100d0031a0307021966407101100c00c80303094072444000c40d119102c014199110031040305020740c9490f04002c0d03021724500304890710f801440001d000300e01c0001d40f43d00803801242070f100000914a8540103101185440c00034510f4001c5004d99028201c0706e4500d00d04505444840b50300651340d4100c0e00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84027807 1250 84026557 84026573
    0xf010612120503040f05060f040203010c0e010c080f0909011e0f030221100c03051006020a2409080c01020c07090209031e1501081501080102030c09091e010801091a0408040e04 77
    0x2c0209a4011f140800100788001007406000358003d40007081080745040c1c0555400044c1040503000c0f4400080150004030400000c0c8030184103000000d0034003d002003c940585000c2e007181030800c00d10000c01c0322070051510260001c00e42e18000c1c1801a01d075801294014001c0c2200e440e14280303403241005030346810840b12050030001207041207000705110008004000079941d03803100c04000100095060300c0000c0120700c058200707803081d00b8411014856104003440c2c9413205009500d80202d00085079096016051180c01c1000269641f10706415540c101141034100c140a10301c14440302d4915100081c0002c1d84013900d00a1312242182c085546141a003035186503c42e1348032a00012910b61004210360003009410105424142d885101c0c1030b0030b134001103401c0320380035000b40100c1c052880e00b01c1036260020754072080324049040722840119405800d1b00316402c00c0c3e4540841204006540103c0c0380601500203a5145c81d0030155907004d0303584554400d15040c0c001100210b420701c400c072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84029057 1250 84027807 84027833
    0x4090207260c010b060901050a0809010e0a0b01080c010206040503160c0b0d1d0604050c090606120109062309010e0402130f09020f090f01061101060b04080f01061212050304 76
    0x204014000c014a1407801e101181d00050b41090a54200805a41241002d00075658018016101e982c18282c03410030032035010800420b05009592142000c500c03045042c80304e02d1546021358490b402560509500d6481c1210341011281113601c01020003011400110644400b294540b80100c07001c0e5142c2089140e10580340c01910000e2070020722403e03070606603070180740d0000d952191071020381072014050b0b4940104980241564128540491442c9401038100744d0103803004106600705100f002e03104140940c242c202008040e9a0002449420140c4204504110794a0101c400f002c0d40d60021402c595010b20030b8030780640344003000c41d0440d500e0440400110030282e1082299200d085846000781280340c506074090901100600c0c5542480306900e849000c040303098601c41c0e4a8403108860421000300030000f1075607912400b00300141800300800003085844020282c6c1002c404885007120311a5001c9448141540c107440300042038040075007201640c6040064895940d0306085c038001000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84030307 1250 84029057 84029093
    0xf030501080f0604030f121b02010b030714060a170f010501090b0a090e22150c030b0d0b0601020c03010e0109110a0608010b0a020a06050a0f0b09060a03020904080c0d0f17010b04090207 81
    0x3c1003410823400340004012001c128080e4005d00211070070b2000d05440702003500841011203a034814070005402c00c10020408500c45103840500d00d406e10340c28141b155401d441700c007400740c15a40100840d41e4400caa40c07020740811200d8614150707007040017a0005171b0920075514410149000a0608112151203a201d9600c4000c003520001c298608110f010007007681e07503000d407442d1040d1441083d110b4816000380090203000400103004580b42c9000840303000b8041411442171040c0301c44607403000c0c050b09506210060004c00c0e8089207182030914103407002c140c103001d5003075403c04005180d4030464503411200c024542e00c0e034800c0c05400480c204091a035001e45524146010b2000000080e0320203070098801c0c0030100981d180050420203804d1054071102e0b030203659a20b0500c05441d012250a40203413040e0b01d82c07443c12500d66100382c1408000c1800e034002c40d81e4083c2c1800f810750003000484212100d40f0b00c50910758102241c0c00345600840c0145a082d9030f0101d50f9004105240d180d04c008109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84031557 1250 84030307 84030311
    0x16020d0804080a0606090c0905190302041a01021c050304170f0301170c03010b010815061303050706080a060303020a0b04030201021b03090a050a0312030203041b03030f030501080f0604030f12 84
    0xb45030110305a481c071142e48100d90b018902440002c4000482c81109803112042c1d443e41500f9143c1000c1000d00a606132031a84118854140000141d40c0e61040256200c820407280112880c0c0364006030810b11121800840d2110a8250070481907200045a90103603000305507100e51942c1a080e030b04280100700080d0030703000c4000004900244002e56030a107020103e01203c81e030520520505003640ca607065480c0c08620a8030100303028502c42051001c04440141c0114100440308039040c01d030402660007618280c000341c9090003910780c08120164041c2ca240400d00c282d0f4034540e40290348011200c80980000d44c444042400c2510039011030380b405014464503417001d40e0459000351aa8004c2076114031a880a810000d414240702d1111800c40342c01c0703550b44c0c100c0d00a042041d40a944018801c4580b1182c1126460b18180765403040e0025500a075240d03124052900c070060200c82040c0c21030020390b80b10009510300c0b05400140f0710341c41981450900f5003080c0302c045c03d40d455640011707900e4240c0c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84032807 1250 84031557 84031559
    0xc030503070b040b010b0c071a09030304090c031508070b0721090503060108010e06150d050a12030b0f06090f0a0503010c0507231011120106030f051b16020d0804 71
    0x407941140316400765000e442d00080d40d0742d0b6509505550b02c14407c1800703c68110b140c0c2004125660081c05410180c80103100b468809124002030555000e60407040b4200c1d61803241012542c3e040c40b038030740f10001e0050b482c03003050300300000d10396200c4032445400110440061414100700144a0402607514041e000944c1400c5214000e8100049401030750300038421480002482e19050150403290b003000005130541c1c1d101d4801ea88089001100726507040164140c00c200003c00400415480c1800303482811901524100001c043d0b13804400554070540681d0040f502c5940c45808855250800b121141c1c100c910340707000304030341d2250b650040d541940303401c0304100142d801c40700820060303114400e00c90400c0c01c0b040c540018009000b00395505079002119061500d4a55409003040410f10800507003403e50104642c16211803d0700038400007034481402d0220312800380203007600484204c11200100c141d050b000201d60290300c1010000d0341d00310304542c0964440108500c14260007480c0c0c42c0e42c42e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84034057 1250 84032807 84032813
    0x60b0d061109090703271406011701060605070206180a05040213080c040501150810030803010b04060e01080402010f140405060d020316020c06090d03021e0f21160c03050307 76
    0x1d90804109503005040040c00030700c00c0c0d80f191081c40405000c404103401204415250880000d000305021241c00c4513680c5640c05000301003003c035009201e2940c1100c185400d000c0d00c02d0943c0c4290380250305000042c404800140e8400095035a4010b1420b1034007c4810b0a4000580c40202540856000b0784002032143d40c1d003015802010a5400030b5080b14000b056550500c42210001d01c5110f0f54880342d0003d480041e8030030342c1c1d0681c20040b0b0300640740245889845803c0182e002780d00c18041400c002804001e004d80001303002c1c1c103001d0242007808880c6420f80002c0c0c200d0800304584803c001003038181501e0f410600065074007915026010a4a445614111000a62007599400f80964030082c207822441c0c400240410f9140380030305264141055041404864401c0d254100c096001d00b0700d1082d40c0d003d010601e00350303d0410800030f108240c03000142c0d606000c0704e001d501c01e441581d41c8640b203090713907204110b400410507070381c01c441d01c00302e41e051000d03420116410081c928000001c0120034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84035307 1250 84034057 84034091
    0xe030306011409060307050714070e0612030c0d0302090a0801112215030f0209090f0103020a0f050a051302070b040b040506010905010302090f04022404030606060c030c060b0d06 78
    0x4111800e8032800c01c92055080b40000e03034090060641d6015004100041c511403090010304441c5100c0c50949100307102e903111f031605001042e080020301241e50410051580350100343c840c01c20080c0e0303024500c1d04100c0000a034403080880344002c01c0c10b0f00024101c0031502e8180f04480101341940081041c6207004c4041c5455a0201c00b1800d0060241043d807200c81800342d8400c8104c90702e8100514252011002c00c2c0d01409205042100495003800290010f45030107001c5817090141901a030307003d44c110b10402034103800e160001940203101d40c009000036103c0d1010a0b0940d00e088482014100c50740250b42c0c003038496100020036600d44a0107020400c4506a411070046100384261003083e030b00d4400c0d50381107a0f024480650b006070188003082601c0c11840f21143c0050025050700c0810003100314404101241c0c080b0315000000c00101001449130511944010301000d00d05141a1a0191030050110920400c0900010b5581d001d0100d00e68940e913422111640c031000511002d5081c00c031001c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84036557 1250 84035307 84035311
    0x31b0f0711060f1309061401090e0c040308160204050703050108070b1b0d0c03030b030c0d06022101060c02011b050706050307090f03030903020301050901150b0a11010f0b030d05070b0c0309030d0e0303 88
    0xa140e50030300f1b4001c0341c0038144005407040e00c07a06035203840300c0c5464111f0014600d5000380030303162685001c01000c00400c4a440041c81401c2c0c411020240c4010244148000c0b00e070018402c07820503141400600601e070700402c1000c00c03103d80d1031500d91108581100d1000e8490000e4465641d4800c08035000040794210303078140c00c0c1a0081d2420002c078403601301490b84461400d5420755000b0b650303407c0d07900024203c0e4003826000c24500e40d03038804e600704400c004030114400c3e00040042080c0c8800a0115030b40a00803d0b1105055401c2403006002503a800c1c5d55088a40070b08000e004001c0001000d0600c45c0c00300900a001c00c902c0e00c1b1038242d40c0c2c14040e114500c58003003030f0b00035400e0000051445105004950891850440c513070402454031030240c0351500b1107003031541000f1054044d00c085840074050006141c0f10500002011200e00b42003601d006042c482c440300740041889500c0c003260103843d4030750f400030741140156a603a0f1456902070444c0300e100d41081c000b915251b80a0018440000514 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84037807 1250 84036557 84036569
    0x81c1d1c0903051005070e040905100f0b0901051c050105132001020a060b060705030304111206010627050d12020d0507050318061e031b0f0711060f13 66
    0x80000100140d089034041107600010381a6480b05040034081505a4081c40e0322020501d850520394083d000000c050f5040c000d005d0f1850381c4402e42c0c100580541c5e00c07581c684d000f550740041000c1180f040108024800501c58181b06500c040c4545640408448070407003481e901c2170003005140f50100a034500700904d060140c88207103940568540201c2038043c000c811000580040007003888640d9200090b00201c0034903508003000780722060014030100040c41c05548124100e0403291440b0040c005101c0303c1c055456000c0d40030750b00400c891600108415004003c05c1c03c0407500219144102032001101e502648e0443d0340c0c00340000c24051b140d01300c205005400d50039203500031034103002143d003402000740c05810b41e00f01708030040d60f400f241c4071001e8035810090f00b000d0800c812140e20490b94500841c00c03940302c04000082090411030b80d5213401403050034100460034461000c140c18914011148010408220303a0701d8881c840d039901041e03a4032030603483c0c4400d0f6119004406100404841d108036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84039057 1250 84037807 84037843
    0x9060103110607033e032205060304060b040b0607030201050601030b090c2205030a0c0312080c030c0715020a0207051f170c041a09030606010903081c1d 67
    0x380c1042d20b049812221000d805a403845948a2007804e50700001c40761000b039036201038024201e046800080300c00c4080052040001c0c54984411b001d00945060340481e400c100c00c0e139802c00c103200580c0e64000381d0340c0003504180c00086450349500801c0c028602d10340c4203503000c480440c4c007004060f415000305200d107000f030360148003448003441402103400e010b484280c2c00700b5041c01954440c2c3d15005104204d00560401110480e60b02e5011900f0010340c41c0c4160b480724a05034007071040c0221074a91011130010340c03405c1055450b20004001303450201500051a00c080083c0500034081d08907100708200118400841d03441c0c0102d000039544c1c040500c0346e503004501904103801464203012141e48c3c02e410075164040c00744d08205600c492010700610a442000052101184101c2d042030121a80f0b9410f4403a81e03524600f4a003050302c0c2440c02852036040040b5014180006202d6806465401000d01030940425542ca01e0200103004110146110740d45d41190a8101c0c040004281d40c0034102402c3c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84040307 1250 84039057 84039083
    0x20316030e0f0316020102031201060503040c0f24050d0c051c020f03070e0118061814030a06020306150c0115060c0317040c12060b010306150e0f041409060103 70
    0x401511160403200e0380b10203410601040f070010500742d1440e0b080302c2c4140305492411041800c8010404808e07003080000400c080100400c21202ca4155405040035030140c0d119649843e40303440c140140211001d000c0206084150070b503c3c0a58291880030403403910500518803038180041c0203422a048200109004800710034680d02c0b03a101b2200d401c0819000c00785103541e80765041c0c1380443d8062495042105030b6800a920341050850000604225660007041030400c180e6038909641035080702c40c08268005404001e56000141c802800e80e20000158403030350350f00002003e0a00302e80501031440d100050903c0c000206600002d0003451100040c200c160301c3d8003085402c0031000e480240412005c003500b46e8960300d8403001a034020b00c5640c0e540c0d112503c415491440c694425000c441f0b0760344420080170a581c06009140160000542814029100c0d01c0d005020084030b481c4580604c4103940003811580b1640c01000d1910380750183c42481e810711890050b40e60000344000c2ea01e0344c2c0c0200c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84041557 1250 84040307 84040331
    0xb011206050108061c081c050601090506070b04050316061b05032403011d010906050f060d080f040b07080403030e0a1a0d0902100e0111030a02061303020109050102031603 75
    0x8240000c1ea101a9989a51540c812042c00f03045001041d4404901c000109a5400a103039900104065507840e4603c0c0403d01c0c001c0880400c1e120080d0000703050100c1010b0074044c94039502d00351116290000c0b01c1c5441600c030360511504501c42d044002c2500e1441c2da42d4081031000642181c121030020720006010410000400c6949000540d5603103c8a80348000320750103c1d05c0b505c01c00248583c01000050080e81c0c00e00c510500034020003031000740383d444220540921500340302e42940b040e00c1d038007400410310700036000591000100d80c004140325000308a16501c00d10050580303025140c0c080c49560780759900e0901c04c07401c0d04544400c074009042f1505a00090400100e008111401d46001c0000d02e252004c0845460f00301040035142e0a5658606501582da4030602c2003448070940c0381d43c400d030144800014011004c0780c02c0c00b211a40304104584000d0750014480d98003054807071003000c0c0c218080c0b400b00e001d06031040340a00305c0d60001c41400000030000381c4801c01000507071400c02003243d00341 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84042807 1250 84041557 84041561
    0xd120504170d0c120e04020d0603060b01022b03150905040b01210308070c021e031005090a060c050724051807051315080601170331030503030a0b0112 66
    0x7880000000b015640f039040080c3d1000c00c915180780391800c1c20840c01c005100803c040741c000745510f08100740c41d140200240a1b6611403050440704c203101500c01d10841e0b00c1c1c030311031100046d919102662403c01400342e41500c02d0b4841d021980c1140c000402072a528012030300540000d5030700ba10207035124400015001e940c0c2400242000f4264840b030786142140e1001c1d00c0070703400106181d0612003c0c18450005030f840740480294901150200c42ea680220f009061818205238400c00074540340c0700600c03100132400124054960303403000380810310b4030f40b04400315064082c1d040010811440e2024107403110023580d80b40b4a4440d2225000c00c59640d40540f4a00000c0038130500700040e07004a40300703001c641020300110031044145100031404c11040e132000036101090307070f1210080d900444014801007900000c0011308002d003000071030900341645070307000340c078160801e20740b40078030061100e040c1207441403851800450b0000c050b40d03143e2400e00c1d004400750a065401c540050700f040300c00ca500074014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84044057 1250 84042807 84042823
    0xc03071e080f0c0d140f011d01021204020d0f0b0a090501050705030105130c1b080921031606090f050c010e062104080702060403120921020405060d12050417 69
    0x600500107100700c0343c1400003120b10440e0981e0300e0301c0000889480c400c41000200c5000b0030740300000510680903850b00001d40d0402c5080e0015900400c01285c000420348942030f00a03804541c1120911040d140c00e514243c00548020102a401803c02150700c1c1d1a42c0943c20f132034040c600a0199581d822801c840501c82401560350010001081d215158095808000841c0329070516051030b00c03c005007240c01c10b04107081207a20340800104503d003030038403011400b02d803604204944013503803000b13180d561a8000e80020361240d596003d01d071000c3c00a590000c08040d50000b034610707895001030400e42d4641154054a5002c80c550008150b041d050a900b1a82010f60280c842a03152020b0035180256050141c0151102c4106102036009a902d007801171005521504041c0d142400400024280340744a034030100142520381003038094409030302da980d81402d82c121400203d035950789000800380041920090308039003190310603401c0e2a41201c020420fa90030381c803c0032022044112004ea641e005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84045307 1250 84044057 84044083
    0x70b0426190f1106010801020c1b01050901211d06070c0b1302130e0c0307060207030503040506071b0303020105060102190203070308090a090c030f06050105120106050c0c03071e08 79
    0x3001c2810001920825408420382070510381480c032007603c9800e5914040c400c0c0c20039242658000b0b0308030301104040200d444218025050703071f41e0300c254000c0080c0240c0280c00740c030707414081c214000c07034240d002e60722040c21141e01c0c0240c100104002c2e910720303000729480c00801c809070348200801710313010301e0144010f20710340c0b907201003011881d03a903000350303000d81c00c040c800d04a8001c04c10208516100506005203851001420010002d03808004105072418016520440c150b4010404c1030010500101c101c8081ea2015284156a22075502d04800350b04145038010618000f0740c18041304260f41904aa400781700300360300315400040c90008910309040c071504029807640c89034004000050225000c0c1c0a108402461406000c0d5100ca03038505417403c100c008000256141c40d1402c0841d032900c500d80c0600f000b868a903052030b48407800400a040180500005c0c82000b16541801c0d5a003003208030b041040c09400e4640c001c3c0e444013400d070300306072848004240c0c1c2b4903441e02003082c5a00042c0f92a00500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84046557 1250 84045307 84045337
    0x132d060e1501090f09150c0801051c060b060d0e06010816050d14030f120403090e010b09130608011103040b0901050c0703050c0703061e2703050f070b0426 68
    0x110f4210540c0040009040c2201e2840c2c485030880040340b160341c0c40902842c0440d03c003040700c808149000f460584147c004920a040340419015a840b04260544541c1c4c0d01a80014042c0a014006011070289080450106042c402c0030003d859000c10042c1c12602c0d10b2003141e02410540c2d07070140040c4c0c054000c05030400380c41140c0c031011400943c00e80c40702450183c01d0721300d4040c172440c0c800c1d11750344162180030403c60980c3c00d01c030800d94050f15000c0204a064501c05295050200e0b8070b48500c41c1c040924442c00503541c41003e581e110b0740c0444003e10040008212840901d038040c54140c1040342c003595400c0030b110010300440d4040c0a41441100c680c4a014645440e40e582170703c043e04101c0700000f01d88240310000c000140b81e48a201d600d07070b40300120f4100d1030414802c040c017529100014201c05001c030360440341c2c034900f8425501c01159450304046440f880225aa40d0081c0583c18001d0484144078043c0000e000380742d41400d200c4405100115001a4145104101481004650102d160b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84047807 1250 84046557 84046559
    0x5030711100f081003080331031209030207080f010c03060801060b04120309031e1b060e0d0203010e060c03060109080a02030a02040b0301090b09100e0f06132d060e1501 74
    0xc0c0c0720300a220b44c4400c0d10000ba801d0282c5984481e42e071a002100da070000403105d04204a034008142ca070f00500c01040403003680a074526a50000d00000c59240e0015020792605080003c1500900c9060301800c1c00c14100ca080c1d0507885140c80c040c04030300320507001192401f00c0c04201308a06005403401d07a610078400b02c0c902403030920f441c6004042448103600f007040c140c0000c4001040d814140c1c04580c0c5070500605039507401c0c144840031500040c00300d001085107090401110750001403640750103c045070140c01c0e9000c030b070011038050000031401141c030b030290a0030450071898103409036015860a903a20900c03162106852907858a0548000e98554442d5031403000500d45500303c0e09209101a0010039030003841e59503090383c1d40d0140c54254a50b000a040590007004038800d681001040300003c10391011504034035511a2005030a142100746043d0610f814084400400c40c402150500e15000034a0032040b050441035900b2007c0b650542444000d00b0b030301c40d0000b641c21200107822074409441e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84049057 1250 84047807 84047837
    0x90601030b19020c010605210c010f02030706060f080c18010b030a0605060a02010b090c040f030602131e06090608070219050c0307030b0609221104060b03040503071110 74
    0x41c500416440d95070b00b198403502d41002e840e00182118018690010071441c1c10102040011001103210070280c0c10000703010341010800041001402070f00b804c00006416070008124118451001c004d0170b06400c001c000200c0710301c1c0001ca80304517000030040d6200007403990304001181b13403408208803005803420010700001c2c824000454120303680800024a0b680c0c0c07030340800c8168104180a1015075903035002e02c02d1342d00b0700352000b5521100040d05a803501d420702d101d4513044502c5010182401c0d03800306d0340c10b9804484030310032006001c0300d2408a03421911141001c2d00411704d4090030000034001540014654069950345010f100c654010b08013040e100c84d0b0301001c0b00800c180c261424854a50107038656107060288401840c01450341d03280520305041448840d00002d01004644c0a481d0035200c600344c03a40d00a52410b0760700c00385611000040d5030000d001341940d03030801080a02c0000502040020010081000b64400d2242d280131803007840400c541038501c6052040410f4259202d1200c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84050307 1250 84049057 84049073
    0x1110309070608061909050a0b0301111e0906040b030411010201090c17100e010e010e030a020c1e03061e090105040305030a0c0302160309030308010b07031b050a050105070e040b03030309060103 85
    0x403141014106034846001d18056140e85c440561000d05443c1d80c2e603050141c1d962880c0288050120b0540082c030a042d404258041c0038440c1d1014240b59040c1c41041c842d5040385201200c005100007040305446a48900141030650b01c1594111000c1020143d01c40080d401070055940d40c5400c200446041490502e8070580c070350010041c22014000c3c42c901a110030302501c02c00d0300401c07074007000042c40c07403000407050308440e0381d160074010950007030020502c00d650015404848880a03104030400c140032145901d074140f0b05254041e4107001d014100305424034500d40d00c541031152203602e6001a02e98034800d80c22100244c0b0003900161040001520500458002e6138000350b4030b01d001072074443c01480103080c11244500440000f1484134007007092660007116140903299250003107103444120358026141140c0d01180307000c000124501d200a00006208070348995400c500244590701d001c90b00240050b00d100000c4d0300c114501102103200d41400801d0b02d200341c03c918010143d40c1d09648401003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84051557 1250 84050307 84050311
    0x803180f030a0606060f0507050607030e0304080109030e0112050417090a0503010905030703170f0106140c011509061706060f0d120203120a020c0c100207051e0301110309070608 78
    0x50444140310886005032010020356200901460000407020304000d0010718410f00043d1030420400d0900241000c5240800d016410500c41d0400103000c0303413036610703403401e60140303078010080d552818a000c3d081c503401c502842800b02c8242c0c2d89034102010444004125502601d02a101d040081020900b118502e40284a0700d400200100c135400d5a8200103400e43d901c803c801c58040e0804a00d940805821440761400340394a084400d28030b02d40b00718034144d82181440b4110401000059038404980390100b20344070668410002d2018040304002000500c0c8148a001441d510300200052031200c00c0d2400800568040050045502c6902c10040404420030999900901d1050450b00042c0c00781c18803100104550081c0d601c4078900911030904c0480146a440d445004201d00b8a280c1c00100e000502c4820454001071000d1030510202c1c5407202d160805600101603038464a41d841000160408031300b0b0442c024050b0403000400780c0d034640030540e80c0d41426803080809100403401260429 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84052807 1250 84051557 84051559
    0x180204061b0213090c0810050105010212130f0e06010207090c021b03010f060e0702070e010501080a0e0705040203010f1410080103080a020c040906060e0f10060e0d14030c0d0306080318 81
    0x180703000d25030f01c0440b001c41d001388904a070481c881c281d041103009004c2c882200444c60f02c51041105616110010352034805520351041000300005005680c003080102c401d0117004140040202c00e52240c42503204a01c1c150303401405031285044c005000d40d224003a000c2c0d0308000354080c2500881c068400340b841e8003140b10803a030654035a02014600a00d5204140003080700341405109802c0281d4080c1c141407042d0001c41a032280600140b00f207917044035820b500440c02d05400100c1042d000300841c1800141d0308050303071041c000000001ea40424141c00350903646601035041801c2640020070200c082000500ca000c946820010004522003030050300d02c10b001c0380155407100740c1c44070002c0d00b290b00c612001ca50095603020180141802640210703400380c0112600c211034101070b205600c40e04c003144104800c021844130a050b03281c499040402da22030384a0a040600c00803245010784030303080b0002c0101c1e14812030111940d0f00d4440d01078081207415080280d450309155401142e0200d412801031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84054057 1250 84052807 84052819
    0xf0e121905010b06070f03080109051303050304020f030618070b16060c0903150603110306090c04020306010e06030c030703110a0c0213020f0c010905011b121a060c07180204061b02 79
    0x103c001511004010a49248203d54944900809140c05040c580041e005a20600d10303060402940030007900d03800d0089905420426181d41ea075200040755030035440f141c02d0f05801180c05000c4211070355903c8241801c00d01c3c003598002c60700c0c2d07070b01807070103000306180d003c0302d04c8003054000f0200d60698009500c8600c00d1030002503140e100e441e00482d0954403000c41260903038641081091200f0540003140700c1b0700450140c0308508021103441c0c0d490100b00c0041d84201d600101041d03a580c0154074401c100003010302100e03180e1600706a605e10070307002141c440010905146408d4074000c20941110b400d04016210107040d55030640901c24800740180601c1c0b01d8a40c200076156415503c40c01602c002c84002c000070540d108149842070a40b00c00e030600a030004010700900c510076400c80c4021888010064002a048002207602034807403040004194008400013160340a0401c0420f0300030070354401002e2540f0710610280f440301288544c2c0720b9440002d03940c0741040240204502c10844140c001006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84055307 1250 84054057 84054071
    0x6120e0613051c08090c010e130f06050409060e070602010606050406080a1401150e03121b0102070f050a060e06060d062c0304030506010b070b040210050d0c0f0e12190501 75
    0x400d41c2100008641004c13500384000c2186a07042042502c502120a20b00700c4040d5104001084405907804910325946460301c40c0c800c0c0c1c601d0f0f41d40c0128004c002c014400d11603080c050410000500546902404900030460b01003405401401542c0442d6000c0e580d6500d09440e2600c105c2d80c4c047c02800400c55540c4540c50300b404c91851041d5a40a0320a46581031241690240007401164514403542d0083d00489000b94a026250098409441818502d0f001003080b40c04080c0c02881444002000c200741f4024140510070b00040840384d032842008104003c084d0b40b003110750785050494070316a010004c1a41040041e01c240c0040440c0101e084840820100390300c04000501803180c20440c25a0012908006004007088107900500e081d103a0a03240c8000e98403841c8146100510107401000000541c1307051912a00c11940c0300095000300f0452110110802040907031701640c418006441800000590300e004804070340c41d03150040080c5111010200c94162000303000905980c02d540c2c0e128 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84056557 1250 84055307 84055333
    0xc0504020a0e131b0503090105160e040b03070302100c140f030f070f0b0a02030703110c0309040c0203130807061706030604021507020a0306020d050c0a0807080604020403080c0706120e061305 84
    0x112403184e0801e1500d501c1d4491800902181c01c4400c005d041c2c140c1c600c441c826140d803007900242d91182d4440242e40c00310748400050081307450300c06140d10094000f81c0040c6c04d8259a540a81000345051050602d41504444000e025541d001c20384070151041d0010001c0012101404000306016446181800c0c0040f4982e1101c0000760012980b580400e5000001c01100c1d80d450310510002111a908443c140180d603903005070760340640b0308001c3c004c0f030f9290b105018040c004c10a4403d507122007030300303040a070307494a039055160b4000d48200c8011642c03e071901d04140d40308140140c8510000b8000740300c01e5450742c0030850303014a00e1450b00300250b8200b10b04800360b1944c40802020b0750207010056564072580a40c801101c400514451503002d0900406a5442e4007000c003d40103141031405900035140d074400036000348034a0380002c00c0300c040060280d604000100b1200111410b40d26890140e50003901e1501c00d40c1c02c0340d202074686412040010b12200340052001c0301e0349028508580d40001254 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84057807 1250 84056557 84056591
    0xf0904030201090b070912170f1306080f22020f13051501080402011e090909060903120b030d050711060a08090601150f030209040e01060b04030c0504020a0e13 70
    0x9101540140d441d80034030824404010701c1e4940010742032411202140c40c024009000c03110003d0014a000c50840d0f280513108109400d5460701110040007a90344e00301d541840410310101c0c8143c00118095030700040e00c0303440780000c241c80b5510701e013070340400040c0203440020012070711182241e0150682950b20043d4031840a039070a0011011400505401c042c0c05680d02c04203c40344040c10050400d0801005036803010845a25008006040080c2c40c0254416a031f141d40640040180343d03e01070a640501215402c80d694980c02074640c081391031418035002065581c40380c0c00da03805911130303000850004d216000400344a80180141000310b221000003401c25802207040500040d211070030301000b1201406154010200001d5414110800c40b1019000d0301c6e0a0181009169003c208440c0640f40c88c0c2015045d461024000c00c040d40d2588140085500140030170b5039450041d4070003044504080c42143c40540ca1362715228141d1a020b8200b0807460150611360001580b950a1591450420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84059057 1250 84057807 84057811
    0x61e06060901030e070605091c02030a08070512030c0d0c0801051c02040213030f170a020606120a020a03050607020c03071a070f050f0705040507080f150303040b0f040303031407050301050f0f09 85
    0x3903500c8503910b203035007020441440301d5920309000a010b83d28800c40180d80000c2e0a81c004dd0344001041c0d01d070fa456041ca641070079040b18164000542c00810000081c0c81c140007022100d100000c1000203c000c1d980c03c8400715404d004040d041103482105c1e00c400c00e84d4803a150491031000713002501c4d2a507402a044040c0500740c4c011260000d405d04024100403000c280b407589049038204282c01d0030b455080080d603a5201802c004d01031100d40c65803060703298040c00150700c1c5030b03005020010110364925015540b0b82044030504014020307221224081d24001c114a412230340309810300a1030004610700ea40c400d0380610800c4900e40340c09031122002034002d101c0600d0b03484816000c2c24080b464101403109550004084c0010002c2c60010080e0400c6a2000f85030004200c000c1c0841810282c0007180ca144101c0e000400100f101080040e80302010f04024415648a42e0701800a015034400d01032003018185c0754580450f200748014400d038104108040112a0b0080107030811100c0342000c03c0d400313001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84060307 1250 84059057 84059069
    0x1030303051f120501050603030f071209050301090308040606120c090b010504051509040f0506030a330914120a0332151504060804050f0d11061e06060901030e07 71
    0x4540d450f0014000d080c802c16500030801c6d000b440c600022043d04050510950200070068a1150400044540300b088081c0180a0180080101840e07d00307004c0d182a00440b011250300c0d0070413001081460b040d654003201f141c8d00c819400030751805c0c14240400350042c00042c030304100081c0030000b00c6585521001c1d040d0320060030800e0780c515060041c003040d103004c6404154050304150030300c08992030025134021030f17a8003c40c3c400700074102d1012000804446400380c41004001c9291001401c6040e84018030b0b527841404282d0442486040042c2c84400380b522094950300c05100380c01c0d616000e42c0001c422072102a840c451024030300d0002014888215105451045000c41044403025025000e6030102d5812034409000d50303014072000c49644501d01a1104000760701004c501004020051000b203184080d0556011004868000700440e400880c820a1441840003094480e0345411012110740c101c4030b1204400e5443c03100380f2680d0780c0044651410155074820550040909100076406458 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84061557 1250 84060307 84060329
    0x4090c06080106020105060a1d040609140d0e09040b06100504080604030e0f030c0a090207020f03100c1d030703030c05030d050708010f09061d0408040801020403080a08010e040b01030303051f 84
    0x4180f10009003190720061803140900689102070100089090326405a5404040c401d25155100d152505c090481c0000003003580c2020b01c5c40d0a0848404210000e511440c1d6603001c07014000f1108001e50040d054401500e000ca041001c240c0031305050703610013091117490a0142c60281e580b501c0b03500e06001101d09030005113849841c03620524100c49500140321044004060032241e41c000a5440101441066402a800601c6104546800d2001407503003034000e00761418485145001d20240040b19000e5001039048074641015181011000e0103480024004003290b5046550503200f80c1c01228080d10385120501960390305046900585110359076982e210b000c03c1d40350240c0a1032110450708203041c00d1b41003000a00c2407050303044140c032030100420149161900c82d810320b100301e84200e170822401540005004030510580c3d80082030341c484a9525548540c0c0d8604000c000398005031002007101c16403800401c0424802e412242d0851201c4818410355007215140740341440b02c60b070024004072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84062807 1250 84061557 84061559
    0x110a0b07080d0507051c0507020c0d151805030301030305031b1612091d060d0203030301060c110d0305030f0a02090a030c080d020706021c0504032009072c04090c060801 74
    0x2000340203654015046042c12030a0011000d00202d200b40b810205803200c6d80e49030001000e8070b208004400d0000301c054080050401c180c1004580c1c654080c001241c518181301410121803120703820700d02c0c4942c01a000d18196400c540c3c1c1280d05030310107031945147c03110322582d845400004c0e400038040208801113600b228034280c544030341e4403d91208941d080c0481c2603010003c11043c074100800c0100041c00c050b800e981c0701c500180c402c10000002940510000c000810240d40100100000030b001c0c1d1000c1401318800002c000104804400040000700c0900c00b250585014a201a401418200015082c0205e071004a81c090400398800e60305444064070411404030184004c034002440e0384080c05210707041ca54040d50350040b04040350b05111040400840240c40f8006681c040c542c01200e0b841800e045601d200382415904107220b2245080704082951a4003642000040c4026880d64411b402c094101c0081503100001581d80c02603111000b0800041c0c00400300c0c0080c04242d103d1000e59 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84064057 1250 84062807 84062827
    0x1a0f120406050c0a200f06070f020105060d032708010c0e01140310030b070203041a0c1605130f1404061b020a030509040507120e0c01110a0807110a0b0708 68
    0x5298003401543d450b030030400885000380e178000d880c218066444140720f00a40d02c003500e07807031030b000920300d00d07407000e0044109200700c03a90b01140d00300d205200c2d9402840b03540c80e4034082100511110030020701140e26404000b08100c45c0104003400c050003000e0b0014039079942c0300b00b542503a6107040d4800000351a452460165a08140c000c00300c0d440520742c690440c900080050301105050002610b80a030034400225018400c10468000c1d01e4030a0030540d40301490701d81caa11907007001b907200c081c03405200c80410351800601e180404450000b000112480340e102074036001840034403522420251503d44d40c1651000225269025030301c14040082c1c0c0545c0e04000c0203601c10800200000c41d0841d101100210f9402420354601c988100c0300003610741c5a01c082070312108540070702c0e400c209003410b074401240c0c403006c222400c280c0400c0e00c9011190402c042c081e9103411482400809540e41403007694085610789001000000000d040401040d407900b0b9400134a40003200d0440301180300084560038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84065307 1250 84064057 84064061
    0xc030b0d080a030606111b06070c09090309050402030f18151509180c101101050702070905091614030f15010510111e010b0a0e0a241a0f120406 63
    0xa145c507140c070701c0c125030803920b500ea22129140b541c2c0e801c858640ba1884c509a641c0d60482e001c442e0710180c1040000d03580d4800601400000c44194003149850100041608080c000c0341d00c10647e900e64808581c0d502045500140301c42e56100b40184240d01d061901c02d403102c51014041d452054208020b5082c0c0d100704030503c40003c03c0c904c034080e154924125601303c00188104616811200700c40143c902c00011902c41707840b0700940d00c00350300b45000e0011450700440c40c43d054130390a040510060b81c036907003481d07502e014480c2403212000704803008000010711100c0340d0950080080c04d0b10400b41c1100c0030145070402c001c00c200185191078004000030b02d40b400d80000014554206800241c0e041845980c881d8203030980c10300c80740505800030f14084420f600030104040018412450562100214021306004854140d0024a0b007445c900300d00035050030407a05c12420b0894070b2070941c1400741203000c1840410180300a01d0041c4500d680d1401514044c040a0501e00e00c0a94940303401d04104007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84066557 1250 84065307 84065309
    0x11506030606080c0f2a0d09050a03030804020409050d020f070801200304020a0513021c050f0c0703141803010b0406141908060708010303020d05040510030c030b0d080a0306 76
    0x80c940350031400c200468000440540c0210640409500d880707040f02071004c14481d860aa04840515208060340030b000c00300e850b0000401c02e0200ca00c21084a0016074241059000d940d5010000b1442000041d00c100020f41c0d0180c40500041804003495640901d89805590790f107000d1b0b0440c00d40a41d0200381008403000401492000340460085126600300007000341001e881420000800607081d5210040a8401402e002e42403202007804039154000a41150382d482c500802030b40044114548035001d03890244c101ca0000c54259242c1d000d0080d00c5a0244101328244800808104a8401c45101411056450242200e01ca1032a2410182180c464500f002c2c0710350702c0e044003442410181c00f566070b02e0b0f400c199064000c11310041466581440c3c66400000c052054008001440346d1101d5440d04880c0310303400b00d4601902c2c1400c182c5d954003483c040d032074104100e06c0000700118481c0d004254800c05c1401d00051811070203020030384602c0010070644040b000003a608501e01d0345445140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84067807 1250 84066557 84066569
    0xc0f02030325051c02090a0b03060307090c11011a010306081f020d0603051912050a0509060711121b04060803040b0c03040509040c03050106060507020d03111603050115 74
    0x151451815030406503820128400040051220030b41c20400a40910111403501042911070354621002c2e00100c4003030f501100419006190b10706001503101c0100c81507071f00810b0024003500e0864140107107040100740b100d8580f0300704500b12081c050540313400c0c0305041074000f849008140014041c0005004e442841d48421581da211010100112a00b0141406174a58040c0d01580c0c40200300002c1018089540000d0030364080c0d0466503c02801d040c0031032040b10700c07484101c90003500c0f4aa00f070300e0318011025108080f49040120424070f160407401840b615214504912400241030086010080d50b0920569217921440d000c00c41103581c00c079990200d50084806100303081c144074046841c2c2c003507441100f8040c440031503100c041400500545018160280c8025240d26060800200010b181d200c265036079407800c4804100b0324402e408071849260060002c0004802c20358040701c48200041c031000e01405244801012201d03000300c0500114000d000209000040030b40340346020300d80398031031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84069057 1250 84067807 84067813
    0x604060c03030b09011211040f1416030b011209022103030a1d0304090509030c0d120b0307030c03020607020301200403140d020d08090f16140409050303061201021c0c0f02 75
    0x10468400c006e80d000300c1166010200444019599002c90003501100e841d00c2d50309801d01800f030283c4d02040210740d01c289555945841d034950f004100383c08481071141303024001684880c10203030038031f1686c010759809031002c1d001c0d60788e94203800980d004a12105111400c55003001060184501950140b0307031387c80034000a0002d8014107441c805a40b4410384c8907c400c0503841c0e60000e401c4842c1070059030300b411004419182e01200e4444001e109082d18250400c840d480e081610500d400d00285490549900607003284c00c246c29502001701e203030040309040781c1c15900d80c1c025070302d03000c040d02003222002c6505501640391411031a02d481c0b80719000d00203000703680c0500c1d4000400d95001981480c03000d414104900540c44042c1180d0500b1a48221000d45102d116240200c03440d19040c0c03030302191000c207100c064403c40e00d810070040c0d810714071003e400e0b0740c414808110203140c40d244003070300d545002c0001454000c0c00d071071403000b04d080c0c003210072481d07562010300c01b001c0c07a00f017086140182054805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84070307 1250 84069057 84069059
    0x4031d03030a030c0309060e0d1d0d0303020903100606090801060501080c03040f02011806050d240311010903020a121202030f0304170c010510060f141603030b0604060c03030b0901 79
    0x441e030340b40940c02411003050b454a92180e1150701a44c40040503903001401444403500382540150794400003603001c0001131911f000300e41d580c204c51403820050507004042c582518a1900c0440c065000348005a84c107000c0d14034078503d00b886078400c0800600b407507221403130524076100760302e801c5420319071150381445946010804500c00070b8040b00e500c6940441489071010f081d00040300d4004a01d800c180741d00303095090101d903440c0c011002d421a015080c90a100505941383c4015841030355000b8940b040451120620000300001b00704861114103240c440903d07950390300050000146036001300c940030601c824141c00d210314048111315021aa000840c0344c103a6042c0e01c005c4a04c00284050101511000502c644440310303411aa45250603500034081810882080000c0c070901d80305500102320003495100810340145031403148900100e056600309000020b548101200c01c80c021400c059032110301189039600c5c0b402910262010f5501e9080140d514640030381181c02074040e03503200303002c8240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84071557 1250 84070307 84070309
    0x1b010c06050a02040302090f1611030901081807030812060a0620010b090705030f090c130e0c04060b0d061d04140a15092a050d08040e010e04031d 64
    0x1061808680c41080003803a0b40e540b0240c40b000340034941000750b1100c2c00c04280404012a140c0c1980641c411803900746113250441e07015591002c8506001203240c0050143c00c1d129130042814030f81c4038412a252001c41841503450300e0600201e03400445134005c010400c114084035511060b54009030a03143d084100f130070078001500e4000402c01e03104100f80d03038143c3c3c81c143c01c20031f4016404c2d440b03020b010300310a820243c4019020303400448a01c43c402c52034800240701e00200280100305804050f100c3c40320818410030900180140b44c03180070483c428440e42c04c41d59251441208010074240c5000ea80352400014440c003515030a9102ca400c6c98000410700d40c5005206941c0ea400c40da012040d0400c040c1e1010306642030070100306029100384600b83c003402501545d500442165445074288100401c519483c01804040803980b98806400c03c100501c510304254481d40d541500038600141404c0c1d5502c0d684051031000d800450342e5000c0304051204154204000a988039101c610342c2c0c054480ca04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84072807 1250 84071557 84071567
    0x20111030f010513020403061811040902150702030705030307081c0603020a060302210a151a0406030b0102100c03020a030f02090f210f070302090c12040308040602040b03090a0201021b01 82
    0x2008003032180c00e1320010407030f4071400f80d0304031001113902040601082100c0c810301d95190305101c500342e400c070210329482061880c052044140c0b107a8010100720518010744c1000035950855841242c03d489412030209480d542000a000b0340c0344140212a600c5c13400c00c0880c8440b0f4040c1d4050724106041a80500060352a2100d0b0b0040c0c44d0b0750304d4016152005401e6184a003c2d40c03a900500350340c06101442003c034083e40102440403030080300036910319500c20910410220f404101074003183c051000740f28131031203500300f4a9120014811100b0090708003445ca4125281d0034030100200b58006010340705140c150249054648054504500346a49900400c009030440900644183c1d154501d0071801c03034a02580f0050180188100c2d580024003000e801d43d90542c030b001c04d9200d2040d410000700c407803a154048944081e0042a4000340c2e490325501650903071409041180c800780c00b0302021603005402c50103940f14140c408024213080b030544c000a418035205021032144048442c5088040d40d80103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84074057 1250 84072807 84072809
    0x3230a020c0c031c0302070804150c0c0b04031a1b0a17010f080d0e060f0a030509101b03020a0201090213230c04050607050a050f0a110f09190624020111030f01 70
    0x1a08025a46840300d20f8030085500c03940c1c03c032b041090080401940070301c4d07200f034604051034407818511001540740d1440c080345010728880105800940d4140c4d4800d84040c0e26040d420200d031110791b40c2030b0348407840ca006040d0842c1d46e0b0b075000588075100301e41030300894030034140c0140401080c0c101034908003140d441d1907040c0c801d51b820130301030002d003c120691180f03c1118203e20076604410b4403018a00300040240109a41d4440c07036204598004000c00c10740e1003850740341c0d1064007105610680c0c445c000d402030340100c2062003e55580325030100160300c5180000803840d05e03400c8005040c2c9508140310b0a0f007101c1d000103184a2012200300012426904100c80540302d04461840c0c0310409480c2c03c0e0701d05902e1070301c01040d41c09018460700308200009803550b822480b0341c03c01800304151805000c101040720540591160354000454a07000d106100482c152140c0030012504c240c46401101103040d0b40c41e41c001c05408401c030b49103a440d03420f1140c41c404c103c1c0789c01c1085c40d504004188940201c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84075307 1250 84074057 84074113
    0x1a07030209062205091311030102160308130c0f06121a040911030703050c01020f0c010f0e011e0242101706100605070f0303230a020c0c03 61
    0x2040c41481d107005149070f000401000c0080083d03807a0314048010303030a82d03640f20300102c8448400309519443d84c030701030090b03804840400007401d00306c06007074604540c000e0b405801042c100d054450880d01003415881504047c0a003145450312a600c0e00500500d2081c51840c445242403400e50200e50904c068035011408140c21200400c000c040f40c1448094503500c2d400140d070510074510004108500070030741c486241c009800703540c14100d07290001c40c0c8608e440c09206000403003102500b1300c0c00e40280c07044080120b062410040d80300402c000d04050034901c592810150344080c011003105005190f01e2400f11000c6983c0030444203483c010f41d41c5007000ea4420600e41c00411000940c182c0008410700010f040800c074203480f0090b00c0200319116074007504c505441c40e040034004640035008500700c501c01c0d40c0c81070b03080004880c146ca084004107460701c1030031022120314130030b031446078400e01c40e2a008a2800400583c0e580558004600d8069610440d901a4001200c549900c0d6503401c22004140c803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84076557 1250 84075307 84075337
    0x503040308042402120601031103090d0f03110a12050a0e06042303041508010906140d02010504090f0203010e06040902060409050a18030203090a06020712020f03070b071a0703020906 80
    0x250410032000b1840180303c446040d51011034019000011a000540204000e032020000f01c51800b8842150b444200d4504400d940482520910184114000d060204451800250f179014500240c1d94541c001d12110000a8002c0074965101c5000c0c42001d4001844407000c11089456603040c0307450385002003000e4804030402c90840c8644190040c080140060101600c2d956030b10b66200e5485090b0900031040010328220010038400ca02e07200d0f101c103945c60f1410a40c04062000208207282c06100801c13170400c00305200c0040c1d0f41e110b0b07000f0407008103441503015840390b042944110415800528a0b88118100a0003401588400080f03e0590301d8640002c01d6540d6600f58082c040d01c3c036207103010b8500f0042c440c20414154080050050300d10116141c8460b1580d510040340e40d00c0c1c540c000d091044160142c2c803001882e00c0000b00c4120900501914801076403100340d2151900690019122043c2035401d1010f20120072240940c0b16155050460900c4c1c0040d0103c0d03900c0c05500d50200802d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84077807 1250 84076557 84076583
    0x1b062604020f12030c1b0a050418021f08090c1807050c0703030c0b090703030206070e0307031205040513020c0c0f120d0302090102011406032e0c021b01050304030804 73
    0x244802e491078940e550050305071115a11221002d03603070fa501c680410721050080065000c4609410301240038a07110080541c1e203403a0501003004001c1c8961201d8462041c0b40112400c01a00d403542c9404201d000301c0b640b6540082c0a04000e01120b5008011281c66000f020aa403855030351801e00700c103032448080110516903100c071802d0b035127845680d0307a0000c94403650f0800410568403501e0102541d100740c1102d116612100d91440e940c540d1800014056009a4001030710240b0940190b000170708000c044880c5140e494444036250400c08840b00b0001e00d0008007403200d0b051110f01d0a50310325211100318075068020880540303928020f100c1c00e200f4410100c4110340c0340d8807541e2680c0511080c005480400d84ae05074042e009501c03002c591800340d400d0644205004400c07082c40ca10841d8041c003d000d028041200c108042c0701c0c00c1c0e859000ca244094115011400d241c4110400601e642e002000d10300c142180b1446901c015140141c10040d04200f000002680002c0054001c0d900071000b42f40340c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84079057 1250 84077807 84077809
    0x3050a02030f07060b1008060907080c1201080106060e09092a0603070305060f0301020c03070f060221092a01030b22060e06030601030201051903060b071b06260402 72
    0x500c42e20042440c007000c00701c2d241003480810ba0010070301705c1c0100c0d021410110035180c1070341c1d00602180c006610503464000140a203000d440c50f164400c1682041e985003210840c181301403510281c0150580c0e07036544c0d80c1031149a80041b01009682c0c1c080318805000d24002401036070350801c8406035041c10303c09200d410010b00c24640d00066000b00241110749034905603100400030501224150710035044000403850509041c4200d0394103c84950255280c0a0b0b03545464004424004080f626103508100c010400c0d80319210f90110700307020307ca60f04428201021700c80c0c9881000e58849204d15000380302319040a6036500c515111803828200800c00525010003c0d03849a071070030300400440c20700c10014005800e80c1e4000c80980ba030b1204191856280e4030305141da9103400740002400700350308124510741c420f0150018003811445281c013258282d12954000c40c0d51300007540803078401a110755881201c100c60071001c03010703090a1501300c10101c2d80c10b0302034495409440d903040c010380500000c0380075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84080307 1250 84079057 84079063
    0xa02030a0f051203160806040e030d050c040503151503063d0b070303180203060f040807202706010309030302040801110c07090b060d0c0201020c060f0702010605010212040303050a02 80
    0x61003d030411155264034290802c914010700c2401c43c2d8000038045000620b00c0e10700741c81900301d820090401917080960f52881d21000344400740c191552a5424080060b007a90100911000b4440c51800e41d000c1c3c0c02e1960070381c0b0306103592280052203500f01004101080490119a00b40500c1110403020084800304034000d61662300714405081010f000004038040e0f80640040614500c2a50100b020800701c04000c0d008901d20b01000707506820000202d6000e01200c4881a00b00c0c0c0078200c4c00e8907140442d55a4081c0309000906081c102e041487c004050f0716103101340b0310020b111030400007941145005a10681507000700400c3c140f581e100e04403810f1510a0741901d001d02945d0000f00050940d000901d400e681001d4107904451086040c00700d18440c450003240410761016100506001045800700090311400000c181190360a116035110b0740360030080d56000b00794074070001e1a03078240088000d003135903501d411044c1550b011030f60740d00300c204005d403c076001c898140c502152108004901242 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84081557 1250 84080307 84080323
    0x90f1101030e010e07180203151011010906050f0c0711042c07091d030406200604140c0a06050f0904060f030b0108060105121e011e05010806090a02030a0f05 69
    0x2082d44ca09009582452000035411099480c1d10000d855083c4d1074590100580c841103078110011211140c5400b080c2c00e00d06c00f211518401e90900207034400803200f03040d00311000d0240990350035403160306110703004c80324010b415045100344402c980760075543d0329082090b4508540442c021655840f0002d6925595803180980007015682c4c0214070741c00b090300d560340315070074010207140702c1c030f4203030240304200902d000014100020390145050924041054801a000030828290040b0b045140084043d060010510480c03258061600c0a05038030222031401d0b00244410f402545c00340e01c2030041640007400d54082045511805035160701b4403000c100030741801d174400c00351440da010000c01080100041141a81c2c03a040441f01d240e03a80301c00704002100313100b000c0c44554011176109200e040403584004407840d010f000115840c100d091910150801b5240301040780340e036490051103000c8091020179040002e84009002c0c240c080e80000c0d84880c02100010988480100340c081000820b0040d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84082807 1250 84081557 84081581
    0x915180c010e1201021b120c0d080a0908220b090112050901020c06070c0303050a05100e090f030d0207050105060a05150a020709020f07050f0a050714040209030115030213090f110103 80
    0xd501c81c2d941c180003a03849006d14501c1c90381d9010304c0d11002542d8014505456154001074000c1200001c8c5850070b50b03400401412920701d280d00d82c0741d0f840102700f04000421000035041c0d149010752030061407108841009802c08005010104440310081e070f8017140c80d40000d40d90718800146603c408070744900900c145a084125409460b003084400c2d9040620440030728080c1d102031261b40c0e240100d050803208100c07090501025840414000118501d0f142c6a000840a0440301040070404c100c5e0f11795000560b0000ba41d540025400040013000c0c0a0250840c0c019502a110a410000090566049440801c40b81d00c00480c5981c1c1e400d208000000080103040c10031561030144446040042d480712200b0340d039601c80d1080b074003119100041c1064a0721342040180540350700304821310007195244103046130701035028400d4090f0b41d82c00703209034103070f1a018400c01c10310540780d48148682e0422990b001d0345900d240487d920049070700c4820350000e090344403030180ca40040c80c2d070051b4014581c500b03d903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84084057 1250 84082807 84082811
    0x8060903030f0a020a09060e0414010e07030c020303150607020616060204030618030e010807030b03060f0414030a02030d0902040212150901050f010516020a0302090915180c010e1201 80
    0x201014a101100542c0114003940140045a5441d00304a081c0c0c800c01c48001d00152080e6005c0201502c82c21044088000040001c680c1d03403d4040c1001c01d0503000e80002100f003c0040c28030425540510844441190350b00207941949059228207000c50184410f00f80076900001d000e904669078082101d0030000340d081401011072045c20f1000080d00603000895080e8549007407035074040d4802d0203141c01181e041c1d61b070b80e40c0c9a06500045030500d4014150206150703c422184c1e000b80e406001651103400403184640c0e1500d064181038001000300c010411098000b0003414441f00c1d4084100c03400b6824820000c01d2850462010400a2099902c6001204140e40900181044144039a014868221094021030b45c82e0000c00c01c1a0000d4000f071400719008001d2903404c130400f071460203ca140010a88100569a50040794010b00104e079003503100c1d0003400c603081d41c040c1e003000d80070f0f003000c03130392190030300540c0b04c3c128007595680c84102007410301c03008882ea070120340d9074180300c02d185034a40700007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84085307 1250 84084057 84084061
    0x6111912050c030340110a0b041403010b0103141807150201020909060405190e10020c0f060c0403030917100e0c01080f04050c01050304150216050d030603030801140a0806 75
    0x289042c000409010750000c1c50304004407075150010030505e2292942e030110800c0004400b0390320301500c03561038140e40350884007000001506840d4100500020b2052038082d404541d00002010b00316000e0281c0c1506061609907070b0540c3d0b0300104c03102603004049229031030540c050b4100d80c61601006a1001001d41030f0910203502c81036041d00644604070003610020304548400d8100410b44008490010007109045851b10f61038046410400c0e40d090400280d6414141c4d500c2c488050342d02c1045106242d50003400035008000040200307541c014124401d4500707060a540d030060440385a803081070460703900c90119040e549002e0014440c0000114420000440d43d160f14a071540301041005001c250b0784000240707150380801e9268400c0c0e6110f03010b8089201d24400645060f0000380c015a403410828070200480c102c0742c07008292078010011600240d001d5407400038a0b01055005403400c141c2405401c0001a400500c0641521030101010360300c24914008180d4054a6512014292048500b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84086557 1250 84085307 84085321
    0x501120b09010f290a0f0c120507050d111209040e060a0c030c08011a0f070b01080a11031501140f06030a0b03010507020a0804060315050d0b0106111912050c0303 71
    0x50034001c40b03010540001001ca4149918640b1344c000a007810800901004651012449015124183c0030507007440c2c964030301162285180c0520485440010420000d0300b00f0a015080118850203035152812400c1d2035012003806031601c031103000d41d155203480410407000503601d64000402080b004001c445451610f40c448801900820440c0ea000c80d1416102c59801407003a00d119041c0c0d00c1d2491801c4920060b054290b025a0111090700d169290070321980000800b44030411780200440f074000c00e141ca1903402e00d0762824007003030071441c4a5800b00846030040792170515240d0455014103c04a45401c0305c1000c81c0005012140741e6034003031400400c0003e100d9055001d0300000c47d0a13002081300b951240360a0b41c3d20075241c0c20141c038000b020720080003428402c0c2c01c10041ca0492103860b003007041e5200003050305014415030460b544103031800144485940040c8041e00024070701c004008402001082c0c2c9009001c548014001e4011001a03004090080044a2807040140b007140e50b03900e8501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84087807 1250 84086557 84086579
    0x20609040f0b091302060f0708160606060f0509010c02240d021b0a02060d051017060a0b0901050f060309010b0a06020703030906020d0e0105090d0c0b04031502030903040501120b0901 80
    0x2500d01481107900201140c41200c0643c00f013150580e010341810302d008031141e18490b1542002030101d51f094400c03c0704604106035003020f256591b1240704042251400c021020b010042115484820040c090000890581e40031429a1603d50103503803500030350380601160408491f1740c0328800c040500002e410284400c8a0f80280f84100182000c23600b000301e0348015545500802d180a98440790601c90f0081074142a809030307030804103410111488079070700d4458900c0e031a200414040107810000400981e120140512560500101c1c0c40361555070501c000507154001500c0011700620000c00010b1440d2000d5010b248000d00060083c9400e69464100966614450008400240d2020000560a400058290031a41040c2c440c42603034600b240c011116030700003803403180d0310021545058020603c20342c4800042c10100f41d203503986500310300f0241d010408600191070880d10400804c8045200030056805549092030242ca01040044d00c010207805111555640301664000000b100c1a140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84089057 1250 84087807 84087821
    0x20109050a1e140306160c050a080703030f0506010f0309050102070f0807051504050309040b030c120105090111071505100f06050301031202012310090204090e07050307060504060c020609040f 84
    0x101c1c2455440c9915001031a50704940b02c3c24042d0903a03c0803020074044911940900040c401c0c03032900450000302a1906842e0090741542601c0000f800654030092540c1801403605449070800c0030f00031810914002001c000e000300c0c85000b0075a4444009040190030340403984107070b401000705408012541002d041d5a40903940450b110b10501d8a02c48802050a100750300c1580c01101641c100b905290900c00030f009c031124201d5050068480174803180e80d03405010281442003400000d03035864044c070320a00310f80d2040c0700c03189030075000e11900000030324480400101107814035000c101a1240180c5044c414000d030400e080f610100e10b40400c0140c0d024001d107040300d020700d1610710800e15040041e8200d610403c03030100002030040b0400034603c1c0f07030000c9503045403e0b88100301480c0e0b6201c4440b4100d030059048003110a4542c050541011408c1003420040c003022000740c8011868814080c11394410b900c52203050001d01ca000380c09540d600800d0301d03440301001d00148061504024090b00601343c4e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84090307 1250 84089057 84089099
    0xa0c0504080a1101030b010c170715050a0905060106092301030207080f030f1305030a080c090303070302010e390406050a030312050a050c0f09040f0606050403050136020109050a 78
    0xb46c01a04a01d940c8035040c141416500411205504007894500c1000c69100340c07400d60760751011740c8119550b50070600c103103481500a0307800099400b200c1c0c40c16a040c400f046c0e00c58800c0041c0d8079000c1c4a4000010100d0490045c00b20016254610400060707002c2d01690601500600c400b25486c110310501500642c440d010030b0f00e840006a4449500d80791303181c107000740038142e90b01c20302c00119043d02402c1159045003041c0300f064280b00b00c510000385168440c0300110010303512010391600c1c4801c2006103201c8a802c600d001003241c0c511040910307140490382e947c80440c1c140c510b400d0b40740b40c03031315071142d80504400703000404000d4888c103001d4180500940c460708010b00d85000111050004c1c46054000c00041c3d811501c0d06980713007041c44143d085050181e51195840d80148000801481440c004011039210aa11795203182426821076000381540b1844030f941c030300346000c0000c84501d10000122074000c2c107a0803000b01c0c00103c40d03c29143c0c0085030083d4031008046140c1020414aa0340c07480707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84091557 1250 84090307 84090311
    0x6120302061f031203090201090918060b0609100c0c1a0909130206030112060b0d030c03080a1823060108010e010605060f0429031303030c0806090a0c0504080a110103 73
    0x8a99070b92140d4000c00c0f403001402c050b0401c9802e10203d4425080041d94038014034181000540301c50a500446050543c1c0010701c0004e5011802006058000e910460703d0441c2d8240c1000d148001190700514201072410411481d840e541c41040b2050001304050040085203085d03900305400001842d62141103100c1c0300b0b0683d48000b40e01003002e0b07040c041d05640d024018a0850746080d21420082100c0c2c1002c403403054039440000601c0d02e4891901404a0182d078510407001c415080c05420b01001904205105041c43d00f1651f60070142ca42c580c4816a0200b00d180030103080b400c0b841ea0f001040c0201480500454000240a11054200c5101400c2d008001c111340d540d2142081480e10654031007620040081c00200080312004800c2101c0301c1400548410b0b1600e1940c001c07015900407954601801412014101459070600c01c490403007185003400421411320100252501c040100f28011a54540c084001c07010b11403000c4d540100441c4048458502441c0341424101d0100d402c0c00340024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84092807 1250 84091557 84091591
    0x41e02070c031703070c030305070522030b100f0521030c0124180203060316120b0606070807060504020105040f030f02040e1227090103031101050702120f0d0612030206 74
    0x3c1c41c07007422a401040240c03030ba0501c02c041c5660683c042c00d002000b44060000134407464904a00c0c8250034481442d40c1000c003d0300905529020040d0341c8086c0c2440c0302c03180102d030709006011121007540309407403040b0b0b003203100d01885020810740b04042030104240341c00049000c00c160401500101d440f81c280c00c8001c6040e0300c4003401803043d003500d80f0603281c29026019411030070042c143e0046402c150050262090400c0081c00e5145041560780f2140c4118014100c50301030220280103242c0010007128400d01d450b1558440f541e11340100d1030054100e0b46c3d1040440c007160f000c5c3c1c0440d4010590300181c821490360304d050501101c46c1c0000180d0249080070000d2a2050010807042260200c190709103080400507601a050114403400070a50825640c1e003003151a51401c206038000e620a6850300c80c1c0f9603c101074182501e0f00540b552003594041c0840c0c1910703104410560710301003071001d0010740b070b40c010210200103000c4503804080607010148100040c158003089440c410b00034021065016 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84094057 1250 84092807 84092843
    0x10031506021c0203090310050903071727011704080906030c0406080a02070b04030e22061809050a0b070201110d0912020a0507050d0507180c0207270c0e03070807080705091302041e02070c03 83
    0x20741a40307440034009100145893f8405185000c2142c1240c0245101c07400c00c2010130100e0060341c0156101204100e01090800a095200c04003507030001c00d140c8150b06081a85c3d840b0520224081c01c010148035070300080c5400da80f07031030000da0a0048640c1c2c8104420614480780c500901d805d02030918004180702102c8918501e07809032100d00d5034000c005141c5e0803150340302e2010181b8050500c070115504c600103040c01c2420003000d443c1d03c91b2009400a20b00c1c50a15215000c04d140240a00543d0000c00c00d9038046803004c15201c1c02c03174001b61150510348045142c040c0c24910340742c000030724183e03000b4032403085000070382e000310120f00f007540031181d030300392200300440d01e4054807010628096910b0241c80c000340759540003a8080310490524140000700c8000007400c201c066009802c81d58032a04003000001d400b045a10300510b0700303442140c0303142081c0da0419640424203801901558440200c41d011400f1503042c20044a0306000842d00c424551038010018002c1c0c1c40182c8010010480f84008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84095307 1250 84094057 84094117
    0x915090f0a081b060705010c0f090801090c140607021305010e010b040807090b0402070b070225050603240901030f0b061e10031506021c02030903100509030717 70
    0x166900c0c20002c000310340d001c0b5003d200b140200b01805400403030070700140e00007540c00d003d2079000828039199013240f030b01c0268004010242960100500c0d0b170610303105501181c032040720074082e116a629000403d2041c0401f00d203540c41490030094004440c01c1c4280c90f40d0516a00c1103040c0c0310368800190469a030f683c8880b210b800b8a00543c0310b1500000c0b42049040c04650101c04c1c1684091b00140c203081a035141e0524100382121580f015800c0082c3c202d020208070040e184035542c501d8500d40302d260504010070030320f0100411000d0a0035a62050400d0301340b01c0b410040798000c00403c980c41540e1030f85880d01c0220702105d001c550508946012410b140f0b484070326030061030070110450f10086c252104201d401d464481a0300145941c8402c029401e800c02006d400240081c0d030020a43c1050701402045805044204041150402d01c08030b55103581c0894200c0d0008a40078001c901a01c03007094942c250b12a80c400103000b06404040d02e551000315801405000e50f06030740d07080c50203a4507040310b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84096557 1250 84095307 84095309
    0x706080604051501051801120c030506030c010228050f06010f06030606080708340e18010f170118110301180803010909030912050c100e0102210915090f0a 68
    0x40401e00c284030013403261002c06100300c04031b0414901810859154444001242c117000400070000785c5942c00c100f02400c1c204902d20341a4028030040c0000500100180c00c801c400c9084542d604044070f03043c0044c440104140e007041c0c8080780035502d09594030b0069030407136041889000003180c18a0070000f6103070b001e44821842142140c83c0c20101d03035540004680b21400c08400c0c4100141c10040080001d00703030198030b204a43c0107031100014080b41000304100700b045110080f903e10040300040c0172514242045d00121000942030702003401640240902514011005040604000d121901804180c6051200240c030030341c000c0040102881c084140b1181d0f0240217440250b00b04010007017074201d9032080008500929090602c03545a040d9682900d407440c1e800d403050b0b400b03203420054610742040301e841031402e203041100c0640b20180c0042e4031881c28200010030090001e000d101c51100980c11641444801402c83d200d030703030004041070f5858001c040b100707009113200040641c0c039092a0324014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84097807 1250 84096557 84096559
    0x5010f080607090e091908130f05100305071214040201141204020111010b0402040902040311030a052805030307020a03020c24030604060b03090102090301050c0a0807140c07060806040515 82
    0x4080e500344841300702d04280261070000c452044500312070001251406076441c0318840c1c3c8004e59142600c00000c1c03c0e80000350040113402165035020403880d80c4003401c881c0d21030400d04000c19140d13100d10060300d0705d22101c8070800d005400d004141400d17a41000041d40301d18400d0b06c0d0442c0d09007944003005e490303020300201d1004071107846010402560044c01d45980343c0c5001000440c4040b60380c004101070380c0050b0f0160020540120f0140b0030012104101c20403488141c00078403200c0305980390942d480400c92307118896005c074903d200038407131400101060b1054010044907600d04200d00000d650303034000c1c2340a0b401409180f150500500e081405001d8020a0807507851071014400711240c40d944c0081e05856006030741350000a0040440030146201c0c440704400141c41d040b120f0103260075120014000b5200d0399007080310000c05a04490f81d0f40c0c00000e9807030f1030388411240422074000c520400107a0340c881d2180c00f600142c0305620001e030a00c101d1058406004540700c0310f00c54126019828146 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84099057 1250 84097807 84097817
    0x20109120c0b19060b0c0303100803070b010e090709060b0703020c120706120e06010305030403060501050108010518070c05060907091401030f0308100b182103160807080c0105010f080607 82
    0x443d101d003000707140340ca03a80359103084001030b440d41c4e03462050f4003035100503004601c41e0804000c0166041d24440550020041c0307001031840d101c200c1d680c40c4840032050240100501400d0003040840c81304100c0140030302000c440800406482e98401c050306d03000701c5070840c014807845169841d9420300041d03040715103190324024001207080c800180c03240381c031110003040c42c03e07501d60385d010b558030003081054003c40c052800756903204d00b542020015540c0c16000305060000040040000c0d4485000305040030455030540403064590300000c1320902407540f80a0882e100710340034400c040601141000c1100c00c0007600f00700010000750b2030080b000e024400600142c450004141c0805d010700d031546d502c1840c108441784040d031140e1100a0940000d07030950061540c07900000701d642008900940d808242d14400c8400600c2e041840340c1d01c0c07003094450800580c88902c0c80f02040f140c0c01c03e441c20300358403510803a100c00003081014000c02e0f09110303070034000c0c180c50400204218040741840c0500e5a40d40d42c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84100307 1250 84099057 84099061
    0x41508060a0f090b0f060306090d02071703070210080114220207021206040620090307061d130f11070c0302040b0d0f0c05010201050105011d0f0a0302030a03020109120c0b 75
    0x11801c02495021492002aa11142d080d40000c0b20360040c0b901c980b40c55544d620050600f0400e061903c500140000341d03513071002c80d2000906400003203840071940060741d000a80c403000e600003030031801481002504200010642071281e034101410506171802210031500721130103082082000000d40b00907040c0c2e0303941c1040800322603145400030440340c1d0001d000810a008170424043c03400c00c0c12030303043d2017441d81c07684c900640c09001e003100c5803100302c10340c107043c148204000000e0b21156641b140700103218440e0221283d5180e00e10440390b0a50006140400d00d00d5481b501002800c6204c5041c0b81440c41d141d000302a100001d0241c8414a400404010503181190b080c440206000305045074010f00c110341c2d44000030400010100d04034802e50825403240d2034000068207450041e08258184203403101185002100c843c407142206204036000100702401d807000c81c001c641c2c40d40020b5094040c105041080c55015000816841e00c03c0000418110070b1803c00c071850507034001700501c03030303921000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 84101557 1250 84100307 84100321
    0x111f110a0e060d020f04120218011d0907080307050a121407110a090504050d0e0105030105151e0a05180a0b040501030c02121b101104170115030c0504150806 69
    0xf900c2c405914440041c078146002000e502140c119034031a24075540d0f1003a0110071070030000c00c8480310f20202d26021031154140b80141000915240010111825050000c1c4400c601000700d500109280d8090341c4d40c0e480c0030b04000e42c0b1a10340c00015101068008150307180d152103040a1380c0b82d0425404082c0c00c2120039541d12131411500724a4540c82040c0b00340201d0800220b115450080344108000c3c03075017240808002c0c0060030b0288900c1e05114003400108215100d82e110100150007034011540e603101d0602f9407903004010a01c2040482d400480c40031100c80c0c00600400700035008410100080d0504001c104010002c1e0140e005e0351030041c40100401c0d4082c2d0800104442e65005960078800e084510a400d5041034240780c0c203200321301c41c4810701e25409001c1c94203907001680d414400c80c03d4945550150740320318426450b8419980100d08410107081d84500c00602c10008103040b419606e041008000416004072480ba03480d04100402d410340c444140c8040701d080d0405032001d07a03107542d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 84102807 1250 84101557 84101569
    0x406080705130801110405090702060f0a0e0a0f030c0b1006020c040c03140c1b1203010303080414070b09211c0e040f0501060216081b01111f110a0e 65
    0x110080d00500034031440818141c101780180c0348680c0e2180c10494941d403a00007040b85440e0054010029904060709200e2806c10441003103500140005001c07400c0f601902080703191011a10300a01131003088018001019841080d1001650299015052640740c1040c102003004440c41b0f90f1000d60303c80c100900c1c076070900c0e81101003c81024180010200b210714400c0c00582001c0324615000c1c10001000400700d140c60888441007880103008040380b0040000790989844107010241c2402800340000d400c02004228a50f8810003035415030721a2650f944210788140c2100d01c1c0140b00c0c0c220a10800d0000c11080d03182700d01818844c00400300c1c0c0c82d40101c442000b0307100c4040b01041003038594002e803440e2a14041c42138900491400000d266250502c02800c0c00380c0400c0c0a0180c4207090350401031040d0000d1640a03503e8581440d4005c1401200165108110000c1001c841d004003a403909403081603c6030b00c00307912100d8400b44005201000703008054410240c009020070320507100c0303c034103041007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 84104057 1250 84102807 84102817
    0x4060f0e0a1a090a0e071401080406020d110a0c110603070c060b04061203080901060e010302030307110117090a0512190503090c0a0b0a1407080405060306010923150406080705 77
    0x740b010490703803075444404207074211011501e040000c1e40b0340780c400c4520402000003c00500d5400032101010f041d2500003400c4040291001c0d05440e008550400200c0f000c1c1c0c0040c402101c0301500c1540c980b45100082d083e0180701030240c6402c00b424005266904203802124401d03101d075541c01c003034014541d640300028600001542c0c0c002d556500081042190301d01d02c40c1900340252a00c0d9224038142850b01c0c20754510f6001890342071150b1004000584000090320b0380365138010960981029481c0048545600030f204019003038108200b8001607100108034032008600400030380790f40c03030500800c1d03100500c0f54562445980850b40322590f1000d110340013940d00080a01c3c1507030801100c000000d0500d8015800500305010700207114994246c11482d61041d00f0a5480c00c0c0f4101002070b10f07841090f0080e440350501601000000a030710740c0c42140c204000c0d203002900304000d900028000300c13a1103001a03005020b0400304074110181e25511045e10201e410942d1284020354507110700300e540e5004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 84105307 1250 84104057 84104081
    0x1061d0a060b030606070f0203030c030d0501080a0f0f06020d051014030d080601030c020a080a050901020610060807081e040804050f010201020301050306040f03020f100f0606051201061d0301140604060f0e0a 91
    0x80247c1a500680d0240020160001410002d54035590107600380e000300e5006901403d400d07404094201c000581c0c0007140810241c101041014602e8281401c6019108600141c2203161500301044100301c10b10451074165402828032002c24800a020f0540e2040c55948040104054000080256100303400070002441c030741c4182c914810030765480450355040b00d10701401085001ca11340043e540d0400803650b11031850050798100130720701440a40b00440180c241402c00008000050301c000d060318034000e24030300d6661036124034030309400d10142c50f0b001402901c0c0304125495408071a1744c0b05009a038142d03140103018066540300c0340e035a0241446109812400d41c01180130001041a041c4208503602200303107000b04036010400705600c00c07030700540c03c42c034113100e028000c5482020021003030754159800d03410b00c100000380c805198040e031040c0024055056092280754002c8814011026000f2a400e0300c0500c450358a031444007461100b1303801240e000340f210030000340450031150004e5074240e40c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 84106557 1250 84105307 84105323
    0x1312030e1002010207020d060506012a0308070c021e030105060103060503060a0b031609090506010603140714040f0f030b010e0412080703150e060907030506010f05130801061d0a060b03060607 84
    0x400c6e9010508060744e044050303901560718001c0005958100740003841042c041241440760044200440c03550602c0380c9405010000141c0000d081503006003104500140c0090286001d50310341e41c140d000007010f40002e50300035401d00022076201e500a001b10419280028040e006980d50365840200500706040c0c0954180302da01ea0310f018040b001e0002c613018206a110200c0c0e0090700b030a0003450040c040e0302c1541018076040750390a00380d4094141d190070441c40d2600700c40403648181104020f014039046008410389468000480d404880441c2040307034420010092141e0b40d800407400c0d40031003242c0260103281000c1901e10101e20030280f0b5075000c41a41400616800480d070100c82043e0540c01c407481d4034643c84c05000c1c1034540682400c1d440000c41c0303000d015600e80340000070b11021542c42000288940858032484080d00032040341d0291504400800c4001d80c3c4090116458004182d080000010b46010130604801030003440169801d000c1114515103821091290a034099801651241 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 84107807 1250 84106557 84106567
    0xc050d0b031203040b07080601050f09190302040c020c040f020903030415030204080a150e16170102040801240602010203101205030c060c13170a06020c0312040501021312030e10020102 81
    0x3218200550b00850003026407410706e103083d10001d401c852010704200d060042c1848030174400641c0c00e080b617900880130355110301e416480052800003040340d904025403103030078854001c008a50000b500e2562941c01c41d4284a05200c41d41180203d10034261901d400d43c10030002030001d0b84058075034100c0c0f207410340b6006203030668642c110782c201080d0703d0040350100d142e032034806020f40c81d40c02000922600400501429001c40141042402943c070914181600454001502d0303082981510001e0040b0fa00a0010782c1d020550081c01ca41760300300d40d241c1c560b0305490201d520781c414804d50b44030710b20180c898000141000c0b2a00070b414580070301140c0c64031040040c40c1c000007084c400c08ac0102c07265941c2e55150f01d2140d440c08500507068000000304580310181d01d01c1d000c7e000414071501908480700507520b1a6003c0c0e1241548a2041c00c1d06290030a1024017040146c15030003410781c10030060080001984901a00c00c4001c40c146010780000c0e003828900c119441c0000030103401c0aa1400014945 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 84109057 1250 84107807 84107833
    0x90c0a030e101b030c030b09041e0503030414070b030106050d020717070309170a020310051312050306041401061e0203090a120204050c03010302131505150304060608010c050d0b03 79
    0x41d802e61000032054400e0b0183d82c00050f40c05000b400001c0003241411b000d44507a04000c2880701d2030080002d000380003403000031030040306220300108002c0e820000b0f036a540c0c502401d0030118001d004000a12901c941180043c01e078880302d00f44ca060300c03000e82c0c5003458070004908032030280d084804156407218202035500341b00400c41006250161107903d903243c44920740303071440b5030110b003075a03c9800c6034004507841c4006035004607000c0c0b0318101e01c000005080d10341030444a4000ba030b19000400300903000200c6a031701ea0b0408040c620072902154148130700e003820030f004107100b0001e22900c80420011400c0d41ca1080c088002c202c7d481620348126030070440844001504842d86500403024114200404020340c01c250150f150300540d080340103869545903038049032410350941c0c004a119030386d03101c2d040035000d520b1280000500c4000c200041c00c003288a40707200a40d2041d10129411842c0400c00500da40c018081c5550580e0340c4d0b20b80a0810f20300000301c50240288400395035250044041380810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 84110307 1250 84109057 84109061
    0x30d0f0e0607110a0801022506020403060c08010e0601020a030f0e2803060e030a08070c061401091b03090309051005040b180909060f0412050d09050318090c0a030e10 73
    0xc0c06001e90449008458080c4004c1403da41c12030380960340100312204801400f10b42c203d043c3c240610401503581c1c65814030400178007907500020b05540c180a048640b00f90710100481c140c034143d011040054550b1401640d403041d640030000c1c049000720b03d00326100740c0201008a080030b000740060b0036000100411041030404800c21010320907100c01c05000f4003442c0d104103072913403076918011752916892007005840a000100003004003c500400b0104101c00c1e604100c54103554895920000d58546840c500500160940c12034240903020415841c20b109000303800380b4942645840c1100c60501081c840340700c0ca59406501880301c2044002104c03059034000740300030410060b0075143d00003d03a0400c05010310103000c00c086039003e0350920803003000e08040d6030740044e441459550320702e44005058485003e554004102586080c4520701401070200041505c21101c100d144c0744841c2c0c1004016222000b0355982c0e170421424000d0480c0d460103540302840ca01900750440300900059007884017 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 84111557 1250 84110307 84110317
    0x90c030312240617010e0609061206090714031606120608060103050a0203070b030c0d0207111008011403030a08060d020d0203070603060e010e0c0703030c1209060203040b090a02030d0f0e06 83
    0x180700c0c400708030403c8415444001484503001d0045034942071751402ca0101c1c80e80354081d00701407044102c00d020620715528421a0720700c81c2d00a60a44406142400039140c80d040716100304524004401c80c0d0b0b841929002c03031140c1d00c0c1f681d045401c441803428550110741d4032000f0340a01c47c410303640c1d02001c83d0308802008028001c1d44030f80c00a0081c4040386c8107240c180701c105e911480290f40305100b03000c000080e00301610600ca2018100580f1042c4a04007052800d1100750000c0c3c0101d20040710b00b40c103030f80c4030212506840310025018000403014050583d06e10a40d1352070030009041c0c42c0820701ca85404520b110b00d140c0020401803c03a034858000a05002c0d2035805000403036525802045802d841403100c41c0102103054440d020f92034401c2e00c00440b440750000c02010565030b459580b00c014000e030180d8142c1d003400c071410040208540b8040d002940300b40c0301a141a01c1c0396002800b000400100c1c1c400d8180e008d0041c0c04021600f1030140c5110f4554450003051000e4120100c01c29120070002d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 84112807 1250 84111557 84111611
    0x110d0501061508010e1513051611071406031008032701020601030201080f0403170a0c020c030c0a0e040305040503030313031b0302031b0f010e0a0213090c030312 71
    0x90451600c40c2c551079a0552040c2603080c82505001080404a04542c107070b4020f5034a003000d42c0b4a14202d00141c00070500c0c56101c0d0046103000c2c103210324801442e81250740d44081341c440300a110b010707207801c0e40c2d2481944110500082d0300c24003200c0304d0501102964002540c811441c1c00591252001429908070b03078004011035025500a00f004e502071803e116404500380050034841d4115000201080300060000c0495040351006c05c1c20540b113400c500300c041e6506a180121401c005030720300c01078140c80340102d0043c840c5a000700100c1c039001c62401c40c664030080c50040401d1801c406584900d6000b0011340c1030010a200002d9241c07010700c0214481e29040d00c6001541080f03140190110448a13070955030011980a841c1c0020b400008541c2e10010b5130300c82105042c20300808614100000c0b01c500304130350811141e81102400021400c028074401c480030024807d2880801c0100c0300f48c0314008e440c001e00800e040011a002e0a40c042d802c1e03179401c0c0d0119200074400b51100f0305041140d0b2803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 84114057 1250 84112807 84112811
    0xc041203030e07080d09230108130f05030319020301150c080c070e0132041d07080105040b0912040308090f06160606060e0306010e060105070c1e0501090b1204110d0501 74
    0x325040c5c1d60088480c40900088041c2c107620030307051100440d003201c4040c502c506101c030b120089020818218548016039911210303200710b21110745802a00e1f604160740520045004217a001c60010442c02034906892064181000f04a0b159000f01c03812500000c0980e051141040025405c403010310202015002e4002d0341000b41d4540404c1c8504201d1400c03440c0e5042003001c01d4001e181d0880301700c0c88203003001201c0210b00004c882c1400904c4092418903400765111303204000813915419084a84500d020f07840314660703992040b17412034450f400d00c4e0600130321080402c0103000203110031003c1c2c00600c0016141d0f101d82558007020545ca98041e03007501e81c60352442c0328070404000250060b08083c0061340b0300080010000400700f582d810042c061500002c881c0303030014a40c3c2c0d2044080d07a1641c0c1c0c001c280b81381800d60b20004450702013f148075544101300c481c907000c10594010b510680442c1e0b01180f010303142122030b071a120000c081c050411a80d0940c0a0460340480c0d40e8810051515401a000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 84115307 1250 84114057 84114073
    0x80f0f09100e1c0206091c1110120504030302040b0a030e06060307050d02060306060d05100807050109050d140a0c06090603060e060303041502031606060303170c041203030e0708 78
    0x80220038001c115914040003540c80c01a062911038400310711039401c00542e0280030040c07902c000390172800341d0514180c101c440003413410780300301c042c001615105000d4210039000040b02020f100c00d428152804030301150440212100119003a070203c8c0e4450f000b4a001820143c1710b070a500010340c00a191800040c0d2941d80c1140407140c14040280c002d20124000c01c80c4904e84008584680034500d4040d01c05c000201c0010b00e6a00e41d4400c507446074505a41c1040a80b40981c028408a5402d0180f8481c62149200200d91940180c02440070794030028007560f200c000d00e0766480801c3c81d04030505049402070210344000a20b008159601601e21600c910f01103a00300f50b0010121141d640c00440b0045003c41807107941d450200c1110145c43c10240d0b05103a02c050103a00341d14611420090b0000400340d2040c0c0402e003c26507002c001034901c690b4417042002e00065480301c030303100306484280c4c1c0194100010001d0130b85190350011607038842d0801140c0b0701c5401035507c0c1070081c9907001600360713002441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 84116557 1250 84115307 84115309
    0xf03080f090105010f050d02040b030703030305010e0109021e071a01090501060f030207080a1107030b040b060a080312060f01090b030a0609060503030705070e0a0207080307020c030f0106050306060904080f0f09 92
    0x15050340d01c4048034000300440d41c58500164a499814420030780034500c0f1100c04015512030741c11146407004013400702d4211655a20b00180108400d109456803525006e00208101e80c0c01e000305c034000d591440303010a10080203405031001c1d6010b1801195440701e82405039600c8461500c40324024030126a00086544c94920301800100390301c2c00d1002058810000d01000a40e030303900303984484810b072901c40d0800ca00030700d00b40c0ca00f80c201d400180800031500200400c000e40400801c0c07144100fa59440c0c0681e03a41d55103035980e4026407401103810803a80000840609245500c0142c001c01450042070181d0b46610082d40c81d1b0040e5880c080e15610b9400600175040c0328050a801030000743d00940c5420300079140c454445d50a40035880b0300701506004201800c06035011b444956030044003450b6241000080a580c0e582c1103502e5a00900813501ca00b08182c3c070600c5443c2c00c80c1d00240c09001d1a41d0b44004100700038030010000c5821550900c0303000000c1c81303e40b01500346400310200060356054114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 84117807 1250 84116557 84116581
    0x403032313020406060201111603030209060409150b0304030c060c031803020f010e03040b07110604090204080102030f0c0309151e010e0405212d0307050702040b040b0d0201050c0a0f0308 82
    0x1030840801d5a040408e800c15524850040f6900c0c1c1c0e080d1705241d11078001c20318084010f803180c0401c0a510080c003007008100072009070f02000200e210380040382c14441d0b842c0c0081c2c0b460301048801a02080c0309094240c00325290760480b02c0c103205980340008510071906901c0c1384180340385c2003e038016401140c1c1ca554112003481000000e43c5007800440c01c0030b02d008070a803030070b12804c400107211140d026103c1606071294815140036198400c4155121170300c1d580101c1c002d42046030454041c0750301ca1702289200e1903140441e402522030102815203c0305500d046080000042c041b9a40e5410000d00701610150b20505c1e00e002c0d1040f0181c000039418035041080c540740c107002d00140b204044240c0e915401034814120303030991700552480300c01c41c5031086420822040800300c0444040c0e00108001a10798041e0041c02414803c450030042c03200c10b5011700040f100c40d100d43c01e4204403900401d20141d130040c4e02801041110004482d8a0115651400e0880302c00710381c21808070720886c080c4a0014081c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 84119057 1250 84117807 84117809
    0x1090c031b052104080901200a0b071d0f060c1518100c12050702030c0a060b1302120f100314010207150b2412010806040201020f0d080403032313020406 67
    0x1003900f24079141001e031680f41040c03040c1001a810301a41d010b00c480200700004c009519211828165000c00b900c2d41062120903104a03001400108a107005403202c500410300c1c2c1c0c4031003001038604032104441c1c000b4803810750301040c440c6080d1305c0303210703144e00c014901007070300c0742c81100e0700000705407001c032413281c524580010b5034060f044250816102011141d84003584100d09600107070003042548406000740c1c150312469840d48514011007240c0428008182c00c0f13115107410555950b00380b44860720068003207009008800301c0406183d000f040c0800c414911250700001061a221401590796a40000144448143c1080c5c8c0c1d402140e4001480b9044140d94080407580105010219144001480404084586101c11150944403681981786401030718010011008018143c0d611052599030f601c2048070f003240140700c2d075100b603540c400000c6041d105038030003500c40c071141e5121650b0940240600501886025847d4001e811880c40382039a200c0c003504006015a40d4803080f80144070a603121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 84120307 1250 84119057 84119107
    0x210a020606010914060306042c06010602070605040e090708030403050106090f1a041a060a020705030706020114070e0112020d0212090d020c04020d0b040e0d0f0e0901090c031b05 78
    0x80110f040141103103080107109a030b031003100c4680d900e81c0d0740c9001070010031056179065860841c858000341c220046000b2004100c1e641011110340340e1342d80c02c0413a0380b05694025803000400510003040303000381d10501d05410803521070075944080d03140c0100c986035811550050390103a44481081100d036489100302c010f2014031981c14084800d44000d440720341c1d03490100a81c001c542d0303403420303040d904109005004242801000039a64200c45580250381e0b941d50b02425129016413600014144d0051052500304601105111056503030f40b01e090b80d11404031001141800a49421103450800324802448464011900161a04048048c1152208000380004816807102e404202d40e6030700011441c0b10882c0c11100940c0d900c3c0e511400e08090088500c94a40081c00e01d00030242000b008a4007202503c003540d80c40c2d0700100d01d010704a445000c03843d5001d030800719110040c41a40c1003900305140910203810046018107030141e00c8400d20ba10164994006000810b090800d0010007924001d1045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 84121557 1250 84120307 84120317
    0xb130b071701060212071202100f0608121305010c030e0603160e0109030b06060d020c0d03020309120a09361b0c080f07020d0515040b0610020a060509210a02060601 72
    0x16001d50345070040d200c6c07410050070f06d42c1c440788961103561082003010a0036504c190188030f03c1c50560640000b61034140581c44590144814244d41035800380d00752403030700035140c41c11040746203402c00555070107807400f80035010005074041800031503d03010000c0d400f48801c2c0150380b02c04155528020568922140854108006442c080010502100050307810500c21100b0a0b598100796003084000d104628080103180940c0541001864069020754410780031401510042d10401890041038865000311201003050504140409042400004032002429084d43d40a02c00003086014850b440d04040c2d55070354540344108c01c03002c0f40810900d03e040e45808c01c1001c02d8416940c000040c0200c020600c000903004c9040025543c0d045210038007183c00c542038030708c0b0b00c420170381034100c0d01400c440036140e640c0031102007035072400d000203410307800405136004c0d0103500c0f9103a40d04030103000094101c00d02403040301486110b0002c016100d403207280340183d0036559120b501c3c41c007904041e4020f1001781488 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 84122807 1250 84121557 84121573
    0x4050f0d120302160c08030405030c0604080613060b0d0615050d1707050c0a0605040e01050609030a0b100503150a0e060610050a03090605010603090605010b0c03070b130b0717010602 80
    0x40c1101c1a4801d01c00102d0070056242c07540e1034400c80790311083d5180034217105100c0300300094852020005001b0b486050702a200d042d02c0680502c000b500c00c61080c281d496000e54005a20004001c6010207550310400d00421404100b00000b0780c00c150143c0140c55131690741d95907441c040e41001c1c88400511040d58600900708540c0c40718000c2080204014501030b0000907980704002040c03002e0342c407081c001004020b50b642c96090042076904240107a0010010b0352001180b83d2404005a80c100349008000b480300c00c40360b0b0f69215000d0000740c481d01c0c274503500309004500d0756001e00c407004c2c0039820006c0010091414018540c00c0d00c1e0a90190041c0d5003003e41801407503210b20310008e14150b043c2c202280d440f2910b43c0120010b0108400140c070040c90840040fa005a05030800000319002d140103000f16602d4051191003445002c2058043d64000c110719000a0b0f00c0c0f00c203843d03000208410a01c01450503071128281c03140104c0c0c24400007980188801d550042c540c0c41c01e0b0140c0254030043c1614 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 84124057 1250 84122807 84122813
    0xb070f080c07030e0a090c02060f060301110a050d0e030c0c010806040b010207030f17040605040305160f05010c06150803091f0e010507060e010c030213080102130b030c12090304050f0d 81
    0x182c4110040682080b00d00040401035032940c0c4d40342e50041c22900020040084010b1000752030314000d9903080200c04070f003400301e030103841c05010341c0c8411809040c5039898002034020581c3c2c1a8006403a032101152100740d082c02c0710100380064071403452100050005000048001010715800900a502c80c0740b604d100c41e45280d03400a96501626804060300d24001801e041c61031079140f103900004d90301d14001601141141e8000b01400881340f0030f82c215120001c1c50682144030809a00501d003880d81d001c07404201561091103900000c50064a00107a26003240c94100041901600034074990352000803080528182001c1d102103409044050000c0c2c9a00c800000b40190b5a242e4824100301c0003294210a110155008070500080c0000030411403681c464098040d400c049202c05202400d2080016025030600888555050701d81d542d580041c1446001205600051b0a440480b03005101d0703051803441d40b82c40ca900601c1c0e808001c0d0744451a100420940014000c01c06004801c0741c0e8680b000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 84125307 1250 84124057 84124081
    0xa030f17011203030b120604032a05120901030209090103062f04050405190c09030b0117061915030b040204050c0406051b0f03040303090e0604050403090603020a05070b040b070f08 79
    0x40b03030303044c900461400780034800039000d001682000c8a26000d03080500c42010b0708092400303690030440c0100c40b41801842d0307900c0b80942030910054172940100c102c03010300c9620f840050030b204005050050a29440802007241031000343c008641c0c00780e0340e4018801c0049074012499845c00800a0f0b1601112589111081800382d4480d16000f542c460000c181e0062400482d17030f5038000305d02810080d06d103991100400c030042a21003550075941c070384004980c0c40c40f040d0341204074141c84002850301c1d4a420915041281860240f10b0314942da4108100504100d032243c0c2d030055004e4507411710141000d00401c02254006026070080600c200010050700303800c50181c806070644d10107901000601b040045003002030389d41b00c01805010002e004030400d03070405800c9003940e4000b10030b0100e41d80c6200c144001c4440942c1c024020601010040007124404d40080111004518045082c40401c2c1e6a8400c03405054070103d400603e80c13020072000c240d00400f0041591603d1410b643c56040c40551501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 84126557 1250 84125307 84125339
    0x12030a020309360a0b040509011d030903070509040c080313080106050f09060d0221100b0a05030606190e0703060603050609071b03020a020306040501020c06011410050a020109050a030f1701 83
    0x482c1012040003c50480040d0302040d80008040e06c18450b80c076051b03100358000d01034003c0c801c0f9032200c0140902011b401c00016145400d402074018002c4030706050405c80f824500420403031728640e40c41c90115046c182030028011481002e06004682802c007611282502c61a420072030040010444c4511b0a5a40d40c2030b450304103805440e80ca040084c24008203145a0308292070f64291030000b64450108440007440000c5240380c0320040204c000d41008111040c0240d02c903141d8164400c4e004903070b0b0b501d0100c2100c0288141112000120341e52107801c0d4030a100120f400c85c0119944e40e004005d03198250003003550105044401923a98a4104030162141c2c451580c0700030030362210403202e0100350081002141e103a4000b41200c0c0c85251519096013b0f520a80c580136103800b44400004960840031081200500000c040124502a4034400c58554111031490811507495000c09030105006001e0000002d0080c1d0300d0b03071100d03c10303054082c00b214100d0054016911a9000400052000c2c0e16008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 84127807 1250 84126557 84126649
    0x50405030a0c1e0809040e030c030a0503221101030c0f09090e01110d0222060e010f0e0d0605040501180305040b030603070308040e07020607030203040305090f12030a020309 76
    0x400340740072034203010303012600c0341041060039030700c1800c50000e1001c4d2802425503101c0441c1c06019803210031424075100e00a12910329002ea200f0b0140119a5001c0e50113194000c98108004911040004444001e204600801d68814441181099841d60b06014130a138290050504e01d5014414a02c0184082090710641660030350782c91500d084000300790001c0b0294040c00c003106454403140400e10000354002d0881c02c40c510500290a0441c0c03c500e0100000c03501c2c0c5480b482d00d1981914015540fa1903803680300c008020070104440c5e003c1d41c0300d040b5029481d0040800042c070b840e25150540c00c4440e0800c41c2081401d56040100000b64808216400c0c1c8030703004542d03600d0b41c03501c0340842d00d07010b8943c00c0100031000101e03001c83c2078522090191300c40c0b555503003140d496840b450b105604a10090320b001d40041c0c0100700b00145800d104c92081e00700310000d01040c1103050948035450039a0401c1d10f0b42030040e0000a219095440e000c215402450443c581c12104034903510100801038440718080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 84129057 1250 84127807 84127817
    0xc03030f1b250503130b0903070e0601080103140703020909010905070911040302062d0a030b060901120e0708010e030903011103090601260d0c061404021e03030c03130305060109050405030a 83
    0x1100c104602401a52548007102c0f40c0c86170200d07194001c0d00ca8540009000c00e010340f01d04000000c10720000c5012502412041e111065940d0070340d11041d4144a01d184894002c0c402c00d2000801612070001c2039100f02d04660001811a0f80c2e85000c030308000c019840501d000d03081081040c0040c50030b00c1150304407541240d0965480b80810849107580c28008000440d15030310801104c1c41d00c074140000d0104584035a010000c11648804000340c074001c0a000c00d000890b400b98144103040e0b01e60200e400300d80c00808540d0110303920380d201400c1d5400d602c2e2801d481d800205041060741424040e0542d07110840300c140c2d04500d40803d08079502d0b1414032039840ca0300c0c00d6566840d0062455492500c028a000080e1030940c001041c014010058810702240c0b1030380f400d12882c001c0028204841c0c082c0c2e40c01000e484803846035448112043da120f510b8103a05020811201d401d50504000400260a0b1108501401d0307145060040c1007001c1640001c0300141031004200000c0e5001c42140c148000718248 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 84130307 1250 84129057 84129127
    0x120106080f0a05010b040b0d1503110102070806011802090613090e1b06030f041704031a010503062514070507050a061107090c0917010e0c010309030503040b0c0c03030f1b 75
    0x1940c8c02a00b09071050a401603c11800032003804000c2d074050412190a80895030b81d161b403140890360300d01c001d1040320218040f0714440041250140c00411a444006040d42c1c10600e12580303986440034a1b80c8801703c920364400400c01009001e010030f46081030340644221043c00501e000c05d5092100070300c6c1641c0c85000034001020008003030032080d032018445003095121610792400018440c0c6d413031003072402c1c0c14042c40005070300c0c07500041d40c0b44100101c000d00f0120b51074501450701c14484400c3c09805000c1240321000d0f411410740040c01c0b4140c015801448800c1c60801407108491003501f1900400c40c00007000c0440000010300c0d04101c511504000410080b22803040b1500c0300c041d00f101c0281c51a0240700d00080a054004c01240c003001e03001d54079003140800054084a0031600010041071013807001401051043c041ca503440010101c1492030900048500e90840d4011a188200c0400b4a424051648610102c9041c5d00400b242c0c19031134000d6074185e110341c501d0580c0541400c4046510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 84131557 1250 84130307 84130327
    0xa09020706110403030201020a02060a1a04050907091815060b1206030a0b0f161803060b06130b0a0905010e06030a090f06020301060c1b03080a1202120106080f0a05010b040b 76
    0x2c416000003000c201400c2c2caa03078803490024042e44c00104484018440d4001007025240207208801d1134018804041a218400401784806481e005003282c0c2e01e402007038400a100c030b80c60302a1100300d162054422074440c10520701318029903000c030400c012283c91b0000a0184142c0803003100c4da020712850f00701071030395640301c006881d040f114440203140c202ca580c00e01c0710038001d9000365401201403684165980342440c2d01164440f01d552240f095812460f5010004103206922178a0140340242980345071109240450030280703404d0b0f01424640741c0000b541d070100750380020100084c20092030903164590380305c40003e00d90300000d004a8440d03a5129007907000c00821408240c009a130081c4195103d6030340f04405040c862207800c0580d05c07000084850740221840c594200143c84c1c6c0100741c181481c0e03400e9021240a03086007125003107a50708120480e2404003050101c2c1c001c1c026030307a405001d49019040502d03001006030421019500780001030004061080c291000e031016820b45946800c1549 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 84132807 1250 84131557 84131561
    0x30301170703120507050105070809100f060b041d0709050604030605062706010306120210081003050307060203070e0418030302032206060602060903031506071406071107050303090a09020706 84
    0x10740010070001503d24451074294201d80075000150040008001581e51480705603250350f01142d1084031600180308030500209198031460130041084030000d0180d48501c0360100d01d40c415040001003841c88020300f43d0420311581240e038400041d24211002c1e074a44004544140a01c1c00010b04240e110b0001030202e03180e48802d0220482d910b03c201443d150441941e040d0144245e030180c2c000f0381030540100d100d5040d03c2001c101d0310303800740202d400c4255115088802d00400780040c048480702c5000080071542c20809009894055000107039a401c1814001c0c01c5035a036000d000340100c0c02c01c1518080031101900c4c0c402640d406040241c0c1c1d80c2d07603804001c589540c52103520820740808080e0582804170a91160381554031036004c60700c894940810341552800f04952004040e424400542070310b00381100900080c600c640c075500c9640d0740f242441e508180044034000000b80c0c851001868040007000700900800d41034010314901301002c0085403400c1e406018620046030009403400c2000304035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 84134057 1250 84132807 84132809
    0x1b010c030b01080a0c080f09070302060c060601081003050307151b02070f050103020903120d090204020703020f2a0105070f0609080d0b0603010b250b010f0f080607020303011707 78
    0x20414141541005030003800741441c1c0a0020300780a0028420b89070604c1402042c0c001c94a03041c000c0d0380c5120390030011100051079004140644140000107840e46006084c42c101c0003005080c03d807506200060820000500740c000381d400440f401c00116038040202c41c40180c00c2803d120454040c02c00a0028180d6a4240c0b5054480c6176000c1c8104c90b80812100c4c26114040100d6a80300c0c3e6403001141a400303812500d036170540006110114443c81c02d80100000141a10045266100e40d000a0226004114240c01581004055108030b20040c0011040e0a0607401c01c0344100650540c019a00c281c00c81d2818180000002e2600074000c140403194588c90740148140402404d03482d1100140e00001d15000308941414503a110b50729211017540d0517114ad4107069401d05400004441468484202150700e4000c05c0000c140401c41c1d00e44a0b5001c0d03c0c00010b00060030380341ca10185c2d00101254007402039500001305101c142540401107a046071500e01e0380201d0340a031034010904103901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 84135307 1250 84134057 84134107
    0x4050c03031b0c0d02010e130902150d0c140405040e100603080909070c02090a050402040f0515011412010303080c1b0105101707030201050d020f030a051f03050c06 72
    0x40b803065103207542e0106103141c0d030200b00b09440c0d19200440510000300c00440c002408030b07c124a981c215030421180d010082c9558032008221980a6000f01d10385040311000c984490b2000214a08401524010080029290701d851042c4018454050880c1c3c0141c3c00380520998403114191180042000320a9510203088010422944d40b482c4c1075400358490451603010780904000640313020300402d0840401d40e0040d103890015030307403840d6103401050f0081049920950b82c030084211240e031885061301c2001d46038040f00e550001e0f80b00240a210405030a840d10820420401d41d851203080303040341c1165894144a034007911a04d00100c0507010b0000c0000d89801202d07019100b401054011500420746803000e40c60440d00e4195030600c600480041140d1039100f000308000551084006101405125000500f043c070010a4482070343d009039102080141c0380c5c000e001682509040200d407420840c00300603100f81ca107650326a01c0740c40c600340c0d0700c0c070a56010428043e52000f0301c04800c11450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 84136557 1250 84135307 84135313
    0x4021302040b120106020c010c08070b06010908011508071205100b04110a090501080c0a020d08090c030d0909110c1218090c0d050c03090c0609041104030c090c050301031101030504050c03 82
    0x180f05014801c3d621092240b2001840394441b25401ba5000f8040800388135041040031345080c05584650251080c0580303400e0402149503c001070008080c41158540f080c4190032040d50351420aa03546400722640289828030b15040c40b00c0c000440000700b800c10782e40440c001182e001c1290b000100100b9940c030343c01c20108000140224026440313840075043d03590903200d440094440154a44e180c1c09103a21220169001e04000201c460280035915402400c0c40100c85140d11303c00003103400d14003000881008903040c0035082c0010340141c000c0d001581d074512916400e0110b0642e6095988180c00c40c100349402c8002002e0505000075403c003402c0308000341c01d50541d410f01d64910702ca954841c20403034400c030b441c0070007064203060528200da000d5803070407004012240c20107041002c02da00030240503502540c1d880b4030100030303241100600011400780c10b100c260145000350038025244600200320800004000500014607410409004d060081c64001011340d02c0303180083c940300142c01e54a40c148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 84137807 1250 84136557 84136567
    0xb04060806010e0f131b0f0609090f0218061308030a0e010e0a030203070b161a010303110303040b0c031f03050d020d021b040510090218090105061204021302040b 71
    0x182000580c18100c400c081160101681c4860b40c6101c0700c1000e4030b005401500314202240454081c807541030b1b03900b0f0303040c1c801c00b6095500d5001c01007030115940101c0105018a004100444651203151000261220194a4911000c6440168503901c02c03c1901c40c94005c94000300c2d180507243c6050140c54180120b0360f40d614a4800585000780e420121800150034010340d9802d41402107207101143e40c0540103001440c10020f580b15150000600c1203020003a40360400d01244000d420183d6040031400703a02c2155046090003480c0d01c9da03081e15124581c0c001c009000c00140c1049405500c480b01c403047c507440740c44603c1035800c1480d0008041d40450074020300442400004502004024095002c40d5100c40c0001e500f640c42e01807100b6020488085800c0d059000d00301500300651080c1a40c18001c2100d441d90360706e90481c2c01201c0d02c6284540700714504559400c1034500680540011030b0ba00e400e0400e01220112103035402031000b4003c0098404016503d580354066801404103615001d480d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 84139057 1250 84137807 84137819
    0x7030c0e09160e040605070c0213020c0102070602040e04030207050306151905130c030e1f0b01180f050910050d03030905011b0503040b280209031c03050411010905010516060b0406 79
    0x21900584e000d50f01c480c90f2002291b40307103020b80035000d0641da01601500c000c0343d188107500000d41140c044410555020008000010b48500c0108084c01c890202640c007401c107810000e1604e695030700114020380c03144050140364550051003c100c542e044a0380c3e2503100001c00c009040c803110381d01c240d4016825441c1c60b440010581c000300314000c00c1c0d94080280d4101003040d40e542d070150003207598440044410528070182c0b190807105a07a00103040c001c0b001036011100400d401030301c3e031158410b103904100c01c0c0001c1c80d00607501a0851400741c180c0c02542d003007100181b07900b803504d40b0043c28996030744201c03c00c2250031f410600d485248405580c298004180e8060f0056004403005c81e603c82c28071000402c2d002020001e6140703e02c00000340940c007045200c6010081d8400f11a19500d440b0306080c016444980c0d291111210b095582c0108041c01c00c0d141240d064100c280400b81130101c007000604c0039984c0b10007503a80c03910a28564400d8040b050074080d00522614018541041c00c01b07202240c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 84140307 1250 84139057 84139079
    0x715020901030b0102070501090b161b030506060a03020109060804051e010b1228050102130611060a0b131d070305011407021207080c0309131b0207030c0e0916 70
    0xc094080e2418003020f542c540049894103120b00405010032001c50b07040c030140c1486c41c09401c040d07050000e84480301e01d15881e040440041d4282e07050781030b13101940c240208201480300070b82050b010345640d4826070555001034202c0c14180980e504201d4de20340042c0610004001c2000d40c0c002c1000c1146845001030302990207400209041d60284520002900400c940002d04c1011108100071040110600703c12001c462000d00d0820740d240c0d0b401b80702c1c1d21089051616a0030080509031291589410f48e9903030241070850091006140350315010f0000d8003901d0315000aa11810000c0300055054910290124140d00b0803040c840c562152401c08010004154003622948030720f01c44100840da20114200c1c0ea640d03114a103106c9280c001e0240c1c00008801d240586140c40f05030064900305400803021541d80422030f001c0c4804951103045240b52510700038480f68400070b1904c0685902825500c0700020841103110b08a03245c244d2000140b19004144030045041c036002802403001c0d43d4a218143e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 84141557 1250 84140307 84140317
    0x1080601021903180503061608060a03050607090302090a05091b010302070606031203060e160c02040612030c0606090e12032205030a02071202130e03040b3702150606071502 76
    0xc2c0d99220b0000c0744a107030018145129106803400c0038010510002308032007a900162204c0d800003180340002c0005001072251900c00c060315036503441d4051860042000782c0794090300000c00340d03107050144038110740082902c1403c204d5440c4815412414040100d0091080010140599140140120800c101103107580403a40310391350140811512005000580001034880f240a04160034140a101d030141a1031251103000600c0002c42e42c0d82c89501d801d024860342002c400103801c1207941000c06c05140b05900190022184c204080b6a01c5810b83c2e81d00c2101c1180d0360402d00000c000a051403502180100c43c4100079188002c240c8101d1610968036005914040d0150041031004102030011101c1700a24a40041110042ca103e50040400030924440b02e0035040c04200300c04210160301c54001e0500c101c840c40782c1c008a41141c1d8004940041103123980c400200c220010020541c0e0000d41c110012410070710080164658400044491040910042c10f5001f42e080c03a01d1480310781d5000d08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 84142807 1250 84141557 84141587
    0x90f0608060c04120f1a07030209031606120b15040308030703051b091207080f0307031b0807080313120305060306060307030203030f1309020d0b01022a01080601021903 74
    0x80e4281c840b03a0b103116141c01039005448a0fa01011202c60100b0029034035034014501810341034a0030020503004400f075a030b0499245010940000d1007800d030f4241000300c0e4134030300c500b500c2d01580e06080c05401003035980c1c014006da030740907103c001c01d100070f6427806000c00c01c8802c00c0820b10f54450380c80c0b8000d0300c0d0380c000710f901d40040b034500400181039409400001c03548101c4946964a0700000d5001c0014000c0708989480052107103844c0810381e0601003001d013030b05500101c01982c840425240040a60303614289550b5020800d205002c0081c1e800c40680e45416401607020344c4903034034080808076141e2041c03400f0f0010651000300d28138068050f806240541415415203000380c0c0c820090565494007840025015172040100e1500f0b40306032805001c0380c4950545201c40c5270344d20300d8000b003039030403503170030303910032942c2d50020b80c0d595a010018000c1c0882220108407074010601014803503040984245418002410006560340c3c1c401c1c4048070044092806002310000d070b90400400504a48804c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 84144057 1250 84142807 84142813
    0x18040209010801060e180f07030809040e0f030a3009060b101d0f03120c15011a031b070c03030e03030c030d0b061b060f0c0f0a0c0309090f0608 63
    0x304000c403040c020b140c02d03204288207000d400c0e103454008548007040300341460726a000d00e4000240752030061000c48c2c01940694000750716001c2080c2003004a48012103e2202a84400020603d80780e02000780d0704c0b4a03542c0d0521000500e04000300c200c00c0850013854003403030072101c0c5800d0401c4441e0740c40307503111501a060400c20803c04505001c084000c44201c1c2c00070071864200d158100f890809600c7c134850000d49030b004140104070203e0b207025000c500801561201042c00110344034104241658400d4103282c4480d294580080624103440b400c0054200b04400000a401d0a0044404d441d07508510000b8917a0b404080c24008074034500c0e03010490008995450a015501e000010f8649021101010754944034084240301d0060039140040d641002080c04501c8041c00030181c8900300744200f802800741803400c040101c0c0f040e2030050032401d13503c2d024040300b191086280150f0700a00d5a43c180a81a07142c0c5040030388031100c041d400300c001107003425019100400b42c2c1c0c20050481d0024012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 84145307 1250 84144057 84144059
    0xc01030b0102060f060303040803070f050d0c0b010b071b0314010b01050f0d050603010603050a0b0702010c05030709140301060801062706050f0607060933090c090908091804020901 79
    0x1141940d1408016500607403100003c1421045000e2a894108000608880c43e00d40d640c502c40341507411014050b00c0c2d810042e20740c182886810b0210f98160301e26445d10826100d010b5541d02d500c04010b00504035450f10102d1801c2c03c008280d01c00080018030b4071a03210780240e0300d16155204100008030078001d1f509012442d6a80c2d400303542943d100c1c4040c4145030b401e105c4c1d041c0107803000708802041c09a240d900d44400001080d02800041ca55a005500920080c035121101a094613005003c2c0c03410050100104410b060303001300386a065502c40c5404810304540c1000081c0901182c0e00410040d51030042d00144262100d40051010b01020a4012014410f1008030045520510503960010f191041021103881d02d4401001c1042c400c106c001030382040760b10b40590400822940d90340020f050400003016800b6521040318191800000380038900c555510780319a003480748102c0c0782c2c464940740108104102042a919400700280580001d07d84440380a9420403090303c05a001e00740d5040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 84146557 1250 84145307 84145309
    0xa0f08100c0504060309061b05031e01050303070228170c0901050a0605030712051e0609041109070e0d060209040b0105040303021b01050c0109031106160e270112050c 73
    0x148064200701d5102d00e82050301d4560180d0107045524403c032a42e40d0b5a000c00741c81c0818480c00311036030404555401d40c0302e02c0c04420030051401c141c1244030030043d041c001000980d034000700321116907605540b6911281c92001c45800d000c0320000c0c1c03040c03030012450408220390a200c4404401880340308100d800c0b0007039642c00c0c001d13580000c0c0a50341d0001418001402828000e000a40d000856450441e0380da1091940700000c80c0c40c107417680140c021140300700c554400d05008809400400488641c185400c0540e04d030f003d4441e9500342c8a0085200c6000111075902840c1e040d40c48050181c4455201032251400b08004d60050b84001c1c03246240c041388444a5100b0016142944da054009044a2444088814288104040d0346040000c10440c8141c007100030b002c1c0c407036514480d84914020200002205080090081005040104082010780415800b0b400490030078800c0c0d40411a103523280b05100e10315180c145004280c3c1032018000111401c18128880d210ba000d64190392010309104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 84147807 1250 84146557 84146561
    0x504050105040c050f0f0d031403070908120a0509040506040e100b0a120f1709060c030a120e0706120902040912021005010b1206040e100b01090806010501080f0c07020a0f0810 77
    0x848034642101c620041b13500300e400c2c150103209606000381032581ea41da0b4850303405455548201c40c80320019104500411184108000180000035403a64090804400c40801003190280303946a9108603210303c04103505465640c402d080e01d408442c00c0c0e800da08408003144015000bc4007007580601a42c00340080c805000f80940c03050168000e00240c080b00c15610341c200300c00c49040b071040003004c0401c14410342ea03640c4002410f20041039800786481d540402c0000c0d182409a04070804440d08103001c07981c00034000700b85403090390b506003410440c03a04103844100052200311002500300d440d1168503018024800601c0400c42c505600300d0309110312061489080c0c0380284a04c21160000340a04e840040601c980c4c40d6101e80c7c040d00c00030b9014050740c0614504004403001c1c01c0b04640d10310344040d031942d201c80d090700503250313110007810a9450000000e041d10002083c0c806010381c01c0e40801c500412400865920a400070401c584040d03c030014102c54000d01d200308841d6200780340b80404030107014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 84149057 1250 84147807 84147829
    0xa120c0c050c06160f1704030303050108010b0307080c01031e0e070e0a0b06030402011b0b0c0c0706050903070504021b07060306051003050907063203070f080c0d1503060504050105040c05 82
    0x71642c501c0e0291341030b51650a803d0403003c04440903040302c2007a50100d02103102510041d406a0b502107890b500d041409821203001c815460b000e500a001c0c14400d0120024a6044510342880c00050304c0d0046180984500131750b9000082450800010341645000081c8034410344120b1080f004035030302c44550007000c960030902c40d613420401c20b000040156005a030060140728030041d40700790b06207282d65905d18420003229220000c040c041059450a0790070040700b03014207064180580340040d40c4c2d000a9840145128243c400c41e0005030540290a0300c00c4504d10403410301d403c44a0007070719990040c010301410302629003d101c0c00c2c041d10b00c505200340201e902980710000500303402d13420f00710700712a910240c850310300c10340c202000340e220001e2220b04c1e01040c0c0c4124811480d124100410010440410712144c6c0c1c042100c8407040c00300100652040340c86c1a580808001111b07948007441c42410300303d42c1c0c009040c4605d054108400d0000c10b42107039115502c1060041241601e6404000c054142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 84150307 1250 84149057 84149077
    0x60305070906090b0711030f06010f0503030702030619060308120405061506070f06020910081806011d0603120403030806130203010609030602090d050106080d030c02030a050304080a120c0c050c06 86
    0x25510f010042c0510032401822414000d94482c40c1030b039038030400b00f898047c44210001f0603600240040100801549505000e03101c01c6002d50b1800c50b4540020f580c0d010041c06858004540301841030720303a0000d900040085502c004150b88500940d0b00c40040040301b181c041c1d600d0700500c40050740416881000d94031014004200c01c5c00c2845540b111006030061800c1150166401c00c20822143c1e5500b44c4800203040980e10121540303041c001d000b505089500f01050030b6444403006010020000d650340510310064070650b141d507504d24001034075207440d036202000b18a02c0014040301345580800514072448084d6000c07203208040041d001c1c120301c002d00c074200002da0441c2d82440042c01540040c10100c100130034040395010961616802c4903d50350000c0010b52007100c0700d04110703800d80900700702d080b5240055402e200034a0700207011840000c00042210100143c00c07a20f180c095014904001c25201d000c101d1060007642c0903214000da11003d842d14895443d0891030791401c2d2046440b00c0703103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 84151557 1250 84150307 84150317
    0x303050108210901090302040f02070309120507061404091109010305150121020715050f0c0405010e0f010215240603010807060c020d05030f1201060305060f01080c0c0303010b04060305070906 84
    0x1152500103000b40c0003c0f242d1070401c4100c03480040942d0360341c01a001c0b80d81103100c0069586e04289005041c2c00781c2507000248617446d890010010480206080c0d0881700a4104004c0c08009459540e05c01c0c030480d04114085840c2c0800c680c1501c1c650000380120241c00c4e28104400d4503a24401103088000154a03400101c3d030350030009083c1e10960310080341907000301006d4100640c0d50f44240b4071902d00760311810f40303035981e404000c5c40f90340307481c010b9400c0720880f04100c3c034090810000920380e8030318089160240f80d80200104290341f0812512002110100e0550788508200010004160302c400d40328403140928454a40300d8542081100c1c100c0d000c1500800f00180741800644002e042e602040c2c2e4801546201000410400d1000b0203101c40b002050030717615141002c903c81c0c0340700103030010000c161a04040020700d848081920b00c02c01c0007401c2501c0e0350340d100c2c801e8000c0f620a141c03001d9164000440009a80c070507000c0504182c8146450134041a03651400403a2264440c0c449d40c00054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 84152807 1250 84151557 84151603
    0x270e0f10020901020f010e0f01050c070c05061c05090607020c030d020705090702030f0703180e06010206070c1b03030909050a1104121106040e18010b031b0a120f0303050108 76
    0x140e203540280b000a2042c01514080c01e0b005c03110318211805220040740d650001c0c1e401e141154028410b890b030110014820030f0a01e24241c9a0320558515805018026200060591650b40c0c030411402c4980384800c0c000d0100b49400001039854410070b48800d0058450b410481410b86004200c10303003449525402041e805180c10100540a10301504000a601042012084030240b20000f800f01e18040e0b1a0803483c0c08101039210364225640d0310280b02d1182c40c0c001c3c801140e9000c40c0d25504481c09162008c288803080c10706075440c9091038850304502072882d0300001010f07000101d0108580d001c04041049668014900080c0c3d4020200d44030042401c101c188030b1a02d28450901782d0030b014a1000c2d9241c6014804640750340d00a800001d079004008080000c16500c811140d0305c070040680080c0700010b00741c4046a074460329002d400340704490440703000e4910f0b03c0700410003005040f000034220b01ca2809050542c0644a0f049050300020308040020a14031400031324503103248041c0f5042c58010b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 84154057 1250 84152807 84152833
    0x172802031c1802090108160807150302070303110d140a021e03180712060c0e061b0c04022a0607090315022b0b030a021302070c270e0f 59
    0x40c01400c1802e00503001d5441c0c8840941c843c070515601a20443d002011900d415401d0030407058081d51006065038480b200c28880380554031000c110145650501588600301440c0c00e80242046082524903024042070f417042506042d001210f2090641c550740e0901e8488040d080305900c1002c9031000101c91031080301c40000e800800960340212922540c26a040205144504290490b4020022142c1580d100700c148030091143e016811624140038020700c140e400415001d0044080198401c417603020350301902401806001d1100c2c3c0001c20442da42c41c0460038044602d113031088010701003c492450f407101080c000a180c1e02426040d115001518507660728911404800c201038100e0640034441c0d0741102841211050311498141c4880c1d01034020041d405040303498490203d4804c3e40300c142103201684810b0003420720f8816024002d030f074030001420142c0c1800d1070ba901c03114404200310840e910826032510181e141c40d02e103400901041c604200500c0e50f40800d890380e0000340c0c010041d03285803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 84155307 1250 84154057 84154061
    0x131208030f090a0501060305010b21150a0209030601030510060f0b030a050403030e010905070509160c14010e030d02040e010911030610270311010309050a0609172802031c 75
    0x1001503240b04982c402c84050380c40a0a45d9070325481100c02e0f07074503007072000d0750351518004a02c1c2101100f562910015503d1514507907800e2952426080c0c0051080481e001c044203404403103541801a04992480d42e40345005a514800c401841100500d482004245000c80711780520449603000710060440e03c400f010f1000401e00948101c00303069581902101000c001e0081d44801030150002c0c081c41440c140c2400301c062001044061800459202181c885822156180e50307a83c0100c0107007113503100c501c8668014850028803024621000c20924100385d4150024000d98030212440c0846903602d1417800b0540c2c0c40b0f4002d1610807a002e1000801d1401c1200d0404950303041417400e441c8200f148030f600c0c428044661100d41c0aa09003c03014414030443d001e4130403a50200307180400c84443e41d41c0b51507031141c800440043c1025119498a000e00030809000f1884040418451341d55800d0302035409001018a0304e090100040203588452150001c4291542c3c0f00b528020b034010b040240000d500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 84156557 1250 84155307 84155311
    0x81b0108041203061a0304020907030c0c140703060e210a080a05130803010618080f06011707080706050c16050f040b0102010e01051302031506030304030314090d08131208030f 77
    0x2c1099079500000540e000240401c42110001080b55696400c190050000254000305030405042c01e00f000c1c3e0051640c0f04104d07041d10768200b8001c14087d003000300b000c0d0030045140e0016180700d043c040c610260880110b06c500c40224071a13070303075100d80c400d0003610001405082e080c103011503200301c0041d6810b40742e904581e5100405482d220909442d50f9190303039060b0400e0300b000000400c101c0554641c07412a0301c00380c01411410ac010f001d0681040c070740d159104814010501a00a50000d5070b408032020001700c0081d0281100350f80006031a080c0041c032a4104006c144214813500004004030380c01d0804d00003e5520103896002031800501c1400090268882070030b045641c0da4402c210395910a100e001e0146d1140103003d0812101c81c01090b2414520501d0b01d00600c820341b00344041c035940041154222030b81410541c400f88180304503130030035016414031103400a68942d07116080244d01001410510301c01c800c1c0360300d59920342007071602c2d03810031b580000d010304c00c10008107501c0032040030785503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 84157807 1250 84156557 84156593
    0x8060d021305040b0709050a0b0901050f070606031a0708241210090b0903030c12060a0b030703050a061a040b030606131211010807020c0d0212010e07081b010804 71
    0x4080384030341e9421201101c0d0101c800391a1100401c0c18003082c1640150224001c013004c4494450f507030304140807410103108140300c00b41030010004070314158086480c207a403401341e000f000800105a5a06103004001e40e082c18004404001c02c00180c44107008440c114000e01e84030303080d100e402050b405245070b1007952491080c1c0c0720240c0d64807502108010000c4400d101e00d50407012419201d14600030811160140403491103400600420001d81052004e071504002a9001115141c4031680801c3c0c45801a402800300c082c0000304100301241c16030016170103503c6505040081c00d81d035020f813055041023050718003040402048200070009030907001c0c0d500701c18020581c625200c200244c0c885a00c4040d80060854505480e080c0705000328003101851142d030a0800c07400700d10f8440c00c000d4540406020880c4100e003c0c150a5040d07403205100400759041d040020071100c2c0d0700c040b6048c0c0c0c03004140704158403032188a040d003000d0080c0300311081c01e199060711442c00c1e030f44595980b2611081096040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 84159057 1250 84157807 84157819
    0x90c03092a0f0b090a0806010e040b0a091403120a050907092c0f0c0f010509040903020a0206032703210c07080d1a0d05030301060507030201090b0f011707030308060d02 74
    0x320352003400b000d441d0700400740741070420380c0c8010003801e100d0351042c26800350581c0d4024000400001000782c950680c41948550940c05070380d40c2810000c018a540d91014004415140403450380100000080642960481036a00710355200345000c1d040c0c8408841105140d0000002004540303401d420150b00c02591924080781541c6a1424441c80032004880100755405113140c002645004e02c481403101d01d050b503030000814007080018003544500300000c0d0085170345000078400d052080c004281a582c1c0180003507528101600d42103200c240040303070800d0030f0006035003144501030000200c0e034400f86110142120b20310501602706204200400e1160540700801401e400138001c1001058030307040c4030700000b45a1001d8903192504100341602a030107040c200c2400c00c0801c5c0c000054a044130068644269030b03603441d2408a0141040d580001d040c28243d1084c00300765007a00301d940341030342c03d138082c00940c03440f074000250360b80c0005100c0900031441120104415040646003030034100c2c009800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 84160307 1250 84159057 84159059
    0x30b04030e100e060a0509040903050417010605010818011e022101031e03170106020303190e0a060b0303040e01093222050f0c01020607031103010b031f0906090c03092a 74
    0x8c074050b141c1c0a036084001850008050110402654030400030b54100b000800c40709042c0310001e88501c00103030040d4911389502c1070031800084250450002c10401c0080300350340710307409030781c440280d04640f0303880d0a02d240302440040d405400050090490f84c01103080d02c843c0050f030408a4140d5110703c010307020020001602d482103030008a07410b0003803000303600a654901c1c04104e2182d03000e05940e041034016040440c200c80070000001c651603030341d411030000260280c0d2034001924501c100c2d4468501d04112000000e07402145034040b00307040c00082038907040d03213408000e0f180c41d140c00d810b00c0252100c0490082180b000d50341c2c10101101c0e2040c4e02800b401056a1541482c0840c003441d582d0280c0d01c44010802c2e02e503414482240c00a215040511018024105581c0180414082c0490082c400300019030a52120503c44004895242c4440807071511801e05001030083c5015004000b400c020705041110302c030b40300c0e001c4550b4010304810050381d0f02c0e042616540f042100240310900010034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 84161557 1250 84160307 84160309
    0x5030309030304120801030f06050711010903030b030c0607021c1a040609050c0603090307031b1b0f051801030b04030c060510061404031e0302030c010501030b04030e100e060a0509 79
    0x8600032030403032000303686038038040c40c2000c008156105483c0400000704010030028a03d144002d0400d5400000071400341d64415003254054681741c80d84d00d40b5801c05c02c032501030580551100c181c400741a000d0310884064941032046070300c281e800094110442d003880389144a0224401100180b0400c034200d4171446c1121542e06202c41a1829906155105c8640c02088410001024410341c160703506801c52071b140741029201e0240704005018012112440c20002805220190245510070b00d080d03890a03081c410300404c5551805242d00307801c1d11401c003254601c2c2c41000a5901a40c2500a030880d82c02c598582d0b550401c058000c900384000f0089105c005441800b8091003256403010701e0380b1700751a00304000e01e1032941070500401440100003e102080300700440102008030890418910495494100d1651080420f855115442e10002004005045000500450207039a0b40d55021840c0c0040000c1200440d40200100300d001d001d4040500740480030384464103183c1001070409020702c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 84162807 1250 84161557 84161563
    0xf050d030519090503150702060a0216120f080702010203060a061d041b09090510050d17070305030628060f0905040614010f020f0d0e0d14060402100c030806060c01020705 75
    0x20030b0180c00308036080001c1c003207801c0c100208195a0300520002103141001400a07444281c0030b4004c0c4006500041c20344015200c01c00b58070207059100d141c4c00c0301c0f00d82504005151845045101d40014995400300308014414000d6074000d042c0201014541ca24283c002d480d90a07000700c040c6014001c2c42e00040740c0e40d035144100c1c4030003216180b10035402d100c41b0000502890f80d1344c00902d00799207800103000388010255440c405a032070944100340c0344003060510460342d400c20170b494090f8000000d43c160800d54040041c500481095038404100540c001448501454420600c8036074081a18204030592050084040c0d114490400600d941e441d08007160039602e4540000e401241e4101e000103403035a01440361411180c0398405800e42d905044100b42c0c0f0b4448004030141007103900041c00c0c0e000e50b502e203960400c1c1644803807030b81140086d04803011340328041200c059200c3c1c82c031000042070a5001d0303a84030f0b00b106d6043e03690058a9485504201e065084040ca8644030740d421711401002400030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 84164057 1250 84162807 84162847
    0x4050d08040c2d05060406080a05070c0203060702030d060b04050603070f03060f0603060f05040908030c030601210c1808030904050c0403060203040525060815030a0606120209100f050d0305 83
    0x1000c000003d111030310a0301c1260802d944404e005050800c020403440e80e0003413442c0e41107842c4442c08545611006811030f4000071a00c0065451b00401c020300002c00e800000810584456150900400d5070700c0120089502941c41080d401c90820000140b0f01c2e44104102d030b03440140d0b0300b0001081911180070300c0c0414032a40090340030a6813407100784030511580010303a0081c08100c4092000b80c0c3d80b41c2d01e00d049800041d0072001043e10102c04285c0a038010164048221080d0141303100007030086d81c200d405000390200c1030001c90107464415080d40c080e03040380b0060f01c041c0c000075851701d00305000303210050400800240500341c0a11011000030100d0005500480c0983d00420401081c060182040700b2a40003074410b0540700d060801c41c2c181c0003503025600001d5007082541c003211290100b8103100322500000d082e03500d0a10f000c1740c03180d12081e507421a03e0098402c45140d07580e4030441c2d20109120702400300c0406c882041004185003550034003054900c00e281003401c3c00140e02c072400300c484c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 84165307 1250 84164057 84164099
    0x60f0904092108150a1e1a0a11150711030405120607090618090c110f0f010b0109080615010212041202010e03160b160215030604060e04050d08040c 65
    0x8052242d42c01d1544580042d0704504500160200303820840c000494458162103040f005410030110400c0100d99490050010300e15a00380300c003400102100001c007544002d030208042008049050014107000890b55561120010300d8509a22200b40039285407205202010b141c0c0320411002c50992a1400c030050f40c81800d02c0101098104440301400f40364581d013051040014880c02c0080354070308510110210f40007884006410340c03040508a849070080e9400d48450f02c07502418044550002494050510070500200030b904415401100e10030751798814900f1340c0d4002e0000c01c10300103803100b08409182d8140100d42012035061641c400da500a6841a5002015855002c040d0350300b0120000c0790100c01c034058003201010400d42c08c142c0c1110700802d8004440440d480c16640d00c05110248115001031072424800d1402c85480305d070750f00490350035009504002c000207800f0701c140b100e54012640f002c068003898500c900c0403102040020000e0b0380d43d0100b40c0c40002c184a0b00a920400007078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 84166557 1250 84165307 84165353
    0x1080a050a1e14010806041a06120307110a0519150201090203100606021e062a0d0203041a0903030c0304020d02040c0806031c090611010b03010213080708010209060f090409 76
    0x43c102242081c028141d00c51202a00158100710000d00b610504035401411200180301a4440001141184011440034103041c400000c04d4001d01c080708400101c60074007180d4013004d95456000340320310074602e0b003010a00e00305100020f114003c1441820680c000281c030001419419a40004c0d1822809410035520113a40d41001c3c441580c0c18405440940002c0040e000d0107005025482c0d5903c000401006804904461440a0070314030a121031200c401c00150b141c035860500d2403080294070035542115580071b01202188000d40c809003a0744201c049001840c01c44d0383d00390700360301d01ea88003c01c1280d002180240400060369207204041d150683c543d907000451502c81c0034503180800354686140b90310305820310500c030035900ca07444c40c00356503070b0703280800010290b01c04a5000d414004e00b1954554004681103800c080405100303070440f06030300d048402560342c61902600700e20410182ca60011020031050111540f060001d16104502a00001d203582da2038458107050400c542c0240b411036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 84167807 1250 84166557 84166571
    0x501210203041a0414060a0203060f0d05070801060807060206060f010801030201120e0601030305030f240d06020d0e0c030d0c0317060616050c030d020601211b0305030406110c01080a050a1e 83
    0xa8020801b0341ea2003e1020811895400c0c88000103441d23280003120382d8460a00c03da0050108401031110000a1000b88001d10030315844075030881c0c50300940d0140030700601c20840007441c1490003802000a40c08103840f0f0342030b00c0c0d09540046454a03050414884525284ea2140d0b03102c40c1c1c100001c034001c6000759241c0c1c0c0c5038208000000010f2002801507403511a11924001403180da440c80fa0816001c200d0301281e0b2214140381c41806406440d402102c00c81c83c1015941101e080800d580035800ba0440030b940d18200b0000c402c0d651612480406000a80081c458030034007042902c03415040080100311a00300f01107100942c0313203411480400c5884e030b085040318001d41d00701003000740c681a40900280800f98108841d41c54000c0d20010818682000c0b060311006102c0810740d42000c1c07090382202000070540342e0800369542da009105000000f84006441c5003022030110b140d05207480160340d400140d446e20051030002d0704c0b01a0002c0e640b2a5105c80c0c0e909503041001d12030341140340081003c9595 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 84169057 1250 84167807 84167843
    0x2408070e060904050c0121020301032012030a0302090109050907091a0f03041104060e16020618100e010b030304061107051c030c05070b031e010501210203041a04 71
    0x3020240441e40914203074402d100c0081c00108140b030340d00f8820321f80010b450300030024200600d8904001d01030801d10020002c4180219072600c1410030901c4c101d1400030100120a01654441c0340c607402c60250001d101240069100307400038441684140340c8a2982511440080d002c68029500d4401198942d8410004520041420360088141e00c201d142400d04194a920207840000c000400750f10b15084d02c4a100d40c0e85900c0030300900b40828540c412490050100f01d0701c51554018400035100d0781e00051000c107461203140d0318100003000a8040408101e0100c0043c00000c00144095500c6074200d803101e807010005440200010769a000f8100302c0c0d96040303410225950403507405290440303484410510400c80c4944034940c503141c0440010882e0400c14141009a0042000b400300003081c00644081406840c010040b24401004141d0f6510010b46400c2d1107040c044441d07115154200c56a4911a8041c50380035000d04140008072480400190500b9402c0302c048a80564021140c680 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 84170307 1250 84169057 84169079
    0x3060f01020f1018051204030302160f0302010e03071502030d290d060b0402040b0901200c010c050c0301050c0c070807050604050405060112091101030b031f240807 72
    0x16000081c00501440d00d010015583c0301d804494542c10801d44130000c1c0382142c003040c18580e203501c0c2c00c007041d40c2ca0100d22891064030ba511a1006800510031341d02e441e01c211a0382c4a117441141c50209414180300d03d135500644401c05c80f8100315525019104000681d0300b009611184800b00d5507011f50740d590480e10054040361605088203090605c428030050020184900c0c00b1a00303103044840800b001c080d460160043c00e20240c940c0d8010b4000b00d00000e25a40039405400000001d8807807040d51114822000f0103120300d00824120303640500c4040c10708d5402500340d203030f20074060390075540b4001d6101c01080c02d640d4242c4800b0f2810340c001409003070f8103105000840242c1f0280001c0c10100f45418009442e0f80200d000385403282e55100c0c00709070143c0c0030f00d11580006504002c24048410b803401c1c000300f50701c824001640400c0c280703d81800706107004079807600e01803c1c01010b2444040c034120b9440040214400000c4c100d008007204090600c400c0b5941e01c02403440d90021b20b48075003040303c40380d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 84171557 1250 84170307 84170329
    0x2090a0306150603020c101104080a08040611060411090a060e010305030c01050108070f0b1612030b0901050303091813020312040305070b03011d10050d200909150c0f0307050306 78
    0x1c201441071004c031801c090040b98008104601c41c01c0403503d500f142c2e400c0640c501ca140d0213203408bc4200d0384070504005910b0b003d0000c64415480e07141040300d00d100d0042d100c2108030b600521100c04070342414000e00d40b5207107540d000042a40001080340c0c40c0c0c120280345400a8200b80d450394000310b40710f002400c090082901400851000e4507960307190034290382204005004014542d10f011840a1070a0140205409429008402d001041d246100e0140003048040071190192080000110751801c00000310b515181004c2d003000a14060f1292680f02620050141c050004000340b811016940401002c1901c030001c5600c03954075440c5140c01c500d4110641d0141e5880c40052004010100c5135286c01b5958000c01c1606040695a00c0d180d000302d00050f0304a998041c048081100a00c00155104110451403488841d0030080000130082c10b81d1088a0003c200d43c440300c10030b001c800807420803640083c042c100c002e0500d004050b03610a55002152345400080300402002014500081915 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 84172663 1106 84171557 84171569
    0x120f0203070f120b031203060d0501061d06010201060b0301030818040606020708010b06070b221509060b0111060c0c0a02130c12060e011401020102090a030615 70
    0x15105102c907410b0325000440454545089480e80e1081140d1004000d008044510035041d01042540c07000340401c2e0017104070150000003130703024001c00c4082d04500344255411101603100342c600f0f000003810b480c110780c1020700c204008240801102d042d41d030071000f19555551201e2792041c0003000704040c50382140c9081c50000300941c3c040b448100f0340781020002d1100c601140d04000d114007503140040c042c5900000032070140d201042028680468414100c000b0404a80b03e00025a00c9000200070440e2500303140400c004491081113550002402d01814540c0704013005551101e0041500941880003d540802003800b000f03140030080d402040408109602040311002c1d00000c16168082901d0043d801c3c0c000b24680505000e0f90203021154845078a04584c04211052002410341555400c0149034156210740150a010314045c03040880c120b000c0140202890f00c0701e5000b6 = true := by decide +kernel

theorem cover : BRFrame.Cov 83992807 84172663 := by
  have h0 := BRFrame.cov_init 83992807
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83992807 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83992807 ≤ n) (h2 : n < 84172663) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
