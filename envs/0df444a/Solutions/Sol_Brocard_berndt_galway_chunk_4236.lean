-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:58:12.853481+00:00
-- url     : https://prove2.me/submissions/aa9bc1c6-0db3-4db5-a839-d57fd40ae8e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 761690647 ≤ n < 761870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 761691897 1250 761690647 761690651
    0x60308040f051f0f0e1305040c030b071701231503161e1d101706030102040515070204061710140603030405040e120a111b06030c160501 60
    0x105061400c1c684034020381c1c034211031420840d0b140c80000f40d00d4141c0115988002401c29912500f0b49004848a03001000010300078521031040c1614401119411907081d40c0c0c2c0500c28004006022001d000e4039041040e0745080b400e11400b8800741a0840d0301840381d4100046080300707402c400c02842d07001204400004089030a80c0c460760101e05126001610712201000051141308c40b00350281207110700c0d10000741a003030b503805803004044d540300e4404c0100b01e1f04880c00050075410b540c2c0d5242000e000040e00d45900a60f40f42c00b002081e10382d0002003000e4040e038070403c0305000a5441c501d41d074201e000340300916079442c00c9a00c08680030b000281d12017902e01ca050310080262400100e00c12001024042c002c1000c0108008410511501550215016082000107111a04040e08010b00004030b000441c2c07040e0204509030042c0742d0100d00c86400140c80b140f8068000e0b0800d010b4100c0d0441c104601094420642d000500d0502c0041c0c200031901000040c50701c42c4c40381d10340303242065580200007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 761693147 1250 761691897 761691899
    0xc0f050904060905340f0302090301060f080a030201060e040c031502090402030109023a0f06030f053d0c020a0515071206030528080315131e050a06030804 68
    0x440c040c0d9030044c1054200ca174650002e4004804140010940e5980d580d5170b035031030140100c003040c0c0c02588044c501036015521080085041c000005400000b411242c0c0102240340450134028211140b0350440b650000c0740703009001c0840d09040544040c4c130303008424141c2c0e440c054410707080244501c00d00303642c0203030010000007114421030f405401151120b20304102010300002d01c5180700c01e0785c0801c203e1071526082110b29801500e078002d00111201c4600050041d03225200c3d24680404c0103402c07100f643c00080000500254082142444d440080c040307043c0100d19145001d070102034400b444c1c001665210054800c920810031041c00d02d410500351806030f4810011b10305502c8045880780c020550210328003144114a2091100301ea403c400a0500700c2000c580f03110401c1c00c1e4810040641050049407408241581c0045000b824002c40d0050b0910740d180a00c9a00d4003052a4080105d00c0c2c01c2c1625004949280c405c0b1007601d038a05d0004460381c0d8031001a00402580d0409011090b003c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 761694397 1250 761693147 761693161
    0x3020f070b01150306060305070206151207030c090b03030408060408070c150810050a0612090c031506180b030a02010e011107092c070603180209090a12030c0f050904060905 76
    0xc00141c3d80038581d60500119072900e50035000e9400039104000107900071000074811100d041820b50b041800100118441060742c00301c249440d009801c103030340480300c030304e0308004c0c441c0c03a8810600203040540c041c0d410189083e4109032141c000400c060810240040e2450411540f086480003400541c2d4206814160200b0002c3c0051011035040e100d004000201185c01d16000c2040c5040300c00344d5507591103015401da280006801c2c229412121760100c0d030310110009850001d024070305008014001404c510307002c02040b000c00c0308485c44018030f28100c2101405e840114594034080e80a0030101e140500f141f0040380c0d07010142c11000103a002c1c444000c100708055410a00a00a180d411340d0411819079100000c00140180c1c1c01405038441c050410819000b83c000742d14001da51164240c2400581d0042082808100d4942c0603582061400e0404c11040030160003081002c1d140030864040d00060181840068050b0801404400f00b440b25181e0341e29000301000d0940a401400039086c281 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 761695647 1250 761694397 761694419
    0x60a0e0a0306020a11060711030406210c02162309090c060307020a061a06040e1f030303020d0c080609070516060e06042f040c0e2d0a050901050103020f070b01 70
    0x50307440751072030186c100800c4a19120b900060b45035080070b005140303040d10704001526410035640081c500d0240380d02046000c0340c44d900c1105900001031b00074019440300503510240c500c24640105841c03030522101000392500070700c8da0350b841d601c0649040103c1d444d1030020354036203102c215030b1a501c00c1000007000700213540411540c1036140704100520015843c1a5074510b1860f15080c520382010781480100440020700500c103401c800c00c155020b2144031182003409030722a0540041d030101303800048080b8102000d100e071514042e60f501e8084070314109000040e10010020344624200440410141c03000c500051145024644c84241002000640603009032290b034215026924003440403d03c0c0d0782ca40800301b40c003c0800315000030150b481c1003c4100f20081c2440c1001c40100241210400166100d840007c8442c00d481d0b40c0381c40354134030101440381d404c0021103000350042c06010402c2001c3d440d81d40d41903041d90070908016807203492508459042c2d000c2e0b0800601501c40c40000050124419 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 761696897 1250 761695647 761695667
    0xf060c0a1b031206141315080a20010206040c0302090c1b07050301110705071a0f030901150515040b0304060e0a120305060105030915060a090c1d0a05060a0e0a0306020a 74
    0x140c2c042c0801341c0c1d0303041e6010356030702503100942c3c126564002800030001658040029011b59050740c0d85107a031100c01840c80c1c87c3d4584000c868100c940000c1d980140c5682c4030003e40c004c0248010701c15890030740d0724104440c0031484001c2c002c590f04000f00303140a60500648618503110001d6028480405106a60b0340c43c040c841c01d0701951904074440a80c0301e10804441c1c1d0681c00500404415290158100e010040007200e0201e0383e0090140c0300404540354015402040b40f0400070610481e070007006c8416290b0b41e804144200008031130a0035140c001d0013030380c08607510440c070241c4130790700c9040c00c030090003010354100c03058001c40301e1190030069040e041484250003542c1c108000e580707610054540348410b54032000d0790b5121504038000c80100e866801d90009010700782905555445800b14241c2d0700701c804034008030702d000307018049900000115020134001168031445440c98503000c1002c0340300e100982d000304204204101c109884031b2031280001c5500c1003046541d41c04c0840028820310300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 761698147 1250 761696897 761696927
    0x10f0c2717010b040b0d2414070c0c0501020d0210110408030c03040f05040b0a0302060a121d150c04060807090b030705030403110703170d150f06020607020f060c0a1b03 74
    0x1317007581e820b0440c205642e40090362907101c030407404031360303101c214808000200c1d01044a99030344581e4288155840204514003800103500c8000350b4140600e13052005543c950002030440d0b00441030400c050b030380010b40038000584000c0001305007041507000a00b51091360064042840002920765542600000034000c940c210544104540e0f10f880c10401a42c504060b0130307034012058101440585041c00c0108213000c00b40c01c0204042c680d1301100c0b0162046a0905080b40f900c9806100c07840d0001c0c07100194906c01ca1a0000d000c2c138218900742094000e5000320030070410160000342d0090f000d004613101900039540d110384c07245001c903801060b5600440e01140003460341003501601040011724141a2503100700326036071b009411818030300303290000309001000b540c0b030b4000701c1c1c0c40c400d58000e07603400b41501d6010002c003541803901c080d1501304064070320070456021002032802c0140c0480c149400c2980b4114450769450344c4c03101260521100368461800c40c00740d01c4600d041580211110400340d40b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 761699397 1250 761698147 761698151
    0xc161d0f0c0403060b061611040b0d05070e100305060a020a0905030d2109060603080306030111040e04240c0f120b031209031c02060405010f0c2717010b04 68
    0x590142046031401041e10380d00d5441505000600c0011220740005249120244c04075040003880c1c4200d415040c9140c41c1038030068a91411b42855091900940c08801c000350342d240c60940b225550b0b2650341c0c0385841039200d40f64a090124800e650b842e03494900554204003241c80c1424084481c10096204100207070200d00c0e04500080c01d803d006c201d003040850340791185010451400500c1c811000c1c010101c8203060742c0c2c2e00c00080092002d10401c3c02075406140070540703a2801d07034181401c4a410f91050701403a00280002c219519180c000c142d40554820310051000c40d6400c0054a60401c0c08c040c441072506160314150300f039a00202c1020098180d51b42d1600450041c11644100e0b00d00140d02032b0907130400e6a4131202c20801c5001000e1044025045404d4041201d109000205007110000c0042e00041c0030320050200034080c0c80103035241d141041106245900c4007811106a0305006211440c117914102e128410403881c1070700030401806040f05505c0b441c44281d00038155586007a12440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 761700647 1250 761699397 761699401
    0x50412060c0e100503040b15030304060215010506120a091109040b040c06140f0f0c15041709130b04090c060e12010c050919050a0306060504200f0c161d 67
    0x8030b06a400d0406100ca580c81d000d00e1606c60351550030745141e00608580b90f041c1100d85102580d20100001d00c000c044540c042c040048030141e44118248060307011a124100502c503024280107540b11442e04400c40c2580060101820300d4189402c9540981d2264031200d6841000180500181c13030740d100c0e51040c00382c1c030303002504e40c0310544134039440d054509560082405400000000d03030004041002501d000d29051006508529140a03200c404214803004800c060204000b00c10a03030a104d03511f402521814504000301040401400b4188503d1550b1680c0c44407403241c80e0b503407200813401d4100f621041380c143c03950005040404c100314420b0087c142c0c040c09031644038041c40f6030a4241342c680d66040c681001e40d402c101d040000307075070903442c2c03050380706070020342592034030080c5000758420800481c0d2107150404000888000c2c6d0038030160300090009120500c0b4441c0304607503030b019801100c1030700e81c40511541031030703c400b0300d000c0754041d82002c002082030418411256080c07007040801c04455 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 761701897 1250 761700647 761700649
    0x30c020a030b22031d0105070602180316030203030910030b120c011d030a1b0819031407052109090c070b011e0e0403050903061806011d0c030403050412060c0e 70
    0x207440b0f940d400f80c00560321a00002c2400d000c2d000e0310054440501d031450500215490f00402c0740e0044070300240307420740d1040105650805002c610b8428a800340e03184201c0380765170080717501e0384502441e2a200e03154003040c05c10180c4c025482182840700203001100c40038038184c050f81c3d1f185520790000340811030060300142c603055031060401012201030050b06072012a0313039840a45028504150401032007081c40403031105000c11400c00b60b40a4420b000100300c0f4a400c0240468182041c1818819010800e000c0402c600040f1502840c20081c84000400704000c00c284550040d1040181d002c10100c080c480008000c01c041d26000b8080c4c10b0161641c2da070350003140d1012012200b0044a504a41400c2000d003000e02c00c03196000e40241480c918150140d0700003820b09070101c500c12550141c040f02c03258660002c201c00b501425014866180c1c14100480c03000c14944001c006084488001002074105231007442079070000d21007080d46840004662078810042d1640188410010348462424086 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 761703147 1250 761701897 761701951
    0x10906052e1202180a050f0f010b09093319081c090e07020f1c090306020c100501030c031a0f130311070f080f010903020d0c030c020a030b 61
    0x1421480040c0c0402003842d02c0010303001c400241409036031003441013480042c1207000c3c0c0c445500c00c040051000a0307528060740b2400030404007520452512054a0041c01199203020031542d02c071b90115017840c4540e407134040c0803081020711501c1c21904480c0c020700384500d0300f6841030580d83c840300f00c40310301103503010030a003202c002c00d40d2280d00c001d41d2140e0030003c2810242c007028180ea0446140c454039032a190910155410000d40314840140e003d003808425015042c825098640740d24924072000c01060000141800041e01020341041c2e8005000410b09004000051f02e4a0822000f80b0036527940f801c0c681c0d541889848143d59541100c1d480600c5540c41a400c0d6205250b07030091302041c1c0d11aa040114a41442c000c120140190003c011586150420001005001e20003940a040d07040880881c244231505000228a030b051080d9a400649c011594400c1360380c07640741c0700c41200300905003140c24854607540a504074408200202c144444941da40d4401e0310142042c4100e40403035001c482e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 761704397 1250 761703147 761703211
    0x10c091202060913090c03030f18061e020109050706030507140909040b0c071505060a060309150c121e06150e130b090a02070209090a08070803071101090605 69
    0xd07029900700003e10300341c6401940344064100700032000401594980e294001400b081d0419004500740c020402c65440e8005c1440038008c0c40108070440c03042c41d0a00c0a800070448004040791803079500c8007021158401d500c040b880301c6c0c003c070840b440c003a0b813800003500400c81502d0240010700c6890b8900e40200d0740314200c3d5840400609040096500c60300d40a8072003501401d0090321103400c011080c04200f06035040b8036480c150400000c4c0c1c90a00c0000c0103020070341a03102d02c0502d0300302129100030a012402600e4024540d07035011803d41d6003072500300c1c1c0720080c0c0f22954407014905200d1200844050940050400e0104000c03c0082c0d204c0700d484403c1307840b10340421f001807032000c0120000d00344140001001214650082255030480c07000a104010468800d03d07195404120074095103842004150040d180c20040c00c0d0911480d00d45030500d1003070800103048e4038000008079036441d00c00c2034024880c070301844c0200a42841c40c645a0003511b81500c091017280c2201e80070070003520303000640003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 761705647 1250 761704397 761704399
    0x302191d191d091f1404110901080111071506031e0302070608010506090d03020304050303040b0310050111030a1b0b0c073c0c0504020c03040602240402010e0d060c02010c091202 78
    0x3802c00030003c2c041d4000013050700800641741c84191305610340c2e811002450049205036801c00480c0c801380144030311048141d1020b2380d140c2c18402683e00c401075260844042c140c01c29107180b0134080d00f540c2400030300255440105a48600612128207445480381264843c2c40b950a4038202d690301e0f07030102c41d869428041c2543c0000d041041001034505500d14140817442401502d003469903500000e811500700e9071001031002c400004102c145036001001d04003500e42400c20f5030304d030030340c0c3c3d107404d036030707402450b41c2c05083c0324030010520750400009400b6003801d64042018000c0c3d181080c1c0085040d0880e1a04840b000e00b240d0b210a03007050149c2810241b1450b0150065000040b4200c0020b0f07200351001c20346000d0425080030070542c9450000340848920750b00299036840c0390160013407510b03040c0755640c80300c01142c170b210f4130b8403803008100741390002c2d02460303d0500c2d2285200050242030aa640007045a0b140132111035001744c064200c9018001300d52598034007190341d142c0300010b1a03640c038402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 761706897 1250 761705647 761705653
    0x609060105150a09030501241508040305070507080a12183b0c04031401020906030402040e01020c010903090503071707060302030c0d020d1b0302191d191d09 69
    0x3500342d02d905400505044841c80c0303862055559a600c4031402c551100782102c02046449121055403190300c0c2e4094010400c0130070840c3e60f4401ca0100425080001d00024100a40040c07050305010041204802502c5111306581d210299403400100d15181d1403480400701d00351004843d90b945c6a10b0045080f20241c0480c0101000c0c45406030805801d0301100c401e00c007104031b41004141200c0307416107101d51038492107590369605500b800b00030480c910003204820fa00401c85802d4a840d00410385e50002e5043d1000701c0d6800b0380c0c3c00400e000e40540c2e034082c400d40d8a4501e8910900d6440340c00c2d5000c4840c280c080c1d4840503199405e000340c0540c10354a024241d03205a03400c1005901c80d600a580c8030306c080c00360605011039030803000240c1e804003664203203490301c4032204d07120b050700d03029071007201c11860030b04506d4900440ca40f8098403410103004001d00400603840038140c42c010301800c9040030024100b0200008440d5128030650b014040d601400100e902d15079801055056001d00a01f000001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 761708147 1250 761706897 761706919
    0x3160303050a021213141f0216060c0e1003140f0402010e180406060626060316030b0a0606020a0305041406091305060f031f02031b030f090609060105 66
    0x42034001e4240600400040c60f82040703903403483c0b180e804405001d803074100c44020180780340d0b06110001306882d582c80d0303d8580040c1960303c2d0714070920940e20300100502e00f01584919400e03088010b002c45000c000341c18a814480703222421644030200f4903084600b01d03115095002c00a100724101c50910341c100030078510b233401041d606900c040c14558007071310524003007051880c01c40220308100c0f1030a40c2c642c40104198140401c024840c02004003034281c51070083e9900680c5c0241707550340a90308002d0300100500788040b41c9951002d2020304030355051004290071a603604c0c80d140e14000011183d08050600e07110010070301500c08101050000c1c3c155032528101400c0c800108401c026100d0b10710f900900402c2202c042e071b240e0492030144502a00e400040c189402d00501ca2080c4601000a200c1e800c013803052882c3c030b4091642c500054180307160058882c0d44103142013900f00c1a035910a080c0c44400700800c0242040c0c0c0b00828810a88201556820385031a1a00ba1742d4007028082c8681c40018040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 761709397 1250 761708147 761708153
    0x60513061d04090b0702061303050405100908030c0c040b060a0806100e090720120f0a110f0601051003050f0a1e060305160e0411010e030307050d05070c080316 70
    0x210035120004198500c16841901e034000b600b22a060002103a200c400300040041c3c0540601a040c1d112100038a000048100760360002c0c0380d48214007071184036103552007680307000c10b200e04c2c05500645255030440e0780d21001511501d80e01c65028a5982c840c1d41840c00281e120b00b0400b007034820040c0161940d0702e003501e81c030b0b08200542000d001440104000c140d0035400e5503440f40c02c058010001516406c8210b840f80b02540c11000d84501d559010b540700d440070b007100059442c100d90920840d11130031602d402c0300700411596410060306c841c00500c01e50142e03200d010310128200b07040f100c0489040e00d2034a11480107034196032045504413920700030f07040050151074a0740c0000c1980c0f0000c07240e0040600718070407071344200d60b6141c005841c26030100e001d100d11a401c080300c5c000544002081c420041c5400d075145c1c080000c03400340035410032210f09040c50503034608005660700140d10405843c0c03031040d2448000c00c150403910007507610007188800020000004021540540c1e48050040c900c00d0b1961 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 761710647 1250 761709397 761709407
    0x9010306021b030703091d070e36010e06010804110415050409060509010b010c0b04290a0b01080106030209010c0605190f0b0306100806180106150503040c06051306 72
    0x1409640811954040b00060200620040c00803e1080c0c5030103201c281015131010784482c0d503508805800403182e09000141b034005105418042086403070714942504000c02e243c08404044980b4441488611080f40da82507100540b410303510034500c00911540e801f03004480d42c030000c0d10301904d100856507074040c49081c42d410100e072074180c00c1840156651780d0404a02112405081a07030351a64407018408414030a01032190b42036403d1805001c40d2140d41c41780300440070003420080c407246405600248a003003802c0d2280405a0950460703d892920320403000150030010700d22400981460b00109000d802031007601c0300340c1d80c180d6618411a81964511004140203448a01140c0c2c95090520340300c010390088074862142c1c1040820320060100074540340c12005081d801040031840401e1014074400542c95502000c29202d40c45141444038801e40100b03d0350704102030013010a01d0005440303400c20025030049105007010300206644500441e1280901102c02504005104040200c02c0c415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 761711897 1250 761710647 761710657
    0x3702062503140c1305032406040603120503040303060b0f2205060d0609200a050f0c07030c0312020a030917030906031303090e040f020423040c051e0901030602 70
    0x1d0900060740141a450311070b250108031900d82590f400052460a2140d94003052001001c01368020302e11114241c400000058003003036000d0b00a003080c0006006551107401481c02180c00c0b01c038a1205000c2444000d005030f04c21142600402d06200000416059010072103404030114104c490400411810044040c2c2036000300250740205154007091307a503260310051229558a180001e0160303c0c040740c140c2603480300381d500809131941c1d03c4041c00f101c100504441d5040054038096584400c0b2142c403280c45c3c02060282c540c284501c000120410120044100c182c0e401585161030990480400303c0e07481150b00c400a00052000c2005c00c284541290300441d80301000080d00d080c851a800402c0381500120359400d12144000b6000c01130542112103480076000c403105889452030262151010344019400c0280240d513a21000c46544042503800159032415290454450030503080080110400e4058030303109014062050022801805003410070344c0d800b9181c2c050b90380c0380d620380200941003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 761713147 1250 761711897 761711971
    0x9030304080c0a050609031e090307090c02070f09020901090b0a1e11100c08010515030105091009021605011104260a05060f10060905091308370206 65
    0x1407012a500050410320a45c0c2c456580c0500035a01c4a5440003240c81d035039038002c010030000700c042101c13242d0398070081000c0302503941d10200451104d4003242c049241c0b80403544800c54045c0854000716081c881074009010090303090341c0b40e0404a45508a40d803251044000c2503011038010300240000c03400407415030902d51464107024048030211400303c0c0c20132205003c0c1c407001329075030320303143c030b5219040700b03055002d4501035034521181c2071580d0007440584010302071148200440000103041010040b0000085c014114081d500c072602c00e81084683c0300c0190003103409500301004103100200420070b541c02c8814000110892a2411050818039070710604403149500901582c1c2c0042003080210340e0290306020780662a07441c05140c0c000625071682c21103010011031400c1042540e84100c0110b4010582e8542c02d41c84503094901f000c003612403520705a0b00c0802e60307030551140211000102c2c0d0b0341d420422580e41e00c0d80360118202d8550004550000340c241c0c284007640f0f14081c20306450b542500d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 761714397 1250 761713147 761713153
    0x103020f0717041215060806061e040207060c02160e130f050c0402220501030501030b07050a0c021f0e030105040f08070c1d01082401151b14070e09030304080c 70
    0x2440d0a200380010366040c0302901d05e0002810700144041192098100924140c0b0262000b4240000020620342544010819150419031444190fa5072641150785140d4000b100f040040300c08007005e9103d82145644568440f41c110340040c291803002c3c0050b22507002000c81e41800d4810703039284d03e1004001c0308107503954801c81411240e251581d20080887c800d00920000a40340325202d0003440c000305422050405080c1001000090410107126402c440c40c1d0500586804408104407030108039003201a601800e845610b192024006214808014142c1d88600c7d0302c000d040140350a03601c0980300148211582c60202001c529000d0161072903c2c0300300c1c080000d89a0b0ba6002d01c5400303902c10000e90044015000401400c1d10130080d641081f0440410341e46c0200c01d0402c0c940d210801481036206c400745048400b2003007072290f002800e4811021001c0500c1d9101c0c0d0070b1000c3c2c08400390000452502c5282d401154403083c8c01c440314400c0c086280213500d540c1e141e41e249409900120040d500d144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 761715647 1250 761714397 761714399
    0x16150e01300f0204170d0507030e0d05010606050301140a0b0d05071209030305062704021011010e1006210f0f1e0c0611030405040903021c050c0c0103020f071704 71
    0x1c916000346440b80074002c1e0003503100ea00342007580d1405801d442903600207a021200492040750007034103943c244c68150514141d40301c20f00e03010071505c280e03415000389a5441c160000c144e03a504440a181601c1580700b0501014690b00140200365134240107805a005040c0312114116009800c100d42c001c5291809800e02c21502c04030343d0640d0f500950480109484204001d80e900740300400c0340c6254143c400750400070803643d80101d5440000340020f8000c0b004c0d400341401d2140140c0c4078071090a0f10000810204500541050315200b82d5440440d40301d007400c6e000122801d092140c0401000842e0081a0000066483c80380746c99440c5811541c040c284041000414429a00c2c48003480c405141c590a003815071400d4502c01040c1c2d00700a0611824402805c605800082038078160b403400d0781c0001e41070b44603003010391802c0c180711034050070410109152103640da4004040e2407007032000011221131420440055040c2e0040140403501c040040c050b40d000310300c3c50103420b2556501c20441900d02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 761716897 1250 761715647 761715737
    0x20108190612051f060e040212120a110706030203010b03180a020d240216020f0f0306090a031205070e19030206042d030209131416150e01 61
    0x31400e00001550b558000c400d0602d907201c0c2c1c41c2d0036000c2c10342d080a005c0041d1404c01007070100c0300802510103401202445148600303000104900c02d10104140e18030754440b00d03050320040078682c0440ca80c4000d80103100b00042c14601034001c1c5c1e03040c0e81540072202d080d550703280d505100442c451840c03036001d4414000c1b9140507031100204103c0407409401001c0c01101e2a49903600a0b41b01b0140c5d804141c4d104000700c0b0700040e00c50a11310b4405030304440c0f807d03110700038100040b0b0b80510460b0855040c0a5079017800350220001030b00044081c46600c07141903104009844208a0303208a80031310104011a0240311580f50131001d0000fa522003480071070a10340c482d0040384542e00b0a403c481c0c14043ca242d5550461018503c0320080310b1050a20180010700b10340c08240252005440004101c00e038140140c100401c80e409401981c20503c1210303070b000f0703030030b1000b00207100f40d44154110034013400c01c41911288500542c2c2410031068481d480090f00c0f08522070020000ea94070440b407031080214201c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 761718147 1250 761716897 761716919
    0x231b060a091e0b19030c02160b07110910050102060906130b040317010612062111030f03070503090f120c010f1209060903020609060f01140f120a11030304030201081906 74
    0x100d0a10101942c0004d401d030940a03048031703815110307207065500101884c8441c5120202035801d8440150700349032500c4607880c0ca21066401c0d80030642c1c1c0070201504000c61040360f06110700480c0c000b42c2c02c0350003903281c5001198483c8026a1030390000755180242c030000c1190030007010381041c0f1070314002c00706e02c82c03580003107220340c0c0c0a03040351000503440b01d2074440c0080b8502444c4040e040c1554580d200a201c100d00c40600a01204000c4c500310302003c114a0954060081803000781070102601e640318042c1c07509d180c03258401018944504590400c0c00c01608001c034040241000140003004003841c10030054038042081c0e01c00000304074400242a00280c40c0e030184101311486080041444591850040e007032410050492006a01480402507018522500581125188282c5101503840380000ca4885503618454035002280d101500c080c4031070005105580c0e5002d120480780c4481c100c800c258176480b81e4031001e40020443c0e03022402c40c4451b010790700e2120000700d0000507a50b03960300d45585 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 761719397 1250 761718147 761718157
    0x80708070308090d092702040503032d090f0f040e0f0f060c0f07110303120f150a12030e120610030302010b0a0b1204231b060a091e0b 59
    0x20005500b00c0601403030000410444940407100d050035040c1604000c1c112a210000e11100140d40f44580f4030b505420b00c20380d0454000d000040c1c2034035665800142000201c00e601c0e443c54031400c0e00f0802d00c500c010300070000c0d00e6440300c000302004102005a41042041c603039030384600d54000c3d42d0b81d68030304d01a1001c01507400c0d070811a5019194808c0803044490902c0001440440d41800030030424000c040381000f21101598003c0360b03040100e032032102192840c0214001001d100c1a180c080c00105010381503840d214000b02414025210003000c24040000a5403044200d0300c60000c40d64400a809a010080604e0020b04081015058021210300e0204243c500094070140d00d2000d0003416428000d460320080250380d25040c052601c0318885580c4034aa080400030b0b02d0385e41c04141041380440b0200700a0b144140030801b9204182c00341d80d01c4071680c6540d1011408402c02c001c039103080030b10075030b00c00c4a0b060b00c40441c1d96141c400311220400c0305c1c2c0a04142d4900b4088041003502c0c641c40505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761720647 1250 761719397 761719403
    0xd06110301060c0212150705132610090305031308070602160b10030506010b0304030528260c03090f01021801030e4308061608041a0408070807 63
    0x4000c0c450fa00510089220700c8a140c030072a000801c403d4174203046070318240d801a0040ca081503843c0f00c031b02a080f0640d03000d500018003180521218440c0039a0b4100d50304200e4500394161942c0001280c507107000c90385c2c1303a400140400c2051000950010a610600019034011343c1c406140c01c1090786c400d0203d074811102001c0a540d0303602d9850901c416400342507402208100d803015a142580c4441d0313a991b1051103044000c0700c0000c0001c0c10180300d50140d40000e030b0072884402640c180003c00a002c80303e05083c03013002490007992421212110300e0b4000c0b409100000d81a200c0d01c0304964669a90300082281415104071402030383c01080910003021120301c400001c6601c6080c030b000040988049001450f0903034801d0300e1840306d40c80d005850741503960105225003d1800030460684402180700c0b0003402820700c2500c00200074502040143c030482c0d003005020044000000181c0c1d181314165406000741170490341414103001e4505001c0d4110707006d1490070f030a141c05542c81c205185c1c0105030403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761721897 1250 761720647 761720657
    0x10e0414010e1b19090b07080f130806070905030609010605011b0212070e10120308151c030206040b1b0703110102130b070c06030c02030a031d0609150a090305090d0611030106 77
    0x113000c0382c035400100e034006007251020452500c88a0385a182160258502038003402e01e0000c2c80c0d0305401540105071001300030860a40b08140341401c0040c0441d25544034150081c064040001c44a01c4184110401d0342c10503122090030202d544003900001030300d040e040b0782107a42c00c80100c034881c03802c104800060800039403001c2c0e949000394114402000507030100b40c46040c507100c0c0900082d000300030035a04c8500b0140f690110340d103d40010b194845403488811001100d026414185580420381d80e00c01d500903140481d203500d60120585241c010b0002c0c2c0d084401c02803045400080c82401400000804140058200854650401080311086d070103038518460010f00b2008209010041c440140120300381048660025500a52680b149681002c20550303210000041e02c40000b000c0e48200d80000201c408a26045079034a5541c140d0f2184c1c103001d00580000201d51a009014002500342d0540c1c030315040003000c80c140690038151140840750130352980d001240a01403040514000d00d103542d9a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761723147 1250 761721897 761721937
    0x2901080a03120516120b04020a021b15070b0711030310090b010201050f0105040f0912090f0f030203030a0e03030d090302060a0c03020408071a1603020c010e0414010e1b 74
    0x406400042d0801c15904180d06020820100980d42c0070340b11008142400c2c0018070884003144c0d180101040c102031644240b005c40c0c21459240c6c00507100102440056003144c030b40345040c0401c8108075901840c0c0314005020040b0100041c0c01581d11500702c0381310f040c00c40810003840d83c03903810b60301f0843c0c08000b1100107010030804400d4030700510300615402e00082200d07080c180d40c80501100c050060a008035101c00c0844034007841540040e146039000a00900220f032415002000141c0a10825040b0340c0c1c14900891300b004108921401ca0384d00600441c9498469601594840386411070036925020030301c002c10102185010b403500301d51080d070140106187c04800001203a00b8109170780f007014414803040c4101c040001f0f40d02d041c1c44404099a0b071441108088220300c1c4170324401c1710080c458500928082540015010b00141002d8031503080405074407060000300c648006801d0b070340f4082c6800422900c0101200c06402c034401000300e10880b000384204100341c0c0d210103030000100c4e000c001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761724397 1250 761723147 761723153
    0x6091a0705090f04110d090f06151d071b050a030912080d0b030102040b0f0d05010501210908190203300c0a0c0609050102071208132901080a 62
    0x201a0340d10461a0804500380111240880c180196080c0454012580c0c0c507000381c80d044080040d1482e0460340042841607400910b4a91a07020000b0004c40d0751a0500f07030300c0d003a41c8100500720001c0e82c00c0d4600070807001c9540100e2040300c24018004c4018040e400e104a034810120795005004079026000901d0400524600180704040710380c40300c140d2400c42c100c0440000c045c0d0003290103c484038840803d0012482000900a12481e440480c0c2c503071001442c801c031102540701425071020051002c0040c0da07138503001076404088101e0f611180064a8007012420929580000050f034020b141190408511010448260040c0c4480b030015900201301d40d003a04c056042c101485034403925002c61400c4000202d80503840016109060410002c10784070a03e61042c007110039565044441445005940d007040b90003075000c0c4409482ea540c0d46001404140c0c014140f0701d0007403c40c4038003201d001c003250b02c03001c0005030594540c0211950010112200b1009004054040d02c90700000d0f02004030949 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761725647 1250 761724397 761724443
    0xb2b0201080a05010f17070b070c08010c02060c09090a0e010c0e04060b0415080a1806020306091f17150405061f0f060503040f1505060a1e120c030609 66
    0x708800b450906140060040e002110009803c41e86000c45141c9158000702d2050b003800e6140d0440883c1c824080340403001d11400c90109001c60700b01c10000c10000c469070004a8452100b11803040f164402044201143e09005503110ba00503510f17440040d1074000045d5460a4070f24144010700001e86030001d0410f5890b113849040010003403002c45c42c0c6800d10b003040c07042912030100d4442041c00052800610701100e0360b008008003d600d5105031050405500e0302100070f41043d02c03980e010340d00d0000000d0000c00c18040c0c00d1507002444450260141ca020010901040314110001c81405162030001e0041d1511040c41c0c0118400d0002d05284c0c600300c03444501140e050b844210000d044500c080050031a25185c01060b174103689422070f945e50301d500700100e5488104100400398261402040d0080b50703660b002e5406490300300c1c0e590010958070024440320b22901222268441c400c0e1204003c0760280e4440b40141074410b111003c00303941d8079159042200ca6122040c2e03044039806050f01400c481e44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761726897 1250 761725647 761725651
    0x402060715143c060d08070302030403060b030303072a1b0603140708040b07090e090709050a0e07090b040923060c07050c0f03010e030f040312050702090a0b2b020108 73
    0x100c02d6908a00c55140c0c641c40c1c0c500307421046500c0620260f010420503103501240c00341a541017140940d9035807162500035513950281c4001e1352501d180c40e03420a450700d008400c690062107660f40e1018220007281442e04074096200c2900c2540c2520320180c070000c0c105007a046e415a62513605000d60a26108c40681602c858401b80302022040b2410407040e143c0008842c1d8109030805030300c000a544210741030f9041040f540118040042040400030151400151403080e1f4070308020900032034488100c150142c0d2500713950484283c0060005024180051340039515000300100041012407407a19440381840c00400c02c921040204007a00340c249004101c031070f400c901a100342d640761480c0c4e900c0f034a4980c4005092503103d8427aa403005041945c2c250412140c0c501100b0a0340c0e0788a07007242420741c09034800d100496240d5142c01013000e4031401001614401c41c6c000e440201113582d010b19220040140c004e03529070150780380082c00790000136a5070390360100102d00180e5451845900014000c0040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761728147 1250 761726897 761726941
    0x120f060b072a090c0e1e10020f030703030e0c060a08010305010b0a1a03060415170609120a0503091501060c02180403020705190816181103040206071514 67
    0x4180106070360400042c000c1811921003442c0001c000c0e401007000c5818000d0071801c1e5078020243c00d100444401303484c1400410040031258807615030b8451500f80e0b00c40c8200d03141c0b10041c0c2c02c02d104c041d0110740240c10030140701403a1001d41e00c001603448005034240c1c2040040c0c03c006500034005100308502441620800e042c11030344c070340e0030b14580b0800c041000288611880703183ca0210101d00c83c1d444540000c4203440b403190001e920152242510304560402c000082028030460004c01c0985002040004001c0312941c18a071401150b60019105071b03001134080a80c500c0f07114010f10b608003500703000720b000c0c11a681d1071000c0e085a500400107500e51a00b45154040503400611001035000907103003003125419650b01c1c01c0714900c0c0084401c0340c00c03203520030400f900a0400b401c40da168007480000549420385461021410840410030843d41c0c480310014040e0010000314000d03241003405440380d117100d4543d00600c200d0100e41502a544094046107400ba0340c0d038284007035403114030144807030011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761729397 1250 761728147 761728193
    0xa050f0f010b030c060a120609020c150f01030b040507081b0a06030b18060402040909060e0d0810260d020705010207080d02100f020c0f030705010b0f06030601120f060b07 75
    0x1a140000070f40381c061900c0d00710303c00c51000402c90441d41c0203440d0a803081e0402c91f41040000c0e03071640c4a002a601240100c8401d000380c08003101c0c1c50600030040d601540c0e50781454441c0e0b0303085540c0d00c1d25015000c0c2c401d0354244030302a070009507284108505250070700d81445801100c07100c50b0070b000e0180131340d804c003405150070802d01c07114644540d40d4401d41030b100c006000d00d0315140d18021074000c0c4a181c018018880c00c0c20401002e0200b240c0140090808400485821079542041100c00c0d03201a140744801040d011000c002c2e0380400040000f81029118501c0c13148000c543c0d075140780c0480f128210000d600a62002c12003980c0500c00500107003075117400b8080550700d4040007500c40304540c240c100f201d69194290b0702c09000c198191403290345a0702c21a55055501c0710265525044104105e40703960030180c0004050410350240c406040d4060070003030443e12640010742e00114040c0f0a8441943d80c0c8103865442526401960000d0880300b007190340c6c41015081074014000014030002e1088 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761730647 1250 761729397 761729411
    0x2090103140112231506130b15030a0213171c020709050c0904090813050307061403040218010b120a02090901170c030105071d1005030a090c080a050f0f01 68
    0x1100701d00800d070f0880d40304600d03079406405000c140d00a0203c00740440c130140301d4109034801100c0c0d00c00180e800f5007011a0184c500080d030b1003054090b103050018007078201085890050311841c04801442d04510440030240c00c25164105410001c1030960000200c0320100c0800d19050009100080c07641003c949e82c20f880240fa40030207541c464049c0b18010815644000003052050300070140c0c1c42e00e0000900038840b10641d4200303119980c00030710070021800c4282000181a10f00040c0751030442c0d4507a210424403203103c59000c117451700010010381e048411040318090004000b940a400380515910958450328412221125410020189444c0900c10081d441103a0344400c4641d04580f12100b01801100040c4070250810342442c6455415600b09001d01c1207140d0416402003145000d80460701d0807800d046c04015504240700b80c4500443c0342000450b26001d070320f40142060500404140e1a02941d900e0030500e4607040e15011760b4203400c4510261a1180b00740070300c03080d40700b00134008d01c414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761731897 1250 761730647 761730659
    0x61611180106110304090f0605101b1e060f0527060c0f040902040b071101050915030c0c0316140f030a0c0c0510022b1709071206020901031401 63
    0xc944180546400c1c842d006401e0403214008004680103080382036030601186800d05440d00140911b80107042c8180c0390145070b130350098820441260011603111001c0b08079007203503c0358003420005a114020295542002c0800300b90180120022440741100014171403500d00c401d203100d11700030202800c3c1040114080e003140a000102a504444030803e1640e5900da20180e151a40c03155911038461240080b4000880012810141420a000d030f0401050085401c00440d103034451503080c0f40c0d0060300180340b41060742e00303070340a150b1241c100500035103010f1f0280c400b00c1c90754014042c01896160501400001c015601420f81e088020560042c4a1101001c82c2c09481e802048448002c008034000480203000002c1200342c002c0c000a00421801c5048160080d1550340106041032030440100c0e03112009004001d483c2410300ca603659105440c55081d205104034038010b405900c40340f250140104003000b0302c03000c003145035100e0940140d031025080d0014060f5a61112032104030181d100040100b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761733147 1250 761731897 761731939
    0x90c0207080115140906121606080705040305064c050901060c030302030907030f11010f1b030e0406320301020405180901111917070f110c061611 64
    0xc804022100303054280d64500120b04c49407e000000c0340d1501c160810001c01299502040c004c0e03030b0044d1b40c0c4550503607c41000340c45e540308078072004040e54031020004564010060103000c0c1d0448008400c40c00c0d01c01410000c00c8090010089500c0c0514103070001010840d918401000300003d84046c0002d41c90404080d010604094004d0181500000042c206607001e0010704003446d448101c072540310350b541c00c0c00401e41000318441408210300a81c1b44141d02e000e40d540a820200034403a982e40c5a285580840d5480ba44841d60781e0030a4899401140c17002c203514440b600f03110300c900d0014180c1c0f0603201030081c1c00c002250690080c0d1042200380843e89411911298140404a4000e02c0c0c0e103982407524014a001c44400052050105101c0b00750b9820541001e040c0c041655400000010b1038104000b00d0002c2e9a20008501d8800b54015101c5c0140407241700801200242d0703100302d01600c0420102e03403002d0303021008082140091010490340000c1290380e21030989041004410054038990 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761734397 1250 761733147 761733179
    0xf0818040b120c1306030c030804180501210201210c021e151807030b060406090605240c01020a0203040603050c0a081807120c031101111015090c0207080115 69
    0x10003040c0c60345a9116a400175048600119072190115580741e40d2810602c01a802c0750042aa5060b10151008000c0034503000710b90695222802d02403d981c2d481b00c140d180640e0083e012418080888070440c1c030080400a19140c07108220004200d031042000001c0c1450300d50210100e41070507003203820401000000b00f403542c0e100c41c1c281c0280c40351a011b41e41c1e061142c1c1544e18038254800c03042d0120030043c10000703ca000da8070a40c2e05200c0c558403040c3d0802564071500941d07820212080a200062100800500c02c1c0c1e1400742c91685070001c56603180742645c1c08180e0130400750f80001400c000e6243c3c184181540203000c90010340c180021154000c2c00040302400d812070500341403d040459103401e005460003050b69990429501040b840c2090034020540300c19079107a02417004441c000d501400ca02c01145070b1090241c0380d41d580a044860007405800441040e26884070004284001c192040006240710b175001030403c1ea290416031401e5070388000c03500c0ba03c01c034888000c2002c1103800c01c10381 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761735647 1250 761734397 761734399
    0xc01090501080f0624030901090c21020609010c0212030903060c031603110c071415120f040c030c0611010b0f031036051b0f0103090f0818040b120c 65
    0x803e01e00b080e01001d003400280c8034485c5101ea00004184000c4903415801564045c0c400e000c103a44117565044200b403500003900507000e10300e4060b4441001450041d00421108c081410038259190481d008500ca030041001d03414035990001072841011f103420401590b001ca8104501859440c2c600368042502c10100c012034107154445034840b01281c0d502c2c00b55070070051034204680329203070389142c80c0005c20340043c1c201d4092001010303000c410880c940200e419602100289002d030f5202c00c69a04840d034002882070701c0100c0e03036500200c0020141c0b0440001881555140c150300c801c80c48c42030303003110038182400d032161080103005007050310041030b50750740040106000501d580081401d4503005410072078440100c90500c404503407101d54002a800307581c5c01082125125485104a400418507184956a0050310440b11200c617601c287c00c950100351080020b0660b09016a0390700140c1d400c0888501d18018007a900c001c400d0a01d48100c881e030110132030380d100000c81c035031b0090b0f0740310345600000c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761736897 1250 761735647 761735659
    0x31209031e020f10090c08010216140f03070f0b060a0810020d02090405040c03030f0806060712030e1f0b0d020d12020a1208010f0e060a0501050d0b0a080c01090501080f06 75
    0x181c55094028401d0708011582e14003a5000560b550300c2c120b0061180743e80480e07420201e00c10125585105200b61400c00c140400c83c9072620380c80d900c92003150300c007000c1035403e6031090484020f6a554188054000c6070b01c00c1c600e001c0c1e52009072902c1109882d006200a0050301c0130003040007200c1e00020b0000342c6038081c4078010b996200d02010540644107020065801038140b1051001f00000ca03c0d00700d044902035600d030f5090060400044405130425a02c1650041d405d00140c400301d8280b4025206000b4a4180051045580c8042d1401c00c1c8245500d03000030002d00c804484401c0e4a4000d100c8001000c40703a0600380c200903400035507182a00c1c50080c144c800c01c100e40000c1507000708003200e031542d001100c0440900d800d5000900b1034030700b40124540909020300c0003600480038181e080c020384008011080c5076003020b004607450f4212500d6500e01e01c3d15155482015100d002e9040060700e00140981895500c1d4000034000040030b0b40315038100420102013110100182c503c60350080421588 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761738147 1250 761736897 761736947
    0x4080a0c0f0c08070618030210210e010c0c031e02150906040c050609060d1a13020c150c03010e07050403121707020712020607020402040b1603120903 66
    0x1128103a090400c01004207030301e1030a0909011010384000c003101e86240403a025651a91422201071416140c0ca0281e900c0e0035a06100515129860000c0f10840e0720b02034110481c04100d41300c580a10752600040303c2c0d40c0d14131034040c01c4402c0c00b540a2140c0c143c20030403500c034655500245501201654a10311140740e00c2c54a050910910002d10a44003800500c8090706000c0001511444207a8045407104507070341c00002c040c14800196001e0150003840c143c00c114010f4042d9000e407030301c060740810a074107080800f42280d1321001d01c41d28403a01c030f600050301da504016090b450303d184c103c40c121005000c6810810380c0d00c0c1c07490072030b8195a04c100c0c2403c00c50b100c008080d500e50169420042c801d011101d0308000c1d442e40541c060075502089560344072152910107090382c03219124000c0040e50313021820584090b0612600a21649201500052800d0b6541a010185800600c0c102c4003000c1c491b4903003024194880103d000d02d5086031001c00c18641c199070080c0045076a001c940c0000055012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761739397 1250 761738147 761738167
    0x10050403031d04060e0a050105030a15022101090603060b03070e0612010e010c030e1608100b030a0210030203070210050114010e040b0d05070807090e060f1b0a08070e03150408 77
    0x280d1400280d4040c0050042540710303101c1100d000022500c1482c407c1c54080002a14a400208450020b804c2030220112042c401c1400010350310103a190b032000e07081d1050b0b05550f410806501d900034816070381c000a90380c0c214500030081d00d403800d4000b403083e8403000b424002d400a10405a420040840d5404da4411403c000316001d400003554204941d440d221703a100f1070b42e4042e00020a4076621506603130070b0034007603260540c148d003c1d4015924564045112924202829880440c1e0814020110740750900140e000801c5076900b60400d0002035008014070000940421551640001040c414415981045010100d42100d04501d070704010424406ea442525103601c44a6075210181c040000c01070f00b4100a9500c10051042d00f04a1103001000554040513100c0d80691081e101c0241041d41c440101d150f0003000094041c810030510954075101111451000380b00d554020707280e0180314600110041c251000c500b0242d4000c1e00709160b182680b860320040594010751043c40c403034450b0f901039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761740647 1250 761739397 761739437
    0x5130b0d050a0606051201090b15041103090f160605160305070609050d120207050a12090b03040309060305060105160b0411031f0c032309010f0c0e0f1005040303 71
    0x80c00c0a0a140103019041007400030799002102501c3c42a1a0032680303101050310780b401c81d018000082c100d41885008182040302204004286440040c4007150408124180300030a60040e240c540842e031144980140200041c01450b069900e11350084a0b401e140500203003042c8101c800c0c9000c0d0311080642c880030940100103850000340c00801c10030002c1001e10b0425030340c5148034080004241411201c40c1e002045008072808282d01c60b02828454186a98810242c04c40011060901448840215070004140091489103000765a010304d01c0e46440c2000d001c0b110b0107403005040210401c90016a81080404e00313000310360001d095800c0342d03038034240508803a842c10440d0340d2501a1031034000200898542c0b1100c050742c2c10200b000025180d25054048400c1c01d01c00c050030709500b0401d910300f92003010100ba44002081c00100c3d05120311905030040b0b99090a081020400700c0840030310134140505d4010010700c05a5a0820030024440b02410501441c8801020815491841001c0603460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761741897 1250 761740647 761740669
    0x1e0e0901170111160308090d12051008030c0a0b13033c03060905010e04020a062102161a0907090f020903011b140a0e010f02010e150702070b030105130b 67
    0x804040c940300c240c860302900c1001e1351031009034001140d0030f011a03044c040104860300e01604503115440d13a00c040644040140030010705000e41c0426403180000c86070b1003440201491a10000607114001c4a172800c482101c00c0039111007101290021408002034001c4c043d5403868401074841e40e20318205445030181e40c1070b00e0781d050900c40c46103000301c80303c00d4040c3c102c01c064030100c030b07030030b00c81030b0b88032803000410100071100650305c0340e814401000204e0159200c0100203c801c62030000c1d0102c000d0603002641e000e601c0c00e0383c44a00880d81901488441c040328000700030700c61030752602030902d10003465840020b030107114016503440084108889a680c121503940d030000c0c000340248100445440b09610f4042501404180c00d0701e0003c0c1502c44401c00c1300c031041c4054690b102c1300102d02004450440c3c2d034111103400c2d0f659440084c001078208020b64240f040d620f000900701031901d800001d05002941e404444036080c1400144503903074404840021101c9420000126042001c001590000074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761743147 1250 761741897 761741921
    0x120c0d11011814010b040b0a06140f19090e04050c090727050312120412030b0d0b01050f06070c030b041b0e06040c0903050606040504211e0e09011701 66
    0x6004103001c0040003800c0d200d00016803c003c1040d000c8040a20003641c44c26903282d82c0c0800c5100041c40218010320042800003035101b41340d410860b104c4401400e5a1009000c0300103c05809901c080069000e000080500b460681c0c004081c10703d03541d01d40c2d4691a29240038403d50f044030000382030307521544030303e80b1103080800d188007058102c800c0040011418081caa01900550292094500c0d040c401c45503040d0f8158208051030f507442c0c03117018246c1054024801050b8942e0482030807592001004860140248910f0056515010800582d001000e00490182d1828040100400d4820907543c0442380c00100e1032520359100d28bc10702c0f8004d440b841e40004000303140e01c00704001c00080c03802d51281c1c2c010f0b01c003008403582c0403500313442640c0e940c80300500c15172081001801d03030f0810703400041d0440e00c1001081e42e00700802c4c4040c0d114020440c18240000d151070300a0a200e010000100b40f2292203081410f6038071900c0001c5000d030201405502c519600348165081b807880250300030030440c11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761744397 1250 761743147 761743181
    0x503100908031810020f09090606040503030703030507020109021513061b060e16080706080c030f130f08030a0c12050603060c030c09040504030504051206220204110403030809120c0d1101 82
    0x80c6c0340c070b840d0340e050300148245406640c40034001072517400d02d04121015160020001c2d42004426a17084001d00380c01004102155219410080141c60704c202003010001086a4151070340c081081c000b00850303460b48590104030b56040351070b1035020528841005550402c1011503210501841b95140c101403804021031340140070070008a092010410800b84e41460b81c0e000416107401c4407440213400709403411410300c22000049045028241080011584200704054818016480341e58131508220703103041c00107413500296090541e0007105d0130072a600c189000c1010341000c10100769241741c002d00c420380868001020545203030321042582c501410081c0148114902450000d069401c40e2007500d0140703541c01e403d884641400b04005116076610050071904024a0542012020a100007a6081a178440e20b81c005c8095000007080610300940300d080c8142801c0070001d2524400800351040188140703d84080d0050100f4604000700862818210f99428461000d00419401041282d038103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761745647 1250 761744397 761744407
    0x270e0406150b0c1e21090a05121903051209011b0f021b0112060b0c071d070e0406150305090c010e152110050310090803181002 56
    0xc0c00c0e00301c0455820001c0012441903690b03240058140901d080704000341d0072a030001c0388030846610036407900c54400000c4a1009040a80d90307180c0040d5000101d0240300001000f031550f0501e040000d00a000507680e01420707604072119580c607201100805854040050b00203c1810701c0b500588070801220459007804d0308000020030300800003515046c1c03000e00303030210748604503010f000e4541c046c28007070b0042c001d040320300381c0a0303a5011040e1400505201025504009056041c45010050001c20340b0b1155a041c902183c82c1c98000c81e94000e84513480381010082600c00d842014a13006000d500b07084a80c03209040000303002d800030390051005d0009a6410982d5541c0c5038000d140258900b000341e842c4924480011207a0114001119030005e028080c4001c01c0311001d8000d0880144840c08105801c100d0502c481c00b03001c0a480802d03580c4000c0f2014040b0345018451325001c1d01101c07004026080d01a65118a0750000600043e01828000b049159070784c401e020f858080d0500d06811550340e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761746897 1250 761745647 761745653
    0x1005100e04060203090102210901110f09040509160e1009020a020d030905100c0315050a0f0b1b0f0f01050a020405090103020d020310111b0109030c02061803070e07030e0a03270e04 79
    0x512340c11036120035650300703200c80021200c480c2c40413203035040341404006141c1107460040c08060301000c0c00e203240030712a0042440c3c1c40503460050401900a01410240c10308080400401c0d800081d0010401a40704014a0190342e8000603800304d40d11040c140403c01c446241003250a062000d1510380c80281401d00c407c0400798036901440c079801d10348100940c2c290700c41091000f007072a00e00031034510255003202070050754004000740c41000301c0300751000d1707040301d524500a042c00d8620245803c00e51000d407a81440080030301426501006d641c000310b041528280000340400c40612000c0c0c007840351000b80105544091005103d001001c032414007040007840c41c01140341e4407621800800c41400e08528000340e5060180500307580d015038030008121007030740030060a5800080d2880761403070700760540c4105850501004005014459211002c0c8ca0203100107400e80755402d05800391070b007122402c100000d411000807202101e0300614051810401d071100480c00718580c11221030141800208010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761748147 1250 761746897 761746957
    0x3121803030504091803020705060706060302030a05030901020618152e17010509280c180501051f08070e09040818010c0f120509040c021005100e04060203090102 71
    0x115010b41c070041000d40d49005d1210301c5050484c01c0100160800170040283d8600300700981041c034011080000e070150f4950000340b40085041c0205c070160030200d9200017540c1c0501200d83d220303401317100c141c03c03110601c1042919070800000394080a5204d202050902c0420418076426100c991b0010030350000c1c00d152088502c09610840880ca5001c40400f60b1713911041c0101e500407003100700100001544003001e02c2c19a200700c92422640340c2003610f400003041c0f417003c5080042820003050000440c92503141780507900140c200c10302070318005c0e03c5001c03115246a81d1104a403603901d0b150149445209044896024044007198099102400e120510036003500402c0380360b640305501d040140e83c00d40190b504070121040500131481d045e044e5804100410660f103a221070b60704d4070b5490401d0840004080341e140c1003443c00181d008420000c85e07403500c1d11030139800518241009820b82d10b080a0751107801c00c01800144030075000320100e41c030780c0c8094058440c4000341004980c4040040350104070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761749397 1250 761748147 761748149
    0x904030309050c240d09020d08031f03020603041704090914061e1f0f03030e0301060b1c150b07240203071b0218090d08091603121803030504 62
    0x94500606440d800e2070318210315200c184507151610300703041205003100c50341350b900080c542d8600d0517180c0407514016034401c00c40390700c0d092040f02c07510303181c4c100540a540b8680d041c10031404414640d41091000d079840000f52507125a000080100c0500030106d40c3d60b1038041e540c800c001d11410510410100408640ca5500b0080a01d00315030a603901c1040d603040100c00040c00d05141568040851603044a4204503640360326027502c100b01960707541c90b100c0a2a01c05910035000201200382e201524542801644020300c10490f50764101586401c4504202c258140c4041180340c0e00d4055415010600310200014142e40000584441e040e08040b088074401c510801039032102d6803903a11410310399100f528001d10396a0b61700500c912000e00d55031541c03400d40d001681d00064a0050b011580c84105109215905c00e001600c803811040d04081c00540d0007030646451a000207107202030b040309040d69241180d400c000c101c0301025898209031110b240440f05004004100301001c4141030b00240104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761750647 1250 761749397 761749403
    0x2091501112a0321130b0a0f021c09090e210a1b08040e0c09030f071a03130206030402011b1109060f1503150330030108070504020f090904030309 64
    0x40702c015030103810183c07038600807014508070a03204180f08a000105001034403030040e070b024060382800e0300c40b80c20009940040e00e04000044102c545034002a074103010108804111205a90713007001c1c40c400123046211a4020b5040d50f0740e8034139a011160300300b0400d0444400d0707510003166402031120302000300340e40300803042c0001c0389a58008010385107102c8488007600d904180d247c1e04050411003e0b101c0020041c1001c20f00000c14006082541d07810b1007804a00c030b440034010708002d458558044a0010118146410703a03100780100941e403440f0a05240c2c40c03030341c100c0d404ca0f5280d6440c40107988010400044100e0280326000c0d20301000001d0881104d046402c4a00064598822007003150b44840c59588175080360301c0980c0d10341c085142c50042c2d50040590b501c4900443e4516010a03d40010481c0c40c5980c501d4440d9498060b040c5521045030807240d081f0414510f40c1170406055441d001c134400c040c003031540003440ac0c40246017007064030070700c060090142a2078141414010042c041070481a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761751897 1250 761750647 761750713
    0x3060a08070812030a0e0d0e010f090806061201020f0301031518080712030e030d060f17030415020102073003051003110d020d080c0d0c0209150111 65
    0x803492090005400080714075902c0105403003c035804485450780c1001d4038039010907880d065a1003815501780a100c180d05600e65588541c0d03181100014140881c1d01840b1080c400074060520507a900462200c2d40240c3c103a462001c10300b40300f00f40500a01c540e08001c008035601100200401070f409040e40d102803881e90041c4000c0c100150b201a40c8441140c009060050801c030000c0003d501036031808121295050008950f0700654010341143e11a0000d0008682d403a8818070000e02d41c503509001074094007940355550541d80b40c034150340740b09900601001d215003401c01080603200350100c2d208964401071002c2c6070094040000d15041c9403103d600880710500d80a00c03078480c843d1162501c00d4000703980c41040d0501c2c40d16418009040c240e01190407010081070400540c0365814958a268402c080b40c1e556000410702d6141440ca04003c3c010800191404400c0503aa915000e40e400071031600481000200c07640060300d020a5000d52880d0900544d0341d007424498544503180d030f0401500b914 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761753147 1250 761751897 761751899
    0x60c020105010e061c05060901090201081b030c03090118080904050a090804090b1c0506100e010608040305180301060b220305060f18030d0b130504050607050d2003060a 74
    0x99098030001d0003246200d22290001030740300e20b4001042088070f03100085602e00070b180c036195542000d00880e0b48041a03034566001908559000607541c0d4440740130130780c015254980302c85000b1a0f11000c5c06501600f0070100204200a0702988038000088440e5110742c45040c2601c1c040007141c210329000d900c04c5207408002403811400380203000343c0582c400286840c00d81441d0240004180310074400c0d0700100b1181040300901980c101000803079006d10000e148900d00340000003642000ea030800c0860002100c010050143c200c0e841e80d40040d4981071560300c81c04445001400050a404810707490340c201900069120102c2e0000c0580c00700503074901346941080001d800c031b004410312005086030b101400141c8200e0480b20810740090396502e00d1024600b0014007032b4550f0700501500b418407903840d405000320746030040b521710440205840c01d0040785043e0300c502d610340b00010042c00034804001446290a40903a01c004030341030320084400f110102c00d851f2060207030800c0f00d50501400100c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761754397 1250 761753147 761753171
    0xf060e030327120a030c02101b02010f030e0303040f2d0b130807141905100e0a0b010e0609150d03030c0e0a0b0405031b0a06030209010e0d0308070201050c160b060d0501110706 77
    0x495542c1e1840649c01c022086c910503801181c2c48080d40048008050307070741c10186040d51082c00150b0059002d1081c400011001e0b0810990801d0162040f5000c1240d00c00340c02e02407500c441080c24900d0300500900c802c0d9680c6010482003024090300245041000141401001800d1385207500caa00b05070112500c10341c00c425841141d07c01020301410039804845900c203906001d405c6106c1101380401603071a0350129554407201c82d5002e0300903812803021001048854207240040302d40c04030880415012680300d40780070500781d0250700000740815451394101ca4100c5d00440c01c02e0808007000e001c0e8800a5501c0b0741c429040e41050088034481d0083c01d80101d40c1203501c40d01c0068a82008107410200e41c40e1010940081d03200602103810710519400e50300d81d95441c050704030041401307500d07291803528040700003e0071903000034420120034030244183c217480c80f042c0040402d801d91004400c00a61602e0380050760b60303401e01d40000d1556003032205420240e02410042d20206100c2d4105110416140b9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761755647 1250 761754397 761754407
    0x1d01051506070f060f02030c0d0506100503010b1810031a030f1e0a051c0e091b1606060807030c15020d0e190f060e030327120a030c0210 60
    0x2a034a50300c01401c1c00084040f450000ba8624024441d410000710707040910459004e80c2c1048505905034000801c0d402110301046c003c4603440b080c2110740100c15404100060514081805001c40070700d40842d1121381400440c07100314120348000c14020841d10701080040203400d03010354502c0030300400c2c1e8031201c85090014a1100780380c0b03030401038425a0200c40751007c0c4080041040c2d005071240405020204a0901c1031510041240651112050b0b8011001d800c050050300400e014248141c100305001101220700403245e0f0154241c16070340c18100c0c5941641c1d03102c0c5003000e000503103060030005400c00c0c0011140c0c110303481410b481a50b1965052a101c40f01d07284040d65025802081d03c044506128a5010a008400600350071500c070208042180c91089e98003c0509003045a40500c05150454148880f00108400039450510001007200c45650381c010701c42116801c8040a41c03040e0f80310b07441e205081300200c4c103c9440071101d04004103080d021502c141c0c060340f0b1201001495900c24 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761756897 1250 761755647 761755681
    0x50a1508010603122a0602030a0506030d170907030209240904080a030510090e3405100507080309071d0105031f06150503160306030b010b0d0f1d0105 66
    0x200390040002c2134a00c00030b0301e100303880071500140408550812002030038500a16655180078a01c0180c8a01c1c00c1c5c041c0c10101c0741c000d4940d91180c0d220302104040107078841383c111461001082c4000d03240e1a0741600e00e240440e5500700030b503c08200010000000e020a0b40c8141c98084841d480010048480900c2480c401c03d40b0003400603071041051180d172a0003500503d40080003c24110703050740e9030b494014101c0b01558a21a0290405008156034094030040b0a01c1c0003403002203404035106604000d107480c0d020b4032401d03009170664802004010300500c1503501c0b0607004400590303689402c50300f40b511000d8501804081c94029280c10420703000841005041c0d5101400038000c120150300c03998601181504000c151585800d80860840d060b10502da502254940342c280d1a030130300e102551032090302d2010403001c26160500800c0810390481038075044032808000c030f83d0307544030300c00c2628060805407001e440403604040480403503a40010100718002c98407002023003d5200c40c01c00c5400c003140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761758147 1250 761756897 761756903
    0xb270906090f060105040306090b090d1806031503020a0f060f0512150d15090b06030d02120c0705040606050703080916090218030f1c020c09010603020a03020904050a1508010603 78
    0xc0300380020311442c40c1450154105070141062420035680759188030544603004c2d41110344284030030902c022440d00b000003c3c001211400d21a200c02d0030b1a03020352449606114103c100344c1c03543e040d4400740c2114180d9001a64000d0143e544103920340c00c5a18103030b801403140a00065113240c01e1400c061080d400c0c1d4440441e601e8408616486511304018505022100c641c4c0c0035003264140000600102c2c251051120402c80104c0c0400309414400386059000b0700d800d001c4c1d000054440940f650110345002d81142d4214104e4461140f2200c041c80c0503480e8100b581c00074945200824080e070031030080c014071031280c5d8410380941d50b0b80072455210034050255240005800d03000f8040c49445802402410344280106a012101800020f10b403140c0792808601940180300301001c8001d459400e840180d22900003010200c00e401e0204d02c1d8490140f0581d41090f41c0440c0302100b09104c0c0d01141c05c1144014000d1000b41084003082000b4200c2e50b400341c182d20016000002d810006000c0e280840b50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761759397 1250 761758147 761758159
    0x403020a030c081c050115031104030318030b071e03020c100216050a06061a0315010f111615020106051305040609020919060f0e060111070b270906 65
    0x410756003a5590700031450201c2e0424418042010101c0898603c10884c0c8000c0602040c0c652508030040c000700c845040c5c3c0300c209403e0075080701c80c81c6952801c03503049079450700e404010106010b580c0b90000d0301580000302071200130740501040650051502c031803e884090254080f982ca031406808a10910034003250310307000000c1500c10341c6400d6014120242c9100d0a44d4071046c0e60341c0c0c85608240c81618102c0e4410740d03420040c09014400c0c203581b0700c5468160300030340c0b07542400000c015a0940b0b620000c1c0c1006030410300d200440f40b06900d0038200b0b0b040f401c00c03125550401d0828048401d514000c002c00403541038149540e5510501500f000c944d0007510b13221069011180c144041c100c000c000765115600c8002000041e01c42c1100b4078401c0c610840c00d00c00401151084d235041e83c03103581c0613074444104000140a01c0c6c4030811101d8008100f402c1106096030300c004011b040200341d40c40110707004000701c1c0340c00c0b8080fa2a206400217038264400f085000b8000c00410034488010b59034039802ca1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761760647 1250 761759397 761759413
    0x8100207060b06281806020601030b150618060708190f02030a0e0409020d023a150e0106030b010f0302120f030304151b05070b0703141f030c06091d040302 68
    0x11028101c0b03a41d0342801d918101d000f100e800c0c017841d142034400b540440c0059001000410505c03001c0c0840d182c1240b41002c5c02b0a0079540800000c42502401d90744400700000c2c450b4628465032118100c95841d40d100c0441a1101c6122804609000d42c00e10070001041e07800400b040424070100c00c40e030314a4203c2d00d5401c60384020030144401000800822a00f096803503201d6000f41c1d0f54251126501e80b09070311424030098100402d14111204030500c1c07004203100040c90400034589040b0010602000c0c000010344c90a0908441d000d401990710140885003608004200c40e541120680160790017074600c004520040a000c99a400b08400301c000d1681040c000f0400203928082a20400d04041c4004144101825034202d80d0104000c1c1920101d00c00141800070800c40c60041a03201f9201d040401028041c40b0f200590369030002c20b00c141001035074626028640c4d030110780002440c1c00c040301030603030368a43c8000f9022407100d0003000c403040d4414050540041c0011207240c403c0d41d0640c0a41000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761761897 1250 761760647 761760697
    0x5090601021c031e05010e07110a0b01091a040905030c0c06070b1b0c030301060509040606080613022203140106151211160c0504241202030708100207060b06 69
    0x10503d9411101140404c90304860101c440c6002d0b2501800d0b020709540702e0350070104805485030000c40ba40500130340203510400c000c14030100034107045401000c0c001c01e209548415103c034a4024045681d84985404a400e090140c00000b45c88540341c01011148441095010014180115580102061514000140f200c4208115000204540d409490521000501e40c0d81585c10980001000450101c1e0100d0103107001e01800000308a0b9041101190500e2004580b00311510050344080030f4001903500c0d1440d0349020301c03400c006260304d013041c2515120b20b4101e181c2510443c2e00115907081000104810104d403609210241e195100d50b1340b00412a12880040c0103144010032948a00b2b001c03803046d810100500041d500d10030a40402902c1c00d1400300710890b6134040300400c1d404020500c1c0e110f1032000030700f480e05a442e11f0021208041c40392002a10303203055070304180d0143c00b80529040e41d1547c40d401810420740702e1502404500c40003800d0003400d000ea01c1d90100b188040112540320 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761763147 1250 761761897 761761901
    0x603110403080d180f02031524060c07080601170303060105070f1109090607180503030708071e0c0807050402030f0a050a060b13030303060801020705121c0f020405090601021c03 78
    0x18107046003201203550061994134440300f000c424801e913445694800034a04601c2c082c0709000204810b01040d50300d90030000c1000010021241c80c41842110711106000d46030f4402d400d45200100903400c5800a0380c40b078072403907180e900a100d41000203922081c4201844008025070380300e2501030707451a0600001c0d480d032080d4000c5e03881091303c00c3c02e2481d04840043c2c49500141380301e110400010410b60074a214002c1140038621003c0480305041d91090005d9a0007008489034660403901e8151030304241c1c180301c000c46444000140c070448082034868200704107000c401d000c0f16041303015601210b96440c2448241d202c2101c0c00d030300b090807800000e00303a1b00e0a039222581225110000180e00c80e21540406801d034046c19284411501c4e08108000301750303140c02030720701804124000f50b041c2200f03941d8582d91170310300d0704094022020208441c4901c10300c1c2043c07001d408030001c00070301080d200c014068000354018098240a801480000381c2c455000088000ca03441742503001980e066503034001100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761764397 1250 761763147 761763157
    0x901080c0913020729060d03030f24120c030201081807090506030d090b03060d0318090207020405090d0c260c010b0a050307030b0705090d080a1701060311040308 71
    0x2010160074025007403503880c0d80d04a0390074403690420042c3d40e00140d00f042444003a000c1602d84042d00c0b02038145200341e0b945405182c10040035217408982c4621450300354003810041c1d000c00025480d001144494090410444c180c81c41840c0c10369041075206c00500c494800c1415000c1e1002c030314070400b000154400d060165004807410450200c008a100c016401c00d4100c0d440000c1e00f42d2500c00340485442c0034003034494980c2e26410541c40c440d203840780300001800020071141c41000748030f12400a0500032403440c98007040080d03c1e00f00603600c0e9a4040020f4005140a900aa01d0000005d09008000420060300f044640701c5e500c0580c000d50303648070207904a40700203511024a15232207a00c1c0000078090440b100c004400484c0390103082061000b0b1120a900042c4203a003d4402000030480a601c0c068001003a468080d42c1c508050f070200d101c0c021007e90003003080700c0010301c101d0402c1d4000c4c0038410b4a80e220313007203014603645d900c000c500369188451080321502d401c110800c00294108000d20f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761765647 1250 761764397 761764411
    0x206120601080c12070c0807050609060709170703061109120601080111090d02041d0a0b06040e010b0d030e010201090209090102070311010b2b0f1406060102030f091c1b0806090102090303090108 85
    0x7d4034100d030950300c02e81481e4007501c03902050f40c002e070144808603411100002c003a1441c0b07074a1241c090f424046d85992040340d40b0003c1c2080b585c41d080201e940701c80e10111025808040c0200d81c00d4000d00302c40f195121400d200b11a010752900b800d90b02c254030070764115210008001c0105111012907000c01c40102411920010700300600d95100c1616081444481c0d0310b40c0c054101c10080d45002000d00003034035610307003503143c469240c80003106060307813626460a00c60b0780502c2c01a001d12840070050740140340c1c00070b000c2e5000d4080420061403081c15001440380f030348070781d5030742604a000a514500761071054690a40c0300070b070988030341c4109200400004801340800c00c030414521603503c1350340d03040350741035030030780d500c13071942250402d00a8100500d540105082c801035281c2040e0240c0401940a004c410074402c000b001c4880720128884040c030110301c0c3d080410304401e0140044815103c5840b40318041c103034080c100009607042418800e44000c100090040c40c80d10840d400119940381e001003002d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761766897 1250 761765647 761765663
    0xa08010315091205071406040210051e030f0a0b0405070f0302130509090d080705040f12020d05010c1e05030903030c030615220519210206120601080c12070c 69
    0x440425452220700036030f505113444082d590074003030610405040c40640400030a40c0000103000058881c41d82181134080b0520305103480742401d031072481c8100080059444480300100c20303c03040850655205005d07240850b000c01841c00800140019034400300c4085003c281c1c0198948041402900100111081c4440ca04001030303c0d40001201d007941900c4030300c8039503c8100c0c2c00c03819607000703000c19403c940c0ca81040c4e400c00380707424440e030709210302d50241c401402d854105038000c64560510481045038088000e00c1034441c042002400100b05841d00d403030f0f900b4142180c1290a00480c2200c0c000c2c24000c01071441d580c0c0d410f11840965001504030f81d0010764082005900f44002400761070944c0300d0381103200590808020340f120070a45500803510811300901440456981400c2c40e10444a07640e03055240c04403031045411100b500d010000e508071900061100d101d201101d40c0380e2040000743c036980c9840d164443e0140d8980221309040450094440220700c1c09801000310044c000d1017a044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761768147 1250 761766897 761766911
    0x30e011d04050112020411031018110a03090215160b0621030a0801090c0c02040c020106051801080607080c071113140a1a030307060209181018020a08010315 69
    0x8241141c400341d0082d03c501141020f0b4104501c0c6c903004010100c0c0404040500394200200c4c4484585070621401e1110b20a15190340b40301d0505402c112490802608025100c1c408034002801621a02404038030800c011341280c0b0300b40c90440203840c100681424203419002c610790b0783c02060040a450203511909407440c80303108240e4500403603030100001002e152107011540001d0610070701a0492511603040c59160810f40d41d215119010b0f4540440b804254600110010307030040c503990300055041140c184c050341801602520040c120750080007151425900c0700c600329940034046d900083c04130010481d540200e81c0d210760213082c0c00c070000c0001d9200714039410480d040303e90012084810403a1403041120304040c500c203410b2000c0c5640c3c400c1c0c4a0880e0000069100d1041d4003000f84060383c003098880258940c05504552025000d1841c1c1d1203040c66140b0001c404005c0c80340d01402d0765503032210f00c0301c1507c1c0c0c02950a0407085840d9102140d08555803600c0840b0140004418180d480403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761769397 1250 761768147 761768149
    0x905030d020307050d0b01020c0105091e0418031e0e10050f27030f030a030e1f050f0a0225030201090b0a0605030d03141503030f19030501050d030e011d 67
    0xc000c6028582513140c0036511601e502c1d021003030301c2500c1040c0f4155001440f0f0243c1d03a1740c002d0211940100100c80340c8071031100800303040b88581c045807404e5400500d006100c00319440450500000c0c14044d8540c94400c0440c0c1c3c1040d6003c95a03448444002070458210740d032942041821414032965a08005081420700084086503070040c04030000740c403c2c00c0340c20384100980b101c2030280022064001e03150007070402201c907580c2c1c801e80e03200d01300f015914404007080c04000d00c030101101402d03500c0000139201c03074440b0801601054079484100504c46020454410303444c0b00301c54404601c207400301d07104031100801141c0550070361410b90955499810a50005275400031b6540b088543c5000082e01600701401d1510784244c0f0341142d0181403134025a9411103008024103075102c007681c941d03040e8003141100403a0441c0191011008500340211341120203000e0b0600e403031980c10a40da003c00940c3e17a20b0080182c0e601c12618058046407030240b03c003001d548283d00b503692170030440d07001c500d00000c0c2724 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761770647 1250 761769397 761769401
    0x312140f070204021c05190f0219050918091c1d040507270810090327030206040f080105070903020d0318080316060506014104090209130501060e040905030d 69
    0xc0311f03241c04910700f604448002c480ca201d02075483c072856508500b081d551203035140715220a0700303585040c0040401c40700e5082d40c03070901411148a851884600074103201e185a940c3e02502409440d44081070500e06481c00c3c8074a0702000c090780b081c0024410300301520300740001802d000d0650704c01c005d00000e203c0024004401022103101c82003000a11880c40c00c501d15051002c5610310b0f800c110305001642020940c892106000740440c0859900c9440d070f00d05114100c1102d640c4003d40290001c940040c804d8480300980d011501500028000c564810108590340501d07030200a52000303c0c1c00010700480e00c1222403502079410078410303902c3c0688882c0c2c414a0f5030843c5480380c40c800c9440481c3e0080110b140107030350300038900303003401885c40c6003005103903210f80740545003150000c1d82c8218008082e60030042d403c030145d00800c03290b6501c0f500c1e028058042c0d800b101005002d0942c4961488580d003103803203030a040720f10668030607160b1059882041b001d480c00890941d43c0344014008620510564 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761771897 1250 761770647 761770651
    0x109150b180a0605160204020c07050306160216180203100504020d0204030302120c1e01020f1201051c030e10090305030d140f0c0307030506060d060312140f070204021c05 75
    0x3078402000310720084040220036025908a4400c1080c24007115010301020413800c08840e80c1140e002d605ca00712132416910b404101ea01c000e07818420702007032003000c03081007100802069483d0b081e2a1380c41125441440d0101d0701e0320458007503600d80695885040d046902645e041a4001f40000d107050342c400c0020280c0c1c01c5074901c1001b040e80020304100b015010408400003443c6056418200820009220b440f10f01079695400340c0c42030350b02d00d482103000a504542d11901000500c60f221f81e400031210000071800d010301d5018000e03095200b80c00480141d6401103480d8596100c0c00034158000c140020003510721400c0381849080c500110014000340042c001c803c0c1c103032000080305080c81410710300d640c0f03018210040940b000424418080c104500302d80d4000300740e060106c0d00b81c40f14404200c0c28899202148038091070500003104114680c1141c3d1080d281c0c941c0d620b00f0305100400341d02417520400c0011451520100039a400609013034020702040b48200708200c00c10098a143d404c240c3d041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761773147 1250 761771897 761771917
    0x10b0406030606020c10081909051c11282906150426030a02011a030f0a020d0501060323012d051906030303020d05010503060601080109150b 62
    0x1010a003805400d0381403040000034281c0d88028081c03040c080000c101c01d08410140c0700104a80800011000701e5080e0741003120200c3d10200300300e521075a0400790344900b40d030b000d4031900c0c00c2034aa00c995020b02c5070502c1e2411030708036005815141c100040049488030664250b000c5480c5040fa24408188071003030b502c40300d2240301400c010007000258510704261004160a1288080440e0514281401070070341e020b451440310149019a40032034803e1130349980460301c0440d40b0002403501c00169064000c01e44e05a8890030300901c900c0c691040584412001640b0820ba80c0250101005407800d0a804d600c214021000020461b03144d4845410300c1d0041600e4510301070b999901c601c0c003038409204100240c941142d1b03505441c22042c10003040000c1d51141c2904d15503c0d5000b156541014030021107070883c03081c10030041241e81c0d18024019400407980400e240d0300e4a00001640e040c041100e52158030141d4030420603a00345400d0342c5c0104400360426404046199003c61003001480c010100030700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761774397 1250 761773147 761773169
    0x1501110f010504121803080f0d09050d02210915070f0302160e01031205031b0406030b0915030d05030c04050a032f3307060203180604051005061801 65
    0x25013800c02101c1c0c2d0740c00c00303045420840c2c58860000280c264001c44001c0c1d9520807207050f40c5041d24140c200c07203030165404a1005504e0b0003c41000c1240010320404414195000c0c0c882c80100c0c98007040c05401c407402c0304c0c052004208041c44007880c2c0010359101c1288954011414010581c469201d00901c0403070840269104044118640b03090310052802008088aa1101c0358119954240b000304400945000c2c0940400400c01d0701860807404048555503540c92501c41d0341e2084010040c016a0000d14044c0e101a03020505003181d02d00303044c0e290a4040c00900401c0380144040310755520051041490082c21311020500e0707a02e540d046402907020b909458555903441c6540503041c3d02202c0c0d110041c100d00c4103c01000e03102c1001e15559160f00781440b9111483d424046028090341c81c0744441c458a000500100b00021540a135020f205c0021100300226507020721580d4404058502801a40c8131400200c101005504540d50003540540349614290f0701180040102d42c0a03040703c10601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761775647 1250 761774397 761774401
    0x80c01050c1002040b121501020a0b0705121f081c0e0a0801090303060312030504021e12060906041b0f0306050604020c0303040b07110a08040506030408040b13080706080f1501110f0105 81
    0x6c05071140d81e5042041b810503441228000f0380080c0da991958078000f4a01c1d0a001d00190300180034200f0386223841d042a10603034040c07030b202c84901c44a280380c201080c0c2d40e4075625800b00d0170080000307503000d44400890b00c80301c0c0030f0f0845100b27487c080c81405c01c1c02d912032100c400c0856110801e000740003840b4860b8034003241180c110300e0703c004030130a00300e114010945050108000341c2e48688460300c400c980b00e8503040e4507207160700c04500010b07181d8101700342602c106018000c494500240c1144120300401840c8a000000070441107c0c0c4441c5c03007204500703540380609001084503580416000074008000610300198101d81c607046070404c032801e4617040715140801540700c2d00f1424407480c441e82d100c05000000c21a80d101e60752401980911070158002100203000c020305e410889003d84604000709464240300aa00c01185000340507025482c0900c44001500e46e00400c0243e00501510480401554400030071151840c051140030341000252444811301a2050003984034082d62000041054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761776897 1250 761775647 761775667
    0x6030c12010b0906040b1f0e0315041502030106090e100e010e0403090f0b0d0902030a0203011506090f0608042006040f031703011229070302031f080c01050c1002040b 73
    0x540c00003890b042c0176a080107403c0c0c040765202079003210f0041c2d901c100c030182e07031081903022140c10041c0448103405204445544012500d0582624030603407151007000042d000c48440c1405901082c411840401d81e1154180081038440701007030303402a207050074200c8980e07441c804410304030400ea100340c074178a070b6a00074031003895408480380015145800c000003555103041e482401a00c41c0000c1007240c1a5680003480031540e092003a050400d4006001f4060142041e0f040e040d100101d100d800302003545848000f83c9400030000c10b0080316496115881d580d590780d11131442c451040e07044030304810380200c0060351a079a404050000b41c600728446030803c80c01e520707215004d02030445420700b0f0a0000d200420001200d281503402e0329a0101c8220480c040c007496407003460ba5142060302c0c1c0d082040f07081105690389580954840c1981955090031140203980403085a510360083c0c0b00300d5005444240c1c030550146000b024054412008c581d10500900100403c80e04290843ea4080c040080e01043e6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761778147 1250 761776897 761776909
    0x40302190b0a0c0c0b060f060705010c020c031b010207210611030106031d0d0e0a080102040603090c090b030d18080313080c01050a050702090c040503060f0f090a0c030b06030c12010b 80
    0x30300405040c12070144200351120b17003003c0c1005100910880c032155031402c094440d18180ca92166000009101d18041100080e480303036441d5000501034807412506c046900f480d0045580c0302d0a06801038001c19080c114161a10104a05200c8030210381051030000156544a0000c02d002d001e0070a944a504060000f0142d42e66042e00c907036902450b9102c84c25050380860005010901418101040040c2d01c01141c07c007a00c542c0144142d52000c180083c1d00e507096002060380310301c10300d0450307041c5403034a41d580100d43c1c5c00030300b030358141d48440d21500707a80c0d00421030350002d10741d0000d1303d90304503a5403807480703186900040d02c01d0b4030182000c43c1005a10010400e10350140c01c00d013040c0d41032411a020040c940e0103825006032054143c0000309080078480d07012900902005001c1da2003030319000e400d90103000390980710320140c854100009410003902091140301d5990000341058ac041c80e40c0c4840c60b03200e10160415038540a81c0502c4030481d580c0c03071809040f1030f441c680041182d401c1d000030400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761779397 1250 761778147 761778161
    0x6160302070b13050d030318030e090a02030106020d3f0f0209061c06091d0d02210309010b03030403030207090c05090a12230c04050a0c05030f040302190b0a 69
    0x14021400340f10502e07181940b0801102501c00544480d200e1460b070b41070845c0a010301c41c108040c80c002c07100300e4005051b032000d00e00c00103241c10f66421a0980710400d4003800c9102c01d02c508401a0007031003044001c40d00c922240584c0001c410840015000070343c1c0350400e4200d802e442c1b82d2005003074210781001703001c1c107008000f05000001821801d040c4032401065a52144440461440d5182403c110700188654041030250000d5101003103081d00300ba040b24484270803e002040f03180700b00103119131032900c0050303048040e13020784010351400407074001c5210841d00040c000400554a0780310764042a10204007800046000c0d500070808a80f8111074002121080c0c4103c1c0d0800008003c801d801342c0350001e00e0812541001060b801c41c01040c00c140303481950f5010750403001c00400c801a601404005440060b0000448080155441d864007042c111213840c400c0ca0080b580034000140001c9031215201d80c440e0080c0140c2d121000310020711072a666580104441501d2000d083c0508034489100300e007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761780647 1250 761779397 761779409
    0x70e13050609010e07020a122f12070f1509021206040203030301060f050d1b0f020c09060409080c2512151d031b0d09030f120507020616030207 63
    0x401e042a01c041002880c05008500b8014203030710110300c541e8401c12501c210550049081c016860b00e09400a0102811008501001403203030401d1210118034074005220504c600c3c014034610414246042d80c540004909845803030054a00d80c0128624040c403da105a400c02d001030303040500e2041083c600ca8018102d00190b001c0c3c0e04010050318000b084a06440d02da0a0201183c0718a0108035042e1140700c0810005d81e09001c8402c0c440c1d0600080460112120703151002c15015200080b641e17030fa420500aa131081002011078034a00b015032100d1090303406418420324040306261964541221219401410802c1241d0ba071995080901298041d203944814100650026220940030b07c00e00d0611a120b6965032020f1032412050010384030380101230b0801d480d00c0e802802d07803c1000020511700ac2440b405004617941010380300710400815242c1c1304c080f40500782526100c030841c0864107007580382804020044040586c0d5110090010b9030314440c0c488500800e580390090610460368008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761781897 1250 761780647 761780651
    0xc0804080717061005010804021f0e03010f1514030c09040c091d0a110a150207080d1b0b0606070c08010b03100c1709030d0e0601090506060405010e0904031205070e13 73
    0x202010b0150209850110b603400d183c540c085441d5400060801281d030040341040cad03040040524074580e0804203a00588100310000c010005511000303174150b5900c030070300540101507078805210101e5507980642e2481f17009012030303280c03407455004560b00c0039003039a043d14000e2490f201001508158041c0034401003d0101001c22400280c803820f554000c2402c0041c800642d002896400e900c4441c21540100764210000116464080c0c02a465011500620055010394900c0504d06401030300041c2c9800c2c22004940001d0750b1584418683c02e001a12840d4491400c000700c50100780b481d47c010018048038000020003500c003404251420000d487c1e42d20085081c441e0301c0c4c044a81004240c4840c0e20384001840c4142e80d480e0080e41180301d41e80003564450314021b144080400c000800320b050716510081008180c496204010840c06075100b124009042d00c904035000e424032070764260300b0511034104000c59407003488842080d0b9070f00301e41d910001264005800554a031481000100c84a80303141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761783147 1250 761781897 761781901
    0x90c0507020105181f0327120f210e0d180b07052409070b031603020913091407050406050d0605060112020c0717030c0714010c080408071706 62
    0x191040c0180b2568413075003c0c07521120f2085850ba0910005840310360312013019080352192000d80140300040c44100f1054401100c90402d0314601540703241c8a400003811b0300203e9403450201d03490980c070046c400030802104603080003454030003509142c0c405120b0012400c001c459000501d45507019550008014014a05031000c00c04600c044042e9071020b80302c203039617006a04009150210a244407102007520001e044001603001514500034441034040d03a141641d5043c3d04800c41c04180d07031400c6038800181c84d154144d40641d0052441450103000305204203a14054001110106141a920b40300101c40c020b00d007041c02d020510141c402114100f1009040c42c010a104200c0ba12000301081e50702c40202d0001c0c0e002e07060742030f04d540c8400c400755601c0745013404158540d10b00e8812411030301031308240c0040840000c42a520209490310041004a140c2a02c501035800c043c503465043c0b001d440c5042020500d90001080038048150003014011b00d0211300c43c444140c2844550303050782040781 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761784397 1250 761783147 761783149
    0xf0b1e0408040e160807050c070b131a0c030a1b050303070c0605070518040504030509150a170c030610050c0f1e071a0f0405060304061409010218060706020d0c09090c050702 76
    0x50040d0044400c7c50321a4803000c1043c081442d0901c29045611614804119000003000d0007580348203542d0f035856011000c0e4040e510401c440c0c0111880100030790014084c5200c001c1c8542001c0c01d941c100d1842081004000f602c816055a000b81e4690002031400741da58002e220341c40c024180c22241c1c1d131600601d4030311048542412100b10412040c410b039265004582072501c2041a118100d0005084044414108a19501c036038040c440c070a0100340c01815040400004840360b52061544e1000d0703502e0340c0d0310700041040c03210811021106208051140582c01c3d403040003214203900b940b038002c203c03031b4100310361629143e0041c56074694242d0050700d0500040d414122041c910701040000f15441e980060341aa0b8503004039040550040b070301100300401d00c200b81e0815504403a54040340712442d242c4c0d003040c078283c0c402c3c00c1401411504c103884024050074190002d240103405030400505280050a5100c290307841407008600052800e0001c0c0240380c8144181c00f02d41b0018100607241408540c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761785647 1250 761784397 761784407
    0x72315072306060102120c0c030105010f0602070e060a05060a031b030b030c1c170702030109060c03050a1a0d24090c09090b010b0a0201090c030b10050307030f0b1e0408040e16 77
    0x46c0404105100416511030300700c010840300c4c101f214011b000348825a116120004620740c1e510800006100e003101c0002c106032043c480c140941c401505000c0e201d070410b000d00640f5032004500c0d41c20140e4030003030181d4589032807040c003104d80400d5902091044003101014079201c0031600107881070f1400340c40281d040c251040c81000c1e05600048410b22181f0398003040a180c011030402135003550900e0700c8007041009607802503426201c6500c08003d90b48030030340303080d080b12003040701300c03103098007011411003685421111048414480d24240341c00c59000c07d44404020364a91071070ba00d840e01e85001d1401c100d5003044210282008450400140c581c946600d40070b141c1c1072040c2c04c0c241100043c0511824802e42210381034682100d010000d165403440c000160384401c4425000001c50400c0220300352070b001c9100e0b002c0300d40003440142940584d440740c00c0302a001601c0581003005140300111141c1500d64a80c2c03046008610f2251a280b070000f81003141480107007200f115404c40c0c104941030319046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761786897 1250 761785647 761785663
    0xb0102120306120a150504061d0a060b060405041d0d1713031202130501030c030618050c070c0f1a03040b0f0c0f18040e072315072306060102 62
    0x858646001016902071541010304604024148001414224585201541040d4040c7e0f2140c417042021141d05241c400c03040000d012102c140b5000015110003040668000c4103010700c00914003441c00d40d5480c009011140a42135007544034006100d1035002c40e509103d103400032401c5083c411038051300c0c4000d40c0312280c0024000d159203040d4410300f0091500c540500742d0b081c1ca0f11041103590308425141241e02a52a1250600003401d10b200400310611a00404044a40040001095240205410026000082c8400350607881801584003144614268074001c21100e101c002500c0c0c10302c2891483c44c5614071480440c51020018080021404a0681e070722203510724806415440300c0010400c0c41c8149030302c00742010008600d5041180c68502c2001012208071000c220407104100115107444291048054502d0580c20030b881c0038080c82d8454601c5000142030500401d0610a800e00d290010b84040d111007104202441d086003094000e5000040301400402c03492500c100003d5540000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761788147 1250 761786897 761786899
    0x80c031501150e0603070201150605040f032604150201150e06010507240c200325020d080417010e0607052d070209180a17071a0a0b0102120306 63
    0x100000c1c0007420b82c490101000c80704402814650b9034240214000c0c0030305a41001d002819488001c0080c01d140554201e03802c40b4400d6090021a6181da124081e5803460b1700010440300c140b050203440c4400e460402000601180d05030701c00c0b8640c580350000e00b12a0940922034044a60000612912041d2061103a004d0001d1a14566804040c5401040104040310b0255802401000e200303490041f0780210011082c540c0d100513001da8116081021038810344c40000342c5801c20408910401680344d4041662003288500040003c20b95002c80c60301c282d03154003030743d03c0c69010030705001d2081c000e1081c10482004074003c3c0100c0b05256240c90711717100090150702c1440400a0f801c1c00540002c0740082d01070407601b400c00c0408200710305129059211050480c49600e01e04000394402c415000301540390204c030750041510b0702895a0b100c0b81072501103a0801016030074810300001800c80700038440d08070305943d9202071074148030742d0441c01d513425044414190741040a40d0320f0003819200030b036548428 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761789397 1250 761788147 761788169
    0x80c03073005090106080c0d020a12030c1209050a14131d07030c03030f09140f2d040b030c0d02040f02090a0312020705010f0f08090f0f07080c031501 66
    0x800c0221180780300459402001c02078188010000074010640c003440803542c0d26010741d01003825a20400048980081000358051600d13a0203004034404090b0303505555200303041800c0d035800c0a8071521021000c2c10700e1040000c803080410311241c10984420001020070009c1404040100760016528214400c41d004180e030f0364a9402c142c0440415040700178039924000c1d81d2079203032a8200714006045a020036004150f030118250740451007200d00c90202d48455142100450802c000c0203075045a81e030010ba400100180844280061480784090140f0004950103010301c404051105503505540c24911940194070054400e40f681c00e044100c003607045400083d0340a0124000c2c000340140c00301107410803014a80401005036070342450014070203030340807138902540c1c820045408030304125030140081c031200341c6190b40d5402170500c5504100c9440a4036600c5400d42c2c203851500c42c051941c0c000b40e6000c1e500400c100203060110140f0036205401a0501c440c008802d01d0240c0d0040c401c201083d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761790647 1250 761789397 761789447
    0x6031b0f1d190609090f0c0e160e0301090204020a0809070b0f18040912090e010b070c1806030203120a091706070518101709060412180e040c0303080c0307 68
    0x280c02a4841c0b0084d01082d00c1c00c000c050003904002c1150b601d454000c45a50300c0b501c0011901e000396451403881456035459614542d04c21600481d1800220001c1c10b40643d2a1840000142d5440c0064048800d1990b41c1403d1454901000d0b0f1a000f615846180444010020340c8144010003040380d00d8641d40302800604100e5040103d4000c0c540e00c0005007041030006014006190700c41c54000464130200410300c3d00c3d90300c1d2004a122442a45401425424008800c205d0340822801010a40194940c005807240e9a500402d0030210000d030740d10142140007401c11241e90f0814001005441c2e94010450003c40e00c122013690f43c80090401000c0c0b000206080c6090900c1c0707400b9a495520117041002914980354004e000300c04000010090050341500140c201d80c8005101c40c03045800c0815955003000007001551400c440c0401150805036490000c1215040510114080c0e84030310042e4006600d1800c2c014030882010b000008610000c2061062141e8050b601c20b8000940c14a0a1111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761791897 1250 761790647 761790691
    0xb0a05161d10231c06080a0f0305090312041d01140d0c091113090c020606090604110304210c0c1a042303010f060b0316020106031b0f1d 60
    0x7155406100c125203050603203000d00c0b80303c040e0160046290051031610300301101100340040e500940980c0e0710640c015800c02010a4060003d510514084e080982ca00084140480d0074030b581510400c046c014002020059007200c6000c1d18580100c0300d10141a41d410030640a901110300050507104008444400e028000001caa41f40102000c8808000162808220207a20b4120701d2501818a40c803400020b59a2203600400b00e0640456014140c50b0355104204407007603101800c001d070416907a0403000c2c202051079000354040d85c019070580e201c9400f4002c50004848031661100c2c01c1000640802c000182041141d10903a503a0009103802d2408011100c28203005542c00182510203294850703003400d49642c02ca20780c0c100c054000780070154160b2034400a540452103a0780150f8805c00000b0614070701d0845440140c4903520022502035500e841d5440d4140c4410326444546500c2e0b481085070f05050702c0e0301d80041c100c5035010700c0580e0190142c0200c0c8103004045103100c0322003462110311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761793147 1250 761791897 761791907
    0x90506010b09010509031507090906081c14181f090b0309190b0a060b0a090302060904090c1d0a0513022106090106030b060a080304030f0f0b0a05161d10 67
    0x2c0c104004d000c039509440442c4687d0103402c2c0507600700d404145000c9010820400d14015076040d110801c004180d1040c03080102d460090003103c10b002000020319080703043c890220000e0240c07080e04100071006070721110401040182000c0c0a50f011390b04180e04461960f080180003003200c543c503044544030b0b9100440982030520a03001d80c0f0080083c1103814042117440c014107809200318032410807205450b802640801c0c4100c02e070b10b50118814410800c0180303807100007401c0c2e03071401420103c0c991115641d01200c2e43c1f00c2d5000100125000400300541220414a00713500005966061040341071080000c4003081c5902000b90180360700b403050a04004525040944104d010700444565145c00d81c0307002d00070b1009020440703e880c1d903080481c40914100840205603007050001d145410310310b9441401b000d100e2001100c001038402011030101d0420b800151145a00d4030700450280344c100801d00440d203043c03e1000510001c1c5010104a21501d0b680982148003507544003050405e201050f92 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761794397 1250 761793147 761793157
    0x30319082203110d090806061c1b3f0807020310020c0c0103060806010509072102090f06032719050c010e030613082803051009090506010b090105 64
    0x103800d000440701c0810590301c21041d0924442150a070b0701d2545000e202221809124441c1506581c009400300c4c0b100d18040394610303403503e50400c40c23111480095860004060b5200b564159804030f9050800010700c460b801c1c07000d1101000c124501984860719508551382040300c0e03440700c3c07a07078003004e82c400c01c010b400407213004503002411201d0103407d016954000e9803005160301158064141c0503c4035500a0050000340e58049002d000c1c280e0810060050b9140001c1c801400c10000c403103d000904409a200c07400b1190000c0056038500c00302040c0909035002596142c0541d004108010345000f0092060003640c0e0480c2c08060031582001c40300e46005440d00d198000d440f4012030307100030000b00180c410180742c1c00703032078200c0d0301c11201d0308160b1600c2d4102c50b0b241c0c00d040000c12003000079502d10001d044021042d5100c00150000ca40520b006403800c0a0880100c1d503114103100302c0c13440c151040001405000b8040c030841c01c03155039042c0c0f92039040c45044500800850390520311f80c042c400b510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761795647 1250 761794397 761794441
    0xf060a0b0340060b0307120b0903041a040303081806040f150c0305091009020d03030b0a12060c08090c0a1206060b0c0312060108040305091903021002030d060503031908 74
    0xc0d580000c861910700c6030102e010201d4500349032440070001e60401080c0181102c011490512003c410394071074080c145801404000c0718003041001165903140d24a820540c0e924604003283c45505525000c0d020b168050285480c200d200c004481c0200750001c0c0241c6c2c400e0f4001035050041440c3d00c0c0c20b0115a0050048240c0305040406a00c0320550680c030080c030941c182d008440d0454030310b1001c80d0868131401d43c00f07234204d1740b1404030038040b13802600030368440034019000140c05541d83d102500e14901e5003000b11030b820740714500d05801640c40004103030440704020180c84400034940000d03540145078072a040e2241810040c980c140715240e80070b0320007401c100d010180e9510310303020002d892303605c010305d01012301900ea40491a03951152004a00c030726410349500d45400e0491040086030000134500f1001d03900a00f00c00b00c0161519501a645d1008a80085071603a024079074110a0714525000729001c1c0d8400d002d40d80c0613210007030000085a0300e41c2000b4019403600001450308001c2c1c00d03072079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761796897 1250 761795647 761795731
    0x50a1b0c141b1c0b0c2b0b090703060b041802160302011b05070b0a0b061b0c0102010b06070f1115070503040501030c031a1203070b040b0f060a0b03 65
    0x207a20512001500c54150104841070f9981c484041901454004035400140420390b9050006950401a000914180c0015020004080200080824503041d4280ca501c3d440380c079400b203180a03041c04160150803100906040c040d16042000580d01401035208403c0b00c079126020007194001c056040b07994400c0700d0340c14501000c00303504000e80078003045400322984040d841c800072191031091042e07840082d0310540c00e111588510007040b000e00f040c0e280c29a4028800c210b080c400c1a00780d03000300c0d08000a0070140c42403843c0c0c2000a400c50b001680d650340100000c03c4503074006104e8110244a85500100c4a0405103058010483c00d01604000041c4560005883c0d070901000101134030488a003642c003404100d201d46c00440541e45083c00314102483c20405402c81407801079640300512024a084905081c000d848514482106840941c0e8560440003803000c9040943c000580c004801d4900d0081e00d440c004c0340388000c3c1320040c0303c1c9102180c1409082160414107a005500041000305 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761798147 1250 761796897 761796913
    0x90f060109030b0117070b0c07091a06130509010501030b030604020613050d080715020c0a121206090509010509010c0f180b07060b040e160b030c0903030319050a1b0c14 74
    0x1008040f171081c01140035aa03c41c501c00011900d102204488055580c5009881d0452030004e1400141018107401d8450340503e10a60349187c480c0c038042d2090300180045c0a030340030300d00018080302c8001a0015410142800688205038a001410f03a80156040d103d582d40c4004480e5501200ca4440c1c00c00c0ba8010209880001030108501c0a49006405190340380850800001d05c0400c078425400d00024680140ca04e0b0804100e007105035000018103801c160050180c50361801c812611f050f00400000c4ea554000d1114220091254907401210340d80204040e03040c101d000707800c6201c020252130401000c501e02055070005650804014400c070751940d03458000302c1c640071020b040320ba00002e009034909050442e45613000540a6981144064540b560354101000940c45900040c40440d0b000d2040010310600c0d1000c000440c4140444404c49070403002c40c0c54a0301c01e640003d05440d4107242404290700c100300382504d00543d02280fa060041c1d03040d1040c540040040317480d10081c0114003411030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761799397 1250 761798147 761798159
    0x5030d0203092701060c1506150819020309030c0c04020702060f0a0201020c190519031220041d011a03010b03131b0f060203190c150e03070b06060306090f060109030b01 74
    0x1046244c55201d0041014005c2c1f03008207940840d0700d04d110714042403621501076102107000d0358000b904907407200081d07030341c80420001c0c500c280ea10903a00e4030705a0f440020405800e900034051515210802c442c00d62a000c180e4001810500981c10f01c1d03201841c0c0081c0c41d101d65030003541110014100b180680e200c4000c451000d0542416415003079800e4050b50aa8004000c400002100004d51584a81c0100614032800c2c0b4010007400803441000d44800403005901001e03480540b00400c4552081c43d210310060480d810001e2069026546074161044100b441181c01025a0b05450007850126125a9402ca0b903a50000250340c015282141408206075400d003240c40100903036000c250412001d5541e550200c0c2d9034450607445c240b000300100b00e9000e000d03200314152188540204451414116104ca06408075085210051110b51000620b142000300c031880840d80584101c0740c071401c5d4079054010684240c0c009107a40d0650741c201d00091403980c060480b0602640c1c200314018840e41c0c41b61 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761800647 1250 761799397 761799407
    0x70c060e0406050108060904030810030212011a06030c040501050702040b091504050c0a0c0609080f0f12010f0503191b0b1b0a0f0b06011e020c0a05030d020309270106 73
    0x10800d5070040b410b180c1c01103010750003900e0181c0101405090050b159a464400b2903468202422210402544040c00000b5982c1c030f000120b0a10b2400000103541d42d004070700c0c0c903809401d4a00450003080180100300031074800c04242c13402c0310000c1c24480c0d170301c0c02c5500c00200201a0201003942c04046c1000344552404070b2140408804c4041d035040001d030f107034002c801007140507050031070b070000f01545400b100203400d6810040c03000744280030031420300480400201c1c09030042504400e0304540410702c0e001e04802d060500e401007030710341a2004000d043c200840c5c0c5500342c030307425641200394100b00d002c1040203c0104031344904841c5031807140b207500c0d11310717100d8550702c405041c5031a80082c14003264494004200d601030241d200d0324030424071405131754004032510000e20b0281840030b001e000c1c842c0c000a03900030f250046800d6002d440300411090401100300c940e600f01c540680d05c101b800c041e1058000040f18014207080312808080001540c0280121089036000541d4000304000000c50b00d8001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761801897 1250 761800647 761800667
    0x603031710090c200102180f0a09050c0706200a0f020a020406060c030806040209031e1203040605061804030e0d02060903011103010e0a050402030604150222080d03111e070c06 77
    0x40042100c9402103040307145c20f034010881303c0305824100c1103441038540b804555050003414003409440c0700310307070b07a40e410012a08101d07000342010707400041403001c1060038414010041c014540805114440d4913061129010359828407080c07001520400892600030084100d8a40e030080c03007400080c3e02c458005110020f850811000305010001041640c0703824002d40c1c4550402030b008000300e05101710351f814900c01001c1011294020f034100c0b52283d4001300000c61203103005400115050820400f84480e00303004581001c400d88005050000007980007101c1c440151044400c003880080d2400040c880e40f1580049a5140d842d000f80a6900402000658101c2d030030a4042c10181e6180e040d042e040d07980445000b5410b40291000500145803c0b0003810380b1202644010f041c07810b404d421540010b00da422020700c210030007404000488041105480d001c54900d000d1204520001030740319103006460184202d040307040c00d0040744c800c168007a07501d030b5070300507110034100740d41d8500c094600c1440c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761803147 1250 761801897 761801927
    0x1810020f01060503060c22030c24020604050a030e0f040e0f070b040608070f090e0f0412021b3601080705040506012001020d0e0f010f0603031710090c 66
    0x20442c0c0001c0314900803a41e24490b902085000d89400104071800120145c1030000a107100302840c1c0110100706001d007180041d012079110346005200406100342181204482c8904560000003080001940414621032990b4035050940c1010b0003400095503004881e030100d07800900e064581c5150700400207280e1000c03e0104140d994042d207170400040584102e000f418045904080822100341c803801c14111500303201d1800c207512544411210348024400c0d110b100b204c05940d001c1c0011322080d5450940e0f400421b0009021115104800c1c7c1c40c90081c0c007024600ca071103510b078107048171050038110890f8020b0006482070003282d0712540203c41036080c095006a4811028080f070b00d8201449480d01940d0140c44aa001401d141d01000c01200d1079026503610303540920140504041e64040d410803104000041c20111079070422003401c40e84454450100c40c0c1c1004002c001081e080144040034090704000364803565594900c02303080c0b2402c0d40c03011100300d28103d5540203045d4424400c10b02280 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761804397 1250 761803147 761803151
    0x60a0b0d0f0f18020a060c050a150b0a060e04050c04120605091507081005060a080c0a09050a0f0e0a1104050d050106081c1814040207020f0d0602070512031302061810020f01 76
    0xc1c541004640c045c810380f10007000d0b9400000004d001c81e81e040ac401e003a090402030042034043e6003a0101d039180039640e0100020942c408807a440f51714080c0112130b48040340a0101d41018030700000b07840d000070300c00409080b0a81d510b0104803015004e000c3c65916900c04405a5a02e04220070004c0a400e012510402c004612403030102d09441c0c02400c541c1c007031980755034641858940d00d1003803c441c1c0c004500d4000340b01c9800c000061640b11030521900502c070b001010340c416454001e060041c1003004003417440305441c248000b8551071500050300c045c0c4005807440113124070a032900500400d4281c0265940388244400f10489228a41c44218903d101e990f0344204040c101d160502001c0b6030f0701404580041c0610284400d041c164082d04040340001d03c3e07150714684003004030300c04c9000d031032080e100250001400303810710004000804600d07486041451441c502041c804074989a041c6009106070400240c0100614200b103070b0454600c40241003034100e2840940c01303503490125144a8071254 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761805647 1250 761804397 761804399
    0x6050d02073201181e0507030506071b08041a16120e09040321020d140105010207060c0b07180305010e011a10091a1e0d05060a0b0d0f0f18020a 63
    0x95018000c41050103490040c3c83c2c611364103541d400490a12400500000c00c1001140ca40420300401c8020001c6008402030020b505014100a040c642020410f11401044130729440010b50342c80100c604a40f2054108010311015030300d151410b01c100c403608414070003c504400d09100d18058000f200410b142c1b00e194034103541e83c061003600c1c0c100711740250114201c41c0d03d40e2a10140e9000c458050640220300500d482001c0345036000325400318600c81e81800c900d00c0140030958040003000081d010500740040100000d030b035003401142d4000c1082003013228007149040400d00c0401c0c0d04014652000090144c0d000e507a403094000d00e0102c03403102950b603240c15194201d040144500d201c1c540c195940034100c9084c00d407200301040c01480340c0020b01400301b089208429016a00c02c0401003091072060356500c210044405840e40a05404e209040c0703a00c041190319006000c5401b0159103280c0450b5813001c1080c404024024103000201181c01c0441138a10a00706500c054100c41c0b084580c2c2e0303015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761806897 1250 761805647 761805743
    0x31e0501031203050405012712020604050616020a0609060203070311090a0302040b0a030b040503030a050c1c180615081b0f0909010b0a03080c0d030e0706050d0207 72
    0x951828400588009420b0407512140c5200350440c660041c020b90000c18a15140701d81c0806a40c403540e8191010b00081003038074104003d8281c0c2d410440710a200404440c2080d4442c191038040151801c40000419003011100900a001404ca0b10750007040402101c140c60401c00701035072048460744006842d10f15240041c03420340c07042d1803024101405065200d4295400d11000f41001310b503803175000c0001038001000610784500c143c41503100e00084c580360300f0009801c41c107403640903041e00282d010a020b041c110b890340e1660030041124903030300422502d80756100906e107007040da100a4081810548205210b1008560600450f140141121170a03007034880382884010301965940c0d400703504032a2409951400f4401950010001d80001030459029000200041300d66030088810090102e900307074045005009140a01c000703410140010006003d40c01c0c0c8034141c0f400b810081c4040480d00040c1d00107603905580000e94410b4583c9150b00f41400b1002440c109030058071420000310005e825a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761808147 1250 761806897 761806901
    0x1501232404180b0a030803070c0807120903150b22090b0a02040807061727060a050403030b0d050604150b042901090f12022d0915031507030e030a031e 66
    0xc80b0742000000d425032302c03100e504407140c241c7c851007586c1030f20051102001280400b00c4040c1d1601d1035440b02d0070960f1443c64000c40915004050880c0e0702e00e0711414849035246d41035040080b0b0319407100d40d40c5011844246500a00750400064030204090040240311102ea900074800d680e0584100d954150b030b9a8021211150700303140010781501002c01003000803047c0e0548050460480b211040b03010400c070007462034484129000031002d5100c03c1030100340f51305071088014003041541d885a45044945555594100181c0000c1401d0030002c22910500240da100c0300350520024028882c005064100c0704402da541881040718414650b440191980550520000c940c0401000e5100c21300c3d18060740e040100d40c04040e85c100f00e49041214984034102207082d20b403100a10040ca044020805001d503242c3c00410460600a0300c009000c03443d40c0004140011800b00b1548158a54800200b1805424006a07204d141c1c80041006040c0b150590800640c05110f0a02c2c00e810020f20400304007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761809397 1250 761808147 761808149
    0x6070816261603030204080d050d050f0402092e0608100e0129040302060d091401060b0f07061b08071218110d02121501232404180b0a 59
    0x40421007000060388480700040100c0d42c40e4082e0a0044c10259241c0c0740310700308000b001c2d080340003030000510300104080300d204d0b40760454103d40c05602d49181a82c00300d060789902030101c81200c4244000b6195200d020540c41030307001c03d0150411003aa07a920000751030b101d4140d603030429859556201192100c0c40c520f540e03040365034150b445040003508414000c2840b281183c00340e282c100401c03012000da1a0711004112400c1d0b0741c8800154401c0906281400466004030304045904044003044078200354819100341c9000c00794066503074001850300d0030040c0384900e90645448940403621422b160044480741c4203003515140d001d00810050703043e004603030304420144042c016004145012518009002c0d581c80e40c003600c0c0c40e103a4901ca8000518480c03020300340900c180d1029070541301c4401a04201da005216403030741d03d8406001e0f00f015107841d03c2e83c0741c0000d0280b410160308032004109a0b9a180c005a40050360787da480b0b481e141e1001c0c110802caa001054603050118000e001e04180920070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761810647 1250 761809397 761809463
    0x131e1a0306091507030905060c03010303020f0706093303090b16020709020a1101060b0c10060e0604200d0209121f020d020c01060f0303090608090a0f0206070816 71
    0x4030400f00c04124290380c018001c3c1c812002c041d0703502c142000280c0b0400600e400364061125041d181d41c514907000345080d042d11401010b9411541080125035003010b13580051340e0040b0007807409020000884003a48007a40540030080900142e035504698166000c4c2e041140526080240380e641e404098600c0e154001c503030700041e4444a801c014031080c80d8040d02c2020322a1078440003000c0d85071001825501c1c0c0e0342103038a60b00c42c0040c3c0c035445030004200101d6070500c04241400030501d00003400014050040119000396210080809800038400f07201010400390141c2e60340700d030346c81280c01c0025000402c030301d07010380b0908001c0c0d004502d00103800820b413000b0441030b0b0a5080f810361101d020390041840c100c0300c0d640030301001e040140c0c280500707009001669040c40300c17245981001000c00300e0f641d201b4800c0c0440d44080c480d888902203540100d40b50481030342c4a4032450313840032270f0440c0b041c0302c00a865400d003c00d00324000c860321070040541902410803450030340c10307840054003040c147c001c202c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761811897 1250 761810647 761810653
    0xc040609030f06021207210608030304021905190f0e060d03030b01091203050c010f11041202010e090411030f0d02030703080c0708070c06080c04050a05131e1a030609 73
    0x10000500004240ca450903c100390250810ba00755006945059081d500700d8045500d00c400120017650144000004030440141840090300d01020b8035200c7c4005000a40564420501001206c03240c00c40500200800b510030f0315152828503500400090345e00541840700b40c1031000040c0c80036031944490183d2001844151392245907038055008110140c11503040c0003010400084a00c1c20560b0b40d20103501035142c05035120301c001541421507c0b99159003004602c1c203906501d8010050301581d098804058207034000d0607088c0010303604402c0f50784105502219003c100000c00c0a200010541038000340c00b1102184070010300c140e142c2e90650801c4005a006011120119108041664000b40f010700c200b450b0928944480e04c3d5030303010381e82c1038880072003580040042641c05500c00c1e920083e80440c9a007070904080000f000b00440f07103d4148600c0c051001105030000315072216030007508580200808134144031654010301802e641408100d0940c602e0500f00341008254944074100903005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761813147 1250 761811897 761811899
    0x142103031305150c03070828150f0806011512020f04180911060702040b12030306100905061911250605071e050a05010501060c0c0909030e210718050c040609 69
    0x20449031308800902c01d5603010303078024030721486408c185400c145504052201080c626002c9044c2c0752485520390008007400c0d03003003008000b050004610281516200c01c2c07030360313420301850708200e0b07075028640e81080f000d910014081c4034140c88080144103c07110301c00d031075070b6601036045181d044030a41140a4100c03941c002c4440311a1404400400d103180c4024400102c40c504d26001c100e40702c09000c2a804151f1001050086619010703240c4c03c8070030903d14040300158180f001240042c018030a60358003241455400080842c060301c00081c440182d0011110450a401c0b181200040f640101d11010f002c0c94801080e00351041c402c90b803070b05c0c4d00003022200d1040f0500003002c0c490140c0c501580e5600601c2101d1000440c2070103030900038441c0d039450701c40c1c400e0310341070011505640e940400b00452800b0036000000e50020707a480d040300011074240054400d05180540408842060458580a070000c040b410140226078190b4204800108004d96902c41c07101c41454429406007401090719100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761814397 1250 761813147 761813161
    0x70302041e0203150306010f0305102a080f0c040b1e1608030610110a020f120106030614060103020f120c04030606030f1506142103031305150c03 64
    0x2006480d65907190701c11840640300d1694a0481e003050390841282030742000754140a1030100185405018a815441c0d1081d10399540c00f66151548400240e000d6120711010610003a1403550400074003e15060400a5000d020001c011500071116010300070041c5020800d42c260030320503a020340d03c4403049a46811554010403600281ea40d41806141c081040b0640c0c405450035143c0340898070501030213489041040402c00b03c862240c0c00042004412124001c04680000380c2c003060070b40540d1104241c00b2240c021130070001e00c9201c41d401c0b96082803000005c02c101a07200c000c605007041300f40344650700c5203001101644581c096098400400703115101d090101c0d41400c5400000d14a802c91909a4a07540c0000b96030007540f041d194071440340c040303400b44003655811480c4151494001c100d420b042c03140b04900000d1492072a070080c0e1419100c022400c03500354504001c44101d1382141d40f6450001200b602c0441158000c0302e103402403040b034aa100c00110301c20b80c02002d0321341515040d81e032010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761815647 1250 761814397 761814401
    0x30d270f06020f040b04090f1e150b030c04080106050913120302040302180a182301020706090c0303201903031401080105100e09030301090e161412010b0307030204 72
    0x140155201c03942000310514540511000300300a2a40740510760703d462421a2000440c1c6035819440582410514080d21042c60300102002d0002ca1030380002d01080c09220300000c1d02c400d508400c1c0d640e10000b003030010001c0c0010240c000c031506000244803464a0b841400650355043d22001c0806506841481c00160086c3e00700da64080e00b441d006083c2a82c82d00050b200301e10043d640320800255501b07020002066008621900e4660751403500048034a0341c82803140d44a81c407c031009d080130191000c1082c0401e404640c01140c0000090280c1c800d03500744022001007500c0101e000c100001c0d0075410342800c812040c49a400010042c141c1c45118003201602000070910032010195180102c0c0031000f8081c49440c00303050315800010300303440c0c11032554601c800c650300902e5a4000880402241d208000b0441c0d05598009c80040b40c2c00c90002c41162528115513286d808802d01c440012518402d603d00e2242910411203d442e607414500800341d00301e4440490035030305a0001c140900150500d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761816897 1250 761815647 761815673
    0x3090f0909081b120316090512120f0904050f2a25060507030b011b0822050a03030e100518091b2206030b06120406021b030d27 56
    0x440136245150b402c460700710119442110b00c9205000c10010300821998042480c10203443c4c180d603104040c01210040c1036076040b400c0240400207000191007015984018188c0340c100001400c20701c42810300c50001d0b8500d0340110751001ea58000e40b040c006074410709014010817510710801003843c11101c0d0203219044440442860110b5000c01500380004445200701c0384260b00f16900003448140c55400108485c0d1054030b440d10401e202c032003400c085000c40342102c20954040401c01c540343e14021462103400c5c459031200390f121480100000505402000c03910141004417074011051000140c16030780c80c0119206800401400062401d103420020540c0381c200c4c01c0180510244a049510b030281c0b030f0310252080b160b041c3ea0910300d0856907031910b40e1501421003410140010004140418118001d4035082c8800b610048046030500100b41e04640c500e2266280f8072620321500514507550340d01c4051200b01162400920684040c46240d001c483c10080300c810143c65005a01d40e0643c9100b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761818147 1250 761816897 761816947
    0x30902010801090903140a0e03010509074b061412040f020f040510080609010c140a0c050313180510060513050913021305090604030c0602070c0303090f090908 70
    0x10f1448680c80d24a01c0006d425040491b0381c8901d908e4090340b0070315003900c2018000c0692640034410501c9501d401829044413110b80f02a80d0051002d624000c07038808003000d8420610314503d04440001b03030424146007080c0d03019a00c1c0c45080c0f000114000714207101301d240048c585030741da101040004900011000c0d074580014010390500d800c0c4c2001404441042c0c400ca91803141340c06040000040c00d000c3c842c0d12102d0b940082020355165003019040000000c00b0071604207002941c1106507000b41d0444100541010407203031101a540381100b014101070144551424081c401e1142650300ea0103103910401e9200c61303418407946450030a480a40051203a140318800a0314081141d456880e0003600c43c0029524405406170503005105400c40880f84d02c0e000141444208107c02c000015142e800c20781c1840d21002594960510344020b01a09000030729102c500e100c00010300d135000c030306035003502e0104d1340d903030080d985d02e000840455403440002041c200c014003c6c0f00190725280c0c60141c40400b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761819397 1250 761818147 761818157
    0x207050f13150e0a06081203061011160509090f0d0e0609030f070311060a320a11160302131808030103151512060e070503030c01090b0601030902010801090903 70
    0x35982c0c0680c01044150040d01101c003a0301c041141c3e20f0201c1c0100c07802441260050000d00705a24080703400c80c80000d250301c0c042c1c04140b03407a524540c89418601d482802c13400030340322024004270f0411203421040c85954414140301d00410b4004001003500d901210400c0028080004540001e03621410b44070009603028000340000b042503181030005040d04d01c1181e0280070740c0f908610b4589035800211022038013800040c0306214074586c1110f07030705250b10700d4204000c40c03d02c210003200800c07000d80d00918640b035001240d00290b10f40c1040c078082e03c0c00d00c0c403000c3d079103186000e0143d400103292a110182d03000d0040381d82680701400030b9005401d104c1114080f80000f503515240c0c40f02980c8282d000b110250301d1030b4610b090704500c4d03208403228131140c2112a00d044d441c1c0141c0307104604450802a20050341c0e00c0c500000880200501c000901d03010b000d07a51281c1da14005c1d81d00034203080005032803600c03203140040e440c0d41c8207208103603289505071a0031685900304071038a8001e018681003101484 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 761820647 1250 761819397 761819411
    0x1050307031e0908070b13022419171b04050f030307020901030c29040e13020a060207090e030f16050a2f0102010905100b0a0b1303120207050f13 64
    0x411a01443c84014060041a40d9030102844c00c002c0140c0000c108041038943c00c88548016640d0800e001840e00c03121004204010100c0203803070f602d00c142002c00e20060391040d202d0407040e03040030943e80d40d42050f100385e1116a4034104c0c00c400440c100b40801e000c00314100414450743c680100c040420700809011203040188560109002c18000c0c0c0050b05c240811b0301003080090f06001c5424091044090110602006180c581d1034500440c01411340d14456000080c5084058003030395044103400034441003043c0c0d92140080d407111000e001e0008541c3c2012446100074000008541040142d290814503107850f081c0c42958200c07407804110352600130380c0e41035800710303400003c1c582c040c10003040701c0c40b10b4101a16800c2c090340d40705522141964103000164010031004103002c0c04035200d0380001308140c00e8400004260b401642c02c8010000c90203c0d65103d03402144038a88242c038495442e50780c16440701507080c0e07954500c911034030341c1c890501c1c1410101ca042503c6088900f00d8120008603200d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 761821897 1250 761820647 761820701
    0x60108160c0c0305010b0a06030b010f030f02090a0e0a0e0303091506060f03010b040501170f01051e0a0902070b090a0807030302070c0545010902180d080307020c06090105030703 78
    0x42d507552040e0350a0391540014402d501c2d1407810100100302504003041402e07400c600107004803621300701180a05590b1900a00c02d0300742501104c0300194010991030240780c480c0040e848022054031080e00300da103056020b00d031450380041260300a004440007015000e4581d171410981c0302d0010041c7d034000344244400080d000c4074401079400381464450f040c4d11a41000001054a50813603009040c010200c130621504848400407181580c1065801030350404d2110f111415104c0b11140703590b0007299034100054140359660241003194403c11500d07505840c2d21a0a40e501c039040e00e400303000e0500030005030340041d0295006001c0c05210700305241106603208009002e41d0600345134040c0c64655800e02c4034640e103480361206d5148016000304419425518008059518140140c1c1005c1c1e50000b140030038a0001912140c1c410001800b0034100500f5150580494105589800261050407890780ba2464400300f0382d034490f00103039038040c1107503a5641d00324040c0800800004280340303400200495 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 761823147 1250 761821897 761821913
    0x209060307080115092603040b1804150b030705070c050d080714030f07060209060405090106210c0f0318080d060e0a0b030d080408043b060108160c 65
    0x128810315225406150303d4543e9a00c1464104402c8004005485109110006c55110051980020801c0d420380e4401d10050707147c503500c03c54101e100b06120201d6001403070040515880030102007620144203101d1000f01c40840c0ba5603e000b04070030154140300041d003442c80703440680115406180c03081c00507a558008682c2c0410703807043c1541d009c64002072180a02000d03080400c440d00c5a40300852420400c041d0750101e40c000c0c0700c8021302a60b000200400c56540e414180c0c2c01801c0000c0c07400e005940d442c500030317025600f60301002c0d080c1c1c00151007059100030680300f102c02c200300f9600d910810074460311080703000f040e00700d8070101c0d0302c000780e00210007145011002d4000b500f14243c1c00a820390034408100c0c00990001c252009007030400006101c2500e0101c2c1c400c0c5440d840c1e0500c55015141d5180c100b0307850203150449a440540913541c400c1c04c0d030014000c0161020400103003410154080841c2d11020340890f200d6000c1000c00021400b400c0e05651000c5010f40140341000d40182d1595034200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 761824397 1250 761823147 761823151
    0x15242304090b01120f1709120c1c050115270e07091d1002090a0e061f11030a020a17030609010e0601050d1a0a080a030c1e02061207021e0316030302090603 68
    0x204008a0301c1101400c8c46820604895082401800f00c0c103481000205079080c1900210b89001c81a10404200030007500104941c00042e811a1303800c0d03031612681e00311b0000c962551107030506503e071071011900e8180710710100701d0141805021880d09080103100a001e200d10101c0850000d80b403070018494091140c4180042071040250b522001301b4108441084207403c01d0881c0d219540a104003695040d1003092003115480203000790454681c0156021700a0071112101d034080060310402d015404264150007511a84941002e421581000e5105020454400d81c002d42c481c00180701c0c08000c14192540f004052422620745400800040c064422841d601000d011410340d408040b80b0b00b03100300c1800340c140b07500213021250070398a0040c05400f43e07040c09803012204145883c0d01840031802d00d103d654015180e540d4586049643c5030b84110119080030060040c1c0c0380081c94500150140c0080d4070401c001107060180400b000405440045011028980c1c00c000c008125103624000c5c40c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 761825647 1250 761824397 761824433
    0x403050403020d0c0f05030c010504140102030705070f050315060607230d09030b060907020d030c03180b0403020601270e0c0901030c0303091215242304090b01120f 72
    0x2140d85803819010500282d4550480c1f882600400700480150740c2c41005d95040310400090b50b26881d5000005034114860a80003600c6400740c00000318110840800c0c010856406a0407507203082c5c05008003901c42c19040d14000d60061040200303a022541ca08802d1083d401c0c04900350007241540c482c2c65250003484000c00000c42c0c0418030410501038401c070300c07560180040d42c99004510f451000252601c08000080090659840c8981c0144d44a90309c4249000d04454124103000c1181c14140080390040310210018821580081000c00001d0440c20841c000c080e014003c0010000009001e0800785080307030054410115920706507603030364240d1802103003c0c100c003501090560070000c1c000340c0180c001408070b040d60803412000030205449005a00410303100020035591040f07004800c034000e108041180e070407030f00c070100358506403e0b42800d038002e48028003807000d0140340c1800160358030001c1c082c101c400c10a0040020b0050083c1ca07080d083e00c540c6c01c104082c1e0040e0b44541111000700441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 761826897 1250 761825647 761825663
    0x29150d090312020307080415020d051801290111010b0303040f083a020a060f060f0e0603060a02130801020408030301141c0611070f0b090c09010311090403050403020d 73
    0x400305040e00840d00c8030345000008402d6155142c1040054032203400900010011001c2d110380340c000c0384250341600e00201101c1c40500c51402c16043c0c9020304040481c400446520306280303581941180c0d1300c250308811f85c00540030703400102080152580101454218015500c42465904c01d030380c24401000a04655455042c040d414a000e0b42d150841d01c00a020084011010a03400b084003010740888180c4403008125001c918101d0490614500d003c005000c030f810485032010380c40315500b040c001e0b43c0381105c0c00f00b1030aa43d50a070103c00344007650081d03055040303403022420902080c1c0040100c1080640424a440c3e580c05400382241d000b030380000c0c01a007000c401444482541766080d00001c4084882401d140d00b8003c40720a4011030b042e0040c85140c2c0c1e820701450b03900103482a1010740b0f40000d40200c003400c040c2030480400004850b910124000c14108501c1480c0c1115618181c83d0020f03c90249038200e0024003c1402014009030140328040c000080180d849040340100325218081c030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 761828147 1250 761826897 761826911
    0x606130f060215010b07060c050c0a0f060c020c0d02121501030b07120603110f2b050601150c0f0203120301060302181509010c0224030906070329150d 66
    0x9060030f40007588144080000e0004010b003001200654002c0f1b50002000905541c184800b41c0340c510550186001b01e004039806501032000318014011980e014002c14000101d05880880e26410030105441e0f100c50290f551a003d400c01811518910032002c0445003107074a02180035181d04070981c0112501c2200e94208125681e005c0d041141d000c00e0500706200c13040c21a070741d400b100306401080c2400b4283ca5540400c0c640e54224410074500032039a000840440700a00402c83c1003054030041d1b0b030621680d0000900102906070001600600b03030384404400c03000ea40d40900d5040e071030318103070382c50b11485120307010260f0740b0340c01140200380750b8900594a022240c040395a440c1e0403001c44c4d2140c4c069880b01000040325400300c5007200300074a440200c40003584009a1184603440b444c0e07030412168000080b82c013500340001c0d4090090003088803043c0c0d41d403c801b10151a120582c0450380706100f001c109d91030a18031301d111411100184403042c0c49079002400c19160f007220740300c201c003a40c580503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 761829397 1250 761828147 761828159
    0xb0903100e192d0210050d15060e0a0515030f040602120a090201020607080603030f0f04031a09060a02090a0e04050c0301050f1501170106050a02120304030f111c080606130f 76
    0x10340000103c943c1e80105640756030f50000b4442c0c2c030954181c00e0a00c1800030390105035031034035030011022000ca2900018516204c40009000c031068042c1207000702c814400c08101868490120358095512020241c6960395010381c1d04056400500121401da030240818004108031002e4240315041c0c002000500b081280002450f101c00500640c003440704a0050044546001c0f00700c60031035500c0c00c3e0095990300040b00c0a0118407070b660000d04890904200b10150141000700780d170051342c1035021200135440754901e042c03c900c100c0030115440b8950132002c0154070440408207912034001c0f025034a400000c00040f9094a50490341c492540d0090400c100b050004592500710640e020310f0040003100400e0400c1c001c2c0070040c0903020a111005c120000740510070825814550180810180c41c0e06040c03034080d00f0007103103200c0301010460518418814170400218400c1c0190100400402c0e43d461302d1060702c43c00405031210b87c100c5810429107088100c203150040040000303098100000b03103800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 761830647 1250 761829397 761829443
    0x304090c081017060402120f0613060b10020a0f020d020603090a03120c090905270c03060604420810150602120c03070b0a050a060b0903100e19 63
    0x740190b14002d0f106101e454101d00d00098031503001e40e0544003803485140348180d491a040c03104000b9055880f540b01041078038240c6442003048030381309100520501948204001060360068210360040c0d1000c00b2071004500500a074960303482c000b50002090912130340104809600440304401680e004a41ca8001c26030b0005076030407040181c1d202000380040b031000003055208581310b07516402e0748407c00304d003000e483c100104000407860400240c444012107400d0392119242c102d402d120b400303582d00043c1c1c1400d060207260340382241000800c1c8440f404607240c2808080e5228001c0480466103501c1c0480902058644041c0240c00d004201c0710702d6090103403094401c40f13004c4000f944208141003000c03e80000304402030f2070402c200c0680300c0d00c0101c141850343c02041c038042c0031565a0381c00c1c0140c2c024a030b031090303016080110062100e01c2e00d80c0480c11085c401c1c00f94141d0150300c19020a00c00701c0955001038800101e44060352807082000e004a0300302141c000b0192450039840c180d05484000d18 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 761831897 1250 761830647 761830649
    0x9031e0607030f180302010c180b0706050c28020c0102120415110f0307200609060304170a0c0b060102010608030417010603081201180b0109060e041803090503150c1602030304090c0810 81
    0x50820f400c049d60611165445602032030000501068543c00030400c21400341043e11118680410182d02107039402e03000c4842c2c01c410041e10b501502901030402c409501c08241507400441c0c05490341e180c40d20305008100c4035168107070785004004c2d40d90068419020188002c45562484100541e1a00e030b040c20324240114101a0002e482e05581e100c045494031050156449500100e6070701c0d840c1c0e61907003800e00844030480125201e06c140003030045070542e0001311000205028402d5018242d640400580c2203c449004406666006110400601228211200c0a82100800417401a507640d4490510b50800b400700700005040c134005101041c038038201c05102907031000c814482c00c07030002c0010302411b4240c0203031401c01041e240070500c641c8540d0002014280c1071012030180c41060b080040054942d805600e03c00d01500103120103070139111404500804039a59814540703403581d400400c00c010183c04c01c80e0180000c0c04000b80b0b078559446501700c03a040c1c0380c4800b005460602a20b9502e0040c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 761833147 1250 761831897 761831927
    0xa09051f0c02060409020c06040b0133020a020604032001170114040207120c0201030b0d0b130501110406180501030513060f0b100509031e0607030f180302010c 70
    0x4400d1108498a000030352000d285001424407a6900078180041003152080f40c2103c20341c81c6c0005040140c0b1000081d540d031013580100220345c103d907203428400900000503085210600c0c506018041d020b05034001ca0305e1074501e240105c60034103c6990200d0f401c0e402981c800e98070320600d801035001e5481e082e0340201b000c00003481e06d031604445d40320b5041a0b002040c01564040649050f12080c1500c440c0c1c1255001741e000341c4030250300c5281d02002005608004400c0780003d042003552591424004101d68030142d000b00f1106240e074450350f03079103450b0b142801d05552030743d2107000f00c403002c1344414014005030125696a107290b50718400201d074080050307440541014503181c00c0100908440751510840c543c05800401c0c2103035035040900103800745c48040c581c0070a4442d185814a074105c00185165001074099507084200950340700706c000c625106001443e0400400503082a00c17a6009440b03200070840d001030310401c02702503480100407094003100513070340da155040f05d0356030806001620302c80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 761834397 1250 761833147 761833159
    0x201020c011e1a03070b0c211c020309071715071d0a0f05060a0c02032e02090307050112060306180515012d0b0d0203040b0108030c03070f051609020a0905 68
    0x181e4280420745d00e00862064900084020a40c03484040e414403c1c0d00d2000c0000f90300307541c03807402a8a1550180c0c410401c1030a11414503002103611a83ea0003501d126100314801b900d0254500451754030408d4841c000e07403006000c0c0541c2d00461141d56100d190140030181d88403001f0400100000501c18800c0c0c0d0b909104652202080000780801207240c0d0035034000307a800329118000050261010286410029898005c8141100c000c00c909070800000d0748012800c9102d1159000d141c00881c442d000c1e000741c01d908400320034440c5501813440c5045401482d500041c406507a42c483d0822255400d81349503088100015640074802c04000000000c1008154070300e440d4503180c200c4c03c030401210107c0c069103454003000d1a94100c24402c910080c500304d003049075107a050022810080d4070842c4d045448090b41030010800780340c00002d031240c2d1802e02000354a0580561148a00304141e108100d810303114044400e07004104200e0001c0090a10000150f12940112409401e018941d040b00340681 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 761835647 1250 761834397 761834441
    0x6180501050906130c06140909090105150a0e0a0b0607061802011103120414070f08030c0d0203030411011b0f031e020f060c0309120720010f0c120201020c011e 70
    0x1850401400003210600d0030003068040102420048a006840c842c80c0d00500c480100300c81d02b041034120b10710a00400d41288400304904003082003428460141141c0c0c00b06440000e40401440c0e40302041c1414002e003c13904000660303403080b050701c15803902c64014180c8074007103008550300914070f801c19400c908095030502d450382c0d9003580003020040c40507112000007055110040c105001c0c40c00680842d1910740c440e0341c4c03500d56040e940c0d40495890080b03403080081c01e000151012040d40c1c090355006d0079801d00c44400e400116a51800035014001e07003c6500341040003d1060204090700c10320a40320400300c00c41c03400c07035441c64140d11a505015504100300c0443c01303040225400e54052600e106194803501d800080034900041d80c01c200c00184070004a1406100e2200f80401c1e1514005580104444800004450002c0b041d0301e1036000ca888a41c401d0001050040000c006201c98400181042d40740314155081d12454003800702954180c0c804105520003501035854400010090080c3c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 761836897 1250 761835647 761835653
    0x5070507050c0409082511010201231005040507080f1b090d0819090e3312061806060603040206030708070e031006060305161b0618050105090613 64
    0x54034200d8600b40c881c0d41c0c0c0749100340420402c403044d07070a4003040341003190202250540034113901050240c159079480e4010180c461941c070500595140717104401c2c1411440ba01d5800398030320114054044010302d12642c002041750f80b03981c41801d06c04c003000c3e0395801040c2000d40414504000141040411813442414032070406811012991601c60036107102c0341100c900c3c00e00ca141401003100c0d03c0c84d4a01c21028010301e00354482c50b42003d0394024148914180c44000c110403144100c07003003503105509110400d40051600541c0300c0f01e42e150140c130a22015842c00f84450a0117012a862000040c0c1c060701c41e042e44000b0415150b0112094422503d5070809800103680c44c0401400f40301008500d5000032005840f84071403108244000e011900000c3c07500f5030000281c0420300445d00000d1400000842680c0502c02c084612645501c2c0d00740e2600030303104d0420305040c0300f86c4282c50f1103481c1c0d80c810a420341c1060145140078010700c000101418644400b034104100a007080301c0344000e002c180008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 761838147 1250 761836897 761836903
    0xf1218040e0d0e011704080c160e06460806010e06060310081902091e01090536011401030b0109091104020c06010e0c0715020a03060f180507050705 65
    0x58000e1810000001d1090400481c5d40248600307803140081e140d0020b00042181240182c88010582c034182c0d012a50f400c641142040032a11441d01c2e081c6400000c9800b82c00c15000d2001c44402c4000000c00001e41004410b11540080c042c17001e0a001520a80304607950703505000700036019101c080c00e159454144500c4241c41c01511081c411500003003c56002941e550203d001040b0090a980c69200005100300001c0c11084040c4c0c020300e0b001c00080d10301c014150003002c0d5480d43c2c0c2e54020741c607400e00052100502005284140585110460007185a404452031542040744901c01c4180403039004d40d00e09680034828002d00800180d0010300c00141003500740c90555014070000900c0c00001d0074030001c1c5088030402d00360802e1000540401e407a5010628034141c42c4215070714420351700c404a001c4070703610603108064000c80e0600c04010308094550010704078030082c0d10f404a0f400c1e44850300303482e00c2495070707100c10080390020804040a102c107004d20b95101129003031082c00c0080584038592 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 761839397 1250 761838147 761838163
    0x2120703080d05090304050d0309090b0d2103180c051e130c0903060c0804060506010809100213080708030301090506092404060f090c02010b03010e070e090f1218040e 73
    0x2a42c544400024032059010400e8400910004101041d00001d074103003c3c010306080d0003410111418090035500d14200031a001c6403d07544141c5051150704071404805084d11640d00410406888650115850b0300190b00c03007500502920062011625000400045024048001c10311030341c2c1d407412588680c2d61072003000038503100d8500801c80c400d0003401203030b000040350001045c03680b0345042020403552004100307210700e106e610f040080f9200c2e00019104241c0c200c48420340b41e800444444c902e80311382e401416250700e403002d015032035a0310341040c035007007806d5034020b4001c0e5400400108031140a5000b5580c104a05503052012803d104c11850080c01c80c8109900c04003414030010041601c81c0c4e03110300014100c030903801d6035450b19040c2d01e0707010344034070340c8950010760800c94007010901e0b061054203102d91121005001d03440c608500311701080c074020a0780c2c1c1240150080303004601801c0c48211250301804d0583c0343d43d03002030039034a2460890b4107c01800359107440503907103411800040e005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 761840647 1250 761839397 761839417
    0x90708150a02121302010f03060b0901030e0f03040b1306030b21031b0d03060602070f0312120504030e101803060e07170703020301050f09070b0d02090603130212070308 74
    0x50160307500200c1e94080e1141c12002c04400104508005140341c0c40c5460201081c400d0361400d44030703003585c00308401785e80b028041c0d5202d04004128144166000c2d82c09114401c50a070706440399510038151413410b50f005a07204040b482d2000803020300000c902952070b006020607007010400c1d22500400305120002104429001e91a04019015000010030a17101782c0352000c0c010111084a1519058540014168100201c0e041600c0803030304038000f1a540341034540da042074200c1e852845e1654081e45485191b01014405481c131501410701060055511940c000c0e00e6090901c1014401e110034404403411031402c00c21003009002c80703d40328524501c2229006032001c540e11502071000d5061122962084501c1d20031102491100840030840c00e040b240220000c01c0a643c4030048003240440c120b03111821500080424491086002d010703004101a04c4001410001048080b40880c1d00c1a5820030440b01c130301a0100031494034246a04007540040041c1c10580d2860383c4e030b8405070041541c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 761841897 1250 761840647 761840683
    0x30a0203070c12021501091806021803030a05030907050d0b0a0902011b03260412110c120303040c14030a061d1204060f02070501050d05040606051f08090708 69
    0x300700c0e03591054140c40d01160b040101030401c4001890f01955801c4c150540351030311214840000758113a80c500c12440c4c0340e150a00440d014034480e80d1600d00961248105160b03414040d0110403560700c007040980001d26440d101c0e1562802c15861003407400c00c0c254409071252603076007078500005081d00b80e440d800c0405074a002c60340100310320068480417400c580340d00d07040007040700ca5030906600000311146010140840280348003016000100d00034111409070083c4440314105802d0381c0b10362005000c2c62407420954890041000000c1c00c400b81114018410303910200600050064622180005152521030010381c540032901080d2103011044011b46220784e00c00700c000118246503001e04920741c000781920480742c184540741003550014002e03003000400e0300c0d08480c032032400055207a056440517110141001907580300e59010f000c000b40308541e02a00d600c2d000a142c0c807a40c04030034022644903524681c40501000c01006031400030512952944004c10400038175074040f8048021400060f11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 761843147 1250 761841897 761841901
    0x3060b190516020310020d06050a150503090c03031b16030c120f0210081f0509040b15030a060204140a0e060103270b01050f061903022212060510030305030a0203 71
    0x1460b0242c80044001a400d8010030740e4103a148030040d401004c28000c028400c00c05a80c80c1c44c10302609580034080c1c00600c7c00b1000358220007e001d040a581d00000407400c41c5e4401c04107002007070460b0450a00c2e01d0500407152856020040140600215458140301c21510b440c41c5440c0c50b0140c20007486003100345a4a003001c0b0782031190041c01d0400b0141c000d4406840c40c58440310045c00d800c0c08803a0188500643d0003055944071080c1184000c41b0401003208200d034640c1c2e159541d43c1030000e40041140b894038004000341d61418484400ca00703000302d10058a6a24100c60004441704c4007840030f20501990b0418000c0b101c040f0070050300700314286000038000c0d0308422603400082c000400340f11034038119021320082222001109061f2402a07c5813000c402001084c0882d6000308519002c80d1680f041018008611a0380607006698088462400180c8001000d82e001c007000d0704045014000315203a4001c0c48494001c984e007280320b440400210350701e5600c0080c44c501025000c1050030fa00000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 761844397 1250 761843147 761843167
    0x140a05060f040902070b1506040602060604021318060608070201110d0e0102070c0e1e04350c070f0b1608070305120901020a0206100617040507031b0603060b1905 71
    0x109490103488250700841d1740f8601401c20344c0703680b0800c42c2e149000c032408001001c07503030502d40140e4048031002d8004040320f80319002088044d400c0103484801091a003c00003800548440c0101c1c038807002d81d280080c1c03950904400800c0c000005141000756814260344075110440f070300c2290040504420005100e003c9400502c1c0a03100e0310a0207403203e8081100030584810f040300603406041400040d40d084550b9801c410390a40d002c64024003c3c01c01c400c800703007460080c4d00446425440e01c0c6200d000281c1ca1003401d0302d064204115505250740b042e54140503900b225240c002c007402842038050304180318601c542d00401200c4600410403030010584004060144c41620b4005221468138041480c2c0520982d0003034012034036200062003880041600071000203500010b031081070b600d1040704000001c0a9100345000790080f60144203100780007000c220f1072408403107000141003c48121514000d001030945e5038a82001204440402c1b10614a2210440c01e80d11301c00a41011034442c1c002c44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 761845647 1250 761844397 761844427
    0x1050310050d081207030603020603011e0306020c03040e011e1a0c120306040b0f06041401110102030a20040807060807023d0e0606210703030216140a0506 68
    0x60300841d0403110000b1108100003100010385030508001240c0289565000c0007101030f503200c2c0c400650009010001400285800c1d04206041d0f1680d04000724607a50b0303035039244120703031040f00005010f4001240074080000482c030080e00420241051094a00c61868862800d400910621800500700d104444890040b11f0540713825400c00310544411140040341c442007540120b40c21131081d41341c0600d00c0c095207001c45a6010184001c2d12550030325081031072845030143d205080905000c0c402e2841911408240000c6100308251a00414401115040402003207044404c50896007024482803050f44e20025058085524910301000280c56010040c4c0c203010b80e00300c030b107452840404001d80502811004011f88014031051040a580b84d5500c101c4c1207441c04084815507400420109415280150940080700c1c0001841c1003190741c0b02e10082d140a0650f44102e004d03800840301110070482d44e402c0b000003071441c2500da44480d031513030f800545c010240b03004280c440c00f0f010480c451015060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 761846897 1250 761845647 761845649
    0x50c0d0c1808010504140f0706111009080408010b030607120b1216050f0a14042307170c16320a06110c03070b04020d02041a0906010305060f01050310 66
    0x3074003040e60a551502d0040c2d018101c2100c081c2c1c0c800107143c0510344015000504001005404005084401d0403c001111010f0f80c03554141c146205400b88004c41600c18401c41d02c2a900c9040401e0340c4038a0f0a103080c0c25140c1c001240f0b4440c2d0040c00401c0402900203000700d840300c00503200043c072107001600141c01c020210801e42081d115002010084440e054008029610101c604c505000012400c0000c030f0186401207544503e001d08602003203062941041d50784041c40d008441c01000c070090a10401c440c00ca42c100005915407107480599800305500f51f4201000041881ca004809500d01d11810a540fa00802c0031b40109800806c5088075807502500e4402221111072544d40788141c0d680e02e8442c0313241543c0c02031406000d141a41204812200e0b40300318100510304102c50390701e42d694660802002070783c10034654504100140d445120b288a0410048101081e08202409002d00c1c180c000b0410b6050614000c140310381c40e80c4038880c2da101040246030079070362903850707104000314031000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 761848147 1250 761846897 761846927
    0x30406090b0405010207060614014b030b0a030f2009100303200613030c020306011508241003060504091101080a151a09102001050c0d0c 60
    0x1101c082c0000c03c103041d001060180d00403801801050340b540007104144161210090110703a1240e004400006110209984e020603d08505070310303a0307018400030721421442e0891107d25099003001d0135050305880b0b803001c4048107664200160313085540d910103040c8016005028403a000200e031981c0700030000420700040c0041c204071020300b4014243d640203c90703800210081288180f06201d409001c4801e43c04843c04440180f005d51907000406102980e4588254108100c294502015841c100b103503500030130340191243c500803800d050003458603c0280080c41451081500050b00d244406008198510304480300c0c008500004025001002150701c440e4210b400d0010500620801c0111484002005c2c0c861904d01c0d0384900d03140d001c58151303901180b0814034000c1c3c01d010141581d481c414481000e0342400385014061701c00500201c040c110400000b6030351040d1404903004007a01c2c120a500248028043d0f403c100d0144d8440e400b41c1005600c0341c075551190721150904c6003001d03000c0707050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 761849397 1250 761848147 761848163
    0xa1b0605360a2c0402030d23070507060e010203120403180f032904030801060503191d16140d0206070c080c01090f060c0b04060e072606010302130203040609 69
    0x25944510080c4000c40f1030032000c070042c000070810384050700d040840e441245d009000c1c0000c83da1852081d02d150b0070380403070101b00000324401003400300718280041403003e0141006060003840c00030001c186050a07040941150070510a25014000c1003400300d41142d0b0500b060700003c030b43c403004520210901d0f03000f80032000c10140e000082c040000400c08070140f041841780c140403114241c1c85080744050703900900045078800100a5a44544003864001c0030461104204580e800307c90701c01c0e20b8101e5030550003440840000e0f6860901003001c100d002d6102c40c2004007071440d242014005d100c928145030301034409183c4a10031940c58104561005a025049900c2581c88480041d42e8071424644c0c2130100d00e0312240400c015032841c15442c01c45200340e59910030301002d995010b0f10b410018208039600c2d911041240300c05507080c412440503260700002d030000c0b0f401c143e10032001c1d14009d203c0389515800810061000d40c54040003008824404640543d5070344540ca0840001c01c4400c0010300740388 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 761850647 1250 761849397 761849399
    0x6051506040f03051608120a0302071211100507020d030905070306050f071202040b16060e01051e1005011b050a051e0114150d0c080a1b0605360a 64
    0x40b007808a40750549000b4421210541014401d81403c001d0602590000c3d0b40010110302c000000c0300c004000c030b264189405414052a03994062400f40c04135416030102d500c450203030740d40b00c03400c1080c00000f465001c0c003070180d4241088003a4541c08461508400c06031505a41c209012007040664003d55114004000b145009000004059410303502c43c030004000c045031015252140c0243c50540e41d030720400d07a240811040b40c50380c0d820502c01d01120116120b41180b181341000307110b0710b07100f43c0c01003100c020444007580c0d806002a200400002c504418001e05012030b90303219902c4022002a0301e03150550307842a00344203152680c1487c00130514414881c0001d48080c00002d4010182c80301c800900c550341c14035885040707809045030700c01c000015046156034a0714150034540301c0d80d40204202401c45454080545c102401c10304140c402500d0b031900c040700c04180c0101c100003440e0914213a4140401c00401d1118002e14010101c400d07001003a00500204052030b030019502d4005000d85249 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 761851897 1250 761850647 761850659
    0x201110604030305061e0105030a1a0306070509041d15040f0c0f1d060121020d02030f0f06030f030a140903010e0703051204030c0326120610050c06040605150604 71
    0x1030031084410501480900450341da02c603c046000446e4428143c55450a43d603500301310070024615540e503560411415007034010303145c60504c0f00740d0007000d0300d5454503983c0c55103005010039221f0041c10008403000034a8505002940802d5041a25007030303214181c0181c4441c145011000c0200401a141141882d00050180790071210f84080340c0c0020030550395010f61903040600070308102c4d8614041030f5016401240c0d80c0800c0941c00203100768a100604207110300d640e20007203800c03c40d04050700840203014080c0c3c2210101e81aa40f221084005000303030030095207010340302e0181c001c3c088140812a0b403c40e079860041400e8036607809001e0020452240c0d821100340d0f441038244403d60b1540a041e58035601400c48504803400d5903041a080c410b22403550303658401036600850020140c48107002081a014001c0001b00305040304a0844286420118104055440c9103152802030140c2000400e10031a03001c60483d41c4030741c105200040c86d644003070840c8820a04908880d601c920300090200b21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 761853147 1250 761851897 761851901
    0xf012f0703021c0c05060f070e150d0c080f100807060507020d06050c070318080d050c101103101d0f0a0e060901090c09020309031606020403020402040f080f06061c02011106040303 79
    0x142c5d02400c1215030030385800402140e507143c1942c1807000078004403c41c0415003002000300361244d0384412042e140410611101d411584900f1286001420701400e100420700c80001064100100c201268405440d05c140c0342c0e0380721514410041800b00103d014019561080294605a034002000f0322052034075030054010750b440840304501040300d201078460710900096060f0151901200100742c02e4802817030a0b80c140d00005032580c411700c81e8100030400008240190b0b0760480d0400740c002e03100d0902502c01000032095401540c0000004601106009180300040b900003030050615a501c1c1c80d8180135501074000704c40a0285ca10a41e0103000359800d0540c480540107014900d00d00c4c04a413034880103820380c4000d0b90419243e0f48248181c40015a8040301c64030041d00c1480c00500c0d056503540444c0c140d820035032104c6161812040100042c4d00705000c03820091003020050082d600d4044005001601021030400c424003403981c0010843e4015036004e031000050804884061034680340041c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 761854397 1250 761853147 761853167
    0x91214010f0615230702040608030a022109010c030804051e0606010f021b040203191e060b0304020a0b090a0e040f02010e010503010e040b2203020f012f0703021c 71
    0x43d40081c3d490904028900c034111100702e40c0644070705101e1800d88080d03482031030f81059000742d0f80141e4800001410303600400c0103008034071580e006000b1200e4001c0c40304d0340800c810170755982d91403000c1140c1d42c01eaa91000c075036501d07d0760504000781903807070b503082c02840e051946c1d0b00003620302185203480f8903442000452500c41c1409a80e40d0040e0035941c5000c90b241c001d43c0c50030b40c80301d10442540070041e03c1c2a03006113a02c411502148144041c841c100001540e140843c1049031340180541d0408a14050203140b001d444015681891810254049843c0f0b0071184140b1188010101d80440d0f95600c0f00451401012101c1c41242241490b0525410380600b92408a0220308000442d4107254000c10559041350044000d24646559070307211704100400007040c16250102d94503000f0329840940d400d40c646c0d18000e0307006000740c1e03080c401d0700750860b40e090101a0310384e9900400030500c0d060307901440c04803250a05a0a4a61b42540745c16072914403a40d40c200c0103465020015140ea50b48000c0e401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 761855647 1250 761854397 761854409
    0xb0a0f051603031d01020702060403021e1c03030c1706130b0a060e030d0c120f0207050a18050919060b061213061103040b01060309020118080304090e0d091214010f06 73
    0x403c901c1a449615800c0341f25440c0b009401041c113103c20805880e0804030442c883d9020708600c00d56045804c0002c54101d006072850381003905124032001819814801d410007003005080c0007108800b603a1a00c5054403000381154030500800041c0c1d000d160316a040240d10410241c00080116122203001d08030481402d101c038007034030848155080d036511501d41030310880c1c1c0144c031124141d64140401c550a03c0b184405c9419480340240000d9a51100907041c030040c01e800b01200c035201180c0f081e000c280c0e5000380181049601c20703000c8283c4040701d95a40344101d0744c040f02c0010b900c20308501040c407a018111850b0003000000341004003410700360010051440c401c0700e081010440c2c511807400180420345019090f51800c000502026000f43e0015082e280141000710001900a2600e1014005a008028076402c045001c012225443c02024242141c500181442005d000001040100c0707500c10a03113a000c9140c03215040c07022801d074031085c0e00c19a4000f1300502210501c200040d010074401c4e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 761856897 1250 761855647 761855681
    0x60204080c1f0503060118050d06020a1b030e04020a1205091e010501030b060906030a02100201060f050604230d05011506090617010303120b0d0507031b0b0a0f05160303 74
    0x303500e005800c607402e00080e800e51501411512181d004594140c41d180345101c001c0030b1020041102da4a042d020304040780b00d48000f41c1d87d0442020000c1141d2080e45207610b10310803406910001a030030106100300d444094a0060311007500307031011524219400150703030426140c00c052100000c030108868910100d9401d0000603107a5100aa5080310024131020341000d4040020138081d10700056040e803c400001c0440340b40100e2a0006100100c0307002c28140580e66440d4200710442c0a1040034009010880d181170030715141091102d10b0714005020703409155070020540440b66a0000c880c24030b183c200c0000c21218025207026100702c0c0c03450003100302143c0c1d0703880002859031240044204600c2a0007000130281d2031176034241c94101d10345072041d005640b200c02c0100d194070b40100008017580560700400b207907890340c18a81c0c840d02803044000c0c000c000f00030003808444602400c44250788000c2c9000000440590310407140c0c0d005885d8103d0360003ca0150090a140d03241e040000340d07940f03010708 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 761858147 1250 761856897 761856919
    0x304030807090f05010e010c08030708010509060301180809030a1401140c090121180b06040c0237020d11040b0f0d0807140a030c0b0601051608090409060204080c 71
    0x420345241c1154852503c40072100041400325510510b1004550030060400c00400c420320f07600c16410350401c480003000514620010021450644092a00184190001c000c0340565002000c01d039802c400c405030103c480013504901c5078508001155034542c02c840022804405040124081e1020000da050404031640104840003c07030380460f104450141c42d0002c2c2c880807801c05108041c550106d41c80b5403660740454950303044400a0070425039226850f140d040745450000c11041350500301070704c4115409030100804d00844200646c80300303040c038941e01c0f007481e52024403e1b061080c201402500480d09903a40002c201c0380600c0130000e0309040300d00f40103041801d020300072411041e000d182d03070160101b1a040301140140c030082c00c2c6140200e10348030f0106c01c3c3c124070910b0902e4041048000903c030740d090006103c0e0913a0219000602481d1452501c6140d11440385140490b04000c0c01c0040b0008082017580c0e03695008460b016030050042d519140c2c1c409499489502094180d1701400702e4000b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 761859397 1250 761858147 761858161
    0x524031c050d052401121b05040f0902040608190908070803091e030d0b040209030f07032906040c170103140c0612150a0b120103140f0c0402130302090c03040308 71
    0x84c602038183c1150302e140c01e000e0041e004440303d0442c42c600c0100c4650b51100044100000c021000f1140c0e5592560707591140361005a02c48035080d948405c40c5544140814880607601c00780c020f4010b1044c05c9101100c0a403028484d004140d12070b00105010f000150850400011001451082c1c11040950b258001f000156111008901400c54400c3e0030802002c41c024882c1d40c0309115803240900014107180c0100b000c00d1414110904c42200b640c0410340070070410080360b07001c00c1c100924800e09940b00c00f2050540420714030141c4200d02c01d945409000301300e94850929404d6102204151a80f29607680c05c041c00e040b05030326405a0140142e1320101074030300300041210b00081c0c91b8601c610059440b81058907640c9a040c2c40381d64421264040003031912550400b910901444c4007207100a549589005500e5104000c0b6800f0b41e9003044c00700316410b03800810b484103441400c0c7c60147c3c0e40c0300c9041040c0e03040c0446030002903000b4079035020b000c40381200c3c20145104030722a0b100e99960303490b810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 761860647 1250 761859397 761859421
    0xc0506070210050309010b1503180304180c121401060206011509120f020a0801020a0f0309050a0609060f020a021b060705060c0a1e110c01030524031c050d05 69
    0x9803020703420035003181c55041c107148900003c40c5e10450800c0000341e0080300c440054110f4030070504400258602000f40322418007120b1071400030140c01001107140614042c420310780c0d00c1c402020341c1103643e81e40300244032060107080d80c3d20450100c803204210013125004290101407080c01040010b120341400440c0d0082014285648440b40c0d40324405010720b08602d0028004900104654a552111030500140c0300e090303109018011200001d61140e409410003004807d520701e40c1c030101030070403502c0d0f4003103003011a0061155400038070200d884460350806a029100380224200410f100160340200c20394003145203003a40480f00c140c0011401440d04015260054001c050030540001e03000c54103121000000701030015803400c01d00009030714004403140d424038a1030307840c000c110070880300e2141540502003402004400d01b000c004504020700861022003210b02001c403031036450720b2400c0c2d83e6601080084070f02d101c002c049214041440c0401440c1e031300404c2401e0101800c013008210344c5007a074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 761861897 1250 761860647 761860657
    0xf0403080a09060e0d1103031b030c010c0905010807120603020325051f080411030106060f180605030114040b03100603020a080604211214061305101403190606030c0506 74
    0xb441700c0c10f000080d41b01d004007007180444141d40740c84104044555404d0740a113460441000101454980320504c9806094483c034801c0c500400c0102c035070511040e81c002e58003607000849032a0181d56101c400d51560010526038102952604c01c0c03d45142c0c1c0d03401168201c2d9400c07000e5044030030791144d48009101a03481c2207180c0405000c119010746e01e50a01c20300705c0d99070040c018a041240c482c81003000c42c4c01c413003454002500184040760704405140e0000558048d100c080d844104c0c03110316000c002006400f06004544440c402c3c0310140d04160f5890b00030310f004c00401000d460411403413801e80d10080c4181e10080340116002c3c0000541c440300810b801784601c1d041110b042d10351071b180481e5086c0d0b166a4484030148800001c0c10381d000300d502d11400c050918100304104c01410960208201441e41d0781e02d400700982002c04001d19a0a1201e142c021036103101c400410050080c0006800c0003082403003c14070212a68070102031011503007000381280c1c000c410701038040e80c840c0103106d024428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 761863147 1250 761861897 761861899
    0x1312050a02090405071a091c11010e0105040509090f061003200a03050102160302012906210a0515040c051210080307050a1b050d030c0302030f0403080a09060e 70
    0x403804004026081a01c1c03010b600c035224034152450661100840440521944010052040045462203441c00d000540c01900107290341c005a20341c034a9a50358003941d80d1a01c800d410004001d00843c4580d00490684025201c000e0195640f4039200301c140e6500e00c6c2850350403000d4443e0601290509036003411001c1643c5e08101c08000c82c405020f403013507000c010301c00c04c00d420014821001020403401c1c8040d0181c00700c08500c086d40070701207041c0207082d1040140d03003088184141c080f150f51080e21140a0940480c183e41031900e802d01d132000c4032101400d84003000e044526003000c01440c414a80d02080c880c0b00d035400c40d000f035a500c0c24203000484084807174444c0455020850366081a08078500242d11242003129500e5154544c2c0240e03003160458242102e00f5880b010340b690400c200d460307640c418141421119800c035440c180c00502d80c03035041100039062142404450051600c28402c88058460001d0425544e07681c9160000483d481540501d00080e084d01020400e0362281c1040f0f010004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 761864397 1250 761863147 761863153
    0x182e0c020405280c02100f0e06180a020906150c0d020f0105100e06042904060b0f0906070f020a03110405070201050c0a11030720330a17040503131205 66
    0x1c4041e00f507038020950204d84d2015445415440c0d594401c00d8001c3d4003c4540d0b41c10080707503001070341c047d05203002d4026040b80103c450385528581c41250000361055040d80444d10010301e902c0d6080031a0304000610320300201c0030b00c0081d8011140200080b00d08000a840c1d080b02e000d40c174010641400c0303a40a865200790118007a20800107202c01d2031009800c40001003000580142101c8611001d021200c1640c500c0450f028419645260a200f044004c150b031a111900d4107240042e0143c40d03209013a1020312403840440d0480c18003080c59840f60700d007035001e00000560f80d20b0741003c00403040010103442c811414000010040c51060152900610710000441c1c1448410002954103004418115000c0c2c4410700010003c9110034031414541c08041034907018240802e0300f882000548170002c4119802802d514541da491108a2100d02c090780030911900c030400305400b03d60941c0091080081a0b01450a000502c2070210040000a2110310080e0280e66183c0c005494204d00501c00340c00f60b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 761865647 1250 761864397 761864461
    0x120304030c030f020c0d0b07030f060524120c1b0318211002030603010b01050c07030803060409140c0306160909020a1718060a02182e0c020405 63
    0x3030140100061400d1a801a5020032282c000806c10140c03903e1410303212840000c082c046496050320070200545e6001da000d01041d401c00300800d0058016908202c08407070719121589901004600b56001c1c0c5c041140304451a04002c0d25444998100500c200c1325442e00c1c41020040f00000011503800c0c00700d0030703640000011100d0400041d107002d011103544c101c1c0c6206203030460319030510003100c000d0504074006880c0d052840c245401c4a000c9003140c1d0600100b0468008008400607203d030032658841e0b2625640c4e950400445c2c05000c04040041540740419810400380710301185c0e4101d010815400c4903466034644030306445d40308401100c81c020490f4a007003401b119806c2d1b002008000883d0034020861440c842c031200140d2000c451070078024803a0003050fa107148040c410b054000c481c050055080c400c0310403900d0700403040c106040e40b2505910000020406203061100c5440049050181800c445240007400d03000b1b04a00032403145180800090300301081c0309061000c1d08140340d00345021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 761866897 1250 761865647 761865653
    0x6010b090d2301020a03141008070902030406060e0405010504170a0504060c020414041b0e060a1806090c11120c030913060e04150c08090c061606140702120304030c 72
    0x648000c000748040c000d203482c1c0c801d0300b1903400d0000b420408496038000480c01c0c03110f451040500c0c8051300b0041c000070520400c0001213800a001d10a5030400c08005036280c80e58548000140041c3c0c2c0700c0c600018000081100340f00b010352007a0b121b24007404a1080700d07100806850440c0c0b1070602c0d904046031040c0414401644120000420306102500005520b5100e22610510440488088401c3d400c00c1f411842085e8902c0319400c0284a20611014542403d4001510465890060584540810421b46030200c2250449070051075141010050050040001032003242810650b291511918911054141410044992284406014500f400404010407500200c04902d04c52515280d80b00852480422054280924418001c0c0c0d0900c0c98103448a03401d0310000000182440a65010002408000303d010101c1600840781c41e079442c0c071071040441103d8041800985054540250503850315000c8058502803c11a000c03105c1000e1940100d0b1303034901c41207070020001b440c250519800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 761868147 1250 761866897 761866913
    0xe1e100c032f0a06020702120303060a0509061816030c0507050706030203041719030f051e09070f0b1308281e0507140604060c08030a1d03030906010b090d 68
    0x60800805200401c910400650341c980007a82c0c3c000d4941c1035000603800114074004400c00244c680e0200510b085182190001e0345400062003030502491008000610960701d50b100c8183e0b04c54440100045418030072034200340500c070202840e01003031802c800070364040d00880030340740d200340d00070020540d441c10500c4c114040e4202400840e165140e00034540790b5100450b0240c190900460385584440f101d0400090550358411440d40c035151910003400058a45032400d80c1030780d17030355000c401c8164844221040c43d00d07020764090640310161020101d0825002401030030054622400c80740318035150a0304541f107030007000402412410403404a101015820001803110740207150100c00103000700c48203e81c2d000301d4a8111038a400a01080c4540f07541c2e0f1000034072002055460b54101410814054560003900c00c6c049d11b8144080005681801c99802401284401400d50f0700c0304114101403076039a4205965040682c0905c01c00403402c154881e00f03459009100505140748100581c0313030461 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 761869397 1250 761868147 761868197
    0x109060c08040b0705070b030c09090a0603031d0a12150c0e1012020910080406050708270f12030702010e010b1309151805060f0c190e1e100c03 63
    0x4490242c6c030350018201c01d009014600c59143c103041740341c0c1d500c1544200f056007100200380d80b5000f0318040083c13000ca544540195030014911060b042440400c40025650603241e6100e00881c41c0c454142d5400c0101001098144030b81103002807081e05803500303055030002e0888007503641106041059400561181b003d5245250070300340010f19029860022031180e1150b8039061000c990000c040c0020001c1c0c52048680c000d900307207800c90150802200319540a02e141c1c1034055980c100c01469583d122050001c100c1002c0031b41e048030200c05245801c400c031a00b0440303024003d0b5181429140c0342d0350040c0200424000000c01d4154505090900080240101e01c01a190380201c6074018908505038403c00741045202820018400d4582c44e0062030b100c00103040c1c000c990f21140910421402d5070056601c581e05030004200003c815240445012400381076165100b56440d461109140f041303202d95000d04001c1d80e440c80b4020700a5001d96004d80c003040d0040010342c60520400c824044286004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 761870503 1106 761869397 761869403
    0x5013c0e011e0f0512030f030a0b1018090c12091b12110409081e0301061e080c0903010603020d1109340e1e0109060c08040b07 56
    0x403c0001c03403881040d005103011000207080c80010300903150784014517900d860326460300508140150000c405040d011b1260950516882c0c0e10420b040542c049181840360a443c2c40c0c03072255401410701c3d8441d0300c10084082c00c0400300260a0040690990044655410348404048414003282c099071000100541d69840040010886181018403101c2100c00194030354003800c00198520802200f400000885400038850320707100ca01942c1603135200d98552991000205041e03030394200c0c0d090700c071011801742e200003110707a011300700100314459001c0c0001c202c3c030717959901060340e410070345004507503400b242d03403080e001400c01c2014240c0c40030369a44184d00000784445102251402085500a03202c0889040d082c004d00581d03282009a00c0908480c0c2d502c0d961045100c1122640c01c4601d000805131100000c0d076500c128100c10359560490314061815261850420b902d0340070700011 = true := by decide +kernel

theorem cover : BRFrame.Cov 761690647 761870503 := by
  have h0 := BRFrame.cov_init 761690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 761690647 ≤ n) (h2 : n < 761870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
