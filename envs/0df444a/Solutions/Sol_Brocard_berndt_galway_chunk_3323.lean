-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:25.869729+00:00
-- url     : https://prove2.me/submissions/8546592a-ff5d-484f-b14c-9526f3eabf12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 597482014 ≤ n < 597661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 597483264 1250 597482014 597482021
    0x1707080c031f0902131a070b061c0c05100e0604420206060414180316060911090708130c0308071104141504090c03021203031605130b0d 60
    0x181c5042c0c00b030700c4064950325290042d5200c0b010341141c110920002082c2c010054001801c1206400352092404295558800f5411070040006522000c9504d031038400102070454064460710a00721038064030b0a050030001030003000003421003008041c00c000102600d4407070896094402484500075003854500021410400e074582e5404000d421620300481d1103407903440804207907699000d45246541e1001800101c91900130399460812240010480401c400703030981e83e02000b500c0a0f02e140c03510100388404440103c02080b130319603030744168200038800c201c1454404444c0880340340fa001d00700b01c0e40060416002400505d29804040c031413004000b8100c840074001c60f48035040503101c51060030070403485404010503a00860404100111482030303885a28400c0010040e14101200507a00b808000e084203c1c040b5440d022204011000d40d032004c01206042a15000846d43ca1a02121000c030b081c036061000c80921605010303100000ced10020750601aa801c3c10b502684401d03800c074445e0060b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 597484514 1250 597483264 597483301
    0x60b0d0905010b18151c03120b21150f01061823131407030b040b090f0414010603051504051e0303070e0a0e010611100203010b0a1707080c03 62
    0x2214826070801c4a1002c008144c92040344a41c0e6000000360404007404060105000750794480344150a81c40700080c060003016040103503c50000480520190100386c1d20703400b00d5034003851800c2e911001c0c2c01d18807080001d01400c0c1e440c00d403040d40a09085d4100680d0f40340600400c02403002d000482da0000e2114003000c030003081111503a105000403907005910303076051061402d0040c1c0018001c0001c50308139000380d0011302890780b1004030568983d0f00c210000c103141c0342c07407941c0f1030745550b403850b40c60780c44201d400d000c0c0d070180d14119030b242000c1c90081221143e400e181d42c1c099042140030000700310040f070001d40e074590500c0051041d50340e40c03400350705201d5403c17072a0030715900c10721031200312400c000091880396080d600e401400c0940300e0100039888619104e5006200c2048006100140c40b5054280b002044042100d004050340c1c001e440c280d070026001000200f00104641c0b44540d4001d0695501140080c90f032030f01804c0c0410000c1680b400200000c02d01000003010440514590940018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 597485764 1250 597484514 597484519
    0x4020622050907020a0506010b1c1e0c090815041a0a06050307080304080601050d080909040b0a110c0604110a121a10051f020325060f060b0d0905010b 66
    0x211448664a0850009641d02465015900e8200003409440c00000c4019803103030048020141a80717041603025580d840460804d8405800a5000280c0d00c140d0151a01101c01c1503540e00b00d41180440352011900078082c44002c011038143c3c100a01c10740400c0044000c04004444000d80e034a40c141801c864001441b001e00007d0240100100180c0641c00b24080d100100c0a07541e400c1c0c0d0b0b072a201c40d941e001c2e500a01c84183c012600411251400141c3d58a40500c200691814910810300007000740381c04603010303a481e40400e000c205129a152081e000700808191482d800d00300414491a52094000c01c0107080b400d254681306400e84d54009184001c0c08046107042c01c090452070076190041c8603184540b260b001c4680031a282c900100c2500e03045d220054201d01d2002c103030740b07204240d54110941e100190b0204220007034030b0f81241e2400c0301ca00300c14040c0500c021202494032801711203180314040c07c0180307014070074010152602c0440b5006a00d1000c0400d0010712810800d0042821415996 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 597487014 1250 597485764 597485797
    0xc11010c0c091406060f1b12070b011503060308040b130f060201020c06090c010e060d150e06130b01020c040e1218100801080307020d03110106030c080d0c080909040206 74
    0xd1900120f400007461a03001070b10f8804991070301414042940034861082810310000d104540804032104105149010660102c408130580c1c894058281d5100e002d003920100881c030014445826100303141c07540802a850108011032540d150f0030f00c24000c5020b24640ea407030002d0305101034866400c4030005003c00c200180b04160b540c2001034000c0d070002414812034040d4000003510881d010411040412040c0c450060005941c4100a102d5000e21100e00c00a565010180706c220180340210028202c0103014140b1800c15100300b1480600c020940c100550401c199107076941d0340416115110141a2400300e103030221004294100000562040350801000c500c66241c07024007146030800f1041500c00c6001160120341c12a208035003402001c1256000b003003513074014208140480b49545c003a02c2d0040d012510041c1c2182950350660050b038150f0b054100503c280a410720004280882500f44080070b820113949141150059640c0782e8420301c6a03c0004e819034031000c0031112112070000989 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 597488264 1250 597487014 597487019
    0x11060720030c0d031a18180a05010203071805120d030c02010b090408090a1737050618010e060105040c031b080103051903051611100207091401060c11010c0c 69
    0x4c00400c0401008141003240301203000141c101200382018080b1610040c070410340d1801c80da112040341902d040d60f0b040c440e036620400410300070320285000c0c203030315a03410301e91000c2c06d10301501c4001c964100601c02c444002c542d18030700d80c00144080c50b80c492802c0100d80b1f804210801e9005100001c441c9800802d1a010017081142070001868210402c84110b040f8903107515403141c03e000060103410701ca0307000580d42c861904840070745030304034404031200200c0d03142c01149201001c0310b140401c584079444032042c0320b01e104005e601145030380b03885402000b000e1000e81780e6a130381d10300600c5418001c681c1c070526086094400d401511000e0003611003a13486020580000f0452b1200340320035541c03400303142c07003d0a0190041c1c10b070101054240c0d644600381070342e241200b003c00c40c91050844120007403131000a40c2d601d800034034445400d02074000d0010740340b6201d60602551300d0a10768060410000006000301500020f9040980c0e0708200016444048000181e4401d070800201604103601130100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 597489514 1250 597488264 597488267
    0x121202071401050106030b0a0b09150408010b0103050c09011d0a0e16120b010e0f0a0f080c04060807030302071203050c060c1c0b06180a05090a02070311060720030c0d 73
    0x2030000c1e20390070030000c0141d03aaa501c0110104d920350380c801c1c0c0c0c0c4455125810400801d121000e0030000d03800402c11401c020781d400005600b0742c0300742d02050240e51106180b620540e018450f55030b1184410301224038004c10040004d282040407a102000380101003118a15602e8040c2c10304c02074016000c03c80d50b1402d100448031215800300c0c980d440082c82c6c00425540511407801550155441a159104044940c10421022070500243e058001d944e001c1e0000c1c06510820440004050380c10160841d009110144419900c8a030094142a485001d0410020f58000f0b61001120b15140e5076400c542c03294a0121800e00c980a01c0700070510034034040c451150341480c000e0414590700d80d48030a4000b00069507009441d400004994402000c1c0090342440c1211440900003403801400c4213400c45c3c661000550f600029180062603071350111303008041541051052a415a25400070701c406c1c03501c854000c19981d120342608043c4050801d1407200f01104105482c0c1170007004041d1200503045150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 597490764 1250 597489514 597489533
    0x11401030f0f051005100c03021c05070506071d06070b0f0415062403140c0a0207080a060b090f01211707030f0201050115090b03060102031308010c200a12120207 71
    0x50b95200318846191b4100d0305000e401c1070101e407075054001d4545030010f184510564000342100e901444410400040020414060140328070410345401c80c0054001950b101c249151984450003040100082004600325001c2a40c0c41030001c0e002c552503030b0f500d141c11002800004455015241080d0021401903070031040201c194021a003010f00c50204141c00700e0079142d180c44031145213000000420002440e01000301070112540c01190251503032500c40c03615100b0500d03070503a00c0300e5403000048010302e000350203141c0000c0200b0520006504012440703002240c0e0002210030a03e03091403800c100544000000052040d40c400240c47d8002410040c20f0768602030b0b04200107500c6c020020079410350100d241d962800c0b49550782c060b20f908240901200340c3c005864241548003c1c0046400302004250f0032000d0700f4080c001041d080320181c4043c00c041c01018040b5203c0304182103201800034005000340a940c1c00104c150b00c1414140404c2d5491088403120066240c0000f414605211307d002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 597492014 1250 597490764 597490769
    0x207080c030702090a0522020103021b0102040306060f080d033903050a06140405150415140427030c0b0a0e2503200a0e060301050708011401030f0f0510 67
    0x6690003521340d42e12940c081186c1d42150300d0b80c0301d20105260b40c11140344130b01c2106011072042c10014074110703000203400803c0480d450718102c984e4000805008222403802800300424000440070030803414185450313140e9544003901d00c2015030b07c600691030b41044c04460800d00c151078000008402d00500e408100358942d5514034040380c10400420040c00382c900c25041160214441030302904038090030000a0003001d001c0b001e428000c21181d5507203030340b28400e10184e05c1010030318520140ca052052000c6042007040c01d0322039440c4c0079424108400d031100604503c00d002e40c1c00c1200c104140340588240c0c40c130344006046200200204202a101c0d6400380c142840194111900645170600da1040b20540102891450b14044820800902800042c40c0c2c0b001058103800821041203000c101810718540c09a032203030742210248081820f0070301c1841d0304600c0510701603a0303541c1080480b1803800407003101181059600c00484e44044581d41c800800e00d40d003c4028016424812442c8180c4002d60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 597493264 1250 597492014 597492019
    0x2101b081b190302041508011a030c03011413091b090209030c100219120306062d030617030307030c05071a1504020a08090c060a020a150207080c030702 67
    0xe4001c602003010381c9019400c0d404100842901e010b0766800d0026019240d0322124060540902001c51026501d500004101c1003503550110150700d0000100114101c04e589501780310030810134040440b180804690644662854841c80c0317082020114050320281d00320758010f0f5144c8241c0c001001070011389100042200c0050b038042030388402c502c01c201e00c28402c0705070385507105041c491994140714450308441486030059078051100c0a03d014000c4541520845004000300e2480c03003000e400d442000007030079030391a000e46034400c0301910303001041c6020b641c001034442c00d40c114160144a50004806440c2d007400c03281c0442c0c0d5481003103903039400581c0e400780400d080a030417204071803207241030f14401d507048840100c0e40c07100c50b2070134003c500307014014200d5103070001c90f1071341e01d600e507400100f20122590b9a03034401480c154148070308021f0b412000074420071042150301002d80e0b00003104228a03030000e800d048104880b080000081c850b00000030084d04011540c14030400011020340032641c000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 597494514 1250 597493264 597493277
    0x130510081209010e040908130306090c0617071d030d1d06030f0c09030a1a04020907050406050d0b0d02032407030506090106030e0c0a0f031106040b1902101b 69
    0x20320000d01500c0c01070440b200e0005540d1281c0e034041d8a81900503d400d18091602c051604002a00c81c0a0402c2241c00c203440072901c1c2e144034400c010303016103d80020280b519114540d201c1288da4010741c030300040c0c5a2010825809078600900903203080170002020001d0403110550106c850181540e88109081c1412850440b414092403c1c04070869118034110040c2648640e985180302005411091a0b05e070140701e90100c1c9000960344e030103d00304103103085416a03401d1030240b0402481d10001010b480c1080810300082008a40100030f503071030285035101c00f10b180c1d030311000410350207000804065898880d5101030801f011061a112144442011008945036900c12060f0261001555100e800034024001000b00c0d0b44660b00044480a00c2000d84150150100005883c022203801103079442028a904000b0402803c0c030940180c0780685415040620308081b4602d54010909100c0f0050388031381c01e02049520034400340d0781c401c82c1844100b0040c50f40c2510074020002d011800c0021403403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 597495764 1250 597494514 597494533
    0x109080609031603020309060409020910030b06030a02070201232d0d0f0906110a0f0201090f110105040806040c0509060319081602030303090d0e0d1e0213051008 71
    0x602040e1180304014120065203445050304800c482c4541088080e011404144608026580c80b03000800041141c2c00001d41c40701c0c98401080010340750041c00354240342c89c08041c260b55403985410359500440c114030058554515000585209003101540f00c600c8402c00c401c1088001040c01520f102d80e000300540b000002c46070707400218400064943d0b81150030911015807e014541c110341e0b85510404008210148581d455805846e560f21051810f001c012490103c15903100183d981c00440c1c903c000e0165100325100d080c003c075401c0c40040c2c4001b030044014a0964094801c5030024070b5100c04031000c40c031b4141003503450450381e40030740c85c494144000451a58640000c0b21910008854440d0384042c803181c1d10604650f00030240d100c268041c2c2c1411001507902030010310700c1001c1030b10103084c580064010080027041500340b1507200b800d0303035003103100445ca10f503894a120496074089a0a1441d40307000107901840040c5000014604160070803c0c4101c11814100c112203030142100c03407215 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 597497014 1250 597495764 597495779
    0x506150f0a0b1b15040210122d0903170403020114040b061507030f0f0e1519081b0a1205150109060206151903060204081b0f1f0e040606020a020109 65
    0x2984c0780309420b8818454070114015191081032688404a80e003003110b01c4000340e00b50700040d100102e48103081c02010628100717482c2807052009280c660304e060100f2000c2d04a5502412400c540701c0c640044103682d000040806000354403150204042850040091a042c60b11108170102114a10301402e00c901c0301102d0810f2010580d024543c0c140c43d407a00d203100c550b108480c4100f4440710f0000b00302041500008030348403000301c54010a000344607965560303181407000d5240301d40d180850b0104032280003081003d1102d01c8040003541d40c1c2044542c0d5454503001c040b41c1c0c2000392510412024900300c24003003114408020303200100341c00c0c0c8980038421b40d01d140070f0743c40f008101c8206070a1100d0355040070147c60005107500114040d10003e05005440e5280d250880e00241c12120701d0f076001c4402d541c100e262040905910b01411030740001c5074625400410665400c04500e10350030f003004e003074420400e400b07400b501341c80080241c020414682d036504025a03d000c01c20f42603000c02c1c0070040201e1030b071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 597498264 1250 597497014 597497023
    0x80f06070e060c010915020403050c0604061e02070f0b03040b162a060603050102120c090d030818161406251a0705070201030e0105040506150f0a0b1b 66
    0x30882519881650a0700009000103075100368200026556030b404454000b404e0b00034410030940300d20b2030041e10341d821460700a00c1c2050520300d19104881c14042040340550168207403010b000d4a030103061782d082144a082c1d182907502d40240306440c24520010465010f017802071071080b40207a149107400d0302c0e000701111050401e26200000160b000a0511009c420701c0014410410ba0b840811503103807043d200c035011581d15400403161a50001500e460341c00c0c9810040741c00c00700c0080403900e0a000000003800c07004510760010203100c10362001031852a0902003202030702102e1016183c2508404c1074600403403246011314101d4145c030246034842c0d401c1c050240d503007501010460b90341403d54101c4072a04181c2184049a403c1141c0c3c541450b4a05802440381c0a02425103802b500c0c0e0320984009000d480300e4400040c0760380c0c540002c20012540c000303400c0c0d404c000700303901c07001c1c0045448000c40d80142c001da103825004075003031400141c0061003000408012000328a40050f0040b80711141e03444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 597499514 1250 597498264 597498271
    0xa031b0b220621020307090302060c2b2c04020d050103120c6507050d0f0209030a11120601030203070b0c010f060803130f08030a0309171201080f06 65
    0x4580f0b80103895010043e02c0c1d0003160020610304040300d255a0326400500c9903801403c0c9410a90800d4002d01022410000181804003065408001841c4a00001807460301c03900392860981d40103503c3c00000702c0b00201403e900b8140175000795619211141d0610140000384400c4891001ea044d44400d09486042e088648692114840408603c1030215451003c012045d1410700151101e040f041018142083c224420003107808001e5150350895002510710a40525410031100c40100b11081e03a20800715150b03110000e04c002600c0e58040d1091000f409102c040a80600c90741401c1c10600c011701281004010080710000b80401c820303102e640d03c0700400c0c030000307405900001d01808451001c0c0060551309480c00000a904030b0000c07181c0099803810381c0f15042d66000041e00503012030391846a10050304111000c00303072182ca46080d1070340d40d114140b000c0d01019501c081b54410404070003d0600c401301c60042c002e0302c0d5200b40b07040d445482f07001c0c8204800d51040501103101186c0200740c0510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 597500764 1250 597499514 597499547
    0x18040521030709091a090112050c040b06041e0906080c1309021f1107030803040203190209071809020c07150801060c0209130213051602010b0a031b0b2206 68
    0x3c09240c8551074000d050540f520b01503120580403044240c6d10f0b1419070600811403000e1130001030085051960425045500c2c140c0600d04003110502d1645400b41250110f81942d00b05428030701000071000b42280d010340010860303030b003024000500030303a0008214503440304c112004001461558100303801c039003280700029040101e00c0c1000b0501c43c00c032041d60349960503d04244d20380040c50707030840781040360ba500b080328020808001d01003075003000c01c0403016514020080c0c2c00111001c2d000516091001418101000600036040d0400c0303502d0807000307000b0040c0315825902c417a1042d42054031400c0c4c0c0d016182a00321b40e03040220342603201e141424100c496a071600b0035100b03030a0b000d00c42c60b500d0050078503406c03409055240b001038a860b02480f144444400000940303040c10034041c10001c402140079811a8105000039070b041d5118064201241d0740b0109042c070403c04220a030003003a1081e840002e000c0000f00d9150f00740e00302628406c40304850114903140050719018207646640c0350185004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 597502014 1250 597500764 597500777
    0xb100e030a060e071203120515150f070f23030304150207060615030c0915080a0203091501030c031502040b09010f12020f120105011106070806180405210307 69
    0x20080345566221040c4250f840098407401c0b5140c3d81d0018010310002ca0490001e0042480c40c0340012541c41150740200c0204620203801c24180d0004120300c4a0f420754240d4402e00089a4942043d62011541c00562100c0e1a210407a150304001c19018002d4402e001c03100070325101040441c20202c21a40f28540c425104618507003411880402500403400403180d083c0d81d02d0300491900001651111900c54581d00443d0300c195504005101c000c0b80d86c1303c0b0761040002802070540940200d40160f0106804000585a41c1c40c040c2007440d00e005201c1000001c840800084180410200f600041e00d01444500050680c494041d2040740319074400c00302001c1c0d0134041e4100c15031040380c0010401c1081d2409012150021031224102d0b4030500c4e9441c4c4a6200064400454804c990490b00502007424543c0d00030000038551911000001e100c101000407102c00691a40d440020340860807908031590305052a0500e845552204240e04120300003904032a02840ca0710b801d0212486400140d8900c3c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 597503264 1250 597502014 597502033
    0x60702150403050d020d05100911090d0c0510050301031103060610230c100e0304050306040f0c15120b0a050604060309050c1c1a1003080702220b100e03 67
    0x140c0a01201820071010004200700c418075080c11800540036041b0401c00015140c148820310029080c115884034140307500305840c0003600007014054030049101070341d10016028080c0f0300032500f110640c02c003550090a04407020341140d4004061416607108403180c3c0305a400c44030415680d55000c90b680c6500c43d24103110252464444d444c002c0000c0b46000301c80140d0076522800981c1a00820f0280307983c0e9114200c0010110030b01d0250a89014903500514a0b0078209004a0b0316124001c0c409008407452701111070030401d400950070010401c91903035880700d0b21044070040c44030110800e0310490b14281510400303a494020446421110000c049a240519006090b00604012001990b49008004500342c59480e4140800e150740841031109540718807500d8920350407443c0724031a198000c00002000310b03070b080070f5a00f0001e40307403c4a007068440d0340a1000501d003c910715548078055003610741e9003406661070f40028102c908120303150b001900c0c030803004903610311411b42050351560050044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 597504514 1250 597503264 597503293
    0x10020901020717120a0c0609210c0c060c0206120103030207030b36010906050c040e0702060c030112020f030a2402181c020d080a0206010f150e1909050f0603060702 72
    0x41172000014107040c1e21102554803580c040361040007098980e04403501ca80305500c0d11400e0040100019820300e003000b0002502e0340860304000d0b004034028070000c8a000020340d0b80300d0003a075901590a100303d0413250f0b103c0c6030082d2582d25900c02140c02080000c04100101c405d004010020403c01c910105040c4001858409640740355100d0f8100355a5000210b0100328603004092040e49072042c416a03462074108a0111207900034496011500101d040c4081d07000c41c101260f0441e4182c90242300c0c400701074000510010400a0125494811161214200851404a15000200000412945000c4075803031b80c02d03880740044071540498a0480028286402501034038011282035104409000550100d040b4428180b001d4600b84404111030003419410403220303002d800a60301221407181350064a0018100721407281e0203102c02407082401703680301c42c1c0880c0380c000901034100540f1907543c0101801488107a50070483c0d0242c2400040315410f00103200da0092420740e00901841e20250030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 597505764 1250 597504514 597504517
    0x306090c04080304030c0e09010c08040b060a0f090516050c0304031b080607111b1c03022a1e090103020d0809100302040e100302220b031002090102071712 68
    0x400008808180301c003288594003080070300051840764440f010020309003400400100001030500240e0380c103125811801c5940301051a030016401840c4d01d61689440e0000b50318043c26800403540f420030b0100c00145811f094000f82d00411004a01490100e611203040340c05214101c800b490301d5200300002c0000800042c807503100460800d00242d170080d1122400e50405000791035000c00594070714203410102d074090000352344400100c00103080554041000c148141c0c00f83c0d158146001540c940e545c103040c0284440d02d0008641c0c0c00b0500d00d0101c4849981c01e80b0200740da440c1c040c51201c40b042c41c405001d4070002d100da10005015664aa10b50b5080040055442e14110f4a00d03209012071030554480b4010f003680880d00703440240e161410030002e600804401840710007101202c0c8410030242e2110400d80840b840c0c1022110103815001140310003030091a0203081e0103220f100008803801c0c90720344c00381c801181d0903401d8440303090b52424120f848120820102c203085c4c000700c0840344135081240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 597507014 1250 597505764 597505771
    0x3020607050c1e01021b010c020a20090124090e010915080105070c060c1e11010b0307030b0a0b0118050609010e04230117030d09080f0c100b010302090303030609 71
    0x86850341d69110f9034000c180100d041c4400c80307582d0003049a160041e98040e0103250211900003c10001400c190002d644010750743e0090702601142c0c00c2207040720041410031a8004e006401014103596608034411194483e10b030f8201180541d034071306030031a40f003108504101c3d00f420b100282c084c0d0a0501c80e00c020a88140c05002c5c104884074001000700080c00790714400d1519440700b42118071a420400305513400b4900500c100b215003942007400039014146007001c5a410310703040d1000e0035440800ba00602c0900030f0076a061180e2070000042055070310040d840b5500b8a0400c3c00324000040041d1490704100c202d030024a0b16002c003e219506107400948408001450081e440c0c0703408401042c103d0f403015129403420807281c066000321859404509004000e807001703c507407800488040546074024070124010361500c400d808028405480c045e20303038929100c903005030760310340c1c0040ca076542d0b8500c0079240c0c103402e08013106040c4c0340d8040d2083d100c10000240c050f600e03554030102085022134004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 597508264 1250 597507014 597507037
    0xf050a0b070e042a1e0c0210030c080f0405070807030609060c030c0219050c0409060902100f0c02060c21130e0610030203060a0b0a2609150c12070f18030302060705 72
    0x43c6464481034445c05444071132078039460701e10000d41c0c6070040c02001034400082c001807600308001c41e9002076201d03034890f40c0b0119503450350005848030301c1c005081036029401800c0c28410341001000344035481e4001c84201d40300d11010000c0403900300083c3d050b00c0c5998902d5016800c44c1d800410310b443ca41e90300302c0c4014868003c0c0c6c0c8070444400300281c01c8449020040d22010740d40c6a030442103003849004044081c0f002d0a0800c401d0103100c400a1035601e0080000380503070404204011410401c1015407500350129562000a01c0007541e50f000c1c98100401a0948031440e070000586240e04043ca40c5c0070300c40c00790507102a0180b00c04240c02a40c0090300c1c580e000f281c0d1682c0011262105000340004100d2a641c42d60385040703013070603104002c00c50304003c1110082102880030188000500e850f1410100e42030100954030718924840c0c2d8014030800d6035982d070303100e410400c0e0740e41d100140c8800100951101d0b00c0b51034050b10349140411050000a000d81c0c010400b0500140c0030310003130000c40e80f04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 597509514 1250 597508264 597508277
    0x60816051911150105100e060f301902091804050f01060819060c09030c0306050a0f0506010e01141605071a13050d0f050a0b070e042a 59
    0x1c000d011410100c502181034000b600b9160303048600501031203c40065400d01440400a50501e00003031034511210081c101401060001541c140c1c443c04191010754464074511500e4000c2d4921740d442440c1985400e84a07200009101c09c00e01203490300c0c50380188810510450071150001d40100294018410035900c40f0307481c80280703542c007500009248650b03c0740307001c0c10504800c0c3e901c01e829107280b40c00c64821500030501e141d0003052200d901081c019000302e00426500041417060f2040c400a800107096541c12207408802d1040d00e400c10382c010400c41004110885c0000780071700446805a507070a001501b0f0401408140d84140c59001c80904035824980c81e1445000341d014161410840403211600306440c20047c941b1a8440307880540c1000287c40c0c9000c04080a0000340c440d03502a81d0b1160702d50500d1003082c09034114624040c0e030342c030400312030104c0c0e02410241d04a00c0c046a58100191030012800310701d0500e170098421071802001d844003040d1400030885c42182e0651516401c0103503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 597510764 1250 597509514 597509527
    0x20d021c020114091b10020c150408010c110105100803030c07060608030f0c0601230f01050910120e1606030c03091a060405010501140f09060c01022b05071209060b03101406030706081605 82
    0x1030038437985c40b00004135102c81f0381200c00d0550541c01d448008150b80c410010545041022000100403a640110b1402c0400d030b0350180c1c1e00d815401048150000340c0c00d0300c00403a40101864000c0f00411900301c0c0c01c2e003100c480d6a03a404801ea002804034011036410081d01c540d101e954185040c0300c910101c7c0504000b0304004900340484d520f5500200a04000f81185144c114070125a105000d03110007400080d00c8096548600d1100f02c10103441005c0415655000f01c01c0e4641c4258401c07801c1c0303580401d0060034120f00c0044412140410f440041c840c51a140000809601804e80341c0300c41d419607030215003490694400181c10f60040d040103a00200204142e06550303100b80300034000104101d1021524201d4140d1040001e941c11102ca68210f181c0018085900d800c404103c400d14108640450006160302e445800fa2881c01009034040c800c00c800500d0300760042c3c10404c2500d04a5122041a540310010140d030b0b90a0b500c11840800d054001060f032044800c944032900302d800707007010b07447c054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 597512014 1250 597510764 597510779
    0xb090301091e1b05010e1002010e03070309060e0102010e0d030c020304030b040f051002070206090f0612151201091119030b01080319020d021c020114091b10020c1504 73
    0x280b088180e060541007200b66000304512403140507907040b2140c0c20502c08500b00340000c0e02c03080c140c50100f4030411001418240e81d51003500018145900c010a036600e901f01c528000e40000d0450141c100404d6002031840f4079544141714808000a0600090003142e12034803041d40103044d007000354000c5010410002c0702083d41703444070070f0065102d100340103500109414660708008540c1070202410703004015100240e5038610581d1070041d411620300d00f0500c00c000014005200703800d849032810b441d400070080e0400407107031640c1c5003600c2038400008000301800c4603800c03514103440c010442c1c5101c01c01074203141080210082000040308a0140494580d1501030302880243c0c046000c0e03500010395002540104124440440810b0001341140d11070038001940303d1803009400b42c90300d40301101a0410b00d00c01d4000f01903a14800900c5080b038103041002640756105171307002c445140c00096140c5004e0820301809800d250700355000d01030200e941c07400c1200b01d403045150b403014200107100109a0340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 597513264 1250 597512014 597512033
    0x1a061825090e13030806031219110a030309020a05060c071802160c0f0603050c030a0c030b190e07210902060904060e060109050603010f030611190f020616090b09030109 74
    0x420019903080103ca000c0d140050a0039001000a40245c1269003c0070b40c42007940d095480c6100c4450905003456003d010403182c040081220850611507a2442418183c25500180c45240207a032525aa03e07251014086144280c6980001541c040c41d003c01c411403208204403190404010050702d4120320f1703080c200401d442c1500559032100b032a00e0070800103d24024008c0240940d040034402c502e040c0d25a1811800010010401641c591045d03508040c17003684501c442131001015000641d10a03aa240400880c50041c80c40038001c91012403803c500032640709240c0700907083c0e50034035940c1090600c0041c000d078040490f007041d41800394a0039956035003e400041c0486414600c0c01e0b103002c01c001441c210b020742c800ea0086000304010302540500c0d510b542c1c1901e420038004141c810941907810600c3c410140c005d0f5580f458030b001e44a0b600e0307000089080c120300d1642141c0a94440140f6950b0714461100000c0210760903400c01c009448420002d401e036440028000640c5403215119070344032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 597514514 1250 597513264 597513271
    0x40e010b03071806060801180509070e09161706060d150f0b010e0a05031228050703110303060117040303200306120316060b0303071a061825090e 64
    0xb0304103c401c0c030010f40d075042d20950300100184c0ca4811940d51400c0014206001904180c408075511000040c0400f00100912401066003008210003464a9048140c4070b550b950049514a0020b210003e4a00d45d912088907400303a0400203010191504010031151452a940480728010403648080441c4618483c0403500304a0b010040b441021060004090060251000e403141484c18028012902c00041d0b80400811101006d0b55401c040014682d80340030060041d40c0081c21031070b4080780154454084d003595882602ca0303602c00c4015002064607404203e070600c2c00120486407101a0f0401d0350b078500c0d0002e009081c0050b00d0b00008503006884c019210040310303020000018001039090000c0c0d0107640c0c615881c05141000a2405064000600420043d00d65612402803030540e66050046030300d12940111486075200700e0803500108900c04860b11032260301c1c0c00901082d0641082000e03441039a00401800c0c203604112400081d10000050301c6040020f0700c00d00bc641d54654642c041d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 597515764 1250 597514514 597514529
    0x5131a1206240712050c0d081512010603020102062211010e030312070210060612020307021f0b13020708070212160e0105100e03071404090605070e0f01080114040e010b0307 76
    0x41e2920079081140d01d41a910320f403903003081010411062541c00103e00d1000020036441c1030b501d03d4271210f80450100c00d803e07404681c0f08001c03d1040c0107555055000364112403013a0213544260750b944200d210b00207444150020250b42e0003014a0002d0304a11901a00031414103004060282000109103035411502001500b54019014400300a404021440b0202c10b02d010030b100a60a0034801010b0314601c43d8164206038021000c19070650090104104c40c00c0540030b46103030480540c3c218030240c000860603d02402030900c1001b1965000e0007240c140b25000381c0181d107410071a0b800e101b0250401c00059000c1e01559074a068034400102c0410024940c03004924001d50400d0100315041c41c2030704103503042c84101020781103686c8021a0360011500c29420010007204401c0c0071034081c10404030000c152900d01700802c0320b1190800600341d240398003035920b0104100c007000191030354813081c080c00f40c00052141c0c0c205040c1c40e1680240d00c0b942039040020517180c2c1400c01103417170300b0510b42080d807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 597517014 1250 597515764 597515767
    0x90f02091206130204090206190207060311070807020f010e0301020d0e010e070e0705070f060f1a180a0b0f0a06021c02060408091203160305131a120624 67
    0xc00d914000304900507948804000e082a03042582e11020304a00d03101000740602e842c0d00401042d907940e4000d0300e00c41da1202002081050310317a04000d403079107820300400011070b1500c406c1400c0041c14105842260368002603c91520a0640800148140b110040e03410428000102e08843d2000c2c00501030000319544041456420f1090940c20343d05120110394140d42310070380c1001046500300100b500000281000c582d04d4007a4200ba0b51050b4104502514180c00e1821318512030180340d006c09407405003007006121403826181045450b208151401000c002d0601c04201c842a40c2d034840e880c80c040041c10082d0082c040d401061200e003040e0301520140c3c0058611200c031005080f0400800c0003248060708840c0b40c60340c0da1400a004c0d8241c00b034050b540b084100b85802c1400c000b2200c0e91540c01c5800041404545001403c03580903291480c0d00000003440012804030b511046101a03881413030860800042d052000c80f4410010500341c2d0000b4401182c1103120080c0c40c50300503070210105440d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 597518264 1250 597517014 597517027
    0xc0a0c0f0f140307030602211e010b0316261504050f090a0b04030903051e070f12060c09050d0f120c081207091e030c080703020d0f0c090f02 62
    0x82080703001039440480921aa46969210b40d40c001c0381080a481e804140141c407400c8200c10364280c4940303081c1640054403da800d000e200301b032500b80d0025a91840302109800c1c1c4e2181034082090005641c0c0500110001900c801441d0040b0308101a081c0006d050750aa20f0400701c07000078240095500780c2c040080c0b800891840d0803c0c3c06a9a03200c8580449910030b0304262400f140d4942d500100544540400e01c046402c1500c951003120095400c203040700c540ca000000b132210071104243c01c402c0c1910800000040b040340d040704200454a0b01090744c10466455102d40d0080e0220381c402c40200b181c00700012840c1da903003024903100c49014001201500b109850202c003010524809a0207101d02e540800c400200080200c1d007006040d00c00030090b0761a0104141c03040c21040c0c1180a0103204914015900e0095590300f00480f4052550b101c2ca880c4e03a0356100d138454481c3d0102a401000c1c400b44040403030a00340c041000d59120781584403080b9980d119079021035082428192803540c000540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 597519514 1250 597518264 597518279
    0xc02031303060219111b060f0a02060a0506010f0e01260108060a0f06030c03080702030723040b150a111906060303110c130b03030f0a020a1e0203060106050c0a0c0f 72
    0x902411610500b49803031148500b0611503611070500b1086c500300760105100c081161038141c290b854070034078000b60380c1d103400c04144040c0d1968822a00c5e28030300c1d882c140024003a0b41c800c00070040691b86a40f03c040010b00b400004648240341c402440181407242090640906040d02906001300380a0026025500b4884c228000381d0303030403410101c841c0c1d08144013070012900c00300c0108112076000d505969100c2e203602c04282842026440030540700344280c0a01c100c8154201d00100f01c6c50111010040440000100b1001c402c00d10034040c80102e00b1f00c0700c1c11069004802c883c05003c0503000300c50a000710221545c841c1e003a588411071340c46032140d00030820160841400c1c8214001800a01005040c40b40451502103803800b2603800151290348605007514107200700c50310328000f181e4050340d070806a2006903550600e400c003190110762004502800034102040b442a00d9802400342410740d1a24408540b01c0e0044612000107025a020140c0000c408681d02401803082d1240e000a00d40752526 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 597520764 1250 597519514 597519547
    0x408091311032e15260903040501030e030c0318030a0b0c0d0c03020a0c15061d0103050c030a050a08031b070f0501060b040506391c0e010807030c020313030602 70
    0x81c26284a89810107001504c040d4042683d041224500001d40c2c0700440d800b028018013121101c01007010040034020b05a40c08801882654002e072401e104921418109036924400c0030020040b5400900ca0124900f0b410070486002010040c12516440307040e450f0140200307410703035003a112103e00007103504120000340518000c10901d42011800c25120640c007500380c01d500c03030005058102d59070081550ba002584504068203100e03400304181581100024042c245c280030a848920440c03100c002149000030b403001401e42e00c100503001c4030030195242e4100c1d8001902c01c942c9603982400703490311000c0c1003000d0890540110034000440030903007041401c5500343c0e04180f51050f001c000512042e00c03240d0881e80001040303000791006c13001e9214110400812640d102c484140c0c600220b024402002413500d0702180d1040030a01c03444c85030b05080e00c0041e100180c01e030114600c800000c069500a911550709a03240740140c900d05844c06144020300341546d001110070590104645000000182 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 597522014 1250 597520764 597520831
    0x30b0906040e06070e0a091d1908070f020406030212061014032505090403090e0906011a09010c020616030201060807052d040606031a09040809131103 66
    0x200e081240b210100c0009485520091a0805218071103444842c0780e121005000c005003040c100401c81241c40304061000c00c249400800c0c4984960a98400c03201420103d080c00c6552248806161030280c2d5901550060640810390b80599500c2c0c0c0040940ca0740030b4904684203101c40508901d00d060030a80c9000074082e0041080001c54400301c6020340c034005160b007070206101c103043c00241520303400b140d100079158000e1500518400280010150000e502c0d1040d035000351800300c3e20360740350743c90701341e5410b000d103d030048070100c0044240020900c2002001918018075181c50700303010315004070301140d04c0f52240007821540c082030002419428880c00340901001f00c0648065454070707000603c0d080c1d1004180f801d0b60000702200d0176881e40011541d2a0300009031090048544e1028007030300070542c590034007082c1d0420410460043c5400384240c1d100343d034040001410100080244442030101c3c1e00c00c00b040540c0c2c1c0c0e4400480036103070400f070341c81502c400c02d03510310500c04130301d100d4458100007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 597523264 1250 597522014 597522019
    0x509010f06120917070c120b040201081f0314031e18010801180203060319060525090b0f07170c1c081f1d07110d08062707030b0906 58
    0x400f030014400d03002c00341c940d9035010a51500ca13070070b504011444540700d42c095444041c41440d050104415110035500c900d0003602d07062803566820a207031110a9180c0c0f45403000a02e0808103000242d0740c4030708030020310a00d200301c03828007003030b600e0701080385444501e10f1440c14408103011960150441c81a5103400c420702c1c0001540d4980180d04071400c10241c03000b0710303a54000c00020400d031010062035a02c00c0250403004105981d1341408001841c041c0c4401100b400440d03170780e042104403441d01d8078143c803241d600d001c6c119181440380200c03908540c4440b0000e420400ca2403021031400301e0458104040b00070f025664656403048280f034854181c0005c20301404c0c4020081d03000e904024034980c003001c400c0c01101c1c440c000304503c1078ad04043e0b030004600881d21594020032000da80841c140702e10b00503201c2c2003100c90b0711251166600300c456044000070301c5000000d18941040c0d00302c148001216030b1241c4a4040d010600004114121b580f000004c0e940c90503990146002032050790040000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 597524514 1250 597523264 597523271
    0x7240c020a020310050408070b01030b0702010c08061f050c030f130603060509190906021606050f24040b04090803040b0609040b01170a0c090603021519080405070509010f0612 77
    0x1c0c1d901090321048684141046180d441000078207008801c400c88001c40e500c42c10510940da100e00c0c21600034502030f00ca0310015847c0110001c0314501608115008850060208007280e04143c0d0145000d01d94081400030060306002d800e0780004c080014040f0307110200802038403050740310440e100116044c4d101004040c24200200501d0320f42c41030703c40e0403c03041108001281d6202c48100050800b1820061070280b00091001c0100024000400c40520032070742480301e0f44030601c041141000c1612030516403075520f4060860039502e045542e0050078040d0001c40c0f6452175100250444050241c00d44426400008000401c44022b4211742e102c81d04849840140c103007501c3d8400003400c14068030220780c40101c201500c0400821004922503401a0340210440d15608150054209880101d00a0300015200204042280296a661007078866810348079a80610101e4030050060001d5035a030090f202c010905403030f8030883c1e81c040c141d11316209403110301d0100001c1c9030500c0008550180380c61b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 597525764 1250 597524514 597524533
    0x100e03040b1c02090607061b02070810180f0309031a040f060504022107050f1e010c020a080111121332240705070c1a07240c02 56
    0x3004002e9954a400b0a41c4496003103002c51600701c0280700382e000030760f8000c00100307103001007020035004041d0001d907181080603054030150b020b80e41d811850003000c5a98102c001c2c82d00c010001a40a016101d6150b010002001500c0d150540c42e541000010740016180d50381c148140702080142c00ca400c0c2c52540f0308441c2d482c1c503484141000b428400000d0080d0b48a10200d0295640c88030f6144039152505407840001c15400745881d82d41c0854450503004151600c0100030514211165115008140b50710a44848110300112948200c10310102da01c8903400c2c0022a038034809219400210051004059407501900d4041600c14070040102448090340303d54040001e1940c544050303a01081c00c49401c1d8000c83da050f8004910221089440a200c0c450203c2710070b01b00668041c401c00542d4000d91410344901b03404840d1442005000b401d2004180e00c100a46103103542003500000094419505004150f82c1d188040b42c03801c0b00342080318941c03984403085001e4610400e44850b080b40020540e841 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 597527014 1250 597525764 597525779
    0x50604031b1a0f030a11030a06090507022b05270f0901030819020f01020a03050a0606050c15060d020901150905041b0804140d1d1518120d02100e0304 66
    0x200d5500383c594480c20100209020045a401ca0645010140103c2d80c0701c0c5040b21002d4001c0000d4446d006500d41444045034140b4008590680958800f03514040c0303e9015070040b04202c8120020301c400c20000300050403c90072415500c101004040d20911900486601007048500311181c5151240c3c1c03072403004200084090341110499400115600310030990200180d09002c040d52000d02554000107c80001d1681a4840391040b43d107010708004158a40314226014000c200b8200826805038550f51074088990590340d41c42040181582e602400a0740480c09881003a4400c1c200302e2444140348004981201406001d400103540400c07901c10b91046008030a140814a03c0038000794000ec5001d018150151130210740b5050119550840003400c020042202034403425003112002e2103844d454a014000c2c2c2036007195600c03030a818050740000342548240074000760750f8000c2c9100c11440006000b4400f804803020b442d00544410b007110010395054402410158446800800c42480047c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 597528264 1250 597527014 597527017
    0x504232202040b0d08040609031e020127030c15030c3905010e030913020a020d1409130516020613030809030d021818160503060a050604031b1a 63
    0x80da0121404544a4500d41c003103011810120405070815400242c040b655640100988049921900242504440000c14a504c04c80b07c00e0000f17002440780030002900c0c00103000f03912941740201c0900c10030ba0b60340c0d54801210f0403240e070084411000103201c0703070076454052042d01c503114000c0c14018142d00980c2c0d02d9010f0503070760581300c481c806882c001d0f030050f80e09240003091010354894020003804100c1c5107210f07501c1d00101800c82c0303e07440801c1c0c03c40704c015940c02941c648400b40d800811a20b0355411080d985201c2c0001c0d0400c035000144015952a900e00351155401e1340782c1000041c0341d0400800241d9009841c186c101c09540c02001445003c21410101d008010b80514003451039480e1031941c00d0440c421000c401c10210300110b44081445504024070190100848002008079010358500003840c0048817071480455042041414a0b80502d000f1540280d00806102105885000145458010b500140e640300c1c5c000f81062034443c1e00c01c001d04054203040400d4040304003585840880b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 597529514 1250 597528264 597528331
    0x1806020105100306050c04030204050a020306030f0d090e06060f0703030e010b060909010b0c030f0c1f09050607030903030f0603111503060d0305090303070b010e0a05010609210c050423 81
    0xa555074000003406c3d03441c86c80c00d03540174642c000c01c18061824034000d014040d401c00c2d02d640d0310034042c1d080c089504175000101c2d58010341d51610f0340c03802140380c441020305041c801040300750010380802c081c040740035010006148051194400040400c0b55980241c00c40f07020b00a00d601506040203246050b0383c136150b11030304480301c01040d07a544020f403070145425070040c01469542d151001ca11100c60410205402c0c2c41c441240310048480111a4440015120080f0003e482c3d0b07084100801d20040c0709401c451241d50082c100031801001c0080654100c0340168019116600c101d44180304515000c7d4030029101140c031102d0f4207504151000507104100c0c404010241b01e400901c3c030519441c14401d80e4002504203890fa4519070703442441c1c0c91350000c112003800c0128a0500045050303401004441e0603100c00b0031080c0d178140c4501c3c1c160300d900103034440d00313651050b80314a00203220f0b56180210000700c4140c0e2801203015501c4240868600c03805400d91001d044003228102c2c43d9801000f0483c503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 597530764 1250 597529514 597529523
    0x90807061a1c060b030c041803030b010513060305040c0f151409030c09040f06110304050d091401110708030315010f090303020a150e01091101020705041a0405071101020a18060201051003 82
    0x1103084d1030f840028070b00940300790b074103421a0408001c08101d00721280c004404a000761424040c030340440300111100e10a03442806d0845e04419000e00484c0d2003030f0b204640c8144501803c00c07945890303403031603003580c803055110100f410606c184100d21540e02c0100c01d00c200034003840380b48c00c040303040001985410440982d540a410a01e00050600a0700e407900c0120780e07003101d0300f0802e4144845c0c003205554021a42540c062013500d400c1e0085501c83c050440480d0b900c1001075401707a00040c011144055066030308041c0b4400c0d1840400c040f01e007403005502506008564440c5c802400e0005003a070001c1c5480e00b810b000c8004010400300c1e070081047c0411b540c1c050180c0c81c010310326102135402805510b440b1a446d40c6490306403810400c00720b10901c84040b0903000c071502036648a0070842564080f20403100701851241c5440d00c00e0502d0707086580c0103040c1d4100100b040320900307445801ca8103e004a500025000c24007c05c055600009100152a00707100900c6249000142a10b41032650300c002070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 597532014 1250 597530764 597530771
    0x10908031803090d0b100f061d01050c062e08010603110102070303022805031603031d1903020f12030106080114010c02240f031603020304030f080406090807061a1c06 73
    0x24611b2251400e458042c1186004800d41d450320f41c0002800c817240c0c402c00803260620910400b0b265030054003a9800c00b00c0d60401080166074de01c1c0044080d182e21104211640c0807000c1544041280b881064040c001c0c0b07100008030907145050030308213603406000407810b54000c11001e1000c20380c04a00d2040c504500e4059000c418510f0b5492485140d0340300f4050042e01001c07854020705140b0200080c01c1d9030003964180802c03882c0003c0c0882d200200f004408859010300006406c5031030b0b076a40c0c02d1743c450190040d0f0301c0d01012a2076090404007080d05024600c0400401480007e401c00c2055001d49010801c0f00609000c9400103414040080c20182c842d03804410268031a89a116139078104c44e03481110382e0344619400582030195041501c3e4110901010464044a01d2092013a40e2203507800d651030005001c482ca8003515001d401510555415445103000381c0403466140c001e2505610507040020924800c0c44e404244100f04101548103200141007011120307060b8103070f907102982103035002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 597533264 1250 597532014 597532021
    0x715141e130c03150501080f0d3f0507020109020a21081326060105120f060408070506070c0c09020d291903020d23010908031803090d0b 60
    0x40081c10402480034550190100800100300c42088070304041c801c0c1401a41d8840e94113a0301c42c41d14a0001589910083d00c40c0000b51041340c0016034000074402a446e070150003005942d0603841e19903880d04400b0f00300480e07803000ca503e03c21030364030400e1440200000b4413940d0014240d04d525220b0224980da09255172000c24107071040364000d01d81c3c000d0856a0701c080c1c50007107101d0051544100f48162220807400203020000700d03000e0442e0780e040c0010340280da09000420002490055900c0301d103100d885418864a0820081240210f024501640d21b5141d1807400030f260141c010030460400010400d0900060300d94183c0c0c00a0320190000943c468101d030f0140760081c0500c4801c0240780c40382031b9091a1101c1020340d11114404190340d200c92410307020301c0da0315460702c06100c000d400c04005501000402d1900041c600c15181e14443c441c81800c081b0303070660940303040c2c000030740703003d4070010522001e4901d041000003100100005142401d03640c0c800504a00340b015005400c804224001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 597534514 1250 597533264 597533281
    0x708010807051e090a061e03170a110303040606050f04020a1709151302040606140901031e090b0907050409030507080a090f062309100f0e060715141e 66
    0xa424011006400d83c59135142200e000e0024007498400c0c2d0000c2c1a0800c0808884207000d0481d4068a40254000071080e040d00074008031035010444d2131040019070895045101e8003400150b000e0f501030360010460300d0508042101201b0a554041d110f548104862881a42c0261005046000700d20380300340c981da900e0710454148502940003441d104d40840c10000141c040e043d64a084a0080d20200220740e1076130800e4030145081445080ca010050219000c00d41c802e420900202f1010340c03035404000010304420059a468072400c8681400300720411410600811a00d40141021030302445018801d44016110307201d08030f400352030381b0400290060254011580706000b4031f0f400070000718055480c84000c0c05c1c1c400c40e2a0001e1f615903e009281c0c0c071032030404196408180b0040c8265111040180c0075034028900780401024044941e08050840d85e425014000c81ea0081140403814981c464240003140c803042009610030301d0300014840300c54006141081044403450300030285441c0c0e0320300d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 597535764 1250 597534514 597534559
    0x712050c160f06021c0219030603030c0b04030207031401020c0d02010b060d110c030406050a0f020123070306050406060e030c04050c031609050d0c0314120a030c12140f070801080705 80
    0x380070041010100345c49802003540d401400c2040341c1d0310406900884a00301141600c110307120160018200c04031407404506284021a00721b84a401144c03e0076589690308641355420741c500e4040b5960100e07403d8a1a5401c0c0480c0c4046a4148000c0124004000000d072080c011905665203c50351999a08590f030201400c036408506008122916203aa40e0001040703039001c00c2d030410008040c824081c1030315005002c2c8441c403115103d513a8040e00202c031403852011030010004010542c0b1042c0c0082d29440e144a001c02611040d500d43d20560b4880c000c0c145000c1c990100c1a0281d45010104188246179100707494201d0301501c98194807680b00402140e48407100c0e00480d5021141405c2081000030700300f408421207103d0014200d500d01c81040d056103804c0400c01c1d80d45488001c1004520039803007684071f0b48518420f82480500c040001d00c0000c103c50110b806500c202104600307200c410b5018107000341c0c0c000140c0c40c14101a41c10100215101d59035031007441d000d48030030310044058100307800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 597537014 1250 597535764 597535777
    0x7200601060c06140f06011b170d0902120303011706010f050d0201020a0b0f010302041a090712060e0108150907060f030203060103110d0c0f030b0f15040305060712050c160f0602 78
    0x5044e401814600102c2142e00c0c02603d42c030740803400c09207030b075500c402205c0202d03007101d83c009610b10400c0c0400d091029107503008002810000ea520302d980001030342c42d200c44c94a41c0748003000540d204c2d030405207100322440e00941000c1c07a90740031000400218900c2925801620015603a81d003d05240b0310060740b41c150950002400c0e1255081000440310048075407604881c001c940a22040d40f110040010420b02c5c1a1a25000f48080d40003800643c010031082c0968107202000081503585c625000340034460a82080211b900a01001c46403100100c945a03000403010000d082071610380100504201d81420f442c0b02459004000a901603005c0e40c04000316502c1c810301280d0f41d000e00300c1004010300304025100701080015010f043c80510901c1195080d100180000002c01204010402403415a05858443c000204004000901d00740500c50003000309880c0d18000e04208040e50081e590000c18401d060681404156582e060082c6d010030542d80201541e031081c08181045c4002e481400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 597538264 1250 597537014 597537041
    0xb0a030c170304080d120606050301050102030702040519020703050702031e030d0f0f1b030e0d05070807230601081c080c030601110d0909180f030809030c011407200601060c06 77
    0x20305c03041e0022034002c80305440c1400c60000c04c1001c540c646805507001c0c0400e01940780180d005000c68401410140e0060b500b04c141c801400c641c181e011043d84040c1e81c82050201e0001f94049018421401d00304500700111017400c0111f03207126601040c0341c0c0d0324003c40c0900c861407038542000740002d0704150300c83c400c1081e06950601520b0026841003100074905844000001e1800e2200511044003185042c2e408806503500d601c1c0c14060b845441154200c03100c20744070038001c1030450482c1c040c000000410000d12201504056240c104c8003030800c1144468000c04140904d030180d8859848806a540412000724484d00c0745c480b0001242c4000201c9001c200510580c0b55000c407803500704554030101d5074015414400c454030012641207070340480c68014100f01c660074540d0300090044c0c010982c0507038a08112818003140800907401c0d80c00342c40d80000d0361050581403041e0160b0007405420080410403d0038244800c010710303130350740b8201442694208044139250000704a0039410008051303290 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597539514 1250 597538264 597538273
    0xd02040e0403110d080903160314030f0603100b0f2808061f0b0729010b1902030a020c10051204380f100b120403030b0a030c17030408 59
    0x585006880501e0003181d0100c148a2070201130f05083c0701c0d98030a88a103590300082c50401d0108110b5501d00e07260104110180040e41c101505e07440800b4001e5031090107030345022105400c01001703060030b050071021404205401c203225401551110500c606851000f5a52404481c8010f0307907051f1640d4030b0800c040c1d01c0f420701140c0004c030b4100c009440d60250404072544100034940e05070071110078049200350702c00d0102c24041600401c000c04c4220407450200c40782e448c01020202410200b40809030000b091040300403801a6001880f55a44885040b46000540c03a2071340144000e59107000c040c0c3d40901c201108038000b100d032445081603810503501d207490400181271a140420000509000e946112800b0550711140030001e00359004001013000b4203030805448004001c581800001e203028007460304840b0014024a1b010002c04002069441c00e281c10b003070070700cac000b411741e044a4840751041240fa082880410020b2024034103d85191407040e07050b403001c4844605600890340300c0c440d540036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597540764 1250 597539514 597539521
    0x14010c020a02030708162603040b04030302160b160203010e0a0312050714030f070c0f031e180b0715020703230703050a030b011101050a0c1701060e01050d02040e 71
    0xc0000340076003260301c2103040e56001526012240c0d038170400301010400d01c0e8041d40c400c0101d0012181d9012610714000308081e060a0015100383c5194425403102d241102c00142c100141503050001c030a24a00b000903001c0400e00e450f000f04034034040c00c540018a035140b0310a1004541e425030103508421008401d840c1e600c01c0e51f06020b451015100c03881040142850b001469483c13080c9268008081d07100107403401c58644251140c0184402080c510038042c0814220010444c0b00d04200113451007940d54071000c250025881032007200c01c50705030b010f0059243d62625041d104845031020307140800c0e04161200c040c0c0c140120601c50150700c100e2081e1002549005141c0d00030501042d044c8114482c00c0c42540494034281544a0340c800500010001e0200c001c0300c500c00c0c1c0000c3c800010524080c130b000ca210034140c60071610700f502e020420b59640d6564414945c0c02a04483c114845110020f032590300d002d0f40508160709035201c050408c07100164821200e18168141c43c05000303610b082c48a01d00c3d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597542014 1250 597540764 597540767
    0x209040c11101b03231003021e061c200301080d1d0f0a17070e0717040b04030e150a030e030c03041202012106180b0a0b09010306082d0d020c0d14010c 66
    0x200a0301040c0d000380c0140000e034110454274200302000100141042d440c00e10b006200c1b09440b03840c08444000385803248001540d03070f00c82c141c1d40a41c02042c0c0c0d02d440c1d41c0c0e5140125151a2002c0e0112000138054002c3c0c03804442d020001081c4403481041da4040a0042c01c0340c0091507000040d045509803000303440e0020307054900041d4040985034512038522864a5001c0265135008044007180c1c00c1c02d0b00100050002200180c015030407038400e090a00840b002000014010180001c0d010740485020802240740d0340e0600500c28201000c8000e10f103049524581c0c16240c0c1b00b10f029201e09180c040401d002103900c110544549114808603413290b0300300200d020409441c1d540700e030148000303000251030b00e0a0070b0f40c4110351090303100400c0e62040078504007240b003858000701c503480d0602d6134500b4009024581804080e04046031180030382c40c074000b003103039280540d160100c0c415201c0d030144d510111810b0300000c00d201c0c410b404440800905183c0d1402c000f4149038251800499428252003003c400d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597543264 1250 597542014 597542041
    0x11a1203040e130c1208030c09040b100c120f0804080903070807030804053607120e2808030f06060f040b030703060b0f0a0302030a0209040c11101b0323 67
    0xc9110b811007204017680d40b10a000b03205491640500f0740d14080001c40d0055100c003008200500024201040100b101400203061003901d414400201d204042c110040098004001c5a00d00f8182440d401c01ca901e07440051080700e00900040403101c00080300305c52641d00b0000c907002080440d080b500155201d1034650180c1d0002d1142c80d0051100b203100341404580a180002054181c1e10b69595042007030702c0807005982c0140109d4203102640011820400150082c403602540c00c3d0002c150803503008004004000d820106040c1640c60b00b6800000250031100301c035042501484559569107800c00011000d100d4002d10241e04000050300041c2c01840b040903504c00c00d8961010401c4966130183c1440c0c0f445024080c440c5290100404281640030b135020315004400060010b061139000c00121f800c40351400b1001000c00c044115000703100000300012041c4c06100a4107115828841c0101c540ea140d80c0c00f0f105050684800f140341b40044210500d443e034030020350150303200b0b06011130301100d00e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597544514 1250 597543264 597543301
    0x60b1603020c030307030509010f09090f1508030a0c120210020711030606040c050307031a0303040f08060a0603050a030c0f060f0f0f0902030c042007030f0908011a1203040e 76
    0x903000b00440c1c0da070305180c04802e9500041d05900e5541c54115003c0045a2900c5a03411040c00e00c580640042003902e482d2051600c44034000304c6c000345038980000020307801001a401076030f4541c030402140e0070480e4000d03000c0c5004c40c0c0c0804140f06090056074143e040055284030401100d2020800d0300c1800200301c1a007105030816002c0d500f003a1a03101c00d01050310034441c07a42c0040f500400100d64441c2c480d9002c0b0100d1200941000c2d0410b030050700103030441e40a070780101551007221000b03201d101403c3c0081900214004401c1080c2c0d846c40e03031415100ca104120240900c02c214000505104080d4040084568011010080b100e584443c0000401c80400900c0790507141951010028002e0b10800003482c2c1c000f4001c0c4441602d82c000c1102400030752030804e5001c103800c140d110700820b44101401c0440d01c1381e01d0390f8084c0d01004800400741350300c95008019980c1000080c409000303608a010039100000d4460704105e145012026103035104590080c0b165001d05400c0060704200010305103407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597545764 1250 597544514 597544517
    0x10501030b06072013140106030624030906020f0a0305090607093b090309041503150c09150c020a080c03191a010e09010f0c0f080a060b1603 62
    0x12a40c4054240102c0d03010706240100000507100c0703440700c0212005081e05103403074001c04121141407101c41c450103491a64140e9403c3d070040a00600c10240c060041c1d070702803c5072525415500703140601c4050400c44684a007020302d55140d4506003840403039011500105540c2060b290b03600240c480c000e00030902210320b1030b041e018890128001d81d1140c0075607800ca46c901a0620b0007186060940f840100040d0201c00088100d200e070300448001520070030b48608400b001840d00c5603064421701041c3c0e4401c44c201104100044000c6c070019124080c42c040002c8801ca0000d074440016400b43d9101405e40c2050600d408401c0e1100c4c40958807291913040c182c0b098400f254040d42e581d066543d40c0c5044480180d01d50410b42c1580a0361020207942c0103024016210484000340c045054401102c007030300300e0b007001c2c5c08440422a80d19800d004482190065180410039401003590041400e1104c0f0390391800c000e980000b04003015140d40113440a8115000a030303030389900c0e404030f030008180c107142c0450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597547014 1250 597545764 597545771
    0x507091802040516050a260f151f12140108010e121e070302010213150f0e010905060904060e0c0307020f15130614191401240c1a01050103 61
    0x24a40802040c240107881195110fa13803c3c40e9188005503051780700f05c030b47c0c441501c4402c80e2525441c0140c801482c010b46c423421a00000b428400341c0c0c039107400e54006a40340180c00f198284406040000850341d603034412071400b40d650b0742d26299001d02a1041d1b200702c8003002128000454111810352081403040c058004452000c030000d284c116150180c0b2a009200c03000e4981c43d55010384c6014000e1403218443d200040c81d02c00e0304a25660f40360b15a400c4034030f107001d14a1022140c0c41d00405001c00c0d0601c0350070101d0420605900090010080e8000c85000740030115021000c0d1f10b980d04802c002d855091480d000e10310f050b00b0351140b990004c580318001842444890401d8180107c3d10042c4a540060340140541e5160707001c46200c140c11108844a50307455207100ca5242c0c0b401030301030103014000c440038103a150500c17100060b50440060100744080150041006018846125840350440981300d2422a40444141c03442d0300d45101c090300c04404400074510034510504d0381030681f202600d081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597548264 1250 597547014 597547021
    0xa0501050907060e0904060504240504020108010509270c0402160b2508060105070614040327050d061b0503010503060a0603481503090f0f05070918020405 68
    0x325401614000c4d0103401070268004580450442d400c80c5038840d000d03000c00800c60162044070103c0143c034401500c01160b0380c105007c21503900140e034034010724007184d109844d400d04030000020034080c184131100540e218150042e601d0340c14440f40b2000f0f200104219100c21103406144001c6444c0ca030300711030014041c0c0018900c203040400d90034100882c40384012541c0f440203010703901c05201a00080c140642030000c4400078002d405080750314201010004000d08051401510401e07208903018442141c5040301e2403030001034030030042150301c01c55165448681c03d0070b0440003848a8001030500d4105c05c01c004000e04d410030700550486000ba400c0310081e5854004000c100e40003800010200d00c004201c91400c20070300003040d0300203e04440001581c94540c0413003205600c5614414102d030000710b80c1000b040c8005c5041c8e520045041c1000d1000da4002e540780c107150f41007404024900c0d4602001c01301400400c000040141451b120101310881c00e030f02810400201d41d00d8100d08ca1814003001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597549514 1250 597548264 597548267
    0x12060f010207030b072d050a020c030601050315040c0f0803130e060a0513061701090b0603010c0906080711060408042d09090809030a060e0717071809050a050105090706 74
    0xb0604503a0410700d070051503215088111005900342485880010f1440b10303101810b00c110700a040000700035110180c1c5c9143c3c4c880e0290600640f803080c540b01303422050040090b51008240f004c0c0700080341525180681d250f2610103000280c0d42c000d803d005900880201da0310384000700400d032040140c00f0703a4101581c1d50715101540e51027180d03403d41003101000100400e06040300f030071014090346000400e61649a0000700c244104800c080c0e0b46903912042540140510304a00c941c002800740c00900111440e140040c100440e00d2003030408000c0140c00117a98644a480040c40b0307600f030103081d2011070605060000058026000d040410342d880070f20170010100308443d4500c4040091900b212079880c10f10700100802e002203060310003040400212209036020312881600521506d400280340c10036030055490080260403000500014440400341e019000920008841c0e074540081c0200c500b440c1d401c0d000d00003045005001d88074260076502008010342000703115100860444c0c111540e00c120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597550764 1250 597549514 597549523
    0x2a0702120106080f061612050a1e0c0e12030f130305070b040611190611070602040e0a0b060a0210020a09030b0901051605070206040b071a190c0305040b0a051b12060f0102 75
    0x50359010640140810240620f41d40006602030300900000032050b002c5800e91003442d500c0da2b032a07003079a586d8071401140e090b0000e8401585e80e00903102081c444050811081e6640708400304280e45a80115801c012184059a0180a507910509489440e5a241740c04246600640a01c401241e13022910711040600060740c0100d841e181c0c4601e80300100140c9400b070050081884035100d1200c00c000300c00210b0998002080100803c18800c1114500311031010304403450410030603c03401c0108520440c1d41c0d40060350f1113030b6044c7d40d0300060f0f4440750701d0029100104039510040510f92210208800c446c17040d4405c9120750003075228802c502510301d101f110984180c10009511030400d0006102c005001009022554811211080c00c1c2c0301592581032032440884009100740c2030034144610304042030060b500100e40c107050610244c00d01d5610081c2d203d02c01041303102610b950300c00040c0c4000304484146001020448020356a08805c450b80060507411101103004488041c0303110300300e510009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597552014 1250 597550764 597550801
    0x501020a120e0a11060c0d021c030507020a171c02070606080712080d0204051f180509040b0910020a260408032206020a0e0103052a0702120106080f06 66
    0x100a40100600d070341d56084c40400b488001a000786042c014a0000c420820003244400e48640050a9842d580a11803042107040c4056000305800e007400c2c000d0b410b400144d0822559400766122000d04160800110903024075403030300402e6021341604409600440c0c1c0100303003d60080b0070078003a0545032030f42c80c0d541d12030307911801020200965408020403481405003d02000701c94025141640d11030020b8403614809441150800d55008507000141c0c11040903485041c4900c264a510792800e4000391900000502c0503104c100720f007001410f421800e2101c2507012490fa1021510380c3c900d400000d00442c95444036100704000c0902010845409211481c031466010804c0d030715540c0c6800a149103505400480409021004108400100a8005007009010542c0c1d41e41c01c51003010001006e030741e00038104240c048011884200031b4003861000302d001081c6c1007401681d981c1c02e88007140140341041407100165181150208200b05c0101ea040341203407d200c1107503002e4540304001130b0740a1055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597553264 1250 597552014 597552041
    0x4060506031f0f0f05120609030301053f150c220e090607080c03100501030c05070602040b070b1e130804150e040e0304030f060504020d020a030501020a12 68
    0x50001034099410020740301092600c0c002058000355440c01500c190060701c0d00071300c0381a98458824003140c104410802256845080140021300b41006080e45902c03040c0950360069000d8107003420500541c0428803403180e8489210480c603040ca54064003901020328284200b40920100c85002020340b80c5264052001e4040d510b10300b000c02c102d2840304407494410314107201c040035000205d210154203954841c2c8070110203044145002c80005112080040c4040801d22060003403000701c0d0046000402520000c4c02e00090b44203050340103641c0d030700610300000c1050b400000d011403030388100c0000c0c0040c1841108440a55141c821684483c104004503424400d82244000b88541008650b540859400340709640c1c81c003074850f40461040100c01c4c800c00c010440340b800394807260400340b284071088061800a1800c10781166036a102c4a401401d000d40010b850390041001c0d581c64000c1c0c2008154002c00f158003641d070300c1c40c109010703402c9401d644002c5407450034a0342c0d1081f0700c0c3c041e0351802c1245 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597554514 1250 597553264 597553267
    0x30d050117120d0b0d1a1f03050a0204150b0d1e020a17061302070f0b0610122007050a050105072307060b040c031401080109050706050d2702090604060506 68
    0x400385003c018802002c80507800031950240c1004202019104000141951912aa83d14260705079080454001ca070411003400d641c141040850310100c0e8607030b091f543c110f0340400c009650900081e941e107030070f800860103480004bd02805040c116807000d02d001508989031203e41403c1c0c1a03a0040340260a4480e0114558416802c01d5501c20a07015902508c014403210100e141122607034102e8200c003108540700400c4084a0b02400303880c403800346c1d02050455050042981c084d10003060000c0d6140366846858035190b0f8000034860891480d074143c51400c03aa261158070b00c1c10125038690051200b078406529100124030090b03c1140400c0741d26148901c2d0103510b140704000c002869000443c16640c0c0341d6146100c10807640e0324042d5103032411469802062901f503141101e9208070060740030724001d0b0314024241002900c04100401120503a080c00c0f512071200709507140107000a021107808250001041c42010926080700d10300032402a10f01511070360b00d40702408225001400307103c2d0301620 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597555764 1250 597554514 597554527
    0x403200604050d050f0a03170a1b051e190801060311041403030d5910020309420601110102040f0305010b060403030c23030d05011712 59
    0x4116440403c098420300848400c1c01c03035841020700307006440390202e000a0255064032250801070706095040091030300c04101d403c8445c242d00c0789092804001c1400d21101080009041c8085070558115418400013255900e454480c040395000c040f59010300030031103030000850716074483d100d4a03019164001503149054100940d01c440500000000755140c481000015002d400500481050030540210b850080b441c50400c1580c29101940040c50741c030740c02d10344c0a400301c164042d0040030555900030f11041194a20018100b00050f00189181c3d40000180909440c0000703489280b403480503113a58a810024038072100740f01c80c94003e80c4c0f042400d005151b80700c0121045803a001030050401c03544104a681c040e50a82e0060751102e02040b034503403801c0003404400e02601040c0700701210050325040c1541c2d005001d40222240150800c41000c0d1a070855841c40e29141400900390030880f0b0700c0703407008076660020f0326003405240c2000000d042c580c40b0200d000110440c0200b20980ea060519a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597557014 1250 597555764 597555769
    0x1903080606070c080a06090b0106050a090b0a140703021c050408030307110313030c050a0b0405061b15090a140105010f12060b06030c370e0301090203010c05040320060405 75
    0x104484410307220fa00d2800000507102c0300c20030005a48904c18a0302294104050502c0d00381900164007200034410208105850141e02c80710360702c140c0d948a10380507103c8030020303000c131004031000c03101d82513010000070308034141a0001781001d020503125000c51041012004101d502d8080d5203d103212035441800803884071409461180038a8189004513401d01c0140d801000c05c0d0388641d8816100d04003a0751040c411818101141e03006040703c60082740c685032520021800e1032188010040c418440d6000b440701d86c0d00c007031001c804042c0c044401001da50030300111080e11030000c1302e0125020b051030f501c503110841060207050f04a0340307015506c8400d117142112403916690000400c40e8416541c010340c480720303a01c640203103000f8115101c60303d40328007ca13802120003040c1000028400c1000401da003030001240041000008101d02d8000140e40025020078058241000004c0d81542808802070965034804082c000300d074001e0754800c04003156540c2402003030311185081e50700184100014003a90 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597558264 1250 597557014 597557017
    0x1209120d0203130c0605070303110f1b0c0409080a032d0b03100c0206191811120706030c0e0901081504050a12120b040219030e0a0503030412021903080606 68
    0x455420204030f11005940c0c1c40031071644958100c40d012410224100081c103070b040c0b00e0884540d81c607514072840d20800d280b0b420790030f02403c3d2411103103882c60a501d1000f03580c01c0c0205444040f025200b44050201460302c80401e030051410900002e00c1c10441c640000d0ac400e00b04042e42104201c55544c039150340007100c014010283d41560580314101c1c00b80348100c0248a00e12038a0174640c041c050904001d4140f200b2100803003620140740b400c00a4940b844034034549941d40c100c1d40080c400c44034122040224520940c0c19a40343d103640202e241c0011401e0301600320b507404030034907a190410041d8800402414401c00e00500c84181c0c0a11000c202c104411a80a038000f80982d08407080500c3c00d640d01d001490240c0051000203a600b064400061240d020301c04048604607819810100c041e480c400c10801150701440c101625200c1c101003480e81840104180d1f50007200b62581d914240c05c01280081890403507000522402002200d18682c0006980080758166600c031410f0705d17070307c0811220b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597559514 1250 597558264 597558271
    0xc030b061204021516110301050108060f011e0801021606050601210b011803110f0d050c090c0c0114010f080c01021c3015050f011103070c0b1209120d0203 68
    0xd44004100780e20084030001148101170348a01024a00d2105240c10315003540c0d01a48400b425074015000d000c07020b080010054191010f078008812244002c030504054044168488000d9501c001120080031a00d584000d8400380607103805e010b280c0b1410b00440e003202110407500e004800300164584903190b941c124540c0041c0500d000c14070080c1c000c4214100300780580c021130318000d40304004595820003100c9120f0f5142d0845210050a400e0788400313895000208200d849100c40d100002d514403524410396000b01c42980c02001802024140e49405400a004110f048040007000003452540080c089040c0d0340c042e8080c1c00003003143c090030441150544141828013200303090050310a030380c90252038280c04d40c54a0603110303200e0482448080700d002844100c01c0650f162018000364466201404184400f8a0202000d0b1000c1c11103504500901e6401001c0030200d0074006100002e20f405058290704600c500e503603a80301d5603041a5110040c14804004000070702c0309030366160701c0303034091030340b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597560764 1250 597559514 597559549
    0xc0714101b0b010b120f0402180721020c060a0903140f0706110a0e01090e13060e0118020102070f03031403060d0b2818140f060a0c030b06120402 64
    0x114010700e03a9031010484098114070320900021550194803e40c00701000c0c2c0001b6100d11185560401d80c011401d04051140100403881e41900480d001034800c9900c40044210240040a1240f590840b040030f0b40c0b002c888100944500401b26500151502c640300c411503158880322800c00309003036200155002441c0d03440340d091080c4100700114046001d0010028450402c40303684010311a03010700081c1003845083c0c100400c5120238440307200507503030702070b00084174150841c0711060915050014200b865550103c550a00280d150380402e840c0401c2c0b00c40b4400d070240c1d00502c0e00c03000c40d4240c081c00d03440301600003450801c440750382c49403c10080d9004034010741a1505801d041c0c40b90258008140e400c50442490088400710201c800010401c028940c44000e04c64280f50080c3c202c82856500d0003c1c15048016000f0001c82d4000c00c482d4035400c0940c8140c0c0e04914108028200400c0b0303410384080401d0402110340f40f0391030f01100711250002034144440309034465800744490011a00030303a45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597562014 1250 597560764 597560807
    0x519030e250303030f090c0311120f0a2f06071e030806040e010e070e2e06020d0e03060a0c020f03070b0405070f080a030f09050d080c071410 62
    0x10201c101c0e1901014601c880080104540b41d0324008003110152560052030510380442100001e07104124601103039044001240c0402c442000640c9902d4080c46000c030b01d201b21150118040e4001c6000c5990501407041800840c004260b41940442c1c40c24100c2044c032002980c138100351503d100900f18042c050702000a1031201250303010a040b070064402d80201d1141d0f42005840d14090003600a0b103444000207100c0501408003403079031100c0d980a284054420100050340180e44400402225000c0c02c1040c0e80390f82c050705001002004d94012000107002308d891005000c4c1c0111012402c0040c054002c0c9186d079201c00380c4000034803490030300600f18002c40081901003041040904002806144641128101494143d140c49090351200c411160908010810fa40000c10b000d035244c0d40600b01140380e4100300c81d0840c1c10303000c40d40002da4040c00d00f400a5092003191030192001c100e02c40d0898004d0f40d1a104000603130051107005681c844420750040e0416441104440049500d902048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597563264 1250 597562014 597562033
    0xf030c1706041212020f0d0f0c0f12090b1306050c070b0f070c080301090e010b030c030703080c0c090a050a1404020603060d030210090311060c04050f1e090a0203160519030e 76
    0x70181d86c0000180248203001085410341c2000c9440f0b1a520160701031010414000c0090b406811440d0742c829401c00e004c21869032140c5410fa5420084030a644004c0450030362030040c0130600451101c08040c1c565514100015460040980803512119040709291029950b0891b40b056030074402450202080700c0040008002070017400610302030701381c842020603004118014503007140e18046180307110394081950640d0030f4a0100f02c01007a207030020070351561211007405552608501c10007268100b80020b0802c0300d03e04d15a031005005000740c45c414894030700d09607000f502c0040c095401a60114041002c5002441d15180c4100070318880d005a6040b40e0244038440c00320780d44c0324400da0100300c04180342c0c1c055240c01d201c0654081e40c03103a40141440d0410002c100f18500c900c1c19070f07010b078446840c900820000b40c330340036121000c0204280d000b80380202050000c2c1d002a90031880b91040000d51400d1540114241c4014840110409681c1540c505040f400b03040300581865280c050001407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597564514 1250 597563264 597563297
    0x1020904060828080a0503180a0302010c120506090f06040f2a0203160807140102030a1a03070302181308040f060905090c0702190f0f030c17060412 65
    0x40e40014141c0c1406421410307854800501002c540640503107004070010f102070f0004044809a91884c01985072072502c075a0b60121040c45c00c01015106145445218003d034101641500415212000b5648240e100b0b05c4420559060b15015120551b1000c165800038a01d003e1032050070341c1c0503400802c049200c0030b44151703e904965609070380c1040c1c1c0c0f20f881d5a00b0f0032a034514094401040041c4001e520700340c0c40604459180445450052501400080707180911482008107034001c4040002195a81441c00341e01c001043c2190050304003051b040410307400da00c0c01107003503411a40c014041e0500118a54000c0361203002c020320503196025208403003c045030740000a000501a001c401c80e0086060110242105000c0d901013440b9030b041000700201c480002054907001581516040c0050340e0190385100d1a503101e0f0441c02d055803410708000b4080385180c05200031640510010606240c903444d40140c5d00140d030349041495400440800c00146610340c840e2100c1c141d500d08006803040c01e486 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597565764 1250 597564514 597564521
    0xf070f030311070f1e030c08030405100f05100905060112020706090f0b070801050a0b041e08010c02100b040612140c04110406110d021c030e010207051c14040e0901020904 75
    0x1802c2d074511030945030000420090385e4030b40e2464450048402d001880315a0300500703404505600415034180480400c00b0480104402c3c0350680100809212061003401c6076802040f0484000105d00c3d40c42400107200c04003481014001c0d1410b945888100440e98484006580260700855015070345500010110740641c0307528401781e100398104206c6003031010000b8520310043e04030703d00c110f944000400441c0c210b1011070301182d80040d445003007074000c0c04150141c0d503c81e0b400a00c15500b030042000d2010f9001c16070940d180c010200400121140138240001c5450318040c0c04050101c4540c0c42020400301101141d581c0030050031940398121308008901502c00480e2104a0810086005d210716900702200040b00031251005242c88090b01d04000e40d2001048441d641000d6942d1071030812510a030040c04c807441c0c4d040000c1d55544100e15010365509950803c08035403804c0c3d0b12610002900c20030240300307180303140c08581d82401d00b050020300305840017900381c1c0c1096500304903680c001d0b2201d01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597567014 1250 597565764 597565777
    0x140703090e01030c2c0613020c0607110d08010b090f1c0c090e0114040311010603140a03091a07120e0d0501050403090506090109150e03060a061503020f070f030311 72
    0x4000c0481880e0a11404040542c001030b198200172030106114a00004024507034026000c5407500310340c141074200180213114001084819009080c10407100c20b401c50140d0501044445c11101d00c3d0340065004c407010300c1c0a00549982c458200050359240c6455020340d04400002005d0041408041620080c0c03010102011101d1204000b002c0000e449075105105a00350210000d00c040c0300c603400242a01200100020140301000c6c42c00320107000c00b54040000755610111180010107403d40140c1e07a4841184210006485540c001c01d0100e010132584200c0c40c000101b880c240605680d85d01417900301c1c10342000c00c00c002e58980c0c0003d030b52080b160380d440c580560700018842c10203090041c40a4603a0304181e000742000c1100002c036076808030362002222401c0c1941d40610001c0e100449442141c0704841e6450703c14001844008a400d034072890843d00c01c581d40041062070710300160241d000d041e0b984180c0203000d20078440441c0c000300f102c0d40d88a220385070014203888400e005002c19040b18 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597568264 1250 597567014 597567023
    0x9061f1701020c0d030b1e101d040911130b09011205010b0d0303150e0717130602070308150907170a060503030a0c17130501230a0c020102060708010303140703090e0103 74
    0x3d40c140d288074201401d40c405480d06111f804206000c624002c00c02c102c00c5d0301ca04808100c007511050755441e440119428840c90001c00500020659007000150b011020501500c224002d1078008001c2c0b0b0a07105e01c00a1031b401509041d0240c1c1382022205040840c040700f503d595407100000c03269965000c0030101d0491003901c00080300720281c0d41e044020b088940200c80754280c11001e0100303503600076031501e464611417200000d8540d500c0808281c0c1c90056140203103194008a0083c08254000301231364800d07180c09509403c145500810040f6a10301070320190082020601c1e0464040d045609841c2e0064035036101091a03691580071a00d10303403140c09030000180b030031401c0c141000007008a41e1144c00008400d14104003c4903040b45c2080c600380305003030620194170250100700c403490010000030340d01c60145944808181002400c500d14400080b40103009050018900b1400340840d28140c80c0c255907450749a01c040881281c181d88140c409400340301c150f40002031100e0124034014043d5109 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597569514 1250 597568264 597568271
    0x1061d0108100e0c0d0c1809050d0203031b1602090a020c07050a030804090b22090b0f19180b04080a0305090a0302060c13170609061f1701020c0d03 65
    0x1032141450030100d10b0010b8440e06420180100940e101c005039444102900b102c0025071071714503161244000050798130140c0540c65440000303484100c658400c1c1e00090056050b21384190030344000301d8992004070340c8070103c440401ca101d5a520540e0700a4404d040c00e4400700e003654000e0b070300010400c0c41c0442e200d03807025800113000703843c022052003018001c2c14140c81c0d5140d0b007403d558650086000300c3c06a4203441c3d48d01d0810303081c02d50f0384441070441c6034801800020111070300762203030b0042c0420b044190b80d0640803030045035030309465074041071190010b00390014614901000c03a0003d04200610626250502c0d88505d001c1408550880c2c0a24440c280c4199150000f4201505803a0002c0501003660011070385040444c1c0c0100314035a002d9030030300e442507031958110f02c0f1030811350260700200c91007600d103818001581c0340000c0c0c1901446140342222041c0d07030b40074071032810044210b84241008101c80d1080043c0c0c00880e1441b824070342e01500150402000884030b0b41303056910040040000d44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597570764 1250 597569514 597569519
    0x70e07120b060304050c0f0f0f15090d0507050f0f0d0f080903030d0f050f060904030f050d0e100f060b0a030504020f0d0f0c2408040203010e030a090f120218070201061d01 75
    0xd0166087d42100802d07540c0700e20400c1c4000008102e00d91060907117005420820303492102c0c0c2514411110610802003816110400341c0c2071003a5512498001d80c8e00540500c03403000300340e1801014020704840020070315454a039560741c92030a071024002c070851b0101401d10084400355402d101800d81100e4502000401e8441440c150040d1640600303c07008581d082d81c03e1110589078154410360083c1c01d400c200c1c47c42d28103020112854841da40c80d1031443c1c2c1c940814201200390106a113004030701c160b0018881ca007050607421045030814407910505400030007452080e64001d0b0051a803040c00206010140c1d5000c601240b8119001c150407960128071240060402600c00001c00c041c00c0c0390300e81003c0c668201e00c20400440c0340100804203001c103580c0003030110756003508107401c03025022054a4403480100c00103041802c0b1030046481140c5030484c040351032242c0e07400010081d5001443c000d0307034410401000c56000406060b910440d500c07003201254031f218603081440d1240f42e28000e404030350b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597572014 1250 597570764 597570769
    0xf0302131e0e100c08073218030f1e01021e03040c1202010e0904050f07060306060207060e1f1701060c0b091902060904140c0a090503070e07120b060304050c 69
    0x40c48040c0c03031483e0501d44050b48600030742c0800210f903c641582082d5002090f00d450580351501400640b81031960b0700341c034201070761500202a010611031030000803445000b42c41050f4940a240c00030041b20791005c2c180500ea00c031803200115514280e000014903158444d00325007403004a1510040c01807400000703000421990140400082241c144822a4000c3c41c3e4002440b10100c41801440b0b0103140011505201c41882008040b080c08421502d0265031900080d000c0e2000307100d200c0240c000c0240006440e409012000324070640201680890340c02c01d00b41086043c900a40c040c00c00000c414420a4224070508a5000c0e00c0365440c0c1c0c1504245034a0603480700c500051010b0080d40089041c1055104070f1421801415030403a0fa070b03074595061802140041070407031051140401c82800f4024002150001080443e4081d59107045458a035420f15540c2d0b2450320501000146110000780035a02c60f008000c000501c211010920b0040c3d030340010004c0c0c10540c0c00707440e1500884010081e40c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597573264 1250 597572014 597572023
    0x2d031603090509040f0f020a050910090b06040f180e1615110a02010806040e2413080d09020a03061e0e010c0e12030408190b100f0302131e0e 62
    0x10501242d81402a10341940e070550104c90305c0d03c1c0281000e803825221021591900c20303120152001800c11196407420811080460b8002d225072403d20b4907010108005003044000c44040e40d14010710b20241c50f15044200d2501074060351000c1c074982c0c0d01c4552110444041c001480030581052520360007134180100c4c1a12107440703d074000d00340034500070319000c40701010038000d0319540c090800c21030541e100004100a00103602c041030260084840d07240c4414020f9012610640f50b200d90340303032203680780342c1c0e41e0030f01104524000d000c1d4001480079008134210f9400403842c1074805005a210150b5039503408040e211b42a0062080324586007202c402032001e0321400140004034002400440201003000d40110100c42c6c0c0d1901900301c420022069420400458000f0300c802d00131170f980c031882848810a10300c840c5008650840d400c01c0810f0301800300004220a941054000300e12061942d801c00c0040444211025115900c0d903204000320781c240290b09483c6c100111010610101c0d17201c0c1c1a050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597574514 1250 597573264 597573269
    0x6070b060a0305072c1009050a11160303180f0b070c02030703081b0c130f090b070f082535181b04091407060519112d03160309 56
    0x24170448604004815845500c5401240c14800b070004040d2250020324006c2c0441c0158680452400115243c01816507a80c1101441c042d941c00c000400942681c3c2040c01c00c0d03c3c0c3d01034680d10082840c0c4000c1801a80056004901d60030640b031001c7c000e50100b07007012550360007699100000328141c01d820351511156000b0201c1d8101521840305198000750650344000b5405800594494031001c08a440e98001240190040b20030784151400f14001070021088240c0c8070300003012040460034420314040780092458282450b040c284242002c121030b08088420340b10032043e10010810b0084000a1903800240804244002c8601c2c017600c42d0203410b030702e014503c90140e00c82c1c0885000c0710440d079803003410800201c42c0070412107100d082c50101e0115030241e0ba580da028a5000090032034024009204c078504111110b0a520448941500d43c001c07a1a20b180319500a070203603000083c0711405c01202c0f8070740b00121042960203034400c070340346801040c1d18888080000d02c0700703018035030000e600100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597575764 1250 597574514 597574589
    0x20906040e070930170d060e041704030b0f131a04051608060a0903030b0a060305060f120c01080601030f140a1103010b04170c1c020f060906070b060a030507 69
    0x507401d00740d10034001c4c2000960703005817040f0700a0000b81e22450300076080b203454995002061065503184c202180d400300040e142150140c80c841440e14100c50315400751400c40381c102102d86015a80c10800d5644070100400c0200c0d12641d260148002460b05003143c010b002e20300c419035404d81b038549001e5140c1010040b20040c0010502010040e80c1000248161b001e898160086101030481c075043e00a4102850244d034003425003d40450819450b40c8158410002121101041102c0c00c051201c521030806d0801407603046009402c1540d405050701a81140061400013110002044400308840500c20740760602c0c040300741440407020b128040e00740320800c07002d5103901c1d6500d42860081c0c503100328400c21004c0b00301516401d04024050102c100c40a4003c2e0182c9548121100700c007500c5100d114040b48501340c03029100c400d0b806c0c03500c1610401d00d00030b0704e5a49404c0e40303a2100107940e140101003a5000c0c40c40700000c0002030041c42901d006006a1040235810103442c0e103902078070500e0b95641d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597577014 1250 597575764 597575819
    0x50f180f12071403030921060a02070308010501031802090a0c030515280806010b042607060e0409170a081302180c0c0d0f0e0303120604020906040e0709 67
    0x8040c80810b00760300721143c10100340d14080382c500c003090540c0605411507520003080c0100e0302000d03800484107912110b21b0015114141d880010301e008038050880081c001452120041c0010b5000e5401201c040b0b882643d6484690350340c0d030006280f41d000b140d0341161130352149403020034607030036000e00e582003181e03007114801c14500c2c4404a0b04846109100c5ea08410704a6019207a450903a000074001d0901c403010b9076000c0d80c444071122070591162180703401c2d00c0c07503440c0218005542001140d28081d900ca01803e4124504402240c250100804066002d030b40c0b02e0050300020550b960300d13014003e00f0000680c5405050a0203003410b0002407811800104180c05003005070380300400e03100c214803d205122800c1c2c5540008402900034070180c00100d108610006400329080304460503203515943d03c2510950301901130503201d000340d51285420303c460b100410a01d00c2c140c2c0240400d180058000c1c1d040950b40d81c941944a00c0c207a519030040f0b0044d41c000d200c500a03100c00e02c0360464400c1c6010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597578264 1250 597577014 597577039
    0xc12030f150d0816020a0902180907030b030a1b2913031b0e0115050405120a0203071d0c03071b02040e100f0c030501080709020901050f180f 62
    0x806000030024100201c4030009807111509a4840d0300c5040340380c1e0800c8401e61220a0240d1880701c02860440c168032800070a440011900c1060080b103600182d4001e0624000c403648080c0300c1d4010015000c00300781a210142c1e102c554408101e0682c0c800e0141d4406550b640700004001d2020340590804c051052215094801a12648107d40601c0c140d602001e42d035646607102060300e41a0b0b681006108012010f0301000b038082011290080d140715200001c0940da880c40d4040c2c4001c8180640004110300707010030002c92402001c041640003c80c401c0d0313850420755a001908101c1941c015202012808c03050301040c41c2e41100c050751029038642c0c0a0315600f807036500604800c0c17120304c0050018034a411541d0447d140d507080480880c4c1d004080390352007601c07041c0350000741c004500c10400d0185420a80b03103c480c460b00505040b281c40d000070b03000040c10045484080d40c41000040e0500c88100060142c2c014000018103003244030b5900030b80c481000c5020410f62502c0005528410b00001520 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597579514 1250 597578264 597578281
    0x60a0b060f0301060c0f0209040803091b031b0d06050f0103210e190306063008120718180f09020f04020a110f071a04080303010620010603080c1203 65
    0x2124103641311802c24038851845494445050181e2080c000d42110590b01488100305640c0042c6001d82110410b4520002d01d40320382582030302c841140d81e94198881c801c0000c2c81c03c0d8904042c054281c001d02031548125a94039070030180c90054500e490f424032140d00420600140000e8800d11400041c0310000560485c0c20082c8403902e015041480392140c018245501000000040001c5601c004184022507032250f44120b501082e201403455410341c9210f401842c040090590f81c1c4551000080e8146494007520031001b0030014050401d001c2c61128801070050032841410080c80310160040c0b40c450629484010b80d140292001e0b802400c140b001c80060361940c451070f82116041c0e80044e01c0d683c5164044030050401d0000c164180202c110f1104400804200502500c071441d5241001d800740c00102d128600c903d120b00d0800e90014030062246910840803180316100c103039945d010304c000c010790303041c2143d40d941e0044848800c0096403501d6448144959007012500007005411445e0940340b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597580764 1250 597579514 597579517
    0xd020a110411070b0106020d1103160b04022701030201110d140a05090a090b090609070e040504020a0b030702070e010f060c02040f14100504050c03160c030e0d05060a0b060f 76
    0x1030303144075a840c1d03103104a8040b2018140d49465030401c2003e0000d5940b08006901e610941c00340100090005000002e440300010803546880442d425041d03132094641c0720201c00c102c000c3e20032a8002d62071595120071412001104010038000b2042550652440c030000d00207007401d803080c5060303400031008888080d4100040043c9800c0035480d41d030f50f9a40d1400101c800b0b05c030710261541d0143c3c00110100d21040303990b000c240c0c00c80302038406068544600301000300380682220701e8000601c801c01e02103110b05190f00000e4026201903c2900c4903516040300543c9604200c88400c0164409401003080104e0b004240740100340700c0710400c01c0c45052410040030301c0499080640101d40700c143c402034808691703001c1081b06190a6007105035003004140c48003010403070f20410b8032035410300011440c0500b14408403400780a24643c1950001c0c3e81500599a40c0c460f98400d40502140c240c118406446494061011500ca20041d080070319200641d0b0301103c514102ca2806201e041c071400d0728100c5481c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597582014 1250 597580764 597580793
    0x7060203071701080a0f0309180e150408031b040306020a0206070905040e10020309100c0906020d0f0c060c021002190306080c150c030405031c02060f0c03011a0d02030f090d020a 78
    0x9210703120100d036040548c0e003907940340e00030b801c1504102c814100ba0a01940800c05601101040d0348144604101c507003030a038001d0b20060464102000840e22010400e011010301d000d0601c1410306180e41ca848070b0f002c903041108920094bc015001700100346e031340400740ea400742c007084508200c000040d02d825071741c4100c815880c6c001c80c3e42c0080458202207041200500800301c045090040950b8030100400303038540c0d0b1203008007600c04c0c4803d41c440c0c180558a40c15600801303699408420845031114009002c0305540c5409500603a1a9240c40c0480c0d40028802e0003400c45078041e1810640200404440300c0e58804161904442043e019982d0307104802482c8190704241c1c01e4135211005546401d510407640059414412500419000b0b029034000c1045842d0507000d48100c2c1d65442211111035100b10303580c825140040006025030b49440c40e6000020440c0c041c034a04014188031100101e9109407841c102c850b15200c10400c40c0c0004003e07083e882025480901180645592042007040008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597583264 1250 597582014 597582023
    0x40510140d05070f1502060a1b03180c090b030c120c06070c12050610050102030c120f070f20180a0c0509130522020303030609040201031107060203071701080a 70
    0x7491004140601044041c001c0d00e2038400309007000e5500d80944404c41c002002500140c082d810006000c003c02e13103d008030780035130540e18080054188000f1002080303400941c8180d00e10950094010502e02c010401c050003401c0d20000703100106604042c035084400d552644904500c40d10803912180c045070140580000351840c0ea20b400c5249000916294a602701035101c0c0c4c80e03040080c003444000030380540101c5d080c1c0d40c0700c01c0c429210001245c0b20720451045582c20360101c0d101441c960803081c0201000d1a4010b240c506003003107a940c8488809140748240e86503500701c03121000218000c080b0310140002114585900450507100455070740c4000c000510007613039100b204001500400885842a03801030107540c9109880c00360000604060300c06c4180740d0812031058120b400d103034907481c20300c640050007541960755140030089141802230040381096141e05e010070542220380003070076005120321400341c0c486c90300f00b0004044103101103500419a5840340108410784010900b0303015981c02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597584514 1250 597583264 597583279
    0x6131707150e011e09030906140910091a19031404110a0e091e060c120a020c03040f1503020f09040f15060306051507031403150a031104051014 63
    0x55402d128010000710213514201c00000010055803081540001561446a207801d02081c0e02c51390102c50010222054a078000810001241d0a1800010312814540d481c40c003890300c0d82e00c2d40816080c0c1190f03080b407015425004204d15200d5180b196020f460443c031407500700040d4102c68100c0c0e0700c420380a0f0002c0c010f528244408440d036251440088040c0032500b1408096040118180d991502611010740c80001845480941c1103004140310740030303162180c40340f030130071450041c50440104050038000c8001e07030030411780a40b4030741400a00024100303988080070241c6000385202a4000d072a050604251041010300780200d4101d0a95098810950b400544242010604001895482805840110b0030b840010321258136410100558000b81c030300702d0500119141c640f4041c0140480140451851b00d00406403002c11001f4561001c440401c6100b003403101c401180500b0581c0d00180d543c0c4003030942c0e040a038241401030030f4015607440400c5d03c0503850a11416404045a030149200341c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597585764 1250 597584514 597584531
    0x503300a02190510051e1608221202160806100b07020622080714030706030c18081005010803090108060f060405060f041a0304050a02010c020607050613170715 70
    0x3040282c80d5900c3d01c0480104024107110252100780080c5d1b06d000105030180000240000402074840200110385807035550f2a6110711107900c2103091448941e2000b440d14002c070700007051203d902002600c200fa000f4015a0707104074180070070000c0c03c1c0c11003080c1e50b0001d4244118034030201148021201c40c41c9a194030780b01e01348005811446151003000c3e4400b034070390200a66140c6c4c1494203046400f442c045070943c55980082820030980d02c590a903242d00141c104105240c0a900844150a0107182c4a5454401041800c4403c0c1c525000b10300150b1107441100d8801c0d01501c24030340904a50b50065040210400000703007200e10051040f8002c44a02000e400180c81d500b0680707028200080c9415143c0044080140b2240c01c20f115116408030100121152954548100d038081c1e40c124020b070145c000036400660b01c01e51103450481e081b039820400100032550501c61503001c4c81c030f008100e855540290030000304160f4001c0c54800100380401144002511118a01c206800360002c04a1000d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597587014 1250 597585764 597585773
    0x7080a050415050a0614030a1703130f050312060108010825050406030b0a11041203030209060702041407020607020708150c040b03090706180b0301050607020a0503300a0219 76
    0x5002440300e401d00340fa00b80600d608a5811100c00c0e16164941e440040d08424109036442c0c0c0c200c00f014048150f0820b80300740c669200c0740251fa1080d0034203840141c1803465518142c000c001e0302820780b060b07080820303c0701c07603041d040e546290050801d1a00c01401e505107940943c0310300258200d0342441c1141c05444040c0b40035400070000800c0c00810400510340e9a003054102034000720740c81c0310014a801c10740040d000b1a4000e03201611403400381740d5400144ca0b50305600942c8946440c99000c0010f0084030010b0f503c170f01412038010886007512040341030050700a0714040300500741c1402d640110b04240315010000410500c0d01c1908501000143c41714100c0d4141d62040d5042546803440000800049000018580d8100c80243ea20700c00424030000000358956514000d8502d00e0f0010401004589080c0d409002c03200d0004058a1b841640c40000910b00303e08082030300ca42003031041c1e000b11040040c0710041c1403403d0307100000d13284c4171014400a440309040840b060303140c0780301d0301c100d410300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597588264 1250 597587014 597587033
    0x403020f0126090a051c0c0f030507080d0b011b05030a180509011d0903160605042103050105120a0b0105010807110d030f0c02010218010518031f1407080a0504 70
    0x1d40020b04140380790805201c40c03a00d0f000181c00581d400e00c501940e05d407004192a2103600d460102d40c1c0c504441003850742c0c070640212001d0a0540c2084010f0200b800407844000003410012a81c03000041d514100b10001f600c860b10510401441032068030012012950201c104c0d4641401e48c540f4600615180d9007000c0905500d40105030000b60a400104e1001c0d000b46034020081c01035007521882d0743c0c500d950580c0c0e034030510380800c00711443d800c0c1d0b960014171280c0099401030321030781d0011600241034244000c007090b45140440080d49940042009040035005946030305010005095003641503105c02c070441e4418800e280c108204113000500c941d100304250b4610803410002d1341c2441c07401b980010083c10158150006042c038040b03018030824014407c50f03035480002000c00300081212001512550003a600d01544101000701d0313049190307001e00200e090200801070402050000d181e0040031180540002c10221410000f072000494001200b9a07209004540104d000d45c0c0d42c0c80c2040c3c0c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597589514 1250 597588264 597588317
    0xf01051003060812030a050105100212031009020a080601140708030420030604060905060609070e0f060d0e012309071208040329090c012120030a0c03020403020f01 72
    0x1d800f40348201c07a0031091352402540a0000140c05100e141d07226410429411004513646016a011107002414031100d0009150b104031000080610b182ea180e019409130b92140c1010b100065581c010030034950380085c04003100b211514101810013210385d032580c88610000d0b00142c0940c010440d80f0040c4002d00c0609203008071b0140c2035810034245458118050300203081d0444a80c0502e4001943e0350400440141c4281c01607500d400411500c0d006101c1c0b5000100040c3d03400440422510415081c6030080e144d6101c80000000751018171041c0340c81c000980b0050b0f103001c0002000502450000c005160b0098038100410003592960a140412041c440c0b03070300080c01c0c01040380c4160f80d0440c801c402c001003251034031480c2d8029642c081410380c540d046c40f400306e40032075008001d041520701641e00d0810810007030800040e03007000100e4640c154084d03040805203500400020040d1101050044180c04e1902e4102941814210381c0001d20308001c01d03811034104145d145500d109804201c446c000c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597590764 1250 597589514 597589529
    0x30a0e040209120703210c0b090c03030a020d1d0f01080a02070f060903080f010303140901120e0a050d0207050307030818100201020d180809060310090515090603060f0105100306 78
    0x143c5480c500207080d1034030114842910b20180c0c1510b0440d0321800602074401c04012940c2d40200b0030039a80e5504034822000d00a9020b41c420030b454010551020002404660300c103030010301c074403111132400a0040000c6440b125200d015265030044540b0b0b0101c1620b03954a0900344040c2d26512454064001e010b075150181a07059480860420b004070703035004500a6019685400c005d548601048515035800c0c8001400240011162564005490040d0501400524080c61800304d8241d802095509440c030703250742a00002c444004000007000f03042c0ca032401500150020382c2c030b0500029182d00041c800a07104610008070b100441040388588110340b58010880c0d0441c10442c10000d00039003140b10209180751402c00d40104503a503900c60400359541c850a0703140b80c50b040000307000c0302d500041c02d00d80d01ca80e00c1c5034000c500000540904c0b845401003021451800d0790b0502040000180548002d002c2e8202506025040e101c2540c618150380341a50030000484905000304c00034003890b4403101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597592014 1250 597590764 597590779
    0x5211c020f0d150510080f01171501090e070806040b070f0c080a0201050118090b04060903031503210516030309050304050303271f0f0201090b1315020408030a0e040209 74
    0x220000741800c150702c213880c0f007515000d14103024282c0035a142d00301a58651009228040108120b01c0503000180180a00c0d2050b148504107025a41006030b070b082c1c0104c02c29a0325409001d229041c2004bd2100905110005040608058a03840d400c41c034090305500402c0144407201c10b0160199a40300503090f44680000e945052780702d0028020002030091848003803070f4034205000702c202030041c1100190031407012140c5445a0b504c800051030f41000440a05840790a2641c2c5038907840410002180202022164007007402c0145c812003180e80c02c500c0074800e0a200a20f0202d02c5040d42400e40303541818005200ba100e410038074654040c9038425980351100044c40180042960b51801c0080701080b400e0341031040107001c0001c036000c0c100c144181070305070350304c14030210740706ea055818060420b00001400345815241c00303103081380c212100d200c0b03540900000810060105840160308840308800c500701030802e408030380c0740d12034010014104008190225120740d1690304880300c14500405a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597593264 1250 597592014 597592031
    0xb0d141204090b01020d03060828050717011103011406070201110f030c070902090105030c0d1b050307020f010515040f0608100b100f09050d0501020903060405211c020f0d 75
    0xd0307000e4201d03c58400e006008590030605040e00078010041076414100c09000d0101000600800c514481030f03480c61040c1c041602103003c50740a100c044040c0508020101011090600c018252520400501c81c02c010800c010018403540e089140014402220b00076551403e03400121038981e8013026021207806004010032440c2400001464800080300503101140e81d01d03403d42080f801400d443e10302180c01007000030042071a4800404034a4525074000a070307904200c0d005150746080c040094045000041808680d5404004070b104c4420114000d000b10329140e5a000e541000190400c1d008a8540a10020080290b04a0005403c1c441c0032510700f154440c05e903802605006510501442942401050940c03041200c040c03441165121500541c0c640028000c405250f40e405484030356013440782401981c4e05019440c003941c0500300910b600d4011040d414009152515400154002000000c0d58102c01392905251480d035000c0058a071428070a001d80144188041c1c030300c82500d0840b08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597594514 1250 597593264 597593279
    0x103020919080c010309080d02030402130207030203030403091e030305090f0d0c03021906080c0d0b100306050a1706041b0e040f030807030e100b030106051815040b0d141204 76
    0x1101260b00754011034418020510054084411120001d000d40c2c404201d00c1c0f4032441d25170015504940301414144440040c080b15000305e800a42c012001600000f00b030009165000c00c1a00252068048000c5181d542180e1301081c0a0740703100040030b1180100f03603c2069550741c125510030200280c19280c0030030507840d03d40d043d0040e40c00224030071620844440c070f0500040d95030900707441d1541c035250510f0300e844081444540142c03008207546911003851760425100e51781890a2001c042d1004658241090100080f000c5070740c000300340c1c1244001b400105810000b031201d4100f90007240c550002c01c5007450410b0b102807190000f62048409e40180010480010401f455907402070760741100c40e40700c8400450aa849444c83d503645540201c82404641901d94080c1032081d030010b0001034865a0743c1c01003009810410380c450714500d04402007010a8080141c0e25900381da0458080261104035000207041820308000542941800004181c5400c4200080c00c80c01126408540d15980c2c2c032000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597595764 1250 597594514 597594559
    0xb040510031a03070803090312070f0308331002161a2803060602070b07060519110406030b0d08030c030c071506030201020114010b041404151205060c07050d03050601030209 76
    0xc064042e224002d5030f4251002c520050b14a0ac0c0c1c7d004403039908240b000e48007200c5230b94001e40005800d5441cce02042c4951414901d14800c144170702c04000d0b9460408404221007240d01c5210b146c2035411802c0000c0c080074908410405440078213500b400100d080710f1003d841c1e4000e00b0b01c0c01211450304100301005d441804030750030403030340140c0e0b0034480140c0b80e400498503803a00d4031504203100340a004640008556412103a8494101c9004006c2807054032004426541402c6003505050350001d814405158580581011840c003510203c0c64280d0643d90340005200061140b1804600071000c24440380e20001141c44680c0c20240f2051601c070651001001030000b8442240550320f8103000f02c000709081d03a40a8100c52007940c0070b0b41001c0c5030080621103114103000842d842691036100404000c041080c030000361400e1070b90320a101c00070b4600f062a000340079044030512041800000006500000c88043c10700c803924010426403580340050307000c0d0154030f6803540d008807140711207400c0b01d40050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597597014 1250 597595764 597595777
    0x30606110a05250e090303180309060703050c01022a0f1b0d0c08070b0306090a05130605070201090f06050703111810030f0e0a0b0114130908090d05160b040510031a03070803 76
    0x14172a403040c5030b08e101a554906c51804540e41100c001d000400c00300740190054180390309000009860300052443d101000001d03002010350070381001002c640c00140801c014880315490310000c02e03c0c101d481405031080803500001c68401c20510724144200005004914000c017280c408840c20242c94591805064008031422802009100300140707011440f4001c0038022864007000300208400750301c441000c0c0c440200140e00799900da0801c1d05c005080f08000b03e0042d80103490004243c1401000181581c840000746d01e8401c4040c44500e01e0200d01d46031041081c54200c603c00c0d00b254089c1000d4000e803c04d4400342c002d46140014010901c007000c40c81002c0a41324140d1400320340c0e02c031501450b02d00011000707550840c5003642d6005120205500003410680a0101c0a0802078140700140540c903003240c0485440d00040444c50180c0030703c8000e00c0c01741020098031402e2500300004180030b014101480001c05450f00301c9004a40340741d0056120415025050302c07903094503a41c807541e0f241e200c1c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597598264 1250 597597014 597597031
    0x40806070804060b060304030c02040e031e03180708100207031b0809040c051305121507050406031506122004081b040501151d090106030606110a05250e090303 70
    0x1e242e00143c50145e040324400e42d4180c032501e02d191a9038003071100030100d240700e1075007512042020542907201141060032a00200c60056660b180c0b10302c0340c41d8813403e900362500b040e038090041400040804601100c13403041c080c0006848a0640c1021540100081148a1071100c400907130b8080c0908440103048801c015101484120700e0180304407841c2c03080030040403803140c140005000c0c51600d003080800403400441180c980300c0c0404807500850100f5120080400d000150402540f41c00d07010304045c214420300083c203214074001d00a852103030081098844241d070760446c101500e000400300030b00300d00c13540752058990751641d01072950394503007620404c0d861910004404491410b070051034145c60310702030325083e41c003144842030f1000b500c6500000007485104821082c01d444a030070150013010107a40c0800c5a070714005005d4605c051000881c4840d801000d070100201b0340005202c80442d8003400900205082414240003c010603006213012441c072106101914070000007071801003100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597599514 1250 597598264 597598271
    0xf0501030803240603060103020a020106150e120102030105150c160f06110613020d080714031e13050108060d06050405010204210c0302040203070507020415150320030c04080607080406 81
    0x150401c1c400842d103100c1030f15034009401c0002803001e510070f801a084002440c0004914070741c442110741c00c09151582c0d103000007640029041442c1c03422005012a400e80c1e81c0c000c40c80e650520f00410100010100c40d0305a04000080800e990403041101419600c104502c0c5241036072910040388880d0401e220300e00010301c03042c06561249102041243c014600864035004491081d0b0900150041e0400191440c2c403083c01241d010580080e003138081c070742e502d001035540c5040c1200039034465404e00c808000e10401c24000162201b0503045140190380c4242000d00c030a03520000041c04c541c1c055a40204141d090800307120411030150054802d40b41081c01d0828000005580c0c0300c40441c0d0040040c1442681c1c1e041000542072541c0219040003142c50440e01c0e200701c0b074000c0f40998103030504400301c001000401b0041d5a01220003640070b0406841c082c094406104151110120300403101c80341c1103400008600d04006140071500103181c5c941c192910361425000140040e84221010b40b030366801c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597600764 1250 597599514 597599551
    0x40f0317120a0f0b10080a051b1b190b0402040e07081614030a030203180409060e0a020f04050606040b090402091f02240f04110a080c13020f03060d03030f0501030803 73
    0x7031a96081505c0841c0f59500340d031a50301e2040c3d002c0640005400100100401600c0e801e51703c5903000200003e10158480280c080c070344440b400d2424070750400000c400c0c0011150040051060b59015420580482300443d01c01410302e410350501ca0300b0343c40b24245218400803402c1741104408041e084450001d81007408520200a064031b6058a20380100103030002c00c42845e60301d1040d180402445d070050700c00180b40d401c83c3d8032141214142001c0c00815440507500404500d410104c008c4109007d0324103000e94201140820301d207018038003234400c103188041030500e0951a154103841d02404010405100300c2c0d030080481c1c100090390204840180140c103140212603e6503048041c00c50007042ca0a109940d5270905d90341d14101c0908110703144101c10742081916a03407401110058003264000d880050844070030014170b845142ca481d0601c0e070052014101010003501030740d0380404c042e1083c543c400407600c5d0490081500140001d0700d1460324001106000b0608040e40c880c010b2010a000302e4607 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597602014 1250 597600764 597600769
    0xc03010606120b0a150c060905150103061d07050f061201030f0b07051305120f0706020f0c010e09010603020906070606060c1518320303040611040f0317120a0f0b 71
    0x1c0b05070280d0300d0001200c5d00d02e50b0b0307501d100d20307442c0a403280030340800201c280c040d41e01d4030705000344c0307104d40d01d0032403070300300061091101790710441340c101804106014a4402101031951144240e01c03071180314044680c0710f00010f031940310450395500102010b090481d03840b8648102200003e650607100c0c0080c80300090300c0c80303028100312031452110b183c030b0010035031622003001842c041244852100e409030300d81007420420100005006405103401411084c2c0e100c20407207140c0315000103660304100411515061603101c1c10403c40c15961545405640d4682010120380603200c3d400b00100064030300800081c05070b0344005440003ca12566540f41ca1114440002c420f448907204405038100c007160039030001948000c2c09004032a0300c18841400740d0310800038031f24210964828208e00d50000001c22042010b94420b4099895084403c00d0038207040000301d4200101c13901008009140c5041c0e41300c01540d12005407041ca68190104c0c2c2e8039440c10000c2040500341d51030308071503950f040c0841e486861 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597603264 1250 597602014 597602029
    0x6090f1207110405070309060e0a020102011b14030c04030f0b0a0501060302070519170c010501140d0305180a180c03141302090a0b0d03050a022a040c020c03010606120b 74
    0x250081c2005a0200e001000c1000429003d00650203250b1f5078403103940081c0c0c89000f51604031114001400307400d08140000b90a5480080c41010210540c4034151140781e00a84000c0300400b80c902c0c4070340c0b03070368401000100c140b007507800c00750880100940c01410003440950141c4106120070741170000d640c0c0c4503015000e80c0a00e860080c656081800c404d040f102070891011445800342180d03112103910010814403607070229880c6950781c2d440d03400510181040a158512008040e500c44030b00c0b44030750320018170034002c1003a18079064621454401d1030340d568a41003000b50000700c0d400700c0c3c0110140c400d04024403031031030000046030410501c0d00206000002e008d20400ba4003c04070b00d090010350030400489002018010015515a40281d2607101c000c4409042031183e1509592a10203c001a1401c0e09003a100c3c0c0c1740c0c202d0440c110268500c0e60030754281014040e01c020070001b00e640016414081c00030304030f60f0150300c0c0c0540000c0721175000ac0c11580180c1c40001c200042d4940c1d40038002d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597604514 1250 597603264 597603277
    0x13170717240402120606011b14070f18051902030709030c0b09040506100f0c05030d0c031b0306380a09180b0307030206090612070e150301030f17070605040503030f160e091806090f12 80
    0x41c0c280c1501c0704010ee00341c0c0e002158800742c0c1d40741c005101c80e2a540c0e5402d014500d85c0058101c03180c0801d056885040a02c540c0350000400c56403090010720804008001c0c40700f1151000030450140b0001e02040420801d5518803580381e842032264445084000780100300d2507600d021181070548020000c2c82c064441d42040e1030b0401e002c00000c0580205d014420004552104240c940d0402d071010260080000f4001c00c0341d9a6030750000f507501e449207515510b0160301c486001c3d0392400d10f25202a58001400401700c2c1d078103540181d1a05100e0000a401e401591a020801d81940302000b03003550f401440344158440840b440c102d001110700402501b03000c240001801c02c00da8814803800700b07100000340350280f04448141e034504001603a4400940d5025101150342d0390000c4180600e1a00c03510703405602c1143c810801060502407030004000b21f14030a5141e00418000c4c001c03450048108844d90305040060080f20740500f4104142541c801e00e5500c204101c0c080c1c01e05903800040c5100c01c480300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597605764 1250 597604514 597604531
    0x3020a140a110d23030d09150605011107031e08070b090d11070b0304050309060a080a0605040902063c13170717240402120606011b14070f1805 63
    0x80b4a0340344c82000d03580b2180104081c95a11003801100100b408502501800c0e034868907030002c00c142c00000c00e8050300c56a0700114140710102c51071401c04a0b00060100c2102d0b00b1002c00080e250042c0210034884494441c040c4c140c142c00a95101481100800700c1e006100c1e290495010650a8408403004032003200c12000c83c3d0404001004880101409103400c14019001e17a45001004000125281d00ce0100d030343c0840d10007003c00800c1c4040740b06820040800351002d0003044038aa00143c103a100b8100c041c28406003281d101560040c031000751707800e203404000224540d100005030514081d08000c41e421500290a0000314500e81503168060111041c2002008031504040880902c126800811120351151500020200c1c2e54100c00005114040b078040c685400d0030700521801c10613000ca10a6698802028000b00d41d9020744c03510740406680c004143c0381d4044d460210b02005201c0c0c420146c6218507840403807071002d40300c1190110b0340a610185d0345445020500c40554008441508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597607014 1250 597605764 597605783
    0x1080303070807030b06180f090403230406170714040602030d0e0c03070605030c0706021b01180201020c06090609090a050708010f050d02010c050c1f02010c030b0603040f03020a140a110d 82
    0x440b01a00380b010913121f600800a01c2a070182001003a580d0008807003e0740010101c1c0c2c00481e0800147c920038140c0300e030144103645480c0c20404094807403071820300030054418a2400040c00144100c2c1d52052200521410395030b1665100402503580d0040000100400d140c001c00d400c0c20a000101c14405c0038014000d05111031501e00d0035640d541000f00108004a02007041d0000142248000c00200300c40b10ba080c03511a002c515a0340c212030704420480c4130310755520034810250303030006145541c0b91011200340d5a2114500d010505500401d40390b01d40028510091010130512a04440c0c8144000e0392400a603a9803000b4941c8041414451141c000d00480f02e4203016510a500c070480041c000c200701d89680105902146002460140c200084218002950707c204d90a0059900c04019480d003849040c03000c0000074071620002d030008060001032621001018000c1c004250794980008440725140305080200d6101e500499003204d500704d400c1300d5200113143c10301e80800415080a241c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597608264 1250 597607014 597607027
    0x70b090f04020c162903040c0b0a2006010e060d120c0f20100513090e0109050709140a050405030a0c170c2815051e01080303070807030b06 61
    0x80003d60181049a10901580208010b00c0d45401031000081c102e60701503444d00404040c003401c9240c85406001d420070004c109010100c1d5000c16407200396144c0c8030540d540d405e4190b80690344041c540b4038031031503d01c6451484190f00408260745040720100704003d00c172962840108501484420b8000f0321410b42c8415040c0d00520480f81407000910940314030340400c1c1c040e2651200c5d1000800841588100c0740c0440c4211700b021302d010121078401d4205141440c04490002c4030f004180d0141006940e99454070564941c000d400c1a19400d40203000d503420b071901ca03004c10019000b0200b1101075080b00c1d401140c0c140000e4480d07103104541260296042c0404030500321059100503000f0b0311325500008000741c0d05659907004000482c2400003e183c1480c400a0a54840c079841164107145411580f038000031928403005d008122010480000302c96440382c202c803008070580c00f5519a018103c00000c90400d200000a50041da015100c02d801d40d52061000c9040d90502c5240507080381013807048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597609514 1250 597608264 597608269
    0x7030c1d040204030f0b1b041a030907031b09060509010b030f1f090f05160801060c1401020304060603030219110409060605091509070507120806060c0a0b09070b090f 73
    0x521003045002440545003960302e845482440c2c000765400d6502c0c440400a04c1054001340040c0e00103003842451441c20315242c090340e00c050101c40d2113025490134002000032686003007881400f025523400324031281c006440c803c51607103a10389070007104103491070204046400e03d0308070300c59812182035164503499a80c0d50404070022001c0130b01100b040c41c0407070400c466071148510b0500c016008001002030b0340c07009284076905584e0090041140e0a220311071803040940d1005240b07043d60300d5420010005100740c40e1081040c0c1d0000d50b0500307194800310601003041102e070410b0040764025400c5031824203001e0001e000707805405500400b03400810080c0603050400350001141035001d2400040e410341d0380c1010691044003201c100103008031120006056142500c0b003203400c9200d03441c00e00d040594940d030306c858442211554a0074468914000740341da540700401c441441c69443e0a0702d070150701c0c0d8038008110400a944282040c0a83e90340490f190301500207542c900b1400400407902ca040c800203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597610764 1250 597609514 597609557
    0x16080c04170f0f1020070b060d050a030c060e030a020601032006040920030705030a02030a06240906020c060937030312020c0607030e0304081203010e07030c 69
    0x8003a00d03900640c038110b41001410b0160b903000032680c10207014144140c002c1c280465000b00344a107a00005180043c0136680508240c0d01b400fa84054914030503160500001c203041c051070300080c002c2c8121081c220402d580650342240c50391041d06e051114580c17485039541c80c2d0042c184000300581c030010040000c01d0280c0e0030612a0300b445103040011a1403000407500a80c0716070010300c500f90302d45400c1c00540840341c0e14170310510b0504061500f58104442c000305a4807001d00b404d6003641d00800800c10034440760b80480c0c01803041900741424503d0b040c40c1c4894004107246000c020406080000841d07600114103409070000040803117140c0b0000d5010081c600302d1099003548004282e00c600c1c175202001e588180001241d0a003d85407031450352034000c2c0307006100e03074007007030314600500451462000004001b50041e0b218200403411101a043e203c2c654011580070041da481980701c00c0002c1d0000100030750503202241407000c0165180241a4143c490700001a0f000400769090200860429072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597612014 1250 597610764 597610799
    0xc060b3f0706030605130606050a0c0204060f0603090b01050307060c0204050415090f120512010e13021509090108070f0e09030d0c0302030105090a0e0c0409150207050616080c04 78
    0xe0900300030500d2440d09182007681d0700301c207010a544400174810b514100d550f19040e1000b083c010b101c20342c103140300140a802034050480c14800c402c00244c04560b100d40120002c0c28159245224450303032560018080c28003044241c40e040c1000001191504000c9103050903241075484280380c041007542400300034007000740700b075136400700740a88044030761518007407200c0e01f40c0141c0a0200e800d48600301048441d884e102e20384203100080050054107211811128111130703612060020030b949113400341e803080b21305450096102151b1003d0964087c00440501b0404006680b10821a82c0300c09049a4850140c01a040b100c2c10000e03003000100040902c15902c0440f4100382c81c20220110208010340e09090188004030b6000320060000e07041c5500100d502005010003804000c803070340c00164036000d640715480e0081d9102c0c0c5001051000071200c4000028100004550b610800d0610390f80b134040941c0c503801200d40c01e41e1411902d0388070b920701c03030f0061040120340751510f441c120f112108290000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597613264 1250 597612014 597612109
    0x2102010b041b090e060108011505090312030108011503080d020c1504051e0c130b0d1e060c02030304030801210501050a060e070504061704080405100c060b 68
    0x310084401501e440c007441980d615030241d640c1c01400c145501420030398040c0c11002041c1c0f500810804503a80c0030315400e04580001c0150300c0d040b42c00e46e808450910031301c10f80c55054451580c503c0f01c1d0030400c1c030055049030342980081008403111040841086500e11000c1c06004060081c0400101a903008211034986841110305200c1d601c0c0c03842941c030f0b5049405548540101115101e80010030a09410040141e40600304050a410000f160901405c4030700c03c00c0350743c40c891414161a50451254880e07002100481caa02503080482400c6c85403c0b0111181801c0c403900c102410300000940c0d0080d5456102c500c8540e0a10205c04a110741c20328044140c1001d9900000100740288984d501400741c245c00815820300f8450250003803080500316008110040004005050703208845c00b00003900f0400303075840340d11103003840712260186400c1550b001e00c00b1114004029009459403803034034800c1800b4041c0e2100d0004120303000c18007800d07110110504807008086a403140520003000405c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597614514 1250 597613264 597613271
    0x81b1908040e181005040203061302100305070201020c030d0f060803120114030c040e0105090c0f010c35030a23070c051203010f0501110f2d030d0b010e04050103210201 74
    0x10040024a80f40300c115404d9041d0f0340c0d4405000540c00d083c017040d9804041c889403007800810b580e0220313411885150400c420507644401027480e40e0703c00c2d0101c441210000301101d894010b00707013000c1e00506a000d50945080c0c03400c5400240d04102000b43c0303d00c50381074809030003503a11b8a02a01c40100340340400a034103004025120701c3d1542d40e8414040d400c0c0c0c002000050500e00402d4041c908100d2a80b00d070300c9200298600c21450382d200d054909101c0d4003074118180b07034901d0b080c0080108801c10110814241c5416a040c48425070b201461051059903001c0c86108031a11a0340d00032611108401014050f81c00007403101c2d8001e0510850141c8121b04075081c0f0381c2e1640c001103c68000380c01101401c1d8541004020315031380102090f01d84020342000c1c044101129648641c1d45400780c1d400039900350400f820000c207045401e070028036410030710180d80c2e550800e20020b00041030700880e40d501080c485a01c1c14818106841054103a95122501960341e91450000c01072208490080008564a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597615764 1250 597614514 597614551
    0x512030d11090316050f010c0f0203030316090e040f060c051b0105010f081f05060a0f06030b130b13110403061b1413060e010507081b1908040e 63
    0x88501c41d0001003a1403000c030725182c090700c0c02014104060715450710f2461158000503c074030756840301c080b8101780d4242443e0001d554249003032581071406a801960500011040095690030407644400000b015a160700e9403545420040480180a40d40030303041214903017020000564691240d141c41019090040c200018400c0c101568140701b0b00c82801d50351114010401c2d840308031125406400d003038018100301600c2d061190428013010540c448501d80702da010610380d44070100007101501c070f90803010420703030784600d030240140880b1440c0501031840513004c1407043c0110f201d42445400002e080c0503c5034000c554041c040d112022005141404c2088004002a000c0c4610307040c01c2c100c07500d0610003164046016000e000c46a603040c100d5501080820b481c40d080c100c02d030041d1015820310014140d41500101c450740101c0310010314249000071070902200101078100b500002e680104c4040e0a0b40a407413041f000b014610013041c00340b00744403d00100c0064107005901c880d403c4410301300c180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597617014 1250 597615764 597615787
    0x80403050c0f010b0405100303051e040816083322110405130f031116030609050705060415030b03010b0a030b0f090307020906010e01020a170903060a06050a051203 72
    0x50751a02d444940c0e41d03e40306080c090805009081d44503d4010100c1c6003245541c4000d0044d20402d002d1030514070401010070340d640704e090113603405401c10a0803a0701a0644101681c3c8a140c503020b0b480c0c3c50b20031300010340c022041c0030606c040d8200c001101600d2074540c00101c0845900060300e22202050070b0074100c01103440c62050190003601400442081c03101c03e43c10700084130009420701001e80d050032500404581b41c038620240041d85441e00350850484030542c9824000204241241000d103c00c0000620441d078104c0c203059030194080e1101c00b81c0e2074040008a00ca184540c90030310301001e41040c1d0090082d440500a03480c00340022540360814000141007140d6504111685540d24050242e46003410050719404440d4800840c941411a0009152964000c20701410807a6146420080e64820700084002c41c0e40070300342d6504042d8441c0340701456080401c80d00c2c001d1103080c000403404500750050b80110360001c2c0050009ca810001400415420740c05580d07182c0c40104000c90b070300c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597618264 1250 597617014 597617023
    0x90112060b03130b09120f0c0c040501030f1a06130b03073f0209011520030d110711191e0501090e0402010e090a060f0b0901030e07080a03080403050c 66
    0x40600395246180f0124900d85401c44000c007a01000c0e05611944100c42241046012500102c4410070f9494031080510b2055203092071100f10160014206000041003102c0c40c00d031304494500c00c0e1303005c404806901e034040c0f000e03900444003181d00c1320958822a841413503c0c1d000d0440060301900392105580c51365503145017082c3d84800e246405070405410070748442300c0141010050424940e02c03040304400c2c3c00150b45200180a810703074160301801244075143c0110450551640c034130110394070500010000d162250841800341c20503e0422540c0b4916148507402c542c4041e40c410300000b0f80100301c009011030250b20485445500038462004030710001681102d145900080795403400080c01d0900041c8424074a030302801541c10b480060000507a0000d000e6a15824184c6443c006d654544000300081e0900368008015451278000106e0500d6402006101441d000e880500100301589402c070341e150150311803600150440710b03010b030000b4862401140c00c140686001800e041840c50410f041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597619514 1250 597618264 597618271
    0x2090a090204290303040f0b0310120b09070b0403051005060f030601080d020c090f1906120c17060907150917030c12041a0d090b010e0118020a05090112060b03 70
    0x40c0780c4610980107003505004040b104000c410740255042505d06028247e00c1c0380e841c06000e0b8680f50110000d001e0071514401c5200901c991041c4c1035240c0c0003820042c40300181a601241c9c2805244030100b00140400212411682d02c02c00802c82c00b511110307503e005007c080c000507170180e40c41501c030307807255010013145003e0540000030b060074a401c0400079241c13100e181030042c0035550010800680401c01039582d03620070681240007404280380d410000042c40560001500f2904a40f10007090020065901c0d09440c1044180510001c03100c1d06607a5840301110b01c2242680000018461500300c00e0f0825148505800c08580040e00d406a010042c0d4480b0303143d80580d030010138400010002000b46041402c4084201d501d41070901c41c0300f0b900a40d030081c03845e042041c0020800320841241e4048024543c201030b00c040e041d40c4424094222160030b100d900308541110009903d110558802c8501e890050b8840d9868908140d0043d0703108402c910040450607525440007a04003200e2000318403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597620764 1250 597619514 597619541
    0x9010806070f020109030c021908030c070603050c07080f0a0c021305070210060e06010c0515070c14190b15090403020f0d03050906070503093306060306010c02090a090204 75
    0x110301c0c0452008080d14541034404003168103040703580b40801d070041c03042e1280c1a010340d4180e4151213405500f8034980003a40c4040c1103840006502ca1a600e00425004252801d6a509000c640c481115505580c0601000a41502c07010415070075001001e0700241070030002814080403030340050300081c140c22030030402404600d031660b040090f0140d051201e84c2142003c0e80c0d04000d204c0c24070b1b511185a00c002490f4a06001840041005101040204104090384800d96030717103928046000600c0c4e01c040781000c4851011800417451081004607081d521015800c18020342005683c482c18212000503102c807418074191007036058036440d0454040d100f54000d03001001c6019004024a203810000c844140c10546020140321480c01e000c00c4441d04500c09103021034594a40e840c0700c60400c4041000c240b10f0302c10303550481c400ea817007400d5482c040351003029450f00f0aa8540c4207002c12440201c03100d0b0700069131500d81d4030040c0b810303105458001d460480700013204e00340e9070b02003011100b61800e0600d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597622014 1250 597620764 597620773
    0x6090303220b0412230627010207050f0c0a150f0909091b0b0403050714030106240801090b22110d0b0a0501020c09160e31020307052205090108 63
    0x409104003101005c100005400e490544da00741201c1081e1144000760000d00c600110054009003004403c0d413400c00058180021541c800c2c4500d0f00341d0351a81600240d9480d0b01501c02203110500d446d1034410100c4e0303005d485108066207260402c50740f505c80310103c8400d1209400300404d5000080c400c48401903c00c007250400b03a00312400700d01181056601c192103609040005000241c0d000c50018201c440d58958250030111380c600083c00b4150700e4020130800369907032002d0801d42c0c1900040094024250301c0f2428242d8864034032400350f84500005503084031000d021920b8040c010205001090031070070002a2403080c80e10b0b0390b05c180c0d004a401048a98a60300040c125240c6420130380c000704401d0005101c081c0d01c000100356107510080000b001008076401c1ca440141c006d282d41c0c10400c00081c890036141c46040c4a0750900740340c1e030160351066000304289180f140700074400c6900a40c1941c4507503050442d804007041030740e034502c1fa158095481400000079592644100d10b40600743d94800380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597623264 1250 597622014 597622049
    0x150405010c020105091f091a071215060e060c01110a030b0301180302120d112709010522020f1b19030e040504050a02191406090303220b04 61
    0x9080d01e0003c5c010189940018140350084c00385103200000f041c1200c44041030000ea1800d211413071010399459040084c01150811600c903a0104011082c0a6001340130001c000c031080d6446810b003014006c1c070f03002c01c44180103030082e450040094290040d000002288034030300514030704a90b4001c107041a02194454142c101c03207280a02620040c0c2c100c100413000c903600c00d0784000f56a240e0095044e0089000041c81c21008000e680140440601c500011540d8034410b241c142c0c0c0140c02814030016000c1280d40381c1007240f800c02c0c4e03101d0403200024a82610b0a1254100d0002000072200c1c2810503682009503400d201100e00191510100900043c07400706c20035100d040c1003040c81d0503000d001c0b002000026001035000014100c00c00c50540707001901c0e0303849282051500e40300c01406548080070b40810b1011035940113092040d503518201410707500031404144202d0b402180c05007030f4103800c18010780720400e20b0307582c4800c003e1340031190042c6d007907548400d034000e0385e030082e000032403004d02d00c0e03610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597624514 1250 597623264 597623267
    0x207060906031406060f0706020342040c090807031104051006080a0209060c190c0501020703051b150a020d020706050405030c010309150f1409030903071502150405010c 74
    0x10100100070a080521808240000c031045590000b028036202e82000308a40f50340542100984540d44ea220790119a6030903c00c1c4001d1500702040084061189008103004410101034030680c688120140c011240d1190603040002a080c0409202c04001845c1c1c4002660b90040100030010b600580d03c0d9007a104000d028001960001400040741c0d2201d07900412116a01105185e40480c010100586a481c0c3c94001001071240c2401d1a40f40c0c42064200d58421420a25140ca5248070309181040e0395582d80040e42c481c40c461002900a4210085002483c0360060841c440800020008840c0d550f9162044900d0f401c0443c0396030060740110400207007640c04001d44000307801c1c1c3d810300504040c070b003400003680c03030164001c82e40c10152070301040d074100004645582e0f1000b02c1c00d8014001c0d4030480440100505d041c0d242d04000c00b2901c00842c10440001c01180d41d8460050041d01c40141484069140d80d001c0c0104201184030b510401002403c15801d00ca000754800c0c000032540000d400300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597625764 1250 597624514 597624527
    0x203040213021603051c0c02030a030b010207080304031707050f0318030a0b060d0c0902040b0c010b0a0605031f091e14060102031b0c0d060c1205100308090409060903020706 76
    0x1984401c20710401c0088400c54500d090660000d91604d0402d60301c1131420240040038000041039003125040138801111507402001501d0309004c40c0d03404109110300000126980d002c18410503d850300200800d102140c00400740c1004220040d03083e03807400d022681e4017442c00403a8035002041d60800310f260300d01038900111000608404400034284203506484002c0106c10242a0522840558800030f0802040408080c000c2c200c04400f151103965a010a6420398840500d84485528050724050145050b00304003091701c0040c6d4465003543d4070410464290441e02400c8903103503031004800200d100c1c80303000341d20308101000c107645000c2c140000d03071000303540e042800010034059640400c011030f40d0000030f596501c8564102400c1c1d184080c02004e041c8641102d045401031503a5540006100840c0c01401040250b0b9071442020281800204e040360819a141005400105000c1010039003071005001c2e801d9004100141e05035050b6601c1084422420341280581c2055200f008855000039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597627014 1250 597625764 597625789
    0x70c060233071b0b0103150c02060c0906090102030c01090305040905010e090a06050601030e0304030f050d08190207020f0d050604030e0f010c02040507050403170d15060f08042402030402 82
    0x40750280848078804600096040c01040d20b02041025205600824060702d09116103940181c40520079503103030705251585076410b10300940c8240c1403480c9160f0040c400100e480c89071010341007850419030300c42e00300311060b84180244da04610080c03000003070045c020303c141c00e500d61198552558581ca001c20707000c10307103805a1001c414103006004120407da40071031128401c81e40710f84006250350750140181c0003080d41242c640024800030402008000c8100c1700780036620300460884600315200740c4201d4a051048600a142c40c03011191000c607942c0303d070060302d401c41c40103040407104e48240c0003046039006400740a0360540d1040b000c3c0800d240e000320442e15101c1040d621059a205003400181a4445125009000c2c0380d80340006464288101c0990b0040c60748184154604101d00040c8c1006400c140b804148451a010f0140d1100c000e811a050860b1500d45850305c039405420f50903151464020415070f02c03011484030240320362100c2c9804c5041c0350b50b040801030300c900717150060090580310507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597628264 1250 597627014 597627073
    0xd11180103061d2e030803041119090c1b0305120a0b06160503121003030f021603120309020a060201020a14070816060902091302102a050102070c0602 66
    0x1401d44005007004800f5007a8009208a9100d01394543c10000320035800e00303121194021a07080c90040100450a0021406140a081d60b010902d00c004100314000c941801d0340c0305400f05807401000705400d990840703846c007440c60410865181c9030451180842c2c0c240001180011000902170705400501208140c000b100c0500c2000500001c3d0003107501c520030500d44035450b10004055000b0028200100c3d00c0c0c410507046074403103501740407411100704c514900044002c03400c1c08038115807040c40000d020043d0f1518003200000b1a20355207840c10703101c51404000d81007689400803407016882d5181290024092503000580d103540e041e00007042d0310300c04101e502d400001003100b28040b0b02104159000b0865048110102542034602580148074103503000350810301d0740703041168841350225095483d500a445040e0760703840003001200c484034852001c50b0310076800b9440c142000400208400054400e1000510300f0302640c840028003086503010381c00580c000c0d51030880100110301e00103804c043c10f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597629514 1250 597628264 597628289
    0xc06151811030612070f060e1201020309122203032f0d0305130c030506180606210c030303010b091005180d2f0418170d1118010306 58
    0x41c15045902e1102030300441c820440308000352003e00082c000740d40140b034956041c404043da90603026240f8a081e031078442c403401e4014948036405070103008803031103003954101500d0b1000c2c81041d080303070a80240301340d034407180e4202d259404040440c254243c0518042d860321020074003428031114200d0503680c06406c104403601c0a584000c0380006803520f100200b81800f003000c1d542d0003081c0e191107441c960080e2041001360b00001c113106001c00e283d8018141041051440082e111a6581d1035105407002a00f00c0d501400c0c03e0540701ca4100d00804040018040d0781c40c1064200c0004d18507007003a0404140b220002a950300780c1e00d0310b07507140101c3c1c00700703401c000342040c5402000c17040d250010000709020304142c03c20b00d800c102c8290305100c1d400248548840d104110300030108001c001030580700340a2403801c0c00002648080001e24544035a10640c062454520403500f011950000d264401c98251208003442000034400c01400b084011203081c01c5490342030a00040c152052541309800c81d640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597630764 1250 597629514 597629531
    0xb04020f01110319140301030c0801050601080105011706150a08060f0f0603070f0924030b01090503030a0e03240709050619081305010e0703020a0b0909040f030c061518 74
    0x30101c04d44d00061300203182c14212480c0032005545c01c400740d0300907468041002002004002c0c0c1a03560f442034070303a600020840e640d210801528401401e000345400f003008004400710040c160f00c01e4680c0284058010062a5050400f0b00815007200200070f0101e0f03d150704004031400c2004000c0f0002ca0200c8014001511000c04111b203803001620181c04c1040250540905501034200800202200402c0d04140003a42c2140e0602c0415161800c1c002410320071102e500d5807203600c4140550750001c1c040c40c5805003480040c0c2d03030220a06540380c1c05000302403004000360b1413019440c041d034400f1040b0481518050800030300004280e0810340c0700340810300103c50070200d07110090010711404d0509504607240c00159004035420164010215800e20140346584103000c20080d08407442940e0309807603e0380710704845186020305a0f0560f000088080050042000700d001c4162280c020304045443c1c640701c5d21107030203568a55800003080310180c08100256040044060f01880484008011460 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597632014 1250 597630764 597630797
    0x21210030f02060c0c100c050f06010f090218060d06050102120703091a070c180f0b060304020d0f080d050f0606090919060f081b15090405041104090b04020f01 70
    0x25035501900440b0045844c50580604002070070314040d0081003200302c5044a10300404d0a41c2d07800b404ca42078044e03419a4007400000240c901d0607104401840c512080c20400741700002d4000d41c05000071040840319048186c0c9491005003100b02443e4400300d4502e040000180ca0410354508051081500b00200400710750300c080c1807010b0f60301c03090344040740b4001040d051505000b03125001d0440d010140c00000c4203100c02100100c191500c813000e221807441c0031105007c0750094030200e40c0081041000800629102034407003600d5114508891030756045031544801c5420040c8400f81c40c81d5a50188542240345010943e07002104440c80361410a8030b4011a0400034058a0312010b140015010040010355800884c042c10302d100c000c1d10142d80d0741e500c644d1381d9904540d00d22850f40c062403003000d0b0341c2840c4403148181c84806c045203240c04510810300005000040003a0b8216840d42d103d41aa030b070300c5008540c502801002145500d00706801040503000043c0b072102e0502c540d0059081018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597633264 1250 597632014 597632033
    0x1080f010e0f060d050114010e0115080c0a020f150714030610140912010603150c05040612020d0603030f1706130e07030c0305070e010b040605030c0d060905070302121003 75
    0x81c00440784007400d8030f80744003041c041800b00000501c55420400f0201c845c090303842c456412201180c4020481d641e1b50300c21410b020401c42e590400042c003640014901e20801c00040c458074409104039030121982c10310b0142840100c80400c0b03400911401070200e410b0b8040c0004800c2520700c65510b107541490b00c0000c807050046402d0f00203001600f4017040001c041e1900340e860b03a050151150741c25500343c225682c002c0a00d804225507504d1070001a19030a45184a911046141c0e0f4440c54a0305003003180c20741c2c02c040c0085d07080c90015000c1054902c0070035180941c400651084d1600c8048040452001c1c00e4000b4800d80d00380c000c6060010003181c1c0c1d446030480f0340400c4041c040040d80241c2d114085061082c01c0d040034100a00fa941d001040107400078900048955481c411b44950341c0303802e40000d052259101e58000100c0a0000c50300048685d0004c220b094011100028403503a00c0ca104400d0340d0084400e0b201007540443c034180040030f01c0302040d601c110401e100b1030445017542d581130b00d030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597634514 1250 597633264 597633271
    0x91506060a0e01300f02030907030212030409020406031b0e03060c0703050c0a0f1502030609010501050a02100f0e0c0904050a08030603030c031602010314090a14030d06080c01080f010e 81
    0x10000c8028840c5100c0e40503131400b9554151214643e1403407010a0040e1810380a514000d96900789400c0c140806442a07200350303401909038001502d01c503807440d002c0100360b88440010383c60360300013040002a0a20365100500040810b500c3c0460442c5205071304000c240407040e1103100748180c80c42140150341d070114801d54000d805210494881d501070400b203610340900804030046208080300c800520020211048d141c4e40314000044206122031691720030381c001615400e07000200e180040c85950700500180c14242060b03c1225a00000c2c1c814210558008075a60005259070f810344518040c024800c01d11400300a0761301c190315082035030390181e456030006c002030982c072004400f045c000e60f07092040300c0301600c1c90021a5205c0410140203003402680d00d2080740440d00d01000e8250040240c5869446442014003520300f2084035200d000b60344803e200f110800d80001c211902c85103500b8801d05001e000a080100083c5110800240c2941b00280101c00148200801000301c21a0203508a51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597635764 1250 597634514 597634517
    0xc0a0f1208133306050420090f010311030f0f0108010c12020313050a051b0a0302060d09260301050909012a1b0f21050a0c021206070503091506060a 65
    0x1148251107581489156030410004803c003c2400c4268610445030401001d44000711820400c1a044412104030103100799100c5601003002c4c0314140403841c0605892031111700c10704012800780d4243c40584c035164000c0b5003251501c1d02000622494168428015001d801140003c0000d0844003a010b0a132405511172640b0a0350000b0029001c88071b100b6800c940c20358004112296001c1c0e500d8011744400c5019250034807011125410715003894000200700031681c001d00060b16100d2120450300c041c041d0300d007050f81c1071145441810850081c003410b045007940f03d850785580341d5060508101031b10b00060071440c0035a0602c110b09070310603402600b100454402d000f58a043e01030f1010300703403081c40d4410801c81b001c8203e4002081032000071305c2c5058003d4494940c0620200340c44034421202c803012641040083d1060000d2070324207024400403500309000420392503014540f40811403410104407010000500c000c4240040b42c0010040103c0707130200c01c0032040382d0b0300d81503000c5540760244440b00320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597637014 1250 597635764 597635783
    0x1060f170c07080f031503120901030b040608030d0c0e030a0c15120606030f0e06090709020c010609110c16050303030a0c1b0302010b1e0d020d080c0a0f120813 70
    0x90250404104690110f503200030b00076100c40c80030388100107503082280d0403031400401800a00580c6008034007181d0007510b8103180390510700e0400c011401001c60121042e007140d503400d000305882e2002c0018010061042202054070301025100520249802101e0b07406075210110640000e102140102c05580018501050070310250400320307005101c40c909604c86a14102003c18110350582284140640c0008180042038180c2d60761561a10300303c603415400d4104140c10f0000c4490354004040510b00301e000466002d4035840e01c10121400e41022000300040054032008445090207100f43d0352a000d41e49030900c515040c042500e910008100c4840d150392030076103081d070a000c0c21001182810b40025460030761103600c4c019000b0407000c0c0086100300b0b000d621100203850000c0d0000d4107940c0140040307d02062075424020130602190040310601814043d50240803010050070b000c65000d1040b03480000440e05190b00001500d0b40e02100b0890800100b1840d00c00c080e0202800302d9200304243e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597638264 1250 597637014 597637021
    0x402150901050d0c090311010f080708100e0a0203011418060f12010e1005100b0f070203030423040501050402070b040b0a0b030706110f031c020904060e18010501060f17 74
    0x120341c140b24070b030001d81040703140c04c90a0303513040d0b4400901c0043d280310355000c0910303410a2005440d90004a18a0f000150004d40020401c034414a0000e821440e1080c014202580320340041400350400c9600d0342085070701000400c01e5445020f180441c01c8801d0343c0d07006100070301c4220381100f00002011203003d0300c5a2400d4103100d49a410401100701d01603402000007184408040362101404250030394900e0400001c0380014491710200c00403290f1540015241c070300320031040c06180e001042d081c0e80c140400e010000d0a019480d41c01e168420648220f42261501401007004942e4185c00c035500442c41808600001056201d115420503001103802556940340108040500f45030a161a0940103002c00007a13001d420011019070803142e901540c501c2c1c10480c0c00c06650340111014403203124a44060102d24491a0f0b000f80800140174102181c8261a0f0300c2c106800d040980d00d40c054003182c1c04009960341700c01c0c8581c40c090002c80c500b12a1031a183c0303130020f00807041302056032005640080030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597639514 1250 597638264 597638267
    0x3240403030c050f030403120f0e1f0617070602070806010e0601050702030c060f1312020108131b030c170a0c18061203020303010302100507080a03020a11151e0402150901 75
    0xf039030818a00c0800d03a45d41ea103440d1a0040c20303400012080e01030641011134008000040b03010b03d82d17000e41108028001e290741100c440381d20000306080141d40c1a03072401e002c1144114080300000c503ca048000340f0025162034030003850403c0039030201303410b5089240140424810398105581185c024600300380c417840300c0d0000a0811022544803548210006182500090103101030710341a44541c1c1440d001d141c0e210380b00200d0f0482c800e0000c1c001400b400000d102403904909440301c56000c0d003028a0100c2001140d0000d80c0c509800a465014002c00b0401c406038003041804641d01c4964094070501a20780d83d4000f42c00c2035405100f8615003019401802d07410b01d50300403801880405c003400701440807410080c0d101d0740280000d0340500c81c007a01b0b00b820680900200c0b03080380c0e4042001c518019140340120029004600890704102e041070701d01a00c010204002510b400c0d0700e07405043c690404d820b180403024160468140c03010625010040560b59460000707905049101f144e0b541c4d074129800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 597640764 1250 597639514 597639517
    0xe1f0f050d1a0a0b01090e1905071b0804030212190201050f0906040e16050a021203060a0e0f0f1018020d0b09010902030103030801050639120903240403030c05 70
    0x14242c068481c1401040740e401c209401c541030403035003a25006d5895071514030100840130101d803102c4a04403184040c1d070f001d1006a0000d64480707600c1c90100d0000e804001e07611103001c2d042c0c0054449102c045400d20942c5400c902d81941e68002c0002801c103519032281024ae14264003034080c1c1844000700e48454407070001000c07208105001840566100d0700c0c3c2d9010300040c1c105680341001401250a041003445c0038004a440c005450380041c9070601c1143c11440599000826140e00800c25010009080402c40e105d14010580100031800380d240c106600c4d1400340004201c404000c101c4c81003000044c050f803040c810071851800300540c0e501c003030740800000f03059040030240c2c000064600011750294142e000c0d5058a2181e83c9200c09642d07920304100c40d9005401400c0450340500140f00500c0703400c80004040607480c8000195000c0c0c00700700590603c1e11111b001c41c881440000e58010f585800d205010082981c0d03000346c082144802c0d405e00e6184070041004061603510404200b11601a40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 597642014 1250 597640764 597640793
    0x306080106090f0c030e071e0e0a0c0f0315030f05030408030304030906080f01050a0e090c10030f0518151807170d0e09070c0314040e1f0f050d 63
    0x2009002a0380d50b0180c400007020f510b007007204038030701d4200d0081c1164841d00540d040804100c0080404030300302120810144041602d0044003684d0b4100010403410504c1c49a20649400600040404188101030940b800c2015140101450400002002d114403d000c0342076035001103450000c00c1040c0740c59459841180c00c5402a484040200000c056000d04840f040d90110307552580151a0504441182402030142d5a440407403200f0900624594440711640803031050100d038200000700380400d44580901c10200c0000b6220889501044c41500038140c10281081044400e52100d1440701e85444020014040101b0600049507200040c140c03602444142203058a08160751658510705100c003003a240100d034003483d81c140f850305001d0600d413020180b0140001c1902ea41d03006080b01c9120703440800300d007806951400c44400c0c943e10409000a4520302018122030308061214041c0801c41c054101c042c45000b0f0000d001c02c55012412100301d600507660301801c0c903014600390301c15a8030365 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 597643264 1250 597642014 597642029
    0xc0626040c06020d03050903190e041103060301060f150e01090b03010e010f080102130b0903101e1d0a120c0209090c01030b04270c08031c18020102061302010306 71
    0x2a000d00051118000501c400c0381d45640807610720104a100c2075081c0e030340172240c0c1d00785ca400c1440090032500400c0c103030f00940a00ca20780803501100c2280007030203d07807d100c5001c08480d400700030885541001d2181402800c0404a1800d41d14900841004007002c3c003503600f03082082c0b800d60740b140c0381d000e80080c43c0903000003511141c036983c42e1081e10001480074403071032818140201001030450030610031190000380080c2841d02403401c4c400c1c03084443c1d200d061016054400c06000701c071003841030300c1a8500380485140d00c89000700880014000d40d1121070355000030380440b01441c0b400384000150302c244203601000400440004000070342d00d02c42c00f000003a400c21451404c100710700380089240540392034240c904010005020050000300c9007407020400c1100b82d692403464200341d400300c0c0d1444003840b0791084108503803541d1000341117801207100c4290311043c10150310f10001840c040d160f8002408182d80c400350209400007559160080c0c00010245030040c0c0700000e59100381c00c030b030014002c3c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 597644514 1250 597643264 597643337
    0x120a021612050901090608040f2004020c0102090909150109050402060d05092b050711030109020307030503070b010b0f07020f030f010608071a0307170c090a0f031b030c06 75
    0x4049002d4aa58491820741c0c0c0003541c140c02c0070807443c1c02060024042d9401210203990600555905000035588030b041861312860f000060b0925940c0b070002f0001269007a0016864010b8070303080c041c1a050107040084d40750002c40b03142440d20400c0e41c1050440e10461404180c64982d0300100384c20b0f00c0f130f0140c401a02810981000b0010300700103000d429244658580409070540415110b04000b041c90710034000950800881c3c022402007041d961403404010000038039202d052303001034906101503000b16540d03000802d0719000d00c00350b0044540103002c1c40c0807080c503102858100e0780f0b030b031720a607800240308051041038903940e900c1c100162103882d0403042c002c200d81e1380c035014101d0703540034148656400c0444c2c5a01c103070840c042040540380202e4403503d6031002c1d00d40510207914120750051101060b40d90038026002255203621100c4010040030268012040c21820225030441c881a124800c1100b4180b0410004103605a101c1c11240b4620340ae00d003d280c0580300603c0104841404420041c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 597645764 1250 597644514 597644543
    0x2030f0d0b0405131b0501021b0307120c06080f060d060e100f060f0501020a0b01050943210b2e021c020a080702040617160803120a0216 60
    0x1003031040d40c01130074066280381600da60a0056001c84031254040c460060300990016100000122036480710000b004060300c491617201c1034010340b8410450000e54000c1a03c8504101302c0f504041d50b690040c60005000d413581c43c02902054451880d08002440c2c80c0d5a44400c8a210b8014024020350000c105018041c510380300700c241000c0c1695005a0300c10349141c05002034598000511b118005501c0003100805178609020444c0040c001444240d9000c2ca070140a80b9003104065480b4868411004017016150301c0d2625000e145050004801800025140d860030740700f400021150710070790a07401207043c4170790b9400301c0c10075456000d0451140c0c0410340c42d0358584030500c1043d40013400d030340d0881d460483d00412107001d41c8610301900d07001d0b8018000090100e1070450040c00400c0c000b60002c0780c5030307036161050306019105d100500f450750889150b030040b15541d04848801060b06000a506021085500d0510030f80301612081c400c50f4000303200e100103a0544402004c0c19004906d000d4001f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 597647014 1250 597645764 597645781
    0x12070b0310051e1e0f0f0d0f0b0709150816030b0a09020408010b04021e0f070209011401020609010510050105090307080715080f04150203040f020907090305100c02030f0d0b0405 78
    0x8009a950f10712807041c0101e041c4e5031486140204030310103401401d20703241d01e030320f07409101d03254620544443d0007144141c21100814801c1007050701c86e80c45003221080c4c80c5011400188404456005a542c0c1441c0d60506005682d000300080c0c7c0041500c45030008a43c2068001da000340000012507422104e2420000391219081e8080e00456015200034030150044008000482c03182b5601e40d410b1b001c190242038806205e030009051021280c54200745004156000142e01241c240e0080703850055803480d48200d941e0600a007600134400c28001e202c6420554020b00482c40c1da4040c49040000100d0450300d80da80c04c1068000400010050307450203034072058480076a0403c0e601020104040f032002c01c1c020212071241c588a9508081d00d1484000d480705440065400034000307071211100d0911500142c2d8858038218000c8072203031601010f1628500c1c19504007080e60036802c054504d0401410f0081c1d4000c000c440407118450102e5541d01c820440e80c000401240c80314607007040c40c28081000300b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 597648264 1250 597647014 597647059
    0x5030a091e0312020a05120a06030b0a020a02010c0e010e0d0c0b0310061b0213050a021207030c0e1813050a06060e180307050a022b060506090612070b031005 69
    0x64083d6503204070b00301100c403541041e40f1401ea80c1c100001c208100d16020891103a04140d000000e103c008111560b03603071103410b8803034400d441d070b2a01503a0000e00110324540920910700ea040150409030107040e506800a000d03042d02020701401844654654010072039803088500141c16003054442d100d0824600c0170a03401c2d1503004150219405800b40c941c50b071403c003015101c8ad64000d00c9000c0e00407034859000c0c06480054548504150240155022410740100b11803041c181a41d002483e81c0110300b005060000004c0c40d02d0282d0003903001c07422050a101035055120b01021041b52220300e041c500720b407510302d035600301030801c7c0d00d4440d010900801c0b24001e14095003244032461110480e05000310380b68461640c0040c030f284d1204189000609040801c2061049100500282c5d0801b0f034005041c00c841d10f10085031041c0e0381e0740800a45181c00d400c0c0c0780d084101645c20000584465002650700c02c2c02d8042da9901c1d074008400a0601040600b003c1c01800020b0303c03002002e100300b290b03542c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 597649514 1250 597648264 597648323
    0x12030403090f08070b16020409211b0807030203210126030d1a0a0f09050c0f04031104061203110114060a0b16051f050106020c01050a05030a09 63
    0x7112420001115410810781c1c405442d0014040c1400d0f625010074a41c1d290f0203074441854403e4203203078610150f542c034880c0101c110b014410325042081a44040540c084140011400f449040108401c17111403101c0034000250748444515501c01941c01e0a9180d805900c079400e01c444a24104501041c0752800180d0403600c491aa01c2280020405a601000040320320050305074010b00001d1507480c4941c00030003080814007582c00c0030500c084040b038a000711581000c102c00c080500c04000030449803141c1503001810340010340c201942500c0780c0e17140384170f030f844040c3c600c407445600381e003140d56a640283c1c003c09210101100c40c180601d8050034074591034004564552915200200800c131003a8000d1040382c0040040103210304040360f00101d50010103c0900440a4150250005000b044080c1e58890121802c480908401c851076003030b40c0b0140c00140864100585d01d9101d660054141c0b8465240d9043ca50b4590380c0b42d016000003000b6400c070107020383d40c5850f000e40b003805554048004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 597650764 1250 597649514 597649517
    0x70f0b0406080a09030f08100b0429090f090a060b030f15030601030b070507030507050607030e1c0e210d050c1014071817010f050604150302040c03020c12030403 71
    0x500f079845140040840d580fa40d400f0b008a455101c01641e0503111321102c903031011403080c01302c7d03946d500c03905805a00d4000da0000d41100781d003401d16016601c094400d221425804d190340524080f07241011511080461520501400c0d40300007243d04040303583c000d48083d0004100d400e40780d24100000380c0359200c00307072126165510400600c15840c00c1c04120a0706a940001c5121450780b0b400808581e190310528007a4100103040c0001c6001070024803201c0e000740041c0d40c02140b81111000c1050a05800c402c110700444114120080c0d515007001c680e451a00c003c8030031848014aa03200c24080240308170140c3c010380030301d0096407401500310f400341505140000c00c03207000000303d40105d8102c817060201c02d94030718042d00000f5410b500c2030341c2a0315000c1c032104813000b20316590348440c400c0b00902541500c0e16519040038001d04641440341d00c1e40030368201c405000104145660219400c59404040d00075511900c2140c0710501030340403160040000003c0b12000d2908040c401d520f074005981c100d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 597652014 1250 597650764 597650777
    0x3030c090b030f070f02150406060e13050c06031503060a09030806041e0e190f0b10050f0d1103031303020301140103081c1b050703031d0d05030405070f0b0406 70
    0x242400224190391103540321290f404101d80b108a0169503503080d180b9184110700c5484418008040f00b905010b004a01c1000046451401d03d85042188030004002088101810a0910105200003a0025140707820384a0968a4036140300c21402103034071207200c41e0144940c2d8144014104940c1c0701150150095941007070503190b440800055a04140c0405501d0905441480b0180102d51200016006040032504016510003a442414103401c806550303280d03405a0300d40031300c03210794403803644040d0550130840c0b00b80c24a80005c1d040a4070403c0d141c007400b1030465240401400c05a1100001c4004045940350380804022003076451150100700e0180d403c214010094a40354103080b41a40d40c0040041d003041c0c0740380c1c4e020800307445c02843c41e0a0f40d03407110301c0d0029415480c060101003003040c1d0341b01035a0f168036050103029a50305210006144800d48030719441014003240381600b5140c240f8103183c1d43d40700c0d41000d501e04003280e0802c1c800e0340f41c4050005224010500240b0031075030380380c4036035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 597653264 1250 597652014 597652019
    0xd02070e0615182107050405060d0c0f031a04030906081e1602101b0c1704090209010e09060303030112170a030606090605030103150e0f060903130f230a080a03030c09 73
    0x5441c606200c0d404009905c013400610171361909800003540010040d10905203042c060b10b0780c45203545d1a900602680318200824014800c540311483c51602c8202407051032400c03d540e008107038510074421102000010400310340c44003088401c104030842881ca07020380900b80701a50100c1088010b091310094031440c0ca1440403255140201c0c0302c0c000c4100203040503120700b0344c01a111010b0040048600c0184d0b11800380007024243e010b080030b408100d0300103880b1b00c42480050314001030710701d00c01d101c1c642a50030007000b42d8002044034151058a64107401d069418030b400019290b0311ba00c00e042a070008a05080c003240c1c0741d4080012568190340b844030380d42c1e0b1070800f5951480300b8007001d0464a88102c103803c81c1c1c0b450b6007007690002c09503001c442c0c4080d0f55485d03580c24040c080d1178000c4039030000909040d0440205060001600100c0c0400b0101454520480c400c02c508044a0a03003802d0085000c042e9a1040c525030001c000c12420350760412000c0c94000c0c01410312081741300200725005d101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 597654514 1250 597653264 597653299
    0x32d02060612070305100b0102160306090b06040902030c01030f0f05010305030d24090b1201020706060f060311030f0403030e0a08130f05030c0927030405030f0d02070e061518 77
    0x742001c40381c00801034103681b10480d05070000303403400c62645410361080042540d48580c0d0324001c0001103018141c0014072207103c0c602300441c2c4001601003807090b8140560703a0056a008121400030030001d080c0018441e80180454024104040760940360501d000300000c24010044020440360303268000c100030900001904806205915004000345e0122000070301c800072140c0c3c4084150700e802807a08100e420680740540c03e9901a201c100c2d41182c488108000989a144400c070140100303082c1030250000d01d440c2083c031800020800340303101c1c0021000c00d06060290744042c4000345c441040c0c408841c00c9091255482d48910b4048040080d910000203205200b001414107950000b000b42250480382010400d400e100070742344a1009981c4c1c80d90b42031940301c940c4550080440070020f507807100d00e004c0415042a0130b400030f44500341c000e00d5503141803642c0819a0340c191846091010b603651118400f14113040f80604840400e27802c00030b2494143c9000040c0017503480801c448102c0540c002c0c3c4030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 597655764 1250 597654514 597654523
    0xf050618010e01031104111813020a171506030126120d02030403030605130e010b09060f06030903040e07030e010b0f01020d0516080403080301060909021303032d02060612 75
    0x581501c144001e0044c0005200c941100e20141401000440d01b542c1011540509031720800100c074204114040f041c81900b414104440a100c80718001c50404012803805004250427a40170394140301c04178005000c44082040070f441c0700d8405000c4903201c4da102d20f80c0000501c401d15034002e62960b90100810701500001c0c281041d1102c0345090b030700308054140d54501940010f03000301c0134980c403442c000c516070311b440c07019060340c803020b0340c01060007544113000a00711000d4040c5a0b000340d002c0c4041120030341b60034001584030302c410344402d036480d61141c075214114042c903000b68815559000900c1906503140d040070b0541e0f0015030082110000c00006c000c0000d11150740d050158011710001da14003409900504400b991174010412400300c0c13075580f801c0765802500225001740002c0010710071254440702076009417180010851402d2480c5c11001e81c0100c07548001010400a10101c02101e895184610720f85801d0700f40c48100f4500c00000a074803807504648240c001c26150b10519907100c0d0000703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 597657014 1250 597655764 597655769
    0x2032a09030703030815030109031214061c0c2304060b03040203060a021b030c070f150507020d060209120c10030c0504050d2316120201050909060a08010f05061801 72
    0x10700401c03550b0710b143d90035160038400424041d4140d200f81705401c010b07102030040500c5103100b541c0385500c8807206110103049070f800390390303441c006011201049000c1d00c8806a4047c11070031209044640006480c200840c10401c1c0c001001c01000321038609000c00c49125065191742046500303006040c0c850800001600003200c000e58150f2041001c0b82044030540e000702030300c22103041504100d4044444481c034640c4490022500c0d540f144d17104006102d10003022401070210310f03400010503d821000201035016404001c1c1c07290306146028410000158100d4101c08006001040070071901c2c944181c503008842c0d40309016458196000031000d01c00d02c02c0c105852215252182014102024001051503404c4100d9039140102c81c5040d030009881c210f16032420804008000800f070300c810f051480b441d154054110b00500008480040c3c0e000750540313840c4c010640e01c00c0c6003a070340c031400203401658680c030440c0b0a51030208ac1e0b800d03120164000912440055544243d103180d109000b407410306c000d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 597658264 1250 597657014 597657019
    0xc0a150902090f0603010f230105100c03050a050d0903030c021005130f021503040f06060501090b04090e01090c080f0714060304020d050102370f0801120203070902032a09 75
    0x840003903d00140c0c901410b030030003405070002840d044416040381c04ca45a0741101140c40d04804509603a264003142134038094003050b604400c03808610100078100441c200c000038140100807890b90780da0381c491020f880c000140484240580455414041c00400007030b81c0010040c050705240c070a005000d80203550040703855a00700b1074840010f40f1110481011000100d2384080e042034038086c01c134038001c095030180340208401072594040703207844812900e45078030980c14428000c4040000354640003e440c1125504100894002842a40d050041525500040c6038140c0342c000030032500c20010700c092040840a00315000f04d034690701014030a00f0307000381c01d41c5c2c4900200f0002c2e0050600c802d00380d103100c0c86680003505000e405a10110030035074422a0410301400090460100a40c10058061101050503c0c4d8011880303840c00510140050082080b0040e02400f050115142008080c000b8120702400715141d0400301205800d4000c6605400c00d00440c081140402e03a00340c400716070802000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 597659514 1250 597658264 597658279
    0xf0b06042102040c0512070201061404180b070504090b04051603020702180f15040915240902030108060105032a0f0301090f050616020c090901020f0c0a150902 70
    0x100408048255108500070585248402070100141c803a401400d00306912500c80b42d450740c110010b2122039090003840002161705080301003207815801200c6a0310345106a03008505003c0300006c41c0b8070084030300d6008102c8090101000304e015800800340c025190051020310003000300404202c1641e000361150302921644444030140c16000c0d50040c40e0b141c0c40078101118101c08054110194003085034900c500713070800300800000f603007581c9408120103011a030801c0002c40540b039620342c010a508204ca07580d540c0300050070028003107030105030500501074407607810740d40c075242042c020350000e10920b9190321803c00046010b02c2d001c034541c003004c141c2402c020506200540c0e140040f40c01c0d1800d80d0741109040c03003031290030384080c0102c80f842806810a801c0b80c04e210301e00075140c03920007061403100c014100d10806819501140c0380701004400c547e00303440f0f83c46602c640d90091041c80300d41c1520b69400a000f400140340401c10340c0c90070340540c050000740124074840742d0695000d0720009620050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 597660764 1250 597659514 597659519
    0x309150e060a2004060f080106050a050306091909080d23040803101805070e0f1014091008040c09020f0904020c0f03032716050d11150d0f0b0604 64
    0x1c030b5404083c030791184143c2d00098068010b641916503101d60440400200224052503160341c03c03220b640d00600031464071514058200700010b0846c0005400c0e28030131200f240c007045001c42011117124448545400421000307039a0314151086600c40744c10f07650301a0030102002c000d0280010b0349520032014000d001e4980d070310b070380e690342080d8801024200e4043e26400d020403401001d01c241030800c140382900203050f040071480a403000d0a4015018844e2010310780c00e10407521004045089075025080103500710421240b220355030301502e2032040c1c0080c50100f020440d01e40c05981140550301400c400740d040c5449420480c2603115160400754814401c029020031400c1c00d900800d40b0309e5100b000d440400004446090031540291100005030100781074010000d0840c000340340101c050710700200740954045271265820319451242d144505041040b61003070110280b00160106001041d5000d90820030a00000325002100f550b1006031500c105611340c01030301e105101030600000d00b010300b40352 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 597661870 1106 597660764 597660781
    0x7051b1509010f1b03020a0e041505011403040807120512010e090c18010504050c160507090b010f0c1506030c1202180403090308160f030309150e06 65
    0xd1401400c1884c0300801088941c00d115641009a00c8900703007082542c421880c0d118007604107040004002d2948140c240c0300059070801d803180c84001c0c200030f0410070140400c4400070700e80c040c2002017001240d108910074411074824603101e49404181c1c0f031101c100000a070b0000c0c00302d826803004c1c040226018481140349503025200151242c90080c00301e00b50042c1803040500031070366407001c0342c0c6c040010310454003003a0f0201001c108480c02c038078015a4a0085114012160b03150040300100b941c468401420341c0070695690b1040e00d802904d92160388010340d0001c503510740d0303202000000910000120300c01001d600d00c010003118500d0040c0000c0c0c0803620780c40111a00048200720000e508445c08400f6030b90000c000f151030f03040e903445040c03031701c0740342903000c0c006c7d02e4100922010180d042e0400001a4420108a00300740c5805008a040d103034105451020380d0805800119003c = true := by decide +kernel

theorem cover : BRFrame.Cov 597482014 597661870 := by
  have h0 := BRFrame.cov_init 597482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 597482014 ≤ n) (h2 : n < 597661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
