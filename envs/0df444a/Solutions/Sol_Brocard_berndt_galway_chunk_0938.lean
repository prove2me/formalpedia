-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0938
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:14:37.008268+00:00
-- url     : https://prove2.me/submissions/64079d8e-f1a8-48a3-b8ca-e0194f97b731

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 168525179 ≤ n < 168705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 168526429 1250 168525179 168525187
    0x120605060a0302012a170301150c0b180307050714090c03010b070201080903091921050601050906150a020d09050d0f02060c0c0a030c0801060b0f040909060b04050a0b0312 75
    0x1000030680300c84011740c0e0748002c035014005120300002081c40ca420a034130014031510320304000c0d24500c0d50b030400d105410700e0790040d0018401c4640109440c0121603006409001c4aa03228407100180043e0100b00d0742a921040000d036000c900b040c42418003525410210b4240c2c103049400304100d950000d000c4000381007082004201120215080b500781c0c41d82800e0182c1c4990f54258102c0c10350141c0e050b02c94100c1000101d100315101f024007000c0540f0103a044880c11213889412440f444111010f000340540d22140062121b40790020b030b22540a0390042110b1103400d0b200e00d84440c1c40e0010484100913a2152180c404940e4102203e98090642070741e80d81c0b180b84c101d4aa450450880001c003034010680011400d8880c4c405000d0314454180c0944074a00841d0f480c50003014100c5079105200e000d5182c0382d004143d880c944401c6075007548152034154106418911600020604030004a55141e41c07502005000e850b00c1c060903120b035580200c001000103480c4103241c10001101c1d815000410100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 168527679 1250 168526429 168526433
    0x60408010c0e0a081b0a1805040b130c0311240a200303040609021906120c030903200a121d011e0c1a09030c010605010206061027120605060a03 63
    0xa581d0711050107034105401c400e40214045101e1b414141c03c0720103c3d0f03c0b5103d6a649020142e0800c50080744190074510840d41e4026014454400c000c2d0b0050500840702d0041010030703070454030040d0180c3c00400c0c2d00388031484050f0410100d01c0e480a4140c254501050340c440e5550000c5a1200311000c0d41d017040c0080c00701c0d0807140c0e12440001c00c0200300943e85d40c020b4055465400e020494040300320808940240c03103200260a1a140c0f50300100050f083c1004601c43d41c3c806e00442c03801c1980b50300d441e2114006030000e1420262866900056441850f0203c0c002c03440f442084c0c02d124042e501d5030385801601c1c3d248000517040103020103040c417400301f6500807101400c03c804810b202141c541001440303518a4850044187c000c00d0010034403850007444440403000c0010b1000031500002002929aa0401aa2619021260325a1000e20421200011030013000c08804045e40d20140c000e14001c0c50140401402c042d40040065613007603032105040114a10403c2e4010b80100c82e0000b0952031a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 168528929 1250 168527679 168527683
    0xf0c070305011a09190e011a040501170a0803040311060115110d09151103040303030204050a0801052502031303033906020702060409051906060305160e0d02060408010c0e0a08 77
    0x2070480000f980b000302d01c0c1c0c00030344811b60014061210800003880900c881c41ca00320f00c90714112075901e2046180000020f2502e00420007070400c409900d0282513001c49685031090180c000400c15418030601c10590f2150b9101800224040e042c00c243c00c1c149002c1818000348070f415000086001c1d03910031a20444c2d8642c0283d005021289041000301c1c0a50105204880725011150600c640b440041404402c064040c0c000d08141d0720103848640c0101c0d030fa0305400b03007620b1003644d1800c2d20000c025070900310712010511401e4000311070700413280b40030841c21418987c1c0e18103a20980000e440f54032600205940354904510f04003000c50280b0300c1c4680706005c0050801403800040500354001030780d00464491606480060075800020040b500d040720024454003152980410500e28081010401c3c40c000c0c41594000c1800c81d03003018502c41c151900b40c0754103d40380400c030307231107101141d20360010780d15030008101400326400007050000b00c00c04007900c2d03000f181c000310f40305400018040c4691140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 168530179 1250 168528929 168528931
    0x3061508010e060d050703080408060c070807080a0509030a060e010f02071709180106020f010c0521040c09090813050a121b09090f05060f060109050d02060f0c070305011a09 76
    0x400c114004150303d83c10000ba80b072000000c4020314500801200105110b99030001d04101e603c42c0c0d060b1009036030740f16082d2482d48240c60703004003211401d0202002150600d0007611004205041991400b504840001c0ca844031402c01100c1c0c09846078460f0030a160203000e0340301c612010705c2055040c092036035204100c3c9140ea03080d443c0002c102183c2205955039126661511030645110010310f96161b0500945490804003081080d60034100c0c0c08100e035120f1005c4400082c00c0521980d030000c20302840100c668009001a2041082084085100241c0f445405a40c51180e6082c5036100c49107094190ac0c0c030070341c1d40064801d40940c4010004030300d542040100d0543e02100380a00c0380114000d04078008840d800c0501a2858240010f04002203d06040441c1d402482120718955038101544d0400c03c0807105c06000030f00040c400c206501f485000310208904c014103c9081c284099842e41ca241c00a61500038950310505040003803143c2131140900032484441e941c404c0440d4200440c8840074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 168531429 1250 168530179 168530189
    0xc08010b0405040b041506090f0e07080123040c020102040512120a0c03030e0607050406110c03100c09080610030c211202010e060c0d0e010603110108062803030306150801 75
    0x604e9180590703050381c0c3ca40c01564404025402150310301d45a103c000c0482e8480d016404034002110808900d1041e4030002c40d10405041da0750004e240c0c00c101c4940e080d1a042030024000002c41c1020000a42d1a40a01010a0350503030006031078619020400103015804245002036401c81581e2101e80514042180c00200c11030810840d240000e150440c0148443c0c02c58651a02611051004a503441001401207810750340e500c10100c0b400240e015100c09450554652580c4a000e491040c0d8403a41c020b2201d0314045e050580c1c616544246090401e4021108200c95025207401031041000740501c14000c0c2c07442203541c418000009a000000307501d607000103080d0b602a4100301e40790360f1007500100f424407038100564800341082000c0101d142c00c9a070010090034148641c40800440510038030048981000008403010009001940c2002024200300e40006c0c40391030388602c1442c20401d0442c043c2c584c2e09010156491070038000c00f140c85541013100055011808025125800b5000d141510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 168532679 1250 168531429 168531431
    0x60e03060606130308040f1401080603070314071703130803040602030403031d040c0809070501021902090a06050904030c05010c030b131e0e0307020901050d170901030b130207060c08010b040504 85
    0x4104001c0c2011440420b50000707100400c005000308a2500541f141c404170f030b0741c030f00d10120004511401501c903480f00f00d945035007541c0003400410200720800880402c5402003803e58110f07c2d00c8003c1a030345500c900c100c0400760b5100140801c0e40342c1d60200540c00524441c4080e42c2040d0601100a48038030503480081e08200e207a40768012000460000d00c981d46e1402031003006103040400f4040d01f207400071104441d003406200400162075001003004d55006c800004030104e020303034641c01c00003112809850005004d41c0c510000c169a10344031900c6006501070303140d4498400707035460300070700395098034982804260400c510342c0800c1d00c50002c40008180720242c04501005940c0394000100042c9146810030780c1002100111440701100074213500c5d00036200f01d002a0380390300c14065001000140107246101107900b000b00e02000300040d291026052401040001c0e81500061849520300b42851072030340c0c0003800504001c4c0501ca010311103c820304107050030750f14020381c440701e500852103010b02036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 168533929 1250 168532679 168532687
    0x181101111f0f0603050604021203030702070e0a0213030f1b050d020609040e070b09132003280501092009061e03040803070207092a0c170306010207060e03060606 71
    0x81c1000e50403035202507a64840c1042441c1c1d032030804c0d50356004d082e80c06170f01441140500d00c1c0c4c0b110000c81240c5c8162000d40060140b289480d003045002240140340100c0d1503800d1051000261100c0784890045000d010040c0c0b6600c114141820881958415002104000391042109807203c51076011a10303011600d954540c0c0725800410042c2c4030201c01c0d10300b58021140d0101706a94648054000c04401f96046180150050100002c43c2c070510062075240c0c21142c00070280c0c0d040803006691140c00d0001c512040c40c524100d4414940a05500101681d11a801400301c80228440c050761418041e441e040300109504220809100b2143d080d40907640000d00300d800840206800d070030343c142036a1240c1d0307039203480d05115140390410b492080050060007000111500e040c00340c81108a8031003005108021801c41040854402c0c0700705109100707a5200080101d070402510301d8a42000707610b5241d480c0b400c14002030803c070781500140309100503103e03813039002d442c005943d6038080020381d609555 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 168535179 1250 168533929 168533983
    0x20901020c122b0909020903060103060e0307150207150b130507050c030d0906200418110a0c030206010501111e190303061805040503071104020c0118110111 69
    0x81c0f0710303500c4001a60240140c0001010820f1050311510305120b40d44180030580c68205542c246d01c51304c80c005074154800030060002c43c3c2e281e40054a2480b440c8216480d204259481ca100c10302514240d01c00554041b5001c014445002443c241b0b024a107882044141d0145000910030440718104c05c00c0d00c0d1361a40000c54075030283c0c08569841c0c40c414116900c0300110b002d91400b900b2112021a54076060020070285100c41140048208180f000360500b0320b41000945034030b15131091004000c003522442d0301a072007e884c40092540d46559961400a1015810f020b880c2c140181e2000341004141121842a5240842c4902403001c1405d200c0d10003044400000d86421080480c070201c4440801c6918105a01a481401210440700c1074202c1c401d0742000481c02c4410441d4041c09a41017080032200041031040d00e0742c050746000703000500304040d10300500d08542070101441001002e000e01101806100c2d041020069004d284c560300e0081d1001c0b04903101d00300c040c1e07502c00904a0a80c5210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 168536429 1250 168535179 168535183
    0x1a030f010f03080a0f2c031e03040924030605040204060e0c0f07020a0b040e0a050c16110103060f090b0901050d050c090c0403020301090303020307030e0c0109061d0a03030f0210020901020c12 84
    0x6800000100c1141c0c02400c1e030031b0203049205401c0d0880e403181c07065010340100804245d2665410240d10710165040601d0109003801078890440340c020441038801c0d000b805c80000c000c0c410050f50003400c0001d20f030b241520510045a00300c0d08103c49142108080140317803440c10f001c071855050b9140c4102d46400d26403020900c803000c0341e040080001d501042c041818055605d4207840fa21500310f06000d29201c040129541e88108442c00c112010400013a60109828507410800d100045c500011002ea407000c4c40340055405810903940283ca401880c1d07124a04000b00b9070140408540030490741400703035540c1da942d03c050b4204501401c205000588440030720810741c3c2c000c6801400901c180740440c90002c00940c012681200460714011006448840c002a1070003510300c103850345064182000d2050307856050301a81c111801040c4411050780d07803900b2a0240c000d51190700d03800319160b00c904029080001c0c81c003842d54043d1050256034030301e0ba8001415034a07250300341c5141840e00c0c08095454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 168537679 1250 168536429 168536447
    0xc02060c01140f13080702010507031e020313140a030209041e0b07080c03060d03180b0c0a0c1d06040b01110d02060f060330041a030f010f03080a0f 65
    0x1401540391444640c0d42c11011006984550301020f1414503903a0341d04541501100c0d650005040c41c0428010032005501403401410014001d003041001903085d06000b12012400c54080c0d00160400f103800581c520040541c0000b803c54a40f0060358040b084010988006162001038810354281010030103001321800640820507034425040c099801c1c90901d0006a0070545030040021140c600090b00c00a4100a4900a407002402c40390004503684040b039003486c49803184107021111800000741142e0f14030080010300d0840002d0b000e02c00850400d1200303809241e0006410400204030302158240c048810b603030082c1d00f2a0300045513440240120b40c00d504c1845a0a8648070306800a10950340000383e00344280b5445208000320784d1010700389900c6003146840340c40100410821079038403015910181e030284040d114130754105591050b5108c0d901c1480f48403000c24110010900c01440030040d000ca0140040c12040300b126844c0d03503100344c052300c01ca6048600300400c00c03058100f032074411071120b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 168538929 1250 168537679 168537697
    0x61c0206030c030103020901090513030c0c1d040b07030204030203031c09083c18030a08030403050309010e01140c070201120608011a0a0609031403071505340c0206 72
    0x1240d01c0e40b5000c0c0b50000340f64800e01040e88034014240000601c4102406402d228450608a20440503541c0c1d03002e032076101983e50200c0d0f5405c40c03c0400714013900d0402850007203210396100000241407904002d070300a034014000c2d0b020180100802e10140e00c00000329040c052078240900c0c500450031340c10030700500c0c05840040c150b107000100014600340004602d032500b184107040640001d941c1450302c0c10114110000100c204040c0301e0381c1003240c01c04001002903100981585c3c46100b40755919201648200c804030041030020041c00100c001c00d10401c007000c1c02c044000c1006c0600e00241d2a91788130003c10356580410002044401c691048580c402d403407008034001d0000c1c9894940d124082d111007030043c0c805815103d0003505a10b001c0c54468102d624503201c01c0095411511490b000e205129500030951204000361070010708000101e203921b01078080000761b00d06000d0804070702c9184403010a00141c0c4c008030b00c1d40320600108a032030900412030902c14403c0c0641c1c40842e40c540904088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168540179 1250 168538929 168538939
    0x1080c0d060e01090b09151e01050c01020a0807080702070f090e100e010b13140c0c160905180a0327050d051e0703171b061501031b08061c02 62
    0x2400c0c401500300c00c90005003280c46000da1f590700208881d0194801198981c005050342c1c0280b030b03440488041d0f400004041c0742c11460550100b01207070030399000e00f110200084e001d42c10088410380c042185900320505101801105150a80c7e215414240e4002e888510360760b42480381c0c45e00c4041218a44100e50078605104009403214210f00902c22003140c540207039004140100c140103035105a0107910070503030038460b16403030f10717202c408294101c405030501510a6000c0240c000b044402c0440c02003289002c0807520349403005440c0d481c00641900c2c140340d64082e02c1c40070006500a010840c24491050701480f44442d6030b07640200e0341c01e41d82d018130307000748401c40d40009020300401c04030760a0900008620039104009480c40c0d03504004e02c00641203d00251201000902c40380082c07166203ca05070840345103a030004064101002600d20312491041d0740e20364215560580500f941e00390100e440d001c4c000004100c050008000200160710525040d0409500110a6a1050000d80e0082d02c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168541429 1250 168540179 168540181
    0x408012f03060a030203250602030901020a1101022803140f0a080403050f040803040911041a0315060f0309010b0a1208070507030614010314060106090608090a020423060d0201080c0d060e 82
    0x31610783c2004291030b1f085030440b4035440100d03010340004102c43c400c941c10790042080d1401c40c1c5a402400c4840c0c00070320304601031a0201c0603c0d08060040403131408070342040140603200342c600135000314140c200800d02d0b00c0c0b0038040c03400304126080c1030351400f0b010341c00e050005544a140460f140e1164800c0d410682001003000300c0d02c05000000b80c015220b024004000c0d17502034100040a50040e8402d0301c0c2c216440031007002c1010740341800785400124649c0401c6800468070005440b50300507007518010309202008000208400340100702e0101d034252501000203003000c5402c2d0b644a4043d8024110340b1b000034401c2c04219080003002d00a640152040107101d24813082503129490a10ec1074880c02c12810b0414440307403012800034101c4100b6180e06040030321f41241038540000060a11a481c0110042c00c0301689660003201c0c03041500c0003218407200784c80c0c00010030039a0043c1501d802004082c0701200142d800c000c205400090300c001031611800c1c01d0f07501a02601c3e946e00846d81e80304900f8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168542679 1250 168541429 168541453
    0x303070306030326190b06280806030c0105070503070b04050c12010507050301060f050912071d010308040311030a0615060807050c07051e150408012f03060a030203 72
    0x351080c82603921030783d6919401c00320300d841c6140c910006190881121401004250303550050130201036107550b244004580b10300214001f48064200507064454000c2c103e504801124820501c90003400b064102240715042900100780d075084448001c9040c810001440010b00034100166581643d02c504014083c0c038091400c00d46070800040c030603001c2d0540c2d201c2e008803443c0c10b005580c8a2485a41c071a4216880c20000f00c803207904495a03041032203010081e801c890b89482c140301e90040290b80091003202c0c5070500d04410035020015040030740800c0401840020783c01401c07202100d4200c504001e4030308064002030300b002d0704900000d002903e0584184d501124122240049403101d4942200700d42e203600c0c080c1c85c01d100d030300c555840341c3d00a214203100c20314095003c040c10340c2020346002000411540803851200180410318601007021908204041090081c042c2c64212a013024400802050f100720101402103c03c0b5040c08000c0001200c17501c400b850750008540044c201e85441d6400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168543929 1250 168542679 168542681
    0x4060b04050306070f080609130b10051005070803010b0307110d0201090506060a0302010c020d06020c01181b0e0a0504051005150301060e2205160b0d06050a030c05100306030503030703 81
    0x40c46214001c0c050500024041c0d0300031814004c2c084811b40b15000c1e281d60303c10030444000f400400c1e681c8980100240500418600175505200d003018444d0b00020700d06110400480c61031044042c02080401c220a1002819003030540e81116041000c183d102d80b1074dc40103a444212800308000b82d4460318100401555054000d894540e000350191400e58031103000784050341e0100d00003e030206280320811401810500f100030038682c0114001070a00e0110000142500c031181d101c03c0054130084c07000742c1444020045440c510781d418074122440c52500c080301d003218100030300b240803c954510014060010500c085824001c10040420452503c0601050314004a1151074060b61806070003044031128a007034a4010707a039011505408845001d0614411412610101d629008025020118601c06001e040c082c0c120200201e0f2110701c06445001150303543e0707014a1207280702c81000c00c0400c2c0c00707030120815550161f40030320744240c444c0f606070050116684010000d100c00001c1000b150b0b41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168545179 1250 168543929 168543937
    0xa0f020729060a03030f140307090609080109050712300315080c1003020405030d05040611030406080a0209060c06010b0c010612020603070f1b06050f060301020c07032004060b 77
    0x40c0d5150241121905500c48600c084a0254010f5007488051020901949512101c884545040b0b5100180450f06801941043d40c1c100301181c6980000c3c845550000652806010303500000c000000c19510780707655500070341c032400c0304482061201c001030002c4900c80d03211210110754000f030180e00c1d180c5803d40c142a40c5104200080c0f410801925001e0050144011a82818000d2051208203400c0042c10000340340c494050550801c40018035440c00d000c20010040b150300c41c5501c4c3c51030814003915130308141c1c01140d581e400403c810300c00307190060b142d29040300c000c0700010785411038540420700600c2105034010f801e03c00c80c0300000d14500d0840080c1003501c1c0b010001c0c842182c2c0c4800c004881c881d1030000a600617170a000003000d092184c00c0c0165091054603011226104958580c0c09154800e1001c0d01d4003034075002000500c5481e040c01c29003001080e00210320708443d40100c42e8546601d0b000041c510003540c0032907051640e0095540440c0719005004000c490380d11520628541c3c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168546429 1250 168545179 168545213
    0xc060203010b03061e130b0420030108150f011a071b080d020a150b030304050d0b0402180c03041205190504090605030312152220040513050a0f0207 65
    0x1d51882c60052501068028030403049000c0c0c00b1400c4a43c6d1407506401504110f120250090340d252540701200c0303444800b01030030041d9483d403140d0301e504202119003803082d10340441090703203402414081e082c645030705018110340302400b2982091111050a0582d841010320250440d04001c003080b0011440b00000d00403a44501c04130f80011607001d4050361903040310f907005401c04a01102c840b01b60102504102d00ca014000c2c20b41b8686070301c4000003401e50302180300503a84074400408000c11030070060420524105080d0140d209072400400480c032610004100030900c81704981c03030b17034403090180040d120082160707084840c0e000d119520041a50700305200f1690f103181844400641c41c14003004460510030746942e400b13060354480b407c6000e003102015031141c00883c00340e2001c8202411054900c04890110004581d07080395000c11000390a44038841d210514081204110680d03803034441401e02c0c8951040801d080e80d401c2244401020a150958460b500006200041001a1713901d80c0d8900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168547679 1250 168546429 168546439
    0x307080d0b030d110d080c070b01081f05100b0d0603021c0c1706012c010609030506241c0b0106081009020a090302010507051908030603010c1119030c060203010b0306 73
    0x2da81c0c80800c580e03120740c220040c2200d03001011030780c9005d40300700303200b80d40311141402e40c034034111642e5038071607029000b40d000751010380005884204d10075124418070000c0e01400d80c14856070528902c40c1d111312082d032140391400030002a22a25600320350700305000440d0010001c4c10804800d069030070101d130102c00121001d0703d025901140c0d81d000c081080324425100d03001400103a081c00318400c0c5071426030009500344d010f0809000c55240c80e0411141c01384c6010390718040038615628000e03180c0a030250030710422440c0b4074441c0d400c00040750740040041000303c51030b2903100d00e0402c80964400301c0d48006054070031701d00e0011844071380110302940694480a1105492a683c40300d21040780500c00544001a44c04003081001d980318401034440640280141c8960303500104069036010210700c0101c0f402140882000390754a404e1045050084250409540b104400c8407420b407100c07050807807045407203081020304091510600341200f04070f50100045641e5610fa51500f03020790021610700f4032031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168548929 1250 168547679 168547693
    0xc11090402132901031404020d020a0f140a080c0121090203030d1407110d0521100503060919060207140f0a020a1d04121e0503060a090204030213020703020307080d0b03 74
    0x254424032600f40010344c103c46c00400c1d40c41e80e030708000c078001d5010b41c00c2e81d01200b825804200710911841920043c058070058140c0c601d05401072240f0900158400c8000c4d0300411070400f07180e41c0000c007000004001c41e00c161840b4a5085665000300401700000e5054400070690142107580341d84030010410b901c0d0916081540c0d070341000c40703d031012801ca07044290030444a444180f8020303c00f401e0001612610612940e1920071a0b12452a003201c0c451400c0040050070030641c10141b0000790002d0581c1301078800e05100c0c1445104125040c07074014031499000030340e2001d1141031021107000d441c8200c01c0d9915400020661a607988080c802640308c1c4062040c0051500b9a0460b03008101c005808001d1245d41da50301d0b041303440070440c0742101c1444070b074000304016255003417482e041c41c007180e13124603440c2e082000030720414410329000021070703503c1000103101503941c02d0301e20540d2980c036035005a550101803a0403070541c049c1e1a0010802c400c080b0b252580454260008418500c041d0300721204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168550179 1250 168548929 168549011
    0x8070848070305192003030f07050f040b0d06030203060103240c0807080a1515020601050607020f12010b0613060e01030c050301090c1106160801060c1109040213 71
    0xc0d41c400c015000340070620400c0000c660703000c08444107802c2d06a82c00e010902d11041402085509400012151503410000c00c01035407128101c1c2c030076004041440d156090810000c0311813420b01c036900582d140084089460001c0d041c4540000010b5507000c0c050324542c3d41d42c0c2c0b401c45100c0e03503200800c40442e0300c4e6486603109908280b2442e0080801aa81d8025603200d814080d500303020f0203001c0c952003c0d21070307080e02a21000c8003400401805190b0401550800d066002801c08106800c030a01c954410042100036a507a456040340b1000121240c910710002c2d400203131f004013048040581c0048004c070b20f80002d508001d41c0c041c111406a02c1300010300e40c055004604503408a805600800d01c14001400044c0059002460804003410805140f8040c4e03880580f0701082202c41850036800c07100d4030b018840d0f100d0040b600609060030b2071619808595540010a541c00050034040c4100e00005000e5664403600345d2607401001008001100d80400c240100e41800000d00304110709001000907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168551429 1250 168550179 168550321
    0x62d03040c090209060301051509120d2006010506210a06060f05030708190b0612070e120303040b07030615030c0807091211030c03061f0501030c080708 67
    0x4242100601040c46c60b0b00301410040011400d8680000b0b44009100b40080d0b5203668900002442029008000450110900034414001503410a0030500240d05840c050603000030000d040d900101c8040e925903602054009036200041c1850301612044418856000200d80c4180c003500c0c00f95684549102c404141510640b2090311941c0c0082e4484001580e22181c510f2921040e1080c02c038042170304181c02000070040e411621050301e545a440e400d01c074034150080c00e0306a02100c141e50300380d00c00221401040c0c50b400000c0000d0081004d40c800030f1a00d900c80d81c0100007805013544003500c0007005030310080007001e2083c8034002040e1407001248005000b075440204a030307802c40384514210040e075103110b100c000152030140c0502c034900c00f20321290b4082c0a01da20070356508511054034101060401e4000c44030b0f80c0580d06041c6800c40c0e40503200c1e8000b4000340c1c05007081c00c1800c4280c8502c034000d91000301c4a400301da00e54150411451032100c2c901c034140e4440d040c1c4085038a85c180c02503d814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168552679 1250 168551429 168551437
    0x7030519080712140a0b030c130e010e0106120b0402011e12060503010216150605060403140606010e0109060e0a0f06030b030106140105120424090219030203060105062d03040c0902 79
    0x144030400101c002552013522078026000880001c1c023036411070080400440c0c40d94000a00b1008001d8031141000c0402e40244074030502900100d0083c80170500d080007418509002c0d010143c01942040001025a405a03a40c400d400d0400407140c4040074510340300802103d41080fa009007142840d41c001154501402074943c1134241644c0e1070000410350350f0380f04030000d03c48010141e00e901c0d100001078076522640540000c5004403803210442e2000030f1100e0804400500460500c001c403906045140d034400c10540941e40380b424800c401112850005031460001c1d03005152459201c080810b000e541900500f801c04015002884019140c100004017500e0b0b0f03610b0b00d80042c10900c45002e080104481868005004c3c056049281180c07603040e10380945c00020b800c05854030394100c0c00850815524403068110b0f01003102d00510b04503400a501d0324410f1041c94070038400855030200030072082500d1003100150b1291014480c4101540713140e95007007264161b402181c445800039044038580221 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168553929 1250 168552679 168552701
    0x209040c03110910090504020d1b03050f0c0a110a031206051c0b070504180b2d040e100e06070215040305090103050703020d141b070201050d0207030519080712 70
    0xa83c02e0012050502c55112202d5007400c0400411204c0051251528401020342c8203481102191001c3e4042103101903c020143c050b04061a100402c0b16410807030404582207038589500c02e035210070f24441200c0c910f6140101b020781d401101c02035000c041c2c002450301a0030842c0c1c0018000940d450040200701880e00881050355003241691000007030340e41d004143e2100c201d0800d98145a140e80312000c0b171a8140841000103581c8120328a00c030310300340021000400c1000301303000c4841c00d40340c0311460104450309003e0165494602100034500300f401840300d0040e50920400c12000c0c1c07540c10703d98a54003550b03500b0250080114240001d0500607090b84100e4140c1c80305490701c001040114000c1c000107003c441019070030322141040fc0c00380d001341c00500b40e0035600303d03c0c40d08014000c02001070458402e03005004042080d000180d030018191480581c40c0d140c010384921700c0c2e0505440500c541039118004200c190201190180c120600c40d00070315440d9216800018400c250004450384d48d219 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168555179 1250 168553929 168553961
    0xa080402040203090f07061205130f060903030f020d05010509010914070c0305070f050c032806050618070503040b0603010c140d1b0201020414041808070606050307090209040c03 78
    0x4000d4209034006507001403200d402c56428a102001c640e00b401c1c1a40c00400002d000f0b085180041c4056000d07058000d2443c40240d50405415a500c04c1012141c840c000d1110380c0724a440c00c2810300a5000d02d5540400c608259038070a40407041600415007401014860b580076070021600c007d5521032800f000002c007400000a0319a13002c00e82e00003000000440420070100319240004854401490000344210024009208050308040c00c10000240c6218003e50b02c03a01c0f000c01111611004107515009500010161600404a560741790581030b0b00d1107085544051200c80e076801001513200d140202d50000460312039800701406e03200e42c04c0303c1e400001d052965820b00350106800400302a001e11348005407607180d200c400c0d030700003610100000143c1d5000c24201300059000944561062044a0070810303c0744030084000c000425000292041c2c001240e2881000029400200070b001c0060488481c43d40e80c103812000b0394400d41806001da0304102c40c0070350071802801141807144105003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168556429 1250 168555179 168555181
    0xe0f0105010c170903011104080114060109090b0f030a080712031503200a081c03050907091d03030a05220b010504020c03040f1e0f210c05060a0e150a08 67
    0x645044035028568802d050910403c50081345940c01d100c1c01c1c4048601c0b40030a07444a21b44203c19085071803411141b00e01058010070070242d6a80143c004041e24403041001485502001c08030700040900c03040d5580511804000310280504800a03228541c8a03030981f0380240c1c00e0040407010303181018040d900c1c40300400c50a0000074442900c5003261219010f005820049180000d03c0311141584a004190014103007000001d16107048c5030720700d8105040c2402181001c41070b061381c1e080b483c4101c0e4001d940da50030030b000d181c40100507020016041c0040b60f44034208102c11b04014401501c01c0c004031208480e4008880c04082c2c0350540f0203401c0002c078080b80c1e10784818000a0f5211f8124201d60707000c00c11021520a03805071000000c0d0090b822a075405e819002c1140783c0340c500079085440442c00e803d03800c028030901c225243c840950301e0502e2000e202c0c3c2c0c92412240c0c42110b030700500d41c05000851045100350344120601d1943c0802c560341c5d200720145c0700d461161485060b000c00d0008124038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168557679 1250 168556429 168556433
    0x10090b160e0d020612040f122109050c0306070809012003060f0f060a03050405010c03020c06192009030c1237030f090f060804020103050a0e03030a060e0f0105010c 72
    0x2d20540702c4640050540c51602d15204990b040c009000c540480309140310407040c00910265600040302c0c103149003001c140c02010041d0440c0308454803070350010a96110040c00b42005403d01c509120140003600300e403c5824a408080e1904104a801c0c100a40c606054100f0142c5000903021800a00701b01c0a491916404103001c0c081c0c111b10101500820b60070240320703180d101c1d50300500b40705040d5603001400741014940642900e40c080c1c1d907042058010b03c0200b041c0c440100782280c10690600c0c401d204240090302060240c0440884443c4803050362040885e203150890082c668001d040b0191000038000d4001c0002c2c000360240d450110380e101920702c6983c4c000e140d01e11741904501c050110491780815900c02c44103851031404500040c50400c09890241c1c0126444018041103e98401042c2c1801001800564000d02c0607040585031408940c08841640c0400b408100390820342c0c0c7d50340740c0010781d100540f200c0c4c0720b0720214140a400040322a02c5203101c05040e41c605a650280303031042a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168558929 1250 168557679 168557689
    0x7030c03060f0b030304121a0402031e160303080f060312040504020903030d180309170c0d1b0303051b070b0406051c0903090302040f1a011b0510090b160e 68
    0x11042e0714404540d60020080e240d03a0800c0904004d01204540c40e02c2c00000e031170f180140008250301103003c80350400901c00141d901065003400c1c5503036292036903d0034815006480c502010b0312454141c02c02c0090010040c07503030102201e88146004003c540d0643c0703804051503600e00d05012540202c070010312040c4040e2403d5001880c88042c010100c0b814403120002440c12079607000300c01c0c00300081c200341b0402016040308441c1d0080c4500301e81c2c1106821448502501c0b008a1048503205030450010001080751042c0c00d1074888030344a46c05987c5d05d0b2640340161031b99120000c8480f403100040803008100c00c0001d0800150713100c01280ca8149032038810180c0d100c1d080507207127003005129400c0800d540101c520900c2c0c00310b806595815849407441c018801114100b004031590103081480c0c8099100344020000d42070002032a03c90205858075800b090000c140321402000c50003079201d244880030b016000028071500844403078455469101c030800e42c01103500c04c000e0205000a079140300350720f40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168560179 1250 168558929 168558941
    0x103061a031e25050901050102030703020c130e15040311011811060c03031501121415060d06080109020f040b180901060b0406020d02060108010b01050d0b030f1e0c0307030c0306 78
    0x4084215401d01e20314920380d4050582c82029000f03020802d070400c03c030038a030048566006201c00c1c0059483c11040ea10001e44810f15204070341d005600c1c100d40360402c2503082d404071510050610aaa00190070081710312030121080d50141c0010360040d1110300c1c051018420b140340344a4030b80407816911411381c1c901040000d41d0824a40c0b22105201d10f50013150103000661040040100c40481a461003002500006d0101043c41c0490701c5c2150524030100700714002c0d5005102d2800039410300010b003002070600c0c852899000c43c054200300000030420300c1500918002c52003140e80005040c0008144401c40748038008080c2d0001c04500d88000c8080006403058000503180000b0034626120004031180c4e501c240e0281d801688410040c01600e9411b0040a000d40b842c44001d00c9454803800c00203110f4001c2d00180c00341ca95a41c0c248200b166403c0141c0c0c2200c040f04010b90325000d5036840c2d100702121b05072a81d01c500d40503050910a040c036003c285082aa607000b050611a0380c103585446004201c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168561429 1250 168560179 168560233
    0x706021905180f031005010611150114131d030702090105120607080408040e0c0415030c08150301090501110910030c1205060d020306010f081603050709021c02040e0103061a03 77
    0x21700c4060510080160040602800081e202d40d82029426003c8500d0290004580700945010b400180010407208070701d80410881160310015900351540c11000402e8814245146800e02c130a01400c0f4890200c094490540200c42848040c1c0c1d940b0b051008407540d80c540f0032050340104000a004501603c01e0342d400c640201000d608040e2034042450014a058030340e00071001c0003260411850000715090303500240180740c2440a80301c00c40000d405900050030803080030031550003104850f1000d600084405410200030710440407020641c036015840f01c00700078003809050110025140c040d00a880c0920229074541a4000942c80003200903d0054001740d403000d144100407025a508100040c0600002210303111481c1c54a003110345414041c0026141d281300d41141000810001303e000c1c804c980b10280c2c0540c4c1c0300c00715a84410b030506001d54070400c06101281c00310701ca050000000341602d200d804208514208140b0740811144040342c02075050340100580c5020711070098030792000d05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168562679 1250 168561429 168561433
    0x3030604050709120f060c02030c0c010806040e1504020f01170a051902030703050f010f03080405060a110f0a150624021009061b080103020928020706021905180f03 72
    0x160f160b5a0100d00b0000e0b04d442940c0d40c2c0c0c503c1d8807940a0242034407490070907040500081d03107040c61800c840364641728540d00440c180b1040300c9c0001d2080e00c80381c1060120f070440c503068541ea0942059104a0032005540c16401440c1d1421034000b2135000d54aa400442400c8000624641c0c0340c0d040724024200c01010001c004102101107210003410740051401250700d41c801180034a44205c0134955010141e0064100b841c0b40f0800700049064141242d00b9684c0c1950919628007003000d060310b2042c94458184818414903400b420121400b241c2000040c2c820100341150b510032800c5542580c0c2103001e0b5556030b04240314040b404401e0201d202081080c2401036961409078070032020201d44025405541c0541c440018240c80e200c41c0034410310994113810a8007040d411600410408800104601c2a2042d8011040c1d81d840281e4020b0b6845000840150342e40c0c0081e150101c06500b28829244140c50701e45801d803040ca015005940c040f0402c0303030800002e030b6680c00403c03040c0c4105401c015014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168563929 1250 168562679 168562697
    0x5030c0706060e0112060f0b100c110306010b0a090807050a09090201020705030d17010e0f0402120109020d060204060e030c1003020d022502030d03051e071e080a0f0b03030306040507 80
    0x700c3c00c0040c91402445501800c2d11181d40908124040c0c0c2e070121400483c043c80d14000d031070140d481d4521090135810701d150420060381e1515043c601c0004116000d0b034103205280000401010590084c805040d0958449001d00d83c6ca84a0b140c0c2c982c1c0354020107900003005803040c003c1e013000780d100040340e41c014070445034a542d5500c0802e0808064003c800d0010746c2c211020410b542a805850380144002c0481503075034904580b00d039018035030161000b481566404041c0070307c20402d41058003150340051a1446e08001458143d000791b01c14402c2d680462043c40c00d130b1045180c00f00d1841801e84000d00010f00b80b170a0b24804400039030100120303520a0740c2c03d11100180f03400c00c01002015001980f00a4480401c03401018034203078032040010101030400c0d04000000b00c1140038002d18030a421402c010a8135194402d988881c5040610407203c40e40304210f49040c2d80c00010240a644d102900300001c0c8001502e400c00d071070141040a41643c0b00700042001420682d202560000840c9411940303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168565179 1250 168563929 168563939
    0x30d08090a061b02070b130501110f0102120402090f19111c14010b04061d010306080105070801050103050c120408130b0708030702060a0506240c03070501050907060c0305030c070606 80
    0x40ba0204180003011030104120f03054a80d4040040300090f0110002031401c240124140c007404050360300600d81005100c668584180d00d00304003480070701c0c0154000303546070860040721901e061000c40c1c00f60f201e612500d011a4401e071030045c4881c016041c00c0c40243c094003516444c1c1c805040080442641050200308441c0702100c080c40100e480301014001050f2400c0b0720b605000e8050060b00846940c11007003200704078841d08078038000c110b0f034610016800003040100041e4020701c959803004a00f5405e1000304182183c0c0b00304064184c400c01d8038100b28030b4071101420a8a8050801c00c946141600b00205011444283c0a40080031072607014031384032501c80c119a08240c100000483d0080000b00078051001e4050004c1640028400d40400130f51030700c000024081100980c00052003200000c2071601040d0b80340850742c1c08000c00e02203903034034601490060b00810003100c1b800e486014003400402c045129905000d040c5400d940e0703c0c1e0560319007450741100d6038441c480849009546c1c00d030001e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168566429 1250 168565179 168565181
    0x40b040c270509010e061801020d0203071e02120703052d1308031306080601030b0619080603061e1f0902040e0709080715050403021801080d0e030d08090a06 69
    0x129003046910040307000040c900700a0151000500215007a9061a01c400c143e0180000d1017a0310210b0148021f4980045035085402481208110038a040c000020000c0c000c0e0403081910b4000340684210060714100201207840340481801403004210400503580481d10800c0078104041c0c5c40001d031509884820b161720044810f42c008110040408900c2e0307010800b62880b1100104416406107207051211902030800c15114040c010502c80d1100c040780702070340b0981c480030850030050110340d0f4070209409040030814489800e0000103980400042003030401040c10780c007442d00000040d034031604540d10604940002061b15514022042c0c440c042c2c0200c004121008140f502401039590f810410180604076004003c0800c0c0100d0003020018808001125003c4030030b8403c10344102c01d40c1ea50116820300c20307030380013a46c041e405030f46054032090f0184425040360204000c5030440c0800741e0042e11800c48606441c0d908d60041c0000f2890540110b160344d5100c5100c4041d1454491580d4482c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168567679 1250 168566429 168566459
    0x112020f280f09050603010605030411030f030c0c06040e16210212070c0b19020c0708010f0605010c12030504030c06091a010b0403150c03090b0c0d0b0a0b03040b040c 73
    0x301504410407140c040e55900a000c0c407911000703614210400608150115440d4032040c130640d0104030f0000000780c1806103851440d502072000505485142c000c0b006101e5036034001902c010401e000b4180141c10501c0c7c687c00f100c084804440700082107a484c1031000000c2e14130b040c0c1d1031050103032000c0c0316041d11019130344801e10345915240050700d50071400c1d000104500018200b0080c400080b201e480415200e5045030380c0710745140441101c0388c4052034075001a000d00d00d841900e9215000c40807540078819084540044d402520030440300d42d49000444011019a901910301c00b00315180724a01440b03a004190310074024140b010415645075600401c54070014016035910300201d1030004001044801e4a0042110300d00352801c2c0740c00d42e00e80201c8184105580501980d860a020b45400d0103030300b10f40803407030300304c40d2a01107842d1110740000242d01222549080c01e2a00309030103081d182040c500c07010346040e0688181150b5075551244100b602c040c1c0103866502d000d0600007a0558010f00d81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168568929 1250 168567679 168567727
    0x6020a0c0c0f030b070507020d060b1f081803091e04090c03110a0501080702070e150303030403020601180606050a05090420091f0c0308100e011419050112020f 70
    0xe504840e1550134550380c41e030b00181085081160421000000d80d5034001c2602809400050020b460301c0490001044e818100d41c40d10705451510000d5905540c00500441c8a07015084840140c059401503064072849140c001035444a0042180ca8240202c04a50041010007520024038012180c0324a90903c240d81c2c0125407920502d0b800403c5810b00d079078004020002820b06c0039031350030048006034591403179005504603450400d0000702210541550f81103110406020340c2e5490a02d800e00a440d01401d01581da141e512203007000b100300e2a00c0c8200030480d10b1541d14141024441a81113500754000c103101ca512903114603d0711200c0c0007004000d00e01241c844001c1c0c1e0703240c000c1021300c004542c042e501d01d40d20900034690483c11a4000152125080c1d240c075210382980d072a040a18203944260f000200711001010010031040341443c9400c88510f0300b05e81905002811003a0b5251100c80e50191a0000e18075801d031440014440c1c0182047d000c03c43c0f1100e051940e88004000c25080741c40755 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168570179 1250 168568929 168568949
    0x60a12061e061101060b1606020f0a090e0f0603070b030a0e100c030b04111b10050106030911120c04021b010e031e030106090302010f0903021206090d0906090306020a0c0c 75
    0x402c030701504a01c4284001e160394000740200c62500050860f14000c501840010071201480740041200d03960450708280141030a13561038141050005140100e00c0c0140c2d458014610301142c4908030081c0124030494005004007505400e00341410354641016140c950300e561140d8a00040d4181403144c003004081c40b1100180e040c090000c010190344509008600035480c0c00700c03080c0c1c0c010780ca02c1160b09000f03001d40c841c0003007285c1c0c2015901d02401c88000b030880c1032500002058030759040c0c014400c924003c40c0404002d008040420888184401d041c464030b03401303500c01c81c0450620303070040c0c0074160038030343d40b482c2c140381b5188200c1c00d4400599058020f41c000040e0070340344210102d850490100d03c0e070301d20703411903041250203000b080e024040603041c04090656000f940f8030600100c1e01440d400740954040810140c025643e501058816800a01400f180c120019216619400480304070384d4402d007506203140c60b0394009500000d001001c0028401c019004a0608141d41c0020f042d4800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168571429 1250 168570179 168570239
    0x12030201090c0506090d0210090e0f060a090c0813140f0f06010602010902010f0e0d020d110f0103020a09170106150216081204030204050603010b0405090c01021b060a1206 75
    0x1510942030b090580010b03200301030902440c24217807105111204043d81c1510004154004107005890418241e808004422100800c100d20440e040c0908d600a20013640c6104079191110b0845c03040c0c40c2d128030706c400001ca803c2c000644000c412843c05c0c002e140154010483d0409540c1c24505117040150f045121758005006000343c181c0400c04a40140303501e200030040540b0750b0b80001d02010703102e10340ca020002c01701c1390310100d039980d482c265640b10303401007603440c0070036244ca4900c11001d00720100700c0c8561140411005694068000c45548101030758901c00d5043c10459401c0818012402e5840c3c699a50f0b003006c1031071900100034203031841154000b030890140ba40254948404140c2242c41c542e0030040c0c048080d4822070050303d003a698100c2d008101952098046401030402e1050300d60701c5800c20060008000020600d00c100c40d0742a801d03113030b1b90254401003102e88900b44800340d4000e042009168143c500c50f0420800c0803404410120b13415030740d0300440c0051100c03d01001c0401c0d641c20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168572679 1250 168571429 168571433
    0x51011070509040b0c0a18060f020c040509191104050a0b121506010e0303120a020406110a0503090103020703050409050411040c08091b030c0613080637061203020109 73
    0xc240001460304a410a12601d0250f0b626919100041c20444004401084a102d0580150100880000215040103640303a88000045c1121840740c68040580902d1545000a0801d40a043d01c2002e00301c0060a5000c0048601c040092000d2429212422480024403c0d540d0701e00030303980100e402100124a4003280c0c0104240924500d416526650205004076070300c40c260305880d5070050b07003400c0c0401401002d9020900310b1144450702c07915181240c0401025403060740c060000e0760010350700c6603d04009800c034240c2e02d2500c400068103c2c0c0c4180f1003041a98443c0e002041842c0c481d2524904145c1d039080079000344c6109079800c403005030300d030f110081f02800c2500c00e880c01c00009241c842482e003088500ca64440000248440108241864424141e01c0800c4150940c0f540641510340d10209042600314442e458001c0b91810301541000c43c44000344130198025042d040301042070070310070012540541600011282c02c181d81c9440c00082c0948a8a0414031424000c0c0c00124141602d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168573929 1250 168572679 168572683
    0x90c150f0f031e090b0106080412030b01120903020706030c05040e1609032906090402090708040c0f06090f08030c1203040606051c020103050726180f07030605090a020d060213051011 80
    0x141c124404201c440020271010590b000c3e01903c00d0455803c5c00607448141000403100071850001d00305846080100c04020550700169500c2241ca0690f000c01030551541411901e0348900c0c410009105d42d40008120408051004183c00842c142002d08105540f9602c011074070840c4e046e14400ca1364a000c80e00c40d1103074109510f40d4081c100311040b5081f0303c1c1c90390001d950780e00050301d494208405280020108440d140e401009806110301da04d050658400c00104621214000c54604004000d00041c1d000c50000560305810711300e4000c3c055072481007035a59820740000b8001e589041d2900341c006016150351003104d4140740d5500b41a0350800490001506a400c00307072102c02008a907202c0ca218511040303d800d00d241d0710b918080c1d00243c44070340c0c041c0840ca06520340b800e414068080d460800700c40006481048034411758040c001540d40110554580d10b125102035000003030710001d180060700301d9001382011840c41c1c0800710200e8840e004a1103003540f0700001400711b0700400d03c1c04142441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168575179 1250 168573929 168573931
    0x12090c0312080a1418010915090c0b030403021c03020d020313140c01020c0105300f09120315030a06060e10080a0807060e0a0b0a090c150f0f031e090b 66
    0x2003007050004d01e40c064100c420304000201002c04a078084c0d10043d80802e0290400040c1a410903184000d46c00b44200b010010442e418045030300100381440092041500c2040c0c901c03864168000e018040308141440e04000c4403211204101a07080002900d42c544c1031019500131b08081c0b00358545a0710510700540d0039581c405010300b4503803090b103030807640f80c0e40003035514580403013071a050380c68980d4080070280b0444001d13098980400000c402c1e0342c0c04000e0b40b003a1071007100700e00c0102c1d5903a15011110b5880b2001000c1c0703803085080400c0080c7d018080d00444a5280b207020741240d042c52500e4035003070101c4165070010050900c40105200f490300b05405000090018807000e41036202c11a50ba5000074812140001c103e1503d545c29582d54240034800c8d1200c494010301030035010710f0a8102c200080c80803040884441140600100c0e0f00b0003d5405070344500130701d465642c21038950794800e59464815012440c10540c44201216191000702d030f440c281d1581e20b00010555460515142505580c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168576429 1250 168575179 168575191
    0x1c02130614090a0e070305180d0e01050c06070801050f010203250f17071509030f080a0e1603110103151802071406060307050109050d0312090c031208 66
    0x100520a45009111041802048600c24280081120071600c071541d5076015111845a0140000d81c3c0041c1c0305240307801d0030703100304003036a0104000d984400b0306c815103c95409581e08143d120b041240f110f00c0c0204d2007040c41400c141022401c004c45800b04504d001011150303400024404001017005041c0320505080c1c104090000d90b081462003419031502c000040540507160010108884c10b01605400010321a030300590300360083d84e044d001c903003d00e5010f15422a82003d00c00108000740000c0d03c41c44421542c9aa035100c510304d00d01c9000c40341142e010340f19030350b450790354482585108810010708116244001014800a1950400f0a18500f080e10254181030802c41b100c075805034581407410681b20721643c2c0110401e182c0f0f010400034001d05000034070400c1034015586e1000b100084c003511404040302101d40e000d80360380044407081e915100721070304a4081403240f00028080d0440400d50800c2445c001034042d4a916809104000340d8400d0310710280180c0c0c550700203640700c0042c0354454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168577679 1250 168576429 168576431
    0x1509080a17060303180103090f0602070b010303110a0b0a09150e0a02130b0a0b0a0215070c0605180d03022104030f1d030304050603090118080309070e13020405070c0c0b1c 75
    0x405c08241c00341c02e10481148041c1007503640d181c4001044400c2c40d6074111190407584c115150b00c454542444601028081a40801c4544004007020a000600340440a900c00c0400400340c840b01e00c4036020348101001201d0302c1030820269030030079046200b0801c10380c000c1401441d03d84041d00500a0080c4003014032603015040290100d000c0c0c17110f00c100300c115401c3d03240c01a81c849140404a092117071180c1500074510000040c8807000d640501b08940903030107040100003a072100d28110078142200d40481e01c0e150045040b484409000381d02400d01551a10310350b20f0b580f08140600269000200c0f000c6001c2003148640c2c440e156407010348045440c80c1a030110300304405110000396039000e103104852041c98000001140300304c00390410955548a800315528444403494084000e800465481e103451007000b0f000a4110281c50b0603600426400e1a01103010340141c090001070b1200a2041c81840159850040010220030030301b8020300d50411219100c03103d0001c4040344145c0e00c008072982c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168578929 1250 168577679 168577687
    0x40204030507030f14071e0902030402010c020105180a0e070e180a110c0d02280201050d0203250210060510170601090503010f15050a0b04031509080a17060303 70
    0x80c800541007080d682c10130048680c100c1c09180c00d8420224540084506001c0e180001413814420405180000d848803490300c00d8507210660302e001c901049401900145460029101550041c0010452000c0e8051034a082c403200748040358454a00340c2c01486a40c01c14001c1003011030b4401000d18030301d842220f02c1004682d0300781c81100e60b454054901c40c01e00380e48062145586c661142201c03080c01c1c00c9815a800415150000ba44480300e011007a81c0c0f00e641c0f07030a00a40c0c0c991205e100c10490364142c40d124208085401820020f400c014028031000c042854207489880390700c07a21143c4556564020715410700241211816180282e005030f0103010115240480150020712081d004d00c07520074130761010380d160001218541c07901e030f01080d0103504e401003880d4950742d40d0b000800c0c0c49a02e5203620b200907960700c040c800c400c3c016108566411000740018000950308903008500c01c0c200c69004501c0d000c00d03480340305007584805004008110650000e060005c000f0b0060303603000030300710091030030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168580179 1250 168578929 168578933
    0x150e0309120f0616021009050c010206090607140706022506060f0e04060504020d1b03060b030a020609011101090b15100201090c06140c0303011d01090b180a1b030f0b04020403 77
    0xc0e4801c040c04000c1090038a44c0340515141c82084400341e82d2031400c10a12000f04942082901c1d0420800700c14018090000054232402c00003c0e05401111181e45881e0040b4690100c42c21640054000302c0b50f054080000c21a02420006042c460b001c0f1010200c41800c25450490102c55081d80200c801d0300d080401008080407500316260f009400840110315a46d03180300180c2c88039180800200030116081035800742006030411a000d0ba4480d51301042000c2040040540c0d814002038000e40c00344081062480651103a0745022003421020004903500107103a40b2210000822220350201c1c46900f07140d6006441d01141c20a0280ca060000300f03d0507200e81c5444030400c030300c0e000d24401e01803460100101c80204208940d8903d0b030f00c2c1d0541e600e80d61a0b00000421840c0c10511758450740740840049100501c9100f403110785400102110215101310440c283c54040043c0300c0640300342c1e10b2840c071482814005202079541d607680c1d000581c0814952002d004c540c002c0720802e004910500c82800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168581429 1250 168580179 168580183
    0x807050307210501050f07030c0306050609010309031101020706090b13020f060307110307140d08090a1b03080d06050a17101d0d0309120c1e150e0309120f 68
    0x2040e03a0208290380000c01c00c202e030755241004980e40082c503541ca070504000c9140b0300281c44500074601580c062103d001c003440d040f010745115000c3d099001e0010040060258005d501c074003845482801d0052032003200c446901d0032a0080e40701074810545600d9110100101450050351012072410401c4010542d50081000d0302e000c0c1641d00d0003003070f0010110b07480600070070007803407001c1c0154201c0e5560034483c0342103081c16032805c40003e00c45c8680300d04030b14028091100c2034400c2c410500203000940b0745d519124100281c0004207940b407042410080301103140702c0300401d1880701c8034101140507460709041c070208070040d5021f06e49403001d243d000d001014000c00e0f8002409602080802c20600ba540c9445035203480c004942128840c943c020441e060701034020380c806a0141803c0f04030300d18596415203451a0b00400100f409a9104d1071202c03140d000c00300040304030b024658444018107104c088500f1540c1d01035003202c4a920118000f03006180c4020101100c1400c003010380b80055410b01c90603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168582679 1250 168581429 168581443
    0x602030702040f021303210503010305100c030b09010b1b0111220f030510051303050931020d0614100f052502030607030b03060c0a0903080d05070908070503 69
    0x82c03003651683d03107000d03951001e9015210750868080c00040321954902e400d4000100c0c6500d6864610f0f080c1c6c0f0b264058601980c2038904894000c000380140e03401085003200100700048031203040c15070340d401244c0152140106203018182d880c141c11350320500c111408050450561080d8400c0e0b0501d10741d190900b1181007034031000d00c0005514128a0202000ea101c84041500000300f2042402d03000002d0000018074024001c0c113080c4100b2058540c980d071041101c510b5034016000c940d082100c5411410007040700203500c1c02c4040b18800301404816513801511501c0203c41406c0e40114984190000d0b0340714420040180c07139132140320700907904003103400d400076403942c3c605001403444003484250049007118031014001c6c4040888506c4100c8000d140c00714000141d01a00c503583c0010880c501030301c6081d104110040042c81d09540d5110300d5a0f03a03900c80c44084c400c00424890000025040f0b4000c0d00100d61190400300c0d0f10310702040c00505050480c1c0c0f00d4403039035101a0742000a61000714140e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168583929 1250 168582679 168582683
    0x60d020f1003020d090809090f1b25080306030c0303040e0a110d0c081603092001020a0f0b04140303040309060806060f071101030501080a0308010512010e06040b041b06020307 77
    0xa11101c1a01c1e400b58000d005428025040c5401d181440040000c00c100501c690442298034040d10345400c0720707115150400701c81e000350300f0310341c071301c0d22890841c40341b01400e0381081017217080c1c4000340c440320780301d90600c24070740c08a940103000710070b000b02450284a2901f86480503030046040034070304020125814070242054084958640c4403590750302c1840204d4601400202050001c0f2140e24401030543c5c0d01129001c0740e1500d080d0751855443e121303010b0030700c0300354000c404005100c685110044401210b01c1c546410361091611200004040640600889018584000e04c0746000d0034440c0d0384480c0186940c656403c10010000065004100340040e5800c0c3d1406072600c0d070301e2201180e0180300f41020a0381a240226883c020061841c030303800d003004020b0382d0510051b40d98104d01d655070000c00f40d00801145160005201506100040c00c4c911603000740040f4a01c2d8900d035140e42422015981a940800102c0822050010b17001c3c0d4588101250801906130918004009443e0f010302040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168585179 1250 168583929 168583939
    0x4060507020f0a0804060e0103050702100e1608030d0609020306010206150f04110318071a090406030c060f11030a091e0b0c07050111030a0507081e120f060d020f 71
    0x204080501c00c200c00e0a14080400844100c052503080100c400c0c1c01510680000880c6005402c1c482c0d4828080d103402200180c0040051001c040d0101d00580080201403000d440750842c4101d81d0340d8002000300c0244180310185503202081d101c180c050300d490390455000385004005000460b60300064440d441001098100c4620700c81c01d001410508408002944c0203007000d000400c0000100001c40c0502038550306000c68014400401c1c0c0c45030401d00c21a00c00540c589507000b03614051a0041010700e10040001800546a6803003130303120300040d000032000401009660003000e810080c60f0b800807422500a500302040f06000511018803030003040c00740c16800c0b480342450203456040001034010008082d0b101c40d20355444035aa105135204407400507c10404884c240c91001c03049907401080c1da90792500d000d40e0340d01d40018952128074000f90000f2800600e24440031a000904202407610b000b003245818460080003600b60041c10680c0f103401c9100f001c50040c0e99003001081140c1003510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168586429 1250 168585179 168585181
    0xd1a150f03150609070309060f0203070f020c09160e040f05012105061902090d06053909180a090308060f0d02101101060806010317030c041e0519090c020c0603040605 73
    0x201200076151f0780300d000b000241420440e10400c2d00c0c13600911b07c82c0c080c0b603403110801e0304268412655548805006500416048049007201d2100c8403d2402c41f14181083c180300d4202c08081822145006013000d40c0664640045c02b82c1f04c9481004404500c1140064025150f00c1d00d44540310300000d0f11107980145c11201d1020b44450035015a042c58500620303a4540d2035560404401074041280c071b6a0580e07100300b82940b001903184d0294500d220347d905000c0d050341d45280e4040b0260340300303005056100d142d0898900f18103200f800313858031450f07040001007100e00c1240b43c00b902203480600343e10710505034001480c11030f403501c504100040350101e444860a00e41d0413411f0304d03050021100300106500f040c402180b007030b400280d07090480744558904d0320303200110781a080440c0426200003610700310400c010401c0c18103d0b13145018002049290541c003a42c0e034400a000803819400d0b20b14540c550410400510045100b0461a40c80c1800034005011101c1e0002e01d00c1c1c403000b00000d04440da648 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168587679 1250 168586429 168586441
    0x103020d090f0606060e0103020c150603070e1e010f030308070c03111204030b0903040f0b0c1606020109031808101d060915070306050f0d1a150f03150609 68
    0x41c20118415030080c4811508250504004002d80b58901450380411900242981a5446842100c4a811010b00602100d14400556052a210107061154181b24030384020510007906107145000341c000f14111110b840c01c401d42e070762820005074003c0e00030051000041011035080341d1159880030007460105580351039480e050f520500c0342d68660956204000c08640068851001001038a0290f2140300c241c0e40c0380700c986984c034411406800c00050b031044080101c1c4100c54041d1245160a84c15034648000301d44110389080150740c42040143e44031213982046c180c000c10b140c2c41e019944000c4882c2281081e1b1940e640f100d0030720801a115540701e400034440801d17134a04c4c86004100c8d105458103030400c0c171401959541c03401107500041c12034a0104500c2406440b03400e0450314040d000c4016084103404008030b2110400c4261038403000407012880d180c050040180c81540c814450420768000ba0f0240081c2005803c60785000b6031000001134031180c141148940d000e88100c4018000755590 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168588929 1250 168587679 168587681
    0x902030703200409050114030a0b090c0303280c200d0204050a0213080a020a0e0c190210060905010b0405040209060c06010f0e15131d0f0106061403090304050103020d 73
    0x604007002c0400410311030741d150010081040380d0f541c00092020780d890b42d5507540c00c0202e02c1c0c45564103070b01002403000003c071680c018550013003240068542554241e00480d0840d0300480c10800b1080e0380391950383d00b40039010140801501186005001da0615035031f40500101420712448035040183d411603020381e2158440c98030760b58058014800b50030030903e01c00103904013258000c0e8200a0620109404400003107451015400400c80320109103400c07411604c15101400c07400c14000100f04501c0d000650740d40081c102d280503401001004921074090b0225003c9401440c1540d0800c401041001c18150035a01941c01c2158010b03034844d4100c00046031446101030b4207046c0d00414000207419840d039a40082180c0302d031203081800d90788076540112114031444003994042015101c0180001c0c0c0c50703000380c1690078040104004158402d040074036151000c07150780c1c10b6a45891050100300c0d8019052210b02c03080030682030550501c913101070b449001c2c0d802600d04041c0e012071304003105022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168590179 1250 168588929 168588941
    0x318030c06150f0e01090e0a050d21090506012105070b030a0608060a090203010b0108070c0314090d05010e010621080a021009050d020c090c0922020a050403050c010c0b010902030703 80
    0x49525102290b55652849000c0080034031510000344d20b1b0182ca44440703c404a623120b0490b40c042e0244c05500c0c101801a1107510940640c84075201c0c080000568000c400c3c8900e0140324060340082c200356140c2554622440c0e08000803140d079024401c200701c00a00002884000e50754481122601e981d01c002201d80104060b41c8210311a01c502c00920038650a40c0d8410302c0c07024000d038001c5c0502000100151140364050313a040b0000703901d600010001c288250b00382100790240007041441e10150340006100c41c0100701c0d00342d4460350744070b206801c1401d0900c51a40107003401810208440c5581d25042e92158030880043c200c030354002142d01c10035100f07110042e600d9005d09002c00c40d032a518206980d0b00c0b80c24041070070140c42032090480c00f82c03130900c010f184070360b07040700d074a61030311030440c01b440000030381350039400d42d06100d4841511041d101800a0700c150303009966590389451443c00d04034940600d800126060080c5d9520780400300b000722802905540c0ca1041c0565661100d6004400900c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168591429 1250 168590179 168590189
    0xf030c12010e0717040b0708040212030d0b0109090b010e1201060e0103031101150f0501030c0c02090a051f0b0703031a03070801020409110327031c06060318030c0615 73
    0x91420012652201d10aa41405030a43e6511003c40c01da08a18890380078005450140c204250b0130009042648a5400e2545c042d1001c2c0c090700020f5621101546540c20440c101c015060301d44c0c2c114511035030700041103401445012000c3c440522088000303001030f05001441d038010a11448500905402500b08900800c1e00c1201b013143da681d07900300240b0803031000e104451a5420720200344184895405c2d49015207946c48001f89000745404019001000d1489008083c4480041c1850259892001c4144118442e001c082694944403075006611048a18030362440c90301000180884c1c005a820380c1c0045605040008180440c0ca8014008483d01d9005951610900f030011902d00b6064000d0801c41d14100703810300101c5902066205a40000c1700c011030f20404d4116402d0802580307800d00d0000c1c400ea00d060300c1c41d01c0c010082154605014428140032036490b141c0400c41c0c16418803d003035100401d072283d000c10000c0380d070b4028004502c0010140c00e40380c40302c03072250040b80c03042d6070b482c010301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168592679 1250 168591429 168591457
    0x90f0f020105041d01150e150c0f01061701140906040b0606040506161407030314070c051003090c05100507060f0e030705061b03010f0b0f0405060705030c0d140f030c 73
    0x4551309011607280c0303000d0140d43c1d40c00049251070b101c024003940c142404000f008085c04840090b004c40031010750450b1801841c0e40c0702e192950040003800f84034082c017a2030150503604c4c129103060920b5017500c8405150000841c02e05040043e45400801d103190000d910812090241d20780d100003c88034062504850f40c801c200281e40d40704140c0804221000a21030b808113100c040b845003039140c4070344140c0300140c0407980e410a008580e000010007840400e208108030340d0b0079034440d0302007524840d406401c0000b20356118038803002d005441000700000c0c641122810058507403218018024018014020b00c52911000c1264181505801c050014210701080301d8907a0714905042c4c0da100d81c15958244c410b40061150f050020081040300d050b250060781c0d040a25180c00325030034641d030006582d189003c00a210101d071039540c0500800445009400550311810309004241c05c2441d54041a0140514410410740382480c801c1910004000c10361015143ea56145914403544941d0b244002d4007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168593929 1250 168592679 168592709
    0x20607060e010203060906100e060c01090b0103050706120204180e120310030c0f060c08070309030b01030305040320010f050c0a06050405030a1205070e09090f0a03051804090f0f02010504 82
    0x11072015805107104141c21142e64045450300341c2446541002e44145e000014024111181c003800c01c00001c001e038030a2940000358080003525107080c14002a04200c66039040841c2c100005940012400d84860600008515140c0b400840088600841c00402540c64990b1507031450910240644200340b040001c21503170360f160503562418000c009000480e202100800041007451044a00b6000c0e01d0454480d8584c800190704c4280b407907000013a04404004028502000080300300039030600a43c0300c0d84607e0b45460841c0340c150345c598100021507444030840c0d00244410780c1c2c00000c4820100311400e0081c4ea0761141d4031990309002c99800041c0c0900d09001c180320400034004014007400700300d50788001100c00c10034016000c5e10000d44220b00054030f0501c0d40c81e401d02d030450b811a0811110007c0314004035404800c2401c240040704141d000ca1b07000314196035691076000c0000584801110200502c80380c0d660b41c40d4240d071041c1c5c0c01404140c07020041c001164007810456015045002070369880c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168595179 1250 168593929 168593951
    0x10507091701050603030706090f1e020103050106180302041a03190614010612020a09050d030906090807030b18011104080c0112090206030403030b0402090d050f0d08010303170402060706 82
    0xc40d4891160080c410100800303041c1010301031140307a0107044000c014515003001d680390f803000b8001d00c0741c05442038441041182c000801200108a88a883c2002d5450704540d9000260459205920810900c030154241c01c2d074505d042c0d03444106403641100c00249034078280d000300554a00c0041340580520660086008440c0c0200048240c5403207030324180290f881c21521025010020301c150008108501080100249140c003d031140030314030304d4018816503640d000188000400d800581c04101d41c4102404840da01c03100110280a801c03006103001c41c07540d581e200703400c10010020a6135041a02c2c040b8038080d000c0d0403ca41d1071019984003500c50381c0b20b0343c48548540c0201c0e05c031b40c0420b12a405943c1d0b07074030807401040341e03090b0010410b60459a0303d407800d801520b401610983d016600308194400c9946186ca07282100380a030004180030042442c50780d144c0000480c8010034000c41c0c0c401000060780c00241400b00c4c03075454000c00341075180d910100b18640181000280201d00384010205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168596429 1250 168595179 168595187
    0xc0111101406131808090f040f0902030c0a0506090105130b0307020d1704080d0207060f020301090b01030e0312061210050a0516090302060306100c0218040201021014040b18010507 79
    0x2028050482e0f900c0c01c0d080a04001004441c540d00e1031107010401038440340041100b400181c002100094000768080c80d101d00080c0803900030140000d00a41e49601c81c40a50a0400c840154104140c900340c0341c850802c80001d03030324040d02030304504205002072000c90703030f03541c1d280e5040080054129a0380c503030030a404044d44810f0514120000034002007a40340e1801c100144c500d0007541c025082c146007040c2c10b018600658070081c420345071551200040c690502491001b1402044081c000040040e0044001016220401c0c0103400700da205010b200c071072a2a034904150041811601e001e4200a003214032410544440100740b04140703030104100e5046001d8100500c501460169910038010580b419584460303a40006508a0018000104c403810040f004501d281b4150034922200892a40000c481c500001030601c0c485003d0420b1004658041040c001e0081d00c00d601485201c1c5005122645500f00030070281894081202180d41004000c00011203000c11038024000c2e460f01070b0003c0c2c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168597679 1250 168596429 168596431
    0x30408010b03150c04030305280504081203150904053a1b0b090f0a05010606080609040b130204090501090f021c05061b1308010c0909020c0c01111014 66
    0x80c1c060b0140f154090300500503442000d200b40c58206150b4249421520100c940d44c1141d541c0c5543c04007a014100c0300d0398006409800c4281003941c0300c0780e4550a10380340c02e0821189818501080c1340520520400085840c656058413a050f102602a03030355904000b890500d104d4031b802c100e03407101c4452901c0918566645161003a1051b1140001c2aa00342c04403481c45258140c03480181d4500c584100242e01034a45036000003501084030300240e81500c080d401c10511074000c43c0c05a41d0f8590070001c039a045444e0ba507100c2c0c0103c0762a00940342503115029081c4000307040000032120007c03280215030301d035480402c100d03801c140200b212803000c3c40c24081c10340e200081a403091440c4054030404d05015500445050f03031140c0604440c0e114408d2a420b0a540d10031021181c50051181e54003c40403200c0341e900800f0000300106526403c234101070018401c07a0000c50945004210700d005090740015100e002c04028030f080c0400c140349411440c1820941c7c03000803066424440d13003980070700c101310100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168598929 1250 168597679 168597701
    0x4140309101106060f090402092502031e03010f03030804030c0c0e04060e0609070905090c030607120c0309020609010807121118090708010303112503060e0a030e0402090402090303040801 82
    0x1980c0d203407107140400410514174617030b060744a104100000d00500304412219000030720b500c10813002500400c00e51015445103540880140d0012540d20003269044a00d140400401458207255506181c162820400c81d404050309200007e404074007054401c1420320303000c1d03030070203080320b006921416407a400b04025903003915211b06110916484240104000740038590800080c100c0619201090b0094400140980c00b107005080440b00c40e82c90030301503e031140380c1380d6441e00b002c00303030f80301d844000c40710b0011620b0201450311401e40c005880f264101c0f140170b031003424004d0203996220300c225149082c00c2d042d1740c00f4908201d885001108880041c040e00c20700391507016003e040103418006003c804542c0f200010340000010000f00303024480440002d00004140c030801d400d420440c02403644084c0401a8001070b1070381c100b06004041c450292940031007405400071850a0f00c0045c00300036203410380e51040d9800034180750300d65165412182d070064044c041e81e880382c0e80c442400d8020440d481d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168600179 1250 168598929 168598933
    0xf0b090102150c03061908030304110108070206040f060b0d020d1b060c0c060f110105090a0c0b071106090103020702040906021b070f03060b0f090f01080d02030c06041403091011 78
    0x701034a00b030b44005403a1062003108042401d6690f0300c070404c405030508152008405a4401001c180d852051000b184110f004483c03040d417020701400010410701006210208541201042c040005e2401c1b210300300b82600f040001c6109091000003a04459502c00d00941c04641440c0741010048140c0000103520388600100700104d030ba82c0429201c203206600000c0615401c0603061082e18000d060465070141c01d0b03d4002041c8104101c0b4500f10b680c01d0b43c00c43c100381e04c00c051100810540514110281c03007c04030041c14020a03030345052280d200e00141038800c0b0404282c1400d544d210703605540d22950010818004160303541041c0009500008461020401412108200510018071901140d80d82c200030760300b003851511090000d121089200d98000328220b282e04490341e038040d006004881c06071500d44503514000b009850800580c600c4402e64000f07115174404403102107007555025400902e108180030001c10b00314110300c40c10803169032200342c03501a107190316401b120407918105a001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168601429 1250 168600179 168600193
    0x120506060f07020907050f0414040c0f02030304020918120301090f0204080a03030f0204090614010305102d0801020c07060e011704020f04060509010b1c060312080c040f0b090102 78
    0x1031009038403581c01224600542000400014244052101d900c44000e2410358100940342c1c414581d59400f5078803a0032600002460020503144c0340c4100040a00c1900f0404410520844041c5d102d01006201a00c1303401d4000008034980c04501144d22803603012020f6071420000e8101054254000303000364144503262102d90131500b00135101f01d8007580e680c1e2000300110042a60110b020b08040180e1a0003281c090000060000460040901402e40880032106643c1d034000018101e51000307050505080b03914204008032420110703040c43d8125443c07a1005d240401c2200a00902100d51295213658400039403240e44042c0426010250f0302c0383d81d21404182d4042c001103030150b034800b5241d500c7d0f2885001140c0180f40c91035400c41d4040000e04003081d081c0d41c80d4000f5003a00801da0001000020004218900c2d1500319007140604489040810034241552281c4150310342e054101e4003841100404201c0c070010a2054a00902c0e0f01c03402c02c11150703101e046c01d142c0b94114102c080d01600c40d00c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168602679 1250 168601429 168601441
    0x1e07090b030604020a0e0a0905030d0b100c0c0530010606080a0c02030f09011701030b01051212040e1e0709170d0e040b01050c0703061d1903050d0e030304031205 71
    0x21548901842e002005d5248403400c1491301800070310064a040c101c20303a2085c070000010018000380498940040c400540e1058500520405500c0d0042c1002007080200e5070000082090003200161003054514221000003030040c6141040e88041d1440300c8025409030b6600c156054114409841b91503451007007903102d1143d11000e8503001040c1c0c1c40541c2050000c12129040c510183c4682c41051516130400380e14450a420b13400402e800c192203444030748006120714200a50303400b10841440008002480b024020310360140114040c161519030b8200108903000c41e03511000d04900b0b1841e10884080c182648080e03c80c00c224401c10b60049480302104103403901c04281c015040c43c140d2108a03042a0580c2004010001d001402e41440014800c07045003a50400280e03010b140300d01c80c009007401a440341d4144040c0460046030780365000e280a80c0e070818a050301c50b114541c0c235040190300c4044080311403018102c24009170032644404410401499400085031071b02c0c852072481040141c840b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168603929 1250 168602679 168602683
    0xf0207110d080306151c0615020304080307020f0d020319050d0507031e1e02100b0607080417010b090906150406080309090c040801020c070f140913051e07090b03 71
    0x100040d101c6070080c00044c200b428040700c00088041d0b00f90105103808904462085000c1041e5000c80d111541c4410600c06022651500c0041e0800343c0007c6040c1840c0c04411a640e20070107000900801c40b8158803007458407001d121060b42640103060300d80d890030650b0032200ca6644010143c82510445000600b82401501118041d6815995030b20210042812600f0194611024181080030304480c3e907034181c490380703c005203011841e80070704860842ba06c000c0c4107840402095512943d0100428000a250441218101c0701e036041542840040030449a004002c210041c9800c40b41c10070801843c8c100100340103226070500e02e40101d1f2a0b4190060004403400c4e8054445154810440805289001307404a648282608466442c0a4440342d0090998100c651b0340345440c0d10851040c008402104c0d100406040d5106a4401392079aa400149114401070040141151044400010b010043c005204a000e03520420030303075941014000e2340e48441c10321948070014501f0710690414540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168605179 1250 168603929 168603949
    0x1106160b1005012627010b0f06040b12040501090c0303050703080906010b031b0403050f06010503150907060c11180a060602030f0f0a0c150203010303080a1506110c040f020711 77
    0x45081c0c080152568540d401c100c290713000d0070400020214010410f42d020f500d030902d00b824500c000000c203554200c0360600c0204400e596065200c0c041c00d12007444104941c50a42d1803218010b21029200d469500348140141484a00a08400610800070050503002002050072038441d9462f00903903503528500b00e841c1c40007030048a02c0660104007003100b5406080e4001103150025607038034035199807582c0e00c07032030070340d190703400401c00d070401030041049190511140d0b50340c22002c041c80718140760007099107454001e54010300c0c060080004100080c8543c01c43d056100d404050007603601200c0d00c030300400d0000c40443d40300100e14140302010035003510200507100d401e60704103402400c007a68049440c0c00c0d5080301c60138008210300b542c505004202ca20b8500401c041d403110005941e941141170003843c64a0090071100040e090800015400300080c60400484041d440c1000c2d004a90310302490034a40c0303642c1c40d144e000e0b0078900403002c02d09581e8024480e10744507070300d690828480c1d80180483c2d420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168606429 1250 168605179 168605207
    0x60a14031011040504020301151b0b060907030204030602030703091101230f0705030403291e0c090a03030e040b0904020a032010050a0206060108060303071106160b100501 75
    0x1600c810314890040c0d00b000d428299240403440c281900c40d00854101e030002d074040e6076100440f4810705001074000314520160181100d803140d0008203034840090001020f882c5c103014130314010004e600f40d41300750b060350b02440d803000302550b03030307040440000700a08a44541a99003000780c42940c0d0340740d80a4000505481c00284a128010303030414003041160304a502581c2050030104080320004400b07000900285102d09540c50958a0302506440d8049016694036600160802440008244140c13060250a1784080700d05456980800240040c080c1c6000150400d0096034084109504020385075140c0c00259010080c114035102000050134058401030741010a41c3c10610128101201007074140c80443c510341d503442c4219000c0350300c0014082a583c001000844c404411550621506030040c80902e400b10090030702c0300000341c49104040004200c2d0140400854164a0320815950a6456013603e014011614140b5225600086440c07061b0454030300800310710f66005000b000c0100e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168607679 1250 168606429 168606433
    0x1e04050d0f023c0312010e01090c120e0a020301051602010f05010609050d03020f030a08090c0a060203030a020702190b0a1202040b0409090501022b0605181b0c03070b060a1403 77
    0x1030804030440e603c0c9080488201e0074406204501076404000a2110140500e01602a036141c140b1a0b00740d0901a00144016410841981000c5d42c1c40920901c3c0407a007980009401c000c407108461070042225402901035081008100c54060350381c60b081c902c601b19030000c0c4641d0b004800000100d80b024040e800209404400500941c02e040340c1d1a440c051090045604020701d040180e45907030810780094001841141c10030021030810f1061942d115016902c0c995242c0c1443c80c040d40303a001c01003071281c1142c2d010444105560312881d0503143c0030301ba918010070f42034844040ba0f107223074409100d010103c0c0d4802916800b80d100f82c405c40d01103815420310181014100100f0b80d0142401c4107042d2815902804010203c404410452446000c044900080302103210380100581c0c2080c2d0000780301da01120400103a0081d02100c490307001158401090744440f44203240c034817501403034940c01c400e0b1002041038000c00c105840214060501103c0461140d55101800c200341408801c901e5096 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168608929 1250 168607679 168607723
    0x608100b18060102160b0d060b03060307030b0603010207060f1a09070f1d030313050a09020a1706030312100306050c1614010b0d050102030f07030e030a081e04050d0f02 74
    0x3001404000c1c0e80280c81403042e181600320071407683c00d0700760140e040551a80c40002c2c10f2001c04016204950062000e03ea08505504e0088000b1340c68400502c00a00070301c8120001071800d580079412606156802582003060340c19954180d0010b14030056070a040301c0c03005004810624003604441d1040c0c550f40e40c1c1c010b05141d261422200244a00300d2002211a1001031104941e0180003411443ca0555500c3c4004c6107428104000c980550307000d074207801d1040203000d044070b501008504481e41c00380003003090380d1a001c1c00f0910714030440000e903448500640c00d0052001020400c001106d01900041c007141c0c03500d00c0b150707006100300001c11100d00710368020b00001846140d0168400030040300009240c0200301c01103030b0b80c503440d500111100d9500008102007060310b069440c0e000a014501000b00c5160005055070f20710a107203039401480301d2540011902c440b080e146034142450004100e003e07051915246070f0350300000741c9900c04180c40c0154501090b2000440b840302c034a003c1c50b00e5242c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168610179 1250 168608929 168608959
    0xe0d0e01030605090108030901030501061e0c05070801150807050303041212090b030709061103030c040501050309030904060f090b1206070c050c120f0f010209090a0b040f0507030608100b 82
    0x81109120005040c10780381c0000045660390354015034000d01240b40a165522031070341c001070485005070006014070451440800300d0700c8203090034615519035420858a85035a50500130314004007940401195070030708a5119941080d60001012200040c00722480152100c0070035480c1c2c0154001c01c49155010143c003c08101c040321000105005820142c90f0703140c80f0603c05485034400c441900200d04810001c2100720f07070001c08803800a142c0302c00303181541440310030007403144104c0c42000d042180103c00b046001c042031044482d034910091042242070f41d1051a10004a414031603580c1c01c40c41c01e4010002c9080000561443da01f05001034813140c1c2d00c526043d940b049a242050b1040d11500700b0b0007176142c4607112840012005000141840105002d145161040700740071003295034010b00040c200340e1502c101c07003038000381c0e02e09002c15103d440001150040c55a51070301c1c80040d041c07401b4842c90710740543c06807013641c18400a403841c035640e240c0c40c070055491624070540c005c072843e215000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168611429 1250 168610179 168610187
    0x60305030d11120403050a120b15030705040f030c0e0105010e0a03060e0a080310080d0c21030b040f0504020a1e050607110901140a09050c090d030932040e0d 69
    0x62110b2540c0005400d00d030b00701e09940070000c0126404c41c08203070f0000701d4241a9070401080c01c0b1050811f40107000400000c008154070380c030150f0760030211907400b00100300414001c50949002e00034403602203540030f80d0703810100c40c85095840303241c001400b843e00104055103d0001c820200c5d00241050310031900e140d80302030050440d20840c50050103010b1841c00040c40500055000700b0390421103040c09800c0c00185824400b00400440510a111f0381d0400001d440109050711070714041c40c04400c0b000038483c180c0250001c8454250700616000a14003943c019074092405a4000e0312110001910b65048040d4600c4158201c441d41240305801c10a91400354000c000180c03140081100c150103110110303003003020a0b005144041c00c041280e80c040e05050b0b006200030003d030311040c0000e083c104200d901612808030346030300980c0085c0c8104149801002124000d01c50310940c400c0c000c030705003407448214180d60032440c1c9503455103c81b086645030078090800d818203071402a100150009006079 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168612679 1250 168611429 168611441
    0x90c1e061b030c071806050d02011b020406120b0a05070e03100203040f0b0f071707050412030e130209010201060b0a090b03070c17070213090b011406040f09060f0603060305030d 78
    0x100910003040f01524081c002d124007001002072114041207507000c80501c0040e0340d90398006a00401918004501507a07001c2645060341110f02c0381c42200003998008a409030030140c00603120707003541c48802c0c070800c00164500e40c802d4000c0ca404002e030381c5507601c00300c5844e00b0180350340f64158815030380914180959801540c0052088800034008103481d583c801d15100200c50304131003c0100340410220399041a01c1648504152003181741c1858500c2000c1c0043c02a4050700b0f54010f440c500c0c0d00304243c001c0c0303584107152900801d075010a80e41208104046e41c000e2940c1c41c0103509000001800c83c0f0800142c0c1c031250780355190329114a042104901c46600000d21741d00401410983e500c02041241d404a00c007000c10100883e9940418018003942e0102c4441d8070400c107140c04104004222540304a0341920811409100c4500e0004000349070b50241d90000803e84000c0c143c0091142d0322684280111008108180191b965804003a011034015200240040c0c201700a035035a80b04c038581c848 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168613929 1250 168612679 168612727
    0xf0c0309170f0706020c030d020309060f0a11010905011a030a02030a0305090307031a0114010c0b0f07030e010203090106080c010203040b0301050616080a030b0f040b150f12090c1e06 80
    0x66040b016078800c1549040002e5114201580111640310320342d0070288078246d141807840c001540b400030804d0104046100e044141445940b011604070701c41442200100c170301c2d0b5410f10081c8814440c0c0e00f4110b00a10301405100710350100008020114280030030b040e20442d40042c083d000c90360302500c003502c255000d61a1180e160003803a0010000540106003900c180c113500e00411460341c1014203000705080c491440d2070601c81d2094425001441d40741c40e00e688040400b001500e1510380c0341c3c0c150b02800e000000c401c1341c3e500203c100866002d055000b102100c106500b103035034080700c03c40107903120f00c0b9a009015550800b04010311030741c1051402000c0c48180d28500030084121783e00e91104c0394002e0b03040702c00007a0725180503508514004148a00d03000702110100000840d4800107000303414500d002103406100480c02c1508100703a00291110003442441c0070b07000e4075140e40400d03204d40315604550700c56a541358045c0003e1020442403000c02402130429031920042c81e420520001c454403107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168615179 1250 168613929 168613933
    0x1120906090f030203040e100302062b06031a0708040803010e0601050f03070509040c05040506271908060903120718090e0a020109091109060d06050402030f06010f0c030917 76
    0x10400000d00b207000d2100540d0280c0d003d981c641d0b0501c4950703070883d1070240030400d18144c521014805603442204556000e0740036001c41c6000c00c81c0001c0c03441800300f9502e01c0d03a010f6140810010500c130202d12040c0301b00060440f0200d05589025050703805020079207000d02159801e0005200c4220030641a6400c650141805410242e03112039821050740202d420300005000401d0107101402c0c580296801810351f41019400c1606006c045011070041552426040801c07030b00c00113118550210b45019060060a501440200365030a108144102e1207040c9040c460407002804444001c8161000d2160b10407503060181c580c103404940c00a0304290f60500d01c0242000025005100d200740007070300103074001034680426680005010300410f5440300c08001d0800d209803000c07250036030440e48000801ca501039180d41c95540360307070018140c03078205981051000050103501c660142a81c2e105a03001d9840326807004400340100da800c90450360040108028210622029400100c00d0620350b1011003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168616429 1250 168615179 168615191
    0x709150507050327030c1f0924140304050a02040e0f060723070506010b07080c01050a06090513020a0306020c0f0a080703020d110709110d1a040509070501120906 71
    0x110181158418402130f008004040380c0c0b0303004a007a0100711158010102c0240540e4039102c2c0c04545c0c0d02c071080595411051f029414418218043c0801d1005041d038401c000f84115900c5250014500007101c003031001c80c0a03012140500880041140d01c604d83c000080c0c14102e8281e801e02001d01041c1e07000c000d9a000d41810304401110820400303219541a0b5221840014603106000c2c00507148080002d42c01d000700000d00102c0c60019840d070440381246051595103205043c0090385003d0181d0590055080005011b50b102064200206542d00c410703042045071650b01c0b1202d000c1c819850000c0d000241e02030100042038441c0c0c06809000e201000360380c1785400705030441c1e04003104214100c074018408a0103400f070550420038914041520f041100e010748003000042c1d510483c500c2444803050f20b80d0240c030040c100c3c0000740c5e003082510b41c4081c454960141c05890030091891007007802a45040e0000d5144107000940364110b48043e1540d0b0f40403686519800042e140502d010340795140c0fa00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168617679 1250 168616429 168616433
    0x1b05041e0b0c01050115020a020306160c08040e0106030b011b020f040b0d08041a0421020301140a2301060917070b0c0609060901061a0307030605030d0302120606030709150507 77
    0x20044a0b05200c00003401d503040c52081c00042034942074810031035200309900c00041c1c5000030f110b40c000c092840c00f0034540415031000c44403070521480c002c181d4040030500040090075002c00a0586584d134070240b0000490354011190110b6060000e03c0542d0070b600404050b00b07000d0300c0d0060800c0302030008540701c244103020690700409004101c880d100002010442c81009409441700184801c0305103203803e02c0c294803c1d01800d2440d12202001524808540466030254080d01c80c2402c1481000302911f4444030400c020400001c4952118500454146801c8401107485050390305030303125081d034181040e000303000d901001c40c001d1201d40700701803011888220800117814403404980081c0180d141880c5d805050400240441d403284c0c2c10300b0414010882c034409041c4074110754413030081d102e40d201d0760100e01401c142e500c10b0780c040c0103c00c041d4178140d505030005c000d2500048040403054451200b40240f51004542a8000071000c020030701526070b605007024001c2031145881400d0105903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168618929 1250 168617679 168617699
    0x7050411070303050604050c04030212010b1c03110703081b0a150914070302030c010f02012d060e090a02010c0302071805060907030504031421040b09011b05041e 71
    0x40c0302030085200200d548030805505000b5951700c01d07000d80e820f100c1c40c04c0005034600d4900941c0402886080f4039548049003110941c0002a40300001b806405c141e480c0d100894024810f10074141e00113103200c0038014444100085040860740d2200f5110300d01170508802106107030f02c1c0c00d03c9003c140200c0c64120041128505024101d00b8950300004640781c40d860030881c2070424550384010303604001006c00241c0e5020407410890310088c01d10780070404220304101e0050111000000c00c0e0740018903400c40f21200c0b0100c84103c1c2050001c20408180c540070204000142200c1c40d021070b03844003030314074015446011074056140c868011a450540c40d001c000b150110003106031808030b43c1d1581040120700d8140d00007504251a820100824101910020890b80202011700000040040c807030b65041254100f9500e44010b00c17500d844241080e14103001c518030b01743c50001996080400c00b0321070f03910500c24101e40d07412584034580303010b140011441d1001309400c80101d082c5804000082e020240c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168620179 1250 168618929 168618941
    0x90a02031c0e031f090303110a0e0111030711060d020705070e0a0c0504050f04090203161d07020d090e09030d05010602010209010201050912040e0c0403020402120403081620070504 79
    0x1003041c1d03030074400d1050700004090358088640903119910241c02d0130703408002d040365015042c510400c08038411509090503806007505022040c040040003039038040040d0b110403a5030061800b66500b4a21f041c030200402d40e00c0c080c2e10310251081c4551020709546103040d8000b0032003c40d01200250a2a400345c80d00740c02d00d052a40090f52101ca440304102d80741855114503c3d401d119814a581418100004282c282d69180141406036036522050703c00c2d568100481c0c00e101522204d1400001d85420803031a1120096a003103418aa052010480283c0082007104203c61349580700c0500c0345c941a40c0400d5010040c25041c41e03400104280148d000c560b002e8140a042e26030009070740c1e0f0070000002400c5a500801d60036054010108042128038844100c2d8211420714041440702e4580a001c400c10340306941c4002e500c00e100040300c0c14400000b6042603c41c50094030b4010380c594405800780124010b132070120001034041d0284443c40400f0300d501d4640c0150020445403016121030204c0c0031542 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168621429 1250 168620179 168620203
    0x106020a0b07020d0503060405070e0301050109060f0503030a050f0703030b09040b16090605090f03030d0213031403030403080c0703031b18080c0a05010c030c060f05011802070b0103030305090a0203 87
    0x32541444003031040701c4900e550030800c1880180304041d0b1015000b40b0034003000d007900b88119203071740100d0500c5200f03007120512038074000d00030011035a49460200c000d10385031165851501444500007100d107004000e40340652142d4039013502e00b140442000419500040046080c0b594503840141252565000d007031099100360402c0c01e1504000304c1100d18040f40704164070403c50492000c2c882c1d1540803007664011542500c4000c01d600281c80082e0841c003400d45600070407840400c8016403010012041070849000342e4840d0541c41801603442d490307100c22134001c0d0200303a01da0041030b80c400c5404c004000b007501078500000d540310540c441840740d40c40c000082c000900c000d40f0a03005800500c0303c00d0020a9098020030004000c2c20205242c1e0101c4c0c031502d4188210b800004042c180074142c50300d07440c5e42c4007c0400260403c0d50b940d00040c4070a02450032810140312040300c08800c6403088030b12158011022014030380c030355907003100a00402800354009001e55240740005132000c1010305c031313111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168622679 1250 168621429 168621433
    0x3050301051c05070b0f04031a01061704110108060d0b0702010905190f08030a060f03030203180d0803060d0204020c0d0509040b010c02060403060f02070f06201e030406090506010602 80
    0x545004200000305180080d442c1a0791000c03420304000034070004d02c0c0c504071118802c0c0c0c282c4500c003034007140c035060090741d001600054040e070741441c1c511764612010713050754240e849180e840c04040d4007006c3d6082044a00600c011915010500b066008401c42c81d8400801028080c4281180da41e070050004140d070300802503911443d02c2c90070084103200340200890420501070035040180c45148a40e41c3c0207102511440c0000085100c0c45115003108015020000540c6880e6689180082d540e60201030420303020502404040414a01782c000003554a4001d03a810f81161505002c100b00c02e079401500301c1e44242c2c00c001c915412902440a00a030000f161941515031103502c05020075103200c4907009041015460f8040c0050355000196000d49800203000120318142c0c40210009105100014241241c2c9540e141c0801c08540c00c81220307503812150b141d20f0346030082c014001a0084042914103980c1d00445468101052006545c0c4940541404604200640c884d01c1c00c1c45020b130007050042e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168623929 1250 168622679 168622681
    0xf0a020a020a0e09100f020403020301060f06140313061d10090606050409050d0f0c02150c0c0a0f1203021501030c0501110a020a14031e03090a091a090c0c0109030503 73
    0x907240c02000c0c900144000940340906250510040340c4500159541417801e6503521201daa0071001607050760301460340035008000780354035601c83d0101100c1c51701c1171600007070b801d18441083d0001407042d83d000741d040c0c2e0740103009a0704955900d03018054110b0b02003880241d03c4104200b5900400040101050001c00000c1d0413685050650582d030158100c0350096052059010001f40b000078500030290705441d10010090410030201e840c1d00c403a00c0c010358828505550f41d91640c801c1c500401010600e1011039062b035a494050100345c038600c2c41221107a087c058410407800c2c00d00800e039a0300307034880d1050345c9851884419043c0840c9086c0c2095900300c480725400e01141d60403038a010036041003030b80288004a003640c0060642c62140c00340307a10364000294001100d44040080b0b0208404040c542c4488142003ca8285d0360b810400c200b51181c241100c0004800d03d2a10802004040a02c0001a1030b68800d080c0040c0c3c043c05000119040401c0000c2c1f11810710a208060405100e60303a41596 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168625179 1250 168623929 168623933
    0x819180e06190e0a0c1407110d0609061406040b090105040f020c06090c0a0803040b040b0f0903010c021b01050901200a0f0804060305060609090a200408010603150603050d030f020f0a020a 82
    0x1201c40d003242035002d000200e03010b44001c101b103078240e03582a0703804084405110b2a810201d500c08152010085c400c3c0c1c101414001005410b80000040402040030440581d9951f0204410703541e611891507004240c8000510030380c00c05402000410f101c040e002362034100880d2a4601c3c01700121056150f41d0403542c025015031401842c102d00606601c030055007041d0804081349024403039803041c880403c0002900e031036006451790646009040041c020445403d5041029460701031144120403010bd030903800709081e6018005440300c07244181d50351071703050b0f14901009643e08698001c3c030141d84904681d000001c1c040c3c0294065552180d0030050300c95142c008040c003554005010544104004c1c07081d60308984a102d2200c2d441100500017181032603819245882801181003441e141d00000100840c50b6401500703e41c007100d01c602040010000074080c1c24040300d20a00000f00780c0e8100c0d018201015100b034201d85e01070444040d00618001403554442100d610610844015812850000c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168626429 1250 168625179 168625181
    0xb091e091c050d0f14070f02070504110903070512030f0c0a170c0d0504060f050310030b010909050c030a0c260303010303031440050304030819180e06190e0a 69
    0x13900c00013118050004c2ca03509082004603290003080e00c41009044260004200d10800241c0004c01c2d0242c0204524480748035116144e07400541c456010f445944030005103070500302074520306100c001d0040c6040c04013180c02085d03150700c22140301407144182d00c04507005c240b03078040c3c0d021090901c01c4020307a41c41707210b110b55003812104a0704609100e010701082005c550018450241c1190701d28100d5661741d5410041c0ea184412608043c2201d001345001040210030345e48800c03240c9000d40211a503000f8604101543d4080e52440102202c2e0660700070040310003c1c10f4500e203d01001e03a5000c1e110511884403a2554000b40c3c01600002c1c2c41d40c426144000086e060b00381c0081c24030300340b0b030a080001155844480032081d01014900c85801c6402c01440c40405101141c0b030303015041e2a0344541c0c0b801c00c440d40b600500201c4880808903207010407003902410b0220b141c0542c0000c161204c80c40c01c1022008510020041a0042006400c4242d0080d0694070b0802410440b084060b41d4148005404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168627679 1250 168626429 168626441
    0xc03120109050106051219050a0f18021305060604031410111608030c091201050708253e12040303091412030a0f030b091e091c050d 58
    0x1140c02842e0200500c142540300c1c0c2102c00c5842a200d54890302d4641248030208001901c00780180f0528200500485a0881c0c10104000c0d4016006121601080d07811030b00f1584900702c020341c88071800701c08200140051b00303e9940100020803003401c066403502c40c00d0290900c00c1307902100d80c000e20400c1010402c54031640590a0131f01d400c0b03d0030308250b40f00f4103001c0b400718140604000c1000c400a00d00c5c0c9200000c854a8030303c09821042075010009089010b131070142c0794800070440c540c0008030043d0900c000a070100240c4d03283c2c0201000d4555080d1040d8409074011144050410718982d030303083d00303040d4019003c1803029081e04403038000381082d0f0a1080013080312007080000c000170008650f00018480544a014000008110851000805101761481d1200d80c030300002c1030f9034865582100d2a00344241d0192810300030301e4076000401034020301c00c8505a0078040040d494031001e10743c0701c203010f40c0004088121001001007902c40041c0240810003000021800511010801c0c0540509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168628929 1250 168627679 168627689
    0x40204050a020702010807121508060f090c06070f0201020106051f02010c050a27050a032102030403020901120c08010203012c040b1303050d020f0301031a07050921030c031201 77
    0x86003042d50f42d6000801c07034180503000c001044855809608804403940c4042d11464030107541e01000c59035454025100c2100300c40101e06110f1040009100c80c1001c00d038130460b44002000e0030300c3c0400e130f07659140c4e107241d02d00e009a04665a0390000700b5691280c4c242e06c5a10201c090520031100c20703a8038002c1c00c3d100302c0b041400401105010225500e500120f026005200f0a1050003001007990303441d00d11601c8a42c4490707800f448003030000003481180e64089090203141d40c06012001d111000c240e079a0f00c83d41c80700940144660004100701c080645d200d0012611a2984059081d075450b01c02d4260303042a00040d1b0a003a540c0c003c0c003000312405901c001c1d02030115444085528050700c0c0d056040c10024410401008440300703000130180b068013100e18801c0403410854440c83e40e0019811150001d01084440601001d4800100c0000285032845081260b0740c140c5030202038003c1c88001c0150100c459029003c2d220201e04000060001d80f0340240c80030700a580310600d0240d1003c945c45c0603801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168630179 1250 168628929 168628931
    0x506010906120905010f11040e010b0301030807140102071719090b250506010303035103060e03070c0f030c030219153b04180b0f040204050a 62
    0x401c206900919501602444010001481c4445003080360140c01c6a035541c6070328502c2c29150070005100c1c100078000744c0c0c0e03e048202d5490303078a0701e0810010344000c1c00003400845061051200103864400388402149501c40054204035055480070341d8100c0241c5014034112011410b1007040b44c01201202c1a003a0070b1034503846040c0703400b2850000c1d100d4400704100d018400c00213095000120b00c2c5401550703034080125020f030769480c1001401001d243c0140c6010b1032110015203110380c0c02d100811054050a8082c8040249074407100100e02d80e0a02c500300180240f01c400000f04400c1d200c0d0b07804051421000e1580c0c0c41062400950204440d0052004c02c0300c000018004560801540000d0f00c0e810b1f244450b9140c203040c44509010403680c02412a03031204580d405000380e010404803060103034001d4086000441300582e00102c440c54410b10f4000071200b842d070b101031a054121803010504001c01032070040c02c80d129082e0704881107a42d1084d0001445c244801c5090921560760300540a0303070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168631429 1250 168630179 168630197
    0xf050616030c0e1203091201020c010c0c03120c02070b0a08060a0f0317031302100c0209060906012a12080106120b0f0918071403100b031f06080d03090204050601 71
    0x200502062048244030b402100c04c418401503401003001194400310005002101220581d804036010b54840040d0080782c1d401d1a28980d5540d009820965049516880e100b603803466480c1c2d018010815420715500710310400c0781c00540340c04004000c004407401c581c0c8404e510326041090040c6e0140640c0f00c80a009510802000402d12401e400554880220765003a540e461f010b0285e15002580d40c0d0207544081c0c25514914865040105540031610030758a0361019038620080001040701103562a0224882c0ea401e05050314030005c10008440b03007010100c5600e007594440c6810710000e50000f40209203008014400c880d00094103643c482003d032400c0c0f103c0c481c4680841c20304401602164000c41065001c102903481c1003442c40d0801c000b000c22240c01c280c0d5070084130360032061140c0c039601074080c40107441c28002a41c080c00103242c9000d0020007a9007000440c02c801c100c101070081510b00c3e9501c801241c2038a040c0081e4034204100e940100300b0000d18010401100e1000c0d2a046c14408048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168632679 1250 168631429 168631451
    0x1210180c050a08150c190806030606010e09060111010e060406060e01080115060c050f0a03020303190204032604080105040b01031401020309210403020a17010e03070b0402040b04090f05061603 84
    0x40c04084528490b40c6030002c544940d03030040560300503205034044480407032411071640b40c0d214000e1fa10420045049880c10f1b00c1d900019109031200600b00c58102003000001a000e5000700108a540280d86c000041c48800d00c0590a0603e1010342d02150302e10f440b8041000003009a4240f180581075000c0208000c8070380220218035001244100018070110501580602c074041c03000c44900708241064034144000c03032400035169841103ca00e8520020804890280c8903503100740d80079658001e0203c0141e60540400c2d050080d03100000400702d4404010200c1c00d90030038054140258801c207040040c2e5411440c04030201a424800c8444903031060040200c913900008a00402c50201a1103c2c400904540300ba1254441c94001a40008061000140c00003060760070100d0800e841008210301e0001c040059142c1c4201b0001511b9051004082400761034a6481100112002000000c0301c03030305540c071030110012040c82601e56422003801c102e030343d1075607a101c101c50603100d00d42088140030308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168633929 1250 168632679 168632683
    0x30f04031101052a0607090501091a09030d08010302010e060a08040201080601270906050307060206010902091908030306011806020a030302070c050402030c1c0b010903021210180c050a08 82
    0x188000351081c0c2000031009800d9000300100c59005000b140c0900014118040409210856800c0b030342c9240304400000c3d00c003900c41c2c401141540c00580d03c400540f482c0c030742c115800c0000850094108402040b0301d4903560303800c0100984030350040e19240115803441c0009001c40c0c580080080c001c1c40c04200010f0b02990215450768425070900704680a521000b004031500195000311003121540e818442282035008940041198200102800300c1a191014140c9500a5110701000b40e4041c0005111031a40c1c0c1e00078003480200905030391000d22642400c8a000e1035640e0210226810000602045503401900000302c1c41d0040c1005440714907240009581c0d4842d600c020381055404500710301003028180340d4100400c401030044d511f03401c01070301542c03d0f50300212503c410011184540e00800c0d01a0080d8078181c070050312001d05040c950b80901000818400844a05020794542040b07108864403d920031122602120f0354002040d142841d80c01c100d980009120350701c090f81c100880240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168635179 1250 168633929 168633937
    0x2030103081207030b1207030b0903070305090607050c030d0f03050f0f070c0204020c0d050405090f061c110306010b0c0c0a080a1112030d0f06150c030f0e06030c03040b09030f 77
    0x70342c142007a62035544040460007412001c010b03c2d4040ea103140d01429080780068514140d902a00c8500c5150b1034003c183d40d40c074483c05000a01080c402d200d060f000745007900c09009410300503010745003010100d500003418240c0700e0180202080740d024481c116240d142c032a540e8403c0c0143c0389000305003815220b9206c2c10034010b00030380c2046072a40e0100c0454441d50151000b8090050844951124601001d0030030b40090241c130b8010104000040da040b144103400c6401030101a00340c582c5407080d0351804c608901e40050541d003201880c0311003001501c04025a600908095100907240e0200a0589003030980c2c3c4890144900f201940c1840044d03c04581c001c0141e607c400006414908038000c50380105002c3e12900907800045007460302c003210b50700700b01502c00219600300305041e26560280d00072110350440c18000365110b051100000c0c090f039040c1c816070070182891001e0801071400114154811a10f44103081004403d2208001c41800707403503004101040618109a0729240fa8580f42c0a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168636429 1250 168635179 168635197
    0x60f090a030914060d14062e08071713022403060f1804030f02010501060f0203030f15060c0c03010c0801031713030803150a0609081e010f060608070806040203010308 73
    0x300743e075101065a443c81e00f1603ca00484001c1409009202c600b0265030003000c4403418099409040762108424001c2c611980320041c04000c0d0003c507903943c60407901003000502a1040c02040440000c000300c1641d2514803c8580303001c0490140c0700d520520458000000340d691810320070b0011450000e540e0002e40342c0c04041624600e80c2003203000700040c2804243e02000715491700180521080c50740c0120810030404a0350000d1091340d07030320f0030100da80c0d180303a0030110f0041c0c0003400401e01e4035240000300fa0f0001d15445d100e9111000d1100001c030380d6030000121010a9014401c20b5003541000e015925400f0390034200034899600d90f40f46d0f082c040d541d035000310000c100c0c002881d4000c803010139003010285400060b100e850f4a013040303a40751012900c0c80550b100300400c643c0000d50a00c6280c85100303585844d00500581e00900c25070707072021040001c1088007552114100241c40400d442940c00401255582c480941442940079000c004040d0410703008900400c010700101b5007000842c2c220304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168637679 1250 168636429 168636449
    0x103021804020903120307080109050906100b07060e0105070215090606010f2001020403060501090b0a060519020f0a0807030906080c160206070605040b0105011d031504150905060f090a0309 83
    0x101200f00090401194151800c842c00d00881400340141d80881c26505a0f520802d00700025110305e2140743da201411503503000c11603400c3d10103018400c02c00c0c015015140c421040030450300701910300d2500f5180220b501000580c0103d405a2100b110021700d241c01c40030320000383c2024141000020032440e6400c4042c0d00b440300c858900365000d80038001890340080014000c5440301e4891900e4030150000384101c4140700c2c100303103402296240424001048407815143c250fd0052544919401801c0e80c125210550240c00000040110140700441a4034031a1603842e603160001d180c0501548210f41044040006d03000401c44000407201c01c640c0d0320130341c4582c00b1001e284103100140861042602c02050303281020144020071800030781c980d0580d0000d80301c030383c0d03814813043c803440b9203030304580e40b0951540c0180144400c1d400c01d081c0c03640c0c0040c0944e942c0606a05900b1907442038036080d0404032040d42c404070811440c0040b8141080d040b1400802501c1d40c00802d480041c1a840c1e2405681c030030b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168638929 1250 168637679 168637687
    0xf0305060901051903051b0f0414060f0f040f0506011112030105240a0201060303020105010909020f10030209061605061305030703030507020712050709140f0103031b08030112050c010302180402 85
    0x1200304c1486031008583c0001142e00154180e24074800129180c5401030190091038428401c0340740034062540903040ca01e4520145696090421940c0080e10700c80c2500556590300560458865019001d280038440e1408035039800c24034001081e64100070048030958101401044504c0c3c428000c407170440b80c04aa60412441e14200403944403c600d014001601000045000500d030701034200100304c0f03000307400801c2640c0ea0b49413602e069410100009500078240b01072400c0070b181076900404400f0080c6401828988264041000d940c80701e8140800c2d6140f100d070200401c88104843c5034000d4451b404c071505600651348440e039901410000405240c7c403500011035051080040000a00c038504254552002600380706456032418012900303a5414105183e907103c12580d80c00b4001c4511505203030443c1c0c40c64408070f42c0410a68004248542d1380c05551012440d82405036001c1c18005403a607520b0700c0385180c20b074500940621050f0604d401408220b00000c0d4a04000405003800c2d0b4015a403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168640179 1250 168638929 168638959
    0x304020a0509070c030305010b0a050406050c0312040f0c060e011d0103150603060e0f01080309060a03020906030a022701080121140313090207020a0b0904020c0a050c010f030506090105 81
    0x2110456401454002c0b22542c2005495a0701081e407207001806030700d01704001c3e6250100040c261003108411400b0640c108820000248181d00600391084108107603410000100f03044455000241d40a660041c50b0350701d01c0b014088101e0034400280500e05240868104180010306000c0242d003003282e1800b4001c0a10191343d00070b412242007600900c1808031048c0d1a014060020501c3d0b0065080c1c1039281c1e000101001ca8a001c1c150584c1c0c41140110f0400b1001d0701045400e43c4a81d88060030540c090103ca103241d1500d2000d1405105401005030301c40811135420312517040b0002100440503246100c02c0503e9800800640c15554280d5503c592038018402018610345100c0c0000d028096400765928920341c04005803081507282c0c0d012000490f40d66500d07600b6402203041c0a5070111410008000d4001c01030010820340c0c6000d080503041810f0180054140130701c0d070f6001d40707080d0000d03000c0c114190392090005040310032601b010040c0341403030380114003a10414000e840c0036161036000c0c800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 168641429 1250 168640179 168640189
    0x9030a030c060e100c0207140d060903170109021b0102090f060d11030907060806060c0d1b060c080105030c060f040b180607030e011407120e010e030d0806190602070902030402 77
    0x10042d500030115030102c807003855241c0017401d20a09080041c020399002250420080790340c040303c0e280c001e1103c10045040d4a0b440010840d2000072414001400001c40041501400c5140200680c84c0c0c0180c44a010045000f012107402c001002a644100070108007035849001c0d0340d1842d00b069541c240c440350f000d20b1600091089c00405054110041300f041858900090807500341c8242d5922070721940c40b180140400c0b40100420b00b803841d04803020513582a4491852524054031101003a120b1083e0750b110402180d401700c0b11040016030000041c000c904040040e410741200c195101407501000060b4a2424092409015504030f00000c0caa20310442e054a44050704400428069641440e0b00c0c0103480011342903071040c040b84200d411008400040e20584410303e810000c4505880c030281021650001d007400003606128524451b400c40e80c030204a2070481449548654856080c8101008400c6a01c3c0070b405024070350700d5100b440a6030780426224201d0311030910240e141e0300d8620001d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 168642679 1250 168641429 168641441
    0x90703020f31030f02040605030109030503340804030807020303060d03080a02040f0e0f011a090d05070b0408070e1008071e03020301150915050f061c1d0f010209030a030c06 76
    0xb6480300c1080d001005001071125000d02540c403c403410801d4903903510070715090392809400900890001d20000d070b10300d600c400c10000450000b00d84c4e00105001200300307903040c80e14034500304005040d07003081104040c1c002d120243c010100c0d0005508502c4e10170000344601c0300c0d10700001c007000001008142a11066010b490140c00007828008060341c441c079042e440644100c41d00790124040200004540c02c465107000b05180441069510300003400003030045200004000b181c2e00d2190107070004140310308102130406012280040e10700c0d0f900e004030b220300b004d20140a6003082d902c0d032001001a160005440303000c0300c0700e081d0312401d00c001c3c1000a218028890303002075011350924035501141200a14590140d8a5000040142c10701c2516000c801e8441030141a030031042070100c40800d40381540241043c6603040b20b418901c1c0300000341000039101c0e5011460a004c3c4d160001903079601c801e100f00d031090b040440003141000c0021001907914005441c1c0501800141c044c4c080501107580c0040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 168643929 1250 168642679 168642757
    0x3020c0709061205060c071130072303151003050703050309131b0305090c0a030506040209070f0e0f0a030f0b07090b0406080c030a060314030702090703020f 69
    0x8002c2d0300d03601c01420222081c600c0c0c3c111002e0103800e00041b07480746000f041d5840a03412030b09000c1404020f50910028880007400c6c201070807074070318280b44e99240d1941c012500004007805812154506030f41c030071900101e8041342c8038041c3da28200030800c0c7c82c0024600d018102910044c8101d46804420366500e0002d41c001800d603000b0124080305007d0000000d1034071201c142d030841c80036200c01c4030000c100c81e4100c5080313801c3ca444840300264039200390030803034120072000c00baa020780300280002000310300d0f135501c1110250801d100304401d40c030f0310b00401c80d4022010f0030304a4248500401c020040c0c0e82c124044c912074000c010404c102500c2d40d4242c0b6014503404004c21030007001c00d0801c1d044000017210380900050000754046880c01c540d1003640e0413100076456136036091b103d00280a0003900018041d241072643d17114004041004841118138508071075002d0b5982d641d1a00501034a990010943c2051500400c0f0145210080c80c003202c2051210040d4610740103202d50313030001000610311407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 168645179 1250 168643929 168643931
    0x60b041404051606080c0a0305101707030b0a050c07030804210806040b06090a030b0a152c01030b0f070c0503040620071d0c07020301021606141603020c0709 69
    0x10041000000502200e104004006800c0e00307944e01d020031540518101e0304c0e145840814003e11001300c2c0650040c81d08071103903200c0c14040c1d54491a194118403000c051008013a4081d0301c0400903c40d100b40226000710709000b003405039140c8040829018424001c5c020f0822900070300080a211070b000da240b4226910106a0454024040c5c000300140e02c19100284a1071070b0500d40e2246152190803244800c8020300303140f8401340b65480d04000d04100034054010591500e29544d0040a9038100340040c101200e07802d04056810481004241d10f094500d014402c449001031002c0b482054541d5400003000d03140d043c031303556000c400300d40800c49280c0040c00341c80040f8000c10402e410424510000c500d1070031210354424030f804070b250f84041a124202d01ca21200c00d890052211410b10781d90312408040546103800d10580c042400c907885408040401074002407a40100500350003054000d040d250a03041c01428034601c00280ea4000784800310a05a00007a5041112410b004140c020078800e10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 168646429 1250 168645179 168645181
    0xa09030812090c09010f18020d0f4104060b04060f0503100917130e090709060801020c1b01031d071d01060918020706090c080c01050c0a060b0414 64
    0x1824000c15482550030240c14003820400f5a56420304c0034080d4125095102c92048251401c1c4890030408100d400c01007401d5002c006000c0709840714002c10105245000340010a05c0c000300780e40903208208140851280b141502800c0300007424440d100d006003110186d601191a107107082c0c00100b100c08911900b181c14100009880038282a2202c115007090303003a259000001203800040b030f20b0740d4000801039003550009000000000c009040040745a03816840c01c0d5480b4002d200b601401296090196800707010240a2848076000348001000c0301c20007942000c04c080d2280303032160300702e00c003c14601003c280e21000c2a8820b03041094640c02d074140c0c0c0d15440d08c400e00c05c1901c62065008500c0004015044c91120101141c3d125049a015036111083c00e401c00745180031134004460341e05041c43c1c081c0700d40c40101d181031040301082031144100302d00c1e031840d185019040c82c4042c0d001c24140318081c0082c001c0c010010640500c2c4960201b4001002180e44c000140100b9040030424140c060001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 168647679 1250 168646429 168646447
    0xe0303070e062505010603020406060201090b01030b0c0408161505040303050d11090d05010506280e071806050c0d020706090303180b0a050d0f0501050105121801020a030606170402060702060a090308 87
    0x3600800649009072000d1110ad03031208802d07400d84582c444024044608500100003280c0701e001e443d50440542c2c04401d203456030722041c040c40c055005030b00a8003210300c0704d0704011503039039500705142c4607101c3c1c2481030400c1c0c40c0d43c40207402402000803140043e5101c0e281c01c40101c00100c21078802020041c0040e001102a0900c0360091404031503403402018404040c480b90682013203510f40c0880b400a4130001c59041400800c00c0803c081c0552042c0001001c0540201ca142c061b450090b010641d0b5690301ca02c407140026141c500000196020f54100b0300060019a030f1050012054a40600300544c040b81d0b841134050400080c1c0d03200043d002d90218120a10381e500c00020034640200d00030078030484001d4408070040795828411507000c1003080092080c2c1d42402c2c211240e111107045d01e0300c11103c104c40d608900b07990100c03d2030744c0060703074482d018402d0541091100d02083c2e285c209081440c50710b54017052203881000c034060320410001c64020b0215101d4007049000c0c590094595445007149 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 168648929 1250 168647679 168647681
    0x10e0d020f01050105090f0601050c031216121401140303041205010501051f23090301110405150301080a061d0102040b040f05030f0c12160f08010e0303070e06250501 73
    0x30a5050000b54203000000441c0c0c5840144240900068840089103448000c01907489a0026420301410b020520055160200b0440e000d0700c24040710742c1e581512007211800070400c03100c000460600502c4c0003d2100e40320342c40480e0710b041d80d00101d000ca104850380000070b40f95000e00d500c4005010740009820041010641080b8101c0d1001c5c0c5103010165507000030310350500064255003002402c0c0481ca0340c02c1e5024141c8c4251030285010380d1610702403c2d18080ba0070340e102c0b00225511518002010007a03030800300030b240e400006403031465040d5410300070307420380780c21365200040c00c51900c07180680c4031f2158103100954044903020085543d585d6800b10014103400c80d1140c2e0640501c0d5200000c0d503418085549090340300c202003e07008410844040007402004841203103060b01c184006001050311440001014100d015506180e0a143c0408142514071004075440150014801d001980707400c1800c0810441003200c01c50b46400501c45002035100360030117039500d00e40e04104058140030f01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 168650179 1250 168648929 168648943
    0x8010e01020c0610030b0402010806010905040207030c0203160e0c0306040e07181415090c0409020a020c03010e1903030207030311030c070b010501090b04030204021b0d020610061b1103010e0d02 85
    0xf541c00741d56450184c0b000c1e8004510015000b500c09900003001584a5550550301c030005062601d481134550001c101281c101442c11004a400c040c0e8070815031500708403101003060348000900d90039080003415154010042d08000d1100c002001042140d44d8542107280c0200c004021101490346d0307140002c010003410880030000528011302c3d8078541100495643c858401108205c207003811a60070310440440091082403152005d00010071058441d0009000d40c00043c0d00402108880404041c01c540c6042541e4201d5403003482140311006034070b024404095058200113840f1803050400360040d1809d0801c0c0c11040000200300016002a5005425424010405d404072684c1f41c0c80152201481c90081c0c0c00000c030180301c1080145840e4009094100114803064034414210100502d44a449820480540c220604201810f1013007550307030004003040e10f000f401000d02c4101d00c0030201c0c203102c409407ca005402e400751068030250440040c07059080c048990074a91007000941b2210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 168651429 1250 168650179 168650197
    0x15120308182d061609120b161110091403040e07081003050106030c031202010506010516080415050c0607051614010e161403070f0905100b0304050c04051f0e070908010e0102 76
    0x50b004102046e00200e400402e10103952001968019031107414549440c082ca100d051020084080e030750b15031404080c480900c140801e64404100602d8038503081d85892b0031400200d80c0350b4414030080042d03074a0b1030380c002d03002451800c6c440300507150300708014180701c0039400180031982007000010800818222060459020300c0e980500c030400000c0403400e850307094801d00e0008000b072200340b2070854840031421780703a441640c1c10351620ba41c0e0b22482d0170458582e907404020030030114480308202d2040c482c16900c043c0d545440c614003401c1d070854419800c0c0840001c1c11035a0044080d40501e0000d60044c00540d06030401c544412802802c1d07040a807586018200f00521460080011400d0008000c019100006d0f01155014200b01901e00100001040e0010707810401e1030000e2007007505001503020b240140d0241c6a81c0c50940d0911003a1a809001c28502411004100c0c2c5082c0b4803880c41d40580b4880c0f146c903182500d0306442140c2c8841141c0100ca469440d210640d81c20784415801408465 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 168652679 1250 168651429 168651437
    0x30a0503011401050c0c120307060e0c0a050904120815041a01030605010f02030d0905150901060303030b0904110d020301020405040c0809010b03030702130f15120308182d0616 77
    0x10001c01c00444d481e0040000140142e0310068803059185840f81821949007031290440742400b1140d20f034030007a20540c030020220790304000ca100c6a142021401c05021740b000b514410618240b540e40c001840b2001c900b01010040240c0106411910941c034078030045000400c1070141e4040c0e00f0000c580401c16021280c00300b1718200300010b031940584030054008200b40c01031400c280d80c140c00980509010841112540203039010701c10100509d04201d4054007661000142c80d40c154507002c1c0807207960b0100305101c1c02ca49010000040c66408070310590500a5803140001100f520205e80a405650401c42e402030034038800d00c13000c2c1e42c05454544580305150081c4864494030060644074441c11001940022814403000510520764101031410301c2c1002002411151425950b8401c03861500555098000f80c040401030590140c41c031501300c4019031301e100c0d043e04841c42c6103035203113014402d24003510005c40b010110800049c403580c0030280d403402511094605200e035039030400e24408505005c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 168653929 1250 168652679 168652709
    0x14040803031e010b180301061703030f07030b0a03030f0c06180b0c1602100908060c0c0d08010513110409050103120f02010b01020604110d061b0e010314040204090212030a050301 78
    0xc0d050152281c102d84908411505e40259004805492515a14220f4043d920b1709400036041da03000026041448500703000e10780300d040174442222000c0c0090070842c105814180c180105a54848280003203d9040c14403010007800075109a480145003440a0800c903e0a100003007451500c640d0228541c3c420150040c13a0340d0f6055500303146000381d500301c590002800c5101d01c0142003040c0c10400c25a540c0c24a45001c0b0741e60140d071442c001e011640c2080454010501c0b00c100760040104000200c1c843c01c1100040d07041902260b01415034070600e0542940701c54010503800d020000301c4001e00700419050109685a003030100d00700d0202100c3d40c0c0002d15040e04442042e1040c4102100349005902031f10b081d440d940c948083c082d0a00d50100e40c0082c8001c0e01d00c001801600c030390554420a06c241e003101c246c100501074030390420040300a0605080c1410361600705542c070109940154100d9000801c1503060011880c2da0300c00f00c0400c06c840c0b00015551140c0c3c0d401001460407115146051942 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 168655179 1250 168653929 168653971
    0x180106080a0b1804330b0f09070806151e1306080708060423070c0b06030d0c06050c040f060903050106060e130b030f032704090305191404080303 64
    0x20440d4108182c0c24030000011600144031500140c5c41030040c5d000390300d20a12800c10001d07606214605420341981d994000303401e541030108012122203004c1b1030f190102c0ca0055005407207108000d0405115560750403a6003816003145c0e043da051030320813080340141002c00903011621648400700352155054440ba00150251154403218407070600c50303503860f1b140e4031850300b403001078a0b2031044e00c0c2e894101403c01c408040c80120244c0e12520007075481c10f84201e104e05008600000203414507000790403036600c20003c5604880b4180c50700d03a11010014180d5201400c03503290b8015500000704552420700c0006480354031071a50025240118001c02c9240da840c0400d4824140e00d8200b0b6800290359042d264016045601141c658800070302510402c503226034502d81107901c44081d2418228901c2c4800500c910703802c1d010614610b0582e41085030810300d85016145010701c0001032201c1a481d00502d04051284145248240c00b07180700e0b50300c0d55210b81115459800c122290021034a0290394005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 168656429 1250 168655179 168655189
    0x60b0321090a0b040501020d0f09150c06050612030a0e0a0503031c0605040b0d02060715060902070c1706040b04031701090506100e011d0105071704051f0207050105030402180106080a0b 81
    0x421107005170001c010348c0b05003e13426145043c1d208038820030702c10280d1300040c20142c54060204003c0c20b03560340c22085642c0d031404804444015158a010307480030210000324220000c121400490300782801c0b4158410540001c05603071050b00020307014000442d030781c40c0c10017170f14000300350203039094005100d080c2e04c44017400202d641c60302c80c0560000c40701d1000405800c01c0401854401d0140448013103080612040034152810f80d88254a800d40c0041c00c0c00500c41c10401c900b01403c0e5440030101c03104110450140d0340d59001d8806440c0810850128003011f00440c186851940010140806507942e507d00c0f9004041c100c45850107401c3c20310f10f507100548500070400c05c0307440585a0f111202750100700100300c8000e400d170290600104008400200f9140c0348d401802c0000030922565640c203001c00e0200070700c2c0300380c2d950714000c03422a0441c180940118039041510400e28045441e81d40e180002441c00046c03998018481e13038010008188954080106441400251414040600d03884e003445 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 168657679 1250 168656429 168656437
    0x160803090f06090d0f17180c190302041508060f070f05090a06110c1e01090e010b030c0706140403081b040f05040c02240118060e04060b0321090a0b 65
    0x43c07059004140e10f10380080c0a4420136450903405e2500301d02090840c03c410803448000d560381e600e90b5072142041504d02d001000300d500350000581e10f002020440c0c15a88088450901000313100c0c1c0d8852604488062600407450018078a21040314043d0521040b8240f411310b080d18013400007005110f52041040c0100b04842203810040d068405e80c0b4a07012007207400c4079040100b440c8601408116103115a0740800303142401c0022601006001d242e200094a8040c40e0f84c4009500d5803c0001003240500e0803040e05c0e40482a05602a6101003610708440141105c508101100c0c0382c5130140310506602c28101482248c00003c60000f003032404084e1205400b45110b0010311042c0d0050a02650901e07420007011103000d80111104c00c25064008043e02424107642001c07482480010010a0f4200c9807000d2811101481081030b10300300208180c44060040020f03200e00d88440c034580050b18100301d1000030840709448040c0403104100010859072100303071100d2266420342004034294611404903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 168658929 1250 168657679 168657691
    0x1080702030d05040c050607140f06090a2a08030306040b0402031003030c08070512030a0b0103090c0506090d06060603090b06040527031905070524011a160803090f06 73
    0x4504042d18400380c2005404020422590103040c40d80003d02500c4060160501c0d500c5046084007480c00b44c0c610610304524045a41035030340c4914103100c2c2c20702d00400c040500300d07001203088100d6190101b4145800710005064900341c8108040090b2541010010318001c1104803414881118828100700a80c00300340c1c0c103070316860910a02000000d010345c01d03035561644204449802c000460b19594104003180006134483c40313002040158402d1a0300c074008541d10b0900302041402c4d101e0311034016a42041c041c00c0d016400c0064540100d545055151100552243c01400801d4135400000e000d0079400710100c441c4003001c2c000c1042407405004140c82003002e4102c0c00e2042e40681d412800c1000e080c81000300c54003082040c2e190641d419035410b10b4000d4580c507420b6407541c1d1490824541600300448145240b4092a4291074280c1c11402904442030700c450b000303040b2001040c40580c0d105020359411011200403a000c10468000091031282450704291481043c00711a255150542144c1c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 168660179 1250 168658929 168658933
    0xc0c010906120b0102191a09070303050a0e060c07062c091317070c030201080c030412030b060408060a150b120109023f070215040809011107060e0f01080702 69
    0x1003540080b510f58009074404005204851400e6050700780b054812089001c2926000034480407680e00154040e285030308100000010101c4070b20b5500e0003030560160304a1201082218841d1010a5a4810643e203a440c2c413a021340740f81e150b843d00050546034154020f00d0b00152509100300d400320501541480c5110b000e0020111503507101d1842d05840604a0f0880d00c5010140516000090300400f80402e24400e00c10396001604600014000400c010040592400104200700008040c003107162008542400c01203880140280040d010b801660408000ca201700c1c020802400c419400c01e031481c40d101c103580d500927600e96004404030f1191000500100020100401010354564020715500007400101840701250280d801d50070b03040e48020504d24507004059040a580c00500140c1080d528001444104009901c400150070001d1014090320741c003203100b52140c0d000b1190380105003406400e580c221a2200c0004e440c80100da10700f1784c0224900c16450a60b0f5010740e044600402d01500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 168661429 1250 168660179 168660197
    0xc090515090301020f071209240c020f040c02010b0a0501030b0105030f04021305040305090102060703020313021c0b07080a0c0203030403081f0306020417010b040615080a200c0c010906 81
    0x880901903501521080d900b42d0b60800404981007402406070031400e04c601d00100701c410b06c0c8400141308441e00d0b0028103040280c2d080040d40d40d028200c10381c1d02000d807420407100c44003e900001d0002030190075001c1d00141000d2008480c3e0394107600042e0301040484407060142d8031080110100c54540e050725000c1181000401c00081c0f64840407540684010904544041c030402400141d940945d4101d020601c081851009903805105042d4060450310b41182107103414545d03d98800400c0101074003034400582c100d41c226484140d10701c0c801740c0100001c0300d00d0038080300040448500312298100649414940003140344040b0843c0d003d2a0140c0d03c0841d903440c0e5000d041400051110b01500c550701440002000542074000380004103542140e40d503030443c03d0700001d425500030740c4849204520b440e109100030160f404c403180102e07581e45410744503995403040c076800411001801d950b24582c18a42845864040c0000f4003040c4201c0d4250382d26911602e00540e003002e0741d4082d980100d04665 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 168662679 1250 168661429 168661459
    0xf0f07140a03200a090203220213020a0e060313030f0206040c06032a0302040f050301140a0b031e030405040e150c0f090904060905010507020a0302032d0c010e010c0905 74
    0x290007002d0070221240074000300b25690000410407130340d59001880560b004020495118030002501d6001004603912450310541b6a0002d04030b0100c19400c41c0c03400d0b40c080f4481c02041d20600511040c3c1e5805004107a0328182104242400c569085049000a00440400d940f451001c1151070040d503101054098003810600194050585051100c580c0754100500322503884403100e01c0c01705070005840c0180c1c1d55041249102c0d4602c00c5403c00780c0641e041451010900a0031000b0542c0010020b4002034451259130001e070901210b410b130800c403194203030415000c0d0308010000f0421036608940c10409503050400c8540c40d510724050603180300a0210019600d082d503440103094a142c4004400d140c84a124001003602006032000d5a01a030384054440401000f4402c568200b407260008146041c01e59400950341d1007110805071001030702120b86045040100c0781104156803a0b85100d48400030903a58074000c0c01c1c810f41100880d0700f0800d480c545140a0150102502d070080c164030f507040c000d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 168663929 1250 168662679 168662693
    0x1020d0b06190f050d1d07080a08070602030a1508010606030510030222060b0c0a050c010e10030902030c040e0a0203010605040b0d03050f090d08071202070b07060504060e0f0f07140a03 81
    0x3e00070801840030400c82c8500c40c0c20b0520032440034004010785502d60010b000a80c0380360100e1a0032400007035009104000114005400380c41801c2e610038405030f43c9070b8600c60039001610443c0e6000b050712603005004584601c041d0004020381c0c026503401c00c8181c0e40c0d10301c00240340354103110182d0896844030501251101d04000015882d900d03400c0807801e6a95205120301560043c0c0184040b070300054104402c11106000c1d41d000c09100b480d085001080c0c103c0024003601042d414803040c5603555550704215102032200a04020000b44104034422280248130740340c1c1c1c4079140882c4a5481d003d4045110302e030920445042c120f01a200010309201940c00341e0752035220081c1d9103402d400030b01405244e03a5481e64080d0100303118400d9151220414544401140d000c000750500b03640015900b448901003401c250f90081e0740108000c01c6585840c1440340003031503440d4845400d8003880f1842c4100650008843d04039074151030840700c200360360b040e080310702c0e48660320351b541c0c0506009400c1000c1912 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 168665179 1250 168663929 168663947
    0x303180c170c190501020c0a152001020f03011e2402010905061f06030203070e0d1103070b130602030301030b07050304020102120a03090b090f12030717010801020d0b0619 75
    0x2662040340d000d0080d44000983c1407900b81102005400e040b9014402941c1c14031100d031841c0c600b950942041410494102170b0701d500501d80b6410418a10110410078409405880d02c00c1c45601c0215078410502802400d990f01c01d00512500700142003e11105500d4517020004131602d81c1808414101e00414621150090117203c00c111f41d08c40100c1804510140001c50003000e40c112519900400b152801902c8115944a40249441441048059604900070380b0300d449084030403121400f032905d4548604417045003119014841d405012a0325270b803410040c0350b0400420340c014070b201d9480c581242e0320b00c0240002445601000e02151603980100040c6420610500681c0c074080400740d0310017174980110101c000060340758454501401740f0707041040c0d0030519650103481e0a4503c0a07860782e650b40c0880041045c1e0400000042c000e41c8180c40c618031541c003e5100c040c403565607030011070203504150200d5400360b00d414104411482d0402c100d500310462209082e41e0300c0c3c050300c0b0076500036103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 168666429 1250 168665179 168665219
    0x6030510061410262d041a0606071b03150b010507020405040501021207020105040201080709083a0306030b1f0306020f0405220c1407140304050d08070303180c 70
    0x80d40d144042d090384c102d0600d110725040f40309414070f150f82c1403048051104244240e030814141a081c031001c15501c0c200c09040c441d4541084001e52203081c046280c82c030503500090044907111703070303204a42c580e52990003040742c0c018135501a11240f46166441212919140d45010900070044c2d4001810550030655015004800040c203145c10319041440c420021110351005035036079802c2001315a040a10150050128500201100d0814400c240d680044d80519501c90442c5944152040c403031300840e0704640701d08088a080034a40200180142600f400100e40c0c08140b040000c40400402005101d4049194010920300e803564590074000e510502c0301003e55a41000003190a45070701084441d43c3d000c0c203c512081003140042242144d104004060401040d0713145a0781000c0880152044541c002c2802c00c920300392886076030315610031507100a40000400024070280942900a002d4181c0a51018400c000f4103030541014842948002040f05000303c0d804d00481e2100c44425030b0700d80b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 168667679 1250 168666429 168666467
    0x50a0512060a050901030c2c06010c050a1e03080a020a0206280618051b03060103021b0d0810060e030a0f0f0f050f010c050c0c0d1506030510061410 65
    0x41e0f00c1c0c1000c28160502604180e80500c1e11440401c120000103001c000d014542d108101e01e168032840e41c51601900250225040241060501d02031000038807404804c0d41c0d000305826819560494840740d1403440c2c00042c0c01050741800000e000340b44a008686074005075a000c0d1440c1d42d100c51890020000c1042c442044111003d91038400da14248240c10240500340700a02c0b8410190301400250b500040c82c0c84c8182c40f082006010400381c00d41680c0e00200242000360725950000d5414025807840c045460261041c11800ea08064210040c1400b4800200c6d281e00c0140d282e80c41950b010100c420440c2d0580e0181d85100086400c032455901040d2103841465840b55294a9808620b0002802a1070603080016000307407a84092069260089080c1082400d2264440541e5102c80c00d10080900400d1080103220821071200c80c001002000f0403010400181c036410503941d02c000d04e01b054802c80d40307440707008143c0440e26038004060714402400102543c003650801c0b28010040e145103c450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 168668929 1250 168667679 168667699
    0x10602242e141513031b090c02010501031e02030607030203090a0f080c060108070b030105060d18050c030d03090309030f0311060f04110d0807060e120f090a0902040503030304111c0b16050a051206 86
    0x5041f28090751074a40c02541c0049003550460900c608040c080900040c0d60210040840c00180c9001c0303880c1c2d600c40542d00b00180c80783e54140c452802c000c09904003c101000440204080044040c050075400c2c9030750084500ba42e80702d85120355294502e0003020010700302800100113520700300c0000c0203094007000d4040b60b090102103440c0c1541d000100100c4450b001342000c5900c90400304541414500e2909d001d2142c2891514040e141a000b400040d085000340ca0010341418054401a20b154811030b04840851401c01c510102c00c820943d011144820207a00d948040d240c219044865240c00c441c0d51481c019455440d00001c0059502e41d881c54002c51a000700041d5080020f0042c0c42c0042092030358541c0c002d410001c842a40790400043c1174418030042c03000741c40000540c1d42c055446401310345290801c40c00100480740000d0000c028031f400140701d0341003004500b0440d024650349030041100c88442c800070360310b40c000d40710b00390000341e0103100c00e4110b03d956020054004074007034020454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 168670179 1250 168668929 168668939
    0xb0903091c03080f010501050d0f14040c24050a0e0d0c0f08010b03010c170c090405040c15080601020c0f1f020105010602242e141513031b 61
    0xc0c800d44603a0080098101c80211402c1c140c010904984c000c0f801d68400469604200c0003a095000f50762424210b80d0b500d11000d9203802840d0f01450340402c00c443c044195240902d401e8480502500500c990440c280594045040d40740901111000494844c0d42c108070071034100310b421001c02851650303c0900d88080e0340c04681d8800071903010702040e10002d141142400c0b0084d0135a8123803804c1c907001c0e030b1400300c1e803000da568030840b400d400b11b10f452010300680d110143c4c1e0005c2c0380034007040241d120380b825051104011004012004941c0c1c18000050700f91260241601c904008035111800f60704003400ae1b44c50303442e00d010f078940f008000078508030100c1c0c078810302c00301c05a0040d0340020144c3c1d550001844841d80400100080d08138240100d518880300004504034100c0250961640000c20b00e0700015001e81e982d1400a60851160910340c81d40e5030745c020904d441a4a614503010f000c0500804012052002c101e8050081089030380040e03514503640d02c032801075a41d45e00368402c1d007483d0300412 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 168671429 1250 168670179 168670189
    0x60f040504060213050f0303040510110706030903090e06090a05072303070801050d050a0b060a05190509100b1614060106020105100b04030b06130209120a0c0902030906040b090309 79
    0x1010301e00881e40140c413103800011262000d0750039004107220b25028004003415603800000c58041c1c03142500c9401c1a0b0341c2c184000c0d5151072200151030898081d01c00d010440f580e040d030001000350b0080d0740340400c8559900b003140b000c01060b9072090308440352800040140340c05030000f582010151821800c0000120b00541200a51a410106c40e260010a20269a070b0100c15540035040485016100d41000e544c2e840d900d480c1d0010080c0f411000f980042d0312913840d4512a402021302815000c3c511151003810744402041c2c0c01007030301c00c0e40f01501140c0c07102c215034100e1090f0f820383d00c2c1d528034002c107d64180103400301c00c0742d086a00c020b403c038070012040000c1c00158001d260580010481c3c0c140020020407240c40794026000e01c610500040000c1450380c2540c0341c00035000c3d140740020000f241481c401a12481880302c1c0c000e1949800c641066000060030071409000707a00310140740e610341c81d2090603840180c40581d0705070b0154010501240300480e100750080c00310000c032803400e14031030b01080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 168672679 1250 168671429 168671431
    0x810060c020d03230915032509120506071403011202132307021903080a0b0a03081306080604060602030403170913090b060108071d12070b0301080f0601150503060f0405 74
    0x8030304080c02160745942c5e82002c600301250311010001090541c58030440c48904003840c1d4011000010480d1880280240500102c1024114841255620751403030b0522503642d95007500c00e01d0004003440900040060080140c0f41610b014a03551401c40b6020380030002a01304c0c0314607400c0c0003540e9010307000584000301007110395444440f0707031b41840307141021020f410881e0100c0783e00c6100340201d5a020000358000c000d03a9120001110000e640c40b030310b0700459629400380d0402440203030002245401d10401c069044100c51070342c0c0d6400800d0341c51500f4002503509a1180e0400350b40140020710018402d404032504100003100071a041051080000b00329048940d40303107084c6035032800c00f03205100d0000400b80d48401c003802d01245605110300002c006421081000600c1055961442d1455071801c0d40010107441120807107440d10b031a4501c2c3c4031158030a2044902500c03c48103880c1020602299542c101e640b4001c070200f818401e0002a0790941c4000c160903480760b00d0340050480707960f80384641c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 168673929 1250 168672679 168672737
    0x9030e100c02090a090f0803090109050109080405040c020f0304060531060822140c040203040b07080106020604030203160201030209060c01050a0e0f0a06020901030905120702010810060c020d03 85
    0x40032429050062003140e036801341c1082c04140c00e25200c880400c08281745200d0b2151b218003007640c0d0f5900d942403503004014a2800411075407c1c0b201100c144810b00d0050026111b04031020002244680c60581c2d0350542400f01206030b40042c1700c10440c1c0750107000076100103080c800004982c83c0620030b00a48200054000c1200c580549405000140d440a10298400c0c0c0d8518400d400b80034034007000310356658140000b031001c0508008400002c0b000c2c4550b17114640040c105546900b028a000c2a80520496070500001c070700c20000034500340b0000300300e80115003580265207030100154804510040c8048181d0600d80c003040030381c0242d102c1e040201144000c003000026182007107031a0f031064851080c1742031100d900203044680c42c42d03400b0800340380361030327000d03500507070b40d18031000140d002e00304107800a00719008201519902050620080c90382e58401d0303803042c10759919804042e40400c814001d020000d500002e450300142003000b00301d2211402400c22101d001d1000d4801c101030a1a0065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 168675179 1250 168673929 168673937
    0x10051e0406050a0e09010f0b0d020d030905210d03050c03150f06030108100b061801031a030703150507031a010503071716030e0105010311060f0d021b0618030d09030e10 74
    0x30041005c03400e115008070b0041060b82807010003141da0000c0c00d0070824640103403081d5014102d0804041c01046500010240941001042c240400c0344103000040c1202d8180203020300802082540c0c403a00c0b46500c41c5d100b01d000f8074192f0711403020010b21700c0e050002e2036402480e5005184480da484001842c020034001e801002c90b2208540c1c0e40c4243d40d4418021402001e080c40160480c010321100340b41010002e103030000d0340c0710a00702d10f01412060201c000e501800750040120a002c014400c84000036901001400a62294402141140e90480b081110a00d002804c18540e6100c0d000a41d00b0411505c0d1066074806480d5828030346040989a5003550041518000b00c00c1d900350041c100d20a4120008000d40e42c51f40d01c40005005e0940303e01881102c0c006144403000391000151810046109011500d27518403101e054080340391100c86944500c60100042c0350400c0083e40140c1c01d103078000c041c41c24407c00c0c9080718003502d40c5203822024005024044089034481104940f06642642d40d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 168676429 1250 168675179 168675181
    0x51006090b0f0c0102070c05040b0306010608010902090a0f0e0402030d08090d030c0e040c021b0603040503160507090903080f01140a06030b062809170a0210030908030a1410051e0406050a0e 83
    0x2304000480f051481004d00030342021004212485c0c11604050440f14001c10140c0e44105440009096a0aa0300000d401c1000d500000c65030341060342081d44950f209070115200d0a00d5880c0c00c0d502c5e2202103c2080d00ca500010844143c1c3e132094019041020f01802c0207000d08081c00000b8003a11001748401005920041111984440103c000000c00005640c0e0b030385076081170b49440b80c90344500d00507104449100009503080200800c81d010040199030b90030481d1103a01d2800801103d01941c01c20a0070002100110741c1c18002c000c070082600008165048061a019065000d04a08404168811070030b000b580c0065a105401c0f101d00b42d245041908042031460000d00004481e4102c0c280190100180600c18000003030441040e540440f0041c0841011106c200c0c081c11800d28001e0401074003009004440c3c25940050f034400000b240c41d0707011a541c100d500c141c10a000c4c81031a40c032454034484501100340d10390080e0070f00700300900041400e1751170f0804104086d00c56449003000d0007003c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 168677679 1250 168676429 168676439
    0xc010905010507140d0b0f0306040b07080601031811041b09170609190c18090204240303050304051207300c03030507270603051006090b0f0c0102070c 66
    0x2c881e01d03510208500b009201000324445103546801081c3d41c10801d65600d6402a000c1d6030b501000a000e81401411690280791920f010701c84008151502d002103a2800007207807040d070083c02402c894004c80182002ca941c0140c44d109100391187d000d0300e800584d07524040700b0100e05c00001125075561034a840703c4192514965904151600b000060b86810540521801c00e07c045075034000c0708000ca0040c060000d00e42042842007110798030009042080381842c1c0d01c0d0f1159030704505450b40c02201d04028240c8842591162507000010840341040910800e0001038022006543c0041c020b00032248100803c01200c01c040d0b0180d68107807000c48045000c0e0100701d2a089980c0144003100c51118424811440080c00c48044048020289503ca00014164901c01d0701030201054840f861103d070500e071040002e10310441d500035880003c1c1820001500e0b00e0b02001d4502c1140d42560360724110525082c808070050700f041900e1003920404011702940c2c100240040c128940c054000920710921342 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 168678929 1250 168677679 168677681
    0xa030603051509070501120b030a030e01081e16030e030304081c020708030408030a021204080a031401180207141f0c030c1706010c0c080102030f07181a040b0c01090501 74
    0x36800c0c80782c11202d01401c21a2100c800300e282404c44d030003802c0c503540b00c524052044010707103a56544250507114114441e01450340c421040144001e00781c1310b602c03580d01c410102c8001441c6026200b5030310004100800c006240044081c03241c1c80c41e81c0340001d501103c10080c5419948142c4007940c100d0f80110750940c00780120b0041c0b00219100c800b04500e0914660f40b4004a40001003020384588004000508107254540407909043c46803610125286440d140000a0341c100500003000a860085071181038064094800e040c0c4c1d90340c840c030082d0000d064038800040d50180d00b0460300700101070080c0840040802203c03da9035010105280c8441c1c03070040c56030071214245e1180c030400d0300f84a0070b580c9454011a0f0840015030813805803c0703a80d10705005070f454590940004110400102e0000755060040d40a10301072400328402c3c042589400e50200c94081400030415085890b4880c20460702e0354101e211409e0415215160313080c180c0c1c0d012245160703080200c00c04843e03511a0060410040d007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 168680179 1250 168678929 168678943
    0x13170409050a06081c021504030c0b0424020403020a05210f060405101107061113060302031e07020601061d06160204050108030a120509030403060e0a0c06080f0a02160203030a03060305 81
    0x942c45e81c4000d01030007058002c0d45d4080d08400120451032100104080c50320950300758030310b55082060076049040c07910340390044000c03124103200d010241a00400203100c05000322011a500208441161030405040040c503054080c03101c0c0d496a00f0030891100c0f102c040c015030502c1c1241d00040c001500d0309041a6084c2460045c1100d8014a852010903040711240180c4203003980200700040c81223001d2140704558800e2a80454980703a410800041c43d552680045110b4070098903d1406060344d05075015042405949080268016200500c40c680c030902d68034820041c500c00769115100c070b0902040b0b09a10106600c1c1c0c500e188041c0703441c1075041c0b40c000c107401001e007000154646001c0d907100804610320751012050711a02c89000c151694410816907000d9a0051020007140302d100f400c40d41c0e02c0900707490440d05a400d2010010340c143c007521280b841100120b04101c19070740d034141194001d5101d0316944626910304401c1c0c001584003000607204590031038500290b41800c509015141c80f072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 168681429 1250 168680179 168680203
    0x80a020406050a050a0201060b040f0f35030409110a0f230c0708100e120406050304030507020d0f0302100f05060609060708040b070c050901050913170409050a0608 72
    0x8010801044826440b0007180c4604042d0314045480da01d40d224100d007d02000d41c071046a1040101d004950682e4203400b5034100d940c09a0801c0d1255074032035200e01003c0b080300d000c1481c4095a449849034026841e00598042031003002c0d613207004d8417002c0398000c40b06070403510741c804607001c500480c3e81600b0507841030041d00c103424100e41ea003a0f43d6501e540300044010381301070381c0000410040602c8900300444d1020f408184c0648003100c09003074941006242840f144030003840740c0e4003000010808030f4211420345440d9900c5501c4e507074031602c0c00c1d04d5650000200302c0c2c0000300d0080e070001240c01c0240b0000414400e50203011b0b00707000169440700361007072001300f24102d624020910160755a594100c410402c015184946c8400c3e2034213050000c0e003d40c2e80804949400051070400b000221102c0106442085800c6000f82e40c84d2400c0c0319012108a5200201000da80072200100c3e15180c1c2d0203980b9034102020b01d142036120b06188040e100c0540d94503401030b803505403e0103050018803107090314032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 168682679 1250 168681429 168681431
    0x60d022a06040507050f03030d050a09110a2108070b280e1f06080316031b020616150c0503060a05060c06071b12111b0303090411091c03080a 62
    0x709143e101c59803102c810384a440d1044480b1a003045841d00c0a0081d9045101c02900402c0b0a16003440418054840c0c580201e4841d00f010b2110048c03460b0608185090b80c0114a01203201400c114644405030200344003600d02940601c40900052140e03a4418401d02c0307200b402d43c62a2603854541d040c00782004040001c02030500001910000e0005030007035508018150259803c03445080b0140200400e81003440f103400300245005840e58a440d42400041c86940c3d0800e00310301e0310554540d0340c0c03100c580003507000c001000100c100f10a20044680c0d0a40144010041c40c01d0502d501003c560681009070b01080c00401042118584903402000500c03050300d01d60f01c1c00e945192100d4881c00d00034a40d01c1802000000350712039030b40c0c0c080624602503228804d014040042000a00406011802406988182c8946d02101d1140c000c0740705242c800500114105040c13341000b000e883d41d104922940201805001d01641e1140b4409041c6d11512080342c84203000390078000d0290381c0090601c0601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 168683929 1250 168682679 168682681
    0x91505010b0708090609030106420c031101061205070801060e1f080703060e061303090501030905100f020a1706010504030b0c12040803010f060c080a050306060d022a06 74
    0x150220004580545500c00307496a540c1c4c21480000318a4052900e44035059860701ca0085500500d10550800d100e205540003004020081115020441c00d086007581c0200c1044c0c001d04014081c02c8220345c0f141c801d042c030b0030a4151181b00a400c454440c2d104400031000c0100a01c140701080c80442c000d80444030082c010340307007000307580000c1741405003c02c0c460b00600c03060000b416019103075050180c103440b0151045140e51707040801c05055402c0359030519000d200302280900003901404900c495150b11440416403a100041d001010648415038581c002c10705400c280f801c45110350f07031540c0820540180c40c0c8000702e00c000c154401c44d1458541688600c0706100090307070000c0030349d01105e40c800d0160b178641e6100a00700a142c0942c00600344180c5403081844200140d440c0550b05890603201c824846507611070080314442006000a0b00d000320802c0390030347d11441900190340c4008081d01403450310384683c640f5022a40b0030340d0801c0e50034081001c580411036a9132150f030402d4404600402503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 168685179 1250 168683929 168683939
    0x30b090c090f0d05010e060a1b2106081606030b060403080d09020a03050d020d0e010c0b040605060103020c1e06010518070c020312180306010803120a0903090b03010909150501 77
    0x69841140303001e0b4031071820140c0d402d00d1651490300100300030354080300078000c0261072000036950b044252485211a800c201c51000350820140d01800c40e680d1325551007507600010540315000309041e01c40104c070300f41c841c030000c200341d541045001e07645500e065880d06a54038020008044900d1008018420b030000c000c100082082d400a455119230400e40021701c603945440000c0c0c2903d85a4001130050061031011001140c000c100780585e20800c3e124130804002c2e44004466040030310000400c91f030300760400b003408103455520065002106040c01490510700c182490315060002c000114094080704125440d02e0003408000d005007016a881c0c4080280409907855400c03005049400b0880b8451081042d583c0c00c00c004041c15110a108039918510542800c0e0410b03d401d00582c080d100d01000080c010100000715607201d0160503c4e007285894400c00c1201070200a4030a408001413440c3c04503d900c1068000c60003014100800240c103c454034183c468440c901c00e00f1888a4905401049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 168686429 1250 168685179 168685201
    0xc090501020319020a0c0902030402091819050a050f0319080c090618090114010215070903020d050f030d05060907020a0c050f0406080307030305041b2610110a030b09 73
    0x251003424040f101c0030140350030040745002554800a01035040c86a8001118801c07580111b008030f000307036408816a982c0100c2141305100c0069440015848444588000144451000c800c60301ca1010f4941d042002d0f103c41e031070800c0888541c1125040000c2d00c2090f1200c01154903480c106a04284589140c8400c00240c1801607090762809401d00107000340d2707980d510301a072030444107008081c2c0307010b940c44503280c0301d1207030351007a4240c007612031380c007442082004030a14584200c2e42139a8035281c1c0c03400c65081c400324001b40301080707596108445055003a2601800a40458686114001038600d031400401c200420003030310300c00542d00602ca03050b011400c92007a4105039001500c403000e04d40d2500011a0050a003a802429075020108182c0b0400d641a000140250300519456408003d8040701d210240f05138880c0020611010b00300c40d03a0340b444442a1003101c0542ca00351582020034603102d0054451001c6c5121020200003a000a110b8040c4a12400d0384001c2e82d44114914105103082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 168687679 1250 168686429 168686437
    0x10e0f0615090a0b0307030c08150c16080d020c06040605070c020a0902030c1b0309030c090f040308040204020904180c0609031a040503160507180506030a0b04290105040c0905010203 80
    0x25024000120003d40069400d812401c00c090010341201c4106030b59050020f03044000303000e6510103005102e400c8040da0220f8068034010741880640900c0d00f0300000030601603400e41c81d400c5540083c1808541800c2d5002c0c80900307118081d000191220b86010300d8180222207006150384248001001010056120141c480702a81c0d466400141e90303884001c161002400340b40103258804607084616024540044080d110081064049030029240381041061500781152640300c02c00d04400004c0200e44072310000c0e6081400544018981a402c00129050742e40c1042c0fa40000707407012152404010914981c00c0040ca406d14200c0b00c1303903040d6500e000081030b00c4003ca110a03180007004c681448001c2c400c85045200c0110f0b14801034202d4034249440f007000340700740c110801840d00c0c4040b0020301070180910480b0010040c00245d00d6554500302036610140080e105220000004c4041a100030742003507000c0345c5180c0c804c0803503140008101c02d60340c5409241081001480d400c21a0743d030004180c1d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 168688929 1250 168687679 168687721
    0x173c0406290d060b0622060504050102030706091703040812060631051207081006060c06090f0203060c0909150a0b0f0705031c0b03060708070c0203010e0609010e0f06 73
    0x142c01d8841080c20540702030005202426072000c00012813200d50351030b44d0b0701807009501110241508a80d90701c1c041d10030740194030609000d03070800c100348000203000340e003c03114051203010120200c0140c0540c078209078004070b8003201e00c84c60000b140f088000080e0b00056010340f0894401c0c1c6810446008140c110008010f10842070300c03aa40303d6002d005095100c00044c1030050180707000c5400c2840216610040b0f840b03003003c81e00403100c1304650140da5008640c01d0b2141c0b03442e8965800019600e507801802e441c45c0c1aa0390340b4035440c01e0801179905110290249200b00b000070348444803441082640b800181c6942c034045039820612400340c440440c860210790510009584503e00c40394902c203a4072030f58100a16a00001841560390150550320310400c10a000c410810744805109060340c07240d042c1c90200109100c040040c10701842241e5000d00d4501c00740c008901c144400340c805140120940e07001c0d5250351101403454041c4030801405080d5020398005150301d007015200041c4c154030010301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 168690179 1250 168688929 168688939
    0x13060f030b092a09041401030308010f0302011707200c0a061107060c150c020a11090405071806090207150513080307051602120a0302010507173c040629 67
    0x1426078101c3c059000c0c2d4a40b40c00160080c88040c11104010391000024002200824810400440c80d100501c60706401d03a030f411b031610214098800b5180410100042480f03080017400741500c03c0c42c4262000d69040d003802603000b048a4416182008130342c22040c1c2002040080c00d208800750084000b51200483d4002c3c14503100001345c5041850008058140f021402c90030700c0050400f160340042e01d015a0350240c1c0c2e2201c44da902d14010440c02160a0742c018040d540f14180a005200710f00310892108a000040000c03075903545e050800903600f061b48152080c1080707046842c03112006005417075102d05c1c01d521103070030703600ba60b41c4041c2540009403128007000300100d501100c060015a541e520190001d100c1d281460500070354940d1100d0f4400118015401d01d0701140d200f6000728100301040f02c0090310107020b5550844800c140000d11551624120845040494214142240841d9801c0455100b01561500b41410401d40d0300701e030075450549510302540c800c0741e03400c0a81c0f0755684104480d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 168691429 1250 168690179 168690241
    0x906060f140c03040b030108060601020105061002100c091203030b04050a020702010903080a090b03040b06010e01180501080603030d020f040918020915030a060c0314093013060f030b09 81
    0xa407540395010713642014011080010002c61494400550107104400984c001e00042d0390714028461000d0070000c104025904c10f10f000c3e900c0d034460b50404d11981d0190310708001d82680c0d546242c080210802c4042d00800da03100c2e4003903c64109405000d50011180300254503241180c2c3c0001e12040c03a07031001804020340460b00b042a280f06190368002046004002601c1c2d04040c141f40c2c4260030190780541c04a00c1c0544c02200550040780c0a046818030210301400b203c0c944001500e25a400a124a45c14001000840c502ea60359202424200e040d0350525a125410080700d1003c0720901080d402c0400d4a07a0090390050781c0b5000c2d40390f4054000001e600801300e102c404289441002c6500803c05410034945040c1a5450342c0046a2030289443c15071503502c4800c9200e46524040300307001c2c00160b0360040320608014180001a0316502025240e1034401000d401e6001c0c0c200d26000b9400180003444902480795150003030402c080030803984516107090403114a00c80300c404017646030310681c200e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 168692679 1250 168691429 168691447
    0x30215070513060e01020114011a0a0302070606031406010608090c1203091302180616030c0c0f0e01090608010506030c0f04020f120609070215041112030706060906060f14 75
    0x40e040c0c0e04000e40300700d040b0a03015101c460152000061014540c0150700e40044803982c60303000d403c47e504039155400c0c0c00c0106002401800200e40c459410001416020041c03000000c007244260720085024401894920301c031400c205003000f1040e8014000c01007240d00344010080e0103e03c40366110400c69021844040c4c040300c440c21030158808495114104035411100e9107000c0c0c000b44504d0061680718080c40c2400010004940502407907505092055103503440080e001314906080207020b96000e8540543d110000c42d1303100302540011001c0e090600041000380228042e10000d821400001c1c085441c129000c00e82d101803a459240c4a03544008401c0e500e51240d42c100d8003140b241590003550b441c01e4813000d246120003554200e001c0c001402c00104858800729041001640d50044881680c50702c0c0c82c2d0711000001c00c1504c030fa00500e110440c4040200800050203014803498005c500f0518081c3e213082103403902d0f0b100a003407240409a2011007980010f054004d030f00202c0c185903c5107403034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168693929 1250 168692679 168692687
    0x2703091009050907091401020d021504170c01060302100507020d110406092901020a26040914041b061b1407030302031c0b0901050906040e0105130302060c040303021507 74
    0xc0d030302030b50700302505400703000c0469406541d180540e080a030b81074501240f540012a0340d8041c1010b54401030300711030361a154507050940504c2c0c20501400c0c080604800301c02a44a80713601c80764a8640c1a9501e10040085040554042d00c0180090130f215042c013085401050843c0056003000300f5118541c1d100215a503a154040d0700600039213042000703d00700d00e10b9603d00ca18051890301044100360071112030250320016a1010142e406000d4205a03c822001712030601c00c0840840c2418205002c0811003200d1449140c0b0181c070140c01e10400c604250401c110701000c4c0305464052034402003010311032603070400c0d1800503901408540c000c28a4233424601401850803000e4002405195800018154000003a0180c80b1032004103110810750184480c0c01c0760388044100703820400010041245141501d8420350145000e0800704034030916503c0d150840c4d4080b40c800ca071101141000800b80369040001591215001c5450340c0381504549010795900c1c40e2038074800c0c044000500080b000ca00c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 168695179 1250 168693929 168693947
    0x140f0f0d0c06031a150406050703260612010b060f0d09020d03051201060302090109060e0103021603090f1d060402210901050f0901050415050c07140627030910 70
    0x41c446211050300d030400180078191420580b20400603010700482d003880d00c000019002d0004d040d041e0320381490711805131000c0d000b014003a0180b11900e03140c00240c1d904c001d942507038003418031a1004c0705d01d0144104030b801400d02c81246010b138507140c4500482e48440b400c8480308108101480c3c1c42e00320701518078010b80100c0070029008021020a10109a0002d000d00b14003030000150707802d16070301d480c801c40482c02a910006e0000300c403520b003003000c68001c0d0301c0d078400d00d4410314000d443d000c00c00506441e4645501d030214002980c0d07500c20000d80d038000700d000001c0c0186000f1813030701c115150700750300c035054000d40107901c074580c006810310030360414440c0200e0504460f00d40a049103403001081c0d000340402c40b26041c0602030f1200181c0401018401c1d40e200b25408405859580141d00c006402807000070525003490b0310030414000400c9084185a07442d5101900070044c5241c031a643c4000755446851501d03c00088840c003440142c008000e0b1000e008041d10012030528803a0800c0b580304007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 168696429 1250 168695179 168695183
    0x703080c0313170c010b0904031707031113030c06020304060503180307050a0506060301060e0c0a0309050f0712060c0201050403051606200c1606020307061802120604050601140f0f0d 80
    0x40c1c1c8410f20441e140150107842c101c40460004c000049044043c021281da00320303001000603540c0818882541480301e0403070b8010429180000c0c1560740c85550111503407003020000d81c110b454210400c00c04c0704c9101c403003001d00380c940301460809141080150442c000944003e800b499803c20040c0703401e5041042c3c5010503040f13002c5880fa411181000c1c0d81301c50080d01c00d1800b07542082e90114031107400c0c1c0740031805203103149030301391030b017545008101c0050000c0c1404940342e0140e001459031064003080904007070142100b041500e003455203041405c580746d40300d854066904150030840441e8106042d143c1103090131440000041c503d1078171900400c0c2d14a42d0b8107542420307846803c0c490f260840901341e544001030480d448010002c043c3c2106141e24402e4100682c002c00002d40001d41c0c50300070500e030a054031111b1042840540c00517440c2d00401c040000b40d079001404120601c0400c00040740184a5442568241510712000c54043c002404d0103c0c0105000c0a07803d545031211090b0803034460f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 168697679 1250 168696429 168696443
    0x10905030a2304060e060306010908010c0906021e0d0c05010f020304080318151f0b0304080a17100902160204050c04090605120709111201031a07050703080c0313 71
    0xc400000050b200504401000d40482e021880444440e48203200b01c0342034640c0c1d921814418644901000b038180d000500080c1084500300340000e48103024051140c80c1041500d800324264242503000b4640b0f0445007141403200075541c10b0206060010030aa9507004062602401d100345904009025100c2c1010030540c1c1c0d0310010410082c405000041e600440d105494000c0c2c1d10a82042c03c1d590380e503000103d0510012401c08240c801e10380400e4152840884010503001c256640c0c804022600116416147e8202c0007648100041d030205030304402d40300c01c4035203001ca403c0c82e40c0c014082040300c0c0a00e49920303500085070501a01d40120b00c0c42c02d107600610912407032a09103040000d0fa0000d1080c0317120030f4100310001c111440d2501e02e92249455600061043c40d00e081205800b800000c00c242c20300d000200b0000b0760300c1002c0c0405074080d50180a0f0042c601c41002c2428135032101c01405d10302041000e110800010350721984c09600b19040a2009440b03484404500d5408030409200400d48 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 168698929 1250 168697679 168697687
    0x30e0d050d05091206090714030a0b0a0b01030b0109080703060518100902090901180f210905180105030d030c050405030f0f060609060907030203070e090a0519060605040b030901090503 81
    0xc02e41c4000104103280080d01c03988880744251921658410b015248001d84c0d42240300c041c401420552003d004012009003100d4480c909919a0858080d064400964458950300c0613101542c040c000c0400c900390a02e01001358a2601c1c1c4620303160410350000400c3c2c02d403036a000c00c42d2400c1c246403100011440805940718010150094002400302c0002280aa0072100000c0c90760001032080f416a0864002c041c0301184442d9504214000181e00c01c13900d1900040e640c40300807003030480310007522005843e0101d049007009d003080a424030040c8019203c541d0100148020b840104510b07017070340542d0502140300c1c54807170810303101c0380125000075405200703e000721007540c00c000442c0c113289055003042e00d120361200c009000001c1d0003154507a82102180e404210204e00c40d50003075a20078402c0c0303002012a2102c03030001c4d07000403080d81d0010740992181c00b8060f400d01211003840c14400108010001e00e480d0000c060840d008501c2801c064890100000c0c80103042904008892540001a6540c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 168700179 1250 168698929 168698953
    0x611100c0f0305181921110f07060e0409020a1e180b0102030f030703020d02120402041d060a0c090806100e0106020106050a1a0706060b0d1116030e0d05 67
    0x4035050070203810000a0520021031196504480181c102c1c541040140c5071054034420510307980d4110b05012900350b0207010403052440360b200900da0a0141d40d0380c07107251519141d00c4c03052810b00300c1c0709492099000000c00b0010641c001c0203d0f012040d0940d008121014a07000150710860f40707521440240c000c004885610040040c4904203540462118840703104000c540308046131a50050f041c00340c0c0c810415401c41a90180140d40d2140c2c49250140c503140800c1040c00c241d81001070300c40c03450041c8106010847c5014010308102c56001c907007400e0945110140590340b20409003c9500190b52064807502481c480d480a00240482804403841801d208080c40150003052051013041c10007500003295051060280108844004066401060074440f103640c5103054014a104200410428000003c116003d12001000d01040e82601c0306501c01142041e181510300b010010b03d01000f00c180f882004035140c590b2540c05203460480c2101c50801306164030b5a00c80302400c5481000e4200e24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 168701429 1250 168700179 168700187
    0x1b130b030a020907110f0c0f01050304050f07081014240d021806040b060309030f031519030204050606070c03080c010e0a0c031e050c1012020406080a05011e0611100c 73
    0x7000e07004041150003400343d0091b0319454158454216a00018290719035400d50b102d00099030b00b1034014004e48130200200340404d881c12200d079200c0003407608500c8c403500055105101d020060a00605044507030718120040303507d00007a05001c0101030742c1c042ca1603002a16601040e400e059405020610562000b20b10400307500c83c101d81c0341e84518100300c40c1c00c3c0c02d81884010349005100d500021400c0505103060074440707400061220250a50a020460341c5555002c90515132214a501e8006d6050031801800b0554000400690084004104400008008070301c00f4040302d41181c1c4007605c0e50403218501d030140c01e5203001044140708600c81e003020720401030101c00c101d078451507a00783c0905820095505800c03030500c014009400900300b40c00c3c0740c04d00102c100b98070000340c500200c1c4001144c1c101c60403a0029088440002c419030100501d2024034403942c0c1c0501041d0094220014082c014230460703c40700d0140004000100000c203072054401c10022900b40242d034130034001001a014018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 168702679 1250 168701429 168701447
    0x6090e010e010b01020307030305070c02060f03240d02010c081209071811040e0403020a150b030f0c03120a140706050a050a06060f05070c180209031b130b030a020907 73
    0x2841951a040324500580c0052043c00c8840c03070f041e0007450503c209030b102500185030040018003440242c2d200f003401030b0344100060441102180d405522800c0030034407210501c550140101c01c8a44040f04a01e0380c0ea2103024110000341d09280203803043d1010b1030640494000c0c49991042600f1100a11869080c0440d1680a4408461030032343c0d5030a03014048002d51b2220a52082030310001c000c2130200c1140721024a501030b000380110341618900e0780d0354003540c0100c100022480d43d0340f6271804005103820302940c6d10b040e2600c0c00030010450700100007034980d20804140380036144002406594a400b884080706e01d50741e45a00c3d151241c1c0c00f0304240000e071104489600c481d40c0341c040000d181c88020700c148400d81c2c4855490251240c3d4104066855500400c4240e42080c20f44100103101c030f490f12a80c0302d4003403005d10f001d0386540c0d54a05043c81d007039a11141004200c1110755400d019114541c0c0072810004d5204040f840c0341d10f0401280c00c204004001941254141e01007000729500712503c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 168703929 1250 168702679 168702701
    0x306040303022d0702040b040e0f0309100c0209070503071b03020a0312140103021c0503040314240f0c1b0a021507020d02040e0c2e090e07140d0609 65
    0x9011004440c103d24071505440d28050a051801442130740c016060aa00113800041c01400c0098103c11603913a0034545901c0c1c4460045540c400101c4031050304040c0d40341034440d084d600f041d4448130440ea00069600c0e074001c14200410030702200080c01d45110345101001080015600c80c1c5610765424020340b0b0398441601600458400355006542800314410f042580c4d8000045003a60307401c681c00c100e00d15024001a0f4102002100d8110220b0814002030000b507100d050b0341c5d00010142884d450415840b04852011a40071040c051285030340700216945c0070381c048039030f4203299840c0c1c0c4038503119020b113082d100701c0000f800c0340403258101c0c0044e03480c40d10b41c0200d40040d407015449000010900c81d1210003500f00310265449801400d00350000002d840c00401a0f6074202e440f000490300c047c1c0e008680c0c9d0012140da16047c50000503070303407203840440c082d8035020b444070303040446005402e000036001d60304000b25405840810386017002038504089002c0c100313007c095035440420001c0c00700b010350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 168705035 1106 168703929 168703957
    0xa02090a0905010305070b0f0406030b0307091109031e0c0d080c1c0e040204121b0f140f03010e0a02060d0207050d03020a0806040c140f09030604030302 67
    0x41406003403180d50005240d0301d142480d620703000702e507801002c40401c10851402c5072306032242200c0541d4103a08010681650210110b0306e00540f1340c0c00607042500d1314840c6024100100000c0005d64000c5080781c0038000c034070140f03a1400e2006402804190703c07401607081d260a0032030800b444103000701e04160030030380e6103550281844080009030f044c02040714254020b0a03001380c1c485000410603501103041078185641812890405103015101d1418030a102034a021588081d0000e042c002510060740c0d6030b90f0340d82520f85200012180d101d688440744001ca141030520441100448940080505580300c0d002d001f10390f032010321400c145d150208401c0c40400c50411050203101916034005a440d10100d000500004001e00f51078410350400f2050521103911080b5007002180d49081c45940740805100403900d841003070704180d003601988003084245a016805090f2569050b05 = true := by decide +kernel

theorem cover : BRFrame.Cov 168525179 168705035 := by
  have h0 := BRFrame.cov_init 168525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 168525179 ≤ n) (h2 : n < 168705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
