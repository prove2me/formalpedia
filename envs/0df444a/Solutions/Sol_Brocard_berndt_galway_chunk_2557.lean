-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:01.042977+00:00
-- url     : https://prove2.me/submissions/a0fe9c32-27e5-44ec-a9f6-4a110def4cfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 459712230 ≤ n < 459892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 459713480 1250 459712230 459712261
    0xf070303080603030304020a061110020412050105060108153619051e040816060213050303090f0103110403061b1706150a050f0d0b0411041a070201140c15 68
    0x940c000e2360b100d42807003414002c0d8000210100ca810403211034044071b085640490748941c01c00c0c0000405d10042804111090050707950040b400c2c41c000350306c1e00384074055410800c1c00d045120304c05c40d02c504541036141e5220f1000d040815444900b031f01080c0e103412840c47c0c1040240d440b50180002e12821341545902c1d80240c500030300c5035442d03051098048500b00a030004001d070003110901303402c020f1580c0b6400b074072a0968401e401030000503039a6001c0f180440c1400b405e0341c03005001e90004d0003c460f0329500c600c1c604080d20001e00700402c000c1d048c040c041a0034407446d000240780780d203810344124802891022491101701d250b02c036003044403000a50a144111701321005030303005081110001340c070754841000d0f020818680c2021030038040d5140e00909203800c2540c2420030b596441251800501e00b502402042180c100b6020385030505140303c0000c1e0070b0400c030105042030740026620085910401e40c051040e400302000036101d00c0610300e10380c1c0766410101140c1c0d001500501092821401c400d51 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 459714730 1250 459713480 459713483
    0xb030a3c050a11180a050f060301090f0219080a0c060f050c06070e01031b1110050403080a02070503280824150408011121011a1b0f070303080603030304 67
    0x70b1040b010165a121920b82d00700c25419080032006141c14840c5000c0400c0a000b00b901c1c0b500401c080c60410100110303c00000c0559200b6810030301030001250440045000c0b403030b019100040080301294120041140507804500b080c07282025007810710850b4140300c016038640703942d245864101528101c5582c010310440b02c0c00b940018000c0f0325007074011040c040d0f1180c018100804d086c4501c44206040740701440c1d0900c0800c03d401408207000d40140716140e200c034030881040019040c00c2d14020101c0c03e00800103100c2581c005407010a219007001a6180f09400003e8010110a03840000d244440700281d0000440c105402090b20a6141d0050300100d091582504007809050002c01a41c0510b800285c81d441d0400c02c40803500403c00e003d04c1140c00c0705503040c0d90b600c03038603040e41c001705101c01c00843d00301c421032070018070001d100f11204180600518040944406144482100c0e144d210200048540b14400c040b01da03264000c03131800700b242e0103a2251589613581c20107240d180d02c0708640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 459715980 1250 459714730 459714733
    0x40306410a11091c23070b070809060703021006090903201b120a080a0906050903030d110d050103111002010e0a0f1b03051525030b030a3c05 62
    0x2405640c14404444c03210000035401c003500c521801d40380d40b203002007040b012206000114049660719041042418010800f4800041c50312a294032002190f02840d5a400e00c03030070000883c402070500c200301d15054880d07640c0c0e081101d10b90711074100e0014190324a0807000300c0c80c0c500c0310000c1c0c1c0492002042c8034140504c00b80405894001015011b003070103280442e40a80d0700740b548402d0401c00c0012000540c0705030040c56807102c40c0d00e005824001164040c504100f0104005a280d88010054500c5049090b20104842701600d2000c00356010b003406020351070b49010000005e1200c10627901035551001e4030f020702550060001203082e500400d414245c942d002500140000c1d180c0c8407200c0c8000d0040517029401d640c586018402c0c030705658025078540e88502107842111103091400c0c0d8000d1018084d4000a0f0001c040f03c00d000382c0180040403c0c1903940301300c50ba16031000c1c0800362800d68444020408000e64800780089001c0080782004000680182034001c45034501d40c070170303880e40c0080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 459717230 1250 459715980 459715987
    0x27042913020d06030609110603011a07031e0305192714100c1b030e0904110409050f0c04110301030b060a0b070302030c0f070506040306410a11 63
    0x500903030304044202810010703420400c05104a03110722078640614801c8201060259003402d204c02d0748001851424410402000108480f000d080403003c00941050480c07620780386141805c0d85c41c1480c0b11854410f9035116807030300c0e07507551303044d800780d07120324503000300d41e000b00303041d009a0021500828035203000c03066000e014031750840d1080e01d14260f141c4508280280002030b01c1c1254184819500041c260f26114800b00303244603048404052524454103e83c05017000c00c0e10003d04168190a00394020782d500d20105040c0842c2c1640b9541d1414041c0081c0318001d0b051500e0796503070800c4210300310517000f809a442e110f0702d468054800c0c1d6001941c010340c2544d0070740e100c81d0344d200320140c030040e8400a0003500040c00c944001c040d10f0064001e40155840b420401e15072814428442c040444a402ca4201400710342c0e201d00540e01640d8102000203420603180e000001700307607400c015002e00180b43d41c5210100c0c002c070803100c41171110320b0b000c062090f03101c0c904001d09035690700209402400050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 459718480 1250 459717230 459717311
    0x5010507090806150103091b120b01080d120c03090212030c010e0f0d1103120135330f040515060105070201030c0507021e100c0210030506062704 64
    0x1d0b0480e007603041c01b85100940420a0200f00d0b112384070554000c104d482000b440c00801d02407500b000600408a01000e0a949081010001c28280c03111000b00d03461566004c0c0c030001c1d240710f42c0c000d0b10704640c054400c1180d1401c2c05482541c0b50011001c0a25642c00c00c1907415a100c2d001c10100d000c502c5c90070040c108202c0b0001c003641c010090b54603028403440305000b5190394941c9000e1407802488180340c4681c4454004006c04c490820401400001d1400b012098010070400290a6691402800104400501046404880d44214080707901c840240380901c80ca4a41d1501c1e500c4c0558410011150034191914840d148544200d4480b80402c20600a100144d4000e03000407030390900c02d03d0203070302d042c13400e40c0010b100300c030780c5030b007030303151452610101d1406041c10300003840c0d02055420000d45010742c41e4000355410300c0d034406407020551614045420307501c40310305961800310074240d5200300842156201c810007200d002007900c40c50521075018040c04403506444030b050307240301d80e05c504590f02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459719730 1250 459718480 459718487
    0xc0f030a020108130c06180608130303020c0106080604060c0f0f0e22180309091107230d02010203062e0f050906040e090d0306050603070e01021504050105070908061501 74
    0x2400c00a1144941c00300f04c001030a440071000140c0074a45030010040b406030241800b10400d80c005205215010090091800340c10490010440d498903000d03991798001c2e94410702500080e84443c840d44922414807040164071340000107810b03103956030a8003080141e10200c0b10070005039100c0c1c01042001d40d04410504260304200c4031006007000c0003c106800580303420842d00b80e500d580300c03000600781e5540308240d88005c04a000b00005d520501500a040701035540324480d0300360003003400709071904080c10140320460a0143e180c0000568041044401000c2d0203548125111441205c4114000d42c480618204548042d01c2000010151080c0d02800f6070302c014400c55008140881481802c069a031b82c200240081d01c80c00d401d090f00b9040000c01c2c0ba1034005110401d005250402100381f01c1c80c0c030b42d02c090320380c003001c9440c200f4070500c1a10010303400c001b4120450040a1208010403003403090540002e40590030955a1808541d518200345031504020307600c00040c1c18400b4074030380b00e0b5840f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459720980 1250 459719730 459719747
    0x40f06030f15030b061008271203131b0608070e031c051c020a05220302040f061404050c09040b0a0b030103061d0102040f0b160501090309080c0f030a0201 68
    0x1c90360001910801e40c401da000340030455004a4201d500b4404200707140c10004001d410700940d50800d40f00d1414003d08045801c0c0c0140130b11714805a00f181e4802c4500010030000c90f050f1700040b0031030755909007044120b03411b81d035407030701601e40c1d040410036444100c850f1045401114140d80c2e07a440346440f540303801c03103000c0c01000a1036418030681c0c80d0450020002c0c0d059170782042164880a550302c2c001d842003000748174001e0205210074410321140300469081022a03080072000150451580c914110b01c0e01d840d00f032a00041c1d00306141910385900e5203a41c1d0311507400e0b00c62400e540d401000c4900d0410050390301c04c5400800c413103014042d0b4207580c01c081d0409450701500400c85503102da11182c4100141d0002d0b072096902c10703140d071000074009006800c08029209010002c3d49400d040010035988800c1e00c0c0b0682e80740d40000244000da003469001e80101a682c4003009204012540c20010510311031405210001d005409024549103080007140000c100302402801c10030501d0740041d1110302 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459722230 1250 459720980 459721001
    0x20604151a0307080102090103140f06040c0203130b0a030614010e100207030b0405030307090501020a080f0a1209031106010501050c0703060f09051c080a14060909010b0a0f1a040f0603 81
    0x4800715441c1429550502c8a0300c080c1c00c070707600016204c01d51080010b05560204544030030300e0a81605000300e1600e042403203580f25030b0954022802c05407001e400c038a03511414010f014010749a11012690081a04c010244200c1c0356605011041c0c0390109040400ca04001b070718003203020600d400c10f49082403000030810200a0041d107042c9035894a07441c01707c0800f12403c845c203030000000c2080603904410584013400081c4020090700280c0c0e40c403408248a80c0c0000611048003251140c460f0307105081e0340c40d540180301c0c0144110b003e149405030020091218002e61030081b1000840d407075100300260341950310381e0002403840520315180c035801003240d45035441d492511181800c022079801c1260841141d680c07034810024001011000b04035500c0038040345000742c200000c112030211300c0e484898008001f00d9424031301e030b107c040000d801842d18650040d005104100c0004803441d5140d044812070308818040358407481180040481e9200720300812013884003000080c400640709500c07525411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459723480 1250 459722230 459722261
    0x4030e0a1e150f0206040807020a170307050c0907140903010902280617010302091e0a020d0f02070503030c1309021209011a221b0c0201020d02060415 66
    0x241c4401c4240c241c0e01c0600c0d108800031a85103401c101c0462500b4121108040e946001801008a054003c1d1160b4010340080c0108a01040c6c42d0199075605842000800704140c074048649a24204991a074202041c00d032024041c407017191580d81414400280324111642c1c1741200703050040b0703d10400f41c003e038901581641d41e40314560010384030309414107601c080d400d0750340040c8400c00c3c0310340c510704180d60491381c200705801c580c140008100707502d10b5056035412606110150740340b84412000c81c00d82a003101030303a0001001e004460046a00802c038114211a0500041139030708081c109911072008020090752003080000c00a481900c080c108051070001e1740100c59030365141c400241d030005954141d85400c1c550612815503024841c104e032101c80380c6541550510b080300000c040c0320b120034240038a000c83c080129124840390740701039600d000c492012040240d00c41401000400c2c0c3c3c2d0012800b61040d04400d0030090f00000380e052080d94440450311509443c1003980010301111070030480c54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459724730 1250 459723480 459723499
    0x1c03020309060f04030510061224090b011403060103050d050306121f05130c0303030c0e030a0c0312020a050c040207020628140703050f0c0313030c030510060e04030e 73
    0x6560b020000d200b82c0005a08003a00d490950601a080c0100140c81e4180c15203032617410088100f661090040c16030300040c44c03906200f000c219400c428180c0c0180e14074400e1800006c001041503004200381650640f50003407444200c3c080070305070303502c3d002e0002904a03030114200340d8110303114000966002c0b5010b030140d0351000102800c0c5103081d00c01c51907880d42182c500000c240f9520140700b2242c0c003040100c00f601c0c2031052030701c3d910000c0d10341e40005405c048d15109402511806205005820680503088545204403410480c40c882558003044500302c2c8002036150340b152000820b0700c14550418060103801010074100710082d404807408981180007400400b10301d00c01b0766003540311130f0900445820813070f80300c22000786416841e500300c0341c20100c00d025503400300351300c00300384ea4191001408941c3c1c0d074841c3d0b050f260328500071120a100241c02440c0080300308090040d41e4021079119108035900040112201001c0c3d92441c061420300318030300400100400d100b1800c00013000e0014045650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459725980 1250 459724730 459724747
    0xa06060201200d0e0f030711010f0e010c0804180219022b120c0201021803031602011808031314041a0918030c0304141005030417040803030f04030305151c030203 71
    0x24500503a0031700d4520341000c140b81042c041c2589074411409001d19100601c8010300d02c024044807035550040d410001c6003142901081350301c03000c0b80c010340320805407403400d640720398049006540515145402c1082c00400052014000600010183c45480c54520a5040e8000c001c0618030a94040001c000e902c204543c00b05505100740c0d1244c2120b680003503503900c00070084c404541c24080070240a64010082c4c1c510310b0201e031a000c4090b540c240303000406040a176501d510907510541040c2640c2c0000103800181540c10b1401d40e00f2100b10404901141d1102410001203030414030814450b9040444a0401440c04d2803c8030350001c240c000703941641a105403030b54030319080040b40d001581d000003005c1c8403601c103c0001e000c030b00c4000c4405146002441000420500024000030107203c940c03010500c0040c40c480a6802406020302140c0d101d14010741d5085810702d0070746041d00403902c2c25002c1180851802e0300207640c0b100243c000c0d0b4240745444c0d41d460341d00f29041c0042e000c602040c4140903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459727230 1250 459725980 459725983
    0x9060d1404110f010e01140a050f0d0b270f04020303190801050a0e2a040308070803011d0402030d050a0207091d0f031201030609030512040b0a06060201200d0e 70
    0xe001d2030140d00701c0500d494115040c441c0001e0a000d03014184401078110604036a80420080901981c050015444100010099841e80030b98641074403909000304000e01004030725845016503400881e44030240d841d25144948110a464119030480113020740000d5040003d01d020b10740003032002e0220f914107200521200d0641c0748054080000031000c80040005243c071084480181103c00030940030390411030309001c00c1507504881005072410011520f07410900d42429640203642205040f5070301e000502d040d900c40d605c2400b4202d5018a1a10314541540855041c64495540900100800308505105507503940007140040c007184940203005c030300f021150092840d81c0369412003800d0580368660455042981212040510f50b1041c84021003020080c418181126000f05c40058443c0c014203080315140b00d070704072a1070500e00e560203120070458042512441840c50f00c1c0108a05900e40303070200d00380e0710b015007464410b80c10032250040f680780d1000180312218002a002480c50b05191259 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459728480 1250 459727230 459727271
    0x90d050f0f210106110a0b041704060503010e2805100902040914060d020a120201051308030c011407120b030703061d07080105010e010b071a0c0903010f1109060d 71
    0x9050402101c00070111941e0202c840c5030250646050248081e40140300540c0c0d01c6400800c06418080001301090134046909909082c200d030350a140c0c0d5a03641c607800060601d5100784205081154420300080300c82c0404529070040c0d0f04005e01e18060440856a1500984000380124440511081c400580745a20340300030801043c0c0314501103600f032100c83d9030789002c04008140074000d040c0c0003000c0006a45805404007038424070100700e03107469002e00040780d01d4010548041a8103a5a58000c02d00358800030240101a4961009100e03010f60401c0c0708840c0c1005850740004078a480000c80e84441054009011a200c003a0846081c82d80c1c0b5168507050b50310710480d1444140f40c0704a207400c030003402d200c160054040680240700035450404022003100c0705210781c40c0505404103c8a040242c1c41e016942d0050300c1280d9003803d806d204128900541c07203004914841c1d072070320000700d10790040750050220b00c50803580c031982090502824401c0a50006228841f400d82c0e5640140b81d140841001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459729730 1250 459728480 459728497
    0x1090e060111071403250512010209030a0b06030610150302090409050a0c05130b0102031c020903010e0304062703030f1110091a360f010f0b09090d050f0f 68
    0x1503490000c0d65006150074580032104181c1e01e804c003081c6d5031040a540729200c1080b41c405440e00442014500600da009000c2c128072035506008803e50601804039815850740155070403000d864803915940702c05c028580c1d6038460310321a900d940a04100321030095020b0444c0c038001404c0401c0810701669078a0500582444c220381c18200c0c41c0301482103003001e002c240726824090000300100c81c500701c0040e580380102c4407918024506c18451903800f100a40550303080c400068001c0c00300025070302030107881340c100e400354400194150011000c2014a0407030440e031051b4460892204a0a50318100c07007000082d00c6120501c05e04201c04409010200324948080465800000d0052054078200e20710400e43c422011030b030a0300c84240426025260f0f64002c4481c080c041e0840c0810b28140340a140702c45c0303070309650320340c3c000c400550500c81410b412140e4000c00c905401c2020884d88030030070100d0b22083d5801030b540d9116844240325580542c004010300329640d4100c50602403506111070059121941 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459730980 1250 459729730 459729749
    0x40506030304031403030f0c0406020c040902040b040228020115150c1202070821030a1505121c11070905040c0b0c1011160209040c081914070501090e06011107 70
    0x400c000001240701c000d4200d5404ea038120320305403821072b0080d500c1030024007175032055540d01e07044011580c55a00c00c0048000103003080d500d842c0352145508540070300c80a007000410b0103540c460550f61062080b5080c3c2c0110240902500e07080c8070f040c1d150044018004803d11280003401d10102c2d462107000d0740004000e9004000c09404c0407880d504051560764800074444420344840882c0c610b0800f036a501200a0600042c05178007030110780500300c1c0550140390001c0e80c00101c8441ca22011904c045003110700d500e018104d110400d422180c040c0403a600034000d0300302c0c0b03270240f00c0c450480d0400e41d0818050341c4400740707060710346104a20582c03266003020900d6101015040c001285400750051490ba07481c1090f0600010030500080c580c001d000082c41941d80f4400501003240100710750010300079000c12605122100e0076164400c3d45035001c207503040788601c641c101c0002070005051007030310b03c11b03544c0f9620f85181032480c2c0281c40000d030070359051200380410000450404c12201c0020900c400703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459732230 1250 459730980 459730987
    0x203160516050102161218090f06030b01080a0b150904080a0c0204060e0a0c080106020309040c05120a06240c110102011803050a12060b04030b1b04080a0c05030109030e040506030304031403 83
    0x760406c06840d03010951070030b0004007121180311102041075030302144c10754000452045190345a850041c041904010000300800c0e00205030003034000740e54100207201d0115100d490315250428811003e014000c03030307444104107002400050640001d01540c4640f42404003540856500040540300b80c2c3d04016484030255080100003034143c090b141038494182031034051541010f900075103c2c414032501d640165103560545007800d115004958034103054500c40155410200e29030400351801e8420f4240d0460302c4241441c0c1211100c803940868400c40e2181c0201c443d02d43e031032038940020b04601c90305556940e50420f102010b5030543c007003800e101c1e680c1c06555040b007050107485500610000d07405145032500034454010030a08450039250451401c1c0240d41c1c960742e6050303d41e6113000c407480ca048800300300040c1d50500012268a242c0c400c09400000031f40350802c0c5800ca41d0702c5140a80011805c1008a003e13007031a0b4822504150042c0030340b032620b42ca030740f600c1d224604908101e820070f60000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459733480 1250 459732230 459732233
    0x12020d17120601110a2913020f03061509150418060e01060803070b09160f030c0608061c0c09110d0b030a0201050a030c020703020d14070504020316051605010216 71
    0x14055207600c42c1007420800b03d004201c02e9156a100302e8032100600030345c2c0500e2114121010003280172010f07294150010b4045ca0109420f1500c00301075807049001c0c0c02d80900180580c600401c410348200300715002e8941ca5444803003000302a0030090002000d01c500c4004000c43d94807140240d104402e600c400400020000c0d181c44011600300d884003240c1649000d0050000d1a0080101c401c080d4011f030385401c03141c40b00100e06007130802c0c1d4800700000c00180500043c503c41580201c1003100c2c09100c00c03140c015075034201500c0c1d01c3d1085079041d42c041c6422594a20030620340d940340081c1c070301410861a0f0f117034a92018500b2920032503100c3d09121404030300b0201c06401c5005014101000364040c103c0010198006815030080a07088014141c5881c19079400a200b000008011a0020300d10001d401039401c2c40000320720a0103c1000300d015014010500381868000c0b0390013180445003d001e511580281200d4581000c0c104650285400f401c003008110300740042d0846140001c2c00c0a80700607203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459734730 1250 459733480 459733507
    0x90204062103180b070f05030409050106020609010f021306030228030902120c030c0108180a240c020c100c020603010807230109060e01170a050912090a12020d17 71
    0x14018941a1141002080c807103401004c06840d041179208a0040400d841da1030040e0460150303400c203804503850300c000016803690014180b0b001c0c1c45c1c1c00008102602c1c1c07007400b9a00342c1c03045407807140c04c0100044080164510070340c014003c2d00038020494421200030703004000d103a801c80d0b41d1070000a40ba070101ca819440c1c010180d0707540c025400000d2080d1003030080401e450b00301c0010100e040c020f03c1c1c0c001580c00fa41c82c440c91041d00000c9030580341c01a56a10b000410303c683c1c549506032040503103009000b49945445985540b4001d43c004164036401c0c081009403410b055001c081c10000400309a10060316140051800b81100d0400740050707a0600803081c7c8d6041201d4104985000d944259442c0c40c1d82001120041d5030340d41c80d02d00512032101d4010b850b2004c420f1002d4400d03c1900042140b1400d90750700090061b00044280c84644208240c1c1c0341031801003941d09980015101c00400c003121030049050501e40c4003034995204240d41b900d80210705507102104036980e6400040c5520800c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459735980 1250 459734730 459734747
    0x50603010b0d0c1412010c030f0b0910230a180c080c070f1415040309140307300510060e130b09031603021f0203010612090204062103 59
    0x70161a8a04000078075225446899110f2041c1c1302da0040e071600c103031119104c1c407550700031020602000340158485003500a00910701c0d50405e104d81840c1030071000e41031400011242c09510803841c07449205041500d41000388103881c0d1100040d4048160b804c4091b160904400000e1400030008100c19458682c0441501c0c0c2c145268800c01003c0710400000343c8a8000703a4401c10741001103081c040420b0300d40a801c01c1004411b1440501c00d0303228052440554910851003203120344c0d507a40003a41e4424160034034030102010340b58180c0040209216101d40010f4404a12a02c05c82001010802e03c107507602a41c85010107032110b40244000c40c103c0040740c003810707000b48040d03610464a880e20300200d0320078901500f4000d201d5a10200401ca0700b4008000307845039918003003400e03400045240f90103559100c1e411b80c0c640d15000040304000c80b401c0184242ca040325050745800c0140d0007071004c840010035249804a0340310ba56107001190070f45c44a54948035550300c60425211b0340f4814100505040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459737230 1250 459735980 459736001
    0x9070504060518010e060706091a010b0d02130e040b100605041508091006120506060f31140105040e0a080f0f0706020f1c0e07060e180a05060301 64
    0x40200420810642e010003252020320003c0002075043c0b11020040710f000d01c4010030b0030f50200c0d010079410f061042c16808240c001d44501c5400740009120703003c1c020312207401d214000c83c038201400070021068598000300b822210583c0581d680985030006070501000c223440640e000c0031088200000c1403104040140640014140f83c2e0901e03141641410a852882d01c8004c01c01290340040340078003200304090b8030800880c8206024494076038082c0345002d2941c0c482502e043c401c001c045521402d12071917a41c0054030103081e07900c16142c2d000540502c43c96122016080c0c5030981c100da103210083d4426411015845840020154940170400055407800d02c101243ea4110a9582000800342c0044844007114900003944800240c0341581d0a8010b40300c0181609000040b83d00851018200812700440984c000700c988051030790f0603900702c0d0010980940a41c0c003504080c41094001c0e8804060303030b600100004034881c0f644042c400d440005840d01400d49445806001c02d5180a02a058105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459738480 1250 459737230 459737237
    0x30b060111011506050a0e0a090b0112150b07030c241b080a0506060409181b0e0a18050a050c010816270b040f050a09020f070b060f03070308090907 65
    0x40607400f00034081c21060340b040d4010300100151114070302d0300500c0a4072030044001c004003d00e03039403180020080c024021501d40001c2100c0c110f000d02c2d800612501c0b80708a8007040c04800a41131003040000d40d4000c210540c140202c045e442000158800420f00031040180390b01d240740701c900f030080c1c4281c84401801d0001e02c00001c2010b075070b1380e5100c880f0a5002c440300c0f5000c111501d851002c81c10f03a2040e5008030140904114544d42100c1c144503410a16500c41c540701150014200301c00300f00f110890081e10a614503400c0400c0a81c82e0340e0708480384034148205000413155080e500c0d00d1909180640844440c1c110111454880d038000c241e29034001c00f10b14020103400404103000f017416800b04050040101c005550507103149249a03014040c1c4241a102c0d03030741b00d8036000d2886200300c179846090300c64210400c01250480e814000c1c2c0302d0348181310507810f040a210359500780d0020001030400e50403001400a20030340380d07002c0001000640c0580c0e00703151795007082e000b4000544d00c020f200a050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459739730 1250 459738480 459738491
    0xa0b0c0706050c10050402040e030c16050105040f0603090203011103040f050d08070c14030714070e01090b0a0311011806050d29060705160e0610090f09020702030f07030b06011101 79
    0x2203010110300c5550301c02411390f0001c0d00f0781d69071000070001c010014921045100224011420503000294400f13803e074083c082c4841180d07200011aa6403103240036081015440d17180412100b8003e030030201c4e201d0710040003c40c3d144c100717507152070507a0001c417019038580030b00c10303189802d11400b071203032680c0c0010516146d10145050382001c2c190341c10b1580d0090176403a00c90050f5681c000180300b680c0d0700c554007007a045604284581d5043d60b0b210070f8010400241c2605000040c008a1440350b01448074020700702c12361203851900d5000100140780560740c148055510303c0c0341190b2400ca607100140c50151101c640b1111110880720880310314510070310744034240300304000e01d580c1c03140000100508200d5501d07564000c9443c1003402c0080e4480084070390800c500c0b010404001c5821050b103e0002039030018a214181c03401120305100910910b600c3c910840c0051083c5903d81e00245140c0b8000780880f541044541051490980c495200751030840c026070a0215030340c0d210b04244891800700b4003d02c003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459740980 1250 459739730 459739747
    0x90402030439051005070203150714070c060e0118060210060e0f060d1704080c150304032118081e07110402030a06080f0a140313050402090105090a0b0c070605 70
    0xa030025240202840313405000c00c01ea01551141c021920202c0d8042e041d201c0405032240c44418544041d02c000003c180400c0c41c0301e40a044a20030382d801590000420f000725854090280c3d100501c0c0d40072203040010030001d0400708442035802c24000d000580c0100183c0c8082c12105080f6612900410040312100c814006401d0041030f843c0e40101c0c0403140080d81d00b00c61301e07194200d000b4103c50700307c090002160000d01107030003103800c207804003042d201e049400b1012a81c010143c4000c50f00103000c10340b5500d400007203401744c2c0c844646000b03c1d22000200c6800e00129103241c2d84000c002104c001800091030313884e1f00d24200031800f803440c14a0055007805026520f00c0d00542c0c2c4100e50900450340480010700c106000d1f003048004103001000d4460998010254a485800f44401a6a116042d1185241207400081142c07000034400101d0840c0c40d09120800020354001e1011504101041c403c0000070365440980d0300c001e040c40c1131400d6555143c94644ca04081447d4418418002c081c4034001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459742230 1250 459740980 459741083
    0x1407050a0b012c0a150b2106010503180c0301020d0209040f1b050f120108010b04050c090d02060d09231b0d0803061203030a020a110d050703080c0904020304 69
    0x502014842c190012039403105451001001240200303540b42c8451700c0000749041943c001824041c45c0c00c12017000000403540c845186d2942541d0071800558100001800c44814129003142180e04000b582d4180006d82c0009003a42c1081c0c1245426a500049035400ba2805102e00c0305611480e141c01e000201c80c4400400c01c2c80c0c507103050802440f034005102d106001d40c01e41250302000862203010b01c556110514103000b060310f004c0141c01036181c02e002c1041d01c0c22240554220a1700103011505e50101642400617a40002d27000e002c4031601c0f92034000c009000326034040e86066203401c09098820741c11340c1311481d182017280341031102e010340344141d116a06e42c420300f000c4c0b180e00700702101c2c0c0e25110306c1c000c607100e4051902d56040034000842400b01030600740e00204104405a0b4640c0c49010498682c251a52507071528070010400c20403403080000e005038081503200800f056140c0c00c0001d10004103040c0d90085400b10749058141000000c041001c541000340a500070341d441e1002000820441c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459743480 1250 459742230 459742289
    0xf010b0a0512030301032310090b060901180b03010e010203040516090e072d15120605130908071b0306050108030909151302040e01050a12051c1407050a0b01 69
    0x1030041810101d410301040242c401fa6107a0301c226030102c038807407042c030040c0320000d02000d10304464008840c00454075510300008e01314140c81c400200c001e1520f50404d802c10007400c3c40301080c3c0e0155255a90070040a01c00c1c406184100d019901500d859115041c850600c030f2005e401c000130b042e00c0d001241951140001e840d1041c0c400104a14030307030030b801c403400f15000300c40d0003c00ca800614560340498082c4110100a8100415446090500803004440400d55050b80165500000d10450030714154a02c0d8100f105c081d800303400134502d442c69503254845a4442995048104249030004104001892040c2d030b0040c04058083c5040025020008503004000f03080030145a14810344072085581c0c003580440a41e9060303000b1580c4a07900c0c09941c8100b1743c24424244620140100040c0411510b1900001c02e5408005040c0081c84d030003e44813511000e5080030301700700095944c070003000c140e100100315460041004220b032906900e000680840f050701300c00105600181145003884011510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459744730 1250 459743480 459743483
    0xd020604080d0b120609010b0406050103090f1b0b192a030e01020708030a180902070203151005061b0f010e1e010b060a110d020615120705030f010b0a051203030103 72
    0x854100281c0e0f0000b04543c03010010440c49019944c1403090502056001d0303220f001007640d040c4000c03640c40005600b01d800080c809488040754103c0b000000e0000000740b090451101c2051898a403141207045454000b2441d091200c001d602da0103c9083d08020800303609100c8071000d58041c4000007146100c64040c8000609000c20310a41c0905d607070082c010b9101800400c4222a240c42060800070108844011011400c50021802090000d1180216412a0740141c01080e240303048110820440000815400d1001e541d10004100c40d039880b40102210942000000c03d001010780348203040010780d074414803c036890014003003c07204001c9010000c03001403040d021848540d0045490141c41000c1146a020400180d0780402a07040f6802a64110740842129212546803034240c0e0b4801d03041d216804d040c621607128050310702e040b240403180b172850b040c103072268165544007081c0390414049108844c0e075150059050b1604101981c2e2000f0103085034840041812045425200d2006000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459745980 1250 459744730 459744757
    0xb0a081f0302150a27030c0512120304080706091a0603010c0807050c07090e0d080709080c1e090106030e010b09040b04330603031d010906230d02030103050d02060408 73
    0x560021301c034054107032102e2040841c1c041541040c1241080301142c0d80c5400102d4060380030b460301083c90f0402e51040c9001b801b101e0010140d148654002c00c00640004008884110b020814034000135414001c0000e0342e446005201c80c224400f56100c42c100000409c0c60b400f982c582042100c003264000040c94000d00c2900f071041d52a001c148901e810301030710790800b250990414209086a00000408802080f6182c2e01c0038402c0e12101c5c130403030f1201d000e031007021541d50020821a0045c5402c24144101c041031084204080340e0b6180811080c070402d0380440c0109030343e092060312000080c0501c094282c800c51700a025454907030b440d40389002002d031010340441c207440054082009484100311144403d003241c86401031100c1c00c0b6070050f06c00d038081180098640300c040c07082011944030f9034442445c140c60f404035a5041110885d13642d42101c0c3c11405d80c01c0141101da030445030140c0141405170011402598942c1582065454800854203500c01c560040c41040049015101616601030b1600b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459747230 1250 459745980 459745987
    0xf0d0e041b170615030c03180307050a1209181b050702032a091303020d080609040f03120204060207140307051c0302121602010806060a0215100b0a081f030215 70
    0x10204242c0c5084500d07881340b85200005001420042e035001e0340c42400c802c0e10103004c031560b2201070394480c010210001c210354000c101e95000030b100040b182d00c0308092468a1001c0075540c1404402c4540e4000740103c1450b581e04c0040900b1240414021104e48141426458a151980440d99480c4901005803040f0907030285001d00e00940c0386110b501c10030050000240b0309080c50039041d049000c2000700d0143c4904c6441d2051640900403413882410010450001907460fa101c81c04c50502c10442241086811040c4c0c40761559a07101620240220740e000f81582424808601102c0c1401c1c0c114a11983c059031041001d0758903d030008609403404481c50201d65101d150582c40c1140701011404010400710b000407181c0004034402075000e0003642c55286980700d9100784085442000c41c07500068002e00c00d501003c40b200c20007190802d080e516100300311940d4820040454020f0680a00003c2c10b840510010038942509001450700c03034440d55007400d1444c0e00046d14210642c480e00d59652010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459748480 1250 459747230 459747241
    0x703201819060f0e030109060509070e090109080412060e06090307060f0203090c01110307230105100503030306120a0f0b2a07060f090b09010b0a0801020f04170f0d0e041b17 76
    0xa4200e541c41d039034880b800f2701c814180908010344071341c845e004500c80c0d000c60b007000442c4024140640c0b4107064000407102d207090705001f00c42407281c180388019608240c1355440c4200c41501000414840c10318034024544074011480c141c82a9695400c22000b0b06005006104030384401042c403c80d01c6400342000341d400070b4508889800e5000d4080040c2c030706c0d5002010081c0444a6441149290301018020800c640d01e4208108a90b030340b6009168040e807003440010240d04202400c0d0403041b988800f15850000030355549000456100021100d02a400043c0a00002c0820301c00e03d81c01d01c01032010b03060360400307070341c1e59250700a8540290296845400d20221200c0d164040400c254010300805054a04a80310074083c042020300c19000d40800c0b600018544c8041c400c1d035224507052000d5924043c506189041c0c4a1a40c00ca23010103030150309481c94080500b00001240741c00c050b1240482c41c1c0c2c00394200400c8881500d210044101820510034203c1d03408055070300c0700488221f084840c0c0e1500e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459749730 1250 459748480 459748483
    0xc040c110607050318190201030c0807090509060612090f06010807031509080c010203090c0a08030901050d1a130507030c09121b0f0308030f0a020408060703201819060f0e03 76
    0x3107010b145c103806910034640d000100c40781600c549074003e0b02c003030040704440001101c42e108200c98540000c0c10786002400946401d001454002c4002825942080c0311004074055200003524007002951160580814a110070301916006100300005090064a0b5482d0fa40f0781400c064131800300d066a585603402041200810b40b0022a0141c00842d01d900d450100269603104158105104020f0f204001035410400011203103c0c92040c3d540301d091180c00070509002d00194595014869035000002c070042c2c032007800040601c10829004542410300d048086d00310f4070303040f40c281e00300726043c0e01c1440680150a011801e10394846141e001c0c80441c018a0036a8507195008400090000c2200105000d4614003442c00b440c045042c4c000103444001c4480c042b80b04622070341c0c1c050340040b00091041381c001da01c03000a29008170070f0340d01c0c0800f940003440e280350f1243c052100402011040e08649040ca00740c54664003550748181c4d40c14a0800102802c00440c4c628501c0030001c1d040745143c0340703480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459750980 1250 459749730 459749761
    0xa090c030311060a050106020c01030b18040b041e02010c0818060d020a080603030a0c02130b0d0b0115170109091a040606061107060c030503060f0a03050c040c1106070503 75
    0x802401845419880707140003808190018100200c0b4400c04011450b800140c2c41694101c60544e00181a424104c0d8015009800800d4003203502c028950400089031000d0024030703100303d09c50302c450545890140340a1039032038110760100705c035071032115298030041c4d030042208001d0903040a542502c1d20059800c4110003400b00301501d4011130049050385035541150040e203501403050704d0790469a95450b050596074085c1041d9180090700d54925000941090b003400f10340e003080010040380c9020034502051207000e105404440d58003441d401007210304c0255400d940701000510304001140c0408041c14040081070184020865407015010100a020400f410196482d04080d60503480c0500b0007800601c0244200c0e000300e9a07100500e031501c0700116103013007690781c00d4031482c900360703001e0300d0445240d0002040c07260446841000d0a002d80e07103c461481c011440f0b44000d0070903034180414401a201007c408000b0710901c8800310000700c401042c42d0f030b48001c171413410a0b2241d9a51080030518030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459752230 1250 459750980 459750983
    0x708030406080c16030302090a12080f030915042907080a0c170a0e15100e0a0603021f14090604121e0302060603070e070503060d1b0f1a040e0a050a09 66
    0x9041e130000c1e00806806402a015045045491540b5540d58807981c0007640902c501c01400b034001080000741340001c59001d980c121711100101d92044d182d040320030b01e00b903c040c1c0b4141c03803940f0550340024102e0601038a400090079500c00d80003141c101002c02810815014081180b02612410341501032803003904102e030740444015041106040005011000f010309000c140d1150092251b040e41d203101c180201401651030402094800340362954030f6038054400f5103200c803821f03168103001025030394901100c52038090403020400c01e10101d001c06050460000e21501045e00241b160190690b40c20b000d4404540004801c18560f40b07551604900c0e09800c4920320701c03940d21150400c02815400106544911000d4003100d0700c0c240c9550180d03061300c100300d44c44000940104009000b5091070305403100800d05c514400301149c00b0200d002c84c0903c1341c5404c1714401c0d2003601d00c2000311605400001c108203191075805441c003400e0891840b00000000c121000040c0c0f60070208409413441d900ca41c413801d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459753480 1250 459752230 459752257
    0xc122004030605010e0105010206190b0a0510050a02010b0405010807030f08220e060102030909010302120c062b020f090108130203101e0e0d0c240b01020f0708030406080c 75
    0x46403280b4148006090a0150221402107440081115400001d00c680910f0540c41d0700030004046542600144c142820700c2900140c001c04001003035240e4551500e00c200b82c40e210075880b0501c0314802800c54510003d4140720b1400c1100400c840d80e070120741c031401d50350002c400d00710542c100e09004010344580810915400800c0c541c001300801403ca903c0c0c195851070a0042c0c16489113001241c4d203004203641d040c0d1101c5441b00420040ca00082c00c104864494411340707000703d00790000264540c11030704021600300d41254041001c950700c2c008001c6002c810510450400803004140d5640b40034041d560341c14000040d01269019200108042c11268000c0440b5241c409544201000c0e144000c140c0b180102000079042d510515800348880d1402c80000030007116041680c100c0c0c0960b0800b00640d03146c14000503184606880e544000c148000d000720100300780c043d24000a113810102c03800c400154000004c00d00130310001004a400b2183c0038681740e00c1d01d494a60030180c143c896586503408030f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459754730 1250 459753480 459753487
    0x5101701030c0503160506041511010504261c020f0c0708012c0c10050903060916150207140a170607080a061d040827030601090c1220 59
    0x4001c403910b0500196a001e03401c2c1c40c28180d6840c0304032080d080701d009550340840709005c1400034540584001c03080d000e592801101c40b0748620600c03400c48506541c1503444141803518000c14072019950040c44611904000c0d113084405880a41c0c0f294143d00c2c20000680c0010300c04034440485000e072400c94503450143da000e00c3c0c0e21204d250003003001800e035070392190036505411a1a4501d0030861150240c90014020100c4010100044035190f40540c005011051150101a407420011980304d40103a0340182503120121529040d0b20b074144e805105000000862906003c3e40400c18600b2a000031500c014041039031070008600c0007840d0010f101d28404203201a031a100000f03101809081c0e151a0660035488508002c42640c603280240c031020508400c0d1401d2032a03103204180e901c0380c0035003401c0c3c0c1400c10601c2e040c2d8890070550111304a00f44c114290520524040c05084c1c0140100d441c100045003400320054103140240898542c81a0b607026990014110036524145000c440c07908a07a5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459755980 1250 459754730 459754733
    0x1a070c020a1710020702030307110402040b0706090c080c0604031106040308070503190306050607020112091a0109051f03080901030e030f1b07030302072102130b280510170103 77
    0x600003514000210b040c41842c03c400c0d40450248226800f280d0084c01961400d2160f450b1814140300b2840041e410941c20072001598030507800207440428452003012034011500e060080844500b604040415046124913811a941d500c045a0441760300642e10380b00018a500020380d9030107203900c0688821000942c0c2c0d001c000c1c0c0071008060440c1503203a902910040c2a00c00c408070f81d03d0740150341c0c125004000d071f00003540c09840910711035500b6480100b1401d0f46a540c000300511108005a400c2000ea4014414203005001c1d00703a0128090031841844182607078200380148a5200150180e4000a4290f1140e4031030703008200c0142072032086983c0c80c00c1c0b04404815a81c0550803440240e0a00680103048541c0403e40f4801ca907015401404850708009810000558a0740c07010101d071003032041030005844107540554425190b84000580d0350308501800380d1150001107191700c0802c60491040c501403044191016103000360340040044030342240a0700c44a495400c00c10460307000000020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459757230 1250 459755980 459755999
    0xf2903040f060516210b100306030314071203050403020a0b0f060a0603110406050a110d030203041406040201021515040e0708012007150b06070b0901060f031a070c020a 74
    0x107180304900070442c81d540c52507024040c004103c0c488001984c03003800550740e07842e0404040881625201c0000b4040c12900c00500707810145220140440d8813480308009040d04600f4420782881480c41c0300386445107a5403580c1d0b00a082c0190202455900d03008681418820885c0c0300025612501c10300e294180b40c400c00c000308000303c2c1d040d8032507810000b000c07815a01c40e0281c1c1c0045200a00c140b41054201001914550041d07190101008045000c24858100410000007440d1883d2070040e0b5900b0507040c03488800b031020400300b82603408007041c040180d9000aa416183c3d41c0c1e48015035854480c20000380c01c40301d82c05601540603081c991414200b0001281103c2101d04003402081419000c0c6003400303a6407a03210650381044001e0140d54040740c09034003d0380c02104e40030380001c1c41115060000301c058000c40700075038480c2408010401054824819030000c0d07c3e400031100d0340d5504e969102a40c010382d03207042040301ca080b0804140e006006e203044111039075005000001036920348200c0c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459758480 1250 459757230 459757253
    0x7140a121802030106150507060b0105120c0d060b0906030a09081e1b0a17070201210203100f1802090604080106080f0d0333090f06030203070e010f290304 68
    0x140d00c254038000340050040c586c00c1e140641a112500c41c03a003004031a4540c14000c1c0a240d4500341445030800117100450807036201d1610030355441012946440c1c075040d00e04119419500149040c1004104101055580400303499000c0c6841102146080c0030f0b1400e00e0705802447c0b5401c168040400c0c1140c55440c44001900b40131841c10b100c0b4500000000030544d45040445002e46000c0d0307140c980f444e0341070084009113198bc2c01810954240ea00e0750001e554810404c000d5624441c4c0d0100c00e101001480f00d0100c00102429880c1e4a9041d0901e001c1007a160306a49118680c0703940010010704c60384659040c4d03001001804004c0080c56540c2c400346486010039003020445000b01d0100c0c00d0031900903c03801788203d03e00c688608003c6c0000e005208060048400c485140d8004000003890070036038042d903a070084250b071020904a15600c141403030308000360440900c015a5100621001d25903581c504225200c02d840311705800900601074401c942c0c1a06d501c8401d890000410083c1310504000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459759730 1250 459758480 459758483
    0x31e0206040f1e0e070503090c0d0624140d021c2a0b0306040c050c070f06020f19080a050f0a03021305090f0402090901060815011d07140a1218 63
    0xd1049001035000701102d59a490080000200004d40403402061140f0b0145521104107c1101c650b6025040054034121100004031501034603800443c05080c20541400c080a0440c072000c0307040e50400c6100c441340c4d016516400c0c041c1404590000566840c04400c040100e5400440c214684050400c921545a800031003007120b039840940c80d4001d50302c0a45042201e05121a890440e1580300401028050503440c102c1044020f111418102009001d000300074118503407004440c5103000c4002c0e0074030b5220b000011b46a04102d0600c003600340e514114036041c0398444020307a55004260b20641da01c0c0540c42080040e480045107a2a41540580c01420042c48800040144598550030040001030843c1c1e61601c40411101040050400309255504007a994002252050b1134499140c84d08141c0c481008020160000400091880310001410345c03c0c40a019400741c50b2820000d4a90340349034018840da4a00010500d031010b104d0164404680101c88013070090070096625006081100e000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459760980 1250 459759730 459759749
    0x91503100b04031e170a0914030c090f040201170106021609090302031204061b051b010504050a031101140c13060207120206180d0b010305012004031e0206040f 70
    0x200800c1580000c0141c0742200e0b03028803520b899890002c41c114840583d40d0382111712050404501010101c800701500c2c0c3c00819680300d4040f40e183c04d0b40b0400070340a41800c2e901a8000e41b450820588503a0402540715400d082b890750b00d0784840c030041700c4040089406000c00d0310399100124400da404034920150b0f2a507c864622015220f80c03600049600b41c03500100564010062404174002a1109643c4240505c0c00080c800c4040302d00341000001c00b42d1048000780b00090b01404441560004d501001d00d080020491443c160f640d9503a1038668400240a204182c44030382e103001c0b001d400c0038040c1200840440d03102c2c10601441c0c1c0b01c0350880808040c000303040880108042d4070004100c003c5901039003018403000400c1c4c090102030341c0256964903001c28000d21403401038841e003840ba04d21a1040340201040c0d803540c1811821154044880805c01c01c8249040316009011811f8400303807500078603a000b4403100242e801c0800e6000b03400c000d41100c4040740003c0c420041141c444201d644c4141c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459762230 1250 459760980 459761011
    0xa050f07080d050910120c020109020405090102072402070f2f09070c14010903170705040b0a030c0309020a081c03060b1806120a0606090816031106091503 68
    0x544580e282c00b2400c0341e00c1c001407401d00803044946000e01c82e04004801070309002c2440d0310001209025912410704000250391251005801c5051a01c6030703e9103e84840003c60501c43c542d80e42072118031690840360028501844a10109c0350701c3c1d81215151340c3e008904035080b080502c2d090505652a40c40041c221a0b0000c00c03194820100d20300c140c5002004005000d01d50303800c0c500780c0b80100c0c002800c2d5080c0e5007030000220781110900c520043d1901036110340741c01d50f0210503100c40046000b4003100c10081c00303000400800c1c1072074003950118021418042100e0f50212800c800901b048071000c2d500c04801c1714001008a00480d4801100040d1510340d030b100001c1c1002903040d10024030821a41c604108010f840c0f455070740304a84d000b0180244610700e400c07081c00f120304246005480303603000030380d82e14020410150031505460081c071656000d0320483c07004103060a007441071803101502c1d00f0045059420a5921041125a40c0d0340003011440c141010300c0000d030396030700100c400d038440c603201c02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459763480 1250 459762230 459762239
    0x13020c0604140105070c030f030914060a0b100504270504110102010f0c080f0405070b0408030a080610120b0a0902070b040c0e13120c0215130e010f09020702120a050f07 74
    0x6000303a40c03103101e440c0c60710b03961243d266804a92403002c40e068681003650303c680460001742a05081030213031080c2f10092115050416014040342d8515102501c2004058800700005402c0b509480481d84442d035205118034041c050550721401d10900500c00d42e14040820080000709030300d4a280d041c0a038000c124480c044400801150074982ca540089560040001c3e4000307002420154410b00c0740043d2100ca0f41d48070341101050300300d42c010302c030f00b038001140324030035268007c41842c1c0c400e00860f00081c0444880c8005130080780035152605e4080d881e051188165111082c5003801084800011540d03a041820001001507003034908695194220a001940e40e8031001001e02070340329001420340d0881d9642d2911150810441c0100c10700c40352007469409603881000f070300e1541c0d65040c00316903140c42c4114148a00c40681d00302e45501c000020040c007222041298240986010840050b42c9402038000600c013180c44000140c1303207200e03195815003040f0001c9480c000c01038280301240c1100e9100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459764730 1250 459763480 459763483
    0xa2303011518020712080703050a200c0c090c04050a050405070f110c030d030501180e120f04091a030d0e10030b062107020f070302030c040b13020c060414 68
    0x4001064800c0010460240181c6080b4084000700181c01c280041c502905071342c85141d044043e2400c0380c0403070304820821070640d4040c014282d000c0c50151040105150a84083c0d06445d4000d00c400d0441c02c0100302100900010086490541c00c010160b0800c0e2400d02c208912070307030040c000d082c042c1d01c00b0f540000d20b9007804d0203100d0040703420b910341d0a00d9052002007100d603414107c1066295224040443c801c1d518180f10118111070b466501103410741c1401c05403000000c001060482c16850030300008400303000803810001d02c211301c141e4280c1c5e402c140800b501441c000c0d50000010545000c3c1854184101d5031701000c5090001e40640e8071500e811101600c0380d00140d0050b07a0000101d91124509503c42c1d0700c4840b0900d00284580c2c1080040d40c4000f04191548005501d0101d1403824061000d8040002c0304c9041078140003040c1d01400c69001c00e03110110344070010701039510340b094400c1c2d80e91040e24141d8001e18544c01103480e012142c020540e1001305a8050303030000580b14030025400c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459765980 1250 459764730 459764741
    0x2b050114011802090d020f060d05011509080f060c031009110c12070c150302160309050307080f031c091b050405070804050c09040215180a060203031006030c0e0a230301 74
    0x82c4541010345d0f20b50280244201421402e0b64040c100b0040c00204070440d10845020f170920010f080c4514450321005407080f40d990704060010b038070500350821034003030000368a58004810391513152203803501c40451101001e86e810080c07100d410f00c20719500450004006c0c1c5070f00581b01089031407240071400c9400b403030301ca09400984842030001c020700024110303010902c024203c0340340c0146040c2c90b40019040c2d201c0d003811708a000034403103001004585820007901026000e8032024161406041ca50580d9a1141e0100f400084085c40f1600350750380392a0384040a0341e5000001c450030b00404002d1803003540340300d0041a110b240382c0302c080350003207104c0e800c014440e48d07029008108220b140070800001c080010000c9034000c02245846403400f074003602601e1010085030003160701110b00f2080150801c20303034001100310340c003d1042001c0340d215164450b003220114240082c80304103540d4110f4280b9a100c50b550b40212103803500262000041c1248500fa1a407102c101c60300e0030105013014269071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459767230 1250 459765980 459765997
    0xc100509091503030d1d1203131b05120304061407030e040209030a02040614240322020916020609010b0603010612020c1603051504022b050114011802 66
    0x14811000640310000b841c841500d403075801000c80e401c1100640161060ba001c00c0f030f0840c2e0410110362042c5512808000d0f11500c401940359003411480d0138848140711032600c0c10051302c9a5040c5105011030040301c20440d02601e80a054503141e05005032110380e40e036101e48654800980300d03101da0280046200d068440d6580d02d9550758880610280801000c0c3d00240501139050240482d18401682c440c4540b000501d45a0290b882c402d01001c10400d25440c99501070b5544001c468003002950480c0b02125031045074004055040038a000c0f0400512000d900e0080d000780c5140d0a001136407103442242045207585034200c036626603400700c880d03080e0745006a00c15000750050005000450160803100740010b01c6c0300c4c005052000e84111030786448160440d015240a86500a1061042c24000950188001c0802010900305603001c00c400c0c1151501c40300f8440c22410150b4200c4a041002c00d6071507030044000d014041c00d48502407880e580c203100d10511703030410080080f09007580e0f00a407202c0300b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459768480 1250 459767230 459767239
    0x1315050105060904091a01091a01020a11100504030b0c040f06111c020102090303040f0501020c060408100c031113060908150604020306030109020604030c233d020c100509 75
    0x59040c480a00f0300000308990a480100e0041ca06c00c42c183d0380c042c000e107400030b408104440445049100e014a01200300c0c1103400485c01c1c1c0020420081003644410002c0da4030303051006a8040484050003203420040c50009014140304a00c8040300c05001607550180c0c07000170640d95071805035810604000700b01403a8200c0c03076001c041c1107003488018031080b1041c0005482d20360000002811a0301c103400c01d500c04100d0300b07014406940d04004005039501e054806034585410032500550361107001042003102500c883e40114114400d07081548800d004000241d21104111410f03160341c0e20794025503001503403015000407942c3c4006440740004100c00883c50090b11203105100c00b82d40000c0a203609992602012001602c94500a200460207540c01101140c01c000b4201034801d640001003002080d41310300c2191683d1004030244120a008940319946190444141c00c0c88400c0300c80d8800402c6100940600d598020414100c907a40071103c845566040c8901943e0724040e18072101d420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459769730 1250 459768480 459768487
    0x2010f030c020708330714091c050c18162601060f08131a040f1209030303140405060613020c03190e010309020f01050d14131505010506 60
    0x4038003036408400c040c1181d1056031242074884801d01e107030542c4820510784c5074040c0c0c001708161603840c441800a03002c00720701900c03803400c0c1042c00404050040d4001760301721400162034011969200030100110b8008030b0080120413142c10b00503200c43c002c0040c01d00070000c03042c0900c0f0b40d0303120155851180700b000541c0c0e0400c1e00c0042089580d040038803002c508200c08000710080e00c1440d40c0c1243d008000075558040302040d030040042c103a000192040d000141000380e404006075803207410841c00140c0c800b4180340c84d40c3c0e0f810150607090452602401410b00c0302010103001d07501903542d0301564000e403001d0200c132034043e528443c05501154040e05980024001c40e165140c407451000342c0c03d001c0000581070075058055a420f5601500c0b58219011810314109219900710562280040090808010452040c2c001c10b120f040d6081c078890420200180550500126030700c1856184260348032800103242a1005070300002000205640c51000030312510b03501b06590040605944000e05450304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459770980 1250 459769730 459769757
    0x1b0604020a09020a020f1c0906020601050307090e0a020d11190b0318100f0603030908010e0607050a02030d150302040b090408090603040f0f052a03120903010e0307110f04090201 78
    0xb500013004d4142103005840c08510b0031442000740c0120403c265680150303031510580040d02d100c4a130391284042d5000380004001a0350302107400801c0f19850a408038103040c3c400b02d200c2c10320261a1009502c84001152001030040e005c00d5441402400c0d42c0007a040c0d14000050340c00c241c600d1080f500f042d80c04000141da044030b21003624a2072800282243c0c0300064601920b400e8511450805420320390b1440d0810038103505c07888020040000500811080c2c1143c0030b502d0310707580000d2400051140000c0d20152043c03003042124215904110100503400f560003000a02e1503143c031059110f00d0403c2041500d514103c0049070199500c45c5849140148030418810a900020020fa50203c206010310011038a06440354030390b20301c42c80103802c120320107610002c41d0640b21031200c4003c0c01030035200c400e29100012006c0000c003006803415202c0d91b40c0320000c3d000d040d00c01500080c41c00082864800c00005100c154005001210309503446514202484111411940040e0006590800001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459772230 1250 459770980 459770999
    0x20d110c070905330613091b0302030606180a151101051f091e0c050a080c09240403210306060e1003020903070e070e0405060d0203030a05030c120106051b0604020a 72
    0x20078074030f80070f03104500300741000886421b000301e42d60103002010b4807030980c5000e0b40c03a5298100302c4082541421403c60800f000410720034000e05c0c41c003282c0300e821a40d01c24102c0e0f840c4200300005000b040d1700400403032031008004180310590080c040d480d601703010104580e00c04020888020001c0828001c072454503184076440a800e2041d151508841c609040b47d400c05018007800f90704280d01e071506540c84084540042c08100300600c580d203d070b2014425081c2d1503440c280017900246400c805049641441c0c107800309644981ea04c0100b5145d40e01210b0380410880100105004015881c00c10000b0ba41d07500607164004440400d650140c018080111454025405460342c2800072303085030729268440c071203062442d00c25144c102c04106080700d18440e42c9001d0150680c0410300b07507014002c20885a0101e0b41d00d004040403e8144036011002030040e4581d0000c3da500100f02664030010f40d40c3d00c82d03010b0442c2d44013414074289018030b580e8860070301400003002c1d0f0081e540036008500ba10314240404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459773480 1250 459772230 459772321
    0xb1f02120901050319241d0103120c05010b0d03030b2403190e060405010204210503040e1e040b0a14130204020f0c031206040606140d020d110c070905 66
    0x1040559803445e806a035486c200030440b1a1945040c040000d070b5085c6030501d081940406656900e03400d80340c0061000501c1440e040d8000042c0e03040c480031038901442d10a015118814035a42c001c1c0e041000c00050681c036802600301c010082d01c00ca26031040c00c5655550303964030507100004403c03003040403401c280d079920150b90041c0400c01340000d40d0894100752508204013503409888aa4003c103050107600b40b014403840500f0703400314506143d103c3c607070f0b28161607016603c201028480c02d58002402000c104003402c6045d654003c44001501d041d14280c4903403030080c0c0f00ba1000b9840d00b800c8540c0d81c0b032118840b5000f4900da2075804610030607030b4200302c0a5480310405031004401031087c010200b6082002d886003420091300d201385031420724244011118a68419010044440d0306c40c54082c15074003c80703120300d00003000503940b492180380c02c0c000b5108455009070200030009010880c01740c041039a4083e45c0451800788620b03103402052070011200200441404400e5592403800300041d011903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459774730 1250 459773480 459773521
    0xc101404050c010f090320010201050c0a020a0b060a08060901020a0305060609030a02220e060105030f031e0f0f0a080f07030e0709091104110a1e080a050a0b1f021209010503 76
    0x9082c0320341c480d0307500d20304d444010902c444071f09650351821080e580c0a014040d4007a0381200c0c0c840c00c210702800c0095966a889802501c480004004140d058860042200103040c1c2502200c441c1e00b041070145000b58000c441c9000002d1501010130030701e1034881c1c00c0b20001c0d580100141691290354007048074000512956100c650182aa000c1000c0e0b2035000e90b5004010000243c6610342c5410b00303141c28118110551452a0001c01c010060500c10620100e004c100241586444034aa012240300303d1081324031105c100240420300e010700e10f1380300503d140320f04100c290306035036500c1c0d1910660070b60300250500c02050b001990140075020707241d4441295a070203034000d01c454001140c041002c4410a07400c00054400c002840550943c001030f0319020380d10902c1c2c10503030b801c080600041040c20701905101d1850740782d40100300c00d82010b4010000c20b4134010404d2444601c0d4040c01021071b200680c481e4090700400041d0808508a4025100d0310201038549038510313650300440c120030202c040b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459775980 1250 459774730 459774737
    0x1309020c010b04050907081501060f050c01230106201f090b010f150207060807262a030c0a05220f030b0603030328020f0c101404050c010f 61
    0x402c015990360007168050b4100c90064054541804a2542001e0094000b503040c4200d00b001003104a52103181c020b55a0768518006032901400c0340990302400085006404032421403424003125081402107a040b5080d58031000001f1400c1d00014144c2c180300d80745519280c000c03000c00300070804480c007200b00201e41d01600041010340c503680d524110f0b8003a000300807502c0b40080184001102d60240032203407000c1d40002c1545524040b0000c04401000741440d0030006d619100480d0320202e035001c21400f130507074683c80009181441b04440c01c03103900a03801d02241e140d545091403007445c0804a9019030304005c60140b806040c070340c1c00e455030390103044080d80038030700201000710504400845001425201282c0a03415255081000c020000a05010b1194108100340301040d0400d029006e54484140e031031a03044191804400300030300800705c201e8410300d80020110400100410030038204e01d84c0d158201f040c092085c10f0140c4012044070005d11a50019110070781940c05403065008600040c038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459777230 1250 459775980 459775991
    0xb0a140616050732130e010c08060a0501090b04031707020901030303020d05060a150c030905060a09240c080711060d0c0215071d0d0f051b061309020c01 67
    0x1001e410080d4115080e1459000490b041c040c0041a0044074052440904550030a2030f01410150b03009884404580c031401080400b51314114003174011214074034121000300307c0d4405c042c03c0076013a900129100c47c402d2038014800305003580102d0880342a15140c40000e0308003400c0d40d403040b80d08140c1002421007000b0030310140005a54007d021806588030f070b500581c480d42611164419110064800e41c480c6900400c1882003c840c40100c655251451a2205442c20503043c10f40c2e0000e9590803094114000040607000301da0003034540c0f812100944160510768503114880d6102028103d0003000190440c041701c3d01181c0500040c0c000140141010316481102130001102a80000c486000aa4070340c80d04400094041c0900d940511030411152060300e030881004100b500004141c203581150000481c0c4281c50710202070300180e90085c03142c80004210f0603c9030380c4070441d20110300c468903e40c4c000111420f06009035000203240040070b482850078000c00201a4115041442c0559a40c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459778480 1250 459777230 459777247
    0xc0a0e0d0506130309210f031116050102100e120a05040504050114041401050328050601091401081f02030901090f110f18010e04050a0c0e190b0a1406 66
    0x14000c25009244850301408000b01c2d0380b401a0841c40d451b8001d08103441500d08114052000e1446080038039800380c81081e5034001ca01c0c4c25900d40301418561102031040285242018081d25800d40a81d0401d80031152000000e00400b402c8d1002031038180c0039034106045900481c0b0650004d041d890600f410524209030302c81011804807202603024403040107040020f0f00c6c66007464420700d14208186200305d6001d6062101280e550f07018904060a4100c6092950040303007034554180f1800c59021003a1512075960300080d0b03002d0a41005c0e00510110144e000140d4203070002200d034a2440d0180c0346407a9000f058001d4030003904014040f080d15500d892509002400c0f075080070480c01e10541c8514035005000c8103014400340c070030001c540903241c80c2d590396245144a0b24460304488200c0501c500702e0b984c603d040c1f0308010350800020044d844441010507244405228140b0403441040200f1918040000344020b4a00541140e900400308031010b004840310300c21609080030f80600003a24000c0385 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459779730 1250 459778480 459778483
    0xc030b101a1306080412050d0b0409050610080607080c07110d0f0c0b0403150b04091407140a061707051e040504051e0a0504020d021f0905010203030c0a0e0d05 70
    0x41e01c200a1001c50005541c04000c1d070801ca5442c0540040d107022501c510306a0341e0500d140150780c05000500c00d02003840325007200150410340d00036074050014070466040b4a0556a5640d0940303032503251118064000c126038000091844c824001c5950712a41c6444020310008554000c12096a607000320482150311521131a50a68060f0322840e034036910380c4071504194401c0314081d0010000b03000100001c0000c00c040c100c160f0b1400691a100041031485400024028285000c00806024641c4001540110007040c80411211030700b5000325400100400c000d4900f0b100e008050102d00c0140c40000f20f05542c00b5000d40c00385981c20400d14010f04c0b51070540b00803070b010b03c4030711040a0000741404a420135018040d00500c00e00e0300c01c0a1200c0d20360b00c118240d00010807000046a0700c000013400d540e983d401c1c84550603005086480c072a040408d059031250f00072511207021400030301c40050315510000c203d0744520703d080025800c10910a40071a8045040c1e141540d2001141c034191011400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459780980 1250 459779730 459779759
    0x801120f0b0f0601030c0815130b09010e0f0c040b0f2d13090501121202010f06090207060516020c0f03030d020406020609060a0204121101030e0f0c0f0d0c030b10 71
    0x14080900b440c00c0c82c00d4400102652010300c4407800700031088080c0104001112522810007034121480c05150340001c0320b0400030309010040d5039105048900000340d0007075080d10b0324081c1840300704498003a80c400c0306451903807146100e80c202003003040080712110010b1002038810360100302c2c0d0107800e0602400e40c888403200c1e5444074411220000800310804404003c8940007044c50520500c4250300d0901568010030303103000c02514190000b9101e0460718401c3d8001841601c50b10390802026469207480d04c003d4101e51000c07194140b404000c5140f440c9100304440320350845500400803160100181319407000101b190304d800d4032090200021804040c000380c40541400e900402d1145030110b1002d162500143c14049102c1c03042100b032112441c024250071885400c07008100d102906800100d00614160010080c2c90198600240c0e80769004524610a00c0b421142c840455145004010502000f1500204552a104402c200103002c0140c01540b102d120b19140700f0040d59484e501911382c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459782230 1250 459780980 459780991
    0x4092102030d0f0506030d051b030403030c02120615060a09030f1505130804091109030f010506101b020913050304080601081005010b0306040b061303030903061b0801120f0b 76
    0x7000400c008610500b284100350010843e000300b40305908010012a4407074500c08042c0c0200140002d502103403500c4011019812980401240c0d0b65a90307034100104810380b50b0340104d100d01c1d03544a011304400d000040c01401003c071040701d030008240c1c2904105240d80200303801800c0c400d170843e002022401820310091620b0090303240c4c4289081404001c030403240018003510081c1d05015440010804807030a45003607803c0d40320002101d0a186481400c5030140c2c0940c19858070071070502d00601030b030642041d0b00401c4159200c0060401404041c2c4402c84105085403400412246407005450884001600480e0203092181004c140b602c0c0c450550748944c0080441e540b00c28010410396008018611000b64034500c1004a94104110200c2c0340c80040d10701842a0f80303a6031488007607a50710007201c0380c008014640c00c0c1d0542c0e4038680035042002610090310104c0c504440507c2604400741300b581c08901a907103150043c2e090074803e003458144070038103a034441039620383c2d0310002d1864005c031405031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459783480 1250 459782230 459782233
    0x30c010c0906211503140c0103180b150d03050a020c09061810030f080415080403081f0b0414010e0609010206010308280504171c11030d2d020403050c04092102 70
    0xc400540c01034034040702e001c140c504243c1340ac240000a03200300d0382d2041c101540001c20881c203880e0161105000c00482003c0765008030200340f50000c0540280060580c20030302c1e002c7d20b01c4813845100700403c460b4211000340d04000c003031200c1418803649244450784100e40b51260768001c0c0d00d0ba201d5400740080010215103203580000c0c1403101c4c402100785181158094648100246025900100170400c0544a40384e071071190904074802100e0030380c80a000e42400030180c0e4a407a83c501026004400b1248000d0200300000b01040042c1000003c9500300681a001010a640b843c1d070b403101298402151095a02e000c0f429191000c40c20550180d000506507550384e441d9828062404042c0700d0311402ca6040345c1c490540303002d04000d1021002079000d09410064444c0b40b03a01d0286080d48540d148c07070107085141c440d1602603a40f000f850548403c01c416899119601d480101d20200d22403400090001d41c05410741c0011032405401c508003451082c0585038a840400d0507502c640203c020500016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459784730 1250 459783480 459783503
    0x3020706021e1b0a150203060f040c0e1801081203061311030402040f2009270426040b0f07050a03030b2b06050c070212030c010c0906211503 62
    0x70348240380078109100c190303a0080d09a40c03c60345e9515088050941d000080f10390040b00003046079641c49400c0c0c24141d8054403e1010624040c8002c2400c0b0034810316502c507071508400c0f90341281c881c001b042d043ea040f040c0204292000d521400d0425000202580d40c421413100c642200743d0005c0c0100100140700380301e099141e0415104002c240d031b20144a60512515103441451150b05c0d6440440014003950026a547e5240e0004030702071841018180215807101c00c0381590900e0700702109841140907034480380c508080901c030341490700d04901c50081c101034144000c0c05045000c1c4018100c40c000e406400780707450203583c4d03000c6c00c006c20351900340c001c00d5680f2000056400c01424105060310078011800b06013072100f0f510002c50180c040040c00013651480001c499090006c100d40d0829002841c1088040d455416542e07250300104850000303500300410000c4240c0941c2944c0c0503103030592104444020b8082da800100414a00304041d1140c0fa003650b070750704808240d5100051409820308100c4e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459785980 1250 459784730 459784747
    0x30c0309211c0f1d01030e011d030d0c021609051005100f030506030d0507030806060c070308030915011505090301150605040f0b030906130f060c03050a150b04050103020706021e 78
    0xb03155401038000d040c440c0e000301c10942000c0780c0842c40c0c0e041320242000103240c100703002e4030740c01010b084804034a0b1100642021311144400005410100101d00d070500800c2c4807240100d841303c4101e006224105c6400c0001d004140700c60f08200da02a24076141c070407a031582e620008800c681c054880801080080d01c5c03e82e0400e525020382540860b00703600600d42802c200c013004141e1720642002404201011000c0b55042c1d0b600000c8900d00c065482c112000710352079003400e80300c96100341e64800c0c05110b00018203903010701510501e41260040340c00f00a008203010400e5075554400158158995038505202e049050942070314005801d00341c0d5000d88039424048640e400701e54a4200c141d0009041c010000784541c0042d51660001031101343e00034403141d81c0b4000c00c90b15030302c40c0010b14190401050307082d040d50503888540301d02c00b061414060341c100106100940380160040c41601b80007080140110f50007a0001c284803482044010301d400000e0400d40005030961400325100400040c1082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459787230 1250 459785980 459785987
    0xa09020907090e2a16060e03090306010e01050a0b090f2d040204030c1a040b0316031d0a0b0712060b04061806020a0231060f08030c0309211c 62
    0x2507000200040741c009502503442d50b02a0091034010441000780c0c0002c5d00c1842d0020120860a0941d02403014003142d9101180c00f51a038116420f424001e00c510b8000082c50521405014101d42c03000c1c000c0319400d4100580940113502401c541c58001281c00031107403c07615024140c0711100c0980c020b240115001e205c07030307494400c034020a880c4914014002031010440d804545001c8403030517615800031f0b50660705880c41d0340c01142d0000382040c4e408410450021030700884014110214ad07420060b001ca0400316998800d181603182e15590b012092000c00281c2020003031b40c000c440c13800c204200c5800d02041c1c409071152500245003209010808104054000c503013200c500000b180300701c070840e041c2100295204803620000e07101e42641c3c451001070784a00b0444900c40540b01a4440d1601e0010300d580014080520516040c3c070311031003000602280c04029202d12040c01030107140342c842d402082058a00c003120916075083c80410112194050420000d072640f0000c1d10b41880e030301d441600c040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459788480 1250 459787230 459787259
    0x60f0f0d090c090c05030619030f050d030623090612010c02010e060f0108280b01170f120a0305060a0803072003120715150b091e06040e0a0902090709 66
    0x20f140b11403c0c001c40ca00e4090b005016260b1040b4140d400c2c61002800049a041c015820343c0040c000b6003402d81a0f100b13000b008145081d504140791001e0200d241d849040e0341e034411244250b428800b10407a0a16098542030443d250020001840380c420460041481404c540c004001c00003d030b0355403180e8908140781444216403284400798000e140d5850908055250700c1e8158150015105c908035034498070a0080444038001d030080c2c0c54007040c1da122160840149080100c8003901d204501c0c4003154080002078031025140180350701402d203445520103401401e0060f29135a44418076003401308488208002a001d8103000d056000e46009004401c1c81d405031003240458001d07008005100c2c0310104507011214410342c418080c05480705149607403001414800b03040b070240c0d01e81003c00a05114090040c5c441580100c94520b02400d003450408038008449501da50001024441001080d06692031554000c103110004070350111264002014003a0448862011400d000420b000260760303002c50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459789730 1250 459788480 459788489
    0x40f0e100212060d03120507080414010501030c18270201110102040e0c07060216111203030f01052b0b0f070c0f02041512050609061014060f0f0d090c 66
    0x71498002124a82c0800e580003d2146004c0e51001d1055010580714000240720070758250000c104070305001d4002000c4141c00c0e50280e4101d0340c1c29200e1480c885042c450366048a45c40a1842e0303e140c944071454165081400780340909540e00c800c2404075100300c4074606072400c0c40241003690b040803440054841d114005600860b60310502c0b051000040301c03040b003a0484204440d450304c5001c6491b204e0046e111360280c2400d0a18416041c0e0b080290080c0c560321500c40031600052807242110b12640d5901040350a01f070910050303001000182028944840420031300b046418984d448075100004240600c4011550b10000c00c0410140004e1030a04035000402460981e5404146484640c82841c1010001c0c0c8101d035140344860003220440f00c7c5900038140c1740013201c980b034007a0900944032801112440c01d940900000241e10341c100c80c907408203070380c50b443c0f0301240c80c007203007003800700300d410514003c1c4002000b0881c80300c1125044028011240310318070085151241490441d1150486900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459790980 1250 459789730 459789763
    0x10501111908220305030304110d060f050a0f02070c1401020111030c1c05040305030f0c04050d0602030405190b0c2a0a0201020106050301021608030a022b06081c0e0a0302040f0e 78
    0x41132001600110440c3e400507000803030844c0d0f034000d030070009a102c0d0103070800414003071070805c1c100035640341c03030700614802c1107001000c0107161100c0c0354113400c1e44258080104080380b040024081008440e210819100040c8000100710741001c050342c0c0d09502c01d840154082401040c2100a001103030748202c80e03d590450140406c0c10590303405829400040d00450004280c0400116862204070070780e00107004c010800004c0c0f2919050100003540241c40c15280343c002d40080c43c0342801001c99405440390b0241c80003800d030341c031551203040603080031800c542c541e1100841101900c001f4002c3c0400689024050040030007140700182c2100c4096110381d0090340184400fa02044c40f8882e41c280c6240c0002440303541c0d0f554808928001d118012104468000e0f003414070100541d0b404ca210520868040d0802540da100c1480d25a240406900c416500008220042c00c46200b04400304640300003400d407050068890b4001001e403030706950405003c5550b2404000703440780804c0750074007140d0080e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459792230 1250 459790980 459791047
    0x215090a1e02010c0b0709050f060a0c030f030e010603210206071d030f060a0e0d0c02030a02061810030507020d1b11011704050606180906010501111908 67
    0x303440041e000641c00d0200550a0803005003801d69024042c01000e0b01d07404681804113141c50f40340030704845442d0140d180501508450281e46040c454110394003452141c0b240c81495000d6030f001c80f04441c204025078205130f10340c00d6080701d490003409488003551185000c0e4902468518001d92007803158401401194420000c3c400d0080d0000c034040124001c1246440300e91501c03070302181c5030400904001010384102000c1000d00345159000b0703480c0c90b85000a488800140000071144610a41006035154101c25103100052502c10002e00808001487ca03880303a2300d4000000321b00c100940101000300392520b00b000300c4140c0c140300e04503050001d03040c021030002c10403805062203422140020f10400600100d081240e002d2594116420605440ca503802d1a01d490200e40310041504e10a003d040d02d008440780282d4a401101d00c5088a00700800c01e80c1c0c038000044039900900b080c1041c0c0ba0144501d800f100c1c9880d402c028800e580204000c0350ba8240381d80300c1d1240c1c010240710715841809001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459793480 1250 459792230 459792233
    0xc08030a08070512060609151303030f0503070206060d060b0409030e01020c01090807050405040302010e0a0f0614070c2012011407081308130b1204020109050a05060a050c010b0a03030215090a 84
    0xb03c13050304a6000e45210307842d01c4091002c00c03080140d901c010358903002c020842c0e1078103010b031001050581e4401c0d500e009818001880c103880d24003060b10b240b4007581103600010020700700061003059860081401061500c41d05010800320707441c6100c01c1e00000c400c0240c254095804015402c43d401d002e2804550310340ca0401c419032030700706900075070741b0480d20b0b880424141031007500003241140d40002920072220322071070002d150300c0a4010443d042410070400d042d112a10303a2949100b406d0315140c000620780c417583c030000310345800c03400c0e02800100c0c1c008040c06a1200c8480c00910a00a400010210449551540c1c210801080c4804215540c410403040743d0901518071074090303205604a0302e480411020070303010940340d003094184000100e107038540c44c1e1315034901074040d6000380c07110a02543c035036050180042c4036000c0c0680100e001c01c45504d8040c8642c004000815007000001005903a040c0010b44d40069075100768010b078008000c118001041461198108060764001c0c810446907 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459794730 1250 459793480 459793507
    0xe01150e190203060315130c0f1a0a1205011d0a06050d03120e15070807020a11131401030b040519020f12191b0b0705060f0c04030c08030a080705 64
    0x1101c80c0e03803801a4000c400b20316561010045204224401c0003a43e04605d08040a1341d40c8117010078050b10818a40200040c000242184580a607000c49003000803408e10409072104a074081744455040040120788920b45414a100d0035000e0f000100e005055014100313100d00c410300019201c0d11119107810030800044d41c0d402d500183c0345526040c200e02501503c14030b50024000c00818120131b0246114012443d4800301d26180b00300d6041d1150b003803507120442c040381e8a000262004005500c11171048046191010010100840c8490701241d06542c6214403081d041083c0c0c004c0701d114868100340410451b051000d0b0100c0c180e19031070390b00070750050303000115001ca03c1c00c103007806030710244000e1910403400c2c010138444000e900d14000e0700c05220310780311b4900d080025605240c1d0001c0d500102c2d000b20580c08175009160000c00500050b00c904100c50186000a40f001c1d10800d0100710000001d41c0d2404040000c0c1003080245441e45032020014000d540028002001c2090800929241c86030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459795980 1250 459794730 459794761
    0x507050a12030605032104060e12010c02010b0418050c04110f0d060608010e0403091401091d100f080325050d020601030605060a05030a0b04020418050a020f1801140103020d0e01150e 80
    0x22710b4500c5140340d1030000f2500084000d00500b54550802e0110024142c05400030004900182c408002e900b4492007011910401c2d00c3c00103010340c00040c80384c603c034503290f08400b410300c08003c2298948006515135840b00d40c0f05040d07040207542c662004010040c0c20841050041c804100c00003075902d002e0b0380090141c0c400d4000e542c4000106402040e00d07034840c0d0403a40142c0215003200f04c4288907140f4440e4071034011600203e00485066000c540c481c80340400301c08480410740114104001c0400c030a010450020414845124040c0c00001140c0308205a040070750207600603145030350450038002e00b5a04000c0c015801010209001c101503200052015403040d000000b40546442c1da20000d005000610348001800e041c0700e10a4007130003004540540303810320803900c2ea4200c82c2c900d000d11402c00c042c40300f0003c203000120010008100541103158030b20700b051400602e0451502d92040c1107a0703256004a43c86d1399146208404070365604200ba0140080c080c03801e4407858640e542040d01d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459797230 1250 459795980 459795989
    0xd180e011a070503040909060b10091809020f06040b0304110103060609030b041109150102150c07030c0317011701050a0608100b010306030803010305010b13050708070507050a12030605032104 84
    0x4078001091818404284190b0b40900407040c414444c00c082410500068010b01f0015481000001c0f100c0c041c00740541040c0044490100440340c102c0021078842000740708980060381c1054640d160f40080b0f0b40d9960040010304000b480042c1c07241800d040005c0316560035510036061501d0003105000e0b031034008281e1000c5035032184440c0305640d11860703c907141c00c019101e941d400609000900c02400305e01180c2a2440c0402e03801c03140070811074508400a10815114400450410444800820b10074002102210301904150b44c8503003420110b0092403400760703c207a15000c585626403000e190203015094101010704001e20a0a00b018016501c0303542c0b802d5000011543d400c101c03040359019411080040d0380000c0c02503200e61396814814003800781a804603100340c010001040d0440c040780709880c0181a00d98441c24595a00ba10640d030a51020909035050303c00c20010b50002003058000041c01103560707402058440c070780000e05141c1440401198511180c1c0d07003034083c0b03540c00d2205540854 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459798480 1250 459797230 459797279
    0xe070603140a0c120e01020a0e0d020918030f0c0102032202130f0e0a06020301061701151218110306062202091c110109050a060e01080403110d180e01 66
    0x5286036005640b604c1d080c07041e0b818018217100c040d0074030030410b6010700390f481c0844d181c81c001b40c03480d4420425041e0000d94000d603c80d00c00408207450040c0b0820620084000d601160300d0007803411903420307103070708104082022690000100182800d2101c0045e14242200d003041e000c1c80e0f0310343d0000390340000c0d40c1d80c034003030b00c5a840c0381d0b4080c0580d0a8001c04c07118075004090310f0b04101d86051800196100340101404100700300355010200741940031450486000b0b6444201c44681c24404903028989203075100c0c10142c5134581810041101e036000320f4140d01c2200c0ca6104198a00145810905d00821b094454060a05120360320411086130300102561404016500d1050380006078000511040c4180c2d07407030140160004001265450102c80b0500340c035129210742d65007041010034a0039001f05400a00303000908010fa50080c507200390000d01c80d0400380660702200410300e2420704004440d1000a800342c41001c11000400d6100d405005010043c0340700f90b042414441c4c1c21081150304000342c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459799730 1250 459798480 459798491
    0x90403020d11070f03030c060606020a020112050a0b0a08060a0c0f020a021c1703010603050105040c0909021c0e0a03080c04030308060d081903020c190201090603150b04090e070603140a 81
    0xc03020a003c07400107002121005490b00e901c9080c000d122250710300085500c20715081c000f1843c1800003401d132140590594664040e100389109941c007419003d07140703401c02e9031654240707155076070b5070b400310005006110002c1208ac6400840c01c003d480c2810080c90600c54100c1001406030307400305030100c1154050301d41442006a03410f403081d042031209000303005560a1114990b4810303510004604aa4040d0340a00250740c844040008032200000c0c58008903990100070030991610380c02070700300a8041c007000320040c1000c0d125601920602e275010111034100c01104410980c10007038080c0c0080c41100e00b14280740c29942c0182c0706403c00f800203031081d0b20110868013045640c0b0704680003c40c134180c11600d03c145090010340650802096054a802250104043e20b031241e840c00d00d2640e0146c0d59003907442d10b0310030183d00804105400c8410754841c07040c0890318035030620080000f08420000081c2c547e00c2038840c01d0601c520340d04800101810030082421507065515000c0c0c0080740c01100054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459800980 1250 459799730 459799757
    0x1104090b0a110f0a020601030b1608070818120901030c08013c0e160f021c030f020f090909030412021e040504050c1002010e070311032503020f090403020d 68
    0x22078041d81100070403c0c88006080c088050340800c115048074840c0f65110015104d40030001d02c0008410040f20000d0045400610300520404881d604910000246c1c00b00f00040400c2d24141805c010620040c1c40c40018808000c0d6854894207100c00d805d40382c440b9265050141008120b01c1540700c00c1e08084085440d9400c130304942e01c4500c003131150070a5140b42e441d070383e203410b44092808030f41c500c1c4003c0381c0d600580140d43c081d101c800b0322044142d001d400c900403442c072400c504003a01244030b8201542d5801c00020190144014003112001104940e2034505031410401c3d5804020300c0d40600b9001408108800411985c91a070855811546840e07800c2081031280b00c1d10111920f101d0f4000c3c280802d00c418090040341d40b1302d009000781e8107000340c0d03421440d09900fa03031000c42030b800f900d520241c010404144606d40c40d280700d400c01415507240f5001c09081003448070031642144031001c04204200114a09078024880002c0103130b9042540b45882d03100691510a5800ca400a02c9240b040894 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459802230 1250 459800980 459801011
    0x150607050a26070605070201111914160606080706020106060504031e0b041110092904090507050310120804030807050c09090c03070504090203070b1305030105131104090b0a 76
    0x2c81d0420480119503c50300c0e182840d8010344011380e500f10142d483d000d11220212a04821607014140d140c44040b101502440211401d545511041c400707208180a200d012048d00710241000724080c88000c51100e0400d4540e900381602c41c0e0004056a26002c8200301c0183c01c04240d8049030303008080c1e800e94010003102c4241c1125600c60080006d80141d0810040108a04642850020035150341d501c2c8000740304207640302c4045004428001444840f42031700b241c40c007950040c1c1001290441401c00307507681200c00694000b42d60300750100340d02004010314860710603452001441c450041c403030791070460780390382003140329500010340000d10024010003482070401803655807040c05041c0110903d081c030240c0762602c40400b440c900c28007030f40000044030305e868050300c80d060741c0003000741c4041c1d0300d081250b0f420b647c8034840700040c001032200000f505580038414103100f842e509211501910312403401820551016040501c500c0ca0300d280300c00403a180c150513a0b80103120200001c0c4d00d0503601d4601 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459803480 1250 459802230 459802283
    0x140309100f09120308160806030303160c05191a04200102030c070f090b06040509010504050601120e07050a090c08040312090c1706130b040b2d150607050a 68
    0x4800441038000e030303081013544c003020b0248039005602e0b08000c3e07070501110486003140240e0b030391ba81c154020f0010500010104003800c58612090404440b41b842e6981d07030034100001e00034100143c0c10851040c5007440540e955582d590300d2140a01581403a142d074420300c3c40c0c2c6820746c588120010506942c07549900030002c48080c1c2c40c4e010300b140c00d0981e460081c0050440c0a0040411007401c200340e800d560309100c3c082e1010b4540050013000c0c0c6030f0a00c2c0901c4008d240040000d030403c4404c1e41a0800c0d01c4c02c9204060100302c02101800581c0d0a0000380144401581e00c8091418582254021503030342c0f0045580e0004e505141000e8018140d07074449001d42104d0501800110b565040000d40003441c440d03d030000480f2100ba5040c40c1c0e10070490031540c40c15160040d0402c4c1744080010001843c0b140b20503840300c0f230300c2200d443c0310040e88001c16815101d184c0c120905050001840b148910724a6802e0701b40c1e10480381285486000c1c0d1701c040d04c0300021540106072400800783c0b42100903010415 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459804730 1250 459803480 459803489
    0x1052107051c0f23130c0b03070c031b030c030c0507091503121806050d02070605010e1905061003110906210609040b010308160519140309100f09 64
    0x5001e51568510b00e0000200100c0340340501075490207420b050541002d0421030612008103540e00000d81e0341600c141c64001e0001c000f02c1c0d0f82c80c1ca0200104003080f00b000510b004400c039607651042c1c008103140262520048100f42000107151480760030020782c0c800092402e050b4907150404020110340384c01403601185401c10170b071702d60402c80b081580383c185c0e6400310100d9024402c00c4e141e440690900b40c030728036600811103d05161401d0203005007405800102240060100014503003a641e0711010205c0d6800c0c0c00001c84c040d610010f2007080f00c1e00b0709080c0e044500040c4208400d050200015103040000c1461506040e16180881109074414050322480b0402070702c2c85d41d440074003080700c0001c4c00700b0341c9101c114000e4020100720b0740d040c101c900c58400c95005031046050307402c2d500c07034406940104030000f188050b520a0307000000c03070078040d00e007501c01c0e103442c8804c0c0324403545042d031958400420310950341c1e8000c2c804c07181c00b80d443d50001a10741c03549041c941180c0c092000700700c82c000c086403c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459805980 1250 459804730 459804757
    0x82211100201140f0106051204050c0402122706070f0201020403050a110901080c0109060309050f0d110c040e0c0418080a1206140a0e0919050a0b01050105210705 71
    0x865865406401c84584914032243d0320b0150b94400160403030740781c0c080c01030070000303031092010781240543c00208036006400b0380b04440d1080c0c00d441c005000c0c0c5e401000d510241d00e80100501c2410748040c1000401464030444c08505400b40c503001e99035542c8010601400c01100703140500c0c00300c1c000e44c111000b5503045000e0b00c02c824543c4c01c040c0120b8541e10781039805902c0d900c000050351400811840c000303000507910302031114900407045014040d01c0c0c0054810f4041d1110075010880204007000311500241c64100c3c0c0602002c49070390611090200031401142015100300e00c010001c00e03000b80f00302007100c000490340d40c403c0c02004014000000108075010001d45951210b8020344050702080c8412020b014440c0c0303800b00a070041d601446000c0d008020340c44144510312000a5081e404200c800c1160740060f0a00105410b00c0340c0b041b025103443d04600200002d00c1007140c03003a801341a0a00f452803030607805981c0440740a40b8103003070121000401c0040b41c001c6125504495038103204e0003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459807230 1250 459805980 459805999
    0x230103021312050c1906020a030c0309170f0d020a0c03020d2909010f0b01120c02100612060e15010b0a020a020d060b01033803070803040f080c01082211 67
    0x2501683d03500300040c103684a0b01071035005c1a0741c00c1c00100c00100f900e800e9400f03004a814142c2c0d0544212100350000ca003403200b110400703d0342c01d0b1b801450400d00040300d030040010000c0d0180c01e03030604000c62040001c64108086590204220b0359000701200d078199401c80303024038641410500c410030999528401d028a403c456a2882214030640c06a10034030020842a501035240400720741d10000c0081c081102009610404803241e4000e40305603020780161801c81180b1092541102c4031500020f140b91044003400b010b01107030703201d03070b09111a03004020076052040e605248140f590501c1182c01c501000203442c66124803d210018107280d0140030079100d801c0d58980107000e04000d088050000b880c0c50403414855903c0d18245042c00720440c00744010a41c402400301d0b401d03d4404002c0d41620504600040f06d0314100001c00003040010b00b10281c0c0d9050000341400d000c00b09241c1810480f6a50501000d0360b402c0300803c0a040c084560301c001992686040c50002010740b030b10310f41c0311810f407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459808480 1250 459807230 459807233
    0x11409010204081519020408030d1803170618010b0409060b1e0706140f04021e010e0f040608101b020607020705010c30090b12010512030d0e07050a230103021312 71
    0x101900341120061b070240096507081102211031007401c003010f0000340c49240c370442c440f01001c180c107801c81e40c05800e81805501035503030a8001d081c01c0e8003200410300c1c009010800c07010b95104850203000c03101d2000c1e262207003142c8485502c894010407002c40900024403002000807582c0a4014090070307041d04006468800d030f122900c1d620444090b406003c0d40542c602c0b0007404c0503256000310f5416107804054610080920100c40480600369030404e96a4801045a08080104080e03441e94079801103101116240a9402c0465120000040d5801134080c803108540200320385050b80c8003031903d58551099070070b24400c0c080308601550001100a00c0407440c203405a80c020380b540c14103440f030009050355089860041e21810344011402c030340c030000500c0700c4c0c0340c4010b40e003940760b030303014100c904061980300a10110b0b041c1c207803012401c2c1d00c0143e003000181081103000c0c0060040c500c03401c4500758141c2590191484a046290400d58000344440e42d01c040900c03100051301006807800d040000360b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459809730 1250 459808480 459808483
    0x1318020609122b0c0302062e080309101404060c0c0e0718081207140307140102040302010e0108090d030c1404030303021e03160c0f0b0702011409010204081519020408 73
    0x300310b03800300f040f40d003510040c3d5481c0104c8031125440e80c5580100440d41d220000140030300a40750800d1410301e8144c0901034071200da0500c070006094000301071a03884404004000c21a10f2500303c5400b40300c0143c84030082140020251000c45a860030489201d049138a418041042c494200d0f0550b51154001c0c020072550103240034446c40345511481d012103844400099aa5106141d402d003116410010080050b0141e50b905110b0319441044074117128541da01d0248206509110b07501d540e42c0030400f0410344da4440310001d4800428200715141c1e04101c4519a01c07044668541028151629843c000c0303944130342103419020616040701505d880e01e03032400602940c02010f482080c81d03880c40c42020b500c80346800312401000700c1100c84424003a9071900340d842c0a44244140e41c0c04100d9100c1e0b60101b42074400d428800c00311603000180725054940d1007294090003801c2000c1907071041c0002d00100c00300047c407840b0f015038008401c0296807010303040d90203d00124042400b4500100d03000454010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459810980 1250 459809730 459809773
    0x10210051303030501060504080a14010207020a171b010807080709030c060f0905060306030312100b0426010510140a05040603060204080d020d0c020409080c0105010f05131802060912 80
    0x2c296001c4c0200e99a45504071000c0c0600d018140103604001e446000203070034281112410231140c0c00260038401d01c6c1c0c0020b656519254030801111191100b84054640300b401050940c070084290721211030b40a100082503030364010014424014220301050106001d0701d0f02c00011340d4040c08a035821f81e1507841c001d000c980d0400720a070220795039000c00710742481c0220a5a1040700050011800c0c454554816004032a0242848140c1443e0741c0f00840d940c00044014000b421300341e0910500c00c500d1a401c4140c0009400040e000341c0d2400091144840e403400c40d840840d4100d013908016a00a680042c2015100d40d10140d80300f854240c00004002c402d802400c2250b040c1c8080c3e8400d0720941a05038ac42c0e18103034408000143c50072140c500140740590203099010300a080807400d000811b070200d42110f03002c0c0c11050059401d00000c1080d40340161060610b1a00e84400b84000303a03042d41324152604440d039000b403180c0c8010603840e0f82e0f920380300b265a400825001c115049003900c5041c92901c8c08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459812230 1250 459810980 459810983
    0xa03060209040e070305250e01091b02060415110c1603030e010f081612020a0c062003040807080c03160309050406080d030905010e010e061f0e01030609020102100513 73
    0x1410010340f050f01140100b2488203e030340010140141600715114068280000c881c4080320035485207003c03070302e141d10304a240d02929000c0300001d1f81680d60b10810b0b100d0041c0ca01130310110b60244042100107400c0300b98400000a0200000c100c03039401c2510140c280c0902139001480303206860000340b509018595a2048030300030349079841c030550b103400112034615280026401007a890f0000c04e1010710b00c101480307810090351404000000d00c2c411701ca0306903401180104000b0301c0d02146102440524400c0122501962081e1080ba1040401c550898000240043c1000101146c080d084c00070b40c800305c40711680c402068a9581c4080d82d0052045410684140d0006828000c04034003414180304083c02d603000f040c0100004218031100300c015242a500444580d500d6008100114400340610b070900551306000d841e040c41c1808407000c8a5401440c100509640e2003010019200c88500740c44c19a40c0218000c1060309007400143cac81c0400c00042c0703c0c0c00518220800c0081741103a101e201c10325 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459813480 1250 459812230 459812239
    0x9030206310905152128140304050117070c0c060206040c15020d050c0a060608070312050f090405060f060a05040501030b040c140307031506031a09061e0d05011d2118030307020a03060209 82
    0x244c480f42c0311fa646e68001c50240c1c5002c40c44905c5a510b00b2001c040000768001c0c0d0320700e0b0000210181c3e40d220441075600d5406440983e02000c10710003089a0062110b016126007101d10b04100c0b5011402981e440310011050180b1500141000802c0002c0c00a000f105806c00b0045c4010340d13a49a61580d00c880c0b901c419501c8842010f0300c03808051143d4101c0e0340c800d2004500d2410000f400080100805c0041c041070b0b400244414003d406071980c602928043c240c98881030384031032130500054245c400407100c1d54400e03850240c5012503240c21038540c0542030b03218041c032500caa481320030076030040c10b0308151080c14a403005030010700d00341c8c150001e40083e071400104040031290b4005102080400f59840c541c8214622140c43c04040d01c0c440700720500e80001c04403224160030b5190903007125103c10544400304070189a90b80b10300c80801492500d00700c03142d0812003514540030704000500030011a11113130b6400407104002030358100191b801d40b0b42c0007088054455540d146c0b960087d4048424030703028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459814730 1250 459813480 459813503
    0x50309040e031e09301606031503050303070809070305030f0405010311030f010311030c120c010912110103020d020f220801020a09030206310905152128 67
    0x201c070b410f0000d03038801d840054240d45140440d0810280a4601405480c6903403059074445412000200104d0051b2262211690615800e0603002010349440d403070448500001e01d4402c0000030b10000417a40c0c0100c07103240082c0d80da140d41e0103850400040f50700c0030303140744001b103540300441a0101c010400c40380d09803420801d4040122040105001c100c6041c55620212001000071409817840405c00c0c01004060f150205164400680183c45060200307545612100c492646543c10103441030107044994800c016114140e500c0700781c803d2041c00c4450401d5008170300400f0308101501512000b51820f4992903d441c8642075408000d00742488104442c0144d0b0000124404103208441c076030007103a07840f050080c0c215024010740d54004040305846a078004820310302c0120b1000782038403010204e0428003000745000c0304c003c141c0c1c41c090401188075400303c01032030b890b030707155015000003454400c81c030040c1110b00c4080e103040070070344441c80c4c81c1100d40680704075601585a054940702403294200644 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459815980 1250 459814730 459814777
    0x6060b040b0d0f05090c040507030204050a080609010e0c0a03030c020a03020612100605180f0d0203030304031e03151e0e09071a04080307080d021326120d09050309040e03 75
    0x3a0759041e05c01d98840c0e00140b0b0740700007504094021950090041c00c0140c0b0345551140880d951700e41b81d030721001803500180e0621054203801e00070701001c644004020040c40f481c0034005600480c05210050500241c40c0b100421034030360781e00000c003e40c1c002f045551501d244900888030324804407010a1100303a5120040785c001c0c000c1086c0d4500006096680070a1103161007030080034080a64400ea11000e01e017101c2e40160303020001940b2480c440c0d071740c05940d50f1403601d07000d0080600000c82014981030840d400444450100000704448074420441000d14096813443d00300c54180d00464010303000b1400b00825800d0018005080340d000002c0a6002070350b2003d00c80444c02075000e038a05641042018501269006019200100822000601d45004062080c0301001d103540107006042a594007190b510700d200e0f23009007003031080801900d4078507c45c4003480c4031845007a400f5481213560304002c10600c54100185c1701c6c40e20001e4030401030035600c0c0c403615680e600f05050900c8142220300d0b0700314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459817230 1250 459815980 459816011
    0x702010e0d030807050c030c030a260f06040506212d030f07080c1009110609090a050907030b010f0510090b09010e062203050d02070e040b0406060b040b0d 68
    0x2901250580d03108483c54892810031641130340001c03c0401c2d2403001380407000a0035028001010401c503981c4440c60707188594451151268001c104180e09500c5000400241510b000391303503540000200e4000450303965403c0090280e03010341c1c1f00c406140245c0002c2e007601c0740001801c86c02440b80c0c060000d0350714040c6074000407015100c01c04401c460b08140215a1400707501d40140c9a03251040060a003020404d026080c0342009447d14044070f00d4941500c3e00c24401d204c0304060171605d00b40da0052a0140c1500403c40180001d0800310380a41c0c0c2c3d000003049541c003406400e020b558030040b06034555a54012500b8070241703d0084500c180000325020750346600807503620b41115400034215050603403240040d51010700c440411500100100709a0721000a2003401800d030f80e64240c0030115480c11810052b2902601c0c004820a6607c150010701103141c0301302e101039100f40d010140340d03c5c5a47c0e514040c406045158810082c1e004049004982e1251708006170840d0002500100003150240c1d4151 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459818480 1250 459817230 459817249
    0x30f090b2a030f2a0312151002061306020c0d0201021902150c160605011806090203060102120d0204081504060c210c1e0309020306060a03020a0b030405070503060403050702010e 78
    0x703000074008000b03082008281464188110404000440c40e9602c115001350550341700c00c07125401d451800c005c200400704030f208a407441800a4030b80345013041894402035582e03540036200710207050542c107401d401c010f0f00b0b804840003101241c0030342da2940d03001c501c080c2c040d4201403c0d0744214040c155010705254400100410300c00ca07030790215801c54807050b0201d49994040c40c006020315600e000198041800c034010300d402010f00d41c03404c4800319207811812045030000c1d0041002540100b0902ca1280c1e070000e543c10082803040782080d601c100c04101d5800070300c1542d00c01c01060140350b01d00190451240b87c0c2512942c0074032414440042c54400031a07117245901124610b511480100c605901c4090380244d007512070034102108620106e50381c1280c040003200000307000a031600811030460a050102c2c40d0080d1003520401c96550540d4005468182603028040049901100060a000c41040910300600c0041c040e240642080c8c180240141e01501050340414640c0400f0b1000e820082c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459819730 1250 459818480 459818497
    0xa0b030601180b092d07200c030109032102040506040308090f0d0b0a0f06051e0a030c180b010c02090a020a11030c0d2a030f090b2a03 59
    0x648100c1e820040340b2003001116001855016540d080410b08949980c10b90070300900c21165000c58140000d18202201240120002491a083c03014082d2a03504000801c15903449048000c2c2c19040194040c1e00c2c00d81e0312102e0340d5056003407952400078550001c081c41400d0b0b45030848903a914030326210b22030580c86503201d801d4001e88100f00800100e1320b440040c240407030008115000004501c4005064880b5420040c4c0c2c100100c003040c00f410310594442c42c803900c041c034103041c4002858500040d5050f4164010030303884003559541c010050383c985940d0006541d01c42d4030344a0702a26084804848001c50314404249031034425400050360182d084151015802032444840c1c2c2c0d911305140b806500004180f4040c060203400310030071420700740042e00b8080d649030001c012500304001c000700842144001d0f9104e203282e03ca0b00b115112565030b03800300001d806082103a150341e4011411145800258044135844070085601c103401b181311100e6040011030b00c122040d08580074502035450740701e2290f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 459820980 1250 459819730 459819733
    0xa1706010510020304060f03021912320a110a121808030a0e010609020f180d03020a03030903200c031203010f030b09010603080a080a0c05040308040b03061f0c0203060a0b03 76
    0x100301b00081c0700b002d1b603104d000c0703240c500036051140e00506000340329400c400030008118141e00000855070f4502c40c4124202015030003164803d9081000c90f11142d2038865440180c50130300c0001c000010f40c0c3c0164003407058594000b542c468007c84012310300d0703c4a44090301228148540d0b07102c007410b40084100c00340e8000c0c07103151440d2a07100101004142000381c600240d501d90300002209a094400760a0041018820550f00c2001c44042180f00c01d10b52055882a444c0408940110b40d0000d0040440c1d541418001802d034024201601d00a10403403443c04100b03920848564030b9078000c1003440c410034045d8102c07586038600e083d180321a030109010301140d4808240040000c50300c4811101c1c0c20541d4039000140c4140c4070340700c48005034005403882020039001d01c1031020364003080c070400d08514003514010f030516042d40d4030f220052003a803103071031010217000c004148581d8450714060b0351001c3c3d07000944d404100301040540b01d00c20190003a072083c0601380000c0d051039182e0103080c030100c20050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 459822230 1250 459820980 459820987
    0x150108061501050c150903071403070b04031808121903110d0b010903060f0203010f0b120f071e02100b010305010f03060207050a1401140105060705070501110c0a17060105100203 78
    0x1401100c10f5000508035504c1071243c00e6035826052000f41500707004030580030186039160210309100d224180c4d03031b085424896004000d004003003901321031f41d150032551500d00b158140751104442d5884001c640c115045a01401200e4007010342c900c002000c1c40c01000e8826003190381c2802007501100c0e4002800726400c401009810311045035a071144229400505210002e5a107a4994500320740819500c040d02540c000018001085261025030007040721088442c035118a041040582c203001070205a40704035010041140640905003648280c214180040d24801e840318000303540b58540c0d20104006403070000401d6503035200e40503ea05a441e02d100700d216403491030382c44200a5020050540e01c9005071a503100010300c0d404c00c0c40c0d4884013110000310b200c4802c0226100d4404040c1c0c4418866842009241d00055000c1a6071040b2242402c1c12110000d000c860141005808000161f00c0140104049a110585040309801c1c9151108551480c0c0c0c0307840501c2003008c0d050881d00090790090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 459823480 1250 459822230 459822271
    0x110d08010e060d0b01081b0909150402150a0206150103060e04080c030f1315030501030f0b0405010b032a0901120605061c0f02010f03020910050c12040815010806 71
    0x1c0c1d11641c0c2200e40541000180061034540d20030713151080e0071080050300010f450822020040040e40050941107809541508115079640c1e5a02c0d91741412503c0e640980001a06541d185200c5020900780300340c2c42a9940c0b4016402500c44108840785448150180300300400d9511a21a14007070303541d803030a10341a584503030b03e81d4991504460800e0f4054802004044a14030005001d0250101c0c000009039020741480d00c43d00d07030286c40d810180201450200100f01080b24000e01c0302010f50807031500e9540b500c2e203052041c0580781c2c248006406104004548664600b442207000100b0807031072410040705400001c0080340d031000c0c82540c8404d694050b02c2e1000c1490756000b1500218010541c4045c000954102707014521004002c1d202c44c03900328420805d40d60484d081c082109410300c0c0840c900141c280004000b51030041210b000c00030041040302d96100108400081c545c02d020610f922030b5130301c2540da0b41c0d03000c0071040202010441000040d1811000440307901510030b4a48859030700308034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 459824730 1250 459823480 459823499
    0x901090302040e0703050a0c0e15060403020d05010e0d090306050907032d0b011d060a0b0a11012318030703020d0813020a030c080c0f030601030201030b0d061407110d0801 75
    0x3c09010042c003d01030000005441001044c5016109004030041185095011b5030000001007032200c80410204400c4801d5441c0300072602920303030444442d00c00702014240140180b0410300c1d052641c0c0300c1c5110b6850004d400264540c2101d01c910420700c0b07543d981e0080c05482d9401880000c2007403050722021908118986034002c103c952100d19035807520881d850b4000204020390044210202d4401000c0480d282402416031001d03007070762910801450021045141c4c0300d41e03c0c1d48410002101c10b003039405c0c0b50a4201d1034107500945403981480c606040d0010140b00d055948111120321401410858400481030b80d042c0d48d01368010b4a00c101401c401602c0c0888001d043e50818810f515003000103a898008140140d0301424440c4c0300c080c01d0080541c80c010110100743d1280404003440c2c0003541d0001040f5054a6082c44c01040950f2024003044481a59040c010328060034203102c2808800c030780017524170035801d541d5007443d490101481203440d12070760711021000074a00c07030051101d400c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 459825980 1250 459824730 459824741
    0x607091a1207120c03360804030803062707030c18030c0504060828020406031a09010b180a0c02010e0d0201050709060e0f010c170d060806090f0303130611040e060114090109030204 79
    0x41c5803100701c0307200c1c01b10358440e03030640d1184d0011205103d0220512503603040c07400380c84001d01003044250442280c0441030718a00c0000910650400da1164440c0721114420195000700794044c100303404c06c82d912031070440071040c200d02407103008610700340c00058425400506048070402035000402c10030800213190344505070542c400c1c3e8000d81c4403000040002c08603c0c0090700c6000c0460019200e051042402d401c3d612a40030b924841c6903500c0c3c0645a1fa00c01c45d550b079401c841d51010014000c0c042c690241c0c0905280b00d46208035000b40c0d9000b4001540640040e4400c028907610b03800d0f42c1d901c54030180d40d4100341e0055281c000241c01d989070f0095004903482d6010500440c4284000300d144241d40700c2d80c0d03000071032950210f521100200245803040021603041400003010307104122580040356568000200440307481020300d008a01441820b0740251035802c5401c030740590321030701ca0704111072070b8109880c034500040014440562030b00120055404143c0140e5400c000507140d5002c2101034003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 459827230 1250 459825980 459826061
    0xb04090c020c0604290f0702040c050a0509040203060414010e0f010e040305040308090a03020a08030d0f0203130b040f15020405030f0f0316020f03060f090f0607091a1207120c03 78
    0x6060b090f084403903616441c0a86201c3c1c2c546d00c0d02d20b6942d901ca00c1400183c5501c002504180501440030721511a000b1055600700281a00c0046c3c03203503149000100940300ca6a448440b5144003000444c8070580d04410910803403508920005a0340d803110750a41a805c11100540094024001840069054801080305102c002c14a00202d5101d8001603a100c03219070040c0341591001a0f00104100240281c1070702404007042182107140140107c1f11a82d100d480040c82c03100600001010440c0402031558900c2d00101818003035407141503c00c009500c903000e028824490804074249000d8001600d004c01c09800c0c01550601c81c81b6101c0c00a001d0841c3c0d41240e01041e01c4010400584040006c0341c4141500300c0040707030070b080040e41c5500706401221001e805070400000c104801e60080911011105c21030a9120003044503a40c8002c00d00940800c8203054114806004a1075404000101034141d0041c0800c0400e0414a082e02214500318010391020401c0c40202000e1000d01c4007084c0c0345 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 459828480 1250 459827230 459827279
    0x309021918020307030b0306010f1514070609031b15050c0a2309030118020a050139060906050103030216060e090606040b071b050d080318030c01060b04090c020c0604 73
    0x8114590000b410558240c1000c01094ad0b0b4140410a0038804074803481610140d081000c4010041c088407850303881028009419540c41301c48610401d840f8402691240940b83c0741c4000504082c50110800171751040ea10300480c2c1440c2c082086200c0c0c070011540c1c0ca05c0741ea210b01d01e00030491549034541c003c611844072030314201440305419949086c010350080d10300209003200e0558007031042080c000d4954201a04001b004106810090311150f284803d00484c2042c40100040d1035800c040070011a41c0300510550401085000704121070700030b941a030b8800e03000c0d60b0b00700d5091b00004c4480d07a8644103a4001458525490860b400d101d020140c2082001d0701d00da1400b41c03619590000b40e40404803c596111926482140d07001c4481c0c0303150040c2004540192052055495a00043c04090301502c01480384040081340e40d001001110350390407004c03000740f2566070344001804982c0c0241c400c2c403500c04e080603602c0c48100d10100381d161007541d00801c0c0604003400d110080410400511402d000e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 459829730 1250 459828480 459828491
    0x60109020f070f1e051006080106150305090a0f05030c0705010806061b0304030b0c1c092a180c020c03060f041211100b12060108031c0219030902191802030703 70
    0x113a00180c60301c4421140500001c0019000a01d00a000c6131a5a484851aa45464014403881c2003905107000c5c1c0c0c0c8803600d0041a00d4803510149401d10b42c1c0703040020304174180c0b004100c04203d00800500003007540300d030668080d00e5a900040d40d4581c801c4074810b900c20b1080141c0c0508140c0c01c01004a46922117040303a04058886e55841c003d208151660900c5417804980160f0b0baa4502d0300c2c0c24001010000f0a20090307000e99144e040c1c1c040f860000440101010f00c5020310003d401c00100010140001140070641c171080040f0010b01441c0b0308440140540c0800c1032590a000410fa070068010401080c541d66a544035070500520000e41071082000c6150074050005040112291143d1180800200e05c4484010488a4402501c1e180100d400400c0104034000011091b11808000400298480030300c0d040d90800070710845070003511002991070b1400103181d0580c03028110900c02d4642002c801c10035400100a481644584076207090041c1c0707114007111894019581200c80ca0401149 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 459830980 1250 459829730 459829763
    0x501121103131e14060702070e19200406030c0504120209090a1505070905091b0f07050a06200c03030712020c010509060f3d08100b03060109020f070f 66
    0xc040d103d000341600c10210071005035080250512020750814001d00040890518002d030b0344040300390080c1a40640123040140d411160100c0d080000709405044400c4d0401408248000ca80d40050180b4400a485c00d21500480e0740543c5c1140d080e118030302c0b001e200c0e41806034200310b00c20300c0c0288510001e01842014074009102058894a8480304400114591803c620010403200c9a0340c0210710031040c91052044100000c000c0c80408801c14540540ea030003d40b0210350503225011000f4018400c8940300b070b00f130151540c003102d4910307007003504004801c0480d0688001400740070104070442c2c05c1040842e00040c01100c03c0d41d940780025a01508207145407003002d085441c00c54100069400c00001c1240000c698400b55070b00c00246020840c420a00100c4c500c200c402c1803802c89400c502c8038aaa40000400d064040c000f0007680040702c03040500144e40c00c014085541169019100f4040049125a540e0081d2001c8c241d44034102414442d003615071104106001070245c804054a480049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 459832230 1250 459830980 459831023
    0x306050904060906051e130203070b04030302060115020109021315050607031d0109060c02210102030c0a0f0912060203040609080c030c0c0f0f091506070c050112110313 74
    0x9100e07902440c0300084103405401e1001c2690001080b80481c12079610f03085032070300003121b4000d400c00804241407452101a102180c50b0040d80d4000d4216281c0106d000420103030b0000d02c45040c4c440e014102d00345000410010f9080c0c6000c510000e41c4009200940045c8000ca0ba1006002010400360100b88035a154007143c003030f9000f46426000501c0961011000c1d0705c40070300f0b2210120302032800d40001d51421200034114075841000034403036610104041c8039900340704142c07035440020303000841d900d0030078103040c02c10740d030100500c4808110581c0e103d40305940103000e407108440b0302d11204101003c00c0e40d03c4d4402503000a10442e000347e034030044940490140c6019007034214168000315503d0450804407803401650000240c80b03000440401c20440d02c4103500109010710544500035981c030340b1801d10320b895012054868001380040b0f080380620607448820001c60307200fa260a080342c0f00b90102a0165000025404420041000450b2861100201c544503642c00b503a10301c070401c800c2441c1c21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 459833480 1250 459832230 459832249
    0x7060f032711090402060412021201021b0d08040b01051516030221071101031107061e05010e060a03030f090b2d0315091503030d060303030f0b030a12030605 69
    0x210070420000080070104001c02c0c41210120344110f90084040c541036000074a01d00c103901810003001000e541180464403070325402c1140021303c0c0c00a6458030442c0e400d02040c01c181102170300e464401c0c0c0c492002c6003402450300e1030045070003c5042398960f00f800d003407000034980c1e89456010004200b00b81d0070780c60038103004021024440d901a26001c005c40c03c50102a21401d82a803410751070400280000450722031b584001501e0070b00f40403414000901810440e402a0b0201034100b40c00c201c145180007991303103000c000440c221a010001a41c1790880d0100b240402c40d1a0360304580350070340c144040380c012160070034000310034a054141d240d00c4142049050f0003c8034614000404400c010b142000c80003031090340150491149411450a011148810b40702c0c1e10015014800c14004106018000b840c42070301c844004d0200c9555240462101c40104803602c410f400080c60310545040e051450702886404e18402001800320550ba5110b0030380c4100b00c3d07400c250a2594641c4009995264036999 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 459834730 1250 459833480 459833531
    0xf07120e0d030e010e011b02150405130b090c0301060807141b0f0118200402040f08030c0d0806060f180d05070e0f04020904080307030e030d0b04150807060f03 70
    0x40348903181e8a0000900005c8603007480c0d40c18040b10301003030903000300d10074000d00081d50103c503c0d041c95405126900128840c5401481c1c01c0900342c003860b4201d001030f4012960f404401d45840030300354ac4592202100e40802c1c0910740c00110701d900442c4419200340c00084814030102456031034615016090034140c01c0140329442c0d1600419992000407208bc41011101c051805090400b03200660f0384640c1d64034143c05440d00420708544802c11512180e041e100600804a00008460b80b946240340da40c1c0c1041c0c0640c1164410070400c004c86c8c611580300c860003240c0192619082c440b4092660103660001082000d0074100088064895920650006489030052029040e182d040048204070b00c3c1c0b004181074411300844040c0001130b00c42d040d181d540183c00c020995100e4940070811009410004201c004038403000c00c187c0d05034266a4409000950101d40800c8200b41100f040004001107120382507035a0841c647c1004104e00800c001c20b896000d5260004903000c2c2d4440056007400c12045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 459835980 1250 459834730 459834737
    0x201021c0216050d2406030203010501121b05090c0c0c09040f0b070f0c030c020f0d06050a060503010501080307030503100b0c0102070308010b0711102a020301110f07120e0d03 77
    0x341c1611107a09082c881e00034141c242c400301e909945544070320180c880150324501c1d08480b941418043c56502c3d41c050000713564000d000b030059503035940480c1b03680303070b5040002d5030319218000c40030007103881d80000c1ca41103440150030248160f4440c590318503a500f1801c0521354070b01070351405640d035a440c1485a44078030b2003800350380c040480c0342c1000281e040c001880c00d400e1080d010098180141c00654242c200d40d498036103002581068070105145903041d0301070030341180c0d03502c0c41101000042d8016a2003a1554181003151507594010107003603417802e114101090300100010f50109204a004641c070113002e43c0c0b204440d17903403008038441588c80481403511f117940c0440d100381011ba0020341c403401000442d4010f4140910750311401d0b80c540e0941d000e240b09509810024821a00402c1d01c17040d48948024400700d0801122005203a505105204a01c0395181110111600c2c880e41e060758540c5c098540000e052407444e0b81c80f8480c48400011b180c0902001c4410b81d011a6228007401d90b4051181e44c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 459837230 1250 459835980 459835993
    0x2a050408070e1f030506060613090f201602040b0409050a0f03170601020c090406061a0d050a140c0315090a0c0801051c06020904090602040e09060604110306010c0201021c02 76
    0x402c40d0b1010118843c1001d4032540164003000420350004420750426011680079545503107075801c051081110364081c07244281800c46900c0800340503030100e100d014040c8281400c0c2021175200d8000d62181069001c1001e01c0590443d02604103a80200400e030006480002d410340b03185c9501e0325000e4200b0048481a000c80d480000b010390122041d162544032060008050038602c0010b5141d40c144d24000e800340c0e01240c0000c060086a400590042200c1e4085021803205100364011a07404224244030090501c0082005200c4a01c82e10a1000702311541e06c0c81a1294017003200d640c0d1010303161228110a10f418410141c1d1000c4c5114000e00410703070009515000581c0107050414143d000d075106d04444058042c4010701ca10064801650190b40144e44040b20030004004121804010382036902c04500811150426402140030f11014070444e80352b40d48903420030064400444646000e084c0600124600d9402a20500341c105d10500503a1030071008203020040c031030708070756140d80180c1c842c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 459838480 1250 459837230 459837241
    0x9061009020903030c011518020405060a0e0a050a080f120a080402010f09090f0501080d031e02130e04050622260d1109010f030b032e050108011e2a050408070e 70
    0x303281003082c608d2032800b9070815240c140060300600074807070482d0622000e0b040c100c1d1140d0398004514094000100188442510b5628899503284a14a004081d00c900001407031000041e0003580c900304980c1c0d540905030b5440d0360044880c048409120070a00c030700c04d40d01249038540d030700070460300801000c40000d4a41c50001d03401e05e4800141c4200050510380400c5400e007000d00d50846012141c8130f00c0c0541d4410340c192009030600207582c00400310220324410b1004010004c20752900501c5034400b10902c42c0e441440f0300c0140e079082400240341c42c12007010660314008034a80c40c4c1e151194480d0702400d00c548201c0074000c0e14901182d0b0005150006540081c1d50b802100701c0100c16601e180404c904421180440c1e910001131000341c03003000c0101c40c104440f0142001d1100d00380c0c95640c0901c1556034500882c1d000e000d050002c1c004071044608040c80000c0309110f1711145810100d04182101504490060f001409100369010028100401f00708032604000510090090740f007031740e18500e0700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 459839730 1250 459838480 459838499
    0x6020c0604060f0516031505040f050703060501080907030b040305090909010e0d0e090c0904060513060e18150a020c030403030903060f110f090102100e1509061009020903030c0115 79
    0x4001e01d0881d991522081c07203400c8469110000c1c0c04842c1b41000210018540c407405142c0c4510341c41168002e050124949281e80c0603004240112003c1c0c40504c800b46e1a840199400d030421542e0540312740c001c250070400301d48071041003178000b030007801c100c1d01d40b030400004a4180401104e03c0c882681d122050b4440c1044d040050f07900c02d8406240c600740c038820000001d00100c3c00581321a900b4500403682d03c5a550f140c5c1c0c01700c1d000f050002e065101da20045072031003024003268803825000000d036000042c0110600c80d010b50060340004082c1c403494612403000211a034002d845414078603406e0140c08c140f00401c00003000a14040d0326001074880c51854a4402d07984003d00303428040d0b0521181200031400c1c202035a4500d9012521240c60750640c00c0102c0c0f4100c517090349101040c5c1000b16110421001180390003884c004000d542d20190360707122209641e54400e507001011401c1001040240c3d4205601501e100d0380010306403441c0088108007e42503441d80030100601900750801080b00a04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 459840980 1250 459839730 459839741
    0xe09010603020301120f02030c180f130308161809150f14060a17010b0415020c09070c081308030c101a10110604200901030c030305090d06020c060406 66
    0xca501c0e0a40ca5581000443e25400030841d80080000300388055640440d5802d00110a001c603019007503107054507080d4484140010180c2c2c04002c0400200007091861540d980010140c0360161501d020986501080c10040140319401000704010300301d00d10064860483c0300030041404400104400361862110b0504200700d900a201d5085112010130460000c000c1056001004495050300c50017030040656082c1c000f0003514482c018400004100414114040c2c0f007910980102c0c00542404d020060780d03904003902c034165001807a80e0026030190300c5201030310b4000d8428080c0908051f0316201500300910150000765840d000030443d440e44003400c2081140030001c0500c2480400e40901001442c41d503109440c5002d01803100c041288580901b0224010340ca000d421900c46290030f0500c00c841c0549850680090a10031010380b07020700d000c40c0f1030390503603810812000d049480e683c0c0581d50b5030b004001090308004130001900216040384040e2403084400c801803d41c1740ba05141020441d01f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 459842230 1250 459840980 459840989
    0x203090103061403100903020f16030308010902090a051504090e0312090304030b01030605101e03150207020307050d020d020a03050a03023a1e0903110907020303280c0e0901 76
    0x342080303410f40d20380c0d42c000f4244140690700c0d500050f0080311030034101e082181843c5071544510a880707500304441115a0843d007264007a41c0d961200e641c84e00f2a04c0141d200e03c04525522921480b0240800c1c031340310703101d9452030b070613481240c0c03600f540d900e41c0b04140d40b91100c0d000003a030000300e019036000340c0d985007540c3c1c04480c040c09507292074259500c1c4083d104041c000a4505555840028102100100d010b8080d1984c500f0044d0004042a22108a040c04c0d000c200e81503681162410300d1380c0100c0c020360b264140c1c02009004000e0502c800d0000600c0d045c00260390203440600d04c580540c40d00300182e0007440c0140003901c40b084641c280030345010500d0015440c2e50712a00306004003101040099100d60420307502d8000c014159080c120351120b48100c001c080300d80750442d00d10101b40c00000b0441182d2081e081102101d07010000c01000f002c0440d200d00241c1c0080001030103a83c034484040029100b4005c0901403058100b020100311064040b0480200300648801c00382842e0001d41d290051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 459843480 1250 459842230 459842249
    0xa05030a060203011502061902130e1f0b0405010903021903170a030501061404030212120414040b04060f0312211d0c1e010c050303151011070b090f03070303020309010306 75
    0x6088c40b039000c441d11808000148061a4040384004000504041c404000e000c925034503841820103e21002990720322401c0e0901449101d040000c07001c3c4d082080d5011071784141c4803086464655024005107206200f00c582d0049040480440001c00c0d15107001020321308000c1554030780e442420054116101030302b2000038000c0101500911740450b00c1214141c0c1d0b03050300d07052040d156001956160910810704440c9000000c41c010070104480020241381c250111802d10642494600340012100980100b14420030058401e00100d8083e071301605284080d80b130301802e0040445c034541038899032940c0e98030380c0d543c507a0140f8221604003c00c018806d00582c0c0070b060f1144070640044c154489000421012740009200c0c146a070307006151401c40d4030340003400d8036964a041c155099900c0c8010351b807a40305500c0d02d11000800f500c9585800d0841701c50310010000e03503050030741c0f0654a0300900c0d1a81d034420100040707440140c406106280095100390000c58841082000145c1507070165000801217 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 459844730 1250 459843480 459843493
    0xf0415080a05040b0a270501020918010302060a0302090a0305070906050109061b0b090a020405090d11160b0d0e030c06180c03101d06012d080a020f0a05030a060203011502 75
    0x1050310102d90f1601701c1c1844100007404407a00521044c0380807800c48981003110303425011014480e0640050000c00021034458007406000072201030f0249081c0000394010340244001c0055501030f1303000b00070000300201011030055403a6141303454a03442d41c21004a090321244200210358100c00110040c000c2400c01c41c4031014144c010b0003400020900262080c0c003c8404124552410b00011a0403a00940188124907003405000e40c0d40361600b1a8000081a02035a01845d540100f644084525541680d06500341743c0030000110780c209640341140f4607034619804801120810090021581c42d01c041c0150703182c001945900c03080380003070103c1990040d5420000c07540d8003250107219000101800241c00e10400d81e00720b1081443c12000401d84a00b0001141600800c860100c0701c0c000741e82000c016181c2c291484120719202c0c45840310640c03004146d1401481c0c140000a80c04034061302011540381d8400c00a0700d42100c0ca0000c0c1d40c070b03c0d030000040c0480880b410402d81c07401c54034001400f5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 459845980 1250 459844730 459844733
    0x207060f0509010c11041d2503030e010210050a0e061b0904020304110d21020706080601050c0a12091707060f140702040207200f06031801020f0415080a0504 69
    0x40c414158118100071910200c0020405200f14061126030090303c04c101c80d89151411044c3c882d00032400c640e140c4212102c0b001c0c81310b203034290804a1001018440011403441e5001d4403071080c942c5c2f410303040d03015802551020020a20990b80700e010002d50204402c020300003010f00704140030f88840c802181d40e040d4240c03000c0c1424103e50324010280c40050b602e643c0c80c100441d483d46031920203680541c584e451801030100d070440510807040f00114400c80c5e4225040c05030b980d24060710802004c01c1121001600543c05500940f500c1505003066462007142c5a888107004800d00c035006000c940c040c0380c1881110b45404c400300008880c030005103402410980d01806c090411f00c803650401500c481e0032060b00c0703800000d942d19a90b01800541d100c6490341751514280303401d245000c41c5600c40002c2c8800c6841e208204003520000a004d04c3d00c1c40c0c41d40064115000c1a10f040f0302d07a40e44d020007001e003030100042300610041030381d1403160302680c04200d401442c00380c4c0034151400e41c1e400c00c0117210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 459847230 1250 459845980 459845987
    0x60c090e07200f070e01170705040b0102033a1e05060303040b0d0b0127030204050c040e01030c0e100612020711031504051e0a020d020102010b060703050a0207060f 72
    0xc1e040301480c00e011440c8284015a0b900c120340c2046410018010200e00f0f00c100e41d0700049850035200d400d06880d202d030383c85d41242504480b6040c0107004c1c2c3d500601d001c00c03c1c1d0030035a024100f19001881034034980000d410b02c120140744c0d160705a0546540d0900034400b07180e040001e5062003010781d00d00344200da00b40001d00641e90070035044402c02503a9800414210342e420000c4074010012481c049450720b0852460900070b046c02d160490119030402d16103c0503800740140e503440f488125110007506030461b001d010007868005d03c0b24400801c00c10001c42c503014203141146c001c500c01d03079404080d01d0918400c0140994080c4c2540b1440501c3d240a000180d0494443c80400a00c02c00060300c8001900303000c2c2803250782022950b018003410002d04142c4417141d007243d101d0340c000c604a902c0d00000304014801414645804c10107a08403140d510010302c0c1c101c9084d18801e00520010410200440021310503600600701100425800590400d0494041c09588014140b50a1625044540d06000f4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 459848480 1250 459847230 459847259
    0x303141b13031415092a0a0806070305010f1a030a1a060d02180111060114030709020a11070803041215060b0a0f030f050103020a15030f0f021806030106090506031021060c09 76
    0x10022454144000700c4c240c032103c103004020101c4108580042c2414ae0f0080d000b42000c0c050070403440e440c0040440c1c41042441300c10544003101c0c4055240d81e0304d203408d000c02041c036400328480360340700304242400640d00c040207007454000040005a44403000c50880c50152421040e540c1070181c5642611041c003804110203044a850607401410f6080f0f03440007034200400754004031900303440410540c0d0b40c5a4420380e0396680301c0300d5104036014142c907503c505650b1b008901c1080714042814420303c00059135a0701d040100200c100303001c03c1c15070f140c049500c40d5410224010000515444040100503414007401510345203443c0d0401c010350441d0007103604880c050003014082c2d1109041c41150030b11a900c0401410100c901c100149821804494042d5009401e11142c8601003285060117140807001c40b4125010354440220551620080c020343e40c00090441050707040074200028225042e0340c00354100c4042d10507088002100b85000b0044450480700d40080014000c03003401802500c0091 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 459849730 1250 459848480 459848533
    0xd020c03100902220f051501020d0201110d020c2404031409130209060d09140f0303010e1b04031205071203090f02010806120703050303040303141b1303141509 70
    0x10f450b007422001d01c407a020f8117104541e0f484840c6003400700141e2001030310344c20718110340076420781d40c01d000c2e440402c03070030380d014081450b194010421000e00c4202c0a41d00400000149200755881e00350f0708240399031074a12078941d15202c105140d042004043e0b11030705000e0000d0581c8500307410159800c4c00703d545999034044a040d030035400a034000326071b610381050700d070584502c0205022003540e502e041101d200c6221100c45951003150480c070203005e00441030724180c4029013403030580c2d540d41d40035400645d0903000e0180d41c00721040201101203903800881500c3d43e48107450f07960740d07082c9624100c99a401c0d440111002c1515184c2d205000070084a805d07081c441d024600000103407554000594081210246403406104201001040000c080701462080d4001d071010007580340c01002050030548112501c600500114400f00321100c41000a00060b4030700b075100d280c44030703100e0f50b03a0340e403480c0b810754001011780c440008482001161800d03158450f800002a1000b2585005010a8110720515 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 459850980 1250 459849730 459849769
    0x5190f060f170d082715060103060e0606090a03051015060903020310110d0204061709070b0a080417030712150f1206020f16050c010206360d020c03100902 68
    0x45045d03051401881e0340c215800c081000010440500340c603a452400c41200c83d444140b02001130090340c020300c1840221402c0034000141030351400104800e03903012041a507400000100088003040d800c008003188403001090000722200810314225003400950302801c1000040300d070a10040c3c074042044165294812000319030040d07405042d11550103102c8040ba505803000c01c0028240d6400744580000039a560000440740d100c841105494800c10b0103030342d4240100300683e16034240710f5480d5550140c00b4080c0e01d040700c642a00c000980e58002d0f28090b000403544c2e01c0b070144544080c480c141c0d145052840303210311140340c501c2c0e40c90a40618460150a04421500a024800300f85c04841c60000c0307141e00a641c0b4000f08100c4400038800500a07a660f12442034040025400025994064002d00840c0c003c15001b86940a4603964070303552800302c85080340e00210f1469002c01c0808040001500509103618180702450300c3c203800d00f1a440381c064244490720000d83c41c1c103821031481410411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 459852230 1250 459850980 459850997
    0x108061207060f18180e070e100906120c0b0f041517070306080c01030209030c030709290105030a020702040e0a052103010308090603041b030602090109051206010905190f060f170d 79
    0x6400c6c608080c107a5000300d40c8540752104001c801d20340d01e1680810340d01c80250811100d9162103085030440000c0400416440e00013000f44401040c07040034000034802034807404c1c9041d807107031303410142440d00911407004070343e04102684040c40342150140d800079003841c04110403031602d0b00e0103a0301da0304040c8030b0b030506600041c0100280c500b8001c800030f1000181c11146c0c1a036460030306000074016040900823802144d0140721662401c1013804014103c140c1d241c40c190f4442000c10802075100300307001ca07800340d501c000301059014184030b001c84103130045019103851889010701e1154101421205034003214204010f100145441040d5203242209a41039901e942c2c8510344601b80e90710591100701070f000f003090000b042003055002451070f41420380e501c4aa40350340d282030004c07021103810308592540140d001800f070f00c0b02e113500199000c4140c2c0e145c06250104000c2103411640e0704403644003419101c00003440003c0303809441c5801049200c0000c04101e101c466134903102d52600400340c00700034007076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 459853480 1250 459852230 459852251
    0x2811060c0c0a200f0306040b041b0e0a050907150c0624091a0901030b040f021c0803100806011206050a02040f0b0c28020108061207060f1818 62
    0x800c940e2040c280d02124400719040480c0d09216a4500303201c40b0751040904c07160010040c24082800790040b58040401d030a10380f61551a103c0080460000b00e803190f502c1c52001800e0112010940c0c001c2105c5080001c1c070303043c41402c40d0b080c80da46810000c14000c86100b106100c581c40700070201c030346070800f031f000030021002c0301c00303800c80d80108500100e0380e00100c4000c03d4000c2c02d40d20164080f415818000c80000d00d510034807203032240920014000100303040c00075020502d0240b11591091006110040420095180315480c2c214840c1c2a9809100401000100010486d003003019017111030042400d1f41c9060105460710040110051103543c4074004103c08504d150156400b500072584c584244e41d8407038410744401e801a0b80340c5501c0780320b28100100d1070b002c150138101081034649020b581c00c1d9141d0b00152114075010304070315040780c0c030b462032403091450520505010b030070203569041d054507844100030450034504c1c4180b020900003110400502d0501d2103003100380001d14101081c00c00b40e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 459854730 1250 459853480 459853483
    0xa060912081902070f080106060e0415050901060c0501050109020705030a050a090b0d09330207080f0408030a09080d1b0f02030a05072306070b060a0306022811060c0c 73
    0x150b94920b5014030041c03903110729181c0c02058480c241c0c0c03504000300009a60302c00c501c600340d03a80d5105400100c0c0160300400e0031070625801201000d44c44112442c5401c0e40c2e1800310340d81c407209030721030000200d00c00c4d030041c2001004c5c06800e0050030400d00c19130400c40c154580680301e01c6003110010501100040a04410340151000f000815025401c55140e900b5038004071f0107890f55840c00c840c070a25038108240d00c40c1c2080c0300d2100311040b944801d0400442072408000a501c8a031040d02c0b5401e043c030500c0c199030b581000510190040c0f4015503200d0002010240c65000b00f50051815500300030810741303000c2e6210b00325042105141d50301c2d02d20403616051002500b1410f0790081e4141c000c01c1640000d0060024000301102c0600100788040d61702d885140300140418010140d1149080091501046002c0c0e146a00060000e0614003a541d0340d0b40c800003264410b203d08841481840c940d100130030f012124440303c00081d0704001c2c1229045500468440b1001030000f40e50307000124854010020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 459855980 1250 459854730 459854737
    0x40e0c07020a1a070b16090902030c1303140c01020318092508011e1d071814040b120c010f02010e0a060e1c0912210c030305060a06091208 61
    0x8080a030b256454549804004103940004000d41c1c1d0b0504007004180048000c00c00c03041441b10942c2e40181481c1032140643c0a5070015003420203c060500c1844400e2501c00054001940306003100041091082810b50030001c408080c41d0540d0010301140520220003501c0000000045511000a9a400d04a071405c14040b144111505c0d41d0030350300e5002c454002e002c0b603050b20400500c503070b0410749041e00040325080740e020300a503a8080c4005d408800d031802540581105150601041d0103014841240e1000d020354480090559041e8001d981c50600e0b22500c0c0000178150b5400102354948295166145001640740713041020117540d6191881c401e5000c2034188176030720280c8a120100f0306014001d40809408000c81d4014030388002380b040d001074410940d02d440754480000080c030307000b600c2809080d945016104a80c240071240c0c000c5640000d00d4503c0b44c0e0580f11004c19071102e040080031144000d24a901a0f040c6500600c03049070452020021a21000f9054098048901d0310020700d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 459857230 1250 459855980 459855989
    0x10090e0c0d020708071407080c1c02120328030b0a050d050c0402032a090f010f0212040312020105100f120201050706060e07080906040b040f0303091401050a11040e0c07020a 76
    0x1480401d00d0010040602d05ca000c2c1144c446c8100ea4441d1b44405003113403070b40c102d10050381c0d202d1130403402ca54034001d400030000480f9000a1079064ac409488004c0b5045d9070049100300050b42c02d0940000181000c2c08000d5a03082251600b042110b03c613074042282803141d4011180301d0602030b450b200810008101062180201071300a646a040541e640e01c4406400d00d00d00c9503039440000319034942e504103400d40300900d400070001c4208403ca0302c019100100071240400840c0a41c4851159450241e00200b000b9440740140006401c10204003d0860350043c110348c0262904880810258082681c50402d0f107450b8598064100900d10040e1005d10903250018045810f010f80080c40c80b815003107491064130180c03944003013a602e100195445481c01c4800030b054101610104002c101c40f00191006144070b8100000c02030001d8681500810482c802003405070344881c00c0004001c4d207402800900711903c00405d0038541004040e10341403000a2099860032004107440041d584c60724841c40050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 459858480 1250 459857230 459857243
    0x309010b03120901030f0231090c080103062a120b04092009041a070c020303031f0602031e0c0c090115091202030c04090303061502060610090e0c0d0207 67
    0x71a80c0031024007a0f000000c080b0702183c500a00362aa04800c3d000302c40c00c81188101c2a050750b4906841c084000900a1640d03941c40414140411801064460103900035007640f590107456142d80361007420380342c0e540c443e0807060441c1e2f00120030002d481d40401990034130a0801c00143c4000000542c001d041010306550b015090595440a1000d44905000740015008040040c101030b0303428040302d04c00564000344894100c0b801513420502520b44540c0150081c50180c51014082e00020310390342082c0e407100640c002c04c1901041e070f2000710612400500d2280042c5040403200031003441182505a4000f64000e00081c14001c4da8005201002405034024840e0301ca07035031101c80c40c0744421603a2110705d005c15000000495890509038200d801c0c030354024002c000417040e207000e120145c01d1500e001ca040c59154040481d840c0307071844100030b201c03185900400e9103103482410010921005c0700d00349c3c240400800f0601c4500780700001f05034010718805446030b8481781441c1000c024411500003800c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 459859730 1250 459858480 459858493
    0x12011503061a0910090209031e100c140a081306060807060f030b0603150409150b01120603110d0f05030f030603010c030b0a05130605030708011512020a05060309010b03 74
    0x411540c0d038405400d40c0288a5001c410381a00e20030310500c1c01043c1e49545100b03513224020424843c040d0003d2524000240030b0b90f00000144014600e00303118900c80701d82c02d411054080561101c030f4030030714104050a15008003032540301d0910f049940700300040941041046c00010708107400d01e200144081e03500c800c0c1009403a5072540c05c00d40b14806030040c940060011104401224402e0086803100750008001c0c61541c1c49004440c40316040350040c10760015101c3d034030307034011403000404440c05c0440b410780031079001001000100f11980614036030007a0b52a00109002086a401d50f048009030b007610716080f40001402c11100c2d0950b814002025032000190752400c00444002a6001d01c1d8150020302030940700c060240c0540b4101c104440d0000c000c0340742000149881e40103211014440300b030003e46941c83d01301081c1000d800d0f802143c01c40c0e44801c8110320401c10300391400000d0480c0f200c1501d00710802d500042016106110b400d119a5000c008503071002c5c0d00394400c0e5158100107044882 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 459860980 1250 459859730 459859733
    0x9191206060f080606060331050304050103060902040b0a110f101a030f1002030c0904050109020711091302151902060a061e15050f0301180b04020901050912011503 72
    0x9060326000702c1906050070030700040d0360b4200103840d50040c0d0004204600710780d159041a4100b80c2e02035440f41d2048a0807440c1c12803140402010844180154041c5aa850518001405031107941d800001d4052040004000b080000c000ba204450002d242011070958071054032850070b0988003c1e2580303801500e4104452f20583c0c0d00c0355004860600a003c2d21012500401d900e550300c00c2e616440360340040c040c00603000801d50045611030707400a1882d0070005800007041c12214240c100d601c41540c001000001d0240354445145203250444000d00f507440d109809407216070f60b45030003d00400a82103802111001481510f0003100d400c1c004040c0003014460095640000392244100c01d8904900407a020304071801140420340444121940301d45008401c01c603183c0380400f00380411000f031010f4206801a44000c40c000d0002003011102600e007400c014040380d60485101c2e12491040005000380d98102040d16044032007118032903450021019014090b1186050f1200ba40301c84140100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 459862230 1250 459860980 459860993
    0x30c0301090f0207111212070302010f0506040e0714011412061005092103040308120103060b01050a080a0504021201051f080601061e020c0613031a010b091912 70
    0x40c100c42108005010036558440824128414042c02501e550000001140d15091100c1c01400d0301001c1411034140700c1442a0203034050b080081d085005075103d4154003040b010303e00400303800c010111020816a15060f5400ea07440c1c0340380c400c007101405101c10a030082d178000c43d22102c92400d80d400301f42da0303100215044030388410101ca200e4481c035a64030400801a10500030380e240154060407209a00c1c141e410700c43c072510210a441552480204400301c00a01303107a020303007036403156202d15580c2941946004001e907004c03584880d041000c20f119140c0c01c2a80f00c8440c68101c0c08121001030240c5960000c41e850541c401e501c01800d608203c2886030080003501134030a06000802c1403843d590b1a40205c0d61603840a124660018061808100a100090408804001184c0101d540c3e060400012840a800a017203078120080c0c0004100180207507842c001c030650443c004041d5096050440144450298821550081850011243c460008403804d04080c080d08500450f90b80c07610315240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 459863480 1250 459862230 459862237
    0xa0f120b10030c18050907030b060d06030507081002030c0a0e270105150708040509061c030801030c06050a02060c0a050d06090b0a470318010501050d02060d05100506030c 75
    0x141c00079013004000b4404c40c1100c44000309440b4000c150316070585030000224040c00d0b004001c10343c40401049a040b244000b441100c0c000d6114001801c1c800b85040129820302c004c80b042c82d401c41e8010410882c0825400c021114410480c0c1055003018524001107560706e0303013006c0092041c1a05a0f05022003e061552150484d80c040300d0940000140d490129070501440c04010182e9600748001d00c00c0f441c0024800d980503001410300d8406120500141b07141040d110303000d42c08101050b00500901c40c0c2c040c90307800074000e5814a94548880302800a6441e903004011240e181c50210b40d035a4414410801c41d5140f5504441c10700c03040361610322210040000d1054144202000f0100190a61251800109182800d450011502c280c42031800040b6100030090200c4003042e00080110003e000165004014a5115074464001c00f11450708542042c1c100a02c1008943c6802d00160340c1c280c2140d00d54030b00c22402180039200c0c59900b20841c582074010341c1e4002030110820910107100d44c0034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 459864730 1250 459863480 459863501
    0x402012f011413020102030445150302030c2404080f010c02060601020a17070209041113050c0a110106210c05060711101103031311060a0f120b1003 65
    0x140c100781c0703e207900054004814000203001d40c000f03000030003041e030075600c0010603076030303109094000040f041c070450443c286c104020703071084505c15074401c1d1100e00324480d41c2c02542050b80319030100707030660300041e940701c0105100c2403149a005075044400321030301030f000081c540c500c81080e8481d40c450074050784a02c0209000c80081d0b10341098290b08610008111703009036010b80107080010456101d0062850926203001d8020000f0814400143c5483e000350740b017940182d0030405824040c0c42000490414030381040495414002803211890390344c4210b81e503448140c01c2008090099900040c094211640241c0c0c00c8080315100e8222014010b8154000620a41883c0212511070040005a0140300c501400001e64410a1a058180100500540442800c003440d070503a142d8146071465208480500549590121140800000050002c0351010440e5800d08101400078010940128050210100300002c0c25059040045501014160b24081c01e10140300700065006400391100207030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 459865980 1250 459864730 459864761
    0x16020f010c0207030b0a090c1802070b0c030a0e060907060e01090302030106030f0506010b0c12090609220e06060907031d0d0801031202030306010c0b1b04080d0f050705060402012f01 80
    0x10750015414403440401d5a071003c02a07840b503080c981c081c00100003032a40c50309d4565080041c607010803140010b9501c87c500c01903a071a603d02e0480b000c04242ca0f441c800500c019805081484020f09000c100d070b84c199481494450102c01c1d288004039261368681d80041e416500e80000031040c0a9540380d00f5940174080d80c221001c41e603a0f4200c1103071328447c003440b00380d41e038104901c414200301e0320500509401c40c00800003410000e00308001840c240b070100200112070030f0a082c1c4c20a404881c00350915402010001d4503903494080c010a4030154001c255404159451452130824421240c0080e91021402d00300c038502c1261400290441c0070a020a03900c2e01a0040003003c0d1a00c00001c03a4810700303044c0c3d52242d00d4105681d0700c204900c005040d80000d118002c0501e55228248405000140450782c010030180046c4032020b0000da4640e0201d10822000304944404601d0020f0440e4101d0750a28081650410a003941c00000c02c3d0140340844070484c10100c0c820300601508641a44400c050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 459867230 1250 459865980 459866003
    0x40201020c09150d02041d0c01030f090b04021504080f030919081e0319030b090f0f01180207020d1202011b12020f04031a0f06040603020916020f010c020703 69
    0x203003044400368045030308000101d80d400b0a85818140761071307541e854034070240011404900c110050645506810310080b5550f100c2d103001401d40d03a042c0120000d02c11a4041004088001d4603102e4464000030000f07030003600e0340c2d601d42e08100701a9085600600c54a41a103c450340c8240e0040c0d200c1d4040c0c0813851003000c2c0e105450100b92500d01d081001c450180c801024030b903500700c0d40e1045038080742c0788540d00d9000911900200e440c910145000000c420313600010022000420450042000b44c026800301c00c05508221200580600c070b941503480001e211402084000441800b911440800070741100001c80c100b0104021211202d041103015002409034240e041198401d4003404c40c0f04100080e07200620004203a01c1d40d00a04154080c10040d602d065101d40740c445240c500d4696007403940d1041010040714800407001aa0407000c2114203004041c50b6400040082d1400782c0003030080d1200c4070004400c28000c0180b403a40c02d140400074002040702ca040a074844199110940d016070321030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 459868480 1250 459867230 459867253
    0x411060715140105090a090c15090303091a03060d2d050f1209060a020f031b25061b1a06150c03120403110a0b01060f02030a120c050d0f020304020102 66
    0x40c03a402e03040c4c5030080c184168590300d040382513001e080500e005984901240340041144031246100c6000750031151a051011807a5140080003040a44e00c1a180386031034140c1035058a02e04000c480d00801e04544407513030b040300b03810031440504800c103400f4036042005003d902034134801d41001c0195401041510011a580c0450540741c285104158159440070050103142c1d2900c0070180030000764520496640302e040850161940d8441e044210030110784004400c0c0c184810062043c030740c15414840c0b21041d020386d0140d109218240103100c02e110050041c150350503040f901c03020b1079070f030001f01e005003120404100c0018a04161a954020f062904a400903400c00c101120a41c7c036503a002540b50000c40340c006070120001031700c11401c02c20b0101c01c48410f80402c103d40040c1c14003c4440503195450000080d00401a9640d00010f5410501c22340390546c6c1c204400110340c1120200c0802e419220700b0080b01c0d5445004426038440b03140c505a41e40020301540075501c9203100fa000c40303007501c0d0403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 459869730 1250 459868480 459868511
    0x6180602010b030c0105210103060b04061d0a051509070e01030509010c080f060409050a030e0916021f020903011d010b090105030d0c150216110604060509090411060715 74
    0x550011078040d0700130324042156511410080c40c00d6401c031041d4480903158000590382816081e401501d60a8a5408040c0140740c58407801e002030400c0c22841c0d483c0c40b103684206901900042500d400b803607803040010071500e007401051100c80ca000346800c402e0300d030a080281002184003005800a1706e0200011640001403042028502442d2078030b4240c0e517201d1721558800c0d00c00508940c3c0280c2c0391109000046c03010010701c442d0922948440c00800703001c100b400403111000700540d6100f82550303140d881e804d401090703110007105074804400c032021407041c200000e03200c0c0c2c2c164541c240d0303e040c1d9002240100400381c402c1c5003038004002d02250510004100e0590700a001c1d255054210380c80000740c46002d00010340545104d58140541c007413910000074207d0701700c410003080b1207914002ca401040f03d60340c001154114121217107400c1a09040006101e405007003800b90181c22684023160a108d070544401000f002c005001c135950341d80030315201c480102901100c11182d802c1c0454511100507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 459870980 1250 459869730 459869741
    0x301050102030d09060609111e043804150306240f140706050703180b0106110a050a060b091008060a0915110301080c0103090c060e1302040618060201 66
    0x10503070056007072601e00040c103c0202801c2904880041c4e40300000a8400d400f401107881c4007500d008040d46543d00c01701d159140007105c82c444150f01108000612504508030711803000300c405041c5a11542c1211590130481b0540c40c0e9001c81e9150020400050722181004080500b01d0140d800340b0255580e6a000381d8001601d04460350b86d038030107100d00d8101c2d5104041ca00c40f40501454400400308064901521720760141d481a41c01680b58800c0005039a014003c0103c6920201800d2926403400d8030742030320190040c0220350400071204040e40c007001003084035005030761300312064800300240c515111006103007401c9854018485600001c04500c420221a400c0b9550000500680c2da00c8004090050032a60800c8624407204a940340c103c441504c5100802c0480c0045d1568a5050421451070009183c190504060030030404100180103a41c2d2542120021f08100d0070b401400340000361044101ca1860300391278404207000071860741c820154000390401c0c060740540d090715401c0032400d070341 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 459872230 1250 459870980 459870989
    0x13170d09050906121005160318031e0e151206030307030c03030b040f020a09051e0f060906090904031e050f0313030e190f1e030602032a07060507050301 67
    0x3607103180092a40d0070000044c0d00d014500d00b0559511078254500d0100f104d200340c81c12050b007284c01d5040e841c015090311400c6401e001100d54a001c0d00483c2d40e0040a09a944a03541180707100d408940070a00d00860b00c801a14000070b1415225940810002c0d240703030048107150b040000444040f540ca4140881121101c3c2c2e010382e900c58130080641c406401038210480c1c490b40082d6160846017507c8190700c06002c02c4400d41d500c81400516140400004a4403800805020b250b03900714843c21303036160128480030200070345482b501d5501081c0050440c1c0a0054104d4201010100300030070142e00c4406071404801e00159140980c58a10003150070f4015280303020b000480c10004195441020746104c00403d2017860000303c4240c660b008180c420300c181280c144203203803410f0280b04000782440d9000c007428481e0742d00c90720301c1c48220100071462030a1001810650b4004081402000d103d400c00700e05824090103500368011020b002c50f0b40741d100420aa5070a4070348000b2580e5944a10112030495 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 459873480 1250 459872230 459872239
    0x901050a081b0a0e01030501090b0a150e1b030c03011d270703021201020a090b0a0504120f08030403080a0b090114060d02130b070507090b09190213170d0905 69
    0xa4403a03980d2080c4800b55030b5800c0c0c0d03001660000004107030b5600e0b00301c507001c1d510a10020511800c1c5141000000c0000f0307140328405801c041d10942c01c600100000801c0350003407061014641c83e802c10301400d4040720307200180c0f505400000c1000c00440980198100d94404501242440c080c410b0140505010360705040c0c409600d8103070f50401c0da01c101c008901d9001000030b03203000503982c0d40000e94140e8844051010703079401103864036402d5006000c800c004c000c1546618902804484000c000d4402e034000c10080c520302183c42c40c140041ca0711502d40fa6075001d152030740d6074282807c0c0504082c0c011100e041c003641c105010b140c01801e0000905040f22a05240103050a02240c1002a81d401641070400126030038400b0b420680ba89461582c003c0c0b4010419039901c503510f041481c10b0402a801001d0914244500a2100c0d10b40000140c2d010401204101034980450f048001a10038102c0c204c0c05040e11500124202c050580c43d0309000c500c00c400c40c1c0314460b1f4580d095070420200e10486500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 459874730 1250 459873480 459873493
    0x15030b010e0d151401050103150810020f0409090303091e120f050706020403060b12070e0c0a09230a1d0105150705061006020d0921080d02040909020901050a08 70
    0x10b04090b9850400c4620030400f0480e0080c414150104586500300704442c06203400004001558161040c00343c0d0803140c851a0010601702007840341c0e1040300c000340440d41c50740000c042c980003c1d0503056402038490f09806000040135400d008010344030301036003651210705083e6003501c41c40c01a01404512075000f41e0070008183d2035032080d102d44801d1500d150a1002c1005070000040c464802031020b0f61083e180010070705600b4080c41603082030b030b940384400365000c0754040c4032501900c00721980c084407174110310b9070394403d04500b110f200310554030410500d01e900c2c80450490703403030030014883d400b001c4d83e405020315034500c0c00c0d110b001146c40c8247c2c00540c0032801030055041040c4800390460080e00060329026155544600c0c2510480d101d04ca4446609001d21400307905000140c0c0c00c0b54245010a180d0741050041c0368080105c2d007400c0c0c0c00001601000b0204001d031026161005d8540200b191643d9440200c0d8014000c00b240484c860400e00c800800c3c0c600d00110a4000d640c03111008055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 459875980 1250 459874730 459874757
    0x17010905090d0924030f060b0c06060f010507140a06061d06030304050a060e1206010b030103030806031c20030a02070602010b150405091509190b04141b0c0601080715030b01 76
    0x6100d452001352402c040c1c86820842d0300c0700703590013400002d044035810160349928641c541d40c14400b019080600c0346900310302e94501c680e442001e03100c07032030342040c503118601c0344a004041c901003910781c0003441603007000e000103035503007410181c00c9040a01c0c0030a010a0354034802015200d21450160030f5006031040c1e0207203c2903100f40c440c07080d2108007800081c18072010f071441919004d002d0b1702141c1c0800380040103004059004100c150010010f50040240d0203403a0040c089100041ca1440d04010241032070106100400b1440c00b450055107040d6582c500031403000944444003030045501640c01c1c16202c7c906400d0010f103200da4001c40020160509050504210744020081e192850600b0300311860981a0745401080d401007004d07100c0310303c41d881222014402d960802c904540f01d146001484c0c802c540c00b4255140e8844e244101c54502d40301180702c0d078000740c09610b00b021520b2240740004280d54100007001003e88410201600d0100c25941c022026650b96200c46400110210f43e43c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 459877230 1250 459875980 459876029
    0x150d08031b070206040e0603120705100b0414091605010c0507060e0d0c0e1b07050705130e070e070305010b0c0706050d060305030d1512050a0803060117010905090d09 73
    0x141d01c1541a0704592401405400040094105070821000d080462081c0302c0917241c00c0141d0011078840380152810311680380c981544440b00340e400c1c500400d44541c0c00341e0303055070340b85d004040300c58015401d51586d042100c01d19648500100c8680a09516043d001c1000d41c028210004443d902c24002c2c05c113a401c092049400d0a002e50703003140c10800d442e100d0000140c04442140c081c1c03200021803c494503212010724400829007030503841d4240108103240c00314002107591000d0f45c500740c80541480e0800750300f0100034800010b0072502401070010110300b0b5205007009901880580c0c3d0300340666601c1304440a028841e01c1079042c8240e00c00001040745c6c60150000d40003041c00400c0024400f0381e00d496440c01e5501c000000001c199a600c49c1c2d408600145102401a180c0155510300c500503075980c83e0b5450300c045402900c00c00021002a409038805c1c0c40b100440d04039810925140d5030349800c011301804054403c0581402a00f80e903e510511442069048600031220013a6084443c080cd5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 459878480 1250 459877230 459877261
    0xf06020c241611031905061612091a0a06120f2102060403090b0901021b0607050a030c0c1203050a0809012007021c030816050903060c03150d0803 64
    0x140d03001d110500c404075002c04882c1ca40c201d5207000312500184446000d08050824004d090000701e1a0005030302d1401094000a109510003070f0180f10f643d402084013026103c0d2138208205107416418140041e04000054482c403121604010307404900b074a0717641c0104140e0300b050199851800e0345c00002c03000702d5032280480410901030503e662200040c150282e014040d01d2100c0809a40640c09120030164040e400c1e9004002c4c3c02c0380d080c10100081c000035102c602c50010703a44110380702004000070741e50780400c903809250b121007254003840d4540b8006e070544880e0401a1001c0000500020b4080122529401c1ca6135141e5559441c200c80e488080c0d0312040017924000c00ca650b038100001e510940c100c0d8020788140d89085854460001f44108104440c0d0742c04045509298081100002070308500d5041c2c200c0b01c8080702d00c4c241d141025080714207014502141d541131203080300303001030445020300460041d40c1c03208068900c5a69502030000980c80341d1030007007031031b50200005642524110380c44d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 459879730 1250 459878480 459878539
    0x8060d0c09200f09090a0f050f06100906021e01060e01060906080c03160503070309020d150c020c030a062a0320030415053705010602070b1806040513060f06020c 71
    0x259020017952048100c1c0c004950001140c0c4443c5c0500800707160031103414581c20bd1500d0000a070504002d0001d4807604101340b02c42100e00d125820200c503020a410200c05000300c40f901740ca1a41c1e64001c0186020482e2203a64042400d66000c02c0c1c102064100f102e10800d40c4140350001001d010900704c8040d0310003440042096070f6600236000527035805181980d00750240ca140e00501045403040d42c2240c0325483b040701554070a04050550361070100752620308940000d800101041c0b00890010100b180c001c41c001d07114421044003034143e405500841a12900301e1504c00d03590303008440340a4511083c2c0f00a00701b00c81c030206043c0441c20710303003200b6401072442184440c040c01040d110b03141c03100c1c0c0d00013601940e004c144441c0d000600510076580181158070052a4040c54621200c0507441018034540000000b0602001d140d114241218001c0c00050045900c41c21400c000314020080350145407400130707040b940005c54074400948141071601c01030034000c40702030074030a0248a5924282 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 459880980 1250 459879730 459879751
    0x2505040303052a010c020f03090f0d1703101811030f1f0806040213140c0d0b0909010905060721090510090317011a03010608060d0c09200f0909 63
    0x244010f940700801c00c1000d0528540c000414582054040641000351146480030a54800e1160003e155502500d203180302105560003404101320b41051924070020402d034005241c0c000062204d0440c6400e1f00c0c10854039a1450b07484155410700c40e8000380c0741b10b00700007829208280040b844042103000d6a981000215400c4a43da140d446d0744070214880325400118650448010070066003404003c03105c003d00c0540081040304d13000e401c0080000b40140c8020b134000d0000c03a00c1444400c00c2d0703219964500b4004c0584107103180c0104094040c10b40040221083e0103000042966036005407039940f628041c994104c56180210000e1400070846d06500b80e8880c0f20f80000400401101d21032101400d000b551669404a20080c45107003040b0306901100340034000544609c05490540c05a9054640e903150115103602c1319800105029034540d806403a000d40e06400042c8026244e01810b042c45070071074104151161140340e001140100982402d008404000d5100107203015610154409102c46 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 459882230 1250 459880980 459881017
    0x170901021c030207060e0c030307030f0e031f0e060609011e050d0c050a230603070e120102041e230613030809011202030610030b010c1a250504030305 66
    0x200040300700c01500e146900030a900044042c00d21045000f60099078040c9001410705d5080e42000c0b0b540c910440b14081d041092807030300d40b01c0c102c0c482c0c102e035004000000d080b54044050040c00300640c90144885900b21407600d514030b00d15140106000c2d201e0180141400b819a1900000038240907120038154450318100070041102e640d03914100114031302a50340040001c0c04c1006202c2d0510885c1c0140c0d03c0100418001d0199042424210010901c10303220f0720740329240d10a00b5214000070f00b2140d80d201042101e800001d000544c0900120784805c1c426041040da402655a403400480c0605404800c2800801d07100500c44c4c03250200d40000504040d25001c02e00342101011211600101c8059070002214150356902050481d0800800d00045240d41865800a07601d818000c503900309040d124861442a07a0040c015044000d4201469244442e0b01e2a01c1c0b15602c142119034859402d0302140580c01d284c0100d42101454003a900c52501c1c16040da1025203c980000c0c00100710303003083c82d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 459883480 1250 459882230 459882253
    0x30513140a05070905090f07030b010b0714010219030c03060602100e0705030316021f0e040b010203040911030f22060b0d08040902030708071b150212101401020a17090102 75
    0x1c110760001004081400a1039052080c405410445891641c1700c1f243d002c2c120501c049080690041d04481d0050030301c1c0d070b49800c1c074a081c80c0d0740c0701004140b0006501c0070507000b004407109026113000b540143d40400036501c0c1400160b007210014010040103901c0000c2c00342c030385c4c04c06600040c0895980310031140042d0b62240024615440072880382a500b17101d441d0316003142440010030b14440020449000da5a041400c003e1100620320102031007a41c81c1c096416890340240211405824410000e100b4082d41061040081e0b0040d0740040c1c41c80c9183c00042e030142d40102d144507591910980d00411103c541e140c00001d0203c50b144c0e03643c8100ea0f049000700081c5980c00900c001c0c490301c100540c484c5807580010780782000c010103800601504454410340c0e01d00c0c003c1e0716010190f1025400504c00c0c41c500f00700e0001d000d5000100b0f19100c42c80d050003411401ca002810440e030303030403036800d00883c2d05000485c1c030b43c0050305000b8502000213030300c002c9000018000d800311440c10b1040300d422611a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 459884730 1250 459883480 459883483
    0x6080a0b0d050d030609050c030a0207030918020405090903030f0601050c010b0a0f030b06040921090b0f030906071b14100c1107060e030a0602031b040f05040c030513140a05 76
    0x2207410841d1158040001d040030150907024000c0100310440c410041c078580925481d030503110081c07143c03002550001b044001c1500505010300901112181c0951100000880710000d500c41e010303040c40707420701f2800207041d4240002185d01c0f502508aa14806840b4100151120707000402e00791441d54031182d0145003904c0340f081e442e00070714080c084000310603d103040c80700c902c10005c1d00d0781d4051420700019401080d070311100c84035443d1001101c54440c03900480e04540346440c079040708079003040001c0c140720200c0d6040c0181d401076500c0d9081e18180c0e26491f0b0b058400b1030461611180300482452000082f031445103c2e940c032000110103840241001c65071560489a0075a82000465107804000c202c0ca4010024003002c0c0030315003070929200011000195031480300740030060609030004001095068441d6004070800c0c080d0032400d80f00c9403500d481f68690180c0c0d003e0140110315055502060030721a005e2030340140024912490613000c2a20707110f03140c17070b85c14101c05414440e444121001500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 459885980 1250 459884730 459884749
    0xd0c091802010323062110061703040612020313050a0c03050609120f1b1507020c040b0f0103090212030c060f070c151a13090606080d0906080a0b 64
    0x104003410300002280d100140c11200c903d95482180741341040001c5007104481c9030150000c10071111460940128080030180c1c9090200e00c040034015880d20000a1055401042c240c5500c0700c4c25040180d04c00d21210b6684c05180b040c040013404e56401c0110800041c1d00454004a11041141d0701c580300d81c948030315140314440111803800c040c41e81003090040600c031480d0066030303038030240010000060b0f40c03440c1c81c007501d860f00a070302900080c5400364050400c1c0d6500c102d80700b40c09880e0520070440c100c0c0c18200c02100d1303040c050b010f0200c00d103640b49843c2c41030810010009164032004800e61004500814003444200c0e002907420740550107050341007010382005150b41005003914580b9148030301100d400901a44280006025014005000e40c0040a501c120340d88001500c1003400a1102c07482030348521480c1c01160410040c40c0c0d4101903007141840c1400f0711014400d5a40d1901026599495500d89100040b44404140441882400c02075000b28504201050312400000007825690 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 459887230 1250 459885980 459886001
    0xc02041b051e030c0a08130f030f0f03020a05041503060b0c030706140f131b03080c06090d020606061b2e060509010605090d05070801060807050a0807050d0c09 70
    0x540c0440d008090101d01503100b2220100418400d08604006925400902840115109200c01030700080d820483d8580744250003608031500c414503055031308000d080c0001c0341d001003000502107101102c2841c040c0c004c4844500803655001e00e1319280c4910144500c10b00b1103040100340d11000c0002c0c03c0e00b01507002e44030641041c005076139550000d141030011035018480c02a8019291010002d6018a102c8803075805050741c14002d40d40541441e120001040302508400320040744400070040c411840003034076011091204881c115141c51884550340c0c82e1400000c00180d000c1c000081c80d80c140b90000d00041c081494911190100c10851641803d0107040610325401040f0100744244943c09599840c007400c1d10f40400525050401203584140d05004503014000000707050384140d103d40318040d481c19045002d40d20141c0e16607001d02c0c003a240c144511710346403140c0d450200f010718196000604607884440100121450142840350b031080a004c25141c91a0085c400a01410140140c81560 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 459888480 1250 459887230 459887237
    0x70314011b1d2b030c080f03010509070c0b0406020a0e130e0d090806010614090409030c050d09060e040c0513090605011707050304110307080a05030301091d0d0c02041b 74
    0x60b000c210720a10200d078032102183c8594042c80b0359228141c04008810401a80595405008500c0c0d040a0700c05040f80b00c0010311512000918a144e40d0084011b14113071541180c03041025120010308594031001050090640e185200105001900396802440c460a0b00c1c148028030780e0510001900040140342d4140c107550300d0f200020303011138080c05a01221030490405040141c2001215590b03000e050060006100b25500f2140c0c030410400140c90369004010001c1c004d41049140081902d00d03d250101c8562060003c003035030f514021950030b01a946140d5405d0b41c68a90fa0f820030010741907074910a024407204100300d40d000c03002a04440c001e0070b111000403400e40d207050001850700a11400300c008100c0404180500d140d401001c0b20380042e0007110818100510b0360019051418640c003411140c4900c030505010000040083d604031a582d85c0304003ca102c02c1d620341e118010319a0b10703074031550300184248440b282c0500904240765001500000d00e9121000186c070b82600c0941101010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 459889730 1250 459888480 459888497
    0x2010501090e010603150513080f090f0105270f0301110c0601060e0a0608150603160e0d030c0206070819110c0f0307230a0e0402090106080103020102070314011b 71
    0x4165079805000100c0c1480c4000300110307032035610b1300d2010400700c180601e038058681004c100c00b04900140510002c1e044030207a6680c0e4003a02c0300049a07404190214090b104415241c8a150300034030036103101401007003145644003c0303140501d9200c80fa1031882588110360301e1003450a51424420b40000b026103003c5596a150003440c1141342c0a01640032800b044018019121182c0751410f051040b200c1a00700051140c4849412501056405424035005036000c0b0802141132510f030140c1e007100c1801d48508220980b20000c1c04042000440c001d00414007110090006003414402007000c0c80c020441541030201d0601c0c04801d035100801d40c50006480d00d007968510740c6050100002d049002c581c0c7c03a0760803e0000100b625a08103106044221745100c00f0340140502000445549681c0200b01c6006a0744035045c840d0302d440e05490585c02151000000b003650360007004124140c1c0d4051b001800214550368800c110440e410203040265521115000501c420700c110720382c440103103521014038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 459890980 1250 459889730 459889739
    0x1060b070804031e02030d0e010309050d23270102120d050613020732060f1005090705340b0916061e020304120b0f0c180d021f02010501 60
    0x50b2034520705054006511444c4408016580062442000e205a00b040b103402180440160001c0c2140c0b070300580203014601c41c03002c046174401981c01520703000800342d48420030315860007011402054150303c1041c50010308103062026224101d10070541c1407040b82c8400c14191825400c1d41c00030040594181c1d220300901c00d13540b8000101420f402d03120002141060034549a80b00000030032419074203090540c4d40c280c03c00212600d500040100102d04a90442c1803500b1983c031142c1046070910581e01d010316012400340381c10341c0d80c030b80510b66980c0e441e03050850b1800490021400c8a40140700c1c180c1500021080405000e07240c146580200b44540c070620300345015504080c0301468242d1503a40c00030050108640000e0803c404145048003100c1c0184c110304141d1551080d600640309506088401404000c1403110051007402c001c42404440e84440d05541c645000303110b80892000e4081e00031480c035003000d400e0303001041c0c0000c04014040c115036100c0c414a411031450040180d45400c014017 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 459892086 1106 459890980 459890993
    0x1140f04030311160b0a0509030f180103090c03030509030c010f1706030f06010806180a11010509040912020a210212220b070201110115120501060b07080403 69
    0x10300104c91803c0624280ea004c5540101d10f030b05110028901550100956807841c01400c0340360300b05640a625102c15010307801544d81019526100709020030030769040f0000540c041d807034a07030391907017840240b5050495183c4100d040c800c081d02084a541da10160200204447c003042c0002601c1c1e150000303040c001e455003401450b210302c0c400800c07440ca0100e070990140c03005d041401d080351040f24826032524401c400c0500715090030840d52801c0e501500c02407240c0d1400400c0001d5060305540c80d481c0c40030910021a005900a500460412581c04003084020000c042c0b10102042a082c00a50f60344100d5104e100d4040041120000021541d61501c6005144040700a040e074850503110100d41180c2c1060f400241059603d00804d001841000d1381031404080001c0454100030400e1a04040d4400c110380641d03880038001349160110000c1c212140c4500c048642d10b91450030070b40d = true := by decide +kernel

theorem cover : BRFrame.Cov 459712230 459892086 := by
  have h0 := BRFrame.cov_init 459712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 459712230 ≤ n) (h2 : n < 459892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
