-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2696
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:28:16.359977+00:00
-- url     : https://prove2.me/submissions/23ad0a04-d066-4745-9922-b36e988c9f68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 484712230 ≤ n < 484892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 484713480 1250 484712230 484712251
    0x702010e060f0313050f0a030806280303050d0c091514041a03011805010807060503070311030a02180901060c08070f0507080303180c1c05210a0206060a03020d0b 71
    0x940700040d109456402600c1c980d00c00d41510100c0800c05c901004049004042d130380c05002c400c00281d402900125003e040e103849000d01c105403900a454035808880344048400360210069900d09010340030390b20074003940d480d0301c0c200100320302d00e98041c01d080303c1203912043c032007006845044400c8034070b41b05100300004882e0040000280705410306864420f131a0700c05804941c3c03075142034002007801110f11202660181818010030801c07401080401c1100c10500b0b201da500c0e07071990021401000340c0c0b1800c5451040101c140904101e0542c00f03407003070316901d200750482d2400c100100080c6440c240f15250000b03116600c020002000900031f405107034400d0b5003100c0051095a940b505009035900000c400307500200c20881e14201005040c0c4130781c3c14070000340407070900c0b05000c00c281300e00603c60600d8030b180b5203400c401080b10030409640c0e40c00c2d0010300508140c440e1134605420360300c9048068014458030003c0b41b0340d888c02d1603181044a5005018030060550303070340c0341e45003110f0040440800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 484714730 1250 484713480 484713487
    0x6070917153d0e0f060f0d0311010203010e0103030e01080103110d051207030c020a210206071103120d0c0311250b04030c0605180c13060b0c16080f030702010e06 71
    0x1142d9004050b840c01d19001100c1d0103001d06001c0700d02c0e0603910041c40c00783c001440340e041c440a610340c0c044519082900ba01c288442010780d0074142e07010344851300d00720f0a944c0300000024900f113401d1f8030203040e240300e031b5074513071a442641d001159030000030b00020b04181c18103010101035241079020501400d00c250300382e808496844000e4080c6070028030307042d40410320b0340c42d1407421407030007400032000f82c0054582d07205850401c0c00443d83c00090304200900961000a491007404065181c070304d20600001c048a0106000041030f00654204d50200c1c080941010111007003a4000e000d10f6140442898030b6509207100034410047e000f8900e4000d8052404c0480c64a0100c1e005041c0035204501944841d000c600303041c509132088030802400c8003071503007a103108524000c9010030040d103100c1007251100c12618400004100030012640300d151981ca0004080c000c244011511011400c200c6081c00d40c1c171035440a906840d4046110f484081e5001081030200660082d6078105450704046d00341c2e0f08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 484715980 1250 484714730 484714801
    0x1502151609120b0f0907082a0d050703020111011404021903080408010207120801080a030e0301020d181b081c030212040302100c02030f0d0515030607091715 69
    0x80c902c0009080c2d40d0642003e042003640c84100900c0c079081042c0b400104400303441d103403016884140319501c41d802d84880d091400e0400c540e0740d00c400c1800714002c2801c0d0b01d1006502e00a0744d500000d100c220302140c000b009140c5900c0301031055507071544081c2c8480c10b035a40c5503030800802c1c2e4803a001c40f0005c0d011520001c030103c2c800401a00103418400c1c0016519078032810868020350140090300c00b00009400148142d45011400c1301c1c05940c0f40c1850900480780900017070180c00b86610704d035007032860a40d1494030b60452410f29201a800f90012095418041c080d10140140b54020851250f000341e101c00d40c07000740d020854900301001c4c0350046c100100200c031181d1026054506500507032100b005040c58a01500c81d082e07400c48180000c600d0858140300c210070728003c200508082d41da40303500243e0303c01d0b0303c6280c4801c5041c0040503102e5500d0441c002501d02601c901804400d280c82e4900c44101c0e408c006010b5820b55111100080b4641e541c8000400c11400310058500c1d1414000400d071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 484717230 1250 484715980 484715999
    0x915020313030216141c1b060e090702030a0810050d0c0312080907050409031205010b030f0a0c05031303180303111915230c03011502151609 62
    0x40c0956078480d1004120452070500a1910b101c0c1d4901c029140d41a03442000185090340c101800b140042e2140941300700a0b00c16100101c800200180c15a01c030713404100c0d103103086600c6460540d10300e80c40d40c90454401c00c080c007244000031a00c00380035034001c1044c5001c1c54000c001d9280c1c0400018201c90603940c07210003181d03400b607403840200c4552031111418803c201031111090041b0240c1e25100c03015103010900d1a5503201d180c03082600403035441d00c0c00c1040c148604085881c041140506002d9940d44103100ea6075540f085910b03070300da804401c003c14980600c078003440785182c11540e2118155114001c0e2035018454415048042c4000382c2400b00f41060000c0c4540b009500a448400e00c0400381003005042c00408040810002c821100a00000e90004a543d110300c0040300001004281d0310510068400310b41441c1505107903200412078030924a00c0114140c601c0704c9480038030b045490742d041ea070344d5010307201d1003081c409840f00282c180254404130440c10616490086601d030707603603110396 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 484718480 1250 484717230 484717237
    0x40e0a0506060f1215010201150b0a170f040309081f02030a140702060702061810021813020a020c06042412020a090302040c05040b0a030c050418050f0606030c090103091502 76
    0x1030013505034202c01c0000542501e008a9070390361080c00248a0a000e80204204d40785003401402804140440e10740d03c0030784501c41d03000d0b48001058100999062610305480f80307140c1110b00310009150795002140008011070910262203903030707480c254541001c940f482d01030342000f0405130450340d0f1880c845448003c5076410358050075040e0003078801c505281e030000742440c0d001014100071815440310004000d000250b00c04841e80100300050301da0005000b800070150800311507660201418500c9505c011880e80100042c001c1c0d9001c507076984c0402024040c9900440c492041201901020030a1403a0514051805110a8a0865a01c2c4041c030100012a0481400c0400003103d0901c14011400c041c447e41d0812041c1b0705050b800e00785840f007602003d214040300d001c10152078030f1481880314060000d0b00c0150011f00b4001380180d4003401c04d600206003c840380c4c500d1a100c540411aa030a11100b12070044145181c0c040c9000c0741e5000660140049001c200c418080710355200c2484560751002d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484719730 1250 484718480 484718497
    0x41e031b021311090f03120d09060b03010507050307020d0f081303030f05190605040204080309120c10030c020606090402012309130204082a0d050a02030a12030e03040e0a0506060f 79
    0x1103850f42015401c4c414a005c1d5103440c94040c2c1e107c1d10102a000001006444842c0401a80411013440e1441e01c0c802800e40ca0f01003580540c01c2000303000c052034000000e1807191708154201c801d1503403d8403040314000300103c13144010070080c5000c24404045a8903c8040038003034180801c045140000040c01c440048403040307050101c2c80f107412489084c84c003d80e80100b00880d0258140742c2442e61007600c134801c101f0300c0d070312410710320170642e6824800740b151884c1130360020558142c20340d0025002c1c0c0504800b130304100044c0902c0000425500d8554001401a034043c1c0d500302d40141c0c0301c5029099864844d0000d04881010300c641081561024048c140d8421011340250301d5600d40780085203000038500785640103000440820f118810480845c04a10008980014003040f0500340301e801c040c10b109003e501401607072584810701107454110452820b06540c2003080303a400d40390440c0c0301c0c0190f00452461551007004180202c07444d07044250030500c01042c2c2d41c54944852a5400030740e005403076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484720980 1250 484719730 484719761
    0xd02012c03010c050310171504030203130611150703150311010f0801061e03090212280f0602030a02040b04060806041a091314030a08041e031b0213 65
    0x245041c00c1c042e80c08040e015091680c2103003440403a40030b40f102c040c000c4d000c02c1003070004030105411041202c2c0800942c4003041c03a2a078141410025102d41c40f1094070314a050315400c0000b2780c948540b880d00c0c201800100505610142c01c00e0050b8a854040d190f1000c143d11507505144084107403120744011031041c1071400b512740300705001511081500451b102030095600c010405d00740c11a00412509203005580400303c628804250010300107040042d40080d0124441c181c0c000001440544511009610442401480c0030044103800707084001841001c400c2130b000c00080d29600550781100300700d01301509080c0c940c407801c00380382c225911a00c001240f01c0180000ba040920a0141f0708040017550144840c4000c0402c224080150088110400d4254401c3c24040d1001090040c106010190380d5201c15422004000c100190b4040e41c00c041d45c0c0c0c00c00c0034020b820180725400c10354503031079a0f0511080c650918084841142050341c200b8040c80e04050910014030900d02c02c1d1280303e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484722230 1250 484720980 484721057
    0x319050d060614030103110d0b0f0f011a0f030405070510090303080609130b040302010b09100e0115171e0117010b04061404090201050706060b03040506090a030e0d0201 74
    0x8030003000c1e106142d100d10284241c05240203140c0d07116404a80c1580c0d0404501505032107c00c0c0483c02502d01d0020250400d4283c000703118020030242002e9000d42c800e1580f400080c2d0b202d5a007c8a411100001414072060400102c4400c0100030059a81300340a4000d80c0c0c044c96440f070100352010444031807400016003816060003015040400280c000100351900f00c16072510f591030480c440141da0000d040c05060400003801c043c0700b500070f0075800d0030290611a00d800c011070324109d42034079401000508c12403c00089802c001551120f41f46002659482c21425020520210880400f03048200344004507240d005907417041180c1d079030080c100c0300206000d610350414441e00311060030404911450401d0400c100b0100f03014030035000301000b101c001400600d82d01c016030301481103100040c074441c109480041e90f5201107029510031402681a5020b941d0780124581d15140411001808a084010125600c0c24142c0500000500c18140840c091007010003610110710090100307110001c161 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484723480 1250 484722230 484722247
    0x31902220b0a06031103240310020d0c02011109090702030d0c0203070c120f08090a05040e0a12080103050a0602070609021f02070909031d0102010207080c060a06270c02031905 77
    0xb00450002c20584ca0104400c20744040f000045120103010403030f03540c200b5010b030320b8581c40c910340080c401440142250400310a90240c80080e4010061170115640780203244050131b070040c010860421a14213400707123442242000c0112803e80070b4808411032006011603898000c881c40307541480c105603001903807942c41c5494009001c04035500070b20120b407011058140000d06240c0c41e607100c59070082c1115103586040000c00c00501c0c0c560310082c0d0143c00c24a4031004c0b00380100d000c0313031045d004405c90740e00200c00c158152480c040c2844014000e501006001005c00d2081c1d0180000910591000c00c02c100070b03400080040c440c045040b13168040c10c040640045404010031001801c1d40001440b0321649034130b0240024400010240381c0c81075404881d840e6038400e604440b45140d02c960900d485c0d40720300c80f42c2e594500e4200c1e003904a03245000380124511700f4049082100308489100704000100a0811001070051080100154401803140e048526040c5403252000b103695034503075496890f103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484724730 1250 484723480 484723489
    0xf0b0645041d0607080601021c081e0601050d020904020708070b07020105090c1e06041a2502060304030c0c08030d020c15070906051b03040f23031902220b 68
    0x3a040c03003080903480c42c040b002d501240032880d070b0341c024031030b0905d404596500d5005074202040c004100740908101865064401c0e044035001e07015500107005020036004c1c0c0c1040b83d034a041e0980c8d515002c15003e02221003142002c3d0010500d10002510145c189205907550301072030780106400b1a034464110040005480d42440b5156100e072020008003601048900810302c00b16040359960000040e0208042003038036040c003114000e200f280d0b6480002d50200c3e41104c2e50741c2007070070362021516080e102031208010840d8514038461700146844e00d1901d695409a0303186488941c01c50f03440f1001c1d0b100041089003070002d800446498140566100c807044401070401d03840c82e01000d0021070302d00034031101c2c80c2e1045809080d1441410103c1e5078100c02d40c242d80034014028900d449921000038040761081350141a0701c21901002640100c40b248021203040f03000b412000550940c0c8000c550f000354001c044440c0501c01e0014200c000c1a0324903070301e0341411104250010010907140c000c240d016042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484725980 1250 484724730 484724741
    0x3020406020f0601180f020909090a031116060509040902030a0501051501031b0f02101503302303010305030703110a0507181814010f0b064504 63
    0x10b00780251038190304180101380c2100ba21244e9030314040da0b40b803040e040d9100e194110f0381c0c9000014058415440c1000030306030303268490039007100015045030320f80e901058001141000743c0d0428003071443d2242460011102900036150866009446040140240c2c42c01c0c40301c022045c0c002c0001041d03a2408105d40464100b01c10180e504043c40d24034050080b2413003400581c9100c01ca0301e401e100c0d0050b04142280b4200d000358007180701c241350502d0b42801c2c85e1082c40960841e0b120303201c11a00c03408001c46001d0740c03420f0520122509040d4210640141e40f26120542041c01c842d130751424052601154404160800d0700121902d038000100b120130316402007846080c0c02c0400004107031006d80c5540d10b6480e01c03814840c440c01c0ba901d0447c0a07461581c2600300c0f101c104401c40b540340b04103c482c1407611031400483c0b0505207035403900f0b04030300c1c1004d400d00403a0901071015000600c1d00204460130402e2480710000c008091524005480420604c281c0c01354580c0d04141013180d0000847c3d040108882 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484727230 1250 484725980 484726003
    0x2a05210711010e120d11070f231f0233061201090308011701020c1203191a040b0913030e12070f0609060f0e0613030203030a0f03050f040506040b1e070302040602 71
    0x9011002c100230070342e443c803401c2082c1e400088114903003600050403808030a03c40c0945c0f55106100510070001e0381035911040e41075100d190300702c60f60702000900240c00000302100680750b0308060070303514048000391410203810040140010032000b620a00003402c4481c807060440c000707a02003004110440307030751003a2042a8400b4000310300d4014000d0810f40e454110100c0078141000200001d100704808061582401c104070601f80101c030740d5010881c03080004121028429803030908480703900d0804201d4217200340a1001405088a4030303880548a240c0c030040b9890344901c3d000311000f02d00106024035801045c99021103d0341d81d041400107070142e10690848010042240845110643d10501c520003000050b41c5540da10890204504403a41003a08040c1d018070000442410b900c0d440341c100d40c284811640c0401c480c0d00d42034524080c52600b07071005400c65000001040100b001681350f01d400c61146080303140d104003248681da00600c03048460402107a0b01140412440e40c0502000e00c204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484728480 1250 484727230 484727233
    0xf0c06030105300109030504090c0903150911040c091703070506070c02180c1e090307050103020f19081008010b0d0809012a05210711010e120d11 64
    0x540c100b0b004181501c0943c244114116080354150b00d068900326001541180e602000f071050814500303015015a020703204030281d5901c1c1442410007944240404c1d01541e500001c00d08180d480030b03211a010301010041501d945041c10701c1c80120356200d21803000c0010182e10fa681410303180c5003019100c94044004200e40380c004000e031000144d004217146038008000d007000501d02e401400401c1011190340e4010380440c1c0144240615440b00380050a60034503900c034592510504c099881849002d000c030220b42540c4101c2044c8650b40c040d40103842880310085408d41070000b03036101a41420003440b0b480d4041000c0c00c00740100c2c8141c0c1c0f4081005000f00a0083c0488990480817030444441d450f40a095984007007004883e60f03228004000404c0741903404041800382c4030011543c400b60130101120782d4070407108031400e19500c0a1f0450b809030141c440700d608290954540008200d041a01319040050007203941c400d581e2100c040208a8000000030509130701d4251000d0190040282118541d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484729730 1250 484728480 484728487
    0x13061a0307020a02010813050303040605010f05060408030d020d022512110607080403021c0306090c0f020615060909040f0507080c030307061e020307110c192601020c0f0c06 76
    0x1e40c0004140920035030a1806c1c06240d0ba40d4410364402e220402002041408000309200600849810160583d43c2d03421201c9070041d5158200f02c200d208911854600d41c20500c84060500c040f039000d48001c0b85440c01c09850301411101009000900c42041c440020300c502078001440409001810040b5031070502000f030000c1c007151556a150300500b00d0041205030800134042500c2403060f075491241030198403003580031401010700a1301140c0204000240341c129400e44940c42195044201150754010301031540700d5071005411501090100b03500220208801c0090f600c0d21034085104600030b21103580382074458a001c904043c03480e80225a25807201841c1015a60048101c3e40c1b6586d10940024402c1aa200d500300b4040c00500c0c411190b0f403020080180058010300681810f4040006691091000b00c080060324030018009031054600b03840203215030883d519001081c4202040c01105001010f40c8007401d80e40f040d41502c140340c0080c11030409280c0c0401c207605030404119003841c103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484730980 1250 484729730 484729741
    0x406030f170301030f110d02040f0b011205040b0117010b0303030717090604081615090b01030c09110d1d1f0605030a050312070c0c08010518010507120e0c13061a03 72
    0x17140c200d00d410240c510041d450810303580d030703480648a00c0c0041d4040c009006102c10003540a000b0040316556a0105491944060700c3c9041d80c400c0611031075000304241216402c101e00500c1074038010052010075940c44050540700c2e81d08202840c40343c0705030b94941c285010f00f031010035500c41c0080c000c0c1c0e9aa038002401c0c000000c44070019a140603142c0459a100455541001e20f4964100e90340c5918132450000f844091104514105040c1d902502d04040740958944510b03048440741c503a641c03110341050003000e1070403e0541142c11500b001c00c61491781101204529410618500343c1c0d081d40f00440d90411030350185c2c9006450080c00118041e12a408041d1a4180c0300d214440e62030b001c0000580015414900903501e0705c0103503401a002d8102a41c90b699114020681510941c1c0c2045c095003542d0401101405214810209990b6407110001201248005042503000200950107060401c10310780d250700c020020301e50030100b0040350315841d007041e08108000c044405422480708008001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484732230 1250 484730980 484730993
    0x2090f010c030e0f0f0618011803031b021f0305090f01020a020613020613030f0506060909101a060a0c0c0902121602011103130c0503070f0b0906090406030f17030103 73
    0x106403c05036950301300e18900d1310010300341c900c2d058061540250702080011854040c1d0755981c00d905401e0300c0c3d45c0c0043c1451718411900f21020b02c802000900c3d44001c000e041c04e58400c811216510260403e002c0741c0720f560386c5070301c0c48010204c81d9002a071740c1c0040107070328041080060040d4020300000c501d00440094006e48a030001031140072042858050402103440302c0303048440c44d0050514020500d9106e01c1c0c500308a0304004400d50f01d91043c4c00100d04140b61030301101d40248001c000800b000ca00288441024001143c15943c017081400d8ad40780307007038031550020880000940d451030a040340a14002c0303000800c0d5080003600c1d503c14808104110110028a600704214aa00c140c0c81d81c0c44030400c0b030141241e000540140c01c808001e00c0b03161130350000c0c0c0540c0c0a1080088181d42a10f038400c2c1603503100c0ba4455000c006080d40b10030492041c80c1c0c4018141c0020140c2600c2c43d1410480105e000d071140d0341d05c110b071802e100e51003a50034018064a041071101181212516651650b03d80c003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484733480 1250 484732230 484732247
    0x260c0d05060f1b1b0a0804060f030e0601060504150e091e0c04080307020d06090501021c140c1b0106030221120705070302011115040c23030304030f0c0f0902090f010c03 74
    0x101141e0903004c03a080c07150340c01c00c450416594408a0156606d85410000b032890714241d0181c0046818928100354810b00498124140c54a59545e0740c24107107007080740c6898003c64224031040c4011890740800d60748480e0b45a074031802c060201244a425003003041541c1420080a44004d941c040c0810b00603030b500401240ca545404440740c0c5140314031401c010703008181d240001011580300166903e480d061601e900c500389008450304105500c80707481c8500380b070a02160440420001040107003041d11111a00c502d000502500000d4030340e80707a5000c5001c640710300c2110030304d14030301001800e1401d804000d50b03c018001c011b8010f04200c042e56030b030f03943c404103808001d06004040d89500e00900c810440719801e034042103a4408582000c0c00c1591146250340240e59031210103c0c1d15005c080e45d2101085d404440140080d40ba16140d500c0d6000c9042da00f480071076000c0d422a0000890481d050030341c0010f00303050030005940b501018104408002070b60038982c14000d2000380b01e000b09411a221 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484734730 1250 484733480 484733497
    0x150109151d04020105090d171b0109051b03070902040602071a0c06010512010b04241a0304020d17071109060102071208031506121e0408190207051e0301050a0501260c0d05060f1b 78
    0x2804ca44402400033f4188085500916811440450005040da40c0029803804403501d90401850004683c0d451050f644500c064005260380b141c0c00410290500d05000c5500c0610440000750404050300000e0540740b99100b45c280700c8525000701100d0314440701044000b02034409070400d07444000a0b10b20601d02006101034440c0300c121120400380410348071244500c0c400310404d96a00c0300e007480c1c550800710b10b102c2d90a000350660030000350a07500000d010410f036055154207003240e014541d5010103a034801800300482000310211a480f0b6120385c00a0302040ca0f008400b1840c0c4c0c40c01041512143c82d040c06041d541d101014140710215209404980161844511a41802c811440705a2514072641d00c0a5004001103580c040010880c20042540b02c03801c17070080c86113856480900c07060320000e008000704030f0604090303c2d050b404926450140c21201c0f03010340f404d083c0740e500007512144084d202901c140d080442000000800c5100240d07001038030030300030f01c41a00d40001c912040d000359a030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484735980 1250 484734730 484734763
    0x50909070e0403020c040905030a09080303070e0621010f1a0f071b081606090803030c12071205010311120114070e03150109151d04020105090d171b010905 68
    0x1160030f140c401e11041989200c058401c1c426160503162003540c0b0b904c4030180701c000804048002c6032141010045900481042d07880e100c3c2c40c06000b0400a20398800024040d0b14030a6112251500940c040194000e049404410100d1403030601e420b040501d003519a10319110f01000707a0300c1065019000e460003c0d410040403440c5114141485540d2441034003c042d6920603403510744000441c400c400b40564115648480394107035500c40b05560b902013a9003900042905100603600c0d4118003040329801003403407910010702c2003039621150482c0c000b0703081a2520744400746e01007583c0c141400c1035504441000020802c40c0707126003070006404000350042042024110981c070700da990410109400c0d01e40c0a052490950f5220b0013080140f001c285160b484000c0c2400014401d02c90101000ea4040810011491035503158011100d6a00100a055201c00d05041d03920200f50000c154580c4551803100f10380c1d4484118904890a2006458580b41d51b070405000700d0004402107407240c00e007822500d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484737230 1250 484735980 484736009
    0x302040806270706080c03060609150d0608070b0a0c1703070504030c0e070827030315030c0a030803010311010516050c03070b04051c03030e030d05190c0e0d0309080709050a0605090907 81
    0x1000428521aa856140d0b2100b18420090b019072182030040c0233424402c1000c020742561000c41c0354031f0780c2c028411074000801c14840e10120a019801c0306115030310030388194440105216000440790402d48134040060b2020170140200904800d091014000e044c4456049140030b01e0001e01a582c01800400ca08540001040003000b50004040034400d40c0c0c0141c1b07480703152540c521841d0343e002049407882440380004928035030815440b43d9040d01e400900d41c5207141e007107807544070199848141190401ca0708101c0707140c0b40b01807045981c510134404c80243c50310301c08070420545410b215400c8100c2c0d80000700010025995407054070498004501c22250070024107040c103030b0007420104100100b034000050500081030715544190300c90800c010160312040701c4d44002e03004507107c442802c40401c0140380c9814151900324908031000d4400d2030701c010749035211140d0f01c1c203218050307020342e03440d070345403800d20410500e140280009004155440d442e03914200d0102c40d034980c964800d000b242e603c2403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484738480 1250 484737230 484737241
    0x6022d0a060f110a18090b03101a0907080a05010f05210307080f03010e150d020d15110d05010b12190e01140a0c0903050705060a0302040806270706080c03 68
    0x5802c418403140e051403080d42c0b50424183d014000d041d006269801c00c4500c2640030440340821f200d014400c100c041d0040003d8000480068001c1c6092041008030b84904896400e02c0e5980508041c072072107250341c030794905050400708601950410b8203c0c03400325a052000340010348800049100d0a654100420351640d41100c0c0d29055108050002d055035600184040c0b5011030080114125800c40580c10055030750554107800c45e5112003021a0b10002d40e1034500090301d8240480c500b502d0050300d144060741e64010b00c400407501c203468041e800031408541026440038034030900340100850340d509842d004181d1481c4041001c010b0101c0b101410f00007061141804da5440f1306462015000208407014107248c07403883d201e50890301c0c12249400e00e24148100e0303206140d4841140e90001c000d0656030300f40300802400c0d8108190600800d5402e000000340032400700201c5010b20640506810154245140b140c411080340076800e040784e0102d8002c00403e80c0c0101c8840d030040a404c40151a034450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484739730 1250 484738480 484738511
    0x20103050a0b01140d060f09140a020f0f07141b04060b0301030203070303050c1906050103060b180a020f070f120806060a09091107050f060118090203030d0203150a06022d0a06 77
    0x11ba80000061400340d58000c9041002039104d1070251a04001070181a903d0009810591140c140c40883c0101c0502003000c88007070842c06416a14801c0e03944818560a08850310f103440c1250035410b00d951000006148a82410310620b070140020920440c41d42d8119004aa518029840300900b048000503144818190500800b02014449451400480f48a007840c0020300300a0105481c95490031038a0001840c16070501c02a0300500c0745c00603002d80d2103c241d04001e4020400640030802c3c10041c460006600c40d0044d80103900c50124010030184581009000c0c3d480140002c1c094a01001580301040c0c00000d40c404a8009410200d04034000111010f200e025640c401400d6104401070704008844c007240060585045d000147d110702c3e00c02050a080d00c44089000e50503400822080782000f202d40c00650780002030304411514003015402182c101c024a90000c401a044900c404080c5400d00d42c5105016a20a00c410b260800710f049045e1218644640203100c107035070360740d00842d0070356 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484740980 1250 484739730 484739741
    0x60f0313170c0303010603060b0309100e1f050f01091503060908040e090f0d050405061204060b1002150604060f0509090a082a060f04170f0a0309020103050a0b01140d 73
    0x4109090540350b0406480c5590b0340d8000703009400201341811000314900d505403081e603100390718180082420114032090b070401000b69000601803130188030401929081c448544101807620f601001a60b0301d052000700d4220b44043c0c104c1c2800505200808860740d030b103141024280c9030050740010740380ba09440c004082d88104d520000002c2d0703c00080150401001c601c411101075842c007511880c0c204014105d42510650040c01d03403000c41400708042c1001600043ca41c464410f02d80003d0858030600002c2d010f50340003009400503072240b550741b2740d2a0f40302e416554100c00300307072030501030701d401c2c404100c7c1c000c4480d00400740107042034000036400380420082c2c40455900860303516500c0c80c0760a000b5010300c282211030080c0d6401e1500030350600340005170041c450380f5a2225080d41d0b84490751400307420200b070054954207410500660b20f00c1124000100101a100d4400155403d0144000f40917104010594041146407690b100301d0303640c00140c0420b20310709007840e0a035281c4001c0b030b0900007440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484742230 1250 484740980 484741013
    0x120a06030f32071e180605100e1c05011401060e030d180e040503070b0901050a05011202150a02100e0f12030702030d0b0a0503060a0911060f0313 64
    0x21403019901c007448244200301c0c0c158580c15280801007031101d84607507030754445841e112070281d0086004005030b02c4011002001e10035201106074010390745040c0380c62200c0900050544240c0e4400d420402480c0c0142e4043c0d20a00c141072140e8100100c90010301c69642400751a52000d04051621080200c01c0d40400a00c00c4510020396003543c4404004002c20010340d8002c0c001d10450a94035055805401c0c03004503a9400f50a00945904110000200d000e01030320032140c2e44005c0c400c1d00001814520902d215042020002070340d440e10266a9064800680c08640300c07060010502004d40c5800c0b6803804204102c44000799280180302089180001d00043e0983c1d89152000c1c003403110501185170141442424103d0780404036034160f5001520041e0380000c0564401c0113041c4440c0440d03000010004070090114541a40e240042400c003e02190351301c0c100c43d964000c1008111540700801a401c5098400b2802d00c0348210082140e0310002d03001ca148150502030310810000c000a02c6800c89 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484743480 1250 484742230 484742243
    0xa051e03040f0303050123100207080a060b030106060e03150408090d1103010b0102071211010507081b1c052b0207140609060411010305070e120a110411120a0603 71
    0x1e14280c02c10752002040503004400003410b041c00001d4810241000020700c401481c90001c40582c074200704080404032504107000c0d03015124001a04d288140310694000d4056800490351660140c10142102e40c07503000360081c0100c16029100d991000115100380701e18014448206449600b4109558080e60841640c1308040000c00310401002465003007403424180c0c0240968002c803001aa1544c0090040f00341500150f01110007052200c4103104180c101814201d2a140c440c5d00c54030050742c810710050700b05a8100010a40030442009003150501400511b09080140303054001c1c0b540c4034651a44000144260905c8031000c40350b8450710060b41d072803034210355034010f07858005015030312120040001e00074200011441500452a07500c66070740324140c0140c0414110040d0024040a010641000340d051407082003610b0310700c14401c0c40c4500c02c00818900c6a2481e0061403c001c20940c14021402d06c030084000c01101d4007640c15040441178044081d81c2d9101003400148455030000d00807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484744730 1250 484743480 484743487
    0x22090602282d122405040902060909070302210103140f0c2407060b09010e06031c12050c0d06210f0f060908180607050c0f01020f06100806060111030a051e 68
    0x68248241c1c26200204104e40603400d655450007000f0440d01c0d035010103500301c04100281d0680745402c492032a400ba48a0030018100305204c01140401034011500043c0302001c6001030041c424403091a80b800182e0100810074805c12a52554a80d03202c062858000c0c40421441b200101d14080701e80d03000d40716012020b480e40c180d802d111010b898521340c02409040280b001041d65213803222064422000030f802807284090a11800d4032100140f07042c241044080346001180400e01d00810f4011100b130fa00c0103855010701401c0c0000c81e00039911150503d03011074250045800d601c01103c0b03049030040144103030300c0f140d030414014186038800000c000c18a44010710301080900b5000e003650b01c04549460010303942e1380707080c840e0703501c03c02c0710181040d07005801e44507080c42c14000140c240c98042c030640d015070104602c2c0c58541035094408858452840c401807100e20020012a41c1c040f0007441c182c40300c0c41c8241101c2d41c882c0b044101050804c08001618124040c1d20041a064044569900c0c1e94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484745980 1250 484744730 484744751
    0x70204052e031109060a17010902040510080601141512150913060522060504110a0605040b03040c0b030702030d1a22090602282d12 58
    0x140704450405010003004200c6820070241d8220300841c068a034040c1c1d04000e0031264004000414200a01c0d443e803040503100d0204030500715420107109003400301c00200e08400640f0421041e01c20040000c5802c0d4901c42042060b0302c8001492811640c07130300c9405c240c1d0703c03290020401c901401c40059030188400150440c4090f02c0908803481245019540e18084020798100440c100f000e80344400c91041088075000070031401e600580d0001c020811064207508400e018441c00501d18800344d0740c0595803810041806440e0b403000307042100860b00c03800038908121001c0c1c414002c60103407100c0c1e070f10040000303420403001c07002034005031900e013182e0b640380c1c078056200035030301d0380007103441c80d141801d00e984900c3d01217128614050318000113100c02402003103d0410164540014948002182c45541200c0400e1fa284000d050300d0745c24600c0000742040d00815584d40100943c078034410402e0f20307500a5103500c10744042d14142c000700d0901450a41e9954000c82d00b2094041451620500e800c400c0306 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484747230 1250 484745980 484746001
    0x606030515070f05040b0d090b0712110310060c03030b030703083105010c021339020a062d0606090801020301120f0305070c080c0a0b0304111507020405 67
    0xc03030000c09000562402c1d95003840441d803555000700c00e58045103041c002807103000c0900002d4469604d81003400210b0340c196032204d00743e620050350b04030f0100304144102500100d0305e0044000708141c3e070f2740fa24a1828011181034012082e4031070341d0104002e001130082094803c3c0c10100c481d07940142210344454413802e0407003685d484183d0207000c0c11124422200c1c0041e8404500502e407000703c0451140318600070064400101440049038071003d859994401c55115209001c0c1c100748a00400c2c041c2c4060301d2906503000301a001c1c40710002100403c0d514052340c0010b85514590780b2160110381c400340d07a11007100010030710141411000e060405441d07840c500380c0c450303422140650303510001c01d903030341d040030b8201d120a000da980a159040c071040e001c940c1d0b8603404081c0a21030720706646403c10f07544400d01c9400107034200030340d0303904081c0d0302411600e025030241c4050840c0320542451810995220041c0c90100130640c1d0160000e02d1100e0044056002a6084180c02034801e0085261843c1c444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484748480 1250 484747230 484747243
    0xf0807140303250c0c03080a03020f0409020a030b0109031502130806160306140102060c07050304050904050304050a0b04060c35040e0702030702013903020a0501061a0f0304020d06060305 82
    0xf5030308094040b0380380c8141071050316900103950708414960190f0741151107a180d10350201002000f8907400700106108410944010b20050204041c0140c80340e01d048030080c16601900580c60420040100c02c1c00031036181e86c0d6051050001c403c006170b03150380342448441034440b00d0741305c0b03401e501800b420008207140e1450309042c005010355081201545940001d8100b100c9403040b80d00503801940003501107000807005040c414040c500701c90400707542d000010700205c02100e0403566500b012a080005003815240c0c82c001c1c2c148107000c01c1c202410201c009003110100d03840a0321512100000949440003440680c00304911940c5103c080300ba00f800c5d56196501501c51006103214103000502000d00c08000d89043c01c0e4142e480300c1000c2c0000082c401c00c0c0c16210440114800690408801c110034070001c010024402c0d00030300440307032450903c18211020340d0300020fa075501c040e8441d000c44240d101103c50343d010f03040302c1a0b180c0d182d50001c205204030841c2e0080080345807100120a104000520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484749730 1250 484748480 484748521
    0x101b1118150418240c021f0501060509040213030209070c0b090c0d08391b03100c090f080105010302031209010507020904050c0d060507030609090f0807140303 70
    0x14a140d980c0c641c06000071074440102000c100d000340c01d01c49001524108403800d1030f1440c95891510326141e2221002152000c00590700984e0203150604454100d6001010385a10703400c07000c110941c94158090905e118000c4041c0c0710725400142c112401d9144e2840c5009150082c046445500d800b000103050100d00000c1540d1a0389020b0004455040000b0031361408807010340300c1e0b80082140d543d5001d660f00f0807100d401e0000652040e004071a01c560155000c03403e80003e882c078240e042d1034625404c250982055940483e07000c0c3e0102c0950b100040d00b06130224036800c00107820780621070125940040c86d000508282c5183c02c0009501d00c0540050381640d000314107490441045003880c6410f0b00c40c100c0d40320b000c50010b00c00000546408409164030a0003841500c240040002c0010604001c0031003c540301070b03941c1c00b0b10081f1945842600c0140086240400404040e0707150480c680300070304c1c0000d001703d0700041c02d10b04000e550000d64110711040b00460b0740300e003060342c1110b9214000c41d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484750980 1250 484749730 484749751
    0x206062e12200406030203040c0909120801061106010308030907080f01060f0b070b0105090411100807110d02030f0310050307080a050d05030f07230408010b0f101b1118 74
    0x1041d400d0622000b2180c031500480501c100e14051400100740c0217034000410554903000e90f00310014203000316004681c0418800c500da00007814110b40041c01009041c0c1141301041070b802202500c032480000d195054076000b940301a140d55401c80c42c18989170003071b00700d2010b9000d0070229510900f01500420160b034026460076030519110851590305004a0030054144541e400c0108001d041a543c20354200c4c0c01003000700354003103041c40822422050b94050030009900e140400c85280d500c081c0c40c1400c030700e66001034611040d1aa20080d43c9018202400501c1c8000001290b58102042d0841c001060042d060b110059543e4410a485814002081e034103400340040210001d44144e00f201e00c101000040381c4041d85460750f0484080c00f0008035005410410058207030140c80140250000f4400c08002240d100611010302c4000603040d2461405451408802003800d5003101e0400c030ba260102d23031240061481d41c280f441e81503840b003800c160480c2c024540c8a0030300c9103140c1d81902c034841805 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484752230 1250 484750980 484750991
    0x16050f010f05100605130506030705090f01020706050706150806040b1005040b10030903031104080304170a0f0318051503070f02070f09110d1506020d050a0206062e12 73
    0xa800d48800316081c82e443c9031140c01c1800900e0150010301300c07000980c5103000003182c44001086965005036000300204201055003003042c600210b07c203196401c20710140401c0341c03030440040e1141c0200b080c001e00c181d4956000203c448031180682c002050443c01f02c1d4054280381c06c1c8114076180a03103000007410740005002c2a44d0415004044207403078003030212185041d018008800411120004804250721803028801c500310320f102510103041104003440c0e85034500000050024000b2040a009804c1800c1c1500451380c80008210800d800d0b041c0060152250b40d2034440a030580d030020b135400380040c0140990003248c00b005c2d41c8a01d00603182c5500013408600c09a96500d0184103002007143c2441d0140700708607142c1c214204240d11060041c2c18104004452015151184c02080c060108001d04000c45a810040c83c200035815003401c80c548030035103400075140c007801440f42c0d000302d1003c100e1803075000c182180000449030010300700d201e11016401c004c0201c4032301c0706000780060415 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484753480 1250 484752230 484752251
    0xf0c030714192303131403160f03020f06160b010905090c0d11060702130c0f050c2806050702010903120c020303060d0201051306081b0405060306120316050f01 70
    0x50740e0390a280c02181e2001c0014a2983c00b03580811002c4841d541e0340820b00440c118100862034420160803140303016401c1c00410000d00d403501079000c02200c0e0300608244200140c224a08100d03054a8041e01d0b15480d010300d107408264113104030030720820ba8400700c410078ec080c08000701c0c0160503502a40e1050050744c68810034150b80340d10500700107500400368028040040c200c560846641c0780301900044c2000c42c90f80018000c910794040201001da15409001da007503902c007501140d00031b15400c000f41003003401d001c816907a4113803000c006405030842c6c0316194100b45d1400201440e5a0000003803000c1e182c0048000c0c00780c244100c0841c00f08010384440403211606004002e03020311281d0055044d80d440d407040041480121000743d060210800c00c8010407044501550b01070180c40d00c840350b060404441c0781f410445084603d04402d0401d000c140305a560b0f6034116034008a04495503015031907a41219421445262404154040f0385210307801005004a884560000ba00000b008460704c00e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484754730 1250 484753480 484753513
    0x30b151e131a031509060a05030f0a1e0515040f020406030f11040203070c0303240303021b010536030d030f0e0a0519061b051810080106050f0c030714 66
    0x1030f105043e504d034010411506a041004195510510042c989a0311070342d1000841d08200b6040100c5500342c10079012541480305404138040034035502c4201154076912519500d4072307002c01c601410b0364001c3c000003050900440d000d0810542e0b030000c008102d0142c0ea071401807244c280f40e003811031718051500e49440d03040ca0688284c9101c1c07035540c0c441c2e103c1124140d500b02c0003031000183c1d200d40d684103d04241c0b0300030b800361030500c081d500c2a002010488814a20031901b02c5070003140c0ca0402104001c001c000300300c1c441c2404129203040e400c1010a0407100e201c1d6a41c101202c2c2c0064045c4034088480d2080340e81074200c2119441e00800803c0103412502e2900d80f00c0c00240c1c0054110340c408221744544001900700500e000d80600d00c0014811048075950a880c5401e8100100090020a1003c407030210125a2100300804958414000400c0d04014003c0003051080780103003c004a0b1a4044050800032542129001003c2d40e5071120946414011460780024280c02c3e4411f100024010f18034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484755980 1250 484754730 484754737
    0x1b0d030f0b0405040b15030a060509030a180501050a0e01030f140712090c0302100507060e010c140a0e0907020118232a01030605090f040210030b151e131a 68
    0x80201002a440e078846e880150b03000c80051b00c4c0c80c1c042c170595440d4004581301d0f200f241d000d0495000590b40e44d01d800c4900802601e0315050810b04d50300152420009a81c001d030403600301c40c3c0182008a5041c0c01c07900140c0c018040c2510200c11a801e020301580141640015a4407489040d1294041030440a0f004d500300c0d400c1460040291581c80014809442d0601d0011256085460114604080b5944240a40780840e90b54007040c1c0d160002c2050242d000b0f950903aa21441044090800c0300d0444001d0080030901d0302c242c0194856008507507954401c1d0880000c5a0035001091600761140c034001403200003040d03002d0064940b803104058460801708654008060707010400319507040350003400b0780d00403e0308030740c6060643c0c1c1c41c0c00080c25152250700301c1c0301c3c4500c02070000c6030303191034011705c00034280c0c0b582084101031401900001d10740d58040003600d019800d90280752a455031406502059186440c001c42411020905143d00d6400461ba9401c4d51040000300c0140c02c050009600ca901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484757230 1250 484755980 484755983
    0x30509011d070308070f0213090b060f0f010e03030c0a0302100b010212190905091501080a0b1e0406090e160503070b030109150306020414010e090403080402061b0d030f0b040504 78
    0xb0000741c02040407410b9080507000441c010317041100041c3c01d0b903000a038114110300d1801c85007900c0b031904e0f009000d82c138603000b6800340042d580703040224400030000d1254601c034200300b41401206820070300c06440400684400d603601e00d0445103000312904000e56121580400307032030481e0815182c9143d9504c081480d914540034003000500304107544c2e00e10702c1108940300a80080107080d010005075952402c46150146100044400407401900c0004150a000a0040444504150404000e03031500050701ca41742081c1ca004030003880100300010040c0c40d455010300c000904210b01903080724404108059820340810280124958078000c4c152201900d2003a200c0043c002e20040000e0740345608020904c1d803e60701090840c41e00c9903101803c0781c0094102c4000002c0b2004042c07001d50700065050341030f00049034a002d16207003c0d58010030310840148000d020742c07400f00340e1450344006940100131003107000d01500c01c040c0c54400e0042c010441c40784040070060030b0180316031403070074240b0400c1e000c0d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484758480 1250 484757230 484757233
    0xc070e06030a05030318011e02070b0a05060901120302120a020601150c0b0c0307020102070b0106030b010e040605031c0c1a0f18120c0705030a061407050408030d0f0e030703030509011d 81
    0x60341c41550241d403810301c8106d46940c1e552106184120202300280d0048940c01a9070300513101c181c01e05147c2000700c1c004001d1400203191109202c034540c0e5442d201411502079500250115843e8a401c0303007402012924041c6074040422070045194022a0040c103071494403910100300106020202c5042411060143c540031b24080070843c0182800b0042d03601c000107000251500d40c0965401a24201c26803003800000e548142c00480c40d80d0112240d185200102e405010719400e003000640c8400080d45080451901c006290310030a0180b19501d920f503810200040f103500714150107199404c8100c2d0401c48000200000610744201e1005040200001100501c2e580d040c6904000403035010748491002485560070005e9190703000c00c45034001910030000414448003c562015a0f51005048907091000500091000f85000400c1d115a000311a101180d0707405205005030061003840301c1030181c0d00000502905064054200c83d0041160400030030218100722a06664203400c00c00d41300d200d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484759730 1250 484758480 484758487
    0xc07031e2d0813080a1d0d050c0406060f0e06090109080a0303060914150918010e1e010e0615180f06010906020c011709030409090c060e0405060607080d09080c070e06030a0503 77
    0xe45106c0c000314041c4444110794408611503440010304903103d000750854066002100c9003409040901844008004a092501508206410107404142d401581500a01c40031800c2003c41c4c0c4280702d850001c10000c4241c0d02080b43d03500707009002e8500742c010604980d04103c2d002c200b0b1154080c00d184603108030102d1900400d000000c00c1481e08000e01404865540744541402c40c60007032003125010f643c040700910395540140304841c9607698600d0012690b07450542d014260f0900802c03599407010180303e00c40e40701c100074070006110b03480c2c0ca0b4500016429076130070016000b1201100340d0140100342c0b01c440d005541c40d807089a540700e00043e1303580001c203071250524149442c01c40300c40d0007482c0380d8282d13401c080e120441d843c200c50015030156016100030b2820051190031200d1201d8200c0e054505201e24035000c00441c0281c4035008008090041c00203000c07008407801d5014465090b07103da4056034518000300610383e515128028070000940c2c000114900c1e14000441600095124024605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484760980 1250 484759730 484759747
    0x607020d031107090b0a08061b0307031118010815150f0c011b08010801020c031b0f010606080912040e04020108040f0f0305070b0c07031e2d081308 65
    0xc00300348404506018001c0690442000c0c02d00c85500a40996000040c03403185200030080d4041d5a0b9000381c540e034000100340b0038200c101e100384007045c0441c80c039101d50b641c45003e030450061200150a0042c4200844d68003a00c50601940c000c0c859000d0761101d1454965007034000b03524507022a0b8580c023104e1650f41c4004080c0903030192100d20001c2008a041058562819080d15282c440d03960300c018001455840694120802ea805020310100841c00e21030b0010741d181d0b03070f4441e4141421500740507403290184014108050070b90350100800074881d031642ca1102500d4103406580030000c034000c4424024200d890041500c04940055664001d1916540c00650301c50230050710540c1c0480b043c9030303100d0200300c01d11402c40450740b003586c4250740d4031240d080000182c20050035080c0c11000811030840800d502440031410b41c214030280e81e10b842a0320b9000c0c0c40b444c401900b8242506648220f45941904a2010070f152580c0741d02c0c2d2156a0752009540c200030300317110200421a1384180b01010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484762230 1250 484760980 484760989
    0x402090306160302040e01090501050108100806061504090c0f1e0203030a152607122105090d0c050916120c21092307030b1504090305120601080105060702 68
    0x18407440c4541030040c85c02d0b40b508054403044200342c0103074084640f20401000340d541d12807079040e4802d00300e1901911940c10082031a40780c800c060a00c41c8100c0954160050046414049030010715281e07504105102180320054400524050401c000c1105800852b040400c040c2c0c40d41c00c041c02c5540610b00e941e807001070540081c11b041c04a41c8504584400100c0c9042c7c00b2490604402500700d800500c000c0d41244851800c89140c000c5100318400c4254880003130300400c4040780080da001003075030200380940300441e44d500420700025448078500c260b4100340b21480c0021015110151046ea405940e5810158411140d420039000050750740228000d0b241c000d0342c021a00b0100307916210005048090b81d444281c501c0c5151881d81c0b0f992440c000080000007006e15600282040ca48a01041c80c0c00c0c44071744503d407521000e80100110350010300300019040c504018008001c01c100203060f0b003400d00030b000b500100405211010a0350206075103600441d00b035030482d000100668941311159003800b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484763480 1250 484762230 484762261
    0x1d0d051c090804081e0106050a0605090f270c090109060c1b09050a14010b09010f02190317011a04030618060f0b040b060309060703110708030c0d06050402090306 71
    0x1003080d00e6407a01481e001800810040c40205081801810004407240000b11404622500a60503078034107842042152580030a00c021904c0c90308140e41c8902914000c10344840030069996440b4107030140b0140101580100301c40128022074440d141b41e901c0002d42440c6210b00c0400c10701003000c1c80c1e8208002403060054060fa9480b4184801190303120f441070a80142242e0082c0c0c050548071400c000319480d941c81100c40f191030b0080060225450401e81e03520724401e030885581000003015014040a000f0003091b4043d07401d0440700f613410070032030500500e086404070768645041e00d8040009006410a610038080c0c0b0407000480b40f40c549903584020041034810911041001402c441c500800c4892140e034516401c0d014000c101c803100801003200b1554000055441903c0c01d205004200d200010920f80c0408103080004290001b216509214003400030001c1201000204025903a24002d0140400340c500d514240f0140b03480b50100001c4c1d009482c440e640581c002800110005c0d41c1c407481 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484764730 1250 484763480 484763527
    0x1020c07051228030f0c02010c030503100e1e070903050c220c020d021c08010909020f150a020c060708030403080c0c0a0317060d020307090b0f0d03031d0d05 69
    0xf140c080c80b07a0a2001207040703214840c5220403405005101050680092003001c0d200c030149010003503410140d00103000c40103956005010044044006041803142c801c14401804201000c034070a440c20356480202114906410024101a6001300e5446400ba040d40401d03a039118003e03144182d0304009110750384202130034010b44882c40001d0402010094422585a107050f5030161268141404010340307064800110b56104a02e04083d420781a5030046085045d10600d000226035030016000142c1144c60390604540e0002050010f8140c10035504010550808203400360380440711180200201e50203070138009041c007101040040c00080c03040400c0e41e4082c2000217140e08025203195028508245000114045503900e405980c2103611100f25540c0b000d011a488186851154080390300c44d13285104076008641c454070303503101c1030f0b46840ca00601860003600c0c2c405100c6481c00d0080c0944100000011600390711041c2121403040806c02c40500002510361910700a840d80340500f60340c05200c1d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484765980 1250 484764730 484764733
    0x60f0f060f0e090f040201020f06010612020c1005010b040906050102030403030806010e0102010e160f050402160213060923060f030618070b07061401150801150c0209040c140301020c070512 83
    0x800b0704039942e400d50160041c140746407203554914042c400680b400d200ca0381a803074aa4800303401000721690066810074580a07508000d03031642d4030003101d94505489004204019810300001041ca040d0310720281c0304a03451694107109195071400160780341c1c819408054006405980055080c0d40907500c02c8140315030601c00010203c8100701c0603810540c10451034045041d2910301000510309101984000c0c1900b11821803611021400c52400348156880c001e0082c1030b440c81e02c65032030741c06074012070051541c808280030011200e076100800c1c203102c0240070714080c00540440d0140c14451840e42d40a50f000c1c006240546820303d0300510710540d48a110340b20311400b1030100380c8540d014007600038203105200c0810750f40000d00400c0002013050700b0140d0100c003c110710344803c031391080d0344a045480310300d4400600000c1c81421039035840e001c44081c0d0051151014402007000010078182200d840070402c200307680544080600781d106140c400e0322141c0c064101032145203003000c1c3c10380269a240c1d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484767230 1250 484765980 484765997
    0x30209090a060e0d0e01020c09070f05131214240c0d020c03040e18030304150204051905012318190801090b01050108010b12180a06020706060f0f060f 66
    0x2a1070105480c4124103443d8150001c000050f07400b40c04c03182c030800c4404240003500b200810030300400e286035002001d420801840e036000100c20383c000c5007100d02c2c80030b600500040c019210f503100440944888002c880b13140300a00d03040d540319000f140c1c464500020301040645203401c0d600300c58406034081c03c0d0b000740303480410400c1d00401c5240300900321004007401550312503242003089140018002e02940e14410880c1ca00703d2003807404001c995000d68801c0c0c132014100c1e603400b4944001d00940d0007140d0862912010012800140310862044410903a00c1d0080344e240b00d02c9902e44890031860b448404401488864000b0340c1b090301d20b07104200094400c210880403807400c91100c8417560300c0301c1d010f41d540300748190034403010081c20342c003400007800c0c0b08545516040100070307184a00c01c450200001d190700030540d2104001d641c1c00990161804403250b10a442c10104000d40c41503004440c6545403c40c00100c0b8204840e08604a98046502c1d0801620740b440030340f2543e40c10041c5000f00080356 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484768480 1250 484767230 484767233
    0x1e040213030b0103050f06040b040f110a0b0309060601090f060c05012a020105071b0605042604140d0b010515130603090201080a09110d020d0b07110d030603030801030209090a 77
    0x20a00391000310b00a032031495142d49142405418068030a55a08194018200f00008545141400c580143d03002c1404010050720b070611000c2c00040e40130306540440800c10008500b28502c020758040e1040d4425a015503c90ba801559040901d00c1061080011a8400c0043c113000300e4500008600900022075140d010002906a0103400c1c051a1341c0500c02006d2044450b609115084c2d004140c0d044c2407010034108401e807183c00984003002850785454600203400c0210125584404d10005880c2c84c45042c4100440410313500a402100900c940d8003030310881c0c0c2d04c0c0221580303031841e40005010300d071079003810305102100400341141400341300708010145120508008880c0249117650300000c0500701440010b0040300c000d001c02c82c205062030748403804900988201c0c1c100c0c1104440c1c403400c90b00188040384001d110800007811001400781000b9807641c03c040030300c90340b1100304140c8031480740c01d00094003110140e02000d00010034030310040c001030030481e042c0c0d1b4102d83c4503000c0790707051840d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484769730 1250 484768480 484768507
    0x31e0909110703020f030403080f0f19020c040c0e0d03030e0a0c12060b120c1c020a08070f0e07050306041119020a060f1e0207140a0c05010206151e0402 67
    0x3200075144500c500040c29400e06506001c400361508210f005545818550340700d03000c00c1c0c00303103040c101003010001880319844410307c030464078400603491f80c600b03e0307101d442d201039254418400b03414051428040045440c0c0c0c452841c0d4a000b51000b01041203c501c01d44049000388801d0b041c007440c510520b0030b800b001c01c0c0040000001443c0c03001e00d0780814a480d141200035a05c81d10111130052030810200c11002801060904200d403003500c03070b00b51205850540702d00640c50316102035000400e1800104002101040c880c068840003102c902356156640100030070448101c0301800096002e0010880ca0301d000e40080c0c1c12180b09010040c1400078800032619403481d0340e84c8000243e4005186501080316a00504c60400002e1908002c0b0b00c0c050014950108103070320502c0c2c0b0445e070010303c4008124010480300c4403011410200d84c072200961608900465142c05207901604c41e0200003292510382c00d00c1e05000d450050300f41d032000c001036944119102160040303550f0040e024820000b28101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484770980 1250 484769730 484769741
    0x80307150504020117090303090c01030c0509010804020a1806172d100203090f07080715030519180b06100905060705011e0c120603051207060905060106031406030a031e0909 76
    0x280306c00555900d00b803606580e45054464017040c0d040c941002c1c00045113035080000c2d124080f20a0800340d280d9a02d901c00240586803d40120701404003501300803004c603a1550084040d40e202c0c1069030744240030340007400d0380d41800d4003001405401c03909101c03c2803086012400d610980c0c600031240c1c0307110b401c880402a40c1085032281c034140e206501100c1c0b64042000b02070010b29002c0050503215003003030307200c021103151180b00350149600c0b4800301d001c2e8141c01c8a1210b10000c0a0f4041010b00046140c000f82e2007508441035a400d00400701044561801080a646c101902e03210546414607060600440e07411040c4280c07241d550b01c403102c892004510f5000c6129211500002408205c0118058103601c02c0e205000c0c052464404c061000980010f0661100d080d0120401c1d2a48850b21b0014080e1000b442c000b0310340e000390000000c100d034050308042d41420500702c0d070031100c0ea039000906650f4511544c010b40000c4056202203005460030154500119840c907000800c0c90311000b04006456 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484772230 1250 484770980 484770991
    0xc0307080715050717010b0a02030910030c020d0516060b01020a02042c0325150903030621050d031d0a05030d27080f04180b0901080307150504020117 66
    0x1404990480e021418070f202d8141d1140081c182044820007158902002c140140944602d440c000502400701c1e6008005580c02688010b0885800508030180100907110080e80600940f10300d401a01c24070b0f00400a0710844c182400800c00b40600c2922450054030164100314103502a0f03041040241e2140d0080c54403c20310004c41c0304140c01d003484943d81c451300c5200c000c0100e03007041c807002d2040720780742d07088102c1c061400c810498000d90b2030070304120f0741d840702c450200c01d00c1c5000f038900101501900120100c52991600072074092103640d00864a00d18840002c0260304142296406d2a02961022404010105500c416200b07030903003040c43c140c00703c01e003600d07546d01c0420403085181c0f030342c000c070b0300c20000e580c11040d405581180c172301ca400c11010200800c06080411541c01e405031f07107000d40340180a48001d840d0710640d1103160800416904009901071200c0c200007080c0800004100e0700100d034400071840e1071440d144602001000080c0040b81080746803012400140030080145001d82c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484773480 1250 484772230 484772243
    0x8030a2a0605090a020a05030a02030a290403030b1306050f010c0606091103012301020a03080402182a030c04170c03010c02060702060a091a07030e0105070f08010e060f060c03070807 80
    0xb04c06004000e008001640114801c0d40404d14981c0142c80106462064960210b00151022204103000d0403401011007106680644031302000b0034507605800c50004000e043d104160800075000300c02007039035224040d15400130081050411369520502c040b18031035000f0b580004001c0c3e11400c0c505c0985c2d1020401c1c0c642d8050100c0180300103c1a80b002802c0406840002800d241c0e40c140080d441d60404140a418000301d40c000506546075105442d0b51049030140461041c85c10322034030924504030310b8181451948400c4408007054001c1c04890052072103184e01802d003440d00b6103c468101b510341000c000f500a00a8610807038609007e24003074640c441d00a07091520708031074024500700c001015240050b003400841400304a0b940340c011244a600c40303900855695000c4142c0c06841c60f82c066120030b40c6001c00704042c1075400510742075509900d594521881c1da03200c030300c1008440c040d41c0e40c560090701c02e400e4200740e26140b4014500000310354140d904142140e02e606059400403501038808 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484774730 1250 484773480 484773493
    0x11010608070603140a091707050a020d060e060603060411040f021e0304140109030e150c070605040609090b090c09150307030203191a0108090c060301030c0e0108030a2a060509 77
    0x2044c1e0301940007035002c0c004c160208410922a03c900c0340c0420402c40351082c0c030340c0c0012508203000043c00310304d550301c0d0060aa101c1d40c5c400c1e4540a0000d00c0e1901020156010700710104885d0f150200b0540c1c0190f420072901c2107880000c0c020071005040c0e07002011007869017009508003140d035a014103050561034181c0a5103925003070912030f0400341080d81601c1380ea450405030381d00094201c580345030801d0301660908100021402d840300ca80c400e00f070003d2241e2150000005d20180c0c400c000700b050318415640e40402c5503640c0d04102c00d8448000ca0700d0342c000d4846000031401d04940015000300200100300744909859000000130780e034425591800001d030000108400c28074ac0144c05082604031031010040c152510180d032039070060b40085c1c41d040004140c0030908a240c10880340880300030050a403681e9594038a04008200000c2c483c000c1c1500907503000280b0084048103650008005848008045907039482c880a0840311440d030010304800d40e2130358400300750380e40f04032441f1700c840303030001c004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484775980 1250 484774730 484774751
    0x10f06090c05070807030c02010c061b020115080616021203180106210b04060e241f1802120901020d051f0e2706040c080c06030711010608070603 64
    0x15119030706561070a0001c1040014001260002242c02040d01454100b04030040c0b8401203600c50b0003140003820303950802010041100b04444803101075502c94000f00480407070010100f00c00c1749280301d001125001000000e0b01c49100c07802c1c4058502052040d0740920781d034005400c00640060b140007080051511132140b401c0d80074495480078200c6500c40900400f1044107801180c221180000c0c1301c190309101250400061f9009500e02c42011401d88400048c101201c1c40800207455400502e230b2443c0010410124050069001007002d800c07a1a00d43d6080c0542a426841e9031307450803010950800480301c1e048070703144240d0300070034400780056901d0301444940026280c0140041c0c001405661150314200030101e003900460300c04d030342800426510451846c11204890300d20000c4072040b80c50100c2c2507980801e01030b100d0b03403251083d2004039440300801b0740e0314010402c400d0340002c41000420481ca00070b03070f00c000b9080202c41c00400ea180c3c0344c280c41070410601e42c2c048030110341c0b42c0e4000760 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484777230 1250 484775980 484775999
    0x30a022109150c030106050a02010f02030705210402090c1c150611060702060115020a02040c09080d030b0f040203090a2117040203070308070305070c080d09080102161205040305010f06 81
    0x1090041c00b0300c50240a04080c040301d82d903440306100301d005004d4009211500c0782d0003034000044901343e454046413241b500c2c0102519540c402062601d90f010031030190944980750001d081c0c029034014260180d259645c0c0000754403648180ca80001d16505486409041d507200e00070000c2e4421100c4540c54514076116018200d442103500104894002d0420071450560025045044940703c086001d218455413005074244100c114001e07401c00e051003d65443c0302d421412560485e4000411145110400c000840403100c0000a01754004048007800c05181340c990099600601007105440246c40181d0b1001d219202e5035508a00207003000c03c00c00e100301c0c1c2194501b000803243c01500d402c146001d40c0000d032104524000205821004100b540a05208109541d9101d602807200c0032103d03229110503548510005400b00055400c880100c1c1400040c000e45420307080c8403034400302120460b40d0b149801000f2000c110100b14040c0070000225800340203060421020b020000341d801d007082c2013071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484778480 1250 484777230 484777243
    0x30201080c07020d02010806010507050f031908040302060604110c240702011406060309031c09050601150e090604021e22062109060903020610050a0b0f030a022109 72
    0x70055409000b0380d005078841820100c800c0f6424601403440d96075260041c1e0740c40c0544000903215204501585204601c00402072451007000144000000e6400d030b0300721180d120882d00200103030098008103c2d07900705030300300143d8402441c0d052420300724507440180c5461112203441e02541c0b604000c07507541581d120403054111001348002e0008001e651500c400007600a865203010b11300c0000080e51107842881500e02d5910041403003401541c040c0d0f002d00c040c0c500c0c40820740e424000c1c4000000c0e03001440300c20340594582610795a4486619108001103840018540d0781c01580804c0f00ca01008194800803103596074580003551982c01901d09403017402e110360b864490410800c00c081c4001a00a480c40c5e100d50050708580220300b26052201000d0908240e000303000c0c42c1000e51110400d5001318155102d00e40111072100103558400402038140e0061007100004101000040c890860100040d076201020050251818015031803c00c0300c111041c0c0d41305e079150012002d010710001c091002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484779730 1250 484778480 484778491
    0x12020a17071706040e0c0d0206160f030f210c171807090204050d080315060d0e19080901050d0b0d0b060307060212040909150603081902071d061c050703020108 70
    0x1000085d0a09120360382c3c40118041c100c1c0300301100c5a0480c01c56079441c045460050f0840500c0000040a29064005000400b4201c012864008541002030700c980b8007100b646030100e01145131040c2c0001d0038001800c0019480c2c1c1088024420400c1955042d54024010b103d9040791420080c4501c4525042c43c80c10382000c0111401080b04000a60380d10828201c0c2680004038a5620380391200110a418140070010f074220401189150050030982d01496048804405440c100d8070040031103850080d035240b0041088600388055003c9501c01c802922040e1180600000c82d1022880020048000c038507049034002040400c000c442d0400788030410040500d8001013000109101c0c41d1050b90180c2e028140c040f690342c00000090004c880300300c00035135400314000c021041d1641070900d119804160240800c000d0b0070b0304481090705c0014010111161606030310040032140243c80d6410741c0c050b251550000203a0f9100b040003420094944049110710010b00a4038034610026183c039600416 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484780980 1250 484779730 484779739
    0x3080a1e050409061715180106030b070f0216171203040602071106070308040f03090b030f060a060207030201020709020a091509051008060306070e19030b0f011512020a17071706 78
    0x1704c250030340c0008680460610350407404999a0320554a5014030780c141380e041801c0d42c24001c002082c03180c0d10919902410361603803190000c140e500006da03502c0c1508002d48441d1001004200b22103025000c40302901c428020a6400d1102181040482038200340c4054520700c1d0f0009400041100600701071216080c02c1d01c1c241d04128598070080d1110321f0041c40a42449139105011082612542801d005046007615607a00ca0501240072006803030103c4540e401465410000310712a4000140c0700700710b950580c01412038504008030034019411094002c400d02020041c041000381c005117041c031000245550320581d80e071910041203545001140420306109900c0306000c02030f10049285507000e50703181424421000a003002c1125400e04035502081d4004001020080119a0308035901440380140520116602d41c1e40303100a00d003842c6040c40210b100b442d0500090300040d00503006c9a0503a00700801c1000c1148e0b90070090500031070303003003000030384034000501107125881030399070011025034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484782230 1250 484780980 484781009
    0xe0705090103150902060d151a09040e07030215130621020901093203010c0f1d0604090209130b0102031812010204080604020111010b03060103080a1e05040906 70
    0x240896062032041c0800341c440303600d14801010300801c0303404c09080030343d0240c8025920700c0c008220b003008000d541e8502c0c00c251140c082c0050740020081c01007194551800d485c920b00020b8408000042403160074103055401040000805a52520505660f5059107030404c1da90740e048200103603c00c40b80740c10035001d00064501c0714071108102d5080c02030503105886e0060707070799645400580d801c1401f035101011552f80c3d2103041591031890111031007200c1c0c01180c19203500b80e44008060a070741a0000140000c0d62000c4045c4c2c8040c4180844062014499105081d41580d000428000d6010360052486260000303000165428a00161220070244000800c015041c1e0030000351688502e440d8051501000810028a41e8030301a1007100c1c00e240c000210750321070340c401e10b031501d40c08229010380c041180025030085508041c00756140450b401800760415030309581e030760303155038006451170740c10043d0b110010030b40044040c00c91440c0308503680340c050312a40b61246140a40f6842d40000d1301448048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484783480 1250 484782230 484782239
    0x40309120f03260712060b04140409021201050a0203060109050d0507060f2f06010b0f1606090b100e09010e0312040f051002040603050604020703050a0e0f0d150e07 72
    0x100207074103003a0760620705024a4540415000c503d480907582c2c10701c0140a12051094103900803410038564007291501340055075692042c0754003406240b14901c0074440d1076844030f40a160603403112081920090945001700c102071842c03800c4034011030380051169400801d0018540e04080660001c10040300c00c0030307807845155651501da03100c80c4a98024041800f008803a014010b2680b80100313540214108c11540300a0004405046440e590084900595002003406941d031411141d01248002e00d080c90000030f18400b142c14031001c00180c2d002c0b50b503520348000081d940d8506030300a1040f404175002442c01d000307030041c4214002c1e09803440caa16256100821003c0413040d1030b003011985c900b444d13940e6103a05001765202c000c940001c10798003034041105510b1086502400541c1c00e01e603070801840d035810b01408224410f164001d80483d1041c0009140103120301c541c81e445100c044c111f28402e2400001051122041d00700072583c03200f031100c010580700c8140c880d009994111500070207085180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484784730 1250 484783480 484783493
    0xb030402130c050703120b0d080301090507051312150911090c03070903020925050a02120913020d151203030b0f09010e07260901140906130c050301020c01020304030912 74
    0x15044d009003400103040004007400490b42c0420000c2c800a81100b58005103460000d00700e074024010b1010261415000c01e501c4d0b07108000391202600440c800125003400c1c00c84507048419090f50440f00f0411009055401004600921006605c6071102c40300c00304202c000c0003144034004005420a40061081201c800c0d840f540302002c898066483c505252154440d01a000c8491502c650342030a00440691046a0050007000744510650948118444c1c400c03402c10544503103031045034014079020010300e143c130450340109410b4460100001d41289408400c19000c22581c1c03004001450301c5e01120145030b0540282c0103443c10444d411598891a0f0b000160f018206018003280046204002422507000f17800c00d40001d400c40b078450090a03889000000380003012990300481d1750a107040044072001c9203980724010207408000d0980340d40c80300540d1072904001d180a5404801421000900b82c500f0301c01090b0840d058800940d0b01d1400b801d003d400c0c1c1a81d80e01854031b10b07a080c0720101c00f2420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484785980 1250 484784730 484784737
    0xd0305100512100219090f1503020306190807080106050603040f120c050a0506060a060804170310210212030703170a0b0913030216060e0f030111040b030402130c05 72
    0x40860340c56151a0b10744204a240540842410b1041c5200080e10082196a0864a07808110a07601c2044490f2541181806214144501c2c00220b410000402d800c234001e4018603400140074108032200c1c072506205903404030f4154050b82c001d03000a0300602c500c2c0028068240504819100e580c90341c03c255490030388018000a0207000c41766095000f9461a200d00e18000348907401c0070803070703800d00000d013030441e2900c5040e16010300c034046108002038514018040c1a1060350000b151044440d2042c0f41d6a0065100400440001480034004580000400c40c581240c0740807022807c043d50151050010302c00380092045220750042c8030005c000303a170002d100003910300f02048a070129190010010040e000d90606039600000003c204244c0d83c9100040b01d06030350007603085608403001000d603003543c035507540259400600c075002d80d101e007800d208100903030031701703005c1c00001c1e900d02c4c3c3e04100d08860b0070036001042c20030390001c240019440c228076100c8142d045900e081090300c0e52000040e00c00c2c031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484787230 1250 484785980 484785989
    0x703110a0b010312140d11090d060b0a0510050306190f0603020d0b04020909150103180302150601030b030c061c020a0903060c02010204060804030806030f1b09011202060915040503120403050d030510 87
    0x139103501d0200d180807484c7c0141c80c0c40d514098882000310748580390807400743c1240b00322540149031b040e000041c203280c00e41c8044540142912842e240d52100030034031040c144c095040402590119200240031004c0ba800d0b41c0080c01980e07001a00c1341991a2443c0565280d00d2196114900501104d14140d44807940e41e40c020440e03090309100c48481c41c0c01a005410804080444601c1d41202c1c0e40c24950007013940202c01c51190b04010f5240d49010040d01251302c003007403042c0c02d036120100451250078644002c101c020b4030035540e180c600007000480c105aa21458810f000103050800400400209020301403010020380000c0d801c0c5418054020560f110092001e8100700c0380c007000c9200c035102803281100d01003841040d116000c086042906020410b40e03d12030043c4410030001070300c0002c0f80d200d004130300e074018811850312450790100045140c0062400c201c0200400c80003c460b43d0410079014440804c809440e122455810503500305401e0300d21070410b03d4100300800545088058600b42502c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484788480 1250 484787230 484787257
    0x17072306120a0e190203060a060b030c07050a020a060905090f0103050d2106030b0601170108060c030405070e0f041a061f0e0d060906200a03020703110a0b01031214 72
    0x70b0782c0310203080e0701901c03110340c0340301c0a0700400010350060200361040045040c0250200d56031074a035447c4480450380a485090004801840421000c0006030010010340f4015011540c6041ca90b1700001c0c01c03000d00e5440100401c00c580410441030801c140340d03541c007010345810780340b066240d911041d45500010150004121040410b4841144905580c103524503660001300840d5403031340740c135515031342040c0c91940c0420b544a4864003044c00760314041d070585e407202c00a0b18842d11800c4894046810103801114140580000414845482611580b2800b64020048058181410100a140c04641c807060041c084071040080d0b9840c1d240ea0315081010f1078003500d6950450035405c8030b41c1490202503d500550025032001403000c0c9030400d01c0c060740162002c0003401088501d40e18880f030b03c803008015468052150040840c0a940074002e50343c028280340b0a8110107220003400d01300c1c41201241c3c418015001402801201e800034400d40086003442c070707402c000d50304054bc0c1f0381c083c1080d880f0030f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484789730 1250 484788480 484788517
    0x304030c0309030b0703061806081903030e10140610020a02010e010519031d030a0f0c0c090f09050715140304050304090e10150f03081317072306 64
    0x1094071079081d41000f580c00181082c442d0a24082c010040c010601c10010206031390320f1131603880e4038148034074003c0350300007030081c0300000d040701c100f41e2038540c0c24501380c0615030386865520010106010890404162403c00607020100b60142072058a01078459030040c40c5101418842680004c1c0c001116502400e02c01d50201144004940c24840d621850300c840d0311103121607100d0764054004081ca5480c45031608084516040b104e942c134054060b40800040c6461845102d40d80031300c16001c1c100c0c1c011100540384036100d0050200360b80c4803440c603811540d501c220321028031a00b44500b5004d41340e04010030300c000040303900051600300c0c40c0f004040d0b405c1c0000301090030800b0030401c640c0280011442170114003022818162181e1100001c40442401d11161002c0341880620340c00c1500c03240610802914110344440c40c10b0307084078a040450b40a102c00c040b802c1841581c0703804885800d0710080c0440d80c18100c044410503075148511000c118804500f800b0ba59501c0709440344401c603040d05030380 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484790980 1250 484789730 484789733
    0x120d050a180b2410051c180c08241e0f040b100e01050112061703040f0602010e0718021c050a0608011a04021e0a0507060b0621060402092206080a03050304030c 70
    0xa03508503618011b40c1850181c5803010180c500c08010b081d18080e003039002d0b542d03541700318083c1c43e1010042400d21407011200801d2884a1880c2d2060300808003083d40c002000d601c0543c1983c41707009507900030182819508210421081c0078450703070303c5a040742074102028940030401c0007a001c1030007458144481d035841203407000300d10340c040002000082084070a16002071441c80d22039000340200c0030b0a90001d900450002c0c0140640d07000800320400903e080c5180c05451402c000c0c0c0d03040103c035004c1d020801c4020060078245001c0d042c0829000008050600c4803c150489850b5441404076904200304502500c03c140d800f5000720006540150342c1c3c504075144440c0c4c9100381081e0708070208003c196040b060381d0010281142c21302c105010461103107903e04000040c0190592041075405018082a810320300d40000c039040340c00a800541040c039810b000070044680e28800505031461b50082003201c07803180c003030800182140c8005e0010724980e501c008040307100092029080c01080130b806030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484792230 1250 484790980 484791007
    0x50c070b0f1c0c02011503120f030207050607030606020d030b06071e080a170105120a0f0c09020a020c030d05070c030f023001050702120d050a180b241005 68
    0x80301d0141854011007020b880815240c010400c25040c8401986030181d0792511241101c665800c0e240c000e8600081e604000604981825908898104040e001c1c413885002690410070140141030945021038400d00f0940002d143c2440c07107043c0707810107047c450300e061aa21014100c8101e2500704048080354a01d011500030b001500c2c0c0402000108001460f001260740400c07500b1002ca003184c041e45459986004010440c0d43c210503401e1242c00c5822444001003010b5911032459114803603982a481c2d91b440c11070103d070085100c920240e085804d038082c40d80b81c148a0441c02240c0340c00e040c0d041501e00c0d2916074440780300d400b004001c61507001c0041c003555100001644141c1010304658495824504003100418018003520025070034074000ca03e0700c40c00442c028200c00c4403100814141800c074024a009041c3c041c003500c8421385e540b038064075448041d2640400080c0920480120b40c242803106074a07818468151060000355600e003e0340c039a0f00c041104510040600d00b15440e00b640c1704908 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484793480 1250 484792230 484792237
    0x619050304020d02030d09090501090504080a081807120201080a1b0c05071806080c030d210908030405010509150601210f150501020c0405090a141603030203041401050c070b0f 77
    0xc0c0d451706c555607841112940c400882e000366500c803c800c1c03051382d030b80d0201c1c07406684096500400001060001c4020a4819246241c0c800c00150141d812000982038460512526070400d0410704100014482956005241c072904032132614000c1240803600d109200c80d0b150020828000c010a00c90301c1d03014810b08010f104085c000d9122410201040c103079904001340490700c100c9005000c2c0c1e5440307050515020541c0e16120400f44c80e805021641e4100c8101d0481c102941c0e1000c0c3d943e110459004a03040002035071007588102c00000301e46c1485015145403040500a0340b55000903c020409140d03440200144042c1c0c448041c0740304c40101800700800f4010090107102401c1c0303030403c404402c0401011240845000386c09a90460000c0b409010036541c080b01c43c00d441d035202106800002c2c9a102c2c0d6200010b03c050306443d80b202449060b01140040d980c001c0c1d0041e4400700e07091284a04103030450341140300c242002c61800804041442d114003072442860400480402d11003501040742048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484794730 1250 484793480 484793483
    0x1030807030c0506010e15030a0b06010311040f12330915020d0614030307080304080a231201050d0203060f06060d1d06070801120f17070f0209060619050304020d 71
    0x1540c0075583c6450a0700300c682d4040b5041101c0560003107c4c04e0300d5040100f0540c105c0d54101509620700d5444000642c054007191750b80c0250b42074108000074402c0480d40030b410107085005490785c0c5490b01c40c14a00004104107402110031401089000400305c050a006068081031800105c1c40d0005820700aa484010141010005000180c040300d15007030396201605542011100c550425a10020306503203005018004280c14010000f1801099400c0e01030030320b01c02039107420100e0600034103120f14034900700d00116489100c041003484245c7c01e02001e050140c1810744005007103007801e400080e036654028212000042c40c580c00300342280c0341e010440d070b261002207000b4000c1c503505010180c010350040c800100720b4000c01e004507030404c2c441c0c0b102034102d80d1014000c692180e1583c030780c840e00c8403000d0000ca038055141c00042801c060f6000141030250f01030f04184041c40c659006000134010028043da224040401000844202c4e815002000750034510340f094580c0e0342d52000c06c080305d418540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484795980 1250 484794730 484794733
    0x3030c1a070e1302033916050601050303161b080303070f1b2a09090b0105040c080f2d0907050a080a05280b04080309160e01030807030c05 61
    0x100211141c2003840c0303581030740d42039616049070044110030724205d00050701e1802070650000e68849502104148545600b14803820072160910b0003014511a588007511200381100110015403d1082c103004081c0101420740c0510310780894080005075600c001c00000740007800200d0307480d61641006c040c050140205504a07562814180006070100110080007000106154141490000c41c1c40402d0003040c0e108051a000308103591203401820480703004a0320100f80720000103000340542c015140e15500074030219842e0750402082c041602d02d8144032000b0f0001210034018090803001b022640f1007000c91111700f4420549483c00603007d40c901d0740c1a20840d66105000c05524089508000c0f0342080302d84070030803a07641da8800d4036085245409040e5400c882790010040d243c0806068490006c188003130303080340b9a0f50340d036401244150307000e407000c00c8003101b0054840000c01001070520b4001c8412200e051030501400b900c001c05000041103640003003500410907024a4045000550010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484797230 1250 484795980 484796033
    0xa02120c1201360609080c0703120e03160506180915040e0706090b18040903081005010c050a1211060708040c0b0a0e09040206130308040509061903030c 67
    0xa98540c040c2c8081200500049042c00915a01440d40d000c3c0c606102400500316003129516120680244204203090790003074070400807600c1c00d99083c0070b04800303140715414810328102c2c594401452a905208000d0281d07000b50820b102691540a4010031914200c4400c2d41d1008040030f14424a56603810171034103e000c0343d05000038181e6100c1c1207001144140c4040164500d11040310380c0d0743c92140f0500000c201c000409220146106000344098412041d81102108562010070b044840018050f000104000c0c02d000e80880704d04501e20041c1024605841300305a43c3d100c55840310320640008181c4601815031010f03a030301817000310180d1203481082d9500f03440e10440141800c0d1088601b15070054001030301145500d088006e4660a00c066038544030400031352001c1c07101c4284050805e0b81e101c10700b407051054115048d004030001d0b500c5101c440d41c40e00e00e02410301c1148074001c4c200b20312810082003040c0229481c8041d1004aa4051411502200705801c10100f54400090541d4100480a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484798480 1250 484797230 484797259
    0xa0305070215031905130b0a1d0c01050912070f120c0501030504150e0c040e070509160807120b040c050a020c030109030819020408101b020a02030a02120c 68
    0x100141004074000e441e2203041080d03031803000c1d119100441e2000070f401c640200b4021003000650041e0342c0255001800301881d607040d16002c1a00c0c0c0e0417a500c4410b580c48809540990390451801d08000c2c8a510040260100031400a4070f00d028005015000b00e22107003900303040300c03402c128107802092000b2104010b203807500400c209a545421090b03504c0c2c4958200040d46501c00e00c40c1c10700c181c0e08001d11018180d00d901c1d4580107011314403402017081c072030407800c00b10a80d11031181d044140000300c001d05045140106008070100001d02c031002c981102c2851031341a940241125502c400310f842d188401140c3c015584009001303103840c8a4104d4548030145074403036001002480c8402887d001c5403040b00410040500b40c035500d5500900140341880814400b80b10700d030581c840d030660a0400760401e5101c02c1210b01d880e030507100c0c03010190344484601161000400185011094132302c09800403d42d1500400d03510101510024010075052040d07400c03464051000102c0310500809581c40501007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484799730 1250 484798480 484798487
    0x1203120c030c020616051b0c130b1c021e0613030807020406170d0e0409081911070605030105010806010302040e0f0604050a0213030f020f09011d0a0605030615030c030a03 75
    0x86211440161040c4e0011941211624100d110208416a540c925142d050304d550305041c0c0154007040c0c100c1c818100c0041603552007240150007140720041c00109e0b100303820104204140503064101c0341c8500d0000c0100540c49802024205410303c403000340740b0300c42e42c0b00843c04620070341c092100d008803007020220400c008100100f06e0180216070500c8043c2e00c940d000142e88500e8111410b09038024100103510a01501c038164031454020300014405882d911072042d00c3e03100040c4208031500080c8818022900801c101080c85004002095140d0074a40d01070494401805583e042c019803c0015007039a2003a01181d01038541004d81c0782660400f151494004041664540d04c01e6041c100050484181c1d071090f01c1490600703071845100145140c561061300c050710b08059810003003c81d010312058a542480310b00070499a248582441c036a0320607048001f40180559860900342030003001155000607a1940120b02c1c1908404055940300c006860200d00c0c8134840e8050062200c0742c0c003415013 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484800980 1250 484799730 484799741
    0x9040b040b0708060d0303090c050d0507030c09050907030f2102060603060a1b03091506030f0501050601020d09050609130c03020c011a030601030807050f12030403020f0c0a1203120c03 81
    0x41401c490800303440c0c2e848256402042180d0b16038000022205143c00f20348241c1001d080103000c0d1035003420950710307080801c8000c119040240d804c0e03132000d80204200000c200d0b004004000900341003059080906289447c0d40d40c0b8400600400c007043c2041702842030308140320340c000c10301d94444c408404141e100a03460750b5048400310721a0103808006114202280602003608405150220b50088811030a40081c030071910107441401003640c074048000300f0380c0700f1840694080c3c441014520410300c0d0031800d5990090001c1e045401000428224a030001600026208119800c945480e08040811480031000b0740750f801c01c44c2001c002d81e85c1c42d5059401002c3c40c140c100001d00030200c1481a0001a2400031030840e0150301040040010403a54405421003034401c03000c0c0d134000044035901918004145d00440720b07819000060000b0141c0403c42c40031100340c1e500203040c4445048000600e040c8861003a000c00c2440480e1450415106401244003c0c1454400300202158072100900408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484802230 1250 484800980 484800983
    0x151207090501110d02120a0c020a030305030402091509042a06030b010e30100e060118090506040210020a050114010f08070f0b0906040b0d0e010b0d021c050c09040b04 73
    0x4012040e03602c0350380c1d0042001400003c0c180c004015020b103d1081031b610b50b00c948000c070100100b1040341c01c01640d0b41e03500707040194020303510b0a40700d042c80d00412a81c200003429480c0c84865200c01c101715610340d0742880394440c0c2c00c03828503507504c0e040101c1903590b1040f00c80140740c0b46240c0040460215095444502400c5003aa1001c1c0c0e2000c1039411301100c500d030f07000441754024010032170f46410030340a5540d811920300035050710007244024441006a0b0102900300019030040c5005105558543e0300001035252404024000319006850f5603031100800360020b40038801e091540c1c1c0d5014020404200f0f03182d8010000c2020300b14013202c8900b005000c0c090149607102510002491000001d0401e043c0e40b1170b450a40e24080c80c1c000e100301181e00180007150800d00500c40007901c07403214006070502a280701c001040004905450f40d00b19002c5807000b51089218110740b00241e20b031080c002410281400010354060700600b045c0b45070100940040d40c1c0b002200c001c0104102030501c4090150303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484803480 1250 484802230 484802237
    0x30a0510080a0309050409031e02030d0507050708030a0b0a0513140709051e0d0605132607080c0709180c060201062d17030c070f06050306151207090501 67
    0x40d88a189890702c0c2c454140001c0d002601c44501400f16242c030fa070060081c00c0c0f1078103018100d035030070300780809407080000c00d40409604081200f090303005960044562003905803034007926240203503031003401500016003010040da0352102c1004554030368801140c0500700061000c1c1c9020500001300d0080c003581041d40038450f00b1680810107039801403242905445000b062240d0030504801009184608204101d07030098001ca182c0c40030500d18440c2c0b5005404821800d1168050780c10071000a540240c1c80311041102100002c1485561609540405520004c419943c070701c41000c0394a04007181d0015560030340382c0b0104191620395140c42842d8503200700111042190359010a07400c0b50300c1407040c040110450b940718400c0d00c1e0010a002c40d480344408414101c152104051a0b44a0805410008039400007810592050041042400808089085011fa1810003500502500020700303a41d005100b032008210407042010282c458000c0a405000d029141001c00100b420b0054841d05021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484804730 1250 484803480 484803511
    0x30102040920120708091203040c050123191202042d05090408090616050c1e030c190911121303020d081e040804030302070f03030c02060915030a05 65
    0x12000d40800b0b40b01d6070300021440003455030b1901005c1c0c6007803400a04a00d5a802102d0041c1090f020403405540118021000403141d0b03424040003520341c0c1d003100006642c580c0015010b600d82110f003000c65a20060528403003103440208001695690101b1007606c142034004900440c4580e00210107540042100b0f170320305001d44181d00240d0015086000b070703070b8008207818001408030b511080100107105d80645079900d481c1a81d45490041c1800400031180c9400081000300e492805600001000310030301843c280c4901601c00096503114213030803950113485c1e8007a0385400100310a509100400740250144045080b04469001651050030b02604480e40580818460341000b803c14142580c190010074030118024000d49450300020300c14000002c01035164503101c0702e070004007402a885100c1c181c0d2a01d007545400313414000d55030004001c4074002e403010004a41e010701304964007134058444558920b10107022800c540408048110030344800410311600740c030640c1c0314612030f05609440e45c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484805980 1250 484804730 484804781
    0xf1b03140115170108150c0408070b2b06080d0e030a0b100e090307050d090803180406050a06030b040b04050403052704330518060f03011107030f0c03050d02090d020301020409 77
    0x888d01550148a82c00d9102d20f100384415070b801401080300b5480f0315900d5805016042044030203190071684500d4150300c075901080041410442e03114440ea950500d00181e040c8100481c1d940c11041c0400390582c1c00d03000100b00115500081c04000d40801c2d00c555078180f8204110654036400610111610b03c41c8001c5050b0581c42417400c03105445092000c2c600d4404000000110490b00c90012030b4403540c0d48400080640d180c0b01c0007c0105815203000c01c842c090002003100300c0b04e05000c11b038015800d120030080041e5001d01181d040002003c064951142c4133020300d0101012150090341142c0f178801a01420b511010001e007004c5e4400840220100200a68505041762803107440e4005c1051042d62a50140e00101c5a600040142c4250016445c060010f404d40e207a480c00741c0f0648070000344003401e05500407244140c3c00424103142c00b600e0040c4d42d004140b44101104000b5072603001c207095049680e071031104120290010000c0d503e0741d842c1e4180d071008250700c103200d10620803886ca2210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484807230 1250 484805980 484806001
    0x70b07030813051f0914070302060a0f12060b0702030f070b0301050411090901060c02090c070302060c030406150305010c02010b120c040b03030d0f1b0314011517010815 74
    0x10201a4541d590081c0d40c0c0342c512511011000003007080b82c02c0d020388018104050350380c40607001600140c00002c1a01980790410000d5520b010300708801d1500540d805001588403182140c8200c0c280346441440c3c0c1341c14007021151b84c00b500200f21251400c000b000101114480060b00c3ca4034021400e880e200054111203665980c40703407240041804d0148010401c625042e885185040700d007508140c40d03c00e44400145d01c8806c01d80102001c914440c000805500303210b8250360340401420a0585814034036103001e552400000c1c034071018600000001810021180c001d49140d941c420440c0c1407080e00da01d45580a01a561a0038005600c0c011001940d0b1402c9101c082c02582c1c0203020f0050b00b40c2c9c00d030901028040280c0c2c0582c06100c02c0151040010b018030810900564030400082d6006005034440800a59402800101030403e030b40b810851451001d01340c11185940c011303201c280c00b130603410364601c1503801500900392102e40000031000c0020513a0401c0401c0303820f1074111541c542e15241c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484808480 1250 484807230 484807237
    0xc03030618060918030d05090d0207080714090c04080a03020d020c0f300a03121401051e030715080105090603060f04030f0302090402270906220f06030b0405070b 71
    0x31584041410040385034a031010f590313565002c0304202038a00d00010b51aa900507140305461000d565840009104800c60f41404581c01a10031070740580140c84c50141c0c0e40c4289208080ca092043c9002c00110b0702007001c8408580c000c0c5001c4080c0d60704000345090180d2669100b5000c44054000d40075105101e20b42000f022805080c020060400203624080300c40800c50204107082e103103000e402d0301408214041042c402070758400c1d070300e10480040100001055510b040d0350304d80d14920240040c401580e412120760b0005009507180c91801d0b0491000a00c0c2041e680d001680150701d1003900c0c0005940101814140d0318140c4060003a80c070b40409040c0e41e0501100c150003c00d000e0000309000074801c1055040c02c0056140240c100740880340014226030004084010510780c2c5a840040c440342052580610302d0225003500c02440d0050100703104440d004000d628122178a030000c1c030303800c41d2940091031f82c0740c9005081218a8036490b0200c03400b6400c0d50143c6151046c00030015542001d04102e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484809730 1250 484808480 484808491
    0x18060112020306040f0603050307051501140d03090b0318160506070312090c15020c01030e100209041503080a02252310180920070201140c03030618 65
    0x1001004003118044030029040a0591584991524090240c94006008880146004001940e951821442c140d49008a901c403009003800050004001c00407251101d41003c3d03038240c1c0e6004040c1c202e854221158089030300031450500e07010043c0107021015808411a0b90051400c981c0b0b600000040144bc3da022442a954054820401e80c1c000034403800c1c124240c101c401d100444c44501303076590808001e0698116a0031245840050107101d581041081749002080c2010042401c02450f02c0f502c039418004000c8915400141407100e40d00c455100c848028040d80190085a84030316096031542d111007c000c006106580b00c2c02801c458409002c40d10001500c5880c100720b18111041580c90740d01031040404120400440b6400e4032060302d140140359a80e5a02140140c0d03a990340038400203240c001440051805964146070110441c550007a05c080347c4180380c4841c4a07200480d640e0a40400a44004801155213604440000040c500425040300d00d20140340641b0007024005100b03c52 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484810980 1250 484809730 484809737
    0x91205030d1104080d0201020909071d01110c030a12180e1311060c100c0c0b04061d0a0303020306041d060a0509031303050f06010f15270b0702180601 66
    0xa022001d40641d801001c0c0107030b01075016400d1668500070981041c164042c03010150350001005019403a05a07049a4481414203284000801c81c417a00004d101d68a03608906001c640400081e00d002c04000d26044000028120303000150585400800700001482c45008102841e081c006001424840b80c005e840440c1c141e049181e8034003518518000100c40c003500c440c1c2040c0183c040d5a1a8200100b07000000710008003156100d0740e103e14201c5e181d0002c0c0c002003000f00c60104000400c48090b4a40090300b003107000c10301c0c5000d40b8900100c1d2405500b4500548512781c2440c041503015005544120011581000944900841c1c24444801103600c54201d0f000580050403c201c50303070226400041900499003446000300759054035202a800a41c0c0e1036116500f201c019080800c040ca015140c00040c1819503403802c4d0b08010303420154402141403040140e50300480c1c0300310111440620104009414034030f80d4910080d4429403046109a0107241c0c0011742401c1c10251000c064010380301030b074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484812230 1250 484810980 484810987
    0x31d030a0305070221040801111213151419050603101521140703082502060310140301090b01031403091504060809010b01080a0207061103010305011b0f020c0603040813090c09120503 80
    0x101800b03a141d4041c00030cc030007000300c4102c1b281819052040080c0300344961481a05410181d0320181c0c1c2e240741000230400d0324106000c208807070306e001c20380d41d0044001e140041840054000607590103a21a0040f00c85a4000601d401e440d821070924080b0950080c4101d030400302802c4034151312540c550001610b184401c0284c0c1c0104500030156920360034020790300b4944216258001a0780d0b80c0103685140e03440501080601403402c1c80480d80340380e80d10031002040f100c003050380d0319a401901440080c1461840c9010100007040602c1100e010005c000c05000c0e00080780e1031120070036040340c011480010346036400507000c00c1051140301c032281c805031991800b565039864404042d5202d01c04c216002502d4a440300401800b800141d400385105100110b4001c1c0c0e05407050040ca402e00c4498000c1000c402d0040088a401140081c11040265034140d43e039519402d01a00781d1040880c40403c941c14150005850314550744550701850302d03580d410402c7c55407200d4140c04801000c202404580082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484813480 1250 484812230 484812241
    0x6040c060c0b010e070315030501061518330306030b07050309070b0f130305101107110603130203030c010e1e100b040603020310020307031d030a03050702210408011112 74
    0x1900150344201e0500d40410044001c56510b21f010031958000c58141e910380c0c01c140308104016038001c483d0103aa02e030440480300b2038200f550317158465114039804400008000401c034842d009100038140900d1107005510154008020000c203410320041d500e010696000c115000d1003041100e00540c20300000300403260810b940c0c4641607200c07000c1e0030030341c1900b00180101e17909040300c10801107020381b004d0003090745035200040c107558480740303042c0490300704100c40c100048078640d40c12a510001e0721095126a036410717442c0c00070003003500069854072011901c864102015000812119007000581d203c00c55007007003c04148010b01441400390700617032030445e0000b03a1a44015a20b0388010300c0031403526581e8012038104401d400000b04200d8000007008030341509400755041c4652940318241c849144040c2180d00c9000300d039000d008040e00c8102007101c0b10b200b0400503104020204d036041d03064440f1280108950300c5031003030302103a5007031a19000c8280055010340754006c91400e8220801e5480c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484814730 1250 484813480 484813499
    0x31406120705030d0315050103060810090203031e070203070b0a12230c180a0b09010f210204051314041e0c060809010b030604080a0e0a1706040c060c0b01 68
    0x10020180e107841180c00000303466400700000d40c00c1460b1502c00244904054020313038030170303100754015506060030401308205075600011711404000040b040004c07050352600c0000d04500c52140b005401820302000304095481010040400314422400c45418a55800341d0192500076520880082400c0e4680001300003019000010150726020200c50050140981182102d00565a4204c18180421b40c200705c8030134908034840c032020031a00780b913a85190400d42c040a02c0b6848a130307410002441c515044040c040c2444424090441d01a00940000007036528000d4007d841182e100b07484051011141024520601e10340d00c1c500050000361350754903116503590490410394003c1c0305c0c80380c9500d074007c01c0c145071002e4060645aa2200001d0a049045600f501c0862810318442d400400500002844003070443e8440d2000303041212402ca008030008010000e5035100d02d041c4040a03600416024000c5a0070f4880c0d8800c103140c1c1d45440d01c0d20700031100d41e01a1400103020b90400c0005001d03d091 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484815980 1250 484814730 484814749
    0x911120102040503010207080301030b15130c0c0f0605070909050103080f0c030c06090a030807030c17062d1219030e04180c060206010602150123031504020907031406 73
    0x502000161400d80d81e2008642264000d01054503031520101c018420012141da106801a01e1080c600031092180d01c0007404404614102007482641ca040400f040c500601544080541011089403002000d0403c40302900b8200d903000c000600e114004508000c00b0312075a410383c1d0b0050005400e100e045c1080b6540755000080b00c4031341e40f00034081300710220010030000e0b2190b1000c1001d800c9204651801408484018200d1014103061482c0300001e5039021148040040c200170700060940c88080c0403801020281414203c681041811341c40c418160318224620b907c000c0d19586900703207040e2003d644901103221400328084404040b1004a032003484241100580280005140c0a03a110090525101c5220440d04460550001c00420303806004250042005002a24405e00705015050000e03405000300070700580c24035003041c14600103541c14104030300090116540300300000c0c200e240e03545089904a128000710340002e8100d61080c01000c8800348888400300146e00c514080007840702 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484817230 1250 484815980 484816009
    0x18091c050405040b06070b1602100b0303071b0b0705060f010807060c17040e0f090d030509150907152d05030705160b1602190b0c0d0f0207080d0c02010911 68
    0x17814400380d00400c1d114404c060190701507d132407400d111a00c3c0d1000e0304000d00100504051303850880480000d441c0131040750142c99010710000b801012818402410740070540007040000c201180f00d4081190002d0203d000e40d200b03202c0c5543d640c0c1d031040d05a0340c0c0c42e024051400025041a000e03c0010700250507060300c0d043c2d03501d49070305060b20f810070b0b04801e24007200c001e06403107a16024070104c84428070001078900b0141c9024001c92900058056441700f15425144070b081d1544000b41860105000200c040c121001152a03103950900d0000c04280419400c94035405050f440300320003042e40301d05841021080c0e00c0e201e0a40e0744200c000d84081e00300c0b0507904143d03440c8142d8800043c0ca0b507505644265100c44412100340b480381802413030222410344c00810403000da4020000300300042442a03002c0c40405c00582ea828005482001400180c8007070110b560000c1800010021228060521200480400c00c844c0b402d41c0303802c909030b0310049806040c090414108605500741030042034100c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484818480 1250 484817230 484817239
    0x3070f110c030a121709280503030a0605010f090807050111160e07031d0c090405151023010e1306050a031a06010503011409040c0518091c050405040b 66
    0x8140c500480e0404402d03000450700e520504e040d0500468211807109540010149880158545021580e44d1100c50f607880290046d04000c1e0741c0030f030074002c4002e0803007150300406807030312810070100a60140c00c06020b003902103030001028180b0207102c0c0742c41408031100d82c1d0040010794a00341c010740c1c2c005040b201d9447e0138003a2400c01d02e0410f410310f003450010300c604d4942035042e02d04400700400700ca9015076070f02524040001010321800000903400102113049540e582c4581302c0340790103840c04400c4039800c00282200340c00c1080c040085600841260701d0010b100c0131180c00010118100e00e11544400d0104215100b0311500c2c0c1010f0b001d418040030400e0002a150b6110000601c0041c441d034005c95105164200103101703119402c001e20f42000081c01c10a04550503d00c2c1c404c4a0041d1440050041c021200050244255a829540104406440c501c41030040c904000e200070000c654421881c825241d150420a152220001d000b44032640c6032424141481d04010203000d48001440d4070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484819730 1250 484818480 484818493
    0x90e040f0602070c05030709090b0123030607081e0403020a11210304180509101a0402031e06030c0f01030e030c120c010e1605090a090512040f050603070f11 69
    0x280d0395100070500039004e584c096803c1031a084c01c00d0710340107003500120170460501500400041c00d518603e8152848010301c0d01c09402513100c1b04002c9480490050740c5031203100c041c010601e4001081c00d02035880da5250081c0d00114205c0488d03000815100100140d00c9802e02c03a010445044442c0000200101414443d0181d60b403148070041c40b109200703045400c006410000941c04003011081c0180c211014480da15211081c25215104a85a00290781d1a5001c06001c402c1098068004200080c0110745030305201149044049844610204800749071020a81501e13000400300001c8500803d102042c42c2c1103001100a4115184121000e220520020380f6108040c407400e0503041130002001e4880100c10116401d4403448841e58099801c80300b80c06c2d0010900703059a1080d200291104429503c5040743d81c030050000c03005c043d2082c050500c41d80c1400001a00910807210950001c24140343c40d80c00b0840c0a20003594030324041502d0b000c640c42c5490180000707015480c1c0910641d40b6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 484820980 1250 484819730 484819733
    0x12020907110d0306171c050c0102090907090501030b040b0a090c0c0609030f08010e0907170f0106060e1003140a090201090803220b07020312130b070b07090b0307090e040f 75
    0x545000d0b02e14250110b038982c0c1d001e1203008032000703000c0e80164803c0020420071040d2104018000d00240840c400c00c00009181410b46809404880384c002024010103058076009a000700720005900846e80002e007031400c01c0107030345828001d00300700b9240100089130700c0d031070101440c00402518080300e05100141c0d140b2004103019208640c41e0728080d850f01444217a0245c4014034215050f0840b0440400d440d084c00340074000043c802d025640100701d2003a5100c00907001600e4072030b00ca00340d90351a41c01c1c603201290059100d1001c0c1180403054800c50742c07042c01c11074180e05071172001ca170f03281812022200147e0309461980000c841c02e801070400c0e04429880d9000d503800c0da4800503036130112104022506038144003000c1814014031441004030b080c44401d07800030f40c50705a0113941d1505a40080b440b107440318200f8030088014141d400085036982d0491400303d0140384102c421901040301c19100165880d000d008407442810556154a07429080142280200e14058019100301711502c18440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 484822230 1250 484820980 484820983
    0xb01030e2a0117091e07210c17010b010905060708030a02090f060d0203060307060306060c03030e030f040f0923010e271501050f062704140108011103011202090711 72
    0x50003813901c10080d100780030740054666100081d601042e5100d030300815042158040509022a188000d5131a1607100921401c080403e43c035160020300041d51505244501a003055022400c184800e032201d100850b41c0f42c00308a801d01a0a601030407900d0708000081b10b9403069401028440c6005114080b800300c1100400e4068006a861040c000c1d4000301303104d140e140400c01040241080d00e002e0211606112000307100516442009050680341c940390b46801501b4400c0d0348440056042e21500c450762828a60401016480384826052500340303410200e0044440c0108080c081c20860320680e4030f0600007848c422002458501684050008520071006d07540750141c030b04003000b00410a04032070341441030080740e06074801807047d010300c65112415203c2c50252180d900c83c24420125414648a00089150f4a508010342c031030314110100ba02e2160008400d41a07814040080050705c10314900a4800d20082c042d890019540036000d900514001c0b0616074041d55a2821606030060403075a20b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 484823480 1250 484822230 484822277
    0x190803120411030102180906120d0203040f09020a1b050a08030f0603010e0c03100e010e07080a03080c25020112060e09150408180a08100b01030e2a01 66
    0x20129901480c0620050041e8a11050018042200214604500072078040802900c08030820301034541c850010304907a90b004d58075464101d80c241910307650f806903100251603a105024590f0710103c48100030a07403d20901c00d07140101599112604016400d280300e031224404000e0480b811f21405a006001801140c095402600230300c100420505044c81051300b905e00d4440c08801691202e244031300d140d500000c40710031081301c48d0270000780c504400c6000c3c0d0241c482c180d07601b24588284d0400103409000002c03072003900c3e07009540d404c40c1ca03251510741c1c89140c460300e030a0341c11103010000b02c541124000d00c603600180d8414140002c010b00c2c450f0288040d59650780c0001d0601182d60708001d51080d060010000f035440100d4100c00a281581e90101180244052070740129002400240ca6882e8000b008000e840d1550031a0b12a006580c0e45001034061304100360b00090034041c0b080030071100000d607000380c1280025400740100c201d8480001d180c402d0024503040291385c140410489a225404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 484824730 1250 484823480 484823497
    0xd182102150d0f0605100207050910050301050c030405011b14030a06170a030e0301060612180516051011100f021c02070618050a060209010c080a030c080108010501080c190803 77
    0x82412110f1400480841d10642d02c0b00c0c0c0220104407440d0a81503000c10340e80192541140c204015031500307450004006441d03000b10b5010b6107481c0c00d02284881e1303600030790711079803250000f8001001180700250150720100d86040105820740c07881d0162400b0140910b0b84025201e0f00000d0240da60b21500400c00e152030302820240c0c01c15280030040c940d00a20f602c3c048441a80207210301440c261005040c0380c902030450300f54030740d24141040d0710050800070380c802d1a000b02c110340c486109035005a01031800d51113054030551150b240800400d0069145645440c2c022010f0140310403101c1e01e001c042e01d0b45002042c3e10950803c01005c0c10301e00c811183c400d0721001d40c001a10f40d80185003030411504c24100003400184041c04110005100054104400d0f0740807002588031550000145d0710b41d0002c0700000d100c43c02c0800c003c8441980f540c4083c8411030315554650355a44d0700c0e2041805c8039420300450443d50001c8016840705e013002c1c1e40d550803492020a00e440c1250b03965500d6030441c0c101041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 484825980 1250 484824730 484824757
    0x10b100e100201050c0a0c0c090203100906050306060904060507090f2304021602100c060513060b0d05030d111b060106080c120708040218090d18210215 67
    0x51203540d081544140200e400c0e24002041541040c0f4402103c038069000c0d00010400303030110381000c00900104801c0204001c410a42d20303414004007480c00c680c400e000f0209202d1900300c0c00105d40c9800600310b0f0045070084d21003250341d104c1e0b4880c0809490000d14060a209012400044943d10800020010300700319260301d0004441000b0344008140700403010f8416401800b40955900401c20b00700c0c1d00c0e40d81140e040c0706c0003a2440342510040c00c60080940518034000c100415422807501c2c10154901c6a502000192424020400783c40310110004d00a58014002c0e086080d050f03901201122100b80c01f45030900da0151500fa0015512140342c1c1c289070090801084503940080c00300e500200088012810142004402e2420300001440a8100050703a0003040c1075417a43c111480c0ca1905142030380540d46017000480da41e40503141000800621101d50600c0d07440c0794041540c003a9101148800111101400200c0345210100010b030382c4104c200702122100e040c842c0080001003480341 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 484827230 1250 484825980 484825997
    0x10602060601031508030318070906030f020a05061804050601030e011d07080706140a140a09030506070903050307020909010e06100e06010807320409052706040b09010b10 75
    0x1030004055441d00251642540c4c02c012003032144407004001d6a88c000c409281d084120010300c02030700e184c412250f011580562803c03a010090044d0105075400341e43c000d07910400300a507548123101d090300c200064000016668003484140b80751a40050340c0bc00c005160202e51000040c01c1c007421a201d18281c14010404d8400300c2c01c2c140d10520807000144580005003450351302c0c000313005c0d00840d072090780c5410178000028900c413800d01503000303207412000300d4541d1902c2d4601c650000e4210041c0c1c0c0010780b858454040040e9240d88150280c1d01507980c440007943c03c00c481a42405041100a443c00d8a55521001091182403040060b5440b407030346188964082481d201401d0780507000648624100104442000040c070780010910801e015000207195010310f008050000900c803030040c0c1c8002600006001619030300541186008000c540958541e4408205091110f03000c1c030000c41302075800c40800900403403c28009035078400365010010a003220510000f5000402044141300410340b0135 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 484828480 1250 484827230 484827241
    0x1b041b0507020f0904080f07020109030c0e0910020f0d1e1517032517040b0d051f0b030c040b07030518100e0d05120a0c021512040201030906090b01060206 68
    0x1e5141150f61034141c42c0c5102a05203900d4404882c440d0712154848024000781d40740842e4465a030781340003103402002d04040b09480f10341120390408140c079136031214499203110b160a200a40b086440441d50504510f190400d050b001c84041e08200c800036171040c080014481d10b41c80203004080103100c1c0c000b814554141000d40c3d50340c1d851a840703018182d96000340000110106a0602068000820f0000d280e0100c021700c5c00303075a0001c070001c8032440f494011070001601161800603218544148400703200d02e179544800ca040401507200c1010700908905c00c100b001c6003800e4011504044010402860aa01d90b0555096640000011000140002030880300002680c0082d0840102120103010703858611030020700b0200c2e18100540f09442200003042001420080803104c0074440300960745a0060320400f40c066000c600c408e0740620b01c210250400b00840304202c800c03d107640c01e12080941c0300e58004400401d00c43c01c049034190b98070310044010424000405008107155401004a807410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 484829730 1250 484828480 484828489
    0x230a08090601051e03030d0c030b030d0c050d0e01020f011503020406090b030714010e0306041a0705030915040f020d0b01140a05012304051008010305010615021b041b050702 76
    0x30003021454001000501082d5542041518244205104540d0300e10740e800001e070962007600d03d0350a03003e00d868610307100030b034054001502e00c0b00c01300d003501c441c41c06240c1c05a90805410034001c1540c0c0007150701003070881c012903e100500006104a440e44516200650f0071039940041e040d814032011b00e410402c514060051a014141550041c000b00131a900440c1c0d41e240940106061202480702c8070405134440c0c10f02240ba4140202103c03058106802c28071903000171a40d480780c20b80100c100141c0e000e0700600480b401074002000805600e0b4004420079407906024104958841d010402000940c2d180021820340c00c0c02a41400d81a524080c0180c040000c030726285c600800c85804204102d81c1c200d03440c6d8140c00829010804428150b1070021005e11490300410f502008200c0c0d51418998043c4210781620700c2a0000c0100c0c80d00e4840448855102c0c01481c80181d100e440514507940500d92016a800e0002e0b2010035580400928044041c442c0b84450340051800314900c42503142 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 484830980 1250 484829730 484829747
    0x70b03040f051911090901181104140601050a0804030215160801090e0304030809060705010606020d0e040630080301060e0f0609010e1e150d0507020105060907030c230a 74
    0x51030303141e5944880c45070f51880b441d07546402c1100c3c0305e41004000900c0d21002900591242801c050504e04403001d18503003448240c07465100c07503015a25001c90541a60300422415000d480140c641314200039541d0307001c54140e070000b00102c00318054000240845041000514080c2400450702500c0b0380c4174010090072900305174031505000e4142104441e500703034003104880640c0e4200e10400ea0715110500410418482e00d88010929840c22100040565012680c084910840d80d1a154519072000810082c3c1d5602d000d10a1714115181c00400c3d040561054001c1c84036060ba0003454215150b101e50010380c07c03da11150200305202c84101292074411118103010a040354902c1c144226603000a00502811241ca40600902450f050742c0184040860205020050000c00341901c001114900da421081000300010f003800e01180f86540103000d118816030010700160310395926000100c0190121030b07005c3c4144016610000310070340700040801c407000942c152440d924220144020448130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 484832230 1250 484830980 484831003
    0x1e0c11100918090512030105010813021503090a060c0315060c080f09010504080105090a02120f0c1509041107020102072310031e0914070506030c0c070b03040f05 71
    0x100032200d0244415080610300058802050101030b09410000c00e050040c04024009000c3e480f8841c10106181c1c0030800840c1620401c0e6a02200c0741c03111444040c1c00c54510034001d51007041d810403c1003050300540038581c05880b8408442c4040081d8403003004968145910100090b21020400e501002c01d0916000a2545c0d10740450402000c1e1150b400c94040c045543e0400b80002504842c580e10400680e40076001500003041242414400380c4d5071100d115904038011030002c410f8910030703680420342005403084c1001806c024800b4004010440d402201c0414160000703001d03000c903503116445504038690002c00c0301541c1c0e6a990002902e01082c07680b0462200000a40707019080d50700407070650b14003106540440998680070415409040d83c03141c012050080c443c000da1100d40c807170b0007000c50075004903200c414542c803801115889602c0b42c0505c3c1d0b0020010400300344c240c0072a000802d8841807550568513a1900c401c281423082e40107440a450125800506100b804018401040d514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 484833480 1250 484832230 484832239
    0x31e0e1207150c0305090d05070302092a09130c050d090b01050301050a1b05030601050f220b030c1b0f0307050a030f030c0906050a0e04050a0903030b06040b09060a1e0c11 75
    0x200d446a134028402d20425a0040c0030395581c514190801a080080300040e6034010800d450a1400c21400749400c54003100740320000030304140151007178a0b102c086802d20350b409851a2021822803540c113000c1c144c0c204024041000410122100c40641d00c07806000754410075003100d00d545080109400e440d00681243c014a01c0c003001000f1000000075203101c00029130a08a03183d036221001030324203000d0340c6080f48490758001840b141c0c3c1401c004014003850081001c886410b40c603910041c0181c0006c0700e91054842c000c00440d50380d49a0107030245007100400d4111204004401c020700e00f150028181202e06601c0030b12080d08068001c2c044080700842c138030381005510000c2c0703401001d4050a100d280b044c080e00082003241288146004140010050418445800d0010050b0010f0a400b18182c00107842c4c010207150368a04039080f6000c44171120120307400c1246540400440764480030112051020204a0079407440301c241c07101c40702c032180e902c801c2000b0105040271181d840345094094400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 484834730 1250 484833480 484833497
    0x3050f0124050904030f02010e01050717070f0e010302090d05070602070e012309090a0b25050f0915133b0c130b0f040f050a03031e0e120715 62
    0x950f241c501159500c01d4241c0782c502c1d40c4c030306400c500341e0040010126122180d400c007410029440d0f0040c61150000500c058002d116a840340404ca50001c142150400042e80000761201c080d8800d401420103040010300d50100c88089036078652034004217a201c20007681205500304000d0b4040030354035004140d04041c4d0072840c0b042e6091103203030b00700524200d40318080781408610040c40170445041c2a40e8401d03680c84032420102d14881040072840aa01c01200080001107580b074821030039a85d80d085058040c0e420903400c4d204000c95000e801c41640d0260038140310340b15442190000c001e004100364910391026140780041440f46100140d901001c810385140e586902130850b00c49594401443c8100e103860301c00c20035036a10143c2c1c079075119840a50000c07074640e14400c64500103101f00c42000e241c810303290780c0e29400d00a4040c660310004d004191a110501002c107081d55407200c0016a030314080002c40d8520000401130103100140c400c86500c13040003449000410002011402e0f1241000c2c40e4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 484835980 1250 484834730 484834739
    0xd06060e100f0f090513140c04080613050f1e16141905180a061706011211040c02010e0d0207140f060d11220e0f060a03050f0124 57
    0x54421540390000c0000343c0540c025410322583d2010043d100003802140b0301070007416418040e1084011030b81c152600540030810364030a08080398200d89446001d00103070780e0ba4a00c0c1da08100704140c800d0703445004c0d202a40f034500b203042c082d0011227103045400380b0704c04080d01c101c51300d050b2000044c20029803a01c030341403012811039040d012159a0851740044a0409032411070441070b4107034032054018110a640400359a0f400840602c202c031401c00401001790b59118021012180c9004c202d65908040e0050005100908102103070b80e0043c48802481702c58200883c0071100e074074a9800c0180d65803490115414400d200d62800040035100422495041021141010041a6165100d1200d410410401c1d803606d0f0b094070800e041c0810f042003404a03540d440e5040c0d41c0070041c8441103601c02c0c0d18810510742100b0703443c02030300c820181c1201d00d643e841405045107140a00625807182c10740000000092003008801e02c0252580000308654040020045a2140494901001c001c0d144401e20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484837230 1250 484835980 484835987
    0xc17010207030509060c011e090201030b032b0903021503011707050102070603091511090a0f0b2505120a020d0302090607030c0807080310030308130f020906150d06060e10 75
    0x3c0c0c2c01102212402c0c0e860900550507070052448d00d01403c0b0045641c000c00f0070485480e4080c1401a001b80c8042c4419501082007540325030380940c54411203042010803890350a0b04002441414410341840712255449030006242d01800307507001d1800010020050181760303821441004149909002080c40070300300700001c0c0d00e07138810707020b10703000c150303640d01050305109103200080b01c007401081040040c07074411201404280d0004210601941150380005099a04182c20004079032201396664104400900003580d81040c68402402c401c42e00f02074000401d00c02e200d80c64916960040c841e60b12030f10414081d04050506188100b494814018410390b41c031000211046294145809030b135441c00d61401404500a1080185c2004000310070021030002c982c62140c04d03a40641c490341d00540c1c490404501403421000020555140034882d840141000310610381c1000008095001140401d50241c03000c3e00710700d4460140a40707071041040003e0f04440000c02c0010150f44110500189a00c00b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 484838480 1250 484837230 484837237
    0x30f0e0d0b0606040314071d040b07030b040e1b040f0e1903090810020a09090524040e010e0a02091006021203060406150206330d080906070c170102070305 68
    0xa00074403400d60026036aa92000101c8000e564421b0300e08248100030a051503403000d041c001c1960041e41d088054104110b5508903d10440e070102140c055035480c51800c6000d4040c06801d17a801585400004080b1a0248680103541c010525180c41110a140030030064406000c80b203500e49107460144109144085030404400c940740040c0568092180f0302110144440c0e0320102c10390180c0c40b40800c940502e030b00142143c0c081030740c0d003038030f1340d600c40b41d4007001c860040d103545503044585640d010034042425400c00440b4070050000400c3d044c40f1145074250340141101450542109801000710320740072403541c2d040043c58001400d5142031000181d603440c841c00c0c0c4604004030100014a081d40d858119001408000c48955510081400085c0d81d458058902c42d025030040310380050040c80f00f040c3c102c2c1c076000c1a50305030441c5884006201024664003c1a60101c1c0204031080960721004002c02805209031700030401c0511305407000c00040c80c1d425041c44944d00400c11080401d42c0f00b82503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 484839730 1250 484838480 484838483
    0x81e24040b0f1303030207080403020d0b040c0f0b07120e060d0b2b0807110a121a0408041e03200901090c080a0b060705100c0f170a05220f030f0e0d 65
    0x160f5030006404e010849001d0ac0d4402036010800c2d800400802001554560040d4421b00c02c40003d281c46182100c4548014050354151000070301041d40816903000501c5400b10842c201014980c21304d0020910580c00994540d130f80f04c5c1c945a5118003824a6594410000c42c0d000c244107803079000c0301d244010119000d00140c0300907404a24041446100352510f6803460000b494411559a161912180c250903a0301c182c4068220100341850020400721480c41a6072000310145003e00b0106d48102a070125034640394509221000400040c4e0516011009910005181641a020700c1d040100d82c00c0140c00c0800b01506041e18891215008070607180c100d0005040031642c0003010b00415110b00a80001030154400e405d1746c040c00c26510303800070f04001e085a1310043c425808040c103444601c0418000000c1c8000e1000180008200b640f06e15000f41e1400e100c186140030f030603200d12451800c2c203803d5030f103901c844048004064019840d006180031600b050f04110045100040b250422041f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 484840980 1250 484839730 484839737
    0x190504020a0b0f0f1612020f0c010503100801060b22180c0e031e0d050f07060b0103061e0602160b07020907140c0f10020301081e24040b0f1303 63
    0x5500e2a209206019513043c18006500280c40300303100d2500c0c07400207181c48400d5403219007900a03c080c0c20305c041803d0007018046001802a8a29000111290b91000302003607100c0300000c0c00407070801c1d02030041d50004d103040081c01d901d4040301c0c02280603200440c8840740601c582901d040000141c0d0795040c2e420401140400281d100b200c217402d80300815001e500581c1800f980a10220041c24030110810400c01c0c0000c407255a02300810544103803244150114900c2024001c42001400d203402ca400c0300b41040c500494040c1e0303601c0141c0c101154075540d074480300d003c848007448056030401081944410007584c8142940c0b40c2650707512507103d800030280c010030070300e000141e071103000c0c86442d030741f003001c04000503543c11088903210344402c115800c40400e0301075042d481c07136242810300a99068501c50300180050059000c0611600e0070990311341c6106004e052810000404803c0440020b580f50f181c0344105440d141c60301da4001e000061002d007410400d40d050018411002078100741c51541800c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 484842230 1250 484840980 484840987
    0x192102040b10120c090803091c0f0305040e101202040e161806050f0f010f020a020406090c030c0c0302030a0c0f0506010611060f13120323190504020a0b 67
    0x324029006000700d481c0c01600300c8a007542c60300c2e4040b4280e00781ea080c00748104413000c03244400b11030703900380c61152941a030700a002c001c40520f400900741034400c403403080c0d0001c01040303640c1c0d011111840400603004180e000c1000c0011418030301110f58030140300c0711144034007418400300340e90f41d988802c8064012583d0b48494002a0300402000180103503050785a801c8940c1c410000b540b08506a00301c51001d409e10706c0000b00e60030300b4281c072810050000c0248250382c0d0242c2c011654000022000c00451058a44020241c0c03114131440010b0034281c10b01003074030b015240d005011340354508040010021a0480c1303102103507010080d11170818140c0780c030400284860070007005490034958003500c1401480c00000b0142c1d0801c01c5084020710000a4800a07580d01c0349004001d48210b920016405540f4410b1000404940007003030043c0490400080e006182c03003500507803486e41a0508101c000100601442c803c00301c1d5021901c4105c49424406481c085d400f04011400311310403c0d41c03040300030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 484843480 1250 484842230 484842233
    0x201091a100b0a030213181107020d0f02011407120f0c0203120f09060f0c01110c0601050402211501081f17030f0706050601090f06020a031805030a0503091921 70
    0x3501103030341104608401620040c0c440d14444c0500c90707060000c7c2141c501d000e003194a00050801914080350300140030b1182c600380e40e1900c00d122484c00c0e83c120b0401842c8940314241510050107080c0c000c3c01362400c0c4241c8060040050000c01b0b02140020910130181c01311001a075000540b07a503200203e5000944602c1041803040c5240220300c000c070390082001c14801005140e0401900c1ca07034052030002d00420301c55602040092150140442d0280c000320010300070350511b40c004010410032a104880d00c05180c529080302b039001600c001c03030003101100d11284a5039100d5400c1e03802150141041004010a440c11100e0f00c0c440d1003048246c3d481c01c400f080601109000347c0d142c12401c001c2160380d600040c5004002840c044070103501041085001103048101100403e041d00c61603001070040800a4038143c55075414481c48000340d10050102042d251828054048018402c80c000c5495101c0001044144494410001c0e40c4c080d100d00200708003405000031140514400d84002d12520a5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 484844730 1250 484843480 484843487
    0xc03040b0a0c18080616090639050604020906061603031e090804060f0c111e04020f04080f03070b01030215040305010c08010303030f1103070e030304050a060201091a100b0a 76
    0x41201118a00d03040c000c0000e021240403c030148681c1c1c444410f8086e1409189080c0c401d28541c1c0030320f4002854110040c1c15140c00d070441c00c0c0781300e02440f42100078991081c0303281a07441e041c09011110f5030004030901c42142001d144a5810a40455219027803101500c00f00d000b5100b0440058109922401001c42c0c84021525180e100080d550b800d001c2419542070649041d031051180000080c1212080c01d40148200b4080e12007035400071414441424070010400400c1600e00b9160407031152641040d680d40e607910050000e41c00954000d82c90324a04410740d07080100010030144203400801203100050716080c001815254101d860014070a490340405840e401640c00040c0a58a8500c51003215508400241d048900c00e540900042c940b05402c28140c41c01800f521920354424000f00310304a001e20812410200c01a04581c1050355540000b42d0b960398079841403000d40d540380111000d00282c40b040c000828400c100c0c52659080070745c140000107400b8403034907501c03100108040035810712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 484845980 1250 484844730 484844747
    0x91f120501350f0c0117040c03030e031c09050112060302061209250e090d090b09060c100b0901051203070303021b0607020c0910140f030f120c01050c03040b0a0c 71
    0x64000c072051020f800e80400d42d20502c81143e039001c1219030584c00101254172483c0780c8241d6000302500003907403456800b42d0311801c107046e032903605009103a14000412648211480440c0032652481c002d40c1c40c0c130001510445814032000e07106070414000740003586030001110203011610804081030340d0742440345810304d129018070400d541c0000d00c0d21034a06075154500ca00b40c495030f204840c0d02d510380c0701c007042d581d24070702c200c00020409200e010441a10b03d0405400050005441c1c42d00d003600010b01281060504400310300c400360b603041e880c607080c181f8480741400b501c0d09030744139103c50741030782800e0303a6902440360000c04058000554004081024003c140c02080640484c0e4450604a801940702d40d0084011805220b0100001b18080d0540400b48120390480000d488425004411700c00940b001000c4030f0b425200f132405580e60281c0030000c0780c4a10000710402034071601a9543c89003910800750181104010500600c0081140c0060f0703181c000020301000180085007940603614001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 484847230 1250 484845980 484846079
    0x230c060d1401120302010c08070f0305040804081e01051e0f0703060f032405160810170a03090b040501090522020a0c02010207050a0605041703091f120501 68
    0xca9078000114000032080710410039100782c0081c45100302440048400103c203e034800e000409032150300c03100501952107150000c0c0145603040c40d2039102c0000c1e5107002d4904540c1c03448041c0100c010282c40000380b181c0ca41240000075084203480d0006141e081d0a00080c00c031039804581c40c0081048140290b0103040100b004800d0b004080e592824016109100260310038801052100300b1105503205100311481040c1d4040c00c4409110162000c54185d64000c1c40000301880a01c40030410281c041c05003c01d1045207001014041000d02d0300038800c040c02d40c082c1c07001007001e10003031040340e8018203124203641040d600004003c210410b009814500008080c18041c800a0720200c4036601422944030f0a0003a000c4a00c002d61740d50511880d000c0500c11880064000e10050182548051070b44c0340d20300c50b150440e418400341d00d000420050349003214903c10003c900392040f04a4101c90078203005810004200050740c500f08084e20001170307543c04a0700c1443c035201d41e400d000c400c5070403403980d80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 484848480 1250 484847230 484847261
    0xc0c150c1b101103070e12030d0209060c07170d0809060a05070201021620120618070e010f09050f060a060e1203030a020421030c03030b0f06030403080103230c060d 72
    0x20f01c200780c0c0200b5078402c0c1c61182c0050b2007203090b400d55040544c4c2140320f000030200114030f455060b41c2c08030002d400c0f6103c0140d01480410100d21030400c100541800750404a404089418650101038a001d20904000b0280401041005450103001c100e1030740c010b402c3c0002060f2680c85520490083c0301d03440311310030282d00d00c0300d0b40c0b01448030010008202440302951982303854403c4041180700d414008260040741d00c9400014001b451400d5402212007140044070300540c3c4980302841003503807d0700502c031440c43c7c0003410814a84513001d600d030444244291468142403160200300c80b8003070b5000d400c081c444007101c4038805458a22030350614588410559490b8202050000d004e9072151190703105c00c202508946076a00d81800c2040c0c0481e83c5074459002c0c0001a0350140d014090844505500c55030b061000d4102e92101e0005510480c071a50307035a0440e40c1075152940c448101d5141c2940e081140c6400041084000202107140c108100ca240d502d0715000841e05000e00701c0b02c44002807a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 484849730 1250 484848480 484848491
    0x304020108190c08010e01081b0d1b03050a03030c110a02121e01050a0605040204050109030b0603070f26010b010e06071502070c080601060e0105030f0403030908030c0c150c1b10 78
    0xe0f40c2e4000403280c180c40c42030b0030301d000d680d998881095855445e03072115011240201c0e1400d0840c82c1c08402848400d1284088410410b41400103014420781d9a03c00d90f000e0300482e00f010100b41d0301d4812900480e81c1400c103c8810300f417041c00310303954151104009006000941106419000400940c0d1000382031301c001844a481d602c0c02c49000e804203070381c109901e5042510100c0d030340c44d01d070003684c05444060707441d82c0b07126145496100303038418040c0a450b014060004007003807510800c05071402034500c4c441644540300992070750600c0c007903084024201d40e924050300b2a840760f9012000d038821050884404d43c58070041d0403c80c11070500e01e0310b404101b40c03001964404004038200504200c1c6d00010070356a907030381d07901c00070740b210a2041e40035030000d80c041000503b0804036020098002d030080c600000c508001e5a030300c01c410341c801c1c0d0300560345c024080780c2120307810410041420326110156280d4414180840035240c140280000c00d16003a8040b00d0202c0103940800001069040100082c4031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 484850980 1250 484849730 484849751
    0x3101503090b0a060501120603050d12090b04030e0f0a15030b0a0f0311090a021c09060f05010f21020f0108041e0b100b13050909011118030c03060c030402010819 71
    0x18001341c810280441c0c091441d4440510651185108490304000a01443c01941c103088410f02036006500c1c0a40c3c0c1c0c0d8a0f189000300d5521120948110f03c692118002000c00b50104000781c410b5140092051709551000c2c440b04c0b2505480c54001d03200350901040780c03002500081c80c58007564101c41454042d44e000082400022108582070480655041c134060300d420296605074030520429103000603580a0500c5031070b070240c2c800525180103d100107080c0418520702c0d400d503282a4042ca10345003944400341300c2d4520300141481c2e01650084910300d0a402980410170038811501c4084c140226000003a09005d03010b80301081d5004440c2d209025032509e803401182107503068030006d058a00342030011035071110b40c40840344603002c15504407021620b0a0104002c0507402004040d4075504c44640b43c418030000009040344046003003e02190002c40e10070726207880000b02c0041d200e03500c540148813204c080c84080b00d8000d42c082c68803203010303907624451a03154280040e125500c10702d050032061 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 484852230 1250 484850980 484851001
    0x3060908041e140904020109081c0f05090a030f0f12030911010e060d09170403150e19060f06180f0b12030a0518040204080a05060a0203101503090b 65
    0x1041e0303044452aa8a02c402c100d00c100c20b020081e000310100360803d48619441450070382c20319507215105240c0306c40c0c030540303c883e920700b0a04240c940107000a0020800390071590011480000c0000c20315180382015160800280b201e0050704c8081c0c04410050b0b002001c2c4078544684904640d0003d6040f41d111890f0700c0005d00a106028003aa51500300d605081c0c11503218545d95038500354000c04d82414000491408801411004022690038140008285402c003603d8003500065002d41000e0f419a47e001054038141c40b0103e41c04186500880060a00c0002581c41c074950240c1210f0001124452210640020410340c0c02c041d40c07810902201c800d01034801e412110b0301c1c2c3c0c0c15400a01502c0341a405001000c00c0c04480c50300f550b00f043c0320002000b4482d43c040c00240032404002480c2070000404a0101e07485904400401d4010130114000e1142c200511a0806800b100440c41c40c80c041c60f5282000d004d500845011071001070080191511903003103ca40c145d00070b40081c81a050540030003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 484853480 1250 484852230 484852237
    0x3010b041818080a0c050f030d150f1e03022d010801050f04151701021b03090f04020c100e0f0c010e03030702040e1005100f0b0703140d0603060908 65
    0x4208824001044601c0056030303016942d8900941d5030340e80840c18103640e40d00c1c50398202e00001000c0222215540021070300400003215050a0100516903c01088a426080e20180420320240300a824802c01c003070100c01e9400310480714070764401b0198003041d01000e502d0910a62001c6c1d44031410801040180390048819401c88160741c15078550202081c006403540c52092160550081c8000b00440711801c080e000400c5207845403490568258440c0194030681c66800320701c40441e9400b02d064000c00c003000d1a440041c40c1a440218200700c1184002141d80c142000a58060784e000700da80401039a08001da00341a0303203418030034007040d43d404084e659298481c0359075039001d1050840c203000550051140e80740401010300a103181803401e4003480041d000f000109100c0d44501c0300d00c07510f0500c0394071803d0b00a504441410294514161000480c02da41c2e8000421210041080c0d20000c0d8004521007500f040c00b03403806032102ca1200f106001030440780d20207081c160030803000808110015008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 484854730 1250 484853480 484853489
    0x14030d0c030510060e04060504020c010e1504050a03200d2c1c0221010603020109050f06070605090304260d080408040b0c011506031b08190f020702040203010b04 71
    0x40060020400c4114190341059905640145a0110a00107144074040d4444414405440890b030603075518041000ca034060156110b969540302030360741c400380051010816048540582540e00d041548a10b0744807450148002c0900070038031002c036880301e0056400a000203801d8141d0744507201143d005080c2c0c440000c10720807400400d211100c42d0304141c103900d00c541240542990002c55071091201d0010964060580e4000818448004c130154080e0034426548000d000100d1040d1442c0300240c040c540030f80049105408a0004108a484a1040c1c5e120150041c001040720784580000c141144900e810481b003100f130f400070b0440c084065808040f01d82100200326420f02c801060f04640d92581510018801c010420003041414070040180103104409000003e0408814940b614154a80c0e80240c0219444450061003400c03100c91000c090565406c02040c9807a0250000081c0d100c0c0c02006104035175a1254152a1b001c00e038150740310940e01030421543e95840f50f00c0c480c510b0304540304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 484855980 1250 484854730 484854757
    0x1b0b0f01060302040602070614040f031505151c11150a09050a080c10090b1c1802010206070318120522050f0405060d0203061005100903050c0d020d1403 67
    0x6107244280300b100c2c01c40320103501078060f076414407108440d05c821001440301c01100c14400030652051001c5900000d41c07040c40e80c02c450305140c0200200360740d0001d01413214500e684852440310b031039160500000713042e80c0001034541e0409103020404580450191604484491f05408541110344000c008000716521485425941d900070811020340d107010b04c034115000803c0c1f2010b07604000c0785200380c102c1d80341812900d0945500102c0302e260060001280310443d01c00c000c400b500414480c4850030141c011002c5003503c1250000303550b81c10301030507840800d41d641a0750000d0440403809143d000b035000700040b0300380052440062040d005000c2c1411000b41140742858841000d0501504881e33000e04a8140920004200300042900410340c41e040602d113100c032401a60280001c520510900c80303c2a002c82c204814411401f4450b420441072049998050021a100040342c1200c0d1004039065501c2c1d48061003c1100c59542c0c40f001804403444a52a14a006011018281c40e0714000e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 484857230 1250 484855980 484856011
    0x10b030a0f020603250c03030509060402011d010903020d060f06050d0b010b1308010f0603030e060f03010b03150d20010c0b0703050601020f0d021f0c021c1b0b 70
    0x8264480c00800c000800c100c0a100d8114014102440030316484000d1114491024082d6002c046000c800070050744006a484c102c0d400406803d0300c1416005060740005100520707199002a003041c000c030300c280665104040344180d030baa10403655880650b030301034018441d0005502d800d401402d0301c101500b6003076042c0003001c903950406d030b01c0c1240d81e640c02070b401e40c50700e03483c01d00d400f5030590010702840484d41c5a00c40114084509000f000e107180401780c1c00250321451800d0051034001000486807207040c1c1007090061050b034600c16a4151881d00f1041540c1e51a454002c4500003501c0c1d10703031600325200391888021b002107000e45100c0301a502c603016500c0c0d400d250045506a6598400370f01c0300c0350f0b800206a200d8800e602142d4404411700440300c0009007a00750b03618180380c100c0e200005034060a5076500c8880701400003a14200101014005904031283c041d4a81c0e00115050800c1c0d00c0782d0124000f80741c8103d009480211805020b0700c0c1e1a509810407030700415048440014104048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 484858480 1250 484857230 484857251
    0x902040f050d02060d020c010908031806010e0705040306050a0b190303030f0209091f081006050f120a08071a011d070f08070e0619030518030301030302330c090301 72
    0x18039603034242e42c2c02090030785440d00c1118050029000000000c001e90b59600004000400b420000d5003d90030040107000b00c00c0080050310326111058000150b64010308040c01101c0e171b008001e44040d280d100801007800d1340c07032100c41002400c1b0702d040e080d481101c02e0f648070403400c10821034105490103590107001c98440c0110483c182c0c89040700b9540c00240325000141460000d62400511070300c2020041d414640e218070440c0350080d04032045048690714603040001c0d14048400d220000d1082e100302201031644a030468880440c22806000d003140082c28104110210494414404440c02e030b00095503154900752401c0c03154064422840b001c2000401c0001d0300403240412a4000d5035103e201c1d5589084040700c91f480d0030440560422401c1c009954038400700c1c200d004151001d5600001d540ca040e40700821903440101c20603929070030410060000c20303804505816001000003401c5074051902c2d0244140180c01035503401d060f840d48041c4402d00781120300a04500508a0081c060390350034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 484859730 1250 484858480 484858489
    0x20102150c1605031603020102090a0f050d0602130801020703050d05071814010e040207140d230f0c03030f0403120204060e0d050c0901060c03080106050423040e01060902040f05 78
    0xc0e1640868100c00340281d00c51440d0501c0700c4000c0c2d40c4124181ca0030480d510000d40040c3c24401c5046002d0f07500461032200c242401002e08000b401007103000d541d090300d40004110b40301400100a008260000f80302c0c107010000d020f104004008000007159106443d080042032500244411080079082001290045105401d5010004140e035902503119181680c6003041c181c40306012814001201001172882e0340d03520251000b140180700c16610190200101410442080c5d07107901400160386051682020319160742206443d000545590f5030890b03001c0c1c00c03081c01032040c40b0317120307100010030080407150254801d40076910039160750144c04c0244010074142d0141e0302841c0009041040190038a00d40350001c102c2c402d0107503050300d00142c3c50a001c648901d40981204000c81d1560f20040304040d40682104d004140e82c0c036010381094100000715031440f1524520700c103080c1040503401d206a03580d51003410b4040c44003008110035980e403042c60300a50000d00c5482c041110100000a40d03052 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 484860980 1250 484859730 484859773
    0x3160206070e1c0231050601080709030b09150109021c0b010c0303090c091d10060608070c1a15041103010803090d05100f05060405071706060a030e03030c07020102 72
    0x8000300f0300c1c0358039480e6400e00c80c2c510740b400380142c1e44111024509007031001c801000c0184c0d01c1c2100d0303020691015690001e800d50b00041c3c861410030210101300030301c803030b03201c1000c2050701d512820720900d649401142c81d2500040307068828030101001c0001440ca8220b600030040d0301c0b813100d080c0d001000910205c10445102e1000a4081511a00e10900007840707640507000551213000300c400d10325210110030782210550801a1300c01900300d4883d85124108202031090b045d810b0344280b00480c240030380103000b0007010341030009100c0041d0401040103446040250301801d400c402001915207121040c4c802111a40900d005506d08401c0b0114465a00c0840381a20b6021004601e46807511051001c2802000d8082e00d60f80070752580c41e034000c40709010300a000340c3d50260200d02810010208401c0f274501030b00c04428044c03200c0070308564050581d50b580d40448116407842d00c0e0b0f505400154090700d40d4500841c000d000000c00c211905082c0b0015103801030007030b070885010075442300da03c801004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 484862230 1250 484860980 484861007
    0xc0c03022e02040e070801090603080702271014040501080d0804140118140c090708060612040807030f2d0c02030613060f020915031503030316020607 66
    0x800c01801d1100c40041c80d40d10410844005401d039801c015460948401c030381050700100c00800b01c20052000c140d40c010005070150001070010081e161840c0d80d40010b51141050081c0100d00483d43c4000000401c1d414402059281d4040000e91501d80d800d0340920485008240342403100f1001c501c26802e051251505840390840103203030080c0002da007520b521740b00400450300212245040c5090003170a0040c460209240303055128468802d1410085468403850411269440b4403060205a41d50000290304001581040b85960302c8800c04104a40f00d0907031203400070507001c428070040003410001018524000e40d550b00c19050001011565503052a40752800ca407940d08a150fa00c0051701d222014007651030600d643e0701e40380c40c0d011a09207801203800211035000003c4500c1400080c3c0100c14141c1d613881402c5152000d100c0c0003d04200003c400d1641c049030200006000c22444400185070620040849469107401d1450300c0c0d04140f4400050700600a00c0f000c06c51490140c4030186100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 484863480 1250 484862230 484862233
    0x90516020c04110f0a0306060f0e090402041e1815051b161a0711010e120304020406031a07021011070b190608161409190204030b190c0c0302 62
    0x3141d80d040101501515003000c0e0a200c0801c056240340403032500070308080402e501e021800a04e00903010381800c204085250070300014041400c0703030382e40301c9948a502039130440f4000b403101152207103509203540c1c10702e040c1072081c546580000c102c0f607082d01c1c0861f5580b0414400340c1c101c04800c8030005540003541d80760100001702c3d890114100e40d19018088810b02038078100c0229945031100110011940f01e101c4413602c6150600040c542e108469008141c4c000d1f00034099030410019090341d035500b003401a280030300003102060856950f40c104c0801150440c1001e001c0324a01e401054460030f041d2240750161040e0a444440c035010340c001d010a4100c500c0b005800c218850301d0b603c015090003450244500950300030b4010ba03c40c18030680740940a03080c01400b1520792166940e210a401d07030030000030460b801044e1401341e40c0394211140e110521110340345e088032956080c00064001c0b9040200152400c0007003101c0d07a016120301d5040d030f4208d68410b201c111503201081d1a006440e05002c0d005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 484864730 1250 484863480 484863493
    0x120a030c0302150a0507170709050609150c0c090f040f0b061c150e03040e06190b0703120b0915010e01020f120301030506060306071710170709051602 66
    0x4a8000c108858259000b801940d410944101d0206001603049407410241039a5206109005034411b180305503218560810035840d003001200604511014425580302d4a030000b41c0f0301242d214015490030300c40d10741040079142d01c1d414245d9901e9a0280807041d015000d01d60001e0444110034000c1d90241d90401e10194000303109841301a0080c2c1c0c01032055030030084100c11111140864001a40414020a00b900e11103126920341d509682c48208050019802807000340040103441c04942d410031421150601c02d05040494007909003480d500641111350301140f40303424540c1201c5040780824200e40c0410904c0411801c1040390301d0180c5602d2205003010413118040e500461002e80001014012142aa07498910341c40c50880c40c0720100b68103c1c004001002084420030845420410440c0030709241d142250000b03002d113440400954851044401140380118040c83c010013502864011812811130740c204256641300034495207007080e1810000503aaa6100324000e00c48003280e40c0900319 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 484865980 1250 484864730 484864733
    0xf0c03050405040f060302030303040f03020d0c0209060f04060b03090a03090608070e01030b04020f0a120b04050f1902040e041410060f0b0d06050909070905060303040e0703020c0106030c08010e0c120a 88
    0x920020040e00c51307043d51141c02101582c0e08102075480b41c1d00c01c00650380031400c1880e009003001c1c0c04500400901c80000107400040c2d030f90595a03a4001000d50b00411074580d060002000b03440d103940820b40c032000000c2802400306000c9801c4080074041c0c0c48201e41c0720b91f10300084486c01ca00302c40748000507942d40c204c82d80640c80b039040103003900002840036003020b6466841040303a5110301060008200011042100041c0d140151011500304a804102500d403050b004800c01c40300418910204000843c14000700007554141e038080c01c030003041242ca6151034a0422442c41c3d0345901019548914a5051010042405010141c80307144a0280701107140c18498407658111201a24040b5207413100821191903644d4003c0c480d880c21001402050719290480c01169000350846010780c10070441480a0707441c1c40c4041d0307000030551600517943d0b0003100d5484e0042c1a56080209000401c0d103002402d0b2105411610f45840d0031030550754210079903010814200d0180300b0f041c2190f0811403d090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 484867230 1250 484865980 484865989
    0x12090a030206062713170d0513020a21050105010e0103051b06190309020904060912030605210a0c06030c09090b100804020d15090c0503010b0a051c1b060f0c03050405 73
    0x1178000300c1240d600008031450341d40740c0080484041340301c070811002144105000800b40941070b0030090b907080190801480750007180c54903145018841700d4814003100049540c1412010004194000c0001c1041d5611800c4004080d1400e1100384c07a03d100e1200c4200c0c041406125056a00b071000700954901100704031004412000255007009241d80c0d40b1405016032039901c0c150b0310035440b800c0001408084c1d45058651080c40e4182d61042525109062149440342540660072080f40c19901540c500049211032500403800703401060684181b000040c505d41541240c0121800c0791501c0498540f0781c1c000000320b803001b0310042d40c81689501002c0489008804894000d400507040c00021301c810744981c01c04c000305240d192036a40d42d41900d54180407e0301446c0028103001c400a1090011020000303002c26081c6c040c5a1041043e0795140746042020305040c3c1c54140e0198640180004000301e100c0c1c010180c0c03040d0408100e80030070165000b1b11850350060302a80c0740c1c60315030500c1e06010600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 484868480 1250 484867230 484867309
    0x1106041104062135090406081504120c021c0503160c050f01090e1b0c1209030105060636040207060f29010507020612090a03020606 58
    0x3290070076500c28000c2403150b12403c04400a480c0f014041082c051240f0f4528a04036480d16048541104006808500500700c0811508034022000c050788803034280d00020010142030f402a00c49105103100380041b01e00c410462449640118480820225603a070142c52014054100942c0580321400e50f82600207082ca80000150003601140e082c00045007014101a601c000192103080440d0000c021919158800c0c1001c2d000031300e03150000a2404081900d50040a00810640341429480e9000703d42c3c844251004034031200119150511004940000e56010000380d5010307508001c00a0031500345142111064084109012100c072004119140e0b4407200009440c2d9500d651300c20700c0d020b691280007406501c1c2c0922400039a4004030b0f90100200c6420417601007500385c0c00e0f00780032511030383c00707800400c841d4080c24201d03076404142c03001418074810030110318422104c07107007403103d06003001600e009911310035021100c0c00d495110801c18980f41818105162a1010310710718410340c20110071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 484869730 1250 484868480 484868513
    0x3030314010f050f043308010623060703020c04020406090305060a060e0c0309014101030507090c020307021207080607030b06070210050c0a030f020106120507060c0c0906030819110604 81
    0x1b64101d280641c03180030480c030b00714000c840d040f16040c0c0040c88108000e01c102d41c020a104200d02400306a900111102c8111006045104030404143c1c030042c14003c2c00050701c0802c0081c000c642d0f95031281005001c071080b0340816545d81c811000000c1d40040144140002d0710441802c018082d503c0a030240301e10381c002000007413155291815000400c0380030f1165500801c5d000c100300c0003441014480c244401020310b040785443c02a00c0100085140403a10300e040e1450f5000108002c401e1034016859842916802900300c1a07046000c03200d490007048100a85071381e101600c1030ba0b05e41c51006c4081e03400c00d00656a121108101140051030a903030b003600c0070b0700c1d0b50906034207004030189014148941100c00f0340128803102e0f03602e41c03500da0a11840700a40b800203440c11003103106482e6113035205a10301034013051100d08141d442c188104c0d50307400d0700140781c0c040050000350303140d2a020607680c0101c1207400c41059803081020000c1e00881076036100610b404000c01040d46c0315124544488149081c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 484870980 1250 484869730 484869761
    0xd2f03011a1b0601080616020a2a0e011509080307080316091809021f0507060f0b031002180a0b0a030b011e08180106060503180c0a03030314010f050f04 67
    0x310b0344001c0800380078480c000c20411006c3e000c0c2d0314000044411610300b000c00e450840d006104c0000c0014410818028050040125511009079a481d0017110203600c2e08504001a038aa00005400202d1a69007428181590300c04002a0303031201c0156403801500c100030030030b0005100180c1441c105800581e030782e400354542001c07455510071910b4042c0e003480407451000c03500d80c07000c80254104090820804091940c5040042c03104102c020710300c0c0074a40d4001c0540d52102128142d06109400c606403101000b03042d03402c80c00c80d4405810083d88000745401c986070018120303d1452800c10a07000440740700b40c1c001854151003600c01c800401c1c01810450622180b100c880e0380808041017400c0b4980e0309178851074864148458603142c0d219161900340b00c0e80e8180a170070312286500405882e0024500004c141c14100072111031b500381000d01c2070841d08584210400010705501d900301a544c000d90085a602590300c441c00c00d8040d00241c001c480d08004c001c000c007030950400c1d40c01911105400710 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 484872230 1250 484870980 484871017
    0x807090e070e04031701060203030c0f0c070519090f0c0f03020705070918021e0d1211011109041b0206060d030e030d030903110312040201050d020d2f03011a 69
    0x2c0454800700c2c20384094000840d14090a40d8101c5003801e9503014200c240011800c500e440c401c48040b40c8912008650071400101e400000c005013007188a000d020001c0a40d81480c8414001c07511884180c41102541401c014850441c07615038852800500c1d100d540701c0c00c42000d202d070160042d43c001d800427102172041040002c2c2281045c0b29941c611181260026452a1980100000d0000c0c04e00a0003007414083c0c1c3c2c3c19420790f80c1c50441c484107680400520a0031280c501e0507102100440d02440c1e0650070001c404864880e01c00081c42c100b003007181c003041180c4100600002c21501507040c0340c0035030b0000c0003282c0286054240035000030701c43d203482a4494820400b20742030080302016400480d1f120f40b903100401d5048610300a11400d000c005500304445404110540030001e413010b0306214000a9175016091550100c4811400c800011b100b000e00da281080003007601c2822070014041c05126001d2039210001c2160704803625000e0b100c0c0c0806601c4a049225840031800c0717803140f026007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 484873480 1250 484872230 484872239
    0x1c0f031a09041b08010209030d0212031b1204080904060602031c0513050316330209040207060527030c070902180901060203131406030f07360b040807090e07 69
    0x150802d20103070403440001b503100c00003d01410b01c1c00c0c05054048080d500702040c02c0442d440c1c650150f9901c40a06044080201d102080c2c0c00081d1044a10007410100b042d82003009001c503074002021024000d680400c9625525142241c9a0043c441200240d02e0b00b50310504100c84650803542e00000003061000d1000055030301d851443d440718000312404603001400200f03101c0305070b40c0c42d401003044c01809141059400b450022103900740618100869003c18000010b80b030b02c0c0e05032084590f0040003041581040540303009a0a1340c6405d019040001031002582041c012003510000c4840800074002e0702e00f4054100044d41180545201b495924401d641e01580c85484880c000c00b8681c000c0c40e07580e080c0c40300f0380320110442c1d0020180000118904603890301d030501183e41c043c030418019101ca80f56688100e400b60150030031170750b402c20740140603044442035050380c0c2079942816541c0402e541d9a141c05060300d01881c4200d1200c0d4001c00340030800301c11070750004612000400b01350341495844 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 484874730 1250 484873480 484873523
    0x7030e0d02010e0c150d0905030d0f0e2b14070209010312030c050406051c0f1a120a050a03140c030406030902240a030f0e1c0f031a0904 60
    0xc1810040041c1c3d1965810f0341c84403070911200d000c06005882c000d840014200300081c0512034004081101e69503881c0711418850b050054901c1070317110020500ca41c00381c03100c408001c4c000702d81650300c45005c0c214001441240c050224048900d25032010180c40341990703400d6407842003103400c0c240c4000b030405c0b0450040c1d85001585010b503118200401203031000d014000d04079941c0000031014041c0030441400002d41002c1601c03403101c400f00d044051a00848440805469080d0039014442c0c200314420340304280c1081d034de2500c41c205698981c0500412000940d40d043d00c220098543c0d0040024030000c40d100d0124540310310003c1d240703985000600c0b0700c41450345e8429800440041e546414280440c03030080f100521580341801c4401d05444584119800c2e8810700300440300381039862301000f0802c0019044036004508040546070000c11680e00451a9004421404002011008000c40142c001d2081c68082c1d00003100f0b004c2100c10070b100381300e60540050000d03104064221282080c9d90752 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 484875980 1250 484874730 484874743
    0x90e071503050702060c03270f070303030e010c08010b03010e1e0f04031b0b0c0a020f10021201080f100b0402090306070e0102060c0414060702010c08071a0c0906030a0507030e 77
    0x400d40da0010309840d00c008024200b00e005440500000b004005024100303004522000d0b9a80c00a0705030103007150f1491420345010740c1c1c0600032005000b034000003c2030580550061354010302040092050000050040b200d00d01c0901459200b0001440103200316827040d400f103680100c2500002d44182e446a8000d0320b003450480d000c0300c07500303002c00400023010b90014035400c20301c0e03281d82c3c40e403d416010351314610100802841008075800102c0c083e07030601d1080040740c0e1402407220643d00c2c0304240c1d0076445d0181d84000c9040300651008070001a503010006210400c0c03c038040702521112141d081c60501600300e100301c1c039600035001c1c840382441d80e50a1015a000308100e0308c0d5041405448000a420480010011185180705000400c84c800c3d032202d1003020b4200485146649243c58401a07417a400c2580002d01031480209800080020354076051240104451001105580b003001d0080c0c584510101c203a001101403012500180241e00203640140c00c50030045034211070b1a030100e24100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 484877230 1250 484875980 484876019
    0x1e060b040b22141305070f0e0109051e040b010c051902040b040204330e062a0303191116060e0102190806040501050d14160609031506060801090e07 65
    0x1040b0002c500511302d084541d2207042d035031243c0240060b241c08070300642004800ba5070542030280160b002c00c0c59030701c603c0b17516000e03040062840c040c0b00d88a000404040d040030b9403444c080c6250030014400ea6000344280320040313501900606c0c4403a8801c840969242c1a0401242c0040d16110908603c0c0d80340c2c0054405000003003442c0168610310544404054100004180c01c85404420741d50f10b180e001c161060a41c000b5903120740c0d0741c04003902c1c41e50b03000d900307a4a190b50081a00280d901c075201c044011805602950b42508050540113a500c080300c40c0021110703007011042000c20b8804401c0c0c0c000c1080d041c0100e10005a100e010100c0f1400d9030320000c00103802c000181da03644507060700825020340000c1c0655041000398146000304120300c18040340030700140c1200e1200e0003800000c10000c03070107500f20301d034905650341e58590150481503d40000c4507a501030400c482d10f541c04074031030407017150300603920f9004030f03440c0800720401095440100369441c040c54501141d620031014500c0c8590 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 484878480 1250 484877230 484877249
    0xa0f1a300304090902180432070321050a0509010809100504030909140f0a020f1b2109030c0f030a0614040c050d120e1f031e060b040b22 60
    0x3c0700d5510402000f10700721b0030142c0e8024031840600003c10801c4412100e41e0314601181a105500b00013144180b500c1190500441d2084020200402c00d121103c1c0d0314145804104401100400b6020348032401400000d100040c01484014a00e40c410190160452100340c10780b000c0d0780040e07000c3c0c01506c500b102c0c1600818490f81d400c003d03080311303840340340035290001d5030362005406c004060100100002c0c1070203c581e0340104010141d1081d0504884a140c1210107100881d0301c800704090b10303110007800610743d18420328944103c080050040314403410000303000d402c404090b101003101c2078510807206a05481101011030000b180c1c1c0c460074000c003204010032041740c80c1c0792034102d032088056081140500581d403d003500244409c000e00a640d417440c01e28040c140081d0000c01c071540109060780b07251034242c0042541003a00340e8031650040c10101811541c42c00c00c500003074103071078540c820b0007554034080108201240c0000302503e44409144d140c08000010444c1c420340011407608800b240c1e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 484879730 1250 484878480 484878491
    0x110409050a1a040e10053403140f1f08070609030c050f0901090f09080a0c0201080901110405010c11040912020c010f1407050f01050a0f1a30030409 65
    0x1509000c181c50b000d0001c2260f007442010103c0b136090340c5030368905520628641e02c440202d03032190b0f80301c8511504021f450621801e10080389912020000e024184c0c2c0c0c022030320340404a040342883e4441c50f4842e60141c801d0858a88442e0803008005444900d0f50f2548203542c60013141800007402450010200b964030072030803500b58100128076184a0b40050b20914030212440c0704c1d51908506d06d8115000b01d2070003d40e5050840c8450050010000e0080c00c8820026a0452a50300082d0b801c0300c0d14000e03a140504d40da982e101160880d58400d040c05c02c0030000f480100559845120238890b8284a000c102020103108030119042e1046140b08588009003008041080c0ba41082908000c14092900000891980e08054000240202121901000020790700701f44841000010b01d0501c10340020071542c41c1030101d1900a0500d40c111140b2141400902c0c004c9850303404080720a070780300419003400c5001d2003a02a8000c0c82e400d0900140c5941c610b0442c0c007008003400508014842135070040742 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 484880980 1250 484879730 484879751
    0xb03130b0a0e060c07030912030207090c2f120c070509160f03060509010918051b1c020907050304290709330c0f080a200d03110409050a 60
    0x14400d005189044e1280c0a100c00c00c003199011f49004100c5a060442c52542d803003a0a007213003000700a030030a0001c0b50074a1400c3d8008c0d5423040c00151000d121002c002e101502d44424081e44c1c160956020320203a1042c1e20283c8812800d41c02031007600355035001c5400c455624404102212421200d41c840380040301856440701c3d801038950343c50000c20303107401c005a5042200013000d0004c18003c42e80700c5680d40c802c007209200071201007200d0a800c80100e5900510300351340f0b03200d8000c8280415000303240a000c0d00710000b01024903044041d134010090040c0d40d89400040300c15410040040d180342c0000d98901c259048200194020555215040650391604070f01c054490811540040407020544501031424078800c3d0340302d11800c0c4803040c0803402c107840d1072044074840b007941360261034001d00e50340b44020400c20a00405034410a070301d0740b44400c0c3c40c4940c0b65009001500c1601d06980100483d07039100391180c0d000e00941c100403020706040c541c54440100c1103903022039030f40318160358501c1c1550 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 484882230 1250 484880980 484880983
    0x2209020d0b0904031718011503020a1d04060203090307080d09060513050d03050415060f140315130515090a0201031104081b1f051206090606040b03130b0a0e 69
    0x1c1d903805080c0d9200c4040e040c5568001d10400280320046003549002001c940081d10301110080c42c10f0b03082d0020b00c524030f05406044109a000e100c100e00c12030007000001645102800c00e4580c02d031204000040554503600c906000c0d5000814980160104000c00e6001450314000780000c003d80d42d0001031486010301d48601280c502030040c5031401c0e82c4c1120040003460005604203080c0c410324001c126500ca61030140c60094000840880c51803c0101c0443d01e103c9000300074040b56958040c0c185e82d2200142816290840f00074071910100200c03000800c80c4582c3c01210185911581c100c584080d98200ba8114889050700c40c19803503000000701c0000d541c0c1c5409420b20140001000394070301841e02c0c4000e50345d018540160841041c0303912076280f50343c1da51203165041c5180b101000482c4c200f41c51000f011a4440701e5200d20020b026400300725581003010ba418450300018007050724140c02c114a021103504010030302c071348110448005a0014891520543c02950000c4001c0f8000704051a0340303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 484883480 1250 484882230 484882241
    0xc03060f0203040f060c1709030c06010b0313021c05060703060512060c091c0c030606060f0302040b040608060301180516080c1f110114150d1104022209020d 69
    0x401403540140700b8800483c00c003071105034000d40e02600004924140d0741c81920707104c000100500b034a42d016400c12001034000300061000030031100603a00301c4e83c2c0300c40c0350325114041030703551320803c0b212400e00034018202104c16040c00406040c000382c44085a60702c092404100325183c90000f501c443d010826405d01c4c0c0020b400c1c8070f00e0240503203800d04d0300c2c051346c100501480c42c1552281c41d450002c40700009c0150101044650462a08108940c803803c200000e02864456100000c41518000341c019100e813090b030f03003a40c10a00b03005103007034035001044452810140402c0d525560340d40c1c3c15071140e40c151003600340c03c034803c00252420640351080d009014812317038054682900300701412980f0317641380600d130403882d080c8044107a00700d0580e0303108940c50318000041810365881c18032842c110301e0036200007910071010140d4610400e540e043c1480034050740107000401c0c2d510280200040c5150a801411040034904044c15001c000d1420802403440302d80c1c000390b05584d000490408000c103074082c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 484884730 1250 484883480 484883501
    0x150509060c06070f090e04020f010e0a050604090213060908030307030504060f0c02070801051e010b03040c030807081e0703020604060b040e0706050301051009080601090917120f070f0f08040c120c0306 88
    0xb000402d1909030007041009c0c644400e800e0404c00100086025652000408400f030030b07000d0103003500d4079280c0130400002d50100402c1c2126000d501c00001d0560f01c0f482c24101540c0500002d1030030341d2110002030740548000351040303da0503140d9400001412951143c28544207a80d402000c52038903241c901821150f000e060b0240200702003c01c0342403104c5150082d411075410303040842e40c81c0e03214140480c2404442d040100300640000d500b2040c031200c00064000103024103080080700c0011001c81c1003c0c0716929005025030403000004000c910194802103040101910128a6050b10071000f030820026421603008038801100500041c00c144070142000340c00350030803180b00d80c14500021740d20001440f60070742c0ba64942c000c9504002010b1481e0556080903194280c8680b428058451444000c660f00401118410b001482c9148105104110101151600505810100011500358000034801c0d180301020360000200b201498402c2000180581c003907500300c50641c54007405a4a91049 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 484885980 1250 484884730 484884749
    0x4090819031803081f050a0308071109010b0706060f14100216091d3403020d200301090b060d0819030506030f0106050105091e0904030e03010b0307150509060c06070f09 74
    0x85c005031f219020100b0640341c01c1804070343c070743c0b10230710b0001d0070030094044040d00300c0d80c6440001008201203000d40f130200c0c401d00050094a40b12004140c8140240c40742e000c0d00c840f0301e59100c8503400c1620001c418007200d44192500880d070800340100c5907255a01a90480e60364080250002d005103d0804a2000a102a002c0040e00c507400d075940704100e801640340821071514000912080d82451001103030701512181c842d101c40c2c1005120050b0301d4040910304082901c520200b4541072183c00d07a41c6030f00800e088030544503803003400782d182914402103078a500d041182030190040161658000903a41da004503031031400380e040c5404d1030f0740540d41170388588c141101804141c1e003240507240e4021096070741004845100d1140800444402c41c05608402d800c8284010315500c4452902030303035400c0c2c000340300340e075900d0040c90303a1003a10348a1030560300010794060340054480c0b4000c00c180180103080504000030840c10034204081519140b02160300503d0300d0310401e8100c5182402414400c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 484887230 1250 484885980 484886041
    0x306032a1e03012316050c0f0a0b0114010c060b030307051c03060f0807180209040f0e0c06160b07051225081e090316030309060b0409081903180308 65
    0x180072444c801a000d0f07140d80143c602540c60b00e9104a0585010100d1401201c8442560b80065902c4000307018050f5151030f8104001314a4243d044540c2802c0481030f542e5500014040d01c0b02001001c3c000307070466041c00100505030114004000c1d034000380b200552046043c1201d0f2a02178110362081e402241c41d11315801041040c080003041031801c43c0c12600b44072107440d041c8100c51000707126100b41164000e240c09481004204194024a00c202d81007044403816144041004018051500d01900c030345116500320000a01c204400c541012150900505121144880302c440304812141c1191800e01501030301002440c030038003040f40140d01d00301480b041c20510f0b4801106842040301c4048400d6200100d000385100b0011941aa2007a01141c481c844162500601420542400303440203820000c0f100c1d01303441c2c54814070349c0c8180d010800c070f49040900507100090f084403000d41d00900d035446980c180801e2581124903441c1c0d00c40d98460642d842d041c0030240d1b0107d00900714580004001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 484888480 1250 484887230 484887281
    0x1409011d0d1101061a031023240c0a050d050f0322080c0f121312031101020d050403020d08010302090112240905120306032a1e0301 58
    0x1044000c1401001c0c90a60301c10600d00280c80d0142c8545d07440030007203950101700010110328000c040e60155403d144220b8000355039220480010100401c400d00700030290100d550b86213403850306000d004040c0062407041d1590403110810756003001c1c4548070184c014004c1442081000d000f048a850f545003040d41c00c0010080045070a40001005850115240004805018541d60b05038030069031103503041d580c4600a135900f07034844080203486140341c4200d02c45009116103075000e449400c05d421400b49042c510742450380244103803c450540902005500300e60b4061001e000512143c1282c000118203030070319182c021f18221115a6900070044071000500c0103a179060200741c11610340140703004c2c1c015180c0c2024600e62049a144001d10f03140c001c10715081d441280c01c0900c0c11409601a2081e10944e9154000740c1d00c4120b0380c0079410741003512038002c0500e59102c10444165103800c1800144c4450000c01d45060151480e814a50900088541c0525090051040000c0841680d07105007106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 484889730 1250 484888480 484888483
    0x302190f020609010c020907050408330c0f07050601050126070e010e030106090e0601050603100510050c01090501060314010903050702040903020c030a12021204050303030a0f06091409011d 83
    0x10080c810080012540f250741e21604107680440d800810700070440c20090310141a990285c0301e03c0c00d00340912419445012400c114660b030465603030028030085407041c600c00440c079000078003400755850140300e1110542044c0d4003805105124400510007541010009000c141e040200d00491000308d06040401da5640c0100c2c540003952424100b40508402006035000c1c3c0d04c9004442d0198606000000c4040c4240c00c11024648040248e51003a62210240102c42c4811900035641c000c14401c108000d040c1003a40b00450707480c510b05076041c0705000304524250b407140c00d01034516070345030081030040c08130724882055108a100000c01005100f42d40c05000c5000c0c14101910a41da5030031a0030626000340201a4100b50040550709880c1c2a403070a080e0040c01c10a6540041c03080d15011640010090103c4043e2040240110300b9581c039880084003400c0c1e03030034819240b01e0301c40700002195000342c001d10760501c0c240504610540340200f1002d0031180c20064000004446075200c0864010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 484890980 1250 484889730 484889753
    0x609061d030c040509070b0f181503070c0219080102090906011e0509060712020609060705030114190b1306030b0d0b06011101140a0b1207050a260a03020a030219 71
    0x2d030f0b004039480d0386080e919401c0544550044c41d1084c4000f449668212150300145141d900030101e0306403194003201440f851404107200396400c023904101007031840d07005202201a0300d1004146100900c03680380d0b10a400160359004802d20b82d0085a035640d04c1c07811108503548000d0030300c0d10301040c101c61407520113155885143c1509100c2c000405021a84814040b00c6001d6003282000803210303804100259107480858000f1103500402d030200d07105910840440381290740341810400926150001c0007803002c0852002d40740e20700078000008a603604076026045810204000f04405d03071070814064190b658500308184a401c10014101c00110440740c0a504070b04d081c03034004000b07200035544a0042c00c40200c0001d54000050400c882071105810a0f00e40c088140c4403003480410482e00780d65600c0c2c0034005c0b41c3e404140c000d01800380d50000300c6454102d92452200400341c6211800d904d0511003600b0050f0010380290001c1c500785501007101c082421944c058103100520750341c940d81e03400344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 484892086 1106 484890980 484891003
    0x60a1104172104080307060209120a050d090501111c020a06020304060906060b1606020307021504080c061b0f07140607030e0d17060906190609061d03 66
    0xb0104192411140d008004605007611a03403005c003c0c6d0880394030b10f038101820380b0a40c0d000c0c003410420140007a0203100509884c1245000083c8800030350b400075418000013481c00b500c81a000542c00d046003880140b81c1e4000707001d4090403401c09203c0040035201c680040180b1042c007860f07034000303c4114462641000103a6843ca2050001c2c001d60100450701d030b00c4504c00001190031034000755401a0281705442d2911032001340c02403000002d96042d039484002184152801321704100454000080d04d080844807100d0079059901c0307215090f80c5001c13111b0b02080b02c81c1040f085a071400f80c850703010801c1e10328a1420200050042c0980c00719040c0a00c109000401800d004101c825400c0d942078511900658032202482068000605500d800202200c14062000048014280500702c2c5584582c0346625100700280066101c0e140e800c0c40500c029044007255400181062010 = true := by decide +kernel

theorem cover : BRFrame.Cov 484712230 484892086 := by
  have h0 := BRFrame.cov_init 484712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 484712230 ≤ n) (h2 : n < 484892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
