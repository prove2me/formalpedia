-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4904
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:06:42.671884+00:00
-- url     : https://prove2.me/submissions/1a0717bb-496b-4387-8281-fd19c45c9cf9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 881834532 ≤ n < 882014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 881835782 1250 881834532 881834537
    0x2030702010b150a11120c0307030207061707080603030d09050d18080c0d020d052b02010203071e1719150f18060e070e010305070f050f0310150c03 65
    0x110340302c2c5410300c001c0300d9208400802000e0b24003641148100d4502400c001c000c0880d00804614108400060f4050401002904041e581d02c1c1401d180c0a07292003a0b65010000340105075800c0b1300c1786080d00d001d480c0e1041c001c2c14080c01595548000038210b20a240203403140398a00f81407502844030000364056103019035254000018022010020780e403240e441044034a50025410b0369103420080c200c400d82503c05020118900c0440d81c6082c1001444850034150802e01d040c0c0094080d07106650700c83c0350403c3d000852941c142140c000309a4680c10300106012540316202c0d2204601c5012883c0101c90380c1000083c40f0b0a080680c00220b1a8418049482c0d900700001052030155141c000c40c219000c3c002c060000c7d0f071a240016040030722000865415543c0c804000a0041528031010321031903940da50079102c04602030003d011102e000e81303900100240c03032410030413241c1c102084428020414100c81e0301d903640c030560200d800c0f60030b4200044800351404445100c6411000100c3c19034401c0c6c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 881837032 1250 881835782 881835791
    0x201050601020f10020c0a020d21030e031b0f0a0c0e010e091c03060504020c01050f0a02090307061206051909050f0f071107091109040513050309091003150203070201 73
    0x401207aa40441e1200e40381c03c2d400000e07806403914041d5000345000c0c1e205005640881c0d100c0c5d00002c22450070404151245244550700c18041c1c80402e0340c041c820422030404002d400031264051342d8901880307021001d40000a202100c4003d004c002d040e008005400484e0007440007881c0c903141075002031184003100624440081030200c074407140c50f40710300b6440009141e44c140300c6040c00410384e11001c4683c02e0650b928404a21074070750f070000b869640c1103500040740c14100300083d01440e1900812a140552050000014590340030a040040343d610303140180100c00c40c411001300400265201990102150f40b4143d00c2d038505500d104200c407000c01d410015070766010084000b080c002c40714502c50403111800220001d0083c401541c0036900c4808642c042034440300e000c02203d524080100d40031901003043e00035464203000305a07200c481102c00302410030a6540300356a80c010659814840c04261000500345520b100190b002181c2060640c922420070b00610b030000e40c42039844000650030f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 881838282 1250 881837032 881837041
    0x2160b091206070f0f09050303031806090d0e060d0b0a0608160c0203070303080415060f05040e030408070302061c110a080609070903060c030e0703051c0c110f0619080601020105 78
    0x1040441c071420341901e4078070300113203002021115034464402d09410300503481804a030648081001e035210749003005803808000e04000324640341000050074100c00340d000000d0701c17112544c0141504984903003540ea040e00d640c0c050300e050b005084000c1c83c590300502601c070001021903124207000d01030900c02a807403054018482c0200c0d00001140c10194140c0d018001c00c00020380314038803040e032140c010250058154031180070b840c1503815030750040c8002041160140324170710707091003141c27283c4d00034000a600c1c0510302111345444104500c40030b0b106e0b24005c40c22102c000349050554800075820341e001c2050034030401c4840e00c02c2c0c1004c1a940c00041d00e541c0060a141071582c0890300030441034840400c46455540c0e00009400c0d010b410b5401c15413541c1d02082005420407104018610803005849040d140108500c502500d082c4540304004901c1c11240c0401e0008450480c040801d4074240c4c420900e800201e2214400d503070041d00e0b00d0400c50240600340e5840340c5550300400c002d90091180d0b854 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 881839532 1250 881838282 881838319
    0x50601080f010b0f031321120c1704110a06020d0905060a390f021306051e01020102120a090606050901061b0f08030f160804081902160b09 61
    0xd0003420103003201000f1040104851030045c2d50700480b03100d5040082941c42d580c0c16112600100c086d00008940f00e6404906900144a0480304080350400c0050a00200000b400217030146500002450b500d40410288607070b800f007034100907401a04003107245030303903030b5000f595600400d1081c400107a041c070000c0340d40d1034400c0031a600e03180d80e5a22005014ac1d001c1d181400203402154032034503010b0240b0420040027015071031960b41402000484413586090043c441411401d80a05809500c1c3c054240001d41d03413200326070072601c3c0103000e0680707561203400181d0081c0708641641507001100010010f180d000c54102246041c8116420b2040c185d070340050080040b002e014136000b18040c1503003a03911071001e40c602c03101780740a210389003280042a21141d000e40c1c4107552882000d000e1300104424400c16503102d681e00b8102d031800e601a464140c4540300360340151401c00083d12246501c0d08805482082401c070221001d203540ba40582d680c20701c001d85688521030050059030180703c110305031403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 881840782 1250 881839532 881839561
    0x309040c12061a0d020313060e010606020609010e0604080d06090219020d020d141e0301090b1801080c130b1306050a0518130201110607023a0509041e05060108 70
    0x208020042814800d24410075006904001e1190000460601f02c280205003280126070700382d08100c000088280c1042c00c02414088014041032040e1f041c80c909440c407641c006155540b20b0b4001c0c810302d44588520f500b04010744035643c8844200c03800800e141503190103003015101070161540071545e904000d034409a8032181c082140301c010494029918100064000041c0700110307284104402000800c1c1100145030002e03000fa6070019500c03862a045421700050340c20814400000c400002e41c50884260b03520f8410b5491240140c0400c00030160000d5035810071301501d44000d01c0f00300420203120300342c4010300c0305100740307441040700450009950601507900701011100340009901aa20211050001e5854a400303d0400c051111003000c03038841031044a000e5042a4042e1410020920b1900310503003010010711146080b0401c1813418020b05000580c420700103042443c5c1386e01c144070016006100011001c542000c894883d0144c0499980c81640310301001d80304e00886450341c0a0f001d0051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 881842032 1250 881840782 881840819
    0x110f010c0f051c08191104050406031203061d0a0b01110f1f0b090c1e1201140901050607020d0318030309080f24040203010b0a0b1308061e090309040c1206 68
    0x8004610840b104894101c0e0740c182d962003551607e05566a000710302254520352066420701d0300048962034099141c052403000703000485403600c018200410481c82d40402030b02c50165643e032406207900c84e03400f42011340500e083c04415030744c1100ca03001d5030039120400070910034414040500c815500d4403881c446d4102c40700d0040d1601085a0758a91000c901d98080c0e0b01030300f00e000f40d825004c80d0320400c600007015441900c40c9030408a51505400036141c40461200920807180d41c0018459500c8800036281950740455401c10404110300741640d000c80542140b003514410352001106040c0c10444090880f840b4004541d541703200089d4441c2c480301145079000c9560380c40003801d0752081c0001015600301d40001c00000309260074100045248150f03902c1040d40a2001c1115646041181e100c00c0082902030042c1506241c0a40c1da42da00002210348003108403045070109116280c100282d030a1510007900c20005040404e0380580351800c2101003412003410600c0100724900c1502e40325012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 881843282 1250 881842032 881842051
    0x60316030c1b141006080307030e03010501140423150109050a080606060c160f05010e04140c0c0a17030f01060c0804060f230c0c010903110f010c0f051c08 68
    0x10801ca90fa140c010082d100b20008080d48108148071030503950a1140900820036280190f5a903821441d0160450400c81d00c02c1c3c0c4a40d25060040000300e80c0c014040d800c4100c12070300001ea5096119200c1140b850445640845424400c02c00103810300c807440580c2000000d8881407100c556580c200243c10243d40902e803115003018000c00c000d0300305403010b040203810325415101c4150030184a6050900991320200303031410400810005942c10201b1480074502c10b5400340b2066500c054124141c0d00b010b0b04c600c040c0350001a8401034003009028000556074811400013000c4107201c2c846c00c6d90f4006495404003098494000a00c0e01d020b00011511305501000440c142482c01c402a00c2c100c2c860800e1105003d0080544003507002030b02c1140e1000c01c40e0400c40c585031078421000606d060202c0541c0c030305010101ca03060010801f8410ba582c094001281ca0441d0305090710300498071006000001407400d0080d100340800c0103004121074610380f2a003514004035054154048408030001c1c0d5200341c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 881844532 1250 881843282 881843327
    0x14041103041101030c0219030f080c0309060105010e01110106260a120305100302120a0501050105060708040e100e01030f020915010e12030f040801060f0f0605030c090f060316030c 79
    0x1000c0d40640c00031000f2480711b005550001403402201c1c1422080c2e00d000320300140e4905000c0d60225001850280c202c440f040316a4150716180c1030302c503501c450600986051000c0e00240d8403090313104400041440041900074001715039a01c0000021102035440310115101001042030008000501a090036400800a28010303400d40c00c10b600400002d0302d00141101c1047c0040050b17110001440200d058140c0180207041c0306051803400c5401c103820a44c4100300030000304001c1074180b016070701a01e00c03484c0c000c2183d40741d407030a03400c01980a51040321a048004000428005040c444035a0720317000760703040c09050b902d040740124a203083d500240e000c111011401d80b1036003021001080301403121001c681c5045403d08440940b03030001e03440300c0a5070b07440c2c183c01d02082158184c160020551007152810107424090003230145d00000785486032001c0042280345d81580d403c05c96900c4600e02a00c4a0364a0a21503490040e10784911002004242130800c01da1039240f00791461810400384691406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 881845782 1250 881844532 881844563
    0x2d0a050409051003020d0803060a0503070b0d020d0b03060403022506050d0b1503090f1908040e090c150c0114100b0702040228090608070215070c06061404110304 71
    0xc0104400f4043c1c05850f050160040010b03200d02a032041c07094062401c40761130703150800c104801c030312035a04194000d40020f9002c0185228503002d4805148071840c4c09078458500740c0c0300d04010003554020962501c900c0c0b05001c103143d00030511105081401c40910b080d120200380b4005240c89902c1202e00040381040b103074650700318030352142c8101c0c817000303141121041403404034425541050365542032a8001c44203400c50300004004100422454215481c80e01c10140c4484419004074410004000e10540c0011035005040c012810f54240007002d0065071098010004d42e150010b03074200915620b032141d02850f164800464512400707043c854044050304004180c18207800600c0c0072604117800307102000103007400c00c1b2000d014104580c0d007040741c09141e020081020600381d01203c1403203840400d002020364045806500000346031010040c0b80c841060407030f5400300000c000780055281103c0821010b103000788094030350404603014481c51450010752300b660321054a004001304010203030034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 881847032 1250 881845782 881845799
    0x20607050c151008010e0a020f010813150516031a13060b0c06151807140405060705071509230109030c080a021809190213022d0a0504 59
    0x100154581c010903a82e119011201001c1d01c15429030301c0406508a0070001d2044140920542c058003102d00010800345100da004140c0c0c5150b035504180c10405581c00040390710385000328031032005034469960001d280410407160010001030303401e0100130078041c0b0341c0140144030340100a44a81a1400b40700e070380301c910003000a0080083c0d5a051455114840040c6025092000c0c0c0b81c0842c03440094941c3c8d15100c8102c06402140d00c03003d5108200745410304030180c804100540d805030b00d504211b01d1000b000c0f0859607940c0078503407000c0c0d030050002540d0780400c00e011400b20122140048000100420000c003503030520081d005091280d030b00445401810040901400341103403060411100c001d1700d13500c030608030381140d1f0041082a400403244604605225003003421014290901801905080c50455255190015070078a030345200001c1e2000d55542a10f01d4446a581d0340046607941d00d400f4501c0c2c4403100104100e1090740d21b61400303540c1d00a0780d6040359103c040ca541c49a140c24105001c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 881848282 1250 881847032 881847037
    0x2071a180d2d140a0509041b050d0e01110f0a0e010224130c060c1106070807060e013209030403050c13020c060103030e09060f01121a15120a050702060705 68
    0x1202005500d50090325401d00050082480244980c2c2c5d4544e100e01e040284000d40d0385540d0484008401c42640c000d813190321405607188aa041c02010031406124041d0358003401c4a0800017010902c0003070324100c40e80701c41c4000c0120340d51686541e4010340c3c940c801640c5500004c030004202c984420721322140b001e440415964801c20031140003000f00300a07103800300c50020390b81000d00810034001c07810050181611182825000841e4510b01d05640750342d810b030503401a094010056a00c842d0341540154083d0044104021811400e9991760f0a18208a13120740d20801c001c141c2d190f80070045900f04201000311003c1ea6000740040140c0340e00070003800020010000c4400e00c90b40e00380680703003004600b0f1015600950280d03449602e0a143c41042040607040034080f00e10600c07040741c0c00c1415980005079a5204ac1c1880c100013290115082407000031401c00020b185d102e2000c10302441c2002d810b03c0a0103109030580718551140d1744180030f02040b65826105103025a100b88000340115118100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 881849532 1250 881848282 881848367
    0x304110307050f040c202b020c010c02010323150f0a290c010218010f020d1b0f0b0405010b06070b0c07170310180207020a0902071a180d 60
    0x4008004950200c43c48080f00100b01800c0032541000c019010740c080c5c030743c42d0440c070343e1f000345800159250120310103540c50419007559030600c0b5101e0300c02000c0d60300030740c0303e01c003039a00307120614410180c1340c01142a40b507000c46404824644598847c1000d041464210122000250008500b01d09014104001c0c0c2c891803d2144446850010000d901c0c0d140000703040d10320303000c600160b00c0e8418541135407075081076420014100701260203d00300d2a6800640b1012445480c246069002401d80d5a00d02c0034104904c050316101c41608501c042003040c49c80148124000c0008100c040701050030003019105440c0b021348040303a0940498148400c0c14010000369100e0300d00f1003210f444400e29084150030890700982c0404e0070b644100701e0b0700451101c0d803420805008045103861031590008841c441c640c06001b00707465021900100b00624101546081c04030311140300d1691402507841340500c1c503505c0c0d41e84214058040c400d0b100d907000300c5550032402c2c1e41009202d001c4400001112040403c1003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 881850782 1250 881849532 881849537
    0x6030b0f06040917070b060108062d0a060e040f090506041104390320090609030105091f050621070306180309080607021e0102040801060b0304110307050f040c 70
    0xf442900080c1c00c144a121000c0e610203a142e250412400d012409070700040c03600d810710840004101050b0756445c01001d144070380702d45080090809090b400780e11080e038092660030111446010810982040b100702d02180203d13014010940005411402c5c1c60080f80010000d80c03012010400144c3d40d03001071000300e138000c1c0c000921012800c402c900d40e50080e134038065440017880c440034003d00d4010303e00003800c46141824866000c01c0781c482500d04020740440351030000007040c80d40c01540c81000b100c10a480c020001c0c000d038207181402980700d0700c031700f05040c56080c1e0455070f05400d00301034000d5910900380103013602000803010031190240c00642c04034041d24000d007a4041b000810070701c0b50200710301400020840b403561a00e0b02500041054001d11025807000c0200418540d0018088c031401d50320030410304110360f41c0a0464060f0103542c1141401c0e50810354040354418403180610301c0340b8001c403011000417098a0503d0385800c040e0003013a80018003003100b400c00341003541000c45d0450303161 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 881852032 1250 881850782 881850791
    0x1090204120206070816060608061e0a0b01050d0504080919030b0f0a150902220f0308070507030b0c090f0f01021005091504080a1e02060a3b0706020106030b0f0604 72
    0x700c1c0d01d1500c0346c2d9604012100590303154001d10002c0000c202803548010041144150003810304514650a50020010214541c40c1c80304074025900c030300d0503a4005904280c003030003d030415141107046a0044400c484c0243c0581030081859100250ce50085070b411100c0102e0b5510741040c03800a030f20380146206081501c1307074040f00d000c080c00c5448400801c1041c800680340d110a02c400b910440a05036602c4580701c3c050000e001d48080d80c203a0504596120602540c2e034a41131030014103000841d4000b81c82c41d075400c02000700138451440100440c03d4110340100001c1454030800c51000203021034240164405045102c0490301035204613085207004003140c140520041d00d6503040380003102d080310500c03000709013039038000e400100c046411040520400b004032240c1d10001c4d40c8980082018282c0d646440c1c00084401d0525007208203940044904025811001d2009080381e804081c41000c9106030080064032074030605c52031040d03942c04a841c0900e619804d014521041010f04050350243d80c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 881853282 1250 881852032 881852047
    0x150a0e120f070509011202152208210a0e0d03110a0c0302040f05160f09090c020c1f091a2a060106050a141b0321010902041202060708 59
    0xc000c140710450500004080c818140b10034072406041c183e20440c000d0b58141c403280d0050340c581624511b400118000b103911204024a81003216905070515181c491101038007185000c1c000c01c1c110450070810b0480148450381c2c0b5941074440c8100e440590024035a40d508664520340340d1200510a03001e860080e0401c5c20440c00c150401056500032608640c1040c010401c500b4075014081403100500f40030445450024008220070224407401d000304107185050108050160401d0300103011440c0c1c04104110145801039564110f8484041c442c000c4441072440b00744034451541c020b88071b03135695241d0662410000c6841c081340100a000707030705030030310250b5161400842507000a0000c09181800381c98884219820310006800031020060300f0002ca011098018440f40040e0200101155075415422203030440ba00021500104602000030b01c103690704007020085840c090f808480700d240780d980d002d070038080340b0030352046c140c1842000d00c002e005407134a00042c24032280641c4199140805 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 881854532 1250 881853282 881853319
    0x270b03150109020c0639070b1003061506020d0f0c1407180207030c020f04150b0d2906280c0606050612010e0a0b18040b06150a0e 57
    0x3801d8101040e043d074046403107441d818040200c680c02818020303094906144216561214001c100c440820843c80e1483c2e010002613504110f4082541080c01d94041e0700700480d102d00f400810b031105544090030003110030310703880030103c0d51821a01550010325030702c400c60b0010303101c2841c0341e00e0040034408115030040105000c00388103085d0b40200b4019000c00e5003412140140d03107803207803841034555205001704400643c12038000020540c0456204984000880c0000c0c081d0904800c1d020b80401c14180c0042e080e20100d014000c0510030040a020b546a81a41904000344480c4055080300c20668800d440d070402d00004c00800c1f020710041070002d48443d40380342644820071040d00c001228075140e441845041e10604014250480e0030a150644c00c0042070100d20040c0220f43c400f9617a440420b241a21551140c034400300007038208001c40041505146240300c08940c00d80c1d01c107a0300000642a850810a07a004500303070a44040c0c10b08901c180129024040f0300c02254100c8042300e2054101e01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 881855782 1250 881854532 881854573
    0x1050f090a1805100516051c0b041e050714070c050d1b270612030e01110a0308100501020f06181e01050403022118030a0204020309030304030207270b03 67
    0x50f02c0c980040b40310306250346a40d02d02c44d861b004440c01c020041c44481c4841e201d5111031502086c51000220b010084000000c00400381640305988040240403032507a14505a00010b100300c0e4075032580c0c40d000611400c00d4042e889540340c002c102e40a94881400503140012030004850300403d00400f00303481c0042d034106000159004044240500306295401c1000b03000c8284540e1a214418403101d89814030340d44021540a07070080c180b020030342d648107003a4402c0851441407410311049420b5040c09090140c4140c1c4d00341c0c1c41284407031200310089115400068081044150100241811756654452120048810100010a01420f0342400e0040c00003054400005e003030030000900c07420300785806490840c8000321703081c01031030307a03601c2c180c0240f107460070b4642c00810100205960b05c044000203081101c0418000d501920100500c4402000003018602c9140320f41c0854a010b929980c00000f41e0060050062500140c40d02403c01c0030040c2d08580080d420107021150740c8041100d0412503032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 881857032 1250 881855782 881855803
    0x5100f06020622120807021216021203030103050a140f10020a120507050316110f010b03120f0403020d0602160521091f020a0c090b010801050f090a1805 67
    0x1a44031200340050990402d05007606950000c0420040c0304070f03951181021220084442c050004081c00a40158020300c001c0a00c0035001c0005582c421000010400c00292100103a02500103030b40328105040000040380d050343e811000500414066a50f810251041810f103001c0e14003a0311200d81c440d000801040d4a4901520405a1140060300d40203081042080308044068200340900100039040000c91741c00084150b0f603000e1000700e949059407c2c22440300c14400314032440103a44c42102041d07222050103001101643c0080070b1001006415000e1024018000d03401044100011700c6c1250360625000c1c42450058140700c0d07601e00202190f80b0911059829402c0002c24824a05612402048c01d404209c0114106142c4d139021403041c04814000406042c401031031070f54294000c0101051107a84000e0540300302d529006c0c1c0341c000c0d0070420100c90100b500c0800114a900c0c00045030700b10303080042c140750019a600100600a000000e803100e0740c60485101d400e020403014010041c42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 881858282 1250 881857032 881857037
    0x6010506091807120b040903120e01090b0411010f0f0206010b0904140a0510060903051b190906291c0b040f0b031b090a09150e060a060b1c05100f06 65
    0x40001c02400503060395117103100c40e486540360410b86030020750001500020f001d072600300040c0c1504075050540c010003865078091b148504507030070002005611082c5c0481600c0a90303c01c080b5400034882929003044c180400c00151300314a00602c4400c48140c0580f0a0385001000412881c0070814074640c01d0300c003a036800402c180c50ba010000c4c034101c0a60080b005007410b00d0044012450358179400d0311004c0403249001e010000328039082e03480c0c0c3d40c08003000301f4020386404842d40300d66824401d0001c0c040d41c0b203060075007100146039680315401001c21388a0400800201c500d0b014501344e9828207003007500e024042d00c2d59100752401c01030300c40303202b0780042d40c1104030300103500310344101050310b00170b0101070044406803851352445054541c1c0100540000910a010030064828903010100c0706510400000482c41e0031072a01081c4800a5124081c0b20341d842d040000b1511a0860802407280d07200c00716803c01c000d203414000a09039803100d0340c007100d05030081c0d20890715582a045c440802d1307441a0700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 881859532 1250 881858282 881858297
    0x20d080a022103071d04020903071503060915030308070210020301090f060509070e09132111121b0109050f03040305150f1503030910030e0d0207030506010506091807 73
    0x1c00b2000107402c10501d6074a581c0290440c500980020622000d40c1280030071903039030150101164849406880940784014181c40301240c44104621481581103140c1000a041080000e482d0303405210b0b138131407110720300800342d180390039900c045d20701b400c0c0a020766085229038a418401000c042c4007460103040c040e28045540c9221020100c01c6d14240c0d00410f1040d0300e10810f00604c0b076040140070f02422029218101580e0744c512490114403200031020704442000e00303403444800d40300c8100001a0303202780c45000750400c00c2c0c0c10950383c4071141162001600780c204145044101d050034500740701d044a400100c1c0c61320250f0307581428485101080c45030b40d80040303010700400205100b11000d0303180a00010100b85409501111401c901800c142ca0310124110408a00d840c24030407115a61406090701d0010440e0b99002002000c00c869407810b140940c074501c403c40c3d44041014400c4a412400609903a400c103400c00130340c1da10160130254801418008080a0403c030750440d40700e540342c0e0300c0e00507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 881860782 1250 881859532 881859553
    0xf06060c0a140d08060a060c080d05040809040e030316050919030503120f040c030f0c031b060306140d1205041e0614040302060d050408130b07050d02010c0813020d080a02 75
    0x203140c40c441c580582d05204c081c0040008540b41e4445250440b40c003442c040c1520052820002c9041c03041c1c0740c0c0b160340300307080c0410071040c0076503140181010720040e5404c01941c0c0051060315124001900d030041441100300d5071400c11881440a00f4009500805a0000c0300c0c0c0d0500c03404c1089056401180d1680011910312041461107030b070b00c0ea11480010714118249450b80d40c82d19240140c1c000181840a51009007081c0b0150186107030146606c182c0c90420039071316040108401296105a800080c1004804100304070078000c0050b05c0d90001c0c0551058001300e070f94208000b140000b040742086020700c80000c074001410100700c108491040030030071050500c40c00410304044540030b8011704200f0001080180c0f0340b8412105441d01000e8006210384491401e101c181c403c1444c1c4640b0081380300070201d00301820100500d1130501c41c0e011241c00c403002c000240e00380c4030790900007404035900700b000030400781d2480c420400142c03008151030350503a59541c0c2c0d4222138014070720100050f0312921089 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 881862032 1250 881860782 881860823
    0x308090c1008062403040602030a0f020c0a11010509010e0f1816020c190b03100503030c0c03010612020303190c0804060e1305010806010b0705010b03101401090e060f06060c0a 77
    0x4010b440002c684c221840c0006842124a11014100920591f40000010500d07240b5034800601608144c0042d50313241c0340c450045503a000440c40030b07550070340703c80101e00c042e40c0110b00f10b450084041c1c41c0c81c8040e15101d410020640c1984031403d40250b130028860310000f107500c081c00e115410029028845040000000740ba0150701ca00403809203020000c24420040b440200d0070032076035449041076507556203188204a41c550740d8440c039010b20011920015881020401c4004104290002c0040e00d0b80d581078000110710606d00607405d03030070030084da5030300c12480c58900001040600b810305d81201076a4480c2070f17507802a4000d030001800310007d02e02501e06000e000f101110310722028059075042c8503066803a450b044c42825403501000441508003c400c0d040343d034865600a042c0c810400031000d0140160160048110900b1210f000100b0141c170b075842a0482c58101d10002c10075a42c441c91001a0300ea809480680e0010b014482c2072404041000030700e40f001e105030941d11348035900341d207035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 881863282 1250 881862032 881862049
    0x2030a06180507020a200a030b0a0c020102070804030b070c0f0b0403172e09050c03010e012c06060f0a021e1b06090d05030d0b210a0308090c100806 65
    0x5001c1a41c00d00e4180411a82d0000340f0400031034000c03071821088035084602c16142c11120f42602d80007145924004141701602c601e251284054900500030010099012400c130302c14110014101d041c248820b02c04151800d4000d980442c4500f000400040c058641b0000c003005400f084510b050518104020590300c05081004190342c5030500d0400c0c1010402411003038500f94288d080f9100d5415403881c1c40316219a0b010040000e150100b1480c109071201480940c800d02401d89161a090000100428024001c244505540c03098544460000c400e40d40600b4000d040683c1c8a0028000300f40841d107000003c000500c1c81c1c0d0001e1581000c062144d40e9002401c4490590310f40109030741907081114014081c2c0760610459100d96107940141c0014200040c51101910340e1002040d00d48070032240ea400b20411410450b08000340403024228100d40e40140b481040300340d000074a03207000090140702c500790403520300380135141d200d42504041b9041d284034005c841e000809410a1040600780060b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 881864532 1250 881863282 881863319
    0x1212040308181e15070807150b12030318210d020d02040623090d020103020c100e1608210a030608100f0b040209100c030924110105090d0c06060902030a06 68
    0x415818400113464883d482e018801c000703004003c1d0420f600c0c10040c6a944403903110800142a009034401c0008000e80d6334100710340e406c0302603901c0e00000b00030070303400224807103040045816040314079015040046680c00c05018162926001d0141c80507598031030010300003811450303070b0b00300740b100a04e140c0c54104160b4203101d200d110010422503038039071120412450f401ea02802c0142c2d42c0d01c210054a4a8095445802c4425078a441d052090030b410100d100d0084e41101d00e4601c80c0c4a894001e490348078581e80107030b0700d007928101031240706014010026100725000d40c180010205c0d9510562414490038070ba0115070707203584000000e500007440c4074180f42c1180a031340450038100c0d080049281e0042060110b010301c00c1030001ca0042600c20301076640a00403405000c800000c1c01079050060740c2d960a0f149011600701c4005079403001c0c05125680c0b0845803003006121004041c0420b54949030010f000780c52094580e4070200d001030290006600407030403800001400ca24120a0030702c00741d40c81c3d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 881865782 1250 881864532 881864569
    0x30c020c01090807051c060f0203060310020a08180a021905031204030c260f06070e0301051506090a09110405040b1207050402031005030105151212040308181e 70
    0x10014046403200189800035580245c80c172038071b826800314804448200e0300134003c04141c01d011101903000d511303801842c01000254100c951750910f00c203e8034281c2c001e001c003060002e41d0b00c00004010200502c0c0015481e40000c098498003555500840d01c8041040440f040408400701c08015600b400c000c90404002010303000c5051505541d0344d91406130180c80b544820110390301140c4404219440700b14050180402202d80f00d00203941410384805003142d00c10017196201e856840b803030806000b0300d40b0a1000400c03102d00a51800c0821034280c01140e03a458000e0490507002c0b8120915100c1d200c005c1c1d400c00100d54540e8a0301080005503504905000c0c05810100c001c1d1007440e02c00101003050fa00304170760140e100d9644100003821080300d6400150b0540c00c11003800f44c0e0a01301c845d642910032081d901c0200c1c0310f87c102d07035541c1d44505240750561180010441040460044400b42103803180403030b0040c103014079402c00203080810080d1a45015a00880d07101910314103c10301d5410740c400382 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 881867032 1250 881865782 881865797
    0x201090f030b1b09060c01090605010e0c0307120b100801051c051902030c0627090121020a090c1107080705010903030e120d09170325060b03030406030c020c01 70
    0x6654034000000082d103c032500011000114002c124150180c680180000c3e12141c2c8070042d0300f13500c0740a068101400e41e505454140040b61101c04a41c400c0e00c2680b440040518584801c9021103140e84400b0245a565584034290250340d910312070300244050079aa03408000f54185070030402030204800460802000415803000080c0700800c19817003a0110050195000f1500e001103420520800c0c40035510850028810401310b801000000c25200000d10a082100c941010b0100e140000e018482d00a10240b900041269980c81410046072019020103030255031130b107032030003a645c00400d8000415100855007505c450b042016400901c00d80c0e00422080303103498006849841b032400080c04026188101b46255292132600c8085e007503041e41100d0041000280c01000710145010b4540124003100c0b014059140000c07d0320703609228228140d0036580c45641c0c401a5140381d407421560079840c1c00d00c0d48410ba5041c80984020101910701042d0308a0402000303051240b02d289883c180580c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 881868282 1250 881867032 881867039
    0xa06060908010c020a02091513020c0610030c151701030803160302120105060318120a02010c020c0f04020c070306050406020a080109090b0106051b0715140403110d0809100c0201090f 80
    0x650102504e8041d210486241ca860f86c00e10b940c004c0d5446c04c03c2d08001d2802e80440003109c00e034010280d4040d100e00307071919a158008460885041d0340710203843e1148035002440152501c070b0349400741c1c04690410384000d154204401a00200990080d90f2918010082041c3d620016440300c0340603441e4a4218503001d40300c0e541e40b00b4005e0600400b401810007100056a5082040751782452054450072034580a010001500c03981c4e000112a00041d42452810f0100c1030001501c00c030030708001000d00d050703000c0c3c21044c40025041190074188034820190000003091503072281c18001ca01510001d60741e201003100c044c020010681c0182440741c174029821000c581190b0600b81501c90a00c2c0050351819000b0b15000c604c1c840310840700242c0280714002513001924124a49030004c107498121611f0780001a5500300d00a0348000b40030140e0301e090a196034640481106092482901d40c0307401e00700302d00c020503080c4030050742c1000426000c9041d1401d5680215042c002800022100b0401c2d90a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 881869532 1250 881868282 881868287
    0x9050613061d06130501020d0302120a0507090f0305070905060a030807020d21020606030d05120115030204031203090212010b15160b0717130305300a06060908010c 72
    0xc151141c04104400c0c110308411980003041c00c1d045406000345415200e0200380c203c010800400e00c54a80503200b09503441150b2401b0340261030000c032409940a82680d5003601c0030026003001803683c010001c0d12003000c80c004040c254100059806040240885420111400c04444002c1c0c00d603482062045002c00001c2d02c601e044400701079040e10b401806412504d4070000d4100788035010711900c1c441942c0c680c1d059500090040c802d800803400c07240c0f03402880343c040c0d07a6481054035175140e81180310010302035818003a24448248042d032500516060343c039110b0760b0100c0c0360b040c0d0020010ba11008200154500400584128030010700208107405030807000503061030110010400382d440204002420369100c0ca80042c01c160072401e24034983c9441c0d40d0041001082d808151064415030b401704041d62440780d80b0900315603060321003d140602c1ca0711843d040030040c4a07100c00c4000d02000d000c0701ca1b041154243c4c040c0a55100104049082c0003000d00411013a03000061568540a172011440e90b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 881870782 1250 881869532 881869567
    0x90d05040e07031a1005091804051c020703080a0915080c030117030c0d020c090718260a111002161e0b0a18080a020a03080904020702031c090506 64
    0x1d140d0400003920b040d9204d0a1a07a0948400026480030409907400c02c019007010080048550032100c418400c4061605200c840b1404d503400f901e250b2000303401801040c003234007200d444101640112800156255a140b446900c1012032078006030a0b01800c00071100558420600c6440340e040c0b0b01c04c0c1e0719000082c102c15000c144918581c0c4240440045103024050048403040071045007511860200d00c540a50380e02da203802258081e050f18000240d100b4030900d0050031080c0c00012a00ca1145082e4401c0c074400d804070700c0c1c6001000015541a844103040011680c92846200c104442c101c1c503904010b83c14184030301d04030564014010303130400c0100c8a07034050141d0b8400010401070031418699550715002c1a001556548400036442800641180d00702c11412040c9003e80038840c0c40390108c40d25002c501d0744c025005891400d052000600c0d1001501c7c00060151005041403810b0700064034045042d52203188000080202109107a444402d20014110688449241c0744200d4208110300c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 881872032 1250 881870782 881870791
    0xc0c0a090203070f051c02070b06210d0e010e091f06021501031209120b011a09010509041d1f0b0303030c0a110c0a08010c1d01020a0221060906090d05040e 68
    0x80c0c00203146c065055a90140c0c90a000d141204544800032803a001c20a4031003560100d10400714944ca403405c0c54810f404105166881d131018003807840c0c26100c01c1c0c03540c40030848070b00e0500c0606101c154031919143c8020b0300c0380002c403011880480000242180c44007540c4c1120302107406c62034044101c140001d00b5141103d5202140004605c013006040740c041071035401980a010207148003109004008203503034140c0f2148400b0303820b61172840c61101024460903c5040c0804e60600424200d894164041c40d2502c1440c1042c40c3c2580040c9030040c14580102010405000840d03c60242ea5496219501c7ea4040036402076141d410031407114911401103850510030090148206540741c0000d0255251200010b0301c2e00c4880d603200c4482e08c0c040c00c40308110500007030fa1190007074901003035002101c44106043c0c010701803102564003030280c285500d0f20b24141504108100a000410070880c00d40306000b00c80c0a01414141000c0301c50519001100c080d040103003c0c0028001410540745484c0c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 881873282 1250 881872032 881872037
    0xd0b190f051201090501051f0b07440a0206090d0e1009180606030b01020718090218070c020a15083405191409090c0c030c0c0a090203070f 61
    0x442d03455081d82d03000d070507042e038000c00d25401d000074080508031100008600481f100d00501c0d1040d00d40a02c0d813614010074070040d01c25050303100485a4201e2100314014201d51076403001000002c60006401d44260744452650301c000000340080b40a6814840b07103410200308009001d4030710507030b2802080e850141c24004e04c200403151040078058040c5942ca40200207100041022800b100b0f18a00142181e1003002c0100e41406120301081d0320215940040e655840104000d140d803202c814402004110303c101d07040980c2e008107007101d442035110640f00f4241c41d950344900308200d1042c0140e40100707500007102803a071046008a8039803c09d65850b40005c1031200c2050401c0c8004200150141c3d01500400810301e04c1151000c50383d0020081004401d1a480d460400903440e204940ba4205460405504641400075584074a001c030440d13a00500142c0b60781c5e050082040500c0c2c10b690014410425940c01070100f20120b04100b0244002815081c00843c00c628002307038054003000c800041e5404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 881874532 1250 881873282 881873299
    0x609140403050a09030c080a0303050702030c07210519060b120c10090b0d0e0606061e0a0225080118020f040905071e090605040b030a060903140d0b190f05 68
    0x2200e441600400c1c001c46c0c0103a20a80802d90310300301c3e95150000c13050240c0020b81000e0014400300d000108079105003810100604006103007050766808401042040b941c114072404000011607410072950700358440349811281350748118944681101c0c0200741c107500900c000c411078008001c0100c0c1e002c031440f20548498440910369441102d0260b4aa08420304e6220f0101c2c5019094a007903021200100440040760b87c00d844101c2006a035010745501d0206e48040c41102403032490482002e401d03003050320b00440f60055403962852600c2416000891014a54a00308000380c542c00d025180c02c0039540c2e60665818940c07034000c90080c20415151030700458590f0b0350310b0100042001000000d20b041000c08141589600166100301c402e8841c4207007060818501060900c1c16100d513440b0781800900806c003813100c0e9600c040182c05149030980510220031403a070501480d00c801485111560040014201c00744c03000c0080018500c0c0c07801040304d034021803d00c47e07a00410102819100304940601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 881875782 1250 881874532 881874547
    0x601170a021c0f0b0420011404061101020405120f1221061201020a020a1b06022e020a0519181a0f070b0106080c0304050309010f170c0a03060914040305 67
    0x20b4254046143c02001000d100c810001031102e40c0e055030301103140c1e1803038034041c0d01076210044885540446050706441000c0004000b11030080b4680804404504009420640e441000860640d6110515016500400700740410540140310300008000c0342c032505814802810902049402280b041c14602e103000c00110326943d880c0c01103001c82c02c82c0e40009555944040c50025110481940e080311100c01540402810116022105094503030aa0050503011040b0701111217a0031540554100b60380481c51460045403140000d024000003501c815907240380101d50000c80c40702d91404817080102d10861296101c42c95401201201c500402c0d192041c20b46200042a900c11b0071455400b04030002071170b00410003074828180c1255015100d080465075103940061303c44c44115002841c80c0c208001e05000e5601607001401616920325000141000c8000d518150000c00c0d0b075007102002d40401e21104040d4540690000707000310800c00d0021030780c0300b513003003100141c09030008050150125128 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 881877032 1250 881875782 881875793
    0xf180102010b0d083606070311030301030602120a050714030c22030203070b03040f0204110c060702011a010302071104050606250204050a0e0604030e01200601170a021c 74
    0xb42400d000240122003011080c58110220351110154508082d0307818121280103103030000c804415002c01d540318000e81c0ca684104030741ca6201d014201c0511580030f0802c004804208080c5010798410752005030f545c000c0c14200300780d00400900003c5400c1c10402001072880e404544040003618800c0e41a4403038490714428940c50244014070b00e0640c0300ca4044031400340a00c88070700100ca00a4050b00c0c8916150003a60380b0510044802030005001c0000e02c40050030a0382c0700b5240030017000705a070306090403c0445800c0003000da6144006030b44480d400c003d0852607840b004500030007405e086161580c0d0b070b40c41c182d0000c0b16620240c81166900005011a1605000c558000e000c0c42a07400b01161580881507250135100130a078081c1d0320345000580101c40910441c007524140300000e00c0c0c207030358907501110030841d07009070340341000307000680d440480d4190070380003198180c4480034048940c10160000036840303002441c0d074010340c01600d607003000d6160526142000e060751000c41d02c400c01c1c1030410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 881878282 1250 881877032 881877041
    0x70f3203030d090b0c040303140a02150a05090f0601060f0e030c060f03150a030c0b1804020d0b01120c080f040303180b07031a01021914011508120f18010201 69
    0xa5405001c00070300c1014801c07a640c41030700d1051143e60210003a4032095032800c0b0602460000602048071344410f8511205590f0250880114a00c1210b40c2078041103142c19280030141c070101e103210340390014400801405d004100342032503500010103843d0b2400c0d03001032100c4e86800c804010320070003450010307060303e0501100c1c8041c0f2010340308650f07500c208074040c80d0301d90040750440046045d243d5a9003861401c402000200c0e50003001117a060f90030720101d080c0d40d0b4402d80f46001c0c0200010380c429826181c07400a48030303040c2e18070000184144d807080098126242c684480d55411300c0c001c4481c0c1c0894208503d82e82214480e10f03402103e944625040d401881078141c1c0000c103800d0882da00b4100200b211282c0c5c850314292b501030001108170300c8000544420851800d02581255040e483c3c6500c0c820340f040700260141c5810013044101c2440a400c4a50300034841803402001c1c2024401d03c02d040180b8031030350030911401403420717942c1841d80140c0e000c2c0321804d13150b038002c5c0c4c11070005581c800d400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 881879532 1250 881878282 881878379
    0x2090c0c0a050a0c031b0b0d0b0f150904060e0c030a1e020d06060906030905060402330c2a090a0e060906041509170c010612030f02070f 60
    0x440700340186074245019002c13240d01c811180000c02400d00a11003041c05c411904580c0c60341c65007802c065402c504e140141124002241e04012481e1441555907a00d200c292812090915a10f507500143e500b031100760f07051074002c0007182014005018654801400710fa03401421104002035010745814000342140410701802c6083e130000c10070003c031194a0388984104c0700b542d21403681d41075840e403041e4240c96a10f05c0241c0070b03810041c002000741c00c00030502400d45541c031101d00718507000128600011610407684910000000c15103510a18003000011a1045180c0c0c8040001003c0c03d145074980001d180c81c24050303400600400d0096407a904101c802c014094152007051a050514030380d2003204aa09552740c42c20030b480851903c015200f0b101c9400d030400c0e142c130303550340c2034003c1d40780f0030351155140c50129944c0f200300141019042c02c540e015544030b030340d54000340120848000c3c505030194025080d29864900100009a5850761040c41001d40466103c140d0380c50304a4900502c00c1401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 881880782 1250 881879532 881879543
    0x140a090e1509040809040b010f0f081f0915120c0308071e030c0b010506030c0d05040c0f12031e08070c030c051b04050c041401120f11091c02090c0c0a 66
    0x82c18401040107540103070404203029503041003a14045001194242901084072021603000d52101e01d0340e601c10381070703141d04c208291003c44026640005000014405c0c0d400380e10065514070301d60304001440302c8554003e24010031b034620030a03032a2302c800800075a940700081421400240715420001302440884030b0090101085903204624100540050341d041c00440314202d6440c004240e13442c0c11000d07240205500c2150900b49460030800e10300501000c0c00030381d80d10241600010391240511048805041091440224205285006070103090340c01811591240e0403040f929645601411695100805203010301c0c15203e82d0805407215106110042c000c0d0107205107090400c0d8034106031001c502c1042d202004141e031a0b902081981c0114003030f0151910240c00d185050b5031064840e1401c480c1d50010016051a6100d403642c00c4941c120041c840d00301000c90740306014546900001012a0200d84c800c0341c3c04016030010f1601070004001604407580840c283da060401008001007656010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 881882032 1250 881880782 881880799
    0x20d050310050418050f3c030d02250f292d010e0f0717100302040b010e030607232719030f082701140a090e15 49
    0x1940c1d6414200789124107840920803210740c480381810001e002d0301d40c0c120811141c0b0baa1288040c000804201405280000302c0480d44402c80e210030508c001c0031602224034005980303840c20316540e040080d0180700d000c1032040404240e0301054090194084180d448180030300d0b850407203030b083e0000c0c1d00303a402c6610780d010035241041015109540d0244414081c4a01c0b10b07032240448403c0c2003000424000c90f61482c01c0e41010943c200510400940c100030f646c00c1c072984116020616800f4510100d40c15124040c0303203c001c10035800d0a2090110410003031802d4a507081c03040c00420743c0d03076a000c2e002808002e1041c0c40400240caa00e030321050140b81b004822980c032070741c000244099080741840026200074002c480c5010b031401c4000e01c034009407a6208418800e00d162a0130150480c9204180c44000e402c0200401010340041d01c1394480d40b180b00b00ca6000c1900f9400180958814400c00c1d02c8030f0b00070006201058ac11591901c00c45007075045a041036501c4041214642c141001401d402200d00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 881883282 1250 881882032 881882051
    0x203060a180e10090809130905030a020a0b010f081c140a1809020304171c0501180c090b07080c0a0804031a0f01030305090f010c0c0602071410020d0503100504 70
    0x40c2d400c0018112912000c44152040f00002a0110350a45000a12000d806c1102003002c0c200741044101084010310006104c410036283c0034250740c004400000140c1207030290b141005401568580540704828002c40140d041502c80703035a904440c9503118010034400c0362400c9151041a8140003501d500100c50f840c0d10440201070101c0101001020038405a000c000c99548168401c1d070344103540016140d0740c42024608102c03029441003544139489050080c0b095641d08150080074002c103920001940c41e0855882d4203012501c01044a40403c607444008100f0440c0d01000d50328402c3d04076a0080e0785007080c9400b545810360604004041c0f0801040010a2010b00070740c1c40c1c2500c007881803803d281e82c1c400c0c0f084240200c0900006000c500b0520180c03d15003010315100d07601c800d060402101c41070003a00c985040d032200303500c03140050340700c0c01c41809942403400e40c501c00294103a403c0104c0c2d203000100030f51101c0d600380140d401c012011001654842c000007003800100806001003000560 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 881884532 1250 881883282 881883329
    0x1d1c170d0c020f150103150b04090b0a29130212010801050403090605120f0c0c06010e100f0e06040504080417030a0f180b03090f0111041401210203060a 67
    0x5464561002500a50314108591040400d41841c240284182c14000b61b003599201100011020b02c908002580c0e8400000562254800c3c0c1824600030322a00d20745181154281003915118040c40c08140c142000d440030f9000c40c1d5540034002c0004807200001e541259189400074054485002ca080c1c81c48000020004c006500031b5009a0182e81c0c1c4007003d07a00d076401621140b2a04021085c0307039a41c680040e1600d808450f0940e0010380c240203240c5009012845145030600c280c01042d5400903540505c10380d12781814005000b040800300e010719161a0030511840e400c00100440d005d00c1e00c880014080040d0071b01202c0140030f484170400031380c201c3c00c1d1849071340c2c0d040007041c0303004914020300e90f948281c0649520300641961403441ca80b686d041405416981e080500325051303501c509031581c00311820a00500d001017076900c40c12030f1103914040e1520200c410038040c190602c250400c2502030f00710480302840ca003011040c0096505d864200201d0b00009440c0c0c4160110040142180e01046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 881885782 1250 881884532 881884541
    0x60a050d06090504030e01090f0504020d0902120c0a210b1005090c04030b070305010806071101151719030503181f0507020601080c031510090204030c061d1c170d 71
    0x50003071b035070103c821400070300640f08440b05005464a50880110401c0b4610b0541c00070030321596048800304240c1040d5003c10351525400c400c40305140c005100107003160509900758401440d444000358001410140c20b0686102082c83c05003001c0c070b1240c000340c0300c0c005080030308005040240646040b481c05070421042ea03000741c0011034648130010081000c0b40d00c640039441c140c170f00c04400b070300c055180c0790341c00d8540300005c0c00f0340b103c40c2d500da0740d80000c0c0300032010940008010307080c07082e404c00c6e90600d03026090040e00a0041d8080c2507201c02c80300401d501000b0b9035440002e400231504451401c1051528200c10901c404801c1c0ca4030140200724a40c142d0003007805140f0030740032903040342d8940b04015140c0603000c076903d4240d0311003030100b1100050040100e410980003007190340070a449039080d4041ea0b00070b030000d80304070030491400c1125561140f0382c0407125803c0600310300c0d1a002c1c64000355000d80114800c80c10484610411018002c4000302028400d180610865590a071801a80d01a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 881887032 1250 881885782 881885791
    0x180f0803070e04060515030a060b0f0a1b111504030b250c0503030c0a0e0d03031410060c08030402030f101b020705181003060204030b060924060a050d060905 69
    0x1642c4148849050709050107400309966004200d6014060014542e001c903800050009078070305d0b140c0b44001002240480140250700c0380e440f1250740d0b080000b0001e42440e041c1c03000070030084510b415020101d0120501050580801c40e946000c0f070204482d540000d000e185c002415250007030091145800128200058020401c00031201e00ea44c0703520b056030f40c5020540701904c3c582080001030009210788004050309421810881c8804c080c000100329034040c0d054040380440e50704c4038168035226442c050598890b1320441c120168504055004002e88030119005218100103c041011035a00f440a04d50400c010320858824050001c070450280c60030364551441c9440358119082a0341c40820440103980c0c1c060f014640c0e240101000510800c00100402ca00a006002c00b100249580c0000c0000390701641c4071a98900b00f0f0ba0400142d031401420b45080b20445513544103100c400c1620400081c141143c0b0700f510742c1c5207100d00756864410110b04248052601d5400714000c44245d010324040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 881888282 1250 881887032 881887037
    0x120608010b120f330103050724050f0703092c061203090603220b1b181002010b1206010806010506091809070308040303030b0102010f0618180f080307 66
    0x1c03502c000c061900c54142e090036503140d800c0041500441848100c40d404010300d814182001c5500105100200c1c010070f802c02c035099080003804001d000000c0c2444440e10341c01c0000350b804903e0940c00a400e620030010a4101c0940105040d805e15000712000c100426021103800c010164000402c02003250500105410f25004004200c6904042101c0501000c5480c000c620340110b00c82003004540000341003200901d190340e070304103080651941201031b903842128040c0c42410288034101014000d50a0f251030500144180f900c1482c030081c4020b03100b4020f40d500b920003100c140049003d8042c04400310340008030705540d40312800c000190b03a030403110300b04291034132030342ca13501004030505c00c01c10703083ea00c802c45219460130b0111100300c46800031501401c840381955260303252902e9802580c015004607a4443d881c20041d6028000c1c803480025a1800300030207803c110421200f50280f40070a03118540e151042001c00a4025011450b40d42006170842c4d891160b20b005161584110780c060700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 881889532 1250 881888282 881888299
    0x6020f0f0f0a11210a030e010c03090501030509150c0c07050604060c0b2208120f0106021b0411040902071b0e0403030e0a0219080705060408100c120608010b 69
    0x1031840818001095142040a8100340340640c0382c82400700d8107800d0255010000303042482c2001c0040c90840d0b44804441d01404008410303040180481c40703010350346414003005d0f00c030705400254000480c0040c1c07402402c0004003900c030042902d2802141981c900302c06003101c0107100310310507c40d01618813008888100e0305440e8542c010b202c0180250f1003484080360039000c200d80061a1800e00a80c007040f115001e013020a643c49015210011405c01a620304034009030740078054803001c1c8821742c0102d540581120342c0d49041b8009540303d10320654981d25141920140c000c65550360498440744071108034560310780b078407804501c00070350143e201103c120120943d4102c02c101d032200b98404480c80402c804180e0768690f1030980207440498602c00441c000d04190000581d03d07840c2c100b20039454004001105410003102d44c0c54070703c030b540100340b00c2c40742032004000381500000c0311046c3c4c0000341070201c0c11042c01e8005640c880080c0c40320b40865420021702245a10056102d5440700104039401d40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 881890782 1250 881889532 881889553
    0xe03120309100e0a030c050a06050c0d05061f1d0901090203090106150c0b07031e0e0d0e0303091504030209040605090d0302070f02011404121a0f09070311040f02030106020f 76
    0xb400c8581190b603500d00d6800c0150300e84080781c056075507a500a40128260360904200b40c2d128000c403082103d07606100180401c101100c01307030038484d941d07001c00141da6201b00e01d08c0c80001001750b040388440203007c028400f0590340405000001c404600c00700505078030820f584450005020b0b40080316041b005610309100010020412083ca000043c496110024400215200d0071f03010702d0010805000e040c0c50300e01955889521048510700b4400031680012000c07030b210241800c0c094401007120030400d1000940a441d50080b00720303001c0210866041c1802d002400c2d45050707501495001951148401e4200024801035402080c41000c9000598003100c1c850354040e0101c0c043e106001c0d1492a80800400055014030f510003081c1e24221240750a26030703140c402102488802da412107800d0422a894003030b4401c540c18071074111800b4030746801c1c2c0c0e1405c0c44039159500c07110310014000035088440c2c550340b51103d902c2028a0f5420a5040d0b50704d40e1100d4000e0340e1812040080c402078815008000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 881892032 1250 881890782 881890813
    0x60e010c0207151101150b0a0e040b180604180b071b0b0406180606090b1504050f01050d110310080c01080709050d110607051f051006050a0e03120309 66
    0x80b82070380c0f0111010065507000000480364004800c400d08039941da82e0034411002400c0f102421300a080da51f4040c1daa40c0c003840e40042c804801140c90500440c1018803d40300c503500c010242c6003101e00b500c0c03555419500d000001707020f0506440c4c001217039034800e00c4a1007440071620003184204402e44070a05a205c49442e20142d007801c1c00e1000e02244c2006c80414002071007508410164489040c0c0c0c15088186501c0380307000c0b940242c0c0841104c4d41d0b280b54190282c180b04050a0010711840c146500305031a1001150211031800901070401c1000195844840020742c44003541c01c1c2100350b10768032450143d807904a0f40f1114040c14071a440b0f011280c020562052540d20722851082d40c50709039607890302041c840c000c0c4a8160440b0451050580c01e03005403161000f4014540c0034074000d240340034070308800c580420180c0d2030f104512400c000030814907110b100c1c2090100e8507203140583d5540fa000300c08071001c0300351030515a450f014448004104240960103180210044402c1d81e1b00b200014420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 881893282 1250 881892032 881892043
    0x30705090a0608090d2d020f01060801091707020d140c0f040b030d0f050702060f090901170a030804030528081f031209080303071805041a0d0809030a060e010c02 71
    0x1c40c1e8945e88034243d41c807030007441017610b02d040e81140c1c2c06901e500c1d40c261842113880c05156071003100503808101200c0340342c0b000340241c00c002d0400c1c6000b00301d00b40268440450451014a94181b0a0400190a0119100c1083c0700000360780141044080c4203150605030b0f15400c9191115220303070303210080f508007482c0500c42c61614680060051150601c0382a0940d4444406062007041c030600f8032900c80561130f01c030b0051880842a40a0b541d98003000e004000c2030040c10782080128050170362103d1200f500000c1c06e03500307254041c140748030780b5516441c3c11500c61144041201c00640d0025204a0000d01c45101c01001440c80d1a00c4d00e83da603894070640d01035540128051642402104200041048001f000303000c0038080c079240701015107620290f451079105840b500e002441021201150b0b00b071818000c0044e01c01120144842c81183c190111213421000455104483c061920b0007004101c10860b0003008000d8144c0311991301c207003009001041540001c407255420064520481840403c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 881894532 1250 881893282 881893291
    0xa060224130b09030d0905010204210b151f0e091510031a0904051c020703110105030702070312020a030905240a0905210d09050f0112090206030705090a0608 69
    0x6100122000d16110503844107409005102613020800150000034500e0007800c10b4940140e0000d0303030741c51030301010902170401c9200280201e6106503c000000d826240d40540211031000e03240080481d2100080040e0b44542c3d040401d06404018451000d401c01103100d00010211800c942580d614040100050341400c100c552028083e8403031602e181c0a64845502c1030030980c00751414140400100380c020000b0341d8141c65030782c400c3c1544101d0958020040d00700c10180d1002d004414919034070030b107041158203081410f0020102c0000d41c0349100300444001540c1000707242c0c041c5d40c06454065203d1000e884241c00281a0140101d078030b0800303a40c210944441e0020030b0000c1c2c0017a290107a42c9801c440b1450b42004442d2034000303400c3c0d0f10104072031110000c0038010741c0e80b04440c101c06854503259031048001d01904d09005c00196903a5a110aa2074100b0308212a519a944c05200300400182500960002010051040c5a80c0c04805045001030944064605d2600c03403400f52000d060465 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 881895782 1250 881894532 881894551
    0x90a030e01030c0e0d060b09070219020913020411040f1e14120f010b0913050c0f0103020f03010e01150203030c090402070c1814130f120e0a060224 65
    0x9401051940302e036000d8004408140781482c0c624201100140502c02e4a840a82e803641c0c552904211516103907602542000c010f00007094003801d0002c0e040106407a01d00082c1c464420b280000c0c00300780707031030602d079402c40c1d4014800c002d075801da0700c02052260464010400400b983c00c001055060050410102041c40740c40f10410191a1100000d40c4105c5454215004454000700750000ca0082001d0785098002c80000306618041000340315400100414165604007545074501c01701c0c03000301b030321440d071402561000105003200c40140e010b88030300070240310100800000001c6090f074095a16050340e60310701280040c0940c21000301e9036030100361401c1104503001c1011280714509039004090052164032413104090b40c0e140810b0071060303d18082d0070711070f84841d0141e040030194155503500c10500100740200b20b100b5100c0d20880100e001d00140981100b00b00c51820b10300510081c200c81d10018038119440383c49260080d1a40141c040d002c188040342d0100b00d036404038a00c1040d201d5007446 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 881897032 1250 881895782 881895797
    0x10206010e070c021905030d0e0f0d06111b0c0d030801210c0b0304141b06070812040c0e01080d120911062d0a0c020d06111201060206090a03 62
    0x20350400041c84068185401e01c0400390710000142c48604004c2104040c0020313031412903103000e007414103040c00c0c140840101b14488000d05115550b1076913200308a02c00b59901c162400d49894001c00030400c201d06105000c40c08604080099081103054132f004404000740d40a00502c0030a110f82c1840361400180440c03447c0c070042c800040300703010155500d01d80d9a500d075007008064994086108840e0080713000c1c0708001003040b084c4205403145001c90340c014030046c0741d511005001802c6942c4d61380580c0c0d118440000f0707060180800c0e5020355001c2078200d81d00080f141480d00d003560b03c1817440c3c42180032410a20000041c08a00414011070b100035a4441c0e0000f4120000004020b02003141c085555a8000006103c142c41c1c81c2c0c040c01c48950031b6215040d481500c070030440e4210903506200c10b00315100300403901101340e0001018440550503143c92241900e5480c106001e800b6003c810348039000f010030411240f8003111440343c101c405507000c0d100b2540f04c00480c9a00c80700b000030040c0203c0d484 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 881898282 1250 881897032 881897039
    0xa0302010b060a091a090a06030e010b030706050f16230d0f020a0803180601090606180b0403030e0a0902070605070f022113080115150804030c020f040204121a130201020601 76
    0x85c000c040320840c20204039103240c150410005801c154030340c3c000030000399840c0140d41c0104400d11130b40308a07007000c40040c80c6a0385031140007441d511840801b242c070070b20089800b501083e541e28107546c1c03c42d40b00c01c896120004080720340790790107901c02e269000c500c900c903d40c90519006100304000500f0701d0303000c0d101d90559522400160360019155140d400301d445a0502c1441d030500c1464040c043d1038401050380f9140240042211000e86c0400f2821005500c0030403103401d015003160f0482e0360504250000d000700030000380580505521131419103000051160030080ea035400a4411003454550303034508a10058200e80d81c98074072103c0c2c2c0b030504016128a454004400240000d010854549640f075511000400e00f9102400807103403000c00b0500062214455040800c1001001403908480a14094400034122001d15601074060103698081f0507482d21547c0465029200560039415190000c0c5400000d0303480189171483d000320b0350000703c0d0443c070b10456041441c9805a00802d840d034203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881899532 1250 881898282 881898299
    0x7051b09010b04241709060907060201060e0a051003080d0902240a0c020310090f0204050106052503141605150903070b060a0e010f030302010f060b180a170a0302010b060a09 76
    0x104c207041c503024049080044c60700700240201c0544540480fa0242c062810080d032050300d041155001030095906083d0f0500c0f034280801d450766401069000080350035101c07004200d000c450030307400191036094001030a4a04401d203420604842d031080e20300c6000030f03440944c502d2280001d446241030b045410451511014810244103a4545c00102030301c0c4007007140440002100d0300f100d400c0b14100300d080c951200b54505441103500600c603c1c1042d61410850201825051403942d004405214510050300c0905101c0c00800c0d00140e00f1500d160b07a90388806010700304800340c0e03c400320b600e071103860098420102d20030703030741402040c140340207604000995994100111004001503040500d2050005a10603000798507130007040c0218030060b0301e904508000342500e81a08a2081090400720300300000304110045903040780808403c0300100791200c1c0060400d03c001d42c0445082401c04c60045003464000c541000014481d8000b001070106210030300184c2e00440d0108004995506020414503c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881900782 1250 881899532 881899589
    0xe0a060e0a0f0e031c0b10090608180615400b030601030b040203240a052a130e01050f0405100803180a170d03020f07051b09010b04 58
    0xa102e8002145803082d007201989142c01c90078959071241d0a20b00c000b19041403c0c03081e0000c1100503540d11541000c5100054140c0b401c3c1e21030007040001440004103605200f0645a240c0781d02102515150b003000700861140300d0190f02418400c1000880d40302602c100820782c1d01448031081420010031100a042c0342c0c1070b40c40000780498042d110180c81500da6014082540a0361040c802d5004504007070043c1858101e28403881c0c000c3d00ca1f003c2002c208003014904084d40030717100000c0803500340e0b100703d90b160811054400e04040700a1054040c00444000d07005040040c4240c1e031341641c82696985070144200d070a20030207800c400c1c6100061401e01745070f008141d00815424400000a58a06065145a2002851740700701000c6190104036440d201c03400c00c0041201c5400c030310700e01c40d051003c0da840301594109403080c10740c0010b4101e10a174503c0182c0d990076402c501070300c01c800354900ca105010b0043e0803286101e8800c0c400007040448843c41a10152581100000050b101d441084ca4415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881902032 1250 881900782 881900801
    0x21090c05150d0204030b0f09070e0105211f1512112b020301060b0315090402031e07080c1009090902030102070b0108031c0c05070219030501150e0a060e0a 68
    0x440041040d030001d602ea81c0010001141300d156101c44500d41005078a960300001341c54010150054102001601000407007181960001c8813441c01c007440400103050b60400d0348030b4102c06401017071603252948001c503a202c1c2c800f820700d81090010300e4140c0007003110f1001034040c0c42c0c008503224216070045400d4945480400ca0040e060064400042c20032103000d8040c44a101403011003c5210400c6040a0141c04010301d09400c0c11070440c10031850078105400c51003515409004a034000806642d400c010215845481141c81408101010b8000e0b0300d4001030301811160b880303003c0000100c0c0c100035018103500700700e40d0380d001c0400e824030160402403e001e001c280c1e0b0640d024000c00012034007014185000340f103c2c0e4000e60342c40d103030000d0900c00582000a01c001c42450030046440752a007201c100c400803581100c07010494801c2c2520120f4842c0389400c040e1666203444484000020520380c00c03001c0d18403500d0030b803c0381d80e5040d40000984000d4001e800c1c01341c0d030040201d00e071000c107a041220013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881903282 1250 881902032 881902069
    0x203072003040f080d11010203070f121b05070c050f0108012c0709031406010b09060f07050105070207230607060b1f02061b03130308060607080a21090c05 68
    0x419984410101c625140d50300044d016402032881856201d41229000f0380c400c042000950941c07902c0c000c0507003c42c01164801090044242c00b1200d050056405403003080425903080280001010780102260001c81040311440c070f000402081502d84065400c002080503550664103030300b440400e0095240041c0d03004003946a80d01804000300010380c1c1d15203c2d0a203669280503a03899401c00044102c041e90300703050139400600c01480f0b41ca02c00d2003101c02d4404103548040d5035081c4007401c45030070b00c61840007401951a0030f00340601c1d180d000c660442100c01d40e20610740c1d501d10381084481d0300c0c1001001107601c0203040000700005108ca40140c00f484000600c4042003980718030201007000540c1c146100140c0009042041c01d4907072107980000a02044891821890b090340211186030082101a060204030700000e200340c3c0d5014101d40c0080d901048080e1113004450b009822090424080c0d260100484c407031742c15090b032611403002030301c0d00030840d000e21514200c140030040401e182d400c0074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881904532 1250 881903282 881903287
    0x30601140d06180201091401080a0c1214010e2206091415010f06090807050f1504080d030c050a0512060a0503010e16050d08040b030a020d1802130203072003 69
    0x1c80c24603c210f42035072590040600c0c81d00320603c001440003410303400452020010300c610303241e1640d2203281c83d0350100a104d00010a04e10080c400c0c1ea2040c8034000a0003081e082407811f146119181100a040700d0004000c1c032485c1d00d949032501061841500c002900f85d04045c10440419081d800c04242c0364020b80c02019a02039107a00281030280c0000000b40c40e81800004100b243c4011a61200400c424038080f02102d007002c0030161110400e02c00d651141c40c080a040c1c80c25a100d81012420003080c2d0341640e500c0b651403c0b5182c49102c100d03140400f0a1420b03138807600e060301070800c45100480c1c03a41c80900e080f41108070000012030141040b0b8100401d0140400d80d514244168880c07071503c08014800c000303480e0b1003201d0704c98440d040980181c220440940001c0c1c860010b0b0b8040c2c0b003003041c140b41c5a070380304a071100080c0650380001440500301b00720802c0140c641c004081c6564020b503495a414018034030b00a0903844103803200c0b03001403107884200e8080d03601c2d420301c0d03e601c08ac150242c91 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881905782 1250 881904532 881904559
    0x9170c030f030c2a160f1806090507090801230103060207141e01061208040612020c01021207020c2d01020c040e01050610090e06040e2e1a03060114 65
    0x21504044000341d0002550064250540d0008200440d80700170803420382c1e9040c0d420a12030721751908644c070a203410710011012042942e006504081c003e402c1c501001c01c002e141c440e80050020440c1e03c40c7c0c4c2855442c124506800700241c040c40c071a140b01329420020103910b907070f039098025400200c05a80a80425104400b240f0041c085980c0940b010b04c1220441d40c1c184100500b101d00a0303110a80d200350707140080380041c141c0f1081d58101c404500300140f10324031029054000e44a008118034855100050001002841d200034038010340d419401c94802c50b020030103110901155203070200c01d1001c0c80c6040d21140103058901ea10b48a01072040da1811007010002c582540d00b0100206000d175101c02c01c00109081041c0c6980400c911468031201161800c4ca01e070408000140c2054019a02c4500c200240d0000b040070100481034141c03007800920800300ca50403007001c25104895100d0400400082c080720740852000103800040240110740d04e02800c002044079805d1906401103e807a107500c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881907032 1250 881905782 881905807
    0x3020d0c0e0a1d0f071b20010309020a09021303060509030a020f06191109300a050330040302010b030606121f1b0309170c030f030c 58
    0x80081180307a11040380c5001900204000740348541c202018a0460440c980c00f5200341140d00b41e08804d508000860503180c3c0502125202040481c6040818039040c4a4040013209110704a04603e41c804401c9003000c41c200440607a52100406580404841010310032041d01d50300a2102505482120000954994581003a030f041102c1c00319440d0800700e00780fa0b04c40e03010720114002800c0c0d403000c2c101900c0c01c416081d11020783c000814607215510300d0020705100c0711004448140100030456407200100c0e4014629a5241d4034010540034542103002d9500354002074074102c40c2c1d0b0f00002550a040c0d00c40b0307c28120340300000381c44038100f40c246c0a600c40e4040180c3c1e42c501540c06980040b030351a544805151900c1009003665002d0032200150922041c07022841016031400e01c08207c1001e0101d85d0300030090015060f016404c15a00410820425015400000300394071a220805000d0003201000768135015100300180940c000300000c80d03209048400a5900c001c040c1071450401004070f144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881908282 1250 881907032 881907041
    0x10f0605010824040e0c0a05041e021c02120403020d020c06040e0a02040b0f0316180506030a0b1018081b0d0f0b01030803180a020310020d20040f0b0c0c0d0303020d 72
    0xe0faa8031b90170913100e201450074601007a501404040e1002d01c120000c0355101f212940d107102003c05503d0340031402d0340c2c003400101d01c500000d004d0600c06545030301075004e00c6060200107541c214058482c00d0149082d0500110314042955802085642004d2907e82800149000209420711240c0c0c200b002203641c9903110050003501c103480c0380c4a1307142d01d4000210180003a4503c42e140a00804c0800800c4007002005180113682003507600c1c07070300d0b5140c040c2d40002030855545a580d02c00700140500e0072480e4804041180140000c18050342d482e070f212641a201e110003810b00c1048050000d8a001600307000341d903885528031801081100121b41c2c2c0b01c22040ca0790031381040707980b4500082401400307404410181450419075001d4074412600d5030000c0d5a503401c40007082105900814400d54a1429900041c84070300914164250f034200701c011103007694464000c0e01050540e007000030a2000050058a01040c2900d0042005441d01c0d0304201f54002285021401c154003080446c000d030055004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881909532 1250 881908282 881908301
    0x901020a050313081509101e0f1e020310030605071404140a0b122202030a0c170a171b0d08090106091e0203061c14010f060501082404 59
    0x2c240c01070509150b1207500f4803100301e0030003075454460705c1130002109011894541c00c0e04000d0b80002e40c00305094082446c04160b590140ba003510b066294000c81c0d0340398000c00e001d615840107031001051121581400c901040d900703c50b4051070750205100042843e41310b42d421441030305290602001b8250619015805600030a180080c580201d94941c2410481d580c081d024400307005042001e40c007000710781001c00401038646480c0303a654165076030302003040ca201095000360646512800508107058044402e2107810042c140b0320084100b02c40c0003054440d000c55019069601051107082c1e140120b0b00078140004603244143c0d0912824031040006883c9082c072520740c000581380a9100c14212759040c0c1c0038034041400e0030500007180d140c041004003c2074030302c1c0300143c49403103a0011030350004070f40d010b48202003102c1240400f48441016401d0303c1000d6107000348848056a00240e05642c10b0b4030810340810240e5010a05d0301c1d02e4451105d01c4181c9001d81c40c030340341042100003029258140c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881910782 1250 881909532 881909557
    0xd03030e0114010305061b04081506030601060e031009050c04050f16031b0c050a02060301080a0605012c07270302040f0e0a152d050f070203030c0901020a0503 70
    0x80d010084102802189080c90100710045a150324584405846110003080e070365a400000808022281c0c850064070040c1145400322410345a0b01c00303100c10000c00a803613403441ba20403140005001880341c50b07002e403405c9001d8050500706a2441c02000903010103201210b25014541848400313440c0c502c6000c1c401c41e201c00c03001f917650034001d03904000001c50b06130300c03401c0500305100724903901ca00c250401e101c4005841c1000c7c4400650405030708084030b490380258092320000c00069241030024000c01100d028000401050745d0350b10001e003034880b07118200308006081840c0104c0c803c002400480d0b100c0d04a00b005034070080c101182e640c1c0c564040e0458401800303401800d10550070075215010024540680400143d10002c2030315075070301841e1100902035040003202c48074400082e0007035a1074007a074221400301c0241b2809004519007036018100a22450b000008024110b15804a8080d58503a00a0351a5071580c0d0b02e0b40446600014146065202d05824040041e034108001d000699202 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881912032 1250 881910782 881910791
    0xc0301030204141017070b0409060f08150726010801021801080f0c0f070c0905060f0603060a0303050f120a0c0305090d210b060a032406090302040207030c020d0303 72
    0x184100b100b00c40608038031851002c1d20300204100d030104000365009903250741421002082d210f042180ca0a00660417040040c3d0001c980000c8601d510b4021070300303940800d0384c403050580c1c8844070f4954031845c90f0000900c10b071162303000c0340ca0540104080242807149004401112022909000459000703900501560394001407400c4214501001c2e42d16185003483c2c40c0d055030503c200c60110300c0501900385100900c0005004214141c1034007110000c82d0f1002c1c5410000303503580041c0d00240b8044611074010060300400050a10b004c4080741e1082e2401403507090468250f84080701c41e90058121122600c0d810001b5007052109800200d108800c8800301081e46012084001d054a00c09005c80c0116803044003111502d5800c90740f0229003107a1005040c184200b65041400904140050560482c0c0006400d00007140d0682220601d981c0401d401ca00750740c40c1c0070702e48190b10700a105010002e40000c0e4244014a85038000f044110701915114104510320b800052128007040c0c400c402080d81c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881913282 1250 881912032 881912039
    0x903020c04050601051c0b2e0e09240102030f0d1a0a030c0603020d06090507180e07020a06200f120c0412080d0e16090f0c0504030f0f0b0c0301 63
    0x41c0591584100d0038a0011b0500300c5940034015a0001800604c002d1500c03104841184c2d2140b06c00028107943e4081500c45203000080811480d804640044002541030741003902d181c200b141409000310111002d00a00c403044001c4040200c50910001341140401c1044e04041190324015204807942e40c0310004400055000344884150310141442c064400d00e60b04001141146904008580e414180980c3c0d42c065200403000030b10054019075865440c0034280300509500100d03220340342041a020a840944030a03400c420075404584c3c07000182d00421071600091400d8101c09003055508042078803100485c41c42d00b005802001c45000e1a141c041380400c40c088451109907042400003009a16050509000c003078840c10303140015000407000103aa0507102038582c008003036008082d0603208040c002c2c0068021011103441054011400e003486051601a40c0c82048003a03040e5031605803902c0c1c0345079a154000300360781d2000e980c1c052400034035001098071060a07070b10461801454682d207604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881914532 1250 881913282 881913289
    0x271b030203010f1e090f0b040804051e010e030616110703050303010b13091109040e0309030f0607030e1b12030408031c061203090e06030c03010f0f060501110a060518010903020c 78
    0x104c4119043e641800c170104c003c98031980400f400340b0b8211417042140e41d00d82c18080c1c824401e55010a800c08807056504c4505200008185a902c6003661a4121111140109652a581a600d81c65131000c107410782f10085000d00548600f420000003922403c0d031307076600d03541c2c00c43d0000da220a6030b82e0780c00101e52143c3c462440b070b10700240010300010080d40c1f10481140d00e007806641e08240c0625034079142c0b01e4119000304265000404001c04607200c03003031103000740e50321a4401c0d01c2c8000401d00b040075603483c100c00401d100d6050241000301100f001c40b40c00801c0b0540c40404003d440781c4c0400c100c04a10202c041c4020813441c00702118444c0086c1800210400300c41455100e49000c0c0c123000790000000e40e01941080481d207074000d105c3c066480f9040080e00b0304103032004850303040d80382a403c0860180542c00210041080d4841080072940d150015a006200d9800105040d001b20b442c48000604540c071290b00544490304100e0030580b1046034a084482160040d0096442a5034418481c40d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881915782 1250 881914532 881914571
    0x10e0702070608011a04050d0f0201030e0316060b04021909081606020d0e121605100905030d032307081f1d090307080418271b030203010f 61
    0x41280c8000d0803514030346180140048018020000e00100c80c1d80b00382011140041900c003d00801000c40c01311410038507000c465000100f0040740030038102848081850b5000c016070b10340180ca8511340e01d04423000d5a03418000d01060f030803140e00640c00d02100442c0500e010804031200503a4491681d500c4c100b00b466071614468030410104c1ca0b81c0070805005866011442195107619410300004101c0c041000134450b159108405840c1d2080c10300100101e00c1031401d0710211041036468031039800081908403110402e034040c0f640c0540c000b003001c0c0032040c4a0ba000d07071004544002e17504010320601a0300003032078406030307040d0f03000031100b50034822100b100c0980030069040440d050700764189420300c48070b0064000c00005401c0702034540016218441401216861640322002a41d503c2c0c41e0442044190502c2c0301880d071440c9880c844140110180400c501c1c001d410324003401c1c820324607a450000a1500d0509007060400e4a0000001a02c090041840c2c2c890743c0380707000c05c21b008451040320700c03072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881917032 1250 881915782 881915791
    0xe0a03051e060a20070201140f1308061b07080f0d0b030c010f091e05060d02071b0b04090f0f0e100e06040b0f072607080a090210080a0f0e06010e 64
    0x8a180079500c602c5413030110b107a035040b000d0388018070342c41e2403045c00103075009103183c840784d48401000070342c0c2500381d054000200304056240115499040c0c5039207045940711012268203800c1c0b0702d0002805c403030000394005444050720070701c40d41c3e01d000c0400b822102c480c0c1125940d143d149488040c2186103240c20f10168410110a10f8804c031003a500c80e00c004c203a0a0700744141c9100031380841c40c80b69036102d4108100e01424001d03080c19a07a2001c05079081c000d5212000503680003806002c030210340407589500c041150944030321142018280b5138190020310a18100c01d07131040d036079020105403003000d00406d80700c1c2001c032014006044240340c144096803584414030815402000c00c10000034001047e00b41c0100c012408002035648031a0169000c140c107031014000403000f1540c52502d50404190148212000d0350340c6d49458071110818001d442d949440254001072411001c480284110740d11940501c0240740490001e400304544002c4a02181203198507802040c01442207545040e00c03280c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881918282 1250 881917032 881917051
    0x60e01090e12030601020f0a0807050d080c0927040b2a190207030b090d02010b12031c06050607060204050a140306070309050a21021018030e0a03051e06 67
    0x81030300303503203064898610a2684070340760b4002c0082080741c0d1080210488440f900c000b181e43c15029401c0142081d0089241210603100320180f42e00c00074865905140114501d00350f56003043c0b804c400700002d0214014254801b02641040b01d40500500312005020300e02a035600c02480c00c120b141d8010b00786104050410254200d0b200740d041e10004003c43e4815401013003103800d540e2103480200c0c201001c0354005081c40201e0020b122202c41d000ca01c0403090a044d4000700008031200c424050803010500f0070351003a410074000d4400c032071880c803030042c1c000799101da00081e85911b035000903d49400c43e4a0a030f8800781e0100d8180024109007500c04054003100c02a0845406488002a941ca40c001e26004c101501d503d0002d0412500300411500e00382d0000d03980c2e08080c40c1007606082e01015030403180062003641400e50b00000d10340309091035144025259803581ea045d450035074480075404c0090341c11450040000004c101d081c0b0000076011110700740e0030b004424140d0518038080014001640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881919532 1250 881918282 881918291
    0x20c0c0603060a050d0c0b04030b2508011230110703331a0918071502033f0c0a0e0d060e060129031305030418060e0109 53
    0x1035660fa640390441103035011a0798507070341313442031030300c100440324540c4884c03080c40c40840c0c04010000c8801c0014462007003040880070b0b00c80d0301079458207642d00d1010381c00c007c5400c007030044c0a030312158490742a40d54062a03050920300c1000d6140194161421140c8910340180700101054550043c0030b401160158001405818290345911140841114982e4861759a000c22144044120300b08441401c100040400c4442520106580c480f45800100da1042110717000141003800c0384240031400b48203102c01880c4060906598140d000c203561184c0040d440f0038450384040c99001034440121a0003401a13402030300b2242c0091286003425505110020340b40c40403c148030f01c20f0010317604510042c5c0703000c01101048401050700340154490141025040c5419000f0000700002c00314100d45942c4103400200c0004000e4034052841e407948090598000c2002c03c09000d120107a08403450300030001e8928155446200880c4c0244203000882030545030b000800c00313201d101204030b0040815910500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881920782 1250 881919532 881919541
    0x1c090c26031801033c05090f0616020705150705070503071203050a050421120f0c060b150703030b0109060504080307030c14030f030406050705040e0c0c010915020c0c0603 75
    0x22140840b14440c030b41015600e04500e8100324080068100d0007141000308901020502069050014440700360010b06042c0008241e001500181c14402d0041c004080c06464494111001820580600c104214032442201107156035608107448404107190161342d03950034062a0007401e080b036652041d0b00c00d4001030010040c0720020f139030036003046a042c41c0c0b06a445002107016211030190382c0100c0c1d030102c0b04801041703028418a41511869004204034400c12014510840b0341e05405400340303001400d0000c101c000034080d41c1000711080070042004403608100780565010782c12081058000030345a4040b0201c6503000514040a0041d03403512034500f9081002c1d09540c1c0c0f040700b20040030800750500003018000c00041c005440754000c400d5a64a00c0a002d00446c5074000b92005d6810503c1d02002c04c652500a01c1190122181501702c0c43d42036865152910b080c3e00500320010103035481e813503a42e0005541e0781c03a0000902c2490001a1620f0000265514003826a070042d80180070820601 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881922032 1250 881920782 881920807
    0x120709050607060e03040e01090e0105090c0109120f0b07051902030f180a050411070203100209150705010905061003030e24070602280809010605061c090c2603 70
    0x2219000d40164002c24850f0700e10941070314501c5268004000c455200c0004500109c540c5c1010000040030340080c489038440e082d0041c2ca40c1c0d035940c2100e02041048908004e0001e100242103082ea018100804038100d040d140c42e401c4010441d644000128001490805c421041e0504000c541440c4011820300014000c650140d1040d61045960b4002156600f16140d8a040c40b0f03401802000d00148080c910f203041c134844c00e0300280d104a101e40030f030b4040c84440460f181300361000038900030403504142c440c1c13070902e08042c3d200c4c41065499549074a130020104d0020007605000303014500200440526604000b0f02005001075590b2140324011071082c0d0000001c19103640607041180d40c3d036660503051614070000d01c902c01200000d0749106012880f031040300e562424605180342c5900116a84101d041422101d81c1c2c0600380d4800000d10180d00003180d030798450340000400c04e40000e00c440703194480204c281315551010a0040c9c00602156001d4155500507584140250041d030070500f00b541103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881923282 1250 881922032 881922037
    0x90e19030804020d2111070504022805130f030209010501020105040507260609030d051f09020d091b0501030b010c02031b150a05030108190321021b031207090506 71
    0xc1c4c420071164007884103011a6070b005c841c0c0190036420403d0309240c2c81102809084c0002070301c07105800f6031100080c050030700c1d008540605035030b011001c19480d203000b610809082452440400c21005001e81000010110f46800190000581e80c03150035103144100076164905070421411039051106100015100042003402e0310003444940d010702000c1c507a80780c0c0246208035150954854a010b00c188900c003c001031506540d0000d05110503a24081a105180c81e03070180d4a140320385030307081004900303003640c0a01052006e81e000030414180c00d1b1540d1031802402c029842e5083c1074000100099a098401c680c02d04000f0b0a10040092894002a40700c4c02c0c0a80045402031148600d4107070369980300500c200101c0050307031031929507061000003040c80d0424000d014043c8903641c010441501d50070708c000d00103a41075840b6805911180801c0c01035595806103202c0c802d409205040e00500340305105501c00e88a800103548a0079035400304100c9200190058080c40381e18082444141c564104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881924532 1250 881923282 881923291
    0xd03120b130c0801091a030307030f0e1002010f0b2b020f09010f080d0201110414181e01090e030a0c0309080111070209150a060f140301090e190308 65
    0x40015418040304003141c000005504000d2980303151441d9101910340110b52241a20403010003007003200080c0d5415a41c68450302842c541c182d005020040001e8411000300c04500b5061604803041c41640000c113640012018076040581d469103583c294009051042c050300704021100310758001c0b5455001101c08125800b138142c0d280700d25035000c0c1903481350700707406210381c20180c86541c0c0c03980d540d51404180c1046000b100854020140b594802c01c0c07050050f41011201c103099145000d2130000003481d882020b003901c5400c03402d02603540b00b106025006591040f0595051030441c28142e041013405000140c122031070441c41e100715003070b04030b138008150340c40e8124078205860030722998103003a245090194802050b540c2030104000981c84403501402600b442a01e0605058031401162441c01c410000362076017105455034100091480ba89080c0d44480460400c0300c450040400003403000d5000340c10807100d054403070b40000340c80401048404c844171441c1c008816000050354000f8a007440c05007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881925782 1250 881924532 881924567
    0x30f030c21050115080c1801110601090b04151a03060a1502030a080c0a020604080d0207060501080f0d09060e19170f0609070e0f0408090607060603020406050d03 71
    0x840108090103001441c2201210349030150306000500108805003900740610a20640300030100c40605005102e81809403905034003d900b0182c1c450000d84101d44510060380c10800614041400d451042c04020f010b00401e0b00d01003568402030341800199408085a1001c50304090f02c10847d0305480f180c1342102c10044488a940e032b448110002e034044500b6003041418891941d01d440d80c00390000000c02980703c0584413244070390b0303a2003501c4445d40a001044030268001c0c3d800540051400704c001d001c8460b110400504050380c41e103e043c1154026004422164080040029952820824401c025025142015100d0f0900030010500c5010140482c0641e4840d080e501d84a48440404c9003d008564070200012541000040d07543c030a441a800340303400b5a402140340c0c030801144100c10b54242200a0b0303001d4907804514414900004c01c15a00c01d070091040b07060740e540d40002810707214000c080203c0c685040d401000122820381e4003aa100768003402e40a0000303030700b12103043c001083c0d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881927032 1250 881925782 881925791
    0x40c2d15030209030304090c0f050405130f1b0305040506061f0e01031e1406031207080c0307060504080304150213050d0606090c030e060117031c060305030a03090b060904030f03 78
    0x1000740d0280c003503184040d0b45800049000720340e07100260b015030403541445d0365158403d03070318100c1500c1074400c6004160300b100e0300048100c075030020b507007080e06054441d40001420300203640b244d03104041c4c045c80c0384001036151801d100c14403400f040520740003501121204d10410088011f0500c900380358003144203011030b200c00040907a020ba4418001d140c0044144000b000700c01d00d442005041c1031040129a101c1d91000c681c040c180080c02142800c44510402d1414900d52a0901d981d0050218540700d80b00030010305001845034007549000794494038440307890f81000d16011040440d00c101c00e01400b48103100c41e181d0882c1c0c9c000000221081620811003d542c80d0421001501c2c40390404100ca0b0704003104c10b4030044c0e160b403001406071000400d5030802e989891a6004903095884080c1241e4024445178842e071000500031800d0702c0020600289559981d540ca600355081005a0408240d0780c2d8452401e11040c8850039505c224201d94102c03603444d00b560094219454040c524040640d02d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881928282 1250 881927032 881927069
    0xf010c14030708041809120e0a03051009140105040506160507051b040c020a0203060106030e031b15090613031101111305010e1009030b1b03040c2d 65
    0x1020034544010000c2a26600d022508041c0c003203610a01c54080c6104180004100c2031500b0701c030340618150302c030a90b031740741d180200c8044800da07060008280d404080c0050010004000f00300f1407004c481d1420000c2220005810720074654081c0ca20000d4050341030000708400a60040707140742d804804005010882d240514045416006070a001081840f80b044055804c528410a50040d40000c803030034000c0104056049840d02100540290150700600042c8000c42c080e412041d0030b4501078040700c1c00c1c100d0001d181100e881c60240d26841c81c0d0001244440982d03641c0c0451584001c00c0d500900040c100002540e5a66842c58406001c1229080c8034442581082d0000742c08103040414443d1200000c410320002101c103403141034046410140c00b0001c3d07082c03841020b10034440300c1e103500450500d152101020342100815400d10b0804801b0350700c0a465094010354080c0303004002a43d1064201281c071001102c0b03000748a400004240700000ca070744c14004040f17094841004c09030251860 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881929532 1250 881928282 881928293
    0x120b180607140c0102030906090c01020d0504050603040609050a0f1502030c09121011030105130c080c0c0a17130803090f04090218011719121d0604120b09010b0f010c 73
    0x20740f81145009500010038030202c510300144080c054041041a036022001d03050041ea0307034908075803500700460f01c04e1108010501d808009107500c40e01a0901040f0313503015940e02810641811402c42c0c400d440106903030300f44482141c0000740d50104010031440c6041c0110365181d94000c0040300c82c031600360409403030440751041c4824456104e880005001134090220b500d0300a8009010340380c06441461010804010a070145022041a945502105440d5404211080da01c0300b00d108007103100390805800000c00560b0b842d0440020510000d484541c40c406507070b10540154040c3d201380e402401510225500d4a032000b01d032040c1190001242c00031b070700c00310341c986e41124a0311010000c01800040c00c0c6001039402a5505030000a50f40b516903100592424030300e00060180400c3d2404c1c219400c1a401020140403090f408c800390340c0d5940002e00002d4241d40140c022549242c2c0c02c020401c20082c0f000c403815003141c0050002c0c8241810300c3c020a40148071748804034104900011800207114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881930782 1250 881929532 881929537
    0x50f0a030603080f071b21061401060806212a10020105041a010e06101e09050a060503041106091c06091208040c061215120b18060714 59
    0x10b82c03007065140c81e8a1981300803007890b0844001582d840002d40315420003000202610021380da082c03002210380714080101207011761040481100c10603943c40b00004441301000425009107036664403001d0300d140410501203248422030103000901c64805d8100d07001000481d4485280e5002c01210380242c6505032641c140160000303a907500700d08000c402c108860341c19005644074500032030301802c030282000081001c5003024840c4c11510044034011035001d18055450741c031640300c00e1500d15402c1c0c20110340641032600244003e400300703202030401c1102d030034113121400c01001c1c541056810751816858031050240c65040d003d21584c2c001840301c90550724410407142008070b002c040c40d1805003c0c0b0f4400e00908079a0310030360300c3c840d20540d2801303d2441520080d204076406005014154540b60050301d1908134416a510200e0300c40c80030a8607000e203c01c00d0b80c0104204440041d052080c1c0c200341e20300b00c002074184030560b49074040b401a5030070001103481e001030240c035000c0c44056212001d2681070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881932032 1250 881930782 881930789
    0x170f090a03050307031e02060403052109060f090708100c2105040614070f080711030a1706090c040e0a090f050c040605040b03100e34090c050f0a0306 66
    0x81110004001c0c80800009000034174469252000c03007191850a00b81d006460814070700040c3e00100001c4c0000c0c0c4600e0140010b03408001e041036403a000d80d1907008000d03904581040d074035480b400400200c000141c900e41d03080800c000c007030030400d42000c5030691207000030100215040e80351101c100c1d40510615211003104c0d01d40722016650321085c030741c01001c0c19081e0740541d845418822600c08080f203403481103003d6240313501c2e180b03140d6010400c242c2d04000014010310911680345080c8260f15001c0c00200110f0300301d5503c10850b90441c20410035440d0000e480c541c020403442c0c0030444881b003440100c03029500c030003c1001207a515045c000c4060000d1503001001c626244200c4c03010060001400441d01104503814807101c0d440b81c003440100d03201190701640c1640451248089070060f030340001071011201064964a08000030b07032012980010484200d000c00c4501c81111401107110504041c2100690170b2101c0701030010b0091040c0a42c070742c40800300c00001070804580c0c0c040e0380294000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881933282 1250 881932032 881932039
    0x1d04110a0503120334030f181e0c32030a0209040804080d0909050703151406090402030414070b070c030308150d060b1806090c1c09051f020304170f09 66
    0x400f0b100c004e090311048480840b8801103414811f6203483c503011401a034071000702d41090000880d40d5610b80d04e000e02004119080f25107018404500032401c142c4094010305404c852084000030a002ca5001c00c16050300c006551100c002340c804d44a40d07021902c0c01005404039a144590345071810040b00d140300d240e010f104588104544940c1250708582c0c2d0700106c070301a640801c40e581c1c1c0c540341030b020740d55841080042810a80d00a0000c200c440c0145a01240003504d82420040d080010608036803064509031485035801004042849e4100705d5000900110128141803442699804110098a0000a0500030b40300e0010381c42400114a0701400440201000003448850800000070500803044501417040c0c46016100b160072101100d0040c42d014004001541d51032995a81035080440b845252100b11007040c8031102450240da800ba600820103491203940c041c41c801c0c000144000c04841180c0103004100110b404007a1031000070046030402c60780e400f4040d008004520421031210750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881934532 1250 881933282 881933341
    0x30c120c16060c02010305090d081f03080409090c15051c1107030801030605010605071112120c0606010305061e100207050303070302160602030418090c1d04110a05031203 75
    0x3016544038000e031450b54000c6c0c07400c21054580c8401d440d2900c400c2e11200003ca01c41901040c00b1a842900c070446044180c1c1c1c402c42031980300c0e910330b402980581e001c0d00350325480724201d1051010040c101d1006282803040c214a0441c071440c00b0f008e900407074500c210400c81d1540c4124041c0e010360052181340c902000d400d581c0304014680900041001c0c04141c94140c0303407000100300280150211550142c010081600200c0c4190400082d0f42c620b407071016441c050384106800048461001e4130700c44642e10003526103481c103400014101c51000b49228451060790060408041c8003000d941000c040a90b50a850402102d2060349445660f230310494242c40f0004901c014180e000c6100000107201400e041d10700c66660070101d80d20302903405002c0301c010b115400c80d00500c034240c1c46020003512512180d02d4160f51442c001011184c0594130f041000010010081005010b030316250032150110341d00d0700158100740110746c0c1d8200c80e4201c1c1c01014000004034485812076089284055032034102d030788 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881935782 1250 881934532 881934539
    0x50d050a030306080f03090402070602360301110d0b01030e19020a0e040308010b1606020a050409050f04050c100c060207060c090b031e04110306070e0111030c120c16 73
    0x1035960803804400d03000079142c4080800c5010340840d1000000d0b17513050045080940c240c041100a50000304100d41c015401c000f290710410103001502c1854007004048081500c0803c004040400d0b0880c41d10b11a0f403400c040346003550000300560f590304046110000d0604013910058004102c0d440345c001040c0300702500c0000340c0d0083c00c40110181e109803810841583c0d41c403140481c020040da801000302e8107030f00043c00f80c00c4001c0d000d000d400100742c6030648491f081c0d45509080f030b88190684070001c4c034009001d004204160288540110728107500309000e00e070030703120291101003840017075214036446a551a820b070b11403d40481c0482c0c102070215a14011450428010425152801c2c04510b840c10005042e00d01d00003a20b1040c1017444040a9103074240341130380e07810300008201700d4680c000019500a9034408100700f52082b00b003619050074080039080090403010a5000c101155807040180300b0b141100400d610b40d5034842110300b1a21010724900326400c0c0f03c254554507491216400001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881937032 1250 881935782 881935793
    0xc0b0124111006030b160908030f030402151306091707031203020f0d021206030d17100e07021f0204060504050f040615030b011d1f14040608060a0b0903070b030a06050d 74
    0x24050606044140d485e00c0300c40c20256900703a00c7d4460f58400c5e4005000c100b041022178030046038018401410420361407061085d05401346c008100000b842d0041c01e50030302449401c040304101170f00145950028010401e10407540d81c000c2e5000003003030f580541912600c82c42c026010780d14964029006151260356420440c0025004800300c034081115500200f9400d05002c944180c440c0303100d40c1d40268541040c0c000a02c2c084002c0e1a02858070040c4030002860110394602c81d0141640d5805417040e0544582c0c100a20000076000c00689031041008200054014003160210303075007076412510041010700081c0041103c0c0d032114041e00c0948180955499065100b40341c4600e00740c90b01482442050f500ca55034a8401e005103800008424030f91100c0140c01140c8a4400168644500d5117148001e04c1c24207a04a58440d5020079015420300c00a4034211015a01401000c07080500f40b120340f100107655000d2510401d01d170800008081954070304507401c101e000e401d0150001c240501d00d40b510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881938282 1250 881937032 881937053
    0xe10020a0501050f010605041e050d06051b03060a03061a030706120c0e060702040e010e010e0a11060c0d0c080d0c0c110a0501080a0e19030c0b012411100603 69
    0x101c846510b002c00090410903010002070684549603034003030805007020480416085004103603003010800c540000b074507a90703a03055101494840e1901040742c1c20921150f402c002e4130b20b4201c40042c2010b004000d0203480340c44d03120341141c0c2c00c01ca01046000208144090107040f03541920b8060007107110214191750060820060703204514410420211044001c0315510580c0749995481002000200003510b0550080e655011480000049010400050b03130300712350107104448500d4000b030344102e0901004984c0d1480801040d90040d14100414100603102c06204e10b088050108400c45882448001400d8594010741c01074200807441c240da00c00b0704041c00e040c2040f20100031400c017081c5035003021490a412110182c444000c0f94613001050030180c51011849155440340c480c6c0b100802a690882d0300032a802926908000c1d00a4103081403041c605030403c500c002c4032001480c890303060520340c00210100700c1c43c2c218001d601e2448000c1c1060700d4054000c50581c01c0070b81c04010300580085 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881939532 1250 881938282 881938303
    0x150a03020306040308090706050f09130f060e0907050f03071a1b070e0a090f0b190906140c0304110112091208090c03120d0504020604170303091b03060402100e1002 72
    0x207c5040c00d5a0f203004840c58484c00c412582c0f511f4003031040b084241001c00401445010101d80400c14801544150701251082d0b03005441998aa02c284040742c3c0702401000058101590440020015030012942d284d50501c01c103040b0000070781100c4261081308059030810350303980209584210350380300780d56a14200c90041d2400c420000011410030385080c0b140700420307030b1321070505843c50040e81c40d04070458600905510085d15440c0200c1034404146c410020441e1044100140c0c2d2940408000c0740190010076912500340100706020202d0f20214698007501d8092070f0000c8010a40341d540c0014040c05e99000305424000c145a4128a40040402c3d22407000c001c201c075480040042019a541121f0441c600c1a40c0100490030704996a80c22003035002d40060b01013440d007991103440700380303141c2c0e0300d0301205480e0404024000c003c507041c0208030748040c0b40a1041800100d440010340c5030b04016000070f00c9036403d010344640c414041c02c40c0b0341c807101c1c0003403415003007061100010751120202d08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881940782 1250 881939532 881939551
    0x10201110703020303071403092d2a010804080d2a080f0603030f3c0a0905150f0a17090f0106090216080d0e03070c05031c0206150a03020306040308 65
    0x1ca00841040401f010b81e88100110002045442c007248401c82e020034030502d03040b00070514103d160009400412104c036420003001003642840c0481607006c11000021701081c0c4c1002501c1d000d10012414000903108050246c1d00c00150b42c4111a441880300001d12004142c0c820034001c88168140e044814140700ea0401e04219605659150070191207120b01c0300080060041800b41c58408006d20340d26005e88100d003901c0001003d403200310b0144107072000d500c401558000040a49070250b00056800040200395400c3e1030f203001003c80c0150a00034800394410121000c1030085009205410406003c0103082440c3c04a08080d20815180d415944070140958248003001076940720610031100e860403500a0413045084507610380e00c10707500c1026114032813900e4000d102074100043c0001e0084602c0385844801061600701410304103207100701d40c9004080b0007490180020340202e800f9500030100358054281c0000c002c0021588003030703604007942600c951000c1104060308a4001402a501c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881942032 1250 881940782 881940797
    0x91703010905090a05071e09020304050c1201060f060806180106020d02010c110601050904020303070b130606090c140c0f030d02030601031415060d020d02070f020112020f0906070201020111070302030307 89
    0x3803c80c0b03584c40c4614500200668081d41003000204401100c80c4420b1310402c0e184400d07540d90346404c5059810544040c0c0320740e0884081044035240c0501140c200e401b075903000388040d07440c0041c0090403074800d20404080c8070301d8030001980c55171100480e85140c02e545689110658440c43d00035510302c0200d509901640c40c040311034100c540910903000c003410340c070b10041c50607a00382824484e50200c098404c0780c240c4000d210b032000141000e440140308010032088504c0340f8005060100aa800341e909c0a20028940300d00084640d511043c04540000100762075513403810001452850076500b00c40f0502d840c0030216400c3e86010058005600a20003640d00f4170050355680981881410151100403141682118a021909149001e0101212070060050500100304030040984e0302004040b20700c0540c0320018421580c0088284030b081c1444c0780114103020100b807048402d40704d0545000d1068130701003030050441e0300c00d4200304001030030700e11015183e02c9a860003956130381080d01d1407004184070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881943282 1250 881942032 881942041
    0x150d0501200903030442020d0503010303050904050712061e0905070215041109010803030604110c120f0c121305010309030c03050705071e0e0f090a020112091703010905 74
    0x41405503803500c0c0c2e009003c0c2d46081c0c5010040079050b900707a41101d803003180719000c0d1140700440d1281d005d15034500380a0f040e51005000300c000e0074283d040f200541407240610040c00802d03481829a040f1480a890024403a2100c034416a140074208890207c414101302010809460343e682d00c2440c414080c1c2d9080e445030b02d602000094031402c03144030005a0003013032580d40b03070308103140080d4005000318041400707042400c5c04910081c0090b00980b40c00d034400000d1091500305485041ca5008200519a04004400f6000ea4942258101140d910500461801d481051034000c4544075080441100d0303400c13000c003c004a268001c990100c0310300c0010280000c45500034062180c00d01d52558440748550000c0da825a01d5400c1020141c406100f000f034080380d031505010300d442030380304134140c6070007442e19100342500301100c010b148880383c00c3d0540c14000403850005414001c1a42402c10ba09403040740ca141400070820200081d116158043d56000112000c10085061700c4400e0024805503030ba = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881944532 1250 881943282 881943341
    0x61d06030c0d1104120818040612050f0d020c0607150f09020111010c020303060105160609080c160e070809190c050a050d20010905091e1e040803150d0501 68
    0x3580318401d0800100d21070100041c401b0b8009001c8118001d0412680f141e0301000b007011200c240d00301c080e060b070f0107034001c00501004010300300c0840e14040042c402c001603003000075150200e103c1000d0040e007000c10258108056451000c4050403d01c604014100f400551000542001c0300180d010411049550f5410141030191200c44000c5400661454455400440b49a8489030500c01308124000d10140051400d0085410090042410303545540b085241d180c20051007024105490100752000c00c212032030413418543c0509030703040004040e0b4400c0b24542c280300c9908104842007104e50031103800c105c513408101042c0e8805446d045003032500d030002d20413094003620300a01408503040104c10740301400500e0307400c0720506140465100c5c2e500c8000c52000001030315140c1500380307a15100c2446513001c0e820300c1e900c14150240c03140b100301100c2103500100000b91001c0c1290100200040c902469502c00e50100c0e01d0240201010700200c0c00c0443c003d10302c0f5450a110410307115210301ea00b64 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881945782 1250 881944532 881944537
    0x503010e01050f01050405030d08071d2b0209070908070e131101032d050a0506010f0e04180305030703110307020309130f0623010c0b01061d06030c0d11 67
    0x18902445215a80d080200f0480074807040c507002c2d81004010400800c0c00e8401f4404a10318084544560007181003201e07003d003a5404031000766460b4018001c15001c140d81d11070000c102d813600b0015011451820f41c5420600125583e00a500001e80c0001d1081041e444202c0c80211141c0310f045d18009a01c50302d40b032244040c142c4900440d84511068400824541c41d0441803000d014100083c1c0040412007809407a00c800e0301c030100781000380c40d201c02d00000324012503901404608003041145446800030b0300c507248168040b0204140140c2c0004503403203503401080c04100005218400503540c1c070303000344541c0c0304075030035070010f070034489400c41003110311003031f24040c400ea40c014508008904052001c2d0502800c080c03002161102c0c400e9201e07140c948035500c05481071900001e07102203919103071aa05260101010704104440b0a0b1501194515061505441301031602e440404e10070b22220040d80045100664445070000a01403105000b00081c102034041c030100f44032000c800e0301c8007401c2d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881947032 1250 881945782 881945789
    0xe0f1b010f0e0906211e0a02030d05031012082508090d03182606010e06122103010807061716020304180501031e0c051e060325050301 59
    0x42d01030b0244258600e400d1142d980d000ca00a0607a0700a044007601502008510180e28011034004c983d00c4914008003401700c0078218031003002441c0244403071b4003190b038590b41b0074800420044080042540c848468141e0380086c038031b50380c0c003000c00413440c2814075039644403c18210811200d00020304204403240003405034980c1000741e40341011911010f00c0046d07000070301d00320304206d02c00701c54100f09010f004294014040c6240014500009501050302d404030000650342c83c2c1e404400100644100d00c00c0d241d03030041054403034801c0310184103500c91400c0c140c2d00c1038050b451100203420f050100320401850403529203070100c403030503507507400261100d07400f201910010791020380000b05030740b000319034101088000d88116442c00f41c2c0c07004110b40c0702e914500c2400c40f85881da40100306000c21905a0121800320307010340441496180c0d1110303029052031184030b0040d81201c10092000e00b2044146a130180003030110381da01d00e00a0091200244041240c7c10241c0404400c03040750f91080c020399059 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881948282 1250 881947032 881947037
    0x20301030606051c0b150103021608030106032007030c03090306141006050720030a02030a060507032a030e07050d0503030a0e150a15030804150801050f010c020d060e0f1b010f 77
    0x5911b6601c921003145498420343d5040c19020054a804641161400c65405004000494895050010080603030316410409000401031407607904a6640d070f80e04541c2d000e079250911008242040c941650360190707a0384040c0415182a010084550341041224807401201c0f090080707050b01e83c20140c400780181c09014094030200303103c2107811480c010a42000b288010200c41c0c10058581c006031412410a5045400b030b81c8480030b01c059150180030b003d8401808420b1700c41c0c02034200100e50345090140c02b80ca01059103610f8003010000c4c052000001800018062200a007418100103941e60300a0725000103151410001c03502d91000806c0341c1d8141ca0000000700004c1c0c8501c82d154000d40304080761079240f0b41220b10b00100045c11403006000610000046485681000b50081c201040c1640924004c403d04003000c0c11036a8400c540c041000e5048907003144000503030900d54010f140604c0d102030144100000b61040c0c0c04001000d41a61465030031044c40116140c004443d09010130900501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881949532 1250 881948282 881948303
    0x1c060807080304290a110c010306121b05041104050a0b16020904210c03030b0907021f0204050d030315060302120a0b01030b031e071205100915020301030606051c 71
    0x100460b0149a580d40704d003a10341100d01c0d42480f4140c201154400e030040c0001c10b8040155910194080c0060510b1950900f02000040e240a083d050a02905080140282002050750b40da140c0760b0310f200009042e010340200070b40801504030381000d9005000340ea20440a00000040e260412000c4801c0510b80d5a01940c4141c0c0903400e0001411000d8030460f90045a410100304081d0240c9212450488558a0043d05441810060210340c10900d295010358250410084159000070b48055010884d00302c00b00e0058400d01208000e015981100d5440101c44242c00c090541c1500020f0030352003480d404880740d60303442206030304030311078074502d404810310000001d0b0358806c256100304a0b5500604002c1800440100000c0c100007500b0580d089184800d50030070b010103420030850014103440041014400311644880381c0d05c00d0742c422072030810b80c1c40701414020084d492122402d500a0071905544a50716464024013420706802194055101c2e800d00407900761011003450b01c0141c00800d0a031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881950782 1250 881949532 881949539
    0xf02160b031f0f0b0a020a1e120806090c130b040e0109060e0106020a0b0403121d100e0a11010e06070c1a04030210080a0b0a080a02040b03010501081902040f021c060807080304 77
    0x4d855081409044103502803c002c04c00130408070919010140e0782144441c0419180345003248070b25241007404420028400108416911811003898000341d003040c030651900190204e8801d01170003500416140c16010400003050003001c0901030503200d00740d038280000303916402c403100040403d100310030041c0d01030b402c0e450100c0e0400641d190414028070304042610800e621810a513482c411040100002d0341d00000c0784503100b071181d0440d082c251803007484600007442c0300706e42d106003500d000340c403d10b05184100c1840e8060460700070300345000341046482e01705d5405c022204012912503240c048560b0704104d03800c004031004840c26244d00500702c5618042c410401c8810344c4005003102c07041603882c480111141d172407860348001048030300000c041c0340c140b13072040c841900c86020710b15009a04000050002c050042504000380055458000c0b4022450000074043c183c003249841c1400c0c4005006400c4415041c004805140303111010301450fa0346641c5196141010f01c16490140c20030300c01030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881952032 1250 881950782 881950799
    0xb060f030d0311040909080903010e160e0c0c011103010806010506090a1401121b17040b0c03070c0b0f06011704080f0f04050405070f08091504030f02160b031f0f 71
    0x11040140c3c5100c80c2c20301c2d0b217861002c02150220001500c0544000c2504c2480e403400340940440c01d846840506052110200c130130300c01d14030502a00100320510b20004a90011b407000350781c07508280400034441d015001d5803000c980e500030b0080c001d03d406800c00108190525034119000c1d48000341071200000e250124991803202c28904050411401860445c200c4180d80038403480003101c0c501d101da40c1c81c40c001c0003406070b0340c07185100e10421025408104c041400c54140303903030041d03030440c01035a00d96800d101203440b0305a08600420021000080c041543c41d103200d4540300301000e8840700740320050101e150540c40400c407802882d4850421591203d1003802010317060220390442c01c0390800d9140c40009045e91720407100c1c1c00c000759002045000d0749602c801441d401003800350180407114130380e6192510407003009002806002c024a4152032840c4200003103404041210b0104015a445480b01000345e07005032a0300000006440b02c45110f05136081ca41c00071280f00d00b030b0b1211001d240003880b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881953282 1250 881952032 881952041
    0x10080c0d050a1d01020a0905010e032e050f160201090f060c020705060c160f181a03030304030c0210030b090f1b0a030b040f1e090507051305040b060f030d03 69
    0x4001940781c40744408008044403581110f409880c280015846401900d40245100c1c1c11b5071000b03040040340300540550f61004602d2044040f881c0404280c0303001030008003820011a2107010244914100c02c0021020711100b18a0148200442a125442c10000201c6c01d1b1044180060503601140030488000f030707000d900800002e10140155007846644000140c143d4101200320050b54200c0300032003d600002c9900c03140507000444049480909148200600340d499141c043d18255440c20030003245004c66000c0480e0010060440340e40e4501485c00414072820b80e00d08a015050340003c901e00c980c001d0184a0742c8001c06000144642d494054033f0031101405000001d181c280084021107000c5210010b00a105042c6c40116812035440c1c00d0004079140e5665001c40c1902d400c40320502100410440b84030360b0700403000801c010720349060590426201391701c0903070702182110001c2428241a008907100704d0140c5110040c540c1c0e000140402074110720405585a0040000d03d20000d000341d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881954532 1250 881953282 881953291
    0xb16120e0f0f1f020606030c0306071e0203130303020f07210201081e18070b0301060509060a02011b02010b01030515032503020a0e01170d050316020a0203190210080c0d05 75
    0x25890310790f01c0c0010310b41e280e20307146240d0058203d0b0040200302d0500b00305004040b40c09400400f02d03480d289400078015005090708605c43c90400758031046d858400c100b550800d045900f40f2101c0a40c0d42e01d00030303507945000d003038506480c040d455000402041c1003080c0048030340c406001c8590004c60f54011121002c0013800480e843c150342010300c1c42100303081845441002c0d601100d060805040e4051880c0800d654045403074800100300602c04507501c001603540c012003d440c91610303190760f4030041e4050a40401c0d041c035100050900c19207d186d05400c61060140f003038a04010743c3d01c0d1501207009060300f8048881e00b540c003141700641c400040c0c5100075060600b2030f04c4029035540365400103100000c1e0340d1200c003403495113200610281c07040507107407e081c1180310014114106001005000390000805e0500c07141c014034404002d0900901c440b0b140254020261880c80d5a100340e400700641030b01e202a800b80258a684000e1035008410b8030380a450361075105400d002d984a243c0d405050002e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881955782 1250 881954532 881954539
    0x40c1208040f0b130b0711151902010c091e050d03050c0a030507140307030906120e070909060b03030f03040f020607051516031104030204050a02040b16120e0f0f 71
    0x4000200b00c450301848001501d0f10003001680c51012040850340e0f01302c940c21034031003030304200494000642021580070300220251880300500c41c5c2220b0000d07041c090f1511126000100700d10000d641c0c0d40c19444101406480d8481c201002e445018008822408203411441d14201610a008924041001c06a0b1912a10f0800e240c040034060f4207044c400800d004a0214501207022420480040c0d00140d40145603002103003052020340f00188404128418a030510500c04002150340ac042e4011512500480045074485a92070322400014030403070f0803c4c2c4050b0318204090301149008000c98020100c450b18450640c0c60b280c80e102980061a4012a4000000c020381c400052043c051800c4024503090310210f180740ca0509500100110f4082074105481e2040c4140348005200c15103043d2038040d60000f4003039440b174035907400a1080d80c00540d044000890b0302807640c407108000d940024402c501c0720410301c84001043d01c2c06405402e030168412403019503100e80d0304100201e0442010001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881957032 1250 881955782 881955787
    0xb04390534080705030702090105040b06030f09030c010603050705090c0c0615010210110a17060a0e2208030901060e06090406090501140a0207050105060f1008100b0d140708040c1208 80
    0x1e070380c1c0c01030583c01518110382d00d40003c12443d05620348210081d0040400b43c400b8440c2f144814006500d40c40000c0c000d1842c4407048002c14010541082900c00c400d9a14000708022600c1f81442e80c0e4407001881703460b115142501c0020944241c202c142c852050720403006210585070002d000c40c1050307465000c01d045201d0311308820801c00031402415407201c1d070403003d00c1c1d5850340042c0080603150101c45010300c100340074080c000741c1d4845900071801c403030303003240501010345070a080c503040310b220110198a10490f15107203d0074048050300860240e101c1c800200151b13030b5284003858100388216010355002040300c00040c0843c015410030100507228500008400302c58202d1042d1041e01601c13002d840550220340d42040043c00d20070550441822110000d16403080b9000500e100f1080006408111582c00411407e00c550091500a4600108103944544030f00c801c0c00e0085c880d40b5500d43c032400080300401e10711400380150302d001300e8004402803002c078100706071030010442c0740d04201c4000104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881958282 1250 881957032 881957137
    0x915031c050a082a0c0118051b1302040b0c0f01090c06141306021b0909030d0b060705010c030c031802010c03110c03010e0307030e010801180b043905 66
    0x134680c1020902c00c0ca01a0b041d200d02c00c5a1280d421228000c12984001d40c0100c0040301060000a075034000d003c2580642d0082d40301c0c04007141400000c01c0c0d10083c103900210380840d8104041c40645100e00d440c000b26aa003c01070760001f800d90b0300c944009844100700b04024402e0710320403145860050400709c0c41e0340c40c0001104203d08443d2840e0700080040e0000c02000c50300c01c41c6000c0f8040d10400846200019090800c4070039100c6c0315210004a210341c0c5c030000c50080762504d0040c2c2e03904030381080082051101e102c0010b00982400d00c103200009103003090700703608800c6400d00c003480150181c1d00d0200c208820780c2d0907103210411024a1005205420341c5000030360742400b5440003d6912009151181c14625020b0f0492410601d510f0500111a0041c4035141e50251842904080004086960344000c00410002d190101d001164031021810de00d2207445a506241c0c01443d080c81c185c50064200902181c06020b100034030101001d0040c0824107509800c40c102d40c4a0041b5001c10058450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881959532 1250 881958282 881958331
    0x51e07051b100b030d02031e03070314070825020c04051f031109101811090d03080f010f05010e13060512060103060507020601030c090e0c0915031c050a08 68
    0x7142e5502e1401c5910780c00030310202d06042c03040d001a10020300085041002d0241d02003d001e5450750700c0b4005d0400800002c110301c0c46500300703072900c034010a80e80b409424050302c000c280d078400b03c400404402400c1041c401e0306c8056a0128010034569000d040c10700b415804000140038081c0910b17550369019103803d00d0540103e441203008620a207143d07110942c1034020702012040007002c070040c0c00c9410b18108100340111300425000404180000b940a103402c80f8100b850254007005a0440c3d071482c4003200b0075401c08001790051b4002c08040100e07030784c0e560905400541e01e0040c1c0e400100d5a900303071007290030302c0d500c0002c1818042d00302080107a201c402003001c41c3e800d40404021544000d0040040c8001d81c441e0740d402c0140303440a44220360440c0c950030600c0f540c600c01c400c2e486030342e001446240320341407280e807941c1c80008200480a09140307a00d2a2120138500e1100e202e4010315480b254007058004490002154036201d40c0e00b0006203d000b951000340c020508100c0030307000010b0b2150070300d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881960782 1250 881959532 881959543
    0x60903110f0f010f0504050607080a0204090203010e1909020102120922150911041206020c0d120b0409020a030b04030c0501020c0105040b07020316061508010e0c04051e07051b 77
    0x1da0200600b01020000c2010303084d201030307451240c0740034030b00424400070800c04a006a400f8105042454441e20b54040481c004d01c6a079102000c400e20102c00480d032030389010030b594003a2002d42000c06401041c0648481110f10040000b40568010b0b035000041034152000742805402c01001070643c4000f0001031681e00010350102020304e950751000b4042e140b01d20340039602a043c0001e0801582001e0050302d40d2074441d500500300d50999142070b24003007060707a40480d20b00b41030203c2501e9070f0010b8110043c240600c013051181819051041080542c241480b80264a5400800d0b4403052855074844554075a0090310030381c204040c8502d08804142c09000820003811004000601c41c0b5141c00c201042032800740c444d104641080000448540307400300c1c252a42c5411010000b0084c582000340e02d071400d510382c4402000c1d400c18141c0c3c0f03c0301e40e010807101000481503c0c24061a40d0f4980d0101d2501c070301400c0000030220701c4000c507001c01d02c11406424a40d11643c4064880c6891b400718604d0300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881962032 1250 881960782 881960803
    0x306060806010911040312050f041e0611030f1b011b092402100506241e030910090309050d15141329091501051c06090311 54
    0x81d440400104041c20340362180d0422034092880c95801c0c9811640c0c0c82e94940f0b00f400c1c804040010104445100d442c1c0b00045500414a6800043c0009041424043d1003030070313842080c01084250b01d84001e4154003100725640005402c016078640416a03810200e950070300c00364140d4965840900c9250707032981c05041610004a0749809966070700d0949400c02011720515011404240c0040b1040e03442d400042d14401007030b0301c1f917012810380d4a0742c1c041000c04500e800007680c1048280f410f203510302101d00052204500008082e4022075588104500603c410f4605a002e03520040340c111000303105900c00b641d00d62091a0401e40c41c0e50340d0000032094044040151400c01680c910352011194a106420050303161007e007441728036120ba01048134170580314000d4011540041d00c410150002000e2280040000070030110505014030040c0d030710740840d0011400b24080303000200d1686844c56030a050105001582100d581ca00c0d524003000d01003801044042c00319145419101403828010034514 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881963282 1250 881962032 881962049
    0xd0e0313080709060b070b130c1d060d020a06081e01180509010614041d0d08040512040810020a0203090406060806131803030225030c02090f2e030606 66
    0x380c1088041070410031194455014103282150070840002c011080c1d4030100e0300450b064400c0e5944107100074000c5032244004080340105040421000f8240d20445c0e00d014080c0007000c030a079a03c0081c44046000d542019501061900701005410710031215254002c03d0310403030040a50500300e009843d18006e8005000d500d07100328400306150358a01c103c5504c51007100c0240f048501d8091890314422990880d140680d0300d40040880005901144000f01c41550048812042005a0082241c181070b5000c48040c080d150642c3d400e0f114480030355040e82d03000c1000d000c040d800510310b84000e5000c40059400e500050104106035556845411700908030b545034008285886001c104e4000300c02442500c1c000c1c58078901c20250100d812003541d00340e0b498140180d468918176140d00319540344e4100802030070280c2520804141d80213251030741a41c0700752070300881e903112903150180024046800e00c0745002441100c0c3d400f07011403040f41c051040c41111030142142c407921030405454068004894 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881964532 1250 881963282 881963317
    0x31d161e1a0a080702031c020906040b0d1a0d080d021b030705060907300309030c03111f0f0f09080f1e0c030d1d1215060f10050d0e03 59
    0x2010740c02600f0a40c2c82071042c401740d480e04c0c01c1c0210001d00007405080801803140d01054101813500d5010440d40030385041e40800b40c84041c10001d6001070000c039102c10076100400c0c6c01104160034485400c090256100860900340450911342400135045032410180b500941601001d0020040c001004203500503005412245046281c040c5488030035804413010306455070f41c542126803d50920340c0b04c03801c1c80300b41c200031643da403c00b00e498000356000034145010700e08000081244a180e00c0103160000c0d110010341842009660040707080050f07002e400f180100303048181c00c51240c03a500d10400d08904040c0015a2120400380c41d1050a403500292507010720411a090078240d000d00301c4440c1410000d01040548001298941e9a0b0b400000180000794001c02880900c0400d0b9284000300a000010000a100740c1c0c10b07911640c0344e10740001c003401413000c41c4060400440381e0301e28550103000c2501d1071040f03900849450f071140740c0c03034031100c2d540d00103030591180144020034511405069014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881965782 1250 881964532 881964547
    0x9060f18211009080d0c110c0109030b04020603040f1b06091a040608071b03030507080f09030405010c020d0f0b060306240409020f030a03031d161e1a 66
    0x15907000054440104080401c03070310551030000740380200c84259607400b0440e05510320b00050702d40a820030700c0c0c0c511410100ea0180b55544800c50b02040821042191300c512100307001912640594000903211070b0314440000d015040400080d50080d102c1c00354440700300125201c45109039094032021130368500500d401c021241c0e10445030005000003a101c018201c0410402c4922445944118800d021200740003e041a02440c0c0281e048002c21041d001030202c540340050007444100c0300d00000c92800300220760020700220085200742c25020045103040e06080040d0b6040c0c0704000102e81c071196030000c4000207a0060b000c3c40840b44254000895418030404140c20a03000030301c0d110341580e1051460342030624400034010180415140003d4102e054004207007010395900d40c0c55018414004100201035242d80b0031241c4910500d0481c0ac854802100b0580711b490003080300d50030758091402070101860720b10f01150703002640c444007100e869860940d003aa070312410302405a103840219485 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881967032 1250 881965782 881965789
    0x7030e0f010525020c0303070b0402031f06030317090709020c070b2709040503070f11041d21090405280204080d0906020604030c060e0f1e0712060209060f18 69
    0x1500c9050f55001400003804050f001c00c0e0750380034580e0068080b11b202ca02140545d01d0921045150310440c45040d03400030400313104000604414402100001e242480c600c00b4190584c04040c09800214007419441d8903040d980400b035000024500c200380a1a1700c00680c400f40a002040c4040103180064044103000e00c41154900800212500840d0018200800541c0c0803040700d80c1c0c1544403410605403461030070a00903041072217507055001407900700380c18071140b6140c07005c0300c000c4910021100c0080d484030708200c4050b50b0001049200d24203024ac40d216103000d07001241e00c905102d0401c1000c962000013224680c0699200c003803803d9000509014504c018000042640d140b0b0900070101480c0c03400095880b207000b40050100822060b8810800c02143c02811010b03e2040032100d81d0780c0300700d5a0343e8496030b00f005a1010b1103000d10b40840126004100d06048031031107180601401000d440f010065172110800d6075118a0421151010205c03000280c0000036151041d000a00d88903401d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881968282 1250 881967032 881967091
    0x20c0306010803070c120501110c0307050c032109040e0d05030a0c05030c0d0c0c02040203011e150e0d11090c030a0e1204120206090306010806041704060807030e0f0105 74
    0x20b081c007034008020700c0f0081126400036078100c89501d00d501c1032104d400c0c20030500528142109a10020001402d10a41407001000c3c20780c460060080e607140b40c210700d0425541e08180244029040d0042c088a948840c00c1c10140c00304240c094000b040d020040d08040b811324044c2c903070721030108102000740300882c0300b28450014841038904106155042c0140651281d0244500000da402d46a40100e5540c510072055a110140d01810641d141d58492031102094070100107c0040c4009040c000580711841d60082c0840355403548400f40726081800034020804500e89041d41e0b080301508401140d0745681d600103110311142ca08194807410300f401c0704c10070388521003001d050950001a220305642038880484044503500c054014140042c0d10104156010307040409170306000f2140000f50080d40440c4051095204081450701c0001054404006010324040e040c0090042c2000030100740c003030ba00c000403000006007101e1201803238039000ba081d18000c031162441720030301c4003540d00c012003102e80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881969532 1250 881968282 881968289
    0xc170c030106080c07030c02090403020a14010209012303040318030f03050316050910052d03010608091902060d020c01151809020d0f17040b031906030203030a08070908010c020c030601 81
    0x51151800765546c900600c0c01d070040703801030311030f40c2010042404c01d8002c00904200a40c0503801031300442c5041c0300103000b90060314040c0d0104600f030118000c00c108132240240c1441307110080a0954071942c4086950720b40403000554815007505001c40400c40f0302e8400c0074803e102e5a2100d560346001e08a11882426681c003000c20b0140920911016035038821a94000310b0441c604540c40c1c010400b6250190f09281e54500c0d16501c4d5516000c411110050080d8141c8400b43c85419240d101c0018540d0380e00414540a80c60343e015451000041c0380c0340d030080c0013003411880d0260405060307008045c01c5905026030009004108032081011100090300400325420882c03040054140c55004200c01c80014070b0002e01d0b45c01d58009d00001c102130340f24001c0c400c0f40d09011194546456902d00c001a920030303070b800c44000584000030602002075004101c244e0768058055400c040c42114280c0325440090003040030301161840206000400344039600f162150f9a0041804070300c41c0c0107242c14040185c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881970782 1250 881969532 881969551
    0xc031501050427060b0705010504020405010e060603010e040305190201091406071b02030313030506040309120f0809040609231f06051c02031e060a030302100c170c03010608 76
    0x20041010001d204240040e5040c0d02c50f680d100081121011402801c0c19001000c440c0000b09003c800d000c415400075201f40e10990742000140d0303d44000003d5001d00703c0c1c6455010310200014040e441c180320b200382e0030034442d051890819980114072840c5200200a00006030354070034890086c00006d006504d50280b006010703005608250300002c000d05503511a00d074030341140341405021500e0402c204e40302e03200700c0784041c4450b644a1500a8680e0303026501940090030f5060085444038035003545c901c41d9030780200c401c50241015510380000d074100786c8203507a02c940c0e102d00c002031105503406003046601204007141c096258040101212030030281c10b04480040841c0391010b10043c10801c482503800605095844024006c081a48440d601b030101d03140f14004000d1056060500b05d4012040e44180b40310750065072540c09110354003c041c40041d0042e4007200e180030310207245611800072200d95103440d4040b01e6410201c82d41080c4240c1c0c1c1e8020184000004011a5a0209d005604042c110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881972032 1250 881970782 881970787
    0xf030f04061a0307050f0a090203070503071227030e0d0b09011d0c0f060730172706040506040209071407032a060c0e012a02180c03150105 61
    0x42c004030b51307243c0c85402041d000b074000c41600350a42e91a440e1103030040102c140195030302c0c5000d1388010b0250300256a00c4020402065100b001200c3c0c0d8010b484507008891610f0403019a00c10141c0040010300000350107103d181100c079030303c54480c910307081c0c070441c01028080010304140301128219039200510820f1815540a0702c00c941c0c1000c40d8003108044200c802c5c144441d0540c00045052007078a000900441004c0042c08040e1740c44c0d141a0a41000b980040070084240381d403d0f200508003114104200031241c00040c074501d0400481c0d1408500c1001100d0500f0403074141900d001405e07982a03441d503000d841000110f1404400b216407040b0249004004034400c0e40d00c00d100c2e80100007008080c456000181c28283e980b0222000d407010b20121910f900c1d001c241032003001403002849410003e4105141c10030154040c4042e0304042000c5803889440542c00d18032903640a0441e00b040713a0089410a2900c9540c0c5503c10403030040c40e805503815540c0c18400d14642c2d03440d0420849a041c000103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881973282 1250 881972032 881972081
    0x91318020114120c07020103110c01140a02070305030a110d0212010504180c230a061101050903130b0c0a0c030b090c01030b130c0903080a02150a1b0f050f030f0406 72
    0xc1c043d1250489106640552105a50304c01a4080d044030401841e082c3d40100d0a56040901500024080c00381c4802104030f54450600303460992040081c0a0017144080000c241e1041166100354011010a000d540c10040e4039030169087c0d03440312009441e01510400107100b41c1c54680301340c4507054100b44818041c0c408a170795030700c1456268400c0300c1c8810031700103c0481254202e0308bd040c216200501015403aa02c8560181800d148107843c04200e42c600070010f80d600000200716440d4219640320b82c012585040d40950403940002840900d50180104090001d002e07240000051071003418550f400b0300d0080c0302e4511304608540c040b030402d0f0130130f4040d88564441c080c0020300300c0718a090103d0070030207154050342c800e0710070340c401040f500f00000d03242c44c8168041941d001c03160b2202c2c21031034107840320f210380402d42c0d0b0300d00340601c1c2120404a88401c2140550f035514550f03001410405e00380301c200103864000e074000704d0b0900c5441e2070f0710041004200d0180304034184141c095008c0941c0014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881974532 1250 881973282 881973307
    0xe0f03060402061605010c0c061a011d01090e09070317071a04051e1606080903121e0a060e0705030f041502040306051e2a091318020114 60
    0x240640301034002d03d80001c5201c004501e4508512007103800800a1100401c051401445070300003800665000c1e02d4240711440c0080c26450b1301d1407141e0142c0d1120100608540c00c0d0001074404c1260b907061103020a40000d001503031b80aa103100e4400000906480c03891f5040030400150b081024800b0b420040211a00042d82c07102807040d01820030503503c1583e503c9103007891074040148200b070800300030f041c5041010500000c403181c404200c02010140c8980e82c6000f03a803208015965028260070030320201c003c1c160156041d031b40c0581106040b03040520661810b00c800001035402c409490b0f2a40d801303001802800c9010f81c1c20040920b446446c503c3e22128120340a08080c1000300940002500d00e03041c036003540c06403406950480e00404c06ca080c1007500702c541c4042c1100710140044088002202e021142040200128009520003940304444880225641c85040f6072503014541100c0740341040c02c40d1103500c80040b83c0b103100310820943c5000140290404a000010710001042402c8100d078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881975782 1250 881974532 881974543
    0x30c08061305030a0f031805010618060e1b13081005010f0b160501060801021215010306030305071b0b070602070507150e0915061917060105070201081003140c010e0f03 74
    0x3d030a440e28603d801c8804004401800c1c1c7c020390001c076030f2140507100c0144401907006404807080900c2003801030900c541003506aa2052052030000a130000004510002110442c08150b9056154614091246000a00c1c0c03075200d40246005922030900c40c41d800300d20344201405810b0101805841515018180b4080d10400c0b80c158010f10703284a4000c100f1100350442e401605d007032002035403201c080e503040302c407410803c407244655001c04914a40682d400391043c00d06803071301951814a491140d0315100b1094400c0b088190f110f211090001584e1840a4090710141d4071071280541c0d5017185052a51511a658001400601c542d10901c1e070b9842e084170040a03003100542d41070300c00d691003264070b00c2c2c041c0001c8026034004400040a225401584280194805480d1243d40d0300200c0c00410034600306d0216075403808160104000c50156000d00013035544040030710701c0d407024180c40e9a5021000301d0380d00e9080b02c043c3d00c501c084240e01d42e003104120301c07502811756400380443d40c4840065900c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881977032 1250 881975782 881975797
    0xe121f1a10180f08101d0a2a0902090f0f010f200a030c021005123120030f071703130312080105010509150901030e07030c0806130503 59
    0xc0c8100c00194446003502400300180820f0164114490b0340e41191a200c0a844d00c107168440c1c0b5000182204c0080a000b0401e04110b20303000340b142034940d9844662140282000d80741d62001d4008120700010400029400f50803007420141e11255504148408952303001c100c6440355101c103002c6030640e680140c105443d4001e503d01048901892404008d4012030030714804082c3c010b01c0094418181c1280e50760301c000703200f520300180c0407034040e50496040c0103a803400e420440300c2c0b1010a6961103245001c0e41800c1e2035001030107200c138010940c03c00e500c01e00351701112060610f03058010811040d01c00d04604c0305060300540b002a00003500203489050300d00031a02501c80d00074402030103041c108180c904002c02e11035141400c503120305008000c40002404000083d20020003c074680d44a24143d51601d01d010f000c001240303260038818400380d04403c03e1070f41010f07903407003890a0410b800c01103100214001c04000d8071440c02c1080392820600010a0f00002e070400403040c02c00140000100e1303003903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881978282 1250 881977032 881977037
    0xd1d0606040f02070623180a0f0309091d060603030a020c090709080d0815220902030102161a010501080c16030507081b010f0b010f0e121f1a10 63
    0xb04519451110080c0110040509541e141c1880c1032141840001107103c0756081504e0444a5980c0c0c08440e00d4804a41e44071005070303006139088800007580a40761450b00da109090004c0741c01e49501031303881111903565043c80700f4031021141240080e400c1c050b281c0c001200381c025503e417110510002e03541e4002c07040902d000d401200c0c00101c050f8030808240002e000b50b0070941e0044e11100900410070b000c25642c12610140c1c400e00c0348170078940900e01040028283d1900d0b455071080d011980002c0540744000c0c3d815540070002c00080180000310110702e5840b44160017503d0b450307042014100c58050304050305200d000b41c03c0c4803002802d003054070700042030300150103250589403504603810f0090a0f0010642c11000c01c0760f101c04d4590914105490141f140200143e840070b80038101034402d03401c007a601181502c10b408054900c2901300ca400800c002d8229403100d102d403070449142c00b2011411f030140d46004000d0a0b06010305001d04904a9200c4485800501e02c0100107001101c10300701c400c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881979532 1250 881978282 881978291
    0x6050a060e04150b0a020f06010f150e03010c0302040f09020906031305030702090a0204080f0d050301150e060a0c0314030622330605280210110d1d060604 68
    0x855612a00310f092102811100c8410b05566124940c106401c0185441c0c054010400c3c042c02c41400050300b10b0490301c08041651445241c1441074594076051403d0307034100b000c000701c40c03600c0740c4090151060710750f0940d8006948520b02200100c209999030050411940104481106640c82c042640d41090f0752401d03416422100e4078000c1d06e14425100002d40050100d802c2061041165010303000f120858000e50710919422564291034402c407080c640007060007800140442ea041e481e0303035910114141070001c641d90740c1d440060700c0c03a04440080b200142000c06a41d0400d0b83c04405810f41248001c900e40c01c5080c8103000a08491081002040c03441c085140201c41c0500b5421082c004c0c40c3c85881c0000c0741400b48540001c07142d0642c40000544176881001503824402c00407500440c40070304041d01c514819046404010210000c0502144141404421042086d11590480480e500c1c003941d41c1d0a00d04a409003520042906052403d0740c41c048000036030000300311a944250304490024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881980782 1250 881979532 881979557
    0x6030705040c180308120108191407050a26060919020f120106090b060a0917030f0a03050a0c0c0302060423161d061c08281206050a06 59
    0x3d40b410360303a0304401040746660000109206030780c8010410300300c280b01c120b5120703a03e40c1c001036521600440760185a40d0141e00c5800403910128800d0080c00361107041d1859582d44500040304940c00e03030000b80082011000701204180350b00307080c41c000b40d44240a407240c2d00c1d06000f1203894001c2402044030715161000f0300740440d80d9140f0000c22541000301110342c400700c0880002c0c024007090290081451425040340e8091070030f01c040e980e280040b643d517900a542043d004a921080c240c1d00a8001e01c400d1002c0242920140094000c4d8941c81c0e034000b4040c64525040015100d1403c078010500c0f048002440c046903002c58901d86c001e80151ba8032200503503d00400c655030510b41d1034001c43c0d0007001c08400300c0c2144807032004101c030707071806500c2907060b286017803440c074003005880e0254400c80d40390720401c1c4040041d40b1290070382c0c09031000c2820820031f00100f0b00d0078a082c01440600003480502120115002114200d818480c5c0720100b082c0d074200004240d584140d80a440c0078007172000380d00d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881982032 1250 881980782 881980787
    0xc041203020c061b0c0102060c1c06080a21080105060f1b030408010c090e0606090904050a120917060c030a021e0c030403031403071d1c14010f0506030705040c 70
    0x1e8007282e00c041d00080d507400e80000540c44103901c89142c100f181c0520712900e04650720000c0d1030f50103030800440203407510700821000718904907500b1045c0368172615003000140900b41403020394800347c01201c10b40c443c181c40d4641c0014121440404e82d05100300760005009503200c55058030280c0305400030300c503912200301c0030b0042d105a003001403d010307100015011419130010740003840e02c04e01c991590b90043d9125482036803d01c1c000c440d0f80f03070804010301045805160511015400a0052003618403440254440b240c1d221504900400480c181842c20045003c1c0099101d00003044c1c000940401d00780001c40002d6444080c0540d0f0060f030b004030318001c8070120300a100c400003205240e40c99840440203a01c0b034482d0000d2201ba0302044410a6004200003004216441340794541c0e01d40100d50b051125445a0180380b810341900170740040e65160010700c06150f0310a90a0280c80501c0e030b031002004509081d281001e07505401039040605100140e100052a0720035200211004100384e403021208 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881983282 1250 881982032 881982043
    0x120213140103060e07050d0f0b0618040609020f330c070920040e01090507092c0702011a0d0303110f0306130e06040f0602040512030309010c080c04120302 68
    0x90200d52040c40000000b000748540c41666521041000e4030b01c119a01c1c02008404101c098020303140045002203200081c0304d4242055010200510b08405400e51200d180e444c94801c64044039107503038848400c1d0551420444e841c60100302110002c03c8840c009000202c0518158040303600c1031800c81803410814132a4054075070640c0d2401c100c0340f86950303842c0090080c2c0b1114404444003400409940c0381c480c2c1003400c98056071000200e00390241d02c1c0801580082ca0020039401c1040300000e0049540021400e1000c404402440c00c85c030040e41645032928000e00c042c0052040d0781c07404401552805844030100e1115408440d60080b0701c00c43c1c00d054019080d81080d14011a600150000f0709400b1140518017409090340c6841545c007403030b0004011a28011000d43c540d602220002e000a088040900c0300607224400150410359982c003c940e05102d01c0c0c0400721190400300401545110904c2640c4030070140c1d16042245080412a04095102e14022007007110034028407981071600802c03d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881984532 1250 881983282 881983301
    0x7050a1220030a0f0605010b07050706050306030316030e13060f0506070203010e030301080a0c06080411041e02040b220b3112210e0d030905090103031e0306120213 72
    0x1500c451181c2c518044108281c58101245c0f500d28100000ca100100c2030b0640c1c444070791110003418500e040c0f900903078030354200800c0303240c0c140b10070408400e0140c101841d48503920311035240c0c941c40c2d22a001c104411500c140960078420362401d60704020700f20740807522038111082520300c560b4403241c3d0700109002d090946030003a094032001000144107900013800c1d0f40f0b05030042040c50260742c1c07102e00444458509032000340c0b04031400c3c100e03000d0718a001d60140204030031042102d0b9604000c850110241d812680c0f04002460010401d9000010720b0301d0204142a020890142c64504080560243e8040e0642642911310440340e4000c00c284040c1300c0c54428016442400f00c02a0b0715070f00b0442016400b54115100c4c45030011210420300418019451541d458941d0350110001c01d0074050354421000c42034042102500c0c0001d00303502c42070b291138082c0d4080ea41d0100c10249003258420100082d000109c100342c80e01c0c2003040048100030149190541c126003a00c120110540f503800174218010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881985782 1250 881984532 881984539
    0x121302061903090230010e0d1d03060c0a02070503030913051003050313050f010f0801050f040906020c060a11040605040911040905190b0102070503120717040308040807050a1220 78
    0x440c00710b01e41c0e254051413028035030a0f1030311400000342c45e40d90036500d40d6150000a5405000d8a05001c0d0040d1568103c0c84140c85018200d820900700288c03a010090fa29159034100004a1004865050205c3c40250a080d00114034000d01e050104c1c1d54001c480481c10519580c503804150140c0e8003e030352100030344d00a0704880d143c0c609035400c600c440c8098852280b04079004058885a54081c6490300041c0480f031311254800d80c6004240800c14001140041d80280e0b6951000c0005006101401c0c0600d41c4400401c0f03146028201441180c4d0383d40c9180d40c0204042c04104004da84c0801240c0584481c0000401c054900408003115030151340c000d19025401e010800c600d001c400007100507080b984000c18401801c142005980700c2c032082c090703140c05802c81221009a207050380c2c0180842d600c103c081c0049456091f02a00d450703000b80d0012140340000050812802404110020141c102159030144481c50202c2c0e030a001c0c840d50b0001401845000790030b1420104502e0703085c2d500300b00034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881987032 1250 881985782 881985799
    0xe15030c030f010606021005041a090c0a081509011e0c1e020123060a030f080705010c05030a0c03050705030a0b0d0c1805091212090f070b1213020619030902 69
    0xc0c142c1c103011340405e00890005219020740a010000d41e8018035002d175800c81e200c0c0494040c22504a80c03007043c000c1c20306c071041c1315928140206031a16103014004000c038002800d039000c0f074454651030600000d00550600d0781010480540141c0c82000318008001240f00041c14500000c001d480341804001d01841e06415020078101440d0190014503042c4004041181d205030442840c19040a05403007243c0c0203102e403071040c40002c10780d460310004107000307503000c1e0305020180d0703100341c290b48070f031002040068804014443c01d181640982061a0108e04040c0050310340b1000041090000074090075040e525030300d860f01141c5070b440340d1605c020341042c440c0201136103d922010019080e09195281540740c0130006041c5038010881c00311101b01c50b0061860030220b4074014070f289401a11607401805512000943c0d10300401802c0000c00040c1610f944441103034001402c1150700428071801d503580441004010303644c2e01e044440c2d8154841d50f06602160a0138128000c1c01e030800000e4010700403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881988282 1250 881987032 881987053
    0xc060c0c12030e1f14070206040b030711100504030221120109231308031b0c0c0109050f0108190e061812040f1503180f12090e15030c03 60
    0x442600c40c00d0f00d5041e80c0716954903e52000d900c100500c002401c40c0003c1550380c0400001c0d00520042c6481030000b00703141d081c552240416442503009565840c04142d030141c0c81c002d191018480c440403403142c03813401c0006203801c1e1006500d400081f400100502788880d03440c0510741d08031040e917000f4544040346080e250307180c043c4000284090654181303024501c0a1110f0900781c2291050b2180300300315614500000381d543d0300d4a80e81c1015107904041d58040c10360700004413466010f0284004000024001044094005007056029410281c00744c02d8280c05940305981044500f80c004004000107a00c4200c2403000c1c2c4010500201042038601815040c40b0481132121250184001e2400c2540c00c403e4010602c40c034540715500c9510783c074022404080006c040f459141d1003140d003d604011680e0000a0901c65040d03007031503012070b07003071164881e941c081c44000700328483d4244013400c02d000f03214180803680303405020041c9075148400045c0185e56898406001c410324503100a421a40500071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881989532 1250 881988282 881988287
    0x10203070f080612070e040f0f06061410020303070f030b101806030612060902180c030a0e060702250305030c030a031116030c0201140d0903080a05040c060c0c1203 72
    0x404070040d40010036a10204900c0d00e030005185070081e080100070101c0360f1400740300b0b6403942c00c0100182c2d00c03000c81176411404a03034100704854103180b0030400003951509144e18100303120040403c40e0b015407a001c20340c070a83e5400000702c0743c1041480c00d00d03082c1d050034200100d0140120800c00c80e08900c400d11060704039908030f0909510b030f0000030001180035032601404c800325600b900ca4407460340e09105c00500443c500380c0c013030b035441c81c00079000e9001c40c01054203500320410280c4034003600f1100002001031406892180c100700703c904801400b41810f104100a50398202034850185100c0c500d440f40040940300341c010030003142c2c00010f4035201c403006601c1a446c0d03005044000d002c01d05080014140c0c2c01003d0440e0100c3c00c2100c03c1520b40c840761b03101103614001c006002c03810b002281e1030071a05440440042c0c600400c0107035012940c01e80301e203002032590744007802c40c140c00b60601c024840007904e48200d800903240c0f01e11340003440001600305110782040ca82e000740c0d0003620a04020080c0355 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881990782 1250 881989532 881989547
    0x3002030901030f1802010c050a0c0608060f010201090b070e0f040c020303040b09070e04060f02120127060f0e070203040b0f04090629130810390c1401020307 69
    0x10240c03403c200610401d12a2802d5840c644400a100000c0741102c42c0150f025403004411140194122050b40320f480d035030380411201369080407021a400c103003009076500c1c050120b0200c0c200700388001e11a480d016078908907a090003502000078007983d485c600b407184d2902c005041d0f580000070414469802030b410041c1d01e903441903c0603990704140c07000040e10b000c000259502201e800186000c03070755455440f030600505d403c0303141c00c5095070204292020881c0060a0b18060000b00d940d240d00d111500303441c1c42c0010442c2c0c021022840c2000c00c100911907644000c0c2d8200c0e480d815008480740e94402d82242148502c0d045010a50008503071440c0b0308003000c02800603522103200402420f500e0704071001800803085070a21002051075102d0801101040182c00034050450307413a050103403901105818910245100b8001d070f9500d6030b54007881414880034800d46c000c01034000320603d204010985070b0507103c400c082c09101000001d41d04006084401880f16403030100215200d0401c610000e0108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881992032 1250 881990782 881990797
    0x50d0911010e090f060609010306080f100614090c0d0603080d1401240c060e0d030203090c010905012c12030a200a02012007031a090309010c300203 65
    0x2c490410030807060503da064240220f010a1a421050f540e040c00c00c481540180d400504154441c000014644402c0201c24401190700c8042c1a044134034054640403075a00e980708090385442000e58003403a40328000a2a00280301002c840d030f0b01c608003080d00c00500a1907000074000e01000890002d003070b202d41c0c82200b80000011840d001039990b6002c0600c285c00c9010710800c0441982100020140140c180090080c400c1d4004225041c503408882d00f8491040d00c40e00c0469000020480d00b1802404040c01c649024200049524180340c0003c1c9032080c21074008400945200c030914172a086403003122480035000307026018505050182030384030b420200114011541b944036007100405441901c412407110a80182401803240e001100d11039400c3c00e0100300c03484201da681c101c0c0b2109114003c0658010203000d04030740030725809000c41460040c607100c1c00c1d80040c484005580ea100c2061203805400c03030900c2d0184841c80142001800651008072a6114208159200c564001c0042c0c0070b030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881993282 1250 881992032 881992037
    0x1e0702240a0f051314040e01050901150f0f03080f040f03030504031202060705161401090b01060f08010302030a06020309010b0d0b0115080c030103060c12061d0901020a0206070f050d091101 83
    0x110040340a42d83c0d4040c441051000070000e83c41444900c00c03000502d20130040091010400b01146c040f01821900c040d00c0684050351204141c07404030140c503595078000c1c0000402e800d1203600e03001400709042c0361400000c0a111002444800078001c03001036030701811482207100e030800e1b601e00c1c025125600a120486540350b103400d1241d00d990000ca600761103030005442e1980b50140d03450001d4000003540d14220b035418585141c00f0f903171701d81c03d12a5100f25032080c1c040c00040c0d41001c40280c010f6203e041248100283c180041c401a100032510051f0154011405a1070382c5440e8040c50141c96214003040d00110304844030414004080c211074100c4400d400c1c6403400f908004801c80e4041e00c01c44500c440c0c484104010000a00b44c4d50202210340d00c0382c6040000030020650807001d1710041d60220506101c055008030084001400303441d08001c0c1d03800210b103041031405020752180300040c01c10060144000040d42c120740200210348200d01034a004011191980c9081c0d141103d074201041e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881994532 1250 881993282 881993297
    0x51e0d0e030310052218020301051b0a0f091e24050f0309010212090307020a06110c01080606040f062f030301090f060b070f0b07051e0702240a 63
    0x5880c034010044038000c2049000040045052400b031140a51801c4840f40d64200350b4646400011424852108540c01c0d10703101e0010350f243d074010182521000381c12610080850021502c01a0018080341d95003130142c01d00d8028414002003d9440c9211548000c1700b0303a4000301e5481e00400c0c000d1101040e076032219821032040000f00179030003d10121184a802050b0204235140540054030003443d4000d14840c00907203031444e03051241584e81c40603643d04074203500102d5008110b26085070160040c00540c0b80000712801c420210994510105420038184480c0300003161050f1035884c12500a40219030311400324a0740c0f220010b201413000707050500ca81903003d40d0702152803e0b81020500340b059000040d8210303401c040c8140300030585210380019482e9101c0340043c91017080006070059a0007190003451090803400d02c10b020102c014145000c0040811051855080c00c100c1032880c04d16550740d0030703200c0341d03e4404a48180154100e11807160100c08d11191142d10540003003404003800d82e1440d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881995782 1250 881994532 881994551
    0x6071d2e0909060f05130b06070c171b19051e03010b030d140a020712060c12050c0f0903151003031101051014180705180f0d02060a051e0d 61
    0x2c044800c1401070044400c2d44120400540c83d214011482c00302c0301d41c4000802c58140d0001521070360081404503042c07030464008211210380e109802155003030345405403c00a44181401a041d42150400741c4500c07001c20401c403a0550403809040a801c0c054816020410444902c0c03600382c114590070791096007041004016401d000c2201500c2c00c203039881d41c0034010186054041140c111201000440c030960000080002124a09100c2c1501440e40060b40311204200100601e004c0c21004111710304000a00100ca1640021541e180e0711074140241c46004200000307081001481000174125007003800d0001c0c0411403410762045074801d4603100602094048201d003654000c4030a03400000c84064204201b8103002d01c4a400241c0040403850001da4018054156a0040c2d40a0000440101e09030000d05031031001c0c0c103088601100c2608183c03d4940c0015010344807a1002030103075201143d40749840d070081c020354008016000c1c80610881e10180c543c03007950440c03400140b11500b07054411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881997032 1250 881995782 881995799
    0x6050a05030a02060a02120a05030708011205250902040b030601030b0108130f0f050a150b0f090a090804030206161109041e030908070e1806071d2e09 66
    0x24210341020303014046030b150715020000141c01c402d034058158010b41c8043c0a0507a1040c0041045c0300700c586482d070312405c2c1201c0081208005800440d1482d44800f84071020860018000a42407000c442c00c000d03103007083d22622180719241c0e11001c1254008640400d82003d40405184191030070390381000f91041250044070018000d44481c2280c041c55a42140841c44e40d8a100d5803003800f600c40b00d50034408070b90320303030f440c114405005842a0f841100c01c036880b55840d0003085282c0300c1c225520003907054154001482d620002d8813445c2c0c1140e803452164108034480b0306071001035800800068844902e00f07029800b80700324140c01c403141c0c162254403a0710351801864080c051070f08410b8903034291122200006040001040c19810310102605c0058007d5080007564003400a9000c840250f0802d102c00003c3e911000d40c00e0358007a044601000030942e84511016201d01c0ca20b1380500740c0d0f440040104594005000c1018081e4495454581c020340071800b05408060b0603070b0382c00214036543d0691 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881998282 1250 881997032 881997049
    0x41e090c09031a04030e09040807170f0a0e0301061706090d1826010f0c0e0409260d05040b0f10050604051504090504140d030506090403050a0e030a11040605 69
    0x10030005940d6600c000f00240410b08a5225100b81403440d001e03101e030400100b203582c0844d000c42d06600c00107480c0042018040e80380807150715030341c415804c0490b41200c142c40c2c1d004e841e4540c0c04002c0d462001c00715564094001d40010032080c0c43e002b410160590b40c0d95150281202c001003c1d03c00c44c00c1c480c80141c850580c058649611080e09031030320b03040c880004403003011031302440411031105c28046a0380d802071191915414000c0c41c0041c40020f1200c014001c0f41e0344081080c410351520003003401250702080b4030301421070000d0100c07032401a005450b80751402144d40111b8818540340401c007c01c0780040001c1d00a040107001c5038a50f0303a0380d0104042030400e50181c0c030342104040c0410481410800c8001c043e84840c050748908003500c880005084420448040d10603807000121268812000d00c001c800c0140a031400b40b1507450910040b030340c0c7d0200500020300300b010004030280748038490000745900b01d1008041c0d03411a200c40c180185020030706490b051040c0d02e007003000942850309680c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881999532 1250 881998282 881998289
    0x1509060c03050f0c0a02150d0f0b0f010305090f010e0d0e0607051209060702120c0405071b0326090106090e0a03080a0515060403060e070e0c0915041e090c09 69
    0x849515255900154554903000110300390510310405d851080103a8a1014186d9044600602c0300d445a9020801509950418000e00700c1917103080501d600c81d13120303814031a050301d10a0a005c6843e4070340c1c04d915803918003410b1300e901c165480d0400200c030110001c54909809160359a440525a00041c208611445a14801060340d8001003158000b003c100000d044c0010008051307500b811516000309424070f0000500721a02d402c00b80d008205440c0038820103400c14524030b41494548042c0300c0e122141800314801a003403102e00c650781540d1980d500345501d00c00c2c44000403240035080c003030344842c007030003c60191450b40341c20001101c000000009100710255015600c180311500d59030190300080c40c0c09410f00e42400150b210301d151580f130f5500200700861090b80009080204210000d08000e090340141c4070400910052190500780001503990b0410225000c0310596205400010548a290300c4890308610466940c20140180580c28044070803e00041c08000400c0d0400c540c0c480701e501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882000782 1250 881999532 881999537
    0xc0f071205130e0c191209290402090a0e0a061416261008031606060e01030209241905030f0606031f090501020301140316030503030712151509060c03 66
    0x101216105d07070420411a0864604264072080c1306040c151050f520b841d4025030315a00e040d404204040d1041c0030001203078100c60750444507400c05034006440250064000000c154440130041c2407540c3c1070012440150f4015410003000304814001001944115032010622400b003008a200500400041c1407072030400c4881899010003007100c505d420310142240807410801e0308007149421003003009003441d41e07a04400400880003441d001e01a5511a000340c1c031040b00104c010001038407030041d919085100c110300403140f03e80b243d14444541d4660840c03154044440501904060901108141034071000d40a50f80020300012646a945200f41c6400b034141e0b0080c4c1042c2c245c058080d000d1506117208060100300110b0380d0b1111805c0e60000c2c0c124910314007090201c1102450100090b00c21601d40080f07840c0d240749141c0303c0944900000b081381c0103001402520000b001b50f2640310241e06503842c112541480d071200d58452005d40303100d5a44010407452100420307100d000b41d0246240c990b052b0f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882002032 1250 882000782 882000787
    0x3110306060d05073003031b0f09030611071a01170303041a060a0807150e01020604030f11210306010f08090d050d1b02010b0102070b0406080c0f071205130e0c 70
    0xb803040244501c1c0030424290860036210394021702004406204241da000390380208840b488101c0d4044800c1c094400d2030140488800c0d04800103400810150440b40c101c00c00203040002c4180308a00c1e80f041c2c80707009007043c404481010b00035030000610743c1a240401a1001802c2d0510300072a513030301c42614058202045041c520790303c200c4400005a004a015290717040083e034034480b40e8a070103a1904407040e42c0c41c80300c0028080680c80500b458011100348000c01c1700c1d003825240070f00441e07010070591042020051801e0a611010449056002d0384030501050052075070000c0c6035213420a69032280018422074445014610445c81a40152840006810420003000d0b080d1607039445240d0300d200f90b64440e036560300d068080c010807c1d07117070301181c002045038218003000905044144e004000c1442c1d05000500816522103000d0764000d100091086d40e0701c0d0b0412441400d4010340c1d100030b1400092140c41241140d00001621001140d241500c0d113141d00d818918011540880d03441503503035402d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882003282 1250 882002032 882002039
    0xf3b0402160b06031906091101030207110d050c060c1e070509011503091403033115060b0a1d041103070f0c051c0e091e04031803110306060d0507 64
    0x10800c85542200300203086980380d5640f00b001045c1025050070a03a0100e95400390740c01030005203210349200d40c009107400c42ca07100382d568646080c2d4061700301f07250041c1f40301c1c0016410000c0400400000020080a054440a800c5a026503540e115601c5400d01d501c1a1803410301c0700c40002c0da01042e40c500401850582e170800d03000e180c5003508440f00104060b121a410400704080d510947c10034454035010755a0392900b003006c602641c44d9210050040d012200280e02c8070381130b000d100d5070785640c000c1054140380344034811040603040c5500142c0d108007000841301151908401c020b24142c403e0f6405081ea07800c3c100800017103a0701c1042441e00d20b041000041c1441c2d108111024640340e5a00f00b41c01d4600080d00c070785141c405111008402c2c844218003d0400f690002072249900004444141440c0340402d5070041181034090b003903100e0f130040c070081001c1600421511f000400c0210700180c100e80e50342802240b0100c41000345000c0c0c0111000b0032102d00304840d08012058000005000c440c5c075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882004532 1250 882003282 882003293
    0x6061e090b0d02180f0a060c0807050f0f070e010305100f020d0c0e0109170304050607150c021609051003110f120309030f03040f060f3b040216 63
    0x24041054020040030380000304107405150064280d03007510400068a502641c403d204c241c4826244a5120b4209003240f4200c6549461121060b80c501c0d01d062240315200d031910808500440740010700d81c3c01340300040e142d0780d08009007640320032660008076031509a0710607210f9600d03e000c0c00098141c0e00018103c0b202064103820a100c41c400750000149024401000401190f0880076200005010302c0010142981d100f00100c0141221504c0c8050742c0140403041c590724410781c4100d038021040810410302780280d980c1200e105211440e0103001c04030300610f00a46038403403401c0d05492802c0884c4082203071f00303941c03090921a107030040f07a48a4a6083d51900c11614003a02c808603400681c825404020f42c03200c841c034040309010b060045841e00c800c0001c06003441002c2c00700398000d5000b400200310304944410800100c0e1003074185144035074043d5000702d403001a60780c21035031060082d1080b80281c510411062001500301503040d4a00b01079802000140e02c6802c180c05018034000c12228003069 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882005782 1250 882004532 882004577
    0x90c0b07031706010905130902010806040c120506030316051510060815061e04050301061a07030c050a0f05030319062d032325030f050703150617010606 67
    0x103d05042c10340e2020355440002d06580d500280805d181c0b038980c0010021560040700340f07038110604490034405503e000d04000c0c4404144200700000030b0712400861026242072044035070102180c50201c400c001030b424900d43e60400c034281e60301403440d03103400544140c0c0290002015103455035258600c907192401ca03110100f0115003040c0e4000c03000c001038040ca0880c00c81405080500d84815519940b4000400d403c42d4100d910007000900010070703580000c0810b404544100d039041c2800c00c84810301d420700d140340c10820300c030060611416100800030320800001451081200c841580500d642140c80d00003591620310901c10815000118107001640d2000600100c940042600342015903070b441d4000d00710405012540c84e6001070a10f00e450706c105001d45640c034400c409942c165083d20a12269500d0305034440a4500e0554003c907800300a0240030050003142c0000f40f1b0340d0f03990880020030008109610900c030452803c511042c0209106010f0102101d500391210001401c03030b82d12404455 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882007032 1250 882005782 882005791
    0x150f0408060417190810091e060503060408070f0807020402040b0304110d03081306020f03102313050402040207050609011d060903030c0c16080106180e06150105090a0801090c0b070317 81
    0x5c946003000b040d101601c0c8039140030300c0030320410001008150140c0200302d522a07000702d40030b1b40cc82410080480d01c04003ca44100e80c0c07007001c00c00c1c0c08a80b810810064050250b000390b20600004d0000f4a100c00e8002031350090b03000d8884002c403a01c03a6410400e024845900040c041070050340080c0b24500a840c0c02820a4000c0350090300c0c10788103118080300c6a01c00c0b207240c003044040702c00a10040074004074100d00402e400d002007800704000e80029441949175400510156180e00c0024219141d58055481c40384d84081140c00394244105081c1c00303402d003010301c20000c074107041c1081031b50031000403400e0040d800305005e10302c0c540b2044030070400e079400502d082c0850300c5146040900f089000c4d01ca0b030020011680002800d6081400c2c8407024201c041d4000e4a450034841c0020342d41001040803a0000005000000e10309144001a600340c010441c43c1503000c54160000680d1080c10b401580c5002e00c100300c204001a16084050040d0096110240c0042c40480b03580001184060748290030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882008282 1250 882007032 882007051
    0x90f070207063f0e0d02030d0f1112010806091b0402160503031806070509011d0f0604030c080106060215070c0507030c09020a030b0f010e150f04080604171908 70
    0x6880101c01c0b02c504084168001c1040489800c62400303c1e240a210b250102c0048030060b14034191481c02c003c0d580d008a090180c0d6503582c90260100000095010799100151884225141e9046040340400d1031030901c50243c4074015040000e01214003c2504040c2070003151015102ca50160305100003900884003d6110441d402030a03004a0000c00266100f90000a01100c20480d50094035041600141030a4180402400300400aa81110b0191039248074000e00c0c190f030100880c00101c0c01c039942d1310341d19005400081c0c08014070202440f40340603203040400a22209a43d080200e03135504424640303059080900c8046480244650300c1c0144590007201204c1c10030391a500c2d59020b101d040d40c00b01e880f5641c00503000300e006401d07005000c01d03c0c0f4200c0e4802c3c04100a00b002824a103c0009401e2240f90095120440c04004200340c4a054215440e4a0b4079643c94451243d900e080540d000c0c0c4032001020004148641c03508216401800c003040c07018000b210212041e0340c883c401601c0c0d843c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882009532 1250 882008282 882008327
    0x11e0302030423060a06050d0305030115030f020409060503011118360603010c3207120e03100915021810020120040f06050304050f010911090f07020706 67
    0x800f903900e81405100620f50094803190400c6060281100c0ca6640403502820b10001c4200c042900402aa811910140d1225045c2440d4010881c000c0002c2a40c10012500c0814040340700d0b8881d90100c0203652040e0020041502d1b1002038605600980c02d06000c9050080454902c034200080d00454010004115101c2c2c0540c0445401084e00e00001d4400d50725150008c1260f1131900b4000c0c0350382c900103800e00d800340c00410540c030764940700303040780b0111020b0180e03c4610000ac02c076404c442d0b4458000130b003005802030fa06401400782030380d006901c2c4244151062604400751510850300b12507406103031403400d1810700c52281d0213500042040d0030703000c615079044107440d1942c0001c40d05402c9141e00004001441d00a003c2e596210b41800300b020002c203020030310101d04880b4462003951140d013080794480d500c1d45085480c2c4440e0442ea20807a50a08011108210070200b0b2039126076803c0300c0c100c6c070b2030761440440c81001c03070708580c800c2c010b0b803205200f003100c01d02031412000080724142c418030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882010782 1250 882009532 882009563
    0xf030405151306030f060909050d050a170f0703050601090b070210030b2812050c040b0a0f080607030b1804020f06091c020f0a030f080d2c0c011e03020304 68
    0x7840c145540c0083e01090b2a4610307034076428514414000500001c010410110703d20b0b0720f071a40d48201d50a4084244140010448038176401240c0d100c208100303940c0340c092545010484d01c801070205403080400300c3c1c00d0130301240c1a2360284943d442a07850b101145c0382001225001c02c080001c846071900181036448810155031b80b201099130210507400301d40d1a0b6901c009801140f1010001ea004522101c80c0036081000500046041414000c040300c01107001e6500e48000382c0703c3c1e811079105003829a043c0c14000348904012a09034801c800c9901c0c1040b01003210400e01c2100c4c914900740407080ba20310740018005151252059030f420074080c3c40c0c1400c1c0264140130031642d07140c0603009951150101520300451070700341d083d41c3d007440f020b4645070395561669858411032070140c14000e015203008203d14140d48650b9019850b1b45070003003003140c2d01d51610140d41c0920903404410b02c0c101c0c01061002d40c0346d54042c620b91840031140c94409010162041e104034000e40018208644025881d191030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882012032 1250 882010782 882010807
    0x9050f0d0c030525032d0903020d1505040c08190201050d021c150e011715180607031a0d0c05060c01060906060203040513060501140c0c030d050a02010e0f03040515 72
    0x45940b44a51a0b1062600c000c0305481e00d82c210360741d5500d400883c22040846e0099000c80c03540f00b00c03a41981c00d04d4070b1103407a16191002e50010082d4200b09440c10040006201044008800b220210400c0e200310283d00780c4040c0c024900708174040d010503003c00c040c1082c13104e0395006094030442603985644110f0004428420740765101800648801c0408050013081541c50f1510300600c5070614458080041c1c003c001d413244103108082c0401c2203e00c002400100c17030b00b00f0412020341c181042c1c580e107142141014000741080d811220b04003c00a000d4030250400c080f005040640045c1290b03030080c80d05040086030750110b00100d0445d5200d03030002404194a02071540504030740d4019546440c02d12050114000b0500e40d1041c03910308200c400c00c003590b00316400c000300f02c200070aa2540c0304690344202e8030f070507081349120f909881894040c21079998401c01078107402c003880d8020700c074202002606d02e40c2c8080f004640240c1d0f030020030040200e49010f450203010a0702101400d42809000601c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882013282 1250 882012032 882012097
    0x3080411030f1b010806031e1504050d03060b0705100c17180105071d06090f19050102011a0a052e080118050f04060b060d020a0309050f0d0c0305 64
    0x2c0341c29540c0104810342d060a448540318041110030320340301e2054a40940000d55448100407900c11110700c0d0300070510f05240c18400c07640c40c000720b2803070207401d810146801690f42900c0f00781c401c00640752110100f500d241c01001c0350010b98000c0b0040c070003c0701d00c00998000f00203403001101802a030000209607880b007000d244e0b100381c64241200e00c0030030300c400d103060941c0c4004010340b08202c0142c004440d4590a0140c501180c907090340e0803030702c480d804800310300c4900d0701581440e40200c861080c9800081c880f62a41309442c82070f8000d11229410800860705480c0b9201c80e19402240c400d014011070030301c00b1a82c01040c08068000031259404000540c0090301d8021b090009410540140401a404920000302043c0ca220070030032482e013a180f4052820014000500c3e0741d84035103182c2005d80e514820350301c0c6018440350840d0f5030101220003900501d5803040448141c06a000d85628001c400300f4002c0d0003075000c0d2110b24590f000c80e501190507034409800304400740810f9400c03da0020b001c01d05e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882014388 1106 882013282 882013303
    0x301030c0918021c020f1e0d06090b010303080f0c030f060105340b06030105060d02120102040e070801080f0115120602040305060a051605040b070308041103 69
    0x840200b601d0489102a60110f8001d0304683e5407900da9038003010381c84c82143c0c056110b8050000348421883c24819010b0078100390f003030400260600c010f0100c9128819103000420740c42c5a83d440280b0749080c1c009400046400c02001181a11944110f03000940c00c1e01d41419407404101501000000400007810050045040c880b4084900c1206801d400445041d60380ca901461281101841c81c04040e100c000750307000460340f036090622407140070b40d001601c0c07100c410800e5000e02502c406001c5d030a41c07003998200400900d940140c48007502440d0140c0d034481203545060280c600e0805074000c3d0043c1c1c1d03454407900d030400988241c2d48030122402071500d030b4100001d50070401d00902456101a0042c041c450800940e107046502c05486904080c44040d44104007401c219210701842c0200210751104004031400310b4040c044066202d44a0800c50600b940c1c81c501290600c10700302c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 881834532 882014388 := by
  have h0 := BRFrame.cov_init 881834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 881834532 ≤ n) (h2 : n < 882014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
