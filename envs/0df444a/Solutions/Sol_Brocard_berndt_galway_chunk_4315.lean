-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:13:20.307596+00:00
-- url     : https://prove2.me/submissions/081a9e46-62be-47f2-a14e-d7e085051a1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775899280 ≤ n < 776079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775900530 1250 775899280 775899301
    0x605011706040204150803310b0906160507081c090e070e06040b0f031803040b0f091c0b04060e0607020a02190504020c0703030f05040302150307021e031b0309010503040b 75
    0x2a4003d000034007008c101c041c2030004400510700d4086112040244815642d01480380a4105024804042c81e050244c0500c609015004101142c00c05090728503408483e030310b20b480d041c0039800503a2941c00c00c4000300d2144680641c1c1803c00740150602c4901141045910b407103a8000400f41e1003042880e002038411500c892080303074050082d402c2ea80d070b520340540300351110503801500e10084c440d1a000c07080c0008000481942c0a07034808540013490300b4150000000190018200203a020201c03008481c1e420b45103400031080d05100e800151554a42800d2410840b85050071310101c46e0091400c0101c4681e0124110b01340d90390449401000309240c514020304071040c0c1c0c2016412501c00140b00703051060000d02d9004591280ea0b880780c03e0541e03050100e50a0080d480020b4000c196002d5a4035407400f40340246038042240c2c8100d45013040c860708a000c12814076031003000b5036003002416001c0c168803900e5a2002d0310404006610341401500020042c0c440204090200d501c0400480d011404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775901780 1250 775900530 775900571
    0x1804020103020a0e03030a0e120102180108091f0605040b0d0302060a0207571205010e0a030320030405030a0305131712070e0d14030f0d06030605011706040204 70
    0x4005c0c0c1101c0d00d1720329204c80680031034013126040d4401c001c64280a118503205008980380540405900c004007076540005503502c041c050301a6185000340c2c0da1040c50030144504511890840e1840821085e14080c24002264000076075240a95a1120741101098000800701d4001c0041c050042e6260603034209880c080c01001d0403c0103200b58403641c980000d8041204070b144180100d0341c0110a00c1421a0032524803001c03566a0301641c01d4801003141041001c20b0301499405100049010485007a030182000306c00a01140403907540e42c400e44440060010264840d0590358255145007415250260340340600c8a1810405880740006110458640b44401e03d89074442c0b10041040200141c80d402600185201086080200002103815202d09245600008090302d00026404a40c55113030b101003150110f0b0f202840104624503c0e0036000d40248140d141d00c0c100040c0250452802350f0980b00c06a1012200b0004001c944a0b00b80000c1031032504203a049400140303406610b05039010306103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775903030 1250 775901780 775901807
    0x6190b0316030522080f071a150418080c01150801020a02100b011e02012d060f180b010c0210030c020606090c072a08070f051804020103020a 62
    0x4400310a20021504000345041a06803940b4140620b64801d424144089605056200c541501c911020041042d100c010085800040222442e051480d1213841003072100950414842003c030040184410111288841400d42100c09110050720f1105140c01c4002001004c1c20945002403240b802401c00d5020304100030403810580c03020341d9a610218003d41016101c20098011071181110082e1136100f1201c03078000c1611410322449041019006095000020130255947c80700c8060210701040c280402c144d0000442d400d80041c51004c25080e50056070001140318110a000d00c500c51000d407183d00c008800d00400a11026000c1c012902d5910140010307421079a040c4401c03034410b174990444c40d218441c80d005c88035142c943c0024040904c400f1600444100302c1806014006421050390106a088030411070000305d6181e60f584500000552250402c0d40c058441005900c500500c0c0000611007140d004c0c0c076090380780101c801c01c0340e40100001c1c10181e00180019421303010b40c0202e40e0f1503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775904280 1250 775903030 775903049
    0x70f1a0904111803070b251b03031107150c030c0c030b0603150106140a0e0603012c011a0a0c0b0c0a030b12031e041d0a061d0619 57
    0x480d2414400342c640c4000103c0c0d90032122150070360003500380003e01c0e000b05e41c658100b1500e840f50704000c004100d4511945203440d040f04140c0d4001242810004565032405150400ea10910311b18000d8291150007480040b1a0461641005401010301d020200e2611a0030400741944051804907110351116500410780c0309050408018007440102562040b142038045404400c00290364030242e040074428107001900902c94207840c0c820000140c529076141d424110708950b1a50001109504240c02030403800002440006201e440c0c030b4291030918184c1c141030450f550404101c0c02d95403080010348141c402000940d220880d102d50010600c583e00020220f5003400e10400200f41a44814481000642013100c410741628006859031011710100000354605100030515400064600c84400451041440006180c80300c034030761a02c3ca000021407194242ca4041510000c0740c0e0907800200008059030080741483c00c14941c0c032034000340121541c0541c5a019441003561108980180000c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775905530 1250 775904280 775904291
    0xe0601090810050115020c0307050f04150e150a030305040302090705040506070f02030c1e0f120d0f0215130b06031c12050a020f040b2a0c0909070f1a0904 68
    0x200b010340c0894141c9030700a0200041c00445030080340c4d41c542e10152541c7c56041820104242d18041c6e1101d6640b29010704007081c1d040f01c20003e40706080e80c0e64407007010348044408001555840d06644011400308441013050182552001011401140402405001c0040204480b030707010b80b080d500184001070030956140002d2805014009e140340c0228000c1c1320305620070308030b488c0a4041100d401114010000c06501d4070042102c082e1480140175040150241081c0b036010050000d129890f02035226040d010380b04010081c03821b02d40e14038a6040d01c4041d400c2c02088a13840a0907018290004c110322190303240c0c2d00c002402c00b40709003400c041951201c1c0d02c45113020b0b0802d481014042c3c0340340b41040be540c0c0d840e81c07005c1a407064410f0b249814104000030310100c644040905040c00d101c5020700080c900c60000010400d83c0781c000646198481c013507081991400c1d454680d807000d80c01e03014081d131526058000c060b13294140140f141c145002503561068084260603210303203540c0100103104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775906780 1250 775905530 775905553
    0xf151f090b040603170d060801061809060605030109210503190902041410090b030109020d120903080d09060e0a0201081b0d090c0512150f131202010e0d03150e06010908 74
    0x43d43d41c00440c4406c0c080d810a400042c154006210b402c045070074060000d20f030a00701803c0840104001801200e000e680d59902290a0f00c0911504520324803030940403140d914003180c2e1a07211034416800c1410007808004000c2200041344800900d480349180114071481c46d40f00180c00f524150750066081e00030300c03040001303004041d403080d4101d07004200704101c0650a00141400d031a00e00c2c80107034000000310340c0200003c100110151b6000120702c0c2416110f92203954144655010320b04d25041207888486c0141441018480c508031507122078000c2c0000c83e0207500107401800000c0c40140d440c1c14040d03580740200a00707802ca400c1c403003c40008111031069840e1400e8071825a00902d401a507080101204030400024401306d042001003403101c060756000701c81d00003050000d11030141010040c40d03880006200455200080d826034002141542910545901e0700407010001000c05040444100300746103103440c00b10503034009031040d0020307507120b00c010380d88020b0560040c105841030f0111001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775908030 1250 775906780 775906823
    0x8030714240a0f15032a0303030906052406030903121806090a05060f150d0c142407050109140f0d1e0c060e0f151f090b040603 56
    0x188604441d090403c00c21150b1400078048414440c824420921a0281803000c12074014019801d40d412076484400381e5070880180300d038a00c1c039500c1100887c0e10303020304000300080b50141e6035000303080c08a0b1103035520382c10710025030182c1466000c502410001000c0380c00c000701070040b03809120905903091950b0400281c90312401d403031021100349c28000c14000c81c00051000c030304400c12940203401003186840f400700c2d05c2e00380c0d200503040300c591042086920126480d00f600035000360f03005028160381a0b150181691094549072802407003095a003441640403600a00001e800e0078040d2030b007a484400f00d28101d801050a6000600035091910141100f0500011301e0705c1030503003c80035203000f028040c90a43c0c50110482640c81c51105415040754440d109100f8500d155025200110b4240d03681d440c6103003001c40007c011080d41c0c02210007a8117918150201541151802c62010a001d83c2c501c54801c3c090014060001c1150315a14004466a0b5642200002d103030070050011a84500e0200794 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775909280 1250 775908030 775908103
    0x30608071403010c0503060607141c020109030914180c040519030c0905070504050f1302190810051503130503040b03010501030e280f06110c0f010608030714 69
    0x502c0796082c4035050400c0c5200d507040d82d02948001c0e00080c1000302a588030902c94071a065280b481d44a010203e03615884082d644511600e0280c00000b902003072400d000703000b20410f801019515601c1815494135444004120042052410303031611079845d82c1c071001250b0710455002d280d2090b081ea07140c051003016101d5080880f88030341c80c2c024065a8400c48a42500d900300c1d0110301045050004000600b09135100d08c20700d0b40c00a180407510400e980e501d42c101d0300401c1d045081d41000c41e1428030000c3c0c00025031500501c1d9401c0000d201444c00000a60015184070032462044022000c10a0050f80c0400322a0300369101003601d8482c1e48800803000fa0750000d104590000c0c0c10002607805903500030801c03c0b40c0001084060b50342103100745149141c41d90415045401c0744c150030701c0c0c5001c100030b0311906d96a19110140c8039691200707002c500f80340014643d0607031103d914064007005003071000400c40f036130541d00c40d010010311200000c0460401c9600320700962065400201c0288542c0351b403c03c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775910530 1250 775909280 775909319
    0xc0c0a09150e010f090b2202040609080c102a03020303061503040b04120e04020301140916080718030b070207170102070308041106091507020a060314070e0103060807 73
    0x315007465541d44498001078081c4200c401c0d034080c000d0700b4812081c8503000f011030481d016000c11140502d82c030240b2a20800e425a0030000da90116042c07003020303842010080144141c6004090499040001030707a095055400e00f4140249188030f0302c1200001040c1e0501e0030501c01041030300c55160705010303440340c0c8111a05846500c0708020341c8904412401a0f0b405540c014074108825652691203a20481440500c1001d02100d007403113480c0340d86d45000a50182172610500940881b071381050000640c0081d03c0705460359030070341c4080d55550303004016507840b100d20328281130800d103400400c2c000607600350405044954842d040042e503d03000141c04040f82c901d03090141c0c001c070040010300d080340a000b07002400510b9030000318000c901c81d0030b0422008000200030528103901880010004081d80145240f0341d5004110b003800c0d46092002100101201d0a05100c06203100c070040b800b90200404230010b0007012481070110b0b03440b9a00540150014000316941607450b100380364a401252802e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775911780 1250 775910530 775910561
    0x308120f0f010b270d05010b120604021305061f11120c0a0b060613080601081006120305160b0c090a0f060e010804140328020714060c0c0a09 62
    0x10407000d60581d440181220b405000342400d05020705900c0b0f54982e02026070101d81d441e600d01030000c603640c4452003910f040c41040001401900b42003804003440480c00001c4541c3c002204020250719104000c2400d0314010200003029514000000d0b08a4078114565081c115945045143d9503080b102c00a01044858100c40e04103050300c1144c5e405110740820b0f98140d400c0b040314040080c03018280d81d50414401010f07141800340902e13250b0b0790300c0c1c0300b9804034401e9409072004201c05030302840a2a042c40700d40c4824018030303041030101107000d685100003c04000c80040c40c006882803580d000080035038441c0704898203007040b40b038240c82a0440808a449410445400241c0031740d2004031030111481a01c81e1842044501c0040d206403800030b000fa0750112483d1650041c1c1c0300c00b44014901d440030b078a07106a030413081361581c0401203070b810f58003025980300e02020700580108401c2e80090b46400ca80ba56a1011103084983c202540180c8003900481e0400000c541e0f00280c6c1c1003c22407449410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775913030 1250 775911780 775911811
    0x180b0306060904050714031f0b01080a0212070f20060105330a090e0c0304030e03010221060103020d0e0706020f07060e1302070f1a10030305031f030812 67
    0x1d0801501c03100545009080780d0102104200355074090305c0040400340024243c5000c525540d550105070080100c01400190340d60341c07d00b4066170000032058104450000450174020a040c1c0d0b00920a8090044020701117520400b44005100312106140c0e850119000042050448034569450b00b0a00a6922038000014105900b072401c10461004c8490010208403042042c4062103855100f05403131401c01511841c0403d00172042c444082c0200260b03c1f100e540d03460641801000d2008105565100342d0040290811651128424180f00500380c1c2d010f0300b85032110001a4000d100c1d60700b001480905000302071810220228840c0308441d140d800396441a920028000c0d15200580030301800315002d41c40030019401d000310410b0f1829080c060041c603000d0300e03450b5400a0060381c50b003103515042d0380003031056a1013052282c0f508441560710880700b43e400c0d13075000380103400001d006860401120418030580e203c00802d0000442c2c10003020340e5134440a000b40b42d02e03104102e5510880741c0082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775914280 1250 775913030 775913041
    0x1c1a07050a1e0c050703080901030609290f040e0c030c03030309071e03140d0201060602060c0904200403150b010f05030a091103010c111203010605031f180b0306 71
    0x5000719541d6810a079154a040c40c0c402a5481d240041080c0d0401003161800380310000840c10801800918099041940c6a54000c40014261062a0485000107050142104111150808001151401490700c013035114003900030803841c0c00d611003626403203801d0031007441c6200404621074100d600260203489858905505040c2c0c0c82c0b105607a8a20301364800c0c0d000300b01200c2090140340f01d001081c02900b02c00ba599499218052012120000c2c040e0080704610042d250244640c0004160500141849240480d440d42c00b074020110703210700594441e0441441041d1040c541e600b002070060500303454603281c1c14205003550030303860043c0c48149496400c50b010360282440042c041c00c55510a07183d582ca00c0d00040103030201180444404902c45040380302d55400f0b000b030707003c085019071342d40e02040380c00c0305078a14107186989131000c1e4010820051001310390250031603600280c600c0400903511054010322031405100da00402506121518414040003541c0200da042c8000320b040b60806d03242e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775915530 1250 775914280 775914287
    0xb09012405040f150e0a0e0a0b07110d0e10050d0c020a17040b0306010309050109120f09090b090403050c030708070807210c0b150310021207080103030c03030b1c1a07 73
    0x5201c2c58008202c21801d01300303e43d428017404c06078008200701c0c0104619110101175850103200d040101c852007480c00030451f2941c0e0180403022901c120200404250110f030a01426178483c065581d07010b001081c00007451540228110307070b001801c0e440f08000c0107a40e80402034a401ca0741008903080a8030500401d5560a12415102a036100c41b070000c0c80c507200e010056004160018085806540360611600801c480000031408043d66440b403c0311900c7c8080000c0123200c99070003a5414038500500c503001a115900c01d070354800d0745030078040e41c0d520181780c82e10b207180500b0301c004000040000d030740008c01c03040e440a008031b580300b60010a25071584c1d190039100d5007602c0c030704030000502d40840c120101d903603070912540001d80b0f41040d800c40303140140420305100c4828864082d003900050700c00c06a1002520203036200e08140340c03491555045580042080c2031001d40682016201c50b55080940e0b94410030003408542d0700c00c415800311061521000c1d111142204400303030044240007a451500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775916780 1250 775915530 775915541
    0xd050603070e070c11100804060c1b080d020c120711180703050414071e0608190203070e06071103010e01061a0c01020c010c09080f0307030c0b09012405040f 69
    0x2c0c8103402901555a95008860411030302c40181c4490360000d10714000b82d222410341d00b48080003543c500f00c1c0c42c0b800382845c0c0c5c00c1ea504803600b0010444002040400781c0200300380c036031049070301100ca15910100c643d1894042c0c010384010340781e24011040c00d808001c00d11801084041d00c2401040c058000350410000c40d071600c414008120740740c40740010500740c800d0780301a920602c911030001a070b100d00d82000f89040300c150890003041c114001400300800b000e1407040000c1c4507074500000940b5100041c1004400c10841103154250007001280081b4000e0508800d0701401070700b06501d60a13a0301340395540f0041180d460303009519180705540440e10601405042d1440800e100c2c6240300070485061455000710690482d5545c240310b0007040c02820f010b2584d0a04156444866260600280d01e04014a5542c02c0a450740100400e000081d0441d281d80c0300b994200038041c42e940c2ea141d60f51405001550002044001c0c941c5c4a010090b848403000c0c1c081c3c800540d0200020071010500104452 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775918030 1250 775916780 775916789
    0x1609060303120c140d0c0801080a240b03011406011229011101090c05030f0c0f04020a0318080307090501050403021507020d0c0902042c1b1e0d05060307 67
    0x1d039040e102022031081900071150780e10315450482d280401ca1111913645030440713040c0c9845a0744a041c2c0043e1180d0011006001d800600c01820310100c07180d41d03174510303a0300451200341343c60004004540744000c070381e22104511340040c000303010080340303450680c000310310440d50f15000c07582c68403814810300c44612404040e00407d4003e1340d030158110903000b450f8052818941d0401c40018440c0702211000c0c001c1c184818490141070750200d08010805040402c62400700c9050351154000c80200d554028101c00c3e03003241500c006940b04030307141041303001c0c084c800300c24103400100728903100c00c204a41c40114412942a6200c00109880303000440d40380c07156205c0607611050025010081c0d40800c0014442e840c40144207440c070b0141992140400c0c41c0c81e0380051080d03540414200092182d501c1004084d4039075504e1508a6000345600c00d1444401904000d4120b510f6403910100c182c0440c100d418550908032501c0070469590441910307640088660240c450803c000314400d8140022410241e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775919280 1250 775918030 775918037
    0x2403132001140c010207050304080a020301140c0412020a09022704061d0c0c060403020c040b0114031302030c21010b06190302030702100906020901020601060e060a080c0706020c1609060303 83
    0x2c0c0082036034816070341011803c4001554200b081d10000344040004100910700b610203007000c000c140c0101421502c0d01034018006450710020403840c1c0a00d130b0115402d40305294144030002071540045141c0441641004040b90b00c00107120300b4850442ca00d10f43c221001450184012a200c01400192a02c43c411514100301d22a000d041140040703400355400005071060505288648100c1894514155401d50150f0460500c01055013018010700d804140700b800c0240024100302c001c070381e161100401c0b551650602d400c5000031503505128001c1c150360020200505091200b19800c14400c041079400095881d001c264481400c18a06460f110903480071801c41c0e40420400a4000e940300801b8541140110340305030184e9600c500c00c0441540c000c0e0b500689840f001c0c4000391404006801000500011801c2d00708183d0340d0000300c580d0146145040019078540780c41d02259405040d0300207200e0750020904001311200020300403a5030203148500d20b6019980c51112045604900010740007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775920530 1250 775919280 775919297
    0x605030c04020c0a0519140c0d06090201030e03031f0f0b070b100f0906180509120a0309020a0e040b01060309020109030b07110d0f1404050f2403132001 67
    0x515040c0e014091240030f0500703036002d11000d5a13411b82054048100200004404051301050110b10031811400c0e4a50000a080c14510302000440300011401c008110380c2d100ca03204000c69120350440c42d89034541c40112034890420440810160000002c0000c0201009400203544405003003484120360b00070b80484e00d0000309881d004091340000f40814030801800c080051a5050090118010945040c00140c02410002c81c03400000d9111b40d24b45070f940c142828089110000314440d0b550f100d070b00e124130740e030ba5103034039401e602902e03420704007a511680d180000500c048803559010310441c46008a038107203030303210b480c164103c4803864000303400568281c40900000346a420001d030044910309044802211007800c680c0b0709201c214090380001d610107032080c04180c105210386290841440039900b01814140400d4200c002e030001c2621070707004000000700421112100700544e80c0c1001e2020f50380d00e003182c400c83d56204101030031944603813603000b401e030b031154860881107031503030b05a540c4c010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775921780 1250 775920530 775920553
    0xc0d020c1e1828090c09050f01061d040204030c050103152409150f0201060b0f07060f060f06020304180212072a1406010611032709010305011e060503 66
    0x59544005040c0e0380c030441d8254268084444214a050000b8240300d030100f4007105a241091818a00d83c0c880c501c054100760070320040320b43d140c0c1441e05481841c032f05503010084030018070a12030890b000c0b1607003080c4000f4000c814041c682000300242c139000c1c0c80500001030084048100010240b14003a07040042600c5000c50040300d02240903110350320301c1d00c00c1c8100c0d181c45038066078850803420310000c5004070040723f488035028089c1d07000900440c0c0200b4201110003154060a1081850060005a4800e801d242202c501d41c4000003500b0000428030840f034031000082d68a81c030500a80d04400c1d641107040c803042105000f1103100804500c500b50154407200c9098030816000c03032803d00c1c58080000d5201d8841c00114501a4250003a00b000090b4041082440c1c10000182c10140401185c5a06a200d0b400000101c0300200c1c07503104091000702e9000d0203800030081c80b02c103003540141420000001e01c40d05400280d05030205104040c4200240140141195028030030541c168104500064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775923030 1250 775921780 775921819
    0x313080a031b03020306030c0604080a030c06151d0a1811130e0705130504050c120708060c0d0b040e0607051809010e01170d02210c0d020c1e 62
    0x260040e45401c001c20001c60150803100941c8003000501d00203580401001580e1904112650a210041d076843e85050709100c4c05503220040038901070305002c9010404001c00200b9440340034448a074482c0d5146180d1151400b0f042c100c003610340c40003040d4010000c00c001c92580e00c1150a602500c0e003100b0391115542c0c0d00e1080328004420b00540c444080b0125201c0b49055014441d0040d0001016150241c00c00e41000144641a003040443e40d00d41401c02001400001d0411100314003112030914600005204030b1400318590403034480e6000b0002032000440f0300e0703c0074044004000300700380902c01e201405d0004461550390b55020f280d0001000c280c0c1c1a001d607008000402031a400d4a00f0702030300300c0204182940a0b4000700ca00c04c0c0300001042102900c06180c07e51200d0000034000214075504001d580f008207400c502c1502d0070300b40311104480055822520580104415900c24a4000710003940341c0740340f668040e0082102c024152910b4a6040141d84a80c000070030180028102c2c0f440039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775924280 1250 775923030 775923037
    0x20a030821250e040630020d0f02130c0305010e010803030f0708090c150d11040f09020904020c0613050c030708060f0a0603050f0604061409100b0f100809010e03031308 74
    0x50b010301c0003000483c601d946450003408040e2414005140380e5410703c5a044400d005458440490241003c0d00c82d401a0303914250296003640144950010995900002c1e00140c0300c0c40c40c0503100c5150422041d10b0f6605600f000e03040380c050700c8245403076aa8805000f078807803204070b030318180560351440025440c0c0d0060030541c3d04041e9000440d010840c00704041805410549501290075202082d0800444a6400313007c54500e18402c00c0c42c20980741000d00c1000c2c000d24001c6990041d0003180640b11600ca80d41503038010f404020440d0301504081c540410703000002c1c5000e90b035600580d0f6800805040001d1040200e4022400410b441c0d900d60384100404403001c0e102542c3c00351a06000000b01301e00300109401a0000d101a14031400c26291080868807031002881040004404001481c01d000c10303811020900c8a0010858201620008944401641010341c0c403403a10174500303080c0d0340d00001e4144140f008d00000c00440c2c0e05441460307503234001121090a210507901402d4000740070a00034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775925530 1250 775924280 775924351
    0x603020d0615211103120a030203090309220515010e011b061b0f18060c020a0e0702030c12040e06130905030f07060c080907090e0703020a030821 64
    0x4141c0d0103071590f00b0060001c40b8902e10600c0100030b6001c441c103110001c0a0a118600110001c141194a404411825000d055140400d155010001800d814030600803581562401095006440c7d20700f0b0008a1101043d00e50366403c910b410001619881102001450b813903058507002d40314080d01c0011201c0c5d00303460000b164000c280500040015809002d0381006240041c020b42490007844001000c203a11040100c0070850358420300105402c40d22401e00c2035031554a03022a05c00c24500101c2c410f000b6070381c040442c00c5540c0040000e040c0c0e011000d0080c1c002d09c0d800361500041d4002c1540454095402003811100c40040070918a144c0f911185134803030f469840204e202c41098884504680009542c0c1c2900f160024881c0d040003100c3c4a8038100c03864505051441d400c028a01507510240b5003c0c0e80822582ca100c541031403001000110019903000b0715004c6026202d1400503032a800100c0000c1000c040280c3e464840b4a80020952180f640d41d0320404000740740b02e8450002000342001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775926780 1250 775925530 775925561
    0xb0105031f1e0e0702210f130905100b04180b120a031d030d090608190905030702010e220b0117040507051f080103060f06050d060f0c030603020d06 65
    0x5000410004007001401040040b058101c0240d1810b80c00c01160b000c010081403c6401a0422000785e000f48400710b98280340610700980c90754101c0d14031b0a00c034460410348404c3c020714843c0000312070328150402441141020280120142d848145440c2070069024011300c01d000004400b9052045a210a0201400070a40400d801902e18070508003078a03a001640003c00d030a405407030b10b208048404030040b1041d40104185161a034005100500342e0141da01008940d401244102d6440364030032442d01d44086080014826611b0910786c3c0764408041207001c6030f00d4901e40ca10500c1d0000c1c44c40c2d400121803a05040354401c1074500c10080030410000ca041c49640403013141e401d8044c0c0c24a611840c4280001c0030a41c3c1440204944040785404465500803225280344007154402ca8440c1101d60100c004108159540e5450b400783c060390b00010340042d00c42d030004041c03084641002d0200c240f00c1e4030802c40020f607001c045047c1c0d40c1074040a03412106a03500342c0300040580c0d00ca41d0a00c6810300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775928030 1250 775926780 775926841
    0x9080c060d0e01061a03060901120b060f130e070f0b09030304030305090103060b0c011a100e0f061b0a060b0109120305210109090c050909120304030908030712120b010503 75
    0x14a10086050b140c4100c0c05c103810040704224140c00c082e200345002d030000b03411011045035641d0341e1400800c00142007a001d1a440c4c4231402480c2c9900b0341e403440c01024035a00b4402000489900341e51512284504428515501c1000550800a200b01d460034013003e00518500740c1161403d4a1942c0501ca1650406541361760000b03440d0780c941c1c040c1c111b0080030f50010030110002007103031014101e0301e05440e2103061180d100260850300300104001150040d203446c030030750403100006406030094034076000e0311141d0090700492045020a03541811071240c6810081c40b103c42d401140c240300c0c140600e911022070070a000380401d018502030034022440d081701010301d901910354421000e0080e80091002d9840b41040020814000c1144028103010303200b00c03480e4988040550744d214008201251000340c00000320307080c9449940441d010f00b91840407207644400f81e24004d14130b056a00300c0c850015001048040110301e50b8050340c07280140583d00c45046403503820030140080094101030800d0840c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775929280 1250 775928030 775928039
    0x201051f063507030c18090e120d05180105040b010506160c0f14040b030d0c02060d0504030f08090c090115090320121f020306010c08130609080c060d0e0106 69
    0x50000c1d00c20840c2e091030405003802d06010150a48800344020030521103801041d200210a0200030021a40584004120b00280b560550f0521300c14013540e103462103000600c0c1004a0003a0402c07401020400398009003450b01e100100e08844040c1c40c002d0450200300010000c40c60300402074111a10300381034501c108072059861102d1565554840340b480e070301d03004041103c00030400051a103200305580a110001c204000a03499401300e00c0c00d1030030b009103009001d0540d118803080d500c007210140020030060502e410040d19819076080340000040f4200001442c952022030326068052000d032508085908000c66503e105041e400e0180c1005104000000032130b03040782d05081500e160040301c4c4030045100c0140311035648a0301c95244260f00081c10b90005d417586100e003a0003240000c1c0016140d0700e68400407a027206500d44050580c06000c1822081555403003005d808407000c0d500c43c1909155640c51654031040d44e40c030780f0760388079400340010480f0915070303000b510009458100000740305864 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775930530 1250 775929280 775929347
    0x9170703060b010e19060206070e090f04060605030303010e0a1121040201051c1a060712031a1503240f21120d1415100908011b0201051f06 61
    0x1d2140030905c00d0700c60100302c510340510019401c002140340180044202c40049200c0c0000580210250401440004c003800709070b602401c068039000f82580e50320b5070746102101316110306442101d41d080c5407041480c20010f103030f81180c05560f001341c4422445c0060185040808200038016410303c00100180070000650074001d0107031f800e0f04400000c000c5041c4940280c0d190500352842e008003010070090010904003080030300e0866003480d01007100380340c144844021240043c07009801c031300e42a0011035000d8101025521844a1005c440c1d440186100305404a4a400ba412070300843c040b0a100481e00300000e2003d00000c40c1c080c9d07030341d44d5428901074525041040d40800410b0704007250b1040f549000e4011004440d10b070700d1028480381000c47e5020080402d00d4a154030410000b1301990209008800960040000070020070801c0c0445050b8030206011102d410015440d21000401e0310710f110a030824440182c00842001d2810468107441511003c0c0103400342c468002d0010004440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775931780 1250 775930530 775930549
    0x40b0414061f09050408041e0803160b0f190903030e07030503030f01060e06030109091a010f0807090e1e070305030c030703030f020304050d0e01180b0a09170703060b010e 75
    0x1031422111030300b21668000e484801200b40c1107141d4040c10301e402d00c4041040035040d0780540b070600c1c640c0d01019207080504584403032158000000e500012a00c00448c0a0301100d9104041c001c00540b40d20356030320581d807880f440d01241c40c09000300001f80c03030310381e03500880d07104224061090500140b0087c207a400585410f20b1580103c0c0c0640c0004100902041c0d4454400e0041000d8141002d01581c42c90016040e07000500a10740c2e500d59075012441400301c0004a985901e10019a120031540c44003071040c00e40c94180149a100e218074640080c1a801c1e500c255001d2900f01c0c40901b08018040c000f04862250500603c5014030482c2d0000c070111300140300602010041e0f01c019540d40800e403501400743d41c45070501d034085520500c2080081100400d060701002c009280900610000c00c0050380c800019682d160420000c00c240890140000c070028945052583c44005a0726034a4202c129002d091040b007540a8100e40e00c10800500507420020410105043c002d01705000c030b1000c140c5140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775933030 1250 775931780 775931791
    0xc1a130b03061005070c03150f0c0e010e030307020a03020f030a080315090601030b0f04050a200c1002040b040b030903040513051e06010507140a020a060206040308010e0f040b041406 80
    0x380000c140b02482c60b18030400501c40c0c0941c104107050a21a46416004406920024050810740f01100d1a40c00311a804501c20480c145020009466401c0e001440c04003500c40080c040380160742c0d80080c42c58000305403210254000c082d240c8030340c10340e400c4c04855080f540801e90988210002d2000180080014600c10800484203c1c540d113003a00810040a0000e0302d214185441e010001380103440b100c00c4403d09040c20365001c24152105409840202a0241d01403604280308092441c1921035000134020401048221160b00f08400041402c9218a2041c900344210400040005409001c0650f0340614107409613410310b5a980d000c1142980c01280ba03201c0d06a4a00811502102d8020b400010405682c82c03c0001d01c1c0c04000681540324684003d4450045450606a5080b00300b058012860340075081c040ca6565645000e5035540064170704a011a82200020a0303541c2e490b080c031031103118140b03103004658850b070321042000704008d0310075107410180210303144002c541084900d00a2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775934280 1250 775933030 775933049
    0x614070602160c090b150714060106020706021216031d1c150b100e0a0506040807150e0a060806190308090102010b030a0c0e1003120f0806010c0c1a13 66
    0x2010076107800c84101a1070742140c1e013034902d00060b42403191207004a01c0380310000340450542c0c50241f070034002c0c040c4003e02c41c111141e00c1407400108181b94041022070483e415602103078400c80014041803043d0086402c00b400f0f0801c590940c0c00031030320503001c00d161050307142c9901403c0602c403404030b0066810104034802804a0303040010400c0f84401c203480002412800400442d100038000072895006c0065010402181d2450b1003803555403480340800270305000b0406943c4d2a5a0741c00140c0340c131103034420351002c0031417543d0b001d03171041c007442186032528802000d40002a04015003a2020072003d030200fa0480c0303904400320524413600320f01c4c5014502a10700c05441e2400d0500090075501141c0085000340c101d024407800184140c103840003a103011114113803941c0d07904803000b104000c1c07540c00604040034070702c201081d09800074661881c4403610f64072500b2655501e00159a104070780800180400000b5104002d410142807a1420528484c10038500d004c80c440600f40c452001a0485c0309030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775935530 1250 775934280 775934317
    0xa120c08070f02060709030b10120b090705010206011809060209040e0c0a090c350c0306150403050307060e21210415050a180308060901050306100614070602 69
    0x7803604800c1c609070307a95651004003a00c0c903191400074034000d0315100041480c0703114404142141d010a13480c001801c0405011006200d950911407070104042d612503561f8041d680000c00c155201140700b6041ea40490705c140c0e000c41d201c44940700102400e00703040c1c420513400d20003001141d945020344446140c050000380402c03000c580410040c044c030365006c4401613140c1070200351059000b102144041c203100c1100c1181021844940403840304049031000103810000800890503460b0000c0c50080c401683c1c0380402b2551442041405d02c940d00000c0c0842d8402e1100324000f5005400020741442120709890801d4005240d010320145155188400e1340400f0170380300d1529800203d010001c40c4458641e407046e0405448117421646450851082c442d101c10001d842000c0343c1e0030681d00100b0705440c07a140e03611039003001001444165141c030310400151000082500d8000307000742c0201c2c981700c141080e003450040250303681d8074850040410b0000611246c008541103101070980b414040080b80b96 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775936780 1250 775935530 775935541
    0x230d06060c0c0602030315010e0f0a0b1e040b0f0c0c152d0901260c0a0f02010b1e01020c060d0b03190b010311130c0203190c0f080a120c08 61
    0x1c0b940303440d000142154001e0040100080070200c80244041c8227003090034001c401c042c00304200303002c4803c901d508a00b02d0032000462080c550b000b03080b80c155200007290030900d081101d01c10b5100d01d2081e0503403c00d00b4003d044e4403850500003009140150403c854002410304040390a0b00c024001e01a50f9000204541400c01c2d04611700450038901c090a241905480524940f00c900810140034100880c40c4208401003040d0782504a603100001c0c1e002d81c0503d032004002a4a50080e815040090070b8070110f080c01d58014050800d54903030040002c0e20300552481c030b485c6119011401541107205001b09682240c46072030051207403441118000c20f0046d0f506051510b450364200c1d000d8800c00707074840d5a1000c030b201e0f0305540d415030307900000341c9018409075000150311400c0000b00126032860080f00411083d0004001c0c4a01d140a21000d0681c4500403010b0310f03c04071240c0302801050400b402c050009503400700034800c800c1c00e42030040075000c10f511618200d5082e1002e032004151040c05008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775938030 1250 775936780 775936793
    0x5030a140d0c0806010e03191403130b1804020307080c030c040b12100608070207090f0b03030d0e01050601030209130e0102160317060604180b0102010f0905030301030209060a0501230d06060c 84
    0x1a501c0a041d1f000302041c1140307001201804108080240400040855030b2061203c207004595908100d041500000c5403071720700001c220703446481c8640c2c0c4190186a0614541000d009403071060300340751202e503600c1e0b5a0103a13403900c6030710042000220820401000c60b030f10714640c001c1c0c140d00200c0d503211101ca00e401c01c07410540c1c054030707004074051200c0c1c2400c02110790f6002070f00340b064481400010070000c0c440030089010f8600c041031301c3c3d81400b000c50110892455580100c2c042d800040090001e91204401913040384207801c0c569030042404940a03912101c1c540040d40028410707000149003500c40f4120420010803a80120000707180d18100c0214038400c1652560001401c84101d4502845e0100340704282e040e40340701c20f504a841c0c3c141c0c810175a000f9030140c000000169018045500c031b0f032514540300d0b802404100e02c1042580d0124400f8140054450145c2e40306842d9070070180b100340388040005426407100340c0c50020401544c500b050445c018500200503645500c0c480161303515080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775939280 1250 775938030 775938047
    0xb0f0408070609120f02030c1507170a1202031e040f03020d030203060a0512070305011a03010e070605030c07080c010f020d0b1219020103020c07060c05100905030a140d0c080601 78
    0xd04205903460300740032114400842080c0c1c0d07644003e2017480b401c901d2003c20300784446002c1c1241d02084c4d24a40510486460005124151041a4014080a100840b64118010503098000003109001f800d0200d90255000715002084d24001e444620b50310302d80c00014160894080300c6034040907500104142d010801400c0c42c5980d400d0550643c80c0c91408601604281d228035446400d515008104988042c4900300140d500071000380700201070082e42c0403d5a125041da2802580390049009030184041140341c01e03079a9540c3c61500d107881b1040303403030303a01d80188005540b813840c01c000842980708244038001060300242e501503211400b0400e810222002005024003640b1107191501c01076101188100c0000c035040040c000b030700c0b114001203000380203103056207004c0d118040300071900b160040412250386200e20221166400e82070046426100c10140040980d40188420114203006074444551410108000c1e8140200c2d140304e1415540c40300202720202c0c00c5402444034035640301500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775940530 1250 775939280 775939289
    0x151806020c120601030b04150b120120040f03240c0806130506030607080901020d1802120d050307050306040e37020a14061303030806030d0809060a0c05040b0f040807 73
    0x83d02c0381d50f01d0341e00c0364180a00001c10041580c0d07403501480d1000361b941c0e0b025915005001c3c044e4003941d020102014020640710501943e100311907190700c00c030b4039807810880c0c0c2510400c000b1000114910750711440072011400c030394640030800115901e038101c8640f255484100d038a565101240c1090014440c4510301801158205401d1404104031034800092854216003549081d00c4140d599051041c0240101180c02d840e1030708190841074500e409861066201c0c0c000c0355580c0c440d4960b440a6642c40808412903404910b06200040c0e05030701071009183c1c00b00024201143d0139040340441801e200c40a88007003250070b04484d40d90001c010105c0c1e00d420b02158500e80307161035122500004c200c0700d080e10900f039206249540001d11038540e602602c140c0840056000c0d24561039103400360111004561160103807090a4076042080e200b07100c141d0107001c4d0341014005a44a0100110160000c003040d031082c440100300006501458000404c07218505c0f90080351a142440c03146810030790554030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775941780 1250 775940530 775940533
    0x318030f0d090f0909030507170f1605010e01020c100b010c020d150e030f121003020907020a110d11090702160b070c050303030103170705210705060f01060801151806020c12 76
    0x34890006c2d42180071546100e030080309900c150024290030106c0b6100c3c00254139405480420305600d0400000c140c03500e92440b550081c040c4103d184079140c200d0041c00c1d1000200c1c0e0013400403130b0101c02590300001031408107150030103980c09107030003080c01d5468282c800c4500c00b82d0401181103984030f91144031140310030750b40614a4030031982d005650310301a4080d14401840c01c000882c81c1e0302e81600c1000020355000d0040822450b1a41000c0d49555012001703071a282c0032003940c20618900072184030342082e40819414400d4076403000340406244020080010b40c07040064404800d07140300801130003424a890410b6a4150328500801480c1c026170155000303510910040c000285130801e140040c04000c030107184c80e1045820300601d800c0c943c500c0151070031806035035100000c81b10b0004056041c000d03000c030307132060311200c0c034010b141e507400d1140900152454005104219042030640c8640c1071074903002001d001401c4800840c04159800b0f080945e0000c08006d5003070a0408007084641440c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775943030 1250 775941780 775941791
    0x8031003120f02031c0905010c030c08010e010e0408031806161103070515040309090e06061c020a0e0c250203071a030c0a0504080313030c09060302030318030f0d090f09 74
    0x1900070b940c070300941001c429001810466034070545e6166028211007500f280090100a10b5014090000c200203030070000001e800c0307800400e00c40a000d01081c12602d151100c103035242c0d25074482c0407041c0c01c00b4080c3d11118505080c00500707210100300d8540945d00c1139a840e540071144c0c00c0c02606490741011486140d8209001c00740120708041150b51201081068907a51540d5a26007111000380030b8100380760b0207140203000406ca40000415920500050720446000200320320688030690600000951081c11200107004140c4e500e01c1c81900007038401d41c094180300390042d0703260240f003003c0c42e400784500f8104100380035072034200201e03402400175094180d8030466101c007001309071000a12040b803540c070009004089921400864005260300c03400d40780c07a0454101e0000f042c0e0003600c810345185070000c00201c0d4000d0300c0e20079902140d6006000b146019566014014510708801c0619454000c07a540b040d1041000d10400c1a00d0035a5603d2620b00d608114810081e0b289942090304d0702450035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775944280 1250 775943030 775943057
    0xa0605031e0a200303040b03062d190f0308031501080106021207020a0f080a1b060509151b06040311160501030f11190e090609160c0803100312 63
    0x2061038200700382c01c0044070b858807440751011018081c050380030f0b903014400000c00050399060300001c0d50040300d088500e6403000c2000380b004809609000c41c00c1450300d410880783c202c0c507d0801c2d0055414200307020140c0c082d9a4400d95408071460340d50041d20340c0d240000c20000640500810403001140074200074080c1d504001e4000d59810011560350b81c0c0040001da104295a034151000c002030035000303001c8481540703c030f40c52603c079a011901158440135211841d40c040007150545410b450341a9211800c0212400401403040c01c01201100300003c00c10040b180c0d00031401c0c0d0000c00ea0307000d90041c4018106031030020710a0a0b00ca1515000750005060400f14070300d00c00d0404221902482d020484007401a072803030042100c0328016181e01e000040345144000403600c0b410243d2401c2e1a07041d44401c5000c2030042110b0100d5142c2c0d070100381c00002404c401080c104842c440c01889c40c2c00f4600c0340da00d07a074005480e4429164548542c0c001c0c43c0410800001d400c00303c078070801e6440c1c501c0c00e81144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775945530 1250 775944280 775944283
    0xf090b04142e050a02150a1406120d031503020d0615080102070b06090408192705090103080714030d0b0f01020a020102060f090a08072001020d020d08040303140a0605031e 75
    0xb191801030411030002200c2e464140308000340c0c8410344000d2040741c52820441c201d0300080400000c03050b0108a40d1001034414504294082100502280903140321564640118018aa140300344060141032007004400350301c4004004074001d1003184001008605020030b0000304c3c0655021230010382c01004150001031408000540050003641d81145603150303031070044202d00030003d10340c12001604544090240d40482e103400309c0e42e18604054104400c11410780c1c0b03403992500405412a035030100400c0011107034030042c58000d0150344880c4c1083c0f914600181107038800740700d0000c00358070398000341650300d007403a41030050f503000340000c00d110400c9070300107520380e40010000b9450711000c50000e50440300910000c1c5216500184455603120399281544204948491214480340d030180d92040395400000e842d1100e00c105d400400b0381c010014022200c0e110010421801c01d0b4844040340204059881024001c0502e00d0001c2007050500307081c14900f00301c0100e080180100d4a203544d01c0c4110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775946780 1250 775945530 775945609
    0x61303050a080c071407090c050c06190e070b1e0306030d232205040605011b080415022a06090402071e05070f050306040b070f090b0414 60
    0x201e800d01e11401d07502e00001040d2030061020242203840b40c928070300111480402c0e0b0509440c0004001c001c000c083c258115043c7c021148000c40d0b551000c00841c11500902c1d0408020701c030504800b0070701e00221030103c1d00f06111603024201160300800c22020045030b144540c1030269100b80007509606d850b4002a5a4a840b07c9441044c41500540100058012084080c0346a60840425964443c1016040e00c5440d11080311094190305000404c0524160003640112a0305039580c4860400c0d00703078400741070310503074804985440b0200320004045584c901e8501401d82c060f0050300707001c3c1403c0a0303403e5135201964441d03001c00031042141015640e4500380c2e0b040b60001e440050301c440c1c1c01e01e230007512080440c03031243d609020309100b9010054000342d18410ba40981d00400c075010fa80301c003459071711403050b00c005110701001800510001e102c0c070505107040f8258980000d51b40d0303072a103001030603600c03942050010305c43c0d2a171050f5103800d0070a9002c950021880c090a112003881071301d84030b00003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775948030 1250 775946780 775946797
    0x160206151002120307050711090f01050603090a0c0b0304150b100509030f072402030307020a030e01020a022d010212040b1c02030c0904060902180f0d0f0606060206130305 75
    0x20301025680c00c010300c200025840710050403111941c03410881c4028080c5c0c2c010307243c2100c072303400240010003c60800410035402503002c0030b10800542d081004011694100400403036091080001000110714109910b100070045405260380d00d09190030a01d036480e00840d001c1d8041800c0c070101070082d480f8800c8014040c407207484d100b03844e20307041000203042907a0001d524082e882260008604040c03c681e00c5000142000b0402d0306000300c8501c01c0c0d850b8001203070b4000158210050b003501290285108441142c0705105440301c0c01c510b42c0c00503042c0c240d0154040301d4407004030801460b03094540218440e101c0240010008503c008940c4140f81c411800380030303901400401c1c0204208040c14002c0212079110304103548034602034251003420307008240000e20881c28100d00146c01039082c030803141501c14050000250090041c180f0203190178184086400141c1d20310014049414400e600030040d1003100007080f4989882c60091a241010709003007007581101c00140e0020307800000300e800f1720 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775949280 1250 775948030 775948039
    0x60c030f1503250317130f0303090b07060605090702150702150a111b01020a020105060103140f040212010c0c06060609052407020a1e06210203040501020d060e16020615 74
    0x36910107000d443c1030000c03584010440925000520640c07101c15010b0904407880c80340c618201c0e0342d1810f405481d4000d601c03010340405c2ca82e02007444822064402880c1042c05824007184403941c2e90b000c644e8440085482c1c00040c0c00c06020030b40c410404030780c1140c00c020039100615045140c07895401c0c40000140041984030f0396a001c00720860114001d1359000c204403a1008401d4848176181d90107540500c40e0765005502e40400140c03a503000e0f11610300c5c0c0c1e40c0110044403080e52287d401d604424000b070018ac1c0d02609055129500320000d000d00c8081001940d1101406c000e5442d114040c3c0b43c40b40c01250078007110b00428016a00c40c0d410007041c0b282c0340342c040401742d11514500f84a40c0f14800e070182d000f05984402181c1401003a00e000c680160544403103030b8450752240101d075108030241e0807000b506401502030090f43c89907005150080c0c05100014030b41031580d081e40d41103d04580c060035484051008100580515010501801040b030020303010714076082c1c1c0c98001e503020040303e20380305 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775950530 1250 775949280 775949323
    0x503010606210905070b03013602090406030602030c09030118021c030c15050123061b070902160b0c03041109070e0a03080301092405041d060c030f1503 67
    0x4200090f000810115000000c0da0601500c0702552240b0354001d0045416072802001104c00c3d80110300b000d50902c02c1090340030190009040c0029001c0d5000b01d00680d4081c0c6c540f000480443c41030701c01140a0703512407091940e10b01e00e0005060071344022404e9084000b103450500303405a207940d0000c8010421580100391309990a1405a80e92401050007900c1c86980848100811007180e201506a5010944088460507000c00c0c000c031310507031007401c00c1d000366050101c60507810316240c0d6681c10713070429000d84401c940c60b15400c1c0202e80042e401a800d0311411001801072280c19050765030840d469425003483c2d032400741c5421000741404940d0303600403072890340040d1220b0300ca01e1140c507000500600c261070301c50b502e05100340d0301c3d04207000748506240780c103c003100741602101d00300000c3c08007141d2000009d4600b03010040209004400092991068880e003618403205015180c411509a1740380ca45900704008500c0329002c00404d8030040c041c0f00c6100b44019600003032048419411519000c1c43c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775951780 1250 775950530 775950587
    0xc030c120a0506120105041a0a020913090b060303040f050904080903100507020f07051e040603020d030804050d0306080c091909060e0607050f040902030901150b0a03060503010606 79
    0x12510404040362009122901800014603054100300e018603021290303078141c240046041400c90700140c1d0010b1408090307040303041c01030405103c1d0642c0221105401402c1c2424000400d0000b803044801102c480e5480205504000c1ca6100d8141c000c80c0c01d500031070415007011040500440c8500584d13100700d221100003810401f020049540100004c0d0035100004811f1300c4107009030a06441e410003500481410010f2380074001410012202d00614503150381941810116910001c104900c0d04170303440d1007020015890302038a00c4103441c03083d981c0e8400c42c13a0604110b81010140312a140426052400800c1454000039242640000803260222142c44075003454580d003082550a82c0c0300b5003809101020300c00030b9800a503a40507001c00b595529980c1c00400c071100e00c52032440c0d0154900c1400705006100e5141d000e50381c4a84402d00006d247c00c8101110381c02d083c802d82c400b10f02d424000070000310080d414001d10004000c00d5009009840c01d00d14041d0202c1d52110413501b030781060044255 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775953030 1250 775951780 775951801
    0xc030a0905210702210a150b031c09081b370e0903090a031b050d4b0606231207120f0305130e100611060c03 48
    0x100440c800c990403195603a024144444a03411009051740305042c41d0030b18000d00350301540f1100b00c800825000d07142201c500e517504160703800303240303030398141140d850415034802d0714200080c2d140b051072400a264201c2c51070500811011203908141a0b94008258202e1100d0340341601400e003e1080364004104040c80d01d0785e02d0003544002e91049001400c802000740301841400030310a84084496100c0b90359600b1440660301d100300004540c010041510410201d003c4000c01441d4058044004081650345e5000800d03090700e00c88160356241d49490598408549100e0426803038160b00910b02d946000444004000683c113180c4006169418a0301c00402c00ca030b9208002805030a4000c4148100e405081c1102001450385640900c0d00d00c202040c00308000582a07040b142125040c07c0f20321459641c803103080f481c0c4407046050050a01141310070303191403510346010b4044c4001e64020361612207184280c424043d445603007489006544611024408142a5400a50203240300c2d501e485005112 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775954280 1250 775953030 775953043
    0x191203052802040503100b090f07110303040615120c0306020c07080a060e070b070807111c0b07020d0f02030306090402121009020f0a06020606090411181e0c030a0905 73
    0x44100c0c0318505021240940a0b4050019244190102e800c0d141641d5103100032110b130740030515800041d00000810f03d00d1746410403a48009140342c403441c01582280c450b45160410351f002c88001d03441d05400303882e07400349441101c0203180f680c15006503414640c0700c01c1d01e8400726020203040e26800060903001c4400420040d8024000001181e60010490408400070105040d1400c1d46016030a000100300c00c1050660b41c04503040303005186054102e0365484a10000550b8168110680c2d843c0300d208140c07040c4000100c1030240d203103440c2d01e14000000909000c60720001e0001e20103052510040190300001380ea5010b002680c1e410421f4407036000003400d10030344440100f458801c48082a03400125500942d070654400c0d40c107145400300c0d03001040074102140c0580c83c01030f404000050001e2510030311036a00503020f0300701c1c0b02c0b964201c030000c80e001c03007658054244483e104105100320403840f8000d40c3d283c00d16003046121141480310142500b848041c00c803908640c1c0b109003120602c0003e1110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775955530 1250 775954280 775954321
    0xb0405240f12060f090307020a1205100204030b0403090b03100303080c0f04152d2010060329070c080c03042d0b04051c050703060b0319120305 63
    0x9811680b8030a2030700350759040c1104e40d0b00c1050522404240082c10000c1a074004a6009010004803802d02c83c44000c1040110425241485061015610301c0880c3c0300070806940543d4107482c0031700c3d10b424007500414160340079110942c1b041080240e1429a0310302102640d0b0704d032030100c3d07030703070319440000e07100c03070150302c1015580d04c0001400240c81100c1d081d428400c0d850503110840c40c840c040e54004a82c627450003401c42c00c050140660808c05100340101d80107018180301030824030619a00061a04d280c00c481c00601e69908c1c84144140308640c00903e46010400003903a00c4c00410f4807050189003c003815031340078002041d26160800110074140e6212401a10449468a558415501d60940400807011404440540114540c1c040c2200c2c0401e8981031491a4581032800b0140408844c8000300c2050086d01c1980e240000ba40610850004500071031002c0b54020380c1c40101800c10324000074441000b0b21901c00311000a21902c00710041ea0060b050004d142d41d51142c0c0f41201c00d6800d0003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775956780 1250 775955530 775955539
    0xf0f0a0c0309060203040501050406080c0d0e0d1b0213020f0f120f060d0c0605130503060a0c031b0206070810090c02060a0e0312010512011506030f0b0405240f 70
    0x418950080d8004103810825009945448007260b80b4241603071284075900925000640420081c4407084c061000d01d504144200d010030714010000f10b18608541101e02c4070800c54018210300c000041e40818000d00c00403404920b4866038035030754001002c401d500758605c031056802064042e402c0c02d1610a07103125004134031621341c1d91151a0380d16130303090000301c0721000c3c60705022010550500300704c2100d00a255202060300c00040c01d094090390150800e4400c40c1c0c10004001001c0703103a40701807206600031070303d00b070010a00c0102a200681902c00f5050b02030951b046482062000990009049401c0400382c1080c0c1d03d952500444c007007110410313400c0403055604040b4000030040c0d0001d110781c42603001c05010802840d1500702c003a100e00c9014042c0807201c90b03140041c086403500303031102c0001101410000404034146419008050456440751000ca6600c1c40141000c02e410701400301201c0c01214104414039007421805409c480580c01655940c00c50b08414186480784000090074490080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775958030 1250 775956780 775956787
    0x2012060a05120607030f0209100c0809060a080108061b0403060c052718101413050c03090c10050a080411090108010b040f2c07180e1501030c0b0f0f 65
    0x958680d544415640000040c0c1b4060081382d04101c64826035001180050050b00c0401004404440d0040c10903010b851600c810460341403190b68030402403101404c6511000389541c0360003449810051300420b80e4030544e5400451500206d010340456090740d42c085800124440b041034212110700455041c540c0c00761800d0114142048809480344401200720703481c80034401d000014990040301540c441c0e1443c02007103414845003c0181003020780000c0a414030800c2c5480b00101c00c26103000f41c0d0802004400041030000d12a0140099900100f040d520800042c08c4001c00400a100307142e41c030010840f48402081c2040895903902c001c040008101c4800c550b1501440d038020680500c4503440b40d8130705200340118441d1409407441e0b50701d40300d038000303469059180e5669211805925a6506000300e8a021481c0c41d2400c0001001000d50400090b03542400000b003881c042203c04620860103403140108005009219024103079827000101c00d071989038548003003115002d140001c81c0e841d80c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775959280 1250 775958030 775958059
    0xa021005070b18030d021e0a11070603020309120307030e01050f06010e04050112020405101a0304020406080f1c1209060f06052205060a0b120a2012060a05 68
    0x100290003840e010320309a02c0643c41d00c1c0d228003a20140e4090900c8240c0081c41145054074003a4040c00010702030f5101541c556103058409071a981c1b102d5000404034200285665a4900802403c00500002d050440c076509141581d00d03954030031840344140340d510000c001341106200f60000d83d0343c0540c0600900c0705051182c44010103c034211031450020302c2074041c400342c80c580303030086c24102c4008040d5952099969000c0c48040d220041441c68104280d034800501400910301242510760020041030700e80c1810300c100310a60b16107a00c0b19003103910608003440104408103200d805204481398488a80f02c1c004000d0301c0000440c0da10040c0036140201c0e903c14400301d500001403100060504100d1292070380c04002c2040c2444208581440c0a2091703a14030003071650040c0d8114000500e07a00c0e5903940e941e10002c1944c0545040c0c0e43e100c0c047d0b01070003403007000750013013280310154281e9205400300000849011800307001c4244010814039004100d00d83c4074124510090400a0008032001240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775960530 1250 775959280 775959287
    0x819021020010b120a0b06040f060302031603021504050319060f020a020c1002010908030403030f06050a0801020a03060f1a1c0501081b010c2a05060c0106140306160f020a0210 77
    0x3103c1d829070003a02e810380b10005210000c22000c0c0c0803540242e000c0c1d510b40320740040c00f00a0041c4210054500d51365a404005039808125051840c0310501100700d0707150862045c06154031074194050714000e800c0c041401a0b40d0b001c1402c40451031174030140c006244550405034050120f4454604031107100150201c031082d0b0100c3ca041101d44141c94030746190309149012800c903404403001a01e40c001c28070120300080d210343c01641c511107a01d03602081040e100c60028281100c550320031a41613500154034075a19806006075002004a1400240728919008507007101c05182c0c0c0aa0409100000b0f0307010802140c410b04544501ca1080f0411030796071030340402642c490241007018584496030310700c421658400c0e001c601025a10030040c80c510f0441c1000c0d5841038004404850100b01c03006004030b050f44940300648a00310080002080f82442d01d4800700d0309200c100710450003030b000082040740412044441c2c021504117441d0000c9420130070035003203041c180308c40c0000350300c40303003a12940d40415403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775961780 1250 775960530 775960541
    0x21060f02040623070c150c020306100608130302070909050709050c2a0d030b04090f0605150307150503072105010f090c0c0809150301080313081902102001 68
    0x591115404070f0b00516001801500902000800b490a680024044100c09410400c2180d14030304210803a040305900003410001c0444150103d0443e280040041590103c3c1458000e0700300803e003e28130407281c40c001d490740c00d45c0c000ca011654542c4090410010100901c000401d800e01040009041c2031806600f00d40c00345540380d412104925000344114a00d5405001c00c405080c0208019030b43c0700d20035005030040c108030541c415074600c00400442e0581d601141c95501c920400075242c540500d6210410038040c1e030fa14000c0c3d101900c00e01a44103064120f41d030300d420600380755880b070b615030300c00f01c40030814030790354801646404c0e043c0d01c444c03500c1c1d4204074165500c03843d03942601500d07000c6210446d00140c909000080015004c80040b9814a0080c61055405030401e50011f049080c00201a131080e072202050f5400010101c02e00c01e1040c01d900007914040014141d099515522411400f203065030207882440408000c0e0403486c041d1000e06002048040704292051401b40740234001e15 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775963030 1250 775961780 775961807
    0x506060f12090c180121120c2d0605090a0f0f1101110309121c0915020a0c090b0102010b13020307030605060a09061409060f03100f21060f020406 64
    0x854005000f58a00c2c0c4800f24034800c0036882954803450703203400310500543c1d00803001e1005a80030000001e010a1400400000c001042d8a582d4680c6009241004155140c0b0b110840c407500a02c2d056444550101040c0c1040e50300550041416100c14024908205c05e00000502c0f004000054038104060301c20300d82d4800c0e001d00005c4200a40000c01554440c05c135a03242100e50b0420844a10245402062400910360000c1100c201102c40e80414148240d04600000452426142004201000d0850005161091014280d01c00c69a654590041d40c00d02a0082490b241c1e8282d01080e4400d6200381705546000300040e000141500001009510640343c920001c2d04090000c0f1712418a9812a102e1003065500c201410345054000c4941c04414000309000714010001460559143c1003e01320f504400c0c00115900c2c03d1503030781403020300d9803607015107083e100038902040103400442d86c4854525002490440c010344600d40b81d0b00400012400d10300d05803021901080b0303594010491304c00c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775964280 1250 775963030 775963033
    0x90807060309051e06010f0806010b120901060801180204150b0702060d09080406050c1014061309020603041a090a020f04020906370309020307050103090f05060108030d050c07030e01030506060f1209 87
    0x1a51588e00d8070751615401d002d040010a0300300701e200611084c4c0340b101540049640000641e0b1500c0d45400380c25141c000d0aa04031158860244006601d01480f8002c91028803401c0940d085260180d50b8140d406802c0b03000e4403a0381c0100340d08040c44056001200210f40c0000c0701e55546441c0d24000e40160041440c0c0710705d81c4145469045950040c0c03042034940750421784d4400941d62041c0c104015405140080c54100d80c1721840c00340181c444802541c000c52181d41805081201038007140c8602e10000c1c0320b0030310b5510801015000d07072104211946002410303a809070b6103c0c090703400b0460034851160580507000084000d0b102d0300540340c14101500d84070128042882880100440c2603604c241c46c065410307000b0910401840d030181e40b0150070180304021100c17501e25130707407170341400c00d9000d07031100080e038000080c100d03049c008900c112948281c11400c050b0130300c400e40c1c400504050040c1101814150b582e004a03d50b0307550360080d50280d02460098903581d40311034807807806580c82035440a419 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775965530 1250 775964280 775964309
    0x4080a0c080105040c14061b0307051c081314340303050405040209031f0507091a0a03110f07030302070b0117100b1305010801140106090807060309051e0601 69
    0xc81d038060040e14003594000d0540c00445d420440003c690754000f002d150340c0900200801c0c203014105841035102054032201440d190380460600c41e05004100d9103950011245441004203560000b070480d8000506100e0a10203500e1407515a000740e110f001044c2080c418003c01301101b20107413402c9115100c0300920002c0d82018a6034002100380345000007400300304284000e00c51404c1c036a018001d5504000c00711844010384a89140c08489202d041e80444e0b601c0d0801c20600c507400071200c8002303088484424071900c06040e4190247c0c080d04070310000301902c078000e181c50380c0c441e90180c4d484940740b0440c4039a0303070041d450060000d5208900c204c8410b60400000144060b11800c07030171501503000701a04074084180c84500c000c1015004040d0711a540c81041c100da82e059228030360180c402d03c4000a622400c0d260340080c0f21030140c0c04607007042810441817140e640041102001c51340e080c18049040346441c0f4180c1c0c105010308100081d4126a0003058810403800210207040b542d508404106 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775966780 1250 775965530 775965539
    0x61103040501200d0b06120f0906101a09190b041a03060114070512180f03010c050d150504020703090501120207050714011e0302030601020f0309030c09070507050304080a0c 76
    0x24004442c0040e01d5008003407103891000b060390341280402000091031b161500803084503000401c20151410440b001c00c003000c0000f00348080000d05e410034241d02d8007009403460158840400102d408003a0807941c00441c2078100703501c03075000c807a00440d101c0302c00c0461141c41d100491090741083c13140c0302c0030800c141c41008691982d4012640180780c180e40381c00b00c4149030000440d41d9800300404481610551916617088101e102c060120740d88040d241a800000403410090344c0c224407a0b5440c0720740d03d0411919000c980000856070300b00076030800450484401203505c1100c08403940490342190000901c1000c0550007010700e0113503002600c8200f80084680e60240407800707028001015503100403028040007841581c0f00740c840e60b0514050040103400d0a015002d8807001807440b01180d00030051108940e0107108a1000800c0c5100a5040488050020b40d59150301d031a918003c01201e000b150352a0701c1082161050b940102c01c4a950f03039170780c0c55180e0395a180490265000c2130204004134 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775968030 1250 775966780 775966811
    0x6091a0a031101111c0f090b0a0e130f02070521031b0f0c0a03020601210203070b0c120301030f170705030306040f1d0a0c0911030c0d09061103040501 66
    0x10389400035002c4190704451801910b41800450146500303108008500b03a42000c1a034002c101c42440d030ba076883d018441660701500408403600000c21000d002c0c0208801180c3c00701d0108130544045035a0166544081000d0009202c503070100c110441c00050818103000b000110005035075440205000001c1003103489111501040d2040035182500340ca03050b2030704c0a1000034100525051000501d0951042c1d030326490414603500807000360f0000001004801410b0202c041100301075000403010b03c0003640080c1c0c58586501500b4a40d40e0301080302c04801d4010031013a46140c801305a900c0e501e50f140d0034201580c55116804442c0212400380120104240e802034030b200030390101c01141961603480411019001c01c01c030450310969034500c404014202c0b00410210044101d010f4007074008981480c07000041c058000e00d08032030034481c01000198240007101d038001e6600e40035588840940700d01c0300c0540000300c03000c3c22650811030400340c0829103034000d41c0124441c200801821002c0e91289 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775969280 1250 775968030 775968049
    0x90e070b04150c1a0a09030929030a1d0610060318030309050f011d0606040903020a0f0f0b0c030f070e101412070e01090e060603070302091306091a 65
    0x12030002840005050311901540091050921413a00c40040c4020f501c0c07041a502ca0803580c100800d5110220701d401e01d41c124100002400c41820f07000c0c54604a548040014050511a041d4400300040000c600918550024202c100d00c0101c5480c059041c0707141e541e542c9010f80d18076210b03c480e4800000c81a002e88900c0d024207180c1400c94003810042d442c2580146040e0000b40c6041c090300d140221060400e203c0c00e040300c84c20f80c194411260a1040031842c068002380310030b02643ca0504800007013500023030503400c03155100c0c2c112010091649882040303000d40d00401810020035409100d801400d400255118080006c0c0000b0745540e68001201c2d042c038560030054009860303030f149200040c4203640702945c50170310580b0503217020406401107070300c0c1204981e0100041c1c5100d200c41317000d60303015009000520700045909180e00b44640000ca0511020b0240400d0550002e0720352529280c000448102d00010b0008016441d0744045100c013900384620f070020081e01c3d6402010f0245801401c0c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775970530 1250 775969280 775969289
    0x2c031303060e0307051002040816032a120c090b0609090403050a0c0209150a0b03090601090207061118150a050906030705071e051b0f130b0406090e070b04 68
    0x52094551440d119840205810307480140503020030000366020031400c0104d00501d40b4000c0c0010b0f51540b40035a05810f20004c4078000f460100ca10b02c003000403465100e040041e0341282004c041841080c08205440004954051181e10b4030380500030050084d2442d1030412517180460901020851008002d43c5114003131100750306c035061401083c0401e2140000e0940d480c8a4249494505a41d80010f40040701c01c948040380c5000e40300048906c0e0503d03900c260001c00d10140143c0c15814003928035921890140901283c0f940c2c0424034600b488650340007820303c0b6003030003245546e4501000c0404244403c2c449014003136030454200c0fa18503a4001c085a2170700303080341d817520b051003820b408024072680080c1444040120074050100400c9528501420381c184041c00c3c0311010b111840d100303080503200c4c42c00d5030600300603848240c2d107515a28001d401c0381c0003c0354a41220241c590044005010302600c481d0421728261011920600c66400000300c615444d0403149030560b503044002c01031289008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775971780 1250 775970530 775970557
    0x18050303090738160609050106090203090a2604060305090d1404050f13020a11123103060501090218060405030705010516050d0f2303190e012c03 64
    0x502207000891016000c0540707000c0f02d6614540580e040c45800c0c80c1c5440c080c01c1ea0351070f0359404000d08000e0240b051100904201c04254110718142012503140c170314024015141100d0010300100784041e150103403101200046045480d1500e0710300c01402410b0884a49071180300b00342511003101d0158402942c1ca070603150b00549000d04007828083e00b507804590302c2e0f4202c00c0078040b103c442440da00160100207043e9440300c001090908002d40b415040c88001c01c03800301d040000b26000101d03411003501f41103000c0c01908001d8025a05100e000190307502c050040c9140c800003080300d41c50781c3c0051000c90150300000d00a60400c03403c21640d44114400c041d4941c0c0300410800c45d81d405040a480c1044540340c80711001801074441c0c500705440400d1200c000740d088416210400d8001c20364044c5804500000181d002d0a03521342c010300d00c4007a101a13050100c1c2030612040e4801900640210010700e0003e0000b800044120f0464031402034510003c003280c1100d44100c0355000090f141045d0031000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775973030 1250 775971780 775971839
    0x8010920030a15022203060c02070e15011103090927160608041704090605090a0905070306150f0f03300c060204150c02040c0306060e0f0103180503030907 68
    0x418800a5200507281c4604042031001e2041001700982808010350080002040e12014070200900317041e080e41105c1240e140c108113112040000b019081020b41080c20700c0902c1d41911500c4a103107018071014194050020010000501c580c81818031543c40c1100780b101e111044d4140c2c1076150580285818801223018000b017080380e20440500b90844d0103001a500b1061403201c4c1c01c015580290040b08105803200b80800050a1811020354840402d0b4020851340425948464845110b8030000d0b00e03a540350080c03070425070750500d4070030014171500d108080b079650780e00d1450b4800c1100c0e03c4242c90782c101000b42071103d00140c10803108981101c900301423603205608030a554140000300181c079015800d1201240c00440c006200110705400e40b07801c9496045841040280c849841c801e9040505200c01044034a0b04000301810b0b90300e04441c1580d20f41c44060048000308901c00c150400f010407980070707070180007012001390b004000100a840a064640f1a19841d05400b1f00c80c2070510790540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775974280 1250 775973030 775973063
    0xc0f0c180c0e090c1201030803070e010e06030a0b0105040f1d0a0207021f1202030708100501051303020904061103070c0b0a050f0115140c100b030d210608010920030a 73
    0xf851031984000c08002490804000038010010444260011920305000206000300660049404a05486c0034a00601150414004079496007c050140300c015a1030f026104c03890717801079050360003800784031020000345aa039000313544106100c064101c3e01000e014008c15010f080b58021500b1b400e07005010800808005455080c02c585214003800c100074400b810822002568002503019070074076901c07641c41c0e00b01070100843d0b41c1c00543c881410300c4000c1103000d011402d41c0c9a81c8007201e404544007480780e81d80b400d100d00a44002c08140070116000402c200e815170304039008a080310f0141c4148120356448540f00400c441080e1a010314983c6054010006401440780c2d800d042c000601d00102c98031702c1c9441c0000f16420001c030048a90b000740010410320003182c49202c04817101140208401e14424601411212490501c0000070a0383c040c1880c900075642c100340024100f5000070849052142046207458054106a0030072010681031400d00c0d2078000b41a0500c65080b41c0e510b404924203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775975530 1250 775974280 775974289
    0x1b030206120702101a10020106030506060103090206070501020f03100e070c060b0301022a12040506040b1605030a0e0f0405071e090e0108060702010c0c0c0905070c0f0c180c0e 77
    0x900c000b046104485140c9021101d500030304107149842c805100b12041c0590802100c0820301a90700308680c98014204041000000c000b030304100c003070030001850a00c2d0f00120b00680325025024100d1740c00000c28a840b0840c90009521503007a000300414010340b9180c040c10081400e40c0c0b050b002401084c1c224000c1004c1e5401400c410034020b000510306081e2030f640201c1046c02a01000c18098092a608040f1805104080401894401151420b0f040c0400150716000d00c2c0500345a4447c041280c005181e059a503e2500640143c11a5100c82c48014010711182114602c18001d080d611045031340741c00d00d40951401014243c559043c194422180d40b440c1c0b0250100100030444c2e0113100160140c075046045000c1d0007090040c041b40e01d00008080d007560000c623410750410444959100200d010107003564151140c840011030103440b0b50004443e42c00c4042c00c05000604012082410420200c0412044030310b102c823158100ca041070f40f4541141c400940900110b0041c0361800317000d01d031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775976780 1250 775975530 775975567
    0x1005030601080c1c153b1b0a0314031e0403020a06080601020604030804110a0602060a0b18010605070c270b01092907060e06040b06240c100c03091b030206 68
    0x8884030106101d0046c406541210640c540d040002120414100080010902100c44034030000b8104c0301c6188082400b043c40380d040ca01c006410100407440c0ca2490180078021140e402c054141d280c07010f8152500da10310701ea801480200d2142c84101e070000b480741d00031380c082840b40b032058011b00841c0d80c8548040d00c02c860003c1c0101e840080c0c05c40b03000c0d00b540e20310b01e980380640002c0c0d000b0212480c180080d00704031201200b2062040c20b0031a0402030b0414401404c5040d5984c0c1c0c6403054641c0c0381c2d45481c2c9121511900f040380d9a01b800500480244502e0301a000c1d00f010f4030302c080c0007440344a001941c401480707000b8008420050780146110880f140300805001e88560590b6151003181c0c0c40b20404c40f00e107060014540c0d0002ca0074401840b600581d915041003040382d4080c40054064113802e03800d11148021417a07d800482e05448003401441120a40142c4440a2045542c02e0740001c00030501080103c52208039020005141c64078120f482d01501c0c2d014080e2450404501c0741102c1208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775978030 1250 775976780 775976801
    0x308040b0c0c060c0a030e0306090a15150b07152702060f13230102030a0e0102150406060f0b0c0c0d021c06020d0c02030a0807081005030601080c1c15 66
    0x840c00607403042c0790300d4501c010702181c1c1940c406440c0100c610b25000300014441d422180c400d5002000348410001d004c43c0408201d50f100004055810240e8480409807050700d207440c0c008103000d00e000030540e0807080188402e5200d89c00c080c03d200604041da20482c0c001441c0380178182140103032400b07104581c8090501c040e0004020605000280201503050f50040d10710000720200840100440c0c804090808a4000007003e005070303a00c29580000e58a0045025902c10400061000035041c2d0003845080c41c45903031109400024686403d00c0c0300640490700c42c0440f007403407000c8001000403800c42a00c44856298020b094422071400411010154210090380e210039850701004540d070000280149651085c40d0240c0c8524040b1303008022140c0e00d030990350940d002040002101c2c1e901007020b80c1d22841e5810210440e03141c2c10383c80c260350043c58001076007620030308001146400e80000c4901114004a5011103254075401d2050741110b4000d4008161400c00b4540c86507a681da80c0000c050b01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775979280 1250 775978030 775978033
    0x5161d04020409110415050c030306010305060a030501050a0b0f12070302040c2001090b010e0402010e0405091908030105030f0705010804080319020a080f060105031323072402070308040b0c 83
    0x2a00c822100040b50748407420782011301d80c00501041000413042110300414140d0a0243c10402c031118101c1c0c0f00d2100503e1981090b0b0f45900044856170368044400103144c019000300310601c0d01d102d9a20082c072030210054820044074072078030350301c1c6040702165140003c0302000c2d002a40c5150309000103040a01100014485c21610286414244041d1240114600030000c81c405c102c0d810420300303c00e81038000c0c0c41c80b00c01500802c00540d070040441d944c800303000d55000805540301583d0301e042c8405842c0c54002074888440315018001c0b44070245068806c200c2c03e5a4081511a500680d120494030406020801010000c2c01140041d805036920010300c079407400c0c1c2034103030700105000c03a40001286808600340f03105114604500000c0030754880001e0900e0751941c18031134060764259203644401005010341d400c2405408200e0303441400542d81042c111010301751108065502c00850226445101004091201c4800c0c400500c0a044903004041d0a20301b0781440546c4485034082070204055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775980530 1250 775979280 775979287
    0x5061804021b1f0c05040314010b091005090a2307020f120d0b01080403020c0d15050a0b150a0f111603031d060708040b16060603060f05161d0402 64
    0x2100d541401092290000201078880c0f0040d2000301d0940340b0760700307a40f4080d10f850003e0b2100c1040e00001105e082d00c0d0080e44008070080e050342c00d94094500347c0c07940da801407044030520405880c030214900a40741d04640c08081560390312400b01c00c0f150010440b024003802a9000c112552800103a903801035540e00c140e48003254003442280c54182c030071901e6903000c400080c440c003c1c4481480390840f401000d20742808a4101910005c1da2494103200152203013410969190804c0101ca800740c2d0b03200b00c56107080c84075241400032040144403011809014680080d01a0110041e6104a80640307400361145504108013030700468000310250729032000b074415080000108000c5070011001148a41d80d099803001c1c2c00c00c100180b001c0c0b00c0000d540521000d000f240700040d45c80d405d450a07205c2c5c100c00c840d00c9459400d614103402544a1010b0100c40c5030000100520400c0e800640d83d8081403d0144501d8031000f210003821029a00d400c4001100703120744001001c0c0c2c004012011a5005101604 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775981780 1250 775980530 775980547
    0x50409020a0f12140a02030d0311090a12030f1b0b04020a03020d060606030c050a140f07120807090e24040b04020d0501050f040501081203061305190b030105010506180402 75
    0x20b0200280c110002c5000004554402c11810102c0c40041c103000801030400a0344543c0131982c1c803001461400e05054031041c1c0c54101041036825141d0a140081c150300115a0b140c058160454a102059000070000301010054601031001103103041c1c00400c2a680a42003038941c60140030016008030791081d4489000405030740c6410301c90408500416000908525140020302111860740408080c45028400e04151a80007200046034150618981e0366500400900d1541072095800081c6000c07010010080c007a0b500c004024400c03911a141d4024494903800e011071400740c2143c1c001e420303c41c805034a05119460345000440d80c18064000329000c12581e000034107071303002240714031b02c859903400040299203000c03504080c0a4000741c0d030812407075040c06081a1291841c0e00b400c0c14800001001c500c003612889ea4400c040d9403681410022800c001200c0c480911281903c5648103080148c00c20140c41c1c184545412144010281464561707184a140039268001d401036070b1080d8280268030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775983030 1250 775981780 775981799
    0xf0c090b030c121b0301090f0b0a0c0306260a06020f1c0e0c0904030507081209011514101403070e09250503190c020607090504090c050409020a 63
    0x4064684940041040d100351018145040d07400d4545520640071041c00015000003c41c241030112102106000e04c1e004440129000d4006207400800c004218282c100500403801c03c3d260140000304004d00040da02c04008400307840103806190b01c00c00212448032104a1618030b44070115510700c1c2902d466100c65203800d8120b822422a04000c41000100d2600502c03200c800506400f00017501000140f03440b10489541e082042141c8c1d01402070310000c0781c00e2501550070388035600c0d4001d0302a50744150042c060f03034100703000752441c440541c201400a45004400f06140e0240d80b81b48105d06002cbc10741d0810400450041014441401204100c0101d04e400c0f2100071842484c080c3c4603044d0400500c4180020310300010070002071302e642c107640708040125240e01415410420328009859486243e001c0c2601d030f8042041c03807240d03843c0113900c00300c2c2a0081a0940309081c0e40d1202c41d0403071350300d07002d000c281c1d91804001040e01800c510140480c1c60a5481001d4590018041100701c0380c5a803a00d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775984280 1250 775983030 775983053
    0x10b0d050304060f0201150e06010207080d1707110a08031504020d05060a050105030c09011409060d05010509070f0e100c02090103060605130612141603300801060c0f 73
    0x140c80c2070704001018003106801014212040380d291000300a440d8140d56004400c4415025106901c1401004504240e1080100c100a0002581a50441d81c009080640700030f02c4c80e509074010b140d540d000103881d240200b510400d4100c0b141c002e0700da8102c080d503804120368001002070a05030a040e01c200c0c40354076144050b0052030441c02000400d420041c2c00c200041885600c00c80c10480300700104100d00d910f00040e5070904100782002511782c03443d100a864180901c1c544160072280109040c00c0d003150b01d4100a0403a0416a0405034540f00e0180444a08101d44014000b0840030f541311170302424a28018501e911440c80c00e20520b64095001610035a003ea009480e081d450b02014022840c02d00a400741028401c102000003a24109914188402e2000054600038508000024100c4d040c00703130b4042c808407038110103800c5880340780013031001150050100003a541d1100c40300b6909580700d550100680507031500d895907803a02d00c003243d8a9203142001c403050510f00100c02c00192844890 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775985530 1250 775984280 775984283
    0x7020f041d0a0510020a05040902090105160827030d0c14010501031a010b07030e040c0c0605100e0a1404020d1407090e16180f110d0903090e0411010f02010b0d 70
    0x580698801800e00610f0482d105640e43c24241c410860181041c7d00042110112951481c0141c0c0340c030041070040c0d61078081c10300c0c60a0f4049921310444104011344008180c0840129010401900304036034900500040c80c40654069010303518008400e8000c1c84041b4400e842810071200340e42003851030609444083e84200d455107003070f08001e01c401c800c180034240580121040039080c400962801003090400c2c0c3c03c0d6502842e903c205903210720380314512019150741c01007024000b03810310021101445d0319030310900401a400ba070100343c4c01c0081e80544000c003000e000d00e60b81c1984440d0204040840014011a490841d525106070039036805e1000d034009041082001a00b20080e04c4c1c260300702100480d0810310092192030600119407205846001103003001000201070018052480003801903e6484103540404a0318800c0f40145402200106105e651602b0b01240d81c1d4480420f0070303005580040c0800356a00025026500c15130782154440010710000c5046040d13400404c1c440f001d00d060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775986780 1250 775985530 775985533
    0x1a070618030c0b01122019240801030c0536010e09150a0e03040902161115030103030c0c0504090c090537020910050309011103060607020f041d 63
    0x1603800074809115600c40c010034281c1c82c0842030960703d54034120910000072146580c14550b03043e0000c00d03250f104980c144c200a98041d6030f03007e07880d0f0030710702e008512401c10030a01e2006c0002c101c0ea028032a031400e0b03040781d42c412502c0140508010422101a87d0a90f03e00041401071540143c1e8001500450910b00441c610002d51075040003140d07403035020002c002c949240d1089521803600c085071031450354040d0414500050010b014480b080c118030403a8045035040c1e0000c00c506101d01ca0910f90080c034548a0801507d000c9103030814464803000e00040071200708000c1c001040400e0081074410344051259090385a066200c200241c1100c0721410156003000c013841017409025400d10030150084008c3d5450407800fa07142d003803143d04c000d028014031101001c4a0f090b0160400030703010b0b12036950f001071550010b10284031000704079030001c5920907160b44c2400803440e60601100201ca016000251040b40b91060540030702c92841e425400240e0045d5980714024464148014500804e440071340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775988030 1250 775986780 775986797
    0x40809090c0a080106030902181f080c04060503011514011e030b03010f0515060c0f03041217211e010803071b06020d1112070804080f0105011a07061803 67
    0x6000500c43e20050b00000145803604c46640c016a50310072500d801c0421301074406586644e684905050113100d548006400303150140f0110714018003140310995440140d8040180554800030182a5490a02607590402c1c00b01d40501400204c503921540105040c148002055031440e01800d00315002c03030320360780002c1c7d40d80c1d13020209240a0041c0c030b101c600000c0080c08907007002c120101c903441d40391051a10541c1d00050b1032031210824000d0301e42080300241500d40f82d540c0d03511060303214041071070708580008005c0c034542c601040c0907041e81d2203031700072041003410120301c4906a400c02101070100c1d1000d1948201ea030200741c046240c4c4a0183c00c0c0d01c00a542c403099140303400780201c0c5c9045004c0307103e140d503c1c1c028004581c2c00208003000c2d0640d482e0940e1f001152001c41800d00460a81041a00000158510a105050000b402100c1c4064101e0301c0707440c5140407440c00c8031400c0c0640070300a000103d001025442c0603024120b510b01900c000a5441003000100d0481c4200c103001301c01068400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775989280 1250 775988030 775988047
    0x2150c011a06030c1803071403150106090e0c0910020d18080c0103050c0403060504080a1403060f0f01170f010e10141c080a11010c020c030307020405040809090c 71
    0x3030240030741101c1d0100d2003104034070096000030710340d0000500b1443c992401007038152444203140d005910032070014059034919510750300d191550310b2800744614003c5c4910051a8080081781e20300c81d0403507200e595440d41c0e960500900c0001000040c140d01c0c6924003d1000344860340d50703a03c0858005845400822030f00307480407400741c461104003001c0d048880008c241002001c81c040b840a102c0b000918000a166440d132012541d00e00071a08081d0089141030108003c12000600810014180b51681d41c00030080140081c8240301c110345546e045007201500030780c5820250007080003d44141410310304450074488155064404079102c00b2061592001007050203603412203160000350340b1024be045a4141054403d00c00840c0e080640610708000c0701051880c42020000405070b4419085ca0703407000e240b0002000c40340b0b04202a401075107401d45007a905d03030002030300241100f03015001e0b50a0821a400304002008001c000f0b83d40500104085691a595010020700c50301c5030790169510340c1c01c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775990530 1250 775989280 775989283
    0x7121407030b061206040504080c030a020c010816020d111f0501090b0a121b090606080f09070f06050d0e07080f0607020105070507080706110a05091e15031302150c 72
    0x506081d030f000b00c504000c01d400c894480720125134010801e480109003521580703046a042e100303110b402d0310140000700e0034a200b59400b09007261203060903611450f89456511300d400c4a120546c0d020b0300035038841c08081014501600c860f80014803980b0030b072003002c09407035581e5201c250301140d400d5080740c1d2032005001850007440351032001e050a0304c6500300a418034000786007c2e000c0c3d40014008400700624426081b41510030070000d0a00950301344503459454001811079241681c1408400c406d01c000109281400182142140c0d223000d0742c1000141780030829106548528046c00b4405d0705c40e05071035919a4200881c0700201044030081c400120441c41c003605003000644520110390400c420312031030070780c00010384042c1600b02c5402c9070388130200d141c00001804407102c122004800490a0350000303400c40050b05819a05481702007419503076200600d040340c509810594003800746414881005040c9000c0e50340804000c0542c9a4a80c05800044840d01d1042194078a80400a08176400640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775991780 1250 775990530 775990541
    0x21020f19120314040308041208040b2106150406031a120a0b07030e0a140307020901030b010f050d0f060b030f2b030506150904060e04050106031e0c0302090712140703 73
    0x104444400e081c282150307901181480380d4400c5008120905d060b230700a2003186003c075001000c50310300c502d0307030340031aa41c00c1d160111000a80303d030300d20000c6000441c10304100e09541940842d03200264500b41c1401010740083c001907208008011003000d1130047c9441c0c0c500301a91003841100107191140701da14240149201c01000182012f08082e800d182c0c200c0000f60b10800c3c1d070740c080450070310030040428442ca54000c856000c0e600c1020040000240000b04420074140ea08110301c0380c2d411500c42c0184104828801c400400302c0d00940c144102054296010402145004041e035401100d0a1100da02c0c104020411501c00e41c0d01010044003080d140999000c1c1c04142c5c1001c0c442464103600280a400115070701d04501e4100003445800c030350301c0364402005409801e00c0d1800341d0400b030070454020810f602049881000541c0400b400e44020b0351900b90355507015191100441c1940d0a01050010140181080c0403042942c1d01900d81d0301d010306280c03c00b08a00e402c90a1900d4040141a9007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775993030 1250 775991780 775991807
    0xf0c0b19111e090d050d030c1b1703040c08030403080d0506011704060f0e0d0504031a012105011407050901020601062c0f03011806050121020f191203 66
    0x240402c51100c1d928290740400400c0220484501d84031040703031004c1880d40350f01c030800030002c0c06040d03009203110341c05d54440801c02d40745503584881c03518108000d10114601c00c401a00941c0c0d1804c0300741500392030b900256446845461501c00956803440d0040c5150015041107c030800c011404101c140301070700c2035039800300092030035001002c3c04200c103000d4054050805480c00c1c4d107403001541240d0060700616010f00c280d80480e03c810703040360401059600180400c5654034081e141c0d1010b03544500740514140c1e0400403480d4454082044030020400c11010f0032101552641030000c4900b040030b8a56206d07403013030703102e4a03070b2032941000090801f501600007506000780800101c0001801820b46c40c44c041290740402d5003401c1500c0001c500400d60902180e00d503003030102d4000014512071100e50598450602403110381d0300c80c10010900b6200d10a554291880080b0302e602614284030480c04151000d00040e50300001b1480000c01400d580c1c000c2102c1c0c6041380840010540c0c08001d031141c49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775994280 1250 775993030 775993061
    0x220308040918020d0209090c03071e1a0a0f09030507030f02120d05030703090311060106050a11010e0d1b020a0b0408071205030301151403010f0f1509060f0c0b19 71
    0x2e01d0240e0000e0441010104007034020020800042d104410802610f10703440f00090888030101e030383e50b00c0c43c90400f040f9029203028411400b40043c030b00c200d041901e00c0100c544d01c006130409203c4102120400f001920100c03c00140da43e001010031414080d1601940c000c040820303505c1d4041c01881201070340740b02d0701c891a5000ca811005125844020340b50880018900403030243c0203420304480604c40644501121700170f103400040d40541000041580040d2500ca03a004501070464450032100040c1e400415900f00b41c4c02141424403a0b100821008220450070120b61a0386d0040f07600c514941d0081c10f281400010b090001d10420092100282000704a881c0e1900940e41d8480d00d80c001803003940307070103480c00e2841120700707000f88480d101158074800420303140e40e90350b410000001c132284102c1103111441100841d504000b1030b480040204252116809549011000c03070b840d40e00e05444c10104400001c00f1030000300c40703c4415021310203038079101000e940080101002c440071604a03c901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775995530 1250 775994280 775994321
    0x120c0f13142805300d030b0306041208180610030c1a0f03060a030506090102130605040e070e0a3201080f010306020703030f060e1006050a090b2203080409 68
    0xc00d0340d1480c180d0384242e038001c2d14654000201c1c1c80303040002d00c20b40c60113241100348070040c22002511700b0780203010b60380c2405503803521418151100c10542d07018013200c901e6010104207034010480140c12441d030858603a200c200070700071941031000986060007010302400003001032003400000c0c00c1c044c11008100303004098141d00350a80520890000381908800400054030f144c0e19000070f8130040d81c014050f0340b01c07440c1c4440250b000358002111144e165044041c040b451620540544003039420801d900e9283d5111500240c07072801602c0794040d03014a424402190103404d002c14800e042e82242c05500e070b226100c11406e02c40c0c544013a80181044495010440d280d41d5400301607044075044800140d65111508007140507200b035410051003641021310000740c031400107144910603070031990b907450394544451040f0340e13911031500094000f0f041d516090060300d0914004006c1505001c002000064001c03032610012143d9a005407281807000c2810071810705640143d403102480444441c92 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775996780 1250 775995530 775995589
    0x1214060c04030611132d0303050307110a02030304080706091a04050d0f02150c06091204092406020601050a0609030312050a0212010b0d0b06120c0f1314 67
    0x1054029840081c0c400fa44a2680003250304544048a042c2c10300f4502041003280c031a036014081014050048420540c0c1c0d80c1510302c07070303948040c1d804150b81d0b1660f05c0c103103161100042103c1a2044008140ca2401254803250041c0d608100500003850800050040300d4901200075000d5074481d8807403100704021f0751180c130109440350105d40aa03242110b080094500b18200701507034a1945000a42060f010300460190740c0700440581103c3c1c0041007110816901d00f81d01e44e407510408000d12100d10014030050100f5140380e0051100e440071101c004114068001c80c02168000035132024016030800e000510460500480348000340c4401d04001061602c1c0d030b60028443c121036580508060340d10400701e0040586601101c2c450900c603031404003d561034444031150795100d40006101d651070300e81089918200300301510034010303291000c0117590341c80303140d24060342d408400d00c0740c0c4490040240d1826100c20f42e55210203404114641c8584c0c500410900000000b04803c6404030040d01c000c406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775998030 1250 775996780 775996801
    0x192609070306090305040b07030c020f180612010e1005010609050916030b0103021b0106211a06010203120103050601030b100e13051006030503090f0f0108010e060d0c121406 76
    0x1200e5000c2c600080303e42c228182191103001c1c58012409900340000c2410606500c6403061407158000c0350000404000074040015510102001d07414190032000000d01c0d92612810ba07580c12140c0b0000401e4401420070440d04061201d410b400e40940d680300140001e03980f01d01080003902d001d84011034a030034109110786940ca4201d1500341019141c01d00c1d00301a911a03015103103418803800e6016042d01041004072f02030b0101d0b00500c0880c0c41d00341c0d050115911040d40c0e10541c290003c18668054010b680c0900230100010175460551104101c004544002000c41d18021800744000d0080c0e54117602d41801d500c00040e092040825040c00d047c01100042032000c0d800c280310680580b154000d92814078100744041d0610a900c81c6001800001c1c010040b00a01c00e9681c00c403196100c4454610811400000b00c410a50028000780d0060012803440b80340c4a420081c0103025039040e001a0740d462520b4045604017904c51a00c01120a0411500c40d940c81d11071101d0340003400151402c0614603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775999280 1250 775998030 775998043
    0x140415122a0e0414011e0203040b090d121a060f0301030c050907081f080610090f0e0303040b0a0e01051320091308040b0c0d1106060109050d0503192609 67
    0x20713280d41003c00d241091014250302241c01000c001c4410207481e42002c42c8040250003c6030152103010905001814000c00420404c280041640300c041040884d02c02040080c00100c940030030010340c03554006051b80d21030000d07101c08005040b03030550340d604610f4409602d0322a54005406801d074401800125600700c02000d03440308072030f124007050740103c7c2c119900c0208650701c00c5866014050520541c9801340c0c81010541d00360035014003403940310600540071200400350780410f0341c10a0007c107001890802501d034000c480200c000c240e940e98600c0032400c4640a1728040f1a501c0418400400c128203803141800300a28940300309031040c144c0020500c80940203000c042e0300c0c03984030300010030444141c0588024040007130405460344402d1441c070740c2d140c0c00ca040e02008144480e0003003031071203070002d0494440c01040c1d6508914601c1c1c101400800f81452008845900013441000c02030400d01c00341344007803a0b2035941c81d50007145000303d043c000c410a0364a0144210000100900c040300042c16 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776000530 1250 775999280 775999283
    0x1306030206030f250302030115020c0934020304030b07081003060c050c0133241b03020a0b10230a030b04141204140415122a0e04 57
    0x104500d551449880342c4100021038101055800c0d000e42c503071411740c3c10b41c05141a104012a504a9001c0118042e86c1d00d03080c0901c003a6005115200041641800c0d00b034940b15403180c02480040d901b89290020000c1410f06940c00c0160300115003001400f51fa580820340045441c10502d00703604003032001d9508600ca40c00302401c042d840d40c0310041c200d0712a030122401d202e0450b0082290284a014404074108800b00009040401c010600a42032124200d4422281c8140005004a400180d4100680e0501c031340d281c01c1c05501e4402c0074070021010319404806120340e000d820685070516101d0310301d20010b88446051502141c080c008044901c10115195141c5c010000405186c1000500350351401d40000305201e1300030081c8020004c44421420004003418190380c184841254003034038900451040704d01110011300700d000903040c9944004100590520f07a0300500f80ca5403101c00c0c054042c40030854840383c104240328081048260010030000c45081e41544d00740c82d1040780010003201800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776001780 1250 776000530 776000551
    0x1406030a03030c0210020403060213060509010207060c1a070201150f080c0103020706090c031202010b040b210129040608010507050a080907030203062502280816060b130603020603 79
    0x1007100ea00c0c001c21494059210600f17065695039224070700380c0d02030b400050706d42d910000c8501d00812003034010b60944503101d0069000b000c00626042d03044030104101101690275680e515401014000c010b070480303114802580020514540008039810f951403a6032010058401c541d806200489001c0307047c1d12001d0003481d001d40c842a04e41441d400400a51a0081c211b200b020800401c001000c00841c020703601c130360002c102585d20300050005982d424011139500501d0b10595441c4100d90f6401180340204034000025078420040c410aa001d07200b81041d0441404881a000c2d01e180c14003c0070068030703101c002840300d4105a000503005000c1c00d440c403418060100005020800100064002582c0007400c035035880c00c006226061910a6450a4141482154641050500000c1c50619a10360282c1c8041518804407540c451200784840031518400f0070045080300f0454001c0e480903c9020b181c000482d041c0340420000703800c18002c403600071a070810740100090707a62a01030ba0b9101e4030002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776003030 1250 776001780 776001791
    0x31b020604120f12090b16030e0309091e240604030507061b240b1e040f06080a0506071808070308070f0203011a0a08030c060a0b0a030804060809011406030a0303 71
    0x8030036140c0f42c075980c030070b64151840e0a501d0340900404079611402050016480d03011f8084000d0708500780d40792202c03030a00a83c17042108440f182030000101e07500c48030320721404580602d0141d1640365490141c541c000c0c4200e441510400810f0010610708a150301214994135291545c1c0c0d07032030740b030380284e20807401405107034245000c0310801070840d00c45150384400300d20000744140700c148404000c01c0c0e8018030030f2031401c80000b240c1e080c05500d80080e09850034103d1060f0076160100409010b03100a0101c00d40c1d142c600001302e410f000c00141503c80c0c404c05c050101860300f20070041440ca036000a81000e10b42100d01088180800700c0d2a509494200792402d03507c0c840340c01c0100240380c0640d80203406629104400320307440000ca111800382441210345d01d9900c2e6540328501c4c0d890140103182c000301d4020b4400f16450300c0142c2c0c400c1040c0320002e0610038400e41d6a4a0750f14158009078021320114950320104100510207118002c00b4401666800c800c0b070030702c600400c1e6950a2410010141641d42 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776004280 1250 776003030 776003057
    0x130b06121204030506010602100209030a0b0c2101140d031e03141f09020c03090616020301020f120709150518040f09150b0603040b040303020c030a031b02060412 71
    0x1031001181000c1d00003841680c1d5a42c034a0b19595600c000d120708801030040c40880d2070420748a000725000071000134010002203142da20345601c600009080d89040440c20805c40300400b1800e800f4640d01220360741c604c010b56240200c0080701480444440d480380b1804080000003c0c1c104582c0c00c1a00b0301c12a08142c240117015043d0010700030410100850b1210b81c00b084900440a812042e01600813100305151660b150640d0042c0c0c064410040001e810900c409805030a00d100a0f100700d00e001480b494903501581c0110f4226030140d286600101400528655614440e565035900010280b40581885203081684101036000c0150034041000010380c00080100d10ba0030032121905c010b004000759200d031001200100100c03c021a1800018000f40d00144030794410240f4441c40a04186d02d5a5511303034500c242c1610092048051690070700401002c0a010006420310002d0f546001984d19680078540030080c00390400035045600400403c0002001a440c08808001904252500c3d43c0f05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776005530 1250 776004280 776004283
    0x40e12030c1201030b16080f0c0705010f0501030606050114041a0d140c0d27111203031003020a290904110c0a120804111e0d0b040209130b0612 63
    0x140106400e02d0881d0701d0002c8148040b03040d0803405034600e40501c168600c40c010050316648412030340d00300042022400a409000440d0052030350501ca800001140356841d8412002c517102a0400d99507181d4900d000e01031540c001d12440160295002c1c800e041914184242e0322541c940b0303064104090001c01d0309052500c01c1e030020126100203003502409468840e03940581d50b0000c0810481c5181003003c12540784401c0324100020001c43c0352103880c8080720381c0b50f511002405403040307608200340d240c2401d000c8409101460103009441c0702203441c20300d1401000031030141504030b90103130f440e41001008144e40107100010500c445042d151f45400c06200058010f11010b1521f03030464030002400c0707400840214842440c0d034418101255034801e1914100c5144008644c0200140400c1c0c0d20740150389401c1a07403900d000000c08808100c0c0700160007081000150403400c96003503041c8000d004c01c620b032000c0712a5006141799107003505c100c0a41c40e02c403800140030b00300600503054120001106c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776006780 1250 776005530 776005537
    0x206041122020d0b0a0e0c072f0f01050c0c09131a07090f261204030602031f03020d150b1f1d010914030a02030f0303011d010f03120216060e0f040e12030c 68
    0x80170b4402203509c00e000000703001b20306079240c00507101d00070205407450150300482c1560002c0c06600010700381106c004040c0000d51001030042070200c034201d210100050681e83c0f141c50550b0440d001c3c01c00a041024010340258066008044120302d42d04e001e10030540c51840c0c600e0314402d910b010a034501040385209042c514104041c0c440308000243c0481400311640040d8080c00305448045100032000018001c516601d001c001d500820f80301210010900c2c50310301c04900010036400055511100c80096420103240c030f400903030602842c020460031500600ca10f0000320b0b805001d040c412444800090504e22280121030705444414803031242510f0401c03020142c1076010f0211003490540750403060b034a801c24070501d40c003000f000c4803e0381803007690b0b00707030034126009802444041400d544d80c500754004614011303001c511a140001c401642a41103490007040552241e41c01803005800b4030035001c0c03400006500613410043e81c004402c4000903400c001c1d00000703c5160300c070744906410f40254071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776008030 1250 776006780 776006813
    0x80d0203180105031513090b0a0e0307021215010311010f1805211b1003110706020901030e0610300b060303070b04050303160f0206041122020d0b0a0e0c07 68
    0x10102c18841115031b6030310184005020304503c1001e5524218200d056504a5050404a4000380311f2580142000f0748140c0d5031a020406840582c10340c1190300302d82820980c004d54060094560310059560010004026a15149043e41818644076010501ca0a591103800d0084103555034403140d000d0140f1680e40c407440c07808180c501c0358403000105d0019000c521401e600c1036004100c0054241c0c0030f0301ca10303c01c072490729107040d0400302c07541c855100a401000d495810305844008586620314140f003440d2182d918440041d06c031900701480010001100110140040d104980988503070140f004a0004e03c4c3d40001584011368410010900314000d00c0001041340400d10240310411102202540c4184d01c0f84c40203400c01c896028049500380c14000e0040c015070402c002180c080b803042c8140e0600c00b01e02030711240d0291108400f1031201810303401142c01040d40400d031001260068019083e03812401c0340d0f44150f4508258038840220409041540c4c48400020304204200400030340c01d1154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776009280 1250 776008030 776008039
    0x25050d0f110303010803040510170708100e130b090d08180309060a030c0e010e1c02040204081902030105060105090a170a060905010507180b04030209090a0516080d02031801050315 79
    0x7135a450300310b540d50360868003c07a4821810248200e8040d44540b0030341c0c010382459a210780d843d4030f4000c0181c81c03810016100785220303080841c0200e4405034030a0b140d40103010029014000551a00300941c0b440710140c072540d03041e0484110b07502403650202280341c0008090001a030341503010b14400346944924854141c2004010400c1d50285e41c140c0c0c8a13442900d0191208001c42d89034000444010718843c0d202640304800348050401c4050b883c81c0040020320141006181585407080c4514100d101c50410303140e9010504241c085040038040c0716013000302800d03d5420540104001080340303a480c0682014000720158a0030240410402840d010341c20000030058400c4500b040c0303000e010121444000b04088071490031044174240080c4e000c0350b0000800c0c0381081c1c1903a08000c5c18a0021303120351680d00c504004680130910078010503103407003505032003282c40d00c3c135107507d41d030a01401519403030030b6400511050301c80030303088107400da00b0320400d1030181c3d540d6603460050319144400382d0045400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776010530 1250 776009280 776009287
    0x207051318080304030206011e090c09030c09020c0712030e130615170f0601120902030304090e0a0314030405060a0b03030d060e01090b0f0303090d031b060225050d0f1103 75
    0x9100307024000f14042da02030390a5031166a2110310244e070b100f81708810080d903194154000c01c1440030a5001c0c4440c400d0518200401a40d2522170b0701c900380f006d421443d500c643c000380281518008107d11001807010100c1e08000c1d07a0071792006040400da03801d20f580901030401d910715504400d9881746000d000240c1c40303802c0b003039900d001c000c0207aa100004c4100540810010400080700b031480a4414001607455403c43c01040e0903880240400600c00c07a003501c018030012500740454080e9096040c0000c1c024465107081d8100102622149901880210700803c244000b140c008a012940103110340c001086040d18440802d03c2c510810a00303880e154a81040424108508c030003180c100c4417481c2003440001d06000c10010380a04c40b03015150326900030040b1009a00740b00c000711020b14000c0c2061540150032040501700203080381c0080300d1441d4009038002445c1d00fa640d041d480d283d0780b040d101701c8405455659a41d0744585840650078050003c401c556014070404914840031541410390b0346 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776011780 1250 776010530 776010533
    0x12190f051008012f1b0a260904020313140a050c030d050d0510030512040806010f05100c080f04081c0503090d03051e04080306040f020a0207051318 65
    0x20801524064000300d4410700000390300b08140904a052182030400c5200d81c0c03020540807902c103c1204000252603410301005040210140d801810340400401800c2c84142514045c0307400c4040140c50058503405040d00a4142e0308541500c54a0a0582c3c0060340d85e111500c0c0140c550209030b10083c003400560b00017451449001ca20085558130660840d0707210340d29107013056101c0d403c280440c0b0025905011440800125400c202d4012110881d1414082c2d03c4c3d8131000c1c00c0000b107002081017404001000c00281c141049541d0040105101c0c0c031a034213040c400080ca01052401d991000c02c00820a134100780100300c421207098900342c2c1c400694865030340001035100c0300880e64121a045c240703410316030107a0046088a2050905901400c0440402c21058005100240c402400d250500301840101c4c907a01d070181c0d00580c0035803c00c0340c90b031414004200c141d800610310082d40a005001c070103191600001c0e20416170b48201c80306420311820700a86002001c0064152241c01d894404d50030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776013030 1250 776011780 776011811
    0x1e040e070309020a09021801180b07051606020309060a0e03120d090c050d050c101407082502101211041203020613050606120a0b010608060a0509010302061219 70
    0x29568800e494107880c1c01e40e05c1c2c0c0208202d01450f940d031400c0c0d20042d00b81001c00d62203500304400501210018406407615100c0e210394607080f0a03400c6950381c2c01316080600012440e412200103000c54802980f401000d0350100d8038a00808a0030801e0100641480f80386039024080d000040200c030403c241c40d24006120034028040381601561402c80e41800894203040c8000c0c14010f1030740000003000d6000d00b00060043c5024a4006801000190100319604071051300003808201c0c09002d0303454560f00380b0750309114000403401c00508400000c0b00400016103501c010012034020904046280516104080b8007030610101e6911460600141c08a04010400a0b070040c55009900321040ca9840c54000603161064030400f403c190312100c0003620a10342a61030f488101071600c00d9600c20f840c50b5403240200182a00114040344001003004064240492080010841191504003651450700031510500c41c54240c2c0340f0403145000000c1000002c01e4528003441d58a6108018000704e464090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776014280 1250 776013030 776013041
    0x40302061c0e1c0201021e030702070914041208101406160c1409010f15050c1629031303030b0603100f1202060d0b010224090d0906051e040e0703 64
    0x250f103042101c2c3c0384003c01d24030510a8035a114030302c82d50a411507644c0e1400c458203030401805d1408500c0b400340b0105849800d8000d5542c0081000f2240b0780d82c0c01e0900c2c02c4400501c1264043c82003201010030044803542d0249500d04442035098182d4480041c00c0102d40c0714414454200000c1c2c0c00849a03030100310141841400701c0c4e010301024180510f9980030820041803c0c81002180301c2e0181c001d1000b2004040c12101e0a4018240207190003665003015040103003541240d000d444120408002c808009400c14042001c1a100a01142580c1001079005e00000e440c0342e418420740c01c060010140030f42d11084003e000140850340340d11700711100e120b04c00c06070700891100b840340d07413070000d00b21016848105008d075008040c40e00b040c0409201c000141018600360f070462003091080d0140000131100b40d0076030a114001940e13113240414a480c80e040c00b1a648904205c0108810050342c0c2cac4c03040a494003a0b102410281e06160038000e041d140b40a5a00036188540c0440280304096405034040b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776015530 1250 776014280 776014303
    0x32060307080610031b02060a05010519090e1608010b01111603111c0804150c0b2d0a0c110705030a080d0608011d150702030a120f05070809070f0b040302061c0e 70
    0x14803a0362f8882080c0401d9201a20fa007011180084900f48484161500100901305140040f10701c0f51581c81411031040245074880d04181e5590070780c0d86a07559104d4140e0320012904402002d483d149400180c074903c0992002600110405c00340c041c0f19544d0f00f04140b044881442d903209030000070304242043d036200e480f4007404422500700c4a54028000c05282d040c2c0303a0071a03911002540e640740c9524550b620b00e51030752484440c1c20204000302c00c9100813140501c844031400503119002c0000940446501022488603070711800d42041243d400154200f661075200040c1500c506200340200046c01094100c64859400c2071480040c0320300e00c01c040c00820b405041101c0101c4511002d0a800000c1910f40c2c3d001078008120f00d43c4490301031418a481400071200000380c03811046410012120282d40203070000c5d0b12031081c011038940400005000e00320207042203c030103107441c0c8210a10302c80c80c84024040c801c0811244039000c0398010030280710101d0103050189268640b452a11000081c00307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776016780 1250 776015530 776015551
    0x606090f080318030c030111130b12070c02060f0301090b0114280203070503040f1a030f06100c02100f03050108013332060307080610031b0206 63
    0x91210404000c0604036050007010358640070b0030300c1c0040f101c4401529202d41511030303007010203d503032070901c20f1411201e0030084c4103440b01d2001c1c1c050100803c0d80c0c3c2c80745041440600c1340b4040300401864051304901682400300040000c4d10110713419016a481407210702c400030000140360940c94102040d0041d00b42c0c0d60b019802d101d00c0d01400103002e1844080302e00350700c80b000c01c0003080400c0080f186154480c0126410a80c4540e11549581c0c000c0d00034010f04006030318108501121401030051504955042504616003202011400c03a0004d040030710039002e41d50001491070060000b1210581c0207816a241c103140c6960160103275140408500c0081d05c1c0c8400050490f0042c4202e90181c0c000c01c416600f22030b032010032480460005400e5041040085200140d11804100c41450505072103200f0100d07210b0300203286511004040440c0d000b8142001001019540200c1541c0c1c0302a0417100740c3d40062000f8011001050300c0d4003404200110020140c07411030300010000d105a01000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776018030 1250 776016780 776016797
    0x4060908040308040513050421050f040603020903070b07030c08070201032c0606040203060f0d0602040806012d0b0901080a060302031e010501050d020f0907020c1e1e150f1902010606 80
    0x100c1010840ba422140504940c0d40040320400c40c204692807142c2c0306805141107400c16040c2f402031720f201c2c1c0c880c0d80118081381d4006642e82d040d003000e004003c0101076640c46141003041584001e0640c800c610390041003220f000032078000310782c000e51140d003806401d050345541d00310646010705030020740a205d111440c4100c000054062400380226440b1b81401b4102507411182c83d800c0c0700800901d003030101d0312070742c0900010034a6070b03081016a00038580200d4400300d000c4810300010201d8000d404040c030305038994801f88084010f800c11036001590a280038201541c40d0b4580200070040c41e00001c0d894021101d2015000d1f42c2d80120612509844000b0800c5076a25400c2103000d40c141900250404400d030765442c21440c110b030b810341e070222544c0103a43c16191010001031106407941d20540c0313624142070560800d8103241e1001c4401032140450f00c403607216200d0010b541344c0544880d05441c20300005003c0e48031429401174514481800701292000380c0808030107406405503009584c000380004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776019280 1250 776018030 776018059
    0x110415021e0d030209010c0204020706060f08070303091203050714010501171501031101122f0c060613020d140105030105060607030503151c0b25090b03040609080403080405 76
    0x898103200300c2801c24014000b4400c206010390180d0050340c0468180310600c2141405070b107684c0000c00d82e95100701800103801d400d002000358020080c0d007044200c2e6000c1c001c00d20000b90050348403425228504041b07480345106150440d100e100b031030801001490b50403011a20024150400341c141c0d9508411000708440d2809129a6110019950074500c1100c40040000c107102e80034210417031702c040c90700140c9500c410f03110310b040e1507904c80400031011110f40080c07410340d070100030b03594140810301000d80341508104005030f840308042c003400d1040480e581000c002e0411076040351034400e000300301031045e1521000c007814501000d201e5540a9404c00e00060708900c1e240d01260300c0e050303040d102c03603003180c98046d0010034a10150140503040140c03001c40091940040b0816481d841c030804620358680341040c884141010f14418001580c40045e0100070400d03002283d007030640714810052a16652a42054005840684405001490001004420300c46100f00074015a00c09442094070248075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776020530 1250 776019280 776019313
    0x601020a0206070609080c06010b0706110307080f181f0c11030f0904090204050c180f01051b031b0d03060b1314150d02090301060f15050d11041502 65
    0xc501000b54054810054600050025440545c469003c1c03003000c2c0c10081140c0040d450b210080c0c015007910900400c01e8010041c1b03038016005441d002c0c0c0f01c064250f092a14000c0e00f0020090720707206250050070006034014694111107000d000488080f1040c524400c45203480003001c0320001c00185081ca00103c10660007078a003241d100003400300443c40c1449001036108250085c10281e544030b030700c0f4903c80d00560b540d8000c5500541d44003401660340c40c6881001d56040c480c0441c0d150045150302c0141903260b82180640e041001d80034020304412003a48500c50840c818821003001a00c00040710000c2090f00144144420320603840c10009152039910700c03110342c003c0452042042c004c80c042404500d0101c01000089000544100708801d494084c0703a41c82d40101844001d50340d400300700b0802c54542400780e41d00a0080380e4205450784d040030f0000039444041c2c1c0120050000000380150400322982c069104042d143c20b6642e2199280c1410390b9855910110f01d0006120702c0340c00d58160b05c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776021780 1250 776020530 776020543
    0x715021b2416021903030f1e050a0b06090f010306030f1406090102040f0311300111120606070c080f0a0c08010b010905101b12080f0c0a0815041a09060102 68
    0x510f0700100002049092503100c0c04012610403000c15480b031441500c3d0804a00403440403200343c00540c8010401c00c1c040108440d00203000300300e10740c02c042c11070507a500e515084171015079083e01d9000d440e8003400d0050300030f00400e074002009100ea00120400380b081303c901280100380300900340e809a81f1030311582400d0703000b10b0040b41308030744022401300006507514110b00f0380e03e40050700040c11200e8240502c406214000c08040d04404c5812030700000b46020b01c40c442c0542c44980700541051440b040507851307103000800d1a4011000040d0b030205100041071042d00801181c01100c3300704c101c02c844642c5844184400319940010120045188901806400c680300d106a4950300c1035840c002c100143c1c07031494038102051002c0e62404032418040c07900b0404000d030003460f840c119899442c40040080f0401840011070480c0b800c20302000728100d2084520811452a004003140c1300d821800c0040c201090f038040e445031400d80c41d49100105506502002e80c403c540b503151a0792414016030320703000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776023030 1250 776021780 776021821
    0xe0708010f06052109010b010f02030c070b090f150d1803050d27081b01090b0c0703090518060301050709050a030b37050c0715021b24 59
    0x20151207050040301d00c590054801207200c24103440350140d10800c10540c0c41c5055600d16120303510341c1c1c4601c51650f04820140f4200840c1e100451409010950007600c41040380205103203410300042c84582070350f4019150b9040c040c0241104c9282030741406c5035480d030f400450030032046030908801291441c0c000c01a00d50301c540640740c0070b1514926003250b000400b0400e0718003041e01031342c0c045c4c68841d800c42208002100e00c288030f41d5540e0380c12040c004105c50071030f00450741035030b041c0b5420800250307444161641141c06059180d40750200b5140036201d450071504100d4010100d2192523588200c083c2019000c0e030300980003002113480724001124903003010300801c4d41043ea416070401c000360071000350320350081c41d1201040c1107625110086106182003c40424010040c0344000d5104d803c61041d10f0700020a440310620b40f51541d41c482c01c164024090803504280d0114424001d0742800184418070442c0030141c0312082d04000d0306007002c01c50031001400903044040010080e558a4440f00d2020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776024280 1250 776023030 776023049
    0x70c0b07020918010905160504050109050105060f0f0408031204210503061c0807050f10151206090b040501061403120d050907170c1e0904080a030e0304090203010e070801 75
    0x40c2d55508015148071890b90b0036143c29035a8014843c0411824012058440000340100045500e070108102c00d03144181c021007035851034030004014076a01d0380100c504100c40c0007407054440c075581c650820300d070140794029580340c000000c101d5003814108400510a510500103401d07011012204080d0307130081c0c4621080851404c10104004d0b1038142c40100c004090314203444903810056492641d04d42158404a07040d070b11281c0c030802000e006010100341110600e204003c8032600c1c51141c04004800e2040c6801c110050ba000018801980c0103952601d411a40c0c0c204a411300340380680c0240002d00c02c6104440c10551481c499180200d5500da5500071050307401d00304109004098000e05000c0c000001130300c00d03180c000641c1d04c0310101d005c0e900080d1034080c0544554802c00d0140707286000d0180307010000340b5040b016242c0d56081034140c009411502c1141c542856140c250700603c1d0003004901c00f44400300f0006452205500150706031440c3c80c0e0b010440380c441070f8007038554140c28002c09004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776025530 1250 776024280 776024299
    0x120506010b0f07062406081b030406020c011a04060f031a092407080f13030807120906020903160b030406020f0712020a0c060809030a08090c09010b070c0b0702 70
    0x1c0803041c5000c0c007058454032004a20b00074955880d1412104000f4503840c54000e0400c00f911800030310f810700c0d8010315050800c0c0c01180b40818002d00c4024402c0c102011160000c0003003070501c1110ba054a001c110030300001c01100e1201c54aa10010204103103607481181405008626071142c40300341c40481e60300072907925280c54170811174240039500410001c1117204910f5201941030500e00d055a055000c2c1c03440c6e001500740b070080140783e4500200500c884a15200a100c40d00720b0921842c1040c54240ca0404003940320044101c40032a21202c0c40f000c01800c044284c8144640743d0b00038266590120700b01da000d20599040c07103210003403500c071300342a05e8401e10000740820415002802614400208146010610358035806400e04503000e003070060748100c0c0c4907400c1200e0104094050444c078148220305141c0709000d580d81e403150320207060802119101041500318100903115504400801404d000d603162800403000e9044440142c2c1c2000c0041d00004d00d001121b42202d11342d40d00507040b100d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776026780 1250 776025530 776025539
    0x11090a06050c25090507080601120b3001060f1208072f09090c101d04020a03020c060a0e030d02030408090a06030b18090a1118010605070c12050601 65
    0x607540c10281005515001c1d561405144030300390301040200c0415401c080f056103050000100072144020508001d000072002800309680e080f15444080e0b1100c01000300e1158031400c041903c0d0780a07210524800c0144100e24288150194826200740082c00020402c1e81d0303841c1c5a021140c0520300c504150242c240d5030b42c10108000324000c007a038174056004a807280342c054070340b149030040e0360844002c420b1140b1601e030351900d0820711080d08414000002c015201c08031000aa051101c03d400c0c42c184030180c054140c041d5072000c0c600281c4a80204210b459103035022001d4007a5000103084000381c00713010f0000f205401e20b4468106017075005001542040d110043c450001c1d4000750007510360742424000d800ca40d56450300c840010b4061650049402d15008080c8006420b800f200048460f01240030842d60000010700d038030340d1681002c0d06034540c1d0560004290354003000415030025994070030004c1800364000c1c00411006214541d91118550350304c4c09101545040d42000b0220b8000500401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776028030 1250 776026780 776026787
    0x9022115060f120f0607050403031b0b0a0f0f0908030a06050d05060103030e0409020301150f060c0807022419080708040803070e060c010c0306240c03080a06030f030c020411090a06 79
    0x40c41102110440d443d07204d04034503a915062048641070001500000c0500805900034410400a001010b50007060b108a995034511600010446500103541c2c0e0b03015610b10342d00c0e0300211508101c8004c02c1102049a0238a101d8035801141d00c045600c0c20000002110b08000c1c1e10303501c03102e070000080c080d580d00f55502120207880001d0781507881030302c2d9402e840242c0d40c2072003545c4001c1c005101500c0b00d6407600c40707194004602a403101082c8041c01e440f84012800c1c41080307500b04d40d8105c032100746101c030000c5501c1c1101440341c8603a4101e000442c0d241c1c0030344900c41d69844820060f0300c0755200c503662200c085600001c12600208401ca00380b011411b210f015162a1480140c0101030509206141008a0842c3c080d1031619000075250001006008010508100d44195890080805000d5043c010313200b180003040040810592100003050301c104c3d944040065a44814140880c400c141001091a140b01c1c07001d83c4180d2030200c8010907128024216000c00b04040d0000700c44a25041095 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776029280 1250 776028030 776028049
    0x3040b040c03020a1508060303040b12090a060615120b0a061b0501150e0105061e0f120106030c080702060f01260601151d0105070204020d09022115060f 67
    0x301e07100103240da00800180e9844150b034000d04139050341030b410904500e8000301030300d030060002070007a04204424044603e48800302c0d00b030305440c14041c0e070342512940c0c6401c4c9400d8840001a040b1881c25002056001c40c8162900310080c071680c0b812908506d00008100700c0d0010901c07981e00c4058000200b001a00a030300e81c09031150920021144201d0b40e03142d2900b513610018481c0c60344a075046041c882c0407040000e507030142409440e001d0404500540d00046507041c1c40079202544400304510004500e0002202e401d26492281c12201d0b50f035904001c1c0150500d06218808525120002118944001442c86c0324201905400ca0303c1c1e4a03284003841000400d10350310304000c030b2006c162500205e040000c03a000b40405002e05040141c2004020648040000070000216481d800703c009683d12105503110304e501150b0041e80c5440400c840070007056042c0000350401c00d40e1005d4602c69101c045c0407004200400180c0303070544240071100170040d00880d61540c2c41030400c103c41803035080104c0c60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776030530 1250 776029280 776029283
    0xa0c0f0305160506100b070203031b0304030606140405010902030402030a03031a0a030b010501080906070207151b05010b04050a0c08150a08071202130c020d030c050d06030b090f070b03040b04 84
    0x51840d10b140d01108541010121500b690079600031018400e1450700c140d039000041802c40180740c05c060075940003a840b8420300c011007620000c44031802d143c200d801e20444004540c016410400640c1d01c2c40d0494030b858041d055288510b15103400016648640d0084900c223590040c060425500503039401d800911801c00d202c502039500800a94158580c07402110166000713160785006585000d000426241006000001c0d60b00408144403026400203a02c400351602c4c2c01050081d00f01d144c2003212400c00c00d0240d401034200c0701d04c8031410b0000c10750020203681c078180c4040c041903032008100f03000c0e10301c2c418010002910190005120002040e606a100303480103058243c1d9585d100d1030140341c5401c40d00700c00214803912040c8400c600d440100c5000e0100302100c280142280d54001a440e800316000c0c800a158881040031003161003030044500c0d066503090708115150720b9080c201d070b212904445c0304502d4459038081070900790000403ea1f0445082244191441d5102c3d0f84500420300c0c003500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776031780 1250 776030530 776030537
    0x50f0105031507121a030c0607030203161703011d01140102120d0e0307120f1805010c020103110313050c060c0601051909050a02030403030f060509010b0c12030709031203020a0c0f03 80
    0x3074682e4040a0340582d0000e4042005d0030003010000c542014100040d0151040c480c0390104034030710000390040240d4400300881d0581c0c0d480c012280c00d24204800d200c0000317000c0d041d0300000218098180201e214001c0b1054203106881c0da803900c01895003400402507440c09130b40300011551440240d40c00805101900040120b220381140700035a10395006103a0459207852849903240110345d00007034181c1910854500404941a2819144a2250180121410010243d0000c415640039820111444d40d1000c140d039501d282010542c640115441d0b0b00b01d825001c2c4d110304040714074028060305e0030110300d034014106a0340f0344410001180c0080400c113039100c510038030000f4620003c0c4035072031280108010142e5a494503240013401c40c0d0f9140070240c0c6041c40d0400912240d141c049040303040d602449001a507449884036114030f4419155564540103a000080103009940701402d4400c0300e1155002c070301c4200c229142a0142c1c01002c1c4403034001002c04100002241c00045002c000c64041d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776033030 1250 776031780 776031797
    0x80109320601090b0f1305091504020612060d12080601020d050f04270204060e09130b060f06070b340e1c05061015020c0f0d0201031e0f050f0105031507 67
    0x10450300c08101d10588070a0380d4690802100c80c0b414004802700c1d414507088400c180c03525070b001a40c60700806403203004803a800000070b00e1549031010101405600f00310300502024100100070101802120520f0042c0640b00300401481d010381c05075a1385000005149003414207043c0c0c0320800c0d150100c0585008000c1e401c90204c010860f1005002800042d034814007e2a004014402070301d01c09043d45c07512402d0020341070007140c0302403456a008802154068a8240c0d200d00281d960700908601a203070203500418000015207079451801098405440812444114075100e5004070303810b03400d070000c0b4030942c5600c8400d26019450445000c12065850a901441d0719240d1500008840d03810036200500d1040c40800d0050458980c0d41c0c0d843d200070400d146a00340442c004c114008040c90081c4c44150881045a010f5000b9001c10356a07040c600b2100407000b0a4200508005010a4003842c5000c020401c070302c01c5059a60b0598034007400410498810442d543c0c10880f00814143c20403107542c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776034280 1250 776033030 776033059
    0x9060702100509060418052d152205090a02180619090504170405010c02040e2118010f09181d0102070303060b0703140a09080109320601090b 62
    0x350140028064030558400828010b9500e11b08468000d0300700500980174481e03a0303000a025406440d4080d01c4180f0f01f9005d901c405125845c030090b1a8403c0340e1012540328002450320342d0520314040c020480c0710511003a03d600b440d0741d40b80d400030000a9001041207160140098883da15181c100002030035800401c05001d005920303254241d001203804075159400d0000780803002900b09800c15103408641d20b040c0c03406002800300c075500c00c1c0080c0240d4640b2282ca00411040c000d500c00510400c00d44030700803014100e0152a0f41c40001d88081e10a085001c2c0304540d4800c0443c0c02c0c8a8610340c40785161142880b100314120281a2840f45216444100f00103408001d0004d402c800e00b0000d002584403840e902c0c026040c0d03115030300072070a02c0e0024020440401d0344414404040e07148a03216a1b581e402d4048115103100180d04000c00700c1d070a080a003000c100e64440341c00642c0c4d141011040701c4c0300c4036104462240003c0d0754a9581a4030800040c000c1c107900341d00410f600b1800400d241c0440000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776035530 1250 776034280 776034289
    0x18030406030b1305100513060308030405010501170c0303040b0c0a0c0303050a1403060906060a020f06040c0510030209010e010f0c02130906140106090e0c0f130305010c0509060702100509 82
    0x5410640c0080e072240c6100085041104500c04641c60304101449517181420300c68034907011030303c5020b10403128903201180f0045d159101c540a15041001640c0d646800c3c01d040c0c0c0601001c0c0700345643c800c100540d40c1d090b0200400c0844601d40c0080c0a0f603e058944051313000c0a8101580c1444540540500c0000142440002e40015486030721055165141d140f000390503281000041c0d0850f0904000b00461a5079682031a60700c9002280c81c2c2d80c48000791134040b4608800ca4502484e684030742e609200c02d100300c0846140c00c8800407034101c40c0f2030900d40000c40990250101c1180414031101e82c00410703600401c61414161002c1ca0a080c0e502c10940000380741e244010054244159526201030034003890340a458501c42c800b00343c1011551410394006c0c4514081d200d003034000e6040c3c4004ca241c0090240803140d60000d140c3e203181d19a0302800d50314050415510044500e5807902c0c103010b100501400035211502c40003440b2a040c18240c0e0240615000c81e03200c1681005820490300b60309554 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776036780 1250 776035530 776035537
    0x504090c08070e060a0219050f060114041104081506060910181a040e07021908090108010905061e0a0806091b01080c19020106150f020115031a1803 65
    0x18140e8070418981808000a80219200c4818070b0288004000e0592482d4000422508140d04409082202111800c0643c10441c4103082e982007030068800000d602e246010180e11148021a130030090b1290300d2401c0c500e2841540300f031403c10340200f401d4a0640c449500b01e81d61000c4085e041e2071a0250140c0011625040100c503480410040c1422180081d511000e541c050320480948040342c1d0b032441c1d03c0b101c0f203000768811281301001e1603001408a910911030140c2421000e41c201c0c015401524203004079400580c0c142d400200700c03200000d002141c5000b02405240041d044003100079103071344000095800901d1035600804517500006425078200034191154001c41c002e800100c0401e1a09035098405440caa4104482c1c1000e0185007147c8038111440c808012414004043c0b500d54183d001d040150f07c80c1400903114261020000c0c1c10a000c020048020340c000c01c48030440d41550912000365000150054982c1d01c420103200c04840110354102c0020b00c4485c010300352000e002c41c95a407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776038030 1250 776036780 776036801
    0x40501140f0409020913110f03060103080a09050405040c0314011407050c07080303040614090c01050904021b0a0303020309071a0f030603030d0603151a010215060f15340210050409 79
    0x11810003590604c6421900301c000d144044944110715200230000a95803003040c08094001d003c0020f00b2021580501d074100010040035009009500e0305043c07050b83d06455100994610b401052013940c00c1d80c040c491240c40701e10500591845031110f003011a020b4200d14440185803003045030108079520700b00007a61043c0d200c2d5501045c2240c44241031180c281e0050060091540100f0503488240c3c0c000d0183c44510344159001a2140041006243d5088100030390342054043e9414903414140e064000b14841c46000048405103660303500c888070300e100050600d00c03402c98180039000074861040000c1d50071880040450741030151500d0b41c8811681c8036442101d07900810354107030005d4802402403a8033303046505000420031060f400080d407229a0503441082c1c0c080e13030b5000140700c1e6603500e00e90181207d001c0c103490700c07090040010f9000c6600514040701c11f104551194a4020440d40715065480f0110050180d20000340c0d09211403812301c00303112018080c1c00c0c00045244440c9202302807451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776039280 1250 776038030 776038051
    0x80a02040f090501051f0806061804020d0504030e0a0b040e070905120c0f09250207260c0a060c030e01030908160209070801081b03010f021b0c040501140f04090209 72
    0x131351402c41080b109982c1c103101224960314401c0d14038401c1e60006403055122805a4840c1d5441421030300c11210118404083e96005101242c0700f420704c1c1c050380c00944a540320340c503585d800c0510002007141606051260b4004090100424441400301c01010f64001c0b45600340b5070700b81c9481c0c1c00000d40491030f402e42c108d40c542c07180b00743e8002850030301d046805c04c00e416201d40c100ba0a16581d850101c045040210201c0b649070307a00c00c0c0401d4820881c12008240d04103150b003003420004e84002204680b04002c4405100b07281c031a140741d1034100043d00c2120f4850301d522540502a42e003d66803410382e8040a07052640d150840c0b40031403d008001e14441d4203108040c1000800c074810060300030300c090303d10410418404010301c0000000540c04454142c4034000d000510300c0c03140043d0150101400ca480e00600100b410403001d003200d0351504d404803000c0c050729080c106007070070302049032801d102e145c0503111410f40001c02406d00c50202c440104000e000800c1c1c1c00fa1540104e0b21450042d20100c00c0c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776040530 1250 776039280 776039291
    0x18060c1f140103030f091d060d03020f1f1409030307110703120305010602060901060b0a120b1503060a120206030601110a0b010f060f0c08040605031003140304260d080a02040f09 78
    0x14103a1205486c1c010b006101c2c41d400d801c450840c80c2c40f00c4c10304010480c1d401078140e4480c80080c035008001080c20701050b8070480e010542c51010380d245d040041c1181c0c1c80e6503424505581c80c01c400c03001a0b54031a09080d0000d41c110750700e0601c1100c0441c401d084124250140740000710104410310020100705800e6140440c4552400c4c400900e0071400070700070f0201d0f074906030081c022100f1004c219101c8205910301440c0d8101c40d9561031006004c0d59000030341c07002000c40c130954150208001f8510444044a0220f2030a0381d54984e400e204c098000700a610440400010f13a032076005a040c5e030b805130040c80884013070340d0300c3c0d5490030a941400c0c2c10500501e00d540108201d541d601080c0c22003441e100d4600000303d0301456940b001c2e00d010324042c01c070502c24040000742c4c111001100840056411070b8500042030410240907842e648540035544007084190020f000514010010480841c42c4c1d8000f8007205050400480380a04d020304010200c9800b0040014080301c10000d040250150303600008a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776041780 1250 776040530 776040557
    0xa1a241e0c06240a15050c060a0903030c1803020907140d06030b090f0a06022b060302010801060507050d0818010c1115190c090e0a0218060c1f14010303 67
    0x1650b0004801440c5024405410f2055807074050001048420883e03911804038078140b019521400380c07082c0b0328900d2189404001d2007044907080600228086c0c0c50400c00d40c40280030071500b5801440c509802000105010401801d084c00100e0707010303130b8a10700000c07500440300e0303280310f903610610211402d140c443c0300601c18003940d0a9010341005000c0000c042d1089a1042143c84031038603a0083e107e40d60118040c43d00b12103468900421421b00c072150711803241c940d0711400044c0290300080c1d00152084c00049a802c0c02385045803810360b04031008100d40c04209070111750b141402082c25120381025007280e09500b409004000300000d0301e494a008503402c610b0014038100703621910b40c0c1060040d8082c012842100a010200103010f40004a600c195090060303685041c558401c3d0b1140503240d081101d0002c4079400783c080e82c400c0d04200c40308020b84408000050040074409142da42014103424000d13844020164064403060344081b62550005e001107841c2c1c4026401500030400480740100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776043030 1250 776041780 776041801
    0xa0b011e02210c070f080a08130314160b0322020102101e0515061614030310060318080429040b0307080c0406080621060a1a241e0c06 59
    0x1d020b0032580da4170100040c0b82100c0766640300d0380c80e9400380c415040040c40f101100300d00c06080000e9a00401150202c9185e90580e43c2e940e09a620140301d80c00d01000046041003500040380d0103074042403158490721130b00e100701c03556110044074100d0543c4600421380e80701898500542c240d840713410310818411003c0b45400710950f40000c04001100c580700d41d1100040d078440041e0b44d0040c01d03040701029803121924050f814042003001055441c4400300403ca00c00303030100d641c00142c4100e59801e000380f0460140c5044a0040a07c00501da524140300510a12009031002102500080f0000d410381013402805801680a508611800c4000108015210b41c00541154010543c103144616051800340c0040903414040d00e900c0c0321f200e174441c4400100c1e00008205070000b6400c8113543d002e08142604200905240f0307c5c004010100b81c0c0d0b0180c0500d4808002d403401620380040b20010710001c0da6440d2103902030740b86007106da14000c1000000550340c3c0090b249480c102e80091101d81041810791 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776044280 1250 776043030 776043043
    0x7110a0c140108100306022a07050f0d0b010e06010309140c040510122415051504060e0d170a020619020a050d05060103020c1b090a0b011e02210c 64
    0x82c144a018024042020550840c1c08101ca80014005895171000120380703c00c810503d2140082000501070b0708994030020801008540341151521054030001d010301aa80a000300040e02604031000108114901c54000035803003541450f0004003074400d59201c41501102d0b0285071603542c0140742400311070505101c0da130303040105803110740d25035450b201d0507034040c02d00c00000500035140c20042c0b03401d0241181c0c00c906501c40100c01809000c242608a1000c01d83c140700f214803851082d134501401080200403142a07a0607541c5d00c940c012400010b000843c14001c030300300e803407002c403c05040f18820340b070004e0403030a200740d03020b0f11311400c0200b6041c503070300d171401d4110901510403c9040a03ea4110301140c8104200504c0440c4550755000160000d020704282101d0720b0041c20f9002c8100c0d5801101494207400c07c40f0804403588903080ca1000b1a5804181540030901e520542e980810280c000d0103484442c0380b04440000d240030190801c00080007442c00a140800300320a40ca84009000c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776045530 1250 776044280 776044319
    0x30403150e070306150f08030a0207090e0703030c0c12142104140a03060c02010b041401050919020c070603060810050c090103020711060a0e01021005010302010203090907110a0c 78
    0x244010300c61079512035201d48007844010045983e9210030164805840c6100c00104480341036000c2442e90f4a5045850750701c07201403003006000d906004502e00420384a2804d50903021402401d1150035650f0507510450001c0b0141c41a2500d503000240c41841c904511001e60b10680c140c100400c0300301071aa14201c0c60807a02c0e004600c0b0160b10034007040b04070050710212150600d40040f6007d0143c0403400568640e0000f41031181003020001a864054021a001041c00d03941040340505124650303400c14807e025480d03110140401245810b80c0c502ca800c4803c030800c0c10014030f0140e030800400d2504a0b1940f00c0c00200340c441c00c00b003101620500003a000780320729070320a12062400700c40344504d42c40740c50841d40c145580441c44c0c0040c41440324080f40c4601004c1c3c40941c0d110044100540040c500c244428011700c110303400743d00300e00428020f40b41203940c180c00039410030080c4401c0108440c00100540304000c800707142c0071201d00303040100e81c0805014140ba10107050a1030700c044685c0180060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776046780 1250 776045530 776045573
    0x905091c09060c030f030b031204050f0108060306070507080f0712080906100b03071b06020d050915040f1401050411010f030b0616112701051e120c06040305030403 72
    0x181001a140c101d51102103c1c0e074145020305c2511070220040c0c00904c241050030f5010700c0f62054841000d04103e00501c250740782150400b4a5105000044480d01c01c122440760f00f68000c807001c52291800f0700c010b0400c00b40324840c205d00304002d1003e9000790f501b2054047d10146c078441c0784203000c076402100c016080400c01001d8403640c541420800d01010247c0319042207400008005003485100e51050a031404540f000c2008111450400c0d03400380d04180d0400340e40310f11b00030102d007404200080c00900301c80300c1c80c0c15912640d256100d200c4901c5a00006440705004c000e0402e910410030b21440c3d100c0c520541302c401800744102c00041030360ce00002c100040c5440c007800120f8a03501d100685103020b48080d0000500240c0b032801c40c0d842d1024172102c680014a01800f8090482000c481c6800860210340c0c0c0145070f03076034908100540b4404c881c0c0c413103907220400071020281004000b01c99a00e0b640d40890b47c14940007004581075611a600c01d450981005c2810302c100412061034400e02c40d640369 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776048030 1250 776046780 776046797
    0x60b040b0f0f0109150206090d0e1807120c05120603060717040606031a011a0f0f0c1606030b03011401080303010611100504060c030c0c0c05060906040905091c 70
    0x10201e40100950380d1518418821840a080e40741c0c407401e1031001503c05034058881008000070040c1d61030a0984004c0c0c2180201f0007004d425030b03c28030302d0103080c040050520036000211003018920364000340ca10803c02005c0104140340d003405018a0042c0c90441c0d032059903508030400c071010924809070a942c0f20344c000500744030802d58007030307503805500c0e0b46400040c03425100c5151100050845610051010201304840352034020040c403460304031050113048412002ca40740a186032440307610400d80100b142841110005580c2e040075000c030042200c1218800c10307494103042120902d503031003800000c0d110b0310a05181e09080c0913a10060705251941107080d4144640f0781e440740014002c00d001c00156607802110f207101041400456614000104003c1c1414100680507107064056140440c1c1425008001c1610031505c49213140e4004003c1c01005042a040080c90342c0070341c02040d8041801d104c0412090058031031300b400b61042100600301c820900c61454082e444a0600006011491 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776049280 1250 776048030 776048051
    0x3050708011a0a17041b0b0c060109020d0f24050f0f0409051e060609090313050609060403020910080705060f0d091410090c05030a02010c0b040f080d020403060b04 72
    0x40080c007030036600c0000d0b85494444403d41114450b41503648406001c92090034801401001c803010003884c44c0700314000555540702c1042c80f02c00d00c01c40310003482c9a408800100002c403c9a809070040d0b02c6001004103404103a41c6e1b4203000e440c02c202014402c0d0b0480c4140c841d80241d03c504040c008c0c50155045007810100600042150441807c0700303015586908095041010501210241c00700c661102c241072010f040e15240d40f110120342c1e0303a0240c9800c401080c0302c50b1000081e90303240c0d04003076142c120280c14102407200580051064580265090101000681c2c80e203560912a00040702c44d0402c152030481000d00d8180c056010318040c1d24100403c10100d61140c0460b009000c100d0404100e2400d00d16040007255180b14024041f40074051001c02e00c21010b0300802c01003400340c03c0a0b030004d0b0f1110304244c0c981e211481c0007404200312200803000106494005a80309000d10007a400e03460060301d400520354042d803440010b00b41d0024040c0104035080c03240d0b282c80c07941581c0402654003030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776050530 1250 776049280 776049299
    0x3060f061b080a0512150102100b030c0f06190302030a0b090103030207030b04080909010315060e0c0a21022214060d201603020c10050307050a14190305070801 70
    0x115005411882c0020f0703006000e5004000310b83c620800c0003540c00161801c0c80580114082540480d030042c060107032081800e0016025589088100401602081d0804000c100c2c22822035908070781c02c0b680600400c82602c01045d880e103800503080c3c070003585d43c0c90f049029400f2243e6000401b4441c4120000600c08a60b000540b142901e6000d045040c250702c441c10300d0007440c010040c03840d600c601c10500100401c4002e06004543e01c000d4102440700a4492143c004905012620001446d0050040710a000d1140018400c00072401070000c85aa6843c2400c0b03042e42e21151a10011105001010000d1300040c61020020000700d5603480401140000003107461060b52104c000140e160324408003408640d20314200b58400d50909180e850810b040040c000111f000c00540160084000b1106d1a007003061034010558525a981c602c0e40e6124031050f0740fa40c110f482500b08010002604940003d140401811844031030348918551000a40c4000c054980040c0300b0000c100300d18004010903000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776051780 1250 776050530 776050577
    0x90b0702010b01023a030f18060509012a091d090f0f0714030c0301141902041401051b0307051006052d031603060506040b01020d09050108130b0703060f06 68
    0x1701c2284155400c9180d8078118050709032144801103580c5008105441d03040e0a801502038075101d00424400b990301e00342c001b0300300c40c029403482c0c25161310740314040304803040031b100c40c0c1c0d06000740c0c105807031360540380d9181461581c0c003400c03460504e100f48820310203201010000c1d01d8210748140001e10301e21940000d41a101d0700c041c82100382071b00194020102d90f503800d1141d0a11a18090020404980003030300c403005090041d10502500200c51087c0c5401c4ca18a000b00e0301503a084101c54042c500c071070001100c43e5441205541c80b19100682240982d08062005040a900440081844403005500002202c013a540402c1c81000071013451421002c0680c0038026103101c1400956000126001207804c140400450308007a42a129020040152a0748001d00861041e2020402d04800078010381ea5201c03034112040c0032450740c0d10104076039886645c000c1c1d407280c28103281504000650f82c0ba44052081580c00707001007901d40b0307018021006845070a400921051420582d10041014040302030740 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776053030 1250 776051780 776051863
    0x15030c03030a021c090825230f030c060403050c0f0d0f060f1b030213090203040305180102010b0603040b0601030515060a0305090309030703050d02011a06040e040501090b0702010b0102 81
    0x340014130354502030b80160344400040c4002c0043c0c4050003607100b04880104134407c580041c6d903c1443c0c0104074200480c03840500048020707005900411040100024200410200d981c10700c0342050a60440e21903002800c02184904000c000314011001017056003500c040001d4000c58200c01128041103844a034100d03000c0c2c01400006d400c1c801c40b98802c0c0a0300c000c00c8050400440398502004942d89540100b201404503072142e60f180d07440b80343c00021391000340c40c060300048051010a051640e480d890317042c00f179414000041c501994070007213082500103c5081e56403c00ca6010840d840d40c05001e070946c8110640f04140408190728009016800740c0300401c0c04155031580003a42c0d0200810407195998402011030f8082c070350380e14000b03a0b1802100903400043d401c0240364900d03401c3c0700740c1c0c0c60038030b03c4018552030404c2e060041c020380b48600208146d0b2150f41f107405200c0418800c2034214080d041325030011501c0c8881d00c0019150820180710b5504111030016a45452083d49480e1030115 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776054280 1250 776053030 776053063
    0x806060901080103081c11130b09031c09030b0106170601020a120c0311030f03010f0e040f03141201080606011d090708100b0c0102120106020d020705220515030c03030a02 75
    0x101c0f103010031030010f1880001590071681c9854482c407e81010080680180081171a44038052134a41c4030840190080100031501079000302200c1219080c09002d2107003100d682c3c640310b03024540d6500c407081c8031f500c2a40300e88046000d91007a010400c041c088202c2c0e00ca070007800186014400381c1c0c4e918000606000500081040d40e9030b081c0b08061003500300300f0703e40640380e0449840b0860070034480c100d90703c00c0c841d0242d5201c40d84000101c4905c400c3d00c9611607500b044221070501c186860968405416280805c041e4034100030002d9507a51005909010700030400041c000e51030b041c00090003440c0c50f01c550000c0b6148014a14680e9a0f80060165200840d440d0606003030310382c002c0c1c0c180d40e07000541000d5100e4802146c1c0410322007055007d404142e02c1102c1c0703511641d0342c1d03242c141d840d00c541001da840143c118410034000d608203040c100401d403000403818075030713440f2000d591000c640c41a10031100719103a108500c02c00e460100310390008480c0880c0a18641a00841c002c0d541d940042c1004151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776055530 1250 776054280 776054287
    0x50f040b090c0a090e010b09070203090907050d02070f050c0d170d06050d2603370204090e011104120303050a0b120d080a0e19050a061b080606090108010308 69
    0x100c1d482405001c82c200005448014226110f500b080003421015200196940c07030006100018504200c1e510b000e10362a4018510388040032050120141f402400b28040c86010441c6c2c0954000341d1000b03104680c0207640f52466a00700e4a0700a0506002c0311039244200003084008010a00e40b2029400905210901d00d40e0741101000d204058280c40e80201d600c00401401a0207128080c0c1c036030b070000d190b0b40c0c01c4003d0b070142c071907000c4035240400d90350001da00c5808100f2040740e038112440d4105d40d040420150314811400c1190b03a090b0303402500b0100004e5211140c60741814003d0044590610360044002e0401d418860980c0c940078541d24050100754980000c640c1e60311180e4024088800302500691922124100b2150b0742c43c16054241300180c1c0d04000100030a0301d1b441f40510b0314a214000d403110850240000e4200710b054003054035140603400d110b000260051003280354080022015a0700001401d40103007041b140105154040c4900300710060711a030b070221005040d2540050210b44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776056780 1250 776055530 776055541
    0xc04090f0905010c051305030307031202030a0b0316170304050612040303090606030b01140904080924120106020f01090203060106031107140f1603021804020d0b130c0603050f040b 79
    0x1e000c007050050700c01e528145030b04122aa200b4010056580c4099145903107554a2060681e07920580030040c0008030603080d00c0d01140300036001503070840d81d0550041039505800000074280300321201c40a2003082e40b140c04110044200025078011240701000d14101031500d00801c4103449120f14801d0f1040740f07100020101070290340300080c2c0b1504250b0800c0716035201c3c60b00790003155080c000e55840d0840040009440e1519041c03d500c03036548840c1c024145007255040c08082410501440d90803055900b00700320f0708420a025201039207a01e8401d03a20b03949482000307810410034400001a507418040f000740582c030001001411141c031403400181120060129030030034001d5041c000d00001c85806204880d10000070040900f010401c240c0e0055084204c504172040550301c402034002d200075000c086082c01c1c030003905500074005481e0009511841c0c0d1000c006a40441c1c03514040c800140031042440303010403440d0042d054a040801c000d00348060507094a02d07008000034280780c880e40000e40d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776058030 1250 776056780 776056811
    0x30204110408100606170624040506030a02070605090703120e211b120a0b180a0c1a03040b060d1103030d270308070c0218040302030d050f0c0409 64
    0x8000b09055815603028070074446644000d40498170804000494800403044040c1096810601822004060121070502c00d182104070100d0700c44607591448083c17000143e40d807038020055108503800040180d40d0301c0c2914207107085139000307000c1c50b886500104090000031409003100e1060032282c01c0c40110341c242d1400040d003840b481d440692a2903d90556001c44010000b9802c88050400c0542140e400b102c205004031036440050300501c0d648080140808141d00c070111642003a400d4081030030321a2550456880c111080340c00700c85030041460304004030b01d6500c13850480c0c400c69002c010b195081c95112051a14006403a2a12861049060104000b1440c0c001d07007000700302905403500c3d859034a05580042c8240f00582141103140e422403007800208999030040c5caa41511619543d44504904680c103c07640802284c000d0350309101000d4030600840f600d84500d2096006681d12504482814241c40002e00011007011154042c041401e2002e0242c4007a00e01e0800700080c1c0e860a00c5154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776059280 1250 776058030 776058037
    0x7030c020a0923010803072a0f08010906141b0705010b0a0305100e0303160e010c02100504050f0f030a03080a0f110304051b090610020313151112030f041103010e010507020d0206040c03020411 84
    0x50030305140282780090403480642085c80114001c0b1020094800c0e08071080c000c410040320511881035010b505144040c00400292007014000d100001e1509081c00101300e211059400503107180d80a04075524101c952401422080600c0348003540c00d50401c0380302c030482003591105c414140203941c50340300301c90303441030700c0c40440c20790002c2003141040205040604103a000c0d009032801203107103264403441414244419040c49070003038002c1442100ea5101151000702c041c02d01410340d0345650400030201100d0095502c84071040300c2c0182e4a0802d40707000307840d0110520a490320980000c40e2840155202c4203095440b25003503070481402100030008070f0541c4030f4002c8004600c800010080b403404001d203110f0101015907282e910701000c2d40b000b40703642c070803186202d8030b04503000b040040c10300c1c031062084a400500c40da1303507803040d015081c1c0041d083d01d00c004c041c0c1e00a81c2d941c00800c05030079410401c44444401900241060f030406440c3c1e410101c0e800e0101a010303603251548052841c2129088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776060530 1250 776059280 776059289
    0x5030f040f0210050a020c0105270d0f0b010617090c04020c1e150603060411040c0927050a060b030c070c0e01080d140c0307030c020a0923010803072a 66
    0x400c5140f11088101404541110005400510603805060506d5000720101d41c190407400e05230035407a251648005880320312801c0d0302c07a08408036510700b100140036007400c0c3e11100e00c294000015503050440003852000d4110010b03403821000400d0010344000403803a4131841d50305071405651a400340b041549014803085403082d030080c07000d4414100c00001302c1c212100918680c5c5032941921200d0400d940d40e442580c0103400d04c04000524911441c140d0300c203582401c810309201081d150b035405030911000c043c60420600212801d03e010345251140316040e403080d0050420444141012000092408010070b400b107840c900003100030910003103c5960b8014041c014001c8401e40c1c460002e00d8031240c004a40c4008621010081489420307101d080e40c1210fa00000210b0402c0e03210380b02111030200e0014166003142034084041040c50340da002c1e00c914584018200f400d074082050400c2039001d030503480094250810f026600006206c0b440c5041c096030400c10110002a02d07010300e80e58649150311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776061780 1250 776060530 776060539
    0x610030b031f020705011b020303010603092f0102010506031c0c0f020a031a10050904230601120213090b190b03060f160c030509040c030f090309080d050403020105030f040f02 77
    0x14251200d200b02e40041c5181031180c4024040b01c041c620713460342c11201c64200300c1d016801c02e04c014401107200307510084000f4000c00030011320400141240180e03078010382e01c0401400180c07441541550302405141c2d0071002c00c0e401400da0201c0881500c09084440f204c040800c10825560428000007640010b40c4d01e400a011030240d41d52407410b51b03a00b02c071074146500c0154548000400c0548601c02c204100c5201800c07804003951107a03507401110040100308031140c07102d003102c0101d8580801c03072103010313100080f00c402150140e401002031008107a688030740110304041c003560014005014132a0003444000000100c0103022070900e010f8088141d043c5e0301031180d14104100e00804201c0c0074003a80070614169104d4452640c11104c90710200c00280114100b0011014030b400e181e40702178850a82ca290016a400c00d1400600c00d45c3d114000540010b0802402801a040c00b072042690104c0141046c81c9000d00d180e0000e0401d000040018106200100004042c003007850199010b26070f0092 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776063030 1250 776061780 776061823
    0x70b1c0605040c090e010b030f070e130501060306050a0b040b0a050c12030a0f05061206041407031e1208071d0a08010212010e1302090a02070201021606030f050c030610030b03 77
    0x2140103004e11143d00c640b8500c595004000101643e080c1c044902409490300c51594a0340c13074110960700d4458403c015034000609c4100d40d089002244a0a4080cec000d07076038007188440c901030400519507400d4000c800b400f03204200810140c907c240480314180680c0c05c2658852203980003440c1481201840078030403000000c1003003010021030b8420184103618400c03c10a5031110b0050010700021050900025031014012030f020034500b41c0c01040800a8108642910f03071603642d050740e03d0500200d4000ca40440102200421030800c480400144051600000c0c0c0e1038080750050155400000a20721110394190148050315000540340c058032030351009556400940c515501c0d0b0202c24410601554486c002281801c440c4035030301610720390020701d0b4800585841c54420020750056108074154401c59801015149c09046584000c10181c0c40c005103a0b0341c2000f00f42c0c207480b0000c010490ba071008004002d504d40e00c0e00c4000c4402d1186250000342480c0290100385010f804040300320500f03a200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776064280 1250 776063030 776063051
    0x20f0d110c1606030606050414131803020105150105091c084b120a0225030207062f01110f07200a180f0c0818070b1c060504 55
    0x1c9000d00c03c892465404210b0565502d008417624001c80c010903ea013040d101c0400d50f6450b0003890080d20450b440d000088641030018088640c1075007060490150b516401005003041c0541c0a01c88985020301b4404d28001c040d00029041443e540c02c84442e080201441d18103002d010b03029103449102070008401018120700d90084101d0381c0c0c0300410b5071040362100c5a071218103800c41221058011001c0c02e82400c442c0740c10740c0b480e40d600401d8051329990900010760705031400491415580b803001c14480103091182070081c00c191303260304140240055482103c0ca0040645c01d110034142c0c1050140002d401a60410750140090740d20f9514805004036040c0c1141d041407004012007803040c4075040202036003402c0020b00c5400c80d0803842e404090f104081003030402c41200d2150811806800103000d449003501c54003110150f103541300c00200d0780000c00440741c80702c0391400010161074004100781c2d40340101e40200c2d44a88640c1d0740614407000c5540c0442621900290080c00d0000c000b4031050b60b60 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776065530 1250 776064280 776064313
    0x3080c1c0305090f0109080d0b040906110405010917060604021c15051905130b13060326121602071214160303090302010315181e020f0d110c 62
    0x140e80c50a0f041c000c0241500700f0210506c01e40485d2a0b1152680741002c0ba004a07980042c02a8120b8980240d01c9a608000090051158410500701d0758013281d15542400b00040c07078054250416802c014407007404038821600042e0484c0c0c881400c03580541d40d060b000040070040c0d10046008202c007424004050501d024046041003a44e00503121221480300c4081551101ca43c0d5204040d0020244000003061480b2070300b0400a00901038070078004640c65480d40380449a4540c4159045580405031029202d0316409000042d124000b03ca4101b5004612000680b034020f0f22117401d1010040200340198020b101c0c0800801d4180d010751212030290034400030110795030308880480c0c05445403642e054551081204142c81e0113503542c0071110305650040d0300130308210580c00c150b402a0740001a082102407844c001041c811078000c501c40600e070010518a0b409000c140300880e0052000e160007040d41000e40ba10b031a0b14036804105216040c4440c0e4180c415a0000d050394003400815021801c0c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776066780 1250 776065530 776065541
    0x6151212160618060c1d0f2206060207090501260f030f0702120118060c021c030e0609061e1e070804140a15020901020c1c110d050703080c1c03 63
    0x40d00d01440340050301001102e02d400d00c45000c901074102c01b0340c000c00c1b5090007400da44202801810f03000204100c0d89a81d041442d00885010040d9110302c402d1104950511041c0010403440c00c091100c0c4d41020f908050300259050000074080301d1004182c05c498040224101c440b82c0d040a5036960044011001d855030302c000c00030303030082042980c0080310100c14840ca01c0404140f13010600b5000c4648e4480f4042c00c1c00050040842c072540102c0001131800740c06404856031151000a0240d902903482e60802000134480c15083e000242000440703091b0710b4406031030505400d2104481d40d1030640d01b4400300700e202e9404440400c214104000160440560b03030140b1b001c1e031803003400b07000404032807540e9414000c4010800510048811040991500904441c0301c1c1401980c440b01d528102058441040100c0c200c1ca49034800c0143e0180f0014a900c9130009206480800c8015115100c081e80c410360f610004200c0d490000e5082d80800c0280603060400030450a032018540c00032034001c000c0d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776068030 1250 776066780 776066783
    0x603122304090b040506090103020f060d0902150405041d03031518010905040b0a021e070f0f08041503020403020f01080903120f160c0b070e120f06151212160618 71
    0x30304d0b00000c20320515001e40391f281240d9009180750300c0c804405092000700c2c3c2010440c0203059440f01a0480160b542031900328a58280084030358603245000104001da03143c107120141e0713481c030004044403038140100c102c035805044000342030456840302010540c0030342905148203401c460140003103203c180c690001c5010b6402146040084d0711011444422407044140c55140442c1040403219200005000391050a0203800d084a4000107511040074000c00c0300021a0480d000150500489041c0f10500348405041d00d4118202403d580c00f09104000040780d980c144030301b140005010b408100308903201c00420000c00d068509001501c03244841e0252240c0017190408400030400912456031112250b422504510460301d410b441500d006da101e00b0300719004032013041a0301607843d013081450b50f100140d0004051a14080000600c14001e10000c1e901c1402442401c1c1c076038190000301202e8140504c03000c640e0740e212490700c0d4012081e5600004040781e040100c000144090403080783d40c1903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776069280 1250 776068030 776068039
    0x6100926031305011806210b1206090106090c090b0309031e070b161b110301092604030804030809030a06060603090c0f0503030406030f021b1f0603122304090b 70
    0x9040c00b24540c1d170045441e000d0013000815441c010069110041000c80e174000b42c8540018213200100d02182d42c00c10a0501e40c1255484001880b400c880c091103082c000b003c00f113100700403000800c080108a82d8103445000c14454010001c20001a018003c49024564420303075621240340003000303c599500704160903a800161180010601c1845001140c00000307190b50b07054401ca41109503c1d8140380c4000155401c000c2e1115104054a09100da014554004c1912000e030a02039100d081040c1041111700d4900c074401c0c001000020f07104070691f81982d50046c1c0040c1c8038440c4201180c03030700303080c84405044181440c00000342980c040e8071156081d4014800340089540340c00d4407944401c2c2074030070b0680541c1304010402070980b10740e000ba0012903540c0c50262500e121740c00003100c2d80c4101790140c0f00030b81004a1210082411090300120004010710030311070b8900d19101d074600e00c24000e8100081c4044842d1841101ea407550b030001792001d0301c03011240c6a540342c1c1142170003406e210346d410703008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776070530 1250 776069280 776069297
    0x31b071706160f080414070b03100f0b07110d240e0d020610050d0203031204141507090311031903030e070902070c060c1e0b0a050610092603130501 65
    0x82c076105120340e003a10510b58942003025111603480e0350020400341c00d290004c0c040d024000c42d1000c51540114091710241e42c86102490804164032042d202540c050724000e0f4041010b040090100e801c0040c01c850b0440d2814802480b0381482d07801e4005403405000a41d00c11601064010384c140c0c081e510019281048541c140410f2070240d94a4100791250301c4080c1d00740508204a02c0c100d82d216800354400b805485c200500d401d036452007048180c9044a205012032020740021804024048151018060411203402c0030f002c00341441c4d03924080038003070181031944544540c03400c00450003210002440000007581604006006003103800c0082c1e020300416400080740c031007500946100613000150041441e24140c1c2c01c0d00c007285215801c585410110a101d0030b034200501045201c14001c0d0030b000f09078540000b801003111401072a00d44a0500c0002d03d82e07015074031401c800280d503010f08011500d20300040401c008030001b040d05010b03e100010301411074158140e83c0030101e034401e8035a03410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776071780 1250 776070530 776070571
    0x3010b070b0105100c021320070203010516080f070512091e03091e1504060804110909060a0f0b030a03110706050c060a0c090510021608030a02031b071706 68
    0x142e200e00903502000081052000c5c01c094a0201841070505c0b501d005c002403681c10340c11402e400146c1c10204650405400303d43c0d501582020f004c0c16074440444072200145031050f071400b0740120000781500e1075920705400000c0109006100310f581d541440f0100c0041882c1640031182d07141031908050080c0c0c4009011545503140000a482e21403070001d045060221a91186034014080b13545d141da0310000100c142c1d0580841300009101a1509988210841c507150900b06a120009a46079002c0c0c8031410800814030030114070b943d0000325800d00450b91040e031044000142002451381645405050040c204140d00b0180ca492042c1c2190181c48485640b140103031854001d0401c4103086400100006440052591003400300d0121030070071404041e11100402ea03005410100342000da80500711800c41b0088811501000303200b03d500440c900000840d00946030b0082c241c401d002c4101881800e90094401e200410140c480b00c10710f40005224080e00756500c4105980d11044403161612400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776073030 1250 776071780 776071789
    0xe0414030901021e0c101106090316030507020112020d0c09050d03081f1a0c010b04060b040603090f050a0b01031a06030d0c061e020406030e011a1c0803010b070b0105 73
    0x5120000c16009030801360300c3c104105503984002d104031926400341c415100785a07560303081e0798090020700c0d50b0785000050340342e001680380c10000350404c13690364820301c00d110540c032404800448941c8d1500e40582c80b80031a1006842c20075840d00703102c80c114000b00700003001040a5200c5448005141e603280c041da5501d50a20407050414000940080d0440001481440e42e070030380540981d0030f4410002d00c1503558442010171054044100c003561000007000701d0000001d000d610b000d0b0302c080340e04000b01450141640000d12580c8203200038151121411800d0200388c1006280594200080d038400440da880c080301610400d0208940668102048008909101c070f451f5204100280043c540d9480740300040c0c0c1c01d41d0050008070f840f60340302c45000000041103602d082055018650141c0c8803400c2c001c018040c0c565401118003503030b01d406ca010098145c2d042189204480556840e852030744840d81c0e88da21041e402d400900b101c02d0000000075501100002890a6401216201d1b1243d0b220801c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776074280 1250 776073030 776073037
    0x216080d270b0606070f0c0e0702030a020604110102210c01060618290c060108060a022b020f040f060e15030703110c1609050f06060304140106030204060e041403 71
    0x41401081c124022400500da0407642c60704500c00a000904001070f43c1e686006c200c1907550101d881d070450f03250800c0300e511000b00171034004a40740003071801d0008990000303503902401032014100501042480c00310380d0084c0024140030041ca42106200038140e0a503d440364414101410f03a50f190030400913905100341020454000e04c040c0100b0011318065520a802004401043c1c00c08003014105c81248031201c010040c0108a0001e001c2c1ba616240500d0b04286000307018480c131500410046a1a1440280201e4645003d5244940307455542042d00000c0c0a00c804058600b040001c0106e8505000b042c0881255119580c4105059540040c0580c010450b5024019600c0900106259502940200402c01e01840000d414040340c43c01e02494000d44103007030303881040301351000e000d40344040c05141d5001034a03094800181c0bc068000c1b903105d1000910242159006600c070030031480c0c0a421950040d0b40080c42440115181d4a0240c1000c605482c203c54034250301462445022011096 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776075530 1250 776074280 776074331
    0xf10031e110f1312110909240c0403121205070f05040603090f081c18020d0b0a0f020f180406061b060e0d0203030603071205030316030216080d 63
    0x41c5082c0310201c00d0142103034010300343c418000441480041410b503000c4841200942c00b9125500f9183d10440a1184050000d040f08913903402c2900c408018041d02070840038998403a0840c070801340d131034001440317960150b904001c216070180c11001058a50140044071140c00342d500c2000300391600542a504511030340c10300e1001c6102480100500d902075030101400c940601d01814410001e40d0b6210002d5004804802200e0041e100d00c085002007481040034007818800709100f05007140d00000d1400c1421000108108060400100515402d8002e6a00c4041d00705040d9142d02e60910000b400b1742003444000e2071385c100e410460000e49040e0140e42d0455105440d841c602a800c031244802d0740040d01400c0e1506620dd548002c940f00040002410b0141103a014ad0744030f041541c101814418194410b0000c407031080c45000100340088102c80d0410407401560f1a4107400310b00070f0300640541111804a24583c403248000e200542c0c0040845203289841008060130a501584210415021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776076780 1250 776075530 776075561
    0x405060c090d0303051801090305130b070510051801050103030306050108070528050c10020301140a0e010e042d02010807020118021018090b03150103030c020f0f10031e 74
    0x2c24002203030103644a84e400603110b0b0f55103c440d00c00c003240c241c2075900820742200021000500641c61002140c840c001901c4550000c80c0b4202d401d40319641e998102465201d0780554420104152a04003655658a00c0d0210000d10566030742e0b003005070003803030180324403404101c810300018185803260048900050710b41e06c4101e02e4080c464803a01d08a01190420b40a206d01000501d01c030350020031107200058041c801c00341e501d41c101200d0749040c40d0101c1841d40244044030040c0170a501041030399042d600020340c60340f0160b4581c20a0f40c0d4519140340f0034481d98502e019031650302d140c0c105500303003803c0c004c6c0c95584441d1a898022402c1340c1080524160003025800201c00600d04180488180384031131902c03c103034802d409000f0f02c1c01c1d0810b5200100217a42c2d8070203004203040c00d10400c0ba07603e042d01e002000c2903255803030180600c030010200a08c103000030b450703c1d40240d642c080c101402c11b2014100545850700108060004c2680d445400032000750034100e03030020409406440714200700e10b0b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776078030 1250 776076780 776076799
    0xb0d060f0f050f2b172a030f030a0b0f120c0f06040f060e0301020c010516110102070803060f0a170a020909060115110c2715010503010b090409050609060405060c09 72
    0xc1e04101c1e1483c04c0e01c044880c1c0f8155030604100384003440150540c00062411000c213030b0600d403042d4108111480c00e0f1005a0002d201d10240c194204003a0380d4010000500441d10903c110001052903440001c0158400028030908000302400541900d54100175a01c101e000846503042200318002c0c0e100b5203102c0c400540042c4681841641440c10106000e070002d07040803103140a035400c1d00c004884032912503100c100301100750f96200b10501150310305200210300d440c1e07494542d01c0d4540f00042040d4060b1444641c2e02c18a6203840c0c06840c003d04ca401c4000742c50076000360501c0d0302c031119a02e0070307803003000d50901048030f41340040f074080c4c102c0754010745201ea080c88100e0b0594025900455034423607405600d85121482d00c0310b5070081c8041c045c0d68018401d0210741c2d0041181a040941848203260f850441042680d0304541201d0644842c21030650700e50000c0400180900011517005209000d20400e01a0802c1c001410b5800742d880b0703a066400991b51102c00036400d02440044943c0004201c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776079136 1106 776078030 776078089
    0x30b01021015060e1305010f0617010b0301050907051e0304060c08151c061409011b08130611070b0403270b0d060f0f050f 54
    0x408108800074401e4002c10096810307020b0b4009025040f104c0c2c044039541c0e6410b601481d040480d003441650703120401c07480000e200748505e0f8045201c000484180404201c2c103541661000c3c0aa0b078110b80c6841c040002d084c40107040300c0c0501c103041014095141c080c042021054510b984996620f00b45407901c001219440451030040154020901c404148040a441540f400c12102e106600c00e151030300d0482802e01003001040c092510010107561801c81d0100da1180320020000c22800a85010342e441c000e03c0d0075506030005a4040000c0c14441e808507007240c07500d00486000801e801200341504095000c3c1c1b03c02da8498840c0720400c01010b6100d0315484440c1d4103c00413203640359468074501c40022150164510740d8501140b85002e19020351b021800626181c0184000596540c09a494600e01801800d020342e000440201da28180340e48240c181140b21140400442c002 = true := by decide +kernel

theorem cover : BRFrame.Cov 775899280 776079136 := by
  have h0 := BRFrame.cov_init 775899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775899280 ≤ n) (h2 : n < 776079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
