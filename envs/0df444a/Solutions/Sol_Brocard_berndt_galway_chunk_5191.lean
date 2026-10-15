-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:03.665036+00:00
-- url     : https://prove2.me/submissions/37e27970-96fb-41ce-baf7-3030a0cee273

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933453237 ≤ n < 933633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933454487 1250 933453237 933453251
    0x1603020f12130618030906020a12030c020c03160609050612061504080a0f020f0f30070810060e061023070f05070501020a0203120a0e0a0b0c060114130f 67
    0x500c20f20504e443d2003038008240b00b8181c41814040d1030700c0c890740e0100e402d640100d558140014100d0b03d20342c1c200381e02410000340b500c2e001c40c0c040b0324000b00380b51101c0c0c01d8800e02d801108114000b040b0b050072a280c1da0b454014864403001403004d41d0155100300714043d0030080110f10f4030302d070075a41c2c10b1030959207c0c8401e0415980e48140c3c5d151100391070040c0d40c1504100c0340e100c154280388031100200340382034941455844004c0f0200741004072480080d140013000202e2441000c5d0f54400c5c001620300600220384409440b94103c68450032001c1180380307807529150000a04680e100d40c620b11540e001400200304e040805001d80c1c20196140a8814a1218209a03078070740115001038010a402a550359182c0c100c0307850801d2070a90035801c03c90565101c2000600165000181901c5a207204d0007260344031030601c1e80031f48803258504401540051030310780126110246074003034590314862404560490b40e880c50045410000d11006c0d60700041c00d80319902e0161031541010a291004c004005100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933455737 1250 933454487 933454493
    0x90b010c0f0308070807092615040b1518070513031b050901080a110111010b040c3b01051c02070b0115030203010803030f07200102031603020f1213 65
    0x12041ea0071404600848144802280d000b000f0035800019400e01d042d45506040e504088000ca45030900c00281c030381c401745520b08205005420b00180c8405410903541094642805e035140700300c442628017001c80184101c01c0c900700101c0000e1828075041d5180d2501c400c00308803401e030f001c5440f481020100550010026220744e00015000030b580f00b102406904260030444070b4101a8020003450b80910840310104074009000c42008000f400e1810b854803030304000031f000d094004501c80e8081e1504580c1940d05400120806401a2020b51107854480d074420084159000c500d200c0c035800c0d41840f040c2c0f45540218014203540082462910f8262a562450b030b0580c0c3c414002190401d012200400410303070313204078181261100e420150308640c100b443c1c40c0d80d6404014029540d9005003000f181420f409084010341000d5845699840004000c02c0d040c041d40c030940b14400941d450091203003c0a02c42e2098a18111040c5600c603c0c01c0804c4103c111010005080f40b050000e620001c1000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933456987 1250 933455737 933455753
    0x2030f0a03120c0513092013030b09030a02060601140c031903060f03110918010203070e0f1c020d03030e030a030902311d0102180a1707090b010c 64
    0x514400e585669000034281050300a031010520242c040c800c0501c001c1c0c0e2140c18160a1780c0603038600e403000003080011840305485810a0b10302c00e015144000580302c103a002840c6d502c005032801360000501c1c58448a03800d40d40ea104910302d00340140c019038045065903100d03055907407819040242050400043c0715149065030300080c0440d21032010f040c0107014480d050301560300280900b642d0002c60b54655101c00001c00051800b0520850146000a5400800c107040321119480a4021500c03490680e1000d030000b0050000d45100301c01c0e2466103040b920300408404901400d00246100401480c2c2c217022203031403585001c4061513115614280489420000b0b08002d410b15500401c0408450041c00348201700c1003990f405084445629407070801c4c0d512090600c1507405600020304d0340c20417005038003422002480b90398550000130941e00141c800f0010411074142103c1c0120041c1d6140300400381c281e00c4155180e0550044442040581510f911861400b281030401c02107140c402d50762080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933458237 1250 933456987 933457003
    0x20904120e0a1e0509010f290406051b01050702030a08040501090204051f0906050f120c270609010e061c080301150e09092814011d06040807030c02030f 67
    0xd408980c40c11070411025403520f00000f044190f8404540354188140c0c0300803081d80740520f1002e4054007900c0c54803080e01d007400c02004115941030541b200d407940e41c002c009510141040f91442100d0b280c6135404003043c4140750203141c894005501d00f80c0a00b60540e207807000200150f4180d540e882440016861314003620f4801c0844040707144011200701f813240740403e9a600400e1841d0710300441484151200307911120490720484c2d403c0e00d0b1481c0d00c10034902e000d1510310500c3c0c103c000d00380824a4481d041e0b076202d01600c1c4088002c00c00365100c405204008000b48210801d086001c8045103060078080301c10400080d845403c0488401c40361504601980b003a4801ca1006030f0b80c0160a101c40c0c0d10a4143c0041001110600b01c10b051400803203956100441c04d0b81012564440030f40c001744003c0d9002c48865500c41b0221031030000581c5214020314260030881740e401030318049100442c60110b151407181d580803ea550030040d550320211504008280226098881e4402d915419041002440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933459487 1250 933458237 933458249
    0x40b010903020a1401080a020a080c071b08010c1b11010509060f03010e061c11041d060108241009091a1f120203060c1305130e06070c020904120e0a 65
    0x55070342071083c0c0006021200040c41d2403001803040c0401900d03a4ad100400d20f41201014400c552a4080d60074240b1030b08840214100107100301090008100d43c1c190042da10962040d01c1e450840c82a82400c15a154120f038001081e117900c0501e058095030042d409040c0c001c0000c0c0c121428100394410111941d8000c0e0031500109625004002c0b603440c007440d6500c030b5254140318104100c540c540d910000200345c0f0b10014400c0391200306824509104400c400d9002404030121707403080d40d4a96049854103805104518084543c003480c140c0d040c0f200706d800780154000291170800c240341a140c0b0006141d80304003100d040c509445010440d060503140b10380141c1884a0a024140302280301c44060301c4158020f10100364402038000241ea000304001d54460480c074900b5a64030100a050084c802d4547c001c29800312080030040d0002c0c2096000c020800a0308003226880d8446100581d1a0510450025400000c2200280c00510098001d481c41c0ca454101688211002c5000500440c6503411078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 933460737 1250 933459487 933459509
    0x110408030a0c1718010e040e16030515060603070e0a1d09070608060d021e0924010c150e07230102061503060622061502100b090105040b010903020a 65
    0x10041c010840b07440d612100182d06402c0c44d0985080b031900c42020b0b81411a4148911200c0e507088988540e000b00d9034030f1700b035070059400240030f0450191410583c1d00041d1941e202e5041e5490b08105040806402604006c04003800d554a0407000c40e0185110b0503481c1e08031814282c000b030160b0f01802800c1d00465203000503502c03460301c40c9542e0b15004a035401402007040d4982030054640324601101c10294065a60b060303600e007614024507920f00000c48140d00010342c0c40800c0307655018000704075a5050340344c1d03125031100c5004004480303d0000c10f0380504103410072a040e400024170384d4003000314007180c101602d800070754031040d154603c4400000710042c80c141d400c00c110950b034140a096440b80600000c907808880203804607982d518020704142c010303852406800013504e40800907004410108109001168035a10a42001c5401031a060050301c50481c003084960402e00035654584009004500203a19003030410004e0402800c0c610f061018611011000da1180074820f005001e4080c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 933461987 1250 933460737 933460757
    0x302060f0409110c0d0206060f1e0a030803180703051504060e0a050705030115030c15230405040c0e010c030f030b1207050a0b04080c10121514150409110408030a 71
    0x3181c0d04001104020740115044481040723000e42c0c80c0b03c0e01c220701d11429a01140310a40103203150104004d640c01700c982c00000400c001040005650003184034083d100d038000c1c0f2411191140070727a6200d641c04002d1181d0400c0038104280601c1070403c0b41d00c24050400810540050151141025400d01d0192150381080c101400103041c240105c012426940b0682c0c04c04929540700e00305401401c0c040d0581a6480e070f0250000688120000e0812600e6000714600c0c1c84400c0006400c0c5901a1254038015170500e410400081d0007211140114441a1600349040b03d0566049414104e1442e07094181542d070048401e007611804985d06a10003002d00130040c8600b860f080204515443e4845a620f11040000b4071065a02051151108000350b698815548894006648010a101442e181c007450030195504030281c2d5180c06040300c2401040015080132107040c40700e910580d41c0b0800e0340c1c5c1070400040100c021107921038090340590181e1981030913140d5800b503003943e001440300c8001a03c1021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 933463237 1250 933461987 933462007
    0xf070b090618030a09050f030f0d210216030c291b13030803150904060903090501020d2003120702030c06091c0e010903060f141305070302060f040911 66
    0x18420021040b118015030402154100040c900d1500303000b10ba0051907184060501c81c4c80420201012020348403d9074080d06403444020042c0740c18800f000031140e00038180301a9030747d4901c200d451034140c50200140010f140e403400e8030440380704501211307880308100031031105846c0030400040075030055942904034140740180703a25280854014101c9514204a84c1c403180b1465240c070000c5079404101e1940348d5550b0510004254540b880841c0c0003c010000c11007001400e41c420307000544252141c1100989403001241e44800c8040c5100c0401e041c1041001d090740720a1007a00110643d07400c9a242c1079a0b030b003101800d26001d9895801503072010401ca101d00c01c4c10710000d80e200b451000200140c1e00b2411400d01e0207005030f5268030a01600001c0c043e101d9101e00c00f03410145400043c00c1c031000f40d16801c2d04009012280c50003025985400c0400e41c1519500c0b500036000f90440c006000980c290340820180b0340c40009101716a22042100080c070720402d0080071480c4d584070340800d840e0b6400c28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 933464487 1250 933463237 933463261
    0x906060c050106140f010804031707050403050f060f0a0e12070317160c0312180c09060b0f0301090203060619030c09081c0e01090e010306020a030e061003080f070b0906 74
    0x142144140da4139000b440d2a00f601c601000300003980302480c080906450f641020b540310700001e1682c030801c410401c108504640c00c00002c0c012644140304035416075030603400003074981c9070075544424082c0d80c400c0031036180d010a401c40c2884000311400e540c8a80e620003800d24203640440c000303d01003040c9000000000c0d10100b11b03a50700411001030340110f00381c3c0c8a001040c02c0800007004091022205400c044004540d00107412a010004900d000b0450f60038030001101c0584140203240382071001c0442c4070310080d010b89110286408c1d03007508590901c00c402010390002010282c10400500c0744030500b00f4500700aa0010810f501c0001e0110100480104141c04540146082e50b100790310100c003c51030000e101d04510341c2c0349002d090a100c0107004039024401030b0300c82040105010000f00c184901940241241011500c0030840e40740640c0c08681c580004440d11002e481d1486420004030362020001c08042500307540c0b040c40e2040070760f5140a030103000c2d6030701c0f800c070b501040070010811050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 933465737 1250 933464487 933464489
    0x1e0c090a050a05010e040f030516080a091703040b04030209040201261608040816081606021c0903171f061d0303041a0c011116110103020a081503070906060c050106 72
    0x640800f680c1c0389071035207d071041c400000c040141000340009110540281c2c140040b032040b07a014030902e50390381142000804c65030060041c10110030f084c44100c50304410000440301262014640c8505052458080104100c0002d205a05100c5420414031090340c5004e4000d40c007004500007251982010100958a0781c1c0f44444101071148080601c0042101c84080c1c5c2d4403001321045070502e10b011847c1c0000d860250081c0c80145444100030082000650780152080134501d5a08501800c4080a000c0c1660308498010b40413840e20003486440d1982000e0031540840e0118100440314034003841c0c042c03640c08991103040042c000300030b2442140b0340c20402d00340b03198049008608060801052001141041e0030004401e80c3c00148143c03030200a40111807101030410070700f515240750040945c8400707400403088a1911226500056640c060710030b540005034180e4404510342c0d106182c41029143c50300e880c56040c0308614000071011258080d203c00b4010365a00c641c100f08061034040c0c292921 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 933466987 1250 933465737 933465749
    0x4c02010c0c0b04020402180303030c250314030709080a0c081006141c020a03030e01080a0903120e010209040e0d0908122a0601080304060906030507021e0c090a050a0501 74
    0xa0041c2401060011144980154040b20016581e115895900110391103810003142c1602010040018a00c82c1c01d025050304105c10807a0030b01c00100890645207103060b084014041008e2600c000c4130011b0040146600901c83e0800400443c1c652130858500b5400607c12516840708000500c40b01c203050140c0002a42009007e005003800c0803400c0f00e008680c3d000c01801030030002000c201c00c4200d02940089160041c080701201d50312400d000300060440d01c0804d011132400004036400303200510a0415030760f0955940d4081500a4138020083d080e20214110659001d001e0700416944511585812040300002881ea940071113101802c41c040650012080f900410054007104806800b2182c070070320f12300c50344001c0b500e8041d0920711141044481031030a01c6004c0c00450202c50001c010010340d40d1035202c00c240b2680e1040100c003a95000c40360107006812104071003402c0d4040e2a92901c528100d00240d40910f01200c2c04204150130885205074004d85071000e010700345e0028401c0b2405042c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 933468237 1250 933466987 933466997
    0x703030c0e0f1c060203090a030215040302151b220501020106030213020906040f0602032701021905010e1009060b040504030801031b05061c05090c4c02010c 69
    0xc00640000c0c041c0403482c04140c01108060407082d68105102c0001801944c004411901c0781000c0b00341035900c81e48410110003511403d40c02d8035282c1c10452026204562690041043d100b50340817012151002a0150340c1c030318586403041642c40040e0b40a0090800c101c3e105c12030f6a11400d20b0418141d01c1a4007280c1035900d400010b00140c4c540721400703030146426010150342c500b020408203c00784100d82c0586100f202d041c402088031a0b0200c004e00e131440c65600c200c2d003081111400001444c183c0241d05001d03a001300c0400039a00900c0840541c0c050069000207031302566505000d041c0300c09002c002004603540e411303007c10400e09118800c00100191801c00851501d5640a402018103000c081d0505020080c00c81c0000b002c00c0401020f050050415520b44a020745040c50aa00703241d144445541170100041c180000040e000d80b2404005100801048030440d1400c0002d02034040030844807503880e0305a0601800146040f41151103d400e4911803428140003821200400c035400b007042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 933469487 1250 933468237 933468257
    0x16230a09170d180b0c0f060a0b0906010f020a150b0109120302060105010c0507091e14150f010c0b180f0304060207170114040b09012708031806010b0703030c 69
    0x803400600300b1507000003400d000c0c0c2c072050811424001e400007075001920421001864070850580401c0110480e1109401c80f0f0041d1500c4040c04142c9211151b00c541100016002543e1307580301d21140641402c0a0042e036020008a40b2030890741c41007811201c0402e519034080082d81d59000c001c420050000405440182c2c0300c541d0000d448541c188951b42c108400c048811080c8a000c0c4448001040d82c070808000005061842c5180401c1105844010078a000340500121044134100e91040320742d400e0a0b20a03071003000400200c1e0740c0190420f810041681c2c070040c0012003016100b40550314401071801200394101b206890b00140c042e416030395800034041040303000e4001809500b510300c0301002c01a0340195040c0f4600401140c00444070041c1c605042c04240408418542e000c6c0c05c0ca2002441010702d80340742c20b0908070318241d0865507441140c402d00007068541000c0d541240200c04c0101004035140c2000c1d18200f002e0f0001240a0300020301340e410907400d44100079003103080c0d040c0f109801c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 933470737 1250 933469487 933469529
    0x9061502030f09040c1209150b011d1309020a030506042904030807050f0d06061418190515193f0207110f040b060316230a09 55
    0x703030043c1605103004586400c03000780c0c01400740c80c00700d05090070907504100c0c0781c80c14140000104107091403088036034900b0003034030303480e5204100c4100010884d0b4000518113500d04140880d9000802d904011280d0750408400160340344407062004500400040405081c5820b00c11011940034100d40813060321039040d0f07110324120005590703000e905400c0040c3c0607950a101a20284078051103400d0b4401d00050341060140c640d400780701510303d2030395a00000082d0340c00a00f181d114000d0700c60012034194039000c3e06803601c91380c148020b418200145140c41e41c1c40010500e005180c20f682294040d0110780e05d8031101d04048283d609002c0303450304007a03010f40e88901800003c0c5031040581e07410f004c40840f01c01c03240c2141d103800340500c003c2d00455a0307524a040400ca000501c10341140300d40a5074a0001e503601d080e00a4208441300100322500c2c58030b80c00c040b90480764a40c1081000e02001c1880c040070301161003000f450455124044136600c95041c00c004200804070b42181100f426410310102407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 933471987 1250 933470737 933470767
    0xb0d1401060b091f02030d05042001110c060d020903030f031503030406080a0b0f1e1e091f090504030507050609071505090f19060207090507020312150a0906150203 72
    0x1a1620241a4881c4c2801c2c0020403400c51050314094202142800148020000c000290750307d000c89003482c00230284c10312001128258848410540d0b2355218540600151030320a00500b40340c1036620006190801c900d002c0780c116000b80000000a03080801045904501c3e4543e00c3e0001108802442c5440c0c104680a0188040544040241560380544c0405919814042056844020222003440245069007a504005001424014018000601034090f500c12110540c0c0c0002081e50ba103554442200030205035070962000c80050054400040c02d03042407107401d000314000e07038540e50f5994250030040d140010180c07145d00d055111880402c078400000c69100607800700f600c1c01c1681e03498440002a0a0104076940c01d6100c9600e0800c8904021103c040c201100c0c401d0702690140d030354841082044803801c40311000940c00808c010034400e58000000341e03000c80d4800341840c68154500109101003e20341080c0303089584c4403410b000010548460010307203c550310045150655054001d04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 933473237 1250 933471987 933472009
    0x7020a050d081306060b21010e0403050c071e03061d0a060e0c0604090b120a0305220b0706150f0315090204060510020a110117190b0d1401060b09 64
    0x2042102c01d5012841c05406030903020909500041d06008103030710b03074815946036880310454001c40c6074165005c03010180000c481c136040320440714080c0d481d590b0b561001d603041d6000740e014035010f004500001c10a08280d805200c034014100c4069120f1608500e0303c13104035a0700f043c0c09410303824400760f4a40890b00008541c1c03c120340c03007240410803070f0b00702d40180c0c50f00204401847c6e11080210b40410303009403940c4145105c1d40100c517800c98101d00c1e4010a44c442030455009000030b50704002c42040e0450912504928030799069440303511503a910b000710740c284c10180703007101d01c2500e40345140304464581d0030000140c1958107080707104070300e169035100d441303107884c2c690a02c1e05480b200d040003503544a6100704000d21024100724100600000700075212030780004211240151000c1800c5e00d075108180a06071440c0040c09400700352511141d001ca0904d00c6000c01e04c1c520344521040499440e0394400039022449210705a215903503481c0d01034250340007600040c8016030180140320f4142c0d54000d50300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 933474487 1250 933473237 933473263
    0x9140c0a0603291f050d110406050d151a0705070f0f090e010e031309050a0c12090203010e030d090b01050907090e092a09090a02030303152403070807020a05 69
    0x502000901c80450b813000c2a02022003e1140c603105458042ca810600910051a0752070003081500165540c91000d13005078040d807400a4014042980040f1142d4014031070f01c006440c000e8155580d03004c011038400307000000428031000200300c58003080b104200c00c4000d000750b030030882d94150800400d240e101c401441005041602c4030742c01006454207501058000c480d08058903610603807072601c0c000d1005503100d00b845c074034505400a500c403019846000d8030b41c03420f0390ba0b40c003a558440c18182d0141801031402c0c2c0c9d05550b60303454003091404c01c0001b0450070301c440c4130118540c40b0300e082030310482d05d05a104600885246041003d10340d400b2880c02c060b0388131030035404c0b40b40e200ca050140c034158040600c502401c1307004280821420300c1c0d50390580030b444100d8461a466030355915050301d40504040094040d4001e2011680100d40a010b000c50300002074008160404400344602e01c4070160109401c182c44000180005154010b10b1540e10461500050503c0744055540c035a5071303c45840c0d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 933475737 1250 933474487 933474551
    0x10b0108150d06061d16020a020906220f0c030c0c05060c072d0c0506090d060c020312042001230f0403021017012112020109140c0a0603 60
    0x9001003080340d9000030003911030086000002d1350b0701c5c0a42c00c1e68450503258411a03000e544580041c0314400540b52500c10b901030285111615004140704501c250fa0b50411580040b80c829a0702281c81c0b84144040f012003618081580c4030210406012260f400c00c501c030402031502d40303030004110b000500316042126100781030b81d10281803c21014040c058650812031060f13000e0b000000e0404a402606142d000700303081d038a4182e8881c01c0002d24841c01114a0f04400d1180200d0081840740d800307a10014010300540c2c0ca0302401c0c201516240500711000c840b180c1000710a004142e03800b00b01101c9004e820309102d151070301030003403071124050121404219040005810f040c00900b81c821b0350015035000d040030b07030440714480c2d019100c0300120745841c410340ca8160001910706d031840c07201000401c40e801c512940e100b968991a03407140d260200344041d90340321001c1e50f00064000355000d484440c100060701c0358607495000c10054110a07403048040505100360200c11903018503c020004038086c2070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 933476987 1250 933475737 933475759
    0x415030f021f02070302031612060b03102901081e0601181206140105060409150b070b0703061a18010e03060901020c010f06290c16030302010b010815 66
    0x10300d8461100b01d0700c00c801501e081c00510381c0e680006035081a248200c05071000d00641f0f400e0f00000703481320721550b116a4859510305d0080b80c403540c00880d11080203002c1e03900400201c000354098034400c019004200440451841c00380c06030002001c0c80c0403003440e1816284c140351104880c0050007039000c00070100a4000304a0907800b40804650140071100141001d40c1d480c0e110880810786294240c03596030420300180b0b824545c03203503003034141d03117006000500782410010010010a000c2140303031280c040c0701102240032100400903103900c46c030540d0541d50500e00444020300352a0140e010710002c410041400c20100901400c0e58080c50781040781d001c801440d000100e4190214041480d018042c0100f40300c0740300419001490014069802845503c6141d050a401c440032842000c0d10301100c00780490724149200c10501e000c9500009060900c91400700007400d00200218600e401283c22408100b01502030103140c840c400b003420480441c0ca0811105c018005c11a0320781441503842c075039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 933478237 1250 933476987 933476989
    0xd1a01121104381806030d02121614010615020d03090f0f022205061504050a0b03070c080c0a02042a03110c010e0f1e10110d0509010504110415030f02 66
    0x1d02c2c81d1607101c005080301075806400082d80e01e03844050341c82c00e011f0b00500a00303115040c000150f25603140d40f0030b905140b0b00340290440030501d110054085031002c501800070200b510090080e600a0301e024001e041041100040c040d1506810700c905d0302c181401c00e842c141c0840c2c4000c003441309071034204500c84103040c010f20004000400e4240e0080004901e114003015084599203d14461071080d10ba1210b0141d4081004415000d17900c42c581d48040040d80c2400690201d50107950001200d0038000034804490383d8644007a009001421403591000074540d081d85800e0142000c0403d0701000b120390b03000000100380b031014002854000b45911005400c5030000054111500100ca80c002002007507603d100c17680c0c9403010300e50020010300c02ca00c42c4125080290031103082482440c03000b4004a088030414001500352007401d103001c01d000344000d8907924501e01503548038001c40340000506140c1454945200361070100d9050086103080c0608010142800394002030780e030801c120150040081c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 933479487 1250 933478237 933478331
    0x7080c0901090305030d1d07032d050d0206040308220204150504060308070606060f02060a1109060d0e0706031a152104031b110d1a01121104 62
    0x984010414417000480044100c0c16902003100030030380703407002c00a0829003020700750b5960300303400003a040215580c43d8248545903110f882100c0c00c2110345000881d130f650380f10365060440007032003500907801c01010401015400344103a030344071007008580c9006076500441040c0e419505000240103d90340c0c0d09004a1000d181d05030703401400020030502c00c0c25101c2c54007824a82009808440c1c4900381100420400c1c0135141c04500c0c4040d66004110960312004207002034007080c0101c0600010400c02c00c2d0762130f105d070b40c000c100d0014100320200301d803180601e0321440e1018562000c003c0500e04035100a544410040d02c915840044070401c01d52800c0604442d17240c80707060710110121200300c5141c0440c103004150140302e58001d0715000c440c0c0580f02c08080c0c48a988da00c00034828154034814a885291002c400410075008071a01c03841110035031000c800d015405c1e00404200343c1520004020040c0039840300d00c111030241c3d82030140f42c00d00d0010300c8650b03405244031003200500c0c13402c201e0051903007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 933480737 1250 933479487 933479489
    0xc032d11090915010f080f03090f09040807020607060204031112030d1d03070b01030203160e0406050a0b1306051908030906030c0706230c180907111510080607080c090109 75
    0x215041c083c03543e603a0039424030100d240c803844030340380981c07100090b07021404015101144006032030b480441d2a104204903500c000140300301c64034101404000d01507258a00542030b031070f100d094016965421400d050113804014040c2511030840ca90056030100380103c1600e40791103604001040c00c1031444592111034058070000c0c44140701c045030f800240701e004203025049a00030390036510854030032035100003030215500980b0b8542d860a400303e0000740c8242c1c0181da0100c20031b8000103440c4402c500148420300c0e40ba000021198403200e041c0301c0c92500500c4400d0b02420340340c090303840e28070307014140303440e40100d00b02c5a201c0c4002200250003030a00c60201c034034983e80410104020700e03145035210f02701e82c1002010441d000350b000000704601140b81c02c40c0d5109111555037010540070000300146420000e0108041201d00440810800c4040013113650311284265000b4191416015440d05140141e000041c5680005c00381b01c0c4d02500002501d40201c00316865951794140e10005032000c03002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 933481987 1250 933480737 933480763
    0xa021201141e010501110304030b0402060912161403300706060905010b04441b030a031d01170109050709080111250c032d110909 57
    0x9a60411407141000714030b50a81e400e6000a0b0b4407566211001100c41807514811090540c0c0100000e01c04111400f541541c4184002c1c000d80c5404420004100b40607281e604061850784102400302e21a40c03801d420001409201c14841349540c18000081d81d1000709244a904403e5407110808441901c00490040c2c2005010150b42d282564075142e00200349921800088918000021440341c1c080c008440442d80c022103a44000422003200300060058107182881d40310410200c4801103202e0030340c0340700032140c803405030090360030010a40d00c42c80360030318526202c1c0c2c000da1180d2001a4029465003001d008180b50340d804590303440010303109502a5044080034008402c000540c81c01a41c00044c410f005a68694002c0b955828a4500341c0304450800f1502d90310a00c1510002c0c15545521040140d5400d00501071342842c1d21061034028140c0c0041c0c641541580500d185421400810b03038220f06450500c000d041c02c65200d0080304441000460300c03640441e8041400900100326845030004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 933483237 1250 933481987 933482021
    0xc0902371d130c080f01080601050105040b1b010608030414040528020c0610031b0b0d0207080d0504060c180b041403150f090d08013b13150504050a021201 68
    0x4042d400203000d41204a030f82c0140e0101c1c445c00803520400c0810f006040740c03c1078603058202400d1206251080e0001ca88894400e44040051101a40309008030402400c0d103001440e0798500348440c4c01500005410194000c41c2410207202c41800844074481c01d40c202c18440f40c60442302c954485010b842074024019451055005028031007407183c114008603485001500d0443d40c00d03001c50b00c0011500c1c410258500001c1c0200d108030000d640060541c0c070701c11080e40c1e1a00792040b01d400f040b124207550a40b201552000300540e125000781c030380900742441c2d81002c0c040c1494000200068862401a112880703000e42036640e098a080210258400050355040d0091400b070708130f20350341ca40c2269904500d1050900b1816401d009401840c1a43c15031402c1e844100c00000074a02c1400391002c100111400552001d0007070500c084400e4000d4085200030494202c460529030492800d4282c40b40034140341c2410710001410004046400d43e5068580328050140003444034010720140d003035543c07050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 933484487 1250 933483237 933483251
    0x105130209092b0905010827030702220c02071a1309020a08150d050c0609010203133506271231060c0c0902371d13 51
    0x103c0e4424400034585499070707035848515940e01c01107a480005840c0341501003560303103421040245444c1850b0b441050f0f031040300d00e41001d5502041314542e00c0c0e0360880c00d00f0018030714900b141c08107014960403a64030340b00400200f401c020042e281c458540b1b2510480304000100300780004d10225030340c0300820010030b0464031880c440c0000780074847c04541149841c0204414545a4034120005104143e0070030010218048490180001942300c0743e80941944020b11041000403691803240c4043c20390444000710020100110000d1000f41c015641e80300100f00a0003402c000c40042c009510000090742d0a1121a080c070f4440a070704841840e14000e030249070b117100e0300809070000402070b9035900180e00480d2107001c5904101c80c80c01c20442c195001a0b61380800038548030701c012108981c02007051081c1c1c0f03651803502000300e84c00100c10940f0b00c0300310562a030101041d58199804420a910f50406100c544007008058a0482940050b10080c0114008150f12804608041d041c42100100040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 933485737 1250 933484487 933484543
    0xc0503060f060f040302010c060207050304170d081b0703030e0d090609090902180403050d0903080a0c080108030a0f020304090f0e060114010f110a0b27010513020909 73
    0x1a40211040d070302030070600070010041c0c24034100301d40c02443c44651030343c20241181d004540b00c811052050300c800382c0a00c401c1d400700d001031000340020034640b603001d07100422040c540c50504031008291014002c2400030042c10b00f180c68140e0011001c07400082c0c2e661840d5150540061a54000042e001d200d101d1026000c541c102a080094580c6910307109110b5503101a8030054078410003000350031440301c040c00220b032078a500d8205c1c1c209110b818a54241100610754204461245e1015000240a2014803841e0402485101804055071400802560402018650700e02c50345141000b0060307400400d10042d4070a0040d50082c0c00006424450385a0040090007c0c1001850354906401210000624030b141101001c04c024410703112000480d0803180151410380001458030074a01450002000040c22b0f106014070680d00158140e03500c0e00701086850310171a1854110280d03a00d03003024425030580c0b28080065040d411950384800399541e00c5031034240050105100e240c1020780d001c1c0c07041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933486987 1250 933485737 933485747
    0x303050901030e0111040506070201090305031c1a0904110d080c0604050c030a0312020708090d052a09161b060212060429240408010506061218100c 65
    0x82420240d9050083c00c07103640107103089030890340d01e01038022800c0200b0821303030078064003400c41c20b4014100303010002c0c2d580d1079190855010034021203000109070301c04142e5441d64483c1c80401000a0b003907003031070382c0c1000c0407c1c203100002e00050000c01821000c40c11560340c185ca42410300d94800d0b0816107580f2503603011a40c9140584044a403402141000511801c0010b4401c0440d60559200440c0103504a1710318000d43c481c2d4000d03140d4103810059070b000c0b62600204803044602c2403000301080d11200a020805070041240d9030000307608540642110307031f00c141840b600403034501c0310002e0303288104000b60390018038210807100700980004403206109169020300780c80403590100d20660756a69042004490740c088981289400210b682d40c000b000d4940c11049a01c0094000f0318400c44540c0000070361180004a141d0035900054144140701080c0901d0303802000a48001d420800c100c510307024a510010444441d0300320000003000e180e8020081d071600f40c4840001001248248000105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 933488237 1250 933486987 933486997
    0x2010605030c030d0512090a060c12110a0212030c0d090309031712040f0501060b0f0408010f0207030c2d08030708090a2001180f0f090e060105121006030305 69
    0x72007405007032010040750901160010300074219a40b05481e04110184400640c2d902a00d805030034440d428101001032518072070003811122a85403400c01a1171955800c061300c032a56940213046100f800103e009940004610317254401014506449698404070f0305180c3c0030741e4101d449407504040900080c103401c0300443d0282ea0040c00a00c540d4121014480ad0b5031141020f110400c088000005020410000007010790b01d10803000403802030b6580d00cc400440e004811150103580c0f0001d010402030400344074141218101800543c14840180c80152180c4905140508840010100302c02c040c141c501c0c5052500310b45148240207c10b581c1400b4030960011210a07010540880224000c04000203140007102d5101212100072819640c4005401e0104044e4505100b40c10342d60000c12296118110082d0410120700d41e021032504408100022655120056903850080441c01105010401605642040d10f403c9005150f00180300d184c9401c011045102c0707490301070b01104060340080182 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 933489487 1250 933488237 933488239
    0x303030a060e0c070f0f020111010e010b01090e040203060f0417030103150c030e06010314010b030a05010b090705030709210206030a0b1905011e030204050d03090e1302091503010e0a0302010605 85
    0x1110f6660110100c4284154100501905584034440d00003c2e401c1d01e003900c12601c10f16250000e045440c020702d09580d06110351000c582d4440010514559124079584014900300b1002561828160003190b101c00024102c2031003003252b20006800c3c400500c800c2c2d51120320021301c15540c0d40c0d4909002d6442c1c50300d252041c44090409a014aa40d8403a0040c50752103900c010140c880f5910315550251782003c52803003805655256a00c3e01c0c0d80d0f60342400715102240c0544000b00300c0703034800c00420001c1c0c070008201030706111043c010700c1852680564114151281d000c4a000e0740000840c9a200e10b0402c02402540000000704110300c07100c6a410408440d507050310203980c4010249200111010035020303150008160701c841d032900c3d45003100382c1c09103001d050030010302d419181c001150915841801c1a00480c80d040b804210a80b80002c800b0341c4040c242101091005a95000545c2c0d400003402c0601c00822800d0031640a5400b944640d0510701c40004a4105000d40c0c42c010380604500d00c241 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 933490737 1250 933489487 933489509
    0x3040308040c0902040b0306041505031203010f0617011e0306090602211b0d060f06050315010f14130915050418050309010c03020c06040906150c0816110303030a06 72
    0x500907099000741c4051b200e61301081c80c00d503a0b9220901c0020206074800801179035826600041c0703a1414080540c401e003d0040861383c960601c0096035003608e0704e50144041003c1100815020104800c02c41d05580606040b0003003030b40389041d812440c0c1142d82019041900d00031039503040205903402050070302e0358100207002000f00d03040c1030410356108030b64003d01c266400140c1125048058020b040c441c0e90b00c000020ba40307450b01803180000000d5004040801c0c000818040030002200100c240010240b070008506907020b50000d0248000c5c000c080c00a40f001b01e002d0b0620b0b0401161003002c5c240c1200c0400104001e4200c442a021661181502443ca0301c481c600e00140203100c00040560010000e501c1d2049000044030300c4204e21000b502180507580c07500040d959524001e100811000001152540c100480401c0d41c4801e000c6540500511003080c800288204c01a02c000702407081c02d814801040d410910440070100c4d0459a25020000c05c000303810210f9841842558145615 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 933491987 1250 933490737 933490739
    0x1006030b0a05090c0705160e0f1b16080c0a03051b070f0b0c030d0c12050f0615090d06090609030810180b0402210906071419030b030303040308040c 65
    0x2400001d014500880f9003040e207620000d8000c011503c02401c1c0188218100d9003001d8030030300f050540300c0c0c0d150800c41000b0980c200740100000f04150603070700300191809013901014209a0403803176100d00007039000240089a80807041c012044165030100c140c0a09070f5078100498a8010203c0c5e00135400c040103044041d1010100150000b143e60640307003100d5058040606222401800e40c102119940e03951008005c604e44550f090f001e5000002c0c0c2c981c450344890714407510728005955000300044c000c5e071618810001503031f0b1200000303d03d010b0342c2400305a46408070780115001101c1c441000d003007079060288032010440e1540c000c0c400340d40660784026064803828400d0702c95618600c00c030161103540096400d074a00f820b600003224031070020f100615084940d6400100d405180980c50f44403606241040358082c07091040c0ca038010001d01e007480c2c411880314a20072141c00745414a1503001c2c10100000206402a4000d8920b40c2004045903102c0c5010301d0014404941250115032180980320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 933493237 1250 933491987 933491989
    0x40606081507090906050d02040b060f0a05070605060108070e0d0320060901050903130603020a020102131412030a1d0604120c06110a02010c03080402010c0b15010315081f0e03031006030b 82
    0x20401c03046d15002021402100c08036000c2002504a0603045a40148204414607405014800074103a4450b26101d0701e417505100d0402004031403000f0203041c144482941081801e80d407040d101000d08104440c0e40c00303c00405d0508550851400e0726113144040c0c4441ca034070405100141e0148100504802406565035886d00140c903030041b020604034007800307050184212402500941071244052000508290000301030310090045944052061008142d84260a080003c2188540c1484800951420300071000042c0810000440d00d0405020b0040c5c08005640707035812107008058542ca500c005100ba4140100702c11020b109400102c0c90800e41c00003141c10224201c0380103501616845c0d200d1000d910151942c1e00024022810403042c40f284000140316500040d0050a50010784503c4900701c1e000903040b245a0560761184800081042104110010302d044100c1805420104ca0310f140381000b04c00f070310b03550303100500e540400b00030409605e4460440300119803036954103002001440b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 933494487 1250 933493237 933493241
    0x1020909150609091806070e0414250504090212220317151002030a03060b0c0c151201030501050403090b030702061611071503051e040b0406060815070909 68
    0x81542d030041014061250507107000301c0010b03880040700403140400c03074205400d5810400704650b40408168030302d42444480c1014031403020f80310419440149242001d005052000c1d0088103081d1080713003111941c0201c2807045c8256030003008900300c155104c1d04002504600031004803840566000c00c40c01d5840208168003a480945805454100d0307041140da541d2031200c5001410300b168003414411041d01a280d2805820307002003194040c680300c4100b22401404d4a5442d0300000003640140025001c100340455a80c030b0b030810031601c0c000041410300e041301140c014500b440c0f251021102c0004240b00042d0401440341d480790796020001030b15a02c01e10480e000c29070b01800103a100d500064400200c8a4201c40b03ca4030700d08041c2c0b400c0d00e030032041c2031600803203802800855000306144001145c040c02046d40003800700c0382d0034203620104000390380940c00003407010744003c0360140410300784045540302001800c0d1007826a0103100c03041100300000301c41594510f0010385e21480000c0c96407054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 933495737 1250 933494487 933494521
    0x151d04030509040507140d15050a0612020304020409080f090f0603370c0504050909010e060c0f04121412030702150c2203031103040303050403030809160801020909 72
    0x64072080c1c14102000240001800c00030071040900503956804800540c910f800f0700024050703030b02c02144c1c505161340c18034040b4500e0352215000c2c8101075401d01410b5001000e0000302c44c0c100d03000507140e40e641c1c00001e02400b4030b203601400c0c20200081009002a01310010540c20100f80c2c0c0c1d010401500006002d0305200c2100c10261400c50385c42c090803070b599000740045460340d038101080c0c040391140d01e88000700c500343ea18420106500060820403800c000b00f403154003d0800c0000c002488420041c0c545407400102444120003001840c1d9021a41d60410b48000d00b800040c80120081035180866400107008841c903d140310314007a103801c44904408582c46484158058200d0805101c403100b0031f2a005403445d801c4203030920144803c5840c024031074414141001c4610640c0d451800d0242000f5900380c0020f80300d030401c010070f20210b500314045804582d07040c501480c1035a20b8583d12403c240405824151701e43c03c1c0540055034803015005000c0403101100c414184c1e03100c540700d0000510f12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 933496987 1250 933495737 933495743
    0x7050f0f12070b1003050f070f080604020105071b08010615080f15010c0602120a050f0903030103051e01020d06030c050f03010216030528020a0c0b031003120909151d04 74
    0x1040102c0400a01105101c0b5003010030400e160b001161241d9502d402c00d07410440101c12030b44100d40401403a460700110000901440b0003a19250405400003002445080005081003620750081d92801e00e000700c0c8900188428002042080e86400d50b01c0008034200d01c0740170000314490013145081c2040700030540030760b2860281204468030302c00192140001f025040c0c641799424801b9100340340c1010030652140d208040e00161924003450104140d100291640006a105000520000d1400148201c000c041405040300081000480d40d0191080400c5ca048080c100b917030000c20040c00f8013944090b1752085940c01458004a82803500700e001c1e00d010b89450303130141c108480100c0d01940040c200034010403495100c6407130a490449600981082050050303110111907030a004001d981040030300504030116185040038001500d00015600000e40504c0f580d95030000114012103002000300300324807092120454a8403002c080052902c101800a1064508142e03200003030801d842c481e6034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 933498237 1250 933496987 933497023
    0x516080c0a060e0307030f0b07080106020a0305120c04080109051c0f08060d020f030616031406030a0210031b0c1518060216140307030201060906060f031e0207050f0f 73
    0x3140c4402203c508102c0f02d60107805004020b004400b00e41c480c03c505a900d400341c083c00206090660008080803016442035085402148100b40041d5001045985540003070b0895230194541c001034680c544215484582d00e586420300c0c000030400c1c0890411030103c1e88c54100e032a248812441035a07134031112800d0390001050301002480500d800300c2002ca10344e0000d0280c6003001c28140100749401c8003520f104c40855055108101036a5050003030b0796507254101c44820140c20617101080c0c0e03c2c811184003c0c0b046039850f01307822205129512140d10480245402c071035001c00d5140140440c1039004050799211040c14074102c51221074000c64451150450006070009182d484040c02504401e03500303190411035170725a00110307400390032100601406201440d40d074800307490040d08580c0b169002500003810000104100c40d0004105041d103071144c2008112a4413410254504000440d0103c4102d0310200b001018860001134120500c40200c08644164204d00000d41d512a44040c134810044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 933499487 1250 933498237 933498239
    0x30c1409010f03110d021b0c041107060e0c1f02071205071701240923060607080408011104030b1f06050a020c151804090809120a0f0516080c0a 63
    0x54441c1d4804d21144034100f44150512001e68036400583c0e001e8005074400600c0c0c2046a84200d000307224801c42d22804070b500b002000280d004513100707030003410b801900b5180d84a544038801e01d0180024860b841c401000e8540301612542d0340964070404844100061290100204241c11104821003240360000d0061030304601d030010380300440c1d00400c1035501954890380704102d82c4540c10600300114201c0044108401d082c42c070010101c2d5520100780d918102d521094000260040101c3c5400285c2560050f0f07030384c003407800e0500541c8580c2d0b00036140d540c40c090000200c000c0d458080c0058a12883c000702e142d48590b00c00d500b0124011030010a8a5081c040c2004680e025000034001c1074950b006459010301f8800004543d02161000d5480c0d0b07950008042d034240005a84050039201c0494007041760b00f60341c1d00e910307201c0c1c01180c0c055406144c04082001c880070003001160a143e60003401c1e050104c07402d2401301d44030040355100350b28800c40368201240310000450070001641014096802003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 933500737 1250 933499487 933499517
    0x1f0915110705030a02060f0601031a04051e040804090b0108040c1e031a18010c0813050c0d08070303050a06081c050d0e0a050706020607090b0706061203030c140901 72
    0xc000d02204180d004608000704800914240040d104d500e260340c02400007407038031032a8400d1a076801080d581c10540703403101c00001054096141e0895540a45d000909503403405106041e640c4042c2030300d0300300240c84c4208400c02103c00000c00a4a01c3d100b0180140d00c80c01006450554050718010710041c10031030180007240ca84040720640000c08807507126256034035140e400645410440c4801c0b40c0c80340b1010840c26001404040c0701056510f40200181c184104000300b50400c080d00702039503c010030b035840003800020004030300c107018010412545055540b50022039035000d188102e010074105000141d05001c18400c140031144104003602e91000948205d4801c456441002401d114090003c410801c80d10310070f403804401114000c002d0480913003400c80c0740040d0360b884002103511140400940b40d6100d0344400c100ca43c01e807415600c81030545003410207401030350880c44140341d490742c02c94181581a08280080023103929060134101d03001e0181c111911425031058040b44481c03000c0600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 933501987 1250 933500737 933500741
    0x306020702030c06071b0f14011b060c021501151e030e0d02030706060e0622020705060a060510030902100c230109170304170306041d1f0915 62
    0x305a00c0107040c0c580c8403404100242aa17007103901d060343c403264141c070f0035101081d5040000c00505a070500710403c00d03107054110168012580050360401613408569a084e4082ea5800d101155000c00705115417081c12500a64410034110018500c16a100000404104115440c8081d804035980c8400c3c4981940340701e02c421003503c499501f010f580300100b0b0300010051004ca200004242e003d550f0f0359441e81885001c1d10820740080d4070001b0b46100780482503448410710480400707101e000004140e02e54038224028003500c48040c1040c0180020011041d5190b0b1052050f54400c580312006002003005c00c800701c801c0c42e14001d400808005001450754026624000c046100c1e21000180482e148100984040f4152110f190b41c0c0d11078050b80104440100c40040704020780d030101e03085180c561235014000e000ba002c661406140000420515205c7c0d800800f14640c20103010403c0750008450555603c481144000094904070101c5099003083c2c0a000c1c81903420401c0d0503145e6082c0e51020300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 933503237 1250 933501987 933501997
    0x140904060b2e2a140304090c0903030306090e0c01030b04020f0d02031008060f041511070c0e0901021206060a051605030711010903030807030c021e0307020f06040f030602 75
    0x1030701441141e040401c0d0003402c0060041c0b464600720312400c0c01c01d190400b8001d011a10100b0112040001800103031024031094101c2442d000a0300076060701c0c121502034114890f68100d00702041c104026031321096000444501203030f1180d0340400c44142c2e103180708400c96680003052141c2da001000c10303c00a61003034000c00103a21004000604d0044099030800d155409290032040554010080090495503120140000c003178007006010b1702c0c603101608501112009100410001d1011403452810080354881885654500d646c15920b0f9940d05113240d81182a00c01c8210a40b08c1c4000101511018000d465030102d40c0724914603241c41d00800c1144a8220550110401c08280b00328402011002c2201e00700d5802a006155541c507141005400176010402d02e43c188950113a08000003940010480c1d88030100d8540000c1c1c003070703010340200d00b0300e82c1110180c52209003000030b82c020401c002c4010308003540b080716a038810400407001c0c8002c03401288654401069403c00c100042003458000344 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 933504487 1250 933503237 933503239
    0x6090408191b1b080a080d09050109060c0c231b0f1507060f0203040f0303020c0a12170f060117040c051e0405070c0506070309050c0a1e140904060b 65
    0x1514621110a41c079803110142c5100340c0e2500c111681c10898000c540841d040074151801c060003c0c2000303a110f100302c500c42c405244116554560b036050030300c0300030351050031040e5000101f07100c600c640c2a0000c0c40803600010a40f9098203180948140224907400c04070741c041c2460141020b0000c4000d04244821034100d43c81d041088120031311040c5da80c00d200ca500b45a1413600b081d0b100d2059043c00760842c0e4400c1508156288100b05000c080f8944620038440c00394113140c0985d1f2500c10036519400e00078400002882114403000c0c2551181d00000054007207100d0031412105581c2d004801003a0701003e480b5140441d003944181c103412413440c02c100341d006000b5580552000d680d04040741c0e4a2244100b00507255001c070030104801c1c40c007070280c4da0300100b45103051002c030744141c1c807800d4131403402519104c285035951010808004040c8002c0d030540d24010240d0300b00f05c1c0c1c0c0d4a03420300c2c200c00600039660404400080807900c2d400c1000b4181310a840900b0590140e0b42e281d5481008140c41030000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 933505737 1250 933504487 933504497
    0x9060e060f0928050709020a0f0509090a050a0227030d03060e0601080702120430150c030617010213060f0914010302090303071406070504080a08300603060609040819 73
    0x40f6011070303010044080202000b010041e51402c01020041491000030032480c20032208128102541e6a84d12100d90411305429000545e034480080c0d83b0b0003481014a14040d4001d031032540c60b4000c2045d400131030060020b0b029501e00e145074a80444c200c1341d0500504008030b00d0000415030b1544100e1f034066214060307004480c143c0c0449a07030f0310000d4105502844404080d18002c0640344a82400a80740d10780303594240010305156a60f02036510260b210203280302c1d6542c005880c8032403198001c071009144403400f00304440201c41d80c8901079804940d0244160800302c4002034502d10070b48801d0000b81150340d03440c04440c00e02d600a103c5441d81d40d5410304154080c40308101e02eaa09100a140192140b082203c000900004450a090005040b90144041403004110641c0041001ca0000c0d50154110f55103140e840407010f01514000340008410104001c440d01a041701c55481c0d001da0012403c403080c135a074880030010301050441c0d005000101c01d00c400c0c0950b0303840e000e510080c1220fa00b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 933506987 1250 933505737 933505813
    0x110d020f1204080c011103060102030703030c03180b0a110705030f030402030111031609060504050a050121180501050606090a05010807020a060f0b19030b041502090409060e060f09 79
    0x141c0485502581d00b030b164803200041011000c5400d1246011540344092007505618002c00040d4aa00a11f0000303028141c40c0ca0564072064801d500024a010401817030000b240f88034108044020300480d040c040740361501c02e007000240004405c4e20100da80c4000190b246ca050401d0001c0c01d9040038004903003564945540d03012000304000550310078450155801d01117140c25a004010384280c1e44244140310081105100d03680350120340300700b1340f4002e003050060300d0442c451a182c0c030451103402d500084e03d020303505103075003041d003002100a131b000d540284080d03181d40b020000103100d80390f5065400310443e1020403282d4001c500e841c0e4017a8450054036104071031511030405640d1119044000640d0320311510303a19260600708441070290003440b1034201c40c21075035a0f15082c6c1000e007001d022495189508001620990100c40036038601610911030840345140c5000640f440d0800b1001c2c80c0500800074800e500384050319481003942c01c008202c070cc0c0c1010b000d8031400ca480611703610070b0329450716 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 933508237 1250 933506987 933507007
    0x120b0c0d060b070b0603010c030b0108161707030903020d210513050f060a38060c1f050c0c0c13020d060f030c0b0a08240d0c03060609110d020f 63
    0x101403c01c043c060b00000301d8500c0c00d041014215108010b2032003d0600c3c201907518240d9022001c2c3d036200e139000c40c2050740722907001800d0b5483c2d14541d140860070290402005401d540c150070009881d40b0a07000c848035480e00b007006507240c0700a04030040b1400d161549460440e040390704240d421003101002c9203600c3c416a281d0504122540d0203241c901d071700c580d0901601000d544241a100302c8001c2841881065801c154405070100809a03e881103c2e410904600d0782c408003190300b07000b407038012210680792501840741c02ca00382c50f8050018a2802001072100059003040320f41c1c0c0c40d100381c080d00c42405540104440a00c8524112205603824400600000340c0c611820010346440704c00301d01854918600441084c50541105d804400706100030155503422480c050381060f1200b283c142c40f400182509502c10004a094581c05005e0340888001d104409644506890050350148032503600d0b01d00800c151016981003459083c2e08001940307024035240c1c0a08056003580f2045407610784001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 933509487 1250 933508237 933508259
    0x204200706110903151b07231f050118112209020715050108010c09061103070b0705030921040302041a060304050601151e05070c1a13120b0c0d06 64
    0x81c0d0b28645c6203810400c1c45644900e014407440280c224031441883c00c0b0840c0e940c2040003100b141c8110310801c09051813039407000c0c117004000020204042807020301e81c913003440001400081c41081d40d4024400703030189002d0390724010104a0007512080a10f0445400c0d01400044c07000c03610000c400444041c0401e4401a5000900107030380103441122195501002c030030101c03681a8488443c42e89026020100540c00c5480c1030304654041c00c041c400c000b008401c0c0d0b4118412642c004100c42901c104100b00307290010040d41c001c15803802116206408c04030b107440705c0d400c100320030607000000344010001441d00760032241e043c9541d000c4083c000d180801c0440e00c01e070001e40d401c0741c80342c00140043c003400b55103100c0405114aa450b04083c61402449041004012502510104000040e4500520440076995401000003d801820001311603040010390b0b0401850090058503030000001c803c4110310a00c804a900031307000c1c051603100e050b02c2100c581e11422240c400103840341000140b8685c94 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 933510737 1250 933509487 933509503
    0x819050c0703080a09020d0209131e03030b010f0933170c0306090c09030a02030601030c050f09100501030e0708010c0504030201091706072007120204200706110903 72
    0x10000d60345485241c0303030280c02208000d02c043c001d9494003a0140142c0d41321035401903502e8044d13403005240c0e180c8088001c645400a5000780403082040121402e012054031000e0b03540340641e41c100b00740c0c44007a00460700c0e540080c98010004a00000a00060b048801b0080403052101040b151402c3c070081004040c07032860b1203400200e8031001214200512900d10980c0c02804210701c1850340c90b0520000d07404900c0502000030000c000b040e4540d540c1c80400c0912403064008088030360b035694a14100d2000c000070f008160007202c0275200b14036641000741401c0d0240c0c0e09c0141d151b0080c1e0900004500810649003a6042407040324000646154280710b01c6640b10310703560320180d49604500016003646070070390020109002146030004c2c441c0b000709100c2e0b001040703450450012001c881b510011030a08030883d42040c0200603000413a8020b40c0c803d400c00ca44240c400b40008480f01c0014071307090104404900c0203001c00c00001e00068403d9208000380b034002c1034900d040c09100c0d400b0a10341401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 933511987 1250 933510737 933510751
    0xc1203070c210216030c060f140c0d02010b0105070209010905130f030216050a2d0f0b04140604031e0507091418060606040b09030319050712020105060a0501081905 72
    0xc0c82d1240309215414040301204042c980500c500722490b580d181c60703c2ca07039131307108140402000590142ca400d00c990701030041301c1d80300031901e5111a040d0080f603450b60349a04008000d90310344680c00c0308039405141601d110b5034000300444426841c1070343c20400307480001e0204994140104031680000c40d000d10741c505041c081da00810146141e080b01351020301c0e55410151090000794810011001c100702840c0e101e4805054034070710070104c04c11500d2200c000f90085000b940d1480c00200300424400050400c03120203050203100c0c5c0d0600c40a104492285010140a00b81da100082040745415410728000600c100708541b55544e6404088040715200881e40048145c510288060070b20102c04110304064980043e05a6007000e0740040c0345031007544101000c89802150400180c1e07018016501101c030540307032071440040104001000c40d17000c200700b2951140d0740c004850941f881449080c2c481c1078080d001d00c240304c0c10180151514000200309802c021590041d0160700900ca00130240107600c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 933513237 1250 933511987 933512033
    0x20903150c0310081f0209210a110909060c16060c1d0907120b0f04090c06110f03040513020d0c3b060c070b03150a0603020c1203070c 59
    0x91007a0048407010481e0301030301310f90f072003140c6101c0d00071180c1e00c80000300540c0700401603a0781d080d90081000c007a141d141554124041d00840303034410a0100c1e83c3c54000b807080d8034500241c4003140820082c003005480b4091f81e94445030010314841600c42c001d100890016203a40c445049903a6140709445d40c146c03218000651306c0d40a58040d40100d084903540d14011204081c0ea464244402444160003403003041d201130f1200c800f90a561120740700d205100e40082c0040c450040d40d4280f550780050544501c100141162850401185000c6110300c90340004002441c58540360408000c0b550035095001501c0903802c0001c60b0703054540b8400d806101c4c0841d2500c00242e40311400728000005030482d20030561246039035003036000f41d040c0515800300400700c50064a0702d0268942c07628000780d9030451034180a0001c1480a030003007140c04851090320031201c2100b0191168801c8083c0c3c083e003180c070450b41e0b01012006600c4021000559405545881e02030000069522020066640007a05002d405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 933514487 1250 933513237 933513241
    0xf0712170a06140d0b0609070e120d02060903121501030609050403020106080c121f0e0d09030c0501031a0f060d020a0c0209010f03050703030f020c0603191419020903150c03 76
    0x450380c141c46031a0710108888000c04c400a1342c403010010b910040400e4400c2a0241c0050066070041c9003070158403002900002c2d40703101008802e0b5a07440d40760440e001512941e0002408080300004440340308400c244201c0745902c50b03002514110301e91140d0359042c1600c5800104200d12144116841280660300100782140740c041034074207180c40b42c03000034000c02c100d00d1134048c007010000302c0c4180b510341c00d4840140d108030b418030540100401074046600b4014001010b000341e50140d05501501e0081100740304251361080154101c410102c0d400c412981c84103000215480c019030608801003000c3d1104d0b00c0c054601c1e0760300080344e10036004135000c15409140c0c0d9055003000c1501501400b01000b03010040c40c01c680320550703901318070b100040402c0203000a4680d07180c4244a000348944002d07040c95100d0400002c07141d0310b10015912240150301d002c00100d04504560000703400b884400900382102e42806106201942c000070001c0e4161080404a1030729103206d982e194441d034821001e081c0c480c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 933515737 1250 933514487 933514499
    0x221010504020408120d090204090c0602070b120c0a020c0301020a030911091b130509190e122205190e01091b0804021206010803040f0602030f0712170a06 68
    0x1a00100c1c015841804144900c503400158103100e010080002c0d501c032130300c0c1c154450103040700c030000039007003414016413900f081101a420001c1c1d9040380c09a075403064980001c000c450180c8050000440c14400110b654000e41100908040900d072050f203141101c2c16000c2400ea81c090410342c0c0001e80c1d190303c24800d000307000402a0005408441c00052801c201c840344104d2440d451a0000d03200000500329201030001410000808028200320300c0c0740342214803506030840101c1040000390502c00170a64690b0041a054400118820100d0a00040f59800e010311400b00100b0022408541004101c581d41c144000f13080c1284508101040c074180200c01e4002030042c0d201c0500e442c184245200b0044500542c4000d2108918003c1d4a5554038000620340f000240480d5945009400000c00c12040101c0100151204801c041c0c001a030349107001c81e81c0e44201d800b171031040c540070700038840000e03400c1c929442e00d00ca42c0e140104000800d080c00302d403007040948002c00050b0381e41c036040200d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 933516987 1250 933515737 933515797
    0x92907030b030a050d08130c0612050f1e07021212070f1404140d120c050f0c0102150a06050909030904110a080a0b120f0a02031e150709030602 63
    0x841e881500500a42c2880395103050b921445000020706000440002440d0448060000c180454004042c01e40140d560344001c4c14a0300c2c07000304c0b605140d090400081041f1048519540103425a074011a1024000320b0300da5032001d009480705045001702055a220150321f50050910b085070030050003a2400d00100140c030840b00c0304060740c140079080729500c0340c00d444241554100d84203658140c0001420400103100041120380c01020b07880c100c030440d00d403598070040601e400c83c8030f1760844150500000d409271703440080480c580d0040e0f00886000304555415411240c00802040d0041122600c6a0001c3c511240c1258062000d81c404140a0039170303c2d19026402d11000154101807030b1054446c801840309400510454240e5144d2013021060386030b05c14800c0380c0c4403400c0c080e10800b18500d984503803280c06c10982603119200d10f10440d0019221026003c0d0401d079a280140b4034590807030241e003002c2000078603000902000d136000001088050000b4951440e00c8207090801d6040c2001c0320702 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 933518237 1250 933516987 933517001
    0x50d0e012c1c0b0109020d140a0203070815030d030f02070b07020a0501061a04031112100b1e210a0210090918230a080f0c1c1209290703 60
    0x5203040d200498010505543d4000d0542d0b02424002d81d6944046001c54060701203100f9504142125001700b018075216075000c1c500400d081d03a02d0315110b413190300813a11749a0459141c150b05030000102d51143c0342c0070b0f9001200d030041c0c2290150822640b40c07104044484102c9080d00903801c042000b1041003403e1181e1009082c1030a10104440080e1611000902850000600c00000f00c03e109850782d642048041c0d01c0700d40b0740100c803481c0c9450000c800c003a002412223035020341c034011305250540840300d103468a845000341941107044020800d403000d514180c0480c00c01801b420500001585640045005061007500e03008500303840c5c000148100c03807508890001025005500300001003078400b910384440d4542500d120a0201912080d052140c4094003c008103030008140c880c0c01020000303403c010100000b542c00003a003002c00c010f504690610341c500000c20500c000302d08600550701215119000c0d0403458561118a881591a01c5501020090001700242000b44041d890f0041c24 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 933519487 1250 933518237 933518269
    0x7053d021c0804051e030d06090e1b060a080402241b0c22110304050d020c090f0103060207060e06040b0604060b040f0b0a11160302040612050d0e012c 66
    0x1500300d00e00b5450b13070743d03e403c11000b420a188161210020403243d0420a0341d140080703e100030860103980b0056000105040b010032003c50040410079114507041c5900d030014081c2c0900203030328241090400f114407501c002d0080380c1c030900070b00381e4030f00b503a95164007a01103c54811405503509505403200001c44001d100b8018550b000c04084500c54940c94078010b8200d170f00114402041500c1e8650101501e10702180c101682030200402090020014a00c00718076455003c0e241c442c038940f42032090070301040700c243d060030301c9400041000422660091040ad03004c0c0d1000030341a00a402a00d090460030340b01070740d10f50500b030700f80304051510303109480c000c25000204a180600c0c00310002e008070400d105080b42c001010035414081c50080e6140280c5281d00c0040e500d5807445102d00340c02c000d0460109900951800c0400324210944031000604d6a401000502c1c002d0b00c003a070300700c84203002240154108544055200941c01d203020805003c59074003144840301440700401d104502ca4294980 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 933520737 1250 933519487 933519497
    0x2102041b0c020103110c0114160207050a061209080f3f0a090218041101050a0e090403020c040f1a060f07140a1a010806070207053d021c 60
    0x50350365034004805401542c1c0c28200442d00340c00e919407a044a01400440305010350901c0881c5400d8109820781303600c541070846240e0340c0114065000c0f6568078141c020160840380112043c056907003e0696903905200629002c940c000c41030740c490303520b0340040324410743c1e0361004281c5100c0514100f54105180c00c41f80708200d0380411500e81080594203e41128002074503440101c2c1d46d9a00e00c0c0c100c510610740240100d1002482d132203c014030708800f1101071740c0d100321b04410032440f90300c40c100301d540808040ea9039206c00c00303066003001040c0d107000d8001c8041d8826002400040d42310341c0102c03103a1100c41600003419881e140358400c049044d0701c89580c400c0a0800110000d80b145000b0350b00119003188260041181405042d8a0820349a5015100117100b428613a1514183d00b18103068490030015144181c441c2e0390240e903115141e006240c3d0190821510200110000c0744280e481e0750f0401201040901c008140c2411740d141341c000100503001000d42c101415101c412050240080713140c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 933521987 1250 933520737 933520781
    0x10f08040b070c02031e0c0a120803280c0906110a0b012c0a0615050309120307020109020a080106030203070609080a0b0c120a141317090406210204 65
    0x94140900e001080e001c10f203c00c02221400b035440c10444540d03da2a802d00300448a0703c40d8030700300c1c0e45030403258000c4c1c401e9003800400304924007150720f0010200e610400f0b2600f95104d15482c0c4410416444007103d000080104002c10f800150240841e42500c0340c0b15080440d040101c010100103448246200d664803c0540d04c000641c5400c0c55411103002d04a4500000303080b280c0f50360801050b0703150407a100d5207a824008190203a41c01030f001c0300c4c040002e01d082207441000075600c90104891400e81500702084003110543c00e88000d5a2258451000051400291340021490a030b285c002428a03992008180114102046a000905514280b205940e0f15068015580301c01c800700041c40700714441c002c5032038841030100b5944240c158916500451411078071880050000c40890462542d144000c10029032042802910090f08100400c580540c800b40c00b2066512081100d600a035480c1300018040588099410b0000605c02d0352803c0030340d9030700401c02510034004114248540c0d20784 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 933523237 1250 933521987 933521993
    0x13170f0301090b0102030f030c12100501020d0309140304060c062016081c0f0609110403030822080d06080d0503062206081f05040b0112050f1209010f0804 68
    0x81a00e0440d0345080000c00c000e14840300407425030060140ca0846460044140f050020341000509014104c41ea04a202c3d43e6075215907610440040c40f1b00350158018441d010b08851103508542d0b900f500911800444559507408649164415848040090746000c905820407011340140d40103200440041c040c1001882100c1c2c20394450700920300e6a5090a140e02002c2042142c19078043c0301c45401101c0c1460910705600c40600f8899110303126441c588a0049200800c074446c410f10b211724101135030304217811035400385e4a53300040c010072201c0b0001600c1c1040c0381c078861044c6080601c60500b0540fa50128425507095170100d801040c819001003c82d6a000b40c2d000099076400001180c05085046845d00e8000c0c140010326210320040b4184000401e080c040051480000150000c20038280f221003c25007040f5041500c00030010603c07100100484800d4000084100f0f00032001d503038494115a20307180c130b00300001c13186198110001c03c48680c5580c1110500026407442d0502c071180d860559 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 933524487 1250 933523237 933523267
    0xd0b090f041112070b04090e0d08040c170316030905011806140d0902100809070b07020d0303050603030f0703020604110d030e060307050c01060b09040509030720181317 74
    0x8005103001d103c1010314804118010070450008000d601d0040d95165243d035005000741070074403544130310342c800c0f11440e032046d910429500f0f00c526048810002c04030300303000174000780c6440007051555900c014040c5840c050820190844564429101c0e0401545010009088040344901c00f03c5113644d462070810045030001c0c0701405410100a0a90741c1d50100c515040c028103204c2e0010350040700840920f000f00b0340110819002d1010b24040301c08655031211002428418410300a4024158031005e02c0024005c2d080f290304440000c007030364244a912040c20240f500148004d0b00180e0207401403005110140c2e800111400d0107807880c940e90881500c02400c084079454016004501c0040007481d424031810035240c01c880c08070024403131703141c2e1240d9020446d0062031b6402d20032450040458542c1c0b20000c00c03200880e501620449090701780c064210b15549a5402c241c3c4c201d21810450000000e140841078400e8640c14100034095469050480d02401d6108440c10b000c0000c2050101300f450030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 933525737 1250 933524487 933524513
    0x3140304060806012a03200a02011205070207230a090e21090a09050a05060307030b0411150c0102180a1202060705010f0c11010b030313030303020306030a02060d0b090f04 75
    0xc2c01c010142017600924506540c0c0040010380c50100050300e4203080507400841b001041064046a0225985042e00c458403032518140090104222402005041c5607036082140c1c42207503401910b14140c3e0300c4940711018045500c591100c0a004c4080700f00301d180201c91140900745c1c0202c100108801034009503541d00350741000041e4000028104e055007400c10302150604040500722000156560340440080c000a5031440240e42c20400042c9803801d00152240449030407590f9201c40e0346a648851081c80480344a80c0c6d0030000090100c040054800c005140c40d60030b8100050382c481c42d4500007440454130410765885a8400b01007000081c030180d022444441e0102c42d401d580d4909494620b0041403c0848102042e0501c0b81c207800040d0070402e003c20500500303000340140c02603881015100d00c20442d064507400400ea43c28030100c0e11a038061680011301801b140c0c2504616000110690000c5404e401e500351202c21980907800c0503148641c002420070341700a810b00701542c0b015203103008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 933526987 1250 933525737 933525739
    0x12320f010203280b040213030302011a06070b0712060e06090f010b040510110f0c0a12050303070e0f030703060f14010308070b1306240b1201050f040603081303140304060806 76
    0x1451404a21101958019044e0503002401150340f42c3c44c9030705800b03c42095100607005035103040791411315a074040103510000b2800409880c908030003640d400c0030106001d45550200f240401d0100c0c8558024803c40c0054061415540c40e54038041c001c000c1c0e0141c0040141508410714001000003c00580a46064075011950074408007008441120f40d400051300c10156403041005044140a02103901500a035081d11010403003600c418140c48003804c02d07100101554000c02c0001d112034800c00e141d0000010080c8010612410400000e00d001e109801c00c0d15003d80d0745006030180031031032081900100036803007070418541c5140c440101e54040d0402c007601d820800c2c5d00003400302c982c50300341c107030781300d038008020407080d0301c145c0e011010a41c0b908004000030011080100da81404c403015142c0000b01d2803541c0c0140ea003030106001000b07000050541c0c100d40c90340e2020000911182c040c0501416400c01c4e090810714606140d154240c14800804807508208001c0c06284d91140b9000d80c4800c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 933528237 1250 933526987 933527041
    0x1602071703090603190b0108090c0103270b010503010c0903111306080d05030708060109080c150c010c020c03100506010f0c26180102010e0712320f010203 68
    0x40d00804841c00c51044035200740d4000400010418500c402c848018000c20641070100300c03100d20400151102c0760161681030042c0d00c03018400c0030541c4290011441c00307a111080d03010445040341124000550100c0c100e0314040080010700c21810f091240107034200c05c03890047e00340c5180d602c03000b02f10000103d019015501d925010314285456400c4800100b0b240380c00c030b030031926a441004055401c240c6007031340003c0743d040124400b07601c10b0f0358040644070100058541011900100003220704601060b4034400018010750031140c90030301c5115410015074014000d0113118230201400d202119083e54051850401442443e0341d000c01140c2c0301a04900f465554139615090001681c07002c980c3c602c2c404009020089007071101da801411005070081ca2020903e0081c000584c241c480c81c0251b144503510085007009003640a0007081070180c01440140031080500d48200c00040743d15a420103800070028480c0000002046100095510031000b1825410a840d10140b80c10043c144003611030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 933529487 1250 933528237 933528269
    0x100c0602030c190903051b090601050d0b04021614010606170901060306060b071406010806131b0807031401020306031e01140f0108010b01050c060604091703090114160207 75
    0xb440311001c4458400001520031200743c00240002e20783d40503400121840d001d0000c02103a5002e80113140040403070010528440799440c4401141d41e038000700103011200380c4400c0c940030542c54620040100c2c0340d0841050100382a82d00b0107031007140c40440424443c0e89418030400a00f588440002c1a05003021b02c140c200b070f00e44074140b601612040e04003a00191910304001103902d1800300030503143c0c1c49241c010030710340103000ea59a1101400d120f07129580e00f12a00080e2000b040381c1d50108e030746204140c95410070400980b2003581818a8104000b1a88508020700038001c080c003061740c10201080080d132551401c1c4002c02d0300d95191100300d00c1101e0f1100345401481a080d0080701c00030100e0032500d510b924100d00c501caa024401e10492029500c4c14010a0b1954801c80441e8500e0307010000038845610742070705002c01040d000106650256880310201807030000d13480118012070008001141e8103418a03090010341c031001c0d01140daa80175030102080100e03001326200c07040700d044600f641896 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 933530737 1250 933529487 933529501
    0x6280e091317070c060801090e0f060103030e18010f0302030f031806032d100503160e15060a050306030618100f02040503070621020306062502040c030b040b100c060203 74
    0x260143e01c0c0000c200c413041d040f02085007588010464100d4100f06004e0100044004003240c031139440c1c200f070580680280340140046801211650113295000d0306820366182e0042452040210a130400340103003208000c1082985001c109103200c07140084051480c1507240740c140340211081c0c0301c405014103c003100080300c006455040c400b0010b405032550841c40d1001a040794001002c480d444061085040042454100080e00319410958201c0500c0294240005000d200174001e04a60340704074019244c001c1c80c1c84800280800e000d0945600e40c49060080130941444001001c2c0062000e5020641010035000150041703400400c0000103005501c582c07444c0040c1c45140c000607018800c04400050250f80305e18501400001c50079801c4007000640060303000d0744016520340d03900c49030511003030185528440c07041040009e4040c09030104121b41c3e0108003034601703c50381e100c0401c0e074a40c04400c0074100750050b0020b0b020212404104401100030140440301c0c02e0b00040c00b1103901100003141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 933531987 1250 933530737 933530783
    0x51306030902031509160603050903040918080c0a031b0b04020409320f42041a090708121809090f070b0306100e06280e0913 55
    0x9801c2c4c3c40f004280b140d10782900919911289800d110586050690000510a20138450360b80919501c50240d45070030b03c0c00c10010b001d803c40120311b00081c88200313040c0000410850061213a0381c50074014000f101c0030750a02030000035500d031200c800401c1c0c0d24914000100d1070710209a00542c1154005201807423400e112143c01d0141e0300d44c44450b0a06030341c6550f89031000c40079034080c00c00c01d03007100d85405079078050644a0b221615844444400c510760340c20b103100c0c041000314414982c1440c0d20341c40c45c20b58040d803850b0300050b50151981b02c050541504425260040d0f150b1142522000b03028051070141d02980d03a841c191036100c9803010101e40c094000c10005021414190001e040c8945803c1034641140c0b2111140138085c00c6104924001560a03c02020342c0d2098200800004003015008429699003640071400c0754420000c000980445640d42c6202e0041440d40454a0310704603040030180501c28141d11071031050b4844810408800b9172400c1900f1280d0740302001c0012001070b00c644140d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 933533237 1250 933531987 933532003
    0x6050307150c020901321f0c1e021c1101120f050c09092202060d0b031b10092403060b0a0807021c0203030403030b0102030d1505030d05130603090203 66
    0x907105110000008200c1c1c482904185c4c4d40c46d480c143c000c0848044a5200801c0e24072400280e000784032503050340448011444011003000140c00d2101c456a800c0d075407001d50003105c0c03d03440c450302e01d0035252000350b041c42c001180040918981a144907551500e0301d4541c07000060540b4104640008205003034030094000303611120085070244110f0505452862842e0003001d2568010707040100042ca83d0402c010328100c0e00c03c80030080036122500c0e40c0907c6010362001421004158642500c0d03400c80d20200300c41a800400c1c0e4000c0403800e09003008011072a0454080802003240e104014054158988034052450540008580c40b10b0140c59080c0d01410f419031002903031040105a0880e00c9070002405c610449560382905c40c207220a0780da40ca5407a00351190440140d005100040011340070303a0001d000c140d03050040300c0c1010000300c82c5100340c036504921080c10440034602000282410440041c01d6641410428100380b0704c80404207280c1468070070102015211980310003592400d124041c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 933534487 1250 933533237 933533239
    0x31002040305010504061b050307050705032b05070203090a090207060f0501061d0d0b0402120a080a030e07140303190c06060f03150b0108240a1e060306050307150c02 73
    0x9900c407a624280207001300001c6a007070700d8031401e2241d611003031a1b1012001011903455160b9505540302e198080b030f181e80080c0000c561a200400c03407252a03003c00001c2c0d0b0340300c2ea400010104501d06581018054450290a000c01c0d5801888210030307940d100111102a40c0102000688a804a0410101402c800400642c1a924050000c00e84d164000c03442e0041d240741c0e02c2d444050b90a0348060102c0c400c500c013005402101d4600c041001458a042c614214130b0548040310130b910056116400740c2e9005a0800001c643c2d00e54050005c40c9040c8007000c018151079036025a02080e03203021039124403030100c155100d88050905034038a82d02912400d18181c0e00721408000c4503403202c0c001086c03c00e15010a80d15010858440d090920311405030716241380040c0e50304aa10b88a900c801948205001ca0040300e441100c0c0c2c5031201ca445281c4600010301031075860080c03000d00c0d41e400303030120041d580081c1c0405040000500c9151000511340d01102d8003410180c440f6401c0207800c40b00a40e140c2002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 933535737 1250 933534487 933534491
    0x6020307080105011d09040b13060e0c0f12060a02070302070f030f1523060a030611041410050406180b070b0f0112020a0504091a10031b060e0f0310 65
    0x444140c541c461080307416501c0a80340c50b6036103241403031031122001c200701d402e6900c1400c400001e070010700022032140d082800b17901040e01d04680ca589180c00d90340e1303144241d00e15a02040b4a01480c1ca0540d02d500c00401096452482c1141119030b01c0d80c40c0d08004220300b000c590006000c100709072080110100400b0101c86101d0159140d20700b20500c66a4070704195081a82c5e41042c03161075600344a84031070103d42d00f461201310300c4090621101d030f880007440300798400c0101c0d4001000c5001c030f010358890030581d0540240da660800d0f20301c40710329003554403040c090089002820b00c1150481c2c112410342c1d0060074103021401c4600b94409500345103402c107106134000413035070104000003d90154003c403100110342070f0300d81e201c11861208a60043d00a903005031505010405401c00e58400d0150314081d181c1140c255801c00b040e0070002500f035450280c10401901c041041c40416040745c4070702405c54505ca00c405141000041204601c100d00505c2044100100102c41d60f007008506051110441c003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 933536987 1250 933535737 933535741
    0x4020d0c050d03050d15080d2a14070603020a020a20120a030e01080603070b030a0612050604030e0904030e0118090515040b04060605041511010f020d0c030e06070c050703060203 78
    0xf00030602e070480010104210704008403105048035211000c020745001d4001070440c68a13001080340e25144039003001017000c42240a10a840c3d90190504841ea070280350441e04401d00386000740d04d0030b003459001104051040c40703442e582c242e02190f200807440d0814000741c02c59400040100260a00001442e803080c9510903150401402103850480c1e03a020307440c1c6e4100310141000544510200b1038041e075040d0804001030010f015035070003440d00700b070710928001091915180007a00c0c000e441203040e20f90351701c62001c0000301b50b400482d101c502c1070181c509280340d04060340c01814402d072042d045414000c600d040300c0c843d0316a200e20100184180f078014025070900c40c12940102c040050454011424401d1b02903450519008420481da000da03240c0d846e2a1400406042112520801c2d504010b035154041000c5602401005001d8022030700041e40c800c00d440442c4210b403d0403414000b45401c080c03071a1200314010030310035403080150504110040722840c1290814203180c1009109a1001c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 933538237 1250 933536987 933536993
    0x3010f0f0506151b0705101806170a0b1f110d020c09150303070c0303120c03140105090a1104090e240a0f06270510080604020d0c050d 59
    0x3110804440e651000c01c9161904424848400341c42c0d4020091014100406030381c030b010b0680e290030401699800d0740c0c40d0f00e8403000010394078480308000000180c2c290100e000040860f1040000800c1c086c10400d0040d10012a0954008002013603000c02a540e03284025040d00c0d1002500c0c070042034240100d85403003d041001e8a8110140110b90003441541c0209120500000f00310000d271400401c1d030300541e82c4a20341d92a0000d19502941d405000a1221100241c04d80103084065442512500b41c9912103050b400112100c1b01142410142000610b10403410600c2c03280e8117499003914030320035aa50f0440c202001d0301d410301d034106c21030600150004a8100b50b41c402000d080e112015603260041d8400c500052001c107103110940c18000b840491104009540009125140100d01240165407941c200d405807040c0c02e0361287c00c543c01d00300b11400e507895204465200d05101042c249050030444030f650386000042009000e0700b200d403030003001d03c10551445802001c00400954110040d40707 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 933539487 1250 933538237 933538241
    0xb070206091b011e120506041406090a11210f0c07060c1b0501150803030f1324050a0c051801050711040617010c08070f0c06150f050a0506070506010e090c03010f 71
    0x2d81031391491624007c0748248ca403d00621010040c3e000c01e01e4a20f03183d4204015851304094071b0098035540e80c05920b0304500d8034030003a2501070b048010080304084001492100010000d055200b12500d02c4100319213640407009494040344c0003e000074010400510960b480c4021442c5800c13804991044c8100304401500015803e030340074070403641080c2e40c68081e02d070341e40426206214402c0301040060708020f8510700c0b0b640a42c1c00342441c0304068181c03a5103012614102203070088619121010005842c1c51809801088034003460840d00d010840055000c1c7e88911152680c10072034000b8440c414000c10764042d41320f10750024803c04c812a0303100760b400c1c0744001c41c600107900d0354205008003041038010080c051169500e170f21807401c0f20b45010421950310742d080b002199100d984075450440e901d0104001c03030181c42842c19000b40030782040208000c010050780040d128040030000340d400101d02054041c110340002c0d0050710643c951070002030070548903074403032901586040700c0e40700048429 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933540737 1250 933539487 933539507
    0x3090603060b121b0408011e150e09010f0903170f04210905040e0a0b01061701030b04021804291e100306150e0a0507080610090f030c030b070206091b011e 68
    0x2c00c0423848050744a01100e0654012500700b0441c4151a0b50800081c207440022560085090000149044182e0046812120901801d900103a09546111208501c00040d16040b010401000b032013442c050795440c0c60714a0340486a011061901c020b10101750045000e0800f402e0010014059410411074481da0354554034010380e981056580006006401503401c01e04610080c9150000f907800d503250301100c8078000d4812604480580c2d07a000503904086c0b0114000e5124003850000020000018485001824042c51440e1407410600814410780f408812185040d10781d41c000550f2040c0b0711100280f41603101812050a04891b1980d210a400b5010207550040c1c03056081c588403102c242044900c01c48010011502c054082150703403404070004107281a45240103071102da04c41444140150441c0e1045500b003944c2241072041000e00340c1940d80c0030446100900c070510f445102c0aa1300d4000d900d05640001720300108088a9208000b44940c10000000ea00c50031080320380010100410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933541987 1250 933540737 933540761
    0xc03030906010b0403050c0603041a040f03080606090603130302120c060739110d03020c120609120f04090501060c02040606111002221203090603060b121b040801 71
    0x4400c00802c1500f0340f036084c0d40640750810000c0103082140c005002d00380c2e001400c203a4021140c1c0c0702d9001302000e15652644154030500c2e004901030000c0c54098081c54001d01094807034002480040075035205c01003601c2d0301032024000342c14008450f090503400c0000d2000008008100020580101000081c403540034010a689042c0c041c6010507508201d0004c020b040410f8001c2400d003088000c014a06252040c0d003e09011150420148009605004075460440142e0400d5a0940c094980b205000032003070312820141442d40741002903551945c43c0f070381c801019607101240f6102480c0e2020199400b5005030782041069584032500034284000a15040b0700c03c81c00d12074003094583c49612101c0d070901040004080c4500c5040c034100107504040c820b420298507031400d48122503040708117407000b0080104181d03804212401c0007000d01c00d1a803c503106060500c4001c021444a00301110b008400348000e140c40c40e00e030320740c9581022500306010700c44c0c1e42000c10f000c203026038107502050303041031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933543237 1250 933541987 933541993
    0x91302191107060815030c03030a0f0e09060a060c03050f07030801050f190621060603060512010506030d080924010807060e2803060c180902090d02190b0c030309 71
    0x401409554503001805207100107a03400c3c001c98148060001c2103500d082008051301e87c5680740d00d0100b403464214140780030016400d8038503105002d8205504582090003a1814007040c5042004154589040e1040c2d02c10041c0306000c850074035100d003040e10758100e640ba40c403a82d15509418024101e03482030048501c1349440d4000d101080c909882804c840350f010700300d454841c601d481403d40f040e41c0010400c86040e14400030340030080d8054410040030340705d1600d000a0050500c1c0900840500c12079540e030385a8502014041169000103907568081164503203079150790380c1e6403142c9040c8243c55082504c20003503440c074009094924404681604c0380c2d1000c4562059840070125641d94042014540024906401e113403d03031040b80c044403060100c0c1c41000d00301a80c903990f02040714080b0603404002202c004944a501000340d8540c402806068015410882100c000aa081c034849000a10692a4030400d00715108a010b58200a00304801e209480345040c41d0b81949a90084031035042c280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933544487 1250 933543237 933543257
    0x60411030a050705040b06040b1c1107260912071a0a1b0203011128031e0b13140402030d0c0b0c2a1b0a1a09130219 51
    0xc00c000820304035040d0018003c0281515007001d120041c0141c044264100c1d20801002c1501d040c4000240b0740d1903010001d03102d0100028096404030b41c10b00c14400c0664008000020100346e6101c1444d0900906010035076031003c0b1a81c0020080c49940c2489030010401e40a048001c40c0105841e0101d6a035245c0302d0303030100d03c20b07404281c1c11f208089030b0002090101c0b0305e16007210184005014580c6c4081c0c000503502641c40346401090300700c80c60009000030321402100f440e22000c2e0040382112030508040c004883c56100741003000740015100d03c0c0455880f43c0d5a94250b50300c100300d9a1424061104100e406c0308a00108202d4a080310180e010740714003d1200c04880c0b1070b4081c0a107258000302c1e50a0551502c119800480d40152003141445040c6601005144034800340c54201e12a50b07001003d000d541f80c0c0001c49040704480b0103d108403d000d00070003400040d10320b0945c0f0b01040c801200c0e901c0028500040780000344040f80001148003044c020550010041c400004898507110000701e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933545737 1250 933544487 933544489
    0xc19030207030807090518060f0405100f0806040308060904031806032003010302060708030a02040503010612020907030e030d0c0504181e0c14181201020d06050303040b090f1908060411 81
    0x1ca45c0030321500e5004504290a002102502c8403d56081301d0700070110030001950600182c2600e0b01510703400c5424580c4601000802c0c3c08008941c001d02240000d403840b460586c8003d0442c2d50024015070151900c0bc001400701842400344091005101740a21703851074444030300800810320000340240d00035201207041070300c3d9130035010b0324100c0b540101014580b440c9590f8102103600f015221602280d001c0c000414682d50a01801d0080d229544c2c0d8444c2440560040000c00000540820149494040001500c4101004030f4812907082034000c105092813800444680c070941d4060035044d004070030840811030050f0000030135184001581c0039a20b070352980507030440e410a140140415a64180195214400b201400415845a20b4072002c0c5011101280540e0325038a860041c50b5400560000400b25601c03c07107014040540c0214107103410615440e180384152070456100303030800800c0000541d50404080a9500103d10711080c0030780d40c203001503858000b6076040f926a24005040c50307071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933546987 1250 933545737 933545747
    0xb0a1a0c120d0f020c030f1b1b010305060906011d18011e0614030621061501020708150a050a022802010c052a120703090317120f0c19030207030807 65
    0x90030985000d18684885110349111faa0712120003104094040d52901001c04024040c242402400c04e0b102a140c00c00782c8001400c89000400c607074070902d040024006c260740c0c040b103004880c111490700c406000350040001108001d0004d50480401d449000110301201d000300080c29040103049940700060b298201500d0402d81d106100014000500005230303a8501a409070320710f00340e1700b079031960038070500760205003080c2c4c0403038100318251131003514040503590400500005204840c040d00c0700a0a015140001c0100900103140c100d0715003004c50081351a9504a030b40000c02c01c240781c950152079070710114030301c40046103000c0035500e028801c28030580a041294051481d01c045c05041c101e000700959000c00001001c138603140301da08440302c00404458010003180e070103600c581d9a2280742d031905040d48841044440080130090160b003c2a030307001c4101a400141511028181e40c8d1010380050300360155141010001140c5010081015099802403d1850080c2d4074129143d4032500140d071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933548237 1250 933546987 933546997
    0x60a03030f08060a120501090c050307080d030b0f03060f192705010e060106210e15090a0f030f0305181c03060b040b09130b0a1a0c120d0f02 62
    0x8003088105a141d0089840307802d42e5580003074010304114107503481c1c0030f5148006008520448050f9919401c003424007500c030141e4002080118004c150341030409540a444d46032200b983e00a05885100c01c0005598140c0c4d80e110240c8050202c8981d80b41604a144049200740c0700440031302214030009107000c080c1d0080c0300300700c98040c00380112052009030081c80034480030416a031555a44c400d00c19412030610589008142c0781c2d540f4a07100c0c000000340351a0110144995601e2450714085400109002c0b0b4894040a40501030310410f907a40b0341800d09101900e00010309810700705150b4020160050080f480f10344195400b0055a601e2004079042c1041c0810b030714445a00c00150142e044603140305800d0400a2440c0200c0d509039a4400b628182e002504208032418012804000c40e09128400425805215000384441031510300890300100450082090b1280e0403000541611101412554462030b0001150380783c000950f41030030300c0d1700078000d12a0f846040c98881c1401c8003a45c001c0c1c82e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933549487 1250 933548237 933548243
    0x1c17030a091e1a04060905100e0c09061c1505090303040c060e09041515080705190e06090601030b0d0507030506010f18020c0a1a040213050112020112020d020d14060a03 74
    0x6030032200010548000301c100600c1250350f0380d2503400420015800340b06002065080800c04150324271144000e60401188002d218040c4030300c4010405c241d078445981d031400b16000d803001c071903e0415052000390a18801c0c60300c209582040280301103090000001c0d841140158100e4118a858490485e6a03c0c0303110405903100c0707840ca0201c0c000c13403c0c2610000451800010005200490114a00340024564003c0000350096a801c0025013821103003140c0c14550030890200007070600030f00c0d0385441c01c0548200d0141a2010009100c2c1c2d00960220740c0f0072600070145d0820740b085240c01642d424860108503103a000e400000941711020005680031340c1c0358903100c0689214115142c400035008607008074403d200e0406400041907101900c135211030340b2261507000768038081c01400074207074501924400e8646040c004101031003040800240e6540d091901814801e000f842d4000640602c0c4c0c41420b90620020f107483e41c8928075400a100c03442a4100c000440da00c900421403c59881d12000e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933550737 1250 933549487 933549503
    0x50301240203270d050705100f0203031819150b1e191d09010c0c0809040c0c0b1807090e0304030b0c070609140f07051c17030a091e 58
    0x8000c9404042c2d03c062007540000c440222244a03003c000749504025500550301600301e8002400340e4140907414071030506050600020110400c00000d5580c07200500c80700c29040816140701c0700f00307410f014001c200452443c402d0071070704481c00c5c500244500491542201072810f200f6050905000c00f01d500744200c4604101d045415010502158112903180c1507205080b00780040307400c0c0e220b403180003031a5003a55000403261820070010340c2190707948140c01040c41510740800b000908200106c4049110644020a441240c200151110895a10000d11010340c0d041000171a40440485140301c00c054000c86070071542d542d0030881107e542d0740001b1900e401c10001413010814004009030804102001e03a031800d20300d51600811101104000c9480e07605820341c22910842c1040340c9001c8a040c0f00107400c04a103800002404d10a807440303c0d61202850414042c107100007030041802d0381e03403018400c6660b4946603074400003e0a00303c2040b1850f910400d500d080c0718008100c007a00b055440740c61 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933551987 1250 933550737 933550747
    0xa06150212040b0c0118060509061509040314190f120b0603041b0b0f030f2d0a1509020307030c0503010e0403080421170c070302060a0207110a06050301240203 70
    0x3003070041d07a102d1030030380310150340fa400004011b00b11a800c101d1400d0084000199a00b0704a03082c1c1c0c02c00704007504280c1c2d204010852104079540d07034013a40da045685420100c03820170081605140c98042c0114281003500a04880031021360024000407095240342e80d0811000040070015007184c80780e41c2e2050700243c092001800003078220500e4058502200030b82c0c0941a40c8a01e40500ad5102e0000000801004000d0021035950030703c419421450590741d000d014103c06440700300344151060424101d658200200f43d6072089035120018580c6403a10354078095840701401b1000e544240d13900000071b454070416842807480345003079a040e40c841000c4c82c0c3c0c1e00d885030340b07044601d050082c0003031320803480c2c40301d8899a403645214400d4080d2007640303503c80c0c1e1004e00390011603820b00c01402071085103020400b8000103940402c245a201c0e6038544010f0711022a42869140c9524002c00070f82c000d9903034000420041d8002000e14100c42a12450044000030791208403048036440540c080503078000c1c81307 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933553237 1250 933551987 933551999
    0x1090207020d0b0718050d020f01080a2012010506030903160809040612050c010203090a051507050d17060307031a060f0301020f04030b0f090a080703050408060a0615021204 76
    0xc201240c0020041484000103441d1440000e106941200100326001307030b0003000040c0c910701c40f030040c00201d401c0d001c03031500c40c1c0204600e43c41509909040099841c001610085542d100d0820b0000c00c0481c816030400103a040403d9602120b821019548003000000c7c80d03242c1041224440d84c0304801443c1040440c0b2032152021280102c100c0f2041c1051008000a0304e461003840024441903210501d200f010b818028149130804d01a0350442d00f00b080711a10907102d09910004440007035892030310400307618281c0c0c0781c503018112000f0701a000d00300c0b00ca40d51303035808030088012031104410f0502c80d807500703000c05076100751610009102d920102d00716444111201b01c0710b540400050020f1490740f600100180c03c90b8080507018102001c0804c09200b4409108807442c0c0c0a020700e000406582849082181d0300c1e6507040d0010207002d000240e1104061045068500902815080303840364203041907800007410141c00381c02001e001c0c0190b54000d052000824400c080200b00310285802c4c1011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933554487 1250 933553237 933553241
    0x280f0c0e130201200322080a120f0309032102160f02010906080f070e06070203011b09051507141006091b031b030e0a0b04050114091c03050703060509130c0812030109 73
    0x70a00b042d8882c00031b100052569828800200702e0b600c10407800c2c182084041c00035140316010041d080c20186080745130030020341c100d030501c0a607040b00c1d6400e15001c00c250840002900c02d40441c2400c1501d00301c2020104030152001c100c0e0079100762105042c850b100c2400303c5108c1c01c1100c40d00380a255101c0842d07902c0c0c2c028058101c407000c0140006141229a4010a09644c0d106050340400c1c0000c1d4881003845e035014000902500048070140e0408041040720b501d40d00a20380003402c82c9480498202c58004104812034804440c1c0005100c1c0c00c3e80c9012a01c000d008460740c400803103046200c0031900610900c0f0300d130301e180c100c0418006850010030b0114010910b454010090303120300542c040104140480592181d4800e070004600307035030031400d014008580600103a0079079212012103800000c21381940340010016260006050380c50400441c040e003010352040c0e030400194014030160341000c0112081050180c030b401c5440a0b41c4005003695800031803607450300400c061005005650643d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933555737 1250 933554487 933554527
    0x403050307080402010c0f0b0f060d081210033c03172e0f090c0c0609020d0206030106020f060c03060a060c020312030c0408280f0c0e1302012003 64
    0x602d89440c1b80d404954420354a1595441c0559611080c5010407034803110381d40d0165400300c03081d5011a0600ca81c0da8030b1001034000d52a015a450340381c1070003c0d50030380401c121a0000c54124082c0900d8540000c4c1c0035203180c00c0706c48581000c0c011441052500841c01580160f1136030f2560300c000d11800c250710f90300e440c518040d0180303030b8804d84000b900c0104556641c030320034500d4172030389800812440e0080550306540b95030700c80c0d40140d003090002d20580d0740000d050541a50024008210f0602d10320004070801f66000001b90302c0700003c030000c9040c99000a804480403c0801140c000d074841d21800c401902007102c0941d40490345080500c0018403552080c02280d03c003030f007100c000a44d01d81c080081500119055144920042020099990100044820545400c8151081c0144101d4580f6225040000a445400003000d44010001a40c01d400000c0c40c9040c41c89101c0d0a041040e03140e202c040360300c1a400548005038240506440400c0807810740c070040000e41c940b221102c0c41c00c100c0612 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933556987 1250 933555737 933555739
    0x9110415030302010b0103141920131706010e09010e0a0b0a29040b0103020903010603140d0302130e0402011206090c261b1b0321070c140a1b0504140403050307080402 73
    0x42cad0380340782404e00348540303c00f039000302c2065003580703405070850203400c441002d41c000340b500e03204c56030f1203204654003080040c10358805a45404071541c030201702070301410306403501c00700c28441d400e0042e060003280e8190a00032031400070140001041c5400c4518440d8160300d20240d1500300300da01c02c196140030790011010700018100541480354100000382102d22a500036680010303600c20700310a100040c880d0074000411814110f0800e51300ca05920184500350140701e500c902080089010b5a024401100703407020405802e0203040d031144198009000100c40c0d44010910f41c500b1154200707518100b0080d80032004c080148240e650781806800b2101091500c8440101000740c0144554054070964044412130015270395000f03411505020304501c00e0002003221007040a006440e035000c81040350242e0440151038442002c1101c0070708118845130000c0849600340c5806d1f01e0191804210801c0f41c4080b04e003000107542e101881003091204690041c000b031030030800100d134540500106030704140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933558237 1250 933556987 933556991
    0x60a180801051b161205040305061f08030c1207060204030219031104020c06160302250c0e010e0106030f020405060408030304060f11090409110415030302010b01031419 74
    0x40084111124515030800e0450365190000c200c0b92010099501c002d446102c0304a03440d06a040701444110240a00002c0181002e03500503100c0502c00c800b55005560444191545400c00c104502162900382422164950700a2000540c6007008001d07500b54001007030142641504030480e030200c96020314021524591b0900003c009a150419828030403018035202040450441c1000b80588015800360f500c1540100000c4d6114940464001e400080050350130311071403000c00e0309070b010380100046581150b6942c03141101d2080c0854030304d0321950041c3d85c8507010948880b5501d0f070302d41c070074012521a82a00401048428801c3c1c0c80740c14800582940181480e4480300000d04075405980a080198408000d00003400504d220b44465000c541100700803240000703440300316601603400103501c82c0344d8560750f40c4240300420202e4902008020820410340380c02e48034000c081100c40c0816401986000c404140039402407080c041d524040c80000e4003a0307500c8612a802500c10b075041e041d0714607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933559487 1250 933558237 933558257
    0x80a020609160b1e2a010501051c020d020f03100b091006140715050406020d150f05040c17040308010f090510050d020103142d0417071e050601091811060a 68
    0x4070b0360200500940390124106408440542c0402c0d003510810327009107100b41d04042a1011209a0042e90318015a043e00e510340c0c0488c007400052254643e009130287c0500459000450810301a0311008540b042154003049688905500203509191800390401041c02810140c107804140c901910b40ea40c4600c0c000c2d4241084100700c84152042a101280c049401144508840c502800341207400f03e0415003d0090a01c3c2000322000d14405200341405a9075550824000500c00c0181070350b000445035044459041c20b06c0c0003040c1400c244501190090000c1c0701141c003e22a0051901400c1042c19404c8414104001c01c05c1e0b105884030200c3c140340d23464505091904002e41200d106180700a07400c445c2e520452400358003403112000b18130300d000c80d210801000500b020383d034000400d6030182141d26080f01c0e01e080454030020b5942584c40321071280c000400c004001510b94142c0300c4580061115442c443c1060001a01d0b076a0b00400704500c0c43c090707007060b0a1000c00b030410040c040c505600ca41c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933560737 1250 933559487 933559507
    0xa2003070503030a0c0c1205130b04150315060c03050f040806090d020c0114070f0206040e0112050c0103050601120903140a090510050a09030f0f080a020609160b1e 72
    0x1548110340840d1140c10200802500780607501c590780300041a4141082c9040040c5c0e20a040e0074985200c8805120000c15080341420461500c440034018131004203030f40381d8a4084400c1e14002540145002138240790940d0903c541070210304c412204552110828160141c0d016500ba420040104a891100744000152403a08001650241c66060050564075074414802401c1000001e42a414444054541c001810500040b1050306801c96009003148940d440010124444caa00604603680c1c100d0001c00d5074016441411025849401150b0b50151400010f5003034a201301d8289010440c002131200540e1001e41140183d24440d00d44a000c0c00c80d11000d90000d90405a40f482c001882032005100d6814842c4020b44411204c1c105030f8105889070000034420a12400b00800399030118651204200c0d4800c28603842c55480100b00391580d1a0744070082d0b0b112001c0f50300e1a254401e00d60044e480c101503216981c2552446000c0502d80300446203240042e2010001003c00424204282161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933561987 1250 933560737 933560743
    0xd060221040605090f030c0309010c0212030703050a0327060504030c0516050a081b060c01090f140c0109230f03070905180601080d0c030c02041508011409030a20 71
    0x401c5120b020300003000e04109004515081901300346040c10350082050504030280081901c10b95002440c0c2221310032a11700c00310700c461000003800e103118440810520700b056000b2018084000e490798040089031414141c410520348514448000480708405403004103075241c01240d0711034001d00f44405200d1699445034034001d84000101c111142c0c1d45424002407401400c1c0303100900d002002002c001d140e400c0740d0411008c1092815114480014440384000f000390041c0003070b90b821032031030003240455040048095405011940313003801144039441c0c16602074502c11064401c802000d0925850540d41c4031078106042d009154450403184d802c0d18907a90404c100c10243c00d0b110000f0034941016070780b681131103640f803100d036050340c10100061000d8003000a100e83d043d40345280c503ca00003d9418151000c00b6a000b02a4100d81010159650f00721103088040480320311000800040300281319010180b4400c1c1e9404006400030007038115510701c03650308806155030b00030722182100c281948080c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933563237 1250 933561987 933561991
    0x41404050c2a0c18071803060c020601050f04020a02061f0e090d020c0117040204020315090901140702072322091e12080c0c010c05090a05010e0d060221 67
    0x2848190a02c504080340c2801803c00d00748058480c1d040443c82021910f45206000b49648104003403251000358100d01c5094050085820240800c0880d0800c07400940707900d0240113032801070340d1083c035030b00460a061084645007281a0301410b12a00c0c5d0110700800210f540302400040c114001e00414101c100e000042d0080d540da10042c1250001180042e0a14006010b06414400c100c00107011050310700c464280d02030b50480d80140c1d65611081d400020340d0700d2414460704851103070100a85103005610400c0307504175410f21480340d40d4031400102e0b5599454000c4004103140da80790005029102c00060703108a800130b104d22080040b022251404d01000c040890f078058540030a42e0510200c0a0a400540300b248041c0c001c07807540c2d40b100e240c1c4c512508030003010002040d00003140d0429800c15511051200c2009221000302048001c1c815008004164401c80d4a004005130030740c02a4064164108058444204400780d5111107009400580c2c0c2c006052142c02e1591915107204295a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933564487 1250 933563237 933563287
    0xa050111061b3c2b060f06170f0c03010e07031d240c1e070503030408070c060503061c02030c13060f140d030807051e0304150b130c0905040e010e060903041404050c 72
    0x102030105881c500341042c42000e40003524270341c3c100c01032248900c07182d0110b81c1500e403200d05230502078440c860101e000744200812081c0781d040d8047e400303241410101f2100c1c0c4c80768807100c4941502c1c04c0d18070f035030138108016500a00c8840c401c000c42503c858660a01101c0007400d090400d0a01d4480d403070b0b1908507030040701c0440c0d82070700016001d4208401050f681e0f0180c5010300d09141580307400c40c00701d02c46c403150100c0078030100e020980f90703401c551303041283c4400d5580c0a4614031511000c202e01c5005800d50380541c81381042050804103c08e08404d200e440c030b9500080080f030051100d501d041e0ba043c040540f00c4010800100000d070382c01280040301c012284072f9000c0c41552407400d4105035019001c030303400c0600c0450030300c04401c0312940c42c4030001007650950714000a088442401c00e41750881c41d5030000e500701d03041400003e203007881907116808501c010400c8d50303810b0b0381e051030050300e078401c41c06041c09400c0c02800b00726060400c0d9214950200031146001d29184031501c3c13507248011220020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933565737 1250 933564487 933564497
    0x1504030b0109230105030d030e0a02030f1e0c0306060621010b07060e0a0c1a071a010906080f0619290a050111061b3c2b060f06 56
    0x460103600e80f02c4292000e400354844600b49075040400090703d0300041e60500d42003503269100b00032a400e0a1000181042d8010700711108228451103803515126a81100003596070001040c0041041c0480d002032444001030103020b0030341d1481d040080503044000501c0b040c1803650b42c4c80d9103808011a0940c043e0943c2c0040f9070f01c41d000f40ca8450162000340d0b41c901240d0704030301e0138940000c00d83c00c3d045080d1410840031001c006031404c100c1c40507018a02e405401c0d50b118000c0c00700c00e1400402c0e5141620080201402030f183c660f40150b56851420794a85090381c010400248900f07801703e10381e42001c5440901152004c5860300319840740d4845201c1261651001070741c101d180c502070f4202401041c1c01e0924400c80200880a141c1703450004003514541c280c00001c0420145900c07040310308c080160070b441d2410692444c081910525030a1640d421a1081c108540d051242142582d0b101407035103501d4040e105e8421050004000002800f445064651601245004601300c0b40c0019114036620 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933566987 1250 933565737 933565751
    0x160c08072a091104050d021002010b0402071401060b03060d1119030614071b060203040203070f0b04171f090507030605012d05090c0f13030305040303080a06141504030b0109 76
    0x6500c1240c00c000703c0044560801c1004000503210700d282112581e404a030106040c01004009902515030f1405107607000e4800241c400030003907603d8503540609000e1008000709602c84441392050b100a54105070311085101d0000d00251020f4101891011702401d518541185038801240300c001503041212200e40301c1c401070591003403804503594811542d1810310344d41741d00121b50b14183d0b0383e0f802000e0140c40d0000005410342d2420003e801c02040e0024151501c2030380d030007030b03480c10342c0150141154254105407240f042007400039004200704104c41e8030720f0100741c1002592000341100740d4111554010000004003241c02403280a00038041102e03112441146504282c000e5001460311200c6d1514403c424000d5449003003c95078002514200141e0320442c0c5407240c4080e001e000da010040018807403000c010150b120015008592203500d039001c20b6100c44402d241a12402d004002c01e10450400300241340c0f41241c0c09040c0100180003039458a078603511581080c180c241c110a4030300d911004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933568237 1250 933566987 933566999
    0xc01021606051005010e0d0501061509062303010e0406180b0603070b0c06041103071a091005030603120d0209031005010f050904150903140a0801030b160c08072a 71
    0x50503903c414101025660f10f402c29001070050240c5800107030286081039034139401c0100c250b10000c060512010004ca440e11041c41c010032006041c0211800a4114a030303a1203010340b15011548030340c400303076549801c1d83c1c01c00c92826120f40b0018001d0350025118285422003042e49489944040d004c1d9550100c0c501d0180203062030700c5096480b0280a41e801c004070841d101001c11490b801c1707035202d680c0504400309000000c0c646801600070000b4140c000d01c0794115034100c84002c01c403900c4d0a503203100010402c001e0681e031500045440a416400007124402e8910b02d040040c1144104001e0040c140f6440c0f1021914240c20004040d40b0160b949006104140020300040001c02e02255420310a14080d9030301c169038026184051540741d21202c81d441010700035100b56590070703607a1208586402140314006c00c848070078070003600d0303004102000c6500000c0004140415105688504d080c2200030b07606c604007940001c50958880d2000034240151034211907404c40410480c0140035042070a040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933569487 1250 933568237 933568241
    0x510030c062a05010b030303010816090902130902061308030d18020d030806012006060916050f03100b0406020a050c1e0907090803040f1d0424020c01021606 69
    0x2401950a001110003040d240d0240d420380180b510004208072002e40010b440c0c07240c007400881150740ea1502012001050030900050712940407040800e000015079598110001155204040039400440c00c0045d20010042d5030041c604880c80509030520b010000f01441c000c0c500e035504100c125400009000e0610440340c010720b051482000121a00020b6550020b00b0140014900400744484000000c00c568081d961aa031203c4101ea2003c1c48400c0710b00c0c1041e140d5008990140c4100c424001143c0c40303040c0300d2802c0c041c40603140c9600b40703041403111000303250350402400e0b40c103c50362040340454640c0051000d400180250380090840c1c40c0189095400c2003c00d40115000d1007600420301d003403030300d1510940303000c010669085c1c21544601c901190b5000d1203400504040c4400240041d01c8150b04203550104e80000182e12134192418000403000391040e140034010702150305182d070041b207401c0724110400c00e05a200510700360410003810f00f03a8002c422041d00c5600b8200d4058240141d81c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933570737 1250 933569487 933569489
    0x40b03010b0a0e0a1b0f021608120904020d020f03010e151807020a0609054806041d04150912030b0f0d0c1e0f05040b01030f0510030c 59
    0x480081c081007400c44042900c125003481401c4000b400b02001c5240e506041d4041c0b8100e030701000c0f45132504c810300350f00901581003802c09040103120380208810300c80403e090341020750300100050480d645185020f000150080c00e4196071043d400c0210a64100d040d100038081d2510014a00c0c6c0c0701c5d07140182804056200519110181d100c0c2c0240d0f0200b6074840f100310824208456805005ea01c54403022454030321649002003081f13280c00701c04010700500040300701c0e21041072a4042c8a916a45d0745220308520344014028003d080610710301d001c4500c0340001501994041d080300c0c102560f410341712000c80054036984d18444c1c0d840341031000340b00301004440c0e04400d00040c01c1c40481c5140c0e503814003005400314101c040550303810010070960785100d5900b0380200300500b090082d0005081a018085103031064403202c2a199100c040201b9442600344c040301c10103402050400e10f49000d01000d0001608114100342d9150407a25190000d0321030a8058241e10754080d541e94214a0887d21005003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933571987 1250 933570737 933570739
    0x906010305011515031a090f0f0718050d02010c05060709060305070306051c0201051c051e09060f090721110307050303041211091e0f060a0b13050402041202040b 71
    0x9010301800745920703403c002c242076013492800055030042011074050300441d1004171684100782100f070040104405044d5409500d94002c0b04000d80c681550030f940c504000380b0031008070055070504105528020800500d114018180b02504020640e80c02d4200320003100e10303c0124807118070603c2400e0307262042c00c1e0310072007a06040148900f05000514054506000d030140381480c1180c0c07408591240c0300380d8401d4402c0c07074032880d060429045410041c001c103c414400340c03130100310003090f800c6990200900480c1c0000140080b42c5802000050158000700080482d104807080050700d03942c0210809840c11055551018004d0306250040300c01320540d0300c041c400d41c0000c1c400c4c491558044204c508460b200c40100e82c41d042c0c0b03450100301d8403903030a40c866400600c0504000a0403081c0051180100000b07903488c0041c1e403128134004070030109440d4950040300000c0180a0f503581c4500a10503500b001d02c40c4543d087c2c0e40d500240aa034020380004403401440c00f568421030401d8052010841c43c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933573237 1250 933571987 933572021
    0x3022107141e01020718060815040b0c07060b0d030e090a1a0609030114040b22030504150c0209070f020f0303090a06180503040b040f0501020d0e0423090601030501 72
    0x40010180441540b03070a50400301c0440d0010035a00030455000280018103000441004840c8000010902ca00c03520059000f4040f00100202480c01b003a03201d5644101e1250054490300c010034441c2e0400b003000c4582c9540c405a540081d0368070300d16060218444d540741008000e240e028440d02c10400b81a03018101c1c140101307481618801e801142c40303480c05070340064481c0c00300c2c40000d000d01840320502000003160342c03c0c4024031040c0114248103182c1107a4458807402c007030500c0000204001d0014000039014081449101c0503416154049642d514240300c00242540001d16401c0301036031202d01098041e10150240768051258588901155001e9410340c9403485071540c49242c00000204000c2d56807003c01c19840b440032551a03002c1e001021a6221a100c424a2555038802e000d1801c1381c44280c03c00249a40c800286911a442d441c1d84905000c00d00d00c080c030015203000b40342112203d4840ca18988610141c2d844244159492401400360394514100300d801c455007003000001c912 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933574487 1250 933573237 933573269
    0x170a03031107030210050603160b04140d050c0609040b031b01080702160311041e0603031403130f080d0e1b03010606082d1303030b0609010e12010603022107 69
    0x4d40128801e10307014240d000c041030316622000028141410140d8403880c00c20521404122541210060004d852042c415090016003c00810591042d40080200707144c3c000410ba000c907040c602c001d05043c6002900120300c03107030001e00003030074100703584587e1018030318411003e0159a0300c20032141d005881030026090001c0c2109842181c40482d0201401c240c40301c250002c1c1c15200c0e0b60181e108081e42d00290f60f03035504040010340140800d48020f900050320000c450019070b800e5800c40c0d004d90074a551202d070720324480d40c500103624107186041e00c80c06014026065452000d010b411201001d0101400014014034084a440065803088034040d038903040090190743e41042c842da4118181072780d03160507081c0301000c02030743d40140c0344102c0c0e000d92100c046c4012035000f5120707607403801d1083c2ca05100c50082c52090107440e00803912090300117058402c480740e06040440200d511175980b02e0001c562740b40c4035004207042c040841100540030303040564043c05510140700c001e01810410180342c10b10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933575737 1250 933574487 933574493
    0x3043f03031b05190c050f01060f0e091f0c030b040f0209120a0c170a1b1805071e1e05030603160b0d0225150606030e03160c170a03031107 61
    0x2100c08000180140728201700b440082c000200259605101c0d1103009015403038071010b45a0b00f1202d82d02c602490b0710142ca020a01000010420540d031b9291001140c1d2481c43c0014008042c11100c001d8070305166660b151900682c44a02600303000400d42c55000d42da41040c5418442c1c040c4d82030000c3c95050b00004281800903041600f060122805015200f80c0d244c9a041240d05041c1180c070700030507070b00080044503154401e2100d150100c07800417417001d803038010703101c5c426098038400c8503584000745480c402500e090b403082c603030400c200c901c6250409402500c43c4618440845044940c1c3c042040841081a00c0c40c040100300942c3c1100c01511038502d2074507540907174901070f040c40c3d4100c060300401d18081185403a001c192030f40e8900412403407505090704103441e580c1c0c00c1c0303014845140d05220f00031510034003902483c400c444081c00291304e090b8003203510140792440c00c070003111041c00c40b6000040720000141c4c40160038000c07001a1101c6e114510700075044440b5071142d14042842803010b1004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933576987 1250 933575737 933575767
    0x40902100509180106030c0e1e01120608060906012909090c1204031d010c02240f070c060f090b12190e0c040c0203043f03031b05 57
    0x300320380e24103101e500e60a400c80059100c0d0b0a00744807801d43c4529500000700580d042d04003c0040301c071625444200d144010900494110036140300c911382d509120040d10a520541003036050101203040080d5050726040c4581c1483c80c180c0b00030840d03038800e200500c05140185a004043da907181046101d062410407458101d00641405506c6560040d00281c4040080360450704141169802081740f07280924028250b40101040845c10985940c0108500d5005811030045560002d182c080040b10f0070401601c0141010f640050551051041c0d0705000c09074005042102e00c40c0070241219820110001d20f84034118000760104424142c04200070204082210007141d00d0740b00c0c142c0c01e44da0711a0b8028000f00c0618003010303402e14010188046e60030104204148210071101448410021130f0226981e014900446140340c103241c1c6074281100c2d03420840c0c0c03c4249420900296112058104c071f90075001d5400c2900460b8a0310344001c200804800e843c900e180c3c65040140c1071034205402050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933578237 1250 933576987 933577009
    0x62208011413020d0b04030804060515010c020609030703290c0906070201050c16090b041d06071b021815030a152d06051c050d0c0323090f040902 64
    0x802c0020150160542d00c4644803080d08580280e0b0b0a1914149460028841641110705036402c89c54040411038501c1c180c09150010b043c140d490f044100041e4003001041c2d48803045642d03140c8600c110000004900b80015034200407080760310030603c0c00029460081c104000c0124400300c0c020400401c9941c2d595084c2c44529070280f0b0f10035140c00240244034030700350081040003503580005000013034400381904180f03c02441500c050040f8178008000108003054140040720726044a000142a24441e42105001c00c0150200c50403c03400307600413440224100302460103407101c0388100a10100c001c609403074000c900340d00402268501d6182c10b520514441003800c01140c50701020720301c9888000114690160f03100425107a11808506600245014490340d80540c0d001c500b1103c129a02c41c00030044550050040e041e00c0c0300402048815001c00e4508509205000609480700e880c42d0504040003c40b19161070f030f441c8400030800c0002038000344580c1c070681c1820410307001626200318840c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933579487 1250 933578237 933578251
    0x120905030c12070b040b0c07060f05090705030714060715140609070206060904080f04170d1106040b0610050c031606110903150a0e0d080402090a02030c070215090622080114 76
    0x4c40c071f8440447c0c0e2243ca1090b41da0251070181072802000580d10300c2d50180d40201003c0048908150703032041450b40300c2311188903003006801540205141414400000e080c414801c0386003048030040c000075a021242c200300d4100484c140d44080040350705151542e550010042d000400e17140c94620005281098000c00003802d40d2404120600142c5200341603502400c0040c0e00441580210a40c40780e0f1001e000681d140007401022040c54560b20105042c1c2c00341c0c1d0804410a0960360310002d0000d0120001c2810b07081013010004148402418800780442d90282200703000003400e40c0c06d12606482030440b00e20a80e0904000844c2107940014001860350000004110141da51404590044c850040b440f04107001c1c1a2030002c816030701080d200e01c1140300315445016505c03190360440890004a40918104000304142009490080c00181005024140341031404c42800040380c905d411030b402c0404011007002e410110420200c9036a4080e016030030080044c8441606d5100c500c040240501c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933580737 1250 933579487 933579503
    0x2060114041406010c03180605030402090f160e060904090f120306050d0209100f0f0f082103040c03080d0204030507091122080105070503190c0503070e01120905030c12070b04 77
    0xaa04060240f100034489221400000d134050340c8c0c41d14040d06a44c001c6400320301c1804200d001442107082d0000080c01034800301d84401c80c0008010043c2e0390f81d040b50b0340b030301e5001400340490115a5254002c10050b24822412403d919489190071010410860314110034075041c1034003070149172203243c007080485404072000c03051a00c40c042c100c6c4110343c085d0811410242010400305036520524014022107102e000000a007c0d503c07640c1640321a08042c040007803808000400d1080f0174000c1c050354201c0c1c0920f009000666481c3c0d0b034407070079a019820320003609030041000c03c14400280000c000600d20070100303120008403006041940c2c4038140e40d5444001d902403a140019079075034844005013021500070403150400c160b016205400c11100500c86e01d44804184007820080c4c009c0d8007480c3c6c21902e500c2e0558640600035283c4200c450300c0c1504101200b0101c42a00c209805044101c5005002644da00c541484200d814000c00070b00000070003504204010006600e4040f06600603004098 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933581987 1250 933580737 933580757
    0x5061e0609040f0209030d081b2a010b27280c08010f0b071205180303071a060a080a0303050403030b03100509071505160609120206011404140601 64
    0x80041c0605603219401a01d45000290b80409650040002040482c00c69081103000842203540340800c580c504105000c1807541203140040201030440609800c1000c0007008428501c1c4544440440303202d580350f07440d90b64010642c184216001200e485081c40c002520510300044588454007810019810094500c20800760070402311216051000d200f090000c40003030300008121a80c20f002c1d0003100c0342e95910000e2030314034035411541c51030340c84040002c842070000381c181d402d81c03c8809003280001c500c00c1e511042e40c1d8148000c04409104064840321b6009070200d0340600780700101024018030020605000801d0005544107419515190101d240e42d11707858100d0203400e0202c0841e4141c803e61840182e81d51702500218820001c0030120350b2200e40c0c911824001c0c0721041040c0c00402d004008100f81c1c41d5011209a0907940125004034000400381e540342400300742250380b030300140c100303000500c042007040000003808101100c00b405818103002d1000d200b6880540141e0500201700031b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933583237 1250 933581987 933581989
    0x509060f0f03150906010504020306031c110f0102030411220f0204090203130209060108060d02010311040e0f01150519050a030b060408152d040c15050a1205061e 71
    0x8034240c0c84001e410f641c60b01030b040998142014040d6080062405110004140317800d09200b600d10500d0f000b4020704080403d90000100d401001d400f43c8200001c03980d034402880b800300002c1e400300201000043e543c0ca0207003003401e00d44c010340203614030565080302909403a51603152240e8045145082c00120b41d0b0308025060020321560380f1010341a070011081040d0390008030507034510180251000d90142c0d03250401120a52011601c00380e003e12282240750165100b944130042842c64040c1c62403910b0745602c0d0f10548200b0071910003403018103040040c800104442000b1000c61041c2c10701c0c070b0801c210841c0c0710302e85000c030814a000300940842c2140380540710b50068015a44e01606e02965551507405258445c54a101c00b1140d6001e03c1c40030981c4100035401c01c80c040c8240d002124000c10919010000082014100b41d84482280d400421002c0d00306c90788071900c501c1912130f40e9840c05541d1028200000312403160b002c091404080246640b00c04805402103124207000c0c4031102c060030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933584487 1250 933583237 933583249
    0x13020d08030c0d0c11010b011716050705010e0601080d0f020601032d0305030601020111040b070b13080d06050a12050706031d0a1b0e01120605040206040302030a120f0203040509060f 80
    0x10441c90f40e0509244018040d00000070140c5070800d070001b844506d00810040d10540318081900e040d101c013040c0004d440128044a0412005072450031170b02c0d010071f03a2078035400c0d51003200d01400366030080030040040f100100b11509000e041030400c50354584030303504080c1d180e800520001d085801000004282c2800841600c000a14a45500110a442030070000c0c6141c008817101409586440c14461501e4106401c1d60200c414503d02035103014040d9485084080c8080c0000180c0700d4050409000545c00b140a096554100280010450718040c100580700c03010307034006030102600b903640c4d0300840c1d8042084010f40b20076041c042a42d1f00001043d11196222030703101013007801400861002c01c902e00400e09400da410380b0b0010340a940f124014014007001788200f031156040d03a0500b0000541c96001380b41d0007800241483d05240c0d6940102e428011001c2c0100d400b10004076103010600d8000c2c5902030286507900c019401e250a000c0405d50340c100c00f400c11403080e03d0380c0131081480d580358 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933585737 1250 933584487 933584497
    0x20c091b070f050706020106031e0f020d0f03080a0506100804080f0a0306050906030f0a062f0d1a010e06031f060c1716020d0f0210051213020d08030c 66
    0x480d40d059a5084141001500641c41c40d0003101e4074050201d00181d014414007070502a241c0200304030403405560541d20001d100e030800d00b15212542050701c00c0150341c0300710440800d180641e84000030041d440c40c004000039401081c03c84114501000d00c203142c2c9410922400200503802c10074140d407160f0800000354020805510109200000c48644055058101c0c40845005407498002901c070282010f8540b500602e0318000341d030248100102288071030300003450040b0000c6012120b401404910381c40d01c1062420031804000024013180c13000c4052143c100d9403018000421480000d1a000074501410540d03030a200b501c2c08404241421100035130080b4828902c0c0d40442c1081da01d40001e0b10f51008185d00f540c200e1007400402100704008401c40b02c02d40483c480c0f01c01c031011242e0030403215540c0402d0031340f19a0744080c01000141c54442803110b0044064580c07d0319040450740c002d1070844d00030041254240300c0100200140c0382c01d00c165480c564000c50454a954914010381b0080c051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933586987 1250 933585737 933585781
    0xb01090b030a0b240a050d1e0b01020d03140123060a021f020304030504120812150415030b0a230c0a0809011b0516060501090510080607020c09 63
    0x2000041c0036140c0180c0c0e000f810507400a9502060078202d0030712495100940e240790040b418400c0000861039807144000b84212955128005107868119000c4090b05540040c1000d84558941181c1c004c0d44c2c041192902c2c043e0a0314050044405008a0b4403000c2010f10400f03450680302c1c094003c112540c0701190031494000780440c2e80b9543c0926009640d101e144001010a50850780e80c0b0441c003503d4001c80344903940640740e2920706403030304481c5086495200411b0302c400074180301e00700011700d0144016006d4441c14013400b003032035405000c2108550304241d4220240d0440582040017a90f400c0c4a580d029543c450009480600c00907040010030329103454400045009003005445031418000d021249040e580703c03021a590381d141c0328200c47c003200b00191968482d40301e00c007085d0312034401000c081e04c100c0000d0005981c903907100c00030b9542c00c5e04500c0449403184100f2008404000300300004002c0302005007600d00301010082c8d19040c1e1407070968001c0c1c03c130b0030004402c80ca0307450140d1202e1031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933588237 1250 933586987 933587009
    0x708030a020711090c070b0403140c060601350402010c05120301240206060f19060207230a090e1c0201021b06060f06030a0e03040605120606030103030504090b0109 72
    0x1820005540081d8410310b000c550410390440490710504215100c1c2d4070411104012a1074500ca03500c410710784041c02001102000007548144500d900090050b000303e2030b17881e00510703407810b00000140c00b0400004000c51207089400303d07200d004890007038000d814501035900d00901d440e1130004035458008800c0c050602d00c00c1440c1c408a03450074400440c100c03116801401c014100c00f142c04408030000302c0416005a0018000c10102d1420340324090548100038021400742c00c604201031070a405507070043c03025800500c41040000071207e2520b00091502c1003204c42144914000364030001e141c0035400600740e681c203150150b40c0d0208000f4101c0100c40350700c100104540c420090103540034021142140d00303200e1021100e00000290a130084000419185020400400384081a0802010020ba41d902ca40c44946502800d0004102404144d61225500c446e81c41e1984001c14010f03041501400e020001000070036400016901940e4121f103001c10b401681e400101da4101c155080244101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933589487 1250 933588237 933588241
    0x3040614070618170f030105010809010e100617122719090f0c0206070f1b0f050d11070312110706050408070e09030a0503180f071a1603030b0105070803 67
    0x1a0306031862148610a0f40002d071300b0b00c0c081100707074603902684508045c0c190040c40107016a42c0920301595020080b20000112802603031304503403410b0f484140007070000755100c1052092102103480e10494116060092001d240046043d0089204240841c458004902120741c10030a0141c4c80244041000b004000d000c41024411701c501000380c42082205807805410401c4401b450058040400864020705503540e0740140594103600c0b690819010000000342e10f1040040c081507219074180a000c06401c2c514940ca4414130f4074085e0720f40d010a11000c0d00050302d0901c00000d940c025039a01c4040c55048101c00c1c1400d0391030395909014203c25000c1c40c10085825540800078004a600ca80c0071140110391f80e0b00540d034804820f444128030b03500b00704510000f10340150011030308403c220b8030b2600d01e6507241c03050b5820718401c41046450390300001401c10503c100f5000c803206ca03018008400d807401c424425039074000b1024800003024151140440c980036800ba0050746c040c11340109a10303940e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933590737 1250 933589487 933589511
    0x90e120c0102030a0515030a0b0757080a200d1d06030c070c050a08010219030b01120f0b060705070e090a0206030408031023120609030406140706 64
    0x81d420841340003c40900c1c245c00070707003981c04494205e10205006070141030070841070b03111001c12840013059401406050642c0d81159914941e02d00c00d50100001d0031152038121400014a02c40c0061201c81c1180c80c008110201c490100c4444e0821a4052211540c0d22051842034600ca14003080b85049040c440c29800c18603480030502254000c1e00d5511540d14210110060008501800b4034071340001d41480000e600170b001e003004112107402281c00800c1c81e503480700020852900358010207504c0e50089030026049120700e20340402880c0509081c0044980040024689120380b2908103c041c1c41d54050b030550441c41c2c0c0004008400500310644d600c01504000e0755420040c03199041e4083c031480000e04c9114042001ca0400e98000c1c0600d10b5a121034403001c40581010b418070380542d00510001030070a01d03295012551106600818035000c41c03400c10003403c448110030f1400c49401640400803903200c00b0080702c1c166440e84c1010859540da0004c88070b410700904400900c418030f0400e600c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933591987 1250 933590737 933590741
    0x306040b042a0833030a0503040f0e04030507030c140d17010b0f03010b0c160f050909060411040e070f0f0315060f0b0c030d06151116090e120c01 64
    0x25800031146080c02580040104481503c01160000c001403c03914082036001c1c503041c1c50040803408503c1101d0724000307030710000b800d29004507000c0b900e5a000040c20444103a5520002009191a40520000c2c3c901501c000d81140720b003590040800401400040800000b40c0849440d6000070044402058108a0281008108008011050501d0780c00007030b180a68008a4021200e50324039030742541d1800b1956201500000d241d15554058074103a1000d007900c0c0c0407000018011007140030364240c0f500040c054400b03006084100241c2003c8100400710301c4440301050b40d01010748000901813031480e409030a000d525000701e102128a890002a00506094050f00303503406141c03548804003c1c00300b20821034029100d951094050741c04204511030b490400341217804405001e41c0d1411800790a00c008881264001d0340341c2d0100302081140b030b20350003512010f00362500c80080403100f00381046440700c104e1600c18001c0441e22903400c00c500c0a401c0c05500100185005500d031145042018a80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933593237 1250 933591987 933592031
    0x1c0203041b03060b1804050c01050f040e250f08180c040f0c1b1703070e030a0c0305010f021c02090102030403151a06120a110c0304090501030c050a080d03020306040b04 74
    0x841000302041d017901d018102890039000303d610000401c0411140304c015280d0ba00240012508190f06100000c0c05c1240201d08620803126400c9000b00045e941d1405404035195401d040c0c10000c1d42040d4400881d0404030715070300039220454811113426590200c84c5440c0b00e4410594205007400c0002418400075009000d119190b615055131400000702640071141041001400c1401c0300d117900703140e6100000c011908062a07207000c05140c40000046443d003a10403204a03842c8806440402c140a030070711030065242d4000d0000c2d03192500009a4402d10905101c41c8040d95600103540d43d01a0b000300129401907901181e400910481030049000605600480001003c0c64400001d202d10f400803c80704545104406440310f501d401f09081c000740100701202000e800100000c00407040200b02800c0107228801e00841d540d81075242c04616180541c3c44a80030f00c081b864240405000800d00107080c10040c540141c80740c0c3c1d00000640a4190781d500b0300d400030b2800704104207c80900006075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933594487 1250 933593237 933593239
    0x7211109120f03070f050a0c0b03090d0f020d0e0f10081b030610080a090b090d09080714130605060d02091c0803070309140f0c090106051c0203041b03060b 68
    0x71a50404a9206648915011414010b981c00c00c104400c00580721541c0d441c01540100200c640403c081e5450920f40b4426810440d43e01c8404001c0201c9484c0810140440c0b4440c3e280c0300310324282841c0060350360741c1c4001c0400107100d003e00140c94151103000507900c18030030082c44441e4000d1101000342c030602041e40c1444800440315031401400c040403088a014444c081c0164010546c0c040003110740300e0001c0c10f100030540c1c5500052002c40d42c05406035004441d0030010f0108407220704006007824120307903c42c2c021a005880100080348110350503031100041500c030710740c1e404010702c801c0004050742d0304055802200481c0d003c00c1400c503507010388940181a200947e203031000d00c08200001044180051005030708100140c40385100e600031070317902031140040f8140940d130211800d00305021810528060303800442c21031340c2850000c800900403c03c0d4144240313007a0f40c00c0004a80342d0f040403070461083d1b8000010a003085031410707400c485582410141206603440e803a043c0c02611011281e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933595737 1250 933594487 933594499
    0x120c23150a02011e0c0f3f0c0e0103060602070e06061b030a0f030b0d020f04020c03090301020d02030703060605070309060f1b1203050606090a1406160c0f060f0807211109 75
    0x81c0710114060450038155000c04143c47d20001c03403021016100c4126201080040501c000d0000c41d0a0413900407500c81040585404801018003000103084031076a5010004542c4003460130031a460142d000d10b070704000181c480320340c0c561f00421452207603000d00050014a100014401c84601d6010311030501480303907560b05000001c0c54001700b107002260540007950020950542408600e050b0340245600e122090945e8180410080000e0032600803040c110001c60b000410800d0f000c2c3d05220f50000303040c82e8200325040040f00c0e10700801441b50ba000b40014003503031024201c280c50090a803241c134010264401180c0440d03a182282e2a0b600144945020a0410300898450301d001c4055452450000d02400c09080c940701c480c0701c511803280751054105400b003052a004406011b840d4040b24081c070803081080e4601109108044c0ca0341e4004c004000c51007060b2949642d00503c41600100740386070143e1507009a414950072904051505134500f4074180e0702c140b00d190b0f0b0340041c2144840803206 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933596987 1250 933595737 933595757
    0x7090f08150109060506030a090c050a03060609180807030e0307050a121403090d0209060604031a16030b0a12020a0503010c121505150310120c23150a02011e0c 70
    0x400d0f00703945613400342d5035010209000081803013450380d10850385180140340c502e000590361000b05010031119041a12000e80300c51081c0002c0b9958019440080094641310742d8020003612459440d02a41100400300000440c2c404031f50345d81080003501500c0000c0040100c260350741e01e1000d148003202c9007101ea81140342200580031401009407160702c0c1c0c001d4501101603010b503003080204a0010482a07010307005000200109500031260510300103807a1222a0a04002d03c440202c0c410311500001094200380c01c00241d0b88072a03035400121a4000054044103040d40b0000d8100700c1e00c5e4202d6500742d03103400e0003005160f601031b04580c5440f0792303032204001c003007406402c1c002041e21900409820880000701d003070064074103400442e80002901320306142c035902e5941403641c50320b83d820291004408000103004016001c0036080540803158070b071005200140703002c1b070650381010310b1a0303500c0c800104402982500030f4200010031800360f501d403c081485404000300030404040203c0001e107100722 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933598237 1250 933596987 933596999
    0x21e0a02061303020d11191b0f060509100309020d0606051e0918070f1410030e1e010b060c0a0c05010c0b010b2803052d060907090f081501 61
    0x2a44401c1c2c01c1d090342c054091841c2940c4103450a05c20b00051074004d21929106542c900800240244414410000f500840342c000c80a428240302a402400c2c6181e01c0e0b070380c104034842e040f1044400344030003600e0315201425460707400e5000f0f04c900c646c082c1d0806040c05207807040000a600c0352040c1e0307600702c0d11002d41079190030640c0003103000b02da40c403500201090080345620011011032a80619140100e070100c1d0b45941e48510403580c194080e0b029041e0141d501529813402d40304c01003001b401ca280c20803845500710b035142d41c2c1d003a03480350040200c04540c0c001c1041080a4021415240010b801c01c0e6a64840b00c80b01941c60180740341c15602c20703030314003804503443d0b104069400b100c0341c02444005c0d8607401c125095156a00001141c1c0541c01500203101c034880c1d070030741203607196881500c00103290300d44140301042413080c0d011001d007000248411030351440d58109056401c02e100340e454011a584080003a180807042340c11001803042500c1000488480c00a000c0088102070050403045e82da03180c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933599487 1250 933598237 933598261
    0x821070f0606080a0c0305190b040b1302030a0b09060c160f0203030906040b040302041b080103030e01021c020c030f010605150d020c0102132d050105031e0c210c030403080a021e0a0206 81
    0x328000c11425030313807001c038000c1a51141c143340c01c0160311411a07505907469000038a01001168200c071901d01c02c0e4108407031860144a000e501560600e2903070700d0002c0b54403186c0e42c0d10100300e00041c041e0203038401084c15501c04005276503003500080d1006070364a0310b4903602e039015041844100e20460a1840c06481540d1a540102c0314920b5600c03007244607421a5001e82d1070001b400100350441c825940542d00020303030340c109141b110742c1c01d40140404072006000d050070b002c510350900f801681003290400030b644644c1482909201c8208445480e4030142e0030040c0a0f00c94400088030540c00819801d200700d4040b4803500480d144c418200d04044161007175684201410b030120b41050f01c20b1141081154021230017140e1085001694001d41e02c903d29000009580c09d8420076150311000c52450840620610b203a05c041c4040131469001d03144c002841522444001d100a08001140d40820303481e04054040e5074104800003200303103c1a0b074020110a031a00306a00c8100140705070400314140300001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933600737 1250 933599487 933599533
    0xb2805060f03161106040317090c2218061b08221406070306060225060e060705030c100f0b10030203060a0e040c0821070f0606080a0c0305 61
    0x3100101c1d0540e50384110b0f0b560074240c1c18102000f07000707290001045807103003406035911491090316100e400214400f00600c1c04d8030300901803100c1e075200d024044240d0307444080140444060440882c05050700c2003207103015101d02d680701840019132550040411000b40c00a20001241950580300034a08030400c840703070541900d00c0707407054403500c28a000d0601c94990301c0c113030b1a020f01c03c103000c44134810380800d00c0d181e0111211b0300040c0c2d80b000309000c900d40c103004d54054004a00c2c01b031000c0c0d500500070302001541c7c610500c0240420801036100303d80b01c6006443c0040d8201080d02c0d01c401a40380d00c240c0300d401d868580348143d450181c00b1214010700b80300300c21710908003506a144206050300290029400500701d603502c502440c0c400988000600302551050780f044203081181c0385050080fa2800da0000c0d0f0342604c2020bc6000b4620126000c0107035591240c1242000007148a1800c014004041540004006000b2038407403070b0900107210f94403030480c1c2c445e4040340d50858410912454090103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933601987 1250 933600737 933600757
    0xa080a030f1d0103020d0209330f03010504150b0d020c0d0903080d051503010f0f0c05120408075c0d02030c0913030e010e06030a09060b280506 63
    0x80602d41e034070b65100758080d10245524860040c03030404100009403608400e910407602e4559020354481000100340c98640806104607121420820580030140d00350105014007401581d90311099419110a43e41c454010142008000d41d182d0840010300042e60040a80952a12429100072229442202e021040301e8003c94603604014203c0e4110002d000050250700708280c1c020201d054980e8203100d482006507008400080b41e00c4602c2c0b1003010746100103451000d0120501801941c040002940ca60103075000c000ca03565800c441ca0034407007a4903940c0a819503445101170300fa40e60150703036010b8042d150f0019151f0307030885451103204808481d01c100018003283c00300d15405050034150603400c019407004003a100d00c05400c3c1c0100c0d144d032000719180c0c500d24401e903580005041c0c008440350325a0070203280c00800e0b81a40b40200e2a140f002a00079443c41c3d41e920041000d02006912903440e148004020040c0303044a1a85001c0d440051000b21120f03e1703945c070000070245824811102001c01c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933603237 1250 933601987 933602027
    0x80d080103060b030715030c03060b070b04031b1e02090a110414030c06030a060e090c0f060913141914041209180624020c19050a080a030f 61
    0xc00c5503280c40143c200c1007040c9416200d110b0001c00d00c0e91042c603540c100008266000114074201c200002c0a03640c0580c440104a0020851440440c40340c00d2071560054250800d2040b40c10106500c10100a400d0000b818501440b0003100740c0307110515400c410b450084800500302d0319034030264000c480c0280c0e0060b1103601c1c2040708001c4114509052280301c0c800905861000003a080407405a9000f00c0c2c0114101c0d40d121f00c00d1007101003002c5210b230890640001044110400070104408142c02e40d201c1c0d01c103400c0450748500d40ea54038001100894141c1d0818002440002007a446640050b66404510001600309000c801e9051240b400c00c2c5004101003040c0d522240c552008108440c0f003103604001c0300030701c082040080c40d6042900700d4020800042d40c0d40c0380031290003400080034444100540e20b108254909070b03001605018001d4101d45032410007044d42111621407005030300c000e40002a00f540010440c1020610100d080e009840d010201300b03001d40c00b110115180c00c10407030b040d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933604487 1250 933603237 933603239
    0x71a0a0209090924070908030403060b120f060c16050d02060a0e030703020a1428030e0f310e101503020d0f05070e0c0c01060f050d0f050a080c07060306080d0801 71
    0x425a0100140c010310300c1e080c46d86450361201c00850441c1e1103900151032040d1203010f11040c509050000d9401e0080f05c5c0040e000c11080f0000c030301e07255400540400c0f804503010406002504c404030040007040d90100884d80b40000e641000380d120030040318080318203440e001e80888401d002000712000c041e45640640741d5078145603110000c1101110b00316244d44a0f40d9980c214841c44440d08188a818020510b0011078035450014001006499130901441e0317580300d005015256a18002c4042125441110480d00c01c14981201c01c1080034880c0030403824005800c0180708007081080742c0d107004c070f5024002203039598040e5003e0080d9200003504500c66640c9880070806281040540700d1150003070b500312940c2c6090150312018140e40500915100007a4042401000d1042c0e40003040d03a0002c444600b441c1100040d1380090740340019180d19440b0760541c2c2048028000040042c1e8031003101500c1d8a9061540c6a49407154010b0a01281c40d0900c04580c0744800286060340100d05e036100e101036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933605737 1250 933604487 933604543
    0x13090507181503180221060c071a191b0305060a06020705010807091d0f0703050f01090207020109031a0f0a0912030e0118080a02070b030c040b071a0a02090909 70
    0xa181044903501d5007200c1c500c8510060f1b64821005046031030001c030b01042c02d030650010600b000c4d000f40401015403020030555000560b241c40d20b201d030703031042030f10903241c0d5941400f01e6450580354041d440345545400300304107494001000c4c006c00f69900756010003081d51940140401c1c4000307030180c4000f681c0990810810b56200d078002a40c005d02070714103244119940c03120100c0700c120304810382c0305e8040480c2c00c000e10400d1454030550f101c41d46280500407402c06100344030740b01c0018080d0005035600061401c06590140c080c1c03800440d4400b21061344014258003050805100b40c844864a0000d0004a03401c1800c60054011254000e02400c6031101c8480701a001020360240305e444554883d419000309081c0c070040300c1e0903203004a12007507441d110040002e0030054580c210805140060040c08802a0140d080d10103076aa81c94071103941d44546d0134036450042c040e103191010120200d0402c60555241d4000c1d01e541907050364040f04070749525082ca611034140010560078480421806115 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933606987 1250 933605737 933605741
    0x181a01080709060503031e070b040305070308160807180f090606020c0306240a180506010809010903050409150f080a03020d05040608282313020a150513090507181503 73
    0x250400036210755188c814296510752248108a50540c00b1883c080746c108203160f080381d00079078405101e5502d0501600301d40c1000e0040c45000d8903030300c108250604404110060380340100083d00c6098000194940c0d5000000f001d4406400b0340c0006010704001281786080c000740150144c0c100d000880400050b5649004005900e03c0e0400c1e03100c1891240054180740303e240d042c6030003241c03141c081154503207080050100c000140000d1820b0b0b1426400030b000c2944081a40c0980311082c0c0003154051103c4070840301c80b0490380012140f03102e11040002d4034240024a00b11007840394007940c244070000707402900d1500a610880300412601000503003074180e079200081d45030041030341e03521684091194000c21180e10580955113018490701c0340300c4030800b0400761584420aaa00c226a9104981c00700768411414829006081075003c01030300309501072416034902001c14244ce400c0d10b5961504d20000d00800d0300c041c0f002c120328031110341440f40b40003805015900c0c203031040c2d0aa204070078070440c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933608237 1250 933606987 933607027
    0xc0f050304020103151e0e1905040f0507060203030703060e01151b0b07090503010501140f090a090816031b0503090609061b0706270504181a0108070906050303 70
    0x10416644100d00510035490070a000b01900360401300041065110b100c0340d49405940c2c02c240d01f0109481e0401009185007084900e85d04c3c400740002c03465803224903091030322040d04100105076004d00e4001098107680040a1071050b4041d903018408941c1c4c0b90803091159030300780030740b4030007103125041d800f01c0602882c0f0003171140c03c04462034507014006031102d0302d42d10401c4d10f40b8400102415030030822842e09000701780c00341904002122202e8070090001e20a5040781c14182c0c00f031a09000007400c4052070760710044800d07070003a03810750b640e11545203c89640d00b9440c400700d0108280510b1040c0092070b0120002582c0c3d0f201004500c0c2807040c600b003081310b400c42900154003a0003000181d0220b407210f080344000044141c0207003115130070700c4400750042c1035440f001c20349055034400c51001d240e000c01c240001c0702c009a6000609074101c45c000c0c0d002203282840a001418421810001441e0b90078086049890580c05c0d50003280d1246503c01c01d44220340701e0103501d40d10500a480d01e01c118407803039034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933609487 1250 933608237 933608239
    0x31205040f030f1112130801021606180b070302071509021003360b011d16091d060102190b041b0f08011a0604050d1202030f120610030c0f05030402 65
    0x1c0c4c0042500c000552a001c0c01c210800560071012440c083e038824203091190140c516000250f007840c1500100c40c500084d15880a04001d07140d0030901d44911920000c0f044498003c0c41c2a8054074140b50090041d5100100846455800c1a03215145600764810007942130340c020071a803142e030001c4030100d01500301c0040a0f82e0751074801c20686040ca410014803002031907088100520114141042c2d582420142d2000c078143c1d02c6802826402c44240507001d1344840f4400e0349400c06001d246080307542c0c000c290004421500703101d07400b000740c8003420711417840f403c026030898545020803500302c8500f00046c080200050241e5020800041c640c602421000c002c001c0a42c00950385c42c441d180c0303102e0b40395020b42c080b40d55512200002d6111442411200003003070f2011442c00346408042070f070911400c4009017420049180c9542c285d403081c0308070b800704000d00600c9500c03600240d084003000ca04c15621a441040d914030503841389400b9015038014000a6240c0d00302912440b5400d94055000070022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933610737 1250 933609487 933609497
    0x1d06010c0212030d0c180608060d0602070f02040f0902040501140315040203121201061b031b050c040f0c030b0904030c030f0509040213051e150904110c0a031205040f030f 75
    0x144a91304c0184a40300c00e8245c25035510b070002440100000d070503003007070304010204170740c0303200f08421501d40d04502c060700c5510000044e9105110b090840c800800420025071050030140b4602c801e03540c9401500405008550400050740d0320341600f852101c5000402d87c054015004110b8000310403900c0c00da216001409030b51440701406090340b244e510000301500100540300050002c56130080c950320503a0401c0c0c02a00202640b40c5020b422541c4c41c040c8200030403000046c150401805020540c6c0c0031001030014840044021101d00180c510310381d66000181c030300140d100b410301d440503010340584e805440704080c1c540e2607201200c0140d00c1008507000d005041140203050b444502c0206806401c3d0344112900500300001c003e40081036040c444080c400c803080031941692140e4503c071054100b0300311b040d42d48481d50045030281210054081e8010004954a18200c6012511540040c400d0ba6401d00c1442c1100f451801c4400c1900e014105412400091000a0281c6940c0d800e41d4214188 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933611987 1250 933610737 933610747
    0x1080606090a120803190e0613051903030b0f0a05090c03072606010f08040c090507020c06131511191403160b01080d08160e06040801061d06010c021203 67
    0x103d000312621401103071015800010482681e0071030341c11445100d403d90301804512200241d4076038444029202c0852200b1401051040040c01c0050760300e1342c056802040f1541c10241405001091000d150b507020f450700d10001c10f1703a440c02c0c116400503107800814442158032210401d01150700010800024000340c1e00a10344c4102440602200d03043e4075031070140d071034a8400001040c141070000000c003441a00300038440040c84400e11902500d542c2030300020076954a160407071612601c0382c01c26802c51000220350b8118001d40c10900142c84402905c1a180e03612182c0c01c0301c440802652004040d0090000309142030500500603108034003803001c004c0c0f03c83e111184181590b0001c9407048217211030903403400800114400440c01400d03160043c08004000344409880248001c0201e0402c6030201c100240c254068402500365050107044a030b00c03140c541070301c14020300c081c0c0550030300034140081d07406000e00315504a80c420f01040c0d580c43c00da00410340c03c1c400d078421850315200f8075020500c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933613237 1250 933611987 933611999
    0x703020111071407050a0506030412020c10020102070b0603060108100b0303121504141314070b0a090e01050406050a0608101526061f020f01023601080606090a 70
    0x2d07245440c061900c00034000d0000495a180c50702e0f65002501420200008102541d500c0013a03d038415005030720140352991102e4101c1c05e05100070407442e808902e040c4003a1806070705502801170a42310703402c1c030005511800c04040d40c03613009100b42031650b44156002c1803800510303040406038003070160440781014101181171980e0182180c0e54031020002420401041c501070088802c0c0c041c884140d0a264104030b040c1c101c1548401e40c0c0174041120080c031200300d1500800c0703014000c1054040300c2d03071078083e8110000d20f401064880c41c1802c4000d600040744500d001d104500c211240240310060080c600901500d0500340201101081c000b007030000030700c050210700d8086400300c00766100c0f000c0d00202c0020091040b480ca185401d0001000c00b04485601c0300300e21420403441c0d5911503084044e41c40812864175a0340408e0050a500204110000202a09640c400b282008071039144000000d00d0400c941c80780030504038001040c040101da11410154018045031002800b00401c49446017 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933614487 1250 933613237 933613271
    0x403120302040803030712050f06011e05091314010611060a0c03090c060320120403030225030216080312061309050102130609080307050703021302090414041416030807030201 77
    0x221b0030808108809444a1110003a2060560007040302c429141c1a06004000801c107407040f044400c600d00d040d040f081c0c0c540340100240c680691004105c5656840c0480c201c102070440411241c6401c40c0d004008951940103105841030b0214150060226580703078182880509030f012280c405040d81c0380000d0000c909004401c0c40034111549004c0b8611401c000900b0344102664416003c03a0ba0030300041d2006881c0d0f100494000d81c06284c050b8039040b101e141c1104c4007502914650300e0071202c40e0120b003050340226a00440180c214082c488081d52086c0094991051507482c03042001c1610003d00e103490000b41141c0094403100700002c03404455aa80b80c22a40300444444001011782c0040051541c80041e000140500d4000f6508007a000d036140740d43c030103007800020301c5200b016000c000c1c0c200710b5a054031100722004000f844080c1d0045802d100000069405036043c140040c6042201e1100142c0c0441e85400d045241580e9071450302c0b5207500e504842c40850455403a440701d904400702d21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933615737 1250 933614487 933614491
    0xd0f05010603050d052d130807062606100207080709020909060303250602120106080402040c05131a041a0a091d1810020c010b010305010812040312030204080303 71
    0x52000051060550a149180801040b014410040704006001688400280c0b00313901e54081d02c140c007001850646458010b0003075040003a8121003a01001030300303504c002100803c9840c681c446043c4110001d40003198502005100781d01c0c1c89500740458100d0030091521480e10050344144d8040307a450b0b40e000b6080030210b500c1380141c0340e0003082c802c010b07107400c00d2220f40141d02140214501034a01d11445c484070010601d00800403440b43c4d20b00c05002841c7c0407120054160f1501c44a01c1da11400c001c2d05e9058240c40aa0013140b030040750845d064052011200400c041c01001c01c0c5052900c0c030111261200c100c0344800c01c900a10001a9003c500a11016800502c28919443e0220030358010174080803039000b01503d9070a28140620300468251041e000012004041c00300c03a00c01d846141f40c1043c11001c296004c1c400036200d1030404040d0b0182001500980e82446681d0381e510042d5074850502080c40842e050802c0104002007014030004035090f068100581416074410b180f600b19001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933616987 1250 933615737 933615743
    0x203100509071d010312080a150e0103051501030b060f0609030a141c0f030203150307030b01090e030906090108040f1b060f11100c020102071b03050f15150d0f 70
    0x4242400b950b03000301800000880e810f65044910b42c07440d03d80b0744d10780c0820041107091100d24004209884269040a410381e021040b1000e981035451034080300c0c640302484103540c10702422401c115000b44040c0c1c500c0c12aa04951140050b80350b100401001c12000507083e03a102108118012240c1c80500004403414081c2e0322002d02d40780780d603090a003002808201880d6410008003108005c90704140d1590048072549070040e100d41c4c40c4440c450901242401d500d43c10312074010000100620381d507030710b4180c4805c500700b404880700507203c1c2a80c1e4010410402c5c0c0c0482e007400003141e2540300c3e4544a5100f070084e0441816182a5156801c042d809109441d034a540030702c0040c00026041a40c9080c170302660f19140310241c507680900380e1a50082d90403015216211810074403980d1003501031f02d0040780c000404207500795442d420482c07015207621045440d4040e00c103c90a09100111b2184074804580f800f51106035505451280c074419402e0b2070f10740c1301c0b040b0000302004c10700c101d4200742d10030f01c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933618237 1250 933616987 933616993
    0x203060414090a06060b0a02030406031a030616020d0c1a040305040b0d020a020d08042012191101051903050c12070e1f02030706020f041a0d0b0d020a030206070203100509 75
    0x5404d05100f0b041d00d0301a0000710b00450200240ca00c5d8a9000040f01e086076424500020100458001d03400d124143c030940c0d81d414803c51061294107229018041c000a032550200ca0b07180801d0a02a01d85640e01940540031054540700070401c40f50035070350164068401c1c83e16502d000d895520701000c0d500300c9050380400c5a4041500c141035501007000c80d13003000e03050074607540510b040c1d0b44407500c11202e460030352145940e48503503005030b031101c4103840b0442c0c0000080d80d65004202c140c0c0b2a5918801c4400c0d244c40e00c1462081543e0350041085a03889000766045452003484204180d0207484041c0680c0940a0200b1001d088400301c1d41006006021555968040161184c00c200910545c1116498010310750616076019035000811960020b920000258407200105075009140c05607603c0a00050280c2c004008054420301c01898801b441a40030405071188405001441c0e0801e01c00940115181105201601c3e10380301030107240b840102102d5029406552001c155a016a8203008640c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933619487 1250 933618237 933618253
    0xa060e120c1b0a1211040e010c0e0312070c0e04110301151e081b010c06050c07050609011415040f0915060602060f0703050711030703050403031b02010e04020306041409 74
    0xc030007039075021081d10003200c03450301035404c0600d4841c28a9082030018050000ca51845046403590f821844020403040000c1020100752403014000e0010f091720644a8041c0e07500440d80040c4c600c003504c00940d000380d00c403d409070520700181086240a001500c9000c42452007d805079002d000341d40407001e454080180e22482c00c01003101c240c10044c0440201d06c050002448500400501c200b4210300d604030207422540007000682e02c80341d1000c0f006d0565400d00d03041103a176842250042052610079011036180c4c0d9601e87c1d00600700c40d500c000c1c2c03000c0c54000c00e002c01c50300c2d019011781d8440440014000218036940d0315441d401c485142e4022600d008180e01038000c410a04d20032a40242494006044c1c2c0d40b5001135003440005004243e0418141d07200081216140b1036015058805030722004c40380c3d1004a402d0191a5800c03d00c0200c0000c1d03401850010806914000c03440b0503681a11005183e00ca40c00410000e50002410036412584e1100b02e030080140c0311880d01c3c000d846c840301410300e038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933620737 1250 933619487 933619513
    0x3030e0901090e0a1511030c031e0103050a020918030a2c0d0b2a03040c0518071110062402010c1d0a03080a03050702010b0f01020a060e120c 62
    0x40c4142e008151031807030b00c0c550202d41c050104402c0c8440c0e030301030a02011420741c1004540100302e02200d00c500044084200181540c1c01c100550052900d0080402401c1c40b29400803d012400d02000f000ca800401d010740c014104540c05542044641210150a089260801e403940d00402100000210b41201c1c5160700510000c0103081c030a0303000d203a00d41100c1118007003030b40240d0103d2300521840c04000000c41c0c507284403103000c51807080c02030700808416810b107480d2103a800a5a01356050807020000003441e151440000c405081c0d2018161090b44e256902a2030000d54000380c00c115006122400c11520b03054485c40340601074141241199907a445001c00070032506123555029a894400c0c1c00c442d041d003000441c11044640c001e241e06180d90b1304042001d41002d035000a00e590300c003043c04921140c16400c43c1e4842c41c3c031a070003004034821039010481c02e0109402c0240c0542c0040c801f03400400d43e10340241c5030b880303615401c030345a04406e45821000da601c010038258554100c10790342056 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933621987 1250 933620737 933620749
    0xa0b010506030c0901080903070c121106041a1803010e0a03120c050301050d05120d0504060e120f0c1e0102070b0714040e0618010e090106082802130603030e 69
    0x548025980281189030520f450721880c42404032990601c40c00340009100e00004000f11500e6a074070500c01c500069880244c1c0c601e0090190044030082c10341480510581003a0381500c0855400c17100d1180c200b0801d01e400c10441c0e100382d1060079400010500d04070782e030300d090090801f1a11110000c1000344100c1c10024403102a1004807607509050480c03030040c180e4804166810354408991380b50042e841840d01c00d00d000c2c4100c00a10702094003250340c44d44012030340e00c00c9204030300420060140c65004c50042d51a85012040c646031751400b8031050718401507060103020000c3c003102c212078542070140358402203891001910303a07980c4c0d000035006040040c44000c140d0081c0090501c444505002c20003003065000c1c81c0210b04c40d9104040020b07681c1d079203217910b00042c500100351f082d240d940c59170400481400c003103482d00895030920f070001070340c107100045601240703c440b0484010a0f02d8609980518241031200b030ba4002071001e4180041e41c00da100e000015440381c0c91f849051603043c424050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933623237 1250 933621987 933621989
    0xf0d0608030c1006080601051513140f030c01080127060b030406150602030304030507080f0309070e01120309181b021501060c031d06040b0c0a060609090c060507051507020a0b01 78
    0xc0e80d404c1080c00c0045c4000000c806054034801c0b110355000e1042800c0148150240603801c0480d210418000a0540e0447e022103525150640310030441d00f5a680c14580e4a404003034a603400190224010421a110500d104081c0c44244e0034115151000e02003e2040c0c03a40354001a000440000c288410041b45110340d103840040c034002154814900403000c0d44a00000f40041c003441800110030080242100848825462142c0041d45900b050003a603a5520018012074882c2c0d040c0318004183c50410902000302c003a45681c0d449000d60074200b51060405440f4040300300b25894050418010044002030050700183e81d0040032400c00e0500b4042203840103900480510894070b0620011952081041d50030501210190550080d40004a0074520555110341020080843c0c110002030000c43c8a1301010f000e02014481e40752903003091804c0381d007a108000c01041100e001040318174050310180000f43e0040007964030303c480c054015105071408607071030401a04a2440501040700000c8070301c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933624487 1250 933623237 933623263
    0xf072a20030604020607110406050d0b04060f0209030a1502160312110711091b04090204030317072007050d060f05250c0c090e1e010c0905060f0d0608030c 68
    0x4020b00f42500460418402d24a000c1c0410201d48075110854846400c90002441c028003e4a000380050821070754001060340d00310341c400d041c01204e02c0f40003524025220007000081c05054180301d1581c544095030f48102010001c280c0a0121080542c241d080d90f5001b9800b03601c4120403800c00403a8442240c1030007140013040b01060080c100464910300301501c0f0300c1c2050300e014201e41c890301d0590042c171050703064141820200140100d022012a00034100700c1e0b1081d100c0c1c00001402d8010300208010481e0910001428884041081c1140340c0e4412000008a0161002c061f15a004203410990890003a140d15403103070b86818a000704c5200c0c207680680c040c4001c016110910380780d48101c200c00c0c1914403c00c0302c201514410311003402c8100004100e850410031000c09032205083d1501011404007008055040600590050600a000a050345a0f0742c00d10058108420401150802904254081d00600a41030200103034414180070b088440000d40e00c55101400f40752078000006081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933625737 1250 933624487 933624493
    0x10c05040f1a0406110a0204050106050d0617062e081b0105031015020106210c05060304080a120902040c03090203010507110c06090103090b101d0f072a2003 69
    0x42d240720b0058806880c0b1031702e030030514200c0b8070000e41d2030104c007070750040c0d8424541400083c02070742140050208414100f41840100d075103900a40e4910300138010030802e6002074001580c0302e0030340548c01626180c1030307210700709914001882a600c40ca19400080540d400141e28892001c8404040e035235024091030103d15510340200e039400105100e100307900065400045414005000707400140181050351b406401e488841402d102d074038001050141c40e010f00212021a5900b005004c5074400c0b60400a942c0c40c21031501e90445400811010040501d0382d914500e5005a969020b01001540580d5021403903040600400d401c503a40034041e8810702100c401c8101c201c9201140004d9803400072545541c80707640c0e442c0181c0c050024400010f000030284000c118002c440002c00c50b069034858550303881d0400c1a0740c0083c4ea1a1030a49a9480389a44800025076581c400d030450801d03603400814180388005940340c1040e03013860303005046609010290000c42d8903042040051000c00d412401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933626987 1250 933625737 933625769
    0xf020f062101052119150218040f060b0f0a02120403080c0c0906030709050a0207020a0b071203050f060424080c040f0c0503270a0f020f01020601030c050609010908010c05040f 77
    0x60f9580c10800c5c110170004421000e00000740492903070340000500d448041990b980132000502814951035043c2d142c840c624180c02200404001e2055000b5501b850710407a01c2e10400c10030810b016041f40003c00f0031131040c0380140ba000e00240d40900000c40c4554041034440650f0b5a900e81070821964405001e00320040812409581c005080c80c120303071507418006070301c0d02c4800c0030070041d114501029421903c03d45c000948911f0300e0b4024403207280907824144294a21180490035540265174500d41d800380d0303401003031040c80c0c5030344441c8014414810441c0f40915a60f5120b0042940350302c050660b41015600c81010b081078014040daa030200c410030070054082d49005409230001410901d02e5070030b481318100c002203c40b640300800c1c84194089038141070041c0340c00040c1c0071091004a000300c014000c1c072a0207500010b04203050365404144111402c0c00c05040c00340640180781403c2c1000300e10100021601028031035510380300400c0e41c880760b403203081c05061918284581e0000f401541c02e421 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933628237 1250 933626987 933627049
    0x818100e0a06050f13030515090303150f0f0d0b100b0306210709021204060617060a0b0612150f03030a080109020f1c14060d0f020f06210105 62
    0x1000700c00c0e2162070a0980c0c5a40080640c1021401948000c1820107040e460200a010000404c490482c0c0701480e81c0c0f905580b0703001c006449010079281c9103a034002e42120b603211450800720840030b10740c018000d01c5030384017440c0000e000c1100b8900d00b6268030042009003d0b000000b801c07554058406810303103034510704140b404034503001e00d909280340071011034000707001042d1014000440202a481015912070001d282510303610300b0103a0301100c0c12460300100142c0151a520544403c1a014000d080d256031149e0004024008070350109a00c0201003041170881841c002c03d50340165031120380841d4015850052202c01070390549240d109038014401c500384c0d103910040307460660b2442c11b030245e1111013202c5117115a02801d01141982403140324a40900a60b69100c00c2c060609280c0242003a04d0301e13030074420050b105610240a1101c410300403009420001c00c41e0096190203828a4500713403900020004400e00346005901680f90240100807902d06101146811030b6102a0820720780000e607 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933629487 1250 933628237 933628249
    0x3210903120c0c0203030f0a170106020c04090305091203090301060501031803030903020a060f0c0e0a050f0103021c1409010b0306161b150618020405061c02070818100e 74
    0x2401416102e488040b0703901c1143c41441c1d101603896000c4c04481c0c0710302100340c540226402c03070840c0038000754401442c802446a0a2003581c122481d503000b600d001e882030011700018080040f02034042c001c1c1004403100507220001424000111100595111a584810142076038600d60195040500b1301d000304001c5d103181004061140d600d41000244030741e0b84c0c03406900707100120300042c0520717191640050503030500da004041018007942d07840d4400c4040c0e1040140d03144c503900440340c01070282982d03048194000e0303004082c0c801200c128098100300c5081d040b0b0950700c01030103940270609403406000c81114240699440323024106c000c1c029620f02080c2009007105821460000c001c0c0c2c142c01c3c800000409281c5003d40c6801041284001d422000107801421280c071030515141d00c1ca14600103440e03d14801d8400ba40c078020201031405c90035943c104000c0b0b1302140c809512660800c002000541b002c00140507a801503007400705c81001d20030801c0144c40005040405200b400042d60720ba503a100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933630737 1250 933629487 933629507
    0x1103040816030e150301031a0c03010b160c030f020306070c0f080904020c010501080105060a0603110a050901050d06081609050f010605030a06080a23070e04111c03210903 75
    0x1c604191554030503080840703400c0304118070715401c443c0e080f44040003161000000d5060364002d034908a5000340c85201a02d980d07100301c0361001d48440600040c041c10f03c040e0020104100b049115513101500c82d00d130080c030603040d50f01c01c940307a0051060400c02c42c00c1c18002d00b40d01601c107007008428108140c80b07002c0a1b2005040c0107103880c0f4002126182c603510356060b100742040040081245684902c1128000d0505450051140f44904000506c15210b0b006901c0709850310900d032810401443c2064405030807211542d4180802070002d4080c62440d407095400034a4000000c2121110f020b4030f0f03000b003803410381081d0409810310702000510b44c0340103103c604549d010300c2c01c199203a5400400d500240700c160080d00c11405400c24100501c13484515803000c3c0e1400c00030750765400080e8012555561300c1c170300c524148032484600043c00701d00340004d840201d240140103141030700e41d20240e00c0c820300f100100c1100803608000b103030503503039000380d03c5860850f2030580d0030040c03c0702a44001d4172210781 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933631987 1250 933630737 933630757
    0x10060e1f050d111b0c0f0303041e0e0a0b04290d15020a0507060c030204030c0b0c120a050315011d0405060402070b01030b09061510080414030406020703050111030408 73
    0x100042d00c4200050341d60040c8203000d000300185495650890130610702c90307401c0c2c2c49032009200d0ba919034806454000701e50041010010019071600e0f1034806440e089403084003066803a40c0300c60a0014250b0a040009441504c502e42c1c0002c9101401c410070048400320488081c84030012404000c80c034400d5900303400c07075550403220307007040084030300e0f04284080c034000068161740e0020541114581c0c00c000600021031080c0c0381805215035990080b801c034007840c403010701002202441084818521401401090300c103100751400300f00410002c0019a0002c441d201c005540041000942c034844000d5180755a400d182404803007421450301203404401e045500d00c02c0f603551000c030780702d5515541100c0d40c05510160000381d5681d04d0800100d004411a0348074020f000340301c009511702c40524000a05084002c0c0401d03038200c1c003107100710b940c0900100100c8202c100340e15220520203081020b00000c0101798001c12405003540351071403d441901520040c20743c410b00a1100242c003010a960440d09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933633093 1106 933631987 933631997
    0x4050a0608090c2130210114181902210f0601080a0c140703020f010905030d06080c0d0201180e070903060b0d050a03110f0610060e1f 59
    0x4200c2c054101c05101400002e202803045006406e801015590684500f804404c0e1851180d40032380120603507103c00141d2611610704211816000c2000100c407450b2800e000b00040180600c40c108000301c15004280000211841007c0768064000c54146807450b0824190703801d054101540da0300d000070180c0b000a03207858924000c56020280d99510890801c90346941480c10b03801018044045010341d05081000a009004800c032640c012405195542c0c00c1030720b1201203581a80c00101c00707821102084403242e4030758001003a503035020309142c8084625083d82100082c220342041010b00011401c0c030800c0b41c1c0c4000e68800b40da21039603003000940011020040780c0a001ca0004016500c0181c07400006441045460b02e90000b05041350a4819101101030600c14101c81c0080c41055a01081140c59031040c2c88040084080d82c0302c01d02107440c0c04c104d28101443d00c841c002840 = true := by decide +kernel

theorem cover : BRFrame.Cov 933453237 933633093 := by
  have h0 := BRFrame.cov_init 933453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933453237 ≤ n) (h2 : n < 933633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
