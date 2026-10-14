-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:19:19.059048+00:00
-- url     : https://prove2.me/submissions/73080e6c-c07f-4080-9f4a-eb5f28ae163b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201079136 ≤ n < 201258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201080386 1250 201079136 201079159
    0x70305010510080411041d031c11030103120810090504060c030c0c1e0f021002010e011b0e1908120d0f060834080a030e0102031602040203100803041e06030605 70
    0x510024015480d807a45000072428142207a400d03090002d460b45218a080c0c100448609c410941c040e00c002c41e08642d680754081004200107503003000c0da90704004480c100164190380f1101031800c085241d90001004d03e041204010070803c0a80c03110300d044145ea2010400d18803007207000c450750058494001e1514201c0c8011800c1206401c4450108a10441899020610b035030701044106103131208500240c1e46504001d02e40b60300078000c03403101102304150700c2c00c15001c1f10b400034130f0040c601400d0b600510128281c010002800c052280c06040b8810444034074143c0000c0e507841c180e000c00140a400c602d040d85c0c1d102c54100c180181e4040780c3c407540003400c81c0c20702100d904010361121050081da00f0302c8a01201d40c00700c40d6280c5000140480c80180c56102a24200500222070041c4a41d046410422103011004c0012070360443c203a8060358016281d50354130745181048902c83d00428000e03c80400d0000700b1184a4100c44145644001503403545070340c800c016800e440e010300403544d02000303d005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201081636 1250 201080386 201080389
    0xf0702041d01020f130b030403080117160b07021302040e01030305160f0614060102060408190908010f270b040f02030a0f080301050a08030c060c0c030f03070305010510080411 77
    0x4080c120100410841d2004005003509007203a01c0840042440361000c1042022010014003400052402900891070b41c580340d5002071400105008803542c943c045040940c08030030400c0107560140d1500000c400e00c82c0ca421a040035030300551000c80c4140c55044860100c00710a009990444d5002108907400340d086540c20345040d042000c0d55000c0c188806600c602017080c02c4a44442e03a40100d41c001400c030f007202806103081c4c0c001000241550700000a1000003400c54084030788a0001182c01000704c0039100041300c109400f41d00090166082250a0401c03403003551101854043c04003d0035210a84100c0000d03c0000d42c90000d030000e110180080c020074804c2e52030506152004040e24000c11069031080c0b0031941010301a6030034240400180034500303001c2c00103000350110f900110309100204030f900346d50b0480186001c407158008503c4c0c0310030100070000d64850812840c51180c0b80c0c60000307002802058244202841841c8554814901c01d0041c03040070f008070b40081001c08030110100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201082886 1250 201081636 201081641
    0xd020d170d0204030c03110409030f031e1113170706030b0a080d0201090501181e03021609020a0e01050405031902030c18040c0503120a0c03050f16050d0201020f070204 74
    0x40c144a88108204090010400c20784001c002440c450700503a0b0b462415400c2046c100c2e640c000f4118011443c0100341d4000c00c1d000041c0c080c0040c103524000c9001020000d4601801820381103603c01c3c00d04190560306d9003031180018103101414411003103500c80e07440c440c8040c2900c44440c00c803200d81001c401800024802d03000610810030141190b02c3c8948c1e126003040c0f074191000c0c810300c0180d554003400820003200b805050000784400b00c480b4100341681d2100c440c0c000628207080014180d482103042014000d00c4403050b200501c00680519503542c03103540001c0d500a904440000c0c4194031804032560250b801d1f603041d600054000d1150108080100585080b40c500581e4140710304c585e007003003a60301e81e004080581c401e034000707620320308280c5400001d0210b01c0d08520310036080560565120900c44003038460185141ca003140e0782e17607440c1c101668140708142c46003100e8070000802d40181c0105418080e81e0f94403801c1104d29100d401da000b00e080b4001e5007401c050382002044811302518154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201084136 1250 201082886 201082913
    0x3050103062409240608071d0f010e0f041805070b0a0f050309010605040507020c04050a14130c150c0302060907050603010902091c0308100902040e070f020a020306010b0c010b0d020d 80
    0x8500c00c002521343c4414010443d0402c2d80b003040050b44a004014000b41d014200001400b45545000403035900f020010b48414010207600b4100b01000b41c2651165a0f140025242c4913800b400030031405091308000b1514080003082514584241280001c2041d65a021240e418031181d41e00f000300ca242880440e00b660000c0e164403070b159260580420260384c0e500c6014000c007043d400501c80d456004c010712042c0c60000f0104241945404002144414030074071003035204008001090843c103c070320301045400d4281e048940100100004d00300c40355005000031540138003d400b1034242c0d9466480d265660034940c005c850f00301e64203100401190300b0720380280441036001880401780703141c0800240543c4140050a07000215540c052146095140c0959006041510801c0d440e082c00d00c41c814001d500b014004000708803200c54a0a5207502c00d0141ca410a83d00506461255a4440c69802241c12090956030713607510b092000c07285440c001d55a020059800341281400880a4441c02d5910111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201085386 1250 201084136 201084161
    0x30c020111060a0b121f091703040803011a18010e0607080c1018030e0108040204021c050f1806130c080703050703150209010509040f0204051003050103062409 70
    0x5110807501014103000c29442036010300390000340042035001704810400e039800c0e05e20094115400300b48003080400d00720000904600001b0819014625013007000010069039524440000b10034002007041c140f00a504941c1034030078082200200407082e981c2071184800c4d074240e0b20b444450000b100d502890150b51500c00c000c2c025414460a13444c0d040a942c0031144640d0350b40c024071a07547c207140c9140701700368100030b0310140c07a0803500c2d541d5805014640c6d4100e8650520200c240003404542c0c0fa130301103900d00000e1002c1400c840202d442100040c1105540c0d4a80f9001018001000c001200c03141107485000d400062802c1d03183d4040d469908240c1c0f003001c0d10082c3c4031810129031200c040140350000c610500c02003000034614100640114070f280d001e944000c7c0100b040640030b070707800380681d05411030485000a40400c4c2c943c103030000348102e601594025411010030000d498040c1d1269041728001d00341404055450311000e0002001c207501c5080b0032141031410303c0700d10b02a50100040058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201086636 1250 201085386 201085397
    0x60a11010b0301020a0e03100912080c0708071101111204060e030a02040e150a2a020c0405070c0c0503030304120c050c030723010905010210020903071707081c0804030c0201 76
    0x820404207003a030b485004805e002c505034641d0181a81402c0100d00700070601c4401c00c0203441440c0d0313545940c1c2c10083d030b840b10810000c3c0d0003083da025252411200420b911040e2165255075900e401c142d01280c0150082c0801c000402c13a0f2003c22001c14950003544404041d03900e8142019400c0d1a038512005181e03806104400704100113032143c1c070035860845a03150081500c19441c40206002c800c008048090090030701da400803421403c2c24401e00c4040d000c840000360303040d203003c00700d02e06171000c0702c113507445801e00c400d210b0362507041403000003040e00940051242c1c9480e4002d040e074906c07040c3c2e0000c1c8115109000c116840c1e02c03940000d82800e11440964102e030b84800b001926001c030780d8200c1415225200a81281d03107038000d01ca4105030f002801c21600d00da2074240082e48450ba0f0001c040d88464001032002d80d1541c3c240819006410b000c001503d80540341552140e440c84103010f02846072103480c201001c0500540382c000315512007640d9a40e00c41e5030b659000c50b14000581000c905120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201087886 1250 201086636 201086651
    0x30d020d0603120503062b120309050607090602070905060f090c0c01060b13060305060d12050904060b21040f021003111605070506040f030602090604080a030908100605060a1101 78
    0x85143c005001030b40741c1959541c2d02e0b41804410040001c83e1714622144800c2c0e036088402e48242d844001c966a02d4000000b506e0807040d40c001900a01108280102140951020031801e941c005228105541d00c550032034135a580c8130041034088580a680e200e81c042009106004141381070618268859510b6040a0520300501101400d403204d0380c02c0907954040104210300c02e4201074070040004c01d1545020711070303414000045030780c2d40000c481c083d01c1801205102c0c80c0c080e000e03d0441e050020040d0041010071303138407a4894080d811400c080d00c0c403080c101088003049036030003c80a00480e0007040240724002c0682c02c00c080c030401820124145911003004c504599807541c094900d00211060340e810103103071442c19600304059600814820302040c1700c14405045500c0f0f00d001030f00e40c410385c01641e410072940010142e01559000c4141e0744602643c2d8403c0542c071520140440d034040040b01c1c0350701c5028080d803040c0d9603e0b006203500b00c0720030320559000074490321081d00114454400025900c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201089136 1250 201087886 201087893
    0x30307090f0b0408120f071a06011d06091203040f060c0506010807060f050c0c0402070b060a060504081228201b010f030605131d0a03020604031107050301090c060305061002030d020d0603 82
    0x60100d1108c030703814000e49404010103560488105114204c503170700b1401c2e080c01c80f90006242802020150f42c011031010816800000c810030480c0c0c0038002e0703949010301d81d47e6200f01c020260410940e0072640c0b4001c2d003000040d0510009885000d4950940794a2000340f5036260440d100c0d0019040484280315240740d2140a40301c910050000318001e807043c0d4406e18011f018841402c0c0a64400010050108010000c140000c47e29980704500c080a01c0d44d1454400c5503945202420b003407090b04102503c803e807003580d030420402180d085901c12800a0101c440400644031680003030701521140620004070302d00e6100d440807440c5501107013800035030b41c2c0d151008500045400d0b00b0007815607640d20a9072800b0b43d601480885c0c442000c0b0002c00590100c3c1d5802500d5810182c401030131310620129a44100310180b150724050500074000f0031000c101d604000c510320409100b44408240341c0000704502d406c1416040340100038070f4004500d0190043c400000960214001c3d406003940c030031012000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201090386 1250 201089136 201089153
    0x30c19031e03031a010203030711030705030408030a09080a0b070323010b13050a03021309020102030c0303070921022407080c010c020d1107030201030f0905030307090f0b0408120f07 80
    0x1241d072680a009440580d4a0041d08484640c18001505422511078014681c0d001045960040300d0303191024000d00620001741ca1130240080040c018000400c000c100c590001025201c1c00b00b6540e00c043d280c503981e09055440c0d120980d4058002410306c0d00040501c1d00a811100c01040c102d180065521010180c1250000d001c1c0c02c80c5148480018200ea0b0710303401241c07100c02601040362040009482c55001611084071003401d0301800d0b031160074000c15a0300038000d486100070140c0075030b9a6458034040c000e00403038050003103032070300c050f00304c0000189002031415080042d80071340f00c111504010418070004602200c4e040c1f481c0316040003d1400180541d015000388420600045124814041c000e400d040100074000204032003010202e01d550300000c0c6a0084075020308000884401159900001d413240d80c0002d4483e01c07000003885501d42d0b201d043d00007260300c9021480d50035a200e190101d010b10861144d50744a034022402d800349200010001c2c1020720003421450329164099640008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201091636 1250 201090386 201090413
    0x6050403111501030203060a1103060f03210903010c0c0f02040b03070b07030503180d090b0306040603060911030c0103050c121f03050706080109060f031101110303010b0720030c1903 80
    0x21650740b01d400400840c2000c210054201070052818411909440700032040c1d40030050107140300d0044c80c80304420301c2d2010304c05c41030000d880c11040b03d40d004c81a4001822640500c04080c043d61074180c0c030900051240c0c9036426003650000c94403c1c81b05454003000058076030700307940c00d1b814001d4890000b1040c500300c3c01801c50a1094840f80d440b46445d880201503083c09204031034032a0001401c4d0306195602c07104641c151220720030101d840c1c1d1100d0002c00c00030702c0c0513000104440e18101031001408550141022407100440c01c40355a89101001101551b0041d0358a01c0d01460501900015407681c01300c29a00885a0300a085001484c2d1441c4582c0d208a90081d00c250704403010a00035aa88080c01714050240000144241e500c0c041c0840320506007444060502001503403140700743d0380b288611100540e04041240d449503181c03c01104c2592010408980c24025183c580a8035410608500d014040041c040c00d40c000d202d406120325070858940c3d00c0c08182d0420804000590442c02c800c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201092886 1250 201091636 201091663
    0x1211030f07080c010206010509060907051e03070309060c0c0c0b0a030e01050a090b010b090109060503060118090b03011503110103020309030c0106030b040b09030310060f02010f1b09050a080a0605040311 89
    0xb18507803800064100141a00071278003078240c5104109040c1c944904098200344c0d0303450001c2e500c04c4076118209038101030340d0110900800002c14032288940c1340e0070101d41c10340540c40410400c0404107007901d0b6948081e10042c03c5640340c40e010807030900307190080c03d405071040c140424030030300f01c200c15404c441c01254100600d542c2d8210b12801e201c24010710318050140708886a10705010b00300080c2c21190140705810402100100083d51a48a40751500000c040020740b9094103031074682c81c001401010000600035843d014241c54602c0252040340102c2c0c0d0085425241c404962004502a5000030103d0174248010421103581c0d036024803440c801180112103410142c100361400c0340346568042c12014207984240280503001852251003011200d40d810704198000b0604426070162145803071003441d03c0e02e13007100720010102684080142c20078503940c03e00007548a03000c003c2c28800758062007045a1000000400040850384183d8215000b0b003002079841c0d80c10100d15250660308036040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201094136 1250 201092886 201092893
    0x50a0504050106060507030203160f020306040f1205180607050c090f0108070b03061c051f06150903031b02010e0a150e04020a020a021c050f0601030c05030303011211030f0708 77
    0x1090107400c0c410304014180903d03001d890903000341c400940d680660100c0050600c04801c141040207000e076400303516203030b000d0180d840c5c914040c14070381040241200c054800416a040c2da21499220b00d0445515005450099407000080340500003d0340090034100c1c0c86110f2001c0c040d507942e071008107443c030480b4400880442981030800d61800c00a1540c482c040c90403003401401120354070850381d8001345941058000e81079609003006440c00003202c013080078246500c0710103042c04007590030850907203401c510407200721001847c04450303a840905c405000502240e0340c1900e80607030810a0604180145003d0480c810310390300094401c0c5071540007001210813207102220541d0409a03d40558408507000c50600000030400f07510f812903464024800c0224800c1000e10341c4000c403824031419004001c50f03500340300000d01a680c40900f804140c40c110003038140004c280c81d00000301c82c103891143c0101c014080c56696500001410045002d50501504000701884201000102c0040c41c030407009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201095386 1250 201094136 201094141
    0x6010c0311122a1513150e0f120403052a040204060e0112110f09030a05100501030201090816050609040b040507020123040b060d150c020303070305010608130206130504050a05 77
    0x1c00c1c100e40c0b414035040c889400040440000c480013016483c0d1000000e0003800d81d00180e0301d040c900051a0030142582c04e032074044e101e11100c1c400540042c81c031104a086606e040c0259003800d0441c00355200082581c0c1c000d90383d0f41a825000344820143c0c010750561005d081e1203942c0007c050741c0042c0c1001c0d0000d520359040c2e4200c0d41e03104030340c80c1050001400801506034100022809031141c09901410040300291070209034404103c0c43d40d2040c0c004055802c0280c1858080c2c016000c00e22080e07001900303c40700440d40010101c0d08403604200c030341d541c040140c903010520002e90807494443c0d90060ba2072600c0b01c141d0302c0d54080c01d40300e4030242d40005022010340070074440c8aa4240003200141094004000c0004d0041014541100c000c0320518014003192030301c14100c0c1d841d40503504126060415680d81581c000003c0d5005921644040c4a242c5e00c1d03800032100404116080c0e800744a100c0c40c50320141c00d125004150100c0080010040203480d00041001d42c0c405a030285039180c0e44e0401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201096636 1250 201095386 201095437
    0xc010c0905120705090613020c010b0901060f1205060609060c1e030702010c020f06071a01060e010c0348020f090105090408031e0403020f070e06010c031112 69
    0x26000050501142c1d000c103516140c05640303650322028002c0c01e0080340b003180407030703040d644103070f4400883e120225080d540d03084072522160290814007500307401541000008240d487c040d401c010580c1445658943c8070105039548080601405400030703402c030b8000c0001c85c3e410740ba044010070075060030b5030040600300040341a111212400e1132814025800034440100140e0b400004204519011500c1141c04c9007060006440ca2148103402401c140010f0010b030018007403180828101c079450349071244072140000044d510350803070f0540100090049402c42000c10f02c10028180611013a01c45800064a4412070011404101559200d020440380e402c00c1103103442a06142803500940310718260307514050200f0550400074000400e009004400500c81031440b0503581910503049088901904160502940300e4200b42504240f600404001285024008880707a02400060b59000604185520100d030b00c00821504c070110760080c0003450712441c4070000906007204414541c0705a4001108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201097886 1250 201096636 201096647
    0x160503090a060527130207030c05060705160b1806070c050c030109081207030219120b0f09070f02071e17120904021b010f06090c030e06061903080c010c 67
    0x74030074410010f0400503880b000400d80d0f85000c07201d001d640011202840003000a01100486480c100a58408908041490751000c2240e031800d00072030544440e521130344021100f03403080341c7c40980c01c4d17070b81540c1001c00543d540b812154040307510b80110703100c1440c1720304a9041c22015039070b46001500305603940b4107210b41803158890b0244102e000b044912a01da4548403280944207030070907500300000c001401c150107601180c6015484481d1080c0826840d080501040d0f0080d842440d070743e02e400400261820600541c0c51200c00003408050740c0e41e40c3c1241110722544c140404c0007107015200c40010103030f00c0800d841180c0010070018040203410f0030548441d60a80c6511038000358000811001c484490404642d5103190544025907640004403120748038000d50183c0c81c54640c6045070100c00c02c921948100c0c20f40b030322220240f044010b460412001c0d2144100c841486410900c0481c90714640b6034419011000059000d005c1c00d41c0e80d4a0311a0541c00c449030221040e51110002452140c1c0b15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201099136 1250 201097886 201097889
    0x1c18030809180f041e060603080415031401090203060d14010c14040e0106050d020f1201171203151f0e03060f010806060108180712020f0a030b1b160503090a 69
    0x5000c409883d120360180c1c81e41d54041c00150025810303118a92607141d030000084080e640200040c40300c0b99883c6421805544180308844200504140c4410035501c40d014082d101c0d4441001c176400303079082500340d1000350700161000e9440103811007072600280d003034058240c1c200584c81c00040c2650302d106e0301030400e8414a211911040b000c020070f00500190070001c81c10b503081c51910741c0d200c03850030f11040000d100d4858071040040d00464001c0f031842c84000c00d181603800c145c0c4083d5030301480803c00da82c4c400600108040d2000280002036a4607508012600590001043c00c0c022124140510050b81000c00d080300000c0d010300d0700349445040c100142c0d0307001030407005520381540c03404c0c40164036594003400503410808114089040001c070101407012842e11407060b0b56465aa44610307101c0c40100100481c001c1845a442d95101d00d0b00c183c05c802244d410094104590f600d8a94902044605d0649000d1060041c0030b8040e0700d103480303044110028403c000031903a441814042007400b000b103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201100386 1250 201099136 201099169
    0x3010c180605030405070e150d140c03030c0309060903160b0706200301090f1409070614030c07120c06090c0801150312111504080406140c1c18030809 66
    0x1081800001740f4001b40303400481d0400c0d02c4960481d1142c0300d4414010000780441070740081c100c140401807241043c1e1103610480c080c4100c41002100205150301c900400811100e1600140801f43c52810040000d01c1102c03402020786100c20b42d54422444a0b074181e411074091507031f02003208c00c1005040d100c0c013641c0f44842070740ca00d1000360200358040f152205029108809031035402c098260348094011000c1c03c1e05603240414240b42518034076030b88008601c107200001c0c25050b4010850000da404403402441000d1845142800039290421982d514404010412010100503800714105211f010049841402014081031402c02c5103402d496410840360b8080e4441d440410000c1c00310000c4000c000014280009a1500982000e0600d2030545400c2d940d1212442004108042c080003002981c00316107426025501500f800c403000d004510111105610048904050100075854500010b58902d80042039003000041c042c14154030b0350040b15140c2001c1a15000b602c0c2010403403030720900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 201101636 1250 201100386 201100397
    0x1c140105011a1201030204180203070303030c0212091c0203100f0f06090b0108010306050a0216050102091903150f0204091802091608060f060f0705150601052d0903010c1806 76
    0xc0c80f140c807442541e010312000b4401c503900d04043d00801032a0221240f62500242961041c5640e424060301030120300c800440180105954102c40072100016140c00d504090b005142000c8046055000410801c0050b40c0c03500c200c5081c0c811482d400c0c020054003516202020880360003400c04d08060304c200350000ba5840e400c01d10700149a982c00040b00381103075005400440d05803101d6118a000b4410311040740d1003080c500814a09110301500208035004040d00d5500b040d10500d250880f684605000041c01414503015075000005183c2150502a10a0800519250b91000b03158200d40080e6840d11803041880b01d06015480d0807104558000c2e80c0b5a100c401c1000c100000800f82c0300700a00e0507204030598214030056498100940b09036220280400ba03840600e403d000d070f9128442c8124425a0020000040030b0794403d4041c0da02d0240c0352400e5290307940c060300b42510403070b40402000c0e003110348c1441740c52800d5809006000700225561500d20082d04141c0702c0d81c45601041e0003040a011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 201102886 1250 201101636 201101647
    0xa030b1908060f1f032a06050706110910020d0207150504091a0306010f03050d0f0c02010e040b06031008010e010606020c090709030b010b0a170f061c140105011a 71
    0x104003150342c42d404594101040156500c1d078810701c0d0712410f007090002d54140301c0c09021040095501220743c40914035042c5402d0405c80d96122001444180a4580081c0080c003028002600c550844000c10140034019418055044042584907074007900b21001030f0300c10050381000c1da8050242d0000740c85007882c0103401d5110204003504ca445a841032211456861a50403804a60b00c000310300c103003600800f50f47c03040d40d403401e038130324810700d24041503400f805000449281f290180d0106508502603403a4014404442e400554000814285440c0c01644445a60b12507070703924402144110001c5900880c02070a165000e42110350300d003900036040e0304d851070502c0100d4000501c40305400d411038203141c0a5a85510844001d9607a0340001c040b00304550020445031020f10207450f29030f810b80e840c40c041d039010340d0f10f10030b182e0780540b41c0c48800302004001c516a42007880050100710011072124029074440c0d076804020001030702c1c0d204001d0b556880107210780074601d0640c110b030003a007200381c43c1082c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 201104136 1250 201102886 201102899
    0x30b011b03170c03181b2b12030f0e0a020409050f030a09050f060a0903060f090b040c030605060102060c030f060a0513050a0f0213050609030c03030a030b19 69
    0x2406006a221150031034103004201071181c0d000759403034540b07407903501c29504060a491915400c255000321006003c1103104000c040009121024900c0034000640003a4550043c051030650500f07540c80034215405112224002204e0f5115030f040c03144030030782c0311000142802811030300710990072402c4a05041040090500008031009032580440f800a0141c1c0c10f0301d0301d50718042c444030648070140004280c0c028401d411000260854205a5450004a00a504004081c400d622100001c03404038201030010510540c0601c0d0444000c1c000050250940d031507440c02c0740b80484045418519540050041000601a042d00a07100380010b180c1401c1a101908203400010f10049030fa41021300002d40703541c1c80300220b01c01070001a000f800c101c0903000444018020840340b0180040c01c051710309031442428402c079418003031090f43c0f010381d01d800c00301000519808500d199074140324808808200d640c0c00d00041018181c0307070714000f404103607203800c0c4070303101c00d5000000680885c03000d400c0101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 201105386 1250 201104136 201104147
    0x8010b1c200616030e1c02032a190504060e01050d030c05030c1605120604080f03090c21070807052b0209130c09050c0306011115010810050603011803050d06120c0510030b01 76
    0x40c40203203182d260b0001c51009d0104814002c01c4890380500f038502000148010403841006a4805840030302003a0b4560300da00400729400e108140c4c0146d09030074203d022900c07134103540c60464032940039a860304602200c2c080c03071b0401c0044010304210002c1c10070001c92900400f0040c00031204805400c06180545a032101da025402d050000c07400e000000401e08503050041c400d895034003d05080403144e001707040d440018100758004210380700d0200c1c0440c1013800010340804036000184280d41c52400002c400c03550315403064040440401051400006942d42c4aa43d40326030084010100941410300300703580724100541c0300180c21440d08061100e54040c0c0e2048a61061003820f00d43e40a42d400d48403503140c05805c5034050385280f85000045540440400c0e40805905410b41c107028a03210305080500b240c02c5500c0020309920400700110010380030f84054503151044800c00551250764029000c401284e044045841c002c0301d0f442480340d882c050601c1040300600d8501008007480b1040044e26 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 201106636 1250 201105386 201105403
    0x9090e0a020d0312060f09020304050d02152a040828030801030209150315090705011e080c0720010305071b170d020408010b1c200616030e1c0203 64
    0x4020030443c0040d0911080e404c500006c049101c0400541503581c66084029001510111454001c0341c07001d4409520020b0180380c50070028603480c40c107448403070044810409010b9100c4050f03482c03910000604415402900c02000c40b500a0b024003071080b102c0029100501441c1c81e81991501d2101d00800e40c003061540c19a03038162296680382e1201407450107155330b421071555141c0f00305426254204070301d00c400c90043c2c07900400ca51380e1945410041d10a2805010340e90b12400481030309640d564824000780d900540e14a84c450324200198544054004d0751101c4003804c1d071807958070560349507890710800740e00c10060301d070692603c03050880070030308400002c0b0301510340c41002e95130805a00214040340d01c18103028100710340da65130310880280600304c0300002e0380c0310b48401d5080b100d00e400360115490240364450402c400030780c240d114101102d032400c6a80c5402903000d000e003001020f640c000211080d03010b0749800d20095a05403c108008405400c03102948140d60800d00040e1800918001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 201107886 1250 201106636 201106643
    0xe07020c06070f06021c0608070b0d1a0306070201021207080103050316020303160b04050c01050c0a14100207060e060a02090d06020304060e0712060c0e1e1302040609090e0a020d 78
    0x141d0320b411504102101c0180780780050402c52001a1144204030700e00d02d080c0c0f41e180701000510004e0394405035203407030301c0041c03003070030310032081082840f204080d07070b0340029503410500070904565500c00c0c001c40d140c020f040300c04da800b40c0c1d8005020307141e01d921805030560141e41c900d0143d80560469940729101d00031144c695211000c4440071804550741401521401001032860322007201c9682000309462806440695050055100c0d81042c0d51103142103604130507a9a0041682e01c41390f55a01c40003100d040001c801c0c1d0b015100c100840c00c103160004250540c0a104089090741c40141e24505150003d8184201c0074410415003000380c0b101034002120517001000180c42e69103504023030020b00300c3d6a40e060b81034060f240300810985c070501c00301800580903200420448000d0503055800111080c8219408405500480b20200645421a90b5100060104a25003043c0200380d0700342c1e009a041500822150f240910003404548120300001040b00d0082642184580104100d201c0b01346015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 201109136 1250 201107886 201107899
    0x201050c070e090a1b031707050304051003020712080402030d1b060c0f0807081005060306011b2303131e122009040b0a0203070207030515100e07020c 66
    0x8103416101801140002c003840c00300003200f0718040000da07444541e4000100c0f01e600010403841311941d04101e4020541c1d500142e0030fa070038000c420440205400810040744d05120030400072a0f1b41e1196030407807620380035548000d80c072112140ba081d000b88000c10011030402112400708405a54006030709101d02160b0b0510f030003214503040c18100d00d070b0200007000e06214248040d9182240d400441042c1c0d410035903480000c0b40e226103d08895603081504c80c0018008082d00074460344c6810700086411010505046012050840c498182442c41e90000e030395500d40c0c28211843c451918600028560b00c00d809585070454000940c4407000d117030701130210980617171014079240120f05070405002e800c400c010b5088911031032400301c403d55103070710403035032010340300000b5495038185000301900603580b094050600c2d5a441c020b04000390030040981c000c5100c0c0a40010100e4018411002090a0b0718188030451801401000288640b507204c54002c0c03400d2010041c5990f4049251850faa0703044815 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 201110386 1250 201109136 201109147
    0xb09070f03060503120304050d02031606050601030605040513051209031507050733090803062206030605060f100813020a1a090f1c06050606070602040b1c0c050403020105 75
    0x100c00800b03280d00b006401d846842554048030205102035881688104101c034220044008200d0b2603002c0d02c06c030625154500c00c51080060000d8210303544c071040601d000601180c7d14000141511010356052013091024203202c410b201041c032803650903c408a03459490000b44c640840d90324803800ba00c401c00600500040703041d151103171088070f0141c0e410506000d41d001c040308984100342c00481841880b28954618100d2855950040c48541c5411081403400c6950760b0f0240110072a09008042c0588880e11901c081035945d0310a0b0405140038100010315858654144842061072107004c038880d000030740003031014580c4100610b9102030034201500311044684049841116990484034138480d014495862800007600601001e800403218080c9460a038003d100d0030031400b010300504400d4003028900820704be500700507000040501014901496915641c0807600329401c01038850b040043d9603102c902c15019001020020f0380030410030500001d1001d0700304e2203a4840281800001b088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 201111636 1250 201110386 201110417
    0x30b03150c090d061d0f01050f010e0f060d08040f0603060f030b0c0a03021c1b0914010c030203070b040b0106180509040b06033c0102040506180a0b040e04060507030b0907 75
    0x4011203880003171003800c0f0074150062409855201c0d603821056a0340c60500002c40110201140c18102c45020210301155210400d42d8245054000c0c03200741c000e52948240000100d14100620007400c0a0241c9160903042132001030030340b0000e904c0800144070140091010403010050150000b403445038880d030f200e0000c84160040e000c1d6903100b4807548501001c00c0904952904207818000051000b41c0803118800b2055500c8200e5000740e03401c01c2c584103003403140c0b940156a5005124080d0040300d041c548030307607200302905404480441e00c5011420040050f01e41004103940261202d4001ca00700d9810000840d110400c010000341c5401459008a00030382c4040c84040c4180c1850300a0181c0003211041c44880115030340c141006190301c404504011440c1172090301c00381d4a00900852070008280c29a15421007120001741e40459a0380001a044040c00d0090004081c550740079030b050b207001d041084c2101e0b0002d1280c0103140c1400444803043c0c5d51a0003036a4002124141042445228034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 201112886 1250 201111636 201111641
    0xc0902130b03091006090c0804020405060a120606080f0a080f09010c02090f0108060709060e100201060806010602010b27060d050f01060e0a0b0d0c0308030a0b040c030b03150c090d06 80
    0x140440000d00c8000203200f50100b001c80c40d9101804405014420b03182d44403149821165840101030004110b40b01040062a05820903604103500400c540d9010381c82d05c1d02c1a962081142c1c046402c182e85100802c6840d00030f02013050606d900c9806020341102c192901a000c4c4a00b41140000300d100103030380d190303c0c0e0040592201ca190044c007801c645150040801a212100b805006041d01c504000101300c68800c0380300700269286692104202c1c4c55940134442c440030003800c440305654071010003084400080100a00a04050b80041240e01800741408488004d003203042ea0101108829007a034000c414515581161054800c0200400b5038100641820f405400320082e0b542094400140800d05007119801070744551070801491a50384100803081482440003800000c1c241010404103100b03001541c3d00c04141e0701c020a200000c50009000c03500d501c44000c0120f50b07500800041403c0c1080305903a0000c01048440460820b280d403d2558054000c905204203440459482001247d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 201114136 1250 201112886 201112889
    0xb0307121511210405030d09120807050a0e090603150703090201090506070201021f0902030105040c060324090903050705010207030306030209090601030b040b09162702070c090213 79
    0x340103145a203040d07441c0c0340368042039120710222418148603182000460210071180b1020f04880700d00715802c000740a180c008a4020401c0d16075010610040784c505155003c1c2d40d0a95214074010344900c007190702d01030034000c1d019120100308241403204048031b542200110441040442c1c20030440d6031548002450b022912031590a00d010b42d10a1258480c1c1507009051258400d8803585c59458603801402030394051110040e006921500035034030b100c00071a41398050401065400301e650421500840e003507850903031781168003151549007000000d40c14030a140c0c0d1904408418041d48a440310000f004040c01c1c0522011b0550f60b01055003014000d0f801c80f02c156901c03038001c0d503c130a003e06026009280a00c0300740c0c01094100005546050007056050503a540a1710203181d648a940707e00280190003000300c1c5091050802100c4441c0e4000520002000b10000748180030410700303000b0036001c0205510134140b1740103100700d000003650f1305005c6c02980c02c0c8520050300c40c914101c0b11422070503917 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 201115386 1250 201114136 201114149
    0x30a180c080705040b061e0a140c1005160206070e0a180903030e06040803010902210a09050705030a0b0105040c020c060307170106080c07020f0402190c050d020f07090b0307 76
    0xe4200003580a030105084044907000c50b0308203c00308443e010300c0421300c80c451400040c07662400c40f00310701c000e045000d4200003034a494035102030226030240401d142d208440c0032805034800345201121035110302621368002c400e0b42d242448003000c4000a50b0b518030182840081c480031505880d0651940c55114004100001c840f101080305c0034280c2d0002c10000744140c00180c18002c44440c1030f1000609a400750341e0002c0c0c80ca01c0c0d0381c41c00542100a400403603411084140c0c2508064116042251090250040c080006211034203454072034a0403031181c0c451400b80d00f0030900b01d40480c030560120b50441ea800d80740402c11080c051400c074240341c4a9407880303038804404418810303082c0d405a0b40060340c3c000e5400d10107042e602c410341514005411500302500740302c01c11041e001820212410482008060405410b1040020042c02c40d40000d40940000ad40700d4405a8280034080051091148460001d40400c010400209498039218041d10b200341b501d80104410a031030030040000100030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 201116636 1250 201115386 201115403
    0xf1d040503131d0702030f0406080901090204060b03100f060507020105030a06120f050d020106050a0605070c090f14100e04030f0e030703060501081c0e1c0b04080712080705030a18 79
    0x4880d22001c0381c0c52101c0c2440f0180c0d010907000526a00d00020071950190001200c1e01e0070309103403e44c111002c400003460382009540782e10200c801030300c490140801a10001c00d0040c1c80b0300e095000e0300c03621105544103e412079041202000425000411074074803a03020703e405980c95803405000009030000d5405808518180c10500342032101942c0380d01402445082591404680c2050489c02c0c7c9030a4040c60350300034841ca0080110b075003e8001018480d11420403140042c3d035036140d600c215240a801c03d0b0307100340c850b90005016130281e04980d50008007032074002c00140c02d105441841b200300810040074407200150044071140110440390300100300804403200c080c1c5a14106025007000c1c429060903104404143d100c04590711b8081b0718007042541c0d81003180403042e04000552400010001041401ca083c000c007181d40300a1551086000c0c001803503035003690785048800d1600103409070b420003c0b00403e1014143e40441101d4100c0200203000c1100032100701048444a00102e0007050b111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 201117886 1250 201116636 201116639
    0x1121103070b090111010501050a1205010e0601080715020a05030a081e0103030e01031a010f200106140a050105162d0303050103020a0f03170309030927010f1d04050313 74
    0x42e042030042c00082c0080e60340310100c2060801507420380f0020301402d5840f201202d418880c41e05c1d203076200100e042c041c0001040040460308024103080b0f0a0704401032641054074144404c010300600035416441d244018054807006440300d035100e000e114007030740400140501040c006ca82c181c0c1c45140e495140c0d4084a41c0d0759503481e01501030309848018030702090400110101d20b11034420146800350060712000f009040140045034110118903e503600030a6410f29800e100d8800d114010241c04e141003075840e81c403014820000054459803007a0704100d8104600c0710300745186901d949115a11846a44100c000000700001149a80c40103900701c070042c0f643c4506159064122504030303802a20903810003a241c05031403083c50f05600000d0603481d850101003001609120080d03910203400010349050409a1000030001402e02e00440d00c183c107a60010044044030800050040040c03039010740055280521645042c46000889078490030a81c00003414400d0030710403600040442d026807009d59 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 201119136 1250 201117886 201117899
    0x2307030c0b0904060e070e1003020c070609080f03030601050d110702061812010b0607020d1a0903030703050105090709060e040605060d09062007140307021302090102010e01140112110307 82
    0x60b009000b18600ca9800d122001500c588520880b5000310b0b4079a0b26000b0081040090244009020b02020101a82000a400350a0080c031425024082940e240c00059243c84a158a051108010751080c3d4100f041446070a80c1c20008580b005a10002d0200d54008030501c40010303030240e0705000e07421040005503e11816403518104440745030450310403400800da5400e0034229488108820780152041000c4405407a0407003440c1c4e0504e11440e80015900300c101e1148030500c00c2a969814254030110500c16072a800d0b01a0078003400042d11035190340c0c0790100c4000c2002c8450702c40c0710b05220300891004050344441d044038002e004060601540d50300011101401007100c42c406843c403500c0c00309980c0041219200e80036010684450240c104203003a22410106180c0144104503407004221108c010f0f19039105400049130b000740016141c110301400a400d581800e0700c2030809034501104032020414850b078413815500300140801c0200bc0703c1c581460a00244903006500d4407840000280c0c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 201120386 1250 201119136 201119159
    0x20a0302071e0507060509030c03011d0d0c02030d080a24090b0312040e060109030b070f1d010804080913020c25030c050d0204091a0f07020a2307030c 66
    0x858410200c00c28030100035001507040b02c1020100030855009490200003281c844c00180c50941002420348002e80f070b810002908550030f03001c0500c220460741440000e8002c0510400e20740004a0902000c0075402c0c0d07000a4451003070002290078049071704007103010045079174420850141449001400c101c0200c5691000f201c8034070403d01c146003400c0c5040010300b0081400501c00c484100320b107090030b0070400044402c2e00000c04c16410406403d80c0000031500620100b8024416a1119002c0c05100c04000b1b0000a00180240040d03131481c110511a9130308c074000a80c07043e00401c1d000e89424002000035490181c1c00c040b444003070b0001c29604040e075004100c458094a08450f51041a0402c00340c829103020a44800342c0300100d4040c0401860500d047d80c0d544071840200001991011555080c0e01103440c12103507042030040000b00a00301c1100503a0607005185d50000f0490b43d0307070b07590f42c4841c1d40e00100d000b0703001c1c3d0205921102d51100100034070ba0186034040c0710a14129141d8005481 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 201121636 1250 201120386 201120397
    0x302040e040b2406031503010e030a0c02030111091e041104030c170607020a080304050a08030c0304060605042906120f070305010f05010e0d02240c0f15061909020a0302 74
    0x141c106800400342083e20f01080e0050150040d0009045a0f5299054907549001c001440d825540f84c00d0701ca42c8141c0700f4030042508000d981c844481c0c0280c2c03030051500311000050701c084003031f204000020301952803640c1703015440741146d0001c00c0c5021a00214010341611801c100b003840003c1008020040c5000950050b51103400f02d40e100128010070283e62100c05440140150300f121104801040b02c2900440d03004d40100300b00c400240030703a0380305404c0c1e901c111404032103200b020043c041048042e004900081004503010b2044a82d0070741c1c4907484842000c0c04900c82c80140010a40303035150303407060712001071906200120601e48001c1c3c0b842c04801c110781100c0041e2820f0700110310801480f41303140641e503041e0341d001e000701190713014000c85015800f0103030b0b030000c02205400d0094010112461141103090a02c985601c0420b00503454450490003850340ca400010184002140007407881e42e00c104201d4a0010300e0385041c1d482c41e00481c040e04007000150001402100c8507800d60000c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 201122886 1250 201121636 201121651
    0x1060f0810030201080103080a0e09070e010219020f040207060b04020309071a0c06010b0307030f09050d09061b08031e0412090501030e060604021309140a06081b100302040e040b 78
    0x149580d1000d52100c903581c100d000003400300301d00c0b400610118100c0409019402003605261500400c840c0000f0f804c039908540320800070340860559402c07075906000b604100121007845e6a2030211590015201150905100f07000340d6022807403000380011074000315039060029004541d80c2c1042d2140c143c40b00700c0d5000d4104400c042440c0c10341060784540c1102c0f8502e490750301504d0aa400c26004c2c90f140e030300c0900010b04260701d814184034401558400c558a09102c0c000030080a045050050141911a80924140007085045003105200040021801684221040d40d01d541c1ca14030300c000e19106a030072601512318a03007004201304070002209010001502c0b04040c2d01c0da40c00c01101a40e842881008680e0056400b040076800d05802800c1480403400c814000b850311812460100c42d0401c0e20620b40840c0403040c405400354610600001d8086140a014a900f500400028514011803040c0c000c4951289001c0d41c148250305641c080c100036080c0e102103051504054018010a40d4403d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 201124136 1250 201122886 201122897
    0x506030606090103080708090d02031903110d0905040209010c0c1403010f0b0303070b06150a02030d05010f050a18020d020304080c160f051519050d140123040902030601060f 76
    0x1405620b48160503a0489905c074000704d140c1301e13560340c03052441d410000105400030700700418100166030070700c4826404055a0060201c0806500b0000e00729181c9000520641c2c000000d4840301c01c4d0712900c1802591010713a0b0140c1c0d21401d91004071026021100c0240c070361090341d4008501045c1c1041c0387c045c1d0b41000c400034000741c0f02080e414811100815141a8158810071902c0f0001d540608003035400301008020011020044403544255400300c41701d2070044c1c10000310030103034001034400e0b00d01511351004629907207814840402c22034446405030b8400e160141c08074520301e0000c0d404031030040768000d1065440e82483d04c1e00680f50b401040301c0199074040c003413202618209824824080b280220703006400d503450107080c0024042c006554076400c2204001000c82004420410b810011255580030781d20703070803a4481000c5038000c00c0070400800d0120010040c075044d03c401540381b44032036020000c403062620f00080c010585900006d402d401690300000b038658200403c8500300304e00f611078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 201125386 1250 201124136 201124141
    0x30c01050c0408070906050a030b060103090203030f0406090e0402030a1b0f03030906080a0b0a0b090f060408060403300e01091205031e09030406050703050c060103151407020d1d0a0905060306 84
    0x905c0140c0301240107064011040d48810404106096000c9070000c1c01818001a8000f09030040fa056510410034a50945030000301040802d510101400042141401034421400d04c0e600094480c8122003014050018803052070308014480c0d014400148040c4592085440c0d0742d19006d00022801c0c481c035408110400000307201310005014001c1c89140040155022506103024298190007020300d144d00152041e151b044181c49400c000c01c00781c00340381c006004900d0149002000c4101d1901158104841d2114a041c0d0001d004503960b69442e07000b101040300c0c4944040e2600400c900c42c1c000c1e06840007903034205400c0e60814006d60148040707440c00c0ca02c0301c3ca94000072032518015a0202459801003104200c0c0b40d206001408040e880f0746041454103e0a000c1686020001e0b0426100340c2c564a041003454101c07031148070340e010b80b104c03c0529a032400220194592440d81e203110140304002c91788d01e5603820701010102440b81d000304212221900c502150000b804200e520501072f2180801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 201126636 1250 201125386 201125399
    0x80619050a02030402031c090504050a062c01120f0807030e0306011205031804140901240302030607082d040212030301030209041e0206041401080a05190e030c01050c040807 76
    0x3c40b881140c014008080420402044200c00d98404585104200300041c004c41c441ea103901038a4081d03207084070049109410041c4100340d5038142c0b0301c004183c14108008440050045054a0440348030402681d240f0080b4141509102c006201c020b0440d00e002504200305500240000100e0788150107d80003030380c0740c0c01c112040290350303040039000e90300034804062070102080d8130b900c4403d800317800420504406120514144015039241038141d443e0507208190003801100701c0790360036881c1007406900d0b1558007c01d0300e41d04060f0544080203508400155141c101c2d0135005926020000b01403030b4864181d000540858054800b00d11410341003c3c204947c040001c29203058a07001400703c04292901e070768440511310705000341440960320a07050000b680c1c900020700024038100c95200200d0a512000421200005204031012850b01090000161420a440244030f44c0000300140307044440d010f5900e140034001e1800050b6081500700f0141620680240c81201c158004540106480b0798 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 201127886 1250 201126636 201126641
    0x1504080c01322203020307150b09060402070201110f07060e040e19030c05060f1e040302071e3501060806040332030613110a05070c080619050a 63
    0x2081c1e0b0801041011180240b4240c04060303a030410b100c00d01d03414400480034110074400c84241c41c107902681000c10700806100e0303084050460b80700d40c0c0d2010401d05c103508002510302c25000c0c0886000b980c1c042a840d0459009403040501250208100e40e01c07022144c0089588451a0044000084e1608440d519a05041c002c540500d4203540c0504007122034050010501851301c3c00680403c550f481d0002e0208030706002351030189804458100f428588505510610660281d503114601c1c503103820070010076404200d581c10351300a011350580841d01030a4940188116400c449541454170065503803850118070310440d071101446000c0b20b002007842102e82280c4052003007101ca50000780001d00080e120b60380c151402d2900f00451484480584500e01c00d03180a803c1012107040d0000910000d45072060140301c080d99a54000e1000b65990041d0101c54052200745105000c1302003040c80130801c04600c2d2202610640e401c4801c01c0c42c040801c00310523070300c0c20f0803511054544004503000900e42d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 201129136 1250 201127886 201127931
    0x706050a0203072703030c05070e0123010215070f0306090e0601030204050618060d210306050102010e0111071506030f0303050415180308100902070f060c08060d0f051504080c01 78
    0x4c40520143c51860320280c1c0c81035103040088981c2d0182c0d043c045005c40301011058081d00e01c03000170165029155903120300c0d803400383d5282c0d419540304c034404654004d40c40c0403055100c1020f2818040c00320380480c0680c007421842c0c02c00465507040c10100c0001c8030000503214100c030f000315000e0200341c40c0d80d02031048540510040480140041000402a040c140704009056108100303400c40f040008069020016802d45d40b01b0020f030300e03440c04112641c3d090041c01c43d001c1038070b4000c012008000703141c40603511842600410120240340d08400502407580400c00454008035058405042890014000d04085070115a41c00a442d1501c60340780161280c090702030042e03810440409401d850070340e001c500007000d00b080c07403c0001c4e01003400748441c0040c0c81d01c207120743c00e244486c103030314906241030f2100f43d4003140400403200700b080f185a94030200521841c0d0444a5400c00380305504146040800113545810100001740511041000200090060740c920380001c2210043c01d20002d070790742111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 201130386 1250 201129136 201129197
    0xc09230a0504050f070f050d0e010905070b0414091302040603230109020a0608060a030203120d0e0312130303060e010f0815012d080a030513090204060c06050405030706050a020307 79
    0x1003000140300328050406d1407500301e41800c0c03042c1010201041c120660307a0318084888265129042035041000c200304243c050300004c0d43c1d90f81081d0400e034943c0f0b80c2510816004d4440c0e804040131030140c90030500c42c5d585154024006100044e02c3e4103055240d0b40042c070042e0a400d005401b01c0c540401c040c403c0c940801c0c1d004143e107004a140c608125962007016000a900004401d8000016601048050075000c004e40d185500d43c400952707007900f01c030707880c0e04d2041c19600b04020030810b005418011f1540b24000c0340381d607134042d101c0e42011030007480c0641101000c050120000700d81c1060383c02d121800c8a801c007003110340e03070f284a100200c0b01040030301c131301d10004216500920090150030810303910210404402c0c03120b15a1a04544c3c60184000300540c045034001920601603007800100303030064111080107500d0a45008001080740c03c1d40140a86565600c030085402c0280a008407a80a0742141d014800c038200340a041009500c1516103a002c198a4400d0b003602c80381021a24400540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 201131636 1250 201130386 201130411
    0x150a020307020f1309050c010e01050301030f030809100203100911130504020306040f09140f1b15090409060b010206060f09010b03040c030f06020304020103060b09060307030c09230a050405 83
    0x140c0c03e01c000f442114810542c01158105807802010081c81044540341c082ca00070a404981c6500140c46191001c0c442d60401c0ba00f00010303c00f00e2070455144e00c450380d02d45042c0510b9583c1045d29402e05091a0721442c290b070001007400901c0e4842c5060301d055510310342d0104440300000c03100d40d55a1040c948507aa158100500070841440c19038081c60780083c002e400441e0b83e0074001094405c84411610403180d03c1019600c2c00c501c10305c00c11003240b004071084e000305002008213014205070b031a0703201204c2c4210302c141049043d0303001c01c07003c2c1c4480341c80c0902300f406003240a00d0140c014080007804a030040c807038040001c0d080c1c40c100d21805040c00019115078116400d011100390607038801082130b100020742d8040000001ca4000320b8000380c0780185001600c03130800744001000c0e112107600c044e0140009104003602c1c0c2e520481100d4100700ca900b030014004442c11825900b5444950008412424a810201c9010b00c0c2505172110700d4400c6600e005099103441c208012103900781c820b00103500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 201132886 1250 201131636 201131647
    0x2903150108010b0c060f2715090d080c070203010f1e0c0201020a0c0f0602040302150304050c060f0d0c03060b0307110f07061707020109021903030e01020c0603160513060e150a0203 79
    0x1b9901201a044a90040c4401001080c00150083e10700907256214960303009101c3c99003c3e034106411250440340d4a000b81501c0401940d0080c400400900b44601480e400a400003c5503004d604c2812001c003a0074045c000ca8007a6070341007440c00810307900055072608040000c902d162042c8200c0e0040b400d2070704c80d850810700c25140c80360b078a0580c04007129255401c00010005d6030301c440c44580505410849070360380e4a401d1030024140301c2420080c40c002c203801d200c1c0420b4480c0044c141d1300c05c1d040f05d0400260705545d100045002c1c04181d8482850804008140180c45034000b400e0701c10341942504940303800100c4040b050365001e4510a11000406500c60f000d0b0401710700360b6054129569100104051120350006048218568003140c03051a07414000c00805410000124114000340098000861f0703450204503984402840141d1484458180c41e50f801d020f0020b40784601d0300c04114000ca55101d800c080d0038203080849081c0315008000c00d1441c9407100c00225824213044d0741c051401d02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 201134136 1250 201132886 201132901
    0x260601060509010c080d020306030d0f090504090501090605070e101b08030405070b0406050a1103070f08030a0f0509010e0105010f0b1c0e0d0c020109050103090b012903150108010b0c06 81
    0x6802c92201c2c541000790515400012840b24000340084c04089480187c0d03e040440c200b43c541104103048000f4881c0c580190440742d038000e107680381210301c03c0d00c000c51141c140e80740c814014464050014100c40c03600c4240140c2d02e40c024120f0321501429118452882c0c1040d03070955181c403001009061201c8980914800151131802035500076100d082100d11030b0791601100b1046422940103000000e0012600c9a00542e00c581800500401e03080950301d070107521b45942030300c0b8a2110000c0c00403d40080856407103003440d401642c601000001c10000360401d40845800703405c6044810320300d0740c200000851200c0f0a00c081104513640002110301d04448458188044a481680002c0295881c040381c11a1641448900417100c150b81d90b107441c010a031700c0050801c91709500010304241c60562030100245000c013000e810354051080105445101040001181080301070854405002105000c104504500d924007050401d0f04c0e445050381c0c07245243c0b8141d00803900d26038038503884807012072100e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 201135386 1250 201134136 201134147
    0x201050a060b0705060c0a1b11010306060e0d1101090815010509010e07020d0e01140a051e0405100302070f080c06040c0b0f03060d053c010218060f130f26060106 71
    0x46011410070303248230b40551030401c074210b440c4c0c24240c886038107184184d003c6682c58841e000161000e41005809400d802002c81d6002d241100020140815646152a1a80103403e02d100034084002140d000031105001c0700c15a1030300f80300b0030340195508400400c2c0c600e005401e180c8a8035003075004040850102c10110f442900e008426414442e8000c01040718001341d800502c007000340c540303070950740d0218104032000295080280000f0b0341400d00013804103640c0d0580080034209117103000758407550b86050603064411240d000074081d1a00240c40600c0402c00b107200e511076802605c00c0c20595641d041404098894455815100c40302000090910f10301040d14500d5980039404440e004103401044401204042ca8121411074040d90881013074000000e40d03c0e01c50000000035170400c1042203020813144288003100b031007080d000c221420001c9020003684c80700ca00300e000c0d0741d40c800c0e91400c10f081d08110741d000303020b200b00b4020b0001e5501c5007050784400074031405600601c1d20b80c0c03a04404864 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 201136636 1250 201135386 201135397
    0xe01050f0904091103060601030921120e0114010b040f1502030910032708030114121002070309060e0904060b060c0601092a0807080a0605100201050a060b0705060c 72
    0x440c15414040700306151968424515114030031604940b5516000c001c140c44c045006228904050624004500183e9030013514103908420854182e4036040c2114140da50185c1200490300f440e11306030f0078403841001500000d440301c0002e00c4100707090b601d69501d10300900c244d004840320182001340c100251680e104000b6080c540c1c0b881138a0070001144000303003c0c020310301c030503400203a16078280e18501402440d2034107440e4400c1038070b4144082155100080e03030005202e00080301e9101c0741c61046980b02c150500c05150140c9064524481d5080e1100e80203400405050700001c032501030200d90310b03008075181c03403100030000c280d41c090360b54640c1c2d808007610010490503085130060110303101d44101042440d001c0c141448001c24121540060002c4105030107488110901003064075925158000a035542c2086003450200410350341c80c1414000f07403c1c41d034000c0d508200c0c669113a900303803541940890700400880c00240070b200e580d00c1245500e801103420151960700014081000003030b81c1c0c0c00818 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 201137886 1250 201136636 201136657
    0x7020304150e0d0f060504050606060a08040209090717010603110d0201120b040b040e0309031c05120915010305010c09060f02070e0a06030f03170a140105210102030c0403210e0105 79
    0x5184403e5a43c0b0f10700220000601111242d88400a200c20030805000560b88800161a00c5040650483e0014902240948064003444100010400b181003d2150708040d258040c81c08c0c0102c04072000c0680205103500c000e46542c0c107580c540c228985412001a070400b44c05a40b00c01580800458240040200039001540a9a50f00c64242c4135251401151800c1c00d200c1c01454440340f8540502d03091240f5031000260404105100c030000a8114045e00c1e6604001d4142545903500c800d0442c0c5040040014010300c045c00c0300002040240c1500300c20882003050740c0b441040c41d0f407108181c0701102c20850080141c0c01c0028280a0750f03d460420700d40c066240c14004c6200e81d52a11a06a284038010003513002400c0b415510700c40100c2c0c16411900540354140400c0110152426080c81e407406005c0d961080f80c3c4005a074500c0c083e44007245501c5a1100c008540e20b04084101403525402840200d4851480030003004040c2c9041d403110340103054980702e95411800039001150030794080c04105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 201139136 1250 201137886 201137899
    0xb0105071b1710060504020a140a03060305011107034e060801020408071202240904140714270d0507031a090609070e06030a0f050307020907020304150e 67
    0x61120460038440b2528005031018140041c080083c440075a1a260021402240100040f416096200444080c1540c181d80c20750740f07400c02c400f0300b01d0107024039134400750066007480035951081c004100101103040c42511552041c1c240640119000e408140001204040402c1c0182e01108620030a8102d000d80707040c6103d14107180340b41802220346642282086030b5000c00c050010840400801c800f404000c00c0040249c002035002451040760b41c290080d01c0f840c008081c000b410400002d5071a1688000c100344140d400c1c4591303141594808035407140002c2d00041c0350045a140050441d10483c00140841c1c18032050510700135074030080304030312540018080040d580411818007120001e10306c00d0420103038507514a0030b81c2c0c039560000340210f00701d90041e4041c0070209074005070540c2141c072400110255607644e070001034181940e201001d0803103d481d140840030480c0100003418840d108030b450403000c1c1c035409022a640e01941c022106480841c00051440324020001e10351181c030000c006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 201140386 1250 201139136 201139139
    0x603090f021003140a020310051e01211404030807050c060a0e12070b240f220f051b0307020d0c060609020a0c020f010e06040e0a0e0a0f06050105040b0105071b 70
    0x101c2e0030128044a005e8810b82d4040144501c2e1448120200001d007000c4881413412a81c030105a1403505450641d14140300550407001d031103030704035400601e506007101010054020005405514035000322012400203030100c0008003014011025110031100100c0209505d40d1102c0041005112507601010144900002c081031442c1c04002800303810f101d0400e40d91a0b0a040c55032050342e18103082401182e111000c1001aa80c4070740300c44518030841100e4512628481c0c01c01c03c9905044400f00700f104506080c1d4a141d007000766008240281510b4580c07551b4820000f95010050006480740001030304a160394260151040700e9085d54070f0f020300302c00140c075a60ac4103400302300e80c00044000003113004010400c0552800d08141c01c4444000e0915204498040340060028406c50048208406180020900441c41c0d544410745801400048540010050400c5c03a45215907060032103034203061000108880c20f250041048004040c3c40741c13030810951b9543c8044855600403994005620b6040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 201141636 1250 201140386 201140411
    0x604050c04260115140a0b070303052502070602070b0412022101150608100608070513030206030a02070c090902030c100c1a16080c0702190f0306050f010603090f021003 74
    0xf44d01e103a100c0c00c0070800042443c102c0d0011100020036003851094104000c208150040901211405079047c540000c1590f9042415403c81842d000075000d000303103045184019580001e41c00b01a581d0340d400715080103136142c0c0540100d11603400b80070b240c03601c2d407244940141030840c08801668009403d0404003106600246c4c01c5400c0310002c2c1d1604010840308000c0700b500044482d4011540e1030b01f0001c4e2604118024110210140241301004000a50f1401d458a0101e0a8010f968001c10151b80c13403d0401c1040040e4015a000f5102e02e80e640000140700541c902c2074400b0a41e01901812151030001d0800880750450032040301404440212040003410040c1c410500301d400310280c0006081040f100303110500c202440d1028440d065003841010f411401c16101c681d58100e4015100d105401190f10b10504036a0209101e6034010501104000503070f081240301c1c110700341212860b680d035044214240ca810b0303400900300b003220304924005410021851444e8113440d04000c90014813003032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 201142886 1250 201141636 201141641
    0x40c030618030e09091b0a03081c2304060c030f0c0f030b03010b030703020603060103110408240f0402010e060c1005060a0f0e010b032703120604050c042601 69
    0x181140d01d01220340004508140e00074418250030354058a00401c50310301903c103540e40304114607820704d000340750031001070059841d54070b01d0000c0c0d9448248540c507020326909221603040700c400d50b12030f500d08080307400301c0b50450900c003404c481c52915185945511a9103901004000486003001055104c0210220000c1907000e24445010b1550302c0e00344800d07010000034110f421080e01c42d440b0341d05150a101d903d036400680c2c00152074044460760b58a45a00b00141c00034205110412410003000c200080c0b00880491107510340c0c8840850441000d2805000c404204011545590b6602da100c01203030140d4070500035025204c2000e00b54a20f0030010040c41440d0170856000300791030b6500c850030415241450521400100300041c0c40501450034034807200000744050240c203280140100004035840280b040091031111400500d00c448021542d4031703034a80c0d00c0511070304031959451000c6650f0307003407600c00d00d841583c80e040c0490a107401c03c003105008000d00183d45128500e05c0300c441e01c40400031f1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 201144136 1250 201142886 201142901
    0x10c111921021c0c0b07030509031e070209010312020d02030a0f030f0b06131a030c1b010605090f06091f0504020a030204080627010b030303040f050a14011a060306030d0503040c0306 80
    0x1610365101341341d510316120500260042c80c81d02010304150502c121040b00006445071000320b0414008c0f15050b0340b0054200380540200a036102c1d039144000070038481c4602c482c0360681115802e4442c0080c0f50711090740c0e6032081365124400a076000c6103d03546544640d00c000c03d59280c00101144007110390000558a0308181d01c10704c1c000c0e400c4d08080150130f02404080c1401080300032444c2c00d42c13900c0b0820041c94010141e00c030b201e11100c40c1044124103005e41c4690090413008250b2040e60030001400054044201c0c2c8450246035070701c000c204411980841003000354038550218002c1420001844080d403c64a07020701451340900003c500303e40240401e070300c101664508200c0291800400401e8a0861034150140ea450079940c0c00054074080216079019801540d203580c4007181e4901a1b04d02010118007426210b441081040c07058019001703010700156901d10802004909420880380707100607158030781c2c1039000c2451103030114040d0010390351142c0100301104000395207031284412340b81513 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 201145386 1250 201144136 201144193
    0x902010c0f0f0c06020c04290904020d05070b0301030614100527010e060102071707031106121501020714010210230106020328080f090f010c11192102 66
    0x3d00186d08550800e4481c1000c4070060084105103107620204034102c070b52080c1c0c155405605a40000707419926000e18409880d82d000c002c9600c01550703141d8041c403c0d0028041201c202e03040040105085415a48440c0110b42551402c1a5039140004021410304420741a42c4800f0031542101325221401e50440d0082850001940103481d02e0400242030500c1a0010003c031481c070f08811044071130000340d19040e642d00603e08485000318000080e100d0040441131043c24542508109a400c02280003e41c0d010b803e800701c50b205a21a0002c00078040d8a0351360701d00580c4403020324051850243c00800b0280c142c83c1001d24103e210305004d181c2c1c00030981114001da07000107802800085200603032046040702d007034110100410504010b10107a03016000c80c00194a030303008660b812200b0712200010a0208008010b03945000102405031162012417030344034001c10f10300031006504503840c1c8000c298030007115810030306c1c07880b00c80c2241c1b500e0388400e40443c420040c09030120780d007030030585840202 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 201146636 1250 201145386 201145393
    0x1507120218090c0c031602031006080309130c020307110a05090106080f0c03151306090f0b090109021806250609050d1806050706090b0a090b0a0902010c0f0f0c0602 72
    0x304081444615180600043c0303108500704071040c903500c40482603c01001d144401c11440400500000c2d141c00c03844991000b40c6031500000058540001008040a482c02d0342c101e405c1c10b03203002c4503508a039041c60718030016800030000000000ea8148104400300030091155170740780c0d1200c3c0404c0002409070024008980d010060028601c0d2440080350b01100c0007510350b1840c60041450701d14418000e1055000b04040c603017291000c461500030354060020040100000f2620750b0360000034110021080c0e028420a01c004100b03010f00e07000300d80b445221580102042c171080c0c030a001840d4070000c0c1100c020480f9540e241083c0d80301c1d0503644a55805801c0114600040381401742c00d1110f4401d100c0c0c20f00c8808411555010a0107140000b1101c0070705182da00c0700d01c0c0e03040280240c01141002030400c1c1c500d600f0420584d050381e0110050502590301401c003075468402020484145082c00f03804200100c21b8140000c0c440305900c41840c1c4644600484602e450761242440555904100301681 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 201147886 1250 201146636 201146677
    0xc01050702010c1706030a082b0c0e0a080c1c3c15020a090b07140607020303040807080702131e0b0604030b0c0c01020403021908010b040e15071202 65
    0x80c0e2002e035413003107880d039440d1491140c248400069501c0000c08002071032a00081140b0f90007070144000b0107a24074101c541d04601703040484c0c120005084c0d261002011510b4290b241d03005080c061b06036025507510394014012110904100f103107580301c000c2c2c05002e00c0307401d200950000b04465200044800310301200d0384181c41c0508070101c0703080014882d106101d6048006400f1070fa0b9910883c400c001c0b82900142e5800f400740c0b00f1200101d00e030f0010444c100d800138516082020101080321150901c81c25a8480d4640c00c070120303202d10041d14045d10b4080c0500160b4007042c403040050041510080101090700c101d184440c05868115003600c55003020310100350b628000c1400344099030041202e01d84c1c40c007829075a944104100141100c69800d2000ca007140c014142541200c0c05141c0040c03402c05440c1b10100340c04d910788a1400f940fa003075400d10100141a0401d400340340400e0305604041c000e4580500541021200c0040030281042005c03681c030206c14130780e84001c101d40c09003612030b1101603 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 201149136 1250 201147886 201147911
    0xa0c030b011a0a0813061b0903120918020a0e1804050d0201050115051e030f010609060507080739030b010509151c152703120f020c0105070201 63
    0x81c802c05440c0c0008000c100040155183c0c8001300540c405d680c0c8088105c821001c0c10510010014003a00b0405600403040407034141c0d8010b000c4c0011244a0650041c0713900400c58119080340d184d00c203080a0780c480a41c00640b091a0741c018040303407280f0b8130b4003040b01005600050318003810407014070513640141c014003091180034050011b81380c81e030380000c0c4900d52400c03809071800b006800e55201007200100d03c0407040307441d440f003c10060500060340c03030302c0742041d5801c07140c480820b114401c007140c80c00703100180007401442903500315600900c000c5d0a1041e581c0b02c8644285569101c88502400a079005907014440c100c03003041000c5514486c002d950031460b10b2148040107800c050310441b540c030100001c120942990440800b0240c64460181002030704440016007a0080103061050000056040b00c0003170380710446140d42240585140240c00c2116604110b08005c050005184c1200e92004a10703560808c60004c840300c10014030b084580c9a40310300310350040d1008401070351a4151380448 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 201150386 1250 201149136 201149159
    0x602010c0201050606090411040b07080c060108060603060a0507030e06190c05091c02030a1e0b010b090a0605090d0203032107050c0714060c0604060c0807050403051e0a0c030b01 78
    0x40c0010340020851414560b00090395070044200d0310340700b6910b0714000800c403005941982e00134132190003200d45801080c64221680c4d00005030a01c2d07588101c3c0300018803000000740c1d09006200c003038054007840e114508034001500c1c0061030401415255000d050846008000c924400d24410401000f00b80084100b03c0560301b5141120741000070900c40030700c959541e100d2008042d1440030312441d5201c00c5101090410052607005000b56000e10b04188881c415400a40b43c0148600000c11840ea2140715800c0700740101c1c103600d40c001442000034480980504010640340800400e206018020f9600207450740e40010035038604618078410441d61940303a126401e4002200341842d604045103040096903541080c410416036000c41e08c0601d103603884074421a04184d40f0601910010700d080d080400140070050101c900103006000004c1c0c40314814410754054a50210280801c5100e080c225240c0c000346640c01c00090141c03d41010000c1c1a0300e2100c0c0c000d51254035500413641c03408020148 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 201151636 1250 201150386 201150401
    0xa02030d0e0114210c0301090f060303020309010e04061a122d070c06020c0102090109060e0307050d0512040e0a0605031507051b07081b040c080118020d060e01060201 73
    0x7845500c0600000680e0003207005a40001c2c0241026110318040c2220708600013440d050341000f0030030301c060118070008000254180e031254002030180d92602e080300e404450403888040c005802c1030084140d01c1d0301c40c000d07110b400c280c0140003080b2152a030b5a111000d11001c0c00484680300000b8005400e8503006655a5000e41840203110b10000d5901d11080e426502034481140100c0340c4000a2000c1d000300c03200c449050300100d0031525aa10310988138001e5102904040c042400c0100001d50184117074612800d15038064094003c40c0d10f040b0a12660544140c4c04441a000d0a0300c407110440001014100414400d4101440d909055460304111411a00030700e000c0e4101110003039024000342c0503c0c4c0c000080c0d10b401035030740f20403081c08070f00181c410011250314098010001407130f403000144002035290104410850000543c108400c48110003401c1010440c1c00d40104102c0090310314911900803072030000b510300012000007008079081070300038105a01000c001800f6080d424804d03840d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 201152886 1250 201151636 201151663
    0x8010f08070303080405030c060106051c0b06090d0302120d0c080717010e09030d0c2105241908010914010218040b01050409050103080a110a030c11060c0604050a0203 73
    0x811400c011415454503264000503060005140210f400c1007402c000311290100520161185542c60b2200280203a00c0400007800d00a099103441604281e18860846100c0e1f00400480c988900b0704248801c4440041095003540201070b0b020850400100040046044420000441c0c4c5211040074107903c4002d0000c10070020445c2640710001d05044c503180c1903800c0228240c8560351210382c2c451451182c000c110380300c3e50030b00d070880400c0c50708582000303a0242180014440c2c0e071041a041402c035802107030413410810b081c9503a41081c4000304290031880c20042c0c0000c412070f038a0012a17150259507485196507030341d0f544506c018092200004011021440020741c5800780100a1024055841581303a02c1985da41071b41407120380c008c0c0211801807109500038041503030750b0b081c242e0041d0400c4007000f012400c07a034030a848114001c20911800e542c151216500009161101c0080140601d000354024a00b0000c0e0340100a0800540303200364466402481440c0d860f206243c02c207106207182c03d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 201154136 1250 201152886 201152909
    0x6090e0d0c03030207060b1305040b0114060d230c03150d0807120e1e0f0411030c0d0603020616110301020903152e0303030605011805010c0c08030301150801 69
    0x5010301d501c03400484555816140258440200d400c1520041c43c04281c5254004512612a150318200342c10151013240038000324452a0303030b240045500c09040417066075010b9001c02952202d03425960040c0d40c0300c03184640c169640850810302080402e4103079402c0050348408000c0100d07409007451802c04040c01034907030001a840c150b80f064414056014000d1562006e14650980240300d40754280e0744c0d04004101154014002e070412405c4a0300350314650007404201001c0e103190806006025011a91040c44e03499966107001d40c0c40540c12110013520b82603140c65000000d83d503010044d04100d04080100600c40210380b500c26203419607541424060b07401400021001e9801142c070b103064022510401010740d039541007a0050b500c5d4980b501e071071401d400c0c822001000d690707552002a68400e880030030100c0c2d110303801554854100c1400c104070b505c1003a82800154070070202e110310380b84119031440290791107144107421500241c2000501c12850003102600c10340c40101d442c01000c0d07080a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 201155386 1250 201154136 201154153
    0x1308010e07031509080702040c020f010c17060d020d1b050307170118200d02030a030305061003140a0b060d06090506041802060904111e0405040606030e0c100c0203060a06090e 77
    0x200e045d14000c1e050042c0c4196910202c1361071140c000e0011400c02480e0300f00811201c1841000907185640d1691124a0405141d00040c080e0400c00c95500c03415130001c00500010301159641422800544240416951111400a01070320104803000142229080c1041d40c0301401c00c5403400c5641d40c1d000c140281500c000b1480104141103100e0104041c9010030500f40180340b00880c3c140d0031410300082d010f204410b452002c0c90ba25a01c00c41c0503180488621805200091084042c0e80010b84003082424066000c6400c110300d9070300c241d402e000c01600e40b50404080707910040c205c1c1c50f164040c851060311001000b081e1b00d090f20403402d240c5000c8500001e41651900420000e02801030715901a590701e502c072400d0702c902e01060f00e0804406610340600c2c0448054901941d8000703114007801076042800100b0b26900074040d1800b9500030600410504601c60100250000700310036007418001c06105072005038909101062060301409800304142d0f14100d001c00417a1320513409030110740c001c80070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 201156636 1250 201155386 201155393
    0xf1d070f0503070215040803090f0f06160e06030f010810181205040302190503120301060e091915030515010b0d0b0f09040b04020307080c0105040b1308010e07031509 73
    0x3820025a031061800075200d6864100036450701803808450035903c01c141c8101310400000500035441090710800756450003915821591741c5814040c1c0300e20b40d5821410000f544a011141e88052a451a00d04002400f10714004035034160300c2524010407804580c001440540703000c00101104c50092582008406242e00c02e59580041c03807500107050440b1144890310f043e00c1403007a0b4002e990018030042c406020948445941862489280c0c040e0007401c100c0750116070400e003a030b8100c80043d03c8074082c0e00198030400c00c443c0700c010042000c244441d01440d030401c3c03052040d0012905015a004441c40c258140180750451513000c00c204090305400602c103000b4140240c03807a4008101c0e000c100b8402e80f0002441d01c10b080d4116940000e4458200403e212070501c1040c052030082e015651060388802070b19454641546160b030100310200001c1048129510003080000b48001d04048c12503190270800b400d4030380480c051712081d80522410b10a01070400840c3c00c480c920a1020020300d4100e5a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 201157886 1250 201156636 201156647
    0xb03031903052703071e020f060c120c0a030908030f041205011103070309031d030601060e120703120f020c090c0a0309051501090c02030909130302160f1d07 69
    0x324100800d9180d00105968055000340ca0400b642507814601940d054036078041ea030707034104d254245d03614103071003070b81e4005200c0100b510341309643c001e400c01c4410318194003841b074168000900e800d0a48138621171144a5400c400142038540340d0100540110300c020f040c01040500190000b1610390000c1041103104011402140c00304c601501c84180100402e042450040c10303554103a1107040c80010401501e5a071590003d101130740309440d8032411109400002965003000090340d60940c1c007000c014044280140f60342040c40d40001c0246240d00c8500503840d0410500358400c44034101488a8404059000031000c10f26185510007809003181c61000206916805442d00f2152500042c1d04040c551003031700712000d0b803078208080302d0304a54a03103a0006c204400f442003030b030380358901545851014408400c49503e00d4008040c1d85a41e1510014414224a40c0a0031070952003001c82c41c0d661050141c0440c1d009054240071500440d1414095401c48050f510340c51030005021010000d0098016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 201159136 1250 201157886 201157927
    0x601020c0118260102040312120902030d03020f0903120c010c050a140319140603010614090606131508040308071106130c120602091e06040b03070c0f050c040b0303 72
    0x3601c610030604007a12040d02541c0108a0302030b0079400000e02109110b49402c23450b501c8003d030b5542000c4c200b001000101198074130500250f0680110001b480003901c6230300607200c40e00c0940301a510348103142c0c6c00245000840b4030285400c0d0f030302040510250314280301c0c5180030005410f05034900b0022034001071204c4108042000d80840102c04244001c074001c16003820071b00510710410403552103400d40800d42100325a490310035820032002003421420b154072202e0212026250011030f441d01e00801249030803510fa00d03002550b400c4400100482001c003c1a103a0710a07888055043c20541001844000024000c5003440310800700da0549400000d0080c1e40f1403054621030130b10841c02d14185c950804030740d101340d0a480420310b0807410700c00c00303500524105400b200d50003003070300020b283c0d40c0f502c4030811106070303020500f03000c10071a1f41d030240010b65000d2032070300d819843c0f2100303a640d50510009521040e10941d1260b04416650700b01440754180c4020210021410154040b900007104a100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 201160386 1250 201159136 201159149
    0x60e011a0a0f0c15050405060702070602030f0d1b0f0e0d0c090c0201090203010c110f07050d02060706020d29030f0c010c02030c030d0206072a0314071403030601020c0118 75
    0x2d0030b07140c0120710071094246159800113000d811400004140c6001d001c09903000d50741c0c0c1c0100008100000e00000d000022039059030042d600f019400b0010000c00d8005581c0030250035101c0840072400c2d1100c039103c2051190b180c8511a0201c140c24008001d9503650b10f80b94064201c106104c004108401491401c81c2c65119012444464843c412401b41410a20080d019801c01c02d0b2a95000c1d0880800084151400101d4a0a80d404500c5c2550b650303541c07003050f4104081c0c40d4004051700b06040207100e114007824000d031516515007000011107002c0d8507401030f40140304501210a602d452400c1440c844220001d00d00012a496900c3d01c46150608480c10300120b9504042107403414000c0305c0c0070210080544218107007800019440300000c84010380094503da2003500d1801001444030407101074500d180f0303244506994256030111142c80030520101c0d09105520001d0300d0741c0c102441503001359014607100d04110700068a8080d5183d000780c1170003d40300c400c4d43c0c40703030748208040102c544 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 201161636 1250 201160386 201160397
    0x190507020a0e0c0c2a06250c181a06072d020301020f0711010207080d0c0303060509040309080c0d110609010504080d020a0308070806030a140c0d0501060e011a0a 71
    0x2503480400501d8407504c1d000305968080c1d800d82c3e00c0c800d240da420b26004207101031060610903070070800700200b9102c0e1014000144800c0e00d4001400000039540c050002e04c2012650000758440c0035500b01c4101c40300d00b84103500c4c0c0720b18454508156071200305858841c2550f40310700380010381ea6402800350003105090300e0b185200ca0450040b400c240e80c0145183d4024008550f00d4411350030600840e401030710152604940e460307018000f944001442070840300d2000107070195450a40701202c50b4031100c41c042d020903840703400118a5540c0d08001c103000d54031944416078050320b4480e0650a0110900d00ea034071824131242d0350004600b89142c1c502442c0f4003200d405584001e62401603805000d50f40010f4400d100d0800e0107013295400052035107242c0d001c0d07120781c40039545182040301c81107405c40c0d950f038040d0401040c040c0050415600078000c0f082942c140c966480c1540701144083c807149009481680d1640f400700408001840006d000d480b400c1801d400d12003d1a4041c0001d1041c201c6c0d4800b0000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 201162886 1250 201161636 201161641
    0xd0c050106050a03030c0209011406031f0e0708040308010905060f0f06040b121b030c090d02040608030a03020a090e010605040e090a0609111c0b0a0b06070b0c190507020a0e 76
    0x6000c1d4060806040010001c1d41e01c00d4482c10024206012007404074001d00d030160000c180181a42070b41d815800c8010903807803840d5900b20840745100310810f0f03109a5402e4070100802c10107000504070380b240c00390f41e44020350707481c3c035040040c9829010b9101c04030540c50481488020384800115240c1e1280550784c5428501001010980c8c0d4403c59000741ea1041e00400c4030812a6658a102406411041d000d5426940310529401c0144000e584200380304500b0002ca14250820011a40c2c40c0c0c1c0c0014070024103c2e940e440c016095a020b901020002035002403511003081d00000090302828003481d07080ca841d03040c084050000d100b60300891070729403c014009030010714200125040e0707a43c460810300a400f05464555100ea1000d1602485141d0020007500180c0c1505001103000e42c02c42000400da480c0c28460301c1c010030440d038080e41c00c480c04200440124001002143c09440c401a100d50780c0c07a0821510404003c0d00344094042040c1006007001581c5e030216070109850903011202802d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 201164136 1250 201162886 201162893
    0xf0b0a02030f121b0f070b0c0c060106180f03020a0b1e181206130816020d050d082a0f0403061d011d03030a0b0f03070906140409050d0c 60
    0x5006031000c94051035000a411449212580b0903c0d01580390703c6408441e003841424100d51500a00d000151040300500c490404501c0d45c03010560850903018401d0f1400498980d40350801500341c1200c0c2c04520013640002400c0e901e121403000816246150218850455001403221b5596105004000714080351040c0d20034414610350071403124003290309944404d0443e100402c00c1c0e0805246203c0c40303203007039001c0c18080041110f0b442002103001d100810501d03542c82503c9600405404c1c0c40d054005010100103131201c02c1d40201032f44c010801085851009040240741001c01880c2190851414400c80005550120506030081d002c48406403212480c03250280140100c0e071003d440076003040c07042401c00812801001c001d174070180080c000c40070040c0c0802d01c14841151003800380d51080000556983c0e45500190702040001c128505080441c80001c0c034000c12500107403641a960881000440110190581300090039601801414400d840d185d440b840c1501708901800a1000a803040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 201165386 1250 201164136 201164143
    0x10509060f0a030f03020d140a031d070f09051308030a05070c020d1a0702121b24010807050d11040e0a1205040e090f060412050d090f0501050703060f0b0a02 69
    0x111400742c07610302d960f0f03a039003030512030020715100075030241c011481919580f03441400303000904590392012038034000c900d000460041c11902e51965030908181c6065040030f6090100c20001d0500c14070712000c041c2860305000407600098682c01d0114a050320900010314000240d03988840420b4000500307650703041301030728105030b00c410095004600183c110100301d03405a00304a42034061042000681d680401660ba5140b0030910b035a070904140040040002d0404e06900300c29003110540e013114000f00101d403078414842010030000c1c050903006000b43d040030045c04004040c11980306224075219241e548000b6040c408842c0120740380d04070311700b00b034901304920550580d1008800506a003000c200400703a80003800b622505c020740740c02140f658903000800501c940c140708054007158480b81d40700d4051221171001082484424403800049a86602c10224454061100101890f10514009003101c1d4001c1801060600e4050180119400e003101007040d180103103083c641d18115003105034035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 201166636 1250 201165386 201165409
    0x7030803090c09010b0705010506030703030e040905011805010209100e0a0306020a1b050c12120301061b201005070506150303090d05011508030a0503070804020a180b01080a09020901050906 83
    0x42286090000151056140c0018400b450051002700a140c41d92000c1680301e4100348005800a040589440000c1c50241d02115040b03108800005074541f000100b071000200c045026201654080303103111035420105200c42c14003100707241038419283c0c502300151802c1034902000e03003490390104401382074902481807201841e4400d48684d030307680c0c07003441c001d40d980e2a0950600c0c000c0d0441c4001141c2d41c0780c00649444203003146038605081d0b80c20850125442001c8007070502000d8a5102c50402240355000c90110700b40100601c0c030350300740281d41800010348d14100e2003c2040700400001003c40d0002c941c40e81c104c40e050340001245030f401400207203140640c004695003d880d849502042100541c041c4644407650142c05c21401d0390754804030346070301810000e0800701d2002c1000446191281c600c03d03a01900c014850b48806880e600140550b40d40300485520710f507a42d600d910301da0740c0c210001e19800fa502540902c007030450390303022032a401c0301071040030300500d4540301203a0703184d0710744070b6108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 201167886 1250 201166636 201166639
    0x302190303022808071a18070b040b070602070203160305060907210303092d02040b010305271c050306011805030a0807021f020709050901060609030f0302160f03050f010e07030803090c 81
    0xe824207010031000c20900891f0740b14421032092a030b0024807011403106860441e140c040c2c0c4203040c2003494850360040c3d44000d5003280c3c1800b03011511282c24030320841d020040c601400003083c152805520003803801885411200456415401d62514603c640c150040f42070713814603010031640428a41980c2907800281d82d10429110a0800140100750710320815000740211020b010321600344c0015000c03100251000e40c01007007225070701c3d00008013041d10340c2c070500d881c1c50441e12122201e007074420803103144114040000700004213004296900c2100c2c200b444d142e18000e0340b207440ca405e00183d503075911580c005010420104005c1c007555680c03125080185202c2085018201034284001e444801a02642200e2880d050102e080c84105110341401e5480c80d84441c01c80c54195103c560684098140407811407082e030f07400d01e219590301e804c0003004000071403e15003144d0640c544182000400b4a069903641e240640200321001c0004885044a4021000a42e00c0d25100c01c1c00c1c0c00d1052010405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 201169136 1250 201167886 201167933
    0xb06030106030c0e0405010302280509070903030e0906060d0c110d05040f121208270c12012705160803030f0a0506030c09060307030219030302280807 66
    0x1640a802d80c200720f0101d0341694800648644001c10032040300c038207020194000020304101024100e02080091901d40104540b0040c04d91f110001005214121102000601c0c400c000704200758100309640c20850045074070786010b00d08040800d01034000c00d8621300720b1980700c02c8401a424006d40304030f2000300c8072406650611915070005441580103104816068141610010384d01e41d000d000c840025900c020f120000142e1a80103c1d1050400f410b11b50220081031a800c4070b103001e44100e65170012017100a400d588180004004502c40c3c580d0000146034100700420110301d03010150410403031440a0361051105150030034601c2d01411140220818602c1c140c00b090521000025602c642e465030014400703a42ca840062043d10030a03035006405a12071200140350785020f501d540c2d032051024044650b29a40c80c0c00080b000d101c0300c014030701e6000a00794107101341907050020f08400d044040c002040e6000306c51088051040703400d4050304608005c6241020004409000600c070600f03020345 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 201170386 1250 201169136 201169139
    0x15060509070c080d1503120806010810030b0403120e060420010507020909030f03150a06091401080a021e0714010c140f070c240f020706030e010204080304031209090b0603070c05010b060301 83
    0x1055070b10000329021f0110f450513000652962081c200103200e103195258181c00035141d942d03071b4018240702400460074480c0c3c450544a0800300f45c480c01d080c69003400001c00c1e26042c00e041c415120414030071402842c40d1885200d240c141d8000040710070499040e5000304140d035800c8803541c02d42c000c80700504c180c010700009120003003003c1d07880e4452481c41115102d0140d80c3e920000e841c04000b40c4a200507643c0b6141c141c1c151580a002107662008104070003600d0b00b04a0060fa1691a4141654104480c1e01182240a00010a1180321081021002001348407030210b0080c000c084006000c070740f003c000103803040c02d4403030303800a07240c07402d40c40f1500250072030722800f00300c29200312204080a100780c0403c00c60300c81407040542e540507003459009010b09c50b0070700d103003200503100d510399aa00a40d001c10001401d0349003000140025400344030381a60441c4004030003003e902c0701351701c00c4c240769040400710f03091582c584088982080700c5090001c001003213403800314050001020103d500038400b100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 201171636 1250 201170386 201170393
    0x110604090207051e03040e0f1b0a02070906090605031906020f160302060a0915090201020c03070303030b2e0e01030b0a0b030702070806010e0a0b06070b010315060509070c080d1503 79
    0x218071500c020b500c103041413012400042ca6560380900d1056001482d01040031a0880f4000004d00e504034485843e040300c146406040084c141d4048a0200016403101004000c40b061522858000d800400f0081c0300300e41ca000c002a5031511250401e4105d550400020002c000003581140c02e08c001401150351030300084009081000341c07d040950150040c4030000c0c6c846000d1784141c0703400941c000c01840050304820044d9005040001c03040b4150b02c20f80e003081c00d460b42c080200030b00561013a07a01282180004080c41000c0340c01c20b0072580c07030711030308616214410a1070040403041c5c212450700c40561901303034004802a1140c614603e8000702c2d4200c0114010300820001d501c00c92458003101c5070142d03210b803000c0c1da901003445400d9101882402281c1618080c0c0c01103048424020281030422401d80c803900d40c04442a4000c5414400f010006142e510043c06442c0c000c000803101c2400d540303042140540700b06d0020382c00508810f40020030006040d2207900000348001d091904050103920703841c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 201172886 1250 201171636 201171643
    0x3020a051e0d0c050702030601060e010e03060c09010f0c2406030618050c060406091e03050f0606130c022518140f04030207060f210c0e10050711060409020705 70
    0x94282e40c00e83d060080002d07140d4055401c44100c15401340080206a281c00380031621140468600b50401c0032113800080903680c00c1000c54083c01940b076045035140e60a03800917080d250318128400900082c080707000301060745408010040400c0001d442840c002280c0e40000420341a040140315910b01905c0c000a664000c4420344500d04c9031003200d0b01000c480c82080383d0380c002d61041d0f10001d0384480d001d2141140000402c49100400d440c0c0204075522130b602c05003080f01c0054000c50680c0b1000c00c2024920344078030f820403040000f0a0800141c0e030007500c000d40300c14510815540340200040c044620450300801d000080801c2c40c200712040c0032100c0d624015001034103211506040e00008038960700032000d6090300455050700101b50151a0000c1a901c01040384d49040600810b0703288040340740d54419452103101100800050500f03642c5070050903180550080c14040da0505400e0821141c03c28200c0b01d1441c0c11462031041d107100c5d600018480e210f140c200c684020700203d00c4e07200300075000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 201174136 1250 201172886 201172897
    0x1d04090b0601090905010f06140f0c0d0f030204060807080601091517090c060703080a090f03080402031e0309010e0310060f050306130818030a0b250503010f0603020a051e 75
    0x90740c0d0f10000e02d5952200e6400d640080c0141200303074042c18400c00003180540354101c03134141c80c0b0415504014100482045980101c51669443d412080d01d0794101540030030380c851988032038202141081c1c10400014400c68006100c3c400384400300010a003143c0c02420300740000d00740010880f56000c0201c0f03004000c044804010001e24082601203440b40c603000c11002605080a801c2e50701303084c0703a42c4044440a1010340001c150315940c40304040421f11043c4a00e488500a031902111810148185450400d6041d0041909907404400040035600070080704c2d1a40350074a05048510f0703861001074180200c202709128030300c1c4dc000000908400d40050641201c408a069402c43e90f41c1210310205442d841200800e880e800b04860303041417028406140e1220009030498520103000c0c3d45866010105440d5096103a59118070890080b900c0b0340c0c1d4112078030f4103207012411545015482c4042c965140100e405050f00490400c00c203e12070019640e07455008001e404039004110103000550703200307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 201175386 1250 201174136 201174139
    0xf020408010c05160f03050d020a081e060306010e180f0c040b0109080a03030207080913052502121b190204060504020703121109030a03020105010f0501020a020904031d04090b06 78
    0x20721140000c410f020b40240c0d0755654102e06249480030203035076900180c0f18141812400c0c0007050003034031007100c2580f01900614885132140c02c400e080044500e444241581814018042c08504104030398901298150440b0101001d038117541d124140381c3d846414840c05072884504c0b480300b102c02c00c6500051042a080000d45040000502030001181d8400f201d014000d115800010b188001911039401461481e00414641c0e00b00308a4100045003030030340f144403a5105071103906010820101e40805415580340108a03c0d100c0008180a03480340204526034511030b40220348140f8048220b044507051130511000e5071031a04000c80b41a14240c480e9074281e001d1864800e010949083c03030700c21030303005a07015100d004807500084200d00c0a4092604002031003a014803100407580c900300304010790300740700b0340000c030381581409801207502e48203501180c11580015000c2000d6101c445005400c00e40614084d20300052211104603400f80b6107004a400503d083c1c10b81c82408044050207004100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 201176636 1250 201175386 201175391
    0x8070e06030d030e030c0d09031509170c03161b08070f060c051e030c060c031302060a03090506100503010b0a1d040614010b0304060c0c150b030c1309120201020a0801140f040f02040801 81
    0x300102b0044542140c8014050800050984e2842e43c4541c040e280d501036a404480c902050f030310f2203d825070b841050454041304602a040e5014480e030b0259005049a44020f003a0185800c2582c0d51031101c230702ca4031051210f0000c02c2420701c07400780003825456030400040e8a0486500b2401960f90740300c401c00f007006018503000300d4601554001280d014403244030a109140e141d603001c200e0154884c0c2c9101c0145581c0305401c10018805001c4c01d80b080a000b1003200e0704920302010315003591040782d2074a00c2002c200000780100000f818000b06862001100903440e5611071409500a000700700242a1407021400001020400d241c0150704c102d109100611034003008001c00d8a00e001e034130500030101120b203092114142203035031003060650001030072580301202e0240800e0300c028001b40d50000a0703072250090020311030005105502c15100d8402145020b46a040c020480707401030140140c4800c03004880d4115613541c80c0c51441e9040000c00c00c01c00c040d0b51520f04402540719200740600d950 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 201177886 1250 201176636 201176663
    0xb010e0402070b061e09060108090115180f060506070b09160b131e0302090c1c1b0516171c09030f021912022508070e06030d030e030c0d0903 62
    0x140d00309644d01d0f02c0c1780e000d49410301d41e07144e40006542c2114024244d13450741d03503600c0c8480c0031006405500c03401442540c3c804074034001158070340d4017a03079490318040c400542032880800075504c40303008a4100940000301e80b01c043d00c440c045142883c080641e0603403004440b0038041100241200140100343c00d10000c220141c0d900c2400103070390f4419038508240012500000c0026003800042141c0c0620351480107032505448a80d001501400c03500541c40c415900d03052184400c2c0255543c9840f0941d908082d0300b003d007580c1140041e1401c0020007041844040d1185800e07400540694450211841803540d400000c0500b51009160691082e0000780d074100110580341d001261042c80c030b03180b100c105d00e00000349844641c048040c50715000c0c1103211751035490b42c1c0c01198100b042c400316075010301d0202541ca4120002c0ca001c49540001c0300d011544018044d80e42e6000076454152285410040b5441c001c00d40114258007440480340014040c0d814103148059008007220f0a4900c140d90800600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 201179136 1250 201177886 201177919
    0xe1b12010e06040f0903020c040b040204081203011d01050a060c08090907050706060608090d0c050f06090d0206010506130603090c050a08101b0c03080c070804060512090f0c040b010e0402070b06 85
    0x180c002c00000340148c0c000c4c01100f121403e00d80c03c40e0f1404a4040c00162800c2e40d500700d603920341501100440407000c004801030006c3d441400f41103031507000701000c074402c950415000881042c868428981070090781458a07040215000c00d80700040401442c1004030700e814000502164060301d421950545407441c0816054095005580205074200041050808140c41598524215181038891344602c845640c0c1c898003c0110034400d46096024040c521608070303019240c43c1042e00902c0c8207000920405403c5aa40c00104007140c5180c900031175410110b042c0944c0d48490750304141d4010421030004030b01010000b640700e0f030b004020b00003003000d400c100300150040381e0071948450000d400c000c00400864481d017030700b40e04159a0240b4900e010507036034038130320700e0f80c490340c0b000000c54000b00b2a215840c0c9824036650703000311250003410842d10b8400c0c0003034480c00943d2802c0d100340e554004900159108152465550740301a108541e182c0c0c1070b0820080c4024200c4501d072041e020643d10b000c00c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201180386 1250 201179136 201179141
    0x3020414011706011101020c0307060b100f053a0b011803020d1b0e09060f011203081603061a03041101090b0a1b05010c1e090e1b12010e06040f 63
    0x8082c0325039a141401d4a840d001100c040d8036600790150150340902c03402072020000c1c401040c2c00c92203048000f515035010014030600503280c5190f4004d00c088030728240d2020390400102c4440011a81c1c080d4180d00c100404a5400e5451280c04885074202e500ca000341d000c030590000d0300e030440c241c8a2400d4203103e10ba82d50f5a410203804000e402c00c061030205c9002401543c02d0f254211040360460480a44950384600d11000403101101c0c194801070900c1840e2006c06401400340160600c0c40d040045142c0b030182800c280a0310307038400c80c1d031241d0181e00480e10983c89040034260300d200502c040c100b00e24108034690000c0e20103459505001a400d02158098603104080382c00b8060002e09080c0098002e450280b9114240001c1165504206000881c05e01c01c80311a210700b62640307010070100d000310740348003200e448000c0140071451307070140000e01c8120041c039031100c189030201c800210f03000905800790042804141c0d10300022030001c41c0300d1600c0d0590601c608000c0d2820408010301605100a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201181636 1250 201180386 201180407
    0xf021203130909020109050904030c02150702010c0f11030d02030c01050112030906080901020d020408150109020c0a06110705061006020c03161e0302060d020403020102010f0902100809070b0a0302041401 89
    0x41c1c1c21507a5000c00c071200b0700d600250303141030050602e0400542e03100042036145400304c600b00d002900c6154640c1c1140740c03076104180c90799016503582d810f003806580083c104210664020f080e00d4564890301c2c0800a0000103154280400750a80b032800c0036881e030280d96500244d50321500c950901002040c0414806500340a9503015650110080d00d00300042e81e003040b016204502c0c1d03540800c50000030401c54001030000301400c00c0144180c520074103911000d06010381015035281e004018402034040006401e100054001e0400100380e207044400512605c5251401003240c040c0c1d500b0022544030007070b4124100c038000e4090706d80c9400301400305a29a01012004035811a13515820303c107901030a80300a2440d0114894484410340f41d40010300143c001c100340c0d5179080c0d0001418000c40d40c0c28024020180c2902d20280300c0369000e540041d003041001100d200400c44850000b500c800805c02c0850002c01b11021102e0b03482c081180f00038041e40c020b0040007110a0b030155440c1715544240312400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201182886 1250 201181636 201181657
    0x6082e0b0904020108070216150809010c0518011e02010203040506010b0a020715021e03040602010b04020f040302060708120709051f0f03020a03090b09060a05010519060302030a0609090f021203 85
    0x6116a82d03507401507031010006000071302140700303008003500302403440035441016122035504001500c00020004144500003043e640710350341000c00d010348158210003074440d0720320000d810400c03050b11800126042c80316035030018603c2045140c654005601035000f107000e10b00610680350035a88a60f14a04188540380c210300050380031520070014208000c0e0304043c64100352058480074203103144d841c0030901341003080225913000010104145a024401d0f00080d0303030309540550801c6101503040ca081d00613440013901944000802c1000c0219480440b21808000d500911460500702ca00500288141c080c46005a0007a00905181c80c14400440e0203003425907284803407402c0c110030440c040d4024200324800c0c1511030b450600007c00b14038120744949810001000a032030030042070710136540181c0c0884c0c000e012018602d01086402d20b804010307030b10507040c0540c0d09c0c0c86540007400140b400b54059a9154034041e0107100700000c141c21601480c0c021906094a041041c0240d9102d11030022500b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201184136 1250 201182886 201182899
    0x501050d08190c0506040302011b020a03050f090a030206030a0603061107080910210f0c090f03031805060307020609060604020301060e0f04020714061b1305060c0106082e0b 76
    0x150b55400700031091502e4403440303180c0020390801d2580d481e441d007603040c3d030101e0143c1d4503003040011604c01c03075410081c10800c2d48010481800c1e1528041c0041c410900348610491002610003620b403514070000e40115400b82c01260f60b450b0031003081001b05054002207544c10304100140c03645003842010340700051f8000b00881d00d0000400100034000c00d007a1500d0051004540044900e141c91b0203041c110016000004506007207a601400304540400c1140b1003030200c42e40041c0407204400b820a0192507242c10940c005155190300904003100795484503600040020070481d03443e030f0201d0a5401496507404445507500c5520400c4145d0009000b854001178450b0f081c00352a02d400720121144e104060801454030401c0d4444c45000950b0018550943c1c2c003002c14000200c003007200004498411814040c200001c107540240081c0f403038886c403446200c01003103040781104290700c4a402000044d04a4600340046000710f01d05e030013041032251004001180c6240c00c0440d6001d19a64101c00a092 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201185386 1250 201184136 201184147
    0xa03110c01050901051209100f06030c2103080714040b0711120c210a030e130203041101050a3e0604080304080a0c14070306231503010212011403010501050d08 70
    0x260030f0706c1c4e40002c00014446c8107001c1b80e03a0010f2614800c0c0c040c246140580031902504600b4102d112400c4c60340030036581030481d0020345400d001c1840c20004190b0500e40050f00303890f080b02c111403078840b03060402d6480c100042e00140400e6400010140c0b04e20844564030782040340802c00040000c0481d10800c00c1d04a2005021240b0b0000c0c0104241d428401204c0400201c141c2210f1610713000c0141100030034060340301c2a400d494204420050007010040c103524624043c1c0e590001c01c0c1480702514140a00811403041c864050031915840b08443e114502c4200380120b8800141282d508242c104c0200841c0a20310b02c0301c002c11114415500404410300d162a0b07a81c80c24423603400080382c1000c2285042103031000070009803595241c080004000c0c90f12600b5800c16008a841c50714190b00f05100c1c5130752059901c14040038040d404240d804040b000702c100c0b02c01190180c4900954141031040160010520500100385034170384100603030003044560788030400e1160340c04c4204005412108140071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201186636 1250 201185386 201185407
    0x503010c022509020304231c0f050417150705090d0f02010e0303040803040911090f010e04020c150a060906030c1404021603030b031005280e0a03110c0105090105 71
    0x50b00241c1c5495521180c00d61503803039040404a800a85048812200c82448500b004004040e001f03040d5250340050019445040e0a003807108a071101c4400078031400e82d0004a00710700800642c0c0040440a01030086c1040c0c0003840398480b500501c100080070845d01c00300e04143d1151342541d1060101520440e02034105845039a440350701d24104034100548850066501d0301d007030000e04010841d00d0300031070310b55061000400640c0c00c0d0441d807906e415024480c04403165201c00685140d003000303083c0384602a5106d80400c001c2c0c40b4440c6219480c2c41600c0340303140c00c0000041091300c00e200005041045580720341031001610503a01c80907142d142c03609810310203240d4602c0741032205c0e03000400051818014045113812003100340c1381900071a580d8150403002d41010f0202c5e11a80c04110b01c01c000c01e01c7c281c0581170202c0e0b041940d4ac400c9103001038814181030403991002695868240460707080d5070396450002c01c0e00e909400d244015000d100e4018055500034015103441c910f0586440c0c0c1045e0380034a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201187886 1250 201186636 201186673
    0x40e060c250b04030807270b090312041d0106050f0301091d0106140a0815160207030203010c050d050f0f0703020f1204050607091505070210020a060606030509070b093d080a060503010c02 82
    0x49d21035043c0112940300c0c0790540d2500061000b40169810801c0c280015085480054816880402071003c00c00591008040803000c80741540c81c43d1200180c142000781001d803c45161a014858540c40c10802041205017181e402409850803030f40030406c07903103500500d41c940701c1d1403c04050551044001c2a403d9070f10f1842000021980c0c411101100d640b5000a400d45112006034804100300050303c500c2d8a050740101940803084075807100e99814852190154400018240000c1550104401080501480c1101e01c0c0724904901140d01341802c1c1029030f01c40000340c030a030b004521141400a0042802d580341010700304952142400c211140d020b1054209503000c03007100f1401a5008140012818031800c005460550b50028452400c841200e14110054011a00003034060000c83c80542d24044c0c10010280c80c0400c0e01e0350503a170f00c80c1c070600d04030005c03c40e840c0d5666400c4d10b02520940c4204114891005d258060160301d0f9108189070807a60300303d0020005811140fa40c182c0c0c0c08034079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201189136 1250 201187886 201187897
    0x6060311040c1e0f05160b01050109080a0203060417040515030106020c0109120b06150d050402010923040b040207021302250f0b10050402040311040e060c250b04030807270b 76
    0x17414090b00d082150200c1c07000c1c05510a004444002c0c1100051003656444001d86000e043c144000705039550035600080ea41c0c01004100500704805103901c0800003a400003680c009100261044402102001900035035400074011a00107110703030070b031900c0e0310361241c07a00d1801c954250f403651a0414a076140c40104480092515401494100c1c1c03010520044000034814244014030000e981d00f001d100041184a141c4d100400601e80c241100c5800c12444070b503c0d01030a07044800040c00e59080010030003030f004070b09c0f020b940101d5001400850101c1d0b41c008000540340c420b64901c007820080f0403846402060800a0501c0c460360006500140c0040d50f0b054220408102c03800c40c99556400103016607105400840326414410078103c96070070140180703074610000f82c016181515117042c0340c1c2d01500604203294a44034510441142040607012011a041e80017415400725103064180079002003410380da81c4000480d0038484425480c9900ca8401c10458404082c52050340360000f040001d070400b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201190386 1250 201189136 201189167
    0x7140f180c0a1704110a06020d02121b01020c06041e08070602131707060810143318040501050906040c0306080a0506011d090a080304060906060311040c1e 68
    0x4107820010b110070746a40743e441284a1116a10564419001d1103c841c505601c46010b550040c0c40d101801a0040b0390850014050740c1142d0300c912040a154400040490841055500c0001c50018403c008102c2e24401c07400b40c0d110031310785008549101004559903d010b0b201c242c0506c1001c002521320740003401000b2228408e03411258448600d2892070342d40740e40284040c1c1c0103403403c00c0900c0d08282030650010810031900e004030714024044607030035452869a44549401c0310802c4500c098030341840c0008200f01014054284c030882184416406014441a0441c008034548a1481d0502403a030503100c001d032602503a80c4420f410b12014040c070024910a050b10b03400041035242e010058000410301400007040c01e540360203007100b100210a03000080c2e840d1741c1030400c44280b00c00035451b092203074803058140c4d50341c0e242d040413401000c0c03040006040c1c1d42050300010074007403001c40803c168081200c0400c6041e0703015009444070f9199000303440c1d0070000e01030801082806002071b6030f0003188 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201191636 1250 201190386 201190397
    0x5040e04021201051602240106051303060203090102040315020a0f051b010203090a0b010e0f010b180415080715120507090e040602030f130206180f0307140f180c0a 72
    0x10418030720b0a440c4c00f200c2c10201203403c4004080c01c181e04020038188912240c403000691a541c6c0000c0c0c25418050055400340f0500182685001819102000056400c02411500d0381000024103000c0d5000d803109070ba20301d03507882007803040c1404c41c0300b100c48120490708d520494603d400001c1d00c06801c98030104d0340350140f075200880c038040280003c5116003c41e00191040200d03a2419644020068203e640140a00010882c8030040d00144905580d007540034107888888841c401e4071210310b45040d260f080350816143d0a541200c480f401740a131a80c0710159074400d51102c40080c80301031344001c807000107101485060042881c82d0b103d036402c8a003915014144a496900ea00c10f201000d45049500e654000308000c01154030205c3c0e81d400c0980d961154000030f0705a0001180e5000e0402859601c55032403202c0041c550360107083c64030307810010b0f0079919619581c1108480100d16500114042c4010381c040520302c0c038014a408880d24070304000b080440c1c44d100c40080d01600305001d210203100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201192886 1250 201191636 201191659
    0x6040c030b06160b010b0405130207020a03020a12021e1309020a050d08120106020712030f0201150b1b032a010b060301030c0501030b0907091e05060703080912040605040e0402 77
    0x12242002018160100842e0b900b01c0d402c3c500d0044100030051344000e06000c8184006d00407940d41010680000608403030160711400a0b000090241d85642d0000354400341c6500009542c0b800c6552440b0a5402203407200c295164108103415401d80c09960254000300750958140541184e80c000000140003030240c24000303480b030f804038081951118003903d0715800800c044003a00d09074001c3c10301404c418805811202d00d4000200d0510000d81c2e002403e2101001342410711610035403041c0c40310441c040e54030302c20940d900000c03101035120100401a580000d030718402880000411580c903a003546003000790100d07050038804003035003030f0100d4041030795207844c9024416594100690f01860107114014286881c290014044565440380d01d0302900e820380402c001c15170000a00c40c2240e03082c04400000c52801d91100780c1c01401900503e41c0400041042d0060680c000c81c03d5120300c1c04003007140d10040b413030308050540b40518410080003c42c100018049890b0441440741c02610280022a024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201194136 1250 201192886 201192889
    0x305030a050310090b01090b070213110903070504140f10090603150f09020f060901050c0303040507380d020409021606050615040311030a020904350306040c030b 71
    0x640c003a00a500c00580007105019035101d401c124040103110086081102c1c142c018000303008040d40d803045d8030340c1c000e0201c0c4110a544a5680d40300d081c00708001d007040104601004003006400424070b10b40a40315200002c2120708092052080079100341c1c03d03051aa0381c81584015030160f00410100c0e09843c0302c000003c00c0d580a0049a01030b42c03064004801442c0ca0307003102c01c21142000e582403285030420303401e0805a200d13100078400ea000d0a0790859a034500b19401039030f0078400c01e1458829484000204000d000c2c003c0342d014155055282c02098520401510445070000c0048822605d005188140f0003030348140d00812410318124005800e2540d03600310007049800020191040101540f0901c0c10070449110702039200c0401c48000100c0040c20845018a0140f404010400030100c2078540460351308000e1700d00344550003005d95075107103013514040d0501d00b84c0c1c0c0e9511705488103402a100c0e000540780304440c07840040c1100182140e07503050400002e0003402d000802810f80e2105025041e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201195386 1250 201194136 201194143
    0xe030901081909210f030c0815030708070f0509090106030b130c03080a03050906061e2403130b06030606100305180d0e09060409020102071e260d030c0906180305 71
    0x1901e29071184807159850720b01000c0d05c00b10313150711524105454a11400b00540d005020150041d00c42c070780d6801040c002d0004285004100d42018500784a502c000107040d101c44607000c400d03142d081c1c6a030326003900d031034040e58280c031000d010050072100e070500080c1c003101c1c8244800d0819030007944031031000f03652030b103500d03503264081c000d0000000c1c2c941e0200111520201714507608810141c65001003210f035441000d010341481c5513810710452034042500409802c140c070700c8c3d111710f070311003209650790514500b008810070140e20125409181200087e0312898041000d034400c0401820002c07030f28400f040110b004000092040001000c0c0b02d4401d041e060040101e03408005a82c4c860100f1820002d0070824200f10090100340300e503040000400040c0d03130200f07041c0d0888600400d29058074034100c9151030701d0070058004280c034064000c0c10b40d46c4a40c0c0410b038082c0c1c03000721001b0388508403a008801c80907142d0824022001c10303421081048101e219401c1030200541e0403581d895015180d5445504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201196636 1250 201195386 201195413
    0x40c1a0a08102111130e06070503010b120a090f050c041d150910090303060e0a05091e010b06121506030f0f070507020d0f060e030901081909 62
    0x154564040340c0c498425400081064008402c08120300d009071402c1d0646003c0c440c501d90004500d00703c026204108204408040741e0090000e04c80d04010b85107040309002010030300010308251041d03001185019001d6030031203040c3c504044405240444050170f01d40c07041800b0701492400355a85410038081100c02c402ca100445c40f90340500801c13038100e8104016192040d503009070102080102c5c403100900000c0b5240700c105103005d9114982c4d5020815401e0400c00c0c14605605410500318208050341079000506440c00c59448880741c0d1a00703a141411207408940000150380040070003544003100c0350880304402680400450400e00c0e078008030b400ca800c10040081100340802c24425230081800900004141c20b4465038114544a00d20001030f4401401f452010040c510204d441c451044048418040d0041c02d19410740107189464450001c200780c0688032180782c80c0200ba03029401008640c0503010513550b08502da01d130303d0079003540e900e6503e60000d4425590740001700052258000f2a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201197886 1250 201196636 201196679
    0x1d100c0c15050108010608030a39080309060c0708090f0a050a030b100905040822171f020405060703030b2107060e0103050610050d0e071203030f020301030507030b040c 74
    0x10350f540352952030303420b503150740c1c0041d41940c0080c01000728007948228416501d400c140001000100601c201c44104405249007a2103181045894024001d403200150700a5810754101e4101d560f420949881c680101c50000702108400c0014840a282c82e50861080300b200400c0d0490300c1e0b640f03900080c0300c50b500c2d80c01140d07504102020033881c01c1981a4030300003880c0e03880d010300481c603045e5078000803441140790125104c01504001d02107a11a030050364043c0803a6006401c509096004032603843c6840c0c00c1c3c039402c01d104804211958215402034bd41102c5000d00510706040300c642e8140d015115003070610303420040080c829510680d090b03025640749520640500070880c1070010003010140c04078020780c180740c20f08007401025240c544e1182006022460402d4450002c540c51034041c02001840d40000d1003404004981503007101001c1c101d2070f03c07a4500b0412601150203041c2039010901c80501140c201100401c04203813480a030681c068400d2a40100c941c0e01e408110070b44000668000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201199136 1250 201197886 201197891
    0xf0c0f060504061b02070602011118130209150405120d1d06090a0605040e0a0204080d0806030c040504050733050c030c0a0605010e0a050405070618050d080d1d100c0c15 74
    0x40141c1f03902881040c2201d14041c0e000c0707140080d140141c01c2d024000324403071800381c642c41003031340034141c0c0701e5040d51040b20f402040540500c1035289000007a0300640140d5220780c440500904085600081c00c490300003041e140d9881d10b60044030314400c03151103031242c6c6401160410903005540e681d9011080988100e407101030300c8a0910360003209100d0014680d8042c00d1040009101c58480018080c0001401c0c2ca0005002c1ea510760200c0d040076528401b01d9009410207052104100340800c03c04141c1d40b2070141c51120080a20680005882031703410f15600c0c02248038141626845100100380790740d02981260704c0c0000c3c11760541d180c144801d405443d5a942c420060100d01d08845540d900203030b5440c01800b82d03080503203400341c81d41c2c0644141018044510031014828a103012001e0040ca03000b40b040c401900681002900e680c808980354090915141d0b0841e00004204404941d00c4084001000d000010b016001c0090030256110001d001038501414001400740300401d10103804d54401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201200386 1250 201199136 201199139
    0x6060d06020d090c1805010501020604030504050d0201090e13330506060c030417010c03062301110a0308010e09030309070b0703140a030b0a080309010c0b0a06090c0f0f0c0f060504061b0207 83
    0x1805c04541040e0000d40c1190810b4003404042548a000e4405590080702c0103508498180700584000c01e541c0d00440c040e900540410000781c4080c0e05100605014400714440e201c0e0181c00d0103607445040c0081251034580f4001c03041c50034103660003541e0080f030182c10310707203441441106189035030003d60082c0300000480700421510b180038010482c00b45081d04050060b035052500700711107040c840402c2a03a031174008002c0165030784245910007411480d6420344003031084504004001640c240603004613030000d14081041840d0010450313218400800142c26070700d00f4004201000c0e441424142c3c1042060a4669241590740c0c0c010000c10f290b139180000c0c9900c80c0d0040c00181012a4411485034006000b182c6a90342c21074030784c400061f40842203010765901c003021800100081d030018170003946007042c1f020706075800a1140b03402c0019034640b00c0c04001c15030002c0b03c400d012000c0092081c000801d0180c0000e01580205412034440d0101041220802c8880244901c440f5400780050303012030340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201201636 1250 201200386 201200429
    0x303040c0f06090b090d0602040602030a180308030c0315030102030a1d0607120902180406020721021507030912080a14090c191a03041406060d06020d090c 68
    0x80030004108858050158a01d01203010b03207884058415a04828030010355050741da510f00310000b0308164000011500da071745544000356a0b0304854404404114070301510b0340c04122481e4100d08a03648240110710b07607a2000340d4510b00d60800780642040b203060004010b40c83e5401e00103180700701c8841a00042004026a076014032003c2c081411109401070014400b5080e4494981c45408058140c0441c000b0341c1072010807910b0004002c2c08168440540610081014075002024600d001c0e04161401054058110000150040082002d644405051720358080541e04c2c00d90701c03c41c0c50138002030b0160f49480742c16016060040400000705020100329a8085c0c1d88a401e40d00c8030303540c903110300b1442c00c504400c0c3c4e1440c100d513203184034205400c2c5440380130b6912490f90014180b0f02c00107111030b140b60b42020b9510b406c1541c00315070000b240c0049a1a85000050041c81208000d01411404100d0b40f1003d00940c403100e40246502d0315078130240c0200700071201c40c10080100c29800b040d4007843c0305 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201202886 1250 201201636 201201653
    0xc1f0b040615090e0c07020d0804060311131401140706050106020f070305121318020304030e0103020712032703020a020301180203070e310b060102070506040b0315040509030304 78
    0xc0012404400e150349080030a83d004684a05030342e41900121095124403a440400d8040d07604002d5001d00807891480401c03a03240090411905180c40a01c102c0303086032000031003070003400310b154490b03542080100080e2140d00c00c1903440c40c130107050840140503010281d0700e003030740041c1054900d192110010041039a0400618502d10111400b0f8464141545d44d0540c0361004410000c001110105050903100704d085040c0c0010424142001e480d5585072203088043c5d04210707029000700e10341c40e005a0b040e501034001c82e001142e0081ca9007400b24000c0006134010001c034000340445204c04a1400d06007807039074a8030411240250010191442c0750b104040c01d5030b440c138144d007064806075010840140c03000101d9030150358200c1035045260741d1311422035610710381400c07100003424400002048044080000b05800501460101c20a0780d1a1401a40d03254401d106c0c8640040081004100c036100d408080c64201119444024002603050001420b5030019150710710503420001c02d2200f00245074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201204136 1250 201202886 201202889
    0x604210b060a050a03150e1c0e0103020a050406030e0709180b010506040305030f16050105180f0706091401140d050603071205120304030201090c060f0e150d020c1f0b0406 75
    0x2c45121010b40e0900d030210308100c096200c0249502c180b0050300d190101c0301e8012090700c00811040322100400f080300c860110604030340c107801007a5940c0280919512074002c03600c40c171855444892805250101c1100245030b84589d404007402800c0000c81c0004050107034088451101e04468104501401d0040060300182d012601c980c00805c003c00010f000401600c0c0844140354130750740c0390303045804803d25040702000010320f9540303403000b0400f041d030385010980340c400002000c03a240008103240441c1e944500b03010308004581c50b42005c1000c040d00c43d803211058401894440c10b17200b00c00c10828115080304c007084040a4840e000c01038281400c11a00006010000342c01c1030300700440d00c0d41c2c0d40703c00050700900321036100000042c042c58002d40180d44059400b010424915540c1c0d840109030a0789500b4190014103407103040c42003071819240c1030f50420801d03000c1e6450302c00b0f40070a16009602150140160b4043c40e2010f10342c101c04c14421b071090003180c4002044001c400400c000490340903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201205386 1250 201204136 201204139
    0xc0109032a0c030222060305072d0e0a14010b04060f090b070f11060c0a02011b020a090c11030a0207030c0518060d03030f020c03070c0e1b090604210b06 67
    0x801d00c04008204074007010421a90103850340110b5509038140c05040c003041502c001000c5e130400c0d00c00801c0240c00904d00f82110505904610120b010741c8682d1000b00c2400c1e05e00304901e41c2024107200380c3c04845131003600a00d000304005031081c0310505600404d04264007200201a001c14200a250b4002c05425100e10442c42d0a9420500384000c03910280220300c0c004d0417445181e99800100503600d040c00d00c0305280209940d8486007201150780c4c4d1402218812030000c0d012801881d511421062201d500560003090404000e040c509804020051300c22808208010f005100075026824002030003080025409041e846040d82420b039403040841d80414095850000c4000d41005600d030401c0d0000c10841e88403c118120342001c9002d010040c4404440314400540e0b07102c105d20001c0100801482200144200d940c1c451210340e018034222002d9404802512503000780e605200000c1001003002040941800d03199070240020860314140160710103038400e955018010341c0c95042c2d921120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201206636 1250 201205386 201205457
    0x1e030504030f08040302070f090c0e0f0310020705032206170c030a09020a0305120403060f020309120705190c0e1303050405040e070909060b09010902131a0c010903 72
    0x28181e50040421031000304450401c4004008075080510034041400140990524180040e0b2150b010700b00518054030200045040454800600d0806400c00c1c00d00c0000100501001100a00d050020303521a0400712003d020810241003400c41701101525a42840410442801e0810802a201074444688054040600000c0020402d031180480340d000641850102e14001f00b031020500c083c941d904000d12600502d410400980c18072405801140d0290307a05000310038400000d90300300d200035189401a504503180c400e2006a140e070091003da8070600031921020f400388a044180f02c6c0b8090111045089607004000c0441402e0710503401c000042c45e0000d05404c81e503405422032042e032240b64000d039101ca0131001c6660040c0001e100034608184203001d50703100c62500c44001c0070b410441d07502c0344403d40c1c00413941e400a4404e840b601303a44808100150b605180100241c0c444000c0d40f00060320003040807400d00710342030185580c0c25100362074074119500520190741a09100244401fa404ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201207886 1250 201206636 201206641
    0xd03060509060607060906050a020d11030402060301140607050f03270f040507020709020705030705011503080f0304150c0906090518010902030a02040b0c0c0102010522060e030d09031e0305 83
    0x79112000d040d00010110f5643d5910019440e100d00600a50031025081515090801c041e80250350001c001280508500300f12100240c1031442581c001654082c2d00840c0030b000503c011080c130380140110000c01801c49051403080c1e1f5032038bc13070a03203907610034200780d0800305201e2442111420010034400d14021b000e285440b080c0c1c00b00305880c42101070140b16a403550041800a402801200040c2088800079959400302d401c225540e40d211941c103d40b550b1a01c000e0301c5001d0310340680b01e000d80f5401400c00d031074080548500070380c54001500c00c1c0c540c55034144400c0c110b20b00360b10410080302425201e610030709141074405003814010354081c6000310040c0c5c0c201c80c480000001a94156800361b040140c50340c495540e03100c0203010b5500251042a0005104612800e0001d50400030500990080c801c560300c460f450005038000d40304600508540003030380c90004245400c80300440d003c08080702e0811300035200c4002543c01a034011f9021620f000740e22000001030307903004030402020742000c0c0401e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201209136 1250 201207886 201207889
    0x180b060c06162c09010906060206010603020d110d0e10051902070c030203121306030603020d0212010f0513021228030e03010212090c0409050705011202070b0412020d030605 76
    0x1203030001c0210445072515400c4030b0069009801d081c9003202100c68116105001e41d1680b20420014001107100786091030001414202901495003a140f141e0701411090b40f07040c0c8190080d400c5404a03480d22500e0720354040074520000064059090a104007040c0c212248401a003001d17840070302d806c2c44c1410017007003111740c0030610002000050484001a81c80855081298890240340c0000750705000348000304491461000141850f4852620503032225036840c0c0e82501128490310000750031181c0c248002d8050300e4092207559141c0e1507500045070200201d0301d100103e4030202d514116800100182900b9030800442c4c4c524507003201c2c0000e1050903807295030502490100b600c440c0d142c5400d003342c00308140c4178640702001c1038000742c0255100d8201503e2080504803c5a0010142c412805060b01e0307031070315008212910b074001010300b034454206401100c0c403280405500070f05a408102e0710b400245020301451089001e05800c605094003100000c0c1480f61100803e01010f00300b40e41404035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201210386 1250 201209136 201209143
    0x30e0c010f122304020102060106020607020d080406020c0f011d07051305090f01050405060a051f0e0a020405031b040c1d100c02180402030d020307030234180b060c 72
    0x4a1090381020b407190002c1d00c07100d401600e0306403080f4180443e146140ba01d9a00310b0010703035003c4d5200343c080e140903a0f01c0e408c04a0384c42e64219070140041c1d0004540386c0116000d10081034109d4080c600242c03410511200b41c601d010074640e10b294a6a5440000101781143c22507128004040032003d080c0c03161412000034940c1812591f01401355682c0c40209560384800c0020410000314207000707000341c0c6028245030b600c41100311090910141480000f84000b03451407001036040c00a007250f2481241408514108014001c11480d1081e03801c220202e50340c2e9080184102c010440708000040703041d904d00707000540f451800c010040c045a18440c034160b21154078100040d16040d034082d918080b00500440340951051406034101e03e01041c151034400d0310310040d5124600980803034000d0340303c1e50003c82c0d4a204051001e001608005582800702c405003600300d81548a00c41380e41c032010341410b1a864102c03440e034048515075038180a2410b0080701c0d80a20b00340708000f00c0380f590400940f071800f1510b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201211636 1250 201210386 201210407
    0x30406080a020c07150804060f060501051204020102010b030f01051e07091401090f15200307021504080f1006080a0b0a05060d060204060e0906061306081305061006030e0c01 76
    0x5801c0d4000c540c0198050040160000400c807410160040c0000320102a141542c02d40301070b281c060400c440c035440340c501800307103000b2281d045e500c681c0750080e0684910410440607104074115500d401075010302d0340d0100310b40c2c170005851800004d0300b0300344202041145a1214600f02103e6144410402916082042e07001158800701000641741c00c00d1004031084200f641083c41c182d21003031008224034030000c002140e846060340b94003164102100104055428035000d030210f40d0f000300704410040c20140500ca0400180354911070400d6258240c00d42000c080a03071b240c00b154444401c0f0025402c0c9405600000c10410029200010180c2c40313a4481c03000050903440082d40f5440420050307121110344c0c0360440e410050441d00d550712000000c224510403802c0502c1450f8003004980305141070822600b10486001c03100e04ea061034440b094420361802010036000380507800004010440c01e00809109008082580680d0750402074040c0440c0c241040d803844d5540700e4410ba0b50b90380d0700051400d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201212886 1250 201211636 201211651
    0x11210903070f0501060506030115020606030c21070308030f070810030b0c0c0c0a0602010203060a1e033801150203031512010b03030c06041110020c0f060903011410060203040608 78
    0xb145284541000350140240398091504074800000024100660140c0216000c000f542a42d0940c0c45441c201540c070088203480552041c42d00c402c400100d4ce0750642c01014100540c199070b01540c0c1c90f199502d282e00300301c42101a803841c03841002800395000c41d0007580a50b881200044c014150b844400d180c0000610310489010000740308408003004101400c0c0d650402440180683d8840800074042d40040d40c00900134451881c010903444100c1a040c54201342007600d2103500ea10350745070724698410315000d0f404d40c3e90110000302d6945000d0b4200100165180308180c44a5142010b0350002c401e242030b00c6011500700380b043c048241603603030724800b0a1f03200319480780000c034003400740c1d03401414007075a6180d1520000946c81c00c1d0141c00305032581f003540a00e18525a902d161001e000f074940c0342c80041c0d40180c12100540115181c805c10542d01654080c0ca100d04101c0c075100400e0031038800407644168132501000704807448a01069035009000544059424217141071b0000d8480c9102a0104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201214136 1250 201212886 201212903
    0x90b1e040f110d03020a0b07030908090d1106070605101a0a0c0201050405100e040c02031c022203050303181603080304080c0d0908010c020607080a050405101121090307 74
    0x2200348003080c0d05811a03008003e2486580000030315000c3d60301c1c4650b0900b01c0e401046200041c00d071600030b2240b003803040e80041183e0b25040070001041440012503c00b11061071500f50515011344139003014003042c40c0304032400101400c0c006e00c040c8072a80c40d9400b000b031000c0301180e4012124a02c005441034108581000c22a42c5002d10041e00c05010300e4019035000268000a45180c540c440342040400c4000c9d01e00b040a00404035089072240f00307d40100400078082c1202120f0000180e00400d4881c603080650029080e408841c040e100925a20a890691011041c0802d01580360420081d1030101d00003001d880300301d10700701040001188006030501070040005420b02c034640742181c600d00398001c19200c3e0182c54078400341902d1040c4c018440f0541c40d0941508120303000107441800b8117281d46410f251942c2d490042c802a041c000c10480d6140a40540e0b003400c250540260b041a21401c0002500c03031031050300441460343d416503601081048002403107032401c00071044403245900030054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201215386 1250 201214136 201214163
    0x8100803040b1c06141309170915071703070306080a08030103060c0c0b1302040b0d1b0b0408061915060302031906030b07030506060c0d020607030e150c0d060503010f090b1e04 77
    0x42c4c40c010450a8406000c00a505000b00d580b8100c400091200460841701002c9a80c6d40344403414081c0a0303840024650a334a580072810341d0001e80107558800c01d0b5180108007242ca4142090504071491402c032031301b84002c401803003041342c0c900840c1c5400c5000e2804851308442a03c544d420f01e41e000d45440750401850b854882551511307008008211806800600c00b00c1c418540100706900750344903030012001a80c0301151481140085504540c403100c02040079803201c20030a400950883d141c418942d68900c86800d0415079190513500800c0c9580b001600c070725051080c0307034054003544080c0d60801d04d014000d000140120002582001c02480c00250030342d244404907500d0301c52104000340070320030400e20444c03040c0c0c0001d6180c440c08165405000e44d0b40710000640e81d400d009481300e07800501480010301007501440140072200b1f1203d2020031840e6841d004030b400c4540000c010b0b0001c03520340a0f46400e12003800c652a4000c0c282010a8254050070510406019805003004280400703e000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201216636 1250 201215386 201215419
    0xb010806130305160b16020d02060708070e0a120308060108010602010903020627030403050304140904030c0b0901061e26070b090301020f0c030c01050912090108100803040b1c0614 79
    0x18400c0d9856021a1500f1141844080d002c0706c030400800c1c250051103002240d0b40315500c0440c4882c00380e0003c1d00c0e140304540300e8400546d803002c0300486480c0c01c200c51a000183c0540030100c500b10f130b54029150b540f02c50070600c000404040c01600640250381c10134106400099000804682c0404410140e0300c201d000c10701c1500c0303405403110150a44e0b00c00401c0c0401030207008801041101c1801030101110301101c402d206a4100c2158044d0204031107407094004a011812a50f078803611796400065156281e81203016000c202d182c00380324080c002102071001c40980b40c6030007144800c00c150f044440300b10444031a80e0380713a03e01070710b40b0401c0d010902e0303941c5031404d4054903000b1898007100364413a041902c0d042d0703480d00308000c1c0100c113608040c04a075041d840803c0c40b039400b281d2002c0c580d217000c500342c00540b40c0da900900803540d64001d0a80025900e1000d0003e04082c144104805a40d1001d0704070501d22070141035500d09190307203801c0080110148039404602d0900d402c3e561207501041126 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201217886 1250 201216636 201216667
    0x10350109060905150a0b100509031e0c09060411160302030f0406031a0d050d050913051e0f06030c0d02010302120106210203060d0615030f0503070b010806130305 71
    0x40c00140550306010350300c010450041440382a00d015890300ca56980c0d0b80e0020035054030554440560000222040046218401c40043c109400003601b20f41200052070202c00e150071000c1c0d010440c9800510861070586003080900c0e810140880c1c080c0303c41d8020800c40310140c829103c804c145e026820282c101014000d1007601c0201c0300c3c090314075484968401001d40600301102132848000d00d40007221000e40741c4000c20109182e080002060350300c0b01241c0036500c591000b40c9082c0c2c0130745060010003159185004e810b00c290807012241c1c1e2a5103c45020060011015118100744080d800800210781c800060042d40c10f05e0841d980040c0151900068000344601104001601c000348d0010448070741200b5044651001401807200001c0451085002c07400140e40700390f0700194207140c0384007140141d0002d1030f10844000145400c0384c0d80b99600007680315407440490b010342001c603080f000d00022504480c0108020b50107440d0604c0d00006182d86101d1455008051080203e18000d00e2003058 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201219136 1250 201217886 201217901
    0x90b03060610120903050a030e031c2403110111030403050d0c06060801050f01050307060e010c060e0f19210c060e12040f3f06020904050f103501 64
    0x20400c884c1c802420300074165440303c8010000710341048003010041000100311410015110340010440168000020180c5016017415424241c1e46115410080c11070440fa801036104160080d5408860800909200c00d00322100816820911003040811f101107544c5050483d145001c8035035582c0f5180ca2402801240c11a003450740c078001c00c210040d0404100c0c7c07416500201e04480003d6030700c400858988000c1c0607000e0029220103100d200180072038006803c4010340c4003d4900104880740840d1030645c0f00c0c040c5242c84000d1050700c0c014072a00f049101c0f10010790b6904135400b02c2c40c4050240000c82c01c11002400f10755640500008240180454845015240300c4241d8446d6203100c083c2d225002c9000785495140c00e072141041040369100082d40d50000c08030003001201802c0640030031005108016140c29408000100c0641d556204640c4111a012400160350410202c07519051445400c1a41c2e81c51a0310040c04040426200c03528200301d02c0c03c0d01440c08000b24010070702403e1030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201220386 1250 201219136 201219167
    0x310051f0e03101b0806060414010c0c3f0206073f180609150207080106030b04050c0315060402090409050a03080912030705182205060a090b03060610 66
    0x4200400100c19070801104c1c002d040030b036991184035103c0030104805445a4030400e44140b0064003041c009500510b07040400303600944a0441e05a51007000d410100d00368050b4001c40b04c1174032590102420707e00300074050f915000c1c4a641c82d05440350b01290042c03142c92406008505180291081811910000c41814018070451410307070070301e00500800303c0340d40302d481030105111689207081507101138401001c03640e0564071210040d10b015070b0b1101e40005010b6003030850081100100d1419001d000324001144aa8081202d5180504121f0306080d05051440d10035000b001024880c88404032509030440c400b101d0040c0c1d18a000000070b8001c0c1640703c001007183c041e020100c014545c2040019225152550a5440a415004605c0f030140b004403048008036a0a00c0307183c08082c2c0a40c5084541d1130003404026811701c0082c13141e401118248650081c46880e031007006204c0c28040031030802460626800d008840c10705000030344a48008045500410b08000c044040c540705d08071043e100b251 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201221636 1250 201220386 201220391
    0x1014070c1112100c0503061e011205070e13020a0207090f090c080a0201020601080f06012903040615080c130905010605100e0103050708040b040b09031b030310051f0e0310 75
    0x15840c0d240391590b5a00070003030790f01c0f4a440c0d420004140a20200c900c01d2000400304c4120044550080c0b4154603800800c070304101c05210210380a04203441070303a000304d000ea04d40323008030f803414401c005086600c0c8140b0b10050b0f0040c00340980c46a0001560803c0da0711a402c0451114070080c000c800402c05504094848034142a0004102d4804101c0c0003026000b80d00356906a030b02c2d03181c0709940384624010b5510a91000c00100175282008074034601900b5450599000d50302c6603001d540c03168205030303020380d0360325070b40c0c0c041f807240750171040c852030041500d42e01800d120400200000d80c2262540c69002e4002d8807201d03103c080180030341c03102d405000014064416020101d07001803081100000741750100e850702001c114100e0203445d5007482158060791242c00c0c0e650b6660784038603d5001400381a418071040c013080d00246c1d00450b4075605100524011070712843c1014a041000750ba40d8041400f42c4030103140d0ba0a00d10701b05464905a144078203055142100d980c0210f40361806681980440a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201222886 1250 201221636 201221659
    0x705090303040f0e0c1303110a0e01150f08090316080f0304030815240d0e030406020f060a020705151b070605010905150a05040e07050402040b04081014070c11 70
    0x10564500340c0150b034581c4c4d107008199903031844d1801c10f51103081c20402d8903c10340070741040050000f031800511201c000c2d1600c4c544a0780c0d0b080d1014040000e0700f0500d03c241c00702c044800f029500504429a54403140342903020303030400f5080c107500e82c807e600103500c02c2d140c0310405105000c003040071982c0b1443c0d807506080e500d1419080042000d4010b6807000381c4000c542031000c0b02e40c074161602ca101c00c0701e25840c1e98a000704a550500b0558000395809001070703103a080c1c481c00141e05001802c0109099009000c95140b400311060900074028182c940d501d1041c0800000b0903000510701c4820406107241c040940c580d4403091203160210b0080a81c03481000960008118203500024100c924100b400c0c022030719140000e0b05070a810000c40303030b08002900d00401c6240382c15000900b070496044103591101c0e4490740403405171384c000d40180d110b03083d00003400c100542d010000c061843c000394400f00040240805520a4004050104400c01c100b074100700c81400f0058415200c000b10003029414140e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201224136 1250 201222886 201222899
    0x912020a020a0801020702011218020307030b071b0b130c09051e1608060415050d1218150e1c050d080a0b03030702040903140301060c0203060a061409070509030304 72
    0x100440030040b4010301d0503140020b6082c07014000c0e5880e030b0b58140c40710000004030518281c018081000f601620b990340b141c1d60710240c2c0707081c44110090340c0509072800b038a240801c000fa15903a89480c202800c050710b110f100c00031075010036419400184060828406c0d01e181d05100c50400415004111400c0c988030501c9a46417100c00d020b0700d041800119040d0707613a83e05c281580265490709851010401100c0041c000d0b02c0c180d403004503840b1813662408241c070703101c0b008181e4896015804130b03181f20015014400298000d6001b0000b840541c0440122500304071080122000b0035025009202c100c442c00794440e82d130490f00881c0e00c103040c1c0c4e400b0207802407030401558811441c0c4190b008038010001140c07044002e0700604080300d101130300a51400131030750300340401000c10140a804000e0f4540c030400030f0b4080500114024521541c60611000803401010706000001d014021f6051811104000c85000030034482c02070740b0308031343c0c4e4656a680d13100103503060704c200b292003945800001404580d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201225386 1250 201224136 201224143
    0x50616170918010312090501050d09170a031508120703030b2b030f020303060d0314090a1701180b01050f0a0503122d34030801090e15070f03091202 65
    0x101c0380142d80c6117036000d1940e44161990200341c000d1900040c402c01141d000c0d001d041c0c01c2035529500c1440f49000081d182206440240c0150800100003519401c120f00500020040c41002d003103400c002c1e000d00b03017941e50289100d2040170001000e1580b95907210140d941d0790311803000d1181d02d141c80381070040781c0d003ca100d001c0345082030107e022603000242843e559200009070382c407400028100703401d40440d40d1001e4804071007d4075560b9100d001040b03051090380f180c407400d800508108a80c0c07a480c81f94041824291101800115605030001d40308202045010641c20b0442e20282c0c3d0f0400301c4103900300490356210317060704815014071481d81006040d00807500249219400c0f1302514402006025048031098924040c083d035100050002003424022001c401d0202d5050760100d100c1c00403008045d11000051641c2900480d5100004000501d40d40c01a10405000b1002500410f20070f410745104441016021004000c2c0d80d0020003640d500070b900c195a00c542108900d446082c06000003503a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201226636 1250 201225386 201225389
    0x6130609080f19030902012007090204090606020709051510170906070e01020a08071b090f0203040c0603051603020c0a0f0f0302120f090402030601030b0904050d080105061617091801 80
    0x383d060101030041c0e20b0910034410f1105040d8140d40c0d0359140b014000c002c1910395041144078400b8001c3d901e0010ba110340f184001c0004081c0d807140420114a800c0340642021034690201081034100410003c000c50a154000081c00d811500c003016008040d60860310074561030307068401095142e0038890f20110016826204003565512050f1819034200126140c02100030010003000e0309100203400500d20000708490002040748404555560b460304806a503411b4984050319603001003844184201540c3e454050071312404c0602040c14460302030800604100b5a000400d41d011400c0741c3c907a40280b00703585200c0e812101d03011141103d41800480e40303510210440240c17107030f04d40e210420381c000703010794980d0b6a036a20300300c2c200300b90001880301a60000b494681015a9a00380e400c0365034030600d4050190f40070ba00201900850f4983c05043c0c0714041c0c01091160130103114a0784001d408044200409920801c0c003400100e07103003440e040c54081e01d010143d03c441244d105907802024014510b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201227886 1250 201226636 201226657
    0xd0204080133120809040b030d0504030303110f121f030c0f0816120507090f0209011d1c020613030323090d120c061b0207051206130609080f 62
    0x20700c00032420032415581ca420f84640d10558440403481e0002c036240a018000c0c41c10060710209410030340e200081e0400e2640000311002c181d0109043c02410303410302ca9801031002c00500d2500c2c250108180340c02a0246001003003107100d130000007521038403200d040002e103c04660716400c038060b100e00d84003180d9911805110045141c151000502660005030000822000c0302028003803410821220301c861020314090700d040c401e401e400110381609118007a640480c0400050311006503000050480f450004034000c0d692108512000aa448a4486180036030880d0088400e001a10100300340e03010740031400c0003221440c0c000100b896000f40c5c0d2910700b05d0f64461411000840c0c100542042e014142c000742e0403a60700100c05000610840106003102461300785960300c41e466541e620182c520140e1110011130200300c15191309601001520046c1008450b40044046914101c0d66909401000ca905082c07605000e00203000c0390703078450b81120b80c0010203d5600c00f1401e450400329403042c0e1001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201229136 1250 201227886 201227951
    0xd050c04150321091a0715290a060f0e030a0c030219031203020c25050f041e020a053603010903090b0c012405120706020705060d02040801 61
    0x20503d15581e0354001582181c01d440e09200300307041000c11505580f400f0144180b030f4204000f0308002c00c0b0b8a0134404007200c0c440b0380c003194001e12220f903c641c3c0d168140d40f80c60b00b04842240528141e44040000d000c0e91414a410701c1d2040c0413403c1241c60000203800c40d6014050f06ca41c646c2840b11050791101070360700030344400e0b50300c00d841a035000c2c1040c1d0310701c809003070f041041000031403c034400c3d00203000c01c0080e0002c66443c54860003000d01c0315060001922011880640104050300348143c01052041040310204a029589102100300c444460044141541c0c0014081c100c0c174001c000365080450b0b034030901d581c03011070101107140d84c141d1030350b0050103c0f1880700320003014541401641d90040c0e140d1303101c8131040d02d0b02002c8011a0020f80c25085a03549441c07180c0200b1100304400200c5081c0d4032078010708249044280041c444102d042001581c0200c0400d0040a4002400004a500c1541e095980e030410903400d000030b00454205405a50800029117448812100c02c0007180c5007400c40c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201230386 1250 201229136 201229163
    0x105040317011512240503060c090901120c0321030f020a0f180b16061505152208010504030306060201061811091f0210050606090d050c041503 63
    0x41e0114040c00d02c560500900401070a94042e442614281c0540c110035402003200c5010203401c3d211007100f1008076141190a88041050f45400c101340c42e04001d098109a140c9410200071800001d014092403002c0001e0341c00340d90070031030000900740007181c0040956000d20728490300d0b076081c01c40783d45a090001c0d04210441c0c8100600d4806c9981403c4580c407510f822884140042c2d078950841c110011400504002c002204141c1c20000c2c40203c0c0c0c400e480304000c0a403864940201d50510242204100008005001c540c0351030062401c0c00000d021050f8070345026000c0c0b500001d408140381d0a200502400001d001101504941d00030f500c6501d051213071586641c8200d08942c1c982c4240fa064100995102090103010f520280342e221320b1007a55460a402c00010990004800d0401c1021170305540d00400f0041d4184503510b1007042034134091190b030500303000207544c50041c00c80d041d10401515a040080000c100208007400402601c14400d03080a00340c5c0d000468180d100c10744054a80307202 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201231636 1250 201230386 201230417
    0x8041b0f060e0312130812120103020904050111131404050f07140c030a0203031b03070e0f060904060308040501030c03060f09020c0307170403060b030a030f050c120c01050403 77
    0x840029241a1240440030501d0808101d50201105011a4241c0500c50010304543c9010340100b10582c2c100304030101c403078030344541e40b0f140840c110035070554414244200c40d6510101c01201d41100e4048840f1a015141c506180780109003020b02007079000d000054907090f008090020341c0132241d61114040590307540e0000c2c0001e5034400c843c1d0000b9000581d00041e07559000c0c071107100c04c0400898105003032001e80c1c4142d070715641c050103690000da072010042000c00c54644403003c2d01c4100c11450181942040d10014205801e040805440f820b520344425071a51121002e0b5404801c005200384401980c0382091081da600601443e0f002a06000f040c00c0414024080c0d013041f90701c4007840740318503807418a0940c001d4103c0f84e140e90050000f0043c1d000440c00342809840b8101d0041c9181e960365286240c44021500710a0444c0c1c040d0300034a022101003900808141c42c0c000650400707603510310358299402e003403001001c100e0300c2c03040010400c60303901441540440e115500c603480e5640000c01060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201232886 1250 201231636 201231683
    0x6080601020109030e1212070b010510210906020d0f091101020c0306040209060d08180f01031103060904140d0309060e190311031317060c160f0507030b070804 70
    0x2000f8000c40c401c1c4511001c00d086c102c2d803100d5030020040545003001e882c64a41009548010303000e6030b55141035401404540340c00e40303072a19240441d04000340d5140301c8c1c41440e4a01c840d8032031038444141c0c1c0e85205009001e90364040b00d0940c8001c0004000404110200000a08030344e40155012101c00440510a5000041250329810010001d101c6035445600304404258010700458010103078920103000150b5440c050220a50420740c0d08184c800d01009100c070b003d100e0f41e5000e041600b01341c96500d0b0f02c048a021660028020396a404499841d1b08001020008070030940080b442a07001440788254158840301080e80318420501c040c0d1103019500355500030b01c00c072480e000510b02401d01f000078092001d51608140b05402e50342010f4504a511540300c02d103501c030314202c500300845402d0944080c840c50b5031001103090140e04006003044da10802c0032110340c009052040d0801b9108c1401002c01c12600250341c4207019007040c2c501203c005120040c03c0e10202e079040340700018400d440c0d1004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201234136 1250 201232886 201232901
    0xc0a0312020c22020d0e030c0703050f0610050f0a0302150909010b0f0901080403120507050a0201050703061a180306040609020307140616020d0506010602010204080c030105060a12230601060806010201 88
    0x5855458001400c03c0080254001d5011140e100d07900c030010442080248050000716071040c5c06003014070318604115050035800403210507150441c2080010f1101d11440c228103580041d922004208200404601019103580001e58400411040321140706a507900500700010305032144c290503640c905c09401e15001c3d018500d003101009004085040d440354804130340c498064903140e0304000c494030b80c1ca011507070192400307070004100160200f50941c0901645800c42e1503458104201813030100151400344584190800001000402380050700151960286c43c00004041d1556400d180c5006801040c0b03c8504070702901802400081d10540c10f04148040100504000e1400c0b81c4404580c5000188210072a40700e00106124004a5000c000307a03030280a09400040e81d0f1428008158030308801c9550b5144280e05140c1080340350340700e41c0030080480b04604212908201d062400140c1142480310103100c1000c00c0c684030001007c00034525040310a20745a02c8502c0e100c02004a003600c104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201235386 1250 201234136 201234169
    0x8071703030412120c03050610050a0c11042301050a050303030f01050405270606011d010e1504050303070f03090f0303170c1c060e100f170c0a0312020c 67
    0x6000060102d80d0061848042c3d00142c03600d02c80444003002001c044800c013143c44800617580350308110060901c56440d45401485003006414107011100c0207000c5440060000e00684020821f0030765522980c0006c160302c0e58010806e80d010300740002c0c0c0100c0e0a8240302d614421444441c3c0010740e41008000c4901900d1000422292a800c1500b8080a000041d104080060380d13048000388076000160401d42911400d0b0140c8207501f01a0001040140c4051600b2840c81c4aa00740c00d111380e030081e0a43c090b2600507203500b00e164042000000301405150710054050000013501001c0080307520a1084403442515080c4000d91104d80d48039600c0f80c0e034007006007c110b420340032001c2107000890b070303e1340090211240741c40c0c01c210784c0316841101c0c180b00415002e1902e0b00707002d2000e140300025203944000d840f2139882ca200d15014000030b40014034882c8051040300991400d0740d0003000e028074071400130007500340c01c209980e9182c1000b0004040903594010b0082ca00401041d01e080e64220051414 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201236636 1250 201235386 201235393
    0x20c06010b030c1b0307060e0d05090d0501060333020a050a1b050d110c0303070201020a1209030b0f0a050a090206040b0a0302041a040e09030c030703080c1b0106080717 74
    0x207002814106034005080c41190003401c2c00401c012100d07481964070030460103005591610010b10b482c00030750b54200c1c4014041c0e0005500b0340304540d4040c09803030400000720341d608031102c410b0070701e88c4c01404250009800205101d9452061100c101c28103240f00c0181c2482e42e40e2540e0a00303607082207000e03074104000014801c00c410f9101c09e104850b440030a1308202807000c00b1000d969600c5180146030016500423b014809400d5030003018808076540620580240d40342400943c0005c0d00c030615100014110145c9000c02d00d04c00e489800070801a581c048451052803c044c0c00c041300b40704d000c8a400b18202d090078001a4502c2c43c030700503c010164054180d50801c3c0c10f201640080b50440a22441095400c1c000002d1080800080d000650481c0b12602e580ea4208181808407a02c0103000e1610f6903c10000417111406c000116007204e50145440030040d240d00641410b5881400009101a52040d01c5c0181101c03066100504a5005004840300d11b82d0701c5c05200a4205c40e803030000d02a41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201237886 1250 201236636 201236639
    0x70905091305030d1a0307061e0311040e01060503060f010f08040b0a1e0218010f0801230d050d0206070c020d2d05012304020906040c03020c032209020c0601 69
    0x8800c64002031546115070300307580c02c0100c01e030014821034400000c2d0341700601d100c40d1106030606061090001500c0d552400324880081541c3c0400c004680005d61002c055503100c40ca2224190030080d07178060140014010740c5942d41d03a0008145410648100e441203a040c0b600c3c000d00e60040c07850011244080d101d00150355030b03d0302d4806014034014400034a860b201d440b0441d1228081d030740030b1180e8800c8100146c07514401c00115403001c4d0b80350070b2076050250030501d450038142c0100c41503045808005064400041d044100d444103400c1d01070141d04030003a0700d4210100140840c4140c0300c00b5a503800c5a51a60b81c24a0031103045d4030942c1d01941024201d051200410195209091600810f10410041d5007918000c90000025041c0a9035143d40d510401403054010041101c14400e6407001d2608c1410690005050408083d150610450b5540c05842556001e9015504500d1000b4180c9480b021140c14441d9002c003414a40c01200c170310081c1c041003ca00a100780c800d400418001400ca6a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201239136 1250 201237886 201237901
    0x122806091b080f06010216170706080606030a1808070819080112030c020301060518070212090a120201020a20090105030a111002070f0f05030c1503072006040b0f07090509 75
    0xa250280005045005a0301c40c010b4070035001c0c6030032004008e50443d82542e0441c0b403005500b45030094204800300002402400303490740d40c0380c1c190b94216401d042c1c00070308410081d2070b50307002e4038024100500180000c10000240900f0001400300b4001044500400d260f03c10011107021009024a03140c0e0003881ca281804a4801c2104501c0d680c4094000900d45407603000040c0030b00c110140400400242104103d500d65040c019002003100c6009410304141c45080040e92880941c001d0104001400303296509680c800c01030a030f04903400241400c203204020002001d80140c0c83c290a007d100e501000107550304000031511001508180c4c0440302c01c03110003c0000d6140030000500451250141c041800000034130b040c2c00034018200b071448200d2603d401c0c5820305c0c1000b0069482200091846800d8850240449510030114508008a0742c45d59160f9a10613018a104c040c26110b0b1a08000c00c100f00220f1035801040c1a801c2c1c1151a07a41c41803c44a05071a4000d240c2c0103030301070001c42e442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201240386 1250 201239136 201239161
    0xd03140a090c05090c071209030305030708040302010213030c05040606091d0613020c0a032a030f020109170a020c1203070623040c030c050a0b122806091b08 69
    0x100d4840c40d1a001c02e42d9403080000e44925058418540c154000950001081400e0400318403104c0141840d810035072850b100a492400000c01e014180903856000400309132003035044a03a481001d1400510480e1a070500083c68607040c0038680c00360303103803d0010507200e00902404003201c040307202c0c101800034030441c10701c1c11a4028007100d4200e440d0040e482c04c508818000342c0f1a889041c4003d00c18001e1030b0800030407584010f0642c1030414060845821100000301e181d60105826040000f80c2c410041022401000004800b4100326000d103004c00301d0350b280f44010b044a8003d94222001a40f0b040100512240200c6500c541580200507540000e4036507001085c0c22003441011241c50150303007100406811085030122004044100180304001c6840c2c2c2c103001a10050b10b03411215402c000d0045558810501403002c1d4181da04005104080310790201d03280d40500083d00400d02803800d001501400082c00340d444541d05007003c103265000e40000c091891680ca0703a840b0b50740d486840241c0d51 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201241636 1250 201240386 201240401
    0x9150a0e03070507180c03060608040b0912130314010e070317040e0a0c080114010c030e0d05010608030d05012301030c1103040803090102060c03040b060918011d0d03140a 75
    0x1820700040c000c00340032031800d020460040040c0c5d55030b0710a0101c1c00d050801280e15048026080c5890b04905125080e448501e1941c087e0380079101d46c103d501e0307840e450792402c2040140304c501c4030b5000514568140d1400e030014112417103105124103044504501500f65a00741440b01c1c6a5400b224007040801c4500c4418012050351503041450140c8a1520945a660031140440b01c40d40702c0011074082079101d60f419004003403115010002c404070200081034160080d0001e01003180b4041e0f18002d03562030309941b490341c6034044001c0020b19924102580c8030b800903d0f12074407840c6001d0000a101d04402e40f403002d00b0074040b1415120111640c0150000e0002c14207100422480c1c681000c010941000100f0180c0600401581c80700002c00009243c80001080340c03401c01b034140203010000c0c2405910f1030708644100c0342009141e0301c0401407605031140303a00703146240d13007000000d4150021159a0f600c0880001041c0c031311810301d41109405690810b0f0907411500d404000040c0c010102d41e220f070a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201242886 1250 201241636 201241661
    0x100f11070b04060e100b01080a060609121113060608090c060307210c0503060a0b0c030d0908120709030218310818091e010918020414070809150a 64
    0x10801e1341e4603092407030312803007012001c542ca0f5600c1001c10701d50b0700240c1c916030110341c03004107221050808000400d180554801c121310440b03209200420807582240c02c50f114007018158000700401d492241c400760602c2c1c132811010403040000700ba114200400d031440b0400014204601c2c50701c41d0042102c40300240090032a900191404000c0c13001c600340652420301a4942da11a1a41048010010412000d9102510313441c020005102c0b120008011354139400c0030035000090350b6404c1e0a0800d41407103030108400c03082441030200311140d90411462420ba80c025640582e0010301c81c1514000004d06552012041c0b00808941100c7c00c80d5035031100c698081e2008540c00050290390781040c41e044039026071601c40380c1e085490200d04001d0101640300e040c412201700d420201e15038801c1d0070581030184210554443c1085004840311000d07915115a010703004003c0703c9441112541d15820507500340000680c40004921501c400080443c62081c1c2480e209130603454142c80340c4014260140c1e0700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201244136 1250 201242886 201242891
    0x1080c0d020a151e0f020c090c07080705010501140f011b030210060609080d2105040c0308042606090706110f06090a1203060b0d090204060e09100f11070b0406 70
    0xc941e0003144008481c24414503114213040604185010b0b04122070a20064104181c1ca02d0f41c5031040e0380061111624281030750b0411045c0c80c0c0001810341441407040c00303402d0030800030f80c04003002015408941250406214540740301000010000d984001454190002d109c503620918014042d44610344040d120303004440c03d601007410030b40190f038030551004010690400040010000501c4000021032191920107650300b42d10446208c3e602c0342b0905610070f282d844000804100394800480040c41c2c021150503240d65481074040048800705c80a582e202d600041440320403000081c0042c001c00004000d41880c0b401d01204030f5581d413030030640500d85e11485d40c142804d074405200d403601400c4118043c0005001604140112030407004010301014a0004200002c0d41c00401b5102007896050010074901503d00002e40070301103e801030300c80300d1202d200b404001c14000518134042d049940e01441412842e0f0200011900319030042c01600e5800c00010300001c82094815521600ca51b000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201245386 1250 201244136 201244139
    0xc060e0d0509040b040f0e070f051206041b180b0315060306061309080a0806010906020f0705090720070519080c010e0303041a07151812170a020306090108030301080c0d020a 76
    0x9000e4401e10800002c607a0813070823040c44a0100703001e080c005044142ca84192201e4611452541e80f20000c0014110016a4034280064205410410010800151095101d510705d001c0b84004203d104880e500c6486800710484000f107004442a00c10140100070300415a12541804440c240030040540d68903034850300c4100041d4100003402101c0c035a90788071070303140c68964005009461550032507001d540c4402103052182d14005468000d0f95400d85d40068ae0303880e150750030388000c85105500780381c9110501d10102c0f0745000003500400c4a0003180e245411000400d07907140d201100b4060b0140c240c0044c17000040d070754014030f07061010745405012030749401d94921060003030195110248446143c009803440501c19000490a04960585002c110300362244c080c1e01e120808005005142151a407165604103003c0c03c2c540c0c80405105828400525100d014a002944220b1380e4500c524040400401e2001001003624103903100031004202080c0b03c081080704d2044940000c0b83e00444c1a9070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201246636 1250 201245386 201245411
    0x60809071a040602060108062413050a0b01140405090a2406020a06270f03030204090c030f0c080118020f0d060b09040e16060302030a0209030601060c060e0d0509040b04 74
    0x60301d09441d41480080750300d8a042c02c20090600030180c1c020386042d4010b600740500714150707130051810380c254092480d028005100c04902020b0303000320a403040b685040700700100d90380399401a01d16261f00341e8a94480c00d6400c521101c5502950065030b1700706020800059044200b0384c07200309800c56032020074115045400030b086030400203801901c01070300014140010813100e402a245825041141500310f140c40418603044482300240c05400c2d40324202c803500516010740d0490700170f00040c40c01403000048440001d000b402301c2040d0a01c02614041c0e4981181e80b042041070306a405400c01c6030030810810760000c01a400000540e07d81d4001008403ca50204900c0b4510083c221a890240c9035075150b802c00c0f00b00e80c0440100e0015400448085400d801901d941c00705881182c01c00507101d4403012242d20007030181e15101501480356400100d003150308112540a410302c220000e214039a806074a4603160030303ca18501d00070130030910200446103410707040321424a4002c0c00000391090840c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201247886 1250 201246636 201246659
    0x2e0302060c10050a020304110108061504080115080303011a0d0b030105070c0201030f0e060a0e0a30090e06010c08070f0b0a0c020c03030f0a11030a030f0b030a0c06080907 75
    0x44110720a610204404070b103400a80103007580801d048004600314a400e840316540b400700381c24030703504100b03d40002a000d642e841c040703810041c11b0405159211350b1150411402488881c111509081c841c40001505000000c1203d05942058205000402403100040030744d40100c00e03c1e01c8100c2d2211042a01074a0034461584140420f55601c0010b00f40c600002d000c0b075201354454103203541004001c3d100c95000044050304008881400513443d441c03484198104550004010802c003243c0c101e0b51180300008907508694504d50200c048204200705040d03a106015100d5200305040c50b500042d141d601403800103001e0380c05150400d1424900f031781c072940011022003044402c04559021700501400c03e103d1244c580b01240001c0450f2490040002d0796406046000c000b003140003d04a4052031140100c240300c0041c82c02100e403600031005c0040c0240040c0b804000205150a9030f10080d031034001000c1d808250491a1a491241402011030300b421008101159a00c81e0090019a00c80d0b6803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201249136 1250 201247886 201247897
    0x31b010806130c050414040c0c02011b020303040305061f0303141308060a05041202070b04120204090209130b13030f030e03040f030309030b0f071704020a15080603010605092e030206 80
    0x50344d071155207601302105514148003040ca041d008610b010781e6105130750b4000c0e065030794903602424080501d2203a10f220140c0c40c401c01c04000e406000c040760000802c0000920315015001d10641802442441c69500382c2c0c484041c40701600050303000c85442e460806600042a07000022815100d140b42c5440c00103190007401d4840c42c006555441c100005d00c420307000700d1405018180301500885203444130402d4680294011150744003803504c00c1c0d408560b2140e110011241d4090702c4402e80e403811801e1104c41101026098602041000014010806040c10709020701d0749521003450103a80500200c0040c0800c0b050b18440703100070000862040340800d030640080d40304e42c0d542c0c03a1041c15842c1c0507100401c0a06501800c05d290420720111035007100307505d01da540140c13810709599a524000621265155440004001e0a211f4554241a400740b2454440e54041d0024486c042e503400070700c12051011141c49d5100d90180005102d0356990b40c84051842440320120209140c5a800003001640700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201250386 1250 201249136 201249161
    0x151205010815090304062106150f030b0d080f090d0605090a0501110a0801060f02070b03011d151509010306030507060f0206090607050405010809160b040501020c031b01080613 77
    0x7610982c401d5403007001d1070592240ca0310300a5030602d4504840070703009100c150b020b00c000c0b4034100038400036103050b0ba001400402c12403040c2d001e0507500d500060051503c0700b20110010381041074090480c2008030620b40c0060303101cac2c56146440c184040c04401c2d40c128180712580000005010710116400303006007030050720000060400c0701520301c4c165003103a24404160740e0030b11040c01641202c2d500910094111b51041c1404102c007051084104e0400b420364002441d100004400820010b00c0c89100e400f01507244500e0080c03d855a901e44070201254050143d44101ca00c5449100500514040d04800c0010f050210381d094803aa5001d050540b1504440b00280d0941d105001c5594100000c9400c41602d0026004a0070700341e8000b4801c0c4613034082d40741402080300100b02442070400259100000340101582d40d191100c4040d91174cd801403089e0750052240d140907250320724001c5102d074010302e4045c008246285602e40151030b81c0c00000c1030140d00c803251002080f035028030380c003e89500180c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201251636 1250 201250386 201250393
    0x911030a06230f160c06020a210e0d0e030c03030c0105070201150f0504090804170f0c0406051f0302190801060206010b03090d1202040f03060b0a060302070c1512050108 74
    0x20358144000b4500800301010248a10905102000f002c03464880c0d003101c41c01c03c40c1400d07980000c10580d002454104018a403510002d242c02505500a60103085100c140c2e403005035001c1d40d03101c081c05991b07240c28042d61a40081c0720050711f580c0654641e8600341c070041c050700c07108805000060b04540141890000350303510380e0104a4000d0342072280081030700c0740003d002003290405203950b04035440ca00806024030b075240c2002c000d0101410641d80140f5280c041c180721802c3c81d03080daa44880d041c6160544611442d44541042d18044c0140000e807040980070100c0c01c0103604034240b2000740c018091090544c05c00c80d8080410b2400301000340e5403026100d1401079454424000d01d8094140d00c9801d11500a1080c80071003000130600100c136612526203506841c1040528030000d2095a200100c41c1030300200000420480f900601000c900480da6190340c56520b45080d401d03441440e1000300f02510361081401070324001090150501b4a902c0c014002c072005010305002c44400303802800e0305c0c1c1d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201252886 1250 201251636 201251651
    0x12070303020306040509160e04030e0a062006011505071106130e060a030f020607110909010e010f090804030b090c0a0f151d04240f150e090a0911030a06 67
    0x3000d0040d06d400101c0180281421240300d000b034413040b00c031401090500544940482d0501d8030036034582c111590000c061038455a0f0700c48000d840c1030840c039040c0b8089403e030800c1000100b00400c19074100c4041002108103280310500c02c844590007007000319104c4143e0307045001c0640711040600030311410034020401c1a400c04059030500350b00204054400c030300c08042400080c0e15200015a49035045d9130645e15000c1c44d2906000c18044506060f4000360142c08020304140c2c1500b15200700080c80c0001c2148000000000055942c42d0102800450702004100006002d80dc290350707100c152001562031200b401c000007050881551300000c0645072050040c02201013503614680c0e4820a4180f0b02030311148070304110040030700a201e10740325540d10703907011443c0d1400c0810f40c0754020111030702c03480198035002ca5814083c114012217150015407100703104031601801c0c048001000c01003a030942e90340c0300032070407014011281d81264403e0450600c00400d48040140300da80610032078000c03c1d000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201254136 1250 201252886 201252889
    0xf040212090606130e100902040b030d02010c030c0311090111030c0a0507090c03140609060102010e0a06090606051914040e0a0605040215120402130207020306010f0302030601060306060e100212070303020306 91
    0x510002c414081e00307403401d0f1001741c3d0484001401e500305c075445000450754090381e0001070004c0c02c84004c05a0107000c0d031b542c0025882d90660240c003134050152820401c044c8951400c404680200389140c80c102000c2214609540c01860768003041010351046074506510302e007980d07003801040e02049441d40d005880500c80d050a5018400702d0411a141c02c001064203c24074400849020f054240202d0184c00455072a0b4404e4201440380340ca180100d42140c2c00c145008802010395000c103550041c500030003c01c1618025003160414480d41400c281c0c41c6080c41c940c24800007820282d60f03482aa80c44220034152418042807940a01512001809203054018020031a0020b003408031241c1080000c2c8c1080100818015001038040e80c40b401401c4c07017000854000e102d03003900a9410700c150400000e6921648031200241ca1094065a045990392001a403d45816005120118441c0b10421417903040500d402c016038079203031045440811102c0b0751461698800341c4180c00107500001008410f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201255386 1250 201254136 201254149
    0x70b0304120305060d0f0203210301051903020603040803060307030c0602060f090c060f0c010603020d080a11030901090905060a0b0f0c071a0406050f0408031b010f06060e0f040212090606 82
    0x1c55040d00701400300c1c0c41c000001401c604510751008010407081c400c0a4155101000b091200c8442040500300303461110300e4250560f002442424494071a000c42510440d19160009085990160100f030858071980e0761100030350001001aa0275100d5103400001041c00c65103004c00426a540203440182041039a00380b002000030004d0341103600880d00c015403500c400040380c0441d25451805522200e44c0500d982c058034850780065403059181d00d9410034064a1340081070000704588980c460b401075400c032240c40b401038140c4503012034400581004800341030b4020b10ba00042c01410560015103554540d5410381109050b6000c080e400b260b10180500c00b0041c00001e44040e240d071b0301455201c2d1813049540d100d14040c1030200000810100d45042c00c1800f900d003d403d41d8000e894a40a16118055181d06a0381e421240340d070806080346031001d0140700303c00035503180d0f03554140b083c1904000d002c225a1100062a0420741c200301c0c0c010102c0c46981c0742801404903002811060034031004001e02c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201256636 1250 201255386 201255413
    0x506060102010e0316080c010c0e030706080f0604050c0d11031b0f0304170c03040b1c0207050709050c091314060a0617060d1202071e080703080d020705070b0304 71
    0x541e03141601c00c216400f000020303100c03180201188401120181d1a00000b00d010740c1c01001c50540c240841c0d00d540075000858107002c076400380c08403080c0c20f80d03a03241242c010f0425a004403544108202103001418240c0009600c0500030b00c54910b000c1c1022031a108031032f1042048240c0003008010300c41c001441c031610950840848090608003207a403c6446003510000d00000c000841481144c40000c010703a0a858000c03104030203881d181c0d5074402520f03880f58044c2260780f4507071040d1f200e40c1d84500418401d6422040d0000014041c1c281030241082c020720010307240003000203007884041211358440e500010541c13100000420440c40d24107540f04c1008000c1c142c544501d018000078080340c0c1c2d000d1094031103018094400e84503a101c0501094000110940142070440d0102c42d00d800c41c0c0e00010300d00c3c00c80c0c004029241d0b4900c040d10065441208501608100d41c0241c0010004203880704003805030724584103070061400445940710ba18000c01ca60001602c02001302c200402c1c800c0550b01d01c203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201257886 1250 201256636 201256639
    0x170a0903170a0e090402030c151c0603030e04090c260f2406130509160603150605030c0c030705070303030c1701062003030a09150c050405090405150103030309050606 73
    0x82c00c0038040c9030054040c6804020060060141c20005820355500b0050300c100030102802c440780c013030b007074030160103281d40603aa801110f07038005607142010007902d00c60312080360341503a101340c0c095480ca0104000f42c804002d0613528903d40384401718000358030b68910004c40441d006114401c60314003650301e041c43e241c00600c600d2600030080c130780022030850360305031a141840c801b00461903944100040a540c1c42c1300d101c01c1038034949001c04ca0074035400101400c004001666204203560740c1d450840079101c61210001101400306400c019041c0290007540c3c1002e00b1030070f00ca00b003500300d10032030345941c10048043d215980319140800c01e16405100342130351050f09141c91407665401c0300130340b603030340300107110710b0042201c40807603041803072000191050380110305801c0d42d540f4100461003601801c1c441500350307070300414070070f803590f40f50702503c40c0e010164841c1d19801d003028a40420401d40304e0006009541034022100310116034ac04030b80d50b01e8060340c82070300e001541d4211410241c3c9040401007589 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201258992 1106 201257886 201257933
    0x90807081e0f0702031606051905040815010509010f0e040201050307030906090c261b030f010203010803070c1d010b0d06080105090304050123090409170a0903 70
    0x20420113008034104d40801040c074031140580905441498003046040081601040c07400369452140c01007410700c9404d00740e80b0034641d410034510f013128404031869007005010a240107098240540007644101920509241110720042c2d809000a070601c100880028181440f9800160440368400d07818400d820716407400d2040c291250140b618140d0030310140500f400d020200e03400b0f5011211000b4005d081080d46103990b0f0308603006010744c041c0910114154000001d00007507008051003001507035110340a013012a0f1801054124240ca0240b4030524880f181c0b90004541c15604050101580da20203294840d0007040c9036070114107954201010031400802c08001752086a0b001e885d10120400c2000c1c2e16520101a40c414100b540700510514001c0c1c01c0990000c10418458000c9007800f480303820909001e03070860200200003035006041031040040a04158003074401c1f01021 = true := by decide +kernel

theorem cover : BRFrame.Cov 201079136 201258992 := by
  have h0 := BRFrame.cov_init 201079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201079136 ≤ n) (h2 : n < 201258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
