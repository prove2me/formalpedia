-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3680
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:53.688983+00:00
-- url     : https://prove2.me/submissions/9277bbd1-dc2b-445d-8af9-3bffaadabe41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 661690647 ≤ n < 661870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 661691897 1250 661690647 661690661
    0x1020c150c030903030c0307091e06030e03090f04020a0c020d080702030705010905010c02011805030307062f1c0b040f0e0c04150303080c0c12030f06030102120106080417042601 78
    0x400074501756100d50a141c4410f5201402130001c006000ca408200b00b18050886542401c01c082c0094280b40f4200d0b010b82078613454585682c00760818411290300b40c481030058100e0070004c840042c2c1d9a004d0140039511154032000181d003003200394031103108000c1c2c0c2c40024514603000328100c0320303159a583c00440c0e40030380300d0180785e0004200c8000b80c401035024107180f100f40022201c041013101d0b1110040303880c541102400b640c1c1c40344c03621940480341c49015171012802c0d108525003142c582415804507070b9881000c0211840c1403034052803a00030746403540800c03180340c0020400d0111780d050300069800f4010f00b402451490107030141b008001e2611340f0400c1e0b0a50304261150b01601c0c0345807001e82d903240000340f50581000b01003003800030740c83c4140702500b400603841030070356240c2c10446002c02c5092402051103000e40c0c41041541400c102c2c4d03e480c5411580c081c80c007034260750b4841c43c0007071a2017010100c1d060011004607020560280c0070801c0c22361070174800c0c401e4213050403141d110380c261001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 661693147 1250 661691897 661691911
    0x606051c110a090c02240403090513020409110d050907230102030d18050f0703020a091d0d030e15040803070302070203160603051006020a0b071b0501020c150c03 71
    0x8a0040200001c40c039900100c294000240942c800503a030b1550032068403001401c10700180c0090070000184d861005400b80f03036203403003010810a89415503028195801c42d014841c880c40c003a1030746404102894049502622550f102400004040c3c0461000c0350400421052101c1c2044000b400140d00001c50700211051058661250903070840208503220040c580700b411030101308a0048047c6090003904903802c82608040d00c5070341c042c200b035800c1480c4a840c444a1341c00100c2d04001594440f1250000e48084050025000703101d8883d100700f91458600030542406000011030319180c1640c4050b625000c1501551580800e541040c0c0701c514048800070100341d810300110b0310140c860383c0a48a0070348094100c8045210041c02c101c000c0032245c0c4a0380000e40c5507410021501e0a40c101003000309858001000c4181080d901d20082d204028020820803a84d0622805028001740848808581040c001c558034281e041c2456102d40c140310130721401c0e4000340040780f0010b020790222407080340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 661694397 1250 661693147 661693189
    0x120503010608071b110102070e01180c020601121e050a03210c02250e040c050f04021801080c0d0e1501080312010b0706111204020f040203010609031b09020a0903060605 74
    0x1149660305c04000004c0042241184100c42011134002c400c10480c0b4043c1408548080101c1180171300310f03007a1460146c00b0001c64121900401902c86500c403003040650b8400e1400055161114119810064490300584070703100d000041c0083c13680007004500c000145400b2290000b202c4000082614190158040141c0c0880c0c108418409004203149a861080c440d02c00c98640d034100103880c403203081d00d0540300c80d00e00c04020070841c508074110000b405020f076005c0d07003010b03000d180e042e06002e5241c0001d4140540c03640021105070282c0111014440040400c000042038640c0180d60340000d40a01d400680d0030750008074641d0400810f481041e5904003c41c03030182c1c20030440c4880c0e42c02c000341c1115030640752046500c03503405e1040504140f0f6011004a0250720341401040310a8100c0c00645001e02d10400050040c00c1d4400041402d9130340101c00e040d01c8000d0300b12280c0e907121540d84002001407000c90b01c1e4410a50003144e48046a000300b0f0184032580e111020017450180083d2032510a403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 661695647 1250 661694397 661694447
    0x403140706090825151205060307030c0e180607052703030a1101110f09091302060d0902060903030c010c0f050a08011a0702090108070f0e060a091812050301060807 72
    0x135590740c1c4110440d40c0002080c1e51304c40e41d140e24011303890700450118404108418401c0c425a14188a402e0348414100c000301840d503d107407500d00c5c100715a4065242d01002c12400140105000d07a280c0b43c0050b104000c07206c091804400050082d040700509411040306400401c18600542616a001d180f005001d585006200e10301074030b00d80400181016507540720001001c280064001510401c0d40306d148880d514020350f02007100364031009204100c0024122449009600c40b0001d841c0c81d8002075000050101032400050114007820f9142541488005030f0255048010f400180000a068a40600c2500014016946809180c0364400050328010042000740800c80391040644401d10b0070034034016082d00070811a1800740c02040e144c2d40000b004001844500003039100801050000c5200c500b450340c0003641d01e80051040340c4001e600c0c0c007504802c4c0d401001e4202e01180d40302c81d00f41030429000030b004d40950030902c035440c003240c0d924000941ca10b01984c64107940624400b5800046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 661696897 1250 661695647 661695673
    0xb09090a0207050a140d03240317040905131a071d0d0609200a0303020a1112060406140604051501080a02190e041d030a050903030f04031407060908 65
    0xc0d04a44801e55052081d01300c0d0102060390010300710b45091381e640207032011070074103403014044c0d403c0382e10404400c0c0c00f02c0d03882c000421050020075080e41d6000c121031081441681812540707002c2c0f9004510020b1030300007070181d04140303508408444c2c1d1091400b203d43c600d62001d203100f20601200c2d07403408268003045601d200940941000c001d035000400d0300f01c8051654441c1c070119284584211480500c40144003c1c544006a03020103410045460480c4076056030380007502c410000000030700404000240000710b5a40004900c400d2041004541039843e10f424000040c1c0744100c0b04a040c1900350011a885081074020b170b52003210b1a40c2e0319807803250b0b9803004550b00030008045907683d075804e0005a01c00c0e4404d0703816503034509150340c5100c0098110b004100c125529881800c040182010502044590200c15208c1e8105281410b40d2952442c0b80404d04500c140c584000070b00380000350201c100701c0d0100912250701c00310402c58181d01d440c0c03e8190380c2141d0501590003107034890503480c104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 661698147 1250 661696897 661696901
    0x40b0408070b0403032906040e19020703020706030f180b04050109210905030f070e09010605031c031b05040513060504090b09061e04030c03031407090f0b09090a 71
    0x1620850040740307405200e446036149140b00342c03001c40c0081c3d00c4040100c00d60b00150044000e0001c1d140741c20003201c1c10840010902c5c400c40c4901e04e040e064000000e9100000d003c115104961403100a641c0d030109441c00a460391a40d0003031502113441d18040d4880d1500d54410303001115030840e0f00c0a030750901500c0d01c0200000c0144202c0d825902c0312000390008903140c0e088200507902c0c0c10282080c01520300c01038a0184203400040c000e602100450310520313400180f0500325001c80d40c05400d075440341714800d0701500480d048150584595008145400c100d19200ca01d4010169010003045041d41c50752202103500421650000d80203120910052900c5030710030302c003140060300001d140f030303580c40c041001e45408620039a441031822081054000c824403515078400038000740b448522070040081911680054809002c1001c09040501050701030392002014030781e8229141158548040010880180c90242c00340503207203100c000030b000e03502d181070343c2a105004160500b99500c2041c00b0f00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 661699397 1250 661698147 661698151
    0x6090603090206070615060f030902180910050411040c0e0307140103090219091103040302300c0f0d030b1c0602091e0406050a050303221a0705010b010207060503040b 73
    0x7034000020008200003c45c14410303104035200c0e0b4600300001c5841c00002078607170790400c2c0401c801c1c50b0a000010006030342d218881058032000d518002e120380c03030300502c292400000d0405100c0e000e25110501c42031154014540c81e440000701d4041c001200030b0307141151041091f800c0c136509680000d2050254514860845410780d8040c500003520248940015032030340340d05000426040036010050003006000d000d0701c18040c0880c1002407450409070740096480c21740c4141c180403400d81c00d01c1c1c02089589109510a841003554115072901c0400c802aa122a103403006c20140344500ea000d00001c41c0203010b1060254801492040312140d1482c03182140030190104440f1a0350030084000541da5202c3d45402c00920020070034240c40084090204607805604000c5c440c21b003c65040002e95000811101101004c1d4007881500c401c00d140740710440072541040041c98400c1884804444001024180c0603001d44000e04c4240750000040e071311f800e0b5500801c00041d0040001501189114200d55 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 661700647 1250 661699397 661699399
    0x3011a031e0f0d05030a20030a0b030a0807031d030622080408010e1e1902010c022e02100612121701030803010e10050f101b030203031f060906030902 66
    0x3840006a060b099401d0040442403100403d0021080c8212a10b40b44540421144211034401c0c12141c80da80d10319040c0801400081e2030707a114807124106407424082c00309087d80c005016906c4003060324029101c80d075010004080d189c0740303209460b0940b03800174445000e1130000345c0d4560003a110f0040c00071031141c401000d0b110803004000014000100f40724885280703400101500304068090801744108800601502584d13101c003690340c00c1c0044480300742d250640d090030b141180303250502c00b10f000c54860044a1004120007180c08145664264194409003850781c00e41c1d5016099840c1d0400b210110300840030340d2860701d143c040c00160080d41e19003826a560405080c00710505440303c240d004c0980003140d040e5008801005171072601d8000d141c000d1201256440300d41d04000105d0300c040c0035020203621400c200541c0600c564040c400c0c1d0705102c01610f9582203441100c0c00d020b903036580261a20402041148080802344446542c914140d0700313a65280c902061030080c00320003a1441f943e060b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 661701897 1250 661700647 661700653
    0x909150e0f0f070207030503030a090623011d090705060903030f0a0302070c150f080604060521060708040b0a09150c090f0918140c030d080603011a031e 67
    0x10440030344590445114456604125440c0c1c0340c5220000b441c030074054001c5056521942c000d02c0020b0001c8203496102007040c500003207002c1a410000c0181c404a8803070075a00d691042800c0d0401d480140c054181c1c1c070295246550384c2c0381e40c60030111001040380c50f96501e8110200901451411400401042c1c070018116800d041c644420300c00250700103594080031950000701c5404100031038842e44020843e80c9203522104050210140880c448400a001042207140004141d5620307a1301c41c01c09000301404404880aa642100880c081d403290420400e11600c0006030b86248a08041842568014504d14080d00c50340a00d001030034180700125004200b115450144c09458412000e111545035035000f00c25247c4500211404043c1c4c11074040345042c00201c204441035001c13487c04007540420240038081541000303500b0300100c07244456245c002d42140460603903201040500800c0224020071800e40b240703550300400ca00c0902c58a416820000e0010305d9101809161001e1045074016 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 661703147 1250 661701897 661701899
    0x60a080a080304080903030a0932010e19030302030d050c04050a17011d06040b071d0d02060c0102220501020c0f0603091c0903060605041a2704061a10090915 69
    0x190941e00700480404c00204241300c10094454001c0ac01d40d00d0f10074600c9162988041e8600d184074207100001c0043c180000085802d2513030b02c0300458038150a801c00c010180240d1203107402500c1c0d50042d40100009402c00000c00c4000706070500312411140000c0640c01c5c101d00c4d00444000400002d0b09590f407656171140c1d10003007071075001c6981c0801c0714250050211450a03180c54040904003400380d0b4108000ca2a14103206080e41c40c00c09054030003295170b400140c41134800034055109000b8031120740e50000c03640250910b1101c00c0608645100c5004100c42902d4030012a0b507030f82072801d480e52012054883d00300c181021401107400440403029261440c8c002d4218004800c8642d102c900060648801041032042901c50f41c070142c40c3c1100c0c2070250790310720b00b0b150258400d09000d46224108008125621901320114110140b003200c08403c010324140c28075030b00034068015002e14040042e1155080d81ca041d90341080015042d40b2138190311030410309610000d0145a945112191801d44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 661704397 1250 661703147 661703149
    0x29040801050f0403030e0d0f050f250c08030a080c180312032205030301031b0905040f0201140a2703150b0102071a0f090d1208010509060a080a0803040809 68
    0x20103100b142400b8803034003039041900d0000c0417a04090052070151f044041308880041d0320135071a605841c22850800c0d100c81882c00340d140c41c0d02c80c220f080801d04414041041c240745000488030b403500c0c0101860050103641c0c1e5030b01912441007200c0c2e880020320020020340500c2404014104080c2e0a09440d850075401c50007092620800c0800a100280c0110405c0396889058005020001c2d0b10900d0b0325600300c141e0740c1c03142d4078001030100a09101200c1c1c1020148100001c2c240700a2128600901284c20182029000c0b0484c503c0140d000540c036082007104051040210341601485503144040b101885204001200480000c800a001501800800300c0d498028024020030300e03000010310764030480700180c0340c8001c0740c1c060401030300344440262003454428182c038540c1000c0c403e040daa58a07030380005040074041040042c40300010014040015030f103c41c1103410b03101c050390040800d0710750104100940e58144164102a400080d40b90b000402c81c0d8050340d04248600c0c603260034610303860 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 661705647 1250 661704397 661704401
    0x160315020706180c0f0b04051e0f03160303091a0904090201030608010c03050f01061e1b120c2a031403131512020702100c020d02150d1529040801 64
    0x2903030558030b07031500880502c024a0b172050b000008001c0c1004442c0303403610300b2010a0106c0342e203a001c0c1441411159a58040d9100c901410854030802010380f2038421100b180d101e0a01446d01080e00000d01040c80424a800d101d9101341640c030034040c2a50901c50884100006008024400c070b041684031180055010424020041c604d522524046614608100d894142400c16445441040b1213250452000c28040541041780221850981403240c900d4903007000649035128010144684a840d6030480e95002d400c0420f0303c0c0c803e0401e04402e44681c800f41242806c0060a148044121001040000d610403161307030b4014181d174240c0b800c108a100e80901c101180742d224089034842406a49040c0368040c200340107251481c9011401c0448035004100c0e030240081481051043c0c1103009025503903510705070100d496000344400300c1c110941040340c600390014079203006800c0c2450b24000144480c201c0090035034007107201800380e01309440703074120652504030641d1106181c10000803c0d450028 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 661706897 1250 661705647 661705691
    0x605010c022701060527060304080708040b0301090203150405040203030a110705090703060f092307021504030e030c03030f070b0c04090f02031b0319020a110a0f05160315020706 78
    0x1070305c40035101c65402d80e00600101c03c0350380501040000c0a18020303a560f5840940b50810381014900b5100c0042c0e1034244800d00c11504044600c1001100000310310010390000c52003000791b111076525548058082c0b0041d140140c43c000c3d450b030024007860510701d1081d1800341c0a84141d50448a005560368085010302e40c040c2c90b860700194984400b407002c103100c90b441400401e12808100700b00f5043e40c51a0901c1068900d0710310015a002c000705200c02c0c420040721079040109648088103092614015005030b000b415258002e000d00098281079140c0881561241c2c0201c00d200345c80d0007926581d40c0d11110005209000070b007004d000105041d6024454812404800c0740c006175a030400007214040c003e131031a003060500c3c00800030008032024602c900da500341031151000d0b0b12040200c2c0c0a448002d000c40d1a04520320649801000380002c000782c3c460307014020000e903442d01c8051400400056158003002d000013017040c840b000e1040c400da0060520a009890024001e42c051410344d04d52062 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 661708147 1250 661706897 661706909
    0xc03020909040b0402121b151210050406060906140306120601091413020f0922050a1104151203092c15010f0509040219051801030605010c022701 64
    0x3d0070030041141170041b20780301c031910a14010700c007220068035030840d1480d0300340400703000705200b80041c0e90803c6100d00707440711414511061a85480c1400700c01400c0070240c85094441d07410b000b00090014000c54440c0140c40e800e584800c02654085c0d5100aa5130026054541081544c01040d488003814040341e070180400e040040340118000b42141103400000d84000280d18100d0399410060740c5000c800e0108903425200d0814555504011580c0ca04008032540311401c01f44c00c540c0100310010404280151041e0306081800240d038090008581103046a00c1c2120504503017440f01c556403c0b07080080d94424a401c050782501c41f4006001c0c50098141c22410501c0020400c02240c43c0c819142d80c4a020380b01c40a40c03c803030680008240c0d40410b0181802d1000000d02214183c072035404031421020703021100e40c5050614480240183c0c4110710b41742a504440340301e02c810750311a008540c2110ba0580d0340d00c80c4800030744c02f040040d0481c00b40e402c040c80594110141740c009400500c9000b010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 661709397 1250 661708147 661708163
    0x903070b04120e01030b10120e031801030f09020d0f050a170d0b030c0a14010207170d08010f050a0611030c1015050301020c030f0906040b0c07090605040506090a0c0302090904 77
    0x2011201a01e03e543c3c0d51541c0341803505002daa0605901c800c9180c41400c103062510b1410050a040114000c102002e48480e00b0301001810a009440d6404c0c0900c40c1582a0703003c000c0c0081c4400d5850842d43c40c604000e5201610000311030106800440c0710202d00d00802c20f445000e4070f25a2060a2004610070204054101092505550f4114401d0f441882c00940c00360030703640c8042e00000c401c440d140c0102020340e00c1a502c003a8640e4401c000c82000b038070b556034120000e1802d085019540751501042032001031142c400100d414a05c03103852400300c40003d030032079095a04046055410b402001040d08151100340030f501c600170010010301800307803c40540001c200c0314408d1500d0b080d41036600910300030fa0040016964100d0008211000b0905442072240c44445410000e03100c0d1155a10a040855011400d42140040802c1002c101c407012a0f0410242c1d55880c03d000a0b91130071504075521100c4040043c010701c1440e000310505a4051800500d090514400207504000c1a14250f030441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 661710647 1250 661709397 661709423
    0xa060f12050903030a0e191b1d0f1314060103140a050c0114090402030a15050d0f120212030411100903200406050414090c040e0604080708040e0921040b09090903070b04 74
    0x248090023030701c01780c0301c90500c0030640703a10072040d10500000500000c941e52001000a54001200c024064850340d0140400e00d44c115000b11030b6030303122400e00041d641d80846154114142d070001400e207038669400405001110f50754001501c94070400508209500c0041210088559403840150320498080100188110781c1007001d0000307150540286004d008a071007544041044402020221070f4844081b940903504454105e0400354401200301c00d9480100a200400c0460039030141c610f42e041d0341001c04544068070407108006a440080c0944041a1904d8161074280c2c54401d03408030068008502255110007050417500001107500d000404c410500080750814081d080000d00d08850910032014041d640c2c0c4e4503404080c200174011440002c20104022816095500820385005102c015207400d001180d22039213000718065080c1c41e80e000400141007100e003514252000c02c58840c2c28082e140d41032150501c0090184681031000380018000680390340f16080c03085215044804441c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 661711897 1250 661710647 661710683
    0x6021b0a0c0605130b070c0806040b07080c1e09010917100b0a05101d06040f080c0d081e0f0a0306052106070e0f0a060f12050903030a0e19 61
    0x1c0d00c1d0000410840c0c1004080303030b840141202d00040d40c1c490400103660301c1c154a40013581c1000d5070301010003400307040c00300001e100540302c11070703c17810840e19032030019a511007100040e4803403048145507001c1e07a076402043c1d2840790300113840740b4a010304082d0007141c0c0340c00d00c0d0385c10403000040e4081a9441351044040d400d074180180c2d980244182e0304c114509082000207000b0009503501041003103080c12030000644076501c02150001d07006040f90b0317a220b403145000200490140a0702400740724100544080703007404100c9041c0300b6000202207040501005018031900301105008a9441c0148050185540f4980c02404120456100041c61502e04010b1081103030456008006003c3c1c3c1da450b0345508980401d1060380403c0b0f52a140e1201c0701d00e800081c1010707040340c24075031300400c0d0410042110364010030060f603c000c1507210140c00710608180741c000d0b1541103e90100c10742041c00818094161030300b08d000400c40e041c2c191485142c50090540740409900000d450f82c14031025141c1d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 661713147 1250 661711897 661711913
    0x2250605011505031501050322050a0b0606070b0a110705011506030b030f0d050904060801021902060a02210907080d0903060b060405061e0c010c1805010e090109050406021b0a 77
    0x40c2c0405041183c01c514024416012040501410300d040c048004005502006d6240c0c9613619002c0721032105032103400c10b00306130b80d40e0940820b08070f034603106010104119103000c00658031803d41c8102c03070b4025580c4060300b406c00780c083d50f980c52a0b07440b800d00c481000140c080c002c00c2505c8008241e404503440c505280201503440d00c61100d0300a411401807a12031140c081910201404982041d650b03c1203100c01103001440558802c2b0075075417002c500d040b01c42d0018002d170b0002510395400c80303030203440f250440c40492003212035002000741c1c0d47d00c0c00e00704414180d50007540f0a442d4410b0303a40300c0303075203411141c10102c4c1d9400c51400110703030580a200f000414468003882c00402e440d0141840c0c00c010214640703109200032500e000306141e90b42c540360755901089400c44030b0800000c0c010313441007010140000000c45072089070b89d41c15078004100b5510070045074560820040900009074600385042d0000c05025000703440c0907400300040c840a885102814285481c0440100305400460034107a00e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 661714397 1250 661713147 661713179
    0x22031218110a05090a0509030403060e010506030d03360b07180f0b12060d0206041d0c0910050c010207120825081503010603320118060225060501 64
    0x4410344a8400c244000d13100d290328285d0107401d02e4000505a2911340780c440c030314016980004c00c00d50421034158100c3d407041d0496806180700307074100d5130b80c0c2010f18400d83c16a90b02c20311400321051034800340d074008400200310100441d0007060740e0101070302985035103440d45011503042000c1654203c00d481c0148003003078904d0003088042444004242843c01c0385480d44a1100c08202140783c2402240095940c03005998505134001e10840d6190b940e1344140d1311065200c0102107001c0aa00002100054035001301c1c0c00700e10004000302d025000092060b40e158201c42854220b641d030a01070000019417520070702041c840c150310741c40c0a52810401131a070544042000e42604109003041d130060580007031201c2e4002045620200b0a020340002082c01014698000b4040300c203400d8a9014142c40303640c5104585144450a6814400b2041c00740d00745ca048006071407a11012020036004078005501070041001d00a41d007030500c010301c0c01c04401c1c0e000b02101c1503c999540c0e03001082010000b0050380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 661715647 1250 661714397 661714399
    0x203280206040f03021005093a110406060e130c12050a0203060f06070c0501080c13140307060216030204091533050109090e030f040b0405030705092203121811 70
    0x191408c41c2001c041024400c101801d4900c100e50707183d00040c00307a805092402c0d0400704c13404005002000d410902c0100e000e1445c407031f009a00e4a44041f450a11500040c2c01c04480035160021030f04801030040010200500900c080046111451040b01c0850261034050004004050307207070b0516004111800900400b25803081c403080210100051511100c003003103d0090070500d4540d561901304190501c11012508840a91800c01103020310500b40030216604e0706900b00c0c5d400c5074a680301070380e45100c0c001900b0350740c1c0440c10b8100010b140a030418010188603403118506411b18810040540e40780104d141c11120349245040001c0c4051020011198040f200d9800420f06d06400600701540328040c0300ca48503140c0ca00c2003907401d001c004848c10f041146251599982c1d0341c1036203182c40d402030300910380b003030242c441c0c001030b145002e4000c1800f4401412290818140000b002080707042d01c0482101881000341600c94140c8282c0300e042c1c19540b12103803036080070003140340410b01c03800328070340319 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 661716897 1250 661715647 661715657
    0x1090204180506010e0409140c010f1b03022b390c03051507110c010813020f1003140603010e0604030c0c0317071b030203280206040f030210 62
    0xc0145003105030041c5840c2109103400150798680c5001225122611113850b0780041c20400c2540400081e4100c030041d146000c01a1102500c83d4801140d03003540d40001100020152400c0035144002240341501e00e9100c2d00440704842c202c4408013a05e03401e40180480e0850308116a400c1154010385080910410007080020f8100c0c80345080301d4032007102c00d10300d000400c03050114040010010550004c4c44e0000211000442d0b000f5000524000485103070f40064124a0700c0304502800280009a58005031502d0182d603480300c0c40030945114220301a40d01001040c1c25190030b80325440c102014413000c2c0d0b004506107003840880a007804028000c0c0d8041c0e85401c1000c1309a08001c540c03903401c66454a009101c00c0306509084004182c1074101810140c800e800c0354207950040310040c100d9910614070403601c0da0890081c10425400391001940540010943c5c00d4043c4a4005034000303162082c41225103030b2426004203485030003076001040c8801060ba070600651602203841103801d00c0038541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 661718147 1250 661716897 661716899
    0x13020307110a08160309051806030d1107030b0a0212180d09050a0501050c160905070f020604020907030e07091d15070c020409020a031a060936071511010501090204 72
    0x1800826105000d151580c08100c0b420713450405214400d0b2400602c00100240c107645000c100c1403031a80c000342d51f0240b00303104443d251044030380030b074079a030520f08000d6010381031003455511070820b004030042c0b400307910641c200807201c00654074595071401015020080c0b844108084a11031410b80021081e50611407001d004100315500d031502c4500f030311002e207005500c400410030708a140000b001c5143c01c0d03808000308085800c18542d844203200380c2e103959811300d5050002205030b071500000d840c0a900080200c0005040724066041014000000d000301c030592a41c0300b0f000c0c8119051040001800c0e0307140c059401840001300700350359121840180400a504105502900c84290750301c000380143c0e200d190200656450304410001543c00c08001c807003d011000396a0510402220040c2c880c040c01d00124041304a2075014a00d010a102a9049401c01010141e8542c036083c4a0b001c240384104800401d1041c010381c450710017110305031980548403040700e04c514290707541600300e06149441804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 661719397 1250 661718147 661718153
    0x6010617060f03070b070f1b05030613080c25091413060902040203010e0a05010905060d0303020c010608030403030f090b1602010305090c0a1d06091302010f05070213020307110a 78
    0x2411508290102c0c0e6510b44a50030b2400300b410a44943c0c054004008041010801d0241c1074810701c40c2203201e1030018038405029007414000c00302a000e580d8041d80301000180c4003045800142c0300c034602410902d0300f0190454010780c500310b400041c003003070b180d1a0902d018101440c182c00801a000200e4203210841800c2e0940084100041908940e403d0096a5105014030380d8010741c41281c0142040d5038941e142d0340d241e41500803e039002403001e4a42000011207209034865680200320080c043c00b49000180c800302d0107500050f401c08100d558880300058102c800300001d1004600c04d4460442c4c4000c035400c06080440258400d00518200700941e400e161014010140c1c40750b82401c00107011344403003100c20b240c032141c0c0e004540c000c1d507240c00125440d0041425903511459044c1500c2e1103035500400d1120504050300c01000140030503082c60700640c080c8000711224000c2d8075025060244c40c0d000030f101e0815400d400d184050703000023071004103a0b0040c10f203094150184010704000625036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661720647 1250 661719397 661719437
    0xc1709031531120305160f0233010909021305090304060c05010b0409030207080c0f06180607050303191409060106030e010914010c0e0a08060f07031b030e060106 71
    0x1125036031814968000454003421a11020b01a03401c100b003003440c0a4440406402010265070070b40c03641d0010380c2850142c0b4801d4540300820300e101d9019114640d444200d4080ca2144040e0510403002d0613943d90f050b500399803000c11b0080c240e00d440401c100c0740c54014448584900031601030403034102020042c140d58000111012921189400c10304001d007824568018507904500650250400402400703240d070010b807803400d031001c90341a00d030303030210600070032080c101c0810042c1c0d041403061003203c0c120005c0c81c0301c20b016440302a007010310303040031540c0381c3e03046510484001e2119040110401d104042c544500c101030004031442045a08101e040356035100c03014460041016102e0928445001081d0408200594050000c1315070107800c1559074040e114424141b4001141443d40e00954903007810742e1800c4035458005000142c55240c40d01890100c000c244506040d100c114403070021010030004000b818841c1d40004207001c0c0c000d04a407c4c014103034015404c00024851081d1800c0d100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661721897 1250 661720647 661720681
    0x50424030308060a03120206040302161a2104030c0512040315050a060506070309150203090d0b070c0807050a111017060d0c0e09160f090c0c17090315 66
    0x1802c0c0b030002c43e0b80f40e0303000640440b610f800051100144078040350b41e40703400041060249200303409803003440d0401c1c8080c0311041d1a40c881c1c40700c2c40715002851200f07000e5001c0200034031500100303041410005040303504480d40c3e06880c1100000c10202210050260501035407400c081411172075072503d481d40e00c55083c95078125806900d603d071303590086000c203002030344000000c2601401e40380d01c8108500380a4800b6501e80715070696011800802c410f940d00c04021110300150007001448042e0b80e80c0c40d1040001c60080c080400d01200d0700ca00c101091820b0702421607d4412801840c44003214501800d007280b42c407202ca07003d90500c00240489542140d0380c007038422880388400e01c15a40300d200040486541d520050840c01e888400494461154560148615898002c94101e82c0340814141c04640d020300c602a62030040d16030500c414444c58000c0340b1240843d00d4501c83d52100c40d2035800ca010507800d005040d85400089422440c00e003407141804500100300740100c18541015160304107020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661723147 1250 661721897 661721903
    0x1701020d0e0a12080705070615210501061d1305030c030706020406110607050409020a051207020610170312062205100905061503060117040b152e020307021905042403 73
    0x60f400d20f0f4015003400144000144600342c4014114101d208250001c005503d0b020b503019420020080f5050404898111000d441040264404c0d80c071400c20403202c42007490204c1d2a400204010b0021500c13c10141c13800c40c1c0038410050340c6a2502d00c003d00790012003840c3e207606030024820024103e030880300391401c40381c0a03180546d49080e100c1c0102c942d8490f003142400a0103400c010b01400310380c001090703446000d250270f2215450303441b1103080030703040b21000715170b0302c4c580c0104155200000d16103c000d800602c080c00b4050701c06015804008511504102e014410b5a14810450f4500072282c400340201a0020104054281034000c103000b43c0c2d000119004440b000404100c050f4410f10100c1c0410038010440c1980b0f041501d800c0f42e07240f6080c0c030324407040940c486858019183c0302c524500062220b00008584080341c6008091212504004a00f9800240030020168580e20b003019050240502c000d01d2150400d41048104e0795181340700d0007506d9003070032080c000b8800080f00c081983c1d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661724397 1250 661723147 661723151
    0x10903060c02160905010806090318010c030e0306090d0207141311090613030204061d18030f070506010f0b0a14070606030c0e041a060a1701020d0e0a120807050706 72
    0x3101c40d005a1074100c40c02d0080740b44454a02c00050440c0841c0d2110f41030710221429544e01c2d442d150011596400327100035220298014002d84c000700d40c001c1ea00221700368402d05000e0244112007000904021040720090003907001032a0840341103034140002c20103010083d8003200184880b101156035101e031810044402070391609800c0c0c2c00c00c840da064400c0410000e103242d590350607445031922980841c0c48100d02450400d800030452101840f008031500801924540703555507400c0320360100751105404044240010480b401c9114007210040c15a10b001e03400038107155140c24000c110b0010035501c40c40030001c040c41956450340c0d00c41580c0c809030042a407950784451080c01c10360010404e43c2e100616030900c3c00c000240c001c125980035885240903112081081e0300c00c8070078801600007101c0311540080350b20030a1100015504000c12000c0c803ca00050501c20450b20340f50498050180c0403e10f548012211010492480350703454a20100e07142204540c100000050000e00902030b0007000d207a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661725647 1250 661724397 661724411
    0x30b10020c01080c0c0d1d030a030518040608101d03120408460804080405151317061605250c0608070e09160e03030403060c050301091a01090306 64
    0x20300704c165075a924031074051311418207580001402208125282d280101707960f80716500d55250200300b01c29450303003686400d440c2051890464580107105100d1503800359072001c002c00c0544041211000041032400f0000b48a040c000d00250f11103440b2802c410320760720410103d020b0100b000085508280d06c5802152100204840c202528548d0350038101038095050303030103e2b8446000030000750303190301e01c2c0c00b4040407080f11002c8814640444020300619010041042142040000c918540048681050911540d00c0c0c440101c59041d500960f40210888400d154421090000e035400007200c681508503030032100405003440c011101c003900c055001c40c80c4071020407014040e0860300366108800c804040c7c0c96400180001c0c00540d94100001c40c402e040d180c2c9802c09603040e50082c0303402156642c0b503010107a000c5411500d0710044681602090000100003000350084010341e0601d91600b540700d604044c01c15007121200a03030340e0b2045401070303200c5d0150f0b40c00090300c0d07040e20b40160b00440d081e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661726897 1250 661725647 661725661
    0x61d0a0f03030b0d210305070302070c0e0705040b1801031d151008010e010c020c03011107120905120a0201030b01081e04020102011e0207060e0601030201120b041508010c030b10020c0108 82
    0x30300301c20006022034107103500301c070750078006011a02017441440e2010401d548030344000310201d004500000701480e60340743e0140908149910340d1503200546140080c41d040c0c4550043c0100d400040104003542c480c1c0901e10060342e010300038020002d202e09014540401d80030a0155104855440114600d9984004c14800c0c6550125040501a040c009115403594500124020140800858014090040d015841745010700400c0703096492007100c10300b0407807a611041c00080c010350000040c0000e12200080c0b40e150580c44641000300c0e00c018113141e00940c00054140d513048041c0e0340c100116038003044030007800200f180091107407481d4030b440d45907a02d1005070300504845c884480c035446413070070104800c5015001465581d104040502c02c1ca8603c0c0180e650b502400c5c080203012490a81c41a00c0003074103544450f0545070024008220300300d03001031818000c11290810030300780e5103420142d44003d4241c0180c0d80403481c02d0b00d440006990b81480251280c0880540034100411600850a2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661728147 1250 661726897 661726909
    0xe061509010210020f090a050f0303040b03132a0608010b0a0e0f060c010e0f070305070e070507020907080402011710170c030706080f010906050306131e061d0a0f03030b 74
    0xd01c1c10046660314038903160f456094006c841e03507a106001807000410035040461404c44d0101c400750040d4100344c18039000f0501504001d044038070304204980008045810750406a00320b03a650b41d5214644242c3d5030541d40072020a40050003801039480041040c041d01d45d0403200b001c6201d00c2c0900301e03407003500000740f0303040c2407041b00507440040801c50044445040d4003120607482018211800f910300710780c07019118003641c44040c0031500402c2c001c0000246400b41c0c0da5104449140c803520b40030b03a681c0000e80e00e000c07d842c00c10018045800708011541c100000304080000c0041e0118103242c000c8100b0809030060045800c00800610b5080040c401002480303c402c100a01b83c4032056210400240301850480f1041c00c00c44d07041c000090314016078400c640c10780b407010f000b600e003d82c0c401541c12840034000801715080905804030302c518490188602c5000d91043d1800b045c842e41c0c1d400030443c41016136103007012a810090380c1200185d8207130401c00b10a81d240c00c0100c0d05403040800100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661729397 1250 661728147 661728163
    0x60c0a030905070b040f140f30241302090415020a0504050a092d200c120412110d061a120313181404030302070204180b04170c03070c0f0e0615090102 66
    0x32704159180394204a2001007440e807280c0f848055928440f07070888452071f2951b601520403000c18441d0050079005810050070b9143e005000788101410343c0a0b6404010890740046c01c40c1d00003034000316043c440b034500558840001c1260201c140100080f10800b400f6000c1c2c44110040c016601c03200c80070005401c7d42005100384030030582865050b0a0442000c081c1d404090322410b02d010700305080700018003e005817001d48125030010800c0000c10790710340098503040076040d58081001840100041e2480c0200740c204030030030101700d08034400d640901184021240b44030071150010b0121000d069010089401100e19514400004480440d580c10050009114884600c0d000740e0410003496055002402c0340361007510204031405c04030201a40c4c0c91070096008005104840200d400700c3d0350510342d00c105000e283c1140d072905500c0350b42c0070720b59072000750221078441500c101005100100380400740146008200e002c3c040c0f61100000d9241586240c203d540381c0000304070442c80d81d100708003642c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661730647 1250 661729397 661729459
    0x60a03150b0403080d14010f0312051207180503060c0a230c150c040f06050a12180605010f0503032d120402091503060c0a030905070b040f140f 63
    0x1995683c0720b0500d10342c82d40c020034124440318100100350010360004040030341214801c083e17a84529041d42d546a000702c1d25140010104081400780da18288007682039503000e146076442e00000c500c080541d500f0b407580d03d86d0281d403007504404200a00c81840030101c504000151904601041d000c039440d4602e051280c40010807040080340d05000c01c00b000800c0300585140d4003c0c0031407540d40c10180380b5148518001c00c100300300d40b00001c101d528020405400c01004a003466426000302917451401c840b000e200c00400c1040f141006024001c1c00d100d407a024000f44a00c4009907800e00d408aa03403480303801c000304a070210000184068a041442c111481d078039420f2400d80e1480c6006250310510004c0d9004da115010781c00102d4003a4401310700c4141c1501c00a0080c104540e1000c60203001c0341c100710302c0c00d0305041d2a140318900060080c00a00c000e444030503103068a5030300b8440c46a1245865401c540550b20282c680c4240c1951002000301d03541100300c07196850500f00c0c140088410a51240303079 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661731897 1250 661730647 661730669
    0x21f08061504120c080f07031709010c02030604080921121c050f07090b03060a0b13090e060702070f0b040504020d0f020d0c020f01090b0a11121005091005060a0315 72
    0x34100079444c2850800c4a4125048420300c003c441030854840d10148002042c00c82c035003454240d82a2954090481e414050419402c41c0d8402d80100e400c01408035411100905d000848000e10720b0429030804445920801000d011540600c0b108e580d41c00701d0800042c0c0f810f002c106100740c3c45c0e0030105050500444076060141d410241000048a102910280041005598081a951208019a84641ca0040841420900e0890200680e6000300305422078010320440225802186001c1e10000c280c0080091016103411400281016101d800180100c07460900400001c81500c9c2600c0c00d8590407140142c0d94410140307081e0081494000e440d05490010503211a20702e21a07022200c0d030051074080d9514809113891136400c0f528032940c002d18030988107000c40e400744d940b98003140c085002803030b040d072521401c1485074411040454824455031020314062000341013601c0c0594122000c842125a180d080200007051f074001e0021000801d41d032140440c14050403510080e00510000d540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661733147 1250 661731897 661731929
    0x213090203101a1e0d0201050412290f04080c01181118070f030e010608070f210f080304030c0c080d0305060a050d0f06060f12021f08061504 62
    0x4450081c12440d12410f0114030320b81110a0395080c1030402c2240c45808100303100780f00c1e0804040110034080568244e04102c0c081c40301080104000c1c84201d034490052081c128070090720440b10040300182e0444600d80b50200060202ca0f034034041d040394200e0b900c9258240c03120100c54500340140300c01c0782441c964042e000c18420602511180a5611340030036500042d02c0d0007034640c0c25201c00029a402d50004d8020304111482c80d00c264804500070120000220700b40d5a81c0841901c2e0041c1038128070300c10014040c0401049410f8a10f8980450984410085a00c500c2e21103c1482c1d0306a440901103c0d000800901014401c81c11050381c0340e408005800629160070300c1070350340c82400c40e20344c010030315100c00309840780380110740002219001410441c02d541550303295038500b09800300c2100da158850700c01080c10105004200c002d00816054225010514010003100380304488000c140c0c1d4a140209100859009420f0b90388023500750755a01089414044d9550f50b031160380c0c8025940c03070380944 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661734397 1250 661733147 661733173
    0x1612060608090f01060302100e061e04061106150d050a020a08060a0b010905030d181503090209070315210506240604120b0a1b080627040213090203 65
    0x390b01401c26001120961091064254204c51141c0806503024240042c1851007500c90741510311140b00140005040184021246c00c20100240522015100c007003418041039a00c280c030001680300c080c0007080c5038209218104012840e0520241c0078041e000e44041c00d00c00c0412003c801c00381d000c0c0c4581038240c2d0b2080c1503a114207082c0c1c1c85501180c10007240304c00e1503200e8070161058400080c041d208840c003060303042d90344001141003102245500c94000560b000110b900490240141d140840c06c1c12052040210380032004114009151628a003a6025001b1803001419a4884042c02032600918000c03201d15100a00006240740719400402900b491170f1100c00601d18003030401708075000012410003586000e28080c100030401140207680110b49410700c045e80143c92070800098144031404010b42e0440003131543c03408076003d0818480c141c00d000040b2483c0da030354042034030403000b50700b18400305d540c0e405000070388182003028425500c40625488400c019034010115000d40400030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661735647 1250 661734397 661734407
    0x206100e2d18030408033103050c031011031f05270c0301031a1302060a051306110d21140a060803090a0504052a040f050301090b16120606 61
    0x11003000612030b100950036810b0600000343d034140c1300d030440554200106500324a00c4c203400051840096036002a60000d03007008101001c01950080024202c207a0b001810305180801c1d03441a420b01034685a040c1413a414544207032034124a581c440061040c0b44001842d140e500182c00440e4803905803c01140c0c08050341e000b504003401120040101c81e59082085e85190009200c080d2030b801080400810105920842d10381c0400440811030910200340c01190282e00902213420226a0010303c4c188600350030903010b401040d00e880c08002240e007041440361246060f60804040c048802c84a200c40c400818071017440c66040c2408002d031801d107200c4000500d4050f51000d800c1450b2020109101e40007004507840c55101a0131007644c103140c0004d200051100500c40f8503054401c420710000c170b0085040c080c0041c011300002e00c0d1a1414002840000c014603405170348660314120007400000c02800b41a544411048202c0035132801840d0140c69200d5407050404400346000e40100d40e1503044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661736897 1250 661735647 661735651
    0x3010f080705060307140f1306120b0a05031c020309090a020a08150a030b040f0f0c1a070b0403181d0406060506030f0408090f030a050109020108070206100e2d 70
    0x300c101c602072503480003444070510013500c0c144000380c55509889019100e0303d0060000918502020b49442c0f50180507102d4841d00c0e401403400a04214503100c1080c80364026030003403400482d60980310302c6c03414000aa44850707103101800d841d8007560005450500900a54901c100301910800c568500203060354001d40c811007242c07000c54091004244041c101d00c1201540d0000502640702560840c0c41c0d031031413010002e1084071481481124000003402e402040001284503403d80040c2c107081011800e10480354018600b815a01403098101082d03c0401c1c0680040c0c05040c0300da04d0781d07108054101300a055030000070801c1c40f14511a1203041c0300b6a809481035004510030044191104204140e5100c00c1e9400050f00120002050208404200500d1a481700130729803400d0304400c40211b0300700201d116060f21140d65441c00c2c3c2082d13503005034000d0781c092024400390401c0e241541030450709100c240244079641c503003800040c1c0301c010040b01c40714400d1040041601210303143e5401d03401d99881 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661738147 1250 661736897 661736909
    0x1d06040f200d14070203041211030a0f02150702130209031e0a03030b120d141c0603060507210b0a0b03090d020127020118030210020d1d011713050303010f 68
    0x180041c03080b0f900c02e01520090207441c01e0703400b644c0751902e45032903100c441c2c992407801e4603601c10400b40800c5a58003001403095540c1303d0107103007240360703614010800c0310186040c00d0301d0414030400040005a89a007480c012500c1d01360001a1181e4042001c80d01d0000080040401303c4541a0405003100b40003801e00810791090703909100b60740b11481804110b481c034080c4480319900c050904e0003828042c4d0340d1083c01c02400400182052400801d41c0d48880415140c8055a95100014006d01c5502e006143c4c7c0304006051090308038260f6401c0300311003070b82440c200340090350322a400c04c03403940c0e5006e65070020904c0700d001c241c483c140b5040e055100c18403140da43c1c2c095840d00c3c80d05031948261040c6625003a40c1c410104003c400c168006440503200c5c46100103420050240c00300050303580071003611207854143c2c01000c007070720340c0000a01208c48400001604007500310002e00300d0782e0700c0110300002444222001c070f000e448002d220f2601034500c0c50b009220340000b0001090b05030a02000d80100d5003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661739397 1250 661738147 661738151
    0x7020a0e0f0601140706051b030c040f0f0302010c1b0b180306090a0b16030e0d0207030221060414030702100e1003020423010c080d020d05011d06040f200d 68
    0x81e03200043d60320650403400c00011391000d02c44c440129a80b40d104a901c0000c034105c03c0068007400b4081c00440d4401c0301d80407140080400d040c080d901100100001414003042c1c0c8844060079600080c06004000078003e0801001c54884080600240d040c032000302803000c4030540303c003206080103014040d11032545019202c0c0130001140c034000026142d040d140c2101c18141951a10110a524800000501c2c01416200c4034042c4405600304607038224000e5590103030070b04504510403c050038030000044011401c1c4000880c09028005c185d2030f40140d400100560541d00181d200750460181e501c000c0e5010f01c17001c8131034207000d030031100048a010040351003040003529124103408a00aa00840000c0c542c80034201c4860404a500b00b004c0701014100309007081082e58801e0310a40c01860107180d01500402d2100d54041070740a85400741442d404203290038607009004900c10680284030502c079548407881400015000d80c4841c13900103146560100c01741c0442355441e05a4045a800502c80e8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661740647 1250 661739397 661739401
    0x40903050c0115170d1d0f09040b0108150405071509240207080109030207050d170d2a081911070b1815010b0a0302131212020304080c060f07020a0e0f 66
    0x4c1c0002c1a491540c6456449016076103201d5200d013501d80e5888151250003082c0009101c40d5941c5624205200d14441c1141014540c103001d85031f428040900d1380080c4042c4200180000240c000c40d01b00c081c0d5645c982002140c0d840c804003111740d400c2d1a408040030310a50310401540040f4188a04200130042e0202e0345210f564068007802c81d041e111b8003030010b0700202024009840e00300405000240114480300d030b000c04101c0c1c3c0c040e003544a00b202c10380301c41c0c0e140c0080e00103903402c8e211440300300ea510f440341c85102525000503040030350080404604070503d0b030402e400c0b01e40542c0b14049040040b1205900c074449454002c04103581a42d03000006054440ca4401880c00040c903174070b213107181401c44507459180018080d01d641040c00e02c0e50a25400344061810302e403510b5400c00c0100030407800c021111169041003012020f04094900c1107409c10403060203082000034440f111040d05684441d40c407e40d10304042424040e0000081d07211040d101e0000d82d00c07243c000c04d540503514142c1500c1a0b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661741897 1250 661740647 661740689
    0x510060b1801090f0506031b030f010303030c050a080c0d060306110d29010c080f18010e030601141002010f0e03072001020601140d06090506090d05030f06040903050c0115 75
    0x8001c0382c0b0802c85250760f001300034401810110013450700700051000c04000c040d6003981c10300c4103400487c0e9500100d42c0800042051543c1409811a030115a08105142004044001f00480c80082c189012684002341d007601111181c0d100c1e0000703641110b0200302c40e080303880012419a01003100821068109030704201840d81c0201c160135100d00b04500c4041d20161040113484449662038180d400000a1002c007080c103055900821001c460402c2e2040003811203000035100e9000041d03014041d074400b03801440041d0050100441c9040b00303c803203244007100464224090080341030403120303150501103001c164010000c090124070344180d5140c030345545001f040511780d81c20042c0c81030059000000412245400c4107000c040d0440140c0010149003081d01c80c40c00b920b08003001210941d01c9101000b1403036030144a1950380c2201403038007514600704000e00d1003982070040c1c400c44c820f6036078500003070815000c3c2045844401ca000024085901d05107051446c0c0c00e000d118200d402032020308280e03a6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661743147 1250 661741897 661741907
    0xc1f11070f05040b21032107022802040f0209210a2d0f030f031a0609040603050f0303090d09150305060301060f180609050709120510060b1801 63
    0x7034031400c1c8003620306107203840704000140c0038110015811071081e43c4440074880001c0c64501610469070002c40d52005030003034809220010102c0d05000211030000e21101030350120b101300244c0d5112881000303192040f00160480a000d0070700961040c5810f04030041c01d402a006005050011a81c4a0301591285003e041d4000194612405500300804d4200069040702c010002288580b10403480f1201d007062071601421400c0702907414000100c0d0704000c00d54000342c0c4c0d40444105140c03d0010520300381e06405994125140c280c8a850045400e4205d40c9459110b0703c0110b40080c00c031141e4540b8513401c0794032603100381d8403500c00c0d0003204c1c0b40d0101c080c024042d01044413102c02e10000780483d0b03010101c0041201401d030319455503c0f501d00103a04009a0041c4019007400750700c44c06841c4d500004801116025403041e08a60f084c1020000942c0c1c0110310742c01210750140d09403018400c0742c900741d401c0440c110400b03003800b0300e4800041800c0c181f00024101103111006144500c01400c401550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661744397 1250 661743147 661743149
    0x40c15110f060603060403032418150f031104020f0310080f0a080f0702040b06030109150e04030e120f16170f0c01050c16032402070201050f0307020c1f1107 69
    0x340640c0081701041c002882a8840729480c1c00241081ca01c2c00c0310701182c140e807204135520812202d24400c1c203010000640e0710501034880311052080741400c0c500345071010000994840648403071000201c00c4020b450310b0301202e10303101007960a03590f42e1500e17070f81040e0020711900a0381078510a80a400c0f0b15458000b428410749600442081d0806140300c1d84505142d00540c0c04a070030545603a00c030070058a8000245002e01040e10001c1141a402c01070048921116070051a4220600040c8400310340c1040c40a0f0060710140c070f403040e037070003038010f4a841d010541d030310910302d44500c0e01d941c040381040360741c803905445010107104c48403001858025620054440245450381003a121806158040c034002c20080d966030060f03c5d1004d13100040510b03c03401c15842aa502e444409150081000000513880d801e11500c1d411400c05059800080181c000d4607045101442c000004c43c00c81c600070004041c2000b0001c058859400a989000c0091540d81900c071022030300000120703142078030102c1e2501c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661745647 1250 661744397 661744399
    0xf07080f0603070e040f050d1d06180904080403050607021c0512180f030f0a1403011a090d21030501061106040f0305130902041d01050d0209040c15110f0606 69
    0x8070043d4182032400c441403002030801c032007203601103d06000241041c40844100300c180e44800c40416003003100c03038590304550000d443c8290b90421082090484904100c003000c035064581e140c82c0e96491610f5170081c861178101034400e20450f4104081d4550000d50003800c18039000d5104415400040203907800c0c054080a514019546000200c43c03420400404a08205403c112510281800205402c40d44407030a140e200e03580003e80c1c030410036000394441004a60001c1000d1540d031400c151000d890f12002c0c06524075040000f5001c010707503503504401062175080603c2540d03400074000d0610108001096540219082500001d000740c0100d42d04070344008a100585559990f90366020241501c42d0300840500c00c00344180c0140703001c403001d154090300d083c038001aa01c4e810071143d102c0302d6440307204046213078250742c006002c20f4407050700c0005110340c1590740304100c0c1c8551514030f602e01e4403500400c01c03d01140344005881f50b0b01054000e4094107038425128140302e4070b40a80c1d11840200d80742e0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661746897 1250 661745647 661745653
    0x120102040501020705040203060f0f0f0a031118010f09020f070212060601110f030f0319050709061121280905090f01060f05071106030a0509010b092a0708030f07080f0603 75
    0xd801c2b40c103000021114441c8000c0c00c100da000301200018040c280da81c2c10603564010343d0390f40448141480f004400040340146d10003042c640c54400981041d003602c1c010251107907000b24040c1c0e105178a80043c0c0e9415170f8000d0103101c056002810302c1c0e81d2828102c6445001130310b60f03051003d8800b00410804000d038507000240d0f150131500e01d15414985d00145c000c54802d11400300b0300042407094070500d07008002d5542c1c0c1c811032500d41074000b840c0140312140015550000101040c01041001203600c481e4800f184498617050701c2c10208800c00710138507405010700005035a9078a160b0384004204142c0700105c1d2540c080c1d459400640150510034003640b404034400c94051001305d8000da0240403040d00c01c40d51201c1d03d0040d5400318484c0d80007559426066601c4000307100d0070a90a0150b941640f40503200c0050b01d1400c105085000d035046201c0e0302c10400300c6000c6210100c101d100b211241508482034a40c1ca0500520500301e500048030848001880c2e10089000d0801580b4900d000310801002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661748147 1250 661746897 661746919
    0x409030e010c02130c02150a0e0a1104141f14060d0506031906090c150f053f0609010f0302040b0f030a03030b0f060c1e030912010204050102070504020306 68
    0x41d2814900b010040c2d070f000500610388480031070300c1d015038081d406096001d040403c002004d804007004010301050802da0a000303800340c604200003405c420442d0041c03562113508050402141c001d10200090101520182e82002240e401003600303410340740d603418440401a0781d11441c626081829500c41544654204407200074001160805900000002c2c162018400c1150000c0d20350311101c10125196a218420b040c00d0223880d1846000501146040f94064201c1c3d40c0000c00e402e03140083c1400740280442d1f00306031880300d01c1603a030041c9502d85240c9841c0444e05050038282603447c20744641c2c840d201000030b01905001542c14101e0308001c2d42c80c500c09055034204406003601501003600304112007007600c03081d5810003e021300c003402900c0020b07003103054400780030842c48072494241c040c02007004495085080094044101c40c0f090114420b140801d20541e4214851301810316408070000c14200742c0810103500800403604240c088400180c0e4410910040e8003084604903842154201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661749397 1250 661748147 661748149
    0x120a05030c0307140c06071701080a140c181902040803030406020f070605040b100506031e0a0e0a080a110604030c030810050915011704020a030f1704060305070305060409030e 77
    0x400346800c1200f50034050700c90340310720181c1551130704682280002c55100109000c002e03600026101c1d076000c1d070301003401c03555810000ca01da03a07100c0400c0c0080484004d100d0401d4020780c103100e0001d01c0440140512180d40340c412000d81c04407401d072440d10140a05040c2440f2110171407080703600311074040000c2c60450740c85484250080d0482c00d83c00013049010000000000c0c4148a0359100f1881290442440e042a06102c0041400b641046004107010801e12240c4840d0f45c1c04d042c0c581140b200d01e00250340e11409600e010703202c40c119022040c0300b8121043c0c100407400c405020840119a940c1c10043d08859100d82d4502080d680607012030302c00700d941e5000c40d208000716030307000300910f9240045079500d002081400d2811990540b940f803103140b5141003982d08c141907003080112200c85003d542815000200c010b80e040c88003c00217581c852001d0708205c21800000c48a01c901d00c09191038a40c1d0f42000340c041d040403280e58000a10f4403000408520f06446696007640d0141eaa0410304034000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661750647 1250 661749397 661749421
    0x3010f0302101103030705041d010b03150f1206160201180201050c0c0d0302030c010b01180b07170c010501091b020d0f0207090932100c170702060108120a0503 70
    0x2c8290b00030006811608246400104001c40c00b43c0010340d82d195882d03150210505242200395414000031100b0401005190701c42030540c3c0d04220030710504201540f100700018200b24100e070690750850528078490306220740205203e44105c1031900045d1141d111780500300d00700e07514030503809400e0f048008840c016502c038601030318030f5034248002c840003184808002005c21205580c220010b910018014403002028060001860b00c01e08100c01d18103400580000940720764010b010040c4004101c80080c0b00c1c1b03401d03483c0c14003001c07415040e94900f0b000c0c0640e80600424014803807407038248210340d144c0c1d0101c000502100d1106034042c0c1502c80f244041201c405241c001d2005c01c41c0300b989001701d030501e0240300303c03c509440780301e04200d000c1c3c0941c0e40d40388440240c3c104081d45101c242e0000504680460f00584100c6001780c00a009a0902404e95051082d05480038816400d07c040140c01a00040c502d4141c90340c5000300ca00348400303946110340c640729240740d10000400902c08504054802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661751897 1250 661750647 661750669
    0x120c13030f06020c0f0d0f09080c1002030f0d0b030c150d0c021c0c050705030c1003020703020a08030a05040c08030c03091203070b040c091104151215230603010f0302 73
    0x782c00098581504400514507041c14a0624012034110302c05185103030b42c1101c504906410141814840640342480945c0c40342020140c460142c182c5545501406200384119201c0443e44e200e1241c86091840b8040018141082010f020f03125406c2003800d1454802d8441e244841600f510a181c082d010034190042c00d800f882c000250721500e03840400142080d504981450910760f01c03075082c50254241140b6002207035011500a0300145c48018558841040302c2c280e94549040140c0e549070f140c5000c910340070302c201c0051b02203080070060210203401c9400050040b800b8132007c509080d11120066142c0c82190710070150340d07000300440c030b40c00c6c1443c01003090402c1600d800e40e81000d01c5c13503c0c1c10012803000c940845820345112820b20030269984598083c1d905070385800c81c1828286850040060583c10440c030900c191220304143c9a030046d0052070b440300d05c4c094105a2140c1e10800324440c050024032045045d0030403034800e040f03400c001d02602d0488400c07516001c6114170303540a111b692241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661753147 1250 661751897 661751903
    0x809151315030b1e0406050312070c050906090106051b010204060906030f141f03020d08030f0709122301110d060909120c030c050105090c090906071e020304120602120c13030f 77
    0x12400d002907da0380a11020329040e10100d00d050341d406082c42d00070410b079050b410140c0b290301e00c03200344049a1102d04955055425500345203a07111018072055001c4010713207030210203540c000500071400540c0190081f0403102d4070b8509004c100811481c100541d6200800f10301c816a40c000040c1e40f002d020444d04402608420146200326142d80114810101f1600d0aa8103410b002052041482c5510801c81c4d0119441c6082d022007400c01c3c1c02880403e122100160540e04840030500b020458083c803034040740101e034020800401c800840a0444d00412740d0b844c0d5551500d2800141d00000d40200e4010030740c0080500c0408803516010755050804440560030000c410307100f500051003d220b500d00448261000340302700d070300348030822080200040c40c0d050b20f07801100a02400e075400850b260000f1605080d100a2000100c1c4120720b54001c980c0600801e4100000a20502c4a00d034021b1010356202d070071280b00c80e510029803903c50b202750114011000300506003040400c0d10354201034071480c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661754397 1250 661753147 661753151
    0x41a1e0a05090a14060a080c240c07090f02040f05100e0604030809030723040509030d060f1701060803250c06050c061f030809151315030b1e04 63
    0x9240d00c00725441d1001112040300b02e6a4410084d4049190010708a90205007100c040d0400c6060982c2c042d00c0e200c038006014000c810b003000440162140101d901035501c950544640c480e500c0700e1051741d4421281c03003a8a5403034a80307468031140100d01d008603029070303c1c1112a020350307524240500c005100c105c8032500070010045844500c99955a004000942c051098192210410700405003000803a074095030f4000c2c8040000011140703004441810418115000929641d95540550031403290300041c90030289015000328002141e0070039a0203991448800c071510704040703011a422903c1034020b604a9034020b00200500c0b002d4510720001007020400c2103225008550381b00510740d169604004007140010415403040041048080c0d440400c0261020104a41544110008080d8040548403e00000d81c030019034a46041000d80386201d0350032266a500740c408842d401e0b401034011502e00c3c03102d280440d03800310b21a000e04400c00000526485c001c0f0b0208400110000460082c42c0c0c20503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661755647 1250 661754397 661754399
    0x2090a0614060d060819060b010e011202071a07031a03060c031605040812071214030a021b0708070510030e06160309050610050114070b010306091a04080405041a1e0a 73
    0x204140200151b0200032034588141109502d0041c043c0c4400305085410041d180001c0030700c076a485110404654424140103940b00101c1c00c044040762601103404441400d0304040c00f1109030301d984403c1c05a441018420369080c203002c1012740303580040d15482504075060021810b540c00c03003100f20182100c1410311900c2c00303580300696030901c0320020405403a15800700d00842400980b001c490020510751a02200300007400780084400e010103091154056400f0507410780d180d2000c0280d41d01786035042c0841d40f0b40d681d03900a446c2d54584e28003809014503802e00240d000d0a00071702039540c002292001600c219920120485050144040d001d002c16403170307681140c0030841c02e20080d400380c142180c1800703c15041c0070000d0034140d282061201c44400420008003c25003081c0c8075415254446008030340c6228034240202030706030404002d01136440103428030007000603100003042141d03000d443c180180030445511194080c2291110341e00060400d101075420404074a820551050040048005d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661756897 1250 661755647 661755659
    0x2090d0f0803011401020109032007030c1707170703110f060a030b100f14090a0b0406050307080f09190c0b0f0304020315040503160611070b0402090a0614060d06 71
    0x5104030005071800e460020051103c044500c1c2c0d6054080400e00007844111590707600100302d03008403034800c40b003000d411b0684a5000014480c2c0c070300554020038121038064441e00410203004452041c280c252103402030020300000c07184070b108103541100019040c080d1560300c83c0184d0004200c2ca5980c450b800d588690340341d54401d00988440d08a6980001d0000c03140303800d110400e50143d50001c01d200580001d40c1000764001c00042036844041e850b16211031000001c00c100f0400750b0040402e0080108020a80c42d80c80f00166208550540d152941601d940f0f0f680349210b00c0030780b0030040d690070581c1d00580b800214012805401d01c03402042845954a140c0003c06030440081d0b8011400c0002c00c0c0002c0d131800700005642e020203101400c0490800c0d5032220340da40304010362600a503614400502c14480d01d0342c8000194103c85240340c0d511800e5140c016129403048a04174170034a4107130003003a04810244a48015500b91910030514460580104500d40d00406000714510b902c0b05030220361 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661758147 1250 661756897 661756913
    0x703111b01021603030903020c150f0d0204150206041b240e0303030109090302120a080106080a020c12031f08100b0f1c050d0e0a120f120905040f0b09040602090d 71
    0x207000c5d617400602c0700003030700c2e00030304103100b0000f00c2d845000383c207014001140c00d91701251058650703054169580c1f421203009201a0049611048a824040580c2030442e07401242080c03007184107400d1841500d00c190040c8200d20b20078060010350200c010040010020160005030b5885542e007001c030340315100e80c00003d203980d000341c112801040e21140d00074109501080001044a11101054280000c482e030090035060b0500c80c100130048482d0105880041541c100c0d2400c0000005507528404209690402544192103112010062100135150461408420400d44021311f0180c0104401418100d002d03040102040d948403452104855040e5940c5150070315445194064440081c0c041c00d216051040c0c0241c0041400a10450700c109552100c07842e00c16699211a1000300d4600c600b056103072485d00680c010001c02101d041c070b01c5601e801580b01011103400311030a01003d14071403001815a9442c41e0481d41142d0f0003000b240c00a0803c4e005031a8102d8050807000381502680c0301d07105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661759397 1250 661758147 661758187
    0xd09020d12030c020307020f010807050706090c060e0d05121803012f04030b1603090602030901060f06110705040e030f07080901090608010503061801110d060801050703111b0102 78
    0x104001c084218000a503010b0150242084032030000d1820400103070042024058480c586034100000000003850b4a40104255658150020010403c60240703250484081c90640100008108101064007a51400c4803204001642c01000b412881c050015000490b07040305000700320f080880d4040d07020b207460074807030310380c1c0e844046510300c006126059148289441c0420321030101c007001c00050002c15050519650025806801c0305200350b1084011001010103c1004141e140000203000c461401500042c0640e400c1e06130348084035a642209030750050400a4080311038000300d1003000300c7d10b080e074088203002d101d01042c2c07480d01d10249401ca0059004200c101d40f0820b0220303403881e840d40d10071010700c0503007600c1c20800d00d1541002c0010742e03a0100107044803200d516090503880005820b400c10185c6134103080580d5110382403441d580300500344074020148558600707030015000c54030a0142d0102070004000e41403816050304980c0c2c605514041000e0030940d020403684140101d00c1c0942c03e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661760647 1250 661759397 661759403
    0x2041211041119050904110a0e030606010f120506030f011e0f0605211509102306010f180b1909142103030c03180a1203020d09020d 58
    0x9405018010400046500c5811202540340c0b0501c06845400750001c500340b0300a1103802e0164645109000081c00360100001c1d5454190000c1266201581c200e0031030101c2d51005c4007511000e40c0c03000011699000080c6034140020103450002d08400707500c0d88219000180981503682400b8444242425103000c3d160a00c02c0d06074500f103100083c113140c8248602c400010b03100340203151801d400250042050140d8410701c1d018107400740d203005000c120417002c0485e4112101c969182c8518140c1e19548a041081801c9003058a244d41c1d41c0340760043c0500c14500c8441002064494a0045807044610300202003030080380c0b4011402d40540e82c090380000c004400b0300a6039100c8404980c0300c04000c08075200c0a10160500078014028403071300d9016040ba00703450200780c0003010341030310348840c201c01c06060081c0400000d010048114034011486000390501c1c882040e42000d51045c3e0f2800008000381801003511240e46030310384660028154130035880b40120340d490107074002880c90420440c0803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661761897 1250 661760647 661760663
    0x3060702073011062a1204030c142202030703060e0402101b0f050109020a0f0b03040f031119020f0103020f0403290c04030201180b1c020412 62
    0x30803a035070100c2c07140d00c01c0118404165a90382d103a519481d05100350032400801c000407003015150541c6554007603030101c403286850000e4070101c5040703149110b209038503e082280a829010139844416201300e80840c0c2e40021110b100074944480050189039807003002e41e201c201a03100440002440200000078004018016500d0414001c054219005503110340f0032100c0c1ea000300005030b03980c1140103810203254108004041596400055a02d031a100020440e1816030181d8040c8001540035070512882a20306230812920f0354030102a481e0580304d85820100304100260010b00c190824100a5210381040d80050100c24903040c2003003000c3c44480c0555175045161800d501c0c01d40a00e40c2c1440c000c0c00e0031841c10b40d400e000c1c1f224900c00d50002400c1c0f1101c072070b0f02d5a581c004100f0341c0c030161075030b0301420000fa04002c9409448e81d0b001748001d83c0018103454003548411040e2014808552090b00d00f90300e050301c00d1442c0002d027032050310000c0c0c15942c00e01000074004000035290120612231006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661763147 1250 661761897 661761899
    0x1b030103120c1406010609060815090408090d290115031e0614091501020307030530040c0b340206131805060f060c1f06090e011104060e0d020306070207 67
    0x1b0090608000f03912240070414a94180010329480d0880643d004405035207100030b5a032075003401086442040f103904d40140c2c00920805c00d01801600f0101325080c64008401001310054440d88164000e0060120203440000248141030295200d030504880210480c0a20a050007542c400c0f0f035129802039154843c4074540c2100e40c0341c42480c0c04c0d4040020181401c000c1d601000007940e03402000d1004060140010388000c02107108015100a80e01851b0380c0b01140300034040b0020365040070344d02181c3e007580c1040301050b0807078104c05607807960600340c010420301d2808024202c1007800403c44d104e50540b003182c4e0300c0c0250702e80340010704516410580405829151024484208130420128030f0070510341814070001d541c4d11540b0403c284400c0307481700d07110004c030a0924100282e4400b400d038015002c4106483d00903458101b94215203940d5420000800c070b030036270f4600761404141e1001607031070100000c1c03045074000c100c0200100c0300545071000a01c001d501007450408140c0354070000d80c0c00000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661764397 1250 661763147 661763159
    0xe130c030b030708060711070e0106090812070203121b010c03020a020d0c0b010e0c0f0d0f0f090b0c1303150b09090708030315010c020d0f03081b030103120c140601 72
    0x1000704519041d001821441c0c600100380341c50f480090011020010b081c103080021071001c02042014120091720b6402c1543c1d2900d029105140324030400300b681c0a1415061010350703e020a5842094001d8003800c0c04895110b0000d2990380710360b2003130740c00410701c8511901d0f8600034442d20601c0c040b10340700140e641c0d2090f0400f902e44000c0c41c41c03600400c0103150204001a9100340b05904444045d4031082c1c2d241c44a5000c0d411901408a00c0c08082d24040f503d51013a5085030890a000340c9607040030404c00924004d41c00982e02d00c0f1b0005840107480c0d1000ca10303400b949100410b204554542c44400c5a6182c3d40d40d04a003503841024006007540300d41800045161018009405c202d24a000f0709004bc5880001920b0b400001e000081d1204487c0c01078582c1d074000e500d1031403900e50003032140400311000c1c0341418401c00c18500a800160805000500c450110040b00c4c6a6542d0208203e095a1a50383d810600d075034429004010170005200f20f400048031407901c603035a52003100180c5405e40c1040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661765647 1250 661764397 661764401
    0x1401090b06100c0b070530012114070f0308070203010e030405030d030b01030605090406020706060e010503070909080d05180105091b0d0c05061305030c0a03030e100e130c03 76
    0x501418415140745050851a50700204072140c1551300c4080c142859a40d100b0550342405007103402240910b0280f4540302e070084081840d1280c3c250a0203210650341c0750111130b42c0c2408104804002e401c1900b803180040b92512460b4201d5244443c1101c1d4041c3c0c541c2035a00700203286520444a6100100e1a04114075080c055030041900c0b08004508042c98400007a50301c600801c00341302810f0f514a80410b0300d03486500300e07001401d0f002c0c1842040382014948900254007800302910070700d181c1680170560420381c0d08400e040f11f000078000c214590502e37031044014881410101c480e1034041000000054090041c1d80c800c4640e580700d0403002041c041c10b9806d485000f005211650404401c012165401b514a0f91806030140c035107030800c205501e005002d202098010307980c4040080780a43c002c1040420f0102079560039820760343c4c2100000140031030f0300c0480c000180443e0b841200311006082450842e000a030751464001c4018031900007180009190140b11560300ba182c0340c085c5402c80d018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661766897 1250 661765647 661765651
    0x1b05031b0c040b0a0e041e0f14060108100e032503020f030702150d021b030a0306060e031b0109031a0f010b031005090705090301050f04050c01021c1404031401090b 72
    0x40d2003d010040c00400000d584204c180140644405a44081014050300601040b44c607004542d4003000a15142030400108a54142c203e5400c40c0002110382200004031b1554126071040c03004014501c1d03041d4450024041b00207040da6148820b011001c1241031409807000c0103100d01030071523010129401c001342003400c1d601002030380c1d40c0100300600040e218030050b4070f60001d0740a201a107038601c0e80001c0b40640300d265001014540d24084032030301460040020000d036000c5403010401245c0e210025030380d4514082c51158540c2121145111003002c40e0405000c072541403414014141e00cfe6a40d034400169280395000190403c0010048003202803502d05001d003503800310041c25403070480c0d40b190005415001e82405052440f020501f03050080080c1c8040143c010002d02407807070a12140350f03040d40100c03070589003403103500d18951840d4004078600c0031640b1490b41424460b88241400d80f500303d00050040301e041e408000000105042c594582110b01c0c07003100108101401e0b0510100c16500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661768147 1250 661766897 661766899
    0xb0403090b120c07081909080d0c05060c07021c03050301080105071b060b21030c0706030903090e19060801020d0b151804060305070303050301171c1b05031b0c 70
    0x1c200700c105001100300309881e51000300b0040d91580c40c138440c0f8000b032880c004c2d80c11048829a0080706020183d80190304034095403981d00886401011010b0300711146015010040d10303d412410104500001240041089070b00182642040001c02e48801164205a03403083d400a00044010300c041c602c00c0c01400c1d004500f6140160b0301c031000420100c09840301c4d80c00180f0803980d030141c0c425580ca0f20714501c8004480ba4a141818018001445491b5030000c410700e0b016008483c1d000c40c846019100e414219900355030347e188950305140640d540d1210181c041d4100b02e40502460a20341c2ca14042d10000e0228580003586507544404007409840c1c1d100310325031103400403038800d4403004d500906a403600102803000510f80c1d090080882c0003004183c00140690048580c04001c0c0b58000c4000e50488401c1d40071b104260100607c0c0a032a00340b01d000b807400586206150303004091140034504003402e000300c0d00444000c0150344551440d8040280b000c2c100b0a2904080c400c00e42c18401380c070303407208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661769397 1250 661768147 661768169
    0x4020f0607140f0a080f03250c172a0f0d0905010314073c090503070905040c120203010e070e010512060f18030c120304110d021014160b040309 63
    0x103242e41e85110b81c001c6d02d10300140810003100040700504142c0c0204403100384c001d04400a021381d2500100852070000b0251a40c0e01248040c151580c96081107a0302140102104115041c54a0711046901410701240000e4030408415500c0e00600380302043c0340214503150941d58a280070005070507030380030451006040703900780301b0851841e401c08455203000021584500b128580030704030343c900d08640d0a6013150103c5421202c06601c0c0c00030248016144210202d40d251561500c4240580352304031001405c1003040c00040080440303203c1d0b0520360340d01c000c0c004201100d403020140d00c0c2003000e41c0800d04d0401d5420040105050000c03403034041c00701c6034011b070145181c601015080ea00700646002072002c200a50101d0140d01401070380e41d101c5511007941c4610400c5148201907400541d429035503000d804031104814039104035100c6000354080c1a84610b15216841030314520018944c80c0e04002c010005d40300c40040c0b230b0030440c4c042031007100406003030304207070a00624220342900a104410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661770647 1250 661769397 661769413
    0x90c1e081012210201140103050604110a08150705070602190f2f0c060406050406020106060302070f0f0204021309020d050a151403030d0e1f150302010804020f0607140f 74
    0x802401c100400511020b00c0d6801a15840c03000700e005101c1da007141b038201803800d00007004112010401c14015805100000ea0076003074802000018403241c421b4244903408040d400d66007070b842c032440581c003a800c0c3c2000340c18141d16032202016680900003c440004a1100c02c105064000109665038081450810402d0316644110b1030588811440c030321034040c5468071407811020420000300c840f2000780149482d10340e1600041d01d01c1d0424082d0002550a142010614512910a445603190012006040448284c03201d140f0244c074004260382080d0200140e034103113040790088000810301c2050040e0782d050001101c2040383c02c081e04422110b410080078a01c0003100304580e80980d05800940c1206110400c0000d01d1445590302d036110301d03070400010000081001c1000844000c0c0c61040d110711100c8000036004603030024110041400c0c001d8428005548030794201c0d54070a00c0a00f48000828407900018050b030440c2d8421110304020044440d100c1c44140b01d000400e1130200e00400d410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661771897 1250 661770647 661770653
    0x5010e1018020405282103030506192306090307050108131a0f0a0c052d12061c0b0f0411090103260c0304090c1e081012 53
    0x842514401d1507209407455024041d02045507040300d000348002001d01840d0b4100349640d00309000c940c41d8030300b01510809400628204480e2650032241d0840c861400240c9890360b0a07801010041d0469030001c3e0403001032142450640301e00b00107003070400c20101c011100d246200c504000400340090082400f13119079000c64900244c0c06055030303400d003840b4480741d8900000710380b04d21220360007500403004800340c1c1e0103901d084011180150004a402032242c2d03601d15111054680d000c6121001400810613a0302c081010221049031a01e148a0403002e454000030810b0180c2000c0c00400345042c01e40c5c02d000d910301d03000d28403804800d503048000b54011380607103640d0044503000344417600140019000808202c0f0310040c1d00301401c0010300c88105561030342480c500c0306506035500807020386003d1810031100046001e4504075003104004618050404030b0007400f400f0481019414041361502c4032100030038040b64401140d03480e070b88075800c41c542900d2529000c0074640c00303801c805005000721004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661773147 1250 661771897 661771921
    0x90c060c07171f05010e0601030504121808120c06160801090207020a15030b09090a021c02030708100b030d030e030d15080d02150f070804060906110a0302090405010e 73
    0x1c4501d01100410b00c1d01203201014102140310048820b074450700203003a0708031035590b030040d41038a01d0000c038084d0300c1d6101001542103840035200504440268a81130005a00c0b410507100b01e45c9039400752055148d5990411031800504030168000c546002c102d03620203180c01c026103a84034078040b0b0b8a11813410f58080c040c162036018007640100715000902e180a549804e01c20034028181207100e840100ca00420007001021401c04880c8180380c02c0000c14040800011401c0c0038030380040000c402d1800013140c41d042e00b0b84101c8200d8040c0030391034002175014401e20040540300fa01d41d5021071102c4c020010141000440e181c800705044c500007a28000c81400000d03200010400c49000423070300c1110301038003060a49a4007549140c881c0c03024580c69941e000c6041c0071112070609a00040e51180c407210040c494023114407600007007030b04002801182c881e820940300c150244000003800e111040d19902154001c51841c03010a0300020b29003407604203442424014282d078001118503040c000b1441c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661774397 1250 661773147 661773149
    0xb13120503070e06040b03271b040906050103050d090501051e03130c0605041a0a0e090c070501150e0a0c05030a1a09100e0f01060206040618020a080303090c060c07 72
    0x20400002000155005000c1d092200148070010318503505e4550300c208006080d0300880c0c1c4111b0360040c5c1800c1d12805c4500b4440a091208000040e250480c0c415150702d40e4091444480703548951240592070104201d80714003406140074034007604201c0100003002e0140c01c0b15511103410045c04100d07808507601038034012000241c0000c10b10781c0d261030b101c040307810280e0b0813600501504500f440000742550404001c02c21509440000001c0d0305100c0721421050050308036150211b02014010341c081e140501c14180c1c41a0541c0b11541815010344a0300d0845040c805000411203070004184100304121950fa6800448a4414054840120303801007590001610150596450b110b840c2a8010003000110042c44090000d9000c0c1c500188041100b0000380705040400e0b0583d0003080c00340200b1204e40e8140da2072600204015141c3e075032000018002e9060402041004441d44401a81c69944940c01000c182c0001c684908203181441c0c140100514814801e0000f003200044422020400740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661775647 1250 661774397 661774433
    0x1061701030227012607051c030909090b070e03010c0c110111060f250f0e0a12030309060c0e03060126032107090b09120309100306030b13 61
    0xd8a5140400b443d4021080396020481c8211520b40082452256400950300541d000e1203841c0103c10110701d01d5480710306900600d83c100c0107414070469040a01c800d540c407614032074600146c6e12540c6400c000104c8140315421a40c0802c080140500d4a0b0700500d01e4010710404c80c02008000503905010b08017030b4880400501c1414180007184280c0e0080c404d440c01c0709200f40681d00546040301d0f90b05640601290b140031200390195110813459070040c107104101c0c000c1c0e160b00f04081342100040c0c5158010144d0b16500190f150004240101c1d0712042d05003240c800c0e10040751252483c81c0c010f081d9800019640704004088000c460b07503a42c00141c440c1141c403400401d400480400c0002030001160b50301030b440c244400614010904840b901020112040035101c0078162a85002107402c0c0e01d1621501544207000d01240000b4900b14504a1141c1840340850b440d101500c00400d00700005800490080307550346c2410024041c83e1820142e0120410541c0300d64800d007a900c141e43c22640d00500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661776897 1250 661775647 661775659
    0x6031c02030f16050d020a03080f0a060302270604020306030a0f0602090418031805150c0a05061305100b0108040f141005180a0206160602040512060f010617010302 72
    0x24856160007802180c848182010b18981e440410b00c885614002640b42c003116140f0868055903e02440071a4410303d040d071643e0350007803c0d12403200b12122004054050548155124000801030380c0320b080e1494002e42120aa12110000b008545143d000040003c0e00480c010010003035681d40128650461a9000072070000810450408000034050343c18069001342c0340a011118030303420b10252915a0344aa518000550520b0300d541c2c41200c60b40c41500d40000c00030b00a40640c1035460044c140c1010000304841c124025911170920b041400d850ba440300207404a601c2040c000c0501032641139580c82d02c000e02180c2c42000008180000c0207001404c9440c15103c03070400c11454481c020078010b0a80122098414460603a40060800303a6001003030443d00c0341c4241105001007142020160010aa941494851212004207400317201c2d040b651035500b00004100741d50b5801043d00c00c5041030000f401c2c11300c8d03e107070021080801a00954240181c290f1480f007204030358040e0382e055990540390 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661778147 1250 661776897 661776943
    0x6031209130603020a080a051603050a1203140f010f120f03210c0f080901200a0318080d060609181503060513110f0612071b1b06080603 60
    0x10000c000c00660300005e60069070b29400003038030040001c075400014041c1d000c0d40c0c40c440300c840c03400d62030f100e8a00c40101503410901140f80840c9040c40c480421103100d09011031403204043c4480703d91071007200e5029070118220018480c04140c9109903000d0b0201103105c0200d11001d454480c1e4580039680001c080020450668007464800424100f00364046601804070001100700546180c41c1c078818100040c001c44001800f003001401000500c00e9051400e43c0310113210a04e99a40380d002c0200d00d403d02d40c07901d441003c1d0301c3d660800b80b41c00d0340c000e070b00654981c9082c041c0b080c00c0d124158010b004025400c10103000304404c03407038019074030010244002014200c0f02e4100c0f154481650000e44a14601000c0110408510b210021494030030501d0000d480501c10810202d02414101190070407c00c0c49040c03c688254403400303800c01005e0400c49070245100c044000000e40041c030407500c18010090085a0342224150078010340b0060802c8407582ca0b141021a5494610340d10320405050300c850 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661779397 1250 661778147 661778179
    0x30603151104122607031b020102010e0f060417040501140c0106050a170d020601080d0c230709111801052a15060f0303090108091614010806031209 65
    0x3114000c082c8103c03c462608924205a586029266148035080940f49030004200d1800000c5030f1026038141c603043c02d09600da00c1c25151810341d181e01241950340c0c0ba081d60309804c900704005814000c0391002003049180920700341460101f0142051401c000030b000600c4140c7e08101420803a226886103503464040c001b1900b130161880f94011034101942d400d0109000440c080103920b1002810201c1d840c040000c2c10480e0b0b211070922901240e41c012040c8810010f05c6100844080d40c000c3c01151040c8104100d14850329120300c84480450b44070301d10420000c4054084c152110001c0041d00d802c2400e81c0800301003928495032114100700b800147c1004000c40291080c1100a0110013200071803603402c54159a1600d21151082c0c01240707200048492034000094040024040e01850400e8505801035641100250810300140900105030a0b8001000d1416000384950f804070070241d040d03140050840c11010700018001e40121184034140c0d44940704840e112722080d0399190340152484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661780647 1250 661779397 661779431
    0x90f0406110d06230a09020c0102040e16091a07122705030f0102090a2616031a13030e0109080a1b3303090609060504030f03060315 58
    0x241c49030000c00780411166a01c00d026480041900c4580188284c0d9a03090072115000b815104003056010711a98010300008402d60060f0508809003c005828070b0345401c0302c00340801048a210124071501a200d01c0354a034003609460061400380d908012408042203d1340340d91250402c0a0104444000c1103d0100c0c8108040d0804c04400c5440c4600c02810400111012429109142c4240f241c4860502c942d24103208480c2c8441c0014803480c001490000751080c036014034440f80705403203412141007003032001c2481400b480c0041c4400310301500741545010f02e40e403104052024500c052100410040b4001c1d032989460702c64140c10308030150004c990040b50340ca02e503a009070600380036000c0328604124501c9983c02c84110307118000361520340c50307101c2d030340c03054045190303800300b50442201000d00004888155803022000380b43c08100380c0c00c96118a0151800c4107400c17220f850b9180700300701c24550302502003003070300c880d5103030600c40b42d403442e00e0740702520400400341e4114960350450750800912030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661781897 1250 661780647 661780661
    0x30905091021150e03091c05060415050717040212010e0d030e1b03070b07020f06160512180f0d12120b040c0807051e03100504140105090f0406 63
    0x700c40322444001c1a800d4a540c0001202e0444110850340b032241400d881078043c000003501028011414001d00320104180c41e40c100c0c00d40e48150210304094408103805101e9a440359009a0121444d00180c0c80201d080741c01c020050410005012450100111110682600150100d601d207205450b03069101c0d0050102101e10ba0013449280704050807030f41c141d081030050320000c07000d5805c0e8090152090003028465001e03142d0541042c1028003900e40d0642c05006420f00141c00c8100c081410340c04070f20294421070184141d0314200448000b0071500300110b418840780c500300c160a02140a84c00c824104030541c91510911101003805001e0f02d4a11040100a801c2541802507101070f02d006002100e42d10b240403401403e000000c5202c1c2030074000c50180c803000e44d5802046540d01d103811100c40c0c2103490b8800743da07880c04480000000c201da020f14010000410f01c180003500e09410001101d203040406040c50400e64010407265075100f000a82c081d003115421142940c07a0300d0721200400c0c403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661783147 1250 661781897 661781909
    0x1101060504060620010b010c0b090c060703092408060d0f1e020909060f041403130305030c0d170601050307051c1418062a0d0203060108010b04030309050910 69
    0x14008001031100d84c881a01000040c58070b0f15000c2d8030400714039030350aa604806210303020a1458814900140b0000440d5030302c050154251882220060300142680d4460b11007036002a040000c01d0200c400c01c400545125030381c00e00510100e524242c000ba0801e40c0003000d8501c108a142102c1e400c2c0090350b200340019942c00f1120319a055405420000c0c00c800b0108284d014900d42e0b0000b90800c2000150f80d03004504040d00d0110740d030740b60b50b00c100785409400c61100300e5000506c0000082d060040c2c0e0f80001d07610502c040e585551701c45a0891401801d488a0702c2000203100980a115520b10350031034001c5d0080c03802c0707540ca58903174400f5511449075909185803040b40c490075003112152540401a000c0d0500c00220301034a40400c1000c003c20b44400680c0a508200b01042103d40f2408641ca41070038030101c0c00300b50840c02040010690025803980c24583d400104220300b940e40175030a0717800342c2070781000c05007400d055403001424404140607080c0a80d1240c80814049004403860b00000e140d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661784397 1250 661783147 661783151
    0xc070302031203090c03120304120c15141b0d02070218090708010c0309152a0e1c170d02090909100b060a1d0406240905030102090a061101060504 64
    0x480b45030401040d4000c4910440d14015400c5242d140d20f804a14851040380740c1281c5420754036140c40c1d280100d8080d41181c000d0019822580c000940308500b012a0691040070003e0212030003100303d49d10030401490341c0c1010303509081000842c2c4001013035500c060751407540141c8800c8184042003002c44d1941c0c0000c8480f844800700006640002001c400780c0d800d000091009001c0740d207099098442c1c202c03005102c83d21b4208845c0311001310713500105448002005202d034041a150b41004a55400c030744d8a0002450080850751509140103043c600c8140c8141443ca24441503c3c1d6003003003c05d032040d50a10302d000244140100d030407501a0b0365042d00c01422030b155800c004080310343e42d14030300601d041040d0424000c195940b070290300b500c3c0c0402c140d8440d5150300160b0550f41d01c04da800809555800340c1e6502c8080340850340c10803840345503021030114000c0028600c101808004075031348024801e0380100000c8905071202d480340703030884410307080804a60001503a01809404542c010641040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661785647 1250 661784397 661784413
    0x509070f0312031505010806090603120309160e0402031c091e03050d0305010b09061c1a03060c0708040e04061415040f020403020337050c13050702070603020c07030203 74
    0x11401070040300ca00b030191010000e00704000058102d00c50284191800702d2100302c009074080c24400886a4401e02c010140c44010151100300030380780e0415a95050240d0001d5107a4903280c00c01c8118402410007801040c50314a020b41c0002d9803910760f40c0400d418040901c0b000c803009402000041c4c060b00ba441c0d2415070030700e03010003030300700c280c00d9840207841d41c0c4074100e0100031a034044e11a40c2e05995554501300d00d0102100d09100075540020800c01e00c0000f00424804904071600c6001c51001e0400d4044040c01010f81c101803800e0405480c9a0007624100705040020310400122001c0301c4c0c8070305000c2c2c7d43c0d0359107040c000014454040c1c0b109042d40c3d901e080207440c60a0001040ca60007003100e040205142c5848413504030700940c00300a41683c0122040407100740d01c05021100914101c02605281c0c0030245006d10200402c84221007980c4800c45101d0b0500d8031a2070000c00c2e80d0402c1c010070251500382d5000b956420144160b2052540c00102c07022a000c0a02071140a10340140c1240c4101d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661786897 1250 661785647 661785653
    0xc021f03090c140109060e06070c09060920040603050414030a0216060215060f24180f010c120201020f040803040f0501090303230d05010303030914011104090509070f03 74
    0x81c181c501c108486214440314003041002a60000b0880804181d5800561a0a081c0e0a80f510425403400c1680002c05100c030100268816582c440680080400400c46d18984101082a6441081b104140c5400c0010100e50003000d0006e82c0d0441d0507e240108103504c0300d08046d12031904042480c80180070004008103115000078540c04914420039244042a5032448203d84506511000c1c00300606e800d408517507070f40742ca00300151100400404091900c580e0300b14200700d052801511007a2030101040b00088407100a4912440ea0710583c0c241c0740700802200020400f0000502c018202c0c0c001d0810200124401d6040e40c140d0030801d05c0c0c19660300d44549540303a5130b0b002407040c0d80324492202808102c82d480303820080101c80d81034942104900d4000390341310040ba801c1d803180e0001d0a00344903208081201d8001c941c02035010751400514030042d803c0c4166281002e000030301c880c3e810581e10000e2442400c08440451301c61800004103034072111000c46c00c2c00903c0d4040000d1a03101c1c0d601000b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661788147 1250 661786897 661786901
    0xc0d15050916140a0f050c030405270601050f2b0f1509020a1b060f020f0a080a0608060112020303090409050303060909010b06040b0703021009030e1008090a030c021f03 74
    0x1d50800c6446034240d103401c1c0411003201e8495004d0b500b0000e10340c0d031001030015001c2c00107080100c030224140c9041036103038004a00c40c0c80b4000d0880007840c03000c800709101003000d401540c2e0491020b1034514036000ca00b4003262014410000c46503103000b440703044840941a4440c800010185030030082c0428188803248002601419102008405940030001042c582c2c920844400c64060346801d00303907006004250700040340c008815074045803280c40786170300e0380c26600c02854200c080f810b0164035014450f500402d2000c0003842c07100c2c041d10b884400e210345440024828110768414001c02800080c510100703065004032001c10f904242081c05400400030044040d510a440c10390300c0d6481d07a5200252542a580c0c0e0101c0701e50084400c22050000c0c03015140140074050003801110600b00303080b607818007250840042900001c02043c0c400445140140c1d001c48941c4181c07914000c0d6081c80c60440780c9441c0307441c00040501c071445d020b41046454a54001c41c600c1c0d40d010306806036152002003e40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661789397 1250 661788147 661788181
    0x60e0601140d0213150b040801020d0c030c09050423090705100903030c03120204081f0b0a060e09040501110c0c010207090501140112200c06060402030c0d150509 71
    0x40741c018003400c080340d2401c10703009268070580c0041180300c002c005501e078500200300d10070345600d00c4660380704085201d10302000248002e100b0440010baa030985170840100701c40011700c2c01410941010a0704a4490744040608142c5000300c80009a040821855040341e480c1c010704103503c000304034100070304242d020410400303c90042c1c0d0200d0124508a0701103402c0c407228000140490a51a0ba070000300c1d101300c0709021b0203400301600502e01619003601c6817a001401c81e480c2d004940d0003103600c0080249014252240c40c054407c00f6280d0706280001e4403400d44981498090100400058140720702500105203083c0c0c09414941c2d85c6546120550300c840305a00540c0c0588500d8400194803200380c40f60303c0c1280c210307216158142c0b481c80300440c1c1038186014415031180e01d4070f40030b10000118002c2d0300c1c2000c145585482e86c644186400301e0816034024071141c03042d881070080010040400d0100d0700320032800305002806001c0c80d4401582500b140d0013264211901d141000408680499620 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661790647 1250 661789397 661789409
    0x31801030213090b04051806130609080313050708121c0b061314090411010f0905090108030c0f0d0819110a1d0d021302090a053303010b120c07060e0601 67
    0x106c0f6980c0c690501f00c01d400c2400040701c8980d072004000139039114000103c1c55a19100342404114002c45840b5113009070400d40c2e69a8841c40d4a0700c50408110081020500a20510000d0310f03d400d000e0404842c1401011590211107105042400c501c054a5100d603d0712100240b070741e500c0b529a501d501c010f50075140074019615000812003049850b0804540780305036440780300d40200702220001100e120400d5000c110074440c031040d01003180d940e5048214040e2440c10004d54071160000c0e2540d00d041c0c03248004220b01e800000c4080b1165910009140d40a103004030040e0400803600088401844840700041c1401000b2038181c1400e076010710000400d0480c00180d0074800c03250010000d0152030180000d6200b80102c0301003171440c0300d6802400c440c02000700651403150356800032800101e100b141006e0b00d0340d4058441134828501000c4140c5200e1010758250a5604015852205109080862802440260002d11101c5000040b0f44100e13030303c0395003400361a48802000755030704402c1c002c0b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661791897 1250 661790647 661790651
    0xc0901081e03090306060609011e05091005031605030c0403060e1615080703230901050f01081c052b06030c06021506150c060403020a05010b0a08031801030213090b04 73
    0x4030a116100006640040c3d038018050803070781c0c6450301000210783c04089018140b0882c0703401019030302c106d540b501e07080890b40c1d1545d540c0d407901e6004112000b4411642003040c00414001d11284e05592500c20502036064208569a5140e04050228500881d0b03c02030405040002050007140e01107043e001c80201d501c80b0802d1141c0703034005da050038601d01c2c0e440400603891b0000140c41074883e41000d4050a001c42030078007800c512000b0640d8060080b100c0c00380c641c2d181c0c0d0501aa002108406c1401003011002520710171340c480480c4110714008415035400c10401080c11320525036034140f8000c583e842030701000e01c00020034483c04003400e09440305440864044500042d018000f2540c101d2003111041c002d48160748000c04c0201541c546200304695900511100c110090b041040034003440c0030b5001401c4c2c455003498600c0c25602c1d0b80c843c05000d840c4494040280900c0081070710542010201c1100d65008524012002405005003602a1505e80d000008510319554002c0f2841c3d2401e56003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661793147 1250 661791897 661791943
    0x6070c1215050f0f07110a08030f0f0402010203070605100f06020604030f0212040b0d0f02070318060309030e040b12071e170703120e041b170403090501110c090108 72
    0x80070301120812112051140c400c1070000c1c00c0c0f2058a08181d510144d00e0505c80c0070030b400340d5555403812045010440f00640d001081c850003911203428242e00501050b03403e0f00d5031a0950000351240a540c1009100640307030345c0866018090501200c020b80900026141840d40d43e40f4000d5555109840540100e40c0c002106901c00e03101043c0d82510035449400310307240514105403a00e441c0d21000c603084180d662540400c2c0881c0190005028083c000e0707440500106a800f400b0160590550020017031520301a81a80000d41140000b400030000b214002010702038031b404100d0351100101422100d01901c1c401045140001f0996150400c19141034044682c4a5200c0c44e0303400300c6420a1100d590141c0350420024400894403552851545402c5402012583c0820150b0b0341e000b040b5204215644540316507690711103c1070034182c03242c000160b1181420784000e800704816014982c10403a10803a140b80c2d07008108066042c08001408034461581e540e02010303202e107103c8940d80651115103207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661794397 1250 661793147 661793183
    0xc1502040915120c120f02060d020a11010605090720030c0a0203102c0312070f02010b0d080702210307060906110a17070219140c060a1d130f090303111c0b06070c12 72
    0x2003041e00753f410141c40c40d4100d8880100035a44c0c2094080700b0f80b0880c0045007030b029404418400f0f020113201d16001001204c60910401d41403139107a640f030040080c036000c54100340c81e0641e44c180b010903000503401c1094a83e64002d0340d04500c140e0b007581c540710708000c080c8821143d003e2031607a00102d55900820000b1030020070044907c3c40000090a0354109012403805890060300b0800007034003055125600e0030f4082412400e580222500f0744082d6580c50090062010078003a1051035101da84220f454070880c00405031a0f841e60241c11003101d281e450000d2039450080002115000c90050a032813450301ca0702d006c3d4855503450f42c000106020303001d410b03156400c056003aa209040603403034505048450791401c18641c1d0110800350b500c04541d405645100b02e017489110360045036104041455082811b010b4161070903180110710a1030100140e01102c2c101022000c002d501d00c51020031003803100800600e46001d001406051400d080300002440c940c035602d001d00b0740d440395000381c0c1e414403c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661795647 1250 661794397 661794401
    0x1210501051f170604021903140a031d030318040b0d2303041a0304030912030804030908030a0f08090a1e030e0301110405010c1502040915120c120f02060d020a1101 72
    0x216424111340d01c808081801841c014840400000d01d055188420554a4880c10481c49441c4071500694101e002020305241d44060040701400c501a502660070380450046696407246000100810260300140e404076590b03600034100b4104010b017400300e982d1183c20850b60f5a183c0c40261040864130110201200c0d201101b91001c0f206055922018140707401070340c012962000b08218204241d511001c02d000100c5840d0344035035400b03661002014038007450054600000c1d90045052580144041011a6404110801404090701d4982c86e41d882d02012a80f900c4d248000082c0021200044048907071100300c120031041b8026982c640915461105040c01c9802c000c2c1c00b0b9240442c200402e002ca540182c20440d00613101d441c42c6ea02400c146a0054105c0e08641c00c00d0107000e803119a2031007501000704584002c0c000e40c0d80b070a80c1e0132417141d444010a80c180d00c0b030880980310304900142817006900045060f00d8014044070f50320500c00e8501700003588010070b0000400e50b0303030b00d281203a05014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661796897 1250 661795647 661795679
    0x1407090b071403030a020d230c0313081c05060d08042d03030302210403081b190e0f0105040807090b010203040b0406081012020a090e01020906070c0f05150301210501051f 75
    0x100389000305460b0801e48040300c0cae100405040300204070300034400005034000001c010321041e014800065001080358002501c030040e00c0c00d803185200d0540ca02c041144401114116022540000100d484001c0c11703049000c514181060b00c2c4001400010030316070140c0003485400300c2c010071441040c12100243c00300000680c6c003d000168840c000886100078840085020300034845e0641c1084898421b14603048500f00d80030001401d451098000ca0400095007103100c1001d00b456802c2c5800c0c6240240c1d079121030310400740402e84600e90090141d00910865000d4800000400d541e15100d030700c003900050b0b0544822004012034035002070002c0320090078104a5a000306503074a43c03441d0a40c814080c00072034040524556080100d2000d0340e44080040c40741030300c5070382400d40d0360740f50180082060038a988000e000d41200d00c11540844440e20440307040d280880c00360f40700d00540411803142e8902812000784690f19020030f22a012258105070843d0481d800018200c6d2519865065207078805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661798147 1250 661796897 661796951
    0x3051e030702011b15060e090106080c091806091515060d05060103021303050703060b092716170d02030a05180f04050c0c011407090b071403030a020d 66
    0x41030141c140198812800082e00036140c401126030110544c80c0c1400c0120740118120b07a03e599540d042101441070482c080e13102000740e000708a81c6250111054680142032030461007002040d0010711034140b440b03c03610705402d4800458142d0724018807826651500116849000da4404001450000911500500c44e0701e020303042609100c0c860804d5070203828054510b0741490b800b8440c020102c40e07103900d03400086008600a1030000d1460802c68203c0b0480705c26a801409200b080002c2041c1e00f07110307014040111804016240950300c092800c2c58070060110200010810b0009051001103c81c4c040c4013403413000b5105110745484080c0d07501c0c0300c0c4080303800200c1d10034080c07202c0596211001884a640203040c1c07a4190310104000b40031154116515214140c2c0880e03a200c10200034070030799440c005040c9107110141820007010380303c1d510622900201c0c2c00001603180c1040348606c40c1121808540040325100d00300002510065001440c013803e07690300d0304249001c40c100c6044144c00c00c81c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661799397 1250 661798147 661798153
    0x40f05011503030e040c0e041a09090109020a030b090c0333010315020d0e0703080408070609081504030c1202071809080a03020714030408060402400603061503051e 72
    0x1004c001800041d209500c1003000707020081c03504945503152802100000c142030000f101081c0d11f0b41c000c02000800141440115a240c41c1d60440161110b020b00c030207581d08014091883c0e624100071902c2c01290181654241c011003080c20ae0a03541d143d444401a1080c42c20400682c603001144080f0040c06d2002038031841d80c11910707003e450080e83c003e001c01090b40c0004625138168002079460000103500c00c984c0390000140400c901c1005115820241c09589051045039140c4000e20369268840202c2100c0500000c2c086409c050103840a500c0450348032007003001c0045c152a000e074892440e0700c10f420030b910400100c034410901901c0341c0c00c0311650042c00107043c2070444101324001e401080d82240c9540b00d9211b641c4001b1000c01c06480108610001450180303440d105100d402c80001440c480d460035640641c160f20904a401c402c2381c604e0025409496104c8116404050003c69101409403882c00c40034000b003e5803030b0a054152030046084a0641c0c0411003085a000030140040b40c1c150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661800647 1250 661799397 661799417
    0xa081902120a02060708030708100f0b0f071e020a0b130e040203030405090a0e1e1009080d02040303120507050c1f140c030402030f0f0c01080606070506040f0501150303 74
    0x85000304a220310000140101d9100d95040da01140b0103600468060f2006d0801100b048522607015010f00c2c0c0c401c008100c400411803a0043d214a84110381c020301460100110f511001c1c85040410796901139040030409604030081c0b680c1180c18800e90340141d006800705032011503c1d1411004a030324060384d500b14008882d207842010b910450018100700e0b410f0204220004990760798245407401490310700300001c2c0144285116500d402d85001c00001c40c8625207078144101c10700410f4160340400c0c030510106041c4114641880c25100d00000031b115184082404414190701420140145200070000c2141e034403240e4003035525003d0308105d50b4050341b003140c4820900b180000f00580706004c0440106060844a68078100940c04075400404002c0100804c001e520307081261003a8043d0000c00b83c184500b01149040e00c070b4002005040c140071888010514545444044900709078000c015600d40341058034000e00c01030014001510150300f0716181c19100744803044a0300c01c0302d900d41c0701d441e220 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661801897 1250 661800647 661800649
    0x50a0b040b04021e0c0a1205040e010501020706090e0709080d0f080f13030c050319030e0c09010602030f0c1504111201020c030703030b0d12111638040e060a081902 72
    0x40c5e024821101c9140100d13000440090b050044000f140c0916880d655103c42c2000c030340c0f8044401c143d0041c4e045500103082042415080030440080d100031410b00740055036244001d950403600d69100d0443c510402c8010110a03500c00021020b10809641d5241c0c580c90b4008900904074041d80c0404a8090761029040001d00410380b056103240b1460580382030442e40000c0c3d61040071903454441c0400d80b9100c22014080c014040807003841d004079250052035041c070000a44d2400761101c09081c103500016103442181c4c04009003a0808090051180149082c1c07611050301015942d20501910035654903e001403010f0080e200009062002913040c80e510b502d0440142071488040d0380c11214016408010075001c1c0150310b8044610340354900441d581c000d6642c42c10500004c0e001880302110024002c0b852404000e0001075686241c86424032000b0300001850b00b1400703d50443c034100040c0008039061004001c0b44564004c403003456000c1e60314031a10b5242c0084c071140c040086011f0b503c0f0700c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661803147 1250 661801897 661801957
    0x10230c0a050c1f0b0a0e040f11030c0a08280b07210e0d08090d02072d180b040203190504080c2a0102010e03070305030403020c04050a0b040b0402 64
    0x80b010000300c9068000c80b00c0c0b510182080d48015403c156215403010105042594a0300010090102040518034254441034204034034100020600081802607c0507a50300f0002d034014060000d041a00310303a1b8500c0ba1550f6240c411140843c1e655107940b19140880240c440030416640186000803d6a14400200c50707104003540508608180030070b03a62220409131043e40f131013802800c01040e05821680025024440080442c801c039402516508021075000c03514601315503070109040540da1400d030503002001841901030801d403841560000e0742034a4000b41c030b00e544a03c01010810440e2880c20721060344400c03100324102d04420358400c0d19100c1035911a90f4032a001e5444181414001c07204c05040c10a2181201c440c4c04204002d40001c010010ba00d00710500300340001c0120028042c48183c40c0d0052500140901801000150a06000b8000000e4190707004104104d94541980c40d0002011604062800b840c03525000b440c4500b031920880e400c00c407000c040c0c04a028426401852 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661804397 1250 661803147 661803157
    0x1020303040c182d15050d080705030c0319091e230a060c0201080c120705070c0e0c0d050901110301050f060405130e06070201110316020f10230c0a05 66
    0x1c10641e1244000d0100b000014900319020000d442968075a1104c0d00d2101a03540e404815203044248481c01c10281e80c0f0030440091840c0d102441c0f5484445508000341035000704201280303140800207281011102c409144201e84c4600d03100c8a240c80d4441282c10034040440004000307142403040c4c188504c1d001040c80121400a40c44020340078441e0f4004255499032613032200020404542041c821580c0001c1e0141e13004036150100782c00c0850075410614032442c0a002d0005100c1d00082d22001c0c40303c400c0e0304002401d21060610140e0401c4444c40c09a64040300c99440305600d0035022601a08041c05840d031450040c50300307107003164200000c101a5800fa800d01c00e0f4040010000010607440301c08a1500c058480c000c00902c0801d103044c141d04000c4000c0a003821a4034103051140541810002e03280c01900c110482c01d000d080c910010707450b0414400d140121482000b02d207802100c003907044005060f81000c020f2509600003445006803801c00da40c041c10400060100e5a13800703205d000908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661805647 1250 661804397 661804439
    0x19120c030b070e030a06051305012c030c03092205010b040e07110c0f2101060603360f02041e060f0b0415300b06070209040213020c0d0302031501020303040c 69
    0x8454000c90759a001d00b10f90b14134401840c80040c2c450645070082a0f200050b5402158400cd50314240000d0011916407248030440c41c801c89900d0440503009010480545422915503420030035540c403100f0744540b64002e44282c3e400080b0f0a00010311003446103041c0c144000d82c900040100b0f20b54401045a5558800901a003003100c2007188030501000c00c1c0640a00c011640000a01a0070302c8801025200d0b4031000c012201011014410b101d0355614000600700040c0c0d1048036005664605020610110b2a001c0e6105080001035602111894000030428038098030802065a484c01084c98051081c440c4241d01e440c240810001c08102101041076400030385000e421401003034081500d03903001c2031003045007009a1843c00220442d03a201d42e091803c0c04561440c20702055500281120740f00820080c001d8030440800301203101030390140c1c7c0010700e10506544400d16900380c01002500304940c0c0c6a10803102c1c40000e40303a0350000c07084a020716001080a89584e0034403640c0d50021004074482 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661806897 1250 661805647 661805671
    0x1202031e1006030c08060105011107060305090307080414180702030706050a0603120519030605060703051c11090406050a2d030b160e011d19120c030b070e030a0605 72
    0x591040741521809000e944500034825220303040003901c610384030058000b08c0c140311400d41d1440425400042c02000c5850034070b000305450341e0380850242503000c3e60754002c4c40114045000729000390a02e4101402c0c003416610b881011840f43c0394440c42c01019256074000d82c10030031101020440c00d40149600c51b901d904041091a9607565500c10510f009030a50005a00403034100c00c444040101054621080e203802d0048500b00b01c0040d1340d9208200f0000c060040021340d2a1000c0806c4030102114024000e041054001c8281c5d400e4040d440b0119440c4600c0c6080c0f000708183ca0401c43c40d4058644c41c4c243c9402d2203450a070399580da5062144000341c0e241d107481c00040052815206948102c121421316900203803030351030241c010301403080d00d241404a4240000398440740c1d50180041458101c8030400000000b0116906041c49500034403040112a0380c18814890a4900e06044074408c00c1d0421041d50b44c207100316070281564910703d6058000c03101d41c40101d10140c000581002e100f1b095 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661808147 1250 661806897 661806913
    0xb150a0e0303130602160f1203031d011b0c1a04021507121205040f260f04150f05040b030c0c01090302060604201c15030b0f011202031e 60
    0xb49950003580040d90a245185030622465a0600001010040e0f1a03d960845410071920050310142c41c007521804007021107000302450300c40e0300051514101c19005940211440700e0903800380ca24109405000403086607410740d510f110311042d01c0301c182c11902200d0507810082d102203000c1030140c0103a900c5030903d00b40c00e010001440007440c01c144942070200d103880c0c00712006030020745154096080c0501c1c2208000c0800d602c5400d032419180e001c503000c80c903010200c250f100340c660307100f0f0103403110500032900c5200701c04034a000304181c1d002c41070007013003110040404031520b90040f844480000c000344400c00101400310045c1da0004541190354ac10b2001c032401043c2180e9035104150010707408035003031108600b803130302c50080884209022410b525004142000c6184101100a00001c0448c1d5024102107031580c04000003807811142c4840362a502d09100082d0801038405080e0540e940740005950f03100342e01d8242e18a40c3c01303805040300d80c02c8102c01c0710821500030000e00c1c4501642c68 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661809397 1250 661808147 661808149
    0x90b0313030509120a030914010807080a0221061201150b070c18051e070c0f1a0705031006210203070c06060b041404020309061b0c060106090e09010b150a0e 69
    0x11344038011440c90000303203408602424002d00300c11750b5920215841c0c100c01101c2d41142d90040c2c040d43e201c07103242800030711070704c94084050007481080c0741540c4850007a8400d940907003041c400b150203100101d41c42130348064100405800c950b032512a04040c42d110b10420490303486c0d2030b4007410340140241440c0e04410342c1c811495940c100381038902d15803143d0360010014680e4014252910040800c54500f441d881d0607030f0041c100c601a02c2010b0711039840400d1401c1040360902000024010340c094852403803c103039401400c260402d8990b401010000100410814450100050500c1042403119100c0c4081030310203009500c050401c1c01001160130120001c5403460207060014003025034841da40b54540402c10451131150705006114a0040040c09041c031300c001802034009a10000f000d040c0071401020401ca803103007140358101070040900000d000c41d00014440704440121345282e40940d21120740724200d44d0346408681e40484080c2d00208006086401b800407407046041c03640b15410000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661810647 1250 661809397 661809409
    0x11010b0a1701090b01090506101806050c120403050a150908031305031e0c011a130e1c030501060311280c060207060e010606050c030715020d0507021b01090b0313030509 74
    0x1030000c099039507c840c10b100c1141072918100068140504c1d20130781700501250300c80351442d880d20401080141c04507945c40000801e0005007414004802410b649036900d00e000f43d1105a0058150f451003441014031109200500444070b04035804007000340b4555440d2400400821415400e858a10050014132400b00301c400400c81d900c0c5110340e0140d1510b21401c001804e540340c00a0002001d0607807064601186c41d501900035840007511800b054801e001301d5460b00d40301c1c5600403500038003913640d80381c0c1040d80c041e4020b40c181c890a44d02884151803200f40104284903041650141d01c880750208a02c02a00501d0b0740318412040c80c003008803a43c552142400c4e41c003c020140e130400e0307840c00e002041b00c50074814a8018541802c10318100084401e00c00d460f40030388800501b10090446518440c009107504943c201c0010320010000c9003000d400c002d6944000c58040e08004a40d0345014650398040c1184c0301c100c8008030060791659444480803201d011078100700704c080c06014804042150358403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661811897 1250 661810647 661810649
    0x40b220c1106100e07030b010903020f04110d050604051005030a0609170c0f01050105030f07140402130305012043030f080a09030509271611010b0a1701090b01 70
    0x701c03e84120a800c18030350102c800c002418610a042c81c003540d00d00d1590304842c00d44100c0b030f0100c40d0032500f40f04400129000d0401c0e004030544d85130001a8850304070721683c1c4614051002a18100540d035982c1034544404c105901819034181d2104800c0b0340040c604ea0002e80a15215442c136600c0312440303940d141c405801c4481d1340c4031681c01404e811840c07410309100360f43c010401280109091000c00c1003da480c0e0095004043c502003111110030450307100c540480b4591a280000d1071038aa40d82e0915a000b4035694980c0040300901c103801104900c03160003078900c0b0f061001100c11401c20070524201c440c012035040b0281e0701801200440400502d01107025034207001c1d484040300d19499150041882d02c00610b1810444e00d400d912201103a84101518105401a42d0b00600e007248685014a040c0020140a0090300c49100b0854951040702d01600c00482c9a180d810b40343d4041d00172982620302c9021100d0b04070582403010420b80c61a10204401c40380d10000014943c215500c030f0f210801c4003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661813147 1250 661811897 661811911
    0x30b0f13140f010e21070618030c0501050615031306091704030b0708010e1501030e1c090b0702030a0204051803030708060f1909020918100302040b220c1106 69
    0xc0c58910150300004c0c040d00802280000240004042c003401445021181141d400450075011a065040000d40c0d88420005202e444403024600078034500103010080d60715086506508041c085a11800c000364051914080d0105d0241180d440d040e030b04000d0801000b081d038445845018240214810302e081c0101142130f1040f142e41c0d5411030810342c40d0b80d94058560700c20060301c3d06c01008a9045201125000b040c1198030026410304000102c003c0d1865400320b40050060300a0701c0d00519803000c80040c0d8411030b40355580714030382c3e90a2500d985c0c0107441c800b94054210869043c010718207503002603480340120b000210403580c0042d10a1450304119419004550a04c06010851034820301152a0140c111003030018030b0b000c82e042d050040e42611031458001d401150b6400d15a40b01004a04c1088400a04d00c802c0d1511194400c1c0d1194540310681c0101e00d4100032035034034140300715a48110710302403c10350212980d8482c0c500061034501c24060030002603c10b40002c41c4400d10482d402442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661814397 1250 661813147 661813153
    0x15181005040e0a0e0d1106040206030a0b12011a0a03020f04020904062606161b0c080a03080a110f0715060504050a0b1e0f0f0a09050903030a060f030b0f1314 69
    0x404c44c00d0189480207103845107040c801c5c074440f4070b031420000090032a480360b0306550058807511a07602447c0504151810150300c81c3c044001e0420a0380150302c20070010303585541a41e03030f003511407050040c80708081c000690032030100001c7e81e1ba2802d15800030400140c01802c001807456650541c0c1c89a01242000564030603c06800030681c08000c000c800d41104460161402aa082da44090072840f03640005c207648030701d1941c8400030701c075000401d000209201c0d410707a0346104c003d1400800c0b10000300c400c003410514002e00304032200041810307507801c44550501c051070910345031a007610b1203c0081920036583d80300c88010410743c8030b44c000c6600be088201408503440b01207504120700d251250210190507100a48081d0365980e40c20128402c0c6042503c2001881101c1c001007000074840e5007090300e0b407a09043c10700c00c90980000096100b56030391841000810744400108000c50703081e2101401d441c075084c0c08940300b2000300d10304a40240d6002c010204a403820b0791083ca016151003c05d080c150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661815647 1250 661814397 661814411
    0x110c1915050a0915080a0504030c02130e06011406031803090307060507060b010c080f0d0e0a050d0f0207060806040b42091f020a17040515181005040e0a 67
    0x1d030048490405040001030440003c0d81300d02000301961001003002200c42d40762408242854082c0c101c840715550040d1a4140482c0132603800400303002c0000d8181a144101000051840042d002401100710000c180500d107444000d5412074201500d2010062400200310f40c221507a01002104001c144607101c058442c009410b000046074590341d070060500c58038800c0c0200140d0b184088031200313000455842d84480d030041d610802098043d50100b030701d224209025092040010b44200d8010725036030785a005542c1030070100c2c0c039884540b180c44041040c11020910030300d0103410051001c1005488a040a042c2c0041004407240c00c1e01c003980c400c10100207070122207030841551800c40e00c2e107801140c64203100d100801c1c2070904850a480d0100d1052540407441d620910010000580080507900707845488418020558400d102d00d5116000d090001c0309001da151003038501e040321600c01c48440310808402d104805007903100c00304c1080410000800e9036003000b09282d005002d03310001842c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661816897 1250 661815647 661815667
    0x70c14060702100f02070c05041503061a0301110a082a071208220b060d02030a080409180b3c180106030803040f02040b0d03050a02060106110c191505 66
    0x4449008038181d20f14010886d00740070071540000f0701c1c2100d02c103a030300251182e050030104402c1000e90304010102401c0885c2c80c0903100b1503601c103940c110b104034000c11842000d0141c1c080244a44a0b040c4041103048000401c40066601c80b000d5100c4001e8411115116075440c041050340200f204a49100c1004004d603111075010350500e03484403174100c0c1c1c0c8c002101c101d01e4080000380404070043c10b00c2e142d0000140c05843e078818190180e42d0240448071104070502d004402a04180128901c80b8501a400007880b010a4000c030005500304110310f80a0700d03045102c105102c1255544584036900f032610340c144100d08821942c810841c070040d60318508141c500341d440800290b4101060383c0c140141840422081012240c2007170b0b10281c0c004d1041080d101090140c1034440c3c5aa40c070240380d0b5186000e040e000401003091754000d60a840041e0b8a501041d5400200114014100d0b80400a070380b2503400c24a03580c52003000340781d00340c80b4a030344c1da81c02c80b0309018078000c0828009a000b00e00c1c4120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661818147 1250 661816897 661816901
    0x5040305070e1023040f0912020706020a06151d0114060f0702010804050109081617041a1e03160e1012020d02090a1d070f0212181003020913020909070c1406070210 72
    0x24032300161000c0c080c41071800c04021340c0c0b2041640c0c050040f655076940012449155009d203070080120500030606c0c2ca90104c846682da11092107042c40d4400300741034040c080c0c0b4000085172005000e4101c01750508440c0e400446007224010412141c0c1e65803500d1190205d490080900004403001d03e20001c00c11061034605071031039004411414183c1c00344000c1c00848155502c1100122000e902c031500c404c07040c503082e0003e1030b2664050040d0040002444204401a214101d410f6080e44410145003955010b200c4540c070041a0a00040c1082c032007585e6041c0f00790005c14180c11045005401e01c0f4280d0300080c880740b2140d0010507054005040e00c007030700d105406500c2d404035241c1401c001c03101d0034200180d00d039130035a4840303d8502d00000e05902030341d065425000c40d88102504660345074001c9280078000358800080644100d0000030005410b040c980221201044007030020155602c2c0c802041c0d6150f5903581040b10210105080041d070071808010b541c1c4a40e00c103a00800c246081c960031982 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661819397 1250 661818147 661818173
    0x60c1112100b0d05030307030b03100e10050108160b220f0e0f040f0312060b03070e030708030703020c040905190501050601030515030c0108071e05040305070e1023040f09 75
    0x4002ea03c203079416408108040140c03640040c09090120b001d41c40701d000281045071139521040034a24158190454900000f01c038404448000810004c1d40d803660a001da4411890b11892461030b5070b01400e00050718480050541050b0301e281241c110f00040e8948400312840c1d4101e50304440c44404100480b003822401c141e04002203580c0381c40345040c50303281d0300000f035a41e40c0064144005420a8101485164030800c02082ca1040303a944030306021070020240c0140c007030020b200703104600000c28070b0040401100c95540d41038000b01f845035000024030019080003181a103d030f008200141c54400e5180680c480742030301c207400004040c030b0460b00140071070b88081e02c42c035250700c0340202e120426100000e58122002090030040c05594504208440c3e0001d0344581200c0c0e040140700b54050160004064401d480c03181081c2c804540e00e43d5140036942c0c004840015070b9031620101040924480c20380316881e9101200781d2140da00c003940104041e1021018400c01140d51584840180044014001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 661820647 1250 661819397 661819399
    0x30e10030e030403240c030506010807090f05131122120b0106081906080309130c0e0d031205010b0414091b0d0608060705040806010e040507060c1112100b 68
    0xc051181501e0590342ca0245010007002114104001030031111400342d0b0341e000340200f440501500070450320080c00f400c02a40d40030701050400b804582c60701c1c091166203058444107020240c586207002d0070450550404045c1c20230303141e503500503242d21001c070b0380040c18400350b40c810f030066002c0801203241007102c8030f5200c074180c0202c1d003008400007907030111801e044410070710308040d01d6143c2441a5098540c00400209401d1402d00002844074003c0040e25a80d607080741d48459800d00041c030041076498403074800001400140078448146004440078604074001d01d03103c08903800c040c0c6100202c481c00e0304010201400032500f001070001e1390204000851094035050309900f40000402d14500003000c4071105200f02140c100b0f01c61200c0d90004000b0070014048502904102402407c0d960080c00f8000c1b40d4040e650000c9984103403031320481c0c0034580c008000d02e4030514060b403c0710154040c8800b19803850000703498075500e03a07541000c1895507a01340040e011071800c982c901c004480103041c0301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 661821897 1250 661820647 661820651
    0xc0314060c070317070516030801050f09011a130305060a0506040c020f0c0906030c0406090f0c0219081b010c03150f050109092007030203120c030103150b120a030e1003 74
    0x40400039511071307402500c1c1400c80303100b4400342d111250255018051490212203a01c150799481c014107605c0075071035049610a40b400311008001030203000c0b488a0034000c000c07040d05e94113402c1c0d4034080c01c2401024084141c2511200841c0c803a907409080c8001591104c40264850041c4034242c6131620031a103407181e5600082c602c00d16134210356601c4035500b042c5584200d42070382c00144152014000c0c076041d20b40040040008640355115000103104050841e07c04900e45050502e00c6800020351003c0c920b400240c1490740c41096480321902d601262503901c0c00390140b80c03802c1c400c20742401036940341d0f4515200402c00d4881a4111030103003940740d21616a49400d01000c0180389d030481845404e8a40e480004540442c66983d044000700c60028100c11071070300001c44c0700070300d42d0100c050014668001e524000f03d407508500380c400e0f40401c1c0005481d41e0040750ba484035940d00307503011300d80600c405841c032990380c2c640c84081303401c11044020580204144001161080c1380401c0044860441d50030700b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 661823147 1250 661821897 661821907
    0x2a010b090a20120a0903050f0f031021081c06060c050d0801050109031e0203071e05040902010f08100302210606030a0503120a021218010c0c02010219030c0c0314060c 73
    0x503188180c0080c15213580030342c0d108142400d062291045400908081190b01e50394803ca80b4040d80507401100c06c440c03540440c17034001c203041d20074541d1300040c0d001c0c03480501040801900d401d88998041806816210341d05a00407206110600441c0300900c22500c034030880c1c01c95420018100001018084c08100b54080144a40d0380c0111484095980118403c646241004420f05800e04000e030f0207540f51042d0800000c3d03002d003030000e00c6070b4000108000310190781c1c1c901c244000c1c2c0381954402808140f90008040c029446006915130016801c00c000221694940225241001654460300001694040e80c41b072890100119900030009a0043c01d880c0c0403510307540d4980c040c02d9070700701c6122640c00c003003a1044100c1c0c043c2e0b040600c452803440035500b070102c10590001784410400c250b6500b1b20300028506401074410030107194068020384516030720f40b035520b001e43e045d660045060140300121036000c2004c10304030ba00507520402d002c0030365080c011070700c0e0316141004003070044102d41045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 661824397 1250 661823147 661823167
    0x3060a05040506070c020a0305011406010f140414130f0213051c06110408010e0318040515041d030304080901020f0f0d0e010c020d150f022a010b090a20 67
    0x42c1c4643d101c0e24174603018281c1c2c0580d20005040e05120380c005002582810400c000403443e4803902c9005e00b00907251000380c20110071007622544074054121007080c00c03d02041202054155074030251280040507040303105e080107108800c03120034480700702606501045280c0c6546001d941074000d0082240c203422403000300504001c0504641e0002410789031541c030b01d409404102c1040e5009802150000d02569081c00d40f155507a40100060007640c0c40041c9005090f81020f100b070b6030103904503621140034040607070140400740c0b003411440540758611109589903107600b440a0f43c0194842d404059440b90301000082c905100c800c0b02c061039800076664004c00d00c8001503280b14110310741c00e001da103030414140181c80d032110090300070f0b405c10000100075040000441e43d4070700a80703401030308008007600e001c40442280070307403800500f08106c001088681c504103d039030208150f10410022a6900025010400c84001912580986a2641080300c0010307001e00560080c00c28801d119030800740400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 661825647 1250 661824397 661824403
    0x140c040302031c0c020d0312200306190f0909051501060c0f03020a020a06050a03110405030304030b0a0609020c0a030306060f0e0906030f0f030a0909090503090918100b03060a050405 80
    0x10710303540f04004180e0842841640109034420344543c000b030840f6034084007070070041c3c90000c1203a512900149081001001c000301d85040002a01c3c51914141c2140c0c3d9690034800c06c500d1219000004002e003401c0000c041801120807070103080444408110018140380c61464520141c5082c20a104108014810b82d68002031001c941504038000c0d801080751390509034242684509c010b5001f1810840100c0d0298100c0d00034001c464450b038042040b80c281c150703006a40d019502840342e25402c00c0000700081b0f50346100643d00200c40c0c8100281c802d07501c02d081400c07a03101101e000c0740c41d0040c003100401e16425100c0c40c0024001402d100c555128008401003894551043c0184540912000700f006620100b2110b4030400420b0f0449102805105200b603680e000b81c0000c00001e8912075021803d03400a02408160b01e5110b80258207069402c1300f0061882d03c0207003110030701c0010703220301c10303946200b0807038000c074180c00c4030000544d901c14000381804d00c20001c00c66580391341040d0a21000504c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 661826897 1250 661825647 661825663
    0x617010602210405040216050d0c08031b0c01020a020d0f0306030804030b04050f060a020405031b0d0308060118230103050f0a020d15030606060e0d03140724140c04030203 75
    0x103030b03680b802551000500382c80980503a800440d0028408280c6c0c082881080c1d01d561115800380e81259150300c00c0c00301c11981d011006e640104100d4007440810409084040340144481208200c6070030028104039080c22a00104411801640240000a10107030402c0c0e0810f82060140350a200147c25601d070b2002911507484000c007008075050000d01840010f11000c4d5111800000390b51031030502105820203508203000b00d51090084425941c2088889545403880180c0945810901401ea403000e0b40c1e02e200080a4605210744101215040310005562201038603452000003201e003441048500280102e000c680d051519080c1800700c110b40003523020f070780858000c0c405039030350720301d80f1860b405400b9010301c0603e103441fa4007000c010804503400c004191000da41e201c0189060450401c00642e602c02c4003c1c002c81d049211004004921030014002e450088040504004143c956581318415041c4414281d507a01c0c030585c0510305070b0f440c2290304403a0b011a03040c10715084d0b4002941380d01c24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 661828147 1250 661826897 661826923
    0x30706090f1214071205090616021c110f1206090609120f07020d15020f07060509010c1d0f060d1a030c06040603090c050a061d0117040807020301090602130617010602 73
    0x4d000d446240d2948103101301c9058900c050285c03600e5000080c0e181d0b0001c0b09c2128102d11580c07071110810f409003415580c1700842c68002c0000701c3d4514032442031104980003000615002030003641856010711080224a018140d40c20003009540f42200c9540d00345034804d07000906100e410041940848410002d4135007843d0102d030900c0784002c1c9440d0203049080e056104100d0a800840c03101d00b544456030180000714003c0782c040c0055513511080701d0072200d10a4030200420700942d200036214042c50040d003200c0b840904103007c0003003510300250603600086e0010070100d484d1b1288080b506013440c00748214400c19401000c1d00c41c4c03088000f038002d000b94052903040581c3d0344002c03405d028503047c0c1d10004210143c41050900d80301d182c020003c0781000070440c2503400701c3d218a540c1b9440344140020000091084803070359100c96880000f03035488204140c0c1e040d07413520b55800215040744000c0c03140c95013480036500c10924100018003c0f060180c0c08000040d00a0010810703950041000d0340c0c8100c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 661829397 1250 661828147 661828163
    0x90f0316181a060f0d0b0319140606010801180216060f1406060d0f0b0d0803100f03050604031b0501060e012603030c0f0f04080102041809170a02030706090f121407 72
    0x107400201c04010300606c004a649485000804200c401e040001008583d010b049c000791400ca40305102c940d40e07030007561010f000550120040040c03444100c0d02d070754205d00f807800142c07620302c2c090900442d18501000a440450f80d802d0781c1038030000280714880d07541507101292b0350309286c10310005505009030100c09401507151554101002a0f5601884403030070005c05421815840d4280001d154004544030b2002c2c031996240414403400c1d1000b80070840703910000070030b2155101e54045550140740b45040f4400c60484d0b03101780c0010000c1c0600c030003800c06154035003180d40c945071513a0314a1021906000d91450100b0010300700c4100401141e40c4086285266036844104403a42403180c819280544418130010034086006241034000300125091002d009200400300c0100b2021102d05540c01040b160040f903c0c0c142400109001d0036481c46c03a40140da00384039127901c4081c16a030409100311070380c0c0c1108050804001042e5941d40d481400c91038840380c00120b071001682f01d0300c144c1601074402c0e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 661830647 1250 661829397 661829407
    0x1c050d051206011e0806010e090906100501020f0a020d03050708120406051b0301050f010512070305060f01030b18281e06060c0b0901060f120203011d03090f0316181a060f 75
    0x107401401c00b503903100e40227841d2514501c1e140300440d8480b00151040001c4494614001800d50f10024071840802c1000020741018401c40d070070041464051a0101e0034800c0c1031018001080105000d020f03000103010000d40b8903d454a000c908440d4001e101020140161761071310001003a89050b24155030099804ca409034641034016505401080441c514404035442003121443d49904600d000e1201960710040e02000b100065054454010340f098211120a940f03281c0010008032164102c214606d50300c810701c64034008660f060f00725030000c101b083d032222110300b4240d070340c07503541c01d000030034454200072590600b10300038100c000071400900348103c0c0d8400f045038001c080d40300c100200b07a00c10603802a595169000c12000b118103909a12075460005410580482081d04210300c5400101075480c1820302810851b10030034180c0c9050700b40c440c81c5101a09565200e04000c0a08440030090030803200303007003080c403d44014000c240180381041c1071010642d00c4d090700340c5005542c07041400340c4035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 661831897 1250 661830647 661830649
    0x60f090e07090207050d0e0324060f060a030b15042601020c1005010e07020703030203041e0e01030305030f150a0905130b04030807121401051c050d051206011e0806 72
    0x440100d4200d1900c480c4002000b2041010001d54030740103030720070307220807d0548100d800c05880e4240c44949040304010088100b40c08449134038041c0d40903000070101030390a821000460240d410008c1d140011a5032202449041e02e8101c008800804e000c016862401d4181200c12825106d48205241d041ca81800e442408c51400e4041e11082200c100c1200c44010150310b2010240c40203200342c4540d80d0320200070407000b82c404907140c1e05881d011340045203414500486020b50b0345074400b15050221035100c021810b41c8400d00018000c501a640d0145c403810840c604d0711002502605110000c030705403100b42001e454110075002124081000091165521501d00700281c401c21801050103801904110416401c00b41442c050101540c846901e12590501001101c0d131450422252103802c0740100050b14200c80e803404248080fa5440c010245036590742132403d00140a00c0300482d2001c0740e01c00710143caa1083c03079032040f001d1034242c058000b8002c0c44500c2c2d032103021f0118104940480000c181d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 661833147 1250 661831897 661831903
    0x2042a090b03041721100302100f091512090809090619180f15030b090a02012f100e0c010318110a21050d020609100213090905030a02010f060f090e 65
    0x3000c0030b281d940d40101d140500101d006c00c501808101c0c400c80304a04404800c911070143c0e6034100015031510b440c607505005c561440380c0c0c0284202c0c020031900c0c41007420036513003900402c0b035030b00e00c05c0c0040760325500414100203040304010900341c0101d802048415142c040d001c0d83d1011206080030380141600003081070801703001032590303140c4110b04000c650042103d03406c1d81c03402200e00440380e030659900d038800110740b1a861400c01a00240d01d1100c00010400c2c0900d000300d5480c004103120082c0b600000380c09003001d4190b43d100c1c1d10f26070f56840c440500c501c24040d442c2e10b11b10034a020404034524105040072040070b88070142045465201c002000d0b01c0300b280307a2000d0203440100f0402c1081c0c02e0b01d182400100003100325024022107001102560000641e18011821f03000503100072400031040d1802500042491241e9203800b200c000b4105486125901810340602e000d07540e203101407100031742034078020f10ba00301c03000380342000c00c21202c0300030381c41d480c16100c1408000c608a5100f0744113500d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 661834397 1250 661833147 661833187
    0x201120c091a09010801090204150806210d0e1008070e030c1f0908061302120a0b1e100f090b30120c030a05030402042a090b030417 58
    0x9840708420820340380c4140d40c0b101400200d9000da9440030745030780b66000d1900340d008521960102540148906100901030001c003079129401500c0b01c100d0354070b040380012100fa401801003c4075000940ca201c0403e612406000c850b0200361540c01c3c980003070300c000810202009120104008007181001030a6906000401c540e513002801005e24451170710300f03d03100d0704110000c5004100d101c034000034501008a072082c40354402c124000c600480c69000c0c8020f03c1403a03807261407180100b440c51000140b0350b041450007448942e942c4900d41440e0701d0071070624500138000c0401040103500070041041e1185c1d40000360b0f074580c2e8012900301c1902000c034400400408403410403040c481343c10450b2165450100500c01c40321400c0b00e043e19066409000c40744140d00d50f4050503081002400449070140700150340091014000203040031140c41404541034000fa03041c0001055000c404224175070080400016280d2703000d0003440c504040da0760302038440411204005114020554003020900d85410078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 661835647 1250 661834397 661834409
    0x2270103060506040609060806070503060a090509060612010e07061101063201080f01061404031406060108070e0127120f0201080a050420040e030c06150d0201120c09 73
    0x401658403450880c1c0646012030300705000700e181900004c1c010803d4003038035040355803010107400aa00c402908940320f900040032690080c1d6401c8000464410301d20502d031044400401808140c1083c00811003144d10780400b0380f019030306101114445400200e440390444a1700c0c20081070040d9948605805401140d00c602c41d02d402c0b80080c040020428180941140e81307940380d003d04140240c00544020707d081d10008031b81c448070401031003101c6c080c2c0a0101c11500e48440c0714180355903651002880c02903050710711529000710007031281551f040f44c000c80c3c000503a814850000c075803a000007003a101d013803410038080c1c59000c94183d614a00c22040c0c40068100030140d809100100d00b0200f10364a1904802c0f80001c00c1d00d00062038000c4144240d500443d8400188681a111081034400c0507810180c555407060395406070104030380040004100d03040051025240a107001c9100c040400e01030034449008a2107507400000503a444400742070f106842520019072a16426404c45100883d40c001d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 661836897 1250 661835647 661835719
    0xf0f030d0c110d060e0c0103090b130602070b07180503061b0310050a06050a09140a090c020f030a0c15050c0f07170706020d05342309010206070e0d02 66
    0x103542813000d10f401c8541d0401c1081c003251311403880fa000442c122407c198010300080d0303045000c2402034a01c041c19550b55802001c2c09401c4c003407070341c0343d0314a10b45041d500f0b038001c51001d803100c07041c924001996900a003811070140209180c00f03020004803060036140740c0d2402c0c50000c0004d60703040c03031042241c0142c04054400d14219498100250003a8410800345002c40d4440100044602c02c46110580340c180241c0346015407450078981d440034245a0711810254007070800072401c20031041014064030040c81d540c07030314a250307203041c0660f46070a4031000044040c141020099601d094074104c415031200e4007681580c0da102402c0210b1074421280d0b01d1310080b003001680d0001c0c04296000381c02c01e65520b160070455616200c11041c002d0f48101c00c04251030600d00e0307002e0b1403000e54801c155010b5109090095000c802e00413074403011366442d0f040210500001c142001c0d00c0d6410444264080c00b10305001d00064044000110000c850b440024465842c0850054105400c2414241c541c40300c03da030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 661838147 1250 661836897 661836919
    0xb090f0613140117160531092909040f0b040615081912020c0a09091406010b030411041803020105160c0803040602030903041802090f0f030d0c11 64
    0xb44070403100400b4101ca00148018031804c0800c3c0b54009001c0c0100403103911484400c0c0300c4c0c0c0003521150850301ca020282c02106900103401c07643d4014641d0290080052100c1c602e08140ca84000c5846401080c65001d547d900c0310b0175641e00c8110350305007400c000c0f80e035806950340304e141a6a4021020360018044100c60060108007c2540c200e000d2083d050411082195210110f241e03980740a04408801c9440c1001800e010520b80030b030481c0030000781d2041e0380c1b00440e5100460182020341d442403100658950300b0205000c08980c2c403a01c2d40031034502030300da19407401c1d4000e6110700000d440503124040011482c1016590365211600504582c3d02036407841d0340394180a40200f038100d0f050074401048030320404000c2e20510b96807400b15400355075141540c076181c5999009410041040c46984020040400c81d10022000c90321000f0854002694a01c0d45000340021441855442d40c010b00072000c0c1250995004034018103e1902458040708409403804c2c03c5e0010b41225004a401494101d2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 661839397 1250 661838147 661838159
    0xa0f0602030703050c0702060d05040203010b040c0c120f09090c0201060315050f01080f030d0b0301140910060b04030213090f0b01080c04050906090604021c0203060c09040509070b090f0613 83
    0x256206800315101009941d076205a1300c80244a801c800948c400c81c208100c001007101c40d8800380c3c0040c00070b40005a814030303100c080340849800c8030f09103010620130705210080000381c041c071b000304160500e801d841381400800042d00f049601d0040c10b42d040e445920240206100b544503e0003560403000c104c0c440703410341c1c103020010310080d0349940d6070703261400021443d0500000e564043c0445400210b02d000655016040244400d0408035415522a18003801c40480304c804c09005020101c060b009143c0384070404412200305a00030300b02894107000400159643d42e06445100540d0391002c540c003901c80c980401d10103a8000020f02d070076500302c004203880c10009988101480c0c01c0c5c2d0108040e446144085960340b0049419041980c003d0000400500301600708481080114a00300c3c010a0f040c0d00086c24900100c4010700110300100300b1000901c0c040c050b00d9000001c0c82d0250a21034104048545e1510407001000d000741041d0000384402d403a00c8044600119042014200442d1984 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 661840647 1250 661839397 661839401
    0x2010e1e010f1509020c0a0f29040f061a03070303030c021203190b06040e161b02130209060f040b030405061b04050f210715090303020705060c0a0f06 66
    0x180c0385658038040c0c070b81e0b61800e6584543c07001c0d80064664040c0300c41c070345a0b80c0e001951040001d0300391030090141c01000142012210b80090b4483c011125500d13002d210203031101d25062901105001c081410312012944c801103800410303070820008210446000b41c06940318440c596200d4061040c0200002455450b44c0010303460b01c401c0e030a0b54130420020000104902080d034030741d100038120303542995180d41c0c59404041c3c6c3e00405030406060a035940d0005c0c20b100421034000b143d030a0f51144240640e136105007a0f55219000000982c07d00c4107507004280c048401000071803446500050a81440d035030740c070540b24900303a1100400c1d42c4544034040c6c074465800a440c1100c0760301c20f03070000c07070150002521490324684603a185a4141841e00c020440b00e40c10b00215180c10400e040d5601620312281e41030302640b201c1e07480040101602c1d007681c0310038a00030341e0f050703408200c211801800080e41c0424100e00310b034000ca58181d104d0005000c02070401445000003400030701c05020100c1040020b03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 661841897 1250 661840647 661840693
    0x6070e270412180614070212060106050301031e030f0336060c0201052406090a030b10051f231b070603020a3203130b180a080a02010e 59
    0x6549000b2100345070144040c00c40c02501070900401c84150603081005c007840c014002581c001003004040e4006900c0c03403810244285c1141000500020050090200c44036908441d180e0080b01c0c924401402d0300d0041400c0100c0b0714640401d5200c0403403e84083c1d4180c0d50300700d401c414480c0341c0222001e030300000d50210a156411100141803100350402d490042c41034611401e01c08100c40c20003032030240b999107035440484c01164800c0303060200d440c9c07a071511482c3e54091841064001c10324145180010a01c881e1544428440c0c410903628000301180c4400301c180b00d03c214141440f48090008055401c209070341c0e081034080d900803880100003100c5880040d100c0b031303012082c1d49100752940701c210180c1c407640030908003086039106864040341c2c541c1c0201a103200d00e00000b0445804e4a42c40a00584c001d8a89503074410046000c101070103c00f02c2140c0d0072071001900b401c410303141a0a095210004800003404510700411211101d90003900800405c42c2640142e607003100080740050341035900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 661843147 1250 661841897 661841933
    0x708031305030106060c02090711070311011d0f12070e100302120304050105030f0c0c0d0504060e0d05100903050708030f0f1e1f0905190e06070e2704 66
    0x98003100140c1801c041c85504156003241d602c0340b007402d8031502800040f0380060891010851485d841100c01c0200344001c40256208003a101611003490000400c20500d00d41c1603001c000e104421100d503652003041e03035420200190340c60b1001110f0700700464203141040d0701c4a40118443c00c100300001d032945c000001a64802c8400907503003000514855030728020341c0222401b1a504001046182c000c01240c1030b03100401034041ea00e0440420042801c20050200030004100d010070107000c403176082060414001001d960414103811551500b0b5075480d01000140300c0340e540d5040c403100b810b120300121800706411143c600d540317081004084a09c99000c0b03412442100f052030105a1100844400d5448140d400d20714002c10348411000e48034001903d10160f1180b0302d00344000a0300c003028094244a085007070202c0b0407080055500c54181d03021420440790b01c0d00100308009401e9003104c41000c20038015180b0005d082d11100f0320500c003510121108000103101000c01007080840703041071703140c199 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 661844397 1250 661843147 661843177
    0xe18010f0b250f021009180209060d0203040f0b041401050c09010816110a0309090b061c090303060504020c1e0313120501020f0f300a02070f05070803 66
    0xe41c41505400301e000d40607441d54000603020b100c000045a920700301e01c0050103440c580f080060140e001401010310040c40d031000c5121140c0402014594001c4500068101c2030203624114106000810610030700c8960000d19501101081c240070100a000c1e00169220110300f4080c02c3c035050844500d414813442da402d6600305000500440c043c1c106035801c03448180c58079003140d158070808040c00e6003000d000000b000f140c0303c0301c421030a100b003103001b20350b0b0301980700d6240550608061304190788256000b40c3c001c1008100d84a58a9a07070194111002c02c003283c001024800c038a000c8029180951006030b21a00108503440203c0c400f0490320714002411924000d45250000c030305d5280c0c0500c442c211a03428411908110f00b250000a821100780700380c0006141403245801d1320a079400c00103c1d03004410002c1070300c06601228000310640502c00c1c04085075000108540b054203840c0080403000d003140c000c02c40a041042d43c0218001c10b50784041920059034481243d00d60325040025041d440d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 661845647 1250 661844397 661844399
    0xf040b0703050c0601120819020f190203010509430e0a0c0c050c010f03090506010e090d02030408030306010c03030f2f070f08070201050d0c020a0c0803090f100e18010f 74
    0x5042120940030f550108486040a201020300c0c86848e0380d012484007540903d44111805a5050195100700840c1e0b001d001010a4540149400c54070018085145a40a2070154542c815103041100c0d0184a10000100c00c0126400701c0030005050b034900507450004000101d40981186083e034407400040038100b20f2006200340446a180c8420400303022504101000c1c2112f5125250300d210001845c200860ba240980c2e8502c3d2410109901985442c03040200f800b461807001e0100021002052000710304144c1400c0d0040e40303910020341300b9070612030794655003c1014020b0300880d06440f02200c01304540c0c40c590089298512039041300c414030403040d882424200c0030751420f6811564101303035500e105520655515005070b10014050341403040c148513400103d1640d0241c90030484880d40500340c200342524203d1181c3e155500080702a400911512201d615442d1898090000c01c0310040340c1d4156005086d142c0000c400c5109810000500c1e4840a00e40940220781c100c400031a000c501203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 661846897 1250 661845647 661845659
    0x2070e130f020108060f060d060303030c0c0c150e0301090c14180613110a020102040e0703022b022208070504110703050304110d1505100602030702060f040b0703050c0601 75
    0x3000d1a400401001000d52400c0155101300f104980c4500007601611050102e48001105038000b100c0c078004a03612203800380200342e854095074002c3c65981c200080f000c6502d94030091503040601031030b00b102220040108042e48101820601504040c2c0200900403503400e02d004001100d000c0d0940b10401500d201c407650900080003070700c0613110469400d80d52151410008400c00c2c0d000741401d82901c41904070403031840f01d0014500c1c502c2a4000580c0c440c40c0564601e07141000070092070915106122400c0041d40b40c04070709584000e0a4600b007600307408154400c00a00841e8001006002140082c5220481d54138080d42503d8220003124489507880c0204010b40c1c1d00301040082e0101c0a1104000080c040c0c009103800a02c41d035144c60305050100b01183c0e4031040c032a41503c007100301c6a82c06103141c80c14815a508546200040c0140c60304000c8065900c5c0704540009008410001c2c10b104044000230540d07020b050b0003030515503100c0003420014403681000c07031586424082e1070000544 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 661848147 1250 661846897 661846921
    0x3070f1103090d0308090309041107050106092a11030a02010b090a1b121107240b03062205070f0509010b09030c0618040606030e010605060909060d050a0c0602070e 72
    0x1a55009003d0040003502d5542220001405031004c00319200600801500795a03038001c6030070005e1001071107511102e29082c40b030f0944000b0361060b07400c0c0345403000c4d03050485aa00384000b040d9600c02200c102c5d8421410048a016035441c3d80000c2602012074204072041d0f040d0403103429814111401c500d141c4a17071807401d0450700581d000400c40e0700381c83c1802c80c036940102501800c2481102d00010150b4213404c40301419800700104499604610340303240209030407a011104046c4000743d040000d1403081011a41d10000507182d05c82c480c17100d01f400c41905a0350700340d40d2000e952000030b80700101d50703490903000c05001034010240b00d00500000840d071320303405209449075200020020f200442420013070001c1640840140c0f603003002d280a500e501601c4038005d090040c4199a0300061054079490114210b4403603030003140c452a4200000c04890761188280340d08680200c2e0518603413592032810505d07003410030000804c00b05842800044060700803a803d003c80d0800c00000c0c0d90760392a4425864 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 661849397 1250 661848147 661848157
    0x503060105090a350c040c0c0c09020307030c2309130212090c03032104020d0605100303020c06040f09050c120103110405100b1603020708100b0f010203040e040809030a0803070f1103 80
    0x4900d45c00f0000c010038a25060f088264040c9040c2064010b245c1c458640c50303860744654008000c440c3e0004140907005916104451034503641e880c1003a01d048030f000f001d0710001440180c52400c0701012030546613917510203045086400380b60100715552800d1281c1d8101602049a10141600078054001f105007070220885050a01c260700a00c4000c400300e0318a4802c00014101f82d801104c2d8001040001d100d500c20240103443c80c1e52100c00c02c40ca9446d009280524102900d40600f0050008020804010040a0549205000215445e500d102000c5250b024007005200c01701c903c8000002400b0407c0d44581c01d00c202928180b110342d94104007080d580d02203207d1108440420000781d61480d0a4428800d0254440c1c41917884a03075441415501d042c5401100d4407444d665034414407031754503188110340031401d400c0c0082c41c101482e00384600b2070315400410251143d8000103c5540942e010712608803e2a440b50b030032a200d05003410b004090200c0440f100c00491100d107600900d00c05c1c000706440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 661850647 1250 661849397 661849499
    0x304081507110a0609030203120403080411041505040207110d030f030b04090c06030b010905120c180c0901050c030409110702030f010603051b0315010e1f060905010503060105090a 79
    0x840d00c0c85896407480c0c01802207017816003c5004c14420641d07a1a120080c0b203025500a5440000505047c244295401400c0d914540710328600300168030307410054908001144c00841d00140c40d070b403090401104031002c4003111903010804180040c201608850010151400c50b5001c00a1650b040180000c4400c185030280030b400c40d240d010001f0034070a070054084400b040c5845941c01c0d960300c0c08550205001401d4405c01c1d00110103040c50340c20000100e809031410214500c0080c1015681d0b82558030030f21a03400c2c104000010311200844003003044500401504000b0441400e00045504403a00404800c030302c0383c0039082e0030b2168031030140160426a80c200016020300000250b0580200000700d10b400d402d8010103410f0450210400420b600070400010100c0c0d052404800c07181030f00404902070745003242c0840d010700c0259402105c0d001914800c2c28a2996a102c1500603680ca014400740c003603001c4441d4101082840340401d8440d007003a042c80d07c000301146a066841d400c800c13411010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 661851897 1250 661850647 661850653
    0xc01080a0b01170c03011406030f060f1f0207050a270e10050a020c010506010906050406120b09070e0406050d0308060907031b08041e240b03030408150711 68
    0x800c0e00514264008606610141403042c6002c03041d41d5403119032a01103480c0940c5003004401000a540d0f0468258140c42d0122840d525514000000e91040b58000d0f0000340180c04000090b0f1285d00c803800b0400121001d080902400e142886000f95222124007400d4000c440040000030140c00c4401411140352288020a070640502c504040c01454240217405280c4584190b0b6480d1b031b00c13148030b42c0380039518450015a552801c0d071230007030070b461001d0300e010304114030311504010701c0340d100082c1c501340c440b02d2403c02d407446440481d45010f03011401036241c0c090769180c18400c109800c00c5031119891000c1d14103101507681c0c0c0081000603440014085c000c42c1d0000700042c0c26152004405a0007441c034200002c0110721103201d065042503500400d00400c00e04030902080c0040039580002204151880c00c004071620780c1c88802200241c46684140e1141c080b09060780f501035000800440c1000d42203d0b10f0707540d60684940c0d1503154082110311903021402161106100302a0002040a01c0d802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 661853147 1250 661851897 661851901
    0x11040e07090f14010f09050409081e040b0706020a021e15011a040501050c010e0102120f0c03040201051602150a03020414040b10080705091c0b0601020c101d12030a110c0108 76
    0x15240d99032800203c80c04c010790385e40b02187e50f9883d4402e810750140121511500d51b5901c00046458104648921170020800c0c00b042002ca200c1030704407540182e2020015884078105002a0f16001003a4000140c00141000031032100301d0002c0c0120701c14171010190069a40d0350064008c0113103800700c1e00d181440041000f0300c01d65004000030301c10f580d00740c000010221000300409003240c01c0200c00719455051300050025a1603a035800c16000b86900c04a44e26508060713002a001e03201e143c0b4004200d403c410039003400d650b140f50f243c003030a94412190b16035aa03c40d2400400951290144400203664041a040c0310305042c411500f1000d000b0303055420407000c2d060161180d07071006101c9000c00004004601ea1234588102d0b00c03070390145400100c5402009450300a9401c5001002c440c11584101c48640c803965a01b0840c020480950408001c00c440b140390344105d5034203840741142c10507440344501c41d00340e90000c010010450155500540d540e00303806103a03100d48000c00680c2c000341075800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 661854397 1250 661853147 661853149
    0x907080105011407050f0d050702032e0b06120a0506012a06270804030303060e131106090913060506030703030f03022a060906060d200411040e07090f14 67
    0x8020000c080c0240120b503001215241c0c421f01d0500c6440c11200021008030704602141001c201c8900484020001500008001404088031108482c0002002900c03a07901006c5038550b00c2c1102c50f005e514001501e094503050040501801081d03c603940007641c0c601d40030f203482c80c0c03408640d09050b220107001030b02043c00b038485101410542c01c2e039003114903c01c00300701c80c034403602880e4192191040c14025103803869428060215521913022010340c00143c0200802c03510012445142c441d4170500312410304604070046a41401581030b1190000307182c03010b03c001800011003450700c6034802c0320301b4001541e5a0080c5902c0752103911000f0007240351020342030f071240d02980207820401c1c0301e04c10101ca05c0c1800d040102480e8045094421590000390501c074030a542400056404030301503a000d407001c82c1d0360382c4901d0b50080143d1418148101440c5100e030540d62604104007072584d00094545468840140c2c904860b019114440460300100000402c4c0c40078140c40411aa581c0034160301c40300c2804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 661855647 1250 661854397 661854437
    0xd1209031407020a0e0f16030b030a0f05010204080102041805180303070f03180602120109060b2d07051b041e09110303030106030b03100e07031e0501060e06090708010501 75
    0x460b0032070b40078002d400c02181c00c1984401042c800d81c0d04808402e05400d229000c51008041020004200340c21304004020540300028100c03800ca0313100d45004426451820f20b1030080c0690b820030140ca500000300011400040040d400c61400c2051040015443c3d001810014a9088c0801070701c5410920019080174007944503142800a103003008a83c10109421200307008201280c102c545aa002c60780341090340d141909503014140c40b000822a1508000044807580a80d000d0224880f086030740200c1100c0d45404101085021005ca003521040f2510f042a120300004c50203440c003c00540d000c3e056840d0034010300022012070400c0c0c3c640350400440e4100681281c1c0070648030a00e1006d6072060984040000f03500914196a00285581c114000c0509191111000d006582d04004210000150204190040366844041c50390301c0740c001080d10f268001101c50140a65190003000603250300350401d01e81c800c8001702e079125141d644928007a52084003c2c003c203400944440c0024196203454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 661856897 1250 661855647 661855657
    0x111041406160f03030c0e0907020709151502070e0a0c121109030f060619051005031f0303030c1416110612090a02011803081606020903010c020d12090314 68
    0x40b140300e911460107912481c0d1180034041c8100e00080c0d0302e8080100b5a0390119044240e036000b16800c080350709050300000d54504550044d03e01490740d1b10404079490440c502d01d240200440f50145401c2c2c2c640c440041c0d180c0306c0c5841401c01954840c2d00080710000f1038030420000005940b01c002009442814100060039034654141408408000403100750b9400c01c541c210740c074540c20043c0220700d4850280801c07181d40d50807214041100300018005030f5140420b11440b001d1074501030303480e5a500060446d5040c0c0d000c010300183d80f9011004000c0c540d05402203c9aa00c05444000341c84c890030303810070003d2041d64600d80c090304100c1ca110000904c40c0c2ca500f6003000c5c0080c40c2600b40b030159142c0c1c20706580155490f100d690b0201018a0031135030040c0800c140e030844860406803251947d10b0f10540ca2241481c001e01280c1d00340042e4040000030350641e80c0e8503502400802c150507001340080d42e510417480d04180440e45074600345e800c0e40c1107409402c1e20154140d4400c2c910940007844035000d5005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 661858147 1250 661856897 661856917
    0x1e0c0f0f040e1003060f090503190201150806071e0c020112020f0d050604050f10031103070906030302010b0316060e040506060705061311030304031e0f1506080111041406 75
    0x800c00010549a480b4445016140f451002c429192031031a014080782c585103440d10b079482c24010705402141c0701005842c0c40003140306440e254109200000ca004000fa00e10070103d00322a0400032904540004030316220b00259101ea0401440b42c00000c10003140b400c040d20000f5040c6041040154800c0d145a0a9103500c00000b509040c44a01c08a8040c2c0000d00d200754001d0f511070400c0028903040c062260001200400d00c078050500b4020107104003903038000500a44036003a85100301b5141080180000c050091040260f41c2e200d19000f406001e070b542d40c05d40701c1d1191214100c2440354400840045544645a45880b0714100d0140001350030001d214a0388444240420310101d0818000c040c400c1140040522800c005407500e0008002c103003003894001d900900062001817800803803007800e2444000311003c6456503160076001046140c80c020940d10183c0301c0505418005c0e0003130701c19510365200900c0340b14881c490035407841c00b952040c4650103004094451141c204030000380580c4031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 661859397 1250 661858147 661858177
    0x1707061a091303090807080c010201110a1b0c031a07031a010f140403080f1201061404030201110c100f14030f0f220809010801080c10081e0405061e0c0f 67
    0xb03514170215003008800ea021101070b0308504001e80d400d6a0a108100c05480741400340760501e010074000500788000309880c0803245040404200500208144000046a105a134140c00c07003560040003a003200159400d60103e414141c143c01c0e90460802d025905c4807042e07481c0c02e103400c2c011801f2200911141e60650350070000308000b1000c00d0340b85000380b030b603444038481c00c0e42c0c2d99a6034901e0038240074059000f1410401072a4103203030f01165003400c450440781c0910b404070020412402032820591901c420650001c0041c04171303403c07150060b40b01c0300c01843c0b03915980c144603030801e03403844584412201400110840800510a400c1c96509907400044e441c0000061204281040e40c903040705103c01d86008501098000c00d41da803100045014002c0c2da4050403001075060003040103500642c4410060103032810020703a40c00200c0b48001c0c03c8103a0422a44c0141c209403d102c2c2c0c490300c050760786100305070b419501038200c0034069403654010480c29004910380141003031003005540010525040702c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 661860647 1250 661859397 661859399
    0x9060325030c15140408100f020f0d2c070306050c0408030d15050f092418190b0a032604080c01020d02010b0a0b0702040204031707061a09130309 64
    0x100c1000c80c40c00a00f1030204200e000410f04a0041d12544000f0320340407200e001084180b00c0080c1c042120f0140c1005a81d01091806021052201034003a5a004d00c0fa0403001040c0d0310540526900300d801041c140c412000300e00c0410400c00711a500c0000300c00314195000d49401c1001606950226034480c80c0c94a0b0503041a0b103590342c15045901114903d56000d8940d040d040c1c00b031381483c5690b0300074801121512601c0b403c02d030200704a00c1009000d813010881c83d10001b80d000c541c21a440c140600024840714880215160540c0020030030f07114012800c5481d40c007d0328040e402d11440c03a0201e001400d00032100e1545c0d803078510824030300821440159600e10700130b0103644d00d400580040c0400b50040d000909120000903c0e00800c00b160404681c1482c0030b41c0d0083d12a1f00560040e6560801c01541d50300c46800420041e200d5a0310003000301003d84060001500c104c4098a100d9116100c14065100e10101c0d40c540720407115030a6900140700000318801d854030b5131210300624801c3c20105809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 661861897 1250 661860647 661860653
    0x8010522020403120c14031e130306110d060905100302060d0b040c030b09091f09060b030601080109141612050f0d0206060a0b03010e010909020a080a0602180906032503 74
    0x300e041144110100d248150248100040056560421b0600b94000c6040c0300141005c13800c64031190702165240721000071282c0ca05003803811458040c541000061001108280c1d4000c0540e01071201c00000a1406101040da022103018180c0180c007070f11030b1361180358115020000d280d40712880910340680d4515004030b07241c407a8017a4400240b555180003585084c0c0da41400340c503003801405003040307800000344000c95000c1049040301c3c403055240300041400c4a403800c00020142159402e506109000000414400540100102620440741c004520488a200c4c90395211800c6e500c400244807500c0c18410701d03070003000d03030301c2e1150041045800380b9030310410513420112100c14090050b00700c0c408003c000d04241101100030544095060714540c0350a000c4680844107000d80c0000e552100310346d0b011344d134a4580440c06889040c0c10b54112445920300f0780000d500c0f06d8007050b0355041d4400d405080303180c400c500a1045034040d000d0882d1414250314001d180705050344030220f40340c4d518404404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 661863147 1250 661861897 661861913
    0x160b0f2208100605010c0b07031805010213060f0203041805220c0509130b0112030c080c07030611040302010f1404080d020303090f0c150a140a02100b0108010522020403 74
    0x40241e040508041003007500c5110980341e454101c50706100144003940000b5240d5480aa4400c0040c80d002a428010b02d0304022201407504007c0c1c4258004258107110070b2985000d5030442d181b58880c0c29a2114100e01a622805941304400280c85120881c04042c400d94108642c002d50b00b100300090968890601c0208941c100030588a2000e40c40d0180001c0c2848002d064002003038411000105c5115603c00400300014001e54407005402100101014091751074001d106510001a90311490010f03105079807844503120940b041030501d5035000e0f102e6400021201540c0c1c040e5075500000e003540d84281c444100354001030104103820440040d0006050022501c814100e17400346135a81001691a480c0114101c90303c0034903000f035502c4130702a5030703084040c015914401c42c0480e10ba454100042d2020f5800007000380328944d00042c41c0c03120903400301d051495403541c00130401c003030310b103400044407141800d005954002d1515003030101c011824165070440d9003400200903103000d84039034803550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 661864397 1250 661863147 661863149
    0x3051e1e060601080604060f030201050f160f05060a14010e0603070801051e0907060507020d260304062009040213080703030921050a0f020d0221160b0f22 68
    0x6500003100b0311000e0340c0d0040c003d5800103000c0340d0902c281c500304010018103810500c402414000009031148200c89900c0940d461000606c030001c4180c4070340c2c1459220031008a1003143e140c0a01c000148070180d25201c1d0880408035022085150703800e05110248240014140725814400d102c00050b01c1e10090042c14800c1c1400302018100f42051901c0c00d50b1648081d09086040e00450f02c00c1c082c8a034000c00742c40207103030100e400010300f100314240560301002c4840107140754003800000f284681115030056002d14425030040007401c440c00071b050381c8844964a1b00d502e08504000c80d0030145400e4015048011480100000c19992062001d2410340e5540c002c80c0860076044003005500011804a04490300790410991500207a5640c0f80d155040640c005040d00084d40c4504207540743ca192540d01c01d540940a400c031a900001c3c0d0414110402e44100c60a03c5680b4031900128101c642500485d1421940c1c0350030300d003111000c905240c11000280800c4851071245c818212000718100c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 661865647 1250 661864397 661864453
    0x7121104050a2c120a1106280b03060103142d010b01081504021c09031107080706021c140d0f050c0403030804021026090f0703051e 58
    0x55480c0900f10079003081c500d403500c8968480d58440790321083c280042103071414908009811503451840002c00e8590403407070b0440c001e2901c85d100030080d10030043c030200e05a504180c0b005140d81c44000012405882c4070f02c4009401d41c101c840104001440d159108000801c1d54090351f80354030a00446507017118808580314a25030403541c034407104403002c4c410100310460a180402103442e04070f1403001403043c1a00300d00c2c011640000c107807032488808100c141140c1c02c0c2c16014414042241402441001c4422184074a8052400000b812100000c3c0460803100385801921140305141c0c006006c00103404528030038808003010801d0038000314001855040da40c100c00195403504040010103e6500078007542e02c8640c01c010074000310360855401a4410740c1207448032442d8022003421a8030030138082140116940e11008a140303283d5108410b84641022800c844840704409400c1c0d41d00e01042c0304c094501d4004810310040c59490380d040f05525845102128214100f0721680d485602001d5010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 661866897 1250 661865647 661865651
    0xb09120c030d0314090706140313080403120915120f150605030106080c0406140c070f0f0e0603010614100e100801170606030c19051801050111060907121104050a 71
    0x4a0b410044804d1540d8011207140300030004035003032600107485000a50f441500d410804000600311500302c403102c060844e48161080e80b0ba03035503480c050a0100c9403801010114005820100d003214680100900c1c074000b40e0348840c200744e84001c54100030108111000e00c80d64841d00c1507150704651440744170042c0402e59515682c1d602d480750080c00603d02406003812000c00b08800c03c1096800710300c00b89580c071400917840d6203564800b07216250418545c424103011106074000203652001c980c02c1c80440d4907003d0314109c44e42e02c100c105400c941d254000c41002202c00d07100d40c6000e00f06172203040300c4105607089c0100d03081107680015500c044011f0614001680c044014007540c0500b030740842607401c40340018078260500c2000030703031100320680140340901c00c0c1d100000076590210045800500028081e40032668441d242d010403003100740034242c0414081c0400e449030450004145200e05500c80180141908000741c406000b6032a000c15580c10510003e481801d07036461068034080c003460480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 661868147 1250 661866897 661866911
    0x60f04050415051206040c03030503070c12020f150f150a0f240315060503100e011203080123060306010c060e010905190201090e06010504031406070201060902040b09120c030d03 78
    0x10041a07180344a0103184035040b0a05200014484010307c03016250316080c56500c0e9070340c0c40c40458241500c10006001012624058500650040303005142017a20400b910f0b520000c4c90326002441d1001d44900c030030000d40c180054001091a0364140704000024800e01d004c0d5071380e4050080c210700d1a0052900e01a01c0309840400316981100d0483d06581e508050289840b0f80c0d40542a81c040e512608040c0100000052010b0000a1a24015080384207060b940d41d6116005000e4500a25400300c0114000a0012408006c0c41d01400c42188503040030800a0030451305000c2d05405c007602c11414800c116506c0c5001800038000d281c1d03200c444000001d0620300038200f030703480c0c030003042c0c100601c01903401442000360740c1c0214082c043e2491a280d4448a49490004880a124a500103098184610b0760582402404100c00303000710310540c003c0c4022502c0700c0340c0078104d202d03038403450104182c10021900107052000c041c040c41003201c2c003078901404110020909060715081c1180019581d551 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 661869397 1250 661868147 661868149
    0xf11070c091d0a112b170c0a08091f12060512030a03180b07080f01060504180b01030609060b0d11030907210203031c29060f0405041505 60
    0x102e449600308408000e2034404410411031070702c2e0460b82001400403000c000c1c07005603070b4540b000309050020010110900d0900488420241000d00c09030860740c3c83c1884030780840441c1c2c0e4030113a49103110b4540c00b508048119681d11130456001420300c54010300868100e40d04241c90100403081004252583e141341443c0c5030303680080342c400340c010318440c2c2140211804004000026600c2c44143c0d800c00040c4404903040045050801240c000d00182e00c80c010441107903481103015005081d589000c1e1043d90700c919040d1034a01a50040c0c0c203a42840284000c42c81074260003007200c0c10030604000906540b142529019540e45400014021100081c50560403000d0310505c010504144007007411420302920b22616404180f080750104c00018500d9900b803072041c1000c0d812183e00a085130341d40da03040e10f045810700e452924080e60b2140780003503100303984000c10b51b104d42480840c01c00c4030401c0500801c201064110f610f0354810400e0603c400309030341c1c03075500c2866038a00c1010640211149050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 661870503 1106 661869397 661869401
    0xa0503030c07020a140603040204020307051204050c011202070206040e1b16060e0a15020d090c080c1504030507060f1103030a0e07080a080405040f11070c09 69
    0x428071a01c010410010502d00e07100707441003d221a075507101d510590843c4480281c12000c100001801450a980150f90040c072070305046080003048604010f82d00d90842c0d080384d4542c440000c0860a40c3c1208000940f901c3c4140103610f01601035022030039a024510400404913001c80218420759846d1070094058000040402d0f01d9984080b8120f5240c941d0400640300300740f42280f160011140844e04915440c3c0042c040300b210981c0420240080d484441d00c2d0b06031959070780d4008002150b1a40400c0104180f100400e4040e803070108002d9401000c1c0c116040304c0200300410000141c0118941d0112401c5003054114441d03000000e40d0654240c11780d281890100004001400070355034071114600d603404040f241e032240c4a0a1140e0b503014041b034007414084050004000c2440c00e50012201c0848140c00401c0301d24258150040e190414142152821041c0c90103102040d0a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 661690647 661870503 := by
  have h0 := BRFrame.cov_init 661690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 661690647 ≤ n) (h2 : n < 661870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
