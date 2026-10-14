-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3598
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:34.113366+00:00
-- url     : https://prove2.me/submissions/bcd8c403-ea01-453c-ab7a-d52a74691701

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646942446 ≤ n < 647122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646943696 1250 646942446 646942477
    0xb040f0c120b010b030c09012001025404021b0307020118030f03081e2a03010b04090209031501080c090610200f01020d0609050f0c040506090105 64
    0x1040103840c90650000e0307001d540b00680030b07030340d030805030446210464071000040c0e01000104441d46c00745103410100742c155910180342e00d00d6007072498220f0348240181035046410070125503503041c2100c81c55942c40043c1c0700010280181d1955201842103440040030300465585407800e0584441e0306440e00d48c0103904805264601e6428450340340c0d8841c920607400a154035a140003154400c15000e4100e0790b011180d0010300740180c078211500003010301000c041507003a03803900c030450301d00540d01800359400c403054000381a83c800f060000c10362140c0034242100c1c4144010480100c503401a2000c03200c0c1c1100c096918046000064103007003102d800040d225030a5400401da040000516003070008003a03e0380d0070b50380c07106d50401c80755100c01d1002a00251a4011411895901c5885002885000c1c403c0391845840300340041d081e0b03002001c404140030703990071040000a0b078030301843d42c0008020140c13020504081100e802184528011540a203c000580d2841c036442102190042c00c01440072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646944946 1250 646943696 646943699
    0x412050f0f03060a06181a090d1103060106030e0309060a02011805010519020403080306010e0f102d080a0207081204150c030c120906090506130b0702010209010c0b040f0c 75
    0x40c41d0303a0782c005541c143c0c0034881c10400401c3c0c41e40684100c9155004180d20014200d291400305280c50391121034031441d11800f440328914070348a03051341440d1944100c1c01ea80640550301c007031625103a4141c1c0210101414180c0318801d60030088216583c41c202520b03e1039030341c84421402ea015000c00000104190100b003440d1080c8281980164003820702d10501d4a6503c070180001c0040e80200d01000d042c01d0000c10110b0030940c000c00c03100301c1d4100d0281c08081c80d4a8007500241128114040302c4c80498a94418604070080841d110319a004900e0040c04942c251350b03100070720285000f014071249607400541c10003400b482d00306450150400c540006840c0c81d00307151203c0035181d0380d807509400606150040214601a0103100212130780d5584044040d010083d03a98041c3c2104103040d2111650344205000dc100c06000c3c044c400c1150144d60b5000b4811403600d20001507000f801c55046903c140610f82c1c09a0348407500d8083c0c0e80d04400301c00c07595203c60904205818643c4001454403003038150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646946196 1250 646944946 646944967
    0x12090f1501060207050f100305071404060909050903040f260d120b090105010e06090402040b0414090106020d0206040803090f010614040f0203010509280f0209041805060412050f 78
    0x1412810703202c20b0703800e440e92141d4039001e00c810040b140c07045640c440c00b21110040700c1440f95114507072180e0b052400c06144044200b0505566206401190014008040920002c2010b010701c542115403400214a4186002c9024145031094020b128608c0c401c2d0202001a0b13201664010101e801d030700640e84500342829000d882082440c4411003100c0c01c00301078803002e02d0800e00480c100d03101a1a1012101481810004298001504550b000c1e9081c0004940e0805107402340025081000b181c040f0342c0740c02c10800040c0f8005900020441d40007039042c90100350b002c101260080d51222016440e13460300403805052001d616030081e021340c64940d00144414441c154030000c3d140a4504109900451031072005070311007401420f0b004034003a404034416140040c122104081074044c0303c0c80048280419406841c04c045200d00301e01d8000ca0702c0c410301c1c50b02d4410f0b14500a00100032904421942e40c0b11078650078002e001421914401d407185050f64040c1c000c0340c0c0d00c04d03a00c00240c0e940b05030140e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646947446 1250 646946196 646946233
    0x10804141902010912170a120f0f0e0604080405010f090924092a030e061801050703090b040b0403090f1707050a0501140705070e0406090203010e01050c12090f 70
    0x74402c2e0b00151041c07100080e440b0015640c42c150540003030000300a26880085803407158010007404040046461100300d0b00603541c4078020400c0c803007000c0032900c140c2c07922402068130301041580c1c405402c80d070140400103200c0801c645c09ca038000e080c038001e1800070500036240e03802e403580b013401030605081250248021284070041c4040081d1075002e01e031a00d03012800211303a010754105803056400c141e170707041080700000300c8045d020061902255141c0031041c410b00707080003680d10812542070100d552141410038014550310071500d1070100000c10482c2c5400b1041800035101405d00309076003000c80c3c1494400c0c001680a81a40e6600c1c410807a0754400700c00340600c503161415214040e00101181e6464120180d00031980165159280c0c54140907140d1000c2c0d0020b42d040319588240c07400010703460b4003090312522503405480f000490741441c3c0181829100404400300c4164900f20400815030724103029201c1d08450303003401424039507903251172602d080f8908070007141501c60510b0003994020f406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646948696 1250 646947446 646947493
    0x2090f060102010c051306050c01021b0f0d020a1a0901060812070b10060e01081801110a3b0f04050a0227091605160b0106020106050f0f01080414 64
    0xe03030080010004054017100e140c029540305440b6243e00100800c4960702c142e0103030012056500c00149003440040c100c8081455502c140d4072503130008030076031044900600c942078440c49240040c0481071017503503802c402010800ca4031541000c0040116011a41c00d62001011380340c07100c11280b60150f0a0704600e2503401615003124800c455200080700ca0b0840e0ba10304084910503299801c0d510341c020b0040d100c0440080c130218400b48102090340d012042405480a015040307840181d07a0b40c40d0b10340040001c0460381c0320060009182d08021559036401c650b98216801000313007819004a03000001e4400300b10195500d51090404013804104060365000302928203000d12071800c0094005280390b2010141000180d0061030b403000648519007101c042c070740d102c51516007146400b01e0042d40b035107500754050003a90503c442034014044960244180c0c2c01401003183d40c40c03400c5000c0c0000680081014040c1410800b00402080810610190001581060000351220032180c0701c811014802034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646949946 1250 646948696 646948699
    0x250c05070f2d030204020306030a0501150e070f0210020a0207050303030a0b040617061515160b01050d081605160e220302030307080403050409060311100212180a0302090f06 76
    0x40720106030919260203405020a00d03601006402c0364510307020030000b5000101065007500800c910607000680a00c80c24408807085201181510708104540445150042102091100c0d44914800344c41e0000742108250f010384001607550b003403224040b0700b803002076400f10f60544004410700090964640010900c00010340b003c00160f170b99030004001d500305000b800d06480d0131140c040340b1200e0303080d80c810284400180c1696683e01ca010003519513980031515241c501d0300d4954090f410003c648610600405044030400c40441c60340e11030601921800803246501c0070075140041c2002014004214140d0508280c81012903880140e030200c0c80007112a90b0122000312200300705541e5084541401640650081d815660341c2d04040e103243c0c030050000e40a02c5424440050007034030600803580514031030700004104121403810300c480340401d00c010790295040384011090080701c0b078054400c10322101011941c0e6006a8001c542c51800329000603402101300b4082140c0c6500510300c0a005110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646951196 1250 646949946 646949969
    0x3050606240f1c050408030c180909060910060501020d08100509012c0709050d03020709050c04090b03060402010f080a02040803071103150c1603031404210503250c05070f 75
    0x20b0401500700704c3d48202c074001c18920060000c100c0345040391f4050321448030700d04003400c2c4200d1440b000640c880ca049401c181d09902090402c002c9030400d200881d20a80944030512100341404001b079101d080c424405010441540005401d5238401c64800c002040003400d41001561210403288607614012072038000c0d05002222610030644440f0701c175202d5a00b070b5031650445420704082210640c0e400d4015000c610a505010400c0100d910419005851301040d081e5280d10700007040c0c007905c1d08880040d00c2a00400108005030340c020040c4a601302151400c51020354422024000030b00031504550010b21020404104202c41c410021142a10407000c035000740318880d12306540c07940c00b03e50880c10000305200d00010111040300e1912405d02c00d0a01091480c9107030030302c003844030044805031502401f001c40180100300300d201084209030319192451461600b41d54440b0300700303c40301d480c4220034060800c80401034820480300c000c030b40d44001075400303560b0f84565240f00064240908407000b04d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646952446 1250 646951196 646951237
    0x4031a06030f0c0109050f190609050f0a08030315030703080a09060e1e010f200c0901053a020607060501090522080d0b0310021206040603050606240f 66
    0x640000f0764000080c0142e44108400c0e09040500640340780d24102e0540082c819848211a902c5401d82c0c007018145540d104640d09160108014070140e6598102c0e010307000d8a407090028080110840b90f02890074110205890034070000701c0e00c0d103034150f440034000c0350010480c003a40c1a4000600011a0910340d0b030811408221420011400c1c2e00f01da520000c074010710146086540650b11540b031a0b0024241640400619032400100d803c0c0306d845e81c1503d42118100051610f004189a03015040607203140c0021040c51051000d611504d4840e0062440d020343c0310040910460940142541e01606040c2c541e030032032801e04040c100030701880440c1400c080c0007130034048203a041c001c100b44c51651030300d00307404c2d6585615040d503010780c00e03d510103502d90200400d40c0c0c404008820360300d50541d05c01a582c0488400380714040300007808241c4298100002040822400960741380c01c40403c41d842941c281d81c444100040d05203d042d50000d082c0c01280301080074442c00c0280a1011044014820340da = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646953696 1250 646952446 646952473
    0x1a280311070c0e090a17210f0414030c0d0e03073206071e060501051507080d0f0603080406030b0d11040b0d020319151512080904061401030f090506071404031a0603 72
    0x200d03c00c4440b5015121071400040129101c0c40c0c0c200d03000c100b8030041d04ccc0761225528805084c90f0606076a9030110301c0141070004e0b5420200102c0d0f0080c0400d50319451580311005035090800f101c80107114001080b54411300c0103a86200858400340d51049440030141c511590001e26941c2e0303d07105803080c5140c40000529070808040007030304980d000240324517005e03040d40d800000b60490f000078086517644500c0d1220602040c4103040c0514003c40c4082d0b05d41d032070541c0080a6030b41031040d80d4050022150300100044842d111030110050417a4042030452001d00442c0d103050920390701035030602c03c0001d012544650701e400c42c841d0074050090504004514119034003036880c5201507041f80c010f2030744100451720041c0e41101340240300b0690289898031090001e8207031400d40d00300c41003e034442c9040000c15030b01882a1940704516210610080340c05484a64941e00010810743c10300c0600b40b020303080e008020b0100c0d406158011010318484100c10300f086400017044402c540648100880c00d42c65 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646954946 1250 646953696 646953757
    0x215010332030d1d0d020105011502010c1205070c0615090606050705030a030b060c070306050105010e03010e0c041802120304031e0b011a280311070c0e090a17 70
    0x41121460003035103020900010303c0010a03405420621000c241c1d04d035141030120520116002c149954008216541080024000005191109000d42e032414000c591010703000741614080d11148000007c8580d01c4c0f500c1903805641c16400141100c4c074040600c51900b50340104001035441d01d0304d0800c4441e4962009540500c5840300c040e00aa100344492440d07a0721136000360100132805080542041945425245000502d800c01c0b07500c031383c072040103001d65680b00c0e203800710018044009010b002c28002c4000d8686210320000d9000350b4607103a91142c2c6000d003072007995103690301500b41801540360800340d50700c0e82c10601003242c982d0580c0910001c0e40c01040055040071b60030040511580e46010050b014001c0300c1c81150320064000c0c0612414a031101c602da840100440e03400e998900703401e0000404a81f0100b0040b0040d1006229100114641c80061000c2c1c81d05003051006d60746848a80380d2502c0682c0b100100541d0100205040160b0550003804040544040c02a4040020700c01c4a01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646956196 1250 646954946 646955033
    0x1050604030305121806090109021005040b0d0b040b061c05070c15020c120d0504030e09160c020303130803040e1b0a0305040309051f230301060f02150103 68
    0x1400070700001e44946180c1351440d030800e41c1c0552002494a03d00469401d01c0001c40b00e00185954540f5010150b0800c40307458041840a0315085151900300300011040f4000d48024814003a42e5000e04162038540ea40014001c62008145d991a42186c00c400c00d419102215200e4003a0304020109000390b001e182000d203030603440300c02e40d51500b003c0d1982000070f400500101140d84120100d5400c0400200000c000f10003003103402243c0362a160a028001001d401d00703c0340203501d0303102044248156101141240821890442d0007002a400041e1442c020780d8040420304090030b00000b4042320010080003114a400d031003003e103036100000c0700074180f40180c5a041031401080a420041d105c6e40c065580240711f420520805a12840881e04008501010803409408070602a54039034008070040030500301980c450891003d2612510994001032180c581403264848004d501e43d0f000341300f110103244100010103240c0d0f070f49041c6122070725080c182d94060304111500504602c1202a4803ca = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646957446 1250 646956196 646956203
    0x19080f0606180c0f04030c0320300607030c020d0513051005071a0910050603070b0304020a0e090601060f020c03060f090a05060c0c07150c0305071e05010c080105060403 74
    0x42c0b180c4210380207189010700051401c8032000301040307014455140c0c000940007460081048080c4c0c03508620740b80c0186003407400f0070860902c1c00b44401c205175455280c120000352451032403610303075100100c00070398100c1890030107d9540106c504104102c0d078954040c0354041c03019800c403440380c140300c002a85d0a2260340320310350200d08940018022414074030000404c41c0058034001c0c1c039001070b0782c642c9119140188114000c00c040700050140e54181000480e5801c2c404030303810052800c007030000a50f1180f09100d40d0b52011008400502555283e0240c100144141c01202105180c00400c650701c0341da00b40036101c089140784130002400c500c00a141e0b0170740080540201115242c1c10400100080014a0460030348625001c02000070002d1203040e008011068202d034454020340c107002d0071b1400d15080314100c100804000d0b001c0d0340d80100d0b0030712032541504006070350721000e0908003005082c082c03615070002c204903001001c0100c150300c040b110085c1555003003810790b210700412003a44590311025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646958696 1250 646957446 646957459
    0xb0a050f1608070e100314070e0a090902150d1b03020a02421504020309030a030905011404080a0314010602100f090203070f0e0c0702010f0c0501060519080f0606 71
    0x10041c015190b503038100629080501070410030344001550010844020700000b500c030003a504d101d10a50241a81003001e504001c0c0940b00e862020803401d000b10f03c1050143c13502c0d6001c200c29500c8031002c850220200707030b000ca0b076540204030303c181c09400000da03030200c00c240040c000c41d80702d031091081e03406400403036000e44100b01c08840c440c0e01038030ba4030310381d8000d40000d0002c0e0040707401c444441c0081c01d44911003080d0755240080c403c1e84c0c01c41c09494418025401002000301c0354002004903165138400703050000700407900e030500c640102103804491451030346140522051000240207402803178269642409810404020001008420b101301030141e4441000d07000c2c420401d800c011a20001c03c00c0002d08004150006481d01c581076000c10114140c041d000d101c40c1e070340b0f4236450703034441030f00044a0301e801d1540d80000c0c0b1220343c02d24a0010401c80214103010800b0a40200004180040c852213580c48409451528001188524400d1b4490045440c4801c140400e656128480081a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646959946 1250 646958696 646958731
    0xa050a0305060f1210061208031b0903060708011e0f06050c030d0609050601020708070b0d050901140403030b01020d110c0d0c1a070b0c13090b0409020d0b0a050f 71
    0x290050480503010580c001c404050f04000b0b600c41c1400d801d5a007501c13030010141c00c03014400c902d00f1507180c0d03082000310541c00440100400c00d803001303c90700007040f0807400304018900009041d59010340741c0425858007980701448411070b40102454161075049841c1d11801060086660303a11040e8424015411886602040000d000c2c00c050801c0912105c10f60780340c02d003c25041e20489510384c11140b50260f5980034001c3c6540c0c100021800742490f10010f021481c20008594004d00600d00781e0014641c6600001c2c01a04080d002440c11f6104070b80c4003090741c2000d10740a400342c20400c00681c014428909014221031144c1c1e101a4101d070300708060300004e00d09000b4048000c074900003e030f80b2106181000204801d105003a11101c203540b62246442c1c0406152680400d98081e1003130b9600383c0180f15800c440180c0803200c00840700c100c1030010b12523914401180c00751440c0080a940201c60000540510544805003481410340040404c241d6441e0204290b946106840900c140700450300e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646961196 1250 646959946 646959967
    0x308041829100509090a1b1701050d0c050306070c02090c04062102160c080d14090d060b0d030507260a08100e0406090b0105100c080306060702060301030503120a020a05 74
    0x1c001402c4807241c54000c0c076100d0840d010900c0d01e071094030a101d54943d5400000d55111099800000c1c0100718504441d082c80c490100c0b905059045c01118440d51140c603045003082154a003441c0142005825516036103040c1ca40500380383c0f003c0000742d01030000180020000c03100002101d0940c1e0181d180d22003800c600c4610320108145294140402546c2008034252500d5100810301903140f20b00d840380700c1d003400e004d140360511000c4042e110911608085506c54024240d040d02c625440c1a10203410b29152401c214002d80346981c01f0070b80150544e00903505140e400380003880c4240c090034034500c452002c40c85042c0d64085003980410982c07001d1002070140c5104100a9030403d101400d20f100c483d071601049103600304182c400700d03010f030b41d030309941030804c250900002d006002c116200d141020180780050300c0300c031000e9401045103c000000641c950b60f0f40090381c3d0250b4000d8542612503850f40b0307089540350b00c09502c164205a9000c0050b043c000e5500840d00c0103009a5202810000c1002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646962446 1250 646961196 646961209
    0x7140f07020d020d081b03130302090702010603120c0c050a060801031b0b04120201030e060c03160201021b071d070c02040507050d110d0e2b02070308041829 69
    0x290220781c84040b404040340540c0d138420000e8841030060100544e520041d5401c15074042034005003901383d03001070082455145400d040303803089036010b640e515201d80c0e50131002c900400507904010103040984010700e80c019405501041b5103031240b080c40c0480e60711101004050f007618483c000009416400500000d01109000d21100092000849603243c0360768106000b0340041e00007044c01c422810800055613818011b000110780c1c448098840b900344074101c0240d5100041030742224002d06062240740e90300c00d504607030704038113550301d0000c8404405140a032101d03001c1c0b244141031130b4420344410038410302000640c00703046192505048100c1f65070078000030b0840206a0001c0c003606101002ca0140a0f00030440000190741025aa072244820054202c90003a1902c00305540072200200500741c0c00c0110300403109a01061854a001040d422485e10340c042c2c00050903450041000914400441441110100c4148040c00584492203e500000070780070424290f2000d48401c0c2601800c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646963696 1250 646962446 646962457
    0xa1104020f070807030c030e060702091611070b0d140f1b071e060f141305010902060a02101a030a110105160506010320060729190507140f 61
    0x41d444141002481d84036072183e03410000e403c0d404542251200c6007050b030312904039019030a00311001b5060541e00e03004280c2d0300000510000000c0c2031510280e106900a030004102c429400d42102d10f02030b100d00344203600390011100b5808090800007021140100c004465105e0300f80e902545443e695905c0c1d902590b8030f0314120913043d85030200f18000115440344096407012401c2c10000c4480d2450340b07090800c494002058440c610300e04807201030040d8008403100d82000c0240036911411401d41801030042c10b00d850001e6110f5030004042c0180703074000c924a102d158548004001c4449010201144810203041d0558180c000804c1c19000a0b100010b21424400c1890090304121514080f0804425200303020385440d4080c800400800c540b44a0122000888007182220401c0301e0010962900400d50007d01c400382c0d03185460b06c44401215207003800c0c400241103600e00d0800800c0b04181c0b0300603000d00811030f402e010004902d140103101041d84140d044210701d2034255607000d480080e8112 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646964946 1250 646963696 646963717
    0x1002010207210309060c050304050d02060112140321070201050108010603020f0402030a1b0c020306091917090315010311011e1d0301021305010206011212030f02121510020a110402 79
    0x1c2e200440c0105905d849601d14079101e42d02c3d010303076904060400e030b450b2002e840c41c800d085600240c0144104c540342d0464034240c550081e5020410130340d400c001415800350302c0c0405410605804036030403112442d2880303402a030054008110316620390042c1403c3e0f03502408042d401020b4904030b9403641c1059801160b01c464850400202c20b01d408d00a0500180c900018800160f01d0042c00000d40c0b406100340350304050608003e0003904010800c0002c0c0c41103c0307202030000781190344c0e019500203020040320010500181981c40042c0c4880160b640d0f41801c3c041610704c2c8200381c0b4003204075405000e01e04607440101d0155004200e80b010300300c4446554020488a02c0681c0381d000515440074005815100d14210f802130125041c6400280307030a20585c0502075070340c80705100e100401d40030126011070711110314000c140c08000600e4680a4814090b00055881d8203804024204c0c0c2040c500c01b0020404a03a0200101000d040807a40c452901358058590941d0f4003c03222540703415170049c9100d001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646966196 1250 646964946 646964951
    0x3090f05060a0819050f100e100323010c090f060305040506240d060542010504031b06031d03030f04050c0907050a0e04020f03070c0201120e030910020102072103 71
    0x8401c80c40340c0955000780c070030b2034056521b10140541040c3d00303540000039200b407969a20251808800b02c0040303055900c00948006007050400d001c8940418000340e2154144000707200c001c5890380014500601c9101d000300030910300034085805482406820b00581d0000002d01071500d07041802c0b0b038407800342c0d85075000c00d400a0203400c0b20b0303468500141400501446002a5501e8000e0320100c1d0311742a90100c40210420010b2002c09900812a04101400c82840100c00301403d100603550303481a0307000035004100f4031000d9010b11030640e161906650155900303108000ca807001540c0000c041100b6400700d1740007400019445c0034107501d4a9485800340b0202c1d80309110360340110300c02080595030000001e0f000100b4002c00b54004074002d00c04042035504610304240f0022000c514000680380508100d800c00c440000d40e07107d815064614143c1800811091301c60004140e07890303102d0072010b4082e2625074604a01240184261081107420500017500c150030901c10311282c0f1030b400758001c140765 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646967446 1250 646966196 646966231
    0x1806050a0f0c080411010206010513020c030d06081011040b070b0402030c210d0519080601020c040e01200408190501090b012d0602030901180801020d020703090f05060a08 75
    0x307018010710807264060303200d490701030525007407508903026a10b03d084c0c1558032104c0100440d48074a0112610150204801030f213030740c000c8002a04502ca800034401e2150706000000c2120000414400c00e4502e039018100114042800c6412041c080c1c2d1207154107441e0140b21002c041142c1c00c0b01c0b60b80c810b1004050b50768040d69000001e60420454040281c46000c108000c05120010840344a4007a0203080c500d080034411605402c840140070040d50030803200c000400e941d64000c1041c040e0b0f00348000c0c0107201d200c00e03410f0040c0c000d140e84c60900302d10f007800755042c602d04900701044400b680d076a00301401440304c81c0d074400f565010002004940740d41d43e5019410121f0008003030385010303100d0321040786000c514030607441800e03e080140c890981c9510303103010404c40381c0010480300010130a0808644030240c5040342000e04000da030083c0c04e90b5000182080100ea800da004200442c800c1d2662079116440d0801c082c013883d002e004554000c0700403c5a607840601490409074400d07100c0710000b0611 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646968696 1250 646967446 646967471
    0x6071404051306030b010801110a0302070f050d0503070324051c150203070807180302010311040f150305011a03011a0906070b0703050a090b0619031b181806050a 71
    0x550300020b00c006400c2e51002c00340204004500c00b1401420300e44028840c0b0704d146e9840101511800800c038041c9a400644c690421010002c2e50b03c032a074100301510221031070007101806651048825400003032800d5845480c0c0320403c40072400001004a0890b40c81c4e0621007808907120011881005030fa646029410014403030314a411580b20041c400075803030b070030404800b41200c4009090300040c8158040e080c030b103658901ca82d43d02204d80918001c1821045104214014480c40d001300007102c4110b800440c0c4242c000050f90f200707d40e180c0d0f042040380c0e603e00032a81d852806604240170b1100400c0104082000500b00c14025580308114626011030500010040d51044400312041a00c1c90304102d02e00390035205240d8003894001c8103100692055032503c500f40b070010081441220200b10042e042c3e070054910401441d8892032203043c5079060720921861681c1071241c01d1078036441010044002c1d0a6020f890351000200d6000c0c101c040965a0388405000001c100d040c1c1d117643c500751403200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646969946 1250 646968696 646968709
    0x1f081609090c17010b070b1302011b082a0c01090501120b01210b150c0316050a08160b010803070b010b0d0e030406180b031e070c0204050133020607140405 68
    0x70220039105c030f941c5040600e00103a1158004100c00b1090415a50660142c0d8000e041c01c400c03606c40d400091400c0c0b96501d09000360b070240440807000210b020001d01111404506049051072544c003c17542c0c0130300035200442d0280464096640040d0400c1e0f101260242c080c3c010144c8010141010b10b03a0800401942544402c3e10340c210000c1b035140c1480b2521800c280c51007000c000b44440d0303903500e03048c0821a00da980e8495060800001c4040c1c650b0182482803d020007078030f840e404108a507559503401784003030310b020b60110144c40c443c0c0b401c0d00000f9184000001c1707604656100ca5003146a0b07203807a00f014140e800003011145240d44468030794044400c01d100520240c072680e103840000b2842c0d5017101c0d441e129150060244070b0410403e00640c90701800a0b60789060004d0000300003540c0724a011140b001c0303000c0340290000c1c10200040b03003211400088403840d11200c04100003001c07114402d0784101d023029200d00056001800820307409403060410204c1c0e83e076544034052400d6610004180c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646971196 1250 646969946 646969949
    0x105070c0813120b04060509010c05091215090616020d0c02220906050a2022091b14031b0c0721052b05181f081609090c1701 55
    0x80c0c03483c0d01c13003c00041046500c9001d410400c004002c04c000c10064602404a10510400c1c510030f5035034049803100000200160b000c0010100c4a115240c2000c07101c0f00c1c0e584070203840d240d10360455449001442403001a00c2410310300e4540d1040001115a006c0c402c13544060903541008904103161007a54950030f0083c001c2c0799105c1d0500081034507203031403041c04840d00e0791449105a000f80350030b40380703e0000d101036032150481c1c0e8171442c20b0244940c1101c00410a1944005051420b081d0950700001441c4420250007117142c481c0140e440030026525800d00c4101c841580712203920f0400988416480b018120b810200800c81e41030b1034079110305102d401c2c09031034a11124480c5400031401c000040c00001000078080d500c2c12180115113944051002003e2440b00411a000c600b080c040c41c03d0b41010750b10703100094040f0300003002d04012407401030207040a100c04142c1c5140460311b1008002d800349081056540c81c042c1140c01c0c041d00324094001d01a4810411240030304031007010f1034480c3e00a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646972446 1250 646971196 646971203
    0x305070203010c08061e1e0604050d32030711221a01080118090201030902220506030705060405010c06060f060906090b0f0712020f070609050307080105070c081312 72
    0x10034070300842040825010800c420003019080169017240d47c43d9032000c1c40310550001011246062220042009801164002c070390001c0840c01080c02e00c9610603070b8001407018a40101c1800a5200c0100c0c41607282e01c542c2c0d51194020010700303000c906100c40883c01d0324001002001d541084c500302d0000a011504000d0000390344120300c0c1c10100c84c40c2d00040c0d44413801c0c2007840f0103600d0300442c941403108000b4040fa100380c94224a004686c840d80c0050320b1558000c0480300c0100b00c1e010a103202c104000300c0e5090062a00000c503280f880c00107014412600000d2034a45400d08081c01110b030420381d000115023040d00c8000c082107502c03c0f241c1041c0600350702d5654581c100d2400100504d50000d551040080c90010800311902d07020540481e840c071600018109191484920308030310f0440c90350740c03114807809003042c04206550b101d0920f5007107030070840444850a48030310302c80d0300320b03070083d101000815035000c3c410001a4000b405000200702403404ad494096940d0b00d0f08202c6d50901c503048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646973696 1250 646972446 646972457
    0x906080102040e090109050703330212060a0b03070c110d0807021c030c11011106011814160c140105070201020901030f05330307030818060a12090305070203010c 71
    0xa000404183e0941c0c0c0c0d2182c03440c40280088a8540c44607500c0d24a540005400ea100d9050f440148040c20310310915130700d402c43c1440d00004000ca444c00000c1d0455000b0400c0c80b2007030b10110320340e4a04881580c041d14165a03400d840c64a5070007080e0f40580000380100c42503100603440281540d51303a007000c0744007400780d00a44c1d510752507441000403500e6181081071040c00905200d00201e0f07405081d03202e80c1580101c001501080050040c1c0310200e1001159500d0300c5104008184a41d20700c00680f200541d52078284910944411310000c0d0000440728409000c220100400c0032a100325404024180903000506803d000320020500b0349600301c0e41c40c40940e400291402c0340d0350703051143c2d038a0462968020001418411440034a003a014545034802e00c8508100e012524000000301c086464002c0880f4003040d90f07842c0c40748503a088200038041501c101e002812427800c0110454195500555411600e51031043d9a50000c1010000c140c0402605126001c0103071001d00c1000585c1181e40c645 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646974946 1250 646973696 646973699
    0x304035f0307141c050f09030d0f020702091501020c040c050d231e0f04050d0e06130f08121e07060b04021c0507030615030b120d05071a0106091806090608010204 71
    0x4401c01d480c0045c020841d90b04043c0b08207d10510088191a644c584110300414403208042010001c1c0c0200b54019501802180601103004084601c8518a46080c0c09480c140c1c41c100c01000215040d1102e80404540100011468189142d0080c40004014000c04038104141c0710200d8984a0841c2c5001c1360300c8040114140c51520814500e60000350206071001c070386040e51301c4903150b19106440000384280c4102120096580109440d440b9120841a01c1c1d9182da41140d0066120144100c02541c081d404500d0070f40800307402251100c1030080c107862303410607644800700341d147c5c08518165220342e91902c94400594030340c0024401e44a04429a0044611406048044410190036801450301e8402d04200c0050030300e00e0103180700a14100000d840c80b41c01d01007200840b200719085440c0c080c0300a07151440760001d024160b003e000d086030cc125600390203640f00c6058001e000340008581545001c0040618011440503205800f680c04100241ea030300501091300d005420103102c036500401e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646976196 1250 646974946 646974997
    0x4030b040c2103320307050904050a0b0f090405100204140f0d0c0612060b0c0a0507080a08070210170c041404090f02060304035f030714 60
    0x2c01c1003078861030007214242a003a5005000c096000c3c21010801005a0300390680100c1a50f1802140d04542e49441d40c0c0e251a602c01003c5610501a143c49a481c00307003c100410241c4c4901c4805840140804130084035001c104480303018001d10441e06842100080f00180300c0701e002820040c4000030301100c04a4941d0700f000045030400c101640681419035020010500c0c1d00075800440d051070804030031034103101442901a0509402c0285e01450010356086588400192422441d0056007a0340d8800d454100b400d4450b845518003801c0100248800c1d005803401440403810f1041034241010500fa01d030340c03040c01d2120100c40000c0080e9000c00d0400c82d4114120714080d810030125010011280d02d50384e01d0301083d1100c4000b0303014080c00320016041500030200c114142c00840c0b0303401321003492102c1d004041c0e4224070314160f09510040046266512a005055041d21604800c0e1200c07000040551803d400003410082044900c901e000e0405100074010419400d0a1500705420b404290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646977446 1250 646976196 646976219
    0x50319060f030b07020f102f0304030e0d0506011e08060403020a02011e08010909080c0a061506030e0312060a0f0b0c010510050114070201030f0f020702040b0303270604030b040c 78
    0x10404e40640d0000c00300e641d41ca540108203803c02d60150800004c0d002101c146103044000000c008000711203440c1201e00c3c252158502442c031640c0b0964620860003201000d0000020321140010069031080c40107000c9021500905045800400941843c040e50f88660b0b515002017a24140d0150708058149003d5503400300d500d019800555078030300340f949008030703004220000509c41e40d00d803d40d41d406d0040801c00347c24111245614500e04440d8400306a0426000900b510340c040d401005d9081070025065000b8001e605680c1084000b03103007405010b43ca11880c040c4010700c10f5910485403440412180c0d02040c25501410a00c10000e45511401c041103085420103014201540034041007042a0380e401006090180b0aa0034015107501d0302c1d10069003d40341e8002000102401e004607030310003a80396030107040c40038002c4900b0b114407103041d003d0503102e1017540303050440d1307000d1088045288001040d981c1c0901c000900001d1070566291508181040c1c1a80c0803641c0c07a103240310420540c030310f11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646978696 1250 646977446 646977451
    0x7140d0b0a0e010f05010503150c04080303090706092106020904090501050c090a050f030705240d1b08070e041e0203090d02070806061f020a020d080901090f030c06050319060f030b 79
    0x4c0070108002d505284c0040ea40c5d070a20038041900401400004407151000b1050310020b20300c101c100c03926403d00f550b4150300d07080540070b104002032011000059004050440d84010780c40c08004102d40d001179180c0304060341c03082c400182c01c6034075010041e001407824410a40306100e2120115210714a000c100500300c401e550110344a0940c5000b24110766801280c01000c1b16000c9890040320000f440300c48914101c20078036801103210101d0700d403500c0045a00700003c00035800d8112042c0c4d40e45c3d040c09072002c650648a000010311303004d943c84400c0c1011781c007110b8550f03040c9404c1c041101c01040f4520599000702d86040d111b400c60403030702c15642e80400c40c4070090810300004c0c103020720701030000c541200a240503100509500c2d003040e11005000f130000c0340d1702d01e4001e07101428040150405004a0b4001082c503400650303110000a14040c802d140d9a042c0e0350b0100c610840d003890000c2c1102c0315000034200d4040c00a000c3c8400104044501c200002045510691110b03185142000c17501000e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646979946 1250 646978696 646978721
    0x1903060f0e063607030503092d240301230a080307020405060406030b0a05010f0510050d02090613150305010e070e0907140a0e0306130507140d0b0a0e01 67
    0x1c0042c88908121050403003421406a441840f841e03c42581150310344014440144040c011004040300340403002c0018a204141030760319084d82000b03009c200b2204103038404045100c545000ea00155450303c1071186042803554071107600d0645650000211961080c0d11030308100107114485881d00140c44600710490780b044981c1041180340010580e180d105070a0300911541d901e00000d016660751b03074001005160001c0321025949024202c1800400c009e0040008002c505400055545484080c2212890b0380303594240c1000d81125251019400070541254000010702103d04180c00c58880f11000340b9100c808070b180304000c04005002c03134006800c403045401505040000c1c1a8010300112100130f070940d0110317981c2e0b031140c5044a103500ca001d001d130100b42c0300141076208542e011540c159205030840035107000791650024100d601a031b40200820640010408000d132032150440314a80d0038000d44000ca0307841c2c880ea0b801100e48400c0340c828518640d60400c045046009200c3c10256024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646981196 1250 646979946 646979953
    0x60d06060914120709091505040b04060e0f070501141905040614071122051f050a0f060807020106050a030b04050d09141e191706010e01050d021903060f0e 68
    0x31251042a12440240243d40189482d070f04003404111111800c100c8004082401f04094240b50ae05041004025101a0358807402d00c4489211918003003000174544059900a0191915100c015110000d0880000c40c00030414030403403003500c40c0a100380a4141c0550303100703503450b4140000035000a03c0306035400b203100d005000c0312001035003040880a0a010440b02c03110744840b220845c4260200c0c1611115031b850828041c41140c400440007049210824018101815100c2007449a4001144910040005034803402c00c1800d019122280c1c1142441c8004980329846c2c6020071806072556208480c1180e2110800080c00014008044185180c0c902964098500304446e9140e200210501e84181c010b0034080c1450003800b0281c0155a5024180c001c08400030a08444400c28030320848084100ea4030f10b10200741c40210b6214143d071464100200316900300014880d0341540418100e81080300702403529507082c04100440c004511406001c1940350f6442040c00944e400044c80040c65070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646982446 1250 646981196 646981219
    0x2070e180a0f02040b190f05030c130c09030f1217130b1f0b0904061a1905040503010e0f0f030903061515040e0108010b06030103020d11060d06060914 66
    0x40c8081400c810341c5410160b089807545560001070000c004240d0303071552044a841c0101000c404208540c02164100f0384c03000d584035134503003c1c961190310089c1d0041e1300a202c0010300c00746a2aa901c071a9200340c1c145000c40302240c0300d50b034058010040e03403010b503100c400d08404a450990300c1311540b0179601c40541c03e925213080c484020040000007840040000c04c1481c0021000c50382100300f00c09800035110040c541035500c0d8a031500e1a417040a1140c01241059404684800b561031031a085452800031185002e00350306890b03610b4400c0d985550300b000400c10000500b668240220160045040080c0c020020080c149501d407a14085200c0026082800750781e803d41da0204050350f003d035144413051290305050703000a080200b0070942850084006c1004640305051508880c103940001d0002c2160441d50410442039000920009500c1b2941c843c0703201c002000d4108600d5159000b50080c4c4c2805850160325081d220144c20100004030304050070003142c40c4040812001040a03105e890808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646983696 1250 646982446 646982491
    0x8010c0507350a081014030a03080414030409020c100b0d0818090c19020d120509100204030f06060501030612080a140d09150e0309060a090b0316030f0507050d180605040302070e 78
    0x9008d840d0001e028040c04100040600c01503c11940c440f800c900b0907250b03142e842e400d00b1802908482c1844c81244106c10b41156080d500d4424005001d00081000502010701c1e0342c0c12065502c91003880748142035010100d0500c0d112021803900840c00c0200090300c45042ca13030f00c0941000440c0c92039085512001d0400ca101d504841207201c1c9050020010507556140100baa1070700105803504040c0354070000d0300100740042d010b80b550105e4810742d41480386a036614011000c0d514503004180580204810503000101c1400003060010781a04040d013806281440000464002d0020341c00307142c4d01c82e80c90b1410082d2620341056505800c4004100582400e0251030741ea004041c1d269008120000d25401f80e6405a101d01e4020800300329055a20b113060100e010b0103070094030f00380f8003090400555110200140c011035100b500642c1d2060304140304605054041c100090f25091441d2400c028500810402d006075807180303000703800030b0599074900140484008401410100422050f0442c108031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646984946 1250 646983696 646983703
    0xd1a0603010c080a02090409140105180d050421060912140f0322060507050d060501020d0e010e06040b0309011a01020703050a0b040204060801021308010c0507350a08101403 76
    0x204044130720060b152642c800110b0000c00102e20b01514040340c80046130710901c01504160701c18514401d044030881c2c0201500f80e510f02519294201188013840103006483e11098110310404410b005a000403500741c4440c81142c0910b4420b03101028540580a070b510782041c420700e258490541550b00e40046000015203500011300b001c04e050290381a42400d03030104056a0345042e0308000e00b0099400c1c9000058403540c84107025640241c20070600180315800403409449041660312041044809c8200449241156403034650707102d02c0500c004100050041c000d944901c1c410b00001507440c2c055800900390000071903c031070442d030002e501800041e0001c200462281d0b4403100f0b400c2c90b61140d10002c4c024003d16001894150b02c04151241c00b01c5404440c4402c88030103800821a204030b030801100e1510403001d01a04c40703440810f1401c0c0c11040b21500407400344a0304110001710302e000c4180c0c2105d60010038510b002032081424420410400c29903240240307a40740c0e40e40d54000b8040c001c0307903e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646986196 1250 646984946 646984951
    0x708120a1d03250203070e1609060e0612090708070b071a010803040e040f020d202407050304030606061d031c03020903070e33030a02120c0d1a0603010c08 68
    0x120010480d0b10f81103450130421032024191000074484d0b00d240040b030f0074881103c4102800c0c000b40c0030030b200154242c01041100d460030b2001e400f41e40f03040440356414100c518054140d4007030b481a0308000840e220288030007000f800301210269550001410321310103481c01c4080d49810030b807000e0b004000e0154004104c9003100c800418802d85e650301c4d810200048403071780c1400b94001c042e01e580281005050204441611068510000031041c3d44050142649544400c806c03045200c0c28545814180c1401900034030f81f103041102d20307068a0341d035103405560845d80328901061201c0280d03801111400b28000883c8003d500802070555040c03101b40c403082d00c2c11198810b0560008688119413014800d850240a00344004d800c10305002c100c407204100032258803159280403804140d560000e0700001a852100180113207002c0c0740319002c00c014200f2482c4202400d1190220320740c80c0361140c420200120b4007440c0d51010030680314a044142d00340080c070700b40c401e03490103520800b2940c11000d0b040c2c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646987446 1250 646986196 646986247
    0x50405010f030b0403090b0f040608070c0201200a021003020a08180307170c010c02061506030402100f0203040801051303140304120e030a05060f04030f020615060708120a1d03 77
    0x260b507a10389060590305505550041e003054000048e50740c540b00c600000400c11541d0b140d0f507818566483d00001c840003000441d0083c00180760300340030800e25462800409840c81200142ca0308101c1d1503002031103c07041382d00118003080d000718100320117982011400307520805d08142100e808038441c100b2500c0740715407a0020424603a92540140c2001c0e4082981e00c081a420008c005c0c00e0107a80d03000e0754500089a03035611080c1010140c42150508034241c0c4c4c0140e42c050a070120310040c50509407075054010700c19004611042c440041c84030000d010315405500c6171103083e0000500360400600400d140b01e04860720030310030010304c0006016140140b000d40130600e40310507502600d40c00603061040d90a00034000344141014085000510302c2094016403207070b10b40e803d95604014060745c42e580129000c5841c000d04a011110b1400c041c00180001482100550311301050044e108042d00800d0f24081200c03966400100e130313420b2030700f601c2e0b50341e400800e002582000344018490301200158101607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646988696 1250 646987446 646987463
    0x6020d080a11070b010305060c1c02030603010207050714091e06040c020304120303061805010b0a0c020607020a080307030f051305151303033b100c0215070606050405010f03 76
    0x52940500d40d202c858007410109400c0e54641d418205021151020301003640d85000e81c0012550450f22a000c8480e000c4184000700603050241240c01c0003504020701864055400f007003031000084c03050100c24007030200401c0500b00c1140e05414040c1d21080104086440019a41340c1300014101c100382541c481d100f2235001c215006820707002c03403c1d4003480c0d10958042030032030307011001c041c0c05400000903140c910500030060a10b0040c8002030342d100f03100d181c42c00c9804010f0030700428030451030051a079001500480c41e141e91940811a020490b6000300500d820200c1c4003401c065014041030181c01162034028207002e15990215502d144a1054921440311050742044082c0702000761800d072280d4039203c115855a80c10050402d59440142445007402d0014001c01c2100b12044c03002c1c40c1c0d20f0284903071140c0490b00c0c14000b0100d540c42c400c070b00740100c0200c40d01c016a08c43e41948100c040c1d0b07184040e01e0b00040c1c50700d0000c1c0c40494207d240303d00e00303090041c00a10519908403044070b0300115030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646989946 1250 646988696 646988701
    0x412031a0d261b01090c030209100810020a030e0c0901140103090507120c060f02122206021b040e031905160c03030e010c0213051b1602010305010602030406020d08 72
    0x41002101d41c0100c0c0c20540e004070620515200700c05015102000f092a0300b82032502002020a0890f1510341c00140301d40450a400e00c00f504200c51220342c89081c2480e850800d40c0c581e602185020388031048210034a07000190441001d9141c043d00100300086002016814038030b00c0081c400c031805018001800c03a211410343c007260f1194005c1c24505030040d081d501c0c015160b0f2840d941e0340040c4041580e080c540c0c040e0005500c0c0c411880d40c00c1ba840158040c1c40880071013400e03e4000c2d80047d02000c0c14860842418500e41e8221103018010400e640060801c41c025015600b86036210b0078000d8072652038006451104039020040b640080c4000441001a414400064070240a400c1241c070700b403885082c10008001100c0022010340340179842d200313141c02c0301d03100444d100881414000d420102012901e032900080b6003150350130162003109603000010303403a00340756141c0112007541d0642180c1d035110f01c15940c162040c6805070610744041e51030941490800380d43c0383d402c2c054032010021001e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646991196 1250 646989946 646989953
    0xc06240d020405150603010f08070b0703080c07111002070e0c090a0312030e0604110102010f020405061c020408010903030501170f1f110307020f2b180506120412031a0d 74
    0x207100e0200e004c014109926540c480001040c00e100d507005804071441a00d07030100d07032480050182d8a426901d60b5034000c41343d440b45c0a100d50380e00003010031246070000c0c400744581950380040b4a030907481c0c01e9000b418030a1900c010409244005030a00480b20f01c00c100020450320352102a10650b600b00c10090f018195522003140201000141c8403042e002c1e07602807004000c4000003d20007080241e0007440901103844103d0700300e104620501da4003480421030540c5129842c4000080c082c00c140005003080d548a07101401d55050120480010703984400501402492075024101020744000900c907035400d0242c1c0e680c2e100900660b0b114121400f090400400d205c603005080511006030049031603003014400651354030f40c0c0c072080040e90f0050440b0801c071010341d00c0c003964500c5070000403006403ca007160103441e44060342503010508a0849000b280a44030400100842580c3c5180c0320a07070701d0141000280f60a001c2c1200f0105403c0c0002d031080c51006200c6001240400c0707078002e02940aa25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646992446 1250 646991196 646991221
    0x40b0304020f03010e0607021501121511040803130b040609061b0609110f011409580305030a022506050105101b03030b01050409020c06240d020405 65
    0x841c400da056007080091759141c240441c01c80c1c011030711502113400d4404a00441f0701c1c144400d0003402e0008400c0c00b090404690741e1141602c625090010019203c840c0f001c1e801e507180d00c940c1040d2420b91001692001c0c04008003210340042815000140c2814241440180030019500c1100c040080000b04011800101c001d05100317107a200d48100009605490480c403a401c2641c4201d220708170307402818529501400f0b03000101c00c3d50404c294038284c1c40c903040041d506520040c5001c1041b420f007681d200822800c0344000310f030a070040c101240c0a03100420027050380c0011041c840c29403001013600006030300300d800c0d603030009000c08026890701c4000071403421108010246503050443c0380c03082024844154031041c140e8205892084030051442026101c0079104000c00b91404d0080c2040400719110354420081404141343c0726180036903030555001647c01c001c1d280c2e9026081201404803003100622100c028504d801f180c1ca01010384c4ca800140348000845001c2e01484d1a440001d41000102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646993696 1250 646992446 646992469
    0x17090607261305031b1e01140126011515052d0c011401170102040302090a0b010e060f0c010c0e01020d142101080609030702030628020304140c0103060b040b030402 72
    0x1e00100098015244100e46da01084030140007040d010203008003049106000d044441c7d81c0c4c0c040d10400f640d1034a00303803190407552a13000d0404407035a40d111110f8421b0a00412840c11070701010161070f18184102c0700380740c004140c8400140b04082205540081c44000340c0440c0030b40010720181c074081d0404e2070040910400f070340600d25500c0d0503851920681034a002a050b903219460652495031450f0304117080380702c1ea0102a60002c071400005a204816401c42c1c12640d03418903040311244404808607540da0400b51100664810205a0281c156424400e1842400c0c10f0302d08808500d980000207034607034540a01c070008010000741520100552041114859041c0741c0c3c10f000c10060100c40d012031540280200c40e03090043c4004a4007005d000420f0350540c42c3c0050140119848002818101300301028254246070085903200c0415000352000d035105a000d10f8290141d070b800c0314070980c142030000c0300f8107040c50b01d060070a018005410b01a00c042e1012589560b5403a2941c0c000201c10003640c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646994946 1250 646993696 646993717
    0x10020a17031e011e05090106020714120703050615010e18071e050a030e0a0812040f020d230708250305010e0106080d0309050d0c031709060726130503 66
    0x102c0c00042c0a03810700094186014443d070f24425069151810407240da0800c0c0f0031500180d00112080c0503641c0403c41a001d05540104031300064201c00310b03080e081a2440c1d109640c950000c1080010380101002140248035003480c00b00c00c03224401c03000a201c50142074410103900d51220020b8426400303220b4141300440c4995040c0a04101c00d5030080c02d551100381803000107401d0076410003082200040c5641e449c0d51105007181840240d85902c5100c07c3d008100365142c821089600300541c441642910085000758070a412070010b0000d07803d000c05551001010652040c10200401c01c008208900c02d000c503e05840d007402c0381c4034220b902a4280c0c0d00b02074865440c0c42400d40c0789410550080040707502c2841a24105a01048150101d0728041d038050f06d540c005c8600c504102c4d12441c46102c0c0c07a4820f00b4541e1b02c4441c2d403008200c0c4804125040482075110a0a00c032034507810410f000749190318001d00d00c00a103000429510000e2014000710850581000042e04009040c03042e560140039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646996196 1250 646994946 646995001
    0x20103021210050a06020111040611031207030f11090d1e080c0a060501050d080d050406110712080901091e0201020307120503070e0f010507020f19060e10020a1703 72
    0x40800042c1590002441880c1c450342519000150302e42c010700a1200c2c80700441c1c2c1240c101803401c0303802e480318031501c0c42c0d0b00c02500040254030142441c2c240e006000d01002d58000450714052004441143c201d04e10500e070701c40080c840610355981e1071500070700d10795101041e802c1c0102a4819450040500e03400142095004500e0a410400028114040fa40100030620459980d07206000c290360340003202030024a410069002a0000c43e006980c00510a803400240b034941420031042a030802c800c212010b41c0720840817101e06600c6031403190400d42e510000c02000a01356242a041d003543e18010540c1801d580e00d400035a8020304c25034400b41e40002c210311030200d201c1802445039008480890229040004105503410302d104843c6002030107840c1c2c0d074074040071902081400d4070003030805079101c156002c01890b01c581603034042e0001c01082e22004075840001042049940545407a4400c643c0b2000008010807520344030308a4ec0d991160b10503940e900c490038200340b0111000410340e135401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646997446 1250 646996196 646996201
    0x90911130e12090a0509090a0f030509120c0a0803091c020a15050c0d080709090b0409021909050f040b070c080903011d0c2d0409120c020a09050c070803040201030212 73
    0x900b4000500500004454203000307680c4400070880000c4041d58181c4a80d488013000100041842503c0c008107406824014140511040020440c04192070221991340040101050a00b070008100d00507100d200065810020041c002c5945520034407110107840c000741002409640b9580c480c080a4800e62046141c01d21404a028000360700c4042e00405910828002d203026600c240c02c01030203803141c3d41e10040020b00d01030705030001d42040c02180e0b901a681d5440680165103c003001c2c9410102c400300301c000d9a00d4041c0b40021584020b0000c80c20312080d600b04400642204451944420113040c07a81842e1001c0c01c02c0c51090144210b1a90158605642d50701039214001117107104465600840c0e040c600e00e141408190740c0a6103900807503019140709001e007405402800c0c04200ca0103031001600303c815440e11607e40c5030740c402c110082501d1602002c150300b0300c00840b401510901d101400141030000291306d030341c4910100600580c41c044003040440e0b02c01d070100d581ea10280da001c040c560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646998696 1250 646997446 646997473
    0x615080d210c031d0307020108060108181e071703070305340611090904140f0312070f1107060e040e010507080a1505030c1311040605040807090911130e 67
    0x24110000c0c0c00e80044c541c49410900d28000008441c03c007541a0340d000d0f640e848100055442c868090b1604561080d080b820005502040101c41c620b5600340b41c0410a00e641600f0440c18070005410103600521954039010600780c001040340c00b1140c0c58680596644400004407281e42504919000c6604441c49070704881d842603142084014080ea500b040070646030b807041c1d0003034821031480c10b411008480c000303800700e03220184841c0203d001609540c2c2818610215504543c045241d0700c1410036000c060221456111400c01405072250501200c0b03ca1a450000e5640c0520f2040034100b00300410f08005640b695000745980c0000c81000380094102910050115182121900c5d941803404c0240041c0310040384100f4111903010300500b642c114405c05101c640d12480707001c0001c1e103803540f168043c7c043e940002030005148650b0380e039440c0c40c14259010b041001e15400b503215181810400808203640340e42282c03003208220742c0c00c0c44442c10804d00720090901250102c40c60700690803a0b8811 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646999946 1250 646998696 646998701
    0x70809031c0305161d060d020a030203010e010e1306050c040518091203010f050d060213080a03080a050403080a020a020106030204061401110118031107150c0615080d210c03 76
    0x200c4429860a03c025581d0780c0384003902600340518600050109904045c1c40f10340034400d060048000341c0b44130320b00500003486038280c2e80140c0c0103e001a030f00000401c808100600818003414030301100540c01d0802801080002e620fa807009003200b507030303503001c5065a00031004450050070003a0a110000010316140007151204445107104d6001e091100340750381c140030303044074182c620558281c5002c60500050051a01144004075400c9508016000034980810001c00003840700000600440b040ea19005002c47c0c2c01614414060b410101407200103030300094040d038000050a0016241c2c0f011000482c0944141e80c80070b50401d10f0701c480416402403c100c4038001003400e0b250149551004c080c2c0030b00721609004800449a9a1402003000920480c4001199a845411a4080e81d101c015690303020903c802c5078008201406075040c00c03c041409110044119409048080e0703291034a0152220780c4205071004202a40c5200b244100c9a00c008040da408814810401800342c032001400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647001196 1250 646999946 646999993
    0x60f15100801090b04110d11040b0f28050313031701090b040e03040807120f1506060305060d11011407052d0a0c140a0905160f02010b0306010b07080903 67
    0x11113003007840e0310b44281031900884100400e12420949000051843d10000b0711002124010500c800c200005101c010a4040c200c002144246d05548100b01c08940101e5411140f0940300c1201d4040d00c443d8042e04001035a61020305007141f0440761303507617203400c844407044920302c0d5405090441c00448d046803d0b1340281c0441d941034800704812000b803002e40361342340214400c00c9029407008200303000300d65480d642d61100707512a01c5981002e039810b695071141001d1b007440f01c02940396030741002c00003541d05000b80f1350410416140f072903518481d901c1322a1171004901031207050002d00a44039555401c0e09040301c00391a00b100984690721080281c680711403441150214034040178101c003c2a80102040f8109540d910a115600b4140760160301a0003c40d45400a030b40402c00a000040c480500d0045074882c19a811000c507540f6601c030300c003401034132020095408580c50001410140d031400510141540e84984c07641c0e071114514a440e4a01c2c1c8641c081c520b801d4000d040510007c2d003400c640001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647002446 1250 647001196 647001209
    0x10305160302034207021b0d02010e011e110c090c1606090812040606150c020f0f030f1e0d1b060609180b0a0c02060f15100801 56
    0x806031648012044018481400060f5041e0040c0450811280420320083c0c00d940318508000e0b841d01d0205031342c44100d00396440341c800c2d41ca07000d410800d200340e06100c5c4840c01101014410042100c0801065030349045240c000e05120a046070407115a02030b01c2078442e14800752601e0030b00d4810180008200c013002208250041c0b18998500ea1603180c900d00151280c8010700d40182040d100e81920940b5041b0032009443e0b05a5503880c00002c0380200300140130419101104800c079080514015046840d99440304120380343d81805460361651001584001d681c0440f004003183d0035810000b0840d10890030030550511600c40f01c1c8864580100300a14154805001c0c0c0024100180b4503580321000c0c0110240003c1a098100c419648881d44208840b400740000151990700d603841c8108464111060072684041107211400300f00c00300054a48c00b1103400018810084480320295a84502170b04d10b540c41d8880500040202e20300f40c044100c0618001c0014600c40c1116102402154080c020700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647003696 1250 647002446 647002453
    0x4060e22060906090e03071209150f0f170106140d050a090201080f04030e0d1a0106032013030b132913030c0b100b07050c12070b090f010504030f0308010305 69
    0x11004900e100d0301c5c2e41c25a4280203940380130300b141d03649142003407204045403e0100c10314021840e1801030040044103640c94640e5540350180103c041c00e5800010b68180421000502d20701243ca080401941100d10a04000d5600620310003091614090420089000c0e80703000108100403000390003c0100707078000c0c0c0320085582c40b5024400001c0d50101e40c041c010401188004481d8180600b4140034240911010b654202c0c0700381e0301c0401b8040a90100e80000c0d191a20101e441ca07807540350503045000c05480ca4584485007445080c04242441b000e061002c0c0c440c00198990041e80b04000c026130711881c0900030310b0b802d502d44101c81d140310411300c4c4030480340320000340040142c12408103415010340740e6644c0300c1c055941b101544140100450b0400b46030000001c0d0310035401000d00502072044c8058840b000404041c44085c1d0507195003911160711580d42001044140021600e802a0540381314491401d400010380e03661084d0f0340001c00c070031440d514032018194000b850606980c03090059 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647004946 1250 647003696 647003699
    0x906160e011407060f140c18040207050102070506090d020304030b130f0c080303041b0506030f0703020c120306150301050d060c0302071a0f0906070e0108040501060503030f131a04060e22060906 85
    0x5070715001c10480347c0600000701002420303c0d451070006480800b10f00100091707d0906607913542404e80e0040c0c40111240e031f00981c18001c03044014411801941d02a10046050525503150303070807503040251103640400d00d4a055282130102407084201156041520110b4261f42c4607130325070340c1e0b80c400c96080d02c9980790544558007030b081d0382c2075030350440303600800c9181183c40d98400e05a4150b00505074105041d420484042c1402c2e0610003c3c000c108e8111100340c0300c1c07401740d06000c084803009003000c1c5004002c2005204030303500c6000000300c5a41103400040c04043c9000203500a2260803405401aa4030f0211440c5004100300418440c0403480d165118a8450710400e03907448009480900120f0305030321002015510840050741d0041c015000071030065650400b090071035000100d0031140441c0091103042c2c500d0100803440c01046030300804e080c00218041300710450b00407400390108002c220000a01903656102454401c090700c0c091145444002560303180062210f44542103040c1d062080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647006196 1250 647004946 647004971
    0x8060f0307032a0b180a030510020901021c0c033516020703021e03030d1103070219170d14010f0812040f03060b0a09050901020a080906160e011407060f 67
    0x3d030040f500380140700c0341003e20607004101003d012002c01508020205000008a1020081c8002011609200580c1c2d0751040000a0800100381141e549048080c0c0b010208180c2c0302011010040d0149040074000c2184041041c2549145100c03088041e0f02854559808140d0748a45006003003d462901740012841410303612024184006544840c4090300da281054492080e00d0013920024150303407410503000f0b075240c01c44081c508041b9411b079011003044407a030780402215100f4115104001400302e50390f0703142440450660080e2240d00804921050044130070303084050003105060400e0385540c0c507540748a0448200d8442c030f02891154840c2d40d000d40e03110908a40179a0442c0020058050850720740c10301a1000e045100c1d0002d1801300d000482c0d101c680301d042d01401000c800580d480d0050b40004019920203401111540c02031030030710855101100000342a00390504180a2500c1c0010060300e0100084030000c2201c9400100c800030040b00340c0c00103280b20902c134020031800d01c0a18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647007446 1250 647006196 647006273
    0xc0e070c051b030a08040f170f0a0602071a0f0603060109020c0601050f030c03060711010b011b021207081f050702280f0c031b080309060a08060f030703 67
    0x400601242c00c003040700285900030303a28840d40550301804880109201c0e50314a202e5500c40d0b480003002d91700d518800e00000c1150703030124071003014400c000c0040d0a0071088080e04c0314005031000744015070008481007000171200d0a41050054030403100329501c0c2501500380005000c4442e203209006400000c10004500e200f6101464010401801c1680c20702013401a070003941c0800c25890711810301300181d180e40800004d4803501e03d0b030b80c6401c1401c004000320340c2940c0389582620705200780c0d111a05074440e01203d05d0011181c048403540a0f844681c4085030401580d50043d4420380103100b00f800310101000090aa40107401b030040106559101080746c659444c240070040d40300d4210542e00780782c11807218032500c59000c0d0a024081103403a82d25000440051362045030100420518138130180e000e089400014001c82010754541035104002030090310404443c1814080d461002c12041d4a4111840c5110300c400340488200720b449043c1300d40602042c4400c000540100d6200040110b0100c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647008696 1250 647007446 647007467
    0x60e0111030a020a020d052d0f120f030a0902040c0201151217180406031103060a0b0f060d022203140c010203031602010b03010c080a0b040e03030f0702030c0a0c0e07 73
    0x10350241010446039400c000840c8259101070350315115400718201c1400e804280344c1c00344007050f108c080d49000c44a41540c10240007003000c0d11281c1180501002d200f069008a801444070303a60302d6907032943c1d0818410700a20240d00069045843e0032040d0992300d40550001c4492086040703400002662505007100300401c80d05c000b809001c4070036100c0b009030445e1001d807420b8211140e0004001220320082811150141d00680d040381c015905168181020b00c1130503044824180e06110b2100c1c0100401c03881030f1601c0c00d207405044009004068841644e040d1418241d0000040c2e0b0700c48221550002034012034002074442c2140d9555040701090006140c101060043c0c002e10b0031a5645020900110310750751001c02955241c1400340404c0c0c1d420300c50403c50344000d0700c441070301d414280519000c55080352015400780780380070380801468000006070b85e030040c810b4a0710380c101c0d612404101e0541c09810b40a11040c49005031010420081aa00c1c0c4141c1e080103c0f42c0440c0d950b95241100e454504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647009946 1250 647008696 647008717
    0x20730020108090712030903020405010e2406071a0108011103040308070c1707200f010203040b160b0a0603110d0f062a0801050a0515030f040303060f060e011103 71
    0x2410440040d40a40c0e5083d6111030780d042a503640b10364800f180c0014640802040340040c80c0500300703004600c1d0601c24070303000d000004036840c5d2a14180c07402c0c1c030305030009520304224218488429030850756148119040c03658800380300321041015584a2581c4003080c06402e110394201180c110f040c40c608020b803441550036507a4001d0b162180f210680b0301c009420000d8071481818101d9090a56403100201015841030011344100c001c0000c25504607040d491900c0c0c41000e07001c0c000361650307a00005440998100340022950b500f840c001d0000d05500100004040301c0b020740c200094060b082d07103c401228091083c240d105a40c400c100101454440c1004025000c010410346c0800c040d80d001c0d00b1068240b002024080b0392400688108040301045400003d00c41401031100b0304048503040c000300b000785c50480c0460700641e00c4002600005002c00e0501101c040040c4c281446a000200100b2007041c00703502c490f4850000606040d801600d26010aa102103e500000c80020440b03031400300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647011196 1250 647009946 647010029
    0x305150405090322050904050c0f0910180e06071106010504020901050403110a170a140c0307061d06070b0708180705040c05090301020a0305010330050714010c0207 72
    0x10628080741c6003814064030152154031302c80d00410a42c481d000354a002d640904000c00d8030808000401c601010b002011500500c400b50910070030b1905c108205080d60008080c00741d40760741d0464420010103514030312280303901c40c903802d000065030001103c00d60148004107031440c90780c0b81c205002c182c2c4070b030464140c0003ea0401c0100f01041101003401014080185001003659644107052448010200300030036a800002c4100304124682c2a0f50303500304982c0c8007070014240b00000290b01c0301c2c4184a004140000940e11602141607841c019101d0f04004111686a00e5242002000c0381d004803103000108141d0004030b150010900f60800c0b84030743e084000c14030700341040c0c02d01c8043d0007600003c070700380034013448aa08680e8003070001d8801c0c00784a90b400101d85d80341d400c08814855002d001d000f041c3e00700c1c0a502074100c00192201030600e4150800d62382d640b0041c6441a41a1030021484100d540b0380000c1c1e01d1b10f2a0302155003400c4549400a240346682d4100400f080780c2503850240c2c14841 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647012446 1250 647011196 647011207
    0x5090907030218090a0e01181101050306010207030503042903060a140406030605011202030705060a02071a070503070c09060609050906210f030a120504120e03070f0603051504050903 80
    0x501c25001020104480b1403074050550602000c51100700b03041ea0080100c0341c9039143c1c441030781c1c0c0c2440f8403800d500800c18039200c034001a860324203840d8a00007030b031030410000100040b140d0740200f1040008680c4401200d9540b692080c203012042e041c8001c0b03a040420603180d446840300b050040d240604801062a12600d192809042d8182040401d191b0456200c042c00004500f4600c00c1900801c00c245540c86407092174810181008003030f41006200c1d18045c0050f85502d0b0380017591001b500c104225207402d50603500041c945074011608020316502c40025280d003081071050547d070845140c1d09050111588503a8141d660540d94016650440507840000e42070b41b80049951050300d0340c06c0c0507981480d0100c480030303041031110300d41800c8035480000c2c0b209209512441c1c0178400903c04c08204414102a41e826802880c02081d00c800c01c49500300600155a05018103401046111401140d480d0b603102c02401905048500880d6001f020451703204d00d0a00b409114862803000000c1d500c0d21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647013696 1250 647012446 647012461
    0x1c390e0f0601210c030b030304140406090203040b010317250b0903270616080705060c09060d02090f040e0d200d080c040f300b0c0c0f060c030610050909 67
    0x28142c2020f04410180ca4550b00903050b00d00344024405083c092542042b50700f0303020305100c01e0341c1840e800400c00b244100701304000303d503030329820606407580240b081a81c1240c1005180c8107004c0d00150220010000e003001e503114101c203010b884218072a81506226698201e42283c490080c80d40820500e48110003080c2c1100c0560302407030780404014011400c04072001010301500441c1e81c01101d40c2d0900240326001e208081002c00c0e0300091aa03151440e00b1161000f148650051540a00200da00402c004142c2c0e40d90540710788064802070810040e002241c0c070345568441070f080b41080428187c0400c0180349152000015041000c10300500b148100340d84c0c125180c0700001e08440464009000201d0360004403402a401801c0d08001c0c0d00e0040c69100d00d00e45408581440e01c042550b41c140c001000503404840035034080f440a00d00ca40310b800c8001464104441c40385410514007c0504003c2407028460143d4081c0400740c80180b1001e8459100f07907298441e01c40d400b54411014000150302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647014946 1250 647013696 647013701
    0xe2206140a1a0a270e030408031308010207020d060e010b09040c051e0306040b180304031a150108070f090e100305010b06031012031416021c390e0f060121 68
    0x102810070001850b6900001401d0031b41d007064100ca003e40d0000500044100d440403483c5015050240003140f400404d640051064500440010f01080d200c0561080100742075012202c803041c082c01c03210091a140c600a218175406001c4d25100350a01103070201004030a002950a07440702400509460b280c03604d9201400b040142500c2285091034250b0701c02040178000f902c019440703050842c1100314a440001c120f03000083c1170341d041c00d02d08110054982e0b40020710f150098450f08101640210807601203032040540e80060380c0c20721385c00f4148400f40600c0480c0801322801500200440b185070000c00586200030f88100c2040c19801e40c06208285a8050381d1001500c241003906040c002c9035000c098582100210300b0800002404040035418021012021004801c0b8071070801c059541d9540414607440e81500949108c107041d100030580d440386814952101d507042d8014090360f94022900090084071014402d40c0306601162041d40165084000c2803104030842e6002000001c04c00300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647016196 1250 647014946 647015009
    0xd320309070302030f16050919050c1b030c10090c14030a020a1e060302031b031b0f070c0807030803070f09031e0c0e2206140a1a0a 58
    0x1040c0c080da65000005035001c01114441c01c408101802800c81007400030841145144d010320702410504040013090540310001d009c0a10000c02c001406850300c41c00c1403c103008100240503803034400001c0c900414000001b40080030490740072228440d0341c0211300800d460300004000d00b140710b000c0091005c00213000c41c50202c0000542140d000002e80d400040c24191603a00612800d050b61016501c00c0c0e020030100c1018001c03600b001e61641c108246410f165848840c03103141702d0400400401c0700300c40d851204410f010025200191154042c0d0749091442e40007150843d0410410040040c0c4040302040c2d15040325004540c090039a0f59086041d282d0155003040c2000f041240c20010000039100e030f01454003c06000c405a0252201e845d15103100e074a1034110b8414012044100711403000d143d41491480c0711410302c640c1c0180300030320b4080c0103800c8075142940c2c800d1a0108200f0903075030a80c4001c41800008088000b00350401082c800f1036102401a030b202082c1d0700c00c5410300347c103050481d0324 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647017446 1250 647016196 647016211
    0x90605060c0a080315090f0103210f111203010305070609120b010312180602030306030c03011b050a090305010e03030a1a010c02010e0f0402070f1101111f1d0d3203 72
    0x1206544010001b5011300e0211050039028640304014000d000c00c1e5200c000240481c000074a01035888000080c08000490650108000c0000c1c1c1002c801e84080c001c1407410000c0b559650b8480d61641703032881d15107125009c0d45000070f000c20400207450390340b0307001a00003541001821000341d080d5265810074076811059401130150030150ba030008200041003500810055004d16202d00300ba004041c100944003510b64802d038101007402c0c03050340044202095459203410400c1da22090114203480c960b0041c0e0000e0165481c200800d40525404801544100c48811040002112011456200206241a10380010200d42c0148019401810a800a500008e08a606410412000406036400420b0855101300d540c0f10320401c12031804880141d008090810180d2074202030710442d07598018480e01e10351054615009100c00c00a030b03011484030094000001c0b0359138080008183d45070900824407001520b6501a0062596032003194070740502c0b0f0441104d4108225230b03680d80035400c080c0401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647018696 1250 647017446 647017471
    0x50306040209031024030209220203061e06010c031d130c090504060b161b0504050c0a180f0306021e03130c060e06090402030a09051006090605060c0a0803 68
    0x1d41c1d0381d404000c43d00e03a4000100000c203d01105e0200980018500c0c00c2e120701c201c038088014401070303684054056000c49141c0d84550301d6503e0307085030800840d14100194140c0584414400c000f4003102c41d40d00c0c103451015041110391030b44c03001101d9a00014001400082c0e00303801c0c41c82045010301415070760318001840c003512400d1500d440012505c09400800209414810402003820300b80551801805020a042c1c00c000501c00082e04141c01c4200003003540d42c00d00a1151010543d240c110701a0001410400c42da1034811003079011031340000c02c0e0b074002c5030803a4030346111956071000c42416506060400d170041440c65035100041e4200013030800341c01020315a80003034000300f6030185124a460540050508816050000d03010f00300760428002c2003100315410800382c0310b00089484481d0140c800690fa81c0d940400ca800410f90b050004190b80078404050b00318100a400490070782e50500d0040000c15902d10400c51240b055455414441e007007076040b8000b240050018503030001000002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647019946 1250 647018696 647018707
    0x108060a03080c010b120c030a0210030f1109040b1207150903051002040f0906030503120a1506050a1106060f04022101030309090e0a03091701020d0509150f0c0a0503060402 76
    0xb2141607400140011106039540c103e60141841c011015201c0725111070098049107000300c0c0401c1d10740d030044c10041e002d0311101e45119241886503204401d03101a03500100070090b0080200d035015800000c080c2d00c580c1c146000714803940b61a0400c403032861a454002e001892901700410040e1441c6040c04080c070804a000201080c0c060041503903040300304c200188e9650030944007038510401600b10385200d528000c4140000348002040b0303914001c0e8600080d82d2903482a05180c0541405807201c0c8101540e2a40019007540050207030400441302c1e2113210803112000304141e0b03203e00031500507a05c10180515461507007442e60051100f002c4021010900382c01a5043c00c2c140182a441100001ca401d101085820382a2155403001d2041c0001342403160240c0d20000e06500f00e0b4090550302d0144603079803145d148802d50456610070900c46080c0f1031890311110958440d010f610003130350b14150802c00140c9044481e032040d40b26038000c501e15400d0020b1080704403516003008144c25002a4200702 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647021196 1250 647019946 647019953
    0x1514011412100902010212041a13080d1d0f090408090402090306040b040606091a12010e01230601020d02030f0306310b01030b0d080711041404050c03120304020108060a03 75
    0x10718802d00c0364103000400c8100311880024a040703208240802203200502050102d07100c00d01400962000385025192505104070808107803284650013540c2c0c6204848402d882070360041d006c145001002d07c105d043c0043c901050201110114400c1940701c60440002070005498001405619201910050401e100640401d150071000e4a0a4400310641010001003001500a590144c143c00d0001d011b03507031042da0003081d418040c803440c40c42601c85140c1415070002c04d600031011240c1800007440b8840e81c81031001d0401007aa1144080018a80000b50700b0754000103c4c1384011039942e00030762a00d40c00c203038402c41c00d0300040e20a95010f80f820070380c0c0c00d038080c480140c15018081803042c000c00c07103403405680040701d004501c02410315007044a04115990782008031020f16801c00354543c1c1e90300d10345c500341c84c505031496801e5a1251038041da804005031300000c1507118a218400f01e42403055032108050f41c0f10f0b120341100314100300410018005511035004660400c80c007425026480351a40d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647022446 1250 647021196 647021203
    0xc0509131e0207031205090c090402010509040e10060609150206060607240f0c03060b0a26090f12040f05040903021e010209010f0813120c0c0e041514011412 69
    0x2421340019581c0100c4858840c00742c400d007908803035000000c022030390b040380110300b02010040000e410f104011a03a2401507c03143c1061088100d908240c46542e81e107100c29800a003150b000d0070b00050000080442c5042030310343c203040300c0501e5400401040d903c40007040301d540d00800303003240c01402858041030500c00344281154903042c0d07440b0204032200c01301051000c031500203008004140c14a04200104280d210072160800c40340c0c6480d121391100c3c202462a1410b00e02d81c0762480851140c1082a046804550740108070146016151800032418490410340241e016200010081300030401140ca80b96100d48a818824010b4840b20705000310300f04d070500070304c00c01c1520f1a5000103000c1115a40040f108902c44800d00b0515883d00f04805c00250000441e01e009195503540f038200c0c0e2216004505a01c92540d0090a03d00060f40300e106000940d40b09407001c0760fa28a10102425203200c00d80540c092071894441e000641d40e1904900c0d00780c0044001035907030407072600d00c081c1c2c18404052 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647023696 1250 647022446 647022457
    0x2d061810020d270b07180816050a06090e060d0c031b0513060e06040e160f150305070e0d1104090506040c060c0305070b0c120702060a0c0509131e02 65
    0x70100002e8581801ca61012504002e5a9840c81c0301e03c2d811103100000c1507040c42c0c81d00304c0c1091074280c3c1c2c005100d0701d20507030504043d00080454480d0300b07000b00000816081000079120181c40b010031087d078651040d80c0c185814012120300c546020002551405e181d05041c000328021076100c03002d16500c0e1503c00e10a9064000316400c05448841400360b82401008081c2d010400d1500f00989403612803c05c03100300014140c14851074482407400304a080800c221841400d0900e00d0102540c0d484c510300d03021180d984100d001d48412400514100d07030091190a104026585410320b1146d600c0040003c0444880c070200c44000300f0603880403031604e440c401c40f081140b2404c010305490409085c50071407410035621000c20030120007040ea002942c00016600c04541c02441180c0a484d4840e0070501c0d4090f4a4040e9a1000f82e4820020660782c0050540d00460401071300b0022420381441c1210780340b1440004c1a00213030001b84c01c08400d0682d5011145656001c18030b000784581c2c030078004050f80d100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647024946 1250 647023696 647023717
    0x127030c021914100e0a0306050c070803070c030f0c021005030912030109060f12021503070201201b0604080315040219020f0607031a010c02030307050106082d06181002 74
    0x140f81100e508143c910400c0045440c1040a05800d0840c00550070760403500000784456100c00100740d52000314005c0e44d041c180d01001845c0c4034170f07214500a200101e18401600082c541c0c64072020a18003801d03210a030103030007600004021081442c02e641d00e60010381101d10900c5030180f40c030700c000040703c00746000e058624004140c1500d01040680f49003660f03000108045a120002e2006a4030305c03010100c0c00d0320000845440b940c0b00c0e01c0590040407050b805a136841102015556064180c100800f804180c0c824600041001100312581c0c400d000c0724000c3c2118070401c080381000d0440c24201c1140305000780090301c0c010032481c481d00020340010208004d43e1001d8030b60340590f1418080e40354401d9651034208242200203100303589015213008403e040c0105071000307000b951400d10882c2c01058010300240182c5075030360005a607600301081d0109062840e40b00543c2810540541e000c2040307090750040440c1d456400d115000e01010442c00440c81c400c0c030400c05942d0302c5900140140034123 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647026196 1250 647024946 647024969
    0x90d020904150e0601052e0c05150f04020406171510030c0b0d0e0a0c0b090a0504021207020d18150203070f030f0e06040e1f08010e030702030127030c0219 68
    0x5042c0600031108181d24420090340e0141c109a0302542c1d00c4c0740c69150603116032030308040081c80c03400c06a0612b110341000c041c0c0381d05950204242e40b18401c0da41402280f0a46040004503914040d40741c08500a100f03020b211341250031812010304504200581001c82902000540c507569038580c035075003501d544010340001010480d03066400d82c0344241c48440700e503100680011905a5100c08128889010390b100404000c07039612040c0e1215480b90019002c007900466841104101061807201c08941090051140780c400c0c101043c81596900210424501b00c14000781c14404024070075244c6e9201d200c118402440428003090b84c459a82000900a0319010b0b0a41c1c0403980c001c001d858442001030240008100801940380e02401c140d80c03140c07841e0500f0745542c1c5400074400c42d0034800d5000414a60800f41c440704083c03004001008000d1088000704002c0c40b810640d640c00e10782010369281c03040d001e4456240030038018190064024030003082484c00e0350594080c01c4000c40700d40c2045034580c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647027446 1250 647026196 647026199
    0x840030e04050703090521040f090906060812070b3c09161e090e0304090605091b0c010f05041101080708013209010303030903090b090d020904150e0601 67
    0x709485000d4000115180600502c1540d486080e5501405c0c0081d4000c0300b109010103c0103088101907401170240b114071305200598804c000000707000c1c0d910701598054980740d4005444540058074100e09104140010304111031a12000310801d17005100188500f40700a440e28540c0d54806d94106410514010301003d0700c00d0b541c01e80380d200f0003c2c030883c0d10b5801820104506061050b0a81c104c40492012a0000080c400350502e01400e5178451b1080a040900c10510300c9401302c00380007681c0510904004d80c5549600b0010b4001060b5440d03011540000303410200d03048010010310304922504c00108206001c0c0c801d0404849044900380d66641c0401ca014401c7d61384106519000007403490402d00c0b41d41400c805145101050302c1e04000e0545001030000541e00d0204000c9040030b0061000c0660b603900e0401502800c500101100002c0d59114045114200c100a0350345061010b401b03e1707070604099003403028400000e0000c0e2213160600f1250b0740f8070700f00c60180c0383e03101001802824155 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647028696 1250 647027446 647027449
    0x5070e030c04020d0f230108010509030708030750120601171f0b070201120c0207080f030c0d1b11130e0a03020c04021602100302190509100840030e 65
    0x481040c0c0023001180d040c40144a400100041683c800940281400c2d90340d403030300310040d1044558031002040b080c10980c3c40d01c481d4200c400b540540c0c0401e0440c011400030b0384a07014101003513540d40407101c8410038000c4d500a4540301a005d070b4441c0d0181003000030031789252800c00e5040412030b1304a00c2c1c1300c0300d0b000040708a204101c85000502c03254211500b4860154006007078116000090703402c241c1d448888150051007041428000d0951034180d52114441c8107070581c99500c1026032140500c5100c02c00c10b40d0703601c0354441c03924102e2401005454061250750341d0b01001301d200081940854528401c0031b440400d80310f0301e000040c4000081440e071500d4075001e030a0075103582e0103074440d91050090f0040d4045607581e80c4000343c1d04540c03609040b212842c0c143c0c000e0103100c40c41000500c034030a01110664000c0300400d1825402c43e44003e00aa80390300072242e184080fa00d1038620500c50000b600c2c045102c03c0441258000c51070003280c480164081c5c040e444410180640005007540401d10b107a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647029946 1250 647028696 647028761
    0x3071b1b05060924220f0e0103081902032704060603020c0a0303020702030f150714040f2102030f010207110901060801150e090c07030305070e030c04020d0f 69
    0x3030000361210741c03d000c4400300044840c0c1d400b80800040641c2034140c100136064280c1103541083e807284040240b45040704404c2c40001c05401181c2e400e01c448403011a0948180b00c0441c1200d50003045286482120407041d4007080e849000c060961105000c640800b001c001030700b02034040080f0461000e000341c20b00300401e42c4c8480c0e0080040c9441000210805c0b040441c0c42940e058050034050703030302c91551001ca0302c1c0c0091060780a0150184070401c540901d81034056902681440c3e03141e41c1e000700301517801c05c058465403080d6441e2103030001c0b041140c01112648a00c0c0708400342c00c001002c030b082c0d03004070381071078081c040c0940786950000b20360781080362890540440a40640307100d0000e6040404c041d0985030180100502e401e42e40840c80100c52058007001c0003000043030031051040c100a1000f0700c0c00d80040c502140401d09050004003903602c11503003d2000b4000400500007007a8103002c0c80020351100041905203a203428502410300c44034000d14017010044038802c0e08200400c20072445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647031196 1250 647029946 647029949
    0x30905190308250e0607020901091b02060708060d1109090102031b09060702060f04030f030824010212030903041a04091107030e060d29100306050901030803071b1b 72
    0x281c1e030304001e0b0205000898003c12244038140c1e4180019011801d0000545034020410000e500841038800414140305039080341c8580140d811600e802240b55200c1a42c07549001c0ba0710600044a03880003c1c0c4610b030030b1440e0b00140f4054400c001725504440081a400c140899100d18240c0d000000c0c000b1405008900c550b8400b80c20320810708213400303d000103c40e4403c4181c040d125000c0855590512030024048400a5520102441d816500b92601918900d4202c5a00c8880000b03000c010144964146072403c142c0f40c140c1c003034031200100750219400d0b900040c04054480c030080c400841d146541c5d40c03810450140d110302c2c1c0358aa52903d0205010364101d4444001807407010700c851130010703810240800d0840c40072129151584001c1b0400c000074404400c140c615010444000800c1109015821681d01c5095a0031000029298425030a464481c803ca64005500c0702c010004154003002568111780640f41c0000060309004c1416015800c801081d90381c0d594213122000001d025115020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647032446 1250 647031196 647031211
    0x501020d02030c060a020a1b120801090b060318010e0d0815061309020322060207020111010b06041208090a0b0d1a01090909050a200415120f03030905190308 69
    0x603d0500c1c80e0103400d4942e40e0203810705451079004100c03500a1405511601c102c0c0c48a55090400034040303041404998401c01070321408954a40d002141d0200305002d103070441c98020344114a0750725005507078120308030072808100d240d540c2d80c2d40d902c001613028400d00d50540001d0381d6060072400c00e0000e2040300f82c582c80300d451180070104040600c40c0b120a050204945111030010784075074886032030b0342c4e03204641e034002030300c08040e516001d0400c07105034040c00001d4000c1e07840030654148024020301700d0305c5428a03107030b00003020701003000001c418135801481c0034480e4604a05086494000c501204c2254000c41aa80c1c0081010380e0a14500e2080d904c81000b5101c05c05110b010000000c3c00f06019402080c502903286c2d1030080c02d114007003040c1450f499008144da800e048840005040e2520002140b5100d0303070130044604588600f010301e483c141d070b13010003c418210340c40355102c3c000b6030459002201459150584400030400a0000407404200c6040d844028140c901cbc0003002418010f0203035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647033696 1250 647032446 647032453
    0x10c17031f080a0f0f050703150e06060f0102060a0b061303030323010f0e040318171020210c0310090c0c12030e0303090d08070f05030f1518010501020d02 68
    0x50307000c00d50803d404014117402010922200c496030801030b050000640010b01400304003a00c01e0804101584603504801495050300d64907102d0004010101001c00700b2140180e01c6680820000700b0280c1c0424204880142064a40706001e841d0211905c829842031b000303741d980069050850302424241078103080f0201c000e481c0d42c140104440b9528450240302e12001c4408002070405001c1c0345400c4071902c0c07407044030032660394501c88001029550001003206000e407a4040c54000341c0d03030050f10b050300001182c0e5006942101000034485e048131101c1d440c000b10107208080210b107542100d501607070a540b50903036240b40c4410a0b09846040d80d004940e03852410f40d06004075584030307010b0380c8419804500380c00b081e1340407031003140a850b201218401c240000403d000300d02000241c07900c165400c075100c4403159510280d00381c3d010b2a60380060700c0440e6080000401ea11840349840764002004411035100694000c0440d0340c00751340c0c03400444030b100c24400602c2190703010002c2c44106881803004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647034946 1250 647033696 647033713
    0x1e0e011401030804122a08070801020403030207140102030415080109141909020316080715050a020738030603160602030d0e0a12020604110618010c17031f08 69
    0x410f205482103104942801c810f605200b8208103100d40b0020144d5440fa9011039500c840040d100c1c0054464821f8100a01c26024001000c00b018000d4034112030701074000e00b900c18a04014030410403100d1001504601082102241c90303142064003001403101a40c0e04650743d030400c40240115681060308101c1030580004000e000d503903180c605011850014804540c000b007910210b4500251580b804264400340d410100790f00d800012540100c85400f41d001c0e07030120b8010f00c1610341d13107e0750a06000580150105000040c014542c004c268038003090107000012203e00540031401c40e02002000011000060028900e0300f0450200561301d0003680d28040b81ca400000395403407003600540c04289868141c01c1503a50b40520a00c0c10f01c0e40c000400280b640040700c1c000791107080c1107500f242e207006510501c00c80c0e401c0080c00d451409504034909444100d51200554180b28a102e04032083c0e4410055007448446c030b80d018502401004240c50341d403010059041c0c2c1400403d03081400150f01151a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647036196 1250 647034946 647034953
    0xa0c030b0d120e1c1502070f0807050703080a03020c011d0619021903091a040b040f080c07060306090b0607020d122307021c0312020c011e0e01140103 66
    0x244004141e0b02c4522010900d80306003080c0c804202ca0204a130340b001c25140d10b24900c40302e807540075445074403501d10400b031001c0d0300540300100e0007049000b4140c9200410220300107140d0700001d0a0b141d02410031140410ba59035510000396104050000c0001e80114000c81421424015038008201180ccc404074250888034041e940c500004000100862900300703c000c0b03005542d411280c20366105c40b06600840c404090140c0501940384084030b01c0c2e02c040020441003445840018003643d40312520303041b10341700c0d511000c040752044803040e11151010030500302d00c0001000803800400e00307078402141072407411254034111030b4110302e102c0c003071082009200c005035220440c0b000c049500800020401c2c40e1300404413206031b846060b840c440010b5513010040070a422014140851084a0002c00b00301d40305005408071581c0c07003000b40814007201d80e03480c4100d00768001e0600681e1308030000440424900c26400c54516585030a90180c1d40d44400e80c105140c01e00444102800b0001b400d5803652542c0d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647037446 1250 647036196 647036209
    0x31a010305280f05040804050111190305090f090702060907080c010522150806150712081b0a08040506011a1209070b04080d030608010e0d1404050411030a0c030b 71
    0x400303000c103042d2000c040c00c00c229101d91002550f010310b0725003004079180c1443c1030141c40e03015006560200d01d00c400c00e150b0504002810713a01c0b801c000840e030a013010440c0d038196030341e070040b089040d40b058441c050080952600700c1441e21890056008103424204001902d09000c483c1d0890401c5421000c41c0502698010702100c800000ba4009460304008628615804020781e41000f080074a8001d00684080e0b4003408044c0203020454403a0048192544642020b02c512a0010819404d181003172860500442c64145d021420710414a103139408001c080400f58012001140410329140501042c8103080040e24050907032118011402825400b04c00c0003400703844d85c03c050008070480003c0c940c4106120440061002545503601c1d241c5442c6019210748041d03042c240020700e40a4001041841405808601c40000c00540907407462040110740c00601d00003a00300d62841080006400d465078803035041c6032820042440e40320308100520800707941c0c17100105420541040c1f00d4198a5030f620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647038696 1250 647037446 647037481
    0xb0f060a051c081204060e030315060c0106051201020703090e0408161506090b131103130c1e06020d1e0806030f1203070e0d0f08031305030a031a010305 67
    0x2250802c200108206140681406100e0010000c2c00702150110f40e8a9104442602032441074105004d036143d5075107010f60b80d0108a90036004888001c503100c0c81814460010840c036a001d000200e0907944500200e2110300c0129004107141c1e50000f094000c4c56402200c08019103004503107019641030684403280300e805000d040340c0040e44540c03543c904002e2281031031000300d50700f814180231070390340e40320840020320302441460b010b562070103a41004400e8034410b400c0d244207100005825510b0700101d03207141841102c1d089400040003800464120300c10f09000c000c81c18081c8000d60480c0c206000203041c154045c501034188030381c51040c081c411001c13051100d00704801e032512504603910340001070714100c1c0c440501c20b050301a07403208144200b10780004600c9200e05440304c6003400704000078014448140507026204100c1400b004000030316003001542c01c050720107900001111144c0358035085600644105005c0b0f540c6102c29141c02803040c4c4184080c0100742000c05c603c0c90614076421480e000e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647039946 1250 647038696 647038699
    0x72c0c09060f0c010510170c0d1502120a06090b090c090105030a0b120106060212090a12060b0603010905060918030904200d0f060801021e0711040203040f0b0f060a05 73
    0x210b01e901c5042c4440e029519488140d00092001d03042c15801110000204d000c0d400814100402d01c6082010000b98210080c0d40501340500c10250b5403103200c815148404000b440b075800304044030060b588082e0300381c06075642e998000380c07483c6000070700b008890f040d4001c1809100c0220800c1000c0c11010103840400348203003001c0d9940d54035a030b151002040084c071540d034400c0e07010710515401281503000030152034054089031158820720ba41010280501d9031031035448505502300b8001c200440402c410054803a000100300442058000b52098000b41c201d607000c0d075541c2c4d082107010f00e070280d0495080403d074030b11948240c851101041e22803040030741c40c0d8025522506000b031075404143c5428008001c151483d0b0f160603c0b507001e0006007c042140003681828400003281820040c821290603000201002c140d410b80ca948401850f00107140988510f102c941c0401029121400190321480c03040441506030101444c12550218024280500358040c2400f00012a1200a0b0050a9600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647041196 1250 647039946 647039959
    0x10091404030809161403071e0501030e010b030703050f060a0c1710180f050f010627050307090207032007050d140d0c02121507031805072c0c09 63
    0x4038101401c2c500010041210454803c04100103079540c00e40221781c0e0118421416601410b5031109407074504c0610340d0104030040c400050400043d070090344484405180b00001094080c07000c40002d05001407a801075545801429400060150921005500004900042200c0347d02008000d010f500c1c0c540b001c02e00c810108000c00c0c1e0019182c0105070041501d2845106003001740400038000d0310440300312510550800001c13500420b4041c41450603102e140e624540900240324903202440000c0306001d5a00383c03013a00c081041d440c2880000c000d80a00e02e405642c0f1180f03460002d107a00c1c9080400544200c031900607000f40d1001141c07400803140100c0724500920307643e0405d4114209107800c50300c0d040c03103074841401c10300303070005683d5500c10b0085a44403c00c4442007038068846040709090350301180100005a03401d0f00039030006100710000b4242c002d03070301c42d9980e130340b484d00c0019000842d401c004540880740010030224955002030940c00c40c0340c0942404002d04c4540e00405641c40e11804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647042446 1250 647041196 647041201
    0xa09050d021305070513050a050f0d1a0405070617100b0c0c0d0507031101050309030d0c090306050403020601090515060708090d080f121e060f060d0c0503100914040308 74
    0x5481c6450060700341c0c1840300800241c140080e0240495200640c500300c0d40421b400c0000303003031800c00c00c89001c0350405880c0141d0f121000e02000790160905104075941481030613400840690703494440c0c451489400105091414201c01400b15071100d210030400c10700388c00c200622480c0307985502c0112164400b4050322a482e110b880c1d820841030903034a075080201e02c65040248080010800100c9003d00303d50043d82c0761503401126a031208850003d02580100040301f03904c40307640c1c070241084219141000035261a0781d00c88042d40c909031820341c0107a11072001405004150b02c01c0030313042000b04407846620011900451241d02680001806814011034000c8141c2c9845154404040c3d104139807a540e5036607050070200b250400c4100914814685c40022603110540100c05440000010700c00c41070340d2420700300a4684107000c4495044407050103010050200350007041040080e80d100d0548134a400c0c0c80900c50f48006d640041015400d100c0324400410544841680003505413421403941d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647043696 1250 647042446 647042449
    0x203100e1906050d030516260714030f0304080a021c020105040605060603133005040f0501170402090a0b060d0c080906100611010b0303070c03021e1e1305070f12020a09050d02 77
    0x81e09000700c002a405800403423117604015400904c0c0e03a520441800038403c9a400c5415568002e0f0040042110009c101003004102190068404104a481101c244000c001403a1180c00b44d8150b400c00503071b44500034072003001194002d072640801d00303031011410b520307100782c91540d140300380c1d035015141540c0ca007070b0084070400540034884c28000c1018078400c504103011000b070181c1e01904c40c1c0010728400b10004a80c66100b1014041c010003044a0020b454449800b0000b95588c0a80f204208699400b00100d1a449540290280320303103c0c1000122500681e6000d0f011902c0201000515000801085000c504468046060b00c020b440d000100f540807003100c500404c3c514050355031500c4082217400401a80070254002c0e64401c0ea50711041102c043d09035040d01e400802000e034450301a03490301d032100810304178614200100601801094a003252024104c40059901c400000c0030624903004039904010390000710310100004614001c1d0351540140a190280910b61152501c2d403884030a6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647044946 1250 647043696 647043713
    0xf09010908060103030c0309060c050d050a05130308090a0902030903041502071a04090608010921031401170609190807020607231b0901090203100e1906050d030516 72
    0x2606401d01124001c0d616401e000e032050600c1e1204400060724080302080c0340e8032071900d6480455102c0000d20189403040c105a9480e004820b0b00310802070180600500c00003e5410a801980114459542c3c0c8881101344114409940c1200e0311042c010000d000a0780000400c66040319601d600710500700c4103c1e4000c03405d140166000000c0c03580314452200c1c01c4202c413002403040718480c541c104025070b031f140c0c081400d03108003a00103081c400c1042c518080c4c80380b03000c104142d5040e0a16000501d0040c00c000c040d901e00c820380041030400f8070502069a80b0750104003464115860b00c0c01041c00c007081905e00c20303605c1c1e41c0003402031890348007080510840d00d41c201942c50080d88400c0c5d2690b03042c0112509419501c445080c9503c501c601c0324144800310b4001c00c9450b20890180041c0026800d10440380041d6102801010510075990000107106001c500154001c2000c2500340f1b200031103070030b4808142c3d84180c100c5e610810b10b2403188000a42c0000c2102d017072443c640342804080c00d49041200e131 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647046196 1250 647044946 647044949
    0x3c020d0c080318010306060e061207031b020102090301051005030a030324140f040629070501020a020610050a061205040f05071517010e040f170d0203180f030f090109 73
    0x1441e2002140f1103d48803699150040c1c142c0703080c2d8007006915650034089809440c40c00c000c540242d0b007000900c00141c06440c125a0003411400c0c00b20301c0480c0d0000306441d1500b0907140c0d50060350b020038100780700c0c41d003070280d03e0f0002c6441d1206800d00d428900020340b40c0c0c0c2030180c01000d040d940e00400d16446100e405a414005044040c140325070354520380c01802105440106106070354012120303000b072500703110304810b44802c22220b0008440041d401c061100800354401c490340428008200011024001841d68440c0ca40c050040350403d143c0c48241c82c081600050312551903003030b090220740d620491006001040d0000481d03540c030355080200d5061102d09002e4001d0280c00e6001c2032310302c0500c005080901541d69120050300d01c200d074106469000f80100301ca002000c501040100b0820704900340d40d5405200b00205030310380b407208198568040500d1040894000c0201301001c843da200380224030388000c020b080c95029007840251240314065104803040c0c00440d0084159209038410070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647047446 1250 647046196 647046209
    0x201090804170c0d200a0503010204080c09010906080604080a0e090c030118020315010c03020f1f06080318090a060302041a0916020307030c0602163c020d0c 69
    0x141e40d1070300c0d001080114101c00c80c1032052403161038980400790800703518120500c3d0704040c20780040701404000d40c40e00b4503c001480e51040800c2008102da40d0b0a1004100509800b0024855075020700180440041e05920643e03030700c1d290200030480240f02003112903000c0d61000300c1540d50b030811001030303841c60b0071242082d4001144e14200310294200e00c004506036050120780c0840da101083d48442a031204850b031820009180108400c00e5024240d070f4201c7c1031003070040d20741113030300c0d0341e011468844c40d190720405650184e031100b007414449119400c05003065401540c0307840c02c01306225a091a401e10b84600814543d400550883e141e540f1442c00f5550080c01840302c8540f0030303502c6841e40320046101d4400d1400e01e001c1441c0d0244440842c030044c8058002e141480c0158074240d8140c0714401080c1c8149408008001d0400084001400c0182c410010148064005c5a8521031407079002503400408007203030348c0c540350104410940c6104a078100e940803002406880e1040e1003203501d40c00700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647048696 1250 647047446 647047463
    0x3030c1315090504051f03060f020705031305101d011805030f0c0f09060109090e07030605010806190204080a1e0b18100612230f0307110a061707020109 67
    0x30315440b10030321040741c1040b1002d12031a1101c0401e1001d145403200f0036500705122500030030003d00107070028485440d41400c010300303091460301c82c2ca007142d10450a00e81050300c0100c05000b00d00d45000a4100f44010349000c040c2c16010242118040305084c00d010706021191100f80f80c1c0342c00b041d02c12006068050305461802001e8800d45079590307081240c0c0f510410340c050b410ba01c5814403d004510420050b5212040d8070f14042014004060700b103007440c4540102000400411282e0080c140202a503600810151030041100d503002c241c041c02541015004020070840c0c40c2001070702e03250300b640040c1183c040600401d00201c02504c824070050406904004201c075685226160140c2881104191135500e407014592030b0880708079002c4c840700c400842c61a80045070a510640311400100b0050218100701c015549241c00c1e8809020381030f981c0002070b40000c00001404d070107040c0344150340b0f020207079051403c060411841000008000000000000c021501c00d40007042c4131130700103015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647049946 1250 647048696 647048729
    0x406031a030d030f05060607170a0306090207080304020306060906151c06080c10020705030712080c1002090a0f031203090c0f0306060603060524090a0e09060702010513030203030c13 80
    0x9809006135185a448844c034002c002001410200201c8e20207503401049100192a20240030f4807a40040b001402007560700c01022652119030320041070361600400c00580c0701c2c501807042600c0c0100c010a043c1c0114105806d000f056100d036191612084200d590284d1106000c99520004404500111001e1030408400044c546004180a00c1180080e10741a140c41c001c50b80a981c2d40c1c1e09440f40d60703010703805480c003004120030794116025081d1190340c01625280f07a108080b841e1907000172003590510b60004454070a880c1c0265064000c04241d000c105030742d451070315440b500340140c0030440280340e12107900c04100000f0301101e0018084241205191548a003008001401ca900444000c28a00700300400d540c41d011041003141a4015089407020303160040300d0945401171080320340c0080d1121030101e481c00c00e164480348952420802032003246042040242034800150181d000c080e08500f15101003a130200480794030414400b000341d69003600f40b84240b00003413103900000416600200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647051196 1250 647049946 647049973
    0x91107060f050403170106050d021303020603090601050906150708030408070b0c07022d041a03010c03141003020319031b06020a030b03030c0a0212072105010c020d050406031a03 78
    0x31690003a4041d56035402d01d2000c064160000b0703802800340001081d01802107009d07459039600280489603041a406003082c1d920b6011640740c0c1c1060300d2507100340c0c0202c0c0041c0628203043c4816a401581140e2090080400006026540c8034001c0d0103040c849000001405000140c4102c400341076200ca207600710384c036204a06a0300d94126071002ca204110a81110444101103c015407050891510395a01241d1810412000b02141920100c1c081e41400444030166001e208240f821440398601007010301e0300300b40c042d40c207050051580c00d010a10000901c0941c9000940030801c0c0380c840c0c1044417080403814151452501601c0105036060450b41c07c6081240c1e507001742c4a80c0d00c4540307052100400c510b080586034012601c0c101226840080d4010251802d50304118003203c4c201c0548080c075444104910304040071010070a866262403101c1e104100007480b681c000c1e4041480546510608007500a0484c80349114000c00c040d1240d01c46800d204c11402100c0880c8002022a03088018601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647052446 1250 647051196 647051201
    0x30604050a1e110f0d0b0108030a030609020a080c030a090f030c030807080106050904111303051c05040b0304330605120304050d140a200a120507091107060f 69
    0x94007110030200402e0980040c4020700d40340320480340c0c00240e40180f550000b00384400280328840d2540d100031250b04080100c0d400d40303030007806001000081c0d5903460340c10b8030280c20b0b00c80b244c0c410008544108a182e401d00d50001c3c245800502c4040c0352a030ba6181c3c003c900015120031080a8500d0b001c07001e0420806401410909074035201c1d4980e18503a80d030303020066600700b100b4420600412002c1021440c249000d902500c50014045009802d010700d184d04000f43c3c0700390341c000720313115805100d294501041d91803d030107a0488a1500a06d0142081c01c2034245010150000300701c1080440c0700d081c241544064100d030030692a9a541105032080070003030142600f0305c81d650041c202c094540f0060b203404800c42d400d9403c00b5121203100c84059840f450806c180c1c52044507a4058100ca103c006640c5280e84502e100c040d82c1c990b00441e10010030405200202c0c1e11801c006120016040002000421110101c9510030030004026841e01c1d64514144200e07140281440d180c061045011043d55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647053696 1250 647052446 647052463
    0x30c12070522030b180703111c0b01050108240103020a210902090106030b420307020c100c061a04141902160605040c12060e0d0207151b0203060405 65
    0x80e103c44c0d82680751085800484c031401c940c0e01d00306400c45901400800c4000103080d803a940054801c0d80031070240400070000341c88892003111021403440040003650ba1102001c1d0300400c02c0c100d01814080b40c0740210008032074907600c1038185138001c60030a03c0701c0e0003401c20060105404890400e5070308006501401400c02c244101c3c4201070311b800101d0018400d10a400b070501c07000e00240c80041350714001d8080c8085510043c400c0c1c2a86a079001080c0c459040c84400f134110501100791070b03050002003e800d0402212455029203d52013069081e16480b82003132070b03c5500b08030f0000e40405111400681c1d00c0c50300e1005500681440c2c0c040624a0004050354070841008071814554071952031000164850b640079500c0702d0307162030001740c00304845c0c2d401a60824411503440340003da503030074131041d42001d0750f0040e982c0d99620341c100701042d80140106141104544007a200c00307070501050907020b00c9440b20080800c1543c00100b2034185400c0d40010030140c0040407107100d4900f03032800c103a441c51070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647054946 1250 647053696 647053703
    0xa02010908030a2304030204060b03040c140f1915020c04050603012031060e0a0506041502010204050301020d061e050303181f23030c1207052203 64
    0x100c04000400351408015100880259660054611034800704035888001c200003403522008100310000040e503ea1148100400018408075160300e03090410403c01820342d881002c991600440e002c2032139481c41030b086814442200e010380d071540a0740c1c006206002d560172100c1d04550560b03040070060340000300c2c418080c074212424081652540c0505d8265208090600c4070303400341040c0700f5a05000c1c0000703044980551101616050b0300300b0030150103001e030b0250143d00030102c94814450035504c500e02d51940032068407000c101c00c0c5040c0c082080c0d441140304401d26040c005203219440c41c400c1d011a4000c00008009545601e24902e00100411407427103a6001c41c2030000c410740c1c003490380071083d80071100010007550034460300000361103801d951106126401005012000300c48031102356413100c100d0042d80c450008140150b04607801b40c5400d0392001c1030f034a0a00801c0940d42c103180c100d40e0301c6030948150200707035100c0314000c0d070b424000c00040b0740044003c01c2c04a80054030418103003085070b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647056196 1250 647054946 647054957
    0x12010504020703124203020d02030a050109080316030b030a0602130b030406020a08090d1e031103040b180f03040302040e03040b030403180501030b0607030f270512150f060a170a0201 80
    0x10718101c051030640d00e11520745c07501d58001034104098500582c49004079070015040c6d0700c2d1610b480ea1014211404514100c45040022050114504509034516140c0120741010080803c68000007580d541c0d01000041c007031a00011280c0603d00940420310042c00880f02664803401c00e40b8014010750840004440001c19403000100e000b640000c0480303001c0c5c81a21540c40d07a0445240c5045149819000da00034980c451400c1041010b10000961042d8029000b4030950700308060314211034481e1100b11081c6620150b40000706a402004035011aa03045070000f0b80c214400029a0071401980c3c8081c802c0400442000b080c90340102c09081c60310031142aa0340090349520040d0201c40182c100391b5003082e0148401c40000303004145180c4068080d0410a1803203003c4281c2100d82e41c80c811340000b42e040b001d40701708201d080000b0041e10b5021030f80e01030300349030368100400341c0021030003411855004202d1010030070780c0c1c4940c2020700c040d02103444601605601901850b80e030701c00210040b0300258 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647057446 1250 647056196 647056271
    0x30a050a0902090103080a0203160303090203010b0a230a08030307020708010b10080103110109360e0a030503071806090303023f0f2d1201050402070312 67
    0x2005200e007000580e40141400303526404d6071551180c85d00003003910015031104020050300a03403410840e903611446a034009c614124540706041c00e60745a030485c1e03801160f60320f000f444004005038115100741d0500380c904100065460000d409010160f0000405000000610035002d0f03000c2498419564528002c0c0206406101480581181810140e00040c44030006100044080c0d400880740c1d01c2c149801141c9980b240c2c074103919007150115074810000040b00360310100380c2e80c1070790182d1440a43d100b04000d0010130800b070b49400c0c40b844000c3c204680000041c0195002d200c0c400f0b841c1600c11980f003c40c0d6290301d000b52030250640001e401500c98511021111241020b9440305a1130801190003e6115225101c900261080c503c01046909200c03002c105503905028110480300250604ed02c104910315940e04034982c5c03020007034012820080403903510075100702d150450b5002d6170010380e9800b031800e04035400c13070001c500d15051034102031060502c07011195448200580003140040103c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647058696 1250 647057446 647057461
    0x60b0405190308070b0702012d0b01080c0d0504150609021b1615020a05030f0a030615050901120603060905070306051e063307031b0f0f05031b03030a05 67
    0x2001d4440104030300000c00a000015140401180d000085400045840c1005c20304d034000012038044801c0c54004d280c4012159902503000f00f00030b4000a09040c0d0039410310030480c01c07242c8600050b141e2040e4549001c01d0410500c403054460300942c3c02000c100454407507903140080d50100344208074116890100c101c0031400070601000c1410000c640206444c68a8100030803c0712481c3d04034194041d4445200c0490000c0c001040d040d41e048103920782e5a25030910140454034a500500c03001007501c80c050240641100465000341c1c3d007401c0c000101019525501c2c090202a0401400c450411280d807040100004040050b203101d4101801690360300b0700d546000c054204010540b0145031070220b28142008402c4a803110840003100214486101510300700c05080c80141c004450000b400205242d448401c0d5079000d418192524210015611441ea1208031801c015181c103072100c90324800c1143c10006c0b100c201d0b5480c40c1403104c43c0c454150f4962a0340048800007240ba0a00300020300d071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647059946 1250 647058696 647058739
    0x207050906040b06030406050c16031206080f151f0603050f07030209060901081e010e1602070e011502100e0705130e0a0b04030c2316060807050702010c0204060b0405 73
    0x43d03040a00040c0c1595925200c1a0141002811050031110100151140b007000c00203c144464040c2c1c444500c911042600b180864110360b011002681205d8082204460007040395054401d80e012990f0306a19802c5a005551104100791500c0a590381000510345030550001d80c40f070088444000341654541c1e100341c0592003008007183d4070000c01c2041c05840d40c000d044590b000070f2007803081d204007440206000d65200b02a0403200321030704540b081082d002411035884210305100e10150031103d14103100021109010300440810902e41802c0c452003d200308010220107039005802c2c4a00b00898a0b0030f80c941c200c90040724043d5003d8031800c8a0089580070700b03590348488100501c824a01038854101f0031101610840c100948010902c2c04903c404130094124810302c9603404128000090741442c10443c1841240f11304400707142084065000704005600000c80d080c46035030b41c0b41c41d00c0101c2c4c10380d091403402540686800c1005c1003c0b12020080d0007035070f6098440303410702a8071703480341d440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647061196 1250 647059946 647059961
    0x1061e08011503410a0b0901060c021f0e01020d0201110301061b0503040303020c041802030a030e0103020d05010b180a081b06040806040f030201060f06091a1207020705090604 77
    0x154400b8440740c1180c002c0c0b003030380202c0742d401c1d070b8140c40f088a64000300548520340d0441d8000303808900d0301100300320501c0400101034012040150401c0084c0d603c6010400070001485072805100030f038581c540a43d224012010705080d4080c41c1240310803910013007e81500e015101c07560051054002c01c1021600502c10b24100001501101d41036030710781441200e9507852079280440c145c007403011020000e441000034102942c13181c0c000c1d260b01d00010040c44102d40c04680c14041c190036840c0100c015031000300d0640314191301850b0501c0c0909058006a0103481400410609289000000180118140c020b840c1c8000c96030420f0080710140343c2040303000f000a02445083d90001920003c00c10001d120358003c0d854041c1c4032908007030340c4034007450400d0401c407010741e44643c0d01d03070144042660a114500292807090009502a41400b40003400c40e0814026004007642401e21043d46011040c141d4403200c00103841c0c815249441a002501c482c400d00c46c0e9401058258045210307403410b40900362 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647062446 1250 647061196 647061209
    0x100905061315020a020106030503070326060d0308040203190308040215030106021207061b12060902040b1209030d060b0a12110d09031206090209130902150d110301061e0801 76
    0x902841440b000002503216100d2002035658401740000002c2e000d001809416029031100c040113108901403c0c505c458203843c200241c00c80400300050707592008010106540c040c0b800e40c0c2c00b0381e15480407a07e8030050808c855070701800c4804060405500c880c5030341c0f00e50700c00c1d12900c0085520414103562804280600300250300130311840c0700e083e408074002d007010074050b00000c25141c600184a0120030035601c00c0400040340340c4c1c2c5540200d6001c0c0110001004203d404615041c94801d80d41e0f160700400b89420302289250000c210384030020000e81700039224046042124940e5a1001081d1f035209036a01c0c004501c4084000d06c051740e051040064050ba0f06020910b41401810048001c006038001141448031700d203500300d080082c0d4800d40024000905005a0329010581082032403400c105103c541700e4104203007100107031104100030015800c2c0796001600c07114120f0180016080ea1240314240c10404000011031b5580711050f0003144000076900201c3c0365941c00308490700b101c00d000d02c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647063696 1250 647062446 647062463
    0x1b0712032003070c0b091903030801050d030e12010b010f0206240d1b080f07080a030c05030d020a031406042c0106120c0e100311040506121009050613 66
    0x1c00e86000000e000700d855015002507914040c40b6546403600201e154010a2803480040b81c80d00d45c41c20025107000c90841c00c280548a0035195540080080b00305004490080315040c425104050150703600c01c8400301b00070701c0e203810348507000322450003881d1980181c2c3c00108401740b80200e03640082036440c003410340242c01445085015801c5801c2460504410f6004030079004881d0100d40c000f1030300c240302e00d113055860381e94600e001c40081c80e06a144140e50620340020704100f02d01000000d95004090785401c2c10050001d15040c82c900b03500541d2402900c40e40006074404120750f043e808000d6440040d00d0340c051719103a80b028001140d001c42e45800c004080d00c0c1d10b400d0164200c20303041103d54540340003c905641c40b0394541c1052050344504642d40b4000078020320405c80da12200c103074030a4030303020300708600c0e860750b1110300306c07400c200e488e050080b07a607240458410740302c3e1003141c01440000c9003140d0b0158051030a20f0000d14524406070703038500841c40406d0303d4080c0380150801854000460 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647064946 1250 647063696 647063717
    0x612080a03091109070f020601081614041404030323090d0804020f0a14040501080c0306220c1413020910030209030c0907080106020f0118060f0f021b071203 69
    0xc1c0c0042055071015282c0c4801e00300c18074900d80d40d013807540d4458052550782c0600b203010002e01a1030320606800c0f000180d00014100d00070340c180c200ea41001c03100d1441480960383d1450001c200145102c02290039200700703a2080009140d0140c00205012154081012001001d410004590700041c1c403040110b410881d0800036651040401ea90010300050440c2c0c03821ba09900024001880da0b800b161814460f06030480c04d40c60148a51390040c41040003400440103440d00081d04d070080100242c68000c4000c0e55410980e481c85000c481cac041d800702e4410700c036641711240300c581d0194140d0010710414880c4078100e071405040c000d4a5040c00040e000213034150301010250080d422007105075405201d4ae1a4020299450000080c01049d56440700c07405035040081c02400d12011865036038003a81009aa100e030003a00c4003800c1940e94002e0380006085000c0914200a00841d02600400710b00114803e0004109004960400700300c1318101e07000386c0d07038800104101c040c3c880006804510b45610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647066196 1250 647064946 647064967
    0xc0105041a06031204152120180909120d0f0f0b0918010906090b09060a050c09040c210e07080724120c090302090601050c060a020c070f030609020103061208 69
    0x80e130760700c0d600c040e051068034a4042c0d03005c5003d15803604105200251035074403240403002344001c0f00c5090342d49050490f02d016400310f0403414044130190350a000d8000308000803c1e82805005582400c188442d02668580c40102810090300c02d4106600c0700c0c2d40390548090903050b00f40b041e40b420b5000604008410b544442030011a00c044200c0b4020360354880840e940010030038420940362900c10706200c1014100410306900e402401000c00c400d66217402d09010b0324200c184180d0704201c0b07081700c01082c1c642d124501103a198205040040c00d41c030444100d01031682c0680c000c0c45071900c0c4442243e240c40e90b03171100c6c1c03036403035440d4480c900341d4000b2020704072843c03062030102070543d1484e800c0c48200004174070400c5084981610301d00001411850f4203004501e42181030f0340d0400707001d103003442c1008004070920743c032448094880392505074006a0191500310900c8620020000d18100d1a00559281441d0b4050684442c080380040d01c0e041003c152000031900503031025410002043c10074076200c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647067446 1250 647066196 647066219
    0x901050907090e0a0b090c0307030b0d0c051c060c0804050f121902011506090302030c010507030e0f0307120605190c02070e0c07020406150305071d04110c0105041a06031204 76
    0x700b044d2903564075006104065100c5141c0280100c0328000c0c1a0359030f2034001c000400301c0c0d0010200f54480c48940003d003000c142c2c6c4c0b003403000c141d03001100d04210050300002601c0a101c907440009007418103103003007610145d0304034892602c202c0c050025500f4903542c0c49006501c4d42d00c080e4280c802e45400307000002c5030a000a8841c0348500840c000007994000e09030340442400841e60040300000c4c1e19030360134011424280103081c2c3c82e04080c24160b00300303045a83c0140142c18114040d901846141e481c0494075901082002c1c002c1002030035201552010303040040c0a0001140c040d04001b0402218003200300c168810101240c0542c2d000c0e00e8600d04000040c0d076003500c0681003941400c802e000000c0965980d110702d000400c0220160701242c81158005420b0703881c0146140c00340000400f40266100301040c0880360307500e0894001a00000716003040c11140078a00015416600e003404000070021103185181c0b40c080404101c40740c941d034240800d40e175040c801c001400c0340001032200b00524030001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647068696 1250 647067446 647067451
    0x6150f1e1305010b0a09120309030f15050112061506020309090414010c050901020d090b0f0a030f050c042d090506030a0203100605040b0d0c06110a050106030308060901050907090e 79
    0x18400300d07962101c0e403080e030300392442a001a00d50b004006801840c0d56080507515009141e00340c40000d0110241d10041d100794803510018099501d000200010415400c10401c40908490b07410001540c4900c40400010fa800304219551460001c203031a0021380d0aa1040c1128500da00035803408040c172045c80700b90032000d08201c51004480b10f030028001e03028040e0305c1d03c0103e682d56081d151000074000900e003100f190b0700b10f0103001c828081840240c0648088070020070007200c0d101c1d03481450700700c120b005122002c11601406d00d428140000d070802c090045c001c8130108078030f04080380e501c0407101401100070b51141100f8214110108036034015508420740c000402000c0d1440203c20780c01081c1002003a00505003070f90b560380c505214038030b031a12491482003010380c0c1c0103030022540d0f540d00c20a082c46000304001d010264005404030001005085080b55100c0300030b000c02c0340d880c03030f02820200c01503403401c2c030402c14400042940c0c20400b92840c424105a035031400214540300c455040820302 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647069946 1250 647068696 647068699
    0x605180619080d020a0c15080a20070c0e071d040f090807050d03110a14030406061d0412050901020327040c020f0f070f0b0f1b06150f1e 60
    0x280744000840c01010700c025140d200303203900a001468090719021101424a0f00500140301080c0a2100c903e50311404a60303000f20306240020381104100e1800c01c2c42ca10038000120070070b00026483c820003003209820000c070780210007a502c058035100e0058510641c00c0c038200c00224035040500c001e0b031a050700401078120564900081180f559103504280d40c1c80090180ea20b907011440c0141e42951610403000784c1081e41c0d031040c2c14003080f004002c1030072a904807600e01030381001c00801e003802055400180140000a00c00059400015200480e00c40844041c2e95001c110070038000303c1c80c050400c507420010705074051841e1034000100700160380c20304003541d8080303046000e03d103d29454030301c100d146909c407540090162a03a0495214900005d4140348030844d0070204082011000e428029029624075142158448408401c4ca0003d400b8115400e00482070507040389105c880041402400307410040e956141d080490014001040d60241c02e594111180c50380380e808801601d050300610160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647071196 1250 647069946 647069989
    0xb0d1505041e0b1f0f02060601020715050304050115031a0f0f010e04030c081803160308040e090f031201030618050303130206073207030b060d080d0f05010906051806 73
    0x6110303a1a0046034000880c1c2004a50401c0d024645e0b240c04000641d400a0244001d09000341041d25456500c1800d0b0b0501c01071240204c007250030800c0a4214001218008016070421666401c00180d6400d1300c21640d00c1c40300c100c2c0081503122080d00c50040c420b80503038111010b203900e400004660108000c1040d01044051610840000c861b0350042a00d4880146020400310006080500740b020b807003030500c811052a1030410010703600c003094404503200c5683c0c000b441da030303008201030505c04100458001c5000015481424080c201c507030744d060f00e0049030b04102200342c212604450078413010000d00542d00620004a0b040140000080b03000d1000d051241802c2c80c036640c2a91100204004401d00f45907901070240010694a03500090204100101007851454a07a4002d1032000740c41a80100c5001d462001072000403800c5070151030f40044200700b081030540482008190a0065440741c606020340000e4070701d050f00361141d21482c001c84140301c80d11400e081241a44400101d00740340c21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647072446 1250 647071196 647071219
    0x3170c030c0a11120d1802090f072303040b07020307030c02040e010603080c0102040303081e040201140708220f21020d05030d021903020408190602040b0d1505041e0b 73
    0x6030709100c002c52400b44080142c1c4c661031788140d1072065682c2e10b00e044030740c201c0f491001070250f070b900b01c40303142c04c401d9203586400282c840507022120400c102c100ca580030345107003210f455003140800c0158030841c091118001240c4076404100d07103d00c510503018001484c100c03003260141c0ba140d40700b515040400c400000d1500c0d900d903240485c2d60003a002d85142a580441d040050641022a05030302c101c0c0c000c40411030504031a40e03100309603009040a070402141541059152000038101e07400c00303070481e10b1300380c54004010441c41b544040348c03803900b40d100051100003800d110038900340c41928242c075103502e5050000807407600314083c0070030143e03842078000d40d10310701041041c4000d040202030600c015035148066001c141e03c03101a0400d007000c0520401040107040d8001c905d02840000f080c002480d02515424828041e00448c3c126504110001848050a4540741e102140103001c1c1905000c0341569141008125007808000403c14000d103001001d03200380aa100b09aa10310080c0b1898450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647073696 1250 647072446 647072477
    0x120e01083d0f0f0305010606031118012105100609080d030b060706020a05070611030103020616150f0b1816120e0102070b0f06030a02130f0605120a03170c030c0a 71
    0x2c0c000b03903006a61480940c01d09105011080c0034075000350185007824003400b0201c89100c5c1c000d10848071a40a001c20710311510b12a0303031148100c80301125034140c1da20a06448071414800a02e81514008017070011008009001806409a4821144410040c2c60301d52440d071021f03000b410301c5001c4254802d001b001301d0300c00600c01c1e2021313180308111640e131036880700fa161404004950541041c40c9600006000400040c0c0e03a80b8200e66244070310046c0808103110a18011441c618058003101c1303550305002038010364115a80c450908420300310707401180d1864501176088403101c00c0d01c83c6040b0411601c80030f200240035010804d5480140b000014000840103041822a0809013084a02d4080403050003d802c0c118807809402480880c007038a02c09a8950000f2242c200341c92039000240d4940c100c0c94a032030380d603510110040001400b80620b00040d08912619441c0401c411000320b000580031907070703103c0d80000ea6842181840501480c51315284d00e41c9281750031000e20307441000035410031100e90713 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647074946 1250 647073696 647073719
    0x50f1f031505040b070302030c070809014802030c12030d1e050633090402070b041406040b061306181a03030c06010b031003120e01083d 60
    0x59040500004050419213007025038a040078106904060042c820703c5001040c000440302081c1c2d000100a980303005040041e11055a4600301424000c07070741c200504007601412007400380780428007150155030007003440329010012021001c1d4240c5d00911401d28681021068041102040000c0303c0c14205c0b02060174041d1000881080103900d135501514016401c14001d0581041d0308456000d00c03201450a2001d642d8088440040c020085018261001c42e612044038100c84003d0310039969a004c505281003a140141c8080790300350b81030030034840500004154180650384c07010010102d502c0702d104020380c003c14008007214a9540b1000058845020b03c4151440c0c44020004603c484007081c1100c20b00703942d56255802508208041d00c0c040348003007002c42c10b551504800503102d4480180d072400c130305500c0e0001400100310081d410b2000c0e030450f0750654aa40242c1c0e582d402540c1e10a014110045d00c080f00103d0003420310880140001110005002030142920103c03010796581c04c04c880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647076196 1250 647074946 647074973
    0x60b040303080c0d1d0d020c01050f0a08070306090216020307050604150503041112011d1204051309050102031f05060a050a0c0609020339060a0f050d020a11010e01050f1f03 76
    0x175a510000b00b0b1014980c05200c4000d1028007400c009090500380c00d03100b00c90748200d4580c042003040510018400741d0003a4002d0f005040400300854a40b10402500207080c056002d099209101e251350000c2c1c0c600d40074080b142601c070310922011a018050030301fa01c05820292003280c521500c0c2814001544625800c03000d08080040082100c81300846100d03221f00c3e0881e4540c00b2604990704c1d8000034901c000803541101d40645054600d14840c80344400100b8083c50010700c0d550000062000f54840b06200c04031880c00d00402e288060340e40d90800096108004015000c01c4042c004803113000c1c01400044045400b5000c00308400426900281c14981001d04012400c18002030f0144c0c144800783c400400303081880c99940d0000d0389000060020b0086880341000c2107040c01c99841c0072840760058a101b00d07020300c0c003951a040c41c4803010703103511500380003a14a1343c0b0b41480141c01d10b00c140203460040341d904103641580e4a51100c2442071100d0502c0741c9031151035040d400000648181714a24 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647077446 1250 647076196 647076251
    0x60c0b040c0504090606170606100e0a0504020d15060504030c0306020313140304170c09010b0f0408070f140405040b0a180b09030c160f060f120515010201060b040303080c0d 76
    0x240c03050810200c1041f000301d40004001c990300074010400c581c0c0340c0c14080d10b244e50362030070301180b98910386001038001049900481e0304140007095407104400c2079080701401014101d05400783d107850310700843e4a8000d80c0300c0501060150034007000403039119402160400c100000c0f4408021035900c8040c900c07007562000d000d6540c400941000795421590080f205014050050024001e0900c00600807000600481407541c900140098401460b40700321002450007800703480d10140d440004501c548000d00c21450130f54455103241c1640c1c9401d1146601c84e0398002241c04007034a4103040301009004c8520b40e03000030700020904002182842070307518850720741d00d0029903542c200c12200038240b4000b40b03c0011410308080e0140f04d903000d00050300301590841e10300052001c0380307018211001050040e04000c082e1502080c44070061040c429072011484c2a0001d0000c1ea03951000c1074510310507480f02a00140e1440b000c0340d6150700420007003010b00d802913800308407201900680420241c4091821 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647078696 1250 647077446 647077451
    0x303080a061205151812091807020d08250f050c0109060609060b070302030d0906020d05190e0f0c0f030c030321010b040b0a0f1119031404060c0b040c05040906 70
    0xc4080515100b1a0b801140c2004240328503170b0f1007111030340c2c91442da000042460008100c4555548901d40c40c855080c004c41d040e442241807482010351181002a01c09001038403290028410083c03c51500314408401d4488425000380884110342e101034201c5d5070400c01108004200041100b4040e1488050280b600010480d00d414044e0044800c0e0394001c500b1070304140102b5004c66004016140d42103404440480c000c41546446d2009210341e80e28621510300e0a400d111005a41c0b0606800118000310304100c1801d401064a9580e040041000b605070702c002c00b40303140c50400c6c0030203041162019003102c1c0040c1d0034900007815500411071840001502080c80481c03c4102041c060050203c4400c06103032500713020b03540b40c45100da1603403e800d121100c0b400143c40340c4034080d4181880c4c3d16000756500b0500f0b812011889101d01841035001481c414049402410120121030846100b0348900000740c41d140c2e01d850340050024800d984140004800041e103031113901800c1001881150700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647079946 1250 647078696 647078713
    0x9050d1a070e031e03070b130804090f180519080705190201090b070302190f02130507030606110601050d081b0a06050a0c080a1a040e0705010e190303080a061205 71
    0x525244c000007803400e120b202840f145180c1c14450100c121000c07543c002c0340c0d4101135a2464144800400402001000702400040005683e6400d501060b40700750500400c2c4012420140070186200308803801801d15040440e81140d200e02c0c1c442e900c14500c0c800d101007401c0180d15200d1505040f25403080c1400c0d0440384069100315a4440310b21401351444020b040c2c20f0110742e0702c001b503031034500744030143d040803c3d11080001d1120300c409854890f42c2c000c3c440701c9d0b00d507440142d50340581010344071480404c3c200400418181d0003403584035584182a03000f0052a0318000800c045a204940c05964900c0c0030088021080c18420745065a00170403030017884000c3d004c1c9031290444a000b40310003c800d1074090000400c680c424015908044a180017080c1c002244101040502c2030200d549c2e40180303040141d0f1085080400d50070304807a0262a11900c420100381408441200040a5a2054400c0710103000190207010030540018109a001869a03140c0407101d02000105806546540c001a103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647081196 1250 647079946 647079949
    0x303020706020703080a031a04050907091a06030c0d0204051f02060106050f0a0315150e0901080a0201020a030305220b041506080705040e0a170a02010f050709050d1a070e 75
    0x400401029280b0041190520b940c8866526001e1740c14000200342e25203004110462469412501c02000200b04000601341014001e07511440c602c036890419080c0081c0304900b103250940424560405841c082c510359645001203020f50001c2d809554903503083c44003144580b150000e007803009041050700540081c134600013a161120580c070000810004218031043d4076031290a1310400c0441c1c2c2030100b203041d81680a044d41e170500c0d4100d0320714001c4c0c8141c0c10400691004141c2c0e08040c00390b900030703103998944134101d80345c0c84260710190140c1d1002c402e60000030310a501c070f01ea11160b10700282d0100070440341c103190b0306c0c2034003842a80e641410b0410b010520040707148010440341d081000708101c514200549071612030b144103540c401c5588804500c0c4000f018441445e0080d0301400644445042010307010540d009100a00c00562070000d40341c139220316602c5445c1c010485510f0301c000309442c2a0401010b0052680d08170f4040c50900706642c80e01c44440d10007805002581c56010490301c0030700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647082446 1250 647081196 647081203
    0x1416050d02061003210215070203041a04052d0a062f191115040e0f07051608120c0a1106040c0311030a0c03150506090f22081201030302 60
    0xd06110429030300c09001c04c00030b0280c1c040580b080b80060b018083c480b40b100010f9081100c0c01070001900754440b030401209590100082041e504004034001c101e071002071501015004a0060f01d80080c0050b510003521300c5903101802400c81d105400440e400004d0b008594424850b500c010003003441c4510103844800080c1c4901c20306001003080c1500d04055030484da42c1c40011041111140310314044c20070070301000e0301410106980c05401240d015032a004c41d80031680c442e00c60001724503100c1c80460030031428140c0b0719020b00450390340c0ca400d191403007003581075080605604403410b800800c1949101c001d880240381c8540824462943c88040c00d075000350072085c1d20800c40b052074202c10100000074178040204030590b84c000c000380000100340000720349001d01152000c0d0140c0e85450b000410080d101107079680c084c1d19520180041d44480b020b01c0740b149015142c03c40c41d5482c800010380509610480b0002095001000e041c00540584410b83c0303a84c03200000200406034400184185034040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647083696 1250 647082446 647082451
    0xf0414040f0504120e03010e0105090303070809030a020703120c02031005181f021602150a0215040201050702090c04090f05040204110a0503071b0209091b0a151416050d0206 76
    0x30041c0b00502c2c056840d40c1e050110040c000060042c4110058984e403006d40c0a000340711084c4000300541c0c14911170244e680e800860b0800002200d401c0010010440403050701c04040960b0000d0240b2800e50f0369624803401d10356400800c00144444110141c5c0c4d040143c02c84c800400c4d01d0000f4142810f811011040b642d4981584881c0e0000c00d041100140c540c0038075107030011a403070042e00c9402c8242006a41a080d62010f513000c02c40b1a841d50607401d00000400719685650201e40072030315144440008000c003190047d010440510004001d800c00c01d4110b03511040c0184c0c2d580c5015103604106040720380303114004884642d00c10400085040c1445052925408012141d003803140da00e034010700c0c40c4401448001048180343c9040c00c0781240d03c01c0001140c0d802800750380c41d446e01c2c4100d5030356000340034cc0c0100a031000180d5141141440c00c840415584641c00c290542d80350b041055a0b150040c803030303e030544841041901c3c48495100000b4680b00e04c2903020f00400c02140328001d01c1c04902 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647084946 1250 647083696 647083721
    0xa0b010618050f010c080705120a050d051308030402040203040318150201050a2f04031e051b0603073005160e0901090b0103090b0a06050312041d0c0f041404 69
    0x252043c100940ea04204444010760344442610358480c41c40c58550705001184140750505103020945980050700301d03010788810404024104010381d00c81c4c844d008035400c2d1030009858000f08101040160a0a40003076034054040c3c240303003030900c0094100300005403030341c1e100308000000301c0318400c4a10b0b42809100e4210b59112400d2040b050780b507002502581203404200c10784403040c4460500002100c2c01d0750000c54120155105c0020144046001d040c952041184d0b20f01885003c4502242c032601d4000c3c0f0000060001d0b415983c404405458030416000e80300001221000c3d04018900c44044020a85443d81808103050421590401240c02007002820030310221814070b031420340315045240e04441000e800810f0000c11500107070002c3c0303c2c2c1900540b914101c0310412134000801c0d007007071382162016802ca0b04007564030003c601d40c0d801070b401401c2d10b141048407144502c04005980301d41103180c03014006e00d080440a0b440606911903030099940c44040c40c016075492030644102c2c58040d0381c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647086196 1250 647084946 647084959
    0x40315021e0a020f0708060a0e0a0602070c03151802060a0926071a180d140a030807030e0304091505130606020c0d02030c04050c0904060b18032a030a0b01061805 71
    0x46c112416200e62006206c280d5495032414501c0c0c0c1c105003000005c91440c0c001000310b58524950815590484082c00280c0340400b04007240c1c00310700220701c10805420030243c0c00c4410f112040e82000074581c04070311180c081000d017440204104088840a065407141400e18100d40510510007a0070315603541d2060480d6080c2c2c00c070300c02e0509082021101c2d07440402c10038034505ca00381e40c00124004c0100b0000340c8001ea00319420704e0440c100041070010240680c9643c2e440c4c0e90340074400c90946501e100b9698946d00203110410a80c00c00c1e800c0522442c0a4895400001c0e0b03c500c00b0981d2078a0310740b28015640c1d01c2d1042005415011302580c40700d50010703540020410740076008a80c0c1c41c50710074200b40c021503503040041c052440d940117613120558002d005000742c0c1e030f8404149040707803ca43c107021000c01c03245130aa12070b813800043c041c690100400a500c98000176500100610034221460358140c00740702500300014803e00010f80c041d040e01e03120500c5085188010380580c0c00d96801690003103c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647087446 1250 647086196 647086199
    0x60f0b0109030b040302070b0c010b03060f01050f19030524100501140307090302040222050d2f041d0d020105010311100c06020301030b0f0f0c040315021e0a020f07 72
    0x240c1c481c1c1c040e82a290080c20101568666107801c0740751010b19884a4020f440c00b20f1903076812031041d0880503800c5800c0b0100d40c01303521000900c1c1d03058442032180b542d000c90303284004122407c3c2101ca0450720070950608007001a03507503d44908107540d2030a02d4038500c81d02c50500188920b800101e5400401c200b220310030560811001030110019802410000741c408400a160347e0700c1038501401566018005540740d003802509191241340700c0c1c140654071200c44401013902e04180746000c410a81012001c40703c42024074000708900300c07203202603840b0040891014550386030750240781140c8980325007a13181e04001260480c1440080341542c003c59051000400105141510741c090004084901c0d408402d459842a50342c29a4103400404050022000001388075056044078455414050388c1001c654500344110b03500c0b03100312849540114103103c24004941100426403d0701c0d0416001803405400300c464440e0703050286c040482290000030301d02d412641c14044402e64002c200e0040c400c45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647088696 1250 647087446 647087449
    0x31b05090909030307020a03121d010c1b110607021c0b070801080a0312230103110910120303050a0f0218030c01180308030a1b03020403050c010c0809010804060b060a020a060f0b 78
    0x21041c041c0c7c040c2c1000341d01540c100d81d800300e0b6072000c01c1011147c2c5240c030518520b500103034007070814894410701040401601081c15440008107803070240e0310000b140480c4001030200840341d045036005a80120f41c801140310000035251418440500510395100545000f0800800c008416000b0701600d8219804a1001a07000391840c1403c4540700000300d04800035842a190981c01d005014034001740c100000400d2001140002c40c0c6010f0503103c981440c1d03250701c044103184282d407269400c110404005200881e2190b800260803a02e100004240251122a001d05036001480881d10300026030301e1080a40c502004160680351003801c007403175107a1a500c083c059034040e1f0312018048500010000341e0000556102d401d1000e4000003040c0c41403001c0308010025081400111071501c52140c09240c650300810034018500d07844412641703025407000044800e1345000d0300c112541c58a81d00d036980c190b5240d80280907070101230f600601c28023505041070f0050f17904840038144100c0c030300700e81741d00c40f03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647089946 1250 647088696 647088703
    0x50109060516051f09171204060b0604150e0901060e0607020d05010b10020d090504020316050a0207030c1508010e0601140a050702030a0c17010606021c031b0509090903030702 77
    0x4002c00030030b180001039100d091450400252840743c600b00c8500003080402c0000703640c006528280185c0c0071140002c041c4005403401d1040442030740b001000c1e5400600001c015410042807184050138060078950348000403040b4a481040c448003040850321048000d01300003010500508040c5001405035845c0c00215006216402010340a40c8142c0700341424072400350042050710300003400c0480510341222000f502e0f9014021403c3c00254034010003d19850207000740c0c0e0180404004402c40807102946c00d0b109644003101c05019401000f20000c00304d404910100000c0c00e1030140c521113098090802041c0d4001608543c810000383c1d801c1c0602640c0c03184454440d01c004e0320700c042c1d07181c2000c2000d45041c003c09000030340c10301c5000c542104000070356244408485040403002110a8029442e6080c0c603035501400c001a48100300301d0400344000002c820402c021800c0000e401c850b03460416182c8a05521142e001c03801c00106410281495004654424102009503046090a0100a48 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647091196 1250 647089946 647089957
    0x305030406050c06060415061211030a0e100506130c0c0b040308090106120809010c15060303052814031816080c0a08030a0c0804170609010b030a020d12020708061f0501090605 77
    0x30454a45604046c0300c89a2b8000580380307112a8850780c40745030500003c0d015082d0705a50b45100c0c01402c204001403042801101d0007650001c00c80d515400c42c00d0340d0f00000300b03040801d040810580c82d0640010400b911a41c1380a280a9612031a19103000a1480d080d5945584001010028440004007003200752090b25003090342441c0082c1540e03114104203103031001010310740c03c0e4140782140001c10160010700030448d03149060a141001d1011140400210030807144403400b19410400c030340c8460001c00000d6900100c2c0f940b4280700d82142500040ca000b034102100303030710313903000200a008101d020002d1400780e503000c64912841c2810000895124002c008008080c820180040700c200710070141503802034000360300b02640208204a20694480701a10060306a503e070003685203203401c0208070898800d03009000604c409400341d541091425044039200114041c0043c04030b8200c2003480303404d004402d52400744144030418004540e020803030341e1101e4140401c40104005040c0c022040d940c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647092446 1250 647091196 647091209
    0x50906040e07030617060f1008100b03030c0106060c021c200d14030306013e3c07061d03150a0204030b0a0209011e03060305030406050c06060415 64
    0x141c0361504901503003d041d071600051803181d000344014219a0000500f1071080d000203d0b82c0100d80c480c035900260441950040400c5900268a1912800020f802c90a043c1901808483c43e00391103030180343c2186c000c1e81180c0f00144808104105510b003400801216800c0c150302070007101c0711076544003086c400e4070442e01c01c604c00415008241d5550f1500003444a0780198181c10454294600745440307900443d80c0a01150b8803059480c0f1712840088280c000c5c8211001c00c5508441c00000d4003011941851050302c90301c5695000c03090100c040c2e00034441604000c0c0319030070310411440f40103820101240e1400e1954407400b8204481070f03001d4200d60000007540030f0501290390041c0880d082c2208120f00c4040b90041c40180b04036441964010400c503402803030850b0040c1c4504250b04280d11903540308500064114050305207800084444407001e502c00e00300043d00d50741c0c4e541c401e070450300f2552290b0041003010071840034000040c400d01d940403a040f58104420340d540b5050356184d00c158000c0f00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647093696 1250 647092446 647092469
    0x306030616020f060114040e070f0b0d060302100816081012150c08100905010308041a12010306090c090c020a14030f04091b080c0403080702010e040504150c05090604 73
    0x102285000340001500340319400c05490842da1903c6c00c000d090001d01e4107040c011484c0145414061402003805c1c800d0b42c501840007040a4540840c140c600d0b0400c0101c520403c0e5038010010050703882c00207042c0040301e181c40c3c406082c609500c0c444411a480c442800a0140c200104105e2900032286107065440b4004400c2114010b400d08124600c00c078601e021030180381c20f801594070303501700070320303030301c9011380140d840e86c1152076100080070358500703100040807030205001c01e000e185c011507600341c80040400030343e50801400d05440310b0703800800c7e0f00688800e0383c3c6007804014010b201e007512001c0c0035405410f01040910740ba00940d1740135840340180046503140b4521075111000d004484c2d0b020469102103032140d44801e041e1000300340000344a81d0080440d1b0503a0010360040b4051807050400c204410b0034146140c603402000d80c0048812410040c4c118072104040d5900c1c03042c6402180142103594581c00c0b400d4640382140d100041da58180b007800d2090b1000d07552454100c0d4150741d08904403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647094946 1250 647093696 647093731
    0xb011d151b060103051905030909090c0d0602070b0105040504050c130f06030515070e030a120e090c130b03190911100210200d2c0d021203060306 64
    0x545018095412510a415510100d120480d41c00003126410f032401401a244036034611500540e0314209424014000d8205000001280c58001e401940c48401c0d01b06962601c0d0400d4009403550f407074240b049848075804103829041c0426081201d02412041e94100881d04007500d40d16600c072203844d1003034828400c0040d4040c268519803c070500061040a0a00030f0079164a005903c030300810b4a03268a440c3c42d40c0009100078070941d04a03a1049000d409001c00b9405603c4480102c0442e84c41d8205200015240d0b00c02511040d980b40e204d6100c04015980b00c10961030400d44420407a800f90301c00100500034480c002906d01d001015003900f107600041c1c6029242317030500150103200c155a501c41c44c00c44240290036000f1540c1c60b114015071301d080010300d4102d05540c9518a203180c080b0602070f014481601030b548541c2c40011040040ca103003110400b00151200b1240b10346c102a83c083d40c1040b541c0c04420364041102c01c0139801d402c0f0101e03046240c040042a1794040043c1081049000520b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647096196 1250 647094946 647094979
    0x507091109060d0914010c0e09090d091205030c060c07050d110d050c010b04050106020102090910060801050d05010213080c0a05180c0a0c17091804050706030e010609020c060108010b011d 82
    0x2010607043c000c00002c7c4609018404068080860b041106008081500016900d820f0214481d40c100106841d01513a0500703100c0c4162045503002002ca45611080007030754030151042010521a00e150cd44203996050755180190074a0100c542070401d0124501000c0880c1d40082441198080c03d0b1034100c3c0c50b00744040c410b60142411403c855040742c40c1400124910303506400402d2521801d4518000548400f840195090300d28403d02d0b001402510050000703192030418030190701d000b4000941820b0081603003030b80001850f4441400b980c0144030803989401e144410000401045503041807000c071040b400e800b400d1008082e000b0700d100010301c501c00c0394040c1303194032207071500500c000880c00c0400708042031030740c8030324440707071040d160500055110504180110f210f40d43c4000581242407801b40160090700041450311801c0d501c1e00f10114101c001480904500f4940c00000c1000e94504428182110011b0400c41d0402000c0f140c058085403401c000048800b90546021b105201181b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647097446 1250 647096196 647096213
    0x30702010b0a030b0709081f0f091e032006151215040606050a0b0d090606080a060504060f020f0a0e060409020d0903030e031611030312040507091109060d09 69
    0x100c1c081c2e000200280c0401400501102c2c148900d100c0d84550301500d4030f407104c00d691200003c030b04021543e0400d15400070040b064011500041041c900450601c101da603400722034010747c0d4003855081542c42c5081080c1940240b860030403040f855441d03541510f0902038551261401001c03107007200e1035040303c1d42c000d803165001111965011011b41d241445d80121102101d80142c5003594024100304011440b450100e00d4802150401d4003514548542d180c0c856018108403601a18050342d910700000c1c048006000c500c5d80d141c072131000001c8030f1400303107003079001c07075214600100c1c20510520046189051803001c03902c3e4002ca604100620740c02c0000040d2151141e5004a148540049070340304544030307a03801c06040d00c2d02c00e407403d00449541e60140ca9030b070f024001e180002828150059070200398070000740c070050f82d000b4054a1500880d03103c060028035013604c08440c150301c000e1007006000700c00c1c800c1041d240785d500c11007840c047c034070800a4454050345600d8494076690f07403400010441c821 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647098696 1250 647097446 647097461
    0x22020310020a081504020414040f090501020a02010e1509121b10090b1f1701060803070309050a080d09030b060102011b05030a110c0a0605180114042a090203070201 72
    0x410096695a40b8220024281c10007a03079190488072504516030b65600d081e0003600e00b999103407004a40c0c44040e480400000d0542c07807045440d1607036140340200c003040c028001001303410303100d8001280c5041c0740f90310180b900c030180d80040800c501103000d020402d0004a16143c040030203030728880e00d52802d10070b400c2c0701c010300c00d40111607407207080d1190729a1241d40c1c020aa08900a60850b8a582e8518003204802c0740045140030032000d03540c00901071490324003140030301035030000e000040b0f07581c403200041e01d190301200c810760224283d41b074108003a1501010f400003406465020b040c4091344183e010f442603002c4c2c000140042075000001e05181d100758000d141c4004400806860200000d002401c40c0d8410381d401c04d2018140f03114180c100b2404011102c0e28200e0000400840315682c9400300186005001e03202aa80301c40051103a0300400d02803010603036403819203195681004d00d448454460500588844035011aa40c6801c490000381804201ca9055401507541e9484481c220b0040420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647099946 1250 647098696 647098723
    0x1020919050a090b0109080d0c021002010e0627010f090219030807021e060d060e0106050408070e0915010f060201180221070803180406050d05060403140d050f0402090f220203 77
    0x454150508c4c07103174400344041c40c860003501c4080d00d425201104a090341c904a00000c455446440498100c1c0038100002c0c250742c152400111060f05084001425100800d0030907101c1394603145604194a0071001c400741058505001011152a50303985081d030340240c5001074854901640c1d00401c2d06800300c02d030f041c9100021301b03995480d080c0100000003000d960140341c4000305081c002280712405502201d043d1f44c8041d005164582c80c0006404001c08001c022a42c240122900c0d03002c14044114954042d1110300b541d2640603050550090840b0101944940340649050103100943c0300c1000e00c0d640d11500411682540d00181d105510340074031548460080e1100003800e80750300980c0c060701c0b10306850864040c0180c130f9a030420040309400d03000d0060b151380c01c0040401c000074040c001c2e030000f41e82c1400c83c2c981040200c07032240c011030b1001c40d00c0d00c2d220314080d010042185000d114055110000c0e607030f030043c07900700015240241c0714000782d010141420404001c040d0f5a040085840c0b1594 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 647101196 1250 647099946 647099953
    0x100504060f0504031d190b3403021504020f060706140a14130b07182103021005041e0611030a0c020f210306012001020919050a090b010908 61
    0xd0520f401884894038144000171254225221041e17440c11141420f038100755406074a00b80c07820400742d00f890754010301018414105005403450301540580c0c02c80092410200340e0070104810b420081d091080c5d40140d81c0500c06000c0c10400141d031047c00f12401d500e800d403080c0703450305428030b8030030010030481081416000b404000c116080c0190341005400003900c28090070340380c644000300030801d440e90800803d00150b01c00020212842001e40901d00c02200ea01c10395020365600c04650790900c898140d00310065084103070400d15404001044002d074820300704010351b1601d0344400f407141c8001c41c50344010490284d1138005004040d040340c111030031881c942c280c0d41d0521510f5503004100d2882044054041d00303d1288460f0400300c0c041210b500c05249000c4c03c034010910240490340000c003a2810f1020b25405405803403101840c50820256082c001a902d001031020004840d10a800b1840d5284140000380125150290004202c0e8607070f400201d0740501440041e203c100403900510014130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 647102446 1250 647101196 647101201
    0x30a030e0a0c031103011d0c091f0914071b1205130e060102070e07020601030303150b0a08060306060613050904020114130612020301030231020d0b0307080c0102100504060f05 77
    0x1107201000107030713007000b14003c200c80c0f21140b00201240d9000400044541c001290030f4880341040c000242d0b106c190900b4004154220314203108101085070015a00c0710b544140032aa9800e03841c070302a4120485040100018840720100e646213241c00c907000b8030026403490340241103802902562070b0201c519000c60106074981c0d00488e660441201c10034010302c12076200040218500075441c0c060310f4103a016041d180c1c04c5031800e401815210039071054010050100249400c469805416001440d68552400b801e05600b050703d001c0000e00054400c1400702303c0014510844803030042110070646510425607580e000588004110368828030f0a228000786100e21200e07150078034801ea410030b07290014000c10080078601280801d0200035000800a10040140848104900c1b9400b2280300204e20b01035240c50480c080ea0805030110013001d4032400186280d143c10301103840542a03020082c294840c8200c0000e5403000c90100c170018072380d5510302003824411190488071810118000a00c02c3d0b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 647103696 1250 647102446 647102453
    0x2040906060c050d08010608012c09010b010905191703090d080319021c09140d0c021c120815090c0307030f092a120c03120809030a030e0a0c03 63
    0x10401c02c50803243d5005100400c0c0d00c1e107001d810b0090584101c1c0d5a85009a0700301126503905a82c10356100315030702d86c0c1480110850500015181c4958140c000101c2c411150302c001400c03544640d0441c9125004a04100c03120541c200e610404451401484142d00d81461940904620901d180c0b25008a1514060001c0c0300a00000714060f08206d00b280d84100307c1c0741c031920301f00d018545204144c0b4030030320a1400b1038802130300609002030080c6066030000e07184402080c9170501c51540100450907410340182540f426980c1941075000142c510851b41000d951151440b811160a00003808411808038042c101c181800340f00005002d400c3c0700c0141461100c1d807503190000c6a0402c0040d0604c00784482d140918010003003050b90010402c007001700e10307880304040d4003074071811020b0f600700c0381c200066480303c041e0400d0704160281414080d142d00f1070506446030b2011400310024404a64180004100008111204c1c0301c01454001495840c90700c0503420000c10890191604e0041c90020060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 647104946 1250 647103696 647103707
    0x201090201141803120a0801080105010803162a080c0d050309190806040804051002150601080705070606030f060b0105130b0a0309140f010b0411090d0611070501020a0f110604150204090606 83
    0x20290281c587d038445070b9072500e030075090f92400d0060082d90703003060060307940140310406801c03680340c0b040001034031590301c90110340b503001140003aa040504100008201403038090103e0700c0e2049055501c14820307a05078542550300c0c800d49911030b000b0070780c01e82c1d0318030260500e0002e60080c01840341914424101030603c50b0352604a0f000b0640b20311031444c0d91480c1c06000103455804100d4800040016503200001513032101d01c014800024001d0400055000603a5031048030003540c0324020550942006050410171261307552200340c103200b020405a55003400c640d4825017182c50341541e4954414141c2c00c01c40c043d00c1c900200800403100301003500c000760360104000a011003024020007007100010f0400054035403c914030511030030200f080360010704105025441c01c60050782c0c01f00c3da100d003003507201002c0e600c514000d8403ea5804580c4c405030503400f0840a10140c19407034199200b80900b2100b07604c4a0000d0001841c0c500d02041d8008440e034a50152002001c082d031041000f6a92040040c0c40d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 647106196 1250 647104946 647104957
    0x3020102120609090a11060c0a03022a150306031903020a05061605040509100f031a06031506040f060f18050f010609050d050a022e020109020114180312 67
    0x1900c159100002e505041242c2024407881303103103000703000208164440c099400b00e10400036420410410101400107010040920082d100340d000708180c403600205029050b03188801108407806404421300d2655502e11079882005109400550b40c1c1c0324080080d2a001e140c84a48039409480c10801e001d05401040b14040740b80075400b918000c0d543c20440d00c8444400c81a80341c0443c10a000c00e001c103003014940d071603102644d58120507006856103a82100d1060385c0d8801c440445001d140c5070f00c1c040184080c2e580140c429002001601004010141d01d503000038a011701aa42d41c41030100c3c400965002240100302880760400019106c0e030010000b09a0300380c00781d9805040c00041844450b15007209812145182d0f0b951a031941850b081100a0180700741c103540f98821405420b000d42d07185824100701040c403031091100c1444441d007002456404511480a591400862a01503601301c00a00f0100d81e203200b0680c3e82c1c2d4800740c07151206882c201c8040c3c2c1c0511840220140070480c4200410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 647107446 1250 647106196 647106217
    0x305092b0b151912050c06040306021b010e0709020f120a06090b090f040311031312020f0301050411090a1409030d0e06042f1c06050603030a09032d03020102 69
    0x100e203000c41500f404601c0c2d40180044094984680c0100034020f108050100024070403c15680000307102d01c0001c00580142e002699080c0c1e000501500c1e0440b07000c003041d4402d001d43c0080c054200f99400e0a41c8804062081c00e910715000610140e070002c2d4030302101d00c0900c002403087c0003418441c2510000341a14003178454050314041c1c55034800e280107580f241c400e804141c01c000c0c0f41c0c1d50b80d0b501100c02403403c3c0a14040b9100c140640c4a820a80c0c862039409002491380003d007441c100d004001d2040301850685020764900380902c80800d447c0440085504c5066503110710a42b0b540c48000010441c40c00c5400780001032005001d10f0380b90200040400e494118820b0280390004007013035031a400c0c00d0320010080e60201498002d111000040510342843c40110307058060f4603400420158501d81c10341c030801b02880c006000420042e0301c211034100704182c005608001c00500042c11208841c04040c1810b01d0491020035400c0624110800101d10b0003901c0e007540b241881c000c5d010350004107006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 647108696 1250 647107446 647107471
    0x7081b0f01050a0c110a0f11090a0b09010e010e2a0f130f05011b0c030b0c030717130314041e0e070305040215130f1706060d0305092b0b 60
    0x4042511170460349850000359006001c42e07400c20394403082548a550300440707644180c2d0110310707402c1d41ca14080701e02c124031110010a150024600b081402e40d4140c02c4001034a01002c014800c800c00300480c603074040300009143d43e110004096201c080c550680303100300822030004068a421401d82c01a000361a4600c0000003025211240d20000b440d480c0105c50018800003412502d11f03c00310b0003440c40350301620f0010003003a101e80b00c01c034020710100c4a04d00d01910000030300c048130342e0008a00c40c0403004142082414100000c074122201c2000da030140400c148070350708000740c114500485006244c2c00340140150381035150710504c5829548110a1004880000120380c6802805a18883c5900502038004900b01c002c0d40083d43d0080c40845001d40e0501801003044001e140c400000b8080c0e901900e901c050000c180d8510b031100c0100341c90f02420320703c1000000aa000300c15a4400c2a04455001001a070720041c402c2e490200ca9040703c035050f0500d111030034400e440440364012040010903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 647109946 1250 647108696 647108711
    0x51c050904320a0624120504110d0206040f0611100905030f0c21090a0503011b141303120909090c0306020c151009061a07081b0f01050a 60
    0x402d18050b01016620b084400d000801d000c140489580965110710100c40009809840e0384070300b903601c052580002c1022502005035841c0d560444034441900214100500072031a060341c610710710012038102e060040b80c4048c540801c40d03039640c050700c000d0010403280e030b60040d540301d00091078840c4590000e4114000c9424410030a14580070704216542c21100540c07508070391040c0d44a50b9441000440d040d80138900788070001e40d10703034852000d02a995001590b150b14200d001c1100d501429806144a03a141c100049500700020004056104403410715110016070b00140100c184a800c0000d82c401d01071240120800c2598404510701c0103681e5529000c182e02c038600d9904a0701c09800280c40a02201e038204000b40058005100180703000065400303d42480d001c0c019250416100c01d8400c9a0001040c0204e22484c8942001444142d46290704000740034942c00703461248410241413100d000031030100d001109000015050740f204100c03900d0340c40f1001041d000b45019181001a107040241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 647111196 1250 647109946 647109971
    0x3303060f0f09031206010807090509090703291b1201030f05060a0204060c150608150603062a0d090b010e040605240105181915020d0801050d051c050904 67
    0x1604c0c8404050200414030391201030040d903211a0040c0054100206004046129100c0024590260164000a100490035072070400f00d5550502c101034042c401405581e1020741c900c409441c0c000d6a401e044056060001e0348280c5a88103540005101144440000081003400d841c404800c80c0184144c449680391056408240d125900c107a20002d84004003d1011611086100c801c0000003140025000e5440303045a080925a6041480c002a400d08200c21030074240100c40e40800d01d00254664089070004000030b100301140700010402c40495501c280600c2035100d540314542142d0703040d045684d103013000c140c11681184c003100c1c0e1038100804034080c107800c100604040b0754070352080d0b5002040b8100450f140d800c2003507840c401c10315150000085481e42041400c0301d886894100702c99905194104000d03480c580b12400855001d2421401d81070f91001c5900d05407403046861140000075420464909040c05162070784840a40490410182c3c0000c004c00c00d20781c040d0780c14001441c4028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 647112446 1250 647111196 647111203
    0x7091803080106050a1206091d0d1b0c09090b0610030b0a2d03050705100c0809091302150901020d050712110a0f0c050405060402033303060f0f09 64
    0x12004010601c05001400050300500180039144014680f071003440c05440001e60507520154000103110343ea40d5582c0340480551020383e0821640e0400400603851031000003411402d10712554520080300e00c038001c0401c800d104a140c02080c82213000c1c09000418100480421400d4a14512881050000c52134043c041d000f42c02d800c2d28000c11110542e03285c1340d88100c210281720380b17101241041f501c1d05007210304545405009940110010180c4030b00702014005040c0c1002c00c98824000035010a500040141d811120802d90a0303480d54425180c00700c1d0035114040828000b5441016024903460050841010380500e00c402d03401c441c00d520b0100020380f00740c070550402404842442403c941c0c5103000e0403003c404030265800300c88050565449206d400704002c44121181207118004101d545414001d203900080e007210113f195082007001c0c905041054690040c0c925000301020220008805204c41c02400140075603800b441e00150602c5105801c990380c071140c90b10f900200ba217068001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 647113696 1250 647112446 647112491
    0x22112061c030504050913050a1103010905010614030708060f0109021305130e07060302040e27060109061a03010b0706360627060e340501031107020d0602120403020709 74
    0x805010a09c0c1d0548401180b038050854054040d03482e401c030300002500910564004040d42001e406480120101301420030303407698800b245c41c0e44400140242c1d000c400400c5811200380707500c0186d40b50751501d03111500040640c0015406520a2680d521380403150f000070000b051020300340c9070b10980f00d03e400d030100d0145008043c9402482c50000b2134005001900080324a12001c201c502c207039a00b82c86030b140c14000d8100e8440c1c07984859003081070460201c0180324540320324840d00c2c195810030784078a0003400b5500c0b0280045407a400400000c506440640403c010180f0701105207200d10b14281100d422404d0007143c1c02440d010044c80c0c1c40040d1406002e0a1402c0c000101140a560300c0b4100901607051684145019206600030700d599005543d10449410704034440f010001600c04103c034074105da014506040c01c01100144c0182103808503000aa41140d0000c04400c450030004000d00410116044041c03803002808141600052420122200c41c4011f1080304014070700b4940d0364040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 647114946 1250 647113696 647113703
    0x905010b0a230a0f080a0606081303120c05120f0112200301020d0b01081501080c0c0111070b091e03030601050d0f0f0c022112061c030504050913 64
    0x1c1c4481d980c1248030b04541a4215004840d8420042034844901c46551041e403440c0c01045072074041c0d181654214140d00e030301600407801000040d01d01400039202000c000c14048804202010b60400c1500440c004003600c040040e041054510f00d50000d00a5403140d10000c4c080003140d00025051812030301b50034180d80012114003400600f5071781e07044009a070220590a103a80003802040c058400748080c2c80780f9000300e00d0200b48219900c00240c240180030742030401007031140600000c281d03080b00c3c40a401051600c401640c4041c100840e500509180d48281c65a10b4009a072030213101e4408905405100361360240c600c01d4507420003c205000f4040c0c0072124a40050000400941c01030000d0850b0082c1560702080004e004c0d8100c40455040c203a41e02c8029541c6c40d0b0700d030304080c0c1c10820507240c0400c0794010f0b000000115036501c0c6900a10700c2c0c130400e0021040c0003928640f2980c2d1101e10181c0c81c07404050307d502e10751030701078855005806860300401c1c0300e130000340342000e1640009050f2501f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 647116196 1250 647114946 647114969
    0x91905061909030533060d150608030c06090601060c120e0d060216060c11031e090604060509010e01050a0839040e0705190809101410090501 62
    0x80c20a00c0740062505020090015103180000415000c0c0f160307000c0203080400000c1c0300c821040c5a10300c1c14042c0c203440b038603204040c0c0c2040721686981011400352a005480e5001c0107001781c00c02c070302800c0250450483ea0201080482046100240c56400340e440c005c1500c103143e88a18045404c540d000001410409541c1041094503000d9101001070980140141400e00c00b55141c620a9030320a187c5111900440b40c03680041c041c0c43d10071082c001009242a040803c88001ca13540c0c0c1e1b01802500238103501555520b5550308002c24212003e184014103000c2c1c80359550030700504286c1024240d0750200301110f844030710f40e40c810b0302124065440360b1610f551a488050448417030681a00804146040d40701c03186420765a019812102c0d21000210581d60341d04103405d150f6014030181003901400814000300425000c1144101d01c110907911740a58141c1e280c4000c1444d106403c0701440c00e05144c40da000e40312410a0550610685944100840caa6071307400703025081303c4003403052035913802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 647117446 1250 647116196 647116207
    0x80d0e030d0804240b10020f06070504050f2e050c060105061315090b1303050106051c0807050313030c030209060108071b020a03020a06030504140102070317070c0b040809190506 78
    0xc502d1148004050f45004c0e00069641c140c00200340a41d540307091040140e440a4490104d2140030081c05907c90303c82d1a21a051074035001c08640d0b1440c00d007003c2c43c0306060040c03180000c00c103ca55011034211103080304406c0d400700032101a2a99000c102480214024080042901d0401d0341c1100c1090703a0100307048451515000c0c0740040102000c01e12030420044001c009400240030000e024070f0205506000307000c0b851440e1103821941543c1c003060140501c0205d04803480d08441c2001078203030f00000350315652585480c040c1c1c1184101e014681804041c450040709010400840c08262071080e1401601e0b03495407001503031626000c5410900081c6007a6080c040f03880003145581b02148041c003000d039500e4036603001819201031a00400006940e4604010a01800c0d0000c96000c60704a0001c51402c00aca860041c500b0740309002902100d25410b01080380c44d440340a45078002c41c0c100c0d0401c0111708240c503050040760710115125205010f000442d00841d240307007075010206d03074004080c1403608 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 647118696 1250 647117446 647117483
    0x140909010608040b07030614060d0b130f1802030304061112030f01090f09020f1507080d0c0e06040807030609080f030a0e0c0301180b131b08070e090a0b10080d0e030d0804 75
    0x56003c14628044030751142d120070300700d886890318800810a00103000c0780340c0304010504422284482054940514ed610300d280150b10301100b140e00b911f41610f003400c50075814040e4a80380c005162801d5510781c400104002900103084003850507210480820b10a80d00c2c07a00c0f00c00700340d40b8601006036102c2c81290b04401546051480d00204c003d4424007641024200d850b03a500d1340c1c00051582000b9134441b0050320b40160b02c9405219101005c542c007904060400801503540c4603c1d0000520703156840140c40140a000b8054071210742030481944d40d85c0c0760441180000d84034000c1c2c4206a072090300c0310385002c0c2c81e040c001c10851203140704034030398040b0964850004103074000d80386107000300c02a940f0001245203090341c3d03040d01c03070300c5140d40503001d19090007549000015807080d0840a41c200901040c030f0404500102e0407900100c1c0301c3c6075922801c801c4491110305a010f1040c600c43c910840380724070341254442800369012002c0c1c924000d0103074816250901c08980048c00a00c010f43c1c1710000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 647119946 1250 647118696 647118709
    0x1403010609090218061311040302090601020a1a0a0f0e0312060105090d0204050a11031e0c0f030105012006090a0c0b0c120a0c20210c01140909010608040b07030614 72
    0x81701c002004100140c0103400d10200f2a5400d2014503100710740054284150300b054808560040c10a100030031940c58076868440b000d4203200070055844402c100425100081034001c0a5002400c00042249800b04001c03207a0f80e9020006c6240241c07100000941c03d50f00600a5480712a0b014002035a10f041a9007004000d140007003256601541c0c1303440446940e400c0e50301461040c596104410302c8403070011007402c1c1ca000010300b0a18008810001d02d280b1074040c0701640d0440b5820300f00780000c00740003402003802811105041a15228010410120410024103c0340160244800c00c0d02c1a8656406403802c1c450295800c805030700c00305801d00f180c0b50802c01413107081c5007803400c4c04006c6040d60722640300b0b000c950340c9682d900b001036026884500d0301c1e10104449028809030500e104051061103515901080c0700e06051001805c50000b6005a107030846143d020010311202d22503848960180042c682601d058075000741000014039a24000c0c42241c007514403503226494a04400700c1003200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 647121196 1250 647119946 647119951
    0x6100e011205041211030712031a030a0b0a180b070c03170a02090126011e090204090204080d090e060f0607050f010c0813080301090908040f1403010609090218 70
    0x10840752035005000030340140701c2e10307000310b200740c21013883d5200c800c1c1c00602c041300e00c030f02442454004104810010300e0000707800009000078200418940a0200132414076218013800035010301602c6598020402013013043c500c1044044420001c2c9010804900040260004000c10344812040418960790142d505880c0c4d03075121313151110448030711000200b00404182c0c0c044041ca6000b003007140c229a040800f01e0140c072aa1a105402c07904482c43c04107100c0010700c01e0243d408402c54240d80a0340800101c00090075101c0000e41d80c4595412a1030001d5203c1d10840e0001d020f56110418600d21440d01482100c180c20b4440400707844400812844188484600f940120100400400a1010b1100c5000c031050072000250100001c9000713800e01d00c00600b03d4001407070a1f6600300c00102940140c90540b1607104000510b600c00c2e1404002e0b40c800d6800001d24072605030710004420b500c200054040b440150001d2081641da01d4540c025200704078002036018000c110014905100c4103201070307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 647122302 1106 647121196 647121199
    0xf1512020f010e1c081b150906010605030106030b040207061803030605030c03030a0c1109131205030f0a0e21130e09061f0f0f0608070806100e 63
    0x4603ea141d440c2000100c5600c503c0c0c110600c89170b00c1c2980c507842c2d250100c191060b0384800517140c0c2d54040d0307a030b0485100c130414001203806c800820080c0c101c88458a4181c10759080c17030401d401a2241c6001c50380c00c03507400e11085020480364018852068404a45514120014280281a08c5c1e0325000382e4060740c0002c1209840752000021503c0d404100e2138007a0032640d1600d0802d283d840c28462145c0e110495900340b1038036184104203003401c00d100700b00d4048030030008241aa0301c0c1c082101d030072485a005800195280c11103801002552040e001aa01c40595601c8000d40d080d500303c0740d2281c4140045030358010052a00e4103200600041e042503c110b140c0303000c00e0703940c0b60030041041c00c010024840e42107500c0c03030306075154018005160900340500d0f03d65039124403c0003584100d000280d917110210b20200d00a4141c9801944040d00300344030550540e8064844178162071446 = true := by decide +kernel

theorem cover : BRFrame.Cov 646942446 647122302 := by
  have h0 := BRFrame.cov_init 646942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646942446 ≤ n) (h2 : n < 647122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
