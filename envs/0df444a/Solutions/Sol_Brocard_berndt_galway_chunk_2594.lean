-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2594
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:10:43.131007+00:00
-- url     : https://prove2.me/submissions/0e6cda66-28ba-4420-9b47-488ddf783629

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466366906 ≤ n < 466546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466368156 1250 466366906 466366931
    0x90c0807180e010e1509011a0d030804051e0318011e1803022d030304060207030303050615210c040f14010908100501060f1d0405041103030d0b0f04 65
    0x2020300360340786190021038000b5a400660380101040b0081d01d0603402000414020101d03000b01850040300001d0091008500c1da0380032086140b8aa0106c0398007030115194000028050a98554081c1c010000d94032075500c42c0c0d107980c546030741c0110059100e0304009210440e05400b1100001c40d440286011801c000001c450702c3c400c1d500000300039042c08419070611202c00e0041d10014040c680c050300c00c00712030030400400782608080d001c010700c00100d00400f00215003000000d9600f1504158020800686152401d0b002440043c050030f821007204e281e420003044541c001000710b00d03201441110002d00b1148249c10045001d0008080da4404000c200f01e090b0555403100b05603a0b18036502c0c4030703110145005942c0c024036544944c003103000e0380403158540c01c0d01d6880141250f203542c4400020484140e012524010750796140c4a104a021000440a05240e0310213035100d4801c1c183c4002d004150303000285180c001048034020117880b03900d041840c0c01d105c0c0000c41c981006443c10300c0106038600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466369406 1250 466368156 466368179
    0x2010503040f02130e070e01062c010302070204090f03021209240c010e0d020c1807030f090804090b0a0806150d0f0c03030c0201030c020d12090c0e0a090c0807 70
    0x90020b080005214030400030740d500c2124004000c8442e11041003111440101030b1788400c11840303000100b40d00740c000041d80900541c41c40e4502c600d80945003000f040c1d8440c5075149001c3e690780340ba04050303084c0580740060712070b407040707082150003082d0480703002c245880c1c024039000c00030347c150711404414040f24800361600b44450640c0d070f00c01c050708116005200349415240c024036045c99015801d03c00080303540b44001c20b01901c400c0e929070030b4420f80010f12050003c03420750380700e41202d00c810110003d0840ca1003988260742c2e54030144d1004c21010850380310006660442c1d04500c40d8540d80d40e00540b00c51602001d04002031272a1700c041c00036841c2c0544a645c000a20132030701c40c06031f0b0240302206c04101421200c81d40c9154044890400b0395203d007002020380c01c02580c22400300c0d28120300b2030065800011801c1a8640680d1192002d5058010790700140209400880f5419003c02d00030541d0178010703205921030f4001400005a400f40d03414407400303d4099a01c0242150803a15081c0444940f0030f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466370656 1250 466369406 466369411
    0x1902030304090c0512010e1b0703020307060902060c07060201020307030c0e092802070f230a110111120d230a15051c03020c01030c0e040c090b0319150302010503 71
    0x180b00c0001d41549884059809100d08140c0e05000c04c031910020401442840301907000700d882c401440d08400c03414072402c0843c840c050025026038414885e0800040090700102003080c80a0561420403280c48100d03480c00b02c041c0c00c0b00003d40d4010041005075545072040c03614442aa01d051030481d11000082075200c0406001c0007900949039440503071a00d07040642c429030080148013150b84542c1030400f14034072001c01070300300c0d82030402c0404200ea0310062903c0c8042140c48030302820286030070b0b0f501d00c50b04840312a0444d0603c000c510300c50701e8215080c003c0140704c0401d6501c041d5900b5190520004680400d4840c200540c0d0407401400d442c00d1651855078000c446500c0040d10b094070815048078098240e0001c0d9202d6221701c0804030000081d01c416145501c00d4003160b120001d1900150280c0d001860f034000050590a81e02c40c041c80c0c190400001c070419070800c003104507190386000400760700880c3e00c41260400c0480c140e003103042c3c520800b4207280e0010b021740c0d03143e811a400200207200c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466371906 1250 466370656 466370669
    0x703150e030f13050f0604080c131104080105091203070917070f06021b060a050f090d0c060206180c090109021e13050f04020f03072604080c1902030304 67
    0x1a200d101403140e00070000c42e40d0100c4005146515290340c020f800c640c101280c02442d001e81c0300c0040c5d148043c10144240e8050301c449001a05205101000740180c240003c441d1b40070960716980c0c840100201400204042c202a034008a01858103011080c50107001e502640c071140d00400403c101c0d90f42c024040800e0326019000078240c000f003440c041d842c0441030342201894411092000903e15000511020141000155156110003103000c01c80076000d20030603031000c1b410820110109980e004001c0070b06c900010304c2010b8508080c1c645000010b000c2d000300d8050381c48002401003074402401040c034807440840041446040e00c4020a40e503c20621411400503004200410101c034001d2580c59260010b40303d8907100c140f0400940b24466051003000d028074212a0040c5c518100f5000300c88841c841c1031032241c61a101d41074102d46c10396000c0044004c0513003a800070600901039980b0a4060b0380036031495910703601d50344211414a0382c1150b042c60740791780480030703940107071404014ad4049504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466373156 1250 466371906 466371911
    0x30a021c030221090f0a0308030a0c03060e0a0501061407020d020d050a240c0e030a140f030d0b0111010b09010303030e030408061807060c0c05041d1b030c0102070315 73
    0x403645010307480c003070b507507001d0581d5444410603070b10095100b840680b428060407202c02c03032609404402d100c1511202c0c0809802d51804100041500c100b40d002108a1130352840c000500c142e0301d0301c100c0c503000426100035291030b480ea001040b42a9001c6060015000c0d0001c0003481c02030594002100d2181d100d400901500b80c807800d6a040c05421b0244108540d046088910182ea5040b0448003034a00c2d4086c00e414a450300065040d203038403910841450000143c0205442c860681394480040180110440544506030b869568008244040c00b5000790300e0101180e10707810310001400c544002d280287d203d0303252161200f4256a00800d041c1141d03058100050340c2100b40910340d04600c15a00482e03020303c149024020381901e08511403212100643c1580d082c551100702c1180c8000240c00080d0420182d0103043c4054501503000700807110559201c00081d1061500e158107222120004031a015070030301c030280103810140300900d03510701c3c03d2010b4501c00d803c564030450304059807008440740c00c1d07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466374406 1250 466373156 466373209
    0xe071409150d0e06060a060f080613061a0913050702030315010e1210150602060c090103060504090303020903100b01020a111c080c01200a080a20120105030a02 70
    0x5a109044941c0240e10700c000307000d0074040741c060965514090b00d14500410006e100080c4040c400c06841100c81c010759070b0150f85813034202c1049800d03e180e12244c070005564003400200894086c1001c06000ca1040126850743c0b4500200200c040c2150004050941083d080007013003907002c011694020a00030341d414404c803480340125000b0780e00d00d4056401400301c40c0303101125040060b00c6400c2c81200c103000d000000c5500607402c10302c0414800e050141e840780b00411282c4c24404080d000c0c8510616002881d0396641001409486c00303d5800d50129034002074882060506003e0312903603a030b40607002e02c00361034401c0c0000e5588a1414000d0f10354489102520300980d02c9104010307404404042c1011089503a0800c100e883d8003400700d0841e5503281400c80c500d00f1080c0f030040d01c100004000c0150410382214001c0d1440e1200608281202c0c0d512050309452003035a2080b03e8001c0c03039048801e500c800711681d00c1c50340c581c41030308201c5c4254001200b00c0b0050307880304034900805010203003070007804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466375656 1250 466374406 466374439
    0xa110913090804060e03011503020d0314120f010303110d12020c0f01050406240303080c03180a11040e03120105060a0908010c0309030e123408070e071409 68
    0xe0919030001002c68100040008103a070340180705000b01001100200480d0300552003070313410b4014500c0025040300768280e402c03002c2409a40040c1c4401c10000d1464940300001c64200c1d0808030480b03c480ca1a100c800c014014540c4c448424200407000d00010300300b4480401d4081c19010014403549003440d000101400005401c0c00042403420002009000c90300301494848040c0c9080c0648400d01d9542c0f84200c21683e41c3e00e030585080700d4040d12a0b4140341c43d10b501e100d20b11350004081c900c0000c2c00709085003100000f08500604075001d10300500f488003ca40401050381c410030009a00e550041c440f1101c59692600034504440702156850364034409040e05880050031680507010395480e00c03c0345a0307265055040350304003034403d07a218150203031940100301c8940400400c05001d54030903180c5452140908201105c0074440704400103904c903030444c440300d0f5070079990402040d07074000c0041000540b003038852071078110060781001898184c00281c500c1ca08c4c0100440e0034801c1c2c4c05c194024088 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466376906 1250 466375656 466375661
    0x905061e0d06090509061f0b0a080606040e0916080c03060105040b03010e06010b370305041e2d050a060f0906020f0c0f0d0c03080c09190e0a110913 65
    0x1806005403d100514000080c07a450b41003c4514480d42c7c2e810000d103402409000340e0220035030310701c0081642840744043c0220741d0000300400c0142c00141c00c02010032032212602c401c078852948a03006116107180d2a00c030801c0182d441d4801807980d0302c05602c04c02c00ba500400c085065500a440010707004103210006401b42c401d03c6120303102e5000c0c500011502158181c000d010800c560280300c0481c0440003c8441503503c84440070b1110f200070450081150310036003040d03030403a01aa10150507013404a05280298400d40411900303c0d01c0074800781000e07050030384130091f41c2966241024004005031542d036100c401070403000300104e554440f6104035031a15840840f0b0150041400c540300c82180001c84000d0348042c9006000c0d214280c041c0e0401c0b0400075190150425540d03d902c1071400030f990640700448080d00150060005204810483e11041c80201519407102103407440103242c4000030382480e101821181c40942401c804d0000a8030600848620b444107a0340e4242c0070b903512509000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466378156 1250 466376906 466376909
    0x1020408190507090c0c1115040311181602071a0301051003061505040513050606091009170d110a0c0b0a0c0f0501020a020106230f012d0905061e0d06 66
    0x900b14a40507005d652594040c18006025124946902d00c0d040070b40200140b0120682104452407010041800050f1004541b1003418801904500c404001c2c0b4244400ca00710032600e034081006000c03862881550b0400803440241a4100d10b1211482c0e609140f000510050041601585103404011101440ae40c0804010040c3c3d90f4642501110444014880d0b8044c0c40303614400d182c0308100340740c0c4508030f01c9524040d1030b0081c0f0642c034210000301401003c1c40340c2d405200074000581c0d000602041d161400361700e5800c96078090000541c100038080e108110480048070650300072110280080d5011800c201642e0740262140e490b061192011241c419070260300078810062403c0c00010000305401030003880d00300781c0090010755242e6421460b54000d11012511204010880c5a19420810544150741106250401e2210348201140c0c60440090820700540c0103003550b80800c19610140e060003901c0115042d500c0c204488000700d500304c0361003d00030401c60001401c0740084600394071070f10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466379406 1250 466378156 466378169
    0xf130645051e0411040507030c0e100302040305033004030f0309020a051002010c0201060b0901090b0d090b100602010b040212070f050c0a030e0306090d020a1b030609051b0301020408190507 83
    0x503680f03094a44041560707454852180100c1c10800400c5045010b80110420407810b0b5440d0703036844804070304001c0d5070740c1c0f041c1c0e06c0414582e00304804008030313106000401d8900040c100404121080391a0604403100100e02d40480135042818000065800b00c0007159898182c0382c041507060140c0002074820140b6482142d1200006844006450b0190001d002d02c0c801500200180307a9200c036003001a03c58203505a00150558005210108940000c0c058501d2036110004810140f661065415a020340341c003150002d882d9420003200e5030902502d10030b01429901542800602c00000f0391960f406003d4005010b00c82110929141c41001924002c02d201000c503045020a802c1c090040480070301a1030203400f40d0070004041401c0000e106842945030f81c010401940d0300e44848c404610380089030b074110040150008081920390080d02d074602d0040340544603c001700705118071200d254402039802a40140020810742a01103010403030300c6114815280c4558080c50a142040429007041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466380656 1250 466379406 466379461
    0x3092f06031815070909050a0e0313090c02190f030e03060a060f0503030702060f0a0c0210050a1d1f0201090f0b1b040b090f13064505 59
    0x20000d80611002d10300c0c580441d40507500b40c81d014552003203201404a03103400200300c4d20041040160115848a40d1090384024002041c80c003644240c0e08561017818481c1d013007080b003074003400301a540388550002403c0900085c42c840082e001e004141400102024046400c00c40c81c0e402410300980020481002c01410b03500c1c9460040d4600c80101f040b405541c2c0d40c9021140702103034905000080f60710032038000308050b080c00005030700010a07a0049500c442005410301c211001178071002c1e030b04021950591545901c5215007000146280c10911800d4440c000c125908602034451030007505460000000407600441d441105038050154040700412009002a01009110035100a0303402641040140f50144504408a40f2240914091906250405c004007085440d1014085a2000c0b0103042c0803e168444088401100d001d1341c41440007200710b202040d440204509100b001148010039a40d0b007065201043e800800000e141c0b511181d034500102d0740000c61035109030800151520074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466381906 1250 466380656 466380661
    0x12303100f0509150f060f0a0b0c010203040308071b0209070302270907140901081b13050901170718180623040b0f061f031a0103092f0603 61
    0x9040040004440480b0320b40207002d04690b204c1c600081882c0208040340324103000b0b13190340d07040080d14206c2103801680a04808400180c808900c0050811055190001a143e10742810084e004200c02002c038020000d4038000f25100422101c1444020b50701a12046215954800c0540c000d00c14940c500d44100300b10701404580d2603003100103c00155081d80c5c142c20715140e150090b292903140030694089010280078100183d482641c2461b440a0505e0703030550030124078160303201c0e43e900c03034140e00003014086503092015041c0180000d0051910814202c4c1d4101286590b81e01c030300190007151030400c03601c5044002d50b034050b0855101903841321030703400c4034034001c0c54220014110004985050300c0b002600c00302003d00d858242e031086810002d0381d003650340c45014190510000510309035220030214400115000081540000041603817400200802c0352000803ea0303400c5010311034101030410400500141e01440c04242c422030002d200d11348040704604e101c808ac07080401c1160000c101008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466383156 1250 466381906 466381931
    0x40311011503081b0c0603220b0a2c03120604061e0602010614060901050a20150c0711130b150a080a0b010801050d030507050109030503010e0f01230310 67
    0xd10301c44c190311305003690280384403408940f101c4034030760015440202480043c030074171040448138028809030018001d422006949000550600703031219030401e6038440c043c040300e0541400c40f01c103001115071580e40c12001d150350241d907403082c6d0000241004200b0003081181c0c41c0c03a00010050030303060104d00b01d01070b60042d0541407201e1a100300c100540c02d000000444581d0b644106a02e248090005880c1818010041d60b2a0340030640210411105811584081400c500500081007000f0040d01c0c011181c81e403030034002c3c000136000c010012410800b100001f480400242c09000046d40c010700248a0105607200900c50254003a820450009081020035100801013201c0c0095460f07024450f11201c903207208540004070720030b0100c0c4c440c10051040f031a010302412911446464428070301100d035a02c003401d540121f02c00f1004118040b005000c0800794118140d4858070007a84551290315040789007444501804401e04050000d0800704c0060320103004900142a034410140308801c7c2c03110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466384406 1250 466383156 466383173
    0x90702010c090f03050723120f12030606030708180d12060602190615030f051c110d0c03170f09010b0301060807170307050a0f0302060a060b03040311011503 69
    0x2100c11000400580c0c011803e00204080202560703000001803400c20300b8034030120822200791844a201c2c0c2d42c82c0550b000c444e507a483c52600300c001181c02400c80c001e07440264074a000076401c0348000c405400d00401070b40b52612000c0d258060301c9482c140c082d40d01c80c041e140c40d500000c0e000307032021400303001c41009407250418038001e0300b40d040d5001040003c2c1d40300000ca80341c078440500015800441545c82c408600a6040070b101222042007454415940384d0300c8080841c0c000b081200c02c0d410040e2208050003c51000d003160000c40d05107503800042245009468200c440e10203070070f00400034148024103118102420007088122960341340e0b42005415240030301c0307003240c4200e007560034580303401407a04060191000300c40362070b0000c24100b8180f092451460310080040c030131a10080c4003000100710100480b00219008281580d000185410b0003410041c1c001e1002ca404da0405504026901030740040725801601031070051584488900d026014101003610358800824000b004001c0c8020306 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466385656 1250 466384406 466384421
    0x60207030801150507061a0a060201050a1a0d140a141c02011e0b030f01061203080f0105090402090601020c120705420f031806180619090209070201 65
    0x39110115140e982d6894600000c500c84204000690705001100018031b8039000310746213020000e280b182d40b032007d40c0030500c081c281d68003840c0140c0d190400c3c086926910300c60450400c1084007000f00003064140425400401012300a050a1201040d480a500180650088142d000c50141400e0001c1c0034482e43c1c924000c0f03500e00c084012015080185170051040c0c234642e101d650000c0621600709607451005184a00c1410f416024918176418074610030301c03d14000d030030b01440c1c3c400c1254003420020582080240500140f40d0003000500050b65061701c0300741d105604a460109554030710004074140400445a42d4002040e6060540028070109110058500560f2441004030403012014002c26400c002201c4000c078581c1d8000302d1880040070554200031240c0c1c0186050072241d880b560680c021600c400401c41019004100100c06005268020034440d0741040e905031010506501d950014104000303401c81c01100314400c545541000c00b07129002803a16520b442d0411002e400703010f80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466386906 1250 466385656 466385663
    0x2150403020310050f16020703050a050102040807060f05030f0c0c16150333030c0b0a1407020f04020319050420030604030804032109030201060311060403150f0b0607060207 76
    0x10f04100110290051044620a0011109244082c1c0318280c125000307800103010032085005186000c030107e241000762500c06449040016a0303280350001030350a111183c4c12040400024410641d400c5d94883c0650340c002118081076070150b291441c00b64040e100396810000c4500481402880724171030740020b0400c0b02d035030a495511a0241000c22412500a43e200615181c0101550311030754440c01d07818602030010140000e4420b49989400000141ca6804122400c800266149440f9800701000844141034020103007020381c0c90380000c0798008196007086c010342c3e0220000c1d00c185401040000845d0080504022074207046c2409000d8022404c443d503642c01c4081000c0c1c15508002410074415030301036841c4d1440e038540d680e08903800c40780304901034420071280d003519400070014860390035550300c02d400000740149181b405000390705e8030400c0b0520503102840108045821611880e03246d400c460b40010b0101402d00a09008049100c01160003010100c0c002e010481c442c0e00501e40e0901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466388156 1250 466386906 466386913
    0x31312051b010f06060c02060301030809030a05060a230103030509190f030c1e080303180a02040c05270f01120f2c0106030201050a03090614100e0c09060405090c0403021504030203 79
    0x17101d060541e1581c20380040290810300400040000c508440003a14041c0001000d4401c00303012516400e151500542d20840c409076152101e41c03e4002c4100f4442c0c080041d0b003a0b6585941c03543c3c43c0540310f4007a6860319402104101940c4800f4619010542c014200000785c200e0039070707100d06000c07120034480d0013401100f40014140092411204880d05c0440d03035010300452665179044180d8564064000364250641b0910030030100580e0740d8014200350798140c0e030303400341c45992603078106801031790941d03200040c0750700707201202c4070350711a00380c0d0305e680740000e00380290450100b04589005081c084242d401c803516003980800481051040c540000128840c40d02d000d144445183d4220760030303444020301013031081050240490081e00020070190040e200060001031005022180400c11180792440024088041c0f0048141d080708a410100b59034049051108400100d01e084c4149e000302c3d441040e0704400a1903264205040b2405140d0141c900101d00d03454043e0144190024042240f0900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466389406 1250 466388156 466388159
    0x40c03060e01091505060703030612060209100306030c0b0f040f0e1608010b0307140d0903020d091e35160e04240e0f0601050406050105031312051b010f06 68
    0x600800c4455590300e84d946821911304020403000d540030401c120217064070b03100300260394604410721040140c0a08d8015035100c080d02c0030082e0980d00c27120688141854000e040c004174000700000d106903800f03004c1041c1c0c4c4202e6403030311007081e0059500c15013500e131034420007003180070034811194010051030018402d03805503c10300350307034540090040e42990407041c800604164820007000c9200c14000300d003e8a00102c01201c9800c0d200c40650540150f44082e90070131200354044002c000810f81d04a00c0e480d42200e0401c1101c0131000340c854090b1005461004495a01d41032801040060752180c141a15140440c00a81c4400040803a6001400c0f05900041c402c00c024070014821350384510034041c0c991a10344070031103a0f90b90040603500c0035030342c0220300c90001c3c041041d40756000720708008028541c541000c11080e03903040d81000741000800c1c002e20a2030400d855000206541c0b05508201410b0b20160458060041d0305504480800f10618020840c03019801021403030442c103024400103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466390656 1250 466389406 466389419
    0x9080c0115060c05100b0a08030307081005180c07061d070501020d0504080a170f04090e0d020d02060c0717190e0906061c02090a0e07031a0a0e1302040c03060e01 71
    0x4040c640c9000d081c6400090551103000038036800240f08101c010501001d450719900e40911710340ac120b480501007182e4809200b0210310300d030302c07180003440308440c4400001c0b041c2001000844015169155441d00845c1440411410313810146012204a080c05525550071180c241e984000c1d104850143c0500c1ca48481aa44034804640c1916000f40081640c1c0741c0700c2da00c640b041003040c1001401450148005071101d2182c000905c000c025a04010410300002d294940c20000344100400c2990f00500301c0300b95a98022500036407144c11003500c02d84406040c1414141502c000480000c007003c00605a804090181c01001518541d580c07034440d0070f100f15013848000c21003583c40301c1e845401406220080241a50244050480d40d54094184030410000c0303034174003145070850a044403001041004040d414403405034802344c02503c1a6040c2d80c0c0c031002c01c1414015009890302e0161031400621500540182c8021b00c0b07502030003c0216844a2030003c00030301e0640202d11000040c0f6000003802c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466391906 1250 466390656 466390667
    0x905091506010e010f120609020a050405040e06011208070c1802190e240405040905010603150506060313050a120801090b06031b0a0207090f050103111f050c0109080c011506 76
    0x410f2410f031201c2000c40503605040c0e800b0f00380c0303c90030f005041d2070f150080381150040c0050480d13400a5103510782c4031420913080205035500400b0000c0154062001008550b21002c0702400c15a0800000c0d03a42c0c01c00c60420071715045554116403004110410f4007c000c18055000b8684110403818101070780f440010216280341184444580c0020f481ca48000203100d441c14075200c5d80c0b0860995460a43c1c1c0d01c02140030740707140b03041c1134071141d554100810501c818020540c43d0507105002c100414640300c0d001580c90700003d040c4504500c80100700c8020400c0c20021003c40980113191000c5e0b400c004d03800103000b00024010824100c1c10566810b113642011026a4010b11010740c02040301514020a40407079004542498210712403004001000e00303003445441400d40d8550400b1070706604504005c034080c3c9016400d0b41c020402012501415a00703206400c00c00746403894083e950700009031000b8094542c11402030041c00000610b002040415844100b201400781e20100e103c9680c0c1d0030a861 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466393156 1250 466391906 466391927
    0x80403060506031f050c090406030503070203010e030406080129070c14011b02090603150705190c080703080a022104060c1e03050c0f0c0102090a091e090804090509150601 75
    0x18942544c1803100075030300035500010750080e116040e9a04081110380060b042d6400c5500554481d0800078000055040a004805040035108011403600f4036000008046800c1489480759959220070180800b100030000c0420010b0150b00c6203031582e0a5003025114802603201d22903410603918000c07140340d40100c3c42c110701d100344444003103600c10782038080c00030704032005000300d6141c00303100c01e15000c0c0030a040c90b1034021651545c80c1505d402081c1083d408508603120a4401e21401300b04045c0010030a5080710750a6615203400390b01600d90000c81001b038007075840051900121042180030035440412010f00c50313405a5000c1c0b1190002940c02c0e01d40f00d04140400d040340c80302c00740a0981174020707040f01e03421041c04e00c68145021104185030a058125050155540c0d4000910401c6880c0c0245600003600d41c2c0c9404001001c001a008140314000c2542500710170b8841e51007000340047d0720140c40c010020250244090f01d0f080b40300984590b520000c000012404002041465114060480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466394406 1250 466393156 466393183
    0x9050c09060c072c0105010801050f040e07180b01030b0402040518090304080303040606090e0f06160201020405060c0105060109060c0803012318160503100e040515010308040306050603 81
    0xd28151200c424080158030800010800d03124040000404402540100030161128003004c0c04141000d02d00340514681a40510304001d8445d0040c0181c1d0b407400071150801d00e08940008812208041c800e0138101542c1c014891444031403a04419030707030150072080030001d0903a401c024920940d8100800c901441c0038031070708842200101c0403004010703030580380c20206900031281001e9840601c0e17440c41e0300860b0102c03412515182d08200502e07583c040c10206010348405004c040340c030000704d50342d1420000d0400021800074419100700703500030350441c1e02401025105c0740c1ea40100d8900d05000e41029100640050540c410001d20a885403010740200d55015858a286918010380007050210252400700444c0d9200d45620059842c049495800d42c680c20f110a581c1c03070140f51400c00a00381c110b40c1c1d824410f080003003228080c20460403000303507803850b110700d480380d1940d0070003518005402d000004880781c0b010020050080e410050400c491003405d0900507a03890b10241078441207548410b0b0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466395656 1250 466394406 466394431
    0xb03010623070318080102030408091c02100503130503040e0f0c03010803090906040f09051507050c0c09071407060e010b1206070f2601030203010f09020d0b04020102151f0905 77
    0x160020741304490550031142c00204007030885031a031134110708a0384103071000c0702d14410002e244070b080d00b840240c0740c03022004550f1201c06c404042c1c000c00c6070b0364920144042040760020010b100f400d200500e007051250080e0460fa2115224012042800c2e000c1e1030880c0b04c00c0d42d034000110404200d00c2141d05840c00e110243d070402c0e410105101c0403000140c80c580c1c0c040d80f6440c030f0504031a000d100300f03c0071600400052042d40c1ca450099a030400300606160104501007101c00e1595800080480c003070720050f50b080200d55104078044680c0003159552469000300080c5070005e018080d007207410b400c3c1c10340001700300880404041040c80c03007281e016061103030040d00016409500400b4100062506400e120007032101c0300c4a18030035640000c0b411807040007240e00600650900748940752581c41225010070044c206500051400860518000c100c8002c050004085920a004030033708490030004240b503500f80b400740481c1b18000c0403441c080300e1b0501c0030300040a003802d00030035000e8515280d02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466396906 1250 466395656 466395667
    0x1e0a09140f1312180e0403020a14031806031905130b0c042313020c070608010902030c12070e0a150206070206010e060d020a150302072003060601030f0f060b03010623 73
    0x1628030002480e44d10020f10b20110000900140f0401500d00c00c0d8860341c00b900845000d460400c048a00451a101440c1d000b07000c010000341815220b08114001102c40c40e0301d03981d51800080700c0588200c608648a42080d040c884400000b504d1004a148600f03219045952201007120040c021486125410982503244001065142c251480554409403e642e80c607441d4010100513603205003188605030740182010443c80358801441405001e80784400c0d4a181441005034000b409590814000241076034049040e081c080d1000e814449000342800003103507920095510042503138644000075002e9000000c00852003c6442416541d1005124180e52210028401e009d10240012038100c2414180803601401080c00c1c0a0707000465078015035648800e1510307400030704094003072011401611910030b00300e903808190301b98032460a203400a200c099a114507800742c0049032411080900d8540301144807c50743d0300540c140c1e03405465000207056407640b01c240100b501140414102024401e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466398156 1250 466396906 466396943
    0xa09021e0c0c1f0f020a2105070c0e0a06090203040b0403030b011403040b07020120040506070309030b0406060611030a080411150415090902091e0a09140f13 69
    0xe0680c0300e030040101c0d2101c012000203c0d18084207800c0081ca080d03071580f2400440caa114000510a21992000d4419032400383d40302540003102e446a24004003504d40101c40b0644140b0a07181c40799040340361880b0b510303070720110600460030548850301040d003010004a440c5406000300c0f80507a0340421040e11369912610200e00509e903402e041410003c56003d1800ca0114140141d400f4601a4007118424205480301a0031959400e0340280c0c0001e040482c80b04402d034900c151821038006441060352985070b840d0031540e0030100d0300002c02c0030000c081400140102541301400395000c0d51501b0681a0750316a036030f03070b40c0e004544580000034103280010380016000c038201c4819a40c01b6000c0884070200c0019003060f900940c100d10b07099824240c925071090b601444502c01401e400c80308515090085021500b40f281c4002c40010440000400d2580703605c564404000404008c0c078104000342014544c1d5400240545541c9001ca03400710200c0c0b00e0140101c0b290307070750307903409544454400c44009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466399406 1250 466398156 466398217
    0x405031e09040c141c02041d090606010908030a050a0c081b01060b090a06050c0f061f0f0e130f050105090312060604060c0b0a020d06141809031614010204060504050a0902 75
    0x145c48200e0960280300003d200c15071907051400f00c0c2051980441c151510741c00052500038014a501c0c10080007800400610201104503807441c10b03a840c1180c0d41e11070099068178040d6515000504184001845410307154424484c480c14060301d4000384101a03992600000500451007425031202d08004100030302d5010784010010300c21110141c80400e01041412401c0c90f00882710034440407920102c004442200f207c1c64030203000510801c0c9038107418400c803040c81c0040100092181e03034000000d40e00340901c080748203040660000080c8902e180420103280c494000398405a079001080000c5a0703a03150031000c0d5419942265202d0000c08429101c0049000003d03090744829582000300500310341c01401031002900e109000c0c442d94081c80c100380000b8102200190421500c1c1038144030384204080200e64881c1c845c03007900c0409800307030700b00040901e114071029001d44d8800540082c0d41604500030b442184e0080354000b54041d5103216070b03c10b0703100d001d02142c502c44d01c6002d0900c800011a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466400656 1250 466399406 466399447
    0x9020a0506070c030b0a050423160305160f050d170c07080303060f030102030402090c03060102010221060a05010903031b0c05180f06270405031e09040c14 68
    0x50414046a603a100451601e502821042e14410005101402400000710b4039071380000020b8000c1016203482d13114810b00c071a0040e4940c5e864641d05403655801c6d502007041d000607245141448a0f074a580c0e03d041d50f40d4808000050001c007038031540010300400113119800c02c43e6005041062014451394030030300d54090a0100886244091240714199001081110043c0111070000c0d9a0f0342003400801216440103401a403003603004100300001030b00c60301182a04038a19061264581e01c83d400185d004e401400008000300b00040d04046003503a0400e4050302956041d14004207003a11400111921096400054045030800c039102100c80d010407000b090560003000507a025948940000300480c0c0b8911054500c58040d20a2140494502443c280c1100040315961030100864580e21129045500040051004030000030240318003403040b6980300781a00300140715200b41d445031141c141c11a001c820300030380c6092807000030240501c1c031440700001c0c2160400c1c2044c4000781c6041000000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466401906 1250 466400656 466400659
    0x9050f121e0c030c030c0c120a11010e0d0605010312030522020402070206030906100801060f090e0705040504050f1b0603010506090409020301051e22080a210c0e0f0307090902 77
    0x801030b52848110910250280409410145558403c0a150189041416000c0d0b5100f0f0701d403030700715202c503000014550705280d5120488010303005010300103841c8006094005a00444000c00a604001e15688603074183c03481605140507092240c40110201c40341220343c1d2143c0c012511f400b070111032841c01e01107500c41c80280058a13010b130340d5001c0740302ca41044d12105282e500c081c0a2040a0b8401200c0c0e10142505000030000340f4a03080d0032141c5070845200308a2a5a928080e604040c1410300c801405020040c000740028242403030f0495442a0034904450a030054070304900c660524484441500031009003001d003141d090800304540c6030701841e011a1b02c0b030380c0c0308284401078030280035081c403c5149007088a280c4070826070100f070700304006065a2051000781361488411103042849402070344c1000e28162525154201658071514018100300300d4212160743c0d8910780f1254101c034951507556a180403010b60728400744070902c00d0740c2c10040d60540000b01e050040750100e80c440302c1c440c2e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466403156 1250 466401906 466401967
    0xa05120705040c08070f0c050c2101020c0609101503030e0d170306041104030c0303030509070807080d110c01092d03080901030b01020601060c0f03030f020d09050f12 73
    0xd5440001c2d04544083c040e40000c1400b110070400d0843c0c00c04031005191606050110700c80d84541d84031030300c800c400388c106849580800c20400010a80900c00480560047d008540d1518102c82c020360f1044c08a03034004851007152120741041003d40120071052440c90902816541150380a844084007100364030780240d0204204c1000c204240b03c2d0725410003428410541d2410b220b000c0c407041e1041686946103460080000700009000e401c0c951040b240c140c50f0001d030540faa002d80074148072550b40410701070b2081001c08a0042d0004c51480b00403a040c0d1500c500300d400c040c0c58140c030303880c8081c00c513400304210110800440d030360092400f0b1401c189858180c1e002041d110314612041c06600309451000010400c1e0303085580500c2604c1080e0401d0006010540c90020001e0425100d0400201130004585202e01058041c0d044550101c07910b003029500e4080c10300310302e8010705401c402a200d40c4603030354044d02555000b01d1409402c00140300c0311450215800702c120f42038541c81c40e03841044036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466404406 1250 466403156 466403159
    0x5060106090810091a270d0e04050c090d062301050303071704050a0602070905090f0d0c030201140424020f090f0d020d051f051003030f020c09161b020a051207 70
    0x41c00c05407170a1242c0f0207020846155100441c00070040408680f102c03003550700402c0824196504400005803400080307401040680d01e08040b8810303805103072100d94000c003501c000d840070003505400904002946801d4448940d11400f1821214038081c4078080d01038000300600c8000c207100a10100300b0700700c02c0c14030510303103941c65010801e4628554010030060300704210901c4498442c0c05112341105005000703106403036120300c0c40b94884049503000028841c0d40c45040c0d0402d4000e400c40d614034405800c200c80d2614250800010140611903d01c801d010300340c13007500d82c5640c944203485280c003080d000740d030030020b442c4140551001188078030360b80000a40c00c44c0c00142d88200b0103a002c50320a1015228003a64590816400c010041200f0255810300701040800155000100100c030f8040c0380c060b85484000c00281c0c00c185540c0401a08080340c2c50801015502280f13540d903494034a0f603564101d020b04400c4e071300100d04c82d4500003940265054410405490041989913941e2107000a440207103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466405656 1250 466404406 466404443
    0x4020a030b130c1b1106032508070f080106020c010e0a0f09091412090d030e040c0f0f0e060d09021c030207030c1d0c03130507080a0506010609081009 66
    0x26005071a44120040d01c50202c18105607204d5505107000b20020301500c4140b0301560703120600080d000303807103024860120000300e02e540d00b12540e458841102503482c241d09042d8200401060044580c02c010440700542c003c00d0610644409048070003d50181c00304468040c01121280701e182c1711942c0c007220284020804949001d4803c00400d00740100003408099881c1420102154409114680d08005c4012201424800403680290f04c101d58007500c0c0003945c83c040d01c940305c1c1c0d680034035007003032509505c90000ea0300100581403603210741d01c0d03030101160076660403a491700b070710000706421050a00c100c00300703072910341c202e503082c24030040c0304140b50131002203000300c2d0010250b4142e0060784140c42c10400c0c0b0411900d03080107810407400c0c00c21500b6441c034001c00c64180251080c4904240000001c1039200f03840f0504580740e610105480b1a191f0b200303c03040d92130203468000c0c4c0d03007030181d030000050b10b41c06171280c681100e11140c050804022040e201c8001080c1840058442d14589103803000d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466406906 1250 466405656 466405669
    0xf07090c0c0c0f0504140717191503020108010f080703020f01020a050d0504030c0509011410021603060614060405030a06050a02040b030103080a080106030b03070e1506030103050f10090803010504020a030b 90
    0x501200d0015076050f519010401040d968100c00d04154001308030148842c0540c0b0100c4400200002d0003820603540712945085030400d5054800c0361309030b140140c2051a500c4400b4004100c0f0300076aa200c0450f62100340003040c0302c41c24801c5d500a9070201800304014100044018604103050050714494481030312a50f0400110541050001e60000381c103004021010314041d000d0a0141c1d5501415810f0010b04181192024601c40c410018000108005803082001d95501102104525410b07952407802c480504410f0240010b082c0401074000403605209068800300c1d20020010700c8000556121400200f40140c540e5002a4080001260608ca100000c50095205074501036489440e900e005001d80d406800c0f441c10507062a8074500c0d0341c3e40c00504002a18450314040c2020340700e1b03103240790090100d07500c42d5402c0304e004400001071180219050300946180401e581000c00103000b4a012039815000050680303109000620060030594040d0820325054107000074900c0312a0000b82c0d130b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466408156 1250 466406906 466406909
    0x90a0e0303091e061003060209121b18070c0803190501060509040509010603230c10020a1406090d0509040905010e0c310203041502120708090f07090c0c0c 68
    0xa9489030f8810308050144041000c0540a0500500510304220920a043e02e1203440040d000d00e4010400d5034941c0d40e50300604182200f40d000320307510780c01030440d118844059401c0d00c1d071241407144021508841100d02e454420030056a03034040652032541d407900039401c040c01341243c3e40520001291042200c1c89070601825594a409854001c420200000e54030300400190080c0d0410f00c04200148820f40305140600d15491340324502003034400003900d0300c0c0150362025800903c5200c2180500c1d00030955001d0540070340c07400000d444070311403d07035079400082c5c1b6a1103090340000c103401111480348014101d400741c002d10105d2604000d44455003512100c2c00700c05c4e456088110301c44103c2c90315101c0e80c0301c4011302840b0902802c0240a46180c845100c0c8014900ba580010000b07080081e103840c051019440030800b10345a04ca156042d0240100c11038048020542ca070f8080b4180101c001000222083c48400a1040340e0901603d04007a194130316000062050100741640011a5a4004030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466409406 1250 466408156 466408171
    0x61b0b060108100f0e06130c020a0210050706051005122b030914100e011a0d170c01091e0b0403140c030f12150603010e0615030708041704050d02090a0e0303 69
    0x240c0e61b04100e410480d14030220301e505001c15240401c68803203070750041419410990100d901c400e4650f1095811740321441040001018180f0b03040400c010302500c4007003001990b9003912140c4145400018083e9112074240f400086240a25017101e5036580c400d0002e00c0b100030758507010a1f200098ac4e901d00e0b0709004c48400c5003040d0440190880140311318411403004070307003003402440a01c1c4422460b5201a01c481c00345801043d000700030b4810300100c00000c8685921301c400c00c0d0365545c000e010040c020249440304075120800c0030007510401c61110220413a80e50045603420703440d1110b6034180c41d148201d0f0103e9038403038002c4c03150f04400d4801b4005807080b103007040c210701c0d69100c0000311210258401407503410b40c031180150f007590a8680100341c038152950800c20100e80c1d01d800000a2000010303526103170a841d800410040041e42c401e0041c2c3c0150301c180313000c80e2010340711803102507140200e000fa9900603030044240e00141c07418030f445070740103c0140000501010074034581c604545c8101c8142 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466410656 1250 466409406 466409429
    0xb0f07110f04110c060f010605040608091603030518030102040b0f13170706081e041506030501090c08060609040503031506191809020307020601050402070201030f050f01061b0b060108100f 83
    0x8410013130b828003000c1d03070201e40c0000500e882d40c10014064000d0049014010402100303600241d40c1703c0d010480c0c502c9022680c41c2040c02240c1e07910700240703143d210b51503503c1040b5014120343c200f42014000e031000c0da84280e6032241450b0280c82e103580d65070010002d410407413407800e20000701c42e1400c40a1b4944403000e2005404210700b841d03000740103004041d01c802d059400101083c0c680107004a2000c1c1c205038001c1c62001214184043c04000e0030458101074000d51a04000700c0411010520300001c54480006490440e030360391081004103c0210b401070302c1740d00100002420075102e545680b04101c00100b08034145420b00d02811404007a01c0c00039004150042c004108181d8101031003002400342c404291306c0c602d0050720003501e070001849141c0c0900e80104a08045a0084d000310440300010403007000756140c1910001c883d12000e120320300204059000300c0754001030410035809110b03000a85030304540c407102c5c011a030301c60000300780e29017040c0c281e80042101982d0484100c000d03c1e03c880403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466411906 1250 466410656 466410667
    0x11e09050a0e06090708070212030c3f100b0c070504060812071b08011415010302070206071b1203050322020904030e1201060603060801060b0f07110f0411 68
    0x24000845955005903400002c0242040440e40e0f42d890480d6010495142080c1c035030301c1d00d010076441d100c141c05014660a102104100d402e02000d07010700445a48038a46014101d003401d080306210450b10300801e09402c40400e4070042031100e034602500411b03462500ca600f15502d0314079001c240c07c502c40c048001d4114103010802d0b481c0900a540207001140b000e4089800c0c6098500624032a00c20001c006500a10b011801c00d0701094a9200a0004d00000c0c8034081d00885040d170360320422280081900140d085032010795200c0d00c242c1d06810303806440720349068803940b5404806002560341d40e01440344050089604000002000c5002d40320b621070b151242041404040310360f030b440301a07000e081c80000301c0d08056034450b01410b8005406090507100f08103901c001c28100c0e500b0030170228080d03003451400030745d880d896801101111844002007010a40b50035808806201d94103104211000500c500b1303010512503445442080c600400d1485c0781d002d0f0002080c10b9a110b00b914104040001c6007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466413156 1250 466411906 466411909
    0x10111605010b04390e120a0b090607230c070b0c0c01030b0f040e010f0501060c050c03010204031211010b0a0b04030303050603010516050703030624020f030c0a020f011e0905 76
    0xc0d02c090040621001d01134003071500d89001030052812400d18411550f040300039400ca000310b0f0361604610f005403540e96040a4604400c1d900c0300e508404490702041c400024003900000700c2c1c40780c06812075540f4810340050034400c4d0340411040c68042c2120300420405800c050314100700c11030080400410a81d1a4911002258106500000324505040c00c0c1074203400e859480b0601210042d1089030001500720003c119180100110080780c10058601000414240d07002404ea1034200d00c00d40442d100d20714140305050903405540302c01411403400c040119940b5000b0301e040c0c03070704140c90720002511981d8580001e0701b00d20542e1110b613121b48000b03000c0c01495494010303c0d92141080e8002d001500740010900b0b04200010a40001c1000c04034007201098425080040103080445410060b211480c040103e200c0d4096483c0f40540310703d902181d203036000481501d28414048014014032150742d005e01c0741c8944410041810031120b00d07880181c080c1e0403004150140748980e01c103010b2904090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466414406 1250 466413156 466413161
    0x21212071d0a0504020c030d1d0717070509060111070902041406130635010905091603030e0406150c030f0c02060d090c030203030307031e090510111605010b04 70
    0x1402505901c0751071001810b454098407071048680aa90040e541d80d00500d0890940c01025124004103051604080d25151020380340518000078200b52009a0f035501c0b0303000304004080e0f032900c0d002d410143c42000b541c90200e1003d40d000e201070600d4141400c824080c2c2e41081b4841d040b0010803680420309200ba1a03041c035109800303000545441d460300006c3d0100b0082c4e881148141c0d030070818005170080f00301000754426000703c0d4088000c01000c0d15041c1c05295900c40901818449500d00300c0010803002c00041d24039501301024000501850071620b00721040c1144400d80b0350401d444c0c02c0006540007164650142841c13180d030351000c0402c0381d45001804400f0543d21130041041c1c41c0044805607460300101c64142680e5440001e0076440d43c40d1080b079040080d4006076040c0000f0040212a0390160003c1804d03020180c82036180a6003000c40310700300c0300706000161042e4800300210b149201e46600482c5d20b007046031445801d0114107558042280000f00080344d0594403142440100e09190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466415656 1250 466414406 466414427
    0x60b0a0513060c081206010219150b04180b0c1c1e0e070b0c0a0803071205011a04090203040c050301051801060f050303160618200a080d0e0102121207 66
    0x1071500c010004029100e4072018021481700c0c0c011641c82ca80459000d0703008101c1c68007071291000050440301c0180c20b10074804507400a07020320481c1030807a804c106240c28030a8641050b044024012140c40756119158076400040c50300020950801407114a2080514031036611602101c011414020f42400c0c8000510504454501103040040c0007035440c401152050685410729a81034030750304002c100519000b0b03d09401780aa113400030a12000942c8000d040705450340a43c030a10032641d80d50306040643ea00c040c40408240380c1440700344600701440d00295000360150f40405900340d102c0e0002801c580c01a1040e0080002d14080c0d0020318800307001d06402894040b05c0d0019051501c0c0100c0d4403403048105100a001d44148140b041040652040200180d42100440354078254941800c00b01c02c9440c2c00c1d03c012510010001c0707246440d04c0707800c0c107940851029041844070240150384a0b10081c29480c10360042006c030561001050000d030a0114080c0c003040c015040200d006030003031510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466416906 1250 466415656 466415669
    0x30a180305090409030504090509060f010f060512061201060611010b0f030a110d1208013615080a15200724020315040b1c020f04060b0a0513 62
    0x121820101080e046001e0b6a1500c03025100030401034820300d0f044502d84501d400500c0b402d8a42400e0025a00f00064960b03c14400d8000c0b12502e80d0f200c01e4618810b504034425040081c85c10400500040000d14546801c2040508840e14810040803000d0943c0ca0b076030000c100190301e00c01c058105440900400d00c4990080d24000b10308480c4001198079001d200102401c840448030541101303865112500781d0303e542064400034507802084004001c0c00c028403440940584210300041c8454405003c0c00c0c10846118144c1c0380c3d5144480444041c10b9401c800798095114080001080d2409101041d0b965200d844800204402042a2803c442214100540c945442903185410080e03080407142903581040b42a11442c100e0501c03460313581324103812103200034004014040c898171090701140f5510340458081c451000c5d02c5003400030740c048400600d0494021945e0400160410400340317488844094804034a4645a044c8155180d0242c0c411500142000942e503080540410103900034146 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466418156 1250 466416906 466416941
    0x60910050a03060b0105091f080105041413020a0b0c0703061103010b0706020913140603061f030f0804030c0e01080706020d080705031e0c0a1806020d050307090f0b030a 74
    0x80201041c0ca1a80d1404020f0400c1d50380e1000307000c00d0b8007540a44010300c400a01e00c90341c150a05110284105110005c1c50106105400100701031070701c0e002d9001042a110300c1034186513070b906484084002421420398001804500104c0e0031411b20000346200d50609005040b034500e546004022507407421001e07044d800040c1f00511250034400d0403102c0c0350340c0281015889602c0032000400300c2c4611080c0030301079485c2400400e80e03400c0014526202e03503811000e40b5155607403400a04003043d04583c60660301c00e0700000900000341d601c13201c0c00300c15010f051560f04054983c1e81d82c00d450302850b000b141403040c3c51001040100c000b04000320180115201500d2691051380c00900100c130041e10f10000d101c0e0120000301c016a441009042101c2c107005e80b018241040c9203d101c80d0351040d01d04900255050040305000e00c00e640d42e00048880d9a401400d030076056240c2101c05400c05441402084081680000c80001780c019842c090448031441c59500e081010000c4205d131000b19a11541c0c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466419406 1250 466418156 466418159
    0x50a050a0f051003110a08010905060d03082a0309060405161a031905070f1205060306010e0702070803071505060904030804020f030a06110301080d09080a06020a090b0c0105060910 79
    0x11115841c0d40304451064407183d0300003080500039405007034220001940c02c4000310b0b010310100d0703120b403015040341c401030300c104481d848410901c10000301c0518040c01003070403800400c100582041c0c9240501030500f240800030910308601484587c03041d16910816031011080c44288482881141c10080302c5855041419181030801030005405010210600c0740100c00204803200103e11124202c62105e008c01c418500804007030450003000c040200081c03032074600b900d80d40c6242d220395809404004d0060000c1d80c0780500942c5440c02c01052941140a080c00c0099400f00400c0030300050b6109140f11007015014032450707021120002c000d0740c4903c48000520020903040700580e9000343c0c05881026080c0d6001c00480d18080600030000c0813203280000c0300369110131450245041c0d84804040e0b5070f0300405032034116403d411034000d02d1016000101420006000c40d070041c19004101e00b0400d503d5aa00c6220150503000040240520703515142040650701d0008101940044410054002d15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466420656 1250 466419406 466419419
    0x1605070f1d0c1b0109061a040902060d0504020d0507060f030c030b0609240a050c0c01020f03120a0b10020f0d0815060f090619030c030908090904020a05030610050a050a 74
    0x3160240c00d40c0c0600c000050b0410b50084401c0d500741200b00c103e8024444604c807850b018009040020200d80740802d1102101c00c240340c54050440c050780c00802c52800c14906014aa000b0140070f0422a803000c84901800b00040051021500074000e84d00c50b0000c0038034820300501924804500340742051300e4060032008694034074041d03440e600700c20b480310900074078544440109180001070700128280041081a10541e00030018007200048400b40c0e0320748a0710304011780e03444a042800c0503c81d041880540702d1405d0b0f006d06a58040c80b5990302141c12840080801c8444013900d4208006800c5160a21341621040003895003015a610300b1251520746400e0346206440403a10342441a0350008642e04c64450741015a4961300f0000c18441c0c0c0d0b204015946008046100c805002088c103001400441c01d00911800901039003000c0d2070351400014904000310f12500805c01ca0340400038080100d15500d04000c4188602071040c0a6160706042c40d04024081c1d605030b2205d8807680c3d07600000e1150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466421906 1250 466420656 466420709
    0xb010f090b090a0801150609081b13021c050906060d0c051003060504111201060c0b0406050c0c01050a0f0e0a0c090b0d060905062d06090c1605070f 65
    0x486240c80d8606841c2d030b4901002801c001c1c46036104580d00c1d802c0034944003255241070680c208644480d11104044c44c1d0b58243c136034444800348050307249899620030111683c03d0003030041d00c0811040c0d000624128501c0c6031018000c10300f0740d449034080c2d6541c0c104405006c0800035590006000c80d111681c04000d0358440c0014070316030103407078018a484020f485699000b03801c4503029250040051298401401d5000d0940d002070384c940c0c104000d030800001da903070b00031070590409980042680410b031b511515a403001d484054030200c1014400c03c0004076001e0288922406600c440c1d001266030b10b0395000020680700f88a50741031194001c030203000005200c640b122801c45103000008500110404005141400011400742849040c0000d07a0100030f0081303581e51041e041281d0703203100301c007044407180f01080d01c170f40760f02c0c02c10b9019034042145443c24451055010404159152805024904048248040b210111000d03400310800340103144d08804900060074115070000444a088550f6082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466423156 1250 466421906 466421909
    0x806010812031b03242d0a09110712050307080a021602100804060b040212151203030c0d060905130308041b0803071205090d1e0f140c060901020a201906030b010f09 72
    0x1607a084030344401d41600c0f40080c447c020115080d08204588041e088102540c0c00004211130480001078468281070180098174010b680f140da8170742c2c040d9194060540203501089059180810401c01d603401680c0307440b5103c40c070400c5651840e00905081c6088000d50700c07111011442980103000c030710f640c540c0001c01103030f0100103c101c1c0c11043c60788002040e008214180c0c03d2800340000402c010640d10008000c00d40300c03800c4c0004001803507503406e94038100e800544140c13000c0245070b680ca10210740320f07280550300280a138114145a10f1089444010045e0359403081600d500041050001d000c2090700c400b040c0426424582c0c5440022000600000b9048000410424103024000f01c0d017111140315440d4a41d00281c2000c1c01103090a09504045000c00001080d02c100d03105061030307003081800da170b000c1c21043e0000c000c2c400740c0b66651443c1c025903c0508482103500c04140c0c0565427050702c58010b0000905100b1030312814401c0041c255410b00810300e06000858140c4401070703611210b04070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466424406 1250 466423156 466423219
    0xc10020406020318190b070b010603050106120c110609160f0b07021903020303180418170913020a081e0c040302090402220509070806010812031b0324 66
    0x100600380c5000505211a50107001004141c170b00004295400e03051b00800d03001e4080c04501d0403da98030441281580c1c024007070781d0b0004420902c1d4807072021842e04035a04120142c10818001d084d04146280342183c02c4880c4203655000140e0840701051846003a00500f44025441d43d40a00b0005a002d17180315004000380a510034038008180600204070440155234001e041e25911130881924501082c030010086100d075103014901e210490352a80003e003000c1c1d002e118004440110503d01c1051703044481245d420000c4440c4103100c2c1d0846200920034500740e0b4481c00b0081c24102c80e0b0320144070140e0301900110801c4400d20034498148016501100e40c102c1b01c1114a03620f030720104883c1c1183c80741e10307100000031410010108606401481c840d0329031600f00c0303402c0f9683d4081e00380e540e40281320b400740c0d50b04030300200c001614032040111b601c05417020460070a441c14034000310681e0302c216141c44440d024044081800d850300e071440d4950342c20072200210000c0b801145582c1c1d0440e114a400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466425656 1250 466424406 466424437
    0x33d090b150f0c011401090e03031902090a0810060e0906130f020402120a05070e030a02130e0307050f030d05010b0423010e18041118150301061503020c100204060203 73
    0x1045807008110843d103a581d020030080c0159a03d200648641c0c80c02030151044041c100307003d0314031441d400015244196941850034407015101c130b0400009600168100d40c102c1140c090216000c20208880c00c482c0040400004a1030300c1e00c4020400102d0103484c5103040d0300403034180846030f200503410f54080c940014411441ca085440002c0091107070880d07001c00d003a0309104000013140b55511251040e402511040b6504065104040d110458000c00960290454071064200b450340c2e4064208000b031141124589240b51701c2c2e041c5845051100e00d8001d034070024004c0f01d1005203001e1140104041007030141410300700110941101309840369940741849203102108507030f01c609074856401d00041d19980070000704200c0b01a04a40840701500e6411450050360100c0c1400e808071400c4481c05607002455448056035074090140c0b004a16900d503495020106196000d003110701c58000c40d5071001a5250204114181080e0400ca03c441000d80b060004000d00d9801104543c009000d07540603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466426906 1250 466425656 466425667
    0xa150501051e12090d030f0507121802180406150f1503060f060906140f040510050f1305010e030604051c020a0c0303090303080f0912033d090b15 64
    0x1c2c00a034010000d424032440f000d40c060154000c000b103540020081199018080c0001c0598290242c1e070b0151012800100258030b4001444800d034003007004101051180514100140c0000340b00c1c0901d1646540d2504409060104102a500c01d0706a102080c540c071104440c64120410413101943c46224001807410f41402079980c82035000d04090302841d08410354003500c90100400001a5014100100b0a901c00b50103800800f02c003550440620824641d280c64200428441a075060002440c2400020701c900950345520401038403a10540003090350100d441d002c0010900b03484d80e901e66000f604084180310204101040d02c02c41c4001d08503583c03050350f20080f0224688a120a0003400c0c0d0700741d0344804010941e000218408490283c0c0e03890031b0380d03200c41c82480c2044c032058402000f298081c150102d200040240035640c0321901c0b40700240c0480e0800b4144c0301140b100d030340003404c420105841c0003030f03508100c000b08050001d2800420100a1b00700c0441e410200390195642200c201090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466428156 1250 466426906 466426957
    0x12100501020a060e150106030213091803180b030f060f0409030806150d1e3c110a0e19080705062a010504050d0e013c0203030a15050105 60
    0x170030b08840804480c805190b07500c0300d00400a41006048881c030f04d440c01000a64030003a80950045404020008402c1c0c49541c2d80c1950001e5100b18141d0b8051403181c400101c140707100c0045e51141e002000c24000700d20b002c10401154072540480e05119903e41007464003c01d50116040e039101000340c4550741d0400c502e00d0710318880c0c0143c0c0c14071420740303061031801d0f00319036020103941c6a610310000d03060015031382490002044200005030008040d401c6010242d0300118210503286003030303c00300c1c001100184c034040310720182d00c0030824102091000304424082d0810149039055445541c0d000502a03091100a40d21000d85100e5644200c1c0c01240d40d110304a41c0703a06c12260038688184183e030900081030054068402210181c880e400b03810124000c441c05901c04110981051351072100d40032866a21144401815001c465008001c203442602201c0c1414044964031a6800450709e80c5040d800c2c800690340c80168120940100707241c10000c41e41c200d4196090490028180c00150f10342c00d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466429406 1250 466428156 466428163
    0xa06050409054219030506010b191809020d02070c05120c040504060b0406060c110904240b04020c0114060d0201090e09032502010f110303071d031212100501020a060e 73
    0xc10f0140c0c407402d8040000b8484484101c41c00031240b103078003a140b5aa80e512600b051600a0602451500b132a10070003c2e04244143c4078400d05001555007000d1054071343c841031041760042c81c6540b4800e50300241d02e40c00c6c032101c200c1c100000d05003244c1e103002c007000c0074007003a8440c101c00401f0760095840b60007280802005401c4016902c80c003800400183d40e5450008200140c080c1c425074080440304500b0302c00c1d003001c02c00300744a80d4020319540c00341107804041130801080d40e120454500e6407804040c5250307486000414124080b9000422404c0000c82d0400f640a0046e2255208444074200800140d0304007030158100c514041c14000c4035620102814110b05c41c15408054401058038881c4a5644000c0048034082c003e9980c00d110050004066130000040b8480810340d500600c001515184200705031b090321841c801c0c15070703483d658032400b2030b203001c2d01154005000440032850001c4c00342000d02c07880e4003148600140c07101529001c0040d4070341100880240800e0303120440c004417440e042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466430656 1250 466429406 466429531
    0x241a090a0905130210110616050c06010803030601020c0121090201180e0f07050a08041e24180305070f020a0e1303080901060305060a1a0a0605040905 66
    0x101e040c020361038154080d601003407009008034400d00b01850114a164071541028800101c00c00c02496242c581c04a00e603800c0c160498400d08014040201c04401c40c014080c4600030300000c00110b480c4d007491400641003080c02c541c003e04100340c1d8514102c200010044412900050803c0040c507108680012500c600e44000000c0f076031000224006a0000c011305038511481c12141400c660b62036464048611384101c02c0340c0d00c0020312100c041008225401c41140403251040c860414400300d81d50340c100302d05a20005215031540c0c0740007084610f6014050f0640361030200306050307004101307581e0240c01801000c13009070042046845107811074580b01101400750004154450891514004038100b6203000e240850000d586880032404400c4140298415a0f6000300902810703607504001c0d00040c80207140300a14014500c02c100442e8541e0b40c40d1402070801c0f80e0761180e459043c081460143d40001c1d0800410340c0ba0304011202101d03440c00c400f0384404540600401510180da49806d011070740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466431906 1250 466430656 466430669
    0x90c020a05070806070806090606030402040e25050306130323120103050105101a07060e01021204030c12171305010b0603012c01080d0807020a0510241a090a 69
    0x1140b20200b4403180c0019810701c42c60650b0b840c60800d50b510400d0050030041650450703009281030000c1401071501380c100e0b003080c1c4040e034110341c0d035030f178040300c240c2c14000715441240700545c4841d8050095003070604c24540e01c444065a40e40c00c3c0ca01c0766031300424070031495044510703c1c60181030080000f0b440301c0440d1621040009002c5045d40c4a0501d54000d00c81070b10b415504205207000050034a05030b00c2c05a002c00010b07544c0a05121140c1c0341c50700a0005801d410460395420441c02944a102c00030480c00380740071b40c4e5142d40c2000c0030305d070080352024900d50100c284107409244812045240c801907a20040c0c2001c1d2108507c3c0910707100380540072244800da03101c2c0021002107441203c0014480040c0c040c50200b03c1c44140302c15108004820a00510119802081c4100703000d074010040e403600041c1c01c9c4104d4921171440d880d1141803020f4074148041560311a5140c1e10900309500e505603610036425243c104543c41c069024007104141d41580d035003150081032078121969400d540b1001401f1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466433156 1250 466431906 466431913
    0x807050f04090b030c040e060a090609020315070f03050f070c05030c01050a051906081240080c03072304020309030403170f0f0d0204050d03020c010201061a04090c020a05 75
    0x216aa07040003d4242007107114040d2142c0340042c4104c2c1b8003801340c0e644130005240981220380b180065400913040c1c9800a60341c0c03035120b1780100c0040e00c0c01c000f14034142036a9404c54099080250000303001e40c010b40342c60302c101801c0105220840108160250300b000750b0b41003c917001c5020349485825400b4040415a940d403804041010000d4160005441810316800002c007181d00c1035188402c6031030501580c1915031010700d0700c3c149280b003000248804500c2c1130041041c0000c41c0c0d2242499154640820000d164401c503500782c0012480b40c032000341140d040a41032a60311400440d075907090b140706000300d142e140d4044041045098024103031000026105641d039203440c1805542c0c0b0341c8288401c469240081c0b0302d04500ca1421000d8031100c0740002901407030301509410401c02508096000b40603141d00f00b10006050317440c141e07030103070080c8203801400d002c0c07a0250003e400c5940c10b40c0204014505842d445001070740da4011201500d19107070f00040c2e01205000b0072450a1444800100740c0e12 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466434406 1250 466433156 466433159
    0x19080915040303140f040b01080a0302060f060a050d030e0a0b0403240219110d0f0203071209050d15050f130213060b0406050d06141309062409180807030807050f04 72
    0x18500e01800e0b1060b8080e007207c0b4403d907a501d015550300d1145440280058100350f001c110740d141c14442e03264000b4001800d00c44c150b82c4944c0004d20400c05080214042049200703a05080c0c00c0c07440104005003890030120742001c1c51070b1a0681c00703605240142c0d11210341c048500f600c14009a0582d5201400500c498200b9440303540080c001030068802e041407482a4601031080c07511481200144006039400745007050403981d03501008500180844042c048031000114450300c61101c00d1408900030000080544406a030500803200d010740040c1c10f440e01d14040000403039040c1041002c09506890303000740c0071105c02e0700c2d00c01084c0d503412a5070005e0340040d001451640c090007134140c02080d010308000c172594483c00800800e1001543c0c50304000c40307104140c001c0c42a903200c040300d1400395101240d1524026840151182100c1d110980040701580c1070001c681d6604c2601c00302540310a8800e0191400c1c0ca68400f107000d541002001c00011750001a03140b4451030a035a013900d0310b0302d80c1a488130f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466435656 1250 466434406 466434421
    0x13020f0c010b06041401081306110403020f0d120509040605090403020f06070c0b06060309031c06060905030a02060306060c1c020304150e0a1401091a1908091504030314 74
    0x95000c020010010340c02d20340446540c0c5801c03c02c070340444403100d090889400c80c600041d11101c9000340001d0340d10b590340c25000d0206030729019081152880c80360f81a0368074114410045602c0480c02c04a00038030603080020005404c3c000040c02c00005801c2070341d203c0396494005805070034582c1003150084000d01c00c0c407040503000200402c200710740c401a1001070756442d030100c178101502900949600d141c000451400d0030301c0401540c12401c03100c00d50f072500110000d1071245c45044002c05440f640e41e8a010030005070320180c1c00000d0003085014000709100b5030005080c900020740154811200020700c6481800100201c040c0200c02200840702d24040c0c000103512500a40302e00004800181650024580301e0f400501201d06c0042070418081d080000150342c0c1c8410941c100e052144502c2c1c0031a0b080e088003202da040361001c00c0826564030201c407000d40c1d1140442020800d10007048103204042001203100e001032041031944404075078072402d0882c0609400c40c1c0042a55801c0c2c414072624 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466436906 1250 466435656 466435687
    0x5060301061a210f060603060a05040c0f0816080c1813060503010f0902090708093f090117040302150108060901060e06240c03030c0301090b030a03050307030b1302 72
    0x12840000c1c0b4105030030794072030f0b080708007203048500d0420342406200003540343c074003a0051500084080d1000c4400b6480d10041000c9824444200300411400882250030603130054080741d0021403284859401d80a4040c05001100080e0400501e04004100540020341d010b03058450018014494505007603002d10500c028540350264034080c1d420440104441091800b85484141d4050304e0354001d82d546440c21502c0b0b11000d4408542405a0440401c0403044041103880c030038181201100100040794030300b600b2956000704000502000d000d02c0c905a0f81252100710343da034844203c00016030743c600d022401c1401d03d600211200e004100045001c401c0054983d1164041d000204a0035841d8488040180790171611036901108980c40b80c401120003881c940e0b4030001c0010090304040001c1c0c2d031281150000c03540c8001c05000480100040c00c2c4034024100790204c2503010746240601520004c0051100405100905896500203030640e11840c0040000644481c0115101c0c000359244a21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466438156 1250 466436906 466436917
    0x40303090f0308150f0352120b07050c01090507090b180609040f080c010903030b03010b1e12010f1a01020601170d03020a050d060803030109140f0604090f061404230601060305060301061a 82
    0x2c40342c47c0c604040b5110b01d14003020745030503412840c2e0403940d94545204488560001078100104d54a49500c080080c80402402d80680803064010803140d075440248401c082c5a001c3c5a4900e005c40c00a220a42d1030f48a0001d0f0400c3c0c200fa0042c400304100d0410020301e229100c04251190304e80314440007450703419801200040c0048000748a010034001c1040024a62401205685003a48001c030800e49889266540e01e201600c00103c1c02c030305001c0c1d5410407200d58500410701c08a0b0301e00713104207960341448035a000d001c2c01c0700c000c100c0007400d0034180d58410890203440141a030000702c80d06111300403001c0c2e4404080089044c00f040f900c031041d458aa801c20b1007905c9440b820460a0601030020141c1c0510132402541300c3c2c903065071180100005400f5943c030540d8511100540d40e4080303403060040082902c841d030b1080c1d401e81080c2c5000003440da56000f042458125020340c0c43c540c41804140303e03044424900d008600380d00c803c40028010b1500f0f0b40080407443d0a403428502c1040c00721301908 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466439406 1250 466438156 466438303
    0x2e0312051308031b0c01121d01061205010c0908031206010c0f1211030405010210092a032001020a060e070b0a021609110f03040303090f0308150f03 65
    0x100b44c0b43c12000c4459450b145042c0c014040f40b0ba92503d545900c03117540c80030031070b560110200030301c01800c902450f0869035503070482d01240181080381c070140902405a1020340d2058908080c006180c83c040b19260f000d08074100c0800c2804170040b0b05c071a8840c0105100d6503811020360004180349140250303400d5400c94201001c602070191031030310144040103544c02c856040c5c0241500b41c200c11034490040006200c2201c00e02450440000e10a0030f40c4404242e229404050803906411803c0c043c0c042c4100030000c1c00110444100c0350f501e40d90100d00c0c100b080741d0000d000700d4403074000800301e400c080240d0041311046801090044016600107a072859401114012204181e240c08040064444016640d5203020080110521401c00b039401154014060b140010700c0b01d88564071140503207103950080d000600382000740000c142c0c00c0f904241150000f200d45410116074400443d0312081e0600d49040303084a00700380c00d8400c100b8a0a0039240d04071161024081400041d11000e81c1204840c800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466440656 1250 466439406 466439437
    0x91a010e040c0e0105010e090a110a0507150603021f0c02120d1103041d0c0708070c061706090a1d0304060c0c06030e15060402212e031205130803 64
    0x103848000f49071076a0503200103a552091019011040c414090406440101842d540d140000c41401401014200e180c13070070360720707560745014a042a0858980b405402d60240e071030004100010307030b12a030b120521044014841c3c3c6041000240544402c201305a02a40102854641d284014000f0641c44ca9040003504da01560b840c6140d42550b0b240560700034a40b600d8840883c04294400901c0100d40c0140b69024072840c01999603180c81c01d9400400e001c45020071410800d1040076000301d11341c54915a2403480e01e64074034015001400415014103100071043e82d44012403011100025801800000301701102d903110b0359600001d085051480058640300d0b40440040351083c464015100c0b02003c120080030343d0150103100c1100b005002d030680b98407070783c00c000c051400031007001204614910404041e01a01d014030b45c00d4443c00d102c5c00d04050fa61038081c0440c038605000d03050542540c1e0080e144c41c04d0402010015552032180700754404681c8083e54000a40b50300c001700030701045070058002d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466441906 1250 466440656 466440659
    0xb010503010c14121321090b03070905010e0a210b070c0c050f010c0609050606030f1204350303091b03061501050d240f05090703091a010e040c 63
    0x403500d84401041d10b05607000c003002003510403400150389541182001744d03461a00c41c495510400807821a001c034146040200e40040b02c40c86c1c101c186500144440c0030603600e1440c001c0380040020407140070b1141404100050008541c803183c5500e4080c0c0181c0d035980e9003a40810400d40014400d2110440c0c1e030840f4000003a04091040ea845a80c0c41e034407500820b452070230b0038208560705e04404001d604220351540c081c004114140692542107004502400b42800e14406141c2002c41b151705808142d4803006c400706501d0241d00071a42282d04100c10300504401d2880311001c07802102684030852010b071640e5400d045408001140249003440403030703c10141d1004c0c0b581d075030408040381c039615070807000004040c0103240f03a032140c4500b81450400e00d08420204560b088851400000d6803515091003280e900d82c0140d09004081c21465941080a0b449c01b400520700c844000e10a0003010744902844c4208001c001c2a402c070f207000b203403440141350307161800a0023111003100c00341c0b80800b16010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466443156 1250 466441906 466441931
    0x1207081e0c0f010c0f1a07030c0905100c030305090c060c07060e0109120f0213150302011205010e012738060409110c01150806010f060813110901030b01050301 70
    0x240510b1450b01130711143c44082c1c99807203103c1440b608040a03903e1040c0f000d00c103802044040f40e0103116811a40b07000420a0482ca001050107111ba008180074440781c060000301c082d040440c041150f54545400b158503503510b80010b0a0042c080ca11a401a1010528240003140031402e0001d580c0340750344050108000c1c00c011503d03504240b280fa100d03c20725201d81d00100e08150340140515001820500a41858283c4141100d440c501c0c00188a80b650000380119a840b0401c16429004030500b0b10140d41420a4505000b01c18450308048440c0d949a5000021840110003182689540304220fa40d5030842c90034480d41d29110019054400e6600c100300b813280c1c100748004042000303441b0b181410309003a040e0004204c015115020081e042c03145170454030090141600c08200b941000d100207280080707441c980a0103030843d0028055080301406616800762049a0001c0b810400a840c0581420a9400c00410b07003041d5401440c518000310500423441180c45c101c440540003004500b0302542c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466444406 1250 466443156 466443169
    0xa050304170610120201180b1b010509060f10030b0702010212011d0103031b020604080f0114070f1b14072d03020d0501060f0303260103050a021207081e0c 68
    0x300d809205011440f021321609400c07000c0c4020300752040c10450715040c07642c004a010001c581c1c2c0884040d400009013001b0114020306141c00d1209684001e0241d03003010744040380c45940c01081c070035001200740c0c00070302500f484002e49030080d03800030482c65007818201d000a0207035104d500c3c1300c6540400c03c800000c40d0300401d08051001d9044080303106459007103990480795401a95804410b00d02c0d0b8081d48030242c2e035400c0003400100140d00040207624a24010a030a50300043c0d0b800c01100710050030050340d250010010683c8072042d15010750403008a10003810030840c402e2018144e01c01c014090f0342c000740005031030026603c00d4480d840c1c0d0201032080340da20303c0d070422014a001c160514010401410003904151006200c0e00c0003091040c0c5a514000804c10075074420b80004481704001105401c1c04009110a07850001e01460780f5070460300c030701d1350341d03c4840c400900071a403503500a054510705012900141095a081d10700210b049031021481d6943c6080020b034901854546192915100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466445656 1250 466444406 466444411
    0x14060112050d0f03060b0a0903050106060e03060103120512010305010509070b0a0525021c03031a06030f100305060106231305060705030c0102041d07020606060d0e0106080a0503041706 81
    0x10a0800c07102c9200301c920584128180c4185030312074002081c0001d200e8080c102071030440c0c1d1a805880c2ca103040050a503042c940c00201172140305240071403076440114210b415030380c002c070314030141c00d441010480350ba12800404101802220002008000b4103402150241342800d04803006241c844240c0340846c0f144881202c04544200700003507503920141942c1c0071441010704d10340c01121041d00854401020b0112a91030151071b501e240d410035070148503e02020501c211100c032085805000b02d00c5503c07000c1c008800c184484400145e03184040401c03c80919070040070350361a940d40b040e003e0300042c0100d11666008003501d02c50840d00886006446400d11240c1000b08501d20704014402560300c1144280c4107800304000e0340c1401d5009000a00041036100b1f40662071a002511100104101602c0001150026014801103a56200603566401880d5000261030466042810300603d440e9000004600440c44030805000003c009441220f070040420b075544c21309002d815464030001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466446906 1250 466445656 466445663
    0x7020a03060e061f090c0e04140106021c0207030807020f1306050427030e03030c010213050f0301020a121e1103160207030b1f260705040903050708031b030414060112 73
    0x10400411010009402c606c40c040802c1c20a0304100701c181c0c010909566109c1c04034a079100c042e0004000b455810070510f1a8000c56925000d50000000e10082d00c0c0c500345e11020b008560080340610941d82c3c0c0707480301c1034884130043c217100d42c040100a140000e0305c50391003058440e034605815402c421714070000e00740350010b8030b590904c00100e1503902660502071b0002241d4040c0700178880110030314000d00c001c1040008944070281d032203143c03c04000c003254400c0c6615020b41d00510484401c190480d64241c031551a4080214142450f0000801038140740610030011501f408000400060190010340c0200e160103920600c00c80000c40a03a40e80700345200061064002760300003440413540f1038004c200402c03081005410143c0c0c83c0d050911003070750392900b0082d413450303900440b014003020009000203003415101403000b1442d81c0c030050401d015a0901412034440000040d500c2803903403100380a041356010b200c0752241410b01703100c41c5001c5520300c944181d2280c0d030000710380c2c80e442c840906c1c8410360 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466448156 1250 466446906 466446961
    0xc0d08100315110c032d0f1e0922050a09080307081306051512120f0d0605030a031701051507110a0b040602150c1e0f07020a03060e06 59
    0xd014102d98010300512809200300101844041c0d10100c091004042000009400011900302c044603132104102c0e07040c402410420410401881c50807401c10348601038004000c45400b010616003c545d01d1040321159540188600c020107642c0229603102c1c50034020180b000c01203581c50181034004c5459a140141c51294140001800f440c032903400e0550080c0100d03044003010055507203620623600c1c25600b01a00c1001c41c0c1183c000d80c1800c1500d601907211400c02065000a55000c0030b110303101d14445040c150b800011804076140403034000c0702c004c01010741110760403801414014410800c40002c441d060b9210800000c5074a8111032510307003450844141032a11465a0700e4a02000e40c00c1c6401c1e80005c1c0124000525600315000350005148503000703040303403d0703501030283c103174400040c021820550184030019000c000411079200030700c40c4400300d903503826606003855468014a41c00a40c040c0c0c107040c01004100840d0408001c5150b00800c4031040d8513100e0308501c01c078500941c030951b50031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466449406 1250 466448156 466448183
    0x602011a040911270f0708070c0201200a051203091e070504020d0902040e0f160e060d0309090504050a03351801110901020c0d0b011a0904020c0d081003 67
    0x5000515810a60400038943c0400960009812500d804c116422821a015982080000382d009201ca662103003007407510f11040b08982d40060240c8c19009400c080d1420041d00b0039860000802c461801d07550444101ca110904031001000f00f64021502540680034066074180c50400d44407040003659030003406803a01d01d040905020007504031000f248141601c84403400d0160300e0314440e5541a5540790081e180c0c1070352503605540361003078021a41400840f10082080320307032607915405402c00c1e802c44620003881d0140c10110384140d00c1d0740020501038580000c6c00108080007618881c3c1034465129100703c0b04c8500184034087c015081403001680c80144480c0c240c4654104480e4000b042c003000b694009144100070b82100d0001004030000140003805040540e010000b2980603541210440d082059559581240c00b00602c24000740103120721211602021035410b803030025101a10841d2116a8580d04990b1440740701c03a880007140c09400840c1c0c414074a5810501902c2e000003c140015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466450656 1250 466449406 466449409
    0xf1e1507020c060304170a03050714040605071209080d05030708011409040204200d060f080715030f1803050a0e010207060f0c02280608060301140105010c020f0402040602011a040911 80
    0x341d000800442d18140d11b0300c40c9040294141020340380340c81d41c1d45d6000545150129016081032502c9a003040103684c2404104440e541c80000c6452080d480884042c0400104000b61001c5280e030b0003e00003402444c40700d10015030f04c0400f030340c460303030241e612082d20ba40d03241e080b906040302002405400c00301520005015003400d0700800180d020b001d02070002c00c0800d0070b1818080e040000545c0b1429120b25041011075a911a840040c04545010700292840d0910009a490801059005054694030142e00f41d910750385c800c4126420105c0183e032903d0003468028450ba01240b0340001080f04003a6054480d4400112101610000d40300c0d8100381140c514265598030240c00126071050302c005900303403000b01e2078003030940d1103c405d000940074074241f060203051601e0051009000b40e140010312055129280004d40c11241c080c28240d81b44440c500100e400748400c4c0c10350781e0f00301d400040c0020302198154400e500302c40800d5481041c0382d151604000a4030300c510000f5207805021540c80c0400e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466451906 1250 466450656 466450669
    0x1401060804030c060e0304060e03010b030303040308100306021c15030305090618030106060302120901092409051501050f0a030507090b0d06110a03050105060c0a0605090f1e1507020c 80
    0x4a8003909200041504030784c2d40d0300584170390650300c01d107039000494204613164010640380781c01c4608800a00003110944080317662804010809410031401074089a050004040101e01442c0c01c0f04095642e00d10384007180040310b818024900c03480e890301c03074222254041c4802960a89a260f03076200e19003040c002c1045070641102c8010000011980504d40040d5000d120321307001009107440168442805000b1451486002024220180d05120f00703035000030355054040303103441794992003070b4100e81020401d6401003032080401003540c803d04081045540d0782980b02c0c1d040310000c48119502c0204003080c070203151000d100051641e0306c003420a20410549401000707a103400507100401d10700f2251640019a401e80c100c0b45451940001c04204c035036814000e80303015140982d1111718050b47c4034021556007003000700c041c2040d0350707031008100901002c0c440103800003a00011507107601101030300c280075100c4c400003010a1b03200340e8a1038030b20800c1440e15103104071030781e4018040c100d4000060210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466453156 1250 466451906 466451911
    0x50402150d18150608031309021303050d0305090c0d030c110d0507060309200d0321092306040c1514030a0c0f02160302060f0c0303010e09010f14010608 67
    0x21240d495020700d491038180982c800105501409003c0e003604444066607013150713555040801d003078104128040301d0044005201d0211484280016a549041540c00e04800d0040e00b0080440c010740040485080c0c1c160001c50040c10300009035103d8454140401449400c1e802c070040200d5000105840403070b075035030240035403c24050300d1008840415a04d917424140700e0741011380030990702c05041040c0304415502d040380c40c02c090201c2041e100c4d1580059a80e000200c00101005600580c040c22902c1030341c490011007940f0f1800380840e40e40303490401ca6a4980445250310140d00c1012202051380c00034400e8011500098030b00e1425040441c084040120300400406010a041c50b600360780d00c0180c0103510a038252500041d1062070714100030082c030006103e80c0c0840d80000b069068140e078050504007181e50454000d0f50700c50403100b04a060b4014420041d0490001100000f801308030086500d10641c0e8410080054540240311402241c03035400c412280030340319400511109001307043d503030f4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466454406 1250 466453156 466453177
    0x109060302071b0e04030305090c0619210b040509010504210908191a010509010620030403030806091003120e010e030f0c030c03150a0b0a0314010b09090105040215 72
    0x1c419000320120740f0707800d081c1a4031a4900f01142c808001c24560f05214031900203240d5400f2304444602c08000038150b01603d0801c200c40c6844e0b0102c5c2c240c2034083d8420301b40c4541c2c0e0040410906502d105403c000f0310712400341c14060707801d00c000250320300700600c1203510441d03014000400b00700d05000e0300c0c09c80c2e2203640441c1042c025601d501160081d000c0000c2036001c0710500c48902c8001261800002016546804110354031080c40107015a648000c0304506503140707454406c40702110014412000360044c07200390070ad8040004c010040c180d00c402d41c14451401039401102d591070740c001d188902c56903031202030700030140c55141104040c40340072450540c007014035000d10040700b0100000e08101a220b01d030700c0e0301c0c4d11008440440b802c0a00180b16000c01c12000743c10202419000c405401300003c000040c181e503500b02c2d003103156651080c1480616000040040350340e4485504500a0000310000b522804600c0c0015030b60500500440f48250340c0902810200d4000100904d0160052440207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466455656 1250 466454406 466454423
    0x4080a0909060323012025080d0501060c05120d1103090706080903070308011e0e07080a05160e090a180507090b01030b1c0c0b0d09020a05010e010906030207 69
    0x40e0420960003110301a6020705040d55841e16525108425502c00751040504c1c0c1c1d0601c034910b0001d89040100c0150080c40011040c0e0340d042005601201525101030340e50303041e1804020b602481030000140c10071044143e410011a621007105440d5000e07162002049640058240070303612201705d01400400081000105211001e403d11a0594004460a00f283c0e40001c0701000902c1c3d0151200b90403201c0343c009185098015140100442014050070481d401300010b20303504440e40c0100500104120115152981803050000706240300a440b081c41450914011400b0001040542007640c0c42584825030781c1c10070001441000c034001080781e601250742d011800b62494580d20b4026406100710080c5c441181000984421219410309140c1051301c0c104154a868403400318208500d41d1028003165a018546008281010f0a4000c5140c41c1d102140c90001c0000c4e5410460b0b0482c0300700c078501c0c0d640c0e440c0c0c801128080c030b070f00048a00092020004000071070190b802003074000c3c005d0122 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466456906 1250 466455656 466455659
    0x40f140a15121203050c0906040504150b07050618070b070b1003080a030e150108030a081f0e160f050f0d060302090106020d140315090a0b0405010b0a09080f030304080a09 75
    0x440340301c40c05082c240c0c0c915504003240342440e0b605200d8141e02122648a9500302080c0f003003c40c280740503e0280a0146d07646000042143c6e014808200c0104480b1100c0b681d110b04601c3c1903900c5502c150b4040c0c281f180d003007104600fa500d02103103070016101000c003414100040c0341c4039a98030312000340102941c0c4080d001d020001c02d0101005050a0301292004108034542030a6249131003641e0f01407862807001c030001804103000100c100c0324070440c036140569050b12014032043e0f034080303020b021a540805001c000903000d50342d0503030282324041c480c014800030320018100340c03045c41d41c2442c1c1e02c001800c100f104003440c50450001e86a441c041700350002d203094403640416003441003038020902580c4a61034403c1d031960b200c4404001518901c81041c19030520400c2c00b00c80d803003400001c3d4071406c6014002441807032241c0c800240c05500410500c00b5580d80c0b00388040d5540000000300000c2c0d484000840d000d600000ca00c01c5040c000b4004500c0e540d01e079114407420307821403903e000c01c01805450 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466458156 1250 466456906 466456919
    0x6040b030d031b05092115040c06030506010c02090a0c020a050105040804050405100b04361a030309030c102d1b020112090c051e040f140a15 62
    0x856864035200e0b4400144421000d940100300c4028601c0002c200b06040016805503200d140030040c0e020600b1000e0010080c40c101814102104800403c6031030310818200410710005020207811280507031410401c03610340364011290b8140c18200a034010840f040481d0300e4800c2548000d0888407184161261491141e8420b0309640050b1816030340c90f00b02003070500403450144195500310503009080c40c0c0c05403400390180c4150140b0302c150440481080031076600ca1903590744105c2d1400502e81c0c040c4c0c0e0580340342407400082c100c86441c00c80c0d01c5145d64030185603041c00070446150006c014000c00f040c01c204000c00181d0003002c1948070030401da01c50051103410050044410140741038581e00030410a80b41c0007040c4203e03404545000b10f08840210001d40d800810a061240e100d4102040c04091410241e020000c180d000380d800400c01480d0484800300b107104010310880466003804401e078030180310025150710107030f010340c800c3ca8040810902c01d01a4402c645031500c0c1403101c0901f0f51b9895 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466459406 1250 466458156 466458163
    0x51c080711040608100e0105060604080703060f020f040321030b0a0905090a0f0b01060206060303121906051903061109030d11010e0d080708071d010c03020102070b1003050d020f0a080306040b03 85
    0x44100c1880c1d91200c1b01c12482010a0003151780c05442501c0c001e089c2460400820b0b5502c1039444080e115903031710200d1503500c1c08282c044607000c1500c00340300360740d5030750301d1621050b0700c6101049401e04c61070441030031480d03610a0180c2c50504500514424149041c05030090003000040d14800c0c181c89030092000004a0b082e082c072052038050b0003134141a40c07501401a00300700340101140e00c070303400030000064018802c0c010a508406242500d44030410386080050003050160020f40d8440c50781d0b0080034420340201c040c181507070b04c2048144989e900c0d609003240300307004180b6502d074503400c2103800d01c0c1c0d0184102c0802d00c402c82c05900201c0d21804c0f80c0c440300c0c01c140451065100003070465040061705c1d50401109904601c0c3d0b803522440580c8070f0038002c000c8a0982550604202084880c80305240c800d4054412407500700c00c1580c0941800701c01c80441c401e8620048400b401290b00d00040c0c58004952540d003a2100c1e0090702c030f806c00748e075180300103503000410803540b20740e50b01c501783d40ca0b413400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 466460656 1250 466459406 466459423
    0xa031d061309150b070b0703180609151d060103030e18040305070209070c02030c13091a070905150904022b090b10050f0d1a090106051c080711040608 66
    0x1070b0000141c10120040000e00182942c201070780d1030b5800c000c1e041c005811541e03040c1d80501640380c001003813030400c1c40d400030815000402508a40c103006c40d050074846440380b010710703110140d041089260302d03041302da401002079030000407900d821150040020900529440160702001490784007445200302940000540c1601d06070000791010410904600707000684541214441c02d002d003940b0711070f03070000391784100714103101c1e00418045c012000303601e116800c6202c007541c1c40041c5204841104c004224400c200729210000070301d64141c000741e6803c0c200340a45a03664134001907860b03c000502840081d44c40303282100744081034410310300c0c44d486e18a02007144414238140f0104401101c0d003000d5058600c06800100358080d0b425040100baa20007000510f50f01d420384445001420a00f06503001040c03800c40c40300c40d010540c4c01c001c520385040d80000c040c0c9604407443c0d00c010a0681c0d01c1c2030401741c400d070000d004940030498803010856805600030111002000441c8254851803240d00b0080710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 466461906 1250 466460656 466460669
    0x709181a060a050d02060d090503090a03050c090a0c0f0c08090d03081905090304031520040806010e0c07080c0f01020429090f0111010b0d03050309010e0a031d0613 72
    0x144051004601d40480c0d500300800048400920540403500000c2840c4110206404c8848c0d64518a0080103002d1054601d90100117281c4451240d80781001d0f0b840710710004519100303450080000368030040b24484c80c0b803410056503802007190300c08a420348072504151010b484500d018003841d0402c0c4e407040a100700c014440d9496001c7c904005d0380710b071044142d1b104c0c0041c00b0342c1400c5c10443c146e60004192000c49400000c08440d0700c40e01c0b03003644002c2c032502074001b00c88407201100075190700a860003801151405803c6500503a6168445858a1004d40c1c07031100008041102801003101c02018041680d0300030260740544e00c3c010011403ca0707009600106202c0440c5409040e0502e501e086071708003400001025141285a1001076440748080c244c0c82e05000e2202c00003605031500358450320801c80301030070310403112840303050181c0243c0007280c80c07010070340c2082c0d45410b410340302281c40030b47e440c0d15032118903250500a0040e0356030078044400b2030300010306024005200026010540c024500d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 466463156 1250 466461906 466461953
    0x1208100f180c0c03021b0d0812091e0a0f0201050c06010e1e010b040909260d0513030c08030c12010311010f05071e0f080c0706020c0111070918 63
    0x4810350240039214002e8400090240e440f00351400b003a004200c03410800d10207031120008000010000f0b2040d0445d40f000361401d84041031511380813045d20a55030103500701004036030055200c851b24000468803214186080d41240d0081400030b94201801180984141009410110b00051091615009070301c0012a13030260003c4c004040140b1808503414a10300307041c1c001541c14a80c00070800d108038414250314580e106451000d0103c18143d2003040034120789000703054480b183d0010f0300c0c3d41000c0c801884092a1a020403507508102c3d40b024075056250721204000042925103240d1500003e22138288000200003840c200240c0f041c01c64082c520640000180d02c401c0e02c001086010320f00c4408042c014100300c48400314043c01e807840314460548407048401d40851070304420400309107000a00302c001c08a020094034801054982c207030f9000c5e5007100d08a60300c2100444c1c844c88501110615504009000d220444260704082008201031034010700c00c100300d6861422000703c4c690000307001d58 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 466464406 1250 466463156 466463189
    0x301020c0a15090c05100e060d0903030605090f18070f06090911040b040909080906030703051501030c0c0318030c06020f10150b1c020c0f06131208100f 67
    0x80c401e4640207400c1c08220040c3c0b80e903510102030700741d805030902ca00b5004039008126442060740c00308011002d40080d8482c19080421400f5014442003200424180580880c807401d103800901d2040100076a00d0540c0e443e07501003484400e10040460300d1600541c000401c00c0c083c4409034400800c1c00d41d6803801403518100300712003101d50b9402c603030328800001c000821001ca40082600d0907240d124100044034903041c60121030718410400640c0d001400807081054080d0990300061143c80c045c0d21200020303440c58011400c44020382c620b0300c00705401c40302c2003011078443da43c0491010910254114144d80300c0c0c0303d518244036958041001680421100400e04100b8442d00b0b145540030b41007404090012100001c880b05103014501d90640d020560f940c03440c0d03509880394110321401808659818102e0115034440c060000d900c10302c1c0c45144089600f5007001d500d00381106800c260009060030300180222000c10700030b8807080558949600104400f51280010401440c90511003031082 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 466465656 1250 466464406 466464413
    0x11120c010b0a0f0302190e0a020c010b220f09020a03050c18010608010e04030302130311011d091b07060f0203060906030c01140f130b03070905121002030a0b0301020c0a 74
    0x10346146003540d000b0070281c0410020450310030851400d0b80c2d030449186401501c0d4060001081034541d1003000301d003425801380b0880301d4042c0e00400b8120b0012000303014030214402480099080010314a140040201240c8030484143c2d2200001d8604a000819481101c1d00026050001c5400c1139580b0f402a400302001494451039010481510b21050401981f400720040c100c01c1051080405101c3d00f08001010148170f50b040300d103841c0600d14803094090302c900f05440008005203100e4042404400b00c0a421603031030200c2c510b4614010315500d92655032118000040303c0e50320900d4818903040c00894000f40c1c0c00d009039095055901d000607103d02c0c0510801c585c101000d07000c030740030717030810001e102d220790f0b00260b00c40700300740c2c41258036035502d88070284c00c243d80c40b0750307031584034038a540800124410314400300960290f861070b69000f0f207558a401c1040307091844882e0691560340040c0c02d10b495240d182d0003455110603a00f40020b00c10b00d0080c08682641e110002146080c0c000e42c10781c1003003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 466466906 1250 466465656 466465661
    0x30b030106081b0a030804050118090e060115091406070501140c0702090c0703080609100f06050c0d05030606161b0312031b0c06090c0308070b16020a02091611120c01 73
    0x1000360403130b144500c007455074a030740e0814403450254a04008140743c4003099981c1c0f40b51000300412488008001c03202c4c4640c500d130744854081c018038070034110b90300c020032800d449052003400ba40d008a2116100b501c10301c0c104182984440001c0300c00395200c901e900740305400321600500c6600440051903881686204102600070000c0c0344001e500018492240420303031040d032440c0e00c0042510350f4806034a0380400c9014100b038a078071409642d2036006000c03614a0b03101c405409114400400c82d401e048030540c00b5510750000b240c0082d0014828080041c8404a068440d149240104201070003040b00d82420750501c20380ea04140c44000b28494104000c40e03140c071034055482c80d4610f0b8440f41d410b8003d0014400c1003021805480d4a48403a140c009010101b500750004690005489a448a16140505200c80103c8a4a58610381855103555040c00400c43c071003071030750040070300146585072013a110039034078403c10741410071020040740c01300030303100b041060b00007000c6010303054499000031607482c04d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 466468156 1250 466466906 466466953
    0x806091e182d06041e140304090e01060e0609060d0303060801230a0903080c07082502210619090609060213051c02060309160303030911040c020c01050307030b03010608 74
    0x35590140c010440490303185552001102d1071032031000d040d10813901b40012031b84210b030852100c1e0b010001c0c000400ba42d051344100f50740c0f0b50b000d00900c2440c0d52b41d01600c000c0b1404840003504040d04000044051409a42d0314004620074200002e140f9101c00040d401c444006003140003511180d00341044c2d0a01082c0c00c0750744168108424401c034103003550f00404000c0054001001034a004c210309007000b03008016550300142103c1e80d050400444281c11002d824410020b0b4001c00d02c10f407401d40e0101200001e00201d02440e40245843d8941258811804030095212100d03a91f44001010018509014041c0010701510300582c84a4400140f00310704000ca604c002d21800c00071850010450250b000304020313540403100151250746403c0540e0030711840880900044003020000700405405501c01c045507405030000c040681e80c0c41050104407005205540003581c000408601c00751300c00c0303005541c424610b24000c12000480d8001c6421f4500503080312040f038003d91181003c140d041000100f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 466469406 1250 466468156 466468243
    0x6121005181605090a0503033001080a0b100806090601180b0a050d0303061a0a080604052e080d031a01170a02180d030f0806091e18 58
    0x10300300102d0100306041e180b010141440400b1422000603660f40740690020700018080d0796940007c100c8403903801101c64911103001c0c0c003420b9031800780c0c02032041e103e0589144c50024204441192900f8480c004020400280c60180c3c8201143c12481482041d000300b030031900404565051000d030040300d01e4005401c00d845468000800003d5450b56060001c40d1003c1d10f1000002c11079060450203040303107800660704821a07810441181460400411684aa03079031400c1c6a038903444204070039110107907400010400d400300700c3c6038139103c0f2010030126031456106d9101c19541d070745850360810004848980103c1d42d103425050300f085d011034003002c0504092904101025199a0038660454060023203a4075a90101e901000700c50075401e121140400200a09403844851400600e0009201440170000700013501041960810502d031602900341520300145491102e096200c0381ca10007051054401c0c1c1489442102c1c07002400302e440d540100342107014088003002030401c0d0780c010345180003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 466470656 1250 466469406 466469449
    0x3032607021005040c080f070923150102011b020c03120a0215070e060f0a0e010921080706090f020a0b030106050a0f0c05070b13230105070206121005 66
    0x500aa404282a5000c1402c1c08001034140c4990500f01010142904500c58a204000c02d1011151000500d541156031b040c109004150000c12800440080070b007103240f00401045c0428550b40d8a002558003280041c400000c041c041d40b02030019642e800703a2000096045030460784840c0c1010720903031140b000340700d41c4181307002401080207582d03520a0354440c0051a082020485540c418100310140c50f03c0100090f8546000d1036052419034810350520011680300c4090700709950103132240c0400c0320415091b164541301c0300c1401c3e020004980c4406c8445510420070a0002000c078840d141d99070b40a0070201c030a941ea2413050010003102604480b80000c814001003145642c080e0031500d05c00f8092038a001401d100c50740640d44000c040b40c0007031150089680114228031040c3c080c21040c5800000c0041c001c2d81c1d80080300e000d501c480b6070b4403420f8100d040b8100076940160300800701cbc54805400d41380380c010a0040880718207403e0780c10350403a040c6484100460b250803a0100c07401840d41c0c061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 466471906 1250 466470656 466470661
    0xc060306050a05060c031207090b0d1a031b06030615040b030a050c070b13140a06150906080c0603070908150a0c030501060f0c0606093602030d080c0403060204030326 73
    0x107840c0e82c0c1c01070007c0c0f02d101c207007404002403001d0721985102000b820f90200d1301f42c8962240311620042c04002002101203000e034610390303005103000250740d000c054696203142c0742d284514040c00515480144420780118200086d00607030f101d2400144002c140650b500c5440c2d0402840402c02d884000c1c20751209410188100d8000c108190242908251107140b030028260403403921500c8a25915060380035406841540c2c4203120342ca0300038612a11b2510205c3d01a07513262124041220b400e801112229800209032900d182032580056400c5042070402c8114569580e11151510b08440180464004002e060289514036802424000c2e800703801c0500456040160080440d12140d22142c1000b80542c3d124090000551107903025001d9000b00b80f08408201d0401c41d0759100701510205400c1d0b14202c0079801c086c074400280e0305c0650003006440741c1e9613210300c12242500b010b0082e4204817800c12000001482c02c4c030085c8000c43c8a40c4801c07076460ba0388489005c401c108c1d85021103541190104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 466473156 1250 466471906 466471927
    0x1505010315020901170c0a0e032a0301020d060816060e06030402040b28060809120a0c140109200a050a060c0f2010030213050103020c0a0c060306050a0506 68
    0x503540c100140850050312480554012100c1c5500c041c2c030500702030340071014400c151b9450802000c0514aa80351044503a4000043c5030b075441021041d49855200d45803e40300031030f1906401d5000400080c000340c1010000301540d011180181d11100301903009524242c481140320020314010134850811904000030500459218407001f08000e2080d40e1300c1000544a5548801e04c400d07000d2620280c0700d144046142e443c101403603500030000030a51110011311f80d00000100c4540c00301124003103074205030b001d02e1300f6600701d0b01c15401140d03200001c3d04c5c8010241402d100b0140010b0041000d4402e00d9819040c0083ea0300756680c07001c0c0a00c4c60070800744100d4442c0712101049460514080c8095001800d0180e40a00c46c81c60082502c10042c00700c4401000400c0301340100c040440714005c030700c160300340190103e205601088201c03c1040000304001d600a501a2215000401c01e0742c0b041030702e541d11405d0911070394205e44003199880b1000e00c080d01f88403100700301038201660200d1400a9018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 466474406 1250 466473156 466473173
    0x1030c0f031101050f130b09030f0105100e06030f03070602040509011508070e040921080906090601030305131502060a0b040c09090f0209180411040903050307142515050103 76
    0x8042ca4188400000c040c40807803036600c1240c83d800f01d0402e003101c03030644600c003120880d03024510051003072041c4649440030034018494240a8400404d240c0d400c2da140c8005050a0000140a80d5040c09042c102c6d060510003800202540c900c00d00006075900d0800c010040c41680c10b0b00500a10010043d05401141c0c10411a0b40c02003854280f80051500740c0000a000c0c011592006120010000240426004024003513420b60402d4903a41107659078011115600d0100b1038500881c0e034410740040010a000700024583c8011440034440061f03128078110301c400c51070121740401a4802000c203c0b1451030352060798000c10f4121418050303c80b070088001e002d0640350244503003140da02c824500800346140d048440342c05002d441103103c3c51101c8000610603038112002d8440c521504603002c228070f003d00c90031440503815140c850568540720b0040303c00c030a104012a4030150200603072050240c2c48200c0021031000011100513081c2146011203104072583c4421900740e05200046c070020310b105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 466475656 1250 466474406 466474433
    0x3031803030d1104090b1c032601170f0304080717150103030c1a01060c140c150706141302060f040e04030e120d050a0507050a020907020601030c0f03 66
    0x4000104500600001905620614082d1140245440c2000261240142c003820440b004101d04016400f040014000300c018000341024040c038900310f8960020b801400c80b0041110000e00d00b500701126454009809002038101c2140b075404014100c507910400c001c03035001d40000d00040e40c00c0ca071410301712a17030b100b4050040d155001045207213020150410030440700701180c061000441d9594030b0a000d0020b40004070152410700038906e865007042ea92081c424102c036140e54030481d0b14121a1104401080d214654100d98020f180040c4107a60304c2560759031200c0040640156143d48525110046900402c0544030941400d03080200d42c840c2520084130158041d160a581c1e00045598540303113210720f40003015020000018081071543c0420b04040c00c40007600c1c03120028080600103955205090b0b46040021020029004154411005000d401d407107141110740d07002c4950700054001c070084602d000140d125800400503c8103003420b0200034019580b00c508250f08503202e94000f085030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 466476906 1250 466475656 466475677
    0x30109081e0d0606080f010603020403121b0b2412060408090d05010c02010c0e180105010e030a0f050303040b060d0809090c04080a1101030c14030a050601020312070c0201021b0303 79
    0x50784401d81c00300078a045441c04a0742e1001080410b4940002520011041d55003028140320071002083d054000e10850301540d80080c0480c100b849610300c01c80f00300302e2441d02030340c1e500030390058040081e9001e0f110303a004000a1a68944095080300c00c84a40c140a01175030344140350501d4041a040004a0314640080c1c01000701555113259501203050700700807000041c899071803c47c0d180342e45641075001120f415178990320b518a154020013080740280040c01c848145940200c01044990300070044c00503521000350542c0d42008071a2075986441c0041700017a521038100108020030410000ca0296005c00e04071004035440c001625201040d004200e2082c4c0a8203025020030032040101007907500508040d8122503100c212440d040c1e140340b104e0b1228601082c00d02641d03664441c001d4006180c2110080d43c85402e40d5a001d44060141001802840c19070004021040d005003040410300c4c89200713035888090380c094082c0700091401c21407148003070841205440083c0d9958000c000c45100051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 466478156 1250 466476906 466476937
    0xc0403020d020405090c0a0305010516050c1f110a0801050901082a1809030702090a0605030c01120f0c090e01080316020108180607120e070506090603070306031e050c03010908 77
    0x880e0b107942403038150741b80c035100d03480000120000308014054000341d11848041c2c90340c0c040c0780c9800205030745038080d01c1c14a90701500003c1002c1d22441c4001c04001c0f650080329008100003c0b000c06038002544541c0c1440e0000300030200602a40c1001d502103401080240014404000d41c0b030b80c07400c61610440c4800555011050850b280da40c0c44459140d540c5490600c2e00f8160b051070754041781e680e840040100d010341c01803800203d546120b03200340c8089500260160000a401c031004540c02e10926501160b0190b0705c41101100380c07514411112881500e8880c074219078208821200954816400000a03a0082180f040b43c0300c0000f0105140c264282003440003a154003421810140d4001c86003080c521504040016040c0d02c0012524201042d0314100b042c100c5603030f800303a26004e85010781a0007250130458030401c0d041401c011540191145400180180c490303561110003030790300755007801c207407c0c035201201403007420305c013082e002e1500718002c100340040d503a511400f50003039001c40e140010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 466479406 1250 466478156 466478161
    0xd02030316170f0103231b011727010209011d040b0d03020d090f030b01030f0311120d240b03090c120d1404030c0e0709030f0f0b0c0403020d020405 65
    0x1e0180341a401c00e0b07108141c01682d0380c030f400b800074410a0024401542d081138006891b1003030522001d084c1d0131001000024240300c061250000288010350aa0a8100120501701742d603810410080c0c58041c202880e00c0102c502a013502030901c01c1c0c20503104400603441000340d0451681c02101030012280c208480406010100f40020010101c00340001d0700700340500281c004055000c41c0149100356180c0318200d8050726414145c1000545d80070042000c4419030042c40824a00022110028480d00c0c0c0f80d138030003601e0107a150070070000040500c000c0e00c0219484e03c003c3e009000f0345020f5122803081c40c01a02d4034441c000007542c0b80d44914039038150008040b5050b03100a02030507102d10b5014010074131022941040301d50741e90011210200041c1c1d400d12015100d580d600440c0c00300da801900e01503c59080001092140b10080c10031401d02015940000004400c3c4600ca886940510151174956840d42050030342d0080047c808518210104002e000580d10103501021480e0192130025113a0f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 466480656 1250 466479406 466479451
    0x9011e0e1005030313030314071a0c091002030406020d0509010e0d0203011808030a060506070807030f0e0a15032a1202090402160303062c040f060203010609170d020303 74
    0x40e01507000302c3c1c0c02d4080054403085020000d03e0313034000c4a00c65074544c00900d03030460113101c0303602403260002c01c00034480d40544038169480c801c00340c000303c400350240d2074101200c1c00282c1c4900c02403103c00160308049010401683c050103600e020b030086040c1689400c400000080100d00c1001da02841340030300c5401c034425510254086808403003841d440e12808036807030401d2074268004582c407001d820b040c8000494a07003080815150316603480a030042c20003103a690141c0b00d1031014030710841000000e20b440c00ba296180d00f001801001500004a0401e45e007110003001d940c5282140185c4070341049881c003640f480c04080302c8001c2401e14000280303000020201001c2d204024109621a0011510600401514000741030f2684a51401c200322a610820620f019038800c6d406403084603036038031101c01c910807010010f0788188a106a18414000b9544a0040b038100380c020b01c0016040c003400303002d0700c040e0b410400120390950000b81718020355407500954a10004110365041180c1c000b0300b41c41e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 466481906 1250 466480656 466480681
    0x105160807111c0c051e0634050903010e0115051002070b07030e0102070e04031d130e06010503070b0f030403140f0d1b0e0f010503060d0204090b0609011e0e 69
    0x1d84000d5005030700b03c805500401084240044815100c5000d2415060410900c82c24601c5e46d030a1001c3c00703006c940d900e54102c074610300e081c1000020800740800040c15810b494000155050007691192034460b0190b1092500711106c941c0b561310583c2c50702c013510380c2606c0480921000c4407400c40b01b4901841641200328104442d550191140ba1b40c041101e07400c0580151240704005001c0c1e0880c1e10349541d803106c40c040e00300d0686000d40440d41012400a00040c0c414140c40201c0d005409110804106003a40044444118020005800040050029240c01d000c01002000f95480c1a41007804015904d0f070a4440607200400f071004a000000300c045180341030300c01c84590304048503100c8071100f422601400c1540c80705481c0c550042c0300c0103011401185000703000c0002401c0303110322800d00801034130b43c1d0b80080c22a03070b070080700c003004440160b81e0342c041d062105104500310200d505046040c414566010382010510503c01207804c0c4544220b9854036044800520030425542c40301e072001d039207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 466483156 1250 466481906 466481923
    0x10e04150c270302030f15070e01030209090403080a0b0d03050f0306150f04180c05070201030f110d0608070b16111f0503060102060109060f050603150a0e0108010516080711 76
    0x481c0031410800203900340b4080100c2d01100e0090f800e41c3c1c2240c80404499480c4c0c0069104280c044600d074021507102c611404807551800c4041c10018913101551001540c65001220210300041c1c11030204039a421030307401482c0c4a0407041d5502c0480380000e58000e04540100d00041d0501c0130302100085081d41c038400450828140d03c2c1e20155603484410005216034454007806241141c1e00300c0c104105411442081102201a500d950130a0002c0c3e00450180124211211100d9112829080c098950a0040035980c80b4890300048882c90030302841d040c0612a800b4200c603040900c02d803250b036506808020400b0b94800d0454958411344000034030200300341380703040648525036000a10f050760401d0040d80107000036004c580560307a85448220603036400340994011620b0400342008103082c10300156411981e415022102c80c090307500825200f004036804010040f40c5200104036460080c42002c0c0c000703010000001d1500b09140d0301070030560001c0c1c41c40d020404040042c81c4003440a021106 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 466484406 1250 466483156 466483187
    0x806040f09030215100501050409050403030f0e07060e0307060516030201060e040308090f060c0f0903010e01180209130807020111031b01061a0711010c0312050a050f010e04150c 78
    0x241034003402e000796038810080107190104040004201904c1c1c034003d4820449005a5a440c41c1606240300361010b060050001c80601d42c58000c170114102d001e01800071801054070080c0919071402c0c200800394040c1001d414002c0e04690020b1240035445000c848108100b42103c40c0d0329880c03842c0481c014031607503000c1140011044140400c25034070020303140c040c41841d01142c003004a100c405640740c05041e5000342c150300040004540740788102c0017800240314010000295604500d2581707094a148403c19508910444604411494840300380c5400c0880c400300f0100c1e202c0c40b80da40c125248181d290103418000d644110f0102180100119584c00036449030341114500e26001c0c00e8040c2100b0301990a8900c25a28040c0c9032000700001e80e04400d03040000c5a001000020040d906a8511002981044041c2c081c030810000540141030003880090f200240f030b45031196449800f0441130b0410302c4000340c110700703100104100b0b18856010300b640c80c0e000101d24003102400e072030200300802c009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 466485656 1250 466484406 466484411
    0x5060d060e0f1f230403030b0307050d050105010e090d020a0323160506090c0303030105040b010516050d0906030b01171008100b1e01090308030402010216090b03070603061202010806040f 82
    0x2810550f991450325031048101070300900c038408102404140d2200f01da603100381e884540f4800a40030074031a0b00000760070280541501c0300e003a1540d0200f60014003000c0140c1c0e0701da464030010480c0d0240085600c5e4005480300103800b0300d83c4c0c000402519071120080c068100a42607038080703c07406c1c1c1d4a4407018401ca2044090350b03100301070480b02058242d06542a0303014000c2c000012098100841c000718010b070001c0245165a007070000300001031040e101800c0c10464203100200c040380c6140184000f240c0200c0050581040c9054010a2941c207500180704060800c10344510998001e0090f101c1711541018008843d92a8060341c09298583e40c0310950303030b100d8641901d0184400b940030000c05c41054032408543c0740203120800020343d41c01c03c914005240380c602000460801d03400b40d500300f441403041c0d82c3e884403e2000d00007620490340088a03441d542e00180202c1d07241c01c000c000010f1030281410320034645045156404072560060190504c01380000103202641e90b075101d00b081c000d180e40d04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 466486906 1250 466485656 466485673
    0x4120302010c0207060206060f06030a1407020a0c061b080d2d05010509060306011710021801020d0206090c220218181b0f07020405190f05060d060e0f 66
    0x74080c1c40744030185400341c010100007040c07451000c901c59104403c090110141004a8018003085900040444082c1c40e5240c43c84490328460f907c6460144043e50700602c2030603c0c07402c014140d21950f512030307800d00529000703003107244c0003000b502000f00b50003d01c456115844655018058494402c080820b1500155444540300b900038214039203410a0004100a0f80c980342400300d0300000790b804650541c00000100500c4541301d026130008a00b403403c1e80c0b100b610185040f41a42c02060b10004000f03104600040d030765904100c8a0b90b00000c0348002c140c9410500032481d11070303004030007040c0150004203014003c005003182c03202e010754170a003046603030342100413040d12802a011380c1107106521116001000c4510640f030303280940042d8800d83e0b406403001015040f160b000460b50081c00000788041000340c0d89910801d48074502100200b0130401ca4920080200d84440d0508404c0d40e2416080c00426141c200d40e10f40c580c0e511210029041051482c1980341160304515003003180b0500c3d24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 466488156 1250 466486906 466486913
    0x402101808101401050a120c17060a050c12011e0f0801050105010f0f12051e15040507050408061b070804080318040506060913060819110103050702031903020412 71
    0x1440721000b405400b04104406042d65841c40c0c0c98030038825160b004e10014003c0c058030f5000d840c44a07020313110301461001140d4a41001100c1403441411034038030b8201100b0082c040751140661984404c0405025242001d05203900103410f00600130000381d81140d140b0302030500142c0800101814070000300c20003c035603440031305000c0c1c2400d018150008100101e001400c500441c1d80e84150410303a210080c44034400b100020003002d00820003202e901c0300d10750b0701018846904000340202401c101c449909144001840180c907000b40c100e200700042008100149200490312581000708800541e00d49044608008030600800c1c02c060b113040b000240000e8007500000040281c8902e800795001c4e1180d2000400045070000c030b60050300030400300f103440503c0c6070016000c51104003d0030005085038840c0c0446d40f42c048005000c980610540d0302c95400d100550011010031042440c080c03090345407200f0000e48a015210380807074442402844901100d0180e0140c0e00581452030303100e02c000c01c1904 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 466489406 1250 466488156 466488163
    0x150b060c0a08070c150906031a060f03040302150c0d0e030903070e1b120601050c0703060c020d1101180b092506180b22030f0c03020a120b0402101808 66
    0x881101c1d10400c41c2c200294000344c045c204601440c07a902d520702002c1c034088094020f00000b001e24610781e19031460703040319540c48501a00c80c42a54126032600ca00d05460060300e0a9621708240752000d00150070082c004132140f00726429181d2084010420f040d241c1d4010749140542c0b400c459040c0600100860318605101e10b15101d0f45081803a031100d18442c00c088800392192003a40060300e401200050200c4d4007a40091001d880340004a40d4043e590b42c40f0b900441da1600044001a000b040364180d000d54000ca1461466004d007000300421000722114455544d2885002401d81c410344000989c6808103125443c1200503440c103403040c0040310b42004007814106d000c0c00d000304c0c6090036a0140e40d92260310303000541c0c000d0820f040c030304000c65a10500c4140030800c2c5a200224010020002940c1d04845001983c45200c2d41500c0318158030401420106a400550500258010b44c030b001c1214407a155402c142c05561880d45055800c1d4112042c540c607080883c0640300c26400000d0703800001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 466490656 1250 466489406 466489417
    0x40203010e0405100b0102030a0806241305061c151e0611031e030a0221010924030201080a060914070801120c0306111e040303021207150b060c0a08 65
    0x20000c0e02c11401020704c40a01300c0303030401c10490050340103020313400d0384c5409444c100c0e03044030000303106282c1c4140c0e400e03401304088452400d1b0180c03502c000ca2121140000b0405d4500508004c860300c50038040f00c000c8a80ea900c070100c280d6010b0b1600d42c030340e4000d968400c1f001c0c84003030111800d0104045692900c48034409089200f4a0b002407050702c000800c0c3d40010050b01d01d41480303030b040021000d041134502e2041d60000360074400c040c0e508101c030641c0003c207038280701c000d10f20030b01c1410125850b0000000880d00b4509e0200104c2c0e20107184a0024085111198166582401c000030f064807040b40e0940100100d4010681c0f80303103003550940701840c0070303d10503115101da55900840e581c0c94080f4091900d14911005000c420075060500004e400c1e6040500810340079404641003040621403014509a0310720402c4180c040050300740306050303043c006080312940b03840c081d519080080d80c80c1c104a981810002d02003941e40e03d94005143d40384400c0321070700f0b0811b4017111241c100c1e50030301c000c030703035010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 466491906 1250 466490656 466490663
    0xb1f06090f09020412020d02030f100e0d020601031212110409020d450606030c0305070e16180b1b0f06010510050703170c0301090c0905060a0302090609040203010e04 73
    0x1c06001441034a1402121305880c002c2c2c841d10800c402603820b00c802e50319003540480c1d1600402c1074a6074040000c11010300300b800c000c0408207240220500070307824601c0c1c2400e1079045410110041c000720309100d689180700b000c07510b0841810701000b60311800402c484001c25035070303071000240000c8582554000e04940d181d044810080408003c0124001700c503055580b40d0940c92001951540b16001460070300d441c94186156140800c0d641c0c0c03500d04039141900200c440f01c04120302030040c0803041264001400c26202000160700704840e40b50b2911504800d010108843c00000b09041107400180304020309550b80e0103626913000c04a030408c020f6407941180500e2260610a000341c1d00005034242c100d0742d000d01103210740b8440704c104a0b666402500154180054802100d02c0c4070f9000c20303014420041300003560344a5041407040004d450449545008024010000b40001e9581400b01c4070800000c0c01c1c0107030385004c20782c04940d1a01900e035160341c1c02440031000150519222658604c510311 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 466493156 1250 466491906 466491929
    0x170426250504090201030902060c030301031e0b0105151308100c021605010318050d030504020f0103090203070603020d0b090c09040c05070804090c050c010905010c0815030a0b1f0609 80
    0x100e460684555120115400c0080014141001142030a83c041d480481c01031402145140050f00030425540c010401034046501c0003004006004c2c0a600f0503011606c903030750107001e001980e281c40811802c10b0081c00d00c00d03041124100000443e510889150096075551114516524102181c455100140b20f0380c00c5810240178005a91002c511051001e445038525034000381407000460007803140010100016071044051004690700700b14590f0b48407819039010030b01c4e04c1c06105002000390a9000c09041c0740c113210b00200165804034042095810600e00180c90313071003540050014210440e84650080140820710180d48240c40080103039500917034042c080c00445200850b69442141d0001c1d042c4401400240044602d5820070040304490386403080c00c000e201034a031030848110300401c0710503a40d18105880f84a8110503580c0e882010580c18540042e05880880e40b94401d0450081c09c121014001541441c240144200d107544800c0599104603203520026004c2c005501540c1c14650 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 466494406 1250 466493156 466493173
    0x12280f05060423030409020714060c2d12090309040c02030d24030807020102100c030b12010b010c060b0d0b010f03140307170705070902030c070201120e0307170426 72
    0x141103d00c949002c94529004510303042c5440d02003002500506400c540c100b1a8a40408801e1801c0048034001d50300380e044a690740c003041c0a1018203403002c6885c0303206010603d810f00400000840bd031540303004040c0000c0c4030b903640e07041e4071400c0d8443d0042080d445803403d0040b104443d800805000780b106040c00403c10003100d0000c02450f15180c0c0601600c0b0710b903000341403001071f040794040d2102c1ea00c1801111040070713420700d504050300c02c8081c1c0500020b81d20403000300d640c90030300c40c40e2154000c8000200600303c0040002000c00d68100d0b00039200c2c0b82c0b212180e513516140c0404500190350011a03070740e21035840d0952040d41079082e100a541401e0f242c1402e180710600402221801039020004104405290816590310341200c04141d9090040000008090b0602d00065101c0c516145c2d0450342c0d090548000341c52024800f1418030032500d0b0440c452a4142e000040b0b035030b03290300704007180f04048041014001c98030031500503c81c030320400c070071041091321541e40c018080303801c00e400d40e90350b032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 466495656 1250 466494406 466494443
    0x2070308130f08070303020d06060507050d0f0f0c17030103030e1813120e0909011e020f030402040902130e060711060714030702010b040207110102070512280f050604 73
    0x2a558488050402c0e1484000d48000418040081104a20908026040210710078826049a4082e4451030200e80001100c10400006110105240005041000301c00751846401002180603460440501803100010f07030605c45d9070713044401c641000341070099480da101d1500402003021400d515001e04004000c1e81381846940c41118414400c100d0b42115617480350b11010701c01c406901c030070410300070703c1900c05600b900c2e034a51283c410b112041c00032540c02c2103550f41501d40000b41400b041218070500c1007042d009031030011a604280c04590205242000b400000d0603105e100c070807880300c1172801c80300c0700310307040c020610a1040e28070351034410303040c03104140064643c00c080341c3d0080081d106070740d49204080030700f001d1078000c19984000904544800c0100742282d109110958050324180102502d0b503a041241101409055540e80d0303031000311480c50381e0340791f1594026070301d211212142c04082c00903103903c0c03a040d50b401c129001c500c0b0019040480e02c03204191000d8640c80303612035144408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 466496906 1250 466495656 466495681
    0x9030512070308091b0409030504260f070e0a0e031c091b0b03061207121505010b040b0d05060f0405010b091005030903070618021906030b03070506040e130606080102070308 76
    0x401003900101080140d4030000c0100030055040200c0c180a820321000c521885030340d0072140f06c80300d9000303102a0700312801029803030300c2e084021330046e0750301007030b014442d60220700c035450b802409000e400700300c0002090100782103004503c00765410440c400ca016620f4205c3e41c00c034540480c0150050240900754802e10415110540180d184019080000c40c860742000f1090f070800d00d04031000c2d00d0405c0d841c0c4180500101c0c00762400e5586070300d04d00b0f5100b10110340348106030043c485407100e42e14140c50900020784501508070a61115992400012401d4840c2000c0c00b07003000d0000c2040205603111002e0111715004148214052411007091081e030a01800031240207a2005c801103003080740c242da5030805040c2c400c0c08a04100080304a4070f0058071414501001005c1030545507130303482d0808100800301c9001e0350149101c0d500604040260740c940c2011241540c4a40762a08116514400314407610106600300808035403400310300080d40b41c2c042d4050710f180362084d51040701d15102c40303001003030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 466498156 1250 466496906 466496923
    0x2060a0b0a050906060315030111091c24060803040b040e0603070b190207120f03080c04231c030306060306090209060d09020d05061e0a020304031205070903051207030809 75
    0x10004030080c0031592903c0d1020295600030101c921204100c44048046400c0d110203100c0b504004502280f10310741071a100c2c01c005070000019000314203040e819242c03228de2045526a40e14080202e9203811303440381103500031030003818903103003201d80d981c6e40c5000e40e1145910611825200c01100e8000c60364901d0082824011110700c444198142115180702085400501c00030b01d081d44940b050014088001804181da076600032a002c00a2104909010344201001042407503403280820085c02a41140030380306001d080080c144400008216000c0707414a10040c08540311506c001117000d00301039040d04114152400c03650103021480d516070101c010ba025607442142e101200340010301c0f02951076444034140500040c02240031851680300c580c00c1c03050070b84040d000303402d00400d54a21504480b00c100d401038041e18046181d8506520002c0c182034100c810034441545440120b403815100d0000301003d0358010084d07840c2000e25886101c110340c03142030200c0c049045a8001000018041a00325 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 466499406 1250 466498156 466498159
    0x2030a08070f05121008061303020d050d0b0910080d0c2307030f0c0905070503040203030912120a12060605040b12060a0b0a1d040507020d140705030a02060a0b0a05 72
    0x400c540c41d0741d442a1000100d1850103010084144081030b8000600c0a0300c03405420103404604205060290a50070003400170940e480804840b00ca403c0040e03030000d03409141000d1850031603215805140f05002500060f0340c1507078008075001c04e124090140710703114411214028116541c5030001c0a0a42c3d610300e0340c010103080300c1c1c0380740c801240a1480c03400000140c482c580540d0078050300c0e5030302e40c5203102c0f6010094070001e1b03141c2c10501042010344695a0401c030b13141040c07030940c0b425500090f070706c1c8030701a089405810300654480d907010040000c00c0500c40c5940c441515202440b074010828102c41006501590401707000040079405482250103a4111003882450400c082c040ac130181400600026086143ca01d000101c84140101500304c00b4015600e080c00113a2403500c1035142c0d4943c1c0b2005100c1c501e010305000792250005041031008101c0e080c481030680c6041c220b0b2109000340034026060b0b0000003440b0442035400b00f00300c2d03c540080f46007004030741c40c3c91080c04081140750042d907 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 466500656 1250 466499406 466499417
    0x9161e09030206070c05040c050c0d030603020f190e090a0c050a050d032102074b1410090b0711030d052509170c031b0604030b0112020103060602030a 66
    0x40c000341c03e0100c018003003c0d0107080980d4801b80e031003001c9004c4980c1c110540c4001500480d1000d8195030602140800c0c41c544d290504c5010305540006004214407000c1c0c502c6010324140c4011014154031705000105860004440c0918160420944076984e4120494034158054000301e40f9140c47e08025044c1c0f90f02810030b038601d1140b55001e0300c032456000d0200707200707030a000f0800500301440d00080604030305ca0326280303000a03c0c03090505180020020a951091034101000711620a12206150000700d01ca15031070032a5400d080c0454903c00715410f00c4a14090890b45442c01c81d8a034110b5243e26210312011441c03a43c8101c2e0803921030940c41c05841582d0400c00400a4a0000da080a42c01c100e2035030001c410503030b20700345000d040103107040e201d000700318140d000b00b00400042810b1035a000489005e82003880c490380000c2d46402c0c1004500c604e82c810303140000340c651280401c3c0d5010303503132103501607203035503110100504a2a100b0b9006c03030000b400c000020a581c0d02c044282c8100b10301c6d039180c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 466501906 1250 466500656 466500659
    0x90506060105031f0b0a09050103020307020d1d1503010e0c120a0b01350a0b0a0905100509070e030d030e06040f0303111308010e03040b0417030909161e09 68
    0x44802d90b00240102101210307401c49400d86480c407614103001411032124140e1740c2c01c004e040c0501801059132000d4107052052040040c003039004255540c809116140070314070403451444000341c2031511100181c010761600300d132054540b0400d000b5810ba41ca0300c078125a403595683d815081d98400c91114240a250450102c1d00d64140380d040729a0340c0105040103059815125850b80300e120184d091400d0003818100d05000c068a0401e0b05074000402140a208241406002c070f1049182c9115060f00940d64200180307034409000d4420b006014024030340c0d03d20b410a558002c1c42542d00c0200544203014400c42c58001a00a11038121200c7c00880900b4066403240c50703403021110901400d9003403580307800c521402c0742c1e50b002c0240010320019022895580c10241e50508541546042c509140e004000a01c03241760000c1c25202260a0030150081100703200c0d110714158001e09601e207030402c003510207010f6484566241c4d44074070714443ea650009001c4109101d142682c80001c0031000c100020740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 466503156 1250 466501906 466501909
    0xc10061e05130b030a140105041403131a0d0c0206091501030b0a0902030a02040e010624140c0a0501020f041d06010e060703090305070329010807090902120d050408010f09050606 78
    0x243d061000010140e03a01c01c038064680e100540e00303444070140165035401c100010014040005407281841000941c28180c000203400000d400a0003030589004207003c00c2020000c00b80c2c00c4903100c2c44850014010800320f46e00c06580c030b4805550340341c1580a4054940e541940b40581241265049a5004a03641714254038600410401000b41d030140660030742100580c94501035000c28072000e10001450510740b080e126580c101d261507071445942000380003191903601001c10754560b80580c056954a59106a0052402e5015400100b00b54000b14422102c1e10b8240c0c042d00444d0160640c1c0c007882c40d09031241c040d150340f080700c0300350100307100c408105040e05101c00038004191290601c50042616500d0b003d2402a880e40112401d15548014040410340d90030f4400c4006c0e00354000c445503505080e07869848000364080d003400e05a446015a080d96204002e51075a8402c1e030042d200340c0a00881c00500c04c0c1c0c05030040ca50070390300308180040a03004038410b0b410041e400c030000e0302140e03c4000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 466504406 1250 466503156 466503161
    0x11d0f0706050d240503010b0d0f0204180c0e10050103150b211812040807150302071406060301200f0309010912020f06130819050c10061e0513 63
    0x1020290f00c10350307a074580c0c1c0002044401450f40d625054061000d00345c580b504050a44004060f02800340380d90301c025600182c10301404403041da50446012a030b0100b2400320410f0300144030f0000d00307041c140ca0400500d01f411982600d004085c00c0c140420b02545078001034003990f44564010410042006003046499001c2018100741c070950380000880c644c100b95480c0007500107540c090040040704502541e0111f0030080c0d101c03200c041c00b0b0b06030b04061a003440d86485444a11a6102401c400440c4a0310503100c0d0b411100441c0c4d20120490381d046000101c280c0d50a81206e005001e17620308640b00c01d1081020350907100c0d031202c2c414600c0c40c0800c0355000d20015040075051010a640351000100015440c803010000788170290300618002070f0b148501441c042018040d01034520001c4954408030303400600300c601440d04603800c40701e855810b0070100c42030700c9050400d8aa5008400000c0040911780d00b10f0001c48605020114004070810756034010100030344a1168058000b0350651106007054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 466505656 1250 466504406 466504417
    0xc0901120b06130816050910061d040e060403020d050c0c041e02070503030703050f0601080a0213051c0b0109060602031605010e0a030507050d020109020f210f011d0f070605 76
    0xc0c000a0038840b6400c0f46050040702c5070800a195004410301380031090001c080306000740021101c00c032460030200c08071050b5122a0007803c0400200e0816009400801c042d0b60110b000c01030401c0112001800b642e23a103541081d00c080700140500200d10703504074801c030166031026000c580034003030f90030305481000000c26500c0318004a8a2070400c503152030303080307a00c00351050f540544043c0d682c030f18240708000c04a8500400184030103000340140503469078032800080c2c0c4400d00000040c1c1d02c000f40d00c406a5000300690103664010b8142d2144c0c0015410703001c051041c03505c03c02c042600c50340c031341050720f00381c802e140503640040e44184003a05864030318584110140d805400000742c000c0c03842c0b0840342000c0410000350045a40010b0190400100700800301101840d84000c1084074000c0c2e0008101952180701684102826420711003128103251007403040e0315410003120f0035007001484680c00b808002000c280880b0446207100400c410100d46003000f1902d174405808403030304014060711150400d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 466506906 1250 466505656 466505659
    0x7031803020318010908011d1207050c01050304020d060c02010f0c031406060313051501050a0e041a0c0c03071109070f02030304150e1615030b010816110a0305070303050c0901120b 79
    0x241a800502d0840a00c100060740c41d9802d80866123201c2c0e00080351512008141c001c0c0c50301000c12031900411000720798000408000d1800d60360729140c600001d002012071240c058240c1c1d1404070a6160103030150302c802880d600303905041c40034000c00740c0c0640840f1907031010481d01490381070000324589081c400a5901420311020740e580040c00307880d2203141500f40400b04903103d5103040140094541607001000404451485052510b015136511400e40e003440c8001c2030f800c81100209202c0c10044040e90100c560400071a9201c84450801140d0b8000c0b072500140241c5818001c188083e2103109184040e0200740c0042d4615291070f50b0360b403102601c900e06008069130b20282d00342204005c0c4501320442440c441c000c1c40f01b504181d0030f4203144400c609040d0034149420004181c1b86d8000010369445641003201c0110750310a410281c506805a000c80380543c090344003020b04240c0c01501414643d40265400c0285696009600926100b04e507022400b14101c0030740b0010300d070300c5908180c482a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 466508156 1250 466506906 466506917
    0x20c100518030307031410060219031b0c0f05150a050a0201060306060e06120c100e0a0521010b090f040803040203120c01270807140a1a0703180302031801 68
    0x92501080d81143c00c03d40b400000a0384440584020308a080e02445d001a00400fa0011362894150301075a00d002c0480004e43d40030280d40700c942454000d120003040c0819801d9601009155460034000148060041408003880f0714004609400e048051600c2d91980303aa036140b0b08918231006030342c1a0480082002190b4a900c00031000070f070306015040080c011070544a00500b054030400034980e07500c030698406684108401c84a13a550141800084181c2d41004400c076240840032131014051600004c0c0c000130004040303840c2456990807001c5811040b0020890411068100981424140da00e02c00b0710318a2008500840ea03003c0085030860300c0101100c81c0d10000c0984007025800c50300c81551546d40d548018440250030302c0d004203200c0e00350304055026400c035513243c42140c0070303404002c2c1401da071400c03030b004820b0820003500403625081031998130614021ba1242d000304c6400c80c0c081d4000703800c00c02c1c080c0307908411400301000b5a6154020314245040c9030412203610a114481904100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 466509406 1250 466508156 466508191
    0x71b0803040308120703090b06061e040807030212070503070e0a1401030b09010b03010b28170109060c080720100e0607020c010206040503030f181905060703020c1005 73
    0x154204010401180310320343c00780e12402240003800e101c0200420507014181044c00c01c0e0b00184480e80710b0340d4000c100702c4510703807101c00000410b80f4800c0c810051007128000001d01213035414000903110100e174401c42c1d030584804001600a929004284112a01644002e2050119000011026501104550000401c0c801484c03a5110140c4203030b0068401c042c0603804c3c0a46444280a0b0703442011080d40280400e074020000b04405c1152142e0031000104d80e50032001c05411860a1080200f000301d0784880003460740000c0074000c10301d0003c202d071a02d01c1e1040c240511070080405c02e01c19000358a0b403812107105603165404c20f0982c00041a01c1713020341c040c0040d0840503032050b030000d4002c1100402c2e040c034000304040d1a041002500ba41503501100c10040080c074008100daa2115117003410044540f90032801d081d055494001c0c0030342c1c2d030060224401455506c1041800150b018200301c5241d9201c0c403c003982280309a15410303940b60000b03901c010100b41650070040e0005c110809026420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 466510656 1250 466509406 466509419
    0x190509071103120403030f020c1b010e09070503160306050d0201030b0303130e010906050607021302090114040b1329030910090b010e06100c06050601090e07020f06130206071b 77
    0x1540b0124803c0c49205040c0184818154188200b850141090804514040c4c0340707942d4582c1c03000c0c18885a0b40c1d0040a4440300345036403190701071030301004000c1c0c40302611703042110014201d45c0048944203803000a401003012610710900428044850250109812604540044000d840052a02d5401d4401003110504000c1c15150f02070040c05041d80002055040c102d0080a44845500041c86a2006c0c088200581c5c0ea1040424808031030880041c2d842d80c8001c010307a082d11145074020717140c1e40b0205001400310507280041c0305816a01070901621130325905880782509500344200c0e0f03030319540070022000c00340e00c400954004502074104c03054920314440140c19074001c1c20701203c00ca03001100400001d811940413a4103e9002c440e0301079a09882880100490343c00350010b0081c9803141c001c20020390050941c06c02a1466400804079464055400ba640b0704140d583e0243c80c0c400c1c04006400048402c10200c80d4983c0100300d80d24001440e25210784d00c800c030000300e410b071504d0f0000c00943e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 466511906 1250 466510656 466510663
    0x705160b1b0316030e010b030618010915090308060405010605030a020c01110304030309050d0f0e1c020d030905030f0601030f03050a050f0703350406050901020f0d1401051905090711 80
    0x3521100d0f10000d141488901c0040545480c240030101583c10034401e203140d5035001c190709a02110f080d450000510160410b9805004441c1020304441690b17005ca000903940b070b800c004e201d5130013a00d640409880300802d11003211400d00c00c1000180f41800030416840e03090300100b20303880c1244000300b50743c0d40e400c4000002d81d10a5a080700442c0e6a41c0305102000070901281014034000d0802d4501c0c0030304134401810a09c0700f02044c40c41100907a0083c040c508a803203503a0032082d00a0000d10701e001d0305140c050260b90550050350710900c036010520584140000b2954103072039100c08200d5816000b6501510b10350007458041040c4101442030030315450a0401411a4600943e00c0c5012600ca00c4c465a0480e0100c449001941c500c0103601d2540300807200007070b5000b1b0791182000030700f80e4aa13050180240a20b1103407a905080004140360402607030f810101d00031000d04a48111a6603801c1040f05214007002004403011840c2c2040000e8940341000e140d1181450400000590008504078203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 466513156 1250 466511906 466511911
    0x3020d051b120a030e0318130609090b1f0303050f09010318030507060c050304020f150d1103010e09060601350916080705130f151503050705160b1b03 66
    0x5910070103d5a5082640e0501589410318101805180390100c800d03404ca6606000080040c080c2100605181c03411105a001d0701c010309504c802003104404520f0000c9011006403500b0119950b643c2904001e1900c401040b0101d03545034546600c0c0c0f80c0e13114032030500cc0c0c01070701c1814141943d401c2c1c41007240001d4121241c005120b90b44455952040e490050226400b058455040190510420005817200040701c010b0020458401002118001000d082c622890f641c4580182c1021418505c0c0c40d00ca40182d410381e0070401030040240d6419141c1640c5e0003045503940d000031480a00301800c6d5601034180819501e00c124902c01402e9950306036009410107440f030301e4103030344242684541034401c500c0d210084c00c1250301a1500b9458080052245501148001b072616030341c400840d501240359210390b64400e039401c0f03490324007591050000340001d400404240840d09081c006180e041c841c000b100c2040301c000d81c04003501022130716203010b0ba21008003c5000815041d04290540380400003552 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 466514406 1250 466513156 466513183
    0x11b0206090601151709070b0406020c04060b030c030c18031606030507111e190812221e0f1b17031b070b0c01150b0703020d051b 57
    0x240d070404188580c544403050307100713021a8103d0b600002641d98088500103ea000b1210810810303225240c00d00e00302907041d404083e1110700000c3c0000c0554000c40c074446008021642042142e40d606100c42c411310080383e412207450820000580c000500001401c0d640288502040640e15414040b13450508000162040b81d9800c1004100b010381c14015603034081d0041c0351001c1003006803404950754980c501c001d500c00c42130700003407000b008504101c105840d0303030000200c4030004000d0600f940325901c44400b102c24000044001218980005003010302c8044840c000703949414140c0350b50006445060388089041d0146607030501040304842c00030803441c040c689400400b005042c3c05800280c4c1f65000420786460301403285040040402607540841c40c4000800b44200612801340c18215240c100180d10800030415140c0c07401c0542c07041c5102d415403010a0000c80d107030a2520b80a000c3c0580040042c0c0c00200751500c0c0a22880c050302112006803d2800000341201d10079080407a0400c0d4807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 466515656 1250 466514406 466514413
    0x503040902030106171608041118040803070e03061021020405090c03071505040312110703032c09070e04020d020703110606060307020d08040203070b18011701050f12011b02 76
    0x94910034017403500d03600122038010750b0640b600c2c1d8640180180e40024006000b90500c04136012007615540c2d0341e110359580f2480c0c1140685801d20b00f031400c030b0f001a2132120006290180313040180c01d001413820700a42c0c10f84040ea040303601c0c00c0000d1b5101c020b91103602d40c00c0340e04e0900300c000586490142d14028103044c40908004958141410320306003450b8002241107800020742c9096540050484d0103aa400405100352401090029a1402140000d060203440b692000106042d0322880d81d841c0109a00310415140400b02c1780c400e43ca00050108581c007503040404140c0703c5010700d1154030a600c014001600302444070b0030840803a04100c0f4140e002c1902558049241d540a2010b560710a400311051419800c04440c002c0d03841c3c1022201d9400c0c0030f000c9010605648c1d00b00801401450b1004840c1d5503040c46031038450000300036200d914082582c00c074640d0b40d910410460700d03050303031000343c990110550420704018810061104a4155560f14803d90400c11a2448100c8600742c0380d070000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 466516906 1250 466515656 466515677
    0x30904020301141341041202010c020a021f03061a1e040e191b0f0e0909030a120902041b091a19032d0f02040503030a05070503040902030106 62
    0x18001e900940301500e502c0340c2c3c50a020051200d1892111002100c0f24207060544204880805c03c40074140c0050410001d00001c10841001415411107001c07565550090010400e511016662a42c030307614025444080700d208621200040c507050700b0280700c14a0007290a82c0d07902a0000348010040e40410b503110000f58404490950f249080c418650106009140510740300340c42c070065002130100d4107071a900031991601c902403604081c4103001c0d00d5810411000e0202d602030410f5814641c110042011030300c1e1040f117890b08080300340c0b140202e40091480c1442401b400ca4080344940b1880b41d001e40c1c0c40c21b0182c00341e15240b041c1c00d80e0043e441c481c103070200300c0404054041203040d400400d015100d980c20460000c8500d060716201c98205c4600c014581c444038068020307046450707610b40303c000e13000040c2d405812104200600c0b1500c40c0001c000000d5041a1030b403da01c01d0340100c0d50198130030803032280c5940c441d1005143c2540150150381c2403540b607a4040090368404c1e4451400521000701 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 466518156 1250 466516906 466516909
    0x31e07120614130507050706060f17031204020f0310060e010509100b0a0507030509090f0106030e0a0c0317040e16030c03090f0224070503072d080c03090402030114 72
    0x40a015141c0707046095042e1100c44002100c0302883c2c250140c0d4142c491010440ca54011416030340e0301030740f04c07009002807500c1e601e2b0300b100030125100701e0070012100740c05800094404400c5030840c0b02402d120100070394450302030103c01d480f000b04840d01032046104140401c600c2e40700c3c001c05483c61304036078112549000c0030810701501c060810201c9400d105001c10850b409042200c1c40701500c1e0400c03c2d150b594031705054402d809009a11508400c43c5001c1250900ea4016048c0c107981003501d0401c00c03104560001669446481c1c1d004104000007c010b001141084918a21402080d000039103450788490b082c00240f441981c095400c0490b885201d070070503406d8054508206006e20f02003214142d00c2e151a080c16400d4800a401400c1601345104220500f0211900103540e8007500381d9681d14515042d6030341d51003003005175032003040c20810003443c850b01c806e817a420b140b041424450208084e12180061b9002184020b1188030030086280180c50798000781d802400511221007202c807400c130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 466519406 1250 466518156 466518161
    0xa0c0e060c0c1008010608070f0c1202010905010c0503100608360f06041208070c02150406110f07150e03150105040c0e0108070f09030611130f0602030d02031e0712 72
    0x841c49003030244020050145070351103040c20b90b004001c9c0c0f41071846001c941c4429100e40ca8800c1016203410503070f41c10400c0d0250150400800148194002c0001100c00c40d4201d0b118082654402c1500300440420172034140b0074a0800d400c44e8501d0035940b10001122440c1440c007422aa154001030030603228481c1100052000d0780701031050308050030707940c54103544910144541e8628003040c01807600c041b4101a109001c9068015401b501c2801d0320b4600b1184c44180341c01510a03140040d4684180c2d00d80303244049100310011030420001c0c00480d042c416038a0b01d001d402240c00e000c02019040c0d902c2d0070780e01088041d940d2480012040300ba54100030910056070602c0140405214060341c1640c0d150741c6c003183d0103a10209910703090303150340c620350012900740482e41d01c007601e00c03401c1ca513642c2e05034031040d80104862003000e41c84140007980c40c043e8520b40c0380e1520800c1c0258009000020440446070021a1300c13000882074464241444200d914001500f40e600030002214102c40d071340d0b602402d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 466520656 1250 466519406 466519429
    0x50105040b090c0a030201110c0909010e190b0a050c300c0c0d111e010b01091a0304020628031a03010b06090409140303160306120b0a0c0e060c0c 64
    0x244040c01041e03140c0f00100754501d2462000034100042c0f03125080400005225520b01080000d100e00c4c103a04010102c580648811401304001c1d003d4a18803581500c2d25600031500760b64032010101d01992945142002854018007131031406900300221000034024160940d10004c02c0030205510a902418410b01043c008181c448690810811918094000a8680c0844c0d41c0c40c900140100200683d9a0506040c1003001e030100034a10302005101c5d0041d040040344900a0340c1d4010450390301c012554400c0311409092490460400c04100541010030090040b49a981095003a800401280343c426140413101d100000c1d907900c8200d83d100d01001e07501241c001040707000780a0000c2c4040054010320401d075055220302d9031181e00e1001c00c8400201003141c030000500b50f039224980140c64074007020380b001e80c40d80040d00c0e10202007007000b69080c15a0285402c01c050400d80c1c0e58903a001da000b08480c01850342408119048401c0340e5a458001380b00902415018101c40400082070005044c000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 466521906 1250 466520656 466520671
    0x3050c010506220902010513061d010206040c0e0903071401051509190b0f0307030b090105090115060521150306100303020d05180a0906031209150e01020712050105040b 74
    0x14000500d03000c010301c3c03041c0840304080038070000e03601001e8030060b1804e100b10f08a0111101d00003400151076500507018030010ba8482010306101c038688401241c4070181140c001f000300c0515101401100700d20313024250f01c003100ca81200d142940076101d08240e901c4c0e14844c1121691120204141c0201502c00b400d103040b0f06807000d14081c1480403031481c4083c0804130f4001120755907500f41056030768035a0030780550391000c0d040c2c2d0815034032402c02407601d00c0102c4440fa840c1d0709001c003064281e42c0521680700c4443e249100c0c0c101140c10b10303400300c0d2103502461118201e000440800f408034400205520301a50500680b00800450b100c203150410800030006c02c1e40d80c521544c00c03c0801d40100d21011901d1081c60400d5684150700d42111245010b5101d003600040e1102001c5005080c0364022001d4030700423809444000d00610b02203e01115030b0050101d02c81ca000411905c446c01206442c681200500507180500d0300e03100640ea610045100607215a9114024070040c070030680c0c0c00365008150b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 466523156 1250 466521906 466521919
    0xe0303071b0b191b02250e0a061703031012061506030c020706050f03070c021f030911030f10050901060e160e01170f04060603080a02061b091509010306080a03050c010506 75
    0x13081c54020f5100c01581d4031a61080b500c1c4040704961514502c0b050024080301c1202140a051650b48040284030134054500b240303c0da070f0798043c2d00e031200000713403032003800403962140549040840b801300c40004032904641142d15120170401480c0d19079020400b42040d0b2b9030000e0310134240d24009280800702d40c071140a0181c200000c1034140444c404a0380e01403464240301640c0011403020860034940484206600d402e00803450814942c19000026160b00450b808180c1c102c0318420035440c3e08421103012890742c450300108086803855044258094a10b00c0002506942c070400350741007007812682c03c03100c00310000c11041065000318440c48100c03004e10f0509240030b01b500100500803405400c4501c4140b2a400140401800e900310301c001d990f0000c03409844040c4203034003940d1500d0070340d0201c510100074404015001440020f440408400038425030307100040003005030b05580304490041c1019280d440100d0060810084094698400e51341e40c0d90700e14101120a0846a001d42500e102d100c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 466524406 1250 466523156 466523201
    0x20607080313051e1005092a090a0c0203030601201609060b0405010801090f06230901140d020d0f120c030806090105010e06030a0603061505030c040e0303071b0b19 72
    0x40c2c00101c0c06170350804280c0001da01d4072404d032810702d00f01181401001d02c0c1c100f6214288054424426043da801c02030b105407402e034a40c1c0510200b51031240003207100690080c000a1000c0d0721810300d400c1904007001e05c0551456040103240d06045200c500d4602c44083e92004100401c0b8501c10040241a9030741d10034102410000000e1500c030040c072902c0e6907291039101d1015420360680c4071130f0040c1654a04030b40d01e8025035000720191410303545c5482c4030314000000090030181d5005000700781c9070f009016100e100447d90030000c454080410594901c0340b034041600004001c81074241005c025621111010001c0786802001000004c00c054040c8803c0d200400c000e03600101040314604007102c1c200d8691381c4041c03242d00103022651020380514100041c018901d0160a001030581d6401d42c291007010040800340000d0700c0c100e00f038401c041d900800001d003441e0711800d00d1042c0d074a000081060300b10200e456280b03c2200a40c2c07800030540031111049005500c40c4140a02c54668003080031904 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 466525656 1250 466524406 466524463
    0x10b01081b190e40060b0f0c071203170a0209040c0f0306080601030f0b062806080106020a0c0b0c0f010612170315060702060708031305 60
    0x2444064550010000001c00e100c5480c0044025204040d41d20040301041002c6900000e0440003100c0e040c50103101c0382c200c062105a2000d0404000d003094040c1c0b509505a01100100c2040c1c84100001d000d45d0340b43c00201b01d0044a100404441060410150b03d0340300e818841804c04031941c0c0516880040a184100040d4015902142810000140c840c1e036a90b10241a4040d00c40d80d05080c1d881458140c01c500c066800410071441c000d07547c0d03400c05c5040c0d115440c0550b1007500b8040548207060b4640590000ba9042c9076450f03005801401000b010052508501300450101c41441c012a080c01c1043c0801603020384110f00506051009203250401501c901c0114130b414011001c02240000300345420410411020100c01d0454000b049903569400740907400064040e411110b0040380112801005000d2094034061840b000340e41c00b40c00d01e038404100b141c0c0d021906c1240c200100303100100108204e00e010b1031080500301c00007040041a803400504105411101240c1c40b2807021038405e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 466526906 1250 466525656 466525667
    0xd06051203070b0f10080114040c170309060708070507090b0f010f0503130501110a090f15300203091501050402030c04090b060c070303050d0b0303190302160b0a090212010b01 77
    0x140c4c0641c180a50351282130580102e10102d0700301e00381540c02d02000d2001a601302003202c0c4a18020650311a00944950700c01105000b07a03422415903a2040c4001c00c00c510301480104600e03440707181820b28100040d81c2d800c0c10032020303511200712280e844044c52540d0134484981c0615400074030348140080704010f00980540409050605070540b4a111201000001d51202502415400c6116226521040d0003801160203002d2002c464110351000541080c0303000b042d80802082e526042e44120aa80340600b040c2a1901c0f10085511050b2411412110510040d4064095400032308a40c0c0c804c442440c00344901a44030b50300483c4104208481d12030f000c0282e50036202c0c00381e0007003440c1a0000002d03401340a82c0c0860503090081240000405030000c00802052040100900861008008042e00d0f4016030342c4905280802c1c00041e80200d103c0d600600c0c6084c00680003d60200c0540c4820241c0b10007200c14901055488400f00309615024034000240342c281c1e0b00030f00044001400007401c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 466528156 1250 466526906 466526911
    0x1e030c240f090a021513050d020904080c01140112020f0312190207080d031410060f0f0c0609050609070b0c1902130f090c0909032c060d06051203070b 66
    0x301ca91010003051481c5014008032074001e07002404040c4480039810184100d03445810b003000d000404150000311410940200580399400800c130348c80030358690b116010b565000100d182400d542e2203552035145500404110702a060b40410458107100510501010040000d00d42c1c3c847c0d48007051000d9182c01c00030072205405616004c02c041001034070000da00d00aa41c0d08800928020308019503142c0c2d9159210300d00402044c0c404802c60b85916010503e0051f85020701000120100d80d000c5006003d08441d5511061078a44004800302c1611204112449120104c45a811030300074444505420003405001d000d5040d07086190071806012569115000c01c8041000ea103400000000d554418805401e203d510000500030130400340c20810003018001001c4540501a0601050b4030345035119a509003581a100ca04d222800140910002a030708150301210403503000b507003103c03602c0310030150200c150303e01404508241488100310094400d80d0b1401507a600601001c404903104458464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 466529406 1250 466528156 466528171
    0x90102101503032706121104090906060b070302060408070f0b040b04050715020304090e161401080c07050c0103110903120306090105030d0807050703030b0a0311090a060f0608091e030c24 82
    0x607201014205100c041c007e10007510700c1a10300802c0000314030480d40c0001340c0c1144601c2c01000b07500c0d00c54450380c02034046e1010180060780403c00080c001407800004100c0f09014112984020105a41c0c40e5040201160111003d100000c240000c00004110032030180c40d000c05803240000030b84000a690740680c1c8035102d5030700e8503807880004044080c030180304201040000f100b05581c542001c42088000d8034010313030001e90341d40000381c11403280405560b0450741c4000034002003c40c407001103003d00024401e40c1e913948401c01581c121079034208400c44200f016126041e40b40c2c80c0c11000c124501005901484c041c4e0000c411300e00c0f1039640448450b034400c00c141400d40c0c50310300c2800c040b030081403031072a01500051840000b105020400e070221003911003c45d0360285a988501003603042c3c45e450312500c1c1c8207084040f02408a180154250780d401507044044481014045143c1d40c008412a022142c603a0000518501070410511030104440035840302c509160360350710219400300c000240500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 466530656 1250 466529406 466529417
    0x10c060911040606021b0f0609041505061b01063507030813151715010309060c0f200d03180f061a030a0c0b090102101503032706 57
    0x60411207522101c040102000d0000c00c2a07036102c0b81c0c0079642e80c45501e10000071a0600d9540e41e11480d0904407804441e40160020b41440340b85001e01015001074200c00300011001c2d440441c841c1c803000064000301c000602c84d02c0c088040c0d91402c03400c59445030440e030308008910410100d0184070034070800d4603413a925011074015000407080c07030405030160402000041d0001d9401034000c041181c41094079201c0c0d51522503040310150580d00e640c440c88c2e055101c0084400010486116140c04e43e840e00d006040c0410080c8180c0c0d00c810490f038940c1d1400010800401103a00803585c042e01108035896014100341d0301075a042d83e1786e543c1d2a01d1030300c4841015101c0c0200c19010030f244410102050b40320030041200d840c82e240c180050310034080441e512403804044091140b0700050003650082c0c00c000102030250400c034500060398890840141503110b000d2062500700c000d4428905560804040040d10b2400c41c0b60060460101000151400c645101d21000d036992283c40d5204490701410030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 466531906 1250 466530656 466530671
    0x1151403420709140301090f03080a090212030a0306150c1b150f1b0309030f060908070c030209070903111009091d010c080f0403080a090204090311010b03060105010c06 74
    0x20503110701c4903010040300001c5840103100c00e003900201d03c00180c0f52500100410000c500c41410700b2601c501d10090070907a0f0301003404022074042c2b0701c1c894010011b0040860501c10703540129504031240079000300640d2000a60300c040c16458400c2c500500946401030a10240c0d214000f40349103084180075007864901000c4944002240000310001c03d41c1c80701c1c0c0b501c0302d4421303240904401541c045680205044c0e10f4181198014101503030344d5154180ca83d8601079045855807088041c004100b150b40a6540c44420301143e9510040c1c10080e1040f50758600e40c42c01c40c41840315030700d0060541400d0201c5188140001800c042c0210080f000c141c403c5031206880c1c00c400ca071802c2c100c0d8040d00401e85841c1f08240015030b000c100c10500c03000000240400d070070701c1c44100c4285034101c0d070440c0660000400b140001c2c0c803440d840c07034001c00650404540c00310150000b43c04c6078442c02c8210041107100403426038070b04081c001c0b10031840c0c08602a01c00d41d0314050010f403881007001d400905259403a00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 466533156 1250 466531906 466531993
    0xc1419060b131e0c2c03070807030b0405210a050307020a02090106030e150c04060f0e0306070e090f060310090f14030405090108010b010f030b010507020301151403 72
    0x942c058407420602c4140034030300300301c4500035000c1c040c100028040303030a1815025525005604908004c15070b200c3c1c00990009100902c52045541054107926002d203803c009500201004884065405000000b040d424149032492a065031062059144590b00d94080031074a1446d007900d07900d10a130b081566581d034500108a04015452800a602034041d400120f0481d60503401002440303c0b58044813000b5841c01c1d05122592001c5800c985550300810007441954882d002081052226042200010f128000080c0c249035045a044001601524100b0120b14254140c41d40120554103100c140e0300302800829280c1c0499180a0709590b00c0f180c110b810040009000d042c81d40d00702c00d4204031f0a212418080c2c0302c0d842031041a1081c145c581c0003040a02040c410303040e880c1c2050b1a681450313031143d2415000350034582442c6040c042c0070700210015850a0084002c40c014594000e0205801c240301c0c243c1407450021158081e40c0f098509031551b000441c280300340c10126120001640c0724462 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 466534406 1250 466533156 466533169
    0x1407050a0b090d1202030f220b010311130b090a020f04030c0807140102150f0604060902372705180405070e15100509100c1419060b 58
    0x100060107051030104000c0c081901140f01c86a4000c40d60707441241c0d19401111070b00b80c0c0002d9440c1000e00c07289602280000e08003001e080082d130318120780b5804003911915042d1030028242d00c22386188140108811182c50030110402d0a801c150717408021074914074000c102802c400030601c01060790f0004840e84801c588200ba06c0066612824820981c0e44800026494070b240c0e104600841c02c9030362001040e9030010800303890035500250284842c0d607807200c00b0006020b001d440d46400903030754500840e9001d1107000030100072105002c6000070b50542055400b032001e07050880342c0182101e513200c010142e8007400325608800380c85141841e8100112801c008840c03503500180d4003040302c09040c0c0803004148807240c07055008a06031228182c2d1480a604c0c00340c1c040740c1c104d2003540e402080300001d00e002e500b00319851002c2c0c98914140540503020680d6840c842d503412021650309180b130801c11140b040407040d04244400505a00100030042c405021940080100354945403d80045252a542c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 466535656 1250 466534406 466534423
    0xa030b0307050a080307020301050f041a04030509090108010c0e060301060203091e04050f0f060a030c1503090606060c0528020111030d050406060e070804050c01030e0106050a062d140705 82
    0x51803038500310341c4c0d0300240c1da90f54001c6404034025424200050039020704000b0b111b115980000c603100404215682c2c48a0680008000f1028040240000c0c0c0e402c0c0c0314030652070f01038203054000181c46003990710042d006074841d51000d80314000c200014002c495004c01130f0740700d0703000c240d80303c0c103031291180c0c080c05503034101848041d001441c0000b0420301032003600d11140a140490110181900e96006001c41d002d032500028107c010364107410400c400d503400500038034a4640c0b8000407072400325a00c6d003040d5203080d40042c00040c0594440b03410302c40c042c4022950304010007145101000d64070f0048207108881b01002e4140b000c04100940300c030409104440481030f02c01010030071440c0c01e15000d001041030740160010b0200602c0080e03040ca00414405010f150443d00070501a0b400c44c0045016103500200110743c1d540305c0344006100e031149582c45002c1c114988807580039040c610300c0144004225842142100c0520603a001001c0d001010a508107113444107030707035941d01e803802c145252030240c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 466536906 1250 466535656 466535659
    0x20705040e06010509010803040b0306010c081303080c010b0315040f08041d160e030601030b060609041e140138030a060603060602031e03090111120103020301200a030b030705 77
    0x304000407101100101c0c1140c165003048501103507990700c031901c10743d0741e0080e4003c1d074540d0041000825110340c0500d40e600943c511555001d890581c502400c80ca81d0003c82d030048403450f10104060507048020301818820150941c001c0180400a80035181400400384c000b80981c490014440305008401d02103401401e03400c2c4085800c40640d00361803a03142d100f140c804440031610075246030442d2140d440c26810b84030041c000c18241c0d007507403100d000d9503070050f00302e40d80110200090b124940325405000605180c4504004002484171079a4054412825940f00060303c035400501031804030302490701c51020029190b207900c12503040480c0d45191110a40c001842000c020003e0341c01d01d581202060320710543d418491250341d088103990f40d0041803018800c00000e003003841c0d10360a01c1000795074404010740c00401c0c100c0344501e0001582d4001c02d02d50400d214440010320079801c003400b501d100d807821044170340d605543c08441407800340110f0f00300e141059111000d40415540401c10500544030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 466538156 1250 466536906 466536911
    0x170c0d0806010801120b150a0f181104080715030b220c05090a0603021e0703080a06080a03050a110c120703031209020609101809050702010524010f02070504 69
    0x1902500589018411610107000900240012401001881d01881d00c02d500092032030040c3c854203a286200b0781d11884544c0c00c042151000a01d180d400c11079403008007000c1d50103015204450303601c032098030400e103000460700804000810850000003a480221071003140c803c03084185804080b030240010501140e84001c2d000a90454041c0c2c070005400c144201400030030000499100650f000c0c0030f0300f2440c0381e101c5055041041441d000f50024441c000314070354544401700d0b481200128540042c2c0094001911440400142c0d1b0000c0c4146030241203503038003c09148130301d550010100d100e1403103a002000100094250244c40401005520b04030042c200740f00250760058070b03a41ca0365203200540c00a00003800c1d0b40c14460705442105c8e005a00942500e14240c110400c3c81844410307190751604210503c0a00404181800400406030006044c0401c060a0506000b03080d0b41002e00780840010282107540b008100004000260300ca081c20522003d1000040503410030409520003034003d0f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 466539406 1250 466538156 466538173
    0x100806101409070e1503221e030504081002070221031b0f0105010611010c0e0307060305040503040e090a0605010501170604050606040e0c0901020f4603030e1207050a170c 75
    0x18600240d4403a1f10b081d180d0141c40c840801e200707040003d00202c09060102002c410441500d000405803000c00d0207420014039080d40c2e400c5061400440090000c42d195010820ba003c600c0c215035042e144505c40041d404c9089464070419499224003d800d4404004e102800007161300c1c144a00e154907108100208840d60351203802070141920030102a00b0b652800607413101c1c1c0d034081d090711440164060000d01e526400c01d40c00f5030003040043d01c01c0d10544414800080c0c2c840c405500d07588034050290241c060071019240060503254107810080c10f00141100750451001240d50080c0d000400310703030100c0c5680340d00d0003044462107075821028240007032008201d030307180000c8010700c03401e03800380d0841e0b000390494000c0c0c2c0e8483c1e03a86044501c018075061552120b00f040100d40c11500345c07060402840820151001c2c881c80b00074090b0840109440e40c10042c44d030081848032280360821007011914018040d600e8075198810030b9001041c1c030310040002540080340310b059a030303100d203200201c03208203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466540656 1250 466539406 466539439
    0x19090203250b040f0e040206070215040305150105060d0f0e07030303021b0106060507030309051903020a120516030309050c15031b162306100806101409070e 69
    0x9035440c6411840c0500451030010380202d60744201c03403c9500d44080d40300b12a0610400300d02d0410041c2007a03900460034010080540d0761121150912401d00b2511507440d031940c5060f0342040924202200c1503040756004200d151240300c22a00f6070b402001f0000790003060030203030340001c01c1c0c480303412000c40c41403040201c00c040e0960300070715640141c624000d1292122190103402e89008c0d002c0c100019006004030340002c3e009401c032094440c0700c1c0041d140c0407694031113088660580d031201500143c0c4404180350138040103c140e0070f0400c1c80c524025292044d10700704002d102880b01d9000b4109592941810f007400014030500e008890002d215261070280b07501c21001f03a40058400c044040e6100c82403610b02004101114102000200d035000d1301c0881e9100c040b2800101c481e6610b0400c0012207140130904c091041501c5800440325044907181040e0300185000c100a00c1304c0074440000704280306e45c82881c00a0220701404440040f030035600c2060854004050304480360308021420b0150405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466541906 1250 466540656 466540693
    0x50601090e191d0c040e07050121020d02190305040b13030905060705160e011a0f160305130e0c040e0712020703051e0304020f01110109140604020a0f080619090203 72
    0x1031106400c1110b2113484031404201c22120070f205090883c2e40009000c100c1c95008918250401a0800b19840c006040244500a90b03208419030100c0303640c0010100348481007040c002d40b80e0b01071460701b00528900fa0350703181d9140c40081c0134400e003070003098075800405200f50140c001802000e0b2101c1d031207050351b00d4125540c60403c490b0b200d000460180c04101101410b1095048400c0310710702402401d040b400c208460b07409541ea0080c620000c200d01100c01c1c0012940200292003079a4096581c1c40e10380c22102907a60542002c482840310f00140b02c4241509015202590145005500943c40d03001043e00c0c40134000c0c04003642c03a4004110007051542040144c01005082d01942089803280504039100d4482214001d601c03d4101d4412503195118038219001504403400009a4819a07110001c04041c2a001d810b40c0d90b00ca9400c2208505044401500070942100d080f4801414a820142c6841e070043c8031020000300400001e03038030481b981102c0c0072150040c050368112503112180320310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466543156 1250 466541906 466541951
    0xc1303050616110c1c0503120105030c04090807020907090f0308130506070822090f1a0105090a03030e0d060207030e0f060414090c040e071d010201050601090e19 71
    0x12140c841d500100c034090040c8000c61001c200f00c000340c1070756a08a020800604010082020680c2992000d480011401c00003046500890040c3c0c4840d9031506040510700321010300b140340520300700240c582c00501040c041d62260340c1d04461000302a40c510004882c00300030b540c01003c08500c80e5600000f0b000e40d500c018011900400b03603040c0aa5118001d000c2244a011802406180b0070031211000d0401030b40c1003125040c0e10301c0c41030403056071100c948090b41c201c8020b4a00d030a642d00700200810201d050161403403803003802c1032400d214001d000a06200d039507200c060180700c800b240c081040c2da0381308104850540d000300d0031911040d2605008014015000b8480e0180380284c48944070b51418009440840f0b2615014007030300301c0e40714140a2040409042240700640078071000c90720b04d0a501031584a00c00302c2e82c030f000320401c01c141c20288001c06090040c0c1907924010522406036440358410041c0e41c907020300c0d8146074403480c1813400002c00076102c00008a180070411458211340c51110741 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466544406 1250 466543156 466543171
    0xd0602040b070b0a2d0b040507021f050106080105102105070e0904080f0c070503030c032d0304060b0f120132070309050313030c0e0906070c02090c13030506 69
    0x200680d0707950b51000708844c00c1000c8030400307031400181103040342d88901c0f400a40240c040f170b002c02d061580c80041026078034151280c8000d6000130501001718509403225031200352400206100c10b525080000d0141c21040c05845d0048401e210080130050041c003800e00220604180310141c8605449040b005000640f8228005070106100c041c8900c3c00b003007800d000e00d4000302c42c0b81c50950b600900d2a110f40c4061201401c0d4007036190001210b41e81480500b030b080a0746405107956004e00d80360010031441e10b03403140191000c1826828140700400c3e060720362041c5d016000169850800e030004402d80d42200030290322030456403d10341248010f402840407569020302c0380b80e02106a001006030b601d84c11004101d0708586500040032180309400911925002d6415686080600312501c01e0140d401d80040e65504d07803242c0304100c40c42c40195069813084e500800b501507030074034640041c1164508030000c1e102c2c071034580106040000c80d00032030700e0740792429155103030941ea42d00d0200d0302d4a00032070b03100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466545656 1250 466544406 466544423
    0x129031218090f040210030b030f03030406020408010531020103020412060b030106090c0e0f0a030807110a120f02091503010204090b031615140d05010b03100801020f0a0e0d0602040b07 81
    0x1c2e0044104001c3c0358002c6500801d807908841d0341000440c010180d0000b07259040c40307000512501c8003814401140250f01a00000d60380c1d80c108440e16007034030000b4000b07005445440c40c1e401402021000c144014211011120f44028901e00049010340201d812000040364001e0300c0c0e808000c0a644070543c0c6502c04d500a02583c1c0e56422440100c0d465540303001d0200d05a100407407540c1c030302429070004d00c0f40c00500741d10096450b41c503104465009003004030750315410001a907000d883c101b405480281020003000081026968680c1d00c07000503200028042d20140c07000c1803100718404040d198030380005c0d00864585513503400700d4000d001034040c0c084c0070f401aa28056a02d06c815403030f9a054846c0c202a003d11220010700858100130381d51503400380c0c0101801021a5440c550040c2802407640a41d12030700d0b414000b8a01000c403286c4e6010b041282e104100d90465403400c1825602002c1081c20300080c0c01c112040420389810b103102009150520004001c500361515030007a11505c3e0264255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466546762 1106 466545656 466545661
    0x513021308060906010306050606070c0b0d09080a030609060504020f070818030a0b04020f0d150209060c0d0f180303210b04110307020f012903121809 66
    0x702d0f020b5070803400040003031100d0f0303004144d0030400031200c644ca0f01c0041c0ea199102c4452170721415400704400704a4141c0640da5903c107400158002020310390301c018104000740100118021042340c54a803450200e11420700b4804d0750501c0422000c181d2600ba007580340d1041ca1780044e07100380c100c128401e00c181c000d51401c0c05805c1c0300b14891720100c4542e050510400c500300c4142852240143c2c90102c40c5408940841c005844100140c0c0300180d5417000341c00407408501c0341090581c410b2203040c00404641d68010000c500e030707090360b50341c0c40b40004006c4414802ca0456202c00741c00075120242c40c400d024400000c041c9200c0c9006000a65040c0540108040d201640708401c10f01c14084100503a03c3c2d014400380294008000c000c000391108407d42d080004c2e2025156000d60b1955403420741261001c1008840e100351000340319403550394003203c0100c50380c00c0429160080480101 = true := by decide +kernel

theorem cover : BRFrame.Cov 466366906 466546762 := by
  have h0 := BRFrame.cov_init 466366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466366906 ≤ n) (h2 : n < 466546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
