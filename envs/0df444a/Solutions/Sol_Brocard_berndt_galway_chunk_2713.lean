-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2713
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:30.248393+00:00
-- url     : https://prove2.me/submissions/469af531-f2b8-4763-8c15-25b68e8f841b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487769784 ≤ n < 487949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487771034 1250 487769784 487769801
    0x6090309010e0d1e26040e040f020303041806140a06050d06051e1009030215070c08060c0306191d061305090f150c3c0706060e070e060307090306 64
    0xc010928401005d104180c81c0d6002c16501c0c101520419403c00c00885281e0b100714007940e00c80d03407001d0010505100d210200c82544590180840c0c1d0340740e032108450007403c1c3c003150000c4200340c01c155005c03a0b42040c0c0b0601901c1c0300d0b805080c1495107410103d090701d031a00584180a4217665170328002486503203044250b03550b186c00014400b5202041400c0c446440c598201200c00d20507207180420058507040500c2e4620342d81c036035402d5191003040ca88006030b06802c3d888140e81c0d00ca0f1906004000182c4002107000345000c031046d207844022101e131002c292445100c0d160000e100003007c1d240301081c0828050380304000a1641020161034090401110030a980c0e840e010742c0302180308000a1002c01044907405d80c44810100185410082141da500c6501c81d0a0303407505640031f80e1512040e8010030714050401c54201c031400c0000c2810844010303004802c0c195289030811100098041400b1040d5008481c3e41d50b442010403200750074040780da80017518010422040820010100d1130318420201d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487772284 1250 487771034 487771073
    0xc0e06190e040c050409022d03010204033005030a050711031c05010801020c061504200703030c09050f042d021801140703030b03152706090309010e0d 66
    0x10035040a0510400707851064000070f00542c50b0840c0400036a5984440700c841000b410740c8e0f12401d810f14403107900d00105c0d034080c040d0107600100c0d01204001c04010003141c04072044860641c0c8030504620024070110600e0440081071040002c43c880070803507000154445a6030810b69803140b94440305500e141d003c03144441c402d10040c1e040d100b004410307020b003074010320181001f54140000c2e81c000c25194600900003c0141d80591a400c60640f2070345c005040390040c090302200c0c10240c00c3e95080043d0b101c01f40450000e464800810f150900801081c3c09072140908100000181181408000c000c010307605a00008518043c0c0c00c080c130740c203403132a0700c40490f03840c00350b100c0c60a140e41c4000641d200c07001d14144940310086002420180c020742c0d103015058a8041244480e20b000700b42020182070203144003500c0b0008005d00d410303043e8a0074180048412070320b40703510700154680307031624001c0c3c2c3d03400c90302e13042005070810941c170074285a000c1d030800400189144100d65112a1400c40e5812403a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487773534 1250 487772284 487772309
    0x28170f0607170c09060a171b040509130506070c14010510050105030907090216031206080d1803080a0509180c0301091e060602070824010b0304060209130b1504030c0e0619 75
    0x4000710094401f107420181040268904d842c403801c004256000c2c80c02982d00501010001036841416010140c1659030040c06556150034413400c01040048a401c00707507107030b820208200841c00d0051041601c6040b00ea92244038042c2440c004503a69840905500000c0c840c15901107540d1b0341d1440106840340003030742d004102e4200d6140151000d155a40030780011890700c50100020b410205e4519022134542c40c1100e403806040108141070706498001800074140402c2401d5040e8108008044500c002c585008442c82035400800b48010111400c41d2040d0f0188010002c043c2140c2041000382461034660041085000c2e0740800c4540e1a840a00168400e4808100115090040d0404048140301034804030b0301c100b500450b80101841001b50200c00040003605114140d0b05840709000c0080001c0072060102c40d4a001500800d150300348244940304002002e559182c0464089a40c401d50f10401649004941084c4a40044c003103504001c0c120101c0c002a0051034825000e0028000d441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487774784 1250 487773534 487773557
    0x3060619270627050402220303020a02130203090a0803060d0b27150402010e2b0c0501030608190203011b0903110a080c28170f0607170c09060a 63
    0x204803502c00d1043c0e8400052540808500001a20207142919002d0b030700565034003e10380c1c088002c640c044074a0740110030211004030030581e0204010a042d03000302e50490f001c80303049120700c08078442a1005810b0350321400e004800a10a50040d40e4403e50090180321a0b41d015140e5040c064000c42d601000d2038084130304120045488036400302c42060300c0c0c000b40034140808140500950020308044d060245081304160a5501d04080d150b03820b25880070900641c5454540d600751100054085903900e10f501004142944240700f0341d0101d968150080c02505100c0d0141d000344100d0f00026601552183c0e13020341c8843c800c203047e000865a5030385070b100042c44c504054505d41d80001307074a4800d155030502041032440c00106c0e41040030007220307090190840380b10078000c10300041441021500b0b080b6400a03000d90f00300090365450141c80c003961148208000010740720341c4102c44410105a5403403224403580c4c1e001428951004411784501e06d49141c036000240c154002c00b00754000209840b901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487776034 1250 487774784 487774787
    0x2070c05100e01020d0c020a03060e0102030604110a050d0f0e010212070e040902010905060309010e1f060e0c0715240303170c0418090606080102070314030606192706 73
    0x481c000300304a2034641c100110080000351600501d081d81070401a020109071b0555035410301010045074000710070800d5408001069010350400c4070454403480c907044022080c446c0039000c644284496a031340e1498815031020601c01840703c60031400844d0382da2151018180000d01c000c041381e0030403082640f005e240c1200d00400408505a9190217203060206080060740c0081d8051705440c2d00b00c59084d16513540090f0180140340a10315a60786104140e10b5684403014007425a8800401c0310060008540782c0c400202c902005980a00ba24401004a5400304818000000060844107000b1074030629004034034a4000070840003851901c010101002019006040303a846540c9100d80c840742440c000510301e0700e9009503c900a45003401540b402402c8006d644403115450340440100040d81e2115001c40c000d40124a080b40402e00c0503000701180d940e9503081d284075643c000c0c801842d00400220301c8851420b071640ca00240041003d1102e6000500710401029007501d81040750b0b1103140450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487777284 1250 487776034 487776049
    0x60f0f2d04060503040b09010902030d050406121104150c050607121407020a110a0317030702011104140f0a090203041a01140102150601020703120203040e0115080615090402070c05 79
    0x103112030186020001040955080401c0d00c0c0c2c000e420140c0305401d0340d0340074030041c058409560029031500903101500d00d8642c001c3c0c05401600c48503951002c41d071120a0300e0000b2103e0051183d07080503407e0004104042054040c031070440ea6614000030110710903501c0d00d10301082603880c4c1d004a8521002d0004000301da00c40d000b81c800c0740070010315050402041c0607440305400b91000d4480d001c0b009815055448030210400250f030302c490511a151481c68599a031508181c501c14019420100b0408240a16405442c160f61000d51100c00040480e8104403060031460310054000401d42030000300c17605948082c0d80b01d03d001e20079080b1403c0c0c015840301c0c5c2284d8140c11402c40240c0e240d4080f041030340e00140c6081401d4182520341c0181e140d082c0142d14100f801c1d80000e00810105510b145420380c080050070485041070fa10750f00d281d80703c00741e02a40c8200305a0590000341071800040f114641805030092403401c80d2030452901100402040a80e408203100380d5050321000420490350038080c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487778534 1250 487777284 487777357
    0xe04050c0411030601080426090405010501020109021c030e04051f0806010b0403110a03081b0d0e1008070c061d0c040b0a03300309030813050c060f0f 66
    0x100c0400c00a030039aa802c42e41c50102819141c10000c03144002810040200c0c02481c40c44004207802088004042850407603500405c1c015020b0342c281000001e09500501031070800340d5009000c00351118004c1c44003c20b503010140c050303040002041c0920000d8175603100f11800303060000091421480c409966100390300290344a00c100d640401c00402400c01d101040d5070550b548007450559802d00c03000007892519403a0070281200600007560301504c0e0300d00b00d110442402030380690346000d0281030300380c60080c0d14041c4d4540041e401c241070907503503115100d0f50380d2200c01ca05111151940c140c030760000321405071008144050302e025400400450803c2034403910700003140c050000090140102c0c80b0b50001348401000c49210ba80d0404004400000d80f403418403c040c5c0d20410408069001009171545580503408200004081502c5450a0b01c1d03901045420030000c2c00002280d01c14040070368084005500c030348000f4041c0d00729004900303000309506e4030000c1800030110807183c1030050307865150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487779784 1250 487778534 487778539
    0x90403081e0709090b010201020c25090603030f05091f0201021e03100302040c051b0c0a05091501110703060504050f07061704020d060207050604060501090f06050a05060a17010e04050c 81
    0x11420081010742c00b036004420341c4c0300044041900715007100140d001e0300600810654034012002c40b40e00701c1904003080300c10319104a0801204642e100510422a5140d000c05000280c3d141003000890380598018007019030098000707041d00119041c10f4540301030007000b840c0141d40020321000320380020000c09864610026009242d8106405400740001d203d104c000d00075500c80103403030042401041a600400c09034052180d02004110702580c0f11020307024454414410080b01041c1c0d41820207095122752400007852156039207540c010740e131030800ca1201c0e0f24580704041c40400040e0860041600031031081d4024800c1c040d940340080e081c0308a58000c41e0402068000e14208407518400f0240c1203601a0741000c0d11806c3c81c00e02d00c0c083e224950014240d0300c00c20050000b0045990b11a9040303807820301c0200641c94003030fa10b2800703440c0c0d184988c1c1d81c014404402032059217400402480143c505003851081c0da141c80c610401c4141e002da003d035180c44800303c10002880010300082c294070008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487781034 1250 487779784 487779841
    0x20307140d0209040311060103050a0b010e0105062a0f0309030d0206041a0702100c0519030b101d0a08070f051005032806080a020a090908120c0909040308 68
    0x108000c2019001e103004041c1c403800c0b00501250505000f10f010f0000b2100c100c058506640c2c5034103016660780403030fa20840d040250000000380c1c0104440201d41030354002012980341c06400082d5445040180000188000d80780c034041081210820161086100c0440030756165100c0f6003c060030145802143c5003550050b00810001400300700303100d0f0700b25000129440f40c80c0c492500c201e01d0112200d58008040d4034200941040c03039004009807104200c00c1400c1020300070090f2045080c2e480c0d294074941c0141202030200d8140e40110a03078000e041c10640c18005c84c40a8000141da81c02880e0f015940641048030709101c190000201440501026900c448544003a900700a09a101c001c0c000c00340500009208494600e0703c0104071281d0301c40c040300f13110340d68481c120b042d20340555002c01ca104210754140040c88903154016170300c2443e01308203207504111880b0120345001a005107081900c0e101040008802c0d9103050226024a0013551051310625001500d0890740540305440f8124000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487782284 1250 487781034 487781069
    0x60b04052d070c0201050c0705060f03090c0a080c0d02031911030f1c0818010509010e0c010e0a150504120506010914090a080903010e010513030905010f0e091021020307 74
    0xc00ca24500f1000f0340c2032801035030f151140d000c5141440041c3c1c0060f50300c18000a200b50541400384080c40c00b5602100c1903d1600140c07070304002003101c2c28811084950007104081e211803078141401c04070113002405070343c02a1644425160003600420089581c40703144031059649080421039626074450480042051040c1c505086219080b1041039030200118200022800c00039121091901880300d0020321850800c850854040c3c45041119161442005840c0c07a4540c0328150901b00402e02412403a0041e0400f0a020100d4010a1400080c400704003c00038010081c45071508041e80100054009541000210300540d000d50840074680d400340c10901402c0070022403440c01c2d40c0d6008480c140d880640c000401c3c007625803101c286485510344800c0050301d101c3d401d100007a80344299030718420180c80720700550701711a028500200103040b0080b0b40039241070206c40d0320b4005000f140e01c040e0142ea035031400d501100080d030380c2c10050556140028114101001603201070840004810138030301d0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487783534 1250 487782284 487782287
    0x6020d090605160305071a060405060f010909021b150105011209080a0e0f1c05070e0c0d0b01230703120507020c040203040f02090403080403080106170402040207060b04052d07 77
    0x51040c40e00d208540f6030708032904050140301101c801c164004010290024082c101410b204800c4038150b001d6420940050380300d04e81400010b0b0b107008161078040c1100d041840310700081d006640c000010003003001c1c041840c02401c0020781c620900d4401c1418956062400040803101e501d80850a0241000840800912010107a07000e80c0e00c02e00e0008004503042000498001d8143e2120b40c1100301e1010b401c500484030343c107030100c0704d0242007103500701079980d810400501d5040700c00007502c480c1400820b00031036064111030300380e100c14500503030004009601c40d44980200ca04c03034030042000295100c00c00d90888a40d0a0500000d0b100700080d1400590203521914058610781c07040c2e41c004001000c0020442844030101c0c0c015200c0100c0c1e10389482e0182c440d5809450982c042100540009a0188200c0c0c5441c09078180c801e000102d40c403039900740700194000711000c554860301d41e0351a15079519180700c3c2c0f5115104256900e8800704035500c0b02194991075904040d40d8a09040801642c107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487784784 1250 487783534 487783537
    0x30e030a05090402130504020f1308031602010c031403071d0d0c150504090603060605011413050f1305070807030e120405091b030c0d050a0c020d0f180f06020d090605 73
    0x41c101a00c0c0540d44040b01c90018a0031040c40e003191f90b0152000c6400304401540314082c2003500c4111403c40031b0309803940c0d1031543c0e900444401018400c0c60b0181000194482c00c80c90944520a00780034201d85c100c0b1320a400250012a00380300094840001400311412070303001813410b402d0079a00d10020840e00e07200d0224065803406490b80701c4081d441b030401158400c90498008018400c810007601c0e0716450000c020b8440d9104580c001400310a01c1d0301e0442006084490090035058407004080ca460188600003000300440c03540b080c420005071440800900496200320b9803030b85c2e100500c0c42d220038080c00b2205580080403d83d80020140201a1012412202a00d108880344541e40d170f14102000307400a00c0d000308801e14200801885100e188240c081c001c88460381005110340c0da5100511412948a000080d005a20104a650700385009541c0107190303035164544891140c83d804180751007042540d0250350701145800042141d940e05002e030300d100e0780c054540604258900100204103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487786034 1250 487784784 487784797
    0xf071704080a180306052e06030b011202030a05160203070c170102090d0b0403090e09030702040e160f03140d08150a03021c0b0601030e0a0305130321030e030a05 71
    0x7581c0300091054400c9000f80c0303402440702da8421116156603124505003014004c00c0d54250000225414415540c149050404111001e0000003030120381c98a14108c001c2d06100500d6030601141300b01d00c0c0c1c410070715030008610a01c9100c4000c03441c0d08280101400d03060b8120602030854205201c00e10001c0c00d185c10f500110b03540315102c44030340450701001364020301c0380c9190660b110300b65096040800c4000c801ca14429402520b903025030540d102c00003120b0403012a46442e00d50000c01c410001860560310403544545100b0458502c0340c9000c405510120300fa41009601c08c0c1c10f20700400410900324460111000d40b040900020703c41c000d0042c2414001400c82d0101e65501d1602800c1601c800305040025a00117007503044100a600c0000002c09003500d0036070704202c49000162040d40a802a6100b10b60f9003001442d400b18582c4085a20713800c40255401c00013103401c0000042140c080341c0c1410400c214140003200c01d4011006400ca4914101c000e00720b82092141d0035426400c0030a4070031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487787284 1250 487786034 487786043
    0x130302090c0c0106060f0e0d0206090d0606030b0709030615031a0c070b070905190e060112060e010803090a0609051309081c060f08060105090604320f071704 69
    0xe6522110384180140c01000206550b561800100040569102c80b0140c0d1220882d11480c0c40641160148103126520031030107500410100001245400c100c0100310015009080008006d034403a80c0ba00524a07040d141a40061418102071090003824840d414980c8200e09031004034070302c0c566030002e182416009a00081960000144180c91000304840303070076030b100644082602e40f0794800350001e0b0303160040300c2c0150340d440340c0079807803404070107510003030b1800394400003201c1da100c000445210b00d028540740280b6841d46000106807061000e994040c0c60201e02654480981e00207102134441c0d2030b07200b8070030402108401c01240d2204181070203540724020b0089280c0c1000e0409030400d1081046040c0c024510720014940c0c01c0341584520207803105a001420381640c0c81030300701c4c0e50701800c3c0101a0b00c10980d202184140ca8194452101481402d0f00315141d9900d02c0007864814140d40001d042103a0960104109206014003050788040f041c10f10300703c950b400707018026000000810060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487788534 1250 487787284 487787299
    0x1b0d020907020f070f18020c071406090405090703020108061c08180913030306090b130b0109030804030c05030d170402040b0a170f010f0603080a03050c04090e06160203130302 77
    0x20303115442400103064025a000c22542441d035202500d480b00e200c02e1188408003402d1038000d8001b40000d00803100f501600c0c200603c0382034209040301e645000c4070140c807903002c1070401c2190b14603100d9000b054400c48102000d04165840c500015004030001847c80348180a058051104d50302d90905801c10307a40c0100c012511448141800540c065244d00c000307070b000481000b048136581c5000700305120f90740b00e0f580c02e00c1440c0d55000c842041c1e030700c4d240126a001c1c40410030201c4003501680485107201c4145441341819076661101e0001c0d5119402c162200c00000405010301d06040200c2d40344400f091a09045106024ac400b5400f80d002400080c0b0603034560400c03034950303900c0d012100080c00c9060280d2215036240c8811a5079040e46000f50501395007060f808101d5140c4500c1404122a000340810b032400030440411401040000e10000b410302080c0404503000303920b440782c43c8070310401900a0529003000030a445a441a09040c503045502c2007100d00f10562031055235a046079811f07100e12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487789784 1250 487788534 487788541
    0x11060903011a040c09051f0c0803011511010c0c08030402030109170304030f05031b0c070506030106021b0906062b02070c06021b0604090906111305090c090306191b09081b0d0209 78
    0x40300e02301a05100a801c50341c0120000c2a2400e1183c512810800641ca030768500c07109103071545082e61b50443e0301c0000309600a608402040e040030040d07600134401000000c0501e0241d0726a04500307113507482c814440c04040204010190000d00401c40c0e0303c1c1d941002820b41c82e20b180010140c400e407203500c10128201107a00c041c11030041120030080d1034003c00301500c940c0c580030000e550b00960400e80c0d00107182c4418070101400e040c0200b0b80603400241940746081820b5101c0300d80c1c40c241303000210320701094004200b200b0074180b000d04a0fa034403810b012411140740c4080203241c036201e494046c1c42d40e00002000c001701e41c0c6980481c2c0446404500224800c241414010000c00303c148a02d8041d850000d000c104462030b03030503940183c13030b421100417000703403954091030300b00d40901d940c110341540c0031002049511002d40c10a1526201000f4081488210740407105c0d100e1446030074000220f400c49100b4442d5000500401c014250420a41003c41006400140c0805c5006c50045d000e0805840070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487791034 1250 487789784 487789787
    0x9031c0905160b1819030611120403020303160e090a0e1f020d11070506060603180d08010e070201090203031603030603080c0c010e04020a05030411060903011a040c09051f 75
    0x2c2e620805000e5480405260782c40320020050b40c0030540c00020f0700200211808240341840e240d050b1098202c018280490866450b1001040c400400349510b03502400008003401d42400c03014807642c0719602a60303c9041c920701c2c099a498031290361405110b86043c81d10764644405c480e45a2140c0c262401095403c2a084480e04200c5420300b03441140300d1281090800b01d5060b001480c405440320000c0003100c41e001e0030200c40703024401d0018290b0f0400404500189048009550400c80049040c00000c0700021494541041075800d05d0204000c000108603c010320140f881d8270603102d0000344401034855000039260302c18554000313122506e0307000480c14140b0941c001406560320015660740d070302d4000400d990740c0b003565503082d00203044100034084504260081d0381d54401d0b2074403a0750541e02c5c0c59568a1075081200da55541080301801003030728a680034000c02114094802c00790700c0748152002448180c1d0102c10485c4180000d0517010030942d21b52141514199070400e25844441408580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487792284 1250 487791034 487791043
    0x305061c030923210304031713090510141518030a031106010f03020d0809041e0b010905060405060301170c040f0e060a05040c141306030605070809031c0905 69
    0x8403c0c0c400c8082c1c0540d5550703000320883c56003801c40c21600d01201c11031503502c001d0000305244107014182c10500003000000d0994026003002401020345504001e5130104042c07000c444e0340d101a10081d01d8000b40000c0c41c18280c401d4020f840b031031034000f01300c1e40e42d031011480100300c1442268110500161011029601014010480a009041c3e85086406090041052540c0304c9818143d0103014000115001c07086404411290b015140e281014066100c031403c5421a84005803c1511800c8101c0c4011110451340aa0380e1004400240186800d000415940c3c441d00254000c203030411052006a481c1000c0d81e0440d803003100444420030446c50346506059180c060150418109246510891200d40000003001180401c80707065940d2501c10b002611010b54000d0141420410144410400700d001108200f00281c5840b82012a1070f46000440b1042d901c00d0701c0543c1c3c0c078010300031125802040507800080300c6005600b84003d0054030f03090000100a0040703100e9440101d1001c00c9400d20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487793534 1250 487792284 487792289
    0xb160806130204090504080714070620010b151309110d0e0a0b0412031103061f0504170a0c0503030a09051e04140910091707020d051009020f010305061c0309 69
    0x9401e11540c2002d180405880d0848c0c1821940000454040c0700391200c0091407070b044407a00d40d00d000301200382d000399a444003810031040407a075403102140d1140340c036403030002c0b030314840d218645580c0c40b50b9056501d0300d4003c8580100c4400ca041c1151908203141c403900342d801c0500140340010318003000c01c030b00d00d06e40408904000e00200c0251b08002c18490703064540000d20301d1a0308e080c080c501c00d180102c172f018482224140c4c0d000414000141003200950900c180c003000a041c4286065102d808540e00003000e14000c4099a1048180504000c45c569107000100000c1d0003d50418101c494080c003d0040350080c00d00450001c0591945d00c61122500c0d40e5400e4060400c0107107010502c0d0068003103508075031410a80c410301c00c42912a500a1091016031134008003003035440740840130710f400f155010203020383c1d010440c001e80c64041072040c0a8865050003580000414000034410700c803600205032441c1c0d0600d8640b42c2000b0041c1c503129142d0b65040022503045a2114251509035103083c6c81d81c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487794784 1250 487793534 487793549
    0x8040b0903120702030a0305070306050102151017070807140d11010309170705070806070f050d020d0204180b06071101080621010608070801231509040f0b160806130204 74
    0x41040c0f00c0c0381034000c0010312010070300c2d641c14040741c0d6550005030251046c41c80f500740140d00800e01881703540c202c0b481098001510b204042c1c03201d590303022040f0035454002c40e58103007074010800801c04050100407040081081c891040701440d80d5000003882e000c3c02000190059101e041c0742109a03202e5030190518650000c81d040740101d42c0746080d002e070b800c0510708a030140b2a10001083c1407000085039441101c440d078903921440500c0c1005c45d404c0c0c201d1041d5600042d02408220032818031070000d00040d20003e02c100c0070203400c409680003074804010025010700c804101007400f0451440141510740000e0030301c03401031b44420700480c4100c0b200840150725004691884d46088030103400a400712614102111941d0307803079074111400c0b1244031191448956506440144c80c49000c49800c0d0b00230100d14100030450f200c83c0100d417405504503030072140030101350b205c0c4c82004040ca03240d6070030098903078100f10300e82c0c040390000d0700d1300c01c1c041e000303611038814424031045030f031500d804a50207810380 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487796034 1250 487794784 487794817
    0x10e0601090e0c01110d0c1b080f0601290307021920040e03041202030f0a0602030610020d0806130216110906060a0e061c02131707030308040b0903 65
    0x12294620010010780b0114007050240940788401503106401c44c9030f4050003440941050051820140c550b01500130040702c9030701c6ca13000c00d2002d103042480400010000000907100d000d0b520322045003081d80503009407501d02c5010454804450700d50030002c0038001818010b5583c0d44824005030318000072104032001198524804204218046507132203000400c20801003d4003002c0f20410090718110160070203503034001d00003000303a84030a0145404045c00503040d42c0b40b40403040c0002e420200c4000041d1601c076000424014981808820381240c060f20344090304000140c19402024148090005442a00340d800e07520714404035941202c40b032401d0024401640e0505240081c207801030100003078440c0d61180002200d60a0034000c654800c01039544000c800c0903294200201500310545820040440b10440d00105000b88003c04100c410080d600549600d40310a8810300a2510080b02d540d80000b00c4c1003000030b03080b00c02540c01c607501c2880e001107680c0b464122480d6005185104002010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487797284 1250 487796034 487796039
    0xb03270109020f01050906030f040c080a030809070b0a021e012c0105012106020d020702040e1e21300a0605030a0c15110f0d0908070b1605010e0601 65
    0x20541c0015481c81c400d6070045062080c01c1c00554090040201007074001e0410000503014401c6464915846481141100001da031a000858075040c4031280131004160703540b050140d006001c11010303000703101840d043c0e450134807203000081d2962489003003000c00041c8000c1d0b40727040d200c0a401022442c0c40851a200d03840c00001d00b128011043c8195100c60b65103480000302c0c0c507a40508091068a015441e021141216590b610009521900740c2d190110760a2001000503a90780c02140d880306400c00040800c40141e07051459a00c00140a0031825400580d081e00313000c410a03085e03c98010010100c3c0e45400313121410340313503440100d640c030209012141207200070f0382c20080c8814042d03900100b00300016903c500615a81e90011b1ba03000d4801e0400f55003c00c21480c0c0460301000d80c29243c07070b010313580e54401aa454948100d12008510f250062840014a1644010010000c118960080c1241031400030455000d2080c07081400c000d8006074188001e00109401540c94810400103d8130f070f030340c1d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487798534 1250 487797284 487797361
    0x10501052a1906060f030f030f0e090a060302040c08091011070b010b03010602120406080408030c0c0106091a0102060402100e01091502010501090c170109050a060e0a0c080711070b03 80
    0x65040d10868007107107000c5011030117500401c14101070725480035400c055800d080c2c500fa100d00b0070850380101004016040c490703250b1918441c44c0c0c0620304011000c0780d424214070410003520100b42c6005c041100020402c41060000108003d402c1140b500029191b4600e1203417090380c1c851554007178041488040001903140440005604075403840c0c0c291000c04034013504403250303481588143d100140421000c1008103168100941d0000684030082d854424800c02d06429503041d07500c20040b5640d150121075406882c0d03528002c040400340b015080525040d03000403103036280408940200122803e03050031507400383e480b0348007a140142d04820802807152000740030703160901580d4019410004112401400707800c00c039079080e0000c158081503a09001c00000108801410f114485481c2e40780000c022141a00040c00368644440110306040803004c003070242c51001d00602d0400182d0100c904100380040340c25419120035440203603032034407408401c940e0110207040740c0702c013443c01d0385481e40f001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487799784 1250 487798534 487798573
    0x1204050606030106060c0b0403030b0a050d050c01020d0908030f03060f0307031b060503070e0904030e270609040f030509041d030c0f1b0103090501110a120605040203010501052a 78
    0x440c0c1c200c00a200d16503d41a085441c2d640c0300000405100381e110103d80003034000e03000448286030241040c010103544500003603a14080c49000d413426000018042e109580c184050fa00c6140c407402e2400c2030610f13010341241d40b0720882c481c002602d00d010000c034000c0c2d90313110211140340c2c4c401412100c1c2c4640701c1c14120141c1c3d1030000c078a00f0b41d0340201c400081d1540685c051361720a20664650070b440c0300f0148140076001e1402441102013048040c400c030306a9651240061701d648103000c4130560b40c0828284a0b0f0f410dd4090081c510900840b000c0000060420042e101d805d030381450615111419500402d014007140c1c540700e40d602c003265411540d100c1c80000a8211080c00c042100d40b5000c40c24002902c0c1e0081d140c900e101139611880e0b52001d0f50007034110b45805171048000003500f0318030340d5032043e4542200b600480000d00380b24203003150032139501903c03020304003c480031403440d4136140c00a0002d11403420b084101501d0420a5460a070039540e140001e0200e00c41540c6100d020020314a6a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487801034 1250 487799784 487799791
    0x30302030421021209360f0601080f06120105070509030c0402090307150c1505071d031c09091109130e03030a110d0504080d1401181d0f0d0e04020703210212040506 72
    0x161641d0800a50141c01035441039014a106071503078001510f40c075414003084a0003d000e01c1c0c120070000c410440dc0f0700c0901c44c1500c01c5540740e03a00c84d102d92140d02094100781104d420303144560300610801c100ea0340d010840c2c20031940ba44481100c4a0201e180a03202841780003000b5081068000406c04a60115040705129014a54400e006003001800580200381c01a02d0f140e0140c0c003103108040302500e0440d03d0030080540d0305003003010310f5448445109071540d07000006038041010500000301e04041d0f035210003c0103076290030f00560400c2c05e65160b40f1702009002038001341e00d6a003142c4103009000100e540c00a21a10305000619081c03c003140564404010003036150329001174861024130410255040c4e4554070a0204101d40003440721024001c4c0e498441c40b41d14401e13001c10041c0c20204600100030301000f01901c0a0304960780068516002d040e03406014900412511000990102c2ca10301c1c03e40003000c0381041140d902c42420000c0c010811680b4000e5111424001170141c0060443e00c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487802284 1250 487801034 487801129
    0x3501020d050f06041404020103181b030b071409010813020d030305042604090209030106051207060f030e0307060e0708070905010e060109060203030703051e04030302030421021209 79
    0x10b141c68070740500044507529000384c0d00a81c1d144002c10010340c4030b40c0060008510341f4420703a0f264000e45d268415002d00001d201202140d136100b0400800c4040c2c04459401507460900300c0141d0303e5000641807620030f4042a41c1000044000a0131100391440044e00085c0c003e408101901e00901c1c0c060010041698243c403418109056081564110071031050081001c0c034a06040030b16112007c0040d40140c040e140d413654844402181588440c401c3d110003000c520010a03003189051070180400000e0701d100810107051444400346484004101c90401c1e43c007210002d0340e41c015184c454204030f03a5400c0440b042c014590001800400d07a0441c80c10b86a03000e102c0001d03070b11a8001540c103c09103100318005030300705100146245009900c0325074402507415003045c050030b0924804850540c2103404230041303076001c07062006109954000303442c041005091a2220100c040002e556040c142078819600740e070002d0034000c20717110101e454002400302070300b032541d82140203086402d40900041c81e04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487803534 1250 487802284 487802311
    0x20301090c03110a05040e0604060504051303030f0207020a0b0d1401080109050c0a151404030c0303030f0b031501051e0405010906170c010c08070302030c1203150a3501020d05 77
    0x40c5050f03007581110b803a06410b88461746058988150b204035404002c10b0f03958810343d9540300040b607442d24044c0c1c0b48900c8030360041841d4000203250160072140b009140f034410301d00c148201801038407848241020340780c00d003010b280c582e20b030b8401030405880141c2480400d8000380000189260054000f0080184103405560b511440b0070103100704510540300c0c0000750306d1105420443e007800f450b008450f480d0325900543ca86a101e45443c00e1103c03842d8802c6000941c0c070300c10302c04094003074802c0c8140c005048001e440c910205005162145030180900b5101c0d6049400d03000041c2442241c0700229a000b41003445903607036070881c0c8001001d042c801d42011004400000e101028045406100204140c4942400440035121000c80340c0001e0f000b10305500c420055013036000300400250200340d40103407040d503480c030340705c80c4016640c441180402e000c1c0c3c8409005000400c40c039a17420451110000c00040101e1110034000c1c55543d0300d43c0c0800940d480061200d0580c4042e802c460303c9050308481d100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487804784 1250 487803534 487803551
    0x7120e0a05060c060f18120909010b12041101020a02030712030201110f0409020a050d14011e0315090314070b0106020c010e030c09040303021c020301091d030403110a09020301090c03 80
    0x81c2d84076020700e03000303690404400110f94280e0201000d420680424044440e407000c04c402520708100348601e00300d0844040342028461424542c458003400c00702c0260b43c03e12031000c44408207000042c1c401444e100002d0f2814172640d02c20000342c000340b90000c0c1180d40050742e920458810030101c40303007a00117500300740c1c000b016001003c00b110504004101c00600d014a4529104000e4001c80b52010030440104041000703400140201c80b545926001042080c0d450100c46461110f055416035100440c40201000425160744000c1c140003070034140443c4800540c58100c0346210141c0242c12031080c00b20b852414013291805c0c2e42d040e600a6001c4848a10201d001541c4003851601c1c1e20b54180d00044120050b8141600025046403003400c0160070f1140c4101140801030494094081c0d403035010004103c0035102c1d00841c002d000c000300e0641194035006840603243e2165001c09404088074151034540307501c0e0400318100602c004082103469503119020000034080204d0020000f90a08440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487806034 1250 487804784 487804789
    0x302190903051c081b12092401060e012f0609252d061706090402011710030b04060b01021c1e030e010f271101050702040207120e0a05 59
    0x900c41d0003640b130380286a0383e1498400b0000c13444480300c04103000e043c03160004c1c05101d401300c0d03401007110001030500310308405503485152242264051030500000c0041000e550420006144000d0a00c2c0400704206103070045d0b800e0480c0940034078000c108030510b95151100c04103101c2c0c02800c031101511b100b0b030424241c0c032241c0e012021404100000c44001009030342c24a040b0700706c8507881001800058813070440b0012555005602090209012488012004000701e6040346d0004003200c51071110704042e00001c000070002c10708002e4801c040c80c0814908280d05a000c0300842d0b00c0380072584540344c03602d4440080c041d48071046000d403150807004101602140103460742007003282d564001c005003405400d900b44080140e4141455520994640000070a01443c688104aa00085061806e00e032480e0004810109001c0301c1d03928001c0e5420016640d0f13004104860800d181c03840d10380d2203a0001800a1149500044c00710114000f244512034100b07001d420750032411540c080743c04e681c0e00107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487807284 1250 487806034 487806073
    0x11070902130815010603020c0109050d02030309070902030108060103020f18100513090b0a0b0103110c0a140313090c030b06070f140c061204030c0b0a05061f0519030219090305 77
    0x1403c0f035400e04050018400e80c0d11075405001d105000d00e00120b03080d4680c0d2600780c24542d00400300d00050b0800001c0142011041000074014624894114074540c90480d0007a161141030200074481d03262400c09645680d903824802100360100c20482c40315040260079120300b4049031065900072601c1001c02005103140e4800d01500c1c1d0740289955003299140441c26004100000003036045c50b40d1405407500041500c0090245030309440020540048542000034031155601d802200b80d0307101300044211400072662540442d00508400728a400a0540a0f0042e120407012150058004103080007846018030a12422602641940e011a800d100241c1d07100c03505400da0035081201009a440b15030102560a41c5c003d0092030201010350540e510006060300646942100688540034031a5a1508904d14000444c2c24504610f00f6000300324060100c1c0540040a00a0a6299441d600d054041e80481d020b40303441280030044480350b0140034000c0f03c503030b000136101440b402485144904544d030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487808534 1250 487807284 487807303
    0x3060612050106170402040e030403150f0b010507060c0504051002030a12020a0504030818030d1205060108041a100f06050d060b0f1204061104030b0f091b06070201110709021308 78
    0x3504d0021081a0344005010b0b01d502800132604140d4071401401303024020b00140c0301a6104025041e1007605042c3e445041e1400030b240510020303d4a41c0540140c1c2c1c101341104c0317040b944402c01240c00d00381e403a410340e070707038082c5074001c0da0070581502031117000741da0110003010780c0b80c0d041c2c95940c0040a041c0d100c8080380905200180440c2c4104001c1c0049211080030300100c3c0d80d582d54596080300810042810103041c12502004141e00c0313181c5134849100d50050690000003031a140c0403d161640300c140348140e280c9145c410b0101c008001c00c1c800d0090312001400740c078035015442c81c06a44e80368003d1840c2e0003131250070001882c1c00008111288050200c030303980b0804615003400c202c00400101070581c6d0150084548594078150500890402c8001c2c10086000710302c510418544424840c9001000404c031400c0340e000490f0007070003071081000c0d4035004803082c2e0b00306840fa0701d07510060304c09203420800940d161040c2800002d03120440d80041c9020b0440e0740317a00310507a640b4110141e981c60402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487809784 1250 487808534 487808537
    0x81509100e010605031902030f0c0d0f02031501030305031e010b0403030807050d110414010f0c200915010e1002060a0213090e1506030c010206160c1203060612050106 73
    0x1000c0510100c056900880010014003000043c0c90b569a00004d02e4081d43c00c107203a07003504000e40c050003580f50030720494100c26101ea01402202441c84006422543c0c2c5042c0107002080d000c20710010340d2803c204854090440010000706541c40303060103000b80d0003c541051600b0700805e500d041968555a4190403030b1a03a1010905060171590213460b00d0784003c02d1071041103405c0c46190300402d0303d07005075403560801340c00c02d9940b80c3c103103111030400c41d1400f03104038140105484022502c81d404804109059000201c104248019108100d01c02d1400c1e001aa4051081c009000941042241c0218841403d0300e4a500c40700e0740b142400300d55041140300070056081100050440303070036a0000c11108006100303404903e034460300740b102141e181e1900b02210381e00c1184d01d00c42d221009203195420401c00c50040c201042d03040c0000307581d800001c000074140039203c805802124081c8018243d070300d60045c40e2800d88000c03050300800510b40c1784640d40000d010300310401c0701661302d0700c9514161102c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487811034 1250 487809784 487809793
    0x705010c27030f06051f0909060f020a0e040b0303190201140106020601050d030f030219030b090619030602161211150f1f15030c081b03071101060816081509 69
    0x480c1c403413000420008042038030410070700300c60886401d0b1400601c00035003450000001c180401d0b0038075004480048404050301c038810010364154070f4009019402942c0e08460105d0181401340120f030a502502c0308005003100040403d2120741e0b019004110152125007050200d42e0f0b886c0c408a954101c20f01c1420b401030610345444020a2241c401407900400e03030305003d031410f415a1465030302c0092602c14480029660010800c0030f01e81102c41e00d070400310850300300c10401c20300a41c0c001e038158a0320008101503400102c01c150510190b403080112500143c805c02c004d0030809000e4400d8200721080c50380d034042d4004014000407034403a1140207440c00c0318012456601c410f50014642401a141c41e08001540c100150307440d21010005c4441d00305a902040c02018000054841100a000d120300001e55680c0381d02001010030580c0c1e8841000d2415801d0b020102c0c10f0280100081e0704030b028107000302c070718482040c54040c040200719445c42c1e00301c0304901c9488034121071601041c2c4500305107400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487812284 1250 487811034 487811063
    0x2070317071403041a0609160509010201110f041a0f0d0506060c0f010b0406091a06160606030b070f022a2110060e1504020706020705010c2703 63
    0xa9520000758048100d0811505403040c019007240c0755002154100d440d000565514200d003194248001d0b0000000c0e2001c034464181142c1055840e005018140200100816010341580c802d401c0001d0350784244507441e0f41c507031092685843c942c0c0079000380c035140408000e207410100f1100007160307043d510400d035403070501d01d0203642240074042c050a1701e81e1000052000180c0c03e00e091001c010355880c3e40c000094040c2c5103005110503203003903500c03070025185840c15603e0211599001804c2c0384030203d440c0d0340e442580410403c00c0300403001c0c1c0034000c00d14108000c000c10034041a01070003007001f80c50b007040d0b0041880d41241e4a181d03e85500d4407040100c0c122202907003a54144001c12100105581c121401c66802c040d80d1890565840246038810724030500c0ca01002d00c00e20000c1e104030902c1e00524074080400c1804140000401800f0790350005903d0180151a41a51561548503000b4080e11528002c0200810688070b000d142c02500c0000300812520500010700440c2d6120320100003049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487813534 1250 487812284 487812317
    0x304030806040f0231060e0a15030608030c210c150402040f020c0703020901050402280302130b030727210501110406080906011a0702030a0b0705120604020703 70
    0x181c40e080040c02c164080c482c5009000808a01c810040441217038010041e000e20718000031018030303502600034401c0481941006448174007910b000d07602d071014009484860309804034003c0c000750744140d07541d01010070b280e4149034005c2900c000c80070301911f040740c0c0300504014000881c0f066181c090b445c1d60007040121007250340404100c0d8402c1c0024400110b01d200144150b0a80c2d000102400c140d40150405004500e082401c95025103000e40e4210b05025460380c00091181500112000c1c8030149241c210361280b282c1c044583c08001800d041d4413003550348088070705070341056800034040f0301450019030301c503007030034084002211107402e44458140c0307820f20701900350b10f1524a150100d0b004890080220341e00340a0f11103407000c0320211581d0b85141010051070307150041d128088a811220040000710740b01940c01c0c01c4820241e0415584404610019241070007000d4000c0c0990000030420581d44d0300840544140003030f031030b0342c4501c80e5100d004000881c80795210040c0802c0c0308250409200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487814784 1250 487813534 487813541
    0x8010b101b080f0a08010b0703080402091f030809010e0102010e030405010e06041508071e1706061209060a0c0309050618073201030b03070902030a1d0d03050705030403080604 77
    0x32a114444021a2107154552942652101000c0c80da1541e001512020341030740482994014410003c0313003402c00d002a40c004060181c0504080d200d00d08403401f141c6031001904000000e00401c45400305030319944d1a10a11981054500c0ea02289518030301304801d50041c0510b800000b11440030f94030702824000107503613607006043c2241d0059403d102c0451b0b500d02c919a100b907030300c81a0700c0d403a1035843d080078000c0003500e0a01036041480710703100410318003a8110a05001c2c000c1c004261030780707659911000c03d469004951f0402d48400f000018840398600128030346000c0c0703812500c2400341042406040e010360301d00c0f003001040743e8450790020303055011000c45062a40d081106a07214103680d5813aa415442120350740701da400340c1a0186c2520201c00e07a40f440100070080c01d051119510207400207481d5021845000344060b000030006440740d641e540a501502191617500510020340540c0541d103035101410070000c030f843e1401144a4501440039a07129503495620b00495580b05014417024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487816034 1250 487814784 487814807
    0x4021309060506330f0904020c070824041e06020d0501150c0503030f09010b0a0308091e06030a0e0106050a0621061a070f020a06031b1b020f0f0a12050708010b10 71
    0x5d0708144a590804d80e00d0f80001c0c003103502179400622020303081207080c2d070800541402e00c3c40307000503407105404820940a80d15a00c50f030042e1100356401c88560b004952040c0d6403400074036180c4001a10440001d071984013038140c41d850b1104040300308100ca803d40e0440c1e07500d0b03000b030044c0c1d109000269450100a0300144e00844000003c583d101000c0013007a081140e51308102e44508000c40c4017001402c150f0a0549441002a400c500300e0301c4080109482d44000707000b00c10850f0b161010b40381412802d400c610000c10b0040c20705078640355039020081c40702c081108003036a4000a55004000700c66103020300c1c02590080c104190346100b0303a070800881980800300c200c809a00c2e503032110007d07980b000c080e05e0080c0070715100070808224036120355544100b81d12201040c041c0b0702c070b650103900c02d500700a2599260706031009160740c008040010742031a0800c5080b9400043c00700b010564079981060401c0a0744900100e070300c21925001070600380c40b045020150030032000114448601c0c81541000300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487817284 1250 487816034 487816057
    0xb0609130b0307260d1403010303050a030905160302010e090405070621060f03140f100207020607050d2d0c0b0411030d0e1201020f04030b0402130906050633 69
    0x460f40c0344055130f000303140b51112516044400c020b84100900901c8090b0042c6098030f482d11101c540311350000f4031030006000c0a0100a4042900b68046000394072a0803000c3e0810120390107072280342e007103050712801800100c0c00184500070003051800c0c820200e43c00390b54000042e1028500b48481211303803000c1c0302c0404030310a910a0080d42080b103203115050103020781c0042d0420b80d41c00c5080c00c1003440600c2800613a143c0c0030388044d841d407000200710400c1044001d000036948112a000180050207458800b03019401503510031000c503900044101d0f0450b000200403140c0210700110401c0d50200810240c0100b071b18880c405c000540d801442a034454491180c0d140061302c0311f40400d20b003084501811000c2082446004198501440a070356030960302002986000c1462032100c8503802a844010200ca409501003004c540e5400e1203000192840318041251940750b08189020384826100d0314000c400251100003170aa00781407a1401c92520000307c0d0001000e4018400d456000704c25100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487818534 1250 487817284 487817293
    0x11010e1203122d060f0117060103051e0906010501080127090c120506180304080a0f03030e12040f0603020301140f010e06070c090b01020102070215071104050405100b0609130b03 78
    0x543e10303c0c195484035164049108410707001d150040900c8030b050f55818620b4140100041c0d8050544015040d070f81d030101c070038a0049107640f41d06441d5160785080c180c040b10006032440400001660000705141240d000340d8a200443c0da03640b2400156200500c4d00c3c80d0000c00300001d06c60081090780110b90000d03c81e2210008099076160528038040543c542243c0c140c0055040c490360100b074480d007200f80010000514a458601000155038080c0d060004002e007000b210358105043c001da1041c1b030580032000649446810348608080e81d580240109042d20380803420102e4003174803d10949050b9504001d0030314281402600300024203111000490402c410008815500e4813548003600c817007445012000302c014201108801555201010941160b00c103000350780140c2c0c1d5051110704e01c044410581c640e5094581400080050016403490300300e41410203010030480d001035944800c4118810802c041051081006110300c25141801d074043c201c542c40800c0d0210035030140307059540c02000c65 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487819784 1250 487818534 487818571
    0x20d0f1e020906091507170405100c0501090c0b0408010e0a02060d0209030a0c06170618010303050309030409150806070e0109170c12151003030507140109050a11010e120312 76
    0x40da071790b0032500035200c0442c00411908200028001445681d03101309505c2410181080b01041d4000c0e06000f8940412600c241d005092101c00e40c0300700b054942100d07134400070384e48400c9008090f5005106951281d03180110000403150003080320f01c0203d034010101850b005403656208069004501d0300c9516000308600000000c1481030701c1c1008000c552241d0582c05520034000b6aa010010800d170701400070081c1034015040d50460090550744c1c5410100c0c1c482d201d181c0000e203103008540096212a20303048120007090030340b8850340d04503068941144c285544500d0103c8241c6a1b90f4a01c5012414028084c44183e41036003640c003400d10642d04413004854402c0010b130344e0136428407001038107402c0800415a803124962405600160754100741c2c5000f89980c1c2d004010b44140304e0080d200000303070410078040120a40100790b50940010480704880c440f414080c0650310000c3c140c03030109503080900c203000e00b00030b03900ca00d5141050024504002074a8400c0010340c00040c410300c042c17181481c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 487821034 1250 487819784 487819789
    0x2010e01050403120f0203090d0305090f070f091a0306160203070f0606080c1c0206030711030d0f0e0f1b060715050405010501050904020f010e150d020d0f1e02090609 73
    0x80c40e02c21406999203001c1c0d41481c503059030454841050105030540104100111068005485c2e0090000740c0380004099542140e0f45041c905401c0c4500018080d440e0009030380043c040100c002d40d0b00e82402006030b84400e903410903010600303502c01c81c0c06030000c00010320707904c294030f011003400b10755130041e2450003006569908501660780000c690099035140305200200381040055921101525410360b000c885104221500360082c1009205410000020380d020780b1440030402112140c85c211381d21030000403103000180c41c1582071050403615004a0070320044000032003800103e022000303040b5103007210100603412001b40c4940c0341c003c407040000340c0000f00081045031828024034000103c0b400c09113800b42c25908180c2c042c5100394020418000542d4030005100081002420f10314210500d00c004204140950340e001d00c42e502010541d4840c03c01c1070380041110b4045d2040400141e007110000034100c031007400960b9a80803000701c1500b0414900c3d40207100708200144a90b092800c000d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 487822284 1250 487821034 487821041
    0x1506090f04031206081c030b131e0906051503011b0503090c09070903050105010f1409090106092c0307120f030608030a050d0b0a0302130b04020f07050105060a06170f0702010e01 78
    0x640b0190f006c2c0d04030180011250042c5200c00c956850103002070a004000240c0041e65821103411140c1d0b00c684090750024501000310482c0d103200d005005a82c0075007404801001d00319a031650782044818150610718043c494000c0380d1154420440d221468400111641c1e00f00504400082c468045060b90039071707a041310340e07100d080f25039166038a40f400c4d460600d0a64006034031403400381010701d0040c001c9121903510b004041e0300590b41010b01b50348040815016020903441020345501d8032121055a00b10b0121413401509212103140002c020382080668034802d103071001c0d00e450340039106800514800d002c03503860181d00389400b1070a20f0300c0350116070460744181641d03808074100103000720056510340101c000752801182c0b0780000d646541c000c038a05d5002d200c1009a902e03900c03c8511850340d80c56041c3e0307204072000c1110a4450f41c0310b10388240204002c2c0c130042d116040d014800510180710301e40710b00002030f1600741481c003910f408880c0d100d91000585000c00395500c81c104030005080034403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 487823534 1250 487822284 487822289
    0xb010603150503250807060203030a09022706040c020a0b0402190e0f0f0702010c0e06090607060e010c02060105100f081e0406050610030606080402060f090901090e1506090f04031206 80
    0x30800c0c80d80080751350a002e000d034007580080000e401c564002c006140d004402c3d00d600007a460008150600c040c4009903058050b0440d044807a40a960021808240b400c540d9110b90700c02d980400c41c699015400360b9a4540d4404010b041c1c524140026006042c44502420051000300320014941c2d190503100c01e0550f801c07144290010320260400c0158030300752703450b940c01c001c035070008004c00d00c0300c0d4070010014100b20b407906010780760000c0d1005e040d4941e41e0480310000d81162040007011048084a406000f5188810700188503140011615207050701d400c5010b4811034540f0102680910300907548404010f00c40250000c503214003440f075070302e920351162049200b55000103c1d0328103d0100030212004070203ca0400d4a8154280712080e0403c070301e10340150f01162060703154022680f55040a00c152b20500d41c0001c220000011010041d0f00201c40c0d03070b2010025180540030a0b000101d031544121441c80c3d00a443c500031419100c0c1c0f1440244c1c00c640680b400750001e44414003101d0175540c103035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 487824784 1250 487823534 487823563
    0x30a0b090c011701032a120809030d02030301060909050402030102090d060e070b03100e0603121209190f0201120b040e0d08011e0605030a0e0a0b0109180b010603150503 74
    0x6800d80440c039a0f005842000584041d08080c10650543d1a15202c4038452000d440109038103022040c04030941030707400d0004010010703844541016500d81140c16030001441680248100c51a06032624008416281030700d9107130380c07440e8000d442d008445019000107030069030155400c02c000015500c4142050301802d004060103e8030220f150415490110503038004030400c1014802d005054225448a60458062070700c0c0c800716444000000703040817980e896415048900150984241c86110f5136140320317000301001d40e0880341400c6000b2180780721210b030052529000702d44480040d070195000f100da410902c6c0c40001c1c0a62084c0c00325080b181c02c242182c52650203940c41d0f0700046e0780207540c0c6001d8441d001040c002c19005201444905045014030000c2c00404400644008106d500900312900524101ca40c0c61966042c0b056504c0828010744484074102942c180356107580300301000000c0d40c001c6540384140e00c0c0c407600300c0007880400007001c011810508002080d580401800d2802201d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 487826034 1250 487824784 487824793
    0x4080405090702010603050d0e12190c0f060905040c030f0f060810020c1c05070b041a0106111005180604120e0a080c010c020a0b0a0221090901050f030a0b09 69
    0x1403404029031200014075500071681003000c1480090350102d01a10b120300c55040c2030340f004503400009040d80040c405031340c200f44200911074101010252240001c1c50007141a001550b03119100d050031036200d8090380300400c20922082001e820036a01c80ac20f41221442c00045001d00d03001040191070245070a001055112401440080c0c4188061000d682c3d0940e011840d10301c081c0386540c0c0b5184400c41c4441441c030354400b003d1445008504480c00140c1c80202050940b4052500040396046540750304001b0b12000b0001c20309a0081e001c50b0450407c100042115003c1350b21020050300c1c9c01400d0000000e000c4041000b0140704101590140344a005584100311315640003e04130840304040600c1081003900c00c1202d50004a03140400403030a20340744031041c0c1640081001e00d182903001c0b603100d200016008200a50220349d40c00c1c100074001d41d00250704441541c212950207070310080c1da40220030400401c150f280010b040e00d41004058103485946915480c0c0558800044940d015035401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 487827284 1250 487826034 487826039
    0x1230d11010909090c0510031b110c151e0c010603080d0c032c03160506040b090706121d0f1b030a110402090f0a12021306050d1217040804 61
    0x3040424000030f0f00c003409081080c840b842d00c860401c2c150902c1a00d01030300c5040300000d10301c0d00c00d4001148001d40e070b03001014580c5801c40d0041000c01034440307024660042e10581c00d407034942840e02c0401d22500d00c00103420840b881c60800c4a060241c078039908040d00030031583c42c134078200703015201c0118000c010031603d9051f0740360120b06442c14030fa43e902c10075103881c10403052001440300c5099500a200004096541d85402e118918414980c12841c0c1e282c8148410f001c101000800c80d00c01e17841400c0750106a190206c103159a030b4030b40d02503034000c100f00606a600985d0329070321800c2015200302c01410003001c0c0513001410032100307241c10981500080c458036070030004d540010140b14403d0300100006244c41c4c0355600354400070000e051169800051100300c07503450503890b1042080040070802002e1382d8407030f110380032030040311f080307002d00840040a2140706082c0708030001c65101074001442985960350740b030048050100c411080c0100480c2d4569048000d0203038a104510403919907680320f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 487828534 1250 487827284 487827287
    0x120030a080f071707050702180105010e1807030c020c09070203130f06020604030309060b03060106080a111608070f08130f090510090e0c061603110a050601230d1101 73
    0x208002d0040d024203214105204400394420301880a103c41c6142d0341c5a16201c0c08411905403041c0c0c440a5400700101c0c0c2203608115448109030704072074003600c94480d01c500300e20a004c000144100d186a41c1007490b0000380c000b90090b000443c3d41031203071050310010b00f0304100240d64543c06807450700041c1d1010810807241610100c02c071020303001e400312402e0014070305540255943c2c3e000307000400705611201e0941c02c01051b608140c1c0d80d0039004041e54455a104c1c3c070020b05a18040750070700c8015003012a512440d00a0004a8070010440358110151041d642c0f0381c0d5006034000071007102e0403448241c440c1c0200b0002c0010700381100c0072142d00e13210349103401c008800c000c00306d4009500c01450304080c440c213016a2840c900803288003150204044540e030420a0419401338000e41d04010000303a41400150640d085190491094444440c20f50702d081a030366559501160042c41a8804401442280c03002c6007096122381405035160308031801d4034041202214103c60440e542075820301d1031011507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 487829784 1250 487828534 487828547
    0xf06060307060c0f030e01090801020705010507140c0715020c1201051e190903180e04150203070801060c15090510060e131401020c120d0e010605090a0b0120030a 71
    0x500062410300c00400d803a80356060413840d034500040611502c040f880160703900231602c0c1c10090000c00f000315250602d60034401d0181004031440070000300781d02d90441c0740050032070544152000c0305000300405410003075504803e0203100111300c107510803041c811078940c0e20104003881c01301c0984000301e1035060402d1b10800035039200f0540540942c6050070403d02982280c5e070070300c4020500802003416565418103888400b2205010b11090350580404921104c21000c2e09004500c03441d2401c260700e41102c214001ca0100741c4180d0005604e010040000512851513030b41c2003401010311200b80b122003907500e0101c0f920007400321016005080043c00500b41440b030b1100600c110f6030345c40c07528580701640705c4102500550080c0b80c40d000c5011005021400d5050b01d0186540c0400c0b500480301c020800c0e02a031700700c00900c400d80c5040c01c0f07580c0001c20041c0a20303811680098006505034480060f000301034400501c20390304200d03000d41070308812550f03e0904145100000081c6aa5080c10034009000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 487831034 1250 487829784 487829789
    0xd0515040e0d09060804031205150901060e19060c15110d0902040f36052b0c120c020f0a17070602010908070204240303030c08011514030a0e0f06060307 67
    0x5205d166030402020035002a41e03090024a0b1800004880c0e460181128400c54070080c01504984090700200e4240c2d0014140c40441c41e08482641e0214103d0b405500c0d403901c203000704400902e1f81c41d004000110802d0070451242c114060204001a41422242c650f0308500031000038142c4500b6240d0541c20700d40f0a1a5284000080c20720200b024440c4102c03444420b01400102038200071159410040680001d82c450396101055401610100c04049240402a41c51844648040c8255640580a0300003802e41e103900070580081c41907207100503518407000f124240d8018510445925007680d0308682c440150134003c2401c201e100c5200c207910326007489900030380d06683c90444040041a02c860950f4002039046401091341480040401004024640d043d05450030391b031004010903030140c200800d9415295200308160703a894a0302200d4410b40031640c4040340007840307203801c4041c00200469000c80790503808501d940000c0c1045260884820f1403421f40d130810b0b01406024601440000700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 487832284 1250 487831034 487831037
    0x317160f151a030a12140d0c1103030106020705130e030304030201090309090e03040513021306020703030215060105030414030408031204110d02130b1f0f030506060f0d0515040e0d0906 81
    0x341e042d00004a5500c11810740d001d8480700b001c0d0b020800d624032800e140c04500c1070b294515519991050107600103041c0500426000c9500d03103e0381404805d000003502e048541913402820b481d4034040a000c0d1291007060310032480d43c2c59041c00421801c0820046d070080d8400c0d400094100794a050050402c007880d0881115582040442846251b000054800b502c0d4115642c000f1000e0f041c46807002442030840c0082c2514074200d000a03601d80103d50740080703d0003502a180710b81080700010a0641c022101c15000c201c040c00860049000d400c102c051124000c400c9031310f001d0f1140000c900d107401644400f40304e041c03500c0400040006004000741d40c0344041c3c0340505600a0b40c0d00041404201c004406803030fa40d140c900c40800e0752036103039400d03a40c5d0708405032100000003d10010b00480034241000003003800e010214080c1d00300402210361202c100840941019425402480078220250450708914040c00c400c40c10740c0d4880c0701c3c0c1107199010341c0007012600020200074000d5a0154172010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 487833534 1250 487832284 487832321
    0x4050d021b01090603050a0902040c050c0105070e150d0f0e0d2007060c15020711100f12020714031b0708010506010e0907031803020c010e0a0317160f15 67
    0x1000743d070002400790507a1064100441d140d0754810303880e001014400b0001e54080c0c01d113454402c11a401c07100804884031201d009000d940e43d8100c0588014820040182e00890803c0000245a01c54800340030031100003440401c05803608050741c3d040d21004150f503401c1c0d80200301c54001c1280c1100c01d9a02208038210b400c51b0240e2030034580c40e21081c0f1031190308244407109540c00304016060342089035000003007004640703940d4542012404810086000c1740281e00f0340030b182e064640160030080e519a4203a454210043c40c24000310701a403c50201220700c104a2492280440414406030a0703a02e420088100906608030b203062600c0303070641c4404060303450101031203026640000e0150101009403400a00798503450402c80090400e03000441d83c20050001c02d00c10181d01045c51600200c00740c1e1510440d070320b0001000b0769800700d4807004185450581200f00d04c1c0c003140016001004c001d590900100e02e00e502c62a50003611500d003207548441d9000340303441d107260740c1c8500d001d02c0068042d4030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 487834784 1250 487833534 487833583
    0xd0906120504050c0f190902031509040b0703020a02010e0a12180b09011409130b0406052d032404060c1b03110705040905030702090109021303032604050d02 69
    0x1580c580042e811800e002e4298207030100c05e02d40f198100e0500f1400040c80e1650352070703543d80da500029007040d0b50301d0281e00110060360b40301c2e1400c206080d00554100141e000191210202a0000d40c0030287e54002c7d9500e60b0301d03804034160140072000003503000303002a4960b4060880003c1c6055481c50702c20741d20310941c0d64103114240d0001c0582e03000f003000b82019003040c22403203420441800b4907082d142e840440d403000a081c400c1c1c00d0f00300044001c42940e05000003503d07042004620b0802d0b0b070405821200c14141c4100c1d4075080032088926503c0031341a90380d00000d0462006c142c01a4900c0b503001d080001c814007080014910824248145c14580894544901f640480309100d05903802341c1000b10300c00b120f1079010003e0001c00300400000b0320802010220385040d54503a00400c600313034030504404c0c00010300c110391802200c031554400500c1ca95014210340d015903180224628000001041318080381140b00540c8a07603008071301480042c034501c190f001f0000d01e00300c03205051502909006410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 487836034 1250 487834784 487834793
    0x503091212130c180c09050102030c101a0a1203110a03090303361403150f1e070507050f0705010519030902032e0506060306011409030d0906120504 65
    0x180c2d00503810364518251584941012698480d041d0099101c0c00307404101c0c150300740310300d03404907058601c291103051185036a1001a6101d01400f81e20003407d4220900d010000c0c4165808402d0580424404400f030985900110301d03d4401d90304468549404591004181070f00044a0a079000221000b040180069a00100462940c0c8801003d120281d80c08a102d410b500206032512160a00c42c818107104480d441030b420502d0707200b41003030002c040700b07402d5803814041428007050b090500008240c1c6c0307a4854449172424014401d0080d03450a2010720144400302d11500e0180d84203640c1c59440740b046081040c10b18141e8143d500709544408820030107660002c040d140500d04140f03480105080401c8160f000e80366504000b541801411458850b030703182e6002042104600e4818685110011002c1d442110800c4d55501c0e03100c4410300000b80298411011403500030481544070341414004800300b46000c1300d030745030800820428801801001c2e404103a800883c400646c080c045c03402e03d81c69 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 487837284 1250 487836034 487836067
    0x190815031b01020a0b280e0d0e010207030515060f01030c2f060429090a0b061c060515031b0d0c12060b040c0504030209070804030e0d0305030912 64
    0x1000d414404030030507849030507802400300b03241254109843c01c000b03240c440502c1500381c400c0d800b0341000d4801c80f01d04010181c098404d02001801100061008003040783c01aa425200f0500d054110300c204400880028000d002e0740380c0c0403004041c2c1724024205941080f65103142494000e0406103021040744c0039a504c070400c81d028900b11010b010f0b80210007220281c08580c1000300300058400e82c41404200b00202144500303c01281c2d0003040c8003405200c101c408102c090f101c41301d06a000030204c1020904034517943e0341101005010142d5100441d0700d00000d41c00c000f03000c0e50740554980400c107a18843c400b803010228401c4010b019031258002e140c02c1e0002c500111503010300c07851210a0200310003c900300001d04031070070010542482a00d00034001d0a05078110601079818480300c40d0425008005880940e94001e000a00c15a20030b4000c8541758001401036082000d202130b0040c6a44a0020000465009544013a90391901c5c090302484c0010b1101c400710401003c0080c56851000c804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 487838534 1250 487837284 487837303
    0x507171302120304050303210f090706030c02010b2707020607140f09061b0c03060103030504060e030109021228050a120c0605010e010303020c0a030c09020c030f19081503 75
    0x48000703030344550b000e545502e18000d94002d150544030020303c40e2148035500036250385101004958440c1c5656000c00c14020150554842d021a4091542404082e003e40c21540590b1000e100000e19454820006008050301c401d60f490780c07071074180380401c2510110204503403081d002e000034004c60a064200510600f003180000040c240c020802d100400201d0045882d88000144200c0d02c0301c12040c00c0c0c52111180840c111254481e00c500e0b0440750601113190360403250161180c82c1014602041542d8050007446442d40c0341d503031021341c240180d494100c61010705070702c900101525011882445407007840c0c6103009080d450b4040070341e40000c03400256000074a81c4400182803840c00d8900907620107400b42d10060400303042c880003082a65889280314100e0b0302a900710340c0d1001e00a02071000d10041c5001c06005040782c00000c1c4944d51541e0018070340c42c0301900480c0d04c0d041b03104500120941260310000c034040c88514002141a03482184180c00c401c002c0403070601c2c07a0054000036961140d12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 487839784 1250 487838534 487838539
    0x60d06470a09021b0312060a06030603030c030507030c050609011a0103020f090d03050d0e100606031b031805031306080603032b0e100603020102161d09011e0507171302 74
    0xf8900800f04c411003059041e080c2c00f001201c1c0c568040f60b40d4150b00711411140607000b0b842d8403400181c0c491082c059241201d42580b03c55030400b905880441d030300c0d800200c086e0240041d0f01103100001e0020031010744203c4409000040600021906048400300c8201e41410035005114507461103800000304c5943c804103c48950300003801d4502981c1c1c5010744034604540718079081401e0100079000c2440801c0110480d0308000b000d895803425012120200549000c849100003140120f601035404a025058401c503810042c40c2c0541d101451a4007040c007002c09140c0c000f0040116a8012903070f290407010440c003450420354004221032500e807080c2a092070400d00b030344e41c038103212601d5405043d0070900b003819a41308a07200065003024102e1848124010f20030125024040b191560b101e4007901c442210181c840c443c40e211981a22002400326130340340d582c601540480031101405106441001040130a0a103080c400144c8041000701c00c417001e458040c41081014800026002103d83c0d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 487841034 1250 487839784 487839787
    0x321061a180909030702011e0c150e0a0305180913081c0e0c09070302030123030c06070b160507080307050703021507020a0611070209060d06470a0902 66
    0x500c6807480078054520016007007011a030510a08460120003130070308030300070380712001c19550f0700d4412181401c0c0c0e00001d0000584070300d101d50000312410321441c048494000003003000e500100206060134000501100807420020b80e08001500510401d4500d030340403249420b4074501540021100b90802c00000c0c00c0000c0080c281d80e9804003000c140e521030b0144e1504100105007186015966100c04003003a10800308000001c04c2c0e98401c0c0203c906882c0c0b6610000408c202c41703418490411013440803a9458000e21115511940300d01c406000f841340a03d00340c1c15203040c05c0705c03504e004080f030b061004104a01005071001080303013001100c0d0000103518100b03a55100702e0034100c4c02c0c101c4900144e4842c669071001d020030705070f002031100092801003c08005a250344c0718030003c00d00c50304c0720081d001988900040c085107410342401401c1c501807070004c681840c0d0b5a84030a204108407141528100381d901c1100c0c03a03170540481c90090841c095a6107044100c5250016070112903e20030441c007070b0740 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 487842284 1250 487841034 487841047
    0x106290a090b0412060b0f060a030207050705040f090308090d0e0d0510060306020306041104231305040605180d0c0206090102031e0409110a090b091c0321061a 70
    0x10601c8910010b0014405440c0c6a60711980d200071000d100c0030050310024141354084986142076170406048400003481e071440d01c40120412b4019412610341543c4a000300180054161030314003031807403620680c1c0320001e200030003413034081c1401002030300300c1d4800d07400b16507125510303500b10421603040135085400c8000d52201c0c1c07400f5071624103640250348009003081c80010410044d9000b40d40595400c440503c1191040b01d205240c3d0301031482890001c5040204460b003a4051000002009030040e04103080807050300b404d00700f9541c081e00e045031a5561031081000f9909000c000b200700d65a010041c0c0b01c0d81c0701000000384552943d070f1010388524400903051400703078000c01c116030031000004150f5114034008821000103400a2203240130341c50034040b080c2400a280c4d02180c0c000c403040d071501066a4202034182d0f02c1500302100e00c40d0445108070440240614038521049441d100765502020060f0901142c80d0010100803e58092418190103101d11444101041e0404510491603a100d49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 487843534 1250 487842284 487842287
    0x20a0f150902061602100e010816020c0a06050705012d0b041509090b060114160204140a09110603060102280209040503130b16140f06010b0702030106290a 68
    0xc21041c00a40c01480004c010603581084640004401e008442c51408500504070a541c0403110318012400507128200141e6201451020b601c0349028620440d01420038000100f0490391150b007140c40810008100e48003004001d00070300d19009181011890150507840c480300700140c510300481c02860300d4218940a5841e80c0d40b02020340e03000000100081750b80e80e40860700030540c01c6800d0340c1400e038260010706694001d4003609404400d40c2d0016203032074910340f1010404094650200d07400b940f501011004401d000000600444003030f000051421410300d441c41c16450100c0101d80206000d00411007a40c0e00402c0c600c0c3c020700300d01c40c14400d441c441c40c0c210300c1c51012501c0080d44540c1d400207001c1130007030000181000d8941802042c503205d499403131120140c0968821900319200c40c0900e000050066030842b001e12010030103c4070300340814401c40e4203145090300030805444008c90071409614090148600401542c0200e103200f17040e101185c1044041041d036034240c1b1070002080c1c0d100a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 487844784 1250 487843534 487843541
    0x901030506030a0c0f0305010e0a03090e0c0403020604150f0c0b06040c14030c0301170106030b0727080f12030c181c1211061303390201030606020a0f15 67
    0x89074013641c80c507505625182000360444190005451544ca0708804490158000552140342c0360151116107281b40b4106110710451401400c11040d68000d1100000680b20341c0b014001420313884065108410100c1001044a000d06040c10704200c7d1422901c00850300041d000c40d04900d05690201b50701e6480a010b850004100c07007074042c0701d040001000f40303005036900030b036041e9440d1400c1980521903a584c01404d940c0207010180c408202c0b0404140600d0080d900107904007a02c10b44400701c2a0844003000d8100c003598450415500704401940302c114050000c07800507031280e1656402e5040c03540040301c050007050b0b01c2500d141e00f00f00000c80c2d295600031203291241d42c2ca105070710ba404c500c0d2421642c074403440d10501c0089013011f01d80d400703c03810100c0c00510852240402c010090680d0f00d04a55112001680c03040305440454100808500115903141000d0321a261401600480c0300040c04c5030400e0b400442190400305407480002c1a030341118405940090503040c58580c2440e0303d0004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 487846034 1250 487844784 487844803
    0xc03061504090902190e0c250b10060c111203070b130605060d03020d0f0509121606020d02060c1e030406050406060b03190f1d03041503060b090103050603 68
    0x3400008180059512107641249850714801c0da00c0a044e07040d0129402c51541c4940140320b9600d40000000e050170500c07002401071708407001c000d0b07810808036100a41c4443c10075402075908038009810401100b4400a0b4140100785900d000030b0000c016448000403601c20400e2103200e07900041481c0c01c1c20000300b081c1d910913900020014041d040c43c6140311025080340074100d540b5402d0500040491503e07020020030580c042d005440c1103892490304a66403d410001d2109124043c4065511511201c03401c0304a4203035900144010303410100d40b20f1045085900c1101154800c050714501ca0303a0200303050360460104050103440700d0312003c03202c0000608850b54075591401004002c140040c1d03400650080e80a50300400105031100d04041c0c03544004c40c0d60495201204400c40010ba01c0340d400741c600031154180004e03402c0855047c079241100c1e02c84250307250344d00104051040c100a225901d208550500702008940d00d85410328001c2d000340c10700b03d030605503110f0000b511600e083c40200701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 487847284 1250 487846034 487846069
    0x90c020f030a2a02031c08010503011e05040201121a0102100606020c19090c050a0e040b100c1707080a09080a03020a12020309090723030609010909081207030c030e150c0306 76
    0x512000110030f0000c4254091b00000140d1424000189414107114502d03800501101d483c1801c10010358084c05058003074401c81c100709174050080c0769140340788902d5807050034283e40450400d03070354000240382c801940c0344c400e41249402002c104954000031181102141a05c4581e03e5150b1964a416101c0e91540a0008942020b0a5050080c0c2c00710042c941d03501c0e9926040c401e01038010900c0100d5100000075600600f01c0300030f450b59980104803000e4920302c1502d1600d070011000080341072603004408221024140410380c4c01d00580c204042c20050b111503802040c81c1c582948000f90740d9050341e1800740440304090080b50702d943c8240100d4181a03000b5140741001e05144100030b1015840104134007030514400007804084201c9030889019880c020103074401d90f400d2074401030040a0240c421284690100702e681c284155842c4028450b01441d2000111001c0030070025003995554004c01d50300390081c15000c1111030100000f02d411501c440340303494581d51014003080c1c01d001d02c42000003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 487848534 1250 487847284 487847293
    0x7050106080616030905070b090a54050408040314060403090803090901090b0301061806030b060f0303030f100b07061e020a0207060513050604090c020f030a2a0203 72
    0x20300e10600052240c01a40f03d2110340c050710f0040f00c0201c0c215102200000d001d42c00c000010081c20303209101900131600000c1c5203140042da90188075400c407142071207018038a00b440091000010f040903000300c5048200c8024007147c0040c01d40b94000850782e06080d44050340d600c01140030b212400b4152405194015284004041c41001150f0340361002c480850010310000c03c00320340e9080c08401d6076020313140504500241e03402c205590004d8444501060307007640d03039540c0002d1a07100c0c200b01000c401100d0740c0700217405070850500070036502c0014a09030003404500c080034919100001180e40c0706c83c4010018a0a48810411003400c42441e80541110440807520005015182d0700049454203440c4030b160180000e42c4801c0141d0240032005000b60b0480300d0208844e6016500811081e0048650211543c0d00c1d81c4c000750303031900581c0015100e90f0341d4081170181680c0400ca007142c20000d0800540c18604800780083c40794080100030191840c600c40b4407013080d03100c40402c002d0789a006050740c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 487849784 1250 487848534 487848539
    0x18020706020a110f01150e0604020d021902010c0e0a0909110a06030c02060618060108100e0a0e16050f040e010b04180209010f03031211070c03050303010807090b0604091107050106 79
    0x1420007440100e0f1800c0c90196040c8481494814454003031310001c00c0078000111403401601070508000105440c2d04150200a144482400351005102100445000c2d014147d5405802421150f0821903e4140020502407603c0b076665500900101d6004600c08110559141382507400071403008900c1d40c1055646402103a11f54058000c40c8082c4019421108959680307000c007c2032580d2032254100510204020030307203035442011940c1e4016030209003070120503642e0300c000c50740c001c003101d060030100e6441130018100101440b007078006c02d09112107014001d00300f0001034010149a50003c1c031a130f90347c0342c0910f41400d00b074120211001d07004000b0089407501d8a6194902c0e1400790049101c0c90401d00003007900451200c21800341c075010f1303491001d0302018481050040038186001d030f180081c28040c0f80c0000b03c11850346005907200b60042d41d140c0d49040310640c540f0265130042e1940d981005a145541c0d180d0b00141c4080321104030000c18482502e06550b01107201d1884082e06030b50820a01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 487851034 1250 487849784 487849787
    0x10f06060302040612050105150903150c0d0c05030741130509011a0a0c02120a03030509190f06090209010e010312030b01020d0c02060415030f06170718020706020a 72
    0x350085a104e5181c0316120000e003800d000484409003c2d9640c0590300503204007142001314090225504050202c3e20f841c028110000f280300405c850800d0320840004083d42600d07014040c00710f02c81c0c40e82c203009046062000c40a041400d401c0300d00124100c1650034424074540110460051094100380c901e06080954242025640105103000156406481c001580d00f4040d41090480b103555050554000d20384400c2d0241e41e01c0880300200b00b144540c0d0301c0c0c015130b58000e20000d400b061000280b11240007443d0103416a400100103083c180c00501d2140300d1442e070300600180860740b209040031040340030314189000704034506000c5d4001e400a4008102e0313003a128251030517680259070100503000c07008000c400380c2d9039214103940142c100324041100c0783e0140d015202c0e4144010541c2d810151212448002c40d8850440c0b000025140e501001c4c100781c06104140103400d200d40132640c000940f1001640c0c6140c0d41c845c0790440c22048a2640c2003c1c52941078446a83d4000c50566884504490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 487852284 1250 487851034 487851037
    0x30806041b1211040b070f0c0f0e041104050108030703050f0c0109032001020901050f0d060306050705090a0b0c1507120207060204031209240e030a0b040507061d04020c010f06060302 80
    0x140b1401c1840e00300c81030480310070300c07040d40c0c1200c0000040d145020301580d01c000d0b14172810081110460301002d40800c10301c800031310140107403125661104040c0747c80d080105407064040c9000c3d00451820006019412005c4120348456406007065a07650074020a002c409102e6209071302c80c2e80d40b86c0344081017090340c4244000d40286801e00041400c042d046241401c03440380110751400325031304004d04101d90b0a2440500328405610a001410036940c1d102d540980c1e04c2102c092000441c00114528107280c080b00d2000036003100c00f68581046011400b1641e03c1c2001c2c000c2c103a05003035460005024920030306101c00046000c49040d9150303003062901c907019401500080b40e45d03400e10101c18030618450b140000444195050300c0007441c20103e000300094401c1e1203814201309041846000c00e803000c01400c10b29604c9815a07104c00c2c6024103040381010f03000e82243d0100460854004404440b10048803980d08049a0042c0d41c0c4010001da13500400080018014481c06c10340c001440c1d42d050390 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 487853534 1250 487852284 487852307
    0x130e040b07031404111c06020c0d0e030a08070f0c080d030e01051927050c040b090405070635010e07050a02030409020f1b1c0e0904030806041b 63
    0x8000190549400070240c09460581481450710b460040000d0040313002c5001200c19250050084680060140740004680041903400d45115070005a42004003408012100455170a441c0050b06002c0f5440002e440c2c007a460300141501b00301091300d606000580c0e54155985a002480e1002e282e82c80124540303c2041e00c0170300001c01e182860210f071000b010300513144500603801021200f80e500b07404880041403c0c40140d030804048140801541948010710b11240b40142c004026054140041009407a210a04607001e52208c4091000242e80092001c06440d002d080c06c200b9a20842144200d144403079496140440c0d941d41c0d01c841142c05130000a04ae03c00344007240c00b041e600c9030801c0e03400e40300f004001001039004000030008080280c0c05051035181074480b0528205c03114084000d000d4440c0380e41030310ba0308001071110300c0b180006c0800c80e80300500c2c18060846080c81001401a03a0005c0000d42406091000503d107981c1e1b6500040701c601008108070100603445400401002000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 487854784 1250 487853534 487853543
    0x306060909070e1f05010806060306100e220f140c03042d03090b1c0b0406031b151d041e0c0908060f01030b06061606020d05150901032303130e04 64
    0x130700021882e5440382000a04c1a04050320f040d00c0c54541d00c007401044800d5901a00810003402844405aa10394000c020b0356000d201d1404041c800310a0341508480441c6440b49502d03252080c50040c00c803191741d05a5201c190000d215450750b0303444c1060b059840320b88a04030304034180502d8003403283c04800008c441c058000c1e6501d9a605443c1c0a80d5201c034440c1c0b03502800280813025840705440b8503500b242c921143d0251000c075002c2d6603540d40001146140b00e9002503040160010312082e4081040e01241e041c291609444108104048403010410407180c0d901440e00c0740030400c070441e030005010314141280c8204001c500c2414400410881060040708440c0c0540317008100c4801c1c2000140f41a6508410041c0303654441d1410040e140d48210b10548481c1c002204c200042601803010b010a8413032100c0c041202d18100032954091083c880c0e0340751140b54400018804a40e48041349403282d2010600c02084040e101c0a0301d1450048015002a080070341402180b4003d06009641c02103109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 487856034 1250 487854784 487854841
    0xe100b0a23030108190203100b030c090405071a09010e04050a0b1f0f180504090201200106060809010c0f05030618130302010b0d030807140c01021201050a080c0306060909070e 77
    0x180661020340d0b5030301c064080d600d0b07800104c00350b0008c00c03180e10480215074020102e8100411880102d8840003049500366003981001404100102d9020b2409888030385900c0010300d88501400044c00070580305503024003035581c61f000515a1001e50344056400da4005010082c815101006d001070403501e5102d0400168007105100701441c010158a03107540143d00f0305c401400e0900c414040200201d200585c100700900419032084055100072240c080448030000c01c1030b50500002800d40c1001400c0ba9100ea0315100014500c16441098101d001e00e403440d103070360303691607550003e41c516694000010f188403191040c41001501c0ca0084442c40748a60024041c1f200d01c0004c111160b0515500503021a12002c0000d0340d2900c0f40d8100a510000350b0607170384c10814541d1405007240c100400384814082c1d18030050140303282ca030509000038000c8400030400085080003203510340384060000c0703000d007500c1e4000c180c2504041c8451000751820810307010035031030140c0ca80700b8485007004003071000c92070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 487857284 1250 487856034 487856053
    0x120a1505010c0b0103021002031e030103170f0d0b1f030e0c040612031b06090f2102070b0d020912100501094817010e100b0a23030108 59
    0x4100d0b8240d41c0703401c0040b410700382e07203107800388202a034038034030408110f01003040f4101030030207040480c100b10400101c2d031584942c11031402c803044150581002c041c1203030078404054086140411034070403000d04040410389203800c00101e400c90814011520741d001480b5400421b4941c10b6001408101662080701c41100d600001d10044524902070901c03406c00440c1e040010a014459180980c0750344103542d030aa4102c0e4a83e10111020080c040398012001640e080512030380782c40021060410412121244450000181d82d80c119032142401d0011301080500c0c18038165030582e2051030015000003448105080040e4442d1942d007031000d441d510303240c0023152140b92846028032802c0c0d005500c0da20480c1c282000d46601340c1110b242a17410400b401701c0030684104064038084200d280e10380350700001214a0068403114142c010800082651003004000c10205150790220740315610801c2d03892441000c00c884c0c00050114038000e00c3c00c0c142165540300c01410043d81240c06120a0b606c03040c2c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 487858534 1250 487857284 487857287
    0x1110020a1805150a350601030b09150604050402030906060102061302031f090c0801020a0f0813230304061827051512060a050f010305030a03020708120a150501 70
    0x7890341c0103207500440c03d40381e14400c0c0c0c105840180074400b9941001c06a88080e00e2450b0440502d20084080d00e840ca0644600c000640707038581c42d0405004d0805003d84800b94010942c000e800a056820a4044010312120f581300c80040b2400f6203000f1708195501e14040c0703c22552104150744042c0144196000510b541c04481c0c101030400b50300401409500703481c01031512041c1c1d209140765951039640c1c41d010707002400b0842c5007802060200c00250b00c4440094024026050611902041c407a100f0104038004007480d1252805584c0280a0b00700a00c40c0062500840d41d481205c807410b200c002004200f1540000d8004140781c0c18051815103140c48001d80d206d000c440b20100c000a01e0b00c00b0707587e00488201c2d003210707a1000c0c08050b44c0d01801c2c5440c00058039400c40e0b100c0e01c5083d8100c0c40c1401030540c09400707140d0740328503446c4192000354035607528140e40e446030109500400d0340c0070601000708816030040380c1c9104a20440c240c5141020166107008000d0303142c1e03142c4203c050700300008555 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 487859784 1250 487858534 487858577
    0x714060c0705122b09030305010b040503060c0a020f06010801090c1d130201030f0606030518030304030518011211122a070c030b010314070605040b030402010f1110020a 74
    0x958080003800c0c680d076410b045a540d5400c100c10380f0044d0000100080708440c110000340e07640e00c42051011a154003d400e0103007c17104183c001c03ca0b00541040b09001984000890742c1c1c100e2000e048a5540e000d1001c800ca0074030032023000c00440e60156030300010302d01b441500b045107079500851044545594030088442a03440e521200c048542d224400a12a0391004a6841d62315006040100b0254038102141e07044580c03680044010a6544051000c41c2c1200c62842080c41181d100a600c0e50070319403000351450203171146030783c0c80401541511649900c0703002034600995560b6000d001c80c2d1041c04091400d600044a002c1c18816060009480802e0102c0e900780a01c0410a0106020095900700800c55101c240b01b51140b50390800000000b41184114500031070080840b40f12040382c0484150a000c007031340c03000c400c0200038003043c0401003140c0103da81003942424040d00c1d00f05200c0c015030760003500b001c50600d2801008040900001c207600204440c1d01a41d0321a05400443c0c0200f1510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 487861034 1250 487859784 487859797
    0x50a0605090d0908061e06010c0b280c081612060e07020d0804030e0f0a080d0908070929030a02040c050a02010b030f07060309140304030f0606080d0804110a05060714060c 75
    0x6c01e03400000e40c19a01c1d02c441210342c0100044c034151720703980c1d9a51100000354105445066008944541f2045080f164500710800c41c0c04a030002d100100140e00014070004000c4c042100c400743c481684165036000c3c4080c0044000c0341002440955500c0c82e03c1e02151500310741c2e42c009070103400f02030100b442c40303170074014425641a19440b07d460520004d0100f00d491012109400c41d52401c030116900f9010005074120000b90f0b070303449100f01d043c46000ea04000080d40425070440c2070601a00102d4008640000c12039117808401d52003c1d6000b00280c03902c0c1c02510003940192401140070010756114008004c00202e42e0001d21104d00041c00703160b6900d03103003001108c4641011005114091007604081c000601400301400300c3c00041c1c10f55030441c0c1c00765008803010200840441c0030000540a0b4030024541c4001514460708203100141c09da000c01000103010281d14a504071107540c0d0304803c50003622002e0b24030f6442d0525468442c030b80e00003044440100b4450040003e01d52082070045405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 487862284 1250 487861034 487861051
    0x4120302070501140910050307050705100507020d0804051c0c02060a0206010905011d010b030a02130806090d1e0f09090915200f0a0c02090a0213062a050a0605090d090806 75
    0x20f5800c6c402104031456000689150100001000f00c0004109e0400546580709404000042c5a0501100103032805040321054800d1104c0030040001060000c85c6841d80b107101c1e0442258004680d1030700b00c803900c0c1d920038025405000030540101440e80041d49506035980d0705010070090340c07075034892070000014440d54940c080403000140110148080030f5904030301c0b070340c5000d81840e144201d802c0c0c0e0f4542603042a40c1030340c021000c02034018010030084030200070b607003001201c40c15400b80c0c902040380c81c8811030041c081006004020b6500c01c070359100060040c03000070031850840e8600301020b07860b04446240843e041c0f241c0c00080f10704200b40c2801409500d0422440c20200170500680c5400441002040c003108409003000340e210240000d126010040f80165207180c01c030701d8644a0001074000b10100101c000186400c07456980c01c41d010341600035a51030908013a80703041031a000240100078001c42c2400d003400005000042c0300754403050305031a00055075446481140d80e48038104e03420700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 487863534 1250 487862284 487862299
    0x2060403051c0203091e060f041d0703020403030e091807060e01020f0c01090608040503091e0111010b0a06050c0106050415030312140f07021c0504050f01090b0708030c041203020705011409 83
    0x70142841c96600300280a005400d00f403c012123410001110341181d0300c040380c0314020300c022409481400140301e0b402141428210700709411a00c0007800240d0a108541c005ea071980c0105013074034810744d00368088840b1a0111006140c4601004250199203112540984907903190b4100c009400318036008100d00c180e5a203102c02e031815904540303103100508269514001000307008855110b0381804060340c8000450072034840580070004003645000f08103a0308592420400300300d150b50b031088c5130003162140d140541d224540014251300402d8668441580240b0308001401c000400d0414082128080d8a4000d140c6070004154010307901300b00d240c01c00b0300a2200015001060b518601174011800b44100c5015005641c041c144000c104103e02e07000ca98085000c12051401c00d16060000034203203000107074203182030700f40c04284c06140c400030055a00440000c04c0c3c520701c00103940c004d112455a0f080700144a0801030b4981045002d91800290403030b461205404580d401c48651050103481c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 487864784 1250 487863534 487863559
    0x3040503030c0a110613023105180a2108160507080d0518070815130f12051c051302040906060902071a010512071e0302060403051c020309 61
    0x86981e0b100003041e0013030051038100068001d004000041c4280c0a4000c1d101c0d614107103004000f1541a0200203540c48040c050503080192102c17542c40400a00c005404141602c4500d006070421401d007181040d80e02c00c2e10522020f01c1a1142240011007580c2107200c4144206401101c41140880ba10568800b590b0413980c0d01c14440e200601c01e49000d180442c0c02c24152550b000c0a40c0d100799003188072040161406641313280305200810040040c10000c3c040402209481070402000030540503c40034288801000e121840103001c1145500982c84a40c00f176180d8000307000707a0840c070311140d1340e6800b40040302400c1039180301b050f002d400f003200c01d114903180b25030801c00601416001111401e40314600060101000d0001d4441c25110382e10000c85809115078001041e4070580c8a140b0a0080300681c9000a102040c80b000b52406000c0641074100082c0f01442008442d500080d000200001e0020038010301140c10082d0065480182c2443d1001712412a030728000c0046507507000e454104c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 487866034 1250 487864784 487864801
    0xb0907020d0503040c0b270420222d0f0302040f1103150405100f030807060b1f0305070c031e0c02060a020102340f0320010b01090b0304050303 63
    0x6142d2252081c64140e400949400b504811b640000308254045138500b6028001c000351820061003d02c4103440401446d807081024211480400c2c152440346000040c0301c136030711420200500c0c2e03056155000e0118856691803029000d607104d804a550b000d420000038005c41c2c0c9441c000c07038202c408030381c8071419403411502000000c102517903880d00c2095840c611403448a0b205009544200c443c15084880421003a045c00305941009061031b8203014038403824000d00c2e26050201c4152138120360a00d0316095203140400042002040f0f055110044500048400314061907030080443c507503400b40101d07243c610041d99044140703d40140801e980100c0041c00c0d055608000a900e0305501c2e11812603004e580200320294800658000145d40000710341204458410b000e4480990901c500307034180c502100d44a10680e0940802015203104410407424148241c04401040c0c0d0107050203007410100b42001030003003070040b901c507003c0b410440d4002100b00304207081c2e0b0320450f0800007031407441d81e62100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 487867284 1250 487866034 487866037
    0x706020303070302160b0117070608060a090b0a03050102031003120c0f06540f0609020112050a1406061213080403051006080c06070f0b06121006090b0907020d05 71
    0x1c900f0021740d030300e09044e001c240101c3c9640d0080020321420300c0070303140c0d003a4004d051030800d410503001d20008005014468070303140b00c054100c3d01190390000d08481100c00050700b0310040e0784003525541c0041f090092486100954038120392058104045803010b40c40141c40d00b110102000d00601003110403400843c120b9048030644941001200411302c036403100180a03a41040005c0d03c6070402c2040c0c603240e42c120494200c00309000c0d02c3d41d94010740c0305d50b5101f620a000c8200014041c3e6114407a81046900510b07100c040300003554024415850401c003c1d000401d001308002041148490104255090200031a00504062243d4055956902124010116442e82c084451001c2080000003282051040e0080c1c4030302d180006c41e440e0710b0050324a19020145081e00d01c02c0c80e081103102d0010f25000c0c603200c1103c1d44540807030011307543d100c00a0302142c8081440c003c00e01071980a6681c80c001580100c2c1659a080c400b000343e104840184192080b0131115900982d10100c0540f400e64001d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 487868534 1250 487867284 487867297
    0x180302030d0f020405280e0118110f030c0d050721090c1d01170c0a090c090b2209020309032a03070f05060702120a030b06220303110706020303070302 66
    0xb101514003540c5001140500c241064220300c2c03001058009062520f100d2041e130000e110b660101200c95040101143c0d103200d40c1c0d4001e00c841c3d5500c0316106c06015400d410f80382d5505406101540f24a000d07031540e0760320f91089403580116441c040015400700c0c050343c00c4e00d440f4010840000d08614161031395200070981c161041d5001200c003040055407840c00c40d42c0c0100c83c4030074160180d01d54540394019401414a81132080181c00a907050026501d0f0481c2c892304540c1e99041c003007111102d0100a448004558010039030020300000c0300c07641000009030a440030b403407000c4803808650740c0325884012804190303117900d9a9003081080001400c511030000703041f1b0100b2942c01105044040c0100e00d035a012074001c41e40304000c40340e00d00620505009843d845080d038005010752a0813100c0303259061140c603e403174061540e54402e820243d02c0d181c06480c0c0c0302c1416204219030002d40e412007415910076100c00c0300000d0a856100c1a500790200700d100072101c0701d030021420342d126000254065045030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 487869784 1250 487868534 487868561
    0x60206060d020a0e070905120307020d200d0b0106180b09040b13050405071d1306050711012a140706051519090c0903110f0d05060c0d180302030d 64
    0x18000f03c4e03104490460b1380e008082c03503200c0785041071511081c40000910104403009036041403000f0405600d82182113551103a01480075003500c1061011650380c1100c80700c50320703000000a4500810030500d0700c0c009060700c241e61104650421074400000c20b8070464041d0000607481480100720a082c1900038a02c411001442e132124030841541003c200c600454040d610359000920403c03103074100011008400c03581038681b00342450042002005000003010003000e05684e000010b55841c0300b140712100180e00c83c2c00074055968a004803c006c169a80906200620200005a01180601119140c414007141c070f0b5800e00710f80e529038a00810004021801f0071500c01c08031441a41e038100441008058144100d00d034505150a50046500b902200800c1c000d5100b030904c0490f01040703416444000c111403020746001000c02203214003503403044c02131841c41810180081c1617001c40107404001c0c881c0004004640c803522645031040700800380035001d0b80081207000c040301c42e00d40219080d035001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 487871034 1250 487869784 487869799
    0x2040f0b0d060509011107050c150307211e06050f06030906191e0c030c030225051c020d0e18180f030c01020405130c140307020c0d0b04060f06060206060d02 69
    0x803107106c0d5180d40c2c070600007150950001d04040e0058074095076110b5130220000740da0385c210300c2c0880300030b0444410142513000c10785011801c2455100d02d5080480c00394100d40d0307814032a8421300503003c090715041c0105c9101b80400c401a88241c1005801d4070b2040c1c129100816060712a40c00ca201400301550f40a400507483c4c0154041850040d018504800e596500c00200c000b41400004c08a900601c0303060f00b014010085203100406000840e0803100341c0c001d10b602c0e0b407141807074018076000d048403910b15080100510040840d03000715504448042c13786500010000c5101007205107410001900300030848130700461100c0c0c411006114003158070404466003e11001401c1c3d155410484001880d070703400080512140c18034400f000e95a004901c014400c1c602440405890072003000004100c1800120001c2d16980c405c020001a00e10050300d12400150541000000703c001100c1c140e480398100300c8070404400345031040804481c510f60103016251520b00810042c56203a6074243d92000c0f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 487872284 1250 487871034 487871051
    0xf03021203040b0405010506150d020f0d0e0309030f011401061d031203060f010c150507120603260703021209040e06010b030103140f061b0d05040f02040f0b0d06050901 74
    0x303640d030040d801a030143d28003030741c6840c2c2880c000b03003034410091900340100405118030007062014810398100740b91544000d42c4034014050142840d000d44a0440c000780d003081d4120113184404001000c0a04054040c0c48861240d0a2800d00b65501010300340080e20f486030040181c18801e4a5451b0010b900c12013440000002c80002071030055a00044c2841c040300009000d02494480c1c003c1e8900328003030034418090078060701c1d4614490160f004800034151118000340d1168031038600501d032040007070400c000e05c0b9261b09101c4c0c411000165106600c0414060048183c4000001c1e1080c503075040d4010a02a0003018003c60703282c00050740c05070000e40b40d0042c0030700d40c14280b01c02c0d406400c501c0c038990f484e0b40c91410f2a00d40c03006204030103030300e60b001034540c00c020a030082081c641c0031080c98100f09422114106254403446449840b0841e1450902840100074030340c0d40e420410390007220140a00d6003020041012070700c019030460390081210905000160003600885c0d4445414000000c0244 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 487873534 1250 487872284 487872313
    0x90f0a080a030305070201050709080a12020705031603050d090e0403210207030806100f090e19090b06090f01080705010e06040806090616030c05040308070507230306090a030c0f0302 80
    0x1841d030003100031039100c804002c0440d9091007001e038030240610b064903a007032074040050303201c1005090207080741d00c51510f284400d6000f0818080105806022692900c8180c0050068454180012551402110b664104c12407141541000b5a121140c6520050b1540e80d0306840810380b4404881c20f90f9005071242002c2c1c80703984044c14210b0f010782ca07a01018a480c41c10800ba02c42118540000c2c0041d0701d2040108a86c4103615a0545441100310f9100ba00c468106581001143c001e1030101030511580700c081000c07030314216000f10410f558200c0c40381c882158506141c0300034055820790f07a1211504002c550b11509642000c103802510241c54191201c1280d410072030121404000c0e0341c0494184800b65000701400b040308a000d14003080018103020004025100310b20000d001c074900490540f05004050240780020000c01c0b1080b10405007040d228042e039040000028480e00a00c070015103054004100b600e0352661555460a942c1301c0d80c0c4d5120404e080141007a070843c440d55207a1345000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 487874784 1250 487873534 487873543
    0x1204020a030b090c0414040b0601270306020d050a0b0603161e020a050d08090606060d02120a0507020c0a14010c0519030503063d03020f0409020408060f010308090f0a08 74
    0x20341c4007030044d10118105a003032000b81d0b40090038041c181c1092100300030114540d0301c91203820490034a02800c9144026548001c20381c002046000c2c10300c0014000001c112a50780104032318600880300b0b000340e5550113120b80840c3e13050048540c0040b81000000c08071080c182c0960500001401c0158048803942c0141e0829007908804001607800b05c01e529091001c00c200c026140c11880c40d00c43e03080d14282c403010b5120000a4900c90080c0030214910003800030740e40541e510038480522041140c40c01c8048000905401d071741e440d0141c054112200030b5070504854078002da5100d02080c0381c0d0b40c0600070044820090728035056400740941c905122076400d484212000303a6000b5540c0c1601d81c00c148042020300602d500b840c0d480d030b02c480c09070240850404c511410076028046624806036801c1d48069019100d800700075509580d00080201d492002c0e5030142043c1d4604104075a42d81d9140e0741841d9440c2e60a0001a207003400600c400c518902d412201d11031014806003454820131b640d00b0101d40380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 487876034 1250 487874784 487874791
    0xb0121060e060a11040f180b06030702060f0a230c04050d110117010501081611010e0a0b09030408101104030b01180f0c05071104060f0b0a0906020109081204020a030b 73
    0x8680086080c0701c3c1c01070442c0999008905054002460149001c5403a07446042600c140120a4405400500342641c1d075481b6992009024218595a1a090340000d4481c08111080505121060040303100700d0b8042c4039110044821420001010302c1ca0754031050202c5005180e01c810103000c210200391a00c9070701001e0f103203070301c29844070310010048000980300100d103900401c031001ea003000400c01680e108502a801c0074107018004418144114100d840400e428440111076080c40c080e40c910400c00140104441d001d054442480c0e100c2c0318400d51648504d22420b541540007e10142c0d20f99101e5018000782064040c000d454581ea070b541d940300e0400309900250200d112103210071941702d05c41c0034011a038190440c0400c462205800003410a0103882d070040c0200740b9403020b00b4a5622680d003c2d0001d881038114882110341c1c0d1b10381541d040c2d800b000705100090495440041c919005008510165501940302402c01b55003420180301c00e08010000c0c0d91054082e040000480c1190745032600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 487877284 1250 487876034 487876061
    0x160509130606030510200301090b0103064b0e190f0501050319020603010603090807080712230702060327071403061902070f08130905060105070b012106 67
    0x210190348200030112801c4c014010701e500d589550404101b4052000c45e0f045d10b034803002c0052141c03007080049000b01910b8000f45000e225a0f0031060041c1d01c0c0182c1c098404445030480c48941c0341e08003029a44a481c10700619580c10041004c0c00180c1e80d600150385c3c803c103103254540413800308819280c2511000b40c100d4124658500041c050344c20305112940c0740030803c810040e494900350703001c81c8462105104110070196240c030702ca403c00107682e0840d200ea6030080d00c5170b6140c0355582801e400b101003502910000c18120040c103000c6000c01500d485044401c18001403e060a603002c0c0041a030000b0710505d03410210b000e900158031f0720b2200a40799000604002c003031031802c0007640401d50ba0b40752020362107544194100514408030220901b00038806510160315002589480e40c1c044040c1c51004100810201f02640c0303034005410403100310303003001360184450745070f500040d50980f01d0018082d015414030001444004115004a034031fa80344101d905201211544500041790b650510390003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 487878534 1250 487877284 487877293
    0xc0a020d0222061508100501030c0c050a200901080607080c2a070609121e08030a0f05060d050d080612100f1d030d051f080a02040e1605091306060305 66
    0x1001304940004420807414600c40070300307005204412946051141c2410941c9854032900498801c403068902207920104907a807000e9a03107811440e2070782440c10100050a110035002040c036084101c14100e60442014000c580c980c02e00803038003441c0040030000d0804041003010011148041141c1901c081018140e000001c0914480d040c03840030b074000c104000310b032481400b481c3e07400340f14040c81981c4a0101e0001d402c1c41d1801d0089171040100281514001004202080082d40c00981415000348401c001c00d54514040200e10703920010f014086038030007000311051764001c0c4240b60f0800da000385903848614840c15080e260581050710f4600c41600c0b075100f0103c021141c000c002220032002408840440c140701344694900405ca0002c100b552510003082010145000000ea40704052030784d00b044e0380e03d03400c550f80d840710091802c9005601d005004201c044004c15014a001c00c044c2d4222100b51820b4100130548001801050451440e5101c003c0041c41d94851180207520480240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 487879784 1250 487878534 487878539
    0xc24020c010c0810050118080105180706090b0a050d0e030408010b0901150e0904060f1d0f06010501080109110f0c0a050d0503070210050a150b130b0c0a020d022206 72
    0x36425500c4801c100014002104140402d0310580c0c070b603890980b4028a04111180d0354840640d010070207503031052600c1d51800d414405c885d4900c00060700d4200d1210104c4007607581ea410100c03018403151041061070401404102030140c4180b0061960226044021460b031a854030418103643c007940c410300242c0e41d500c00c80f0f1000d090800361503005000d14094014491141040030b080303135600c04030143c800c015500010741040419400711307413a50010041002407107800d03800c1c00100c044940d6840c155118124400c9010341300010000c1c1a150107940707100d843e910700703080400030b05806180101840c405001010145820b40081d00e10004404010301c242902800c00740d0429a1b089032010402100300104500e1680009003851448403201c40040c0366603030304102c0c100503c05c0f4094480760b0aa01e0200048020745e45014005203481c2409181102c0d991343d004805a2244c5001d4403071b69001410242c000d403910100580c4c4580c005042d00003000d5046945a5a40015030718007490395644120a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 487881034 1250 487879784 487879807
    0x1603020c040f02092806030e0f1507090e13030e030304032907090812070c08100c0815010e040e01090219030b06040216240e03120604060501050a0c2402 67
    0xc860075003103c002801c2d480341c0c406119004085d0f0038083d29050544a00102c038a1980401040c00d29100300c1c0140c403c42e0101030000c84901e00b0a85124001a121003804600c0d030165520083c0208022a17100e06811403698050320840c0c440152241c0c580800e0000001041890b91130045540c16a180d4010b903400c49440324044a5000d03010a08221b84140103020300a00014120b1003019140c2089803100e040d481c03c4e00403840a40c01c04071040c010100140120b400d541c0108071641800e4851201907581c009020055601c1204120b000a551884001450070b140d400044000303030040c004948041b15030049011030f0032040802a41811002c0704200740700f4044041601b1940886d401c0d80391944105000030a080c2d402b03400b414255645c0025410411100610011400c882c401400241d614a03090782d1a030704114002590000d02000107038040c61302d440340c3c0041c3c40c0141c41d01e80c1403941e80c943c03c9540300805070044a4480c03643d0384083d50005051003000011200117009039541e460b0b200c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 487882284 1250 487881034 487881049
    0x606090207080708070609020a060c06060614090909100504030906020d08010308180d060c0302120f010602031e0403150506040f0509120705160303030e12040b1603020c040f0209 78
    0x112101103441404884001640201210f401c3da40040e44561a00f0590621030300070601100025440014007400081140d00300354049901d501a000822065584020503101c610304401448a0b40c0810442400c1503d481140640c0142e1440d08071029030303410440d101d0440d88183c1742a004074a1006003004203d6040007103030544080361030028515451540d444040f4042c095039007584200306012400541c90b01ca0b98120036a40049040c04804203c55000c0d000b580413074044c007501c0c0414800219440078002e01c0c40d040700c01980c010b51601d8111a01084c50710401c0c801200442c4040200201040071340f0714015040c00101d60014076400c00104000807600a19a20880d1505000c1000308542c808108452103045001e80f056882042d881e00600307140c428090b07006800b02041d0040705050740b69200d01200302002c0e044480355142c82039120f03064080e52040108861040103000200b0004a20a05c0c0343d9210b40110759070398407410005000d030f983c0410051495940414460003d03d4601c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 487883534 1250 487882284 487882289
    0x40302131404060c05130308030a060504090b0f0405071d1008011b0e01030908071103070509090a02041812030b03010b0f011b170703050d0b0625030311040b03040606 73
    0x350200702907a0984210100e0060040003d031440360b6481d407104907140948102c1c0c4900a000c0c0c910209103841e841c11410702d400640b9590b040a203088000f0845040a101b44641c09030000c80014903983c4241c034100d41c8000041007100c946c0115040050721940c0c000c005110a80300a0341e014a6140c6002c04515401250307200310b5840c0e05100304d441200c0003c1d098151250280e10780940e12510100060b0003401c001c510050050000290f0182400b0138035032030410280c0c085040e1a5510b41e94410000e04131002d03034442c0d4072a00203600410052501e0340c0038240d41120318801d41d80f001d4141d12100c906000c01c100742d4010903107a416800051400f80708015074880100c03000b90400e0364080008140000c500481e0b503810751600084003d001d90b800d91074032408100038205654070b005140080c60b5802000d00c40e18020f04069801141b4a802c2069900403a9140d05408140e000a00080d01c01110342c00d06405040e500d41c3d5060041e50428014400b5000c2d101506079203040911b0420101c0b00c00c1d0307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 487884784 1250 487883534 487883569
    0x2011205010b0a08040503040b0a1701050904150906110c03030603070b1c02090625060501120f1212180b0a0c0e0111030f03151201110a030c05040911040302 69
    0x403005100c295840e4094902d80451440d20000c00d603034501d402c80c031303622441e00b00d4428660040b84862003107612030780010059000300511030711039903201c1c10300c046041d094900031700d603148220009014226541c811000580100804540e0980030040950650704c407900c1c042882d000003041082070300313041151200038103071820010310304841e100401e1701d004c660100e81d640064000481c5441a03443e0b01c259000102904041691504400140e4640131900e000c01c8400790b04000c00054401203040c8042d1550340c1100920350280016500d06d039034200c4020107607060040c0e01c54402d4a0714280c0c0728808120581082c40c5104030034904224803010300007040f091480b070401c81a80c40c1d42d42c0c407041a1060000a003031842c0c030b400828910501f140501480d041d2021404401c000081e1041041400f1a0380d0507207640e00c100842101490a031810001c20511240040103403200ca02e2080d030000012606520700349013083d4032020804191542024244c0c07403008003013428000d40c58440c1001036041980c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 487886034 1250 487884784 487884791
    0x60c110a0b030601050d060e010801150902070f1e06050907090609020c0c01030507020f060403032702030a0209060409050601091b02060f010612060819050d030c0914121504020112 79
    0x81c90080d8050303100c01003440f410030002007507040d0000030a8001d400580700c1e030011210036603124841a4020041c03001c0c1e60b00c0c0559185400180d1400030700c01c9031410b6400c003880781800d1015448408000c07a1075186500410303182c111020200380b1070322516002e401010040c240061405c00c80c14149e0b41c9507007007041e03030a2040011140441e00041c03221140d9500b03084c04a042d0303841c0761041c2d041011074400c4115501600040004141c0c0c91fa2025914981c6107103248219100c0d010000810481c80d40700035015032001455001516006440740c0e0312440080c0040703a01000da58403642007120a0b40024180b0303880343e40e501c2d00000e0070381d82c0c541d00707a030301d880106514503213020042071900042c49160140034408141c481150748030341081b40030300000c00c200c840b102c0400c0080150390003080019a030703d000d802099101c0d00d201c0c1c0a501c181002d166954402141481166000310400101c0c1c203501a207066010007909006211110a0300250107044507140b400d40000340c040035002068100c02c0b4034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 487887284 1250 487886034 487886039
    0x160f030315052b0512121b1b030f0403030302040e01140a230925020601060f12200714030a0822050f07081b0307050114090604060c110a 60
    0x40f82da82101140d042a5507184103840030369081200c00f450014094814090800e8503042684064020800c42800c0145c0280d5540d5402e03207031810a07650f0b0050406c00350104014400c1203410b552440c901304000701600d1500540c02100300c003d0303000d0750089010179000318041011107121094140107158081e8103216802c500800070348040c01c0da004d40d149591005410f002c52030345d04c0e00d005141d6400036201e51b04074202041344c0c031210700d040442c07186c06640c600c590520a80c40850414121146501c4e126040310b2501015a41680a80e4900130029076234054102404400844003401740e01c0310002e503a80720414100800c0c0e0307914084d6540065841003054100c141d0340401019442200d0915420040c4459032220109800d000809062445200d0098000c0d202c0803403820100c5001c80100c4d142d000700c0075080d00c101850301c4080c0d945074010340f00801c5554001c0b0300c081c600507512641c01d807400030320b0000103816402540000300003c115030300f080300300010106404817424048920b003920301d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 487888534 1250 487887284 487887289
    0x15070c030806061e1602040906020319090c121103060103060e1608061b1b01050603100912050901140a03090309080307110f12010501080105090607140f030408160f03031505 76
    0xf88a08050010031a0009110440451900d000000d1540c01082800108e485060a4000e0740041d61400c0031f55580c0040025080d040e44914100590700c000c10b05500b5181090181c80ca8440f40410303548031184280c800050ba600348807a40c00785200b44030020b03108040e190394600d006d01600302d101c904a40d0780c8040c0b0408100007000d03940300312501898605843e4a206012290003218495207a640400d40883c0c0b45817010b40040e803241c0c0046e0308807040311951070a41d1094a603844c60180680d4160704240c00e61a100b64010a890a01814100c7d0320000d440c001617000c1e44406030b524002582d422840f400c066001c9101c0004091107002182450b2040e1600280c800980700c41500c00d15110303040340c8598441442c030070b140051241c0200b06961b500c003c1c250190400301c2d00c241450042500203035036540181c450203804000410740c2e03410104240b0030f0001c0742d44013600564040c1000d1000040c503c1010a00c1ca4000340b181c1241304101c040340ca4081c003510a42004000000103520b018865134 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 487889784 1250 487888534 487888567
    0x20c0c030708071503020d0e15060402090d0204050a090203030711090a050106020615041d06010f1703070b070e09131a010510030b1305070c051002040e040f0515070c03080606 77
    0x40c0c131800c4007210680141201940240305104c2d01c103102c6801e05802c0e008041e40403070a0665240361850444550761050b082100304d11803d40c402d5884501c00c0350400160800c0d0f808503511643c9c81030700092418043e000645580c02807041103803041c80c0e00b8003d0f8080e00b000c040c0150031800c6240140419418100040e4403820020310004420002c0094190700e40c0c7e841c0c1246000c00b00071030b445c034850302c00040c107140c0354202400340380807090708808005410706041904035100c10100c40a541003845980d40c5080c0c5200180460040082c640f000c04407e5642d014018000d005200c1041c4515200d4039001e20780310b08120405114801340340040151b0f03152110055152502e600e00001c10707000a00c001290348212142c2c880050381703803808000c2c19980090051140700d01480403240000f10415500701030703100c1c90040a03070100006001c600000e441c20500c00141f4403601c1550020300a0085e024284a02211080009041041840c050642007080303150402401e9400501e414820b0b01215000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 487891034 1250 487889784 487889789
    0x816051f050c0d1a1504050f0609030a02060f19052101080c0d0201030e0d0201150b0304031205090a050a11120601140105070c150f171506030703021c020c0c03070807 73
    0x3c549491905010110148401d0b85994004000d00d2020b410003181104076040b900030140030b08914081c0044528000042d9440c111006000300303001c110590038400140c10140180107420010f0000500104c556500f8800d440b000380d50300d503215085003040300080ca014642510b1424445001480700c00c401054010f070b0032005881540700310045c0e10049005184412503a01c0e94051407200c11106a41900812a210b0101d081c1e6460141c442d01c00700c0c5544010b45008010a100302e0600c0c0403070815411a503844101e03003080d200f0f0483d080d1034090804800000440da00d281d0f0401c100d00c5481c06814581500300c100c00200840c1d03040400c01440b190030095035505109004c506c0b2400c0100c016500b1001c0c041c0c00c51850048034021501600c0420300c010000d022803680300b0407540200c2034448176032150900c544004024000071043c018203510140001c4200354081040303810400b4841da492030f00c00b002400060303036541010b02e014202400c3d001107a1003034003c003000300f042a000142c00000e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 487892284 1250 487891034 487891057
    0x204080c041a09010e0903090901120b06060307091a04090f06090501170a0809060c0f06010602011a1c022d03060f010b030a050a090c0803030906010b040f0608040816051f050c 77
    0x811b0329091401440d50082450031603101c03c3c0c4000204000c5141d00b130300d0404c24070a1003910459265541005043d002c100c1e0860000f44040768200b18050480040794152090000b80d1440d09444040b203400380d076072855412a0140c0c64100800008049100b25801086070303800e01c180381c015200c0f00316112000018040c00c6c020021400e50100d645001c111900340301400202c80180306080c1456450b0a0240708110155103000401868020ba91495400781d0340d000306200055000309004d07075150843c4600a90b04010310705942c0c5105140a20940003141881c0114800702030078400b01494200020401030200e081000104200880041a260020b1029002152580d101e0300808000e000700c4e07001805502508000180138240031006500a10f015019180c0c142e0700c5070f0343c25125108030310903006058013110b400c0100c0c4c0d02c12145150042e101c0c03a5061b203400142c0010240700c0c0406079069400d40c010307183c10580c0d03d0388208002242482c1500620513860140107511503409991035440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 487893534 1250 487892284 487892309
    0xf06020705092220100f05031e070203040f080f0309060313020a030f03031407081801061502030a020607140d0c050d0e07060f14030414030d0204080c041a0901 70
    0x2050380421040340e0f45250b074102480b0ba040d40036800e03c4002d8640e9407940108410070001209240c2c10445a01100c00c0001d8903158a43c40200e04c04442951004122071000600c2c10000000030f0546070320980191201d0f8015522181862143c05900070700d0f82c04417810f9445594640d40340e11010090340c0c0440310480740507443e55208100d4038089075500c06c000b544850000408420052000c444503e083d000b0f9800704814009401400c100800c2500e0741070115006c9400640c07080c00354030441c42c00c1210300e400841c080e80e5640104c40b044802e841c002025030804154100c10356810020a5801030349894444d001d40085800e8201d10301c0f0702d80b0f0b80391803580c07250f8000660600840445003100f1800800b08200c03000f22030583e841c1c0d00345010b03030000201550f010f0030009214826200d0300c0000c074205686940c46560f07a055070461007100000391030009200c042844012407000e40003c1040102801d104000841000200ca1290704185552a01e90303039000041d841d00354816054514901c1c1c2c54 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 487894784 1250 487893534 487893541
    0xc110910030c08030714010218090c09120304030209070219081b0a03110f0a1509020a03020312041d01030f02040b01090f090605040c081e0402010c081b070f0602070509 74
    0x3482090300c41d0030203040d91900030400a40c0040000007451654010003584041301e507410003440c00c5c0d1203914100d00c076980c01c82e03102a42e58503110310200d400001c0c03418041c0c580803400001c40c0c12180800c213801116000841e0030006d504050000304d5000004e48007500000b03105160780702e000801e55102a0900c080071032104032450001c2c00340d60210942004503090070041e4500240b6020b6541b1581410303010365220700d02000700015151580e1513104c00800c03c011092100c01008010140302030340c1c4111280c0d00080503840074000c00c1d003040300c25040a0f950740e040c41c084101c0c81f48580c0c500ca02d1064103c00400200f244801c10f00900c0d541258085a4248160300407111080700360010803103240d40c400001080340880d88102d0444009550500100c00c00c0c00301900e11003005c4440c0d41c0e455a540107a60005016015000c0d845441418a61042c4c412901d80300a66081100020b00d00e480c0d81401c11240041080500b006010126003034507040c1c104a4000d45600451090b2800f541810021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 487896034 1250 487894784 487894801
    0x70209040f03051312060e01061a0705010612140708150112031e030902180601090b1308060a05430e10050717160f030c0210030b100c1109 61
    0x40741c50b8140340186044c6001c0c0c5174252540c1d0b07907841c0001100d042d031402c03402101020041c055941192069a60049240014401d0719101c0d400084100d0742c0303568030750012601405009807020041e00030644c24500c86144120300d890603150740c00903500303940030302540f41b640d0b451300300e2642c1035071041585640d11150a00e029111000c9150400c0c207481c001c501c6099071590b05034080d400050086501e4122040003100c1640503144c1664030a000602c0d102c001c0c400140c0010042a43c41920715200b0301455680e0304850801074165001c94885880d5020702000a80000e0b4154140c806032840310241c2c2403994100d070514030095048410b203910480010091070151240e10290b2501402e00b40b01060b00b403100510380e9203d140d0449900103180c49015000f83c034581681c0780c803d20b000e100c441036140f030b4030b80c1050f0140c030420031001c200c2d09298403030044c4c58105440001d01c0c11600e000c150700b4002401c201c1d0040c1c0d884180010400403498850200304d506404040444054401042a4446450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487897284 1250 487896034 487896037
    0x5010b0304020f0f150d0c09050303090d0c0b030a020d0c020303090607113f071106030a241511061b09100216050111060610051c0b1005070209040f0305 67
    0x960f40001406412559250494002c06411b50442000c0100e0b00314160195100c04030350003400d8040e0300902070303165a810081c00180466001d2005e8090099483c56158000d52040782d0454609401058210303021038680148400034115001a5040d85803503c8800d640d210f0050511080081c0c0903a407071b00d00c90f000c1c03045070071a10302c03400c00c2c2501903a00d101c4e80122444060610210010b0741d41200400d608c00c0040e15030b51a80401100001d00c814010854180c1000d060140340d80e1340e84200d500c482d42110080710000340d54211400c0a913180007015108000c455456509000301d0401070080d0300404560f0b1640540250506510304000900301803090107060012600102c045010b6111130f5000640001b01003c0c40122840040d00c1e40300458040c1d1200300b402083d9400a0003055292500407110307840d9400a242490034511000e92003100326005102d400304030f41d0b69039100d20300c1d4144002c20f4041c0c1415400c0c050b01c0d0084a0380412003001c8010030140030b10314100c1880042611400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 487898534 1250 487897284 487897309
    0x313060e030703021c030903020a0f03200a02040b150715060911030f0601090501120506130606050a0909111b010b030a1119030c14030a050102120f0a05010b0304020f 73
    0x10440303407942c40d1480c2c003030354604a079000c9030501c0d994001d41d042a60303c03e01508031519890f9010700a68075886c0da07141b80c041a1140b0803400c0c08000b50382012101c54404840d200a4440317001883e08034401e0050100301c80b51174101a02401140600710b4052085000b254102e50707020703d00c40f00c058441e03026032008181c150460759509040025101e0403100d0300001e58024880842c0d00704480d01c03100010b40381100746210305400304200707200c041180c158951046910200150010444c4034211044000b01c40c1e45070002310100f03801044120000e94056000409001c2d910020880110114140f4000e4000e03400360345036090000070500c100240139004039040354400b0b0102c9800320035610f00a00c4442089459501500002d0486d682c80f044090442003160781041c80d2800450401c11510808480c10f40103c1d054402e0703182801c0000c0c030901c0284141150080c1c2138009051180c1c46a00420005d00244011820300300188a084140070850b60000c3d0f0481d00700400802d010302060b120088103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487899784 1250 487898534 487898561
    0xf1503190302030f160b07030e1f0915020c010e010b0307140102240f1302090f0702030c1506040513240b06120708160e060309031210210206031306 65
    0x440c03081786107030140c0c080b021180d1103207035002d0640d51400300c1201141c1c44804010342c0b83d070004142011314001c0b03100151a03402596000700e4140880e48411703485010408800c102c032503000170014024082840303a06011019030000344200d085403030000f0b550751214020700c400c40404503a2042c144c1e00800490329628240000d164550303044034180309800340b040f100c1a00c0c810603c0300140100a090302586201e5500515848098441c0c41c0481070015000b0a5401544400c11040c400d11804000002e014091601c1000f02403801005000075a0005403003040c58080382c0c03450b5000036140354002442210200300d030184180d01c803541d20001d0002e000707585810140019036580d04086400d030992089510751103004040c0c507540314000d5a561030403a00c5002861082d40300405141000003140c0100c1064100ca0400100b402040b644443c00e580d6040040c1c0c0a0401700f0010380704070710150f260b040708403041e070320070f03a254010801500c0700411081c0c00044403401201003000c580c1c4042c00c000d091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487901034 1250 487899784 487899787
    0x5090106020f0d030b0916020709090f020307332a060b0108010503100e0a06020c06150a031703091f0603020411030115350f1503190302030f 62
    0x1210000794541103102d00c0b480082c01840742d02036446009008030b003050000a0018400d9513210000501462000134000046008291000a141c1e840340115102203000380ca00214071119031041503c3d00c6103943c480100300041c1118524251106030750650261911684080c141000c0c1c3c0e821540150380c40e8a11180d01000304940c00e00d50f10500050010900c9a841000301c0030541c0b0041d1445071092040310390685c4003e03d40d144040c9540c01071a9060a03001c1140e4070507116507500c000341d03000340d03080c001c00c0d40c416800c114000d2a15440501540d4060301c1c9121040e0443d1682068803104008480b2448400004034000a80420100798008032604060603103000c0300c40514050030580c03000f0707441541081601c10f13070400007108490413925880b144402c103095540044d20700702c010400d01c1d0380402184c6401c0e0b00c5d030074012002c61401c0810b06a41c04107841e1003032030f01c1a2907002410021480c20300c4080c45000d5140090800034651907900740001910003440d0032440c0d8810840040201d010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487902284 1250 487901034 487901039
    0x6071703010e070e0f0a0504021804020f091305070509010e1903050d030c02010204080601030314040b0703080612030a231323010215040204020313060e0a1b060c1209050901 76
    0x4507080e0038010f040382d03518411101600ca003045917200c10780c022107a1090300000100003500d032070382c01060f40940182c00b881c508000040010100d8204140758a02c5a00004040b001072401d01d004061003241074008100340e00340b515000342903005848541e41400599801c500c240e07a00c12600c12003001249418640007a00c80c41c2050f280d1641e5a0b80e00c002c6810701e14003001d0240113000391010f4400c2c1c00004c140d0360f840e5407011121905a0048085600720030040030039007140d410000c2a0b094041d4450524038141001445010a1400c08111445d002400f15030020b80d803100e100904042c3d400110104a06840005140d0384246807041a50b05000d0741c002400c003003103240401122948041e5006000f803244016a142c0340804511382c0482d0388100010014034080c6c0c00703160810301100021720003c4032543c56004689402c50050b12543c000748900080122001c0f40c0d042c088103503060028642e1a00c20050003d44181e60010010030008030307044d402d94820f02c1c0d00d00040900a05200340e95a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487903534 1250 487902284 487902299
    0x21207021c0c0f120c02061b060a090203030a0e01020c030f010e0d0311030708070c0c0608060a0801180b0901090507031406010b0f090d1703070327030e0607170301 72
    0xc00c0c556105000310940c000d10a0690041c040901d4154002500d0801d400032513942007107100f181c0c0c00c12400e0102c900c1095000d61a130030094949080fa54101d07072925091081c4541c43c00c0070003001244082d0901f0003082c0103840c0802500e44290f00341c18501c040c40c1c045c3c40142d0400e14107101c0140c16218141402114000c15003105000c107000707000b82c2d101c01d17003007060450548107124003180000100308080340d4280e115111184d840030441c070308150301e4141c03507480000103a06c640c007080006444c0b505000041c0390042880004011440080000c041c2c03145030341c40d035114080005000e030f015400c00a032040c0c1082d00410300c01c40c0e108082d00ca070b6548034078061f0396000005034041124810000040384a60340002292040f400b81208036040440c000c08010180c4510001110b054041c44a212005d142c0840550301a0420740c1380840d00c406003006200c1017000c1100f500c0b00321110f030824800402d80020f80007000e4401980c0c000d60b114400d042890f81c50202d0f8088100c0040004000100d06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487904784 1250 487903534 487903543
    0x10f030e010b0424050609240c0105010605450112090803090d181202040e0d030c1209080d0e030c0703080a030b030604020102100c030605030609010204030606150503040f0602120702 80
    0x61302025180c0140c0c641040c40514065205820340144484080150800e0b494001101400320b18544921f003020100006c1d00351442030340003134085007010401d0798035105094100041144201d0000f0444046051134406006013901100c82e021265010000c00e139106000f41c40d0a030b860000c040c0702d03914540c9429545c43d4011907a00025000b60078452201c140700c0c1c04000404440c04e089154007904104006101c2e03d0040b01c1240d000c0c0d591401400007181c01d201c03009140000b038400059015185a0240000c0303190b00341e20007074518088401e00001c9482c41a00c0d55241401c20000d4081d005000591841c40796007100311080c1300d04c0000208101d0742d4402031036001d205603400d00c10341c800c6400303040e034034102a500213025030400c1c0300c6245151035691280040c010f45150110700d8554400110303040003810380b4002c056940001d401c0c01840f085005800050031441d4102c0c420b46404080180300e40000b07000246200600b24000d414000c1340e806440c9905220360ba24000c9082c40740300650768 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487906034 1250 487904784 487904831
    0x30602031815010509101818120206070801050a06090b0306121f140c09040e031621140a0c050102040302090f040606080304050f04050a2403050f0606010f030e010b04 73
    0xc05d80c04000a00c07421b542800001182c0074034001081507254520804040d1502d03040070464120b040786038102207404045c140254810580141425051a0307900a0080c00142c0281e405403940b00410056039a0000340c480448001609480e00c1c0e44480340020311a4070860350400341032052072140c014010051480900d0110150003c0000d001c0203802c604070120121048a25510706101041880c106a04642d0305c0d4a400810380346040f0004e00d81c00e0040c90518429140320130900f00a42841c05001d51624140310345040000148004050781c4d81d03188181420201041445014001000025010350700911340c011b00000c071a181034030400e91044021501a1502801d000700043c0b981d6011007150155840030b00455030b007055180500000d0017000d8200c905040c0d68000c0120b030441c00c940c00c84402d40d054201c1c01501403440c140a403500952194083c5d0940003101031050710303070b08418103855807481403c01250b042412005c50740100104a001c2e60800d00f003007000580040c1a1200c40c5c0c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487907284 1250 487906034 487906039
    0x30406030b0307060516030c14150a2c2a01020c042f04030204060308070b01090525110a15060b090a0302040e0703080d02042d0306020318150105 64
    0x100250a0806035a20414444c00004c5141041140d60b1202c19410600c902e07802410080c400c103a0503034910085074801801000c1603041002c01443d4002181c0d8295003180c03801c401804441100744141007209a0082c80b5260101d2420750106161010700400078651420541c5c980161401c1243c640340c0200d10f003906006024808906c5680d107028450507810401070420084985080a44003400c882142243c3c490136000703010000040c1e03100d004540266209586007500c0b070340c8601d03000f2403088040e0060101c1c241403008100501c0c00c4282e070151102c6c034003544414109001641a01c2c4908258450103850184140c890103000d4600d81510741d503001c0b03c0b4100a004d5640c01441000c2c040d05044580c020301c111005c0000d403030180c01c8000c8484885041c1c0d04026680c2e41c880e035441d800403044008a07600800e00f00451206a41d00607034540689908460100702c90401340e450f11440e0100034281540400890200608585000b0394040103e04540c15000700b00642026040c00b44992803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487908534 1250 487907284 487907291
    0x11517010e06090708070909050702011d07140d0510020f0d1a0306090c090c07020109050a0e06090f040b131103030c06040c08010b060d0216081c0c0206071b0203100e03040603 77
    0x7a001ca1190505d02c0c401d8040741e4071081e429040a01003c041c02000e0141406c540d00c03004400401800c03407091824035024000200019445e0044a0780c841038140c4010744508207081e04180454804140c81c410b01544400040c0c2e2540c40140c11001805080d600a00d02c1c2e04e09805004018020810150701c06801c408680555560b0061203503520710101c00107402c0600c0307101107041120071401030200a0300c1418820515611040030411031034840d44949008051001448039509045802c01d4003c13079035444103003c51030691150710034400c000c2c00c0c0c04805203007c10024103100108180e1035500034001c1c01e407507865020a041c656102410385040d64080e0048400242e981414810804101b101514484c10030074004041402504508020103440c12003280110000e4101c00060001c15000c80701e038100340c100c0b40303041d1044848065001b02950700c00b20a00038941d41107461010180c8480b0840d850301c98041c80802d040c000d40d00056060b40381028142e428038940400039200b030b2070700c669040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487909784 1250 487908534 487908541
    0x60712110f06071d060c0d23090d030813050717010e0c011b0303200408010c0206011406070201021c0323060904030503090c0d050102032d011517010e0609 68
    0x3140c9500e0261083e1000c95000b010400342040d21000c0b6041e0448010001030410000b12082814010340140400015551408190074040044606d2a24441050360305e400e00f80200c010591441e0084405402c0c408088005161000008141c0c009154460151809036030ba420740c904403000d101c1d42c40d55041d400c044611200c410006182d00e0340f076905035940d030b0080100c92464940c003d22240150201a200d0302140241c00d40240c1004000e105070030b2441d59689020000c1e800c44007010340c43d50440d080300004202ca00007aa40f1040c07455801c481c2750742d40e201a0b00c0182c2c0f9003030040392052902050241030700240b0fa055440300e05203854803940726000403c07580c500710701480210362060b840b03140b110206010900c40c00140d54000b410400300c506048208000400c0d04103030301c0048900e44c0d0000300700202c039a0012824890b00e540c1c10919032030b4480b00040b22008043c140140c0a4180c140030915500500c1303083e004883c1500b40c0c14040e12561201242000000700b1a0b50074000d407040c0011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487911034 1250 487909784 487909813
    0x60804060905010c050d11190f090e010b120c030f1801062121120b041d060a11070f06050901090206070602040614030f04060b0a0b0406021e0c0607030c0206071211 72
    0x803508d11240b00342e05407003c440d00d41001c2e110350014040303034410003038440000f0541c07000d18500640a000b101c41c80c2a15504411000e10041c04001d003060341e1100700380203000c07040d0482da03401604156800c0b0785112850008901e14018105580500b0000d81c64030082d1149526041010008600a244a40e0a10300b80c00e8807600c04011a00b40c0d0002900c1d00810301d1001041b60300c45c0303180e60070040002c1800f05004040c161628002031802803142c001c80b0a01481406501c1030150341f10036903154504105103900c850040c3c14641c600075003d03988031000222807210a600203034400c2e0380141001c1e155141420084000d400134040c1d03d02058070151121002c0e402d081c183c07446098000c005081c81d645564407100036209407000ca80d080031401c900400d183d0321f004040d1005e016560700411507490038078500701040c60325400c00300e2250800d074001c512503120001150203003501424001d542001d2480890200e22a50318040d101007107065184078407507480281c211002102d0030440b550fa9800340d50703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487912284 1250 487911034 487911037
    0x12060f06020604110a0f030803060901091104090e1501030515010e0c040b07062a0201050c0a0c08220b0d0c031103062403010e190e030301060804060905010c050d11 72
    0x800c005640010002400a02050354500b074444004c0c000d442c41035590001480d020702107030000c4030486c0002c070800445d400e101d03142600520780e42005100d08442c6102c480c0e92489180540b6030200c4c0c1f03410001c2d403501c8040086001e40c100e4400e10840c0c0d5a5641404c6403500294291f036482c0140004c00043c0e40c500442035a80a0003130310403c1450b152800703440601561148408545e05901c68900c0c03200503d541000741000c0036100610034962151050080c00c4400040001400035000e0103140c907826805421141442c3c0d0004130580e6503e50407070f00c0c80d1040641c406604601132008004140300c2c1c1000d01030050b0315500c00084c041105006419030541390481922400c1805c2400002c80780d11780302c120300400c106101a001c0022008ad145401191720076004030020794401014410300030420700c60f212504002d41e070200070502c01102941d84a22044c842e44007000030070004102481300b82d91100c00d545e82d011000304043c0c81011005415500005034551700c1034900f170700401c0032444100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487913534 1250 487912284 487912289
    0x13050a0c0e06030715120b040b030618010c030e030d020307020f06090a06060501020f120a03020f0c070303020c0312030601030c090b070506071b2d0b0106020f06131e2112060f 77
    0x841b1400d50f2440b9030181702c01084070448250344551a03c44192442d02d0074095903008507202165940358008102800d401c3d80c8407407015908051501d03046281000c80841a50341c002442640941d4949845004070718001a100048050f400382c139061103c0e0540000e95540d05510403c000d000c02a6520010f90b111341003004400442e8012481e030700d1141842030002d11400710b140c2401410b028481030841c0d0a90002000d03c24254000c02042c02499010040a500120218000c1246140190f40c2d10030600000e0600f5041c161a0300e40c1c200000e015003801c502901aa002403502d40c41c86e802c04540d00d10044d03d030903001c590000d40c1121007030218080d8481c442d802055242c3e240e4103440c01045035418000c07000083c400e01c4030514000500106d5428020304003a4010301d011030030b00034400c1c1418009445960030311644582840010780c1241d484c1c65083c1d10b030700c2e0404850007509001c0e02c00907141010818611140c0e1030035801c2c9030480c0400c01c103c60812001c2100c26242c50340c2c0b600305d04050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487914784 1250 487913534 487913537
    0x1e0501090308030a0f180c031103240a09140a020a0b16081b0304080a05060106170402010804060e010e0a0308060d0503120403050702040501061d04060e13050a0c0e06030715 76
    0x300300203a00c01801c1e030400b48404070417480024418040310340900f8000e808200885182081010070020300c00c484201e42420803084010b0701481002100d41c3c403041c4145450151905800b0f0009091402c1d0f990040b200f060308a03141c40f01c078010340300b4019101c0440f0b207000c0b84120407503900410b10444410590311600701c0c03549480c0710414070f5203c211043d04924103401d421035402d8540e001402044c00913000070303d208001810041d44a02d0f001d820f0bd00705810007401c000d904c403001910300c07948203125500a9020300b00201d071525181401c0014100c2c00da02d41d0550740c24060440b0440030006411100a0300a580703021b0103440300d80c00c00a6032110034038041c00541c410310152600a0280340c0f0650414801d0600300d1800b04954041403d54000364000d0740400c1c600e200044600e000c00088200c0004221801c01c00c0a051080308403044801801c0b5604e80410181100c04004003040072565642c0c1000d062a00c4580c1e800000514a00403110741d40030303010f4020006200c070160800000b00040380e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487916034 1250 487914784 487914787
    0x509100303021b3019020a05040c020312150a05040902102006040515130c06030506060408100501170304060206010e0a0f0c020105060415051e0a0b03011e0501090308 73
    0x800f00c50060702e81c01207159a11a50b0020101ca0308444440c11001c0524030300324101840d10301c510050b0401c404143c040314071035121420749005075140760105044d14004c940000d01002c003d641246980600e0403c500c2d1414020180989581c1c0304610b00c2c00c0141c102e503002da07045e8441062000795211030340001d4110240c06040011035006c2e600c0b244c50000d03d402c07806030000c0000b1003107103010070968040c1c1d019000f1011b0410042910b40c130b01a400102d440d0540300304001d9958002103000e65104010802d669007001c40c0b155aa80300407034004081440c220b034221000c803000d40004003003e100d139003a0b040e070401080158800210a9400701d40d02c0d90007409007a881c0a445070501d400080031008125a1b03104920350103a501e110b0100fa1004c650700004141c0b41c40701c1400222280c07480d5260b0301000891080001d9900c5054008030800303010b0303030300810201000114008400fa40c01c4140342010100002c244507d022a811034800c105135000340701d1598900056034181d46500000c2c024000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487917284 1250 487916034 487916053
    0x6040b09180111030412030606050a021506031606050315040e1e0118030305070f051c0b03030708120703060506070201080c03060111011b02100e0a02010f02030c011401050910030302 80
    0x40c03484001d01901c0c01c10000b0500c4405200341080c1a030003200c08941112600d20841d4840741d042c40b440014203483c3c18240d02e0000e08010180d641c50701000303503c400d15102400281e41341ca0900c1162200300140d440a029a41c03160400381a0f034108a80f811341d00e5159054a02541c40d2034011000c10740100001340280040302c59030711035044030b0025024119902c45441c0d546c6480700d44194a0800c2c080d580010346800c0003400200411024900202008000c1c020780d20118040c5c001a81245c800e010002000c00e248004203045000e03038900030300515004903580d0300942c00812050711411040d40c00b0030600344c40340200942c90103a2213010b400641d210002401000e200b0b40259005076050515120400042600c94295000f03488441020341035409885075894040042015806c0b403041c050042c5019181c106a49114803d0003a0412540344070031142d450007441100c0c81300740301c0e500070b12001d4151103100d503030603800b0300c1602d00685881000401d01c1e88074603c1c80041d82d43c5a4050240c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487918534 1250 487917284 487917301
    0x6010909060f2d0b1302180f030c010f090302030307030905031e0c040f0f0f0b3c0a090c0507030f030e1b13090f111e15040510020c0906040b09 63
    0x441402c02c3c84401952141c1015556030ba40426000450b010780d4007503660300c070152400d80d010441141450040b40620884003960b50003007900001c044003031914503c04482ca00c3e0485800c1950350010750113010005a120525500898020503941c05074111000d40e100740d10810300c501031034060542241c1160340080308034a4940c001c00e0b24510680c001060b50714600b08800111000400907143c000e58901c803440d40790070724500d00c05207540c89091500d81c0c000312012040c800300c50032071201642004500c01b011150380ea114080c0203804400c4040111003034001000d031990780115000d40104481380048001c1c10302c00e0040d034014078441c00c09801240c0b10b41c80d18005a141400140e0391148005060050541daa40300d1600654001d0142e482044100d0510b10703c0d400900c001103002c2c030050202035040205c04502c00030b5003201078a0001c80303000c00d0307a04a201da02854201981c06030922004068041d4001580e8280c0c0204846d40181d90703e0f0766003040b0803140000c140c1500012a600000d8100f03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487919784 1250 487918534 487918601
    0x30a0b0411060409140a0507050f0904091e0f1b060e040b031905010603020f031507050919080c0a060503060d080f0405060f1306020106140d0c0806010909060f 70
    0x2900c0505500d0420707882d0135108054801914640c034814181c0b1041103100020303800b920b50412110300b40586009003804d82c01d4003c0c420361080314000c9465030760030b4082015401c2e110342c0c60a640100320300007420601d00742c00e0f11516a00d050303510502c0c0c03c034885121111841c58004665598503140726082d000000d0102403c101050310b0741c94052048580707511a80c0410b000800c42c465000040c91a0651042050350302a542d00640244e000c0c40c1208801c440c0d502440b9008004c42c200b0549600302d8200003800840052210a2031030440d500000300000c00140000820000b2562001d0b1151038940448031404101c540c181d010034121180004200710341c0c024002a2640a411071806840b0008218141d001c421220f40b4404005648a01710390260219000703000036100a001c00381c03403e0803032407806581c48512807050300540790700c0040050300142180204000d02c242c82642da9030340c11900040005c404241d40c2181480010b02c10b0f030741030344074040110700c0c11020322101005010013000d48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487921034 1250 487919784 487919813
    0x60d030e121002221a160f0b040b0609040506011802070b010b070c0f05064807080a02090705032a133f020409050106090b030a0b04 58
    0x4008900c44510090310140b04541d101c442c804005070307584a6103001c40802c6420760040e990884520601808105442e6031010a07403218007503080d4560843c0140c2c0429006070003c001c001030030030701e8041c08001d01d0303130800f038490741c01004030749030301c0d0b444005000070f5000c1280d0050880c2c000b840144241d4024804d464800c40741c00500504001072961901d40d03070882030700036001c00400440d280d0100018a01c03408060824101404495480d21b000304070756005210b840907950031a2648045001007440084102c0d21116015402201000004038040602d0a071440032a0241e418081500500040d030310a00381c3d4007a2588070560342d0344000721001e4202501c20025211041081c0400c812050001c402c000428442030355905c3c42d00181e099545290b501551044600d000300522030041580039400309040007080f060244c403031964030036122480b220001d41c80b5141903d6981405130540c40082500d80b004004c00040074078008056880301e1095004000340b980000040000d10071840c007110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487922284 1250 487921034 487921039
    0x50c030907061d09090c030d020304080312061f090311042d15080d0207061d011809090b0103061d030a030e0114011502280308130206070b040506010b03060d030e 71
    0x3c0341c0070304000905411000c1d40c490805030302c42c00c484015860b003441007000311840c0740011840c2900e40341d070309600c90240026055440e40c1920008006d074569240d042510b00410580040407103c8601c081c00407209404283c034140300b100001182810148941c000a03010082c00051566203810032010740000c0c000c114800548a40f41c000c06209490040c0c0054007514000e041c94a0700948024600701d410307404003040241180d1014070f48083d11102c030390051400c0c40e010940188540c1c8000901034a540207420341c80c42c2c10303010403d03c500281c11606980c4950b4061101800034801180d641d14080004072184c0c20070048203490b54000d07030000898190810012038a104180320102c1040001d0703101000408050806503032241d030621202005481102c0303d54119041400725100351140060001c0611450801040c406490304200d01c00069000b40101d50303403125854200603402068070f08a549102d07000c00400c2c02c3c00720b1402c2e64401c00015044809900c1c1039203044405030b08403d030064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487923534 1250 487922284 487922327
    0xb06040b03040f1703011d01060c03050c1e0102040302042412050705040c050a0f020d05040b0a02010204080106120b0901050103020904020f0d02041a1c0b0103140f070f09050c03090706 81
    0x300203100341c13003d01000c1d941d84548a40b41d62400c07148101148406984044000d030b01001401250303000001001701c6901490480d880e03185c0c40b92082d03e4440480030300c0c080e007800820b08051b940c1c1c0540043c01903910035203050001c400c80710085200511110520b041c40030303000500380000071030344c410b2540f40d40c01482240d000c1c1d692103003c40e040703440c00d00c114000500d0020302c50403e036400c20f180c103069507000c3c0300909102555100c010300768060b901400700030203800540354039010b10035015035016140349002000030315075030800e200c106212302c081194440500380024500723840c103200ea18100da8020b000902d55640e04d50800c80c2c3c5d00b0403003d01903485400b080c10340c800360f1214850110039407801c407092449020b941c02002401c05503207001c00b052030008165140003401024031541142c1d4401c40c0c41c0f104076010742d9100d003041542c2c0083c1c6810302c608140040c203600700c549034000b01d42c03071000c003089291034100080c1d80b40e03c404c48464103282e00580c4200011442014a18a10044c0d440e545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487924784 1250 487923534 487923563
    0x10e060109030605041203050c0c0703110105120c0d0501060f05180d150f0605100e1c08070c0306060b09060a0c031404080303180f0706030b130c021f0b06040b0304 72
    0x41c004c50b01d060702d00765a03203211441460103458040c030509400004803070701c080c1080701d01c000040d1b4405250100401442d5000380700001039010740180c5900982d041002121882c094801d80410f400c0046916030075070400000261050145820b11039070320483d0341c0c0700d14051000d00c0d0b200d0f071013400030125900071185a04801c0468054103505550741d014a101240c280a100f0103001a50180d0b0031692107582c214988142144d0403200780d10024200380c0e41120908291244400d40700c0b0400701c09410001c001441d00200b248455000342641e120300d004020080d03c034040746580d4060141c070690000c10400c40c8202c218050f00420ba610341c483d240c40d04e0f42521a100d0713000c0d01d41159000284540c004810b00c1407001c4c0040740b04103075200000007801003000420a00d9911001849690181540c078008a41c041c0c86003031103401408c034050b406114400784118000c1d500c000410300b08001e100072040d003401a0105002d91440954010303c03480c10181410250b56941e800604200c40034100781004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487926034 1250 487924784 487924793
    0x9010e0601140406030e0115080a110f091f09050f1311130b1509010509101b200d050303070e0a051207060801170307031407140106081014010e06010903 67
    0x42c8054911507070f0100c6d1001d80d2032203090a41f84443e01e40e070b10040c0365040600c0721100018100c1e00481d007003048011702c01503c8005c203030403811120701e260300207900000300202059202512040c80c06808000c81d40243d41e071008001700d400c2030301c112030207241d00ca000c600e90002d00c800500420303010b007441c24804600c000003d110781250b45440d000d01500d6205280c024602160751000100d8002e00031407400b070201c000204a13114814816224050010640a04912071a8139221200a001c49103001103100d04240d4600d01c5510101080c031040c810b030a141d1402c06d95100e40e0840d0303010004500b1a00e40500a681005464035841c2d0808590b41000580d65500504980044506400b41c2003082c14920014801c95058101c0d911603600364103140c4601070000101d6040d5501440e007000c0800642c8650961403003400c0014000d900400c01c41c5a200300306601001c200c0d030341401103d5065110220400c1511003c00382c3c903c03c0c69209004100c5020b0100c55664040b1b0145405100c007500d9030394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487927284 1250 487926034 487926037
    0x3030b06090301141906050f01030c12060605070b060612070f0c0f0b16021f0510031415131511070c14100309050303130c0f0b0309150609010e060114 66
    0x2080b0045000c10500c001c2e091285d40d01c3d0105510040f06005090a010100d4a25200000510b04056072110035a6650b07104654928155000e0b07441030010a0340c6520042c03490300300304000c0d143c5402e07490100303240f460034804580368102c1ca082412a02d91b01d100303080d270300400f400d1400400c0c44544800080003805000c03078408101c6c840c11882000381440b5803c84a07681c0307110f50910655020b1201c800c00c070040300100d202e0001c240302000c161907641a64480c0060030031b900081000b861084128003030003010903a02d0b1510418280000c182c0d41c2c6c0c1400b0b0720454801c40c0b0113002e40d5a01c188103800080103130042002d81d020ba680c0c013464900107a81d02400c0507035540c4401c00898840c51b1801140c500100c52a48072100b624041c00724045a071a503640741e1102030602c0050552086180041108a0482d18018034164a5600c1c0c1142e40d88415200c540c412260601c05010b0411110808140415001c0c003503540036000c070740ba5a00704400203d4592014202c1418000100c00540500c2410b50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487928534 1250 487927284 487927301
    0x3030f0406082403062a0a020f33090a02060f041509151b02120708070515040611030d0203180613051908131e0b041203030b06090301 59
    0x26a94242c903d0500d01030302c0190440c28103081d8216500003901201d54000a41a80000d4400e05138062000084900607680100c5401040c4244021600a440d15004950541c8036a006c005549070b220411030084840496000c814820403540c032261403001c407800d08010750180824049803078074220707900028466044101c9111096000040522030012092440e84904100b070400301111402c00c20f450310500c007c40f0366241005020708480e00b00001c6001516401038025107841001e020319a80b203901c601c481d0080100c0761040480c00605400c14032500a4000300c101900c2c0c0c14142401c2c0304555641e01003040b54018881845000344a10311407000f50b00801c0e0140c170703200c01085800900d0f410074070300410f0b501010781c444081e0702c089180030842c1c515241c08511a954010b91500e42100c2602540914080b20030b058903012034001c4c82005640d0b440303001c6c207040f00d0005507100e0300c130183d038865405110780d080c08801050300002c0c0260407811900781c0042c00641042c8100000c43d007142e1904 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487929784 1250 487928534 487928537
    0xb030c131a161a010810140c0f0c150a0b0f04020715050c0403080d1d030708270d0308060f0303120f09012403020a120f06090203030f0406 61
    0x80608804036098850310051609900c14100403000460052035400b801242e000011050030300141004144000c510b00c500c0301c99828205540c5650b0f440d0340c1c9880041c0094907482c0f8045010402c00d01c102c000078418040d042e21745180000003841c903515a003200006118501c9400d008650364041603020500c90f000d00140060703244918000c028444061000c0103001c0c62040000501040001c0d144c1140c0c0d00000401190070f48850710045e10b43d220b40da002810038000400c0206100c42030341c104081c5066109424080001541c1000b030300ea200e2150000c285003003c0040d0007011010380500941c46d07000d405010000780468000c0760211340f02c444d04600140c20031040001038508a488071a40c07e02c260019420140224000307181060003900c8544c100402c0400122107210035080780e420003020781c128802201400c6814905202c290000720f119072401300010070b04142342c18030800d400d038000e12041344252203a183c1d04000c1c490044244e8050108010100488506800400090405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487931034 1250 487929784 487929787
    0x9040f02010806010e1807050d020f03042d060525020f0d09150309020f040c0c110301090812040c030c08070f0f1401120921020f060105060f0a03060b030c 68
    0x4a1000402d8420300524003414030804441081503078440e01514035400004250412681e1100360b0151001d008940c4c0603040c00e800040c54000d1500900042c60049102c0e01113400c0e02000401d018149011054031803000e00740c071443d000046212a0461600b00c01e01403540e44940452400040942c40480304840159001c0c00036541d109200308043d4010040310b00d0610f140e6402c20400512a8850002d10f60406454038400400d6540b4003034107200100307004004000c110502c2402510a07503907400280c404008000c459000f80c00d0600441580c1d6610000d41894049000511060036401400607221301200e05004400a20712060030000f42001400624141d89400f0b0f000c180c020b51900301100001103e81d04100345241840943c05001302400c1140e255021410b02c00e0040c10381003800742540003040140550841022104461140c42d80c4c2a1039264050424459079031030b00b0701c1141d420680801104402c0b000300000303454161001e203408207009540d11458402c64100381d0320040111350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487932284 1250 487931034 487931063
    0xe06070c1e140915010c0c0504020301090c09080a0503030112050a0203010e0c0a0902070807030309031112280906080a0905151015090e060616060c020d09031104020c03090904 77
    0x1038809011202c2e11040356410507034685107400200c000c1140240c0c6050200c201d0600081008142d1520060a0060411500c941c0e4901025000e803548111402c0400c41690000c500c04101242c418619504003005511316460070440c0d400152001009a480d402649404070059900b03000e20800d480c410402010b00b9844d00040281d064140c1e800701180c41d00c100701600000d21910300f91801d45405090001d0200c1070350405588800042c4400301450080d0144402d140132943c01401000d44c030300c40920760840404020b04854031086082101044590b482040224456200950b01c202ca010b408103184140c0d83d40c4074a4141c030f04003100080c0c82c0701c00400541c00c0d02e01c7c01c85801803245030300482c2c40c1d89501c88050300400003801a4000e41c041d41d8000b8a0b130303481c0c2c84210381a0301c020500000841d01103041a02c01030000d030b00518014024601c600d02d01034412a4040705898000c14011011020311040000944c0048540f400c00e000034804140c0790360307501312090f100354000e4071100160b20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487933534 1250 487932284 487932299
    0x1207020a050c010903020102070b030c0403020a24050403020f09061c0309080f06040b070827061009021e030a06080d0804050709020f0301150309050105011202030f010c0e06070c1e 79
    0x2c15040d501410400042010009030783c2c002141000c4942807400c0542c1da40704d103640e400d541d01c1603802c06900a6260400000c040d00d440c441a00c8031444e518184000307401d0040304444078801c41c800a5440040c2c414000f002e030ae004040c141d0008002052501080c038040800c4140044035603090f404500ca00c2020010881e092242c1d43d014400080034111521f01a034908403120f00c007512034410044400300158001e0909041051212510791000d02d28034207a5a11940c8d400e4111078034103240b01c0c1d000001800d18118004c2d2202c0700c2100302c00500307031908c444a04803160001405040a06d0b101d941c0020004014000e04481200f1641c550700f0502d45400e10b185841016030007450880e10410012180003071040c01d40307045d910410320510101c0301144084024115130403024019500c2c1000015410401881d2041103c0c400d805545a403000d00c61a6422038100806010204200c1e03089041d2070310b4210018000c1d580b14510002d0380a40341d02d03465008100d00240100d603080300c25020b22145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487934784 1250 487933534 487933543
    0x4050c070c0b07031b080c0604080d0b010e01022a0607030203121509130f0c0b09030c01090e041410050c070308150d0201080a0f0504151b0c02060307051207020a05 72
    0x101036030000c1d1850404166801805504100103480103041644905c008210036201191a180204c20440c2e1072800e140c1010704560340401003040106141c419801c080e94005c2d03e83c0341ca0300c81c0580180c041885250103408071900e1140003413180b02070b00b9030000c0c400c1e51018043c1096070b000764011510350401424100329198040c0080d0150312a111078009240d03070b8061902c6e4042d48074614513040107050b1a00d64032301d10262200414104045a001c5040e01c0c001001e8241d0301011030445e100203c0d03030310040d10001240d0044028010f800303000240814000d502c504e0000c44103408480d0881d00030041c0c04103e0b10156020201d03c0e00c0060f00c07100741030380b0600300d981021549500385220705051002561038100d180c0020706100601c03000401d40351741075125002044030300d00103010301d14043c034004486490024895101a142c022198030551250f03240b003404000b66264031841c504a0340820440390001803880301008801c0054441c54403808210074000d80254000748141205e500e00b46040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487936034 1250 487934784 487934789
    0x40e0106080c03010b0a0309080705010207060506011e080114010e030d030501090f1a0405040c080d0503010e010602070e22020406230103020a120e0c120a0605070201020324030c04050c070c 83
    0x1202e0b080c0700600c00343c4505005c507001100740e07080028900141703150250550061501c040e00030351004c140304051040d0f607080548255026a20990010421100901c65043d04000300000901610050101c500f10b84500d0715402414104030241e1400080081d1a1040e0869a000080e864000410002120b402005044d403104802440059105184d40302c000002501a6101d20340300c4020800344044840b50402410001301980c3e990900180007400f01c0e0301c203100303000d038004455000141540c4080b03900d0054580804032040c0319140c2a02c98094840100425031528280a1742840140d4442c0314400c01042e101300186100d0722480702c00c8046e0b40300d40440a040c18010071a41c1c100c103a001c84403100061001d4400542c586040b08a5882c20380c03004070035504107007240b00c0ea0b05086030004070355400070310a407810f12180c1c0d0f80701400c900b070b4002520300d80c030468003900084100e500404140c405555001c1c041b2202e190101001a0545d0410703101d40301c01d10700024900f070600210f101007001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487937284 1250 487936034 487936051
    0x1205060402121609090606050403050c0a06080c130801020a0c060c0f090603090507080303042409050d0c031211090f1c080306060f12250212031506040e010608 70
    0x52034421100c040340a03000800340010749500e00c0381c1c0f01c0800c1c0035402480185c054030710204105038440c1f00190065009000c140c03561300c95040c0c80351342450f0401140f02620b10b9940d414503583c68400f520f440d6034001412124611b0400700c03021600220034805010003078640d40d140541301419091845c12202288000020809405c464131641500a500101200c0341440d000602600505000e41412400d03040300c0c0c1f46000c00070912040c00301c02e20034810702c044148480031181c4090050b4008a482a801c010015002415011042401103094036003141c082c1c2048000012450b15500c2101c3d40c0c1006c503031808030b01081c2d42070542401c030728030400c00b0425525001d0340c054803084010142d61000004019810000001b2101e403180400d13145201d03503c2107403640320500b103190424070074800c54480c1000014483c02d0201b051307400030740704030b0703203209402900085c040000980e0550340010034004070900c816031208841d440b0040100010711500c1c00c582c003d5410804000e0080300050070968 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487938534 1250 487937284 487937287
    0x8270103050720030c011109180411090403030204081c08010f081e030c06070809060f07270b16050d02030301060f0509010909050a09020405070302030907290301061205060402 77
    0x20708181c106524000f1000705114003005059002c0702180ba600c81d18402825550070042a1070020b0b00c810082e190414007240c03100d06400701d4510407011250100d402801c4001c1c00e5940c940941400b0010a030410b00074500545400d4a8103040c80c0b40c01c820070608160350302e000344005c45c426803000034680504002000c4101c071601e0681c00c9540d5500c6800c4c0318801c2c108440704080c500c5010000c80300c01246000a0b248685410f2501812000040b01c03082c40c40c2c000cac01d00080200360b06402c01842440c1c69182c4540500d040c5403000c0c10300081d42010540034503010800310360a030800d0301904d074000d8508040d14296103186405400c11180b078041c0b40555006200500c600ca4100c08004500e070601d00d40700da02d4070b000d403004984201c82d41d4072103d0350071b24060a104180e0842d410400706d80b8002c1e10107109607200e68004408070700c021285042e0942103d0801e02506698001c0c00c074400c1d0b000520520504034204c44c2c46904e6000380d00c0030001c50311251800b900c0b1003c0f0700540f80c1c412800c80e01103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487939784 1250 487938534 487938541
    0x30601021506210304080d0203030403020f010504080307120b0a080a0c0f26010f060f06030c0f09050f030715082a0703030b030307152f040e060d0827010305 69
    0x1041c1c07004100c0f201c605420420300da02008030040007504c000300b01d540100d80c0f0306171920340040d4a80d03000b03860640040c0506907804036088814060303180a55800b0007414507595800c2c6045661402c4d011a000c10307191100880a8540e442c18402c5000d8601000508141441e520b064444a0781710391020b40c5032500e0740b000b0884900302034010048580b070040b0f140c024201c0704400394010840c114182e003050b07290181c049228103015004000b0b42d81d058030100a0352801000581e10507031070040c805c00040f0070f90030611031402c00f080300030b0194401034219802c41e600c07100400504901c4805100008101d201001030918042c24102e5403004080000081401c0914840d0784070710034281c01800780341c0c5503161101c40e52820021207070701da9040071100b001c19800c400117902a20280c00741d2549100e80400e00096403e0003500c42c0d8440345040301c2289860b1900550b0921a54000c020ba81c0c4603222000820202d101c030300003006507540b07040b4003c250300302c0c1d544040881820610014105450314080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487941034 1250 487939784 487939789
    0x210c110705030601050424080a20100315030501090f110a080604030e010c050f060108060601090b0904050a091527050d081005040f0209130b0105190c020d08030601021506 75
    0x80c4e0544a0a80c4c01048034094100c5102c034503601405020400001c0e08030004502c180030403c0c3c004035100d0040424011000004200c3c15851840c0d541e0f07020185640301c0101500030790000b108442c007041c44030896940c90312900c1c00c480141009640c00795141c1d46c440d0070800078201c1144203550460303030f81c5134282c1823203626035030b6400050000b401d10145035440c2c0d4580c0c0c010880b029907903901c60100c0da100c011014003161507180a118501442c803946010448035800340416105441001401e58109540042008082c2c1070140c00002069510311900011900c000400c0b03e5050314107074082000c0400d691a010f440b03800000c019014001c03c03200c000011004916688102024500b01e45e2a403203800030910101950340c0300a90040c6060f458a00c2c08905030060000d00c4811204034468412001d928825502d40c00a940d0026000300141214a480f040c8180550981c6107090203001686501103150000c92200607103880402100b08052507078100004003086502c81d040385100d0034000e01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487942284 1250 487941034 487941043
    0x4060c0c0509090706080a020f07030e0907020111090103090c0b031f050901030f0609050c060c0c01110d02070e09010b1809100911060904090f0c05131a01050a210c11070503 76
    0x10f513010081905c6c00300300c5905c0c50b038050364000011240d00f2680c502c614540645424008002136010748607400c00500d80a0061041c03201c50035110302078a01c0c0c030b011017004400602001200322500314852001055210040300a0352103182c0003c4c605420b011003402c0f2941030007581c1e10240c440e001c100c00500c0014a03039801c0010055100341c01240754005850014189100030f01c23003e420001c003050512194600040d0303ea002c160a03218445407010380f41c4680d07201d070015160b50015a00105041050344154144107070710a440b107000181c0030004100240c0302c00f9000d0408030038008190140b2084c5103040c0a40301841d440e06004024480c1c1607602d80440d0b44010266611403c0007088000007601c0300d40080854a60181541d10101d2051030981000020b6006103030252081d8000400d180c2914401d180211145420740f8000c10186001103c2e160b1002c002141080b15681030540c0400202c0741907600b00ea40c44401103003c07480c000c1c0c02010246032048084890b80903210401c002e840115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487943534 1250 487942284 487942289
    0x10507020a020f010c2411040e06100903080705030a0801060f0e0906130f090611070c03021e04020309010e0d0c020d232b0302030609060d1704060c0c05090907 70
    0x640d41040760f4405001030b2408243c00c04060700403031040c14015038105a909802d10358403801c040800c9004034000d00d141a60090b03019400d003c0c510080800c55074030f802d211032480c01020b860840341c0302b0b0700c070f59410b0078540121804a40e40e5001150111420703030000b0b00c0c83d0140c10a4a090b501c4021000b40003040050741c2c1d4001d500850303160000c50510f450790001d81202c4000600103215803c0036a40036801049006810b42c0c51614144d10307030010701841021146c0c110b401c0144c1c0b5071001c2c1141c082100c0401b91a400081c82003204074550082e403141c2c009541300e405050000220078140c201521b0030026803000640c00c1200d01e00c40b04005903113010710312040da1381202004a079800c2c1d91941c8081201c15103034041c0d803881074a0181c0c0d00308c284802091482d018040e41c01e02a030081d9141902070340016945550701c4881c050000308e6500300b0145015661b0f009002104d2603080a0340e9201480d400364101c04000781c04071610205125401da2404020b082c2542c01c20071503c0c1240a60361142c2103030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487944784 1250 487943534 487943539
    0x10318030c03022109090c030f01031e0b07080a0605060901090e130501061518050901090c022d0c090c030c070c0308030f061f091202040e01090506040b09010507020a02 74
    0x141c4000302450b03c200281c805510350215580e5481c4c40c0000398800c01d8200c00482c900c203d0781440000c004500c2e2100352405400203403e800d034581d0035a42d400254803c0590400d03241c0b1070144000c00070505072400035000d44241c0d200c02c8000d04050642c8000d503961500402e0040c142006402d080ea641300f2148002c42c0e420100c403003031644440500d842e6640b0305600c09451913007401c0d40403808984070440700c0b4001d40281c940c0341200c1400d0441c441d2940c203620615522189502c0100000042074020f50f1240c96180305880410082d4055600c0344120300080c1070042081502c80c50390f601003000038502c1c3c110b00300c1d500e100c0c034070f4445240d80d0140300003000502d9003c00801d1302e900700720140d080a006035500c1689107483e480c1c8500300b041740001c1200e51a03c1610401250750390780d028003180030140b0441c1c4d0340c1c0d00c5645090010f4451800420394007207801541d100140e0030711603028480c164801d803140001e4649800c1508040302c0b0448080c0106116901d868144042e59400046c1c82c013a0940c10b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487946034 1250 487944784 487944797
    0x705070b072d230a090905010602120304110a170106050102010219270b091f0903120e0402070609020906030d0806090a0f3611060c070317090a0501031803 68
    0x40d00030488000084009481520300e0f000d21412010480074041e00d1018030650310020001d99030704071201034602c280b00b44009600402140f40c8100d940000950f07101d070060b100c1e03080390076245000c1030408800e60704c204490624804c15043d80c410030701078a002400300348000c0d824815040203007509416034082200620036000b40d0340d80701d40c004840600211030a12002c0000e980e940301e41291035401800114441d800d18524051b840c1c000101c1644048102c0d80d5030000b0604607900c0b03120841e66071110b40280030b50001ea01100d980e9074001020818410000400c004d00544107101140d40041d00782071007604150550a116a8400000c40d4003c4040300d200d40349071100d0380c01c60000c0c4a8203181c01055403e1200685010b180c02100345580b0640c00480007481c2030540440102060031040203002506c14213200e81e0520f090170103402e200301800c040d0b0b445546d4036640c40d111301c000d190304050110808901051140b0704003490038000c0200782014450b529156404000291965000a050008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487947284 1250 487946034 487946117
    0x612080f071403210106090320010e030f030903010b04060b030a021c0507020d0207081c0509060c0f100e2d010b0a06090e100b0301031205120705070b07 67
    0x282c0050402e0002c42241600c4c3d0b80c030082105940b01d10114408a164042c01e03400000d6a03a2040b0030400c126900055040070207500c03c1e881302021410a03480e18104480c0c0b480380f03640d07580c00b400785e82d4242081500540c1d8903003d40d000d150035a0701142806210707030301d4104100021105041101d5016840c0e0800607a0760b0b1444804052000f94000107034000c0e882e01080290741900019103441190700d0703808507004640ea07514180d5407a00303604054002000c101c442888134500810141582e04030040000741000309240400c0e180c5010b260108515503c00341c420001c482c540e101d00b81a02522002428002550749248215643d808840b180c84030344100b20120241400e5200d248000c1f0000c2100c890556541c2d8000c1030200c40b4007c03098103600f104045510714524007800b100310307500e505401f41181c1ca036803104082d9805c0581c0081c24000c01708180504040d64000303103803150311503440702502e5a041d0f00f0301d88600700f8003e110a0034002c41410581e004000041c01020701340482c013140c01d900300e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487948534 1250 487947284 487947293
    0x90b0307020115030c0503060f090316080c011a1216140607020d03090501021006081b1801060c0c05030d020a06020d020409050c09042f03070302120405010f0612080f07 74
    0x2c03d81e0400790450141220100802000c002140101c030011011100d4036250002808040c41c0242c0740301c822a401005041c107408210300000306914029154182410914010303e130a6503001ea0f08051240002a1081482c1c82c26040d0903007060b0480009002007003221900c00c0f04503a082c09007c2008010000c0f4024540e03600701265503296014246101709101880d02500b000080c1c059107025004040303001030070415510800c0c1c1100e4014004104d08401c001d45074a4000701d2a044980040c4551a6000d010b2403a85a150007030020781d0714a00314030203500b0402900c07982900018440d0b0080280301000d2540010f1210311140c020000680e240c0000c4a07603402403041c1c0c2d00c0440054107110400c1190107100011301050707401a603050081501d904502d1980e943c80c0300140202044407008921244040006154410202c2c00d00500e17010400035000880c4004607400c07034840c0c0d190b6240c0005103229015000080c0003056803181004c0c010f5841c107080c1e0040f1004078508242c082110300501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487949640 1106 487948534 487948541
    0x1050a05010c170a050708040609080706050424090f030308190212010b0702040b0a0b070c150203070f0602120129041401030c0c02130e06060f01090b03070201 70
    0x4410003180001c5031300300210100400c003090102c0070000d050390b402030014140940311902c45e140b40604540c40c01c10540c029404104047c8810820101442c03829020b441d821102c40f108440340e0581180e103482954041800d40400c46800014141c1224030240507200c643d54101c0c050f42c400038008244e00c5003104505c000d40f280f00040040400580c050000580b0081020904c080018005039054045420078485402d00040d050100f0418882001c0200b80d0340036401c0180820020103520ba029100c400342c0003042c059084000c21103540c1c1200c110040d0a070480104e03507112084443e8051300312030056490481040400c110118007400e031001c407240c0302ca25000302c034000c40c0114058944010060305002e0000710080060340e8007045991b0800e8503040004820203081009840e02002401050080c00d40300300303030f81031a41e001080d00c00752880314825a85d20340315004102d004 = true := by decide +kernel

theorem cover : BRFrame.Cov 487769784 487949640 := by
  have h0 := BRFrame.cov_init 487769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487769784 ≤ n) (h2 : n < 487949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
