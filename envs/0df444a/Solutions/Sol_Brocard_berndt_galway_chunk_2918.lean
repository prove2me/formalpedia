-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2918
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:42.640144+00:00
-- url     : https://prove2.me/submissions/a6ce95ff-9ad4-474c-b268-ad1501c3a1d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 524640287 ≤ n < 524820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 524641537 1250 524640287 524640299
    0x25080c061305070e0106120f0b0a0929090f060f060712081609170f0d09060905061c18060e0c0906060c03040e090307080a090302211024030804 63
    0x4800e00c0d03000104d16401000042160076030005151192003000c000008402e00c0b4820302ca40a441c046800380c2d04125802000100468160b1046040d482d81c10003426011412100c101081420b603191103500003030f12404900c0300c58030400e2590300110010071260900b81d86101041180e045040140c6800c9084610101c2c96504034494179400840d01418005104010b0b03c0546a60003c2c0103445605000c0324101c5d251200c1085040380101d81c54044802c401403416000300032034a540500c4c0000780070010002224244901607035104051003c4800d8a42e10030242e0500914240110100d81c001480c00040407460504c5001d86000010740a80344d008075007418841c4d001c0010f04143e00820041020014100c0084255403d8894100920000f40c5138030424602d1405242e90242c000080044d0200c1000d80154250701124825603040710f01c031081c0c0b245811003441148411200d604540003401424030a5403110340101c0d039654101009070104a20b980c2c092066800480e50b0740c2c0c00080601074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 524642787 1250 524641537 524641543
    0xa03110c030703020105030a09020406180903090803091e010c021201020a030e0a0c1703071b0f0803070c1e17070302010e0a23060403120c060e010225080c061305 71
    0x103180c0c141c000b0001245598002062440f0052070041700c1c9948071311100441d074031a080140207010709000b03010a11461003c0340c0080520050881c0400d06402c0d0024443d0300c00310507101152030060043c0e208500c054404600080c1d145030301c5040106890100006a0b43c500a91181c0f52051000580700c0c510f17403101604450200b050703015554030440a0000040036050700380b095840c1321301c885c1564500e41051074a5070081c40c00c0117150419040f900d0b5074800c0c402500300102d46460310f600302055036440d2a1502ca00c10340c0009000d10341c1c49078051100707241480402500b00c808100c02d00b00c0136a20510980740154103924102c850b044084100f06640e4491001c07002d0960884104500078030300501100b20041c2c0000711050450485899081c40d90b80e0015a4000c50700301c01100408071421100414a50100c9001c550091030318000b04840c46051080e5207003043e140ca80f8803a1000d48d000c80c640d4100c9041c504882040d0100800982c00b402484000e01800720241500e020004518040381 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 524644037 1250 524642787 524642803
    0xc02090601170411031905030a0801270e0f0709090501050708060a060c020f042415140304060e0f030a0909090305161a0c0702030f011419020403050a0311 68
    0x1040000040280c00c0c0e40441942003500303e0391100c5003004030803881d0701185c140421201c3d00301240300d40407040c1080c000040005c000c014055903501c900e6a072110205100e08000540ba0300304024175625584a10b00c8507400560b211098404a40102240505c26450000c464106840b06912483d080c801c1040901400f41c0103020341c240100070b85084408920700700d102d031190004000e140c005100c15516220425089420081e2040c0702001c685401d10014100c9201c8088108a0018002552440f03200e46c2426030382e40caa8a1340046512400152043d030006042a00c44075510300510301c0c840030402041000403481400f0719203407501080b000c0c00315101648080245420300100030f0000b44c0c00021120301d4408541211540d110030f00700342e0060140d02c3c10041d042c0c81c0107018001d8111340c0c0809040c07103520840c00c440d480c805100c601e500380e074030f00003001c0c0c0c031101d0800100d22108c5403051120100d01e42080d0040c01d081d62515083e140a186410a4012500035280c00d9082042481444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 524645287 1250 524644037 524644039
    0xe01090516180507050f030411060d020304032003371e23030a0b120609190b13080c070e1509190522050618071401080a0605060a0c020906 61
    0xb03c0d11304228040c14900c0340118005003410000b00040030029148500710601d40050035113501da100e120310b083c009510a941c190013140e00d0301203080c50500c11000481c0c01e1103001c009181002801c0c5d60180c0c08000d01c000411203213444102031210000783d540d02d003004a20655a49068a511a001d0501041d042c0c0340d40d42000900110008085030045540c1216010845459a07030f65580407020000e0070352440c3c2d20780c01804e0004468113003c0010701ca5029010079000c0ea40c0c001c01d011a107285150495400404c0a00e602000900c60050035060058881c02526494940594103031000c3c240000c5420103417076104154103020002c09480038900c0301d4202502e1210f05410402401d905907040d024070b65607019290070011b40340b034010b0381c0b106001e1920140c50606090715071034941d449000840e07043c80780720758010007074020b0b000024050013100e46400d8044001c0b00c03600011030304007000a1100007040e855280c00100d54071458018000700d03200e5aa05500c80300b8520421220f10000303819a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 524646537 1250 524645287 524645291
    0x5010902120a08121504020a0e04052206020a0201090b0a051006090b1806090a08060f0a1e05060f09090a0606080609070501050d0f230f1303030e0109051618 69
    0x84002911000884000013400c01c0d04c0f91450f17175207029294480c1e41503412150018008903802804641280b0b4990443c207049030144030542e1a11032000c08005244510511071011007601c2022581b9540101b074001142d100100c2c1102d000d8489184440d401d03585d40c44c85a50342c104000c91818040300c0080500f10510701030b810589010130080d900d000e42002040d41007414090050341da5034910480e00000c80260010810030b0b5a98126500d0b0101240d810400c40080c4000809000c000d02c506072405c00b03910345520b5140f088000c048003d120051a4503005080e401d03603000d4503a2703440c82c000e203c1e20f1043e0050000c00c06510301b06050301c80d0340d8080e0315554494414461100780204403802074580c2032a06030303111100b00c10107070040e01e000e20312540c100d07190004403102c018900010b811202c5690940712100e440b640180c0803103003000c591010524200d802444002842a04070341e40b00c03400c8400210781c4203c107842c0e060401c01e08180225221142260801c81c038141514809241d60f601c00e02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 524647787 1250 524646537 524646553
    0xd26011205010b0f210717030a14090901031b030f060207031d0a1208070b01090509071e210507062610051012022a1605090c04120501090212 62
    0x104100307172004010038200303c4070800340e094641010400d0742c0081410204d4642c0d40009003074042e44a81c0810928000504030024048030124480200c0d511100c0251111509a2070f58880070b550749042034000025074041900000407500c0410352100d0305000b51001030b500d209518010b41000c1014600100910580041041c0b03540d0340001d9070122142c0b007001c5280c000851409000900c00e074000100000065000030660b54001d134049841801c00304e0444200380d071030700b408080300c0403c00021000302210100c103002c60600620035403491a10400144d112006c0760b5035090502c0d185030091070000b98000c40c10440407070034480344030017280c20100102c1c01e401c081d071182c0c4001c00c0343d0041c2406080d86400001281d4403a0540c0304003480c280d44110344642600c54030001030201010300b2541c4c80f41c01c01941c006c00001250030740c141c255125840412600c2e0000b804185003000f084100030203010700001403030f610107645d26428244580000500c40026104000e15031146a01d11f440d15405030706 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 524649037 1250 524647787 524647789
    0x50114030d0509010c0f0c0302010905060310050402090a03062d02251a040c06031d0a061a040c030b041b0c08091504030311010b09090d26011205010b0f 67
    0x540c140303001d00074030340aa5164110030042c1c42a4202c1c00f8018041c59545503110148049038100c4002e6034801d903138150801c3c2c1c1d00c50410019000135903ca852415250344104640d19003603004100c08480036000565a95480e1035a508844181612103d181466044101400c04c1c9150790484403600d031104508001041c0350708640c09902075910300100e4440700d905800d0100c4041c4510301041080000802ca242900d44500388424501c00e10000c03c0c1006014880c41c0410003041d22040848801070a2441040d01c0d400c0c0500580e1200310303d0241910801010b41e29140202c18140c207803a1001b1442c80e048400380400c030303100901c0a90060100200d40c803015030344611515255504101c9039070700d6030b50030000034426014140708403170442400200002050340040342c5600701c0c14404003c0010803941e01c00d00c800000202c44150544c1c10a5050300601c07070003030480401c401484507608000d00620340d450b05580384281c1060305100a46107880007004000d0240c481c05c2c00782650cc0c0c1c440810110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 524650287 1250 524649037 524649043
    0x305160b04180f0e0303010b0a031a150d0e1c020705030d08040b04060f1a01080f010308040510090b0f040e010f14040e0a02100305090c01020606180c0c030c010f05011403 75
    0x901a002d215881d80c20140c6250025000140320011010540b070f80c0356556035408645074001c40c040300101e07090012040a544d800007003040d5a80010306101c820620a1142c881c460388040d0375542d4880c0e4030a500511000d0400001e0190f050740c4d40d05003006550800d0291034010264840e91090340001900071302c0c00c4e84490260740242c0c0c1b03c1d0604a080c1c03140d18040700a0b040c580790ba03000f0b080c0303403840b0070715904d401003e000303c014402c0c3c170f9040b6140c64501c0000c411100c02d000c00303800c00348100710400680c01d054030304141c1c50203640380504c00681c07102100e04060b8080941381030a00f00214040c440f01c1c4101d0301c2c8500500301548a11340d0145031150341c9012000c11414907115030b0341c1e042045034109003401455251079000300000e5496007220000ba0040c03e041d20880100d224a80005001e9400090040d0095400505407003000130160701101d140d10006000e904040002c1c01501000c3e10100080c0044901481c00410602c80ca80c4010701200c00c140d00c04071481452044e0800c0a480c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 524651537 1250 524650287 524650319
    0x109081c0309020d17090103110304050606060319050103050d18060206060616050a0b10090915020c1501030609110105030c07260d0b03070803030c03240405010305160b04 75
    0x3a08010442c03204500005a000c0c0c200400584075900c0790704882000056070004003025a805d8a0401c0114040e40300c807078042c00211402001c503030111010071079615204000d0360740b1990601c245007915840c8940070b0151030083c1d00880345a0300c002e0809c010560054009806042c2400c0703010b002c50714114000751b0b01d18005d42440d01070080020f0b220340070340a048440c5642e0f0b070000c2c1210b4001943e0716141c00504011641003042030143c85020600c22094095041013580001201e200c403207040302401d0082d408500c01c0c111500c1102c111200010b140008035000394069140098100c40324145081455641c81d8558100002041003100600e07000c803d4640140e000580d1694660002c0e0513100190351100c150001e00d840424200a016207a03000385446c3c500584c145c4a865a48001e000e81d2404140c2e010f460500701440050904c90109501c0d0002d000e0000c00c1801101441012508983d0280c0050314281c1240d405a0030602015500ca4010b200d03800c0e4480ca05403030071a00403034006030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 524652787 1250 524651537 524651593
    0x90703080325020a05150c07141c080403030501080a020604090c0207081006060e030106050a0522020a0305010914010807060f0c0203030c03030603190b13140703060b010908 76
    0xc0030001c180c00428201c4002080c10603218280310485214401940d6004583d01c1150240700e0016065403441c4582c208900555225984e6070519200ba07440114241c0c00490350080380c440c04121035040c01800540d01d81c03407905e581715141d42e400e00c5c2c18000d046d02c04c142c0000025501000030440141c8544080741d0840310b0903580041c400700300000403400c5c820303187d05c40e04403445100f62809501c09a80d000a0480d00d1a0f00c0e0440c50040d104141820f0303a80c10704c2101d50102e0610401c001c1801d0202c2440e9801e0340146c1c607600e07060206103c0c841241c00012803500020303a03800061040004607c940c404131202505140181c1d894911034075610761460017950100f1004602141080c0c0c0250320740403c0719802415a0b07110502030034015625002120800d10034450a080080c00b074240310012001686c0291003001142e40384c1108184004045104403110080380442580c038034410701c000c002540c0301319008103510301814001400310744983c1114404d03400514459014020000c140d00c0c0c0005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 524654037 1250 524652787 524652803
    0x605060a0806040b060f031005010b0c0d211e02030106121118060c0109080708030901060b210705091804060e011404021009050a0f081c0c0b0c0c0109030309021206090703 75
    0x441d101180c205140c08c034844031800d05140021030009084400303441c4090320b0204603880051402d90880c1e01d03092a0040007603000784a00648000c051315084124581e2010303100c094001e0490701010101ea001f41c0c04180003a04031711480c0e940007a24040c60304848044100369040540b4220b190105d42082403030148100400224030444110a4104100e081d0b04940c10507101e00f064140004150300480d2404090b51030300700c01040400d03010099a22174608010380011211191151001c040ca01800d200706000040c8070001013075035250b4540d040842606400d03051402c05103090402d858406174000491703414442243c1d158070100027000c0d031103a01258541341641d2546810350b40100280c000d40d07003100c20001c000c1500c8981c5074284044800d40c00842d481c5041080482c08d039880058081c1c80012030028500000c24000082c55400c6001d040005207400c02c41c100c01d5003128080c82085002c692145110419458082e4185052500400103401945040b040782c07901c1318038502004040c80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 524655287 1250 524654037 524654059
    0x10f14060f03120403080705060907030803010b0a02071205010b190506090607170304080c0610120308060a0810140a06030c0e09010f0203040f02131a100311070605060a0806040b06 79
    0xa0760400030030700943e4100c003410f6030311501d80c10281c41681c41442c0a80320b52080342d011802403400080c4200851b504040c14500f56420011820800c0e40043c9500c030452080c041c000c10000c3c0110440550107110710000500c40352900140488240307040e80340c4800010a03201041b0f9511000b08481d2084030450b00341c0e0395002c1c0d0349009040001101e00c0680840302c0401003104104400c0300516030710701c003e01110003980c0d0b180311110080c03800c1d0084505000300e190101e40042d0092045d2504030348024030241d681c94460f1400d5141c032600200f20404a41c540340040501400020b009801c02c802110607c14903080d91070f0140c1140e00c5214088503480340e240000c40d405829400b044a020451805540e0790801d401c1108052401c2801603200350107038102408004014840c003803c4035040141a0100d40e00380080001e0040aa84258185a100e0030b051110300140b8006020040c03080f9800115828031005010058500380c2000d03165038840b90a10000c25244840141e004100b190050030003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 524656537 1250 524655287 524655289
    0x90105150d05100807080703080f03041e0510060b0423010504030c03060b090601020109030c110a1d100f06050f0702060f0307020606030c061e0702120d030b03010f14060f 75
    0x1078401c0500d0410214901001d0103d4403001a00c1c141c11590148103d8080e9526000181c2e152000391000804404040140c40030403c0c0c2d43d07000d50380c068090180b03641c5000404108920030301d4000e40403221074000c481007030082d8040f40300301e1002d80b0b1380d105101d04203820010460b43c903108068007030003096400450b8800c1a8850b0701120051076010120840290f5031b0700d40040030b0700b041c40c00c0318031600c8010005001035105102e14135102d5003581e03481002c03415036141d401031800d035030000700d0f0006000313400454440d00381074540c00c038420200950f40140c80e200c560a800c0304e0b04d40d000652500030441d001c01c00e55502c882580c421082600700f07207a0ba03000c0352000541c1b6109172108032444c07180200c00c01c10044d8000c03400502c07480054066540e012400007c02021f841100542140d008210380d0802c81c0004000280507ca803014054030803c00c1c10551061902070740c0c1011310300090b200ca411100c81e050030702400040c80110030307051020585124550740c054000404d072500500703410000c0c1d0a1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 524657787 1250 524656537 524656579
    0x10e1c0c082506020903013602011407030509040c0c081e070c03060903030c0e2d1c1a010e0601050c0a140307020f06030c04150221070506070e090105 66
    0x203403800c103030646202c8011450404042e4008a1000e8030035480c02a0b02008802c071120411507c110001e482817030752580d86a03205950110b010168101b10100f4183c4880521a4000748846400307511103a495071000d40421040c0d940c0c581100302044454001c0c2d400045910302030710410690300124101080a1240c1d0b501d06001c2e41c42c0140c850104a0400004e02c44654441005640280e03001c0c4480b5001e900309564075a5404002600124205c0703c01e100c0e1500c402407901e00d03001014552211040800c00240145110007000c0c00032181c0e50304541c00c21141c0c40d10307015149140050802d0035854454028440e48001304107a0600000042c0715804107002e106005e14641e1102c0400d414981080b00c0076a01e410980080b40258185d0201400798540002079910440044c5055850f040c10b240070401c400c410b0072030600075413040d5007012032040110521804201d4140420680305d0a0f40d0030111302d071110141c164000d0207441c54846109803211500d480c10b40380c1c2030301c40340441d00349a0080b0031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 524659037 1250 524657787 524657827
    0x1202071a0d0e0f12300f0a06060e04020904090807050c010f08130221120405030129012303160e011107051507140105040212070b0405190302060c010e1c0c08 69
    0x5c220030101c4040302211640c0311703a1031700645069241c0e072150780e1100c0040c012250036010750700101e202c6082c500001d14203900100308401d0301410202d4001916540d400054001000858090b08072403040c2405581c00002d1840000c030526054030942480100e41c89035020b8030401900420018003c00020300461500d41e0707a880b9850100d40c01d00c14100c1090005411600450b4800d50900b0305c0302d120000384252a00503044441a5a035030541400015114000c080045010760444020b202c40030f40465009907108001d5541102080803c29500900c0c181c041150070b07042c09581902502c1005c40000c800c81507440036101c010348148280780c02c441c10301680b035000702005a0078403a9041c062043d001a4016442528982c22000d5011483c43d282ca00d5801549156032045c0002c20403840c000441d044110110081c2940954894010400c01e40c483e40846070903a4452244020f41082041554680d0840815018103910f00303500040545459180c0030b06036a01c08034007070704050045001c0007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 524660287 1250 524659037 524659087
    0x2b0e060c071209350f06010e061c0c0e010e221403040f03020f0901061d21060f06060a090b030c0c0601170d0f0504031202071a0d0e0f12 60
    0x910740080d01d50030322041c0d83c5140000c1c41c43c0d0304c428104a40d1300100140d251591140ca901030141d5a00300a240c0b40f84440041c002c9506c2201409250f007499007400340d0700c1c00e40c1e0085e010800b05500340b46101d800c50106900c5030001022900400c5510a946840c1d40072800c5600002c40b000310305030405450f0744420000030f1410f4000010001150541d0140140480c0e00c00c0e14040d050750258420094415400d00c20031006c074030a4806044030040a5107801c3c0841390040401f007120924502c2517078040000d074803601183c1d0040e818841c0941c04502040e13444203080307400501c0c0c004406030041c0340070b09078403070840c0701071021000c0741e540f14001c0280c90200c281c80044413900c2da0359104101341381d00c2102c03c400172801108020044035106462400b01c07607074242c460500d06440d503940e20847c11000445c440860150700c0011800450f8041000032140841d040346448800400c000ca080b502c2e112020207a035031003106186080600425400a0905462501d540394503d01c4101403502180d04040c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 524661537 1250 524660287 524660309
    0x6010e060301090e011407020c011b0b040c06020613020109060c0201031b0c031407050c150c0f010b011202032e0b0729060f04020c032b0e060c071209 66
    0x10400310f80b1640300001d12041e4a000340241000e00c9002554402c040d0b443c1e0303005800000d90100c140d4000d40410010305050b0341a9101c55040e41c43d040290312080c0c0341129803010303450f0100724895041040301d070010304c808485501c600d140d42c0043c000c0d1145100361002d06c491000e044080d0380c0203500c0000b40000d8200351080d619082100188035440c8188118045841007407450211a92041a0380c80d4030341c88030041804c2403e04c81002020703034044003a038440c454100220001c02105002c1075505000c403500100b002000040094440c0302d00f060f001c40301510502c1086161828150411400c142c01550301c1464000c149180741005441c0d00100703280300000803010108100e242c4c002c08030000c000b030607410b50081c81c030503062105820b5400c80e41c00401484440c0e6145887d600034860940480222480c00d2044028904a0480110b590000004600c204030080540703021f41601e0182490140a039440c08000005060091030000703442510443c1300284054018140500980287c25803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 524662787 1250 524661537 524661539
    0x72a03081503071427010603181401060501120c0503060409110a06050301030c09020708070201030c020c1206010e0a110f0c01090204060b03060a080715180e010303050c0c0a150806010e060301 84
    0x400c139412400940b810303001d0461250700c80301c40d051041600320003000040503036440c1d92034048200c0203400d0765104482c1850a200307140307001030405200d241601103c1e0001040092803c4005407416401c003800e13040650400401840c0c00d03a00000701e0703034400c00c100c0f00000c5d901c08608007007413030180c203107041d035040050701c400881ea60741c001014504a83c400c40100c83d8094030b520240d8264084c0d60030080c503641042c840500198000c1d040800404907501c111001c030209800020520200005c00000d982c01c010010b208000268000640c41104c6031024440d0b840001e1888480f0302c00c0b220071807880c100105910340354103029000f02a0454000700140080d517140c5003141040c0e4001c0d10210b02c618500e000020300c0b15000b0407644103e034000350600500400c25102524601542e8061032003400250001081401e090040c1901070360290340d42688503851100d2252800c0c42c1880b2041c81688580c0701001403224024000c2c444152074640442c594640304016200080b0030204283d1103000400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 524664037 1250 524662787 524662799
    0x191d03060408040e09030f041202010c05010501060504060212121b040911030123090c18030607020a050609010b0901091a090a0b01020c010507112115072a0308150307 73
    0x60000d40d1189141300000f030703e610000d556a40301d100b11116104005101c204500541c02c0c55401006006041600039020256145030071680700b42c01071000b1030000700c1c4c1440309a50420130043e455040203002c901c4e00800c002c4102070084010220001080150000805410f032882034800418400c0340500000d589004082c00a81090107000b600b80c0c83d0100d0050f0207040594004400c0324043c0c41018561140c1449100c40c1d481a80e0b19481c0e555403c509a01e161420800b4034484c0b901c1d54041d069903209031030141d00381540608100d50a84c10b03c00c0c000b9142e5540849541101e40da40f10004228101c25940c04442c075540140340c2d8001141001c2100201080d0420070861600741e0a85101548010054416004500d800ba1805074408490361440c1015844001d010244c40e203e00050036094130f0700c901d0050180901d0400e82c20080a0000c2c00b42c22040105100400082038648101c0350341c40d004002c20210342c007404000c1c2c04000b1032251400340b0f450201103400501615026a1140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 524665287 1250 524664037 524664053
    0x90f1c0c09091119090209030a05070e0a051b0d0507030902030f0d140f04051201060e0c12070e011b02010908030a02060411010c15090c122402191d030604 68
    0xc10203403160791a8500f00b000710b03e0240340d00300d000740d40c0d180c8154801c1e00340141c05000390800e50342c00f601449009a104003041040104100600a2040303031260b602d080d1108000303440014080e01880c000c4183c18100e0820610162071303c045c0d00c08400100790762408000c0303000d0070702d000c0081d425000380790140f414124003149040301619a41c403401880b103203c9040307103218410003c411403002e400740000e0050340741c01c2880085070042980046440c54070b801c0c8442c501e03e4151541c01c5400340000f00c240081c8000c0b989181d10071500d00746171b800d0304950b0b80041c10701c041194a207448100025400011680220305070302c0504180000c40e600d85c0c03e2090040d580b250166401c0e20000c200b56064840c0350310581c901c4030001d81c091502c003481002001400090032400c04104e400324580c500105840b0070b401a103c5007680111005078400d116040e10083d5656043d01140c8014010441404e0f01c099420515a0030211443c00c10780038103000c444c03c40313030a81300108264140070b68410f0100f070102d14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 524666537 1250 524665287 524665301
    0x7030b06040b180f06090a030b0a230103060608030a0c0308131401020a270e040510110d0b04060b03160e040903050306330906091003020301150302090f1c0c09 70
    0x1340c404240b0b0302c511104000b0742d40079034002c659002003401c009100190144038043c1d004507a9410224441400500d00a4588450b1032641c80c4081e654004006018550285500814a81c0051881c08441803002010f580c101000601401209008200e030804284100403000d50031008449424141d421058084d5009000e10300001e1001003074144600a40ea0305030301c2000b03859528000c228580b25410724032004c010b00a0300d9600489032041c4c2000524005d660403a903100741c5441d0345211480050044130007045441d03009074507020007480107620340c100702d940045003418800c145000c40f00046410742c0a044000350440d081a0000c0e04058201e400b075405003a08507203459010100303203000310404045081c9091003484100c590826219480010140048040c2c40381d858505c7d03101c003140729013014160140009074004010400019815003c824074a401d1405503d0311061800044580d0b5811550603c54100c110491380c1f5001942c503055480c590110700383c0d81c510ba0b100c00410050a403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 524667787 1250 524666537 524666539
    0x403030f03110c010c09090e01022a2407030f2f07060f020705070b070b07180305061003050c010c0507090507200c0102070e070f08040c05030f0f0d020f0607030b06040b18 75
    0x104080b103201c3c0e16060090315252f0307200c0000d800e22004401100d0095962004680d551030249a11441569440743c0030440b8105e500c080410150400b000000c085800180d502d810300d510308141800005280101058221003070085a01c00e04a0144405060312071000c008100d00d00e000d901840410b11600a0008180240181c1d1541603841e140c12000340715030b00b80240385c0005000050b0240d8045c1c8102c401541041a94041854581e0b5846241c584180e07100c00c16400041c0d81041004010400c01e02040403c1c80e003c00304000f2561282d590f855075010301d2400c5600c660006210510604d0810321124080316608000060000041c0d100c07039010007001c0c014041c0d0781000c11050201e0740098041c03281603440d03d252005140c01100d0a0101920891b0b0030b8504883c0022a03503000c201d00c10032603d10700090000d001e108090b580c9001e00801c10081903402c809428110f4400202d82c46038050400e040c04204c0e4080a800107080d4031030794002c0156904049801011040950303c030f0f05800c0c02c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 524669037 1250 524667787 524667791
    0x2401081903050307030e03120f0411040b132003040804031709010903020603071707020f011b080f100302150c060a3e04090c0f050403030f03110c010c0909 68
    0x140d0300c0d000020104844006070105204002043c2000d10991040207504200ba003074a0400000a14400c0007603000e440942c8400340020038441446940482801c03030761000c0707804101c25030145005c100304045001503154550303940d080c0b1200088940c3d840404c01c0078004911541d03071505140c06004d5400500041c0c4144003184906140c0010407412510034901c161500805103142d607082080a600080c2018104010000c1c941401d81040701c00601844094000d41320004403003082070b007129000c0c00b081210602a000801e241508806800d8010f4003044203030321207a54103441301c205481c40e50f00094104110a01a0080100440180c081d0b03000d500b081c0c4401d070300d441103003030b06451820f2580c1d00350b2203400010180c4010102070810317001030300d05100c0c030800d080040c0302004c6800030790100040a44840322015055070020500c0c014215904155003451b0641d1070003044600d0b091454000c0c16650011406880701e80c80680d1079000083e402801040f40c1c040c8018000e01451103034041c4c2d0b80c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 524670287 1250 524669037 524669053
    0x6010611160e01170102030f060409110d060506121b2e02060106030516140a0e041a0301050f100509100b22080a261303050d020c010801050d020d05240108 68
    0x1c0c018002c03031f030150b4254125a03022742c0700d0004110083c10b605504894641d006880000c864454540d80041b150103403100094516040c0d003400425209070302c3c2840c0b42c2d044122500d000c0340c00741c03803a004a1003042d10001540b6a58907180049238110a080c0d00c84540c2090706050002e6000505d00c0c16161140d405100c40c0e103031000d8841800c0765142215011401e0916203003101c001a00140c1440300c1d0628000350030400d45030224040701c420301c40d0010107907440150144103003824010260400041d100711030540c50303d84560055400240a401e109116610100c0d41c025101580000540704002c00b503903036232041903215003030318030f042507801c140510105c40010240804109214099084400d11140060b034101c0d000a0f402118181881038005002c011000c011103050709001e1481400100384001324440302030f01c2d011203110740741e0412076250b0040c071451320381282d03c45007258140c03000640f0b4074540c602541007242c800d000c15050b800d503050f07007048980526070346412900ca4805031280d42e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 524671537 1250 524670287 524670329
    0x204170c01120515100e041d010e0619020705010207150b0a060e010f05090a1505071b05100f0c02032512080a08040615140906030d0206010611160e01 66
    0x180f682141d08916003000b5240403072003403c0c441e00c001c540740441d1424080780c169020024048901e40030701e004006c419410423100b0f4500900c20124511200001006185401a68204c0094060403070103882500825401d0400200350140c4604690000000340d8500c01084840010103c2a8059114a410382c400003042805901030300b030306040682d101c507101d1010920588199110352101ea820030780d840030004444c41441d400d0104095540d442c95943c2c0200c0c1044260140c035185d400d001c0620740b24040006560710180b04514515504200706c14840306107041d20801c07403101c40030790140280d40321001d49141c1e00290341c010030781c494141804652900707070f881500400351200074501303c8100320342d02803580075014803a413040c0304203404500079080d202084a0b040c215840707000440d042052401d050319080d1038540e0f01ca0740560041041140c40340d002541c40106126960501c08144040040004140002d9460b0010740c5210b10341c440d03440500030b880f201c2c240320f5042038071501503444400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 524672787 1250 524671537 524671541
    0x1815081e010b0d0b18090303240105040e07021005010e09190506040b0c04090f0b041a090402060a030b06070b1f0e0705090a0e07030f1b020703060207060204170c0112 73
    0x10303070b54003007516400c1a0342e2120002c01008051180781d13008800c0100c0b01c02c0104509410b512070300e02d0b03001440d2642440e0400c42004104294400d00020300e0f0070202510b43da020060b40c0842d00c0510703101d4000d0711542c10683c1042e820f040981641d41c01c0030000300d8004111091507005024240454903484da04001c0c0b040d4080135504000c02c0d43e0011004103020920b1a00d4040e0041031405d00c0e070f85808e03900c11440048541c0001c003e00c100b40c031a01d6200a6140c5882611542e0020000c00018101c0c0b440005044100040c0000c0c071440703000c03e81c5140244031358840c0490020182c8034a42d910441e05001100d038404441c07032928000c0000400b00c01e55180e44640301102c0d0200840340c0242c03264502030751650422551355400503e40c040c0003518003044507105015507200c0d02c0010700c10740320170030240030f9801da244100e000510703c103c101c0c14143c0c0081c1c04003c4035040071005807105d02c2460010060302c61a0701c002d00413082c4403013044c07007900082041c1c08018001d03214003943d40e5104002c102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 524674037 1250 524672787 524672789
    0x606120303140c1c0b03030c0f0106140108090d110c10030207050105070309120c02060d0903030e0c01050c0705120c03070323010911010503072708070b03161815081e01 74
    0x20240303130310544198058850300b159441c80b400174192400c201c02d2540c039518001c0c0c042d80c21991691560010000d80200e951502181d0f5400c1c078280c40c20385448011540e031030414426840400240d04ac1c140c010320b20511060380414001000300351100c08900008021350407880080d240c6500e0b02002c101c07a14003074820740a403203034003100c540030380914040300f52080040904141d030042002c0001c002c0b000514400e004000b40f0076280045c1e400c9004080360f1401c003480b02081d060280c1040710812141740002d442c1d04448040340c0625030b560300034040718200122420b80c0f07a01840358400100400c1700100310309852002c20550782840201c4900d1444c265100050080e000702c0010a001d0309552044000b182d20191070b09118031a4004000701d03c0006c13204038031005d104603000c0c0c0c2c1801224401d1050703078002d217884840d031030550904ca84203464440e046c100c4407061103482900102c00005a0a15100a0040c0450148542c0080002a0000340d044a240110b280496184407850f400041d00d54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 524675287 1250 524674037 524674057
    0x30e030a020a200d0803100b0d02071101141614070b03220f020f0d0c080105010510020a11060913060b04090c0215071209080c0d0e0a0e04020d0606120303140c 70
    0xe89081100c1c2c817498030380d80c409040c80400c06c00108001c034950f0010001803000c00c2030303c0c0005941e01700d41d08103080c81180e04022239040000c1040140c000301c0203c8140e512b040c240241d00070103040d641c5402a40c2510002039044240141c50000612500c3d06018500c40c518024000d032500c0c500f440400c2881c13820540c0144406080e18000026042100d07064034111805031000c60020410388502d1300743d00d005d41c00710000d030791514010300c17036410800a0f100c200c880354001005c110b00c040e0340307400106440c0e140d003d018400110382c03038003941d9610400150300c035075011042220a403600300ca02c60982c0240219098142032411a034021840000c080c1c100c546803009948081e1620b07035044508202072001c5050068803403d008002c504038000504040c00e00f403004041c0c0c03900314440034059202c039206a6104840c120781c2000010b9140d10403603070169044922960700d41240c07411100038402600088043c0d600c041a49040540550000c0010558000d01047c43d80d21140c40c0c20562140c8400c036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 524676537 1250 524675287 524675299
    0xa090e01031a0606160c08010c090803040e0a0228090611061503010f0c08011d01120314210a05150a03060b031014160c0206090f01030e030a020a20 65
    0x910465400c2402aa04003000604c00c3d858a1034080c0025160402c000c3d0681d10101e00c1d03441000091800d11520291918504040f4034052800090350b459020b80e2042d454003200820004060f603166604542c298088510140c003ca8043c0503e45841c201c0401c3d5070000c80c258400208006004040302e90321b0700342080003040150740b2000b4460b038104030113211a03015901d810300700703042c03490313500815191209554541007290f141c0b500b0103002d40c07841150b900040403ca0300510440302c0e0940781881c61901801c1414141c0761002c4015101c0c40f980c061004907a034103038040241c55024050103030040b1079000d4140015150420141a9203851079003299101180c0002000090f0003a00003400c0e00c28002e00b643c8048219008050580b000001c442ca981f0f42035408020b9100f81e0f004800f805450310f841d0500c44208164041503c512034509054407030140c545a4450300d80c80b90700f2034400c2994902c190b0b629200400ca02079070340e01440100b04c607100000d0f0100300a150301e54004c01d80d20344008080c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 524677787 1250 524676537 524676563
    0x109080d091505090c04050c1303080703050708070605061305090718020c0316150e07031713032f130915092415030b090118080a090e0103 61
    0x180800524090344100c2c1c8404210021140700c003a6440f40f98801d05a0401038420381a88504200849000801c0490641414002d81c00c45441203c10f04007907a13070003d01e0070f0b65580700d410140c956020b5898010400c50000855104000c0d141d00400d00844082d1842550010812201010707500c08403130b84c0307a10790700c9000100b2010705100408500c20080d400010b2070054000400e0341150700070f404107841c0500e8040c3c40c00802014102001c0e9241549038100103440d580c01c0c005485022900c03018000032555a856401821400b0459101c2004464a2928a13540749000180000440300c207042c4038a007882074108000d4031270740810110304002c01341550380710600000c000820000b00241c0d41071581c1600031807000740d98810400d906000d2044005884c03c4002c050808a12406489040703900303102e1880b000c502c504a1250079a039000e061200d160f81c43c0c0803101e0040c007140c41d14032165044000e814041c02101402009400d0643d0344861400d5200c4142c0306214500b880010124140b00407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 524679037 1250 524677787 524677807
    0xf050432071107141008070509090a0b0d0b180a0203100e011d070509010b0a0816020c04060e01090b090402100309050a12020d08070e0303040302040509010b0603091b03010908 77
    0x4031965200c00d407414410070010715800b855203007090580200c0300340580703899101400d00d400103904100700c20302c0c6040e011030b103800131005005009002c150f0f030045481d040481c00301e55254001a400d42c40183c90344007407001c6402c0166544d2000d641c01624000c803408140c00300c54010a003800d01701d80183c000e00030400ea00c1c0341c01000b061401d000b42c4855595904a080c0310302c03402c400600407461800106034450a001c104003c04a040c0d0091515200c10044408400d403c840c8841e44800d1591080d0842c000c02ca0080e801c14960b201203603070280c5028408200b0b01103840c0b10a0684080c00000c00c41819000180b00d801001914041c1d0300c04265054501001c0c444c0d04440c0b40302e44544142e0300b1100240c5d889448110300682032038096003051840215241e8403c0f0503075440310052403e11050350360748000c07a0701c82c8590700010f401349490b6030010f803c554094108280e0b00c8806000c4d150b407440d14100483e1146c800310b0000b22040e802d0b010a2025280c1401420006504082c1982c17502c07034081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 524680287 1250 524679037 524679131
    0xa1212061e0e060a0f080609300703021c0c11090408160507030b0a1409010c12230106030e071a030a09022409100504030f0b0606040f0f0504 62
    0x815280c3c2c030010001010888860422140c40140606001040c80e070030884045030411301040c070920b03403c009c10400f22803190702c0c64103030005030003030350640710340c1e69400d07050890401e043d0300b0244c0c00c11072581d101d03d031086a020009480d240c0c080c501e80019084001e0810200620503a0042c003c05c3d41800070551501c800002c280d1058424000c5034542552179603400100801143e003400d001e079403a040250310100076031020340d110050100810031030110a00c054800039000c000c5003602a51047e126180b8070740c100488001c1000d00c1c000c7c1f07100350b941d140010301038107903241441c0e4103024103800000c808001c5451002500e015003031140c1150ba5040d0307207900070000450103aa209440440820720907540851010301c0c1c0210032080c0355149542070500174844202c0b1011405c1000402c803c1020a0a13120491181c83d40b2440a00d0144c4810000030b1090145801008840415400c0010350704200c511070011601c0581d428424030349840146002c0314401640010403189a008c400701903a406 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 524681537 1250 524680287 524680291
    0xf101515050412080301030218061f05070f11010f14031302010306051009081c0507020d0c08060c0d0f02030c192106030507050d0f030806030a1212061e0e 68
    0x780341a9003403030303a94a0b01c041405038612003954807500000040c420b600b8074000004204482001604070b6092040118008062002c604840070308502003007107101e40f080c1708513120950409442c0030948c6003801c001180b255a02580781c0411890002c0818250007400c4003041210041215411603480307a4035069407080c000c1040341015503e00000c00c6a80e9032900c1a02c14180d07507640c40f0002e40c21300056602e46400070f00c0e400211003003e210305104907417100446a4150341520044a00e84035441c182035001c409070084916406100100052045500c024208003210b03010f0a0102038044448032040744800d4031440d90386042000070100600d08100c4188402c0f4991500c14444404c80070710011041c03132003204101d01a101c507010004c2c070400b008a00c016000880e010381d1904041d40d9407030300550f9200c4000f428004030400103446a5424014450925003103460304c241d980300c07a9402030502902d815100c8080c4d25150000c203494031003c3c1c212803c410a03190004940341000d03414010980c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 524682787 1250 524681537 524681579
    0x90203150117070522081c0305090a140c0402030702150703140126060c040f0b090108310f0b07080402030d030b03100e06061c02030a030c15050106020f1015 69
    0x9070f41e4620072154407038010410a0050030000a00d04072170f442410354030416404049c244410310a0b1100c001c9400300341c540d4040c891483d0144041e10042c2400c0360a20a981c0c8944044104a00980c02251840320200c480c1c401003007da55a4409600b150750540104501d000700b0001800350b034591101580420304104515100c1390a200e4420340f500a00300e4502401440c04501080780ba81080089009010034091103820f115501000a080c940000e040c070001401a00c2d07843c0d05051142200c43c0f103c0da070394011292881c210700b00b403202c48502003800ca841d00c0346940010102031007076078042c0c0036a03400ac0180041520154003100902042c13084580e16004507804900e4825881c401c407004d0b87c07076200180c06032f442c0c01401c01822000d0111803580c08186401c6580050741d0129031b0301086030307042c20401c04c0c5075058141000e1141c25022000f40c2d083c07500c000450f4558002030306901d0200d1a508841244501d4004031068421101c03030100001c180d01d070140174560300c00d40d99080d0622 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 524684037 1250 524682787 524682817
    0xf0509041b1509090216031808010c0306030c080d120b0a1d040b1f0b070f1a0a050a020f030a11130e0105190303020309100504050a0902031501170705 66
    0x11411030a105100420350090400401d82d8030001d2071141c014076074000802d1584002c60074502608000554006050030050070001901c44103031810000100300c80140c6990380003001503012504015006000380d000a4070ba68041c41030000d00000002040d1280d07081e41d94505c04200c00185c52800500700b0f0304092540301030703011000300d141c01d00d580400100a071240c080c00780034181428402d59103440a801121200301ca600710407040940301d500b40b4201c50f100c0c0d1010760f40312030390700705405101c6c1d82c034074014080c6034610081c111a1401c1c0103254040c0304c08c46000c1125031507a159410407849815081c580e070220a000054107107449500c090744074101c2e41c0c006454413207001002803d115a42d00005030522101c00103101c43d0400c81c41d6089200d1242c4143d103006410351f200a0740d68081c030230866100d403002c000c40f0352000f03120303000b80e170001c1c80050322004a480e11040900003a400849024544d180c11200c8080a076210304482c1100100b9084a11416141c0700e900310382d580c1c4120401c600140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 524685287 1250 524684037 524684063
    0xf060301060c03030f0f020a030f0515090f15060a021e03031009050901020702030109030906030b030304060c080a030603080c070503240408030408120f06100305041106181302130e010f050904 84
    0x40d0f1b1a00081201c6042c0340d400190100c0f00d964810f04590001d0b04603030070020804c200c8040c1c1c0c2c481030740a82d0042002d01c0b00c55050754031300c2076125078001c400c0f00ca660040d40106151f0301d116000150344d8000b10002d078089081240071441950b4902040b00d21040084206100700a42e1446074015600256100009882c0c40d5076500030909503040140304070001001007500f004040c0e403520810b03030303a42022009545007910b00400180780d80040748020380307068000a8920303070250103640f05400440d400701995454544040886413035404a1103950301034052541880358185a55582d004480d0301d410310111140c03165110841d550b04020302c12180c6e4031007002200c40000661044601c204a40b06480c041d034940081403280c5581c2112101e41414107080c148400200040501d241c03103481910059211207075204c0c103032101c08446603011b81180340001110b2800f00282c004103c0403442201e0040103e40d03400b10000642e50900c944607481c400440305002d0340c5815040103800c240120303460700c085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 524686537 1250 524685287 524685311
    0x10e060c0a0305070218150111011508240c040b031b04030501091401021c0507090b040f090e0d02031c0f0216030f0306030f0f0812090303060f060301060c03030f 71
    0x5428002e60205202060b00c4046141040401d0036040385000940807600b041c0a00c41c8415540040e09818002140c501c0c1071400c400f5800362031f000c040303038640101c11503640340c000e900d0b00298803103031441d61880b4000f2080034201054441c0120703880052689090b1406501413003a40019000a030040c0ca1006800c06610804014101460190b000002c214a1391706d04114020080300c09101140d0046c89207140c600c1c2102801e88050100300004250f03595402021203240c5000d4025142040010034003107604010000700c4401c0c1c0e030302254100003a96024071182e9891111740c4286005900402410f01008110507000162207612071700414020f46490051044e80c0002140c2161080c0038011001456805920407003c0c0920742010030020b82181c039602d0403440c000c00040c000d0134161546500308582e01044415180a5a180001d1b501306134003100e480780e0040c0c80039842680e001c1c500680615212044a040301d03075070303100d0034048011030f82c3c01ea015012540128141c41da5031b01600f061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 524687787 1250 524686537 524686543
    0xb0c0705060c070608011d0612010b1003060302091315020d020405040e0309010801062f3d021908100513021e040b0f031f030b090d031109010e060c 65
    0xc0d00b8006025105640c18850000d1200005a0040c07180280c5110f4a01d19122911070f12a0070460590381001c0382604201320f81c0c003421504039103c0e0000c40704030201c0d4415038140e1040c415a4800c40d00c0d4016a1502051207038950102c0b00050140080c000c000444011250300400c01c01d40c0d600d4001d4201903454001408503800d5603580e18403600700080c07a441d9581d2040d81c0c2d5000d09001d04000d120a405040c03e0207008032080a4011000301da00511421030204112150b4940c908014502012800c80c0c0d1100500442d605c8007482c0004010001c9403422160013514581c0c2c0003030b03c002018000c0c1da841181c00d500003602c800040d513540200800c0715100d00d80401a400102d580160b40c88a0300e01c94010003c894000c0c44407a04130134042482a4804941201c501ca02410141d0380c0b00d8444542d04200841c50f46c1c030b0a40d02042c1007800001300040c2c441c0092007011080c09507107220006108c1039069600840d10090850810002c465441d07004800858026801130809414400003c140c0c1d45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 524689037 1250 524687787 524687797
    0x90812040302010e060a02030a0e070b160c0e0a0915050c07031b0204050c0c0d0e1005090111010c0c03030b01020c0d080d020c072303030c060a091e0f0302011b090b0c070506 76
    0x200c207d800000300700000c03c6d136015420600380b203c00140046403400752840c0300d0f401101001040403a1408840707080c00b443c0360381c0c90003811018105800e103061488500c0c00074003207884112511014644c0c000380d000d06034842d40b84136001c118801071910030f003a90122030621011001a100110a10114003d611a0700c901880f03500ca203c8240c0ea90110b56088070b107803500b0805440c08012018030502c009445205420b06414544e0510342e4844004500581c0d030411201ca2000c0150f28090030740c20980c0c1c0c00b4900000315800b90f103082100b0313001c000049031508100811a500000f40081d0030700001c1c190300081c4620b480040e801800c0001482019091001d50340c820800c684202d84000092014044200c2c180c9004034011890170029884180d2600360003447c1d40c0590f644c510107074080c810040310050018000e502c40442c182d0051510001052a00344140c00562070182d60306010400c0c513110303800c5415640c90b6441c000d450300c1d665002c258466017443d50f00b8007499400140d03175262000549 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 524690287 1250 524689037 524689051
    0x9070303080114060403080a03110a0203090a0504091109040201050c010f1401300512030403230301060203071e1a0420151602220b04090812040302010e06 68
    0x1050061860900800744181038001c060501a9150802c1040e039401080b00d003107d0b4071200054031100001016001400d1300d881c9800d085000150a100695003c00100100e200850300343c941e594580d401d1004581500d0002030125a84000144043c5002c2c039601c0c0d4010f10504d0494030309400c1003002c50a6441040381141c0300350300d80540001c60351001420038050b26580350400d0300f4030490340d0840302c040409034800c3d20030600f80c00302e034051100034400c2c0c0f0710306a1000c400f1540c1e030606142c01000e40281b4242500c0d0400d90494118440d4010307000c9074100ea10b00d5000314203000c00d41c0c6130f040840280420145582e107105103120002075403002c2d280002c62011b0a03a10341442c007401d1991100020041213099910241c0c900b000568603400305e02500d101c0c04109a0b01d03141008400000b040d81214084d501c5421038114506d070042e400d5801510340c003088800c1c0300c0c0b370000d44184000d480c003a2900501d0080b0130300441e42060324980079150b210317009100108110741006a99420104207940b51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 524691537 1250 524690287 524690293
    0x16020d02030106050406120b0609060a0303080c16030e040509070f0b0a0c02030a120810061704020d150c020f0106030c0302010810090f05041109070206010e270c0103060506070c09051e09 82
    0x207814030840c942400d51002c9c040e5041600e51600c04005410004c490100400740038084000c030300c01180b0346084d121428403141141c850300c1e1481c00c019042c6d882e200490303841242460006122804042242d400b207600c40c118105e071040c20001c2d88a42038001d05461800c200100700070001681d403c000c1e611016001c2c44039401d124001c080000c058500040036216540c40c840000c0010a034400b441c440e03100003003c0402a507403a50f02c006000c01c0c44001e80904071810341e041c00425010150701600e03103900d0507000c480742440a800e00600b038445620010300180203451041026500a5040302e40c08629450140c500546a800a50480e00040c4242501541d11410402004800d030f0b00d9001c40c100c01c9440e00c8480c64285d100a56403141401490f10701005d1034049181c0780301c09002c00002d5250644880f260ec3c074011403030350703a8030400c0711818002802e01c0c1000841c0c0c02c15804444d909900008a41c00960404411002030800a00030015030928000b840880c004540c00c400c0c01160200c0203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 524692787 1250 524691537 524691569
    0x1b1606110c03120c0d17060d020103091a150406060e130603080406090303082211010201200904050a0203190b011814030c03030906070b06030c030a0c170316020d02030106050406 78
    0x481481c11200026010500480c040e46ca00d94507800048154071080031607d0502c2034103140b004038007400c0c41e40001403a0b111403882c0321880b1003110b03a4041c80344089400100c2101c20140c10007040d03c059202e08808a83d0783e0f080b02c040c0341050b450380a6401c400d80000707d122540c80d6185a45035001c0c0c3e00c00e43c00a46031810500c20107601500c0300b904130f104201c140e65040418111580409800a070007050700f145075040344003d174000e4002202508800001541d1090440f904500b60741c02141901e21462034100042c0c0032950074030a03030380681070300444000003400c1d4246c40c1000741810260b0a0502c500e21281340381e07900c4c0203603400014050286100d800c21a05c4c0051624010080b1002840b0340c0090092900544407882902d8405800c200810751907110040400d040c441c5c40c0c03040e250140102a0b400b0305200300c4c02c0044085900c1010040c2d5214032401d000703034030390044039180d915000f891040480980f400c0f000240200380002c0000950b07a68660018084a0007584104000060010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 524694037 1250 524692787 524692807
    0x120e070f0e0f01051e19090509030a0216080a080a090e07030b0f040507140904020c061e0f0403050403120219031d03120d090c03080f1b1606110c0312 66
    0xb040e035004150035101029407a801440b094020031a0301c14440c0138211859a112908002c846c3c54002428007010810107401c0c01180b140c0c61b0b9000c8011000903110307403000b0f403210b0055400501c0c1125035020292003446095920400140e204071448000c02c1410303100811010301c90501c032805201c9030303200000d100d40b141c001e020300070350710040c0a4404d902d000100709245030441c500c00707202903540304180c0e9903010070301c0014020b014030400300d08a840ba4008011041d81c5aa440500b0145c1131050010300d56200b255484008034102c500070000303881400104005180c2c1009a0f0802e081d41c01501d202c0f07a000c414051441062807016800203c10050b00400500708040e24076482c40300b68042e02c981c1d0001c80080c8028899a1409042695a81216400d00401c0c8003000046d40e8007004103a0303502e5440465081c1c603002031321108040351942d1992010f0b440d00098a016400128800301412803030034000b40d44100d001094044c26028100e1120b0f01503400f400103460a080105500d42c035000101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 524695287 1250 524694037 524694061
    0x30506060c07061e031530060606030b120c0d020612041b062a0204150303090302090c0405010f08040501060b0a090f050306040309090b060d050f1b0901120e070f0e 72
    0x100403c207242c03034103031b25111000300920920140c80203001c081344420800488001c90084401d400f07002c00343e04044010400c40f1680010080301c800d590705100101c0040b00700a1940400e59600030321b0340c0b006200884d039040840144000364001086181400c2c40f144900c42c500344c0403201200d40c2400480b80c0c0c5605004441036501900461030002422051201901c40442480401c00240e250307110030361045613190780010000e888000f6540c0c5505d0754a01d0050199071960100f00d1183c2500000115081a502c003560101d0b00160342e489414000c8a500362039070900a0400e8a9a5417544070104e002800314004000380140b650321800018034180340b01d407400d0302d1034106502c039400410070320000c80d0f444882a02a1619000001500042040052100c0c0300c0e40001da0a45428101001400d0340c0308107040b4445c03504240d14036080c421000c1401c915104000c0303e240450140340d00e00741180543d90150301c0c1e1495080480b80d1042e1100100c0e90040c440b0f0344404901e5501070108102c4604003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 524696537 1250 524695287 524695337
    0x60d17030406360f0c0611010c020a020d0b060d020a1806050a030f08130503010501060c061b120903090b030c0c120f0f1c0e010c14090a0303030506060c0706 69
    0x20a815520010395104980308207042da00440d650007811400d04107000d031400f409268940d0181104585c95512507018102a81450600040e54644a2114089c500101e106c58059034010301c0d4603031807070b481e40d60821000c00180815400c044d58048204c016100c01c1400740c098041281c0f02600d00c401b0856080545210303402090041c01d400300208001501c0c50507402a00c0c5d882103009855040c030015011040141c5c0d403050340d1640c2028000107402da000054030b01014000d40701801106002c8040b420f07c1604040103d002039003007101220640340540c480400c02e4441d01c3e1290b100c5d0799844460400343c10039202c8012120780058060421803040004900e08408920500d04004841d41040164010101424000c0d00c0c0021507141603000300d4840b01044110060030028242024441c0380200703958201c0202040c81c0010001040303001c45d0540c0d0351070700d006018120313890031503804501030000500143c0d00901c051084084403601440000050003080d074821030b0500940200c84464000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 524697787 1250 524696537 524696561
    0x2150601030504050a050d21060e07031e1109102309060403080d02180d05100f0608060a0e100614191a0a1b0f230a140d020f070e060d17030406 63
    0x500f02d010000040302c0d0ae02d081d0b025515083c00034149101400d41d84015410851655199140c42d80000320281d2002c00740c0141c82059a06580c4545d0b281c4056070040311307802000026080c1124280c00200c420310007803500f240702030403039810070303a40b50395802d0f4541023a4001e00c3c499801090710940d9003400b507002d88030350400f283c641c54035280b903890711a03d40e00200e81200d0030a4446c10700c260b4840345508200c0090007400c02b01d502c2d80c07a00c00181d00c018a882c1c002c0c2c441600401502041c5420740e40110400c3e0b40d03141c1c8803600c2816051040040c0707480904a5942c6d040400c00e0001603241080044003040100c031001540c1e203104503600100002254460700c00d40700380014a04022901c0340d06040516503205200d1648503002180492406420303106122440c4200d031251010403410704c9800021840c8070301100d8280c080d10300160384401c504d500c0b031140360788095400c000740b01d11040303201d81040002c0c0c940540011039844251400100d210803840c8030b003001060108110880c4210440f0b011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 524699037 1250 524697787 524697791
    0x10e010c02070608010605070c150809060f0c0a0c060f0603080403030e0603041703090c0909010212010506030402010f080703020903030a0525241b0306031202150601030504050a050d21 81
    0x3c1402c4000c0c0c60b00e4410b0044600b08040401e52808210000c1062409060006030490980e14000d200500c07101c811148020180a0000440c109030300c0541c0b5940164a01203041c0e041c452404021100c0101c05641540d03c1e50721400882294030f0320340b160b10051802040d03101d60f203900b14100034007c1665100e86030b008920410400002c02d88041c2d00352451404a0b032803030707034079111100034a25000a810489602070013000034044045015801846032a040078a5407c0c20307070743c0b0410800f941c041124080e011a21000034604090f1141481e60f0f4098000c1c140181404a200040b170302d035410602041c00810000944240000b240f0b00107002c8903203451442c01075200342603940c3d40c1d5988503003c5c511860510302c861102c0c500071541042c4219a20200c920141c060241d5005024007050b102c2030318040311003100c05981c144003089040d07145102030301c0c9508646130130740114004c2c00000c20540b541d0050204000c0018800d100d5850b00144039035540981c15009030f401e55011850b41c0341000168 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 524700287 1250 524699037 524699039
    0x306071701090c030e01060f082b050717030f010e06060a14030c040e090307020a0b07080324040518010615090e04060e0a030915030911120f0f010e010c0207 69
    0x54121000c03141035411005000c5641a4070f54015030240ca08940e6080303895091440110303010940070f2411084075440e40850f000c5200c244112004c0c0e01c00310320054413a040c001c4081051398007410050540780e1040054154100c00342c0c0e0700d54407682041c0c40c048083d1041c64010410356030129a074642000c0212034a48ca45140307402c2c060f101425a101a00c1004c0380800082c0c400c01c07480040d01d0007401840301524251400c20b40194482c0c1c0aa041284103201e403003c04034000e0700c58070948001650104103d03207551164041c03e1800c0c165142c0c012001c0c0c00d4460300383e14a88072030050b170740210800c20784c0c01548110400803500b9120b6607000040900c01e281c07e1400c0c1c01794045404022101b080d010503405440320308007070000c0c028840300a6020722031070504504040c3d001140780111940a008540c80c0c00b00c22104509849007001c002e000c40c803084100d50b070703940b6103a0441403140884004031281904221b0304541040c00c1180b01c28451b9668040219044200780513005184801e803010302405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 524701537 1250 524700287 524700317
    0x50c011115040c050a0b0c010f090206120a0219031b1e050c01060b040807060e090c0403032f0703051e1203040303111305041802010503130614070e030607 68
    0x1c60006140e03040454180000c20709108a625120001e400e015040c103114586808007071696500201c08504603600e0b005e0466070149452248040041c1e00602e20b614008105001d61601d01c4060100140d8580c2003008070003421841180c012100c6031a01c002c620341c00c03400c03400c001101e0105039107001d02071a82d40100102c00380d4120780c10354012504003142c9400240c04c0d86401840240c10911060500040111358600300081030012503150b40c2c1d41641000c1924188241400180d4022411355001d002c2400002d0003264104000c20003840c142040210305400856070120410b1100c01c40e401c68502072050080500c80940e4100d00b810440005031000303406d0b140c0e01d41c2701561100260201201040802d4880e42140c404004000c000c6034440964420140400350349200e031078800d41c03030f1021209a00c0c009407549050940c05071141303400c542c2c60400b8500e03605042c0b402101d249036a845d1160032000c0c0307050104c0c02078a180d510b21405450704000c0c1407a014024205e00c3c107024130180c038003290b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 524702787 1250 524701537 524701543
    0xc0201060b1c1803030615180306020c0115030606080708061005010e03030f0f0901030c02010c0c02060a0e2106070c0b01030f02130f0b0f0a05010503040204200a0309050c0111 77
    0x10031074000b181c4021050214004010403621981c03641c01e5941541070014076516401ca40141d803001c0c0d94000f03d0b4040e0501c20b41b04800c10744051800c02a0f00b5030200f0100303c10783c1c0070300950b50480e8004110002d60600a00e2a100700750411500b103070385da440030320100c41d04010740b401134070182c001407a031800c10a800c81d003040da00b031003014104844000384610700d0f1000e0090740d500c01100950141c4030800703491508010342080710704a001a04d441182d0102c94814091074125010a4542130300685e069002e002e80c9600c003036031500038040d0b00c1c030001c00d49888440a500240c141c0e1215030b070141034880d510701c1c200b0b64090401e4040041c0c841003000880c5541341c3d03280c11a80d00c070001c40e030303035080034804507a08100b42c0340607400d072520305500814800c0c40e43e0070843d404001225503d460400304002c00c422004903014583c00200140002401810070741d20044003a00594164180304090000c1d041007035005410817400661103241038000c0090400040c1d10050003404e140031084501102d680c3c5d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 524704037 1250 524702787 524702797
    0xe0702060f430c0c12030e03100e06070f0503040b071b060204140901030b0a0207060b0d0b0906400f05030418061a091206090313080102091c06060801140a0c0201060b 73
    0x5031709000d41d04842094050100000d04080160940b4003868410101000070704440400c1c100c140100d20004034240c0c412008590020401d403036032800c51b05c42d5282ca0030100c40090980c01070142d424152849021941034041100d17100320005039549040c00701894000c0341c6000020b01480d017140c0140700007011840d0746684401b85a400686842603030800c40e001e828034800b142d1300a0700d143c10510501c0104080d0a11590b420011900d035a151180c07040c0486030900f92408200e810180380c60854a0101e18801601c0c924001070418205181c0f6011622030311080103c80c180e000090802200340740c0005100710b600180c504010340d40c0b03403442c2100c1141121140600c140c000059212507541e462248105034441141250a5840d0100040b50780c1e6004150b80d406444441c2000100300f58140215540c0c000e01404d64107040500102c640700404040b1400c0f940d242c2c50b5030011448007024032a40c804071190107864440c42c1010f098090448801228400859040c0311080c880c803442542110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 524705287 1250 524704037 524704049
    0xa0b0a170c2e03091b0306050906071223070207060f05040501090504051f03030504180b0d0b060d0501020a0804020a0608060306010513020409180c0e0702060f430c0c 73
    0xd91650100b408600901d0001d01c000c3c00b15501032150218000c003400c07420280c80c0705400801454a030705d2521551810100c0b081d4001030209103030310707511840700e410501c0f101c209003141521000c1e801281300d4a01004907820401640051b400300b00055002410480300d07580f6040c241d14003401c10000034250720b0940600390081c2c1d1282c01042155030200790b03041b135900080e0180c42c1026200d240040079035009208040402a001c84035000e00030007403203034003c0844010700c124101003141e560003000c00001003a1a502144211041010070000c0c001000c450b5080d5445106900e4103204001028600360030500411a00c10200f203a01e46000560a0550750300300c415040380000003071810040d00c11a0480c00701c05040620a8001c001200c80401c0520301c500034170141240c0b5800902d070701d46030450701031005902001c08903a00f513800d4407505401821031800101105803801d4802000c0300030703d014205a003200001c1101c14403107400700c810501041d00c1c0444982070651100c000143c8a40210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 524706537 1250 524705287 524705359
    0x603100603200a03090203160f050f01030e0304060f1206212301061706090303040b07030b100c02030f0c0d02131b17010503030304030f080a0b0a170c 66
    0x1500c0d0b442c400200329004a444200d41aa20a0421070040140000b100c0882c0603220701c44105040d5908041c00340140d400310703400c100001c6c1c941020407521800c04c07440b05040c141e40f002480c1a4400034002040600a2921800e00b4001c0c1d2403002000058000711080300e4619003207040c0480443d28651009200504810003d8124141024505456000da0000710110303486224401e910041d000001100c44c0c4088204a800707800c2e00181c1c0b03880044030010901c2d0020000640050341801d0500d0b0081180d10b00064404211070125200d1020100048041040e0705206400c500c0c08202681d6010310f001c02a041420505d004618104120b010082c821010641040401d0760140c0c0304141c7c0318040e11110600c00040c800c0600711201c402c900421602103100080340703034100003080b2030141e5816980c0011404280908440c00000907210002164440c4050f821075640c0350b440c0c802902001071a5070001d144555400c5c900700054100c50700030f2413407144540b86c00000304404501c0f202c00402c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 524707787 1250 524706537 524706551
    0xb1c0c120e12031501080a06060206060d06150b030a0b4005070305090d110316110a0305030d0b031b061c090f020405130b01090b01090902270603100603 67
    0x80d5410320001c41c80c69106101d0100c1000781081d1040c1441e100d01300e0a07200c0182c03030745030f0141d03d005944041c000c074000b42c1d10210208406050440119013280d00a000c002070302c80d240350480610103155804200032090220034000001c15500c00d1075440e9400312140324290003155142852503003002c840d54609200401014840c40791004824000504548108001e00e00980043d0091005860b00400b500c220442100c1e81e070700812010150300000d000940c14810004c0031f0440300500120b0440b101401e52a50318282d031101c0104001440c4220055500d802c2000000310807515070700105842a840102040303104003851006410441081c2c4071103a9500e04000e095114469070711007240018038040018051001c0700288400c0c1e10300c00c44060085032034400c5010711528070f02c032000d03080e040c240004109401c21640445010941814411507240c0e45010304422a0402500411540d03041135070742c00101003140118811003c00c941c11411410004070400c050701d41d90140805055640035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 524709037 1250 524707787 524707811
    0x101b0f0e0d020609010512040606080606030312190f090b06040f14270d08010302150c03220b040b1308010603030503160903140d0f0807020d08060f04060b1c0c12 71
    0x108845004047d0000e001c02d9080518042c4d005082034490b4078131034002e00010035040d01d000300803034203516559141d002d055126151112003a452017039040d028182c0d51f0f2140b00c040c0e0000d000e540e00d4180610031035030461400d1804d01054444c1643d00303689a42c906250800c1a008100b00c02da0072200703401040300402c110801122103204440040007180c86501c020b112000c2e070004509050380c2c401c0e9283d80c50036080000d44031003805010315007030310703a00213100c50460800c1d0500c800410342c4e0401d10308510285c1e01d0703540d8046980720350031400c2100780000d040501066035000e218001d20420008101552458400600030700024003e9507002c181c043c2c3d8490114810402d21002c1c50300040c01440701e1110110043c0d0b6052128500d90111b41d8005100851324040c0c941d0030f2051256801800c7c0c00c00c603045045a11140040c1040d600c005410940550303a02c41340714050140c4103c282c0180c1e110100e1103480c0c070320520802000380300740c2405a428103556010708010f00b1406242c10109940050403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 524710287 1250 524709037 524709047
    0x60602100f0f020408030a110a03080f04032307020301060807140d060608010c050d0c1713060612050106171615030b090a15060206010b1803101b0f0e0d02060901 71
    0xd01500030302c0f0b00100e0041a04030001c40241044840d540312121001d00340f9050380d8507214404000350100e0f48034800114044030050f62507902038428900780700440100c85500c24041e5111000e07101000c070100c0d42604508007440b898025080940082030554601010000143c0e100b0102c5c40c02540030f1b0301a607007088100c0c0c010001900202d40288641030052070010466003008030082a96400c0010a8550602441b0102c1d40c4990310780c001d041c1990b80c80d40320f214140910004959155440b1000611085003600504d11f1910480004c640c452a002c400c2c1601c1007281c0c0b1810b45900141c11203643c80740b06408440440e03441c1c0c000c68403200000c41e0242c00900da601881e0342c1040020040181d407240951007034403030f0313510040a505210303110355040b0703511070b0b09000340120070b202007183c9941c507083c01b810000c02050040444068144591040084d80c402c19400d105240c4080c0050a442e5008071003055071280520b450b05d0000c0950000a031141024040640244030005549055900c41c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 524711537 1250 524710287 524710301
    0x90503092106010b07021302120703020a0509090903090315010b03160306050418060606030207020117060d020a03050105040302010c0c0210030e01060902070b0108060601020340031b09060602100f 86
    0x1e080d00c00c42e40c0e440c03200740080d6100d954201e1041c03a107510000c02800492090f140960880c040c445015a9412401e400a6112403200ca05000c2c0c240183c5070540e464528207881151010040c54035600944207162034000340f403289881c17000d003802c0180408080b00c004e495010a05c510f400b2840e00c00c05c2d00c16002440303560407003900507007006041d03205000c1617050040c0d07540c45400100704080d6070f044100c049020307041c402400a40f20b4048034001d0042855280d42211000b4030306002205158002002c108042d4030864080c2d444500700020f1540a06c2140c04d04692410031540d50581a400141082070761b03031011045c19660710210202c01425480880900344407201156601312a062050b80342c0c00900c00d501407446542d0005040e0f520200a40d03c00914090010391641d0079451300418000e0344200b00d108800e045810902e441e0301c04080d4200a60158020740c9486860703a07520925800244c20903140c042c20144100300095001890a42c895034080300000c8201214030240050541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 524712787 1250 524711537 524711599
    0x60b030108030a02070e07091215050403020d02060604050f060108090708030a020f070f030c05060304030c061d190c0b0d0603080703092c160c050d1d030109050309 72
    0x10210001c211020008002d000d0203145400300c2e1102503444202c2907111408561280018920210402902440410020ba041d100e82040d4040e01c01011040040340e408850690059001c1c2010306003640d018003071301750446000d0f0350070b00c00c918000c80070440d4a10050403290402001d800000c0e8400000e200d98809001103206a80c1d03500300b1800c00941c4c40106128a0300140a5100300184440c0785910a1084a910007081501a86031000300150394000800c290107000350912a80000742440c4101c0c1010f0850b0341129600007220480341d40707070040c4a0181d201e400104402e2030080703042c074080d03001107a40c25400c09136074101649411014010552004005070340c0401c00004058105c0c0103030094802651141600410060b00362881d0032104030120030542140011855004c1400866401d402c21400c00ca1070b08506952513516107014400d5800000d1102c03035a01c0301c212a120a1941e4124040300280701414554a03020f859110300354480384113154a1001000040e943d01c01500780d001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 524714037 1250 524712787 524712809
    0x8120a020c180712050f011403030d11031602150a0506040b1302030405010b0a0b0a180b0304050f01050106020c0109141203070b070e0d0503310f030501150320010306 73
    0x1c150402c0205192003640c9100206100e400c413030100444078410b40348503c81e08400f001a90b468450000700e02d000f6085865090b000c20402d12980e42c560f40610700d0f50410310015141c0d44d1511246100e800c80d800c0c4040c00454201200d080c0c0d40381e05e4403560315002220091300080d140c031a06c00140081c800c001445410a4145c1c0100c1c5c0007002d55400746105901480003440809003d00c20000300121500503a681d81405115176800030b482101c4100010555550f0003030007544949032061990412617045a55034009503103202005e00c280941401404540020841c0c42d840400180c00d005682c045e40603812020003e0a50603174403c030f2030036075444043e000c2d0baa603204203091200d400c4c90120303030580209107a18040c103034030705015020094040d0040061170a0011110801c54500382004c840130b010910400a40c0c0c0205803420006c000f410f40c203404508080c40c52900509440c07002480c803030a034007607280070000b05a404034400450701d034081003030303d0f000748440040c1d0040215801c40e483c4d1007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 524715287 1250 524714037 524714059
    0x41b1e091803050a082a070213090803040b0907050909010b030d0f090e0402030c04091401050f1b03070908030a020a0b0a0b03030304080715020316020c03011a0409050a12020304061808120a020c 85
    0x80406c03008007041e034001c0d542540194201f03181c0307800340d42403160b0042c1042c404100040215003800c0c20b4a0300022060107464107199a4800900420006d40e68000240d5481d0000d0401d80f07003c0041c00390446080c1045004103600482c0a0a048260311404c4d0f803030f01030f070f50000d4110741d010311264400340340c002c004000c401c0301030404082c01c0c1c0e0754481e03182c01e81d0318040201d01c0c1c0584000d201c1d07102cbda40722040ca4208020390401000300d50030140a0382e041c000c0c41040416040400d002030007908519600411040400f030502c00e40004010f0440940585440e154002d107403070102c11282d1050b041103800b9901c15440c944240040010007400c1d200602c088282f1110803400d006985075070b07040390b00b20b802241c668809c141c00c8801803c001d0340c85c8812560100380394100740d001030301c0150280c421396000690684401402038001084040160000901404500e0300214209040e4040ca40e106509904003d403030b5980d40c0141a80000e02c203008940305007801e10030000041212400f80c0714030030310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 524716537 1250 524715287 524715361
    0x20a08030f01030b240409230d02010b061c0203070c060204030809010e090609061005090a1706010816061404030213050105030f0312041b1e091803050a08 68
    0x508080c00101d80034080341340403400900796010f10a10314035001918603034070b0039150304200080880b032400322200201c1e88040b40744101c0f0051000e040040c00c1c070150251072250b001c001d08554151401610651013801950f0009079140c0f000c0340032000c40d410060352511801c2c01a20616140400242400c0c0005408000c100c52203018001c510000c1c1c03900d0003c0f06c0880c007009400c040458415030007140e1140000c07549d140a0004000040d01d07801c003140b8049102d0007080b65a40c0c00d410a8581170940300c400e4446081c00c110003801402c0b094094100341680b15031910344080c00b8818001001000c1c0e070b4541d84008418115002950b004002c40f50344c0b0088048000505024890944a0b020365031524848003004001c80f001072158181c0300710036580d1940d5214100c0c9000e09041584050f00d98082200c801c1d0101a000e15601c228424404603e00150441525078203a15014a45010005800061707001001d0741e012a480f401c25400c9a0f440010400e80051808a501c104040c5030501e480b44c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 524717787 1250 524716537 524716561
    0x605040503011413110a05122103040f3201140709080a141c091503200307120c03020409110306010504060f020a1a01150f020601060e01020a0803 64
    0x440d042a802031107451034503441c403003c1940840e896a248144144100b0006101c6200e0751605000200071000858603240821000751a502e40b86030715500450301100d54076442546550000c40c0c0e003c0c0ca61843c0b40c144d503403620404003840c0c028245400d00d00c0d804210f60002c01510700000c0480b141a40080100c0c21881c06083d491490841004c060008914018801d0300c99000740c81458000f848000d845a13114012541080f110ad0351501900280c485428254402c650814001c3d90310701900e0343c02d107182c1030400701c5425824401c1c90f150011585040c1035100720240b204110343d04080c0c880d0344a02c010ba407030805070046003050b103251144d150400ca4042c0e01800130780d500250100032441d40310001c1c0c41c180c442a80c0060100f0800c2c4400c009442c4180480b8840100c1841503501d031402c07582d034081c0c281094050304064101e00fa80140500c3c10b00d02039512041040c4d1074101010390382804065103848043c060b020401c09403600d40592a4020000c104114bc0e0003101e09580e85400d1026245c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 524719037 1250 524717787 524717789
    0xb060d09120c0206090111190506040308150906040c1b0302071401051201050607081902030918070c020f150f07060c020708152508040201020d092d050307060504 71
    0x8281052030001d809942c4140e0280109035070260040d40740c10314140054502c0c130b0190101191a104000320400c0000754180f42402042c030920003009542050703c0d0181581200424401c1900b0701c80c440b0603410343e22400e42541000054400150054080d00300f20380e030303001c1e2041c9452503440710014041019400101c0c901103480480c540031540c20070500450300341c403540c850070035295618001030066140207001001c0c0030380b05151640c070f444102d2404000d00c450000b0103501603040800c48100a09007040307850410000c0c1400c480e0f80b8a4981005407100542e0f40d806801480d80800c6481282c07142107803000c48141407001540c542107038880440ba682d1001c0d1049862030b0500000000c5a800024101d046e0350160002c2c040d616a900c0301181c40082c010b181ca041c02d01000d00148440c04030040c11124101141e685001c0d5140a000188c40d09050b1032511003044041e0b00100554016168130086190000c00b82c60400303441d1080b904d0a5100942206a141c0229100080d0842c3c0100c0100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524720287 1250 524719037 524719043
    0x20604030206010b1231030e03070e060d060b01020f0a0c030c06020624010210020307030c08091c030213080d1806140306010e010c051b19060f080a0b060d09 69
    0x2d8440d0780c03901079185103405505000c103808219903020030085202220003128030f100b08013005030200080600c0e40004101560250045054109411070605040c40881c001c1c00c9500c02004040c2400d001203403140c2d8840c10054005683d460b55000c4e20b83c07003072010703c0008031440100c1c1c114a019060400c1c2c0f1100c903102c112003400c0c035161b00060031030010600c10300c5014003542400c102e00c001303491901c4003181d6101d036504500404c410000310719441d1001c3d5016a0082d907000524a0030390001801030b100241c042d400b01d500c10803c0351104090115070ba10402c41c0d40c900540c03240207400b0b15648440c0c240d000391601d0302031038100c0724106038050188020042c828290404241d030b54581910070410300080d2a20302002003000442c00d500441030707020079601c1072504d00c1b88142c443c1c60b400d050498580043d01d030311081e103803230b41e6007440c00400b4985050340390b0380b03c032801d0703460070501038265600c030034401c014050b0301e000080c4110070640c443d45c80000c016007015524516105442c2c01004003034012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524721537 1250 524720287 524720293
    0xf1104180f05090601060c08071745010e0409050a02190303020a29090d031104050607020d080408030d050a060806100e1008030d0209090115080109050403030216030206040302 77
    0x4054901e0034054180510329039006026542d0070000102d4211034000d000740c0380403002700b00000004d000c98080c40c0c0107080800703003d40c9a00c90904420041c1d950340c41c0c142c0c00e81a4181e01a14035110804520f100d00c021130341d42e003100441e006c0040c1e42d441180c0800c1d50740545060b066609001380070964600d1140300f1528070505888146040c1c5050703a1a000280040e800341030803200055070078240aa5a114400164071f226a6005203228402c504540c0c20503075130843c0c00500c5171190180540614110030380750711410182850f0106905015040d0007034412400d400c030000a1082c01011640900204d0003600d40e180102c00065016000c03e450702114185080c03000542c80c24041401340c0510f100c0212601924a010264840b24134090200c1620780401c450010310400c003000280070002c4035400150300c40b0710003c02c01c10300d00d82c16800810102540152140280da0002449056070135044001030b8640340e07410120020b004205143c41d42c940c4a00600088c190001003191180d03100b0350032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524722787 1250 524721537 524721551
    0x71a06131416050f0403081602092809080915070506160909050603030d0b28051905061b0a02130e010507050c03070305070218010605030a0b09190f110418 68
    0x1040b50940300e00000303004c83e0f40e0240000d03c0010a41002020010804c411001107a401a000540e1081c410b96118180d01c1481c405041c8001c010006048a80d0070030034100900407481d00d880250340705030f0307010610035204206005540f912500135a40c2c5260403e00f00c400b1840d0010540a2062a4800b400c000c9000404000307124181801240c1c428003024000e1820302c04a1880f8102920710300c190941e100c000c91480c130030310300ca000700003007200242d84005c0c020301d0380307404c09011f01070920340e0341000e0003800d90a0a00880d00d9030403c80e50584203140f05503031100303042540a8148000c41e14001d504c144201c24510207070740b2a80040d0b521200b144001c00c0a0740340e1800560b250712510034610410780081c40075202090180c03010f40500741c00540000e110b200a404c10800c0c007142600710b40b02040011040c080c1444140c4158040310b01c0c00d170358507486414095800b4020100710709001070144d4803900c80d0b03480241c09402020105000d580c1c02500c80b81c07110b1016509524401c030051603a841c04c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524724037 1250 524722787 524722831
    0x4090501050a0501140a030e06070905040f09020108070807020a150501080f01150611030f0705032713020a030f06030c051305040f08070503040815070f05071a061314 73
    0x45040b0845405031554031216640d00d001d100d05400010480303080c150389160711000c03103000b400440c0c8201142c1d528100740c00d04110801040b100c0010020219614000036680142d07004034100d0b410036410300304424103550f80d8070200d24102c0100c40c010080c000300b9801394182c1000d40c002c2810384010034155108030700b0900c1c10700c0c22140104030401400e007013154104201800707400240300041c1c6050a4a140c440407202000c8181c2c85500102c9443c1c1c00011110644858003880304902c40c095640003003000400d02c000344809a800884540c09035000a4920440d070103a4005400c000030000c09000c56681d07410000540030840c4101d50080d0024824101d0925040c490380d48210340c80410188581250b403150202c035080713820100d6a81c0f101300004940030700c007001000080d40c24000c0300d41c0705140415005050304202007504041c04402c1c414000080d1141c030f0595850981c128a407040341c0e0703d16000514550300f413004450128503158000c50043d0722400c1c00d0740706001c0c004030300703070004000e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524725287 1250 524724037 524724049
    0x81005030d023301080604020f09010b0301061b0f0b07020105010b120412020109020307140f0103020306031c36060e0d0311011119080a180b061201090302030409050105 74
    0x110000050b045804140d914414555600f00c500b40c5086032400811451080c0344100e42c4207070008065a4013000401c0210b250200f0042c124590995040c0115450004c1e9114030380018024141841822035200c0000c1c1e00c0307842e0040e035454000c0c100d003460305258100041c0c07440094400e0f1005500b04000412005510700031681000514010070170380d41e0302c50316400038020002450104554890410700c3c09a6130410607040900503480100103c88002010803100040c1c58080c80d060500620810490b40e4000c960a007140200f548411680f0900d00c4044444401c8061107112072a0b03051a480203540086900e50040c250004103190107507140c0c1d10540300e03603040010083e8030800710120080000c2c8540300d001e00e0801500000315480030404103078085074001c0d000070002070050b201d10035417180e440840c240d04801d4140080191044020b811301019075011805403032060090b010464a49030031100b0701308000700300020805a606460020740b6070b4054402c2600c0c0c10308000001c150f81c0392103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524726537 1250 524725287 524725303
    0x18030f02100c09050d02120115060f0c0c121109010b0d0e0a080301051302040b030406021c1515140310051011030d050c1b030a2007030212190308100503 67
    0x90f07141c001049141c801040003240c2202c00403038004680f1020b500c241d42c401d0181c034201d8400340003503403901030030300c2c00007498503a2449400081080c02e11000021519800461058440d175190594a1303050030b050a020b046d0016007210740100080000145a400440192000b40b88924040c8600c0ea000c0c0c03502d035503800030b866001e800d0280800040086280141d0300b0998020641005814141e031460300030802d42040390240ea8058001486010050480c03620503034100e4001010041c0300d40300011510040f6241c010505626891410841100d0151205400c0d020420805139542d10b44680059032a0080d445441d014528000c8407140150094045041d40a42d10006509180d9110048030213450040c2c0300d1a001241000200354802a0031b00ea0b0a50240110042d035442c00d002000414400301d20400c4031541c140704075901c5a0020100d800000c89030102c80030168a9540f105103804c140700544140c000c100d50004980801d07400c411a00d12601c0384240500189580d4020302da2a0b28103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524727787 1250 524726537 524726561
    0x317130b0c03150d0b0106030209120d2f06011e0b07060605100804050303040602030604060302030a0c0608070f1704020402040f03060902030c1e0411090d03020c030c0406050607031218030f0210 85
    0x1700014072503a1b200741d000e4000010000e11080120b050005c14500f8040980356090000f5180300b03000c040403054050183e5036070308464064402e195880ca0407078a8600602401c00d00c1c0e101c0d8142c81250400d22001c60001c1d0511110785507449010b440c11900400f00d52044600600e04102b44503c02c0e03018900c0c07180b055401c1f00c051495680c4a54078a0020b50004002c56800750b51404048056103041203100d4106100304c2194404a00b090000b13002404000c0c003000c1048103587c03400448691000290310038415058005281d038072144001806800f0f140c000c001c1e860a151705c000148001a08024a024029000e1f6a00080703003000380b280094800c411018280c10070032107a2142d0900750311016410400161841c208100e40000852100c4d96202c10b60050340410790720b18942c41d041c00501515101113508205191600001c40c680d4007900d03802400740040800101100e200d144c200e0b510251105100d40b446200c5440c01600e808081c000c02001485002c2d1409504000c0c0d02c503982071480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524729037 1250 524727787 524727803
    0x5180d02070b090d0618030e090105030c040207110603040f06060510080f0a0f05090a1709030a1202010e0304300b010504020d151d130317130b0c03150d 67
    0x4103001c001e8030306600c42220f00340c0000a000150307012600720303c0340403c0c4010700710f504040c00d4158180202040c860700e4006200f03980300380c010850380da000980500400b4040e9400b50320b4640350305203ca00355092b2440e00350458000400c100412050820031440244200420001181c5480910400d8a031255149010030200e402040b6480d00841140e60300007050000030905880c030040744d01c15242e00b91060782031503000070300c50000c20210008804819103040300300750604141000280d900c0315503990141001d00c450560240c02d40c030039080600000b554a0450383d859507124104800ea424440d0181d0502c1800f40044a01d1807a07003000001540d0801c0000c41c0f181d0819003000020f52025260801140c3d03038241d203100906017810300700300800d4030f5202860b1401000c0f14403615020004c050700100c041c14060800001c4c0c0107982d5001410312000c1c13a074481c1d035642032600041e200d041c0d0050039404059082021044d00f10006611070b14020300d011035800070010622101840081c07004103080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524730287 1250 524729037 524729039
    0x105010804061e06060509180c07020405040c0f030b01060809010b0a171e07080d020a20210d1827020f07080403050105060d02010c1101120f05180d0207 67
    0x407600c3d0840040c2844994244403280c0d540d42c2400200c07501540044040342d00868400a24503100c100030b121460319002d401203d1034030800314141842103d0000b8491566100410103202c2d12030003200141c00f550611054654581c07d18801d52030003485040e00060000000841c0d103403060103000b681c4d140c05090300c980a401c007500258000302c0d00340c02e207046100e20182e4580c25241d41483d52101c44010000e005010700b4000d0320b50401103c0c804010a42d40081002000180300044402e040d00a2909903a44812041d00080842504481c0c00001c85012490803d481c400400d00c554070521948603182c9105004504240c40d0a01d4071840c0300b0040e8401910000401d0768245a0320b41c1d02c07400c8018035205012070805010f0708001416124490003080c01c0c010007809115442e040a000ca0b4042100e00e980c1c0d0009000d009e0000000b030125202030b00071345180e4020601072912074a1000188034000c001c2075a20010710b8201e849141080610400c0b0b201102c021440c0f0f1090b0b809580600822 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524731537 1250 524730287 524730293
    0x50106090e0a060f0219120f021c15030605040303020c0706020705060409020d02160c14180604020c150a0b01090902071109190203011221090909050a05010c1808060105010804 77
    0x10091200044030150b0204503294602080f1b441360401100a612045814549000040c0032200c1020b809001c051040080c48002088800d1181d04084000c0020814030310181c00030003980c46a9100a018a0520b070600c0201a050b40140950001c501e0468800074ce496408a907222294411141c11003000c10084c00849500d80027800d0a0308090300c00352070312200d121034840071180100d0507a8074502482081c4641c1c0a11081071b020700030304840d0754481c0140c80291102400b006440035106030f600044011031401c00703004041003c440243c02803032034900707444004043c280702d01c442030005651001c04a10001d03544241c07071038260041e140000701801d0f03905200c015440a080e0405041100e0160700d00c0001900065018008020000e0058180c07440d051583d80d450f80318040b07005107192901003c00303900c40f014100b100c000c1540800c200c051030410324240341e0038010113420b030350038032200750800c0d07401005c4a014042c4c04560015503e999a0410f80c5401d000e009150009034008089004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524732787 1250 524731537 524731541
    0x1103100e062e0908060106020102130b0a02030405130f05090303070e01050708031303120908041401030b1f05041205070e090607021c050d140601031a0a091d03040b0304050106090e0a06 81
    0x5042c1e07600382840c0319610f400109140c02c1c0c09034400ba0041c0c0d00007420040c1806441c05850017007540701e401c5410820320400180d102e010b05d00541d4042c01c0014840c820031599a046210303058010b15041206003060a0440d407294801c40d903540104200103404001ca5100f1021500c415400078051829070300c82010a59920b01800c20603803c0105580070080076694610540700c0d018458214030796114036180314140e91409102d20981032524100c3d160020382c80e074007a021132007005040440c070100300000b015600f60003036800c201c40e203408e04d040c03100400c0720000700c00040d94040046400e280d03403442060b51f51174400300c80d000300503003000c90005442d62003426400e4543c0c209041c01c50400e07495907034140c01c554080c20f5080c105021a414054103503010302c04c551040000701c08040c5500e004001003034a00c0520701c185051140c2d1200c0902c0d00c0c54030301c21310b040441400c0e41540d9079165136400702001c60304282c8040d1529440e0203000541100c0910405044a00381c5015000c401555200c80c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524734037 1250 524732787 524732869
    0x309240c02210d03020a140f030a050711010c1115190207020102100c0f110102191101090c0f1403010207120e210a03020f061b0705011103100e06 64
    0x15000700e0b1865000a24428070030a95550784076900161903107904070004040b40c403400f440d020446010401d4003004d41101c1c0890ba400741e00b041c0c02043da40c542d100110b030810f158420301192546000010041558825500551001840f08844150610122021034160b003540c29000306110209a21b8090b860758000d40030140c0140140d54540700c491051200307903034070007040c6c2000400c103014845c0b030b46412a8400c5296a4120021810100c5440082e082105a04100824030111010b20480313848250080c0740d020b40e008079030301005071399200548403d00300b5006503122003680100c08620303814144240d85049410000c0c001420380c400c1c40549500421243e1560821802c2142c00d8900e03605841c05513102040300d005155811325410700909008801d03003c0e60058100b070301072000c402803c1c40f40350b08240d04a282d40382d0760703206850328070b00600c40c10050744000d50000c020032500e88010388003041101ca405601c110030755900d004000300c03c28003441910760441c0c0301e0344c1c02c1d40001c0c107040d9002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524735287 1250 524734037 524734069
    0x606032007120c0c18050f0f13050c040f02040e091f09080d0e030c010b1801062706020106030c0b21060310020304060902030d140d091109040309240c02 67
    0x41c034000741d2510b405400d011650085011030042000860b17030301c81c86120391a40094000030200306400d0002c1089445000a8600e0071039070700c41c0703c042051050900882d40d0742b039001072041203544030864403040650014440c1c0d00b400d160180004030b00e0349001ca443c1c42000c2d201c40d460503001200d080c2a6001b002180402d84002074148440000710724244598001000c003e0015611002031811450941d40316400c602c0c0100c3c20031150104030010081b035141035a41e2030402c9160a1806025412480c44910080004044001001071880e03010b50144e01a43e0080351103070485612000510424800d00b1a100840d02c8060a41c2c0340c5001042c48254000030010147d910140c4452065803da070801c3c0c60a94205a0768003d080c00c40c80c0c1001180705103020350505400d980f41c440403480d01d42c05807880d141d0301241c844228004000900c3c03c19520158010b008030b90341e08140c00c00900c10490303400340003000e981e01d110502c209000561110103565060740d60072b40540311a424080c1203060700c8140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524736537 1250 524735287 524735297
    0x190603020d0f1409070f0b03010504050702120310080d0c030219210203120901050402030604060f0609090803060a09020405060d0e0304031e0618020108070507020f03030d060603200712 81
    0x100b001e030701030003540308500d914a07441681e404c0041c107043c105041903118200402d2100020460700c0442d8050b079044032801c440000b01940c8010b016820019040800c0000764000005c00c0036080c06c2a0303103007080e5040130040396a40440e098098950b030041c5c2501801503800005451942c03441e443c00c003480c15101e000000009491040880000c540c21011000076800100d403240702c14814054181d4000d401e4002070090341070940100381c865001500103403010380c40d0100603c9a500582000005000c61002040040a2400c1081c2550002c5da4124850810300c0000035000805000b52401c1d038400420603460050b403240e41c3c1008220000c0f800f110b90005220010228038281050084650000c06980d4810901e2a0070717000ca44400c03102510032501c142c25000541d9100000e50390140c8a401e20703c0c1c0e00c0078140000f030a0300c00c141e079080364184400107032481c0032412508550104c0340740303460a0000310540c10340000040300c041e608400c001028040c04e4041784900c039105180701400e040c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524737787 1250 524736537 524736551
    0x14160f02130c0203041e060f0f0e090f19090c05061317010504170c030d05090307060f1e09050307031815022109010e06030603010e1e0c190603020d 65
    0x90709007a01e03501101c000160300041800c0101e200400010100d100410501518480c14034202070000e04030000d036981008129465540c600f40a908410034450b8014041d6030706250021140d50017003402c0716040241c4205011104c140300e4240a0b01e05803907801840c94036414100300620045800044817600032a540c214006202040b80c41c580e10150f000d903001103a1441d16091281c2143c0d081102d8103604101000714040144020017500c034074510030100410b060300d404100794130318002c852028020607c0c1110300081982c1960002254444151100000c1d400c0001084122005180041c0c081e4000308460800203100302c3c40300300d882d004020940c0a0b00e807038406207a04c2c402c26803481d0002d640f00581c89082e00141d04501d03201103013080b0002e80b41c449d1010009185000c01e0600314041c0c44080301240032540c0a4000d8050398400701c086817103183c0d880c0078001c0640c00b0441c2040050207104404407043c10010040028071f8a01d10b17684400c1490030008900a5002d59111000d070b03559140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524739037 1250 524737787 524737819
    0x2b060f09020a030b01062003030c0703050903060a150b07021f2708150c0d0e0309100c0c0f0602151b030910060e100612240614160f02 59
    0x21401c406107028007070f8030507550304065001d085c0c440b9890011f8280e240c64690081d02c0b41e00003080365030000c03a8814040c3c80e6a05841c041d54240100040d41e503040c0039040c100001c0710010703803103400c282041c20002e210300caa4546410340b10380300e50200a0740180d001c039100e49800780c40700052a944801481c0000c94504541407003d0000480000c9640030300c80c0c00000c0040010801c00e6451448507000400300130f06001c0c03011780c0244102c04065403030701d07118016510100028402c3c0c40d074680b030250035001c03541d5454130000c00300d0a40e00302c200c480981c0048040742c503584c20700703990056480c1a001800d40401b41c0001d07a80e0808010918500064515003007404045070001079406892210003d115071104061709505940c1c99402040c1211846410802c519094025010484030182880700800c22400592001f501c04d0701d0810b440660700141c510301c00b4150f16811404c503460350341d840c0c0d42460703602038000c6144a40000e0040940201405001090310160700700d04242c801030100b81000b404003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524740287 1250 524739037 524739049
    0x1a01020309012609061603050708011e080706020c180708010605130306091101020607030b010f0507050c030a080702030708011509020a21061a071a07090f080601052b060f0902 77
    0x5508050035000201481501944043c05100104240c11709005a103060b27000140080014420821500f04009080d691031221682042c0a0b109080a031442207442c0c0101030f548591040505014134859500b8019021080b43d4690050345c040d6214101e40c2d01e002c01c1120360360071560401f45000100c040010004000348568a0698443c0310302c0b51010081100180c203003040140a00c061505210b82070220760383c40711210601d40058140f241e25800302d07050507894282502103881d09032040c28100004c0c80a10307005814214800c900f19001c00d6124070689081e18250800d0002d0700c1c103c20810f0050060b55000780207064607a19200c0c4a40c21070300e40c1501c072301d110310010461042d51418280401600c000d08a8000c0401141240c503128080c0c0d10810783c0ca003100d039a03900603449000400c0ca803a11400044008180040c01ca03900c07a52a20040b0742c603041c3c01e200750340c0328040c1c4040e08141135102194400c00020070003041c08071000162545030142c0302e0903181611403661941e1440c01607840d9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524741537 1250 524740287 524740291
    0x52d012d0e01030605040207170c2404060615020a020f010309051f0b060a0804080a02070b0c060a060f0605070303090813180b031c2102180102011a010203090126 71
    0x40d03a81d030200e692800c80007508445594028034003c2e40100f040401156409005119041c801c0400c90360f50020a00701c00c0c103006103903880300042c0802030b0700d0803103088800c0703041030040d23014000c00c1207020765070309200061012643d070340805a000340010b5405450100c000304a0040181804640f452090b0744003410030030726a46040b00c1031414110324180110340d100d5002c49240580d9118501540400058403030400280000c1041c0f00005051019902c2070102c0e00c02002c059621a80b211001600d140d10351800721403010f54240350402c001003613034440c0d0b00b20f8119950b585507280791003c0d60301d00300c0241048203810768051f04108124030410030b415034803600410140c030203201d2220400c601082a80c0000700d8440c42035109071404004600c907001c151031424110300f81048807010450581041c403170307c140761504c81072001c41d041603090303801c4041c039030104001da00030007004076801c4010b004240d04061040c0180d08c1032024050550145070310070080306200c1000c6e880d420401207000c00c0300d502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524742787 1250 524741537 524741627
    0x9010906060b0c0c04050717060307080708031207020606010f050d060803030a06031b05061c110f0702010f0c0b01091503080d090b150907050d1e06052d01 68
    0x2c3c407814a00780a100e01c2503401c404032010320841c208104020108404081413882101c600404662150390421142c8000c12001041c0d0300000e641b2410151650442c152842441c1440d400007030740244081513640c031500301610b03024000d11114100322041e411003090301195580e11100402d4004040028500c04e03103202c800842c0003401c0d07107130007080c0d0f014219010280055111007404582d03210401e4403040704042010480403514038103600003600d4a07049110662600152680300321410304002e06c1828001e0702d48483e21803114908407100c55195a000c0d0010212200510442a0a8011071240c0c80340a20503524640c80351503580140d40a00700c0300304c20958034501c1d242000b030504c05480d440758940070030824480c0c00384081601244018110020440300064032008820907600151102e032141c54800b00d9900c180044000410a500400340700380010511413060000c0c5044402c07504550380048809032078920300544040599030701704090149000c0301010051066161071404400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524744037 1250 524742787 524742809
    0xc070b2a0c1b2407080a0302091008190218090a0212011e030807060f020304050705030f03180f0a03021302341101090503030c01020405030d02070f0e0901090606 71
    0x2403407260030300d0300180d15090801400e41c481081c0325941c4001c80c100180c0903440c500c011184038000c19128a20079480300034030742000450b45d4418298942c0c05491a018251004030000052120175982c2035002c131101c0ca44008034582c6d540c03001c1c80c2034001d00240c14045145605402c40000001c2c078008007120f02c170496030350104040341106410200700f03004102404800b680409042012164549103000103010b0300000107075001008003613485040b800b80c42842c00c40d201d003010f141842d150784052151902c203100c6d1106010411802008499840341b82550125040060800340180d501390501800c0c1e114076000c00c000090f03140c1c00c000000c2e12462030001039444400600d90001300c0da40b8108003502002010401007580600c194440c1c1c540d8200c48104c890b0200c2c2c1d00121040c0b02d6941005130140004554000010f80540107082585d0044007a1502c2d20f10402d002ca0350380c1340c1c07445007100c023a54034a0100482900e155401e80c1000c07905001141c240165101d001c2580c4456102c0d25201c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524745287 1250 524744037 524744047
    0x90a06030f3219050411030f06190911090405060406060b0901080103060b031f020705012f0a1101021204020102100504051c051308030702180c070b2a 66
    0x44034510510610040c0003031101500b40d190120301d06030031900b40c5031003010500940415a0b00c3c02844610422200e5440c040c401840c0c14640004d0440010020074020302c81c1d00322047d82900c002c81e1a0b403060035072111602c501c0c1c0e039040f0400040d00382000c0c11744074400c503203005003c0340c1c40d9030301d03001d1103039014500600660415140c0340342164003d6016240b6030b0401e1140d078081c1e070380c004501e9044039000240410b90316485000241041502585840044081281c4011401403a0080c0c04050f0240c0004c1240c0d0801003c038808022481c804c1c1c0002d50b2a01030030b54405001d00c80038051480503881c0221190258004103822a80f11030300d4804600c00040030002190703810043c08840030801e950a0105007400c2d80d5041d960900200100c10014408200100c0e15108105a62b005015001e11140e802c0c3e03214403694495100c0d0400340d0081200392001c1c10b040300d401d150b00e40200500808a460a601600c902e962040060401d601604041e030784c0558000888288688400030481529511 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524746537 1250 524745287 524745311
    0x207020a0f0501050a1101141f051c1e061103040605011409011a120f07020606030f06160302090301050a0605010f090e151504080c03122a0102090a0603 67
    0x4000c5036000c0352040c0c410103418012640d200c002c1e2407000100d4104994001c08a4181328007418841007001403040802041005107001e2406064420750103c588005040e140d80510015158041602d401c03440341c0320014000aa011403a482103600c03e028402a1010b166188002e4401d101a0b811702040040240014006c1038030506006100b441480500c5a9012010602c039460502c1092000025485030a02000e55003048032818a9400c11280c0140790101e0600314404d0150303003140061040000146643c2000641034009402502c02000c065440b82c01c030b201c4402c110300701d82082580030f200c06c030300507103007400f801c3c2c00b420440c04042005414100010404010003031b440003008265007082100010301007030a9004080340d10515810340311140800d0a50020b20020300c40340c440050005680e131000b040c500c04c03000d011000e030349207004520007a00803130180305548804207800c004003c03d0050f130b204403684a04400d40c0090700340003036400050413080d80343d48241c000c40d46911403c000c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524747787 1250 524746537 524746549
    0x1401082418192009150f040e07090b030307020a151206080102120f1504051b0301120c0f0308090d0f020301060f09110a0816020724030e06070e0607170409020702 71
    0x8400b0f0490750700c10901000500094481a001d881011564403480c1c02d1010f80c0c03102c4200c44450a0068814083e9881c4007a9060703449000d8482c41046910f081e03101c007028039011048800702900100909441820080e100350b80c84103035400042403210001100a2268030323806140024002c5000058407504e40d1088802440c10082854450881070001c101d0300883c040c462906000058900080c942d8510b40c100003288018031f13200e036004c0c02c08000003d0a403030070021204080c0c802d51144082d1561031b580c00300032127468040107144540074814074415082030400720701180c3c0500000d101a42c0d00d44c000c03a0844409400945040d00001018440070305980100001e0085180c5120f1030860a440d0040449070068140d698104580c507101a143d0300c03c0082e8030281001c1780740078414100c4550844d1065425107034040101e0300b44111400c81b080040750302881050b4985034026400940403c004040c0d015403400c50341c1d010a5803080700401040e402500143c1821580182e48803103a0042000b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524749037 1250 524747787 524747813
    0x50307090c110f0709020901021222061e030525051e0903030a050a091a030109050705031b1c02040b03010f0803041202041a13140108241819 62
    0x2c0340c0c4459800803241c440040c0410840c0c10508005807201071120040b401d008401c400a848240003250400d1950001c3c3c0600040021415002014076a14a0705980d901d04250548418050204001000714001d40180d03600c003846ca0b064141c08019141e03100341384078184040c000080d4003c181510b080e4908400300304504030140400d4140410b00c0006580c91192900d41801c02c440440e102903c10b0051746903c0203482c8801113949003101c1c8108499140e042441411699428800072542013400340781100e014032506862a88182c1031140b071444943d001051014100100500341d8000782c1061018002a01000b035085035254580300e044032040259030020541900b0130042044101e1780048500c03603c030784c1543c01003107810b845101010b82940590000c0d400003002010070014034034542c009800138070315124410050342c03a0001d96070b442c49416140c10740d6020b41e141030f000e42e03650407100f940c1c800502e01080d41c014124000d000d007131809040041c010300e50200e403544101b18070241110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524750287 1250 524749037 524749067
    0xc0c05010e03131a0705030c06060118051804050c06040303020a020a05090f0f06010e061911120d0e03040302190602060108060c0301060c260c0105060405090d110106050307090c 78
    0x60070f25603074101c00e1144007220320402428000460034481c40c1201d030b42c180c032135454200040d07a803a0481d802019440e0034040380c3c514006021803400b48a082d0b140c0783c0c1d603019140c002e841d01c203485007100c185040701d60018001741c5103889207494424541d60f89000401c083c6100c0d5002c6c001e4000a88140103045915030440d903ca00010020803003032030010324009910607400040d501490300c55400684240707a1010005403c2500011100200924641e03002070b05451540c1705081980c1840c89640c0f0391002e00126901d05808000c0d00c003e9202d02e40051100002d2481a40c2c034156490f80021000304841d0008680d01c42e44290401c0001e4050103c40d0060010700080c00b000e00c0c141900ca4a10300c014002d07202809545820181440801101e070f0440c03e080341c1c4000c0c01e400b12131003050a00e404c141c00d110003d43c202000201c05c0d0425009540c0600c7c55200200300060322203405844a075009990a0304940d41c034003000805030390405c1004002d1000003000692403858440050004004110136 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524751537 1250 524750287 524750293
    0x504030207180f1d030712090e010f0e060d0503090409080f2107050a090501080a0f05150a0618060c050a050a0609060b1903080315041119090608041b08010c0c05010e 73
    0x4e1550b80003008585e14103a00650f0700086400341c01047d143c1032815044080814250b40000c181c004062045400783c1d24041c01d034900035500e5a0801105030b0f010035004090341c105001d007210500342a0081d0760942d210759901c60421501d6409031100c0c1c2c1142022035410b142e401100d031a1003d004100707a8204400d45007980c64050a0100a0300c0307106030344a0981048002c400250400000d980040204442050140300d2030426502101e4a11110000b06120b140b281701c0c0000c030540030b6090034905010300080c00d4455031911006450075090303081c0944213070092101d000b000070780c1808010b4049101d01d00c0002c00c41c010307003080d000712464404c0007806082200c0031004039004003110381d800c0300d038002c420703070342c0e81d900c15485030703022400c9a03000c81c2c019042540d0010444580005080310000c008190180007249090071600b12919200d25404516030f0404100400d99049035004109a01d800344403030555120412400c54142d81c894000242203941e000040010a00950148804170001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524752787 1250 524751537 524751581
    0xf0b0403050607080a0f020c0714040213090b010c050616030f0209010c0213020c01110408010e01050106120207110607030302030901050708090d112404050708070609090504030207180f 81
    0x541603072008064448418044c841000032074500140d0442c0b4920024000103644541c21002c0d46070340c480040c05603c02c4076004024007911424580f09545030140c15548140580749442114801031510702560b60400910f9000c000101d03070704018240c0500302d05001041030b040841001400c89118500081401780100000300190fa48035000c840e242e43c045a4100740001e600c1040e400a00c645642000c2a5081501402100e141f9501500c1150038050084c030074035008040b0030342214400d009020125107505004086a066a8040d0450034824140900000c2c103070000104a9044004100d0000742c0020800070307860000e0007410381013582c9050401030b034203204c09015280c88009940400300b0650382c031a0305460008104030012894504035100280c200841c214400c3d0004980649007841610f2001402240c00182a811580e441d130b01c82e400c580c1082456070140c100604160114441c5507404202507040e00c056001d1403081c0b00002481d00d0300181c041c1c0640e0000340b0102002d40d02950 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524754037 1250 524752787 524752793
    0x32113060509010903150603020a1d090604020a150504081603140d050a050c03130b03042105070807141002090f0312071112030a0201050a0e0a05100c12020d060f0b0403 74
    0xe0700c181030b41d9200244a1103481c051a0310f1b0000c04a9910281d400a80c5141c00500c542a2502d81c1100306c1d81c00d20a0921645c41041d080d0751075030150f034004c1d00003201c0601041882280764600c03c0c03000c01841e100345426070f524030451801025400e010b1003d1506074003001003096280c4205960085d000203400c1024400c50003030f18074041d10040b0030a0010002e17100d140c1400c04d008484800348040d11614020f5190142c506460308102d40c11203003c1c224013403252130090a400c0092001e0000e036506444e0012641d2404100c0d085001c04a540c07450081a0110111007072140b80040141410300503152140038040040244940414601a41010811440501055045608541d001604148103883e0440400c41829034000300907000c2c00041003120020390f06400603405500c105005000001071700100da501c80085210007400c65210b1509a680e0448640001c034608003030741412406981102c501d24140c2c0e114112021080399602000c1c01580e0508450750094842c02c0e0b103d9040c5410341d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524755287 1250 524754037 524754047
    0xa030909020d0905070803210108060a0b010c02120f06150303030a1104030c030b1605190305101502030304050d02070303021203220f0b01090513030e03211306050901 73
    0x402522945074000038098800b601c90742080540300d03803080c1100d114a942e01031050f12a00031000a5000001e00c44031400c5c04090208824166207010f4094041600e441c0a4007008064841800741032041044925001d80c1c0c4c1d10703840901c21261007024010500d20100030030305041000380780111404135a4203814030350300e001007946d50106e940074000590b150a852034440d14026640014a150141503011041024a5408a0241618004580c0000c070f941c10309480c3e43c041c01400713600030b0785c0f0070b0120302c500f070300c60b4210035008224104408085915101c2703d01e0030796001c101080260307000000b44030400c5810000615070b640d0038406040a513065980083d182ca01e000d02c141441c00000c800301d0400c01c000c02c4880b0340620640e60b2040800814a0580700201c0071503030036240c100056000083c640c00501881c0d209613041e250000707000885503400e44a010302400c503544c25103d07510a40c003420141081c00490b90300b1903098503450b09000d0340100c001c00c000350401401c00106001e81c0160f642c03c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524756537 1250 524755287 524755289
    0xa35010c170a0603062406090506030705091912050c030d0507120504050307061d0f010905270f180f0706030203090c100e030c0a05031b0315071d030a0309 68
    0x901c414911070321601d1950010b8040b40e0030103000540360580c001c0003034030030751032400e0401c64001590b10782c265207842c259408040c500c00c40380c00c600704100180c00e492141c40107100c10034004100d90720594800440444101d1190080f03103110021041c01814441c0400562514100480052209040d0b40c0740003031107405007100080c1040140d0308a0a50b4500440c20341d006800c025048520f91561840018140303481038a40c100e94201c0b00c0c031070808505081c810a03000101c1a1a4506824900300074001d0b0003d0306181e01182000d0031402c08403056058201501030048508007c4480c207064818442d100c40800c400394050780400ca00660003000030824004517944c0d03040050300c2c1c0d40c1d0b0031000340c01c14400801003540700c800680007020304c0380c00200501500c1405d9007110400916981405040038807401010342c9075110140751590810a0105a0320385030018040d582607000078000501d4550007900c0c14404100c2d84401e2180c0307030703402e0290841410001c4000700151403113514060003039411 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524757787 1250 524756537 524756567
    0x32d0406051b010e06100e060d110409020d110405010605070519060908031f0603021305040f1103011706060103022715040305062406180a35010c 64
    0x101081d04070810b60506504000d0405100080c445800c0080c03a07517858000842d5250303110814003501142107880004400d1044102030709541c414180703611f603800d030801290341165100761200c1c20640140c50304544813003070354801d2000342c184940c010100408e4500c140c21510070042c081c07040c44007080740001d03181500380d4600b00e4a405495130b070800310098909010003501ca0301c400018004541400e18402c140401499182a4840d44400080301a0700c107010901c040218101014045031a280d402581100d20703051740010070307070007040d40e0540301c2c0c100343e0010390358144100d0001030310181804050b600060900c0e08500c3d04100070f0048403507400300301c07441c0d071203002c1101c03c0d07041a150007a500d558140a41c4025880c0c0b03649161079070380d50f802214000c107841c210034440c04a150b140c0d070441d01d9640c0001d1407a801c0400510008030480c00240106500501c50240080c0003c0322100100d91200400d05801d080411910b280f00000c800c0c6d00622041d03854030380c0302c515040e4401d0750944081d40e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524759037 1250 524757787 524757797
    0x3130e040f060b0301090b1603200406050309190305070501050609130f0212120a020c0a0e0106080c1612030b0f100f0c2012010e03030c030a1409032d0406 68
    0x541c0c80803c5c010070410000504d40c904000c2800f401d095103103007000380943c240e5018841846000000e42c82c000c0c0c0009071600128091100344079550003000959484010202281c1405482000c0b503988886ea14000b41c0c003280c0c001074008180b00c130a019466000000351140c215a007881801c050801541d0080506203420303040450b402c56990804c0d44401003030304003c881d8111000311170045030b64400c60061000d440794604100c1030307090001580045075104c40c0c42101e281e20b4280203480c5d40d00300500520b41500c040146400e10f0038500100d089043c00750888001942603608050110b44002e001326104181550060101c0e41d50b480c1c850786512070fa481c0c1400821415041542c0038103032150006c210b0010041c00e04c41c103138400c0c940180504d108444002d41200310180480c00c0351010b14420009410420000d401c00220078010340e00096104000100310000030807616100034140c1c1e07682e0aa404c0016480d240b042d00b158030801010011800215042018948240f40c1c8224424001440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524760287 1250 524759037 524759051
    0x1e10031413150c081005040902091305070305150106030c0201090f03030c05120c0d0b060a020304030b0c04080d021f14040204091b061e0e0d02010c1407060203130e040f06 75
    0x1e103411015055031a29018030241c2100c1c0c03001390407a84100d070440c000306085a00010789242a028550246401034070001e42c0e92030303191500111124629041c2c6d540e1040c500000b00003007082082c2028001031440341d00c00b40d41043e0004054a003c6031440c0210f80c14070300e0000c049000394001607141d50741410f0006000400c1d00d810344090080d10440c3d120140084100310f4210b2014000303011f00010f000c5d04202d1210100100103c9000e5184104016031042c030091002840700b519458000c075401c3ea040e410306039a10140d51410604489020050308034200407440400010307196000c2c505426014081c0c0100c80c3c19000c4110350041000c0c2c032542e10350351b902003484401503152001003001502e908629032100780190004007034003520384007000202d00e00c000c1240308800402102400810134135110841d0740044690010709207064401c800c40ca5407080c1050420407040005081c01d030051502c542154000d040e96480942c080d5541c00c1c8100c04102c009242c0d000411510703036022000040c24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524761537 1250 524760287 524760293
    0x1b100309050c15040305010f050f1b04050904060213060906170612240c27041e1a0d0305040e070504050907050714070b0307030e0c1e10031413 63
    0x4001d402c0006904014103c0321844031101c0303d802441030300e024200a00a64140390940700c1201e0040742c2002540c0303a250301044d421340000342c010501c002420082410242c0b504c000a000310401e0b54111501540099903444180806000d10f0050600d81440c1300150301d840005040080310181a00c048000507000622079500d01c10071042c3e5072845001c60344510465480001e44004500c541200608140006803028403010304070380410f500a184060301240c148920307214003100010160344541c540f4001241006002c400e1296000c6054003c41d4040c1ca0341c0c0b00400d0780c3c000718400c034000d0804107103204c0400c5e0050211070856509424060042d95840c5084a81e40610f400c426400a58601444802a4060701604039140600316200142c1c1108a800d560748035a071282208240052001403011402940805103089070a01900d1200000a000480e82400342044805103030b0000c4c103030240c90622002501003214642002c000d0115054a01d001d82880200181034000c010f280344020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524762787 1250 524761537 524761543
    0xd03020d0f09120303020a020f06040c0509130f0b01061d18090708240601030207050703200d0f03113f030f150105131e03120c051b10030905 62
    0x3000f20031200d20f070781c20300c91038001c010758015001d0f100144038003488510341c00c40c00305080303008941c044100301d40c42e0b241a050165490008140050340b90464000c14040307549a81807540b014030490b82c0c10f40c55070512501800003a541f106d411200c04801e095503040d40c0311060300c09640485103805108558600118a24000542c0c0060429008003054400805408640466041360702c101b640600d58591380114102e005200000e49107500054023040400d50358a01f600d15058002d11018040d94080301007100c8601c000c00c12107170f0620040d0550181a4000c00302c4540603540340181801803c044c5000c0f6540140c00c20442208195208100f81001e901910700d0b1210040e07042940c6a00c0c0c140c440e406040e02c2142d0b1800307003104902214103a580701e8070849180300003800918446d03509010003015083c02c03000c81c01c070345200d4045011010070342e05060700c10b10b000c1e503a5801110416601e0030509140b100200c40e41e000d2022200d06480b035440700491203945020380750000320443d40c1c0c2080783c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524764037 1250 524762787 524762789
    0xf03040f061808031b0901020a14100204120c0b03040f11010c0614060a090516030f0b04020c0313140a0905040c0f080a020108150f15070c230d03020d0f09 68
    0x484058540090b20400c600b50b0003541c0704200f60181056908030300e02400520b80300d111001030041c1c000090040004a0782140030403403650290807036641140c07805035001241d105401a56000303000d00c40290070051480303100005005642c04071400c40c209603840c03142c000300070740c0c00411804e00c801c003070300391031348034588052800d60810070600c280c03800f000103042c40403812b84810b0b000e20720310f034030210b543c850074041c203801040911407a84200f200080120001c0c01c109031221526600c03010650b500c1c0e56070740081e11500060380091a075a040601c00b07948004401c4c1d025407a040d844101c21000c9541d078001c0350b000c540c0c1c4150042081d0380d41c0d1814240f400741c2c94014030301c001c40b4102c0100b920400065a8090f481c400c0e242c081d031a89640b000440d0903207202c0c6105500000d141100d010074180340b00c1504c002e00310b60a400e1704007009030340c4601d50526260803240f14049041ca60301c07200300c004850384200e100f094801606220203070f10001d40b14010307840150300780300350745040190441c400c6000340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524765287 1250 524764037 524764061
    0x1080910050a0e0f010c050a0e0310061403160303020601030b0a0e01050a0606030c0203030f0c210106021c050a0207030204021305120d09171f110c0705090106050f03040f06 76
    0x114a1400340e442c88000c088842c02640184585465095015414032406103048656101c080c10103c0003102254011020388030356805004210402c03101c1c009900030f0300090a903d008403c00d28071681c0c20b151801803828545480c080c44808100042600405c40c80e040d07940002581c80982d44140040d03000c3c008000302d20030f00398640801c1003080140f0b60b020f107050340d66039a8140103290215078100c1c0e40340400c0d200c0c42c201c5501c2030045040b15441100610060b800301c840d8819140c401e44c10901c3c800d000342c1c000d40140c2c000e0030a2100301c4d840e075881d000403440c082c2051801c1c038240c2d030b44c000c0da138801c640170080c060307a07002915490500010140700e0060078018004001d41c1003595155480e00954400341c800301b50300000c0030558844000504242601510007088001c0c051855900341d804480400c285007655640c40011241c6d00000030700303151100500402000740303450107000c01290140d105004101080c0600302c2200d500030101c07604a42c101c901d01006180b14241600249010f498035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524766537 1250 524765287 524765291
    0xa03051e160b1b07150e0111031501180e0a05060102030f301308030408041706040203070902030c0a0c050c030717100522060b0613030b1b070201080910 67
    0x71820890807001c034611504220351101035002c440d02d00f0000c10b018841c0c00030a0001019001100c0490799800440c80c0328806002189660302c0c0814212240e006440241640c135189400c0c0300c281d41c000e01e0361104541c50211210295180c01241d90643d0005408841e00e5526000411466842007040e103643c6c4080303403003140e80c0e10343d44c020450a880c80003100d503d20342250042407100c0707850500441d1140c0c2d0443c01c01d0003409416929044254001001201e0003a4180004540110000040c1501c0e00c070002c001c0040382044d0041501c0e00c50f0390344c40080b0082c01001006000b0700c0c1c3d202500e90b8031185080241400d0300e00d24003681021120b000e980c0d00b40c40340c0d510009101b40c03061299030314800348006403105605088500e400b5100200c91204076071b0320386150500d40c1c20b0101d0099001034007130300002a01d01030030800100c042d03121522040102c00101c03000e001340007114001507004400b003c0c0c445500a030324207412580c0d0080040c0039050044a0001541010050100c1c62032420f2600f81 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524767787 1250 524766537 524766577
    0x170d0605090610033908100321051201120303050609060f193503030601080106080c1b1006061b060c021e0307060605060a2307150c110a03051e 63
    0x15401580740c810a42d00000742c6c2c8080403505880c42100c1c0f03030081e03036080b1140781c141c101c198110342c0082e5080e07400803007000410401003075042c2c5880c0540e400380c56154151581c85200e4100141514000f401140c825032265040c000f1990320b101e040310300c5003030564440100000e440b20310300c01c41c1c10551100810001c0c8174a1324481c42c00a451031180c0403003d4144203091007100508a6a90204484450129414500601c00c65001c1c502041e8011031241c10319250080d1507128800c01130b1107800c2c00b10310b6485a69070b41c081c00e03101c1c0180005010f40c1e10f058100544140f0500303400c126000300c0600640e40e100c203100d114610a0141036a400101d0f42030070820009003031115500e900042041c2ca1140c034007113020440c0d00d040e0342110303e1002c0c2a0359081d5880100c3d403183c11140304100e0f000c0742c01c2004210982c0011900c007800c00101d0b88911002440046a00001e0310031710b16800b041038150045d081003c0021b820605940055207800484080e141d80306114510610601c0c240421011160746 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524769037 1250 524767787 524767871
    0x907211a12070501080903040f1a04031a150d0b0a0504050a0b0f0a15050d140708011508010c05090d0f031701032103060f0e04020607170d060509061003 67
    0x260702d504449081c2c0c0c2c0c4a00c19502c4a1641d61607002d280a400900e1150302c40821029000c0c1c0b01d803068084101d941e1500e040d6076a44c40c82403805507003241d010050220b0b000c01c001000b000c0311020891a00360350003840078120fa40d9203100e5940c000d00903d0344694490100d000d00500304560781603107078403450007017903030a01061642002904951040038a41030801443c034000c00543d015040702c81c050002c2c0f407142c0403035980784d1071b400100342c80e00c06034862190000385865090040403502041c4102c440a0365060000540c00e403103801c5040d8090003000c0007260855207424441c842601d4100322409001521442c0c212a504c014a5840030844d51356000401400303070720660086070009854408001c130140780802c0e42610521711640c078503d129031004101c10a4142e04456009100910032454610180e55104003d184100003260b46240411446612005440750501800007222500c000349000740c0096610900350380c01a0130961900600c40040360100c500640c2d40f620fa80718543c021810038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524770287 1250 524769037 524769043
    0x828050a060b0307020f0d2a030c082208010209030a0b0901020c2b09030506060607081207050a23090d0f0f1104060e010f03030e0a08011107020907211a12 68
    0xa190511b90703000b5002030307100035801503985c80c814440c40002c403201039020004105035603d10603001d0b81030090032120740e00000c100c480204800031580082d9050500036001031a5600343c02d0700a881071b6881000b80709115a00011101c54043d44800d644142c2c0d514100f41c40e019025000100e8040d01c168140c080030002801000b20241c9000d441542d2030742403d0b142102c58004c01e100140003a0060400320300300741000c000500707100d40901170701c134504102e000e90480c9206080b00d0100002e100801c20221041d80000036401462140300f203d504662034030201a802c0c80341a000c14031402e1300c220007030208000310400300b40b50741d040f58102c50b8000541c1403000c40c031a00318034070358480e924000000c61680750440c4c0b520b041e0b51045803044405402c0d0780d000d9035148016828a90b01c400762400000301441c003401886800039014081c0d0341c03240c00714030602291500c0601940e040c000210708071000768031824142048a0641640860880070711616811414140c22100760440804ca520b503c03809000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524771537 1250 524770287 524770303
    0x30912071a0f250e010f0207050307030503040510020d0816091e030c090c05091e09010b04090513050c01030507120e03030f09010207020a120305091f0828050a060b030702 75
    0x75019400f2481581d000304000840400d400c000840c0c600b1039880b04a510801910075803129a00498110545680c002454500b107075004035065131000400703011608100281d25082c900500041100c04100704000d0705800000b00260038202c040d03c0f49510b00b43c41110554000c2c09001d01d07000003c0f008400700010420f483c0420f4421801c030300030005a1546a1003400030003180f90f034800b4104100c26040041c905108420455000d500850302543c980e603220390140208180461907580c0c0340b174000500241c540041420034444192001480401c4000c0341402c4401d40902e00045c5a41e100802a52426078201c541403920785400c1414444c007000100a500440300310388000703601d95491004500380d22500000940144501500300120201c1c0060402c1c010310a04003c2e0030840d0034030110382400b5040d80410584507000c1009611950800c24080d0000341448030580018550142d0340070348910b14074009003072641c480006400c00000c0c1d2015000d480c40030000c0e5134a0403e120001e583d0345407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524772787 1250 524771537 524771551
    0x4110a1706092803030207060b060408030a110114060108100b180108010f03030519030e03120103020910050a0b0a14070b0915040b01060e040f0f0e0c06030912071a0f 73
    0x1c80491010012003e0851801040405060303c294991640d0842c06500154030440755a03403210304d0208540c2e91030010b44054480e01008503103500d24507038000c04031220200380507100c2e49440b1842200d801d02c8420a68003a600b801c00180d20748a061400700081c0c401d6000018525012038080f042c46418901d40400042c01d0b6540203160341c903030b2520242c1140301c0c84003c2c080f6038100f0a03611000c40d600d0440f202c4249c60f0070300091181d1030241c41400d550240c94425540c0304690014411454503018035504040c0d841c8098009508041c01b00b00c640c0340c5805071f03038500100800c1d03030000ca40c42025407081c08080c02c0303a566110203083c90010b40c02d1038182c1e01100240900348040d42c3c0000c42000092140e034126904201c1d607403801d14182d03940120220386581050300c9490b199010325807801040311034000100002072000c9903101031401c01203e840014030402c810418004242c1c00041c000d0b18140032500c41c07556030440b91a148404203142414032038504110030801c800e140e01e2216480c41203030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524774037 1250 524772787 524772793
    0x4170702091f08070b2d04091e1b030b040b03160e1315091e0b040201080705071109090f0a08091c020d151d0622050604110a170609 58
    0x519800700980301d1a050040d0f45100c04c041c072060300039882c84510590504604540486000c86d40614440c60f0f5002d0f030042900d0940b180c2d01420300e607003068210152400c1ea18010416a07603d41b01c8283d852000e002003000701920b4454440e80340c0c2c1d45501820781000010211243c00105588803003114000d84140030b04103824100184980311740c0881075400580c4844510400100070285c1c000030860725205a48044a0350360310b80501480901c03c40780280124001e0319146030501c00104904001404041081410300c10400040c000d6086020711102c201c1d0341801c0c0eaa01ca8140e1440c0285421040c0d40c41c0c41005140c00c01d116103207004004402c001d60b0802e4041d01c0302c98a54000311081b0b0002500001c86000c58004944000740c82e42107654444408201401d01017121554983c000400312030a0300400140192640d1152070640b400d200d9000810720001035403141c43d00d5400061010702021100c401220715a0b40e6040400c1c083d1602900c000e6030001c04500c0c107a504c000464484103a88 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524775287 1250 524774037 524774039
    0xc1e04020c15071403040803070314040516081b06070f06181412030f090115090f0501050405010e1b0705100615080405030a0309080c010f0b1e030604170702091f 71
    0x140c0f01d99036009144c0c2100e04444c0c95501e640e55644040c0c0d00091945007015542e0681100445075000814015402540246000701c00160071008078505a800030316207a00401452303921004041003d4010304044a400c0c0c0ca4060604181e000041003000080c001c41c81c01c2c2c01402c0c501031030b5a0300314101d4020b81ea42d04010300940d251b0340d9038041208400200c44402e100242e124100452042c2c1c0c0608a2400492805400581e00411005035000a4880c0d600c82004040304141ea104039801440215028480e41d45400d5200d090380102600f69401460340c124050751210007002203411559024048413061009007988500500b8940500c0301103003c00700c000030906124207010707401141c108018501e00020f940b4140d0040c01d0b8a82c0480300c200090002c13100400b802c0c4192412000c00d21400304144020008005045020024400c0100c1c102c41c0321045946002443d640c1c415845041c0d400300c520101501d8900b40650300c5c0003580006079404101422004400c0c0552000f00754040751505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524776537 1250 524775287 524775301
    0x31801020a0815030a050d26101205120c0a0201030c051c0507020f01090605070801050a0e0f15040c030902041505150a051216090f05030c1e04020c15 66
    0x303441450750020000d140d0b08003060800914003500c0000c1c0500404890755107180382d8401f4100440e010030703180400c004a02c1d5459075469050001c181d412040300702c0c0e0307091400f00d070b44110500c618019607085d003401c56286401c01c50108a0070384040310303075442692124988071029980c0c035011141240040d0a11500350400c82c0101d00360b42c0c02c41d88600f000042a04468103c000a15004220b40c085205005094000030070a209040b80340b0b000340c070301040a1500000181160106900c460300641c1e0b11041003101c0807811401a4004200380058030023a20340001140701003040c007003a0f940c890300d481d050441841d059800100058030a0b0b0b01442410403c1e640c017504d440c0e4510400b0740010099038240d129280480051100042c0c600f081800c0c807039201c40080d00c8142c1290941c40d40d6244000a40c00740e81c1110100c0010480640803010140c1850701294459684031442800b0f08039a81003564031280201080ca0304c1040980115210811448074980d1100445640620082041e01203944 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524777787 1250 524776537 524776541
    0x6060201150b03040f03032009040614031005070c1505150111030f1b01020307090e100303141809070f17040c03020108070203070210091d241f05031801 67
    0x100c1d004014901d0541d0f035130380c071880a00c25403408203c0805aa074400c00d1991141c20001c43c410b4065043c220ba1110071200c22b00045500c940c100e45403200900b500039407613903400141d29034201c1003c54040340c1e640710070406880c0350007460070052091041344e180040302d00c200ea07c800e100b44050317554221500021030064450f44604d541d00007554000304614001d2440c07080040c02c1c00c002292000c8041c4000d030b00c4040c220380007510342100140381c2403810070081e45a1880f0682005140c080180703000e02e590743c00341c4040000c1c0c1d1150340c3c582000ca02c000c0007101c00c1c1403100c07201344e001e04400020301d090f403402000d0785402000c84d808900c4032000000c40a1706400c1d902e02c607561110340c209000781150019614214001c00400c1184001c000d0a40141c0f21460031124240e03d945484841605000020703084503082d080810131030b041e01c1c0810141d0035814100549188603c16070103942d42000000c1441d01d01128200100300803102d84526095034004001d501c10030014200240700c402241d40d09003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524779037 1250 524777787 524777789
    0x307050a12050907061b02181824071b050102031812090d15020f0304020111030712110f030c0a03140703020a03030b040f0e0d08070f0813050309060c010606020115 72
    0x3103e548112810302155002c0c10300040d41c11884290002c40181c66030005440581c49244105901034440074031641c00c0400b01c912442480450181000c2031000600104020707000ca00d020070001c4600c08110100d001e86d427a0b20030b618004025684e41c8500c3c4c1000b6000c1e50003a107804041c8022a41e588041c00800b10300347c002d42c1e1003040b60710b117001185410028000a91001a180c5003c50304810310400344900c0101a52003490420719224901800007510000c0c617802081119002000f0260010b10100002d031100b42c55411b0a0b0840d418000c460f46c0341c01c41030003010740144400519460501000500500c6851203a80ca0a41da82008102510240103d0034020050781c09585080006402600000b812003005030000401111300a83c1405865001c5e80c0702c0300301d4000107440404607600803070705a405080b034204900203c0c50640000c0640304001c0014045000c0c0c26001010070034140100c41e481c2d070004100300d849100e0319240a00800040c0704d6200035601e42072121480e1502d0650441c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524780287 1250 524779037 524779051
    0x6020a0f0905102007081c030506010c0807171605150a02070309090b0d0206030412031d0a03180e100807091406010c1401021b0615060f1303080307050a1205 69
    0x4803500c4c10340b0030019010841c000c2e4016580128140440c0d424010030950741fa070040c4c0c0c2101500c180496501030101e0b01c01820f12410410903078002e9004c90250b01c2140c43e0598000503100f1180c8a29400d18610301519007013105c080e1312424584207000c400141d1200241c62000851642e49031050307440124070a44d103000b00450803180c01000101c0701c507440300041070301c05020840d0060055000851541c82242c00700c44081c0440101101d160f0725101d40c201070003080040704c14650700c1074092a0f96400f110703c010204000d0451124405c05105c503080e0050100e1394841182d820b00d001000c4510016000b5141c041c81007980c001903450032408be072502c200c1c00600d0124191038283c01140e0102c00b44000703403940102d02c141202984400d2000703083e0080f07280e02c0d100d0885144c41c0d500e400c01c0c0018094403071040c003241c448941e135070341d0b01e040303231090850741c10041c1c1d554426280c02e071103a560691018009a10200412051f00c3e0000d00502e506807180d640e4641c03000d81d0178583d0080390302c240c60035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524781537 1250 524780287 524780297
    0x3050709051e09071d19061a070305090301020a1e02010203010f0e0c1210140904020a05060310080a06050f01060f0903140f060901020a0201152103030906020a0f090510 74
    0x150b01a030310305046990810144416602e42d580c9455400d000d461201c5000d6500000034030401c01c003601c000b6000089480c100509102003807424030000481e07401d030030a20081f40b50008100e41058080c038221000010050000e6498010703442000c0c081c4c8920100014860701000e000c450030324418400c5a040e03031344c0703100d8040d00c0c1820b109401003403c500034a00c40110400f000520703209040d1840c010f104000c40210050090b08103060343c100e400301400c1a501600800381800010fa4a82c481e07841aa80c05660480d1256511395900d03e1024041d0310504030343c02030604040520149810051007611000780007046641d86444c00c86d0004503800a104c0000c00c0c00c0d10901c0054801d40310340c041da020550840e450041200f0780d0728140581038584e00c440da94001204000d46030280140c0d003604001001100200d80351461112040303043e81121080d4058603070058007054001e0340414221608604219100c240701000a00036201d1103041d0b2020664081c400155441c140001290107034480d50f030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524782787 1250 524781537 524781571
    0xd0c05150415141012030503130201030b100206100f0e0604050402131107051b01020d03230403080f060f0607023015070309020616030903020a0f0305070905 69
    0x88030440303000508202d032014503802d0b102e12800071600a03d038040403222411012410082d40003030481c201981300c4441512034811080100b508503094990200d40e1275250b04401d01d42e480120000e107080d808140e0704c003080d0341a170751161740e00091182c4210346401010404980307410319903200d540180b0803078510700c10302800140c0506154000d1074100d4400381c0420f0310075104428000907100c21580803002c0900205001e01480000c0002e151222071291001d1007070704440f00000e4a55039160106400d15444980c54030520000c3c0035401202840907000013001e040c140740c0145407600580705030005111f0b42010403c50700e01203000202d450001007140d8a009015800c0c001152252401808031480c1c2c0ba400031942aa240d4004800d018a000a00300b82d5245100d0b0400740d0501414450805251411040c0144c0b80c0b901203800c000c1210140c25122503440c5001c035005503468100a4000c81d416000003085503c0c20010401d403803285051316241902c580d580b404a0b003040f2065458203e480c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524784037 1250 524782787 524782813
    0x406080121021c0203120903010f0504020a0b070c0b04180b0a18180605150315040f0f06020d0e0d0311070c03081b06070203091f020709180501110403050d0c05 70
    0x30051410708280701c0d20b140003c1c1140c00080c02c1c1032444462404503600050340801c06e141c00e00c241c0d00050741040d01003050703040607004619003156900400307100d010000780e50300030300403100c0d1134074000c00190890507611030304c84020388030004000f02c3c004100c9060020300726091802c5807600c8103a940702c01c0b207046440460b0a400b00544aa1100c440010000d40301f9007022030f0f02d42c06254403407420519101910060b10041c1817400c0c1300020100a5002000d05000005901603c24014507820010b0440c0304101820250000d201c0c0c10003084d82c944c5000d001e120074030300104100e6512907498400300a034956651041c502407003034039001407106429802c2440081c4525010300900c0d01d8440900c6190900c2840351490031a083d01d403100560700104960401c1c0c90541001d08800115906041605006110107907450010707010300f0083d03d85848003034500d881601e01014125401000901c00000c1c2c9958031070003540300d4001500c0c14040e6004411101e8003400780c80201c07903071160040061046401c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524785287 1250 524784037 524784049
    0x1516080a14150a0801321015030605100c030810050607020d111c0c06140d05181510050411040303080403020a170a090e0705070b042105040608012102 66
    0x1140c056000d044543c011402c01024480c11408074181000390303c11003050f607181c1d40580d0803255001490825201044040c903682211401201c0e50a001c04040d050031100a4001e40903a402c1f0540044460040c0d480305070307010314480340107802600c0c0e420003500c1d030182101c00b0ba101030140a4000404101010050904150500301c003030081c4500304a001000002907840c1d04440c8581d010603e03421507500c00e0119041d03910000340701608144040d1010b06403807031818080c01c1c04200607140e840001420907801004602802e01d42101601c15200458000c5e21904200341d44c80c5003590b01502000c10740d41454420310808001c2c8101c2d0605203443c41e9800c40d00801c008204501710302510207460300140d00c2003622181003c543c00c14075218803c2401c024096562644211905103c11083c4102c140e082811505100d810035002041542da80c1410302030f5100c180c0114030ba100c41090110301003030f484400342064506581c0d0b4512039980c0c3c0e50a00c4d400390951440d181e251080c0b800300c80014500f007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524786537 1250 524785287 524785321
    0x9060509040f020f0301140a050a05010c050a1721010b0724020a030209010e040605130f1b090303020d0509030d1d04060803030108011503050a03111516080a14 70
    0x40011400000c0140e0b04020380c0c02240e400003032503c0100c0144012409507141e006c441d18166180000b2518200000d109140b1900c2074505001c9003040c608148641408980c9825400507140b80406c3d08610401c51540d02c00001803001703d1508020500005c2440725080c100c1e60708506690611984d03450b810002e82c0100000141901990000505080b041c00034000c8401c0039200141c84032410400549012a1040054030852a03e81d05200c41c0c1e484c903521100c00883d5003400109400072440500051030b0010440f0100e006058003020300d181c0c001a06400c2c0ca05c241d0075600004030f084019203050241c182119895003102039001c503014403d4210f0b80d081070b4801c43d4290500c1e610808241104c0080c0c200603070307603040000140035005c0240a210785141106060b9940c003851601c3d07064499040716001001c20080281d8004088400c01c9129108a0420300c20121418181140c06084440c0740c1c101001c5814140000c038031417804e125224101c1003030090201d540d9600380c040c0c240c10039a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524787787 1250 524786537 524786539
    0x307020304080a0308010905070e0307090216080304140c0307030b06010f031e0606030501080a03050d05130c12050111030702060f04021c060506030f0d090618030605090c0108070201050709060509 86
    0x1051000040110b810401c01181c0c5000c0e80300c44d005075044c060010191100141003074140001000c0505080d140000c80c201200c1c010400142c48001160b090401c0ba210300c0b201a00b43c0c50003105100030310880c454428000c8403500d00310b40040510b00c09041d2955150700c0040d0a079041da000042305540181380418203240140b40006007032841d0800b8800c18041c034607844e4940da80d82c507028885141c051141034054810b04001b88038034402c0ea6001460340c072444240d0b0300050f40303030030110320b841401c01101c2e02100d81c400d01c0c1d80380d0701e03442c0c01d00c4a5618552583c161120b600f0304038a40c2000300f08030201c9001b001329902130b00c9907030b40e0041c1c03103070085070041c000b281c0040400740b82e080140b0009400248403441500042100e0811104140c84c100302140889400d81100d84950056500301c0c0a11040300c5250030184407911640e080400d4041450f40060100c60500003088041a00031401200d4140300340c03283c0085440e040003c030b0882d2800c44420020039110402800320600a101034018060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524789037 1250 524787787 524787793
    0x5150a0e040b0d060b13060515072105070b0c070317130204020a09080f030c061f0b13030201030f050f0114030f0304060806030d05031041012c0105030702 68
    0x900d400410310f030159603082a0741155980100a0f60352a24580b020300790710003080c061241504280000e0300403a074071500c1002104000800c1000c01040d11425105845800c900703040d80844501c02400c5c0707900001040b035074010b08500041e882042c00b0255002c040d0180c0d60421541c104880b0629211406040602c6540313a0310310000060b520b0340014903c1d041542c0d182d8001c1352070a010545018451400a00030350804d1100ba100400d000904603400280c86000c0040005200100b188524217a0483c000724080006c0c40030b146c2064a40d64400c580c404e90b42003003070155007413002c011150284c03848121645000c0c010000100c52102c0f104160b0700c010166403080544103220382c99503100d0380c402ca0114402c030b02048600d2800b40410451b000d62402c1440c03451400405c1c0c9a070034501c50203a00440750040d6603a550140d08401c0000348442c000b8001200c0b407040d041d038001c00b001100d1010307001840314210203040000700080d03501c0c10201b0405908100754200f00642c0e103030704000c001c441148 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524790287 1250 524789037 524789051
    0xc13180f0501061e0c0803040204091b120b060603060a05190506070b0601090b0c032706030a0b0a08011802370602122b0f020408100605150a0e04 64
    0x100c000d2141070300034010b0352035100c1945240004180c280504003040024001680d8410000c54042d0b01200c0d0300c6030741150b0000c0d040c0030a243c14082c3c541d0300c002e2014550b0100c40b02090000c41e4018030102103008150707082c100c6e5a00810400c0c148421111030341c10100000b420071541c249100c03514510b5003062000d5a010b5154004918250411002601c5050401003030203c103503000345504015003150380c041407500c0d03880d480c05c0b9901d21400c0010020310f441a98806514050014410305201e0010007103036690a000080c040a8281c2c003010703521031017240d0000100c010b014030445401000380d42480c20343e940b0907020410341084218540c81100c402c000c05a540e465080c4400c0307a504048110480482d0401400a1924440c2c040b82145003404026480c030303050504078091560740c1c040903c8104210301c3c01c5a0400340002d2800c0104050020a0100d0030f8000468190b9508041c91b00801072941e840c1304000c001d031066484143c66100400c0b281034020301c40c02c00d6034428400644041146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524791537 1250 524790287 524790311
    0x80714030601050f1f05221d0402010c140c060d020a030b10090311040f020c070810090f20030102160510020708090d0302070e0c250308010612060e010b030603060c1318 74
    0x88900e8841036082e800440400d11141c1401123004199004010450a07070340b0713140d40040e200a080744005080d211000e01d010200040412001c1081c00b4068065030722800f40780d451a01a4105150100100f4100707490f09680781800050f40c3c0c801180ea40e0350f4a9500e01d1500c80501c0302c4401210141c005880304010b204101c00780c00103041c1c44001d10f000f004810311b005511800c00c1c0c0c1010900c489507040140d0744020034201d0b0305210340ac41e0000d00f00b10458900785c092202000780d08600a40550001c1480040550962110350005002d142030701c1854000c0300c804401c80c40b4086004000713003420b00c41c00c800707818500ca050344094400c3c012070b00160f450782c05100c403a210440b0404c1610304001001030001d000502c003200302c00c0c00d000b040004c28500340e0380174140a0701400f0340e00030004030313074040c0356102107070f0300030b20002c207140c1c0d0105160756100c0038481e40e290310480341c0500038030680000c207041c84495002c07140040c841100410001f4104100980003603450f1041c00f103c80e48900303002c900c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524792787 1250 524791537 524791567
    0x2030f0c011e02070b04060503010e070e01170601020102070b04060c1101050906160c05030c1b010e0117100306050405252403110a02010c090602210c07080714030601050f1f05 77
    0x4c4e043c10b0b10f8027030312589001440180404014050003c00c4801d245a2100f66044401c0c00c0d00700c000c0000b004402d0341e6400040780203001e0090082c01014850b010300003404200d50101420800d169254080c0c1c808182050782071314800e950840c1d4540c0110000f929014510802040509561505072450b0741c05407242031558000e168141a103401140380d41004482d08100d4100041084c2014105200880000381440744d0000700507450014100020b61180b4002c0103800295511060400c000d0429090265550a00f886105507400340e00510240c00e8554903e0b0604890141d8903640b600d11a40b054010b003281d1010500707041c5070321131014840050b0508040e04518030950300004240a10100080111450307521407010354000446c142946840b1101800001d000380d18070307030390320030103c3c10480c604040ea0b07101c49143e0050b4a4089111031820204501c0403108404031051a41c0712400c100103015240b041950140710380c2a4000311020840e902c0d80c0201d4035040c0b01c4d0808111184071b400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524794037 1250 524792787 524792789
    0xe0901090f03052706070b0916030f020307051801030807050102070b0f0412031109040905070e0403180f0e1f030507060c0b01082e020c01090f02030f0c011e02070b04 73
    0x101280c80494070151882134285070b513010004850300b20007200103002c0407031464030071000c01604101080c400110707907280030040f440e0120068500c86250356a0781c1826101384c18848000c9100340101e407400a403070319062007040c10000904860002591841e03407200d03000c2d80901c4c01121255000e10102c008100042d01c0070f4071909902411140514092410f0f50105242c1500c040c10b041c0b40000b4441100158000e0b01c070510010740b000900340790356003021440c0882c50362110f60617003200300c1003200300742e400656548400500600702d1680ca07103448440d1a402d08900940203039522540000e6182821101111903e0500742410011691170b621000d081c01c00c6900001c01003507014007080c0c208022070542c0f500410280001c0d2000c158a00442d4030001c40070302545102d5818803285032801551035040354030341c60485008102c00e64052524522070b40303800406901c0381c0103803014550307880d01c041091014000e050b9150050041c5000216211301c41c444200c00031480342d000040b5520107010001c2c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524795287 1250 524794037 524794043
    0x20d0507032109020f01020a0c12020a050306010f0806070e031f0b040f06051207083a024209010e0f0c0f010f02030406030908190c0b070e0a0e0901090f 67
    0x450f21400c0b40c0113101c0141040d0035801e04550103050310f000820f00082d1400140c502800100f2882d520b580002000700c040b0b0341000c2e81c98040d84000250010140a20300c0803180404141c03504d580d12a1000d07658024084101c50f0503802150401c801000700c00148030881d44950030018070f0b84002c00204048a19205940c0103107581c90505016518185035003220220007000180b4006080104a5889011654150042d0a24151460065100040c010701600c0707050b41910404001d0741d000030354818266a000151f24003108903064110224400741e22200155a0f03940060104800d02e00b524030401040c00c1203655851000d2150303042e05101000c2e10041404c0182b401000100c20810025083c125250500c01d41d40c3c0300704030554011069400b203d1081c140050b1a640c1420300747c1261103003c111148020951014141c01500311105c51a101d000d02c0c0ba8510545da1003400b070f5102418440003a80c0081c20701010444441800ca00503400641c180000c02c02e07158980c0d071160b450903603000807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524796537 1250 524795287 524795291
    0x3080103173c090307090911100921051914010e03071403071728050316020601080a02040e101401090e070317071103030a020d120c020d05070321 64
    0x42a15a000c49044a1202c505082d0103281001c440006695113000380318144c4440c2d126215031081c07100d41c0c080784000c0040a0704c464404480140003c0072484240140842001003140c1f843d290681c0c0700c0c584010640c400d00412650741c003401c68200010741010110743c80b101912160168035028028040032008210007951148110b15214503490820b10003800341d90f0052207810080b4507000002c089841074818069942e20305404140c1900c5d200300f03401401403594412142405600600075403142010142428040384030040c00ca072100404c0c490400690b02071076404000d882d042d072201160300e90b800100c55010340000d901c1016a910107080c029610040c40042040c5901409400c0381d0854a001501e941d0b400c40e599112641c0c0498159140d00001140c1c0b14200314208500030508103008044a8441c0380e0340383d00a69400d000f6000c1000101c0350a200c0384100002d000d03605a40c1542c5d00a01301c8441c04606c229429042000190100711103a0404541d00703220b330740d0f0054030a00d21140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524797787 1250 524796537 524796607
    0xf0315170705010e1c0b040606050a06090e07030e0607050f04030611040f060306150509030a0b04151a031024060e09090c01080f0907090216110603040308010317 71
    0x160066181048090003407107029640000da880004903109031546c055021820794986045c010f0041c1942d402454101e48144c50203d0382541120f041011905500c800611955a00340c04a040da625800c1c1140240e1004000c600514020700140000741c111001050410b952a101c1c4829508a2062040d81d040009810702c1900030100410307000d010503003000c0c40468a4008c0c46444c503015081000b04102c40461828925507051008245054102c100345000d0300305810500e0b400c1c07156216140a19140160710203e111015481038204100200071b071101904d00d04184014029a03646540e52400c3c00d00328400c2e4664014800b0301400c0c8a9442a1810300d1000c28060305200c081e210202552020b52410082e03030b84074000c0c550100c2c0c1203d0b103404036200c0403059131401403103030420a500f500114040b022084a00d2008001601462040ba007a5880106000721880291409400100144014804036030361801d94600725a012904a160109000c0c6008209501403e25890141e648d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524799037 1250 524797787 524797789
    0x1305010213031209210309030803090d030f0b010203090907261f1211030304051503100506030f131e060903080c0901050904090503070204180b07050304030f0315170705 74
    0xa450304103c00e25050800545040441c2d088510054824100c9a41c2e0b480b07181c00205440740070030800540d032000910f9201d060400741d403507c400503004414002490070100c05108100c600a00a0403101a005107103005504400e025861307000400100900403104042000445e03140101406040c2032031f04a402c41c2855142c461004c1c58001e41480d00c04003c0d041407084806c600301020660f0b0b231001c100c003041d20040010a066005075885284e000620b80355031500000c0c500c00641c81491075080003143d80c5d450b00c003048810700003550b1900c00d0003800d000250b030b01240042c600c10f01038003038070101d04840700b00f60300120105c5035400101c41c060386401040c000c0541100f501c54001d0303d00c8170030904100c0803400082150058441c943e01c582c0e00d440320341c4103104062084928498010b0424403004e444111020281c08003004119403180750300002881d0b65202d01c00b606c0c081c1e0b82c99030b41d00760b904004c40800c0b4040e0806030082c4020303181901d000540301c580c8200f01603482032990060118980b07020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524800287 1250 524799037 524799053
    0xf15030f04050d0c020916030f0c0e010212030405030f0304080c07060e03010c0e011e0509030322090204030c09020a120c2303011203031d0a060b0f0d020315130501021303 75
    0x283c0c1c40c100b4020460b80b03080043c2d850164441d407101d4100c0080b0f5411a018104402030b000400131280780da45011a0504440d5011042e5400c0c030101782c0032184140060000144244030490700a01a40c1080c81003200b03a001c1c000c0250380060007107400728101a594105681030407d01e501c0400410714442c06010103060078081c000488010b030510b40261901c5c880060706c400e007040d0010122804201400011500070420f98130744080203422242c0341c00b181012883c4015143c22000c0c1c036178031050700c0010740021500032681540d60008030080000c2c41c003010000a500803000b030b00f040c0304c100c00780f8454601007032140c0030000089607264408000500050b00d080051150340c003010100400050042c19112040403001d03644c18038001985554010101a14501c0c0700382d03211581c040c0d2080a005c5c4089031300841300b0398004a4a50038501242d00400640b43d00c0e11500039003540010b40c070080c0d03440c4595035090380650324840b035011a2105584447c04c99104a4450281030314107003060090091513 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524801537 1250 524800287 524800303
    0x605040b0409110913062c030406020a0237050a080a020121090b0106081f150c0201120618060b21060d060203180d021b0f15030f0405 59
    0x180d800b000020704680b580000141003204150140f1101c03400b0400c0394960502c0003030215080b840c100002c41002c254085082d049401d01059065101c1c1142020354020045034100c0d00c00740c008102402d0790758240300503c240c042012441c0c0c200b00c0003000a0700b80c0100201c60240b4050504181d4600b00001c01552004680068929a00400740b220050b600316030b414000d01d1800c80c0842c1c00248401a2078007502d0381c40e00003411018501c000003401500624800d001e81c00e00701c00c00301890401440c5075a032568610580c44c00380e201c00300a1182901030018401c07881c0c0103140001520a8a000715420b40f09158803030b80001c40115181400401c01c0d215410150003032081e01450800303022a2400c5074404240c2c44c582d41c0c0364060102d082a500c0e4018242c0d260340c448004e6490349082d00c13044004041c01c044801c00303801528202c20840e0b1001c5152900e0080c58085280010580c1c0140407141c01380c012001c2d04903c10500180c1001d8603800514890905090f05822600e0309280490802c901 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524802787 1250 524801537 524801539
    0xc0109050714060d1107060e0d090e0f0403030c0207171e010203040b180703050a0c05010f020706050d0c0e040905010501150e0a0b2802060915010f0b07020604080304090605040b 78
    0x205640b02c80d10703a0b168011242c0f02d22039040007043d0000110880902441440c400801d110f10b0200840320a07140030642841034941511144401e070703512100540108000c580e9400c1c2c41d818540000c0001e4040e07032120724000f00c2c510456030b03e2901c590345c0421f181c02c00050f101003588400b170520030710244207210300003501c0800000d5056041c5541d03680310091002e4121103d510060075104100c00b4100b14502c021a004003c031260b5005c00d05100300d03107051a01070309002640c00351181c90681d000199000403070300c4541d030b190315060b07512907203000a180c04100b107810054140041c24296031b82d070041402c0c590040300000790551502420404d140e0b5284980d0051145201e005c0c5050340e90006901c085510b8600405da03580c5146c0e04c0c1d2052900718690354600c1c00620380b4168034442d40082e00610801300142102d0310025004440440d5080c24401c40e1b501d214001418046154100007901b616480607241500300340e150035880742103400c99003028030341c2030781c0d400104050728190107945a0418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524804037 1250 524802787 524802809
    0x7050f0601030b100911040b090d060f050a0c0219120c0506010b18012a17160b0a2c071208090a0504020c0309040c090816031a0702210d020c01090507 66
    0x143c621b800548138003031482041c550030b5021502c0d8449490b44000780c8551603100300e04105280e0303022401e5006201c1038410340c041610b880400d024607800001c08030094441c4540620320000d20342d0303500203030b10100303000318040008a05100c00000e0041202501070b0010b14621074a80100100ba05a01c0d003084d1000c42c100190b0861440c40c400030302003107801345500d494002030006064100100461442004240d801c00d00254030f42d2400022614042158416800309080d51105034050041d0341030402c1ea2480e201ca00c12900d1800c8840801d041c0c01c103040720080d101d68661310390580c0504a804082543d98500000380c40c2040e10741040c00c1e1000c0d2100715821424090144500780e5030740038200101e4015503890604000729401802284c008003400000c0351308400c08100c40030b80200380ca100841361000c03001c08076040190300b07a0074075100703c65903402815034800343c0c412030411038041e0051000544007000f07148500a628001030020580800001c12800c00e240b0f0b1807860001907901620040c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524805287 1250 524804037 524804051
    0xa12051608040b090102040f0303020c0301050c04180e19050d1710060302130315060608010518072312180d0203090f120607030b09280207050f0601030b1009 69
    0x903401148942e00603800021941c00342d03441014880c020310031030300525020307003207510004109030703001400c02c11094040d03000340031075204c0f640b00720358078001c5018070b6071002c0100c00c0e10800c00610350300903486410407030110307042c0c0c00c05490459502c005a020a55940c0c0140d9803013a41c031a00051912074540d07480c80d80c80080d1034594581034801c109801104105034001851412485c1000002d1000d150045102c4030b031041900f144400808032407043c4030118160400000f094a03180c07441070103d80f4088201001c036907403014219510381a15807090072101050281c3d80064482c0401703411200a003081c041d00c141060328580da554440300c01000031a5100314111400f29a01005413000c1c2003040c6c8040d200503501100040c10481b034a030f401000da106080c204940603a05400010350100c090311480c0c0b00f9103c00c003c0ca190b2801d81c80041c05181c100c611105000300003640141055405101500d41d402004005182000380a0344103444402002c01480480100c0c992448024040340d00100320302 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524806537 1250 524805287 524805331
    0x20604080304030c0212060a0c0f0c0804050d0206040f14120c0d0303230f010e06060a0509011805030613060b0103150b0a031119030c08040f0f0809060a1205 69
    0x601c40200010304110f002055041151034441142c014401501c090b21801e03e407841005000744901c2c0403400000d000c20000580c0c89000304100c0407010381104602c0e00c0c1034105005e101c40e012820008a170040010080019100601c03200c50700900b01a841c1e043d04050b400042290042e606200d0041680160000b5540e9070750786240a2000c40e0305050200d28010002d1609008041c0149d10141441e9200100309d19000012000743c10303150084046564ce03210360080c0100d501032180600003080b01013118034440d40c02441d581088044001c5c01500054480010a04116080d21421112000103c1040c104801c500410201d100d080ca010000440845580e000d044050701c10190460f030006452a1003a1080d0410219035260340c0c2c0304c2d07665100c640c03e180002c0700c2003140c1c0f20019213000a02042140f0a05059010b90380100d40e5489800b0355807242c00140c03040d81011141c0b07400070841e5290f261200e0014100c040081e03110401c0c181001d82038141030b200700a000c10150001c0c0c8000c4c55103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524807787 1250 524806537 524806553
    0x1061d0a050411031e0f0703020a03141207050f1e120d0209090f070e0102010c05041e0f0f1d06031c0e1f2706031104260d020604 57
    0x84155103a101088584590034082051106111007070f801d405881280034003000c0001010031500092411106c400c510f0181c40ca4403010310340070080d4452143e44082020a000015480d0000600825940300c02007101541d0f0311a40110b004a4650300035001400c0d001c102804409110244d803901420301002400b0b0807621440c03411540312001c40007003443c451869240c0c0c10759005250250100103d410880303003900d05410100d500400142d420619a800ca5206020711000700002c0d4940d64105400c0c9030340d800034281d110130381b00016030390b424001078145c0b041e42d180c1c40108852000003001c5420007042c45109034038594001098000b442c1841655140016400321664955410001080a841d82101c402164040499001041d40e001a4000003100f1040807696016203844c9800d1000044440361032212a102050124406400304045030090b00494400007114091a1070701c2c0d281c628003440c10126102c0340c0c212520b0843c0319281001e080041020104050005100311300d0030340d9450fa0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524809037 1250 524807787 524807791
    0x30705010f050d0501080609060c070f020f0d020a0b0406030c0203070b0a1e05160f021b120106090e01091b080c04020d06081b09060a06090314070b040308090301061d 73
    0x41003081c984580080d00b4840d00684000340002a420f1109503500e01ca000e60b40d2005562042003802801c2c0440c500c3c5003042c0494600b140e1004003019014926000c00207902c4441c8481034000b054944140010390f00c0a480300701901e00c404100d9265800d0403030007400c0781c900c01000c205640c0200712a0000c6083c007400307154000107001700460814491503801054112880300395540c58189000d110240028611030b00a44485540741c036441e10f1884022691a0300a0518041c0e05010810041d0b032802c0c540001107010ba912030021444944d595503940455a1040308404e441c2d540742040c00c20400c101400e0041a48180440b20555091102141c0c841e01c4200c81c29124981c0056524258096600040010300d0307810103031003601c0c1111481a102c038281c04403540c460070b21303c00000d00c80e242030900740003034a2040d0b076080b95480c01e50b030700d410f01c0214011804506205480c00041ca0722282c0c0d0041c4051441841840d4451103084203250a494194000010640740d03115281c5441590700b076410303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524810287 1250 524809037 524809039
    0x5030c090406030c0920090607020f01051b06010e0603030c0601121a04031d120712060207140706080a110a030b13050a060806060301020403031b060e06070c061a030705 74
    0x80c0e84241880c0020020001680020081c81d0a8180080c0401d8a070740060801d5070010105005040e030144803101d28480d1105065001c202400107001504014040710348000041c1001468030001c008098003410a0300202c403407540c0120010300500d06101c079800d4200100303600035810b10b4580f81e0010740f200414000c22854040420101d82401754024600c803d040218030201844d04060800a03c185440c2d00c804038864111944180e903030a0040c4101c08202c0c080c0050710354981000346074001581c80a0003035588035024010200425a1620901c03001c07a07148005105551905102a00050004059030401c030f1038200600d0508103c041119860035441c9400110070103101c0000740200008112001c1c0645000c1c10070560f40e100d50301250507541d540c41100c10554811003014283c2c800c5000040008000c4000242c00102440b020071440d0b100d8480400e4144031044110300d85030702142d1210016814008240034002c06204d01c4ca1440040381949208168000100313507190464800c407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524811537 1250 524810287 524810311
    0x1e032e06020c15071b050a0603061e031e1718150c0604030e010c2003010f0e071e0e0c030a18030e060d0b0a080a03030506010504121506030f1a07020304060503 70
    0x2812034817410011805080010400c5241a44584000300206005e0080b184000104070701d900c0300625a041c04011294019801298010210030054024000241c126051405c081014040f80030382d002a1281c1240c1084449450f01050300b040911082eaa000181c00b80082001c00752000c00071036034603032043d01814420803402241d001242c4984031803901401200d40c9855410701d040f034200d1101c900e80d5040300284040b8166441c4901111000076100340540e006140030400300005601142c49161a440c0f481840c41c1da07201840c40c80d60045403441c012010001c20814292254404d40403184e9814030f000d00000403550340609050705030182c1511030302c80843d5121801c1c1039900840100e078000303080d400c0041c0d6039116041e903441c96041c0031400300341850002001035110b1000c2e00c00303d41103002401c201c201141c0b900c00015034001c04018845d0b40301e42022020440c0c1500354030940e0300c84c403100d90b810380154441d090a00b5010f001070046400420080003020740c84010347c3d4104c0201c1c00c003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524812787 1250 524811537 524811563
    0x1020d0c1704050a032f060405070b120a0b0301091506061404140f0a120c03063e160807061104060c0803060406050a1805010b1e032e06020c1507 64
    0x16446d402d040240001e0144154446603030a11603001c54014080c501c108100c0c2c4400703840d002c0000302401100c029031210341880000440e0445144c1040002200c0030b400026201200c1c0c5504164005c6c40c00404500e40e00c9490810034164405008241650b001203028203190405400240800800f00c0852240d01c0030001e040060f070b10360400ca00140880d0b01020100c0c0345900d8807032204801d0707200541d142880c1c8030380c1454808461a11459030100040210150b41400c802141d04244981f0000242d04090042c20304410800520201d1503008048003a1900b00364500181030346e4212443d03495492060004200a907004450700032003d070310003441c90720303596001c3c041001426643d20165204802480c00500403070800095089a003d4020500040e0b80f16805040c641c402e11869084d6050b4210003000c3c010350003405541c02c201c007230341d0300d518001c40a086405013000244030006441204a000c025258040044083ca500241c81400401c03a5810840b502d074015510b0190070207001e890 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524814037 1250 524812787 524812817
    0xc1207080a0e030301140f0613030201050c07080d050c10111b0a05010c0f020d0c0f0204050403030b0405010303120e061b0306060408160e01050d020a0b0903010b0301020d0c1704050a03 81
    0x603221410000700f00d0380c4a603900d05103000003441d504c8070503001ea4405040c1c003410b801c00308100e881e0516540010300841d072659004588503803040c0c40e211180c4c01420404244007009108039208071010744c1c0ca440e101c0d100b6144003420609119030400842c0d01d080c2c1035402c9121294117603650440c600c428151400c51801c50181001030041c0010525480c04040110b040d400030301e00d00c5403050079400c441c41000e6403602034400c140d00c100c02406e21445401c0b02c3c0300610381504206d0340140719143c00b2410755030385e074041410b5a000707030011008501d641d080c800f0200e1451190713004119564006140c03a0400d00189088001c07000c040601e0b5207000030000b28152550421500102103140898800f84048009101c1192407801400702030302c0042c000140516003100e0942800e60014050769200703160885a604592045c5002900b55494080300455640c0c00c0c405030000c003403004000300340412540030041c2000d10341d901490030000f0f124180404150300294105902e50725003401910820040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524815287 1250 524814037 524814041
    0x30308091516050c0a06060e01080d020a11010c0b090604021e0105040317070c0306060504180b24131b02120409020a03090204090807020a060302090303250f050d080c1207080a 77
    0x1303451420511410702c43d00204901503110350102c0d00540082200c2c0e92700c48400545402c00e5100481c01607102620060105800001c68903010714141401060360b100c596034029024011500340e00d09802c07880c208400d60510042c0208401c0e070802c04000f85020704000a8081d000303e0002401d0305000544107109195908111140a074205940940c0380d030742d030305d0200090451070007180c0c000ea0510f05c0d0018640e5500300e1108840d5401900c000c0c0729641c2031079400c6d02400340100c4c14a40e05940804d07989940b070321501d20f81145d00a41000c9130640041240d03511501d0440311004c2190300c80038490090395405400d40c2d040c0c03082010056603e900c551003c03400b07440d400f000a035006207449050401c121211005041d550302c241c40014583d80c2d100800d4040f405400001e54040d0400c00c401d0513400c81741c0020b15011001e00910f030349144603588454441070a4103074121202c0e80310700203080e03019800c41e03042944000e00c0d4424901d40020104003250300f000203442d078001d00c0f0014020444c14003c079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524816537 1250 524815287 524815297
    0xd030513080316030f0203030c0d09050709020a0c1e0b19020f03100302120610150201060312020609060f070c080901050c011e110c0a0305031e0a0603030809151605 72
    0x10204a82e01e8640000b55401c0d100f1500d202100032804c2d03a0792206103e4004021740f13110300c99a22009003403d5190741e40d00c4c0078082100003141e00f03020f4020040b480c441648003400e0740001c5552443c00c0140b20b03141c071140f0505c41c0c072450b80c408081d0407004000a000b5646081d4021000e00106000c8a840f528840c042d005840011901050210810200e082d9018180040700c2c000c660215052054000640d22403030166000050221044070031b120118007020601140c0109100018100d40e60392038407009210380412190050b000541400007a0000f0002c150704110140721203015401c08030b00103001501841c0000f0055a4003160300b18160380181e06881d0343d020074100078032140c5101550107100110060003450781d545400d0310142c440004500351561042d0500040845042d075850541c1d258000402501c05402c0c1d24501e00d565040407020396002e508494000f24940d8110701e8042c1030f0100090000a2503401360340c54103240d06903075001c40d411091816413000c3c1840e01c55000c40350385c031134 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524817787 1250 524816537 524816549
    0x50628021e060402011409030d030213090f09020405090601120f061b0c03120204081504020f1503010306050a05090a03080612010c02070e0603151b12011217090d030513 74
    0x8544400341070070303004520b142c4514802d07610b0345010a00d00680b04000d025a140c40d64040d80018540804203000341e0003001000c803050550b4500301c1e9a602c0da00c00343c60714840c141514a840d140030b041141402d0240d070303402ca0464000351200790b04154403041c51178000384c8007800700c80c02004210284030080e405441c0b40a01c5e00300789031809550741780241101c0005c01c011400941410104c002300c9807103100f542c0c141c4989001604035480c01c10210b0300340000191050340c2c09101e035403000480e9551014002d010f060040b00c00c989a61460909204440000341168103890802d8200003000d00046804062540d041c10b01d40ca554440c0008920a820003000c94031f46036291803201c040d6980c000038144200c80407003018001c0c41e40d07144180342d110740801c64820303074000c490004a0070980b12800000c2100c0c0003490041e04007a22000e610038075110aa01244118440c000640140400c0c943d8041d40d850050103458130300b1001a011503050540040040c0030018080380d22038101c0d19010010004101d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524819037 1250 524817787 524817823
    0x150c1a040f2a080327010e190b0c0f0d0306030201050d09050f060a09170f1b0307021302120a1401060c0609020604090e19150c0e0a030605070905062802 67
    0x14a40e0360503a580c0e8405107840a900c1c06a08482e174800d0a0740503902040070041c2c4d545101d1420003810b0182d0018070701800c050f510768407600401d0009030880038000300e0380080d00400f00840e0740e0151504020b20103203400201401c2c07000900150342c0200403a00000c0400c0400504107103181001801c02510003a005c910b80150030a00c40c0c003418980000f000a80070742102030b45020f940d40142068070404240481e818424092009100e00ba080312501d8600008256880c01c001c990005068080e1055440001075000c40c902c140700d0070350264030b603125260390810482d9501007008202d00103014400c3c4801c0000070707018401000220303080721403a2a4054121030b1190784400941d80641b14160161601e031003501604520580c00d5030310031820603080020590302511042c0908003500c9040b081f80d0601c00d41b0181b401141e25203002c00e03001113000703200001d000d00f45140c0007030072040154401442800b0034050149034800c0104941c807164403d200d00719004400000590504889c1c0100800b149 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 524820143 1106 524819037 524819039
    0x80d11100c020f03070f0618050703080c10060e061513060309141c090801140c07110d030305041a040506040318150c1a040f2a 56
    0xc040b44142d81c0c1c4000000055031642c0d010400c110350f1803080d2280041844500d200b9100300108041c1a0500c500c40758844c5d0360780700000e00000d855010005059840c00c03008102c01c25861030748042c244040366890411000800c1c0c1200d0460003000e4450220411750000011980c40c8210030106068107802e00200310010004410100c0340c1c0b13035502c80006038124003080000c42d07050b030b44480702c1d445002e1050028100c004541c0201401e0781083d5504501c2524001038507804007034510750fa46c5501c500d04055110648001e19181c111000080740b009155140e084144103a018090340c01464201d0184448801800c0f01c5c05441e80d0461408a00020f10991110400644603009490020f444c1e038001402d2a04d88840304011640c1071001004114034200e0010034a04501b00c0c809d02803602d9240c980b441c00c0b20580c01000c041000c200340e10102e04880725104c41c02407010f0501c041d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 524640287 524820143 := by
  have h0 := BRFrame.cov_init 524640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 524640287 ≤ n) (h2 : n < 524820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
