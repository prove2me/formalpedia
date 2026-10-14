-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1982
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:53.724017+00:00
-- url     : https://prove2.me/submissions/97efefce-ccd5-4c54-8829-06765d77db6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 356294964 ≤ n < 356474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 356296214 1250 356294964 356294971
    0x30b0105160204050c0c0601030b090c1206013507050901050114090616020d080d06051804030f030b0a29070c0e0c12090a030e030303011a030405150717100608 70
    0xc400084c2941e915030550315070f124104034412148544000001040407500311301c0c0c80b42e8600710a46007042d041030148681125030182900050700704100602c150000000139121940701e200c413040520050300d00e81604040c1c1d80100010030b8000800a0215080c03504003140144820300c0e0440000000c413102c540a40241032480e441031324000380900107603903034200c46014144c00502060101410345081e1800c0c0c1d000666400c40d260915400044074541626071484480c0030070818070b2180c0d110741c4c2c122407600c50000901c0905540c0d14112407143c07a100f6640c405040090520005400c820030110074144012040b0146080308101100024010b20818812240d51070304000a40e2211108043c0ca806a942610040c10301c03c01000b5400c1400550262124043c0e1a101c8011810800b403607103a2109009124600200303584146880110900a590150080c002d80fa0b503410026010700343d2000640c1c2c0000000d00c0c8103210021107840800e0344e900401100c02d850006464210f01a03d884c03c004c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 356297464 1250 356296214 356296219
    0x31c09090908090a060c06050f040305070b040218130302010506031b010f030204090f0504030f030c1b02010908030a030e160e1b09090109020a031401081c020a0512070201030b01051602 81
    0x1428128200300d0642c0c00e9541d000e00090856840300e480d00e10041080e0300c40d203c10b440440c10880803501c9000c0303041640e400742c0c0c1c00d950740394a0b000061b12042000100944101d80007484e0050800710104803030001c0d4000c800c060f1903032412851508009080d1080907015a1282e08130f8000311240300311a0504050700701e001c1c24044046c005c0c04034150000e0090b030f07000010982c10b100e803440d014003669021760b104900c2500c1e02d5142d801100c4040b4102c4001a03034907000328911102031a041c1d03844148c0451254414074041000c603858041040c2160810311041002c0390b2500800c03540b0320021720000f0100d08100b07240910740b5141003c2404042d0001d0940c1406010011001a51216403c212000488080c2400129595480d440d000a500040380c0c0000039280000482100c40d91460f214100c3d80e4a80082044003100c0401c0e2841883e4030011105500c00c114510001034030038030050361802c204100c0c40ba01c0d000b45000140546040d10401c5042090400061410300c092200d20348646030107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 356298714 1250 356297464 356297471
    0xe010e0c01081009090f0308010b13030605220b0405060f0f16090801090c0816051305090327010215041208092103011a040b0703050d060f14031c0909 66
    0x1c5402040600c00c2c1500139484540c00c00c2214414000200301e01102039109944160441e80d0b5840144a14040c90a00c4103d1a440c50380c02c10200392243c000c0d54101030405440c0e24031010215800342c048092500450b0854080b00410003800300501242d9804407420181c0052840c00505a58007140d0040c801005000b180d8402003041c0d00c1603145501404110307000308030300c05950500007808207207441511442e200d00010f401060188c041c0e1541101c00182240e110108114007400142070020007a0700148000e0000c140000803100c51034220310221401010a0010070000a0405d4140c8540d818280d008005110020300009a01404040366207040a4141c40315201a814500120b455080d18916400011440c0d410700009504803480b803005410440108010780e81c45e40202c0c4688440080e003130144d0030101c0d0141c03000300540242c02c500061140d8440c03210110311001a00b000d0b18190f0003540076502402c00304424001c51003000c4802002481d141c03001884203215000e94111180c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 356299964 1250 356298714 356298721
    0x906150619180e040b010819061107021819021306081f0b090f1014130305010510090f05060a1503150626040812040f050d020102090102010e010e0c0108 67
    0x71401220780d0003040c003040403003129030790a0b80e001c3c1c880c0282c50944044a036980001080b040000c0d0030407140302d0300111441c4990654803800014591036441c07039607452007040f500005945100e41c0081d039140031002213030b02d4101480d9503c01e100c940c2007000c42c1588100914520925080d514101f207441c0d900d000c44481d640c0a281ca0b500c0c034890180046420140c0030b0100d244c8200d03e024116084041d100c4203142c0240004001c0058420080c1c00049941030244040c0b055141c4000d000150104030300c400710f961f0381d50351142117a02c2200c0c2524039240500c400c0c03040711142d00400308a040418024413103403d01d040041d90603202d80c420050420404002e60b100d490080e009003010000e0208842e491599500d0050005842da0364542c0c000b0142c040307075a81000c08403c10740c0c081d580000009080007004c0c03040c80301d01103000e4805da422121404034080020010448082140070580c00540c54600e2480064252040d20132804d4460741003840b2445800350008010781084024a00600d4646 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 356301214 1250 356299964 356299967
    0xc060903020c040906050714270607050a05010b0405060103140601110c0603100311061c150806040f0c080706020309040902010c020a08150f010501080a09050c10080906150619 77
    0x80e010803040e42c0040c14140c1004c2401002d5008a00c5203250303458000e0392030b9031010300d25141d2180361b00003600084003c07541c0e106c4641031402c41d10248805804a890000c19440b0180303015043d82048035140c1d1210034940341d50410b8001c15800800a0809000d01c0c070b81c045c64014989402040341d410070902c05a040000c40d4100142c04aa2101a00055590504145004103211103020980d503e0424030720140642c03c0643c01c454060b65400c00140d40d01803002c4008024002c4580c450b201190036130400b24000000b80f00ea940902e216481c0b2006210151401d54960300c4141e209402c0d6401c0044100503640d00801242c00003030089030005084000c40c401614503901e114006504401c0c05131011400c1c410001c0c9441150316800c43c2c840d000c1c0e40380d0310b404100b0300090159500090300100407840c0200c15030001004c0720311a10580e40040310740c2011036410740005042100140c0d0a0040c0300000c5028024250481a0098881480319880c004549a849500541a00f1064881191481c10b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 356302464 1250 356301214 356301223
    0x5010c020d06020d110c070501022802130606200304050d0b04080f040e0f0903092803062d020301080a031202040f03060e011b0207090f0e01050a021e0301060c06090302 74
    0x8500f48200b0885c400f000700b060196030300182c00425881c03290006c00f041ca98000140406142c1da0340078651103522140082080507009244104d03000050034400d048900d034540125009080750307031b80c4c81d14900550f1100d00d03c2080c1c140320180d180e4104210901c000e0310342c40d069040081d0000c1c69904584c4462401d050944100e0f400b210074003101050100d003084030300256500a0085034000b4003140c03100703806607407248218010a640950101c1501d0806207802414142c07040c803d1a4009016940c0c0c0c071400203582d80c005001480c0c07030001c8460303c030420306001c0c040204252100304509660605c94040d5440282000c040d06100241812441403070709038048401404940c1c5400086a86e0b07490f0000140c801d41134030729070381e500301200001480301c00d441a030340010b0300c3e078002c041640c03401c40210010078084210819058580076003082d424400d01941c2c0c000c0c000018010384d1174110030038014954800d103103092a110b00800040004070307840300c05900c1e81d5801010001d4498601d00c2c003603151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 356303714 1250 356302464 356302477
    0xc110f13020c03131d0a06080d121b0e0325050f120a05010b130203070228020306130b09070e060f0a030b190f0c021b0126100b0405010c020d0602 64
    0x14031050342d0f00818100d071804d0300304400c0002c00305c843c68a51540482c980c19a0784a001e51120366100d12012113030280710b80e22084a203805807000141c40c41c178070500c0752a0017000b928040042160104035034124201041800000c0101c05400c0810f11201500351150f03144a104041c440c42d904406014550794000302800c4940c4000c2c11128242c0d0355241260107088980e9009115084001d51024804054000c407889a00c882e8090000540c0c000852051010b01d26400d520301281e03a01d1682c0141c9007004a94010404400400d03c51a860701c0d004680500052000c04030b600714601c00c00521804945294201d0000c480c60210f41000b900442c2d20f10085a00280000d5100c4082c0106c03240072404070710020052a50521a0400302c1c07840c501682c5034800c0100050344000100d040114a0f981800a05081403416000440c04050b00c85800d0800a80400955a0358414842e1000810b9201300042100c3e104c005d003000d1074100060180080802c1c081d001b2041c11412004000840d41151107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 356304964 1250 356303714 356303737
    0x409081b1005060d020d020904080d18110604120b061306090b041406060405040b0303091f0e0406050603010b2208010b030601091104030f050703060203070c110f13020c03 75
    0x522126000309a40c40c541c6030400d4640600d0400841c3c09414809100d100040e00035240c070005903903603828481414401070041c0d07526401400144007004082c01a003c404000c8285501100c0d82d0341001409030603007010080c4140e41c1044104080a40c48081024039a007104101d5429500c1101081d8030a0491203407203070041c9002d101240da03410550205104480980f030070814003080d0140d190803901c05494a5500c003800384000c001501c4e05401100c1c080001405503400c02440c0404241c0309860740c1081d840140b01a800d400400f640b0201c1d00030700c100c0c101c5040c02104d103442d0100744140303c1801640090b540c00150f15101c0490081180d40101070141130030340466482880314020300b004400c5500c40d0095000000307443c5800d008031100d00003500d50291600f4a10785d96840c00a04c0c0810407a21401107010000100ea62803000c0d51042c8003a46440003103072400d28011b00d010340542e42d15403107014102c40c1e4021342d80314200744903511208580010395071340f01141000d2031802408003040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 356306214 1250 356304964 356304997
    0x613060209040c0807020d0315050f010504090203040b041713030f1a04110102011a031e0f0d0e0f09041a0a0603080712090806190b0114030f181b040908 67
    0xf000d260344048482d10810496003542c8030603d50503012416140118044610400014801c0c0b10514160b040f051350004141446031130590f41d0710556090f60400c80e4240d40d075000400400c81800000b25010313808100022911749480702062002e031002410f408054105a2844501e008005000140c4032400c01840071314031982c82c0a103004c0c0801e0000311100e5005500f0301c880d001982103044500201060000c0180001d040918000081c031400840d0b10a200d200790b2000c01c86229042c855040e612405968100710500f00320240521031410b4055240101100c2c000c00c07000c01c04401d134500e0482c0800e85014402d4451000030000342840350000740006030001040c8003001082840d0314080d05440d01c03080c030b1b01651a040e4903110202280c03c1810300303112a1740601803005076401804d40607414101b5520a100d00d61110107a50000c41d864810380819005212001c1a130442c0c104000481a000745080696640310b1120321001d2654140641c1d16007841310100905202036800140816a454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 356307464 1250 356306214 356306231
    0x70c0803120103020f0d17092d01031a03150604060f08011a030607270b04030302010b03010b040506010e090a090206130e0105010c0201050304080901110f10110309061306020904 78
    0x380042000c1c80103e20540070303500241c1d22824949903100005802078204007948160340500421a0b0048c05102d0f07100740d0390051081203c040180d00018042e442d070342c1c1c8480e0001e0b64005000c40d2107912400c1c2c0c295a540c01258010742d40050060a1305200ca4803143c0c59440d044003080250603980c00c10340340e0700183c0300045547c01c4150701c440803164000801001c850110b506050b00d03500c050b01c04500080000242e070074031007085040501c00c1002d005503004c0c0765640d9100d004040d0801c1e00110010f0b51500240611840c003402020101c501c200c6003007003e03081070380c000780110a00341c0c0410b0041c1995030020b5a0340707190386d00503100d850300034240d15910f046241e4580100c03030341c9005003815240500000300381548200c41050074168180c542d986980c4564480c400240c0000b03014030304212241900d0f04a0711010b225600041500100400c000c40b2024010300030307115050340076080d004080c410021f99041c00500a03404c95581c02c0200f1000000341842000380c80b9400c1c0c8281c01900700b41c80c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 356308714 1250 356307464 356307487
    0xb1b0f0d03140f0610140d05100501031406060a0c1e03200304081203090c1f030f0b0a0603110d0204080a030e010201140708070203070c150225030305070c0803 70
    0x600b11054880c0e01141c1d82e0303072814a0100344080990781d181d0010300f50b1440c201114003484441c1d81e5100400c650303505006440c0c40c2c4005035503046450880d0f10909000030022940c141c0039140d060582a0b1060074580b4200011034001d0040c1a0920200b02c8901c02041c1030003c1158a8100003101c0340260840301d60070304018040f80d810f1162244a00b40a42e030311380c2460404015a801e440700007002e010090921100c940060308007410004803406240d03104d2016941c1c1c1200d40c0641d4180040b40c0041422643d0040e0488046108581c0300501700954604c2907034480050006451040c14002521903448a0403003080c0505d02d115009180b000801084040001910400c1c00c1c0c826501c0c1c000c0904580e004a0030b94000c10503070a800c0c003204d03010861090084034000e034040120320449050000396190003045684682c400220ba540c074901041c121541442a0072040500140744480b00c50703c2000070360800d95512004d4204100400d00004200e100c540041c0142035007011640c5401c1c8140d41c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 356309964 1250 356308714 356308721
    0x20301060e100c172a0f120910200a020f0d081c111308011109010207060f0219050d0306170316020d0507030f0314040b1b0f0d03 57
    0x8100104005503076125561405031112055100a90b80309034070164a9650008440040c095070401c0c210148030070035010010502001c40c1e05801218840555007180d201c07070410039440c00d0100c00d80c11500f46214545d00000480c0da4225081c1c6145154082090040b618202000620420b01c0f16500c032095200c0f40c00110050414000c0b1800d1501113840c200f0081c5180d07031440c00918203032051199a52000b25071a09108080203110003041014040b00c450715241d101002031500500c40c0c403402d00070b91700248504803d80b03202546440c0303400c07420b0b40080c0d959441c900c12030041050759000700c02054402d21903004e0103140c8100c40c4510031001d1070143e8503120340b8440400000e00d49500001c200451015444421001001a40c070f02500d000744201d024404944c1030b6000040000c0c8140058001c1144c0f900645c000c071604910020a8a0014002501c0443c030300816041404113000d090142c1086420360b00d18951804051800035915030704010034840028414050000441400c540582 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 356311214 1250 356309964 356309969
    0x20705071517010e0601030b0f03010c030207110d11130b090c0307170610120b13050709061404091d0a0809040629030c0403050307050d0305150f131e020301 69
    0x1242e00c481c90601a8080054880901ca007480702140e00c40452000d500982c443c2d0810007007d0010700e154081c40c0c02090a4415001c031000009070300040a005115000c2c1504100c000200d030f40000c0ca40301e580f25030346401c20700b4400b284203100e01c003400c0c0c00c2043c0329401000303403079405011a444d900d485401e0310f01e6500b0440307000010402c2200d41c80081303110b1800031880340e04000d10030084920091030491b959100d40100d0040503648040c1c3c0301c2c141c0d45180513070301101240f040c04500c0e450802c00040100d5499030010040c807099107034035040e54018405450540f49104800074641156408162501d41d6401520610303014503c2c4450604c00c00c038004140141055a0900c009961000450500c1d00e14841c2507d41c180d400c464100842241c0c00115044801034441d982070603240d40303880e0700310742c00801c08991580c8814441401c00e601741c080c00b40c0c0901c1c40d910005d03200c85034a000c039400040342d01416103c3d5040f14141640c0c030800342e1102c2d03100c9c0c034641c480e40113070200a90040001d500a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 356312464 1250 356311214 356311217
    0x1e24130306020d18032102160804060905010507030801051e06070c05121203010b0a03020f0a020f0d03090f03082205060609062b0203030417011a0619120207050715 72
    0x1444c40c07a00d0b4059059018010b035040e9035041800359081014034011412441122045808011120554441d40c012100f25402441c140340e61703e00c3c041d0003421440040d4401c9041c04002d111400100b03410040c3c1c241100c0301903c108040035140352090080c61349401d0025840200030441405100c003140000381619000c0d03c0ba00080c11101401a039250090004541000420001804010040c2010304140802e0382005420050a484035410b50740100350321100591044086039200c81c03040105401c449184d0504004c106180d4032a1103000e5140d00010f004c0c080c4000100d1320a0000d560a1080e000801040002d00c0080c0c1c076080380c03a1841038900368450320212010071140e280c102100d0901c69003201900c1c0030805000c2c4100d01f020706410050303078940803d000018040c40c10419046040ca205400015000d422401d0892005520341d00c15018850900070b000f0943d02d40d14140010320510b042c81c80c40c9030394164001d07010b403048440040c0340d400341000000340e03601d89101c503844c4090036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 356313714 1250 356312464 356312471
    0x90c0809010609180f140703050d090e19020703170c1e091c03170c040e1e06130b03071202010807021603030c06090b0907051e24130306020d 62
    0x1d955a03442580d103a84c20204425902828007030004803580b24035801c2c1403040c440780c00301e1a0181240d40c2440684d5205803125042806101141e581c8800201d010303054400b40c00380c4a040600700c4900d40541034082107040c590000d90401410701521210300c05844150300e005162401c1c2d4880a510303008030035402c1f081c8020400c688010807415060b2068078001801d02a03580d00c03c40c51000304004554010703001e1003d50a50040511400c200c03ca101c1d20716440095552880d00c020406809002002020076458200400c1010030b05001c00e140c02c01002c590034800c015006419500811110300c034268984204040080c180c80481c0084038054003d807290b0303c02307030f5900d0b8059031160300c3e08200303a000210140e03080c0300003801900c9007014a03004601c0010500155901c00b402c10400b600d442c1074960148000f00458640400707201ca0151040c4040d0100303144000100d86800c1c03410150006190344141c0c0c4140c29034252041d0380b2000c0c0b9450b0302200855403400e000000b98040c800c541200da04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 356314964 1250 356313714 356313719
    0x18060c1404050607080f19030614010e0904030815031902030d08040503090112020d020a0806030d02030c060f1b0703080f150d170409060b0c0106060e0604060c0c090c08090106 77
    0x8000d07502200d00c0684103a142461a41c1c60b103030b0396407128003444410141444101003040e5464580700b5622000d880c0026043d040c43ca0603081e42804101c0c85040203214410340d111a1905801e01d07401643c907040140840d110226a01d42c0d0022240f10f45401d44244546410b12151103201068807600030740070394401600c24071003204e020350222409400c6510400a82115520801d450811220b00140c01828500d80c0e403800816a4402c058a1002801c220240b00c89860188140d403188583c1340001c41c58200c200e2803a98540c14010826034004000c400044c040c642c100024400600c01c000b000c4d9a901d86c9031032701410a40f01503d07a403840441160014640004210141c45006402071825004083c40c1ea298010000f0350302d44644a00000c0c00001a00590350107804050038145584035111800a6841d0b800c590030b6902140c10006030f00090b51081d01c400c4c0441e004e441c59840c08006c000064201420324956030350040851910b403d175006030441e0b1080351203002d107210f44000c2c02071030b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 356316214 1250 356314964 356314997
    0x181c030815010c05030a0503040303090b011e0509060f0405040516301e030309060f060303020105090114060111030f0f0d0e0a0305180d06051806070801141318060c 72
    0xf50f000d0000c003150710800807200440d01030001787d42d110348285008034801080d0742d07406056000030f80c030442120044550006800b50399180040240c281903404195500e450000100e840c50005202c07800703190303520007140501606204007030f08880381a412007411650764540361400d01c104401c8c1c66110000c600b00c000c021407005062500981c10001d508030720040c0c409403040286070064220301317060f134034840000014103500500c1e41a01c0b88600c000b1b0900e145040180c01e41c0c40040801e909079241000c0d203103105405144d002d400840030320b032007106103d440c3c0b0600c0c503511a4500210305080003140c0001c4070004a8018941800c80311000e000030504680141c0e51400c9000c0d0040100e0400d2040d4044241d200e42c1c4202c45840060100d00c0580d01a2151000c441c1c0c203942c4820346074010071024a00041c20400c0c107800981c5868004059898402410003d2a601c21550310a000110308800a200d207900117400c140384114880600c0b003100e01c2c000000740744140b81c820204844416a9a800c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 356317464 1250 356316214 356316227
    0x12090b030c040e0a09020406080601090c1103030703180501021206130c2c0418140312011527150302040b0313210c2006181c03081501 59
    0x40c22410507240c102403c0922000d1200b034020b0250200036645c90316500580d075903000d024014040240680804d504001517801a120301c0031602c018010602a4010580c00003c2101d50003821850300041c2c540c0100f06001ca43c01146001400b0b540c000310f549500590000d202a0003a1811108481801552940300060307410309440103010581c654080702405001000301c054051101c03015400460202d40050b04640c5c800c030b100251001441200b104020451054131a4607005070f00850410f50b5440c164400b80505000c3c0b00f5100100d010390200301170160110030304103c801441c84026010684240c4030782011482a04040d48e030100000050350b01900c21a4103a403403000704240703540d503801300c6075043c0780502904540c02498444e0080c01d541080341e040000518035962044e07900554203198440d101c400e204041004520884031407a6512401250000c03400010003000420070500040d00d46180b2049001d4044100070b079800406034001c0c9000d2007445c81d81c8890b540411540b0045445 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 356318714 1250 356317464 356317471
    0x8010c0f050307081012080405040501060c0f060f0603060504080703082415130e012d050d05070f260c09241f0201050f101401030e0a12090b03 63
    0x40307107003000030822007442442d00316488a0b891040c003c0c07240da105106034690840d00c006451868000c5020b1225162174004e00c1e00620300c80c034003042da046458681180d0403540000041c29103565010b11700d0b0306101c9030401d200564010100b08107514081c14104416881980e003100015549030009111100403014a01034110410440c000504800140050300310300602d5500d45203000c1c07006446800c0d8841c10701004c2c0122440e803c0c0603500d045142100e03c901814038020302e61070200c5901906401c2450b91085074401c54101a90381003d042c0b050601c4451b400110401c41d50640204124141c00c00c019000d0080b0b0840305051038024801c00c1d110047c4002c4642c0c07064901011601c004070130f00c042e400d061031011400840305420340020303101003648218002c0d54600000e8405800f50203100d1164000d1200004109524140c0d010500701c02d014003400d41d040c1003d030a1500d56903c0b1380d00000303040001008440383c400044c00c00c002002035125400700080d14040000c140c1c40a40d5064900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 356319964 1250 356318714 356318717
    0x62417010f150c05030313051905031e0d06030803060f1203070201050306030f0a0c0e010b1c1805030d060311031c03021b030703110118050a11030c0a08010608010c0f 73
    0x103214102841c075101105001e00b0b003410000e883c4660808100c0910007107000b0112100943c40c0711074549840e608043d002c51100358008900341200d17000c075401000700c880c4054210000c6a1450100d0040d800030b018046520040070300c1d1440100400c000c2a000f54081d01040f40e24060b5612030501b009403c1000c05513803035442d08244500f03001540108051500100014140e92144000c48100761406c0f01c1440f007500d49070382c02c4a04100d0501a00b41c0309001d401c41502c55860010001440c60010b170202d440340419035500d501403525002075841e6034407580c1e400740650b550f07000d908131954050000d134041580d840c4c0d851443c0e821149400142c4202462860300190021035031040150000e4000f8465a0a4191079842200325150144001c0c10458400d8841103c03810070f0201541c2110300460703480142030045c1d440c07040071800c000341036034035280c0c001004481000c41402180c01c01085880b0140c2090f070029000c070300030106402100c10b0fa01d40100812104c000c011048803118a010003d20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 356321214 1250 356319964 356319989
    0x210e010509060a180f060902030a08030402130902011e0207080d120b060715021305151801080c09040e1c020706080709051804060b0603090a03090806060303030c0c0106241701 77
    0x103000500800860001c40c0c0240f100247c0303540160007180c10b1800c3c8036011075a4030000400c0008620745001d04a060b00238006c4200b0000600e0f174000b0b00300d046102c018050034980d49101c1800d4903c00c0203881b0190814406480c6056081c010181c0544001c15400c0000340c10143c000030070341020006e0341c45880d0440792081098264484e414000d41c00189012007281c100c10700071807681c0b502800060015070034184c0559800c03401090b040406800301c0544e041020f98802c1c482c9914a02c4142c4809060854000551107140c010482c50100071162200400014220804203503401107032107030480780a91681c144503079852100b22418000780c0075040c2c1c8100321500c103604500004046c1da90081c450f580004003110342c00001500c2d0b030004c803109850baa01c07010880080582c8980d10000510388a0000c1020341884400030361a03000c01808842401c101003041d0381c40780b509400900040030860003038510105010074204013900c0c074042c40c00204072141881010303501c00c01c1c201c6040756425121030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 356322464 1250 356321214 356321261
    0x51005030c03071b0f030e0904050c040e01091704050306010605040608042312030610080915100b0301080604110f10111f020903071a0901210e010509060a 68
    0x8100795000680941c0030803d4494820742036203141c0e901c006990b80951440481c4000501d0010032007003000e245a40034200300001c1c440002c100161040030381d001242d000c0b54820085020600402d4400c402070700000d4100e000601100803031004006460040d42602c050303a81b600000da50074032851082400240072240020302249218200102036283d40f40405000b0500d06025844c2040c000d0040e01e80708000400c0c03003a0f41c0307005002c01860320301c0d504080c4001c0c07034400142616039070300d43c81380355140174020300144403410a01405400303842c0f001c41c41c0e9120358545104d144e4410b011a403c6a0f404030036140c485440c5000039001004600007032034401e02e05488081107601c1902012a28290311580d100c038216110340d1030314005007010b40c030320060301c3e14440d0042524100b017590200e11a0041310780e100d040030f86000b0450b4800036007070802c2440c18407290b40e003a0b03500002c5104004001c1c41c0a0103d480d01d170041d04624014000d1104030380460303c03a802038104481441c00c22640300c442c2803044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 356323714 1250 356322464 356322481
    0x30d091410051207020d030e010c0801030b0c3007080402210c0604060309060c030605060403060930021506180604020c01140106030f05010b04050402030a0b040218090105100503 78
    0x105484a640742c6451420203440402c1d8500101003661880d0241c1c015504411840c1d034503105155003225200020b0125060059024000c04010b000103405010584c0c00104044081412a04d18888007092002d04a04010450509004100c00e052500d0f490b0004a03041900c1102a14040c0350001c003680b465007960600d0302c009044000d08490140a044007212590752200f001c2c200610141e240030030400500d00c4c200e0200c40c216800c0000381490424203028680740d2a06450950340e1148001903580340c00d04100d0a900c01d5008010014008140c042c02d02917000560005101c400307408892058101030005c101100c0100c03281600803840d0003d101e054000c2c801ca0302e401c448081c00052038101c0d4503401d00e0030b45401c050405010035540b001001096458400c2031520b0602e40001c10103541881280d9406125a01c11184555008004104502c8050f0300000301004010b00846d81e4204100d9448420f90006030507500c03403003070346c400083c00342020180b1041142d1a643d90f1840c650b0346055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 356324964 1250 356323714 356323729
    0xb04390b07050c03010c110f1902130212010b190206040203060601051b030a02160602060705180136050303030405070519031208100801020702030c0915180105030d0914 74
    0x41c291400c0c80752400d100203d440a00c5807402040c41d035030f216034590f4a001d4801d442d004109040e11810f920503030201c010b03000c2d001d02e203400281d4110340d2410002d50700004400a40212440030745111b1401d00001040513540c002025454046208800382c0c2c110024143c1c0c49260481b0040d4040c0c0019000407800d604c508002d04040e084000b00c44083e0100000b4185550010100c08025a000102d105a0210682011001450940700811041c54208402400e60094221019061484500b030305aa0380c0a41c0440304049078011046480b01010000391001070f050400c031292410b801800404c0909021040300e01c00c0b50842c00a0440901c0d10313060116000085240c210040d00b114804030002d60030100d05045804207a58844aa007400e4044d811aa1810381c050b0100e0381c410480e501c0141c4000c2190251410121000724640d03852071011a214000c0040131540b0070701c0045c2c80685d114840c0d00560503210b0980465052418008060329220200d01480c090458a00003004042c0382200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 356326214 1250 356324964 356324977
    0x3140303060a1802160501050708010819031805030a210f08041b0e040302030706050c0c0a060c1107030b10060c080d02090d150902090f010f0b0304020604030b04390b 73
    0x25005180c961121179050b21903010940881e0780345d45803030500c80740a91141d243c5014000c50380c007918640070702040051801c00c81000080c04d02080c1059240706200044103038000b4603018055070386a04091130421400c590603203a0b5004895114034240b459841044501c12080890721a110740b6240d07074541000c0300d1241c81a4890070052010049440b035405842507000d240700c0e40085890300c0c034600c6c0640581b0030080c5031401420040c442c0070020f40300064042101e5402c244000307508041d00e03800311280003204010001a11801c07030000100030800d41050312454030300540c80b04040e21800112240078400c240a4500c520038400603007250165801041d1041c4001d050045200d41ca1351aa24402440071800302d1403a070711003e04080d400c28480c425808501c050454160791304040189009501900031106110008000182151944400c40b0055a0050604801841d10749061200c0500f000b080034031816064410180c0c4a100000900001d560200e03007186890820749100b07103540118 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 356327464 1250 356326214 356326259
    0x201020313020f040b0312031506070f030f090f17010b0301110a1b02090a050106020d0f080a0c020a02060304060605010210180204020d0b0405090c15030603070e070512010b0403140303060a 83
    0xe404007171141c0d030108181602c440c02000e0403900d915195216810305091000c1d2603005d180c0400c0743c180014900c0d0342e4218421341c50f00b000c4075000c0c92040b049404803030641007a409080c109002040024410000f0030038140c0c1c2000034066650b4000515081c1c5000481e100701c05041403008400303841c011030a2048044006c1b4221040728000d070001040441c065a400342119540c100510010368107010b0102e40a1080c00d0903a0300c450401e000505d003074401840041815550441204018820300070039140640046c00c1d107442e0304003800e210000744140d100d140d026116640c2910805202d600803520710031480b0620400d40440390302400083d601194666050542d42d823010846540c0310310406006112045c0140355810101d02405090030140c5810320041034140104943d60b90b00250719400d5a5503c1070440a40e155024155001e0003061000800540c0000010450b49101c1000d8070072030340076145882488461a440c2038032072100303455484d0015000035051040c0071100002d404001c085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 356328714 1250 356327464 356327471
    0x50307020f0303150a06050a090311030a05121801140301091d3c060c0703050909010e09061b090918070801020702120c130903030209121006060201020313020f04 71
    0x1d0101c1d01e045500803100e1400b1298000c00c0c9600c60304110301400c0180100d420003500d408201000640000c0300d5210050850302d400800d00a19101440001c0803254810101c502d00f40e0030b20985400d50b00044c3e0300d4044070025040d400117940c030400300641080c2c00c40340381038a142d00f042c041c0e00241002009454010a03120070901e540e1908001c0c61030851020104907082c49a0078440e206102600c440342d200c1980300b404c0c0401508004990b540e000040c10382101c0c2d4950b07041c030381034640e4025000d1030b0354458400000040d91b00303003d00c202c80c410b850110a4a1042d03403a45c40450f60040c40420000c0900e03002e202442c0c050825003040c90304110303402e1071103c16411003c882494000c0b02e8002c9201650041402e400318282541b001000444a5014003801d5003002c0c049040005500d00390b07229140c03540344007400e060107541110f101c004003074a200400a0010181c5945844590003488218603103a0001080c503c18400c1d00d008860361740305c001120b4082c2d02000010051003580340d134460f40c3c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 356329964 1250 356328714 356328733
    0x3021e0d080a05030421320c0610051c060c30050903091c0f0204050c0301081b01020d0f032c160f060305090114010806060406140a0605030702 63
    0x20504050116101a07030748041d600d14080c5882001c0118844072010440b05c150300c106800d581080c0c0c58070440c0900070100007040110040e44100e50407c80030003030328050008020100d200b020500510840103100c05100440e9079009018080a8060740100c0e250a40114000000c13000c2c1c1010f07112002500c0c00040014031585901c80314040a2019203400803c441903c3e0350941c01e0049542c0040324001460400707207190081034290f41680d2001150014108040c810081c40211604006030094001c000310301d0b05507040c903025402070050905620500e001c0c0d01c1c0100502030b1000c1b8a004c10303406041c0415406d0421754183c94001800c82c20305465600300f04041142a156109a0580144a0000c040c090010604040b0004000c0303035540d091000501c081c0c0140d44103001168110302c2c00007803950709c44580c1401070120000030001454280000a44424005003850140300110307010040907546800c011041e1000c529865048600c1c6042004894000da010755405151401a01d05010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 356331214 1250 356329964 356329973
    0xa03020702030607080702010e06040c03030807020703060c0215010e1006201c090f0608150f1e0901050f0a0509070219030504030b07030c02100e1603030503091603021e0d 75
    0x70125810130008940504002840307a090080803191290900a40210f05280d120900480418040076080c484944d001c83c24261080080c28011034201000b00150600d00c03400a4880c40b40d48145101c003050740c4000303d441c03c030406550703000b14042e400e0300b41c11625003942910b0034200d902000c2c0c5481c100c1004904002030900c8403465020b0041402e461044e034807407020f04648400d4200d42c0b41d030800705005100150b044200075800c202c0000c03500b154046a4400034118124050700190441200c000841140210503800b99002108481c44141680c07101c0c1440041c03070980854580c400340c0d803081040301c0c1c2466403000790881c0c1d140c410749520307585a1105a440c03d07030350442140001d00c0068104113108620142035002806803600f408080c581010003035503002030b40a840e19090b03403205100c43d8400c08110800c41d03020b692495000c000c0c0d603030401400d04d400031035840c14075015259505040c01c0c00300f00e0b40303c1541d034010003116500c00c80c87c5840101d030341c00d06d419940100b5200448800314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 356332464 1250 356331214 356331223
    0x7050d050109021005191416030305070f0f02030403030503042108090607021b19090614011b080a110c06040b0a0e04060b091009090509150c0f09060a0302070203 71
    0x28040c20011909040910611200b07044034807600b41002000d00a181c0715510010b11a800d0008070f203131102d8021110818030a02c0c1c800c180101d00c040c04001c008004054050b08071034400d00700c5131522032000c00e0880c001d4642d03204241203440103802c10441440044d00400207150001c0c01a07901c00400c0c04040808541007082e40701810224002d1030070081e4241007000350302e0b400340140c8040c1c030805108000c00120113050368000744c4a0341582d905d5459041d1507070500b10040068031001d0000c0da54400101d1149000948100e0015016205c500ca0420281030082911640454100d00d4898001b80845010009100c262403a0140c94600301403a501c2e8070203003011700912109590b0755a000389000d04a204980d504500071030504400304400402401034450b84101990711010300380241c034045a89000d59005042d06911f05000d10021a0300007034414001d1a81e900d0141d842d03100d030040c03101103028440500e1140039040240c601d090800e00054501e0f80000e040246c20200591b0010303042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 356333714 1250 356332464 356332489
    0x6120d21020706060f0f03020f060a050903070e0108070509040b0106051303060c030203010f15021b030a020306040c0501080c1306031802040c030b03010b0406230d1e05161202010806030705 83
    0x4542c407180180200170880822500a01e140001c030f42005155901181e0b074461a142490301c21140456a000d60354000e1080340c1c1c6a88004090f1042c49841c0c81c1a1001042c0030300400c01e6601c20b005001c40c2a0400488841c061074201754981d100ba0720f4000101c48540c0311040301c18900380c100d0340010020710300b40208104030109460150310396040c542501400d20b1a07610402d81e03001d60106803110281c02040448a00400c000381d00580e110b54408207203031a2241710000d400d80f20350010032041c055000c040ca030545509a0f10115682c0b80d20000c00c4490107a45a40603c5d0782901408008840c041d42c4605880c503503d6240381c0104445070009001c0340c0f11207140b20042174a4660460071840c0038450302e114400100c03000c0000c1e81c180480359980445c420500c991031110540c1405a40c0ea88400b642c18141d444084281801c090b0540001c81c4482c13001d04442d244150700081484510701c506030810345084204c00d200c2d46090f80c00440d84c12101a007c0c580500a03405c010810361600304050a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 356334964 1250 356333714 356333723
    0x7020f0127061d0f010c020f130516050c070e06011e0507030e011d010302210103050a0b0106090501120c0e0a092012011e1509090506120d210207 64
    0x1841e240c80030b0a034844452907844060790f001e11034038103580c3e0313440c01414004081c0b9020844c4409407021031071005d140460740b50b00c111010800b500b543c88a4120a202d91440e04030944140d0342c400c41641e40f4000c031492070a41ea0030202c81400840d04a02c007082e44810140742401000e22542303ca0754001a1010750240080c00006181c800d0540125074146c1461003864904000c1c840c107031000b0b011004000c00d081c10560002801c01580d185413000c0344030310309201500703143c81d60349281c02c1390341d00398403001240c0044001000046e51402032103040101d51040e106c0408a00e0305074507000007844006156428000300c2c5c00c02c5246034848594800c051300342d104d00007405011000402c100c002c030810741035031000070820440941e00802119641100d1482c805061028904c400388000b10b5a01d4004003100301003802d0110210b64408000400c4400b0700604005a8480f1403d0126400f6822180303041a800000c80f544032a1203883c100d41011125184102101400a031600981c2d201d00e00544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 356336214 1250 356334964 356335037
    0x608060907020f06010b0a050c030a0221031302090c07050115080106080c100f0c0803040b10050402030405060f060409020a09050108010b030a0302150a02044707020f01 74
    0x1030400044607504807160380010b0000e02c2c540725800c2d68424050141100500001c107144040d43e0281d400e039449020a8030649440d14000319000759240070078214100607a541034031040040310040201e0f4021840303070301c0744240c100c119000d0152400c80070b08040d0485070b0810004000c54000e220300c000b4030900740300c1d03040e80070f00d000f61040c02d6803056002001a50001000b04489a503a44c24518400415041044214007210003d4035001d14040020b420b0140c0001004100861464140d120704c0020b20170000194036002440308902080303030010b0251744020003055070318080b1021150f214400610100b001000f50780811a06510b5a00c20a44136850310014860300100307004003000d0780c20507001803011041c0d13a00c00954810300d0310f80d9002000d0010000c291690440d80454028144e01c207442c01c0d50042c01c0c00d000c541044080301c08500c110702c041424070400e4941819090041045102030b05005041d0208590002c0b140706003410b01080c6508076801894106000e04d081d1101510f44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 356337464 1250 356336214 356336221
    0x120503073c0506160903020d0204060b0a020604170301080c090a0e01061d011a0a03020d15140909010203010f0504020306030a0605040c080f0c01050f03091e1b0d120f0c060203010608 80
    0x1a00e05080a000d80c2c4004d03040d8484203195591004500c0c04590b0111180a100615800410000e08503904030304180c03100020900d0005800003102805540b281c2407241c0000e904452140441c0001e0140705019004440340a02519008000640055110400040000c601d08117242101c207140d00101454404444050b0031203c0050035500402c0c410070000f00f2820486403500a0340308080000041c50750206e541e403020402d6a115256001408500681d41d503142c03c14000c0705294101401d219075000e400003041000d06000384c80c125810020149902c03402d040400010b50402017038560548039000d0440041240d03800b44902443c05407859128240c144520b00e400c00c044c103000e0b480664030080c45a002030740c0c0300d0216401000010745040d22600da01200a0610100360040d6209284d40125200f50500c0400c880500d40365582d603884109010340c09100b402031320150080c00c46044c012600244e24091b1800c20018ae072103144c03403442c8440703075074860303007280c0007030700418000344501c4100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 356338714 1250 356337464 356337473
    0x9042a0e0112060506070209100519051018290307091a0702010203090d030c050d02010c12090f060b060d050c0a03050106170a0b0a0503100e07120503073c 68
    0x240314000c03442e100c062068a0810303011035901e100364800240508082c2e40068481040d004c0501e0140c04002c0c880040001c0502030504c011801e402160301c100400c02080081d1401003507810309421061031150840d070302d8603a00140c4000c040f50342c80c90441d0400905800451144020352160800c0e03102d07495007504040048624040400d600d442d82c200c10003071200541e0b00041a500c80050441d14101c1d0304219280c111010400180000d105100303480100d6601d540641103441058015511645100c03070340c1e81b150b0141c800c00703400074141c41c6404520501007417039900300481142000e420280313081d0100c40c40340c00300e49003120001c50758800800c16201c9a82e150007024018081481d110007104245500600d0968010303203502d003207541c0c0701d01d9440b01d03460300c8030807c00a22008060340e401901455041001e0802002c00110b03a009031880800c5002c06082d0705c40040303411100640c2414420369490891414603d50181c500c00c481662132422000b00c00102442c41d59081030f40f00300c2e584d80c0b81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 356339964 1250 356338714 356338727
    0x1821060b0a0e0103021c06020313050c0109050d080304050c090702010603060c2d03110a030b1c0503041403010612032708120306040e0a0c150c0809042a0e01 69
    0x2100e200e0760850070108404888000c100381903036011030340c502100c2d03154114581100408031006001e94004001c0107c440c0c485541d80301e00b10b005c3c80603a600e12020200440f203120b0b0324003404e5402081c0c150501c011a0050703000d198428400c0701101d84e584007641c002500d0b03c4d422a54100145c1d1181824400c115580c02850000c03107180c1001d40340000100c140c8481090f41d04204001c001030b05091090042c4250007440180c00310b01516561a41c1d4900014080e0000c07584030350042000150010003402107e08c203443c0c02d074120000d94101400c007540c00032649010180c1a51640d250400428507032102d00c268440b031882501c80140b0341d0100740d5881d16419882980c00e840c100540000c200225000c50405140305c00d00e0042c540c1d9650301000a80103000701c0c2d00c000806c0c8070b10400c140802400365403501c1607031000d070602114403500e500201d61000640341c0040c5106403d00c2428943e00b0203030020301d54070140842994040ca00711100e8800c9078002074a0030002039403001d850030696000300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 356341214 1250 356339964 356339981
    0x706033317010b0607020105070501060b040b1209030405060f0a09081222150311070609050604020108090c062a0d051b120a0e0613060507060c030c0e01182106 70
    0x20001d00c02e540340d14000804ca80038181002e4107016001901c041080420350001018200843d0b0700ca844e80c1d1a00020075454002e81601011814844041a64101c0010035201200c034010b044500c1d1010054410a4942044502c4020700088500100307a0400c140701c0d400400d40d0307040045403140b440307594166407203002901c21001428069000c1c0a049443e8049148406d05400d0100d00c5540030440c0d02214030442002406441c0f40142c020104000440c030f40f07014030700076600d0704100e44a40314102c0e10303450a80710881d4800340400502c0003050121403c5038015580d8900e00400d0000010200d042c10744080000d400603600183c0d40060001083d0007800c84181c5400404440303114404181c01840b5030240001403002100709040325654001c1268195a1215915400559154400f80c29030700054401c6030050304003e131082040c0c0c0b023440b03000344424050b0350700242c9115210055900803001d10600d07165000b443c0004c01c01140c03e10014090f50011040301d4226003203801c0c2081210200e2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 356342464 1250 356341214 356341259
    0x7060f050403121e05010b0405030708070e0609070908010213050103180507030809060f0d050901050f091e0f0d020601033509040f05010b0915030907060333 69
    0x3106220110b9480350340b0b80c00182c510040000c1c1950f00749030000310301079000f150303070080760911002040440307806029104840d0240c0231070340410785822040d03440d4082c40c0203030094100004001200ea10305580c1c0703160081214100995010748501c80d05007613030b120980c01c1c100c40405000402965906114042c035040104805400b8100a0780d00e00e40c41d000f940c840600001c0300850680b8165450f201190a1001c400740344070340e200703289881003002d840102da00c42c0c4154a030100141c8005045101c092280c48010064002c4014064100c11b6507254a00711145500c11a0740c039040c0d002c01041408025000341c1c004160a40c95840c03c1c4c1c510094810700b402c0e00c181030300c0b0400e042114081d55444e40100301c084541d2180002c6011800511640070f2040d031550170072000140040d442001400c02c41000d441042000703a424182d907541f444181c03070301c056603840940d0401c6254407039400254030100f040f0881c0c5012801720311508101d404c3e1070450055001c1208204014035550300400c3c880c8401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 356343714 1250 356342464 356342471
    0x91003180609021c0b09010e01060f0b16140c031009020307150509040501031a0a15150c020901060203030708070801080a020607060e0d0806010e1210180f03030207060f 74
    0x140c4400c26000100400300034005074882d1401411565000c0a00c2c98583c45803494030009210390401d01030a01c41500d17520155413902d087c00b8040139042c040c18040e00d011030300712800380c1d03d40060b114042d03003c0302003041c1b10442d195042c400a50503802036144e016050005001680c03202c07080509200f14400101000392034000c01100580303011942c3d4048a002c11002107059a041d84242c0f003601c44c05034900c1c7e2082c81c040000c4200089250603020f00003900f43c0f0340c41c6580e500e02c041c501700c5001d44403180c0b8040d9210001c200354558042044160314a526001c4021a460b41c0842d40c221000c1e003007100980c1002c0200308500d544044a264041c405140004641d40f4014181d9100d100c0041e020b4051b00c8000340c8003081c4002a000020350728a614201e60a00e0950000100382c1e400c15a859030001310a030001400c42d03d00340000701c042c403a004010704141c1c102d281c00ca03401080c148049502640c0304a08440202e45645c4180801364043c0d02c0c0540e41c1c6145181403001c03250b04200a810f078500e03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 356344964 1250 356343714 356343731
    0x7034d01150e06061207080f01050d0309140301090609060501030b0705040b040306021b06090a020f0105070b0f1f0902030403091a0a03050406022b050903120c180a0b091003 76
    0x1e07041140d40c2190200d60349140307251140c03400f190b007501c1003000c403060032a07110090005280d409610035100b501d04602c0034401d80d8032081041544000c250029000a40c80036080c07200340840079020004680007000029401000d070b86a0003030f144034010590301c40d40e07030384010010312092030714280d8414458a842407409041145c081e043d405240005410b4035408145c806050700000c1e0130300d00c3c100601040f01c01610700400c419a40b510300c400124018070100d1003258003540a181a2180f00b40e0142d03100142d80e44c0c1c03200e4030300c400d000103202c01c2240001449200e1781c02c444544030030103080d44c0c007409aa42d24183c1806003100050754081c40b00724048410007404021000c0c260ba01241c40c528001c200c03601d03035061034400390180c48025074a0320b410600020540c2d04420f01c04d0441940c2e2001403100c1d5882c0c07041ca076100e001c0c1007041841020351400203079607007800703400a217003843c400c3d00e0400c0ca020300e0101041c400940f0b074000f16164400000c010740701c0c1ca041004500112a07078601881443c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 356346214 1250 356344964 356344991
    0x100f080f120307170a0207061d1e0c0913020406030305040e09030f030a090c09110406081003020a180f02040b0d0b03010509030d0906020d020a0e0a0609080307034d01 73
    0x15400303000071402c4c0110101180d0210307541c0e011680b0154000ca03042c0946604e101101c0c078881c1d440980849544123402e03010b40100c190402800c0030340c00c0328010b4003048200500b88104950000c01034165a1420340320040140e40d03e21806c4082d41c06581c42d0f54a41d418203070005d200020141040403164424460f01d0b880484d80c2080301d601c00300610001c00c0ca01c580780780003441160f20341c0181d003070b0394145003030030040c0032112001e401110b14a51b642c41580d250700002502d41c402ea4003000c4d400c81d4000005108a4040205d18224200c01c1480050041c028400f8001281c1040d0494200004001807084c9001c00c80c2c060300c1c120140c204c000308100d090104620b5902d01ca403841041e0b006031100c8050080c00700035030684010490007502559070303103403d91004000303030311501c04d091003405a114041545881008280107448249004511700540f80d1010b81b103d412006058645025079981008140304125420132000d0024560307080b10820711034080c1c0440310303c403080c1c185a80b502c03003100c1005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 356347464 1250 356346214 356346227
    0x90f0b071419020a060f1b03022a100603060903111b090907080313030311060c030a020f27240403020f010207030506100801050f010b12100f080f120307 67
    0x240d404900311007901642c0c080981c1009071000014048a01c0c003030030032800e02c0058000404081c50403655000b804500c150035400c0303008480c8900141c1d0341d0b4404101544040c00106c00e102c611240449000c1b2003004081d0302a1903164004a500c96110303101c000c02c150b0002c820f84503120031035020704044002c64810480000c100380840380300703071440c50220b00ca540040c0141e00141100030140c03a41e44043e43c000c104d420604e48021400140c03545920b105103034000c11400d0003694080d00461864680031401c0e4043d40190000007410b5600704441621400700c4000100b01202081403074000c030400408102240b00f44424200ea48143e02e4004540c04d4124002c907001d40c4d2b41140c0000240d152a80101e2501e24ac5402c020024401d840034850b80392810800c00c0e08480040000b400785c1e030f595002c051074000083c803070101d4400003400200d40c220130030283c640d4440020705c12548566a41d0003c02c0110080c0e600180154008191990f9817290601800303801e03900c0044180e1540c00c0000005210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 356348714 1250 356347464 356347477
    0xa0e100b31320408040803040306020c06010602010c0212090613060c03140a0c0308090a1205040906050a05010c020d050c15071a0f0105010807110304090c0215010e1b070204090f0b0714 81
    0x6030b8107014005420002d94405844c050084902229285d54032850484025032101c0400c03915807240400008040b031050007001245119035011703180207030104000b0f00c01d40e00b010307030f0702c2741d00c40703c04d00400c400c02d590040800c009023216680d07a6460011800c02400403080c11448120550042042d8880103400104010903d9814584881c1c103640c3c407040d15040400ba04001400783c0c40b030754a0041e2041c4c0c0074006e0406d440140070208021a0341d4000c1088a82c194881c0c40e02141c020368000015141c000c44684107a07008209403400107403100c002414640000c2404809408045203407014840d890481481c9a4201c0948107540e042000842034200814030031141082904030002e1741c01031117000100890000c800459440d59146c0251001510540841c11f006100d000e0400300080424050541202c0b000c2d0805101925038000b12200000301211484054804000000058840b440b801500360b00a0444094030302e070718582490151406420902005203007400c060000110b00d0031903071b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 356349964 1250 356348714 356348801
    0x1205041e110d030807080f0712022104030906030e0601080303010504020f041703030a0c020d0c11181f06081504090c05120d080a0e100b31 61
    0x15005051074103a1016210a501c160060582c0380040c08150700520700d075000301c64548501c040c0d0380e661500e24108070300442d40040003c00d003112082483d00c503079000b0a441b80310314012159648004004848001043e80c088001819804080080030f600d441040211403400c00644199490500c0710b503a40d0106014161046e580010098107100420041710000c0c40074040d101c07034502454400075140d1304110f40f8541454140007101d02d240c0c0c4045440c04a01070b85445100c85800d186d165265100400b412454028584020354001d55a1a040240c82910030b241610b28065402d1f104003541e400940c44074040c40300740b00603c92603403692841d12100d05002d56001807170341d140f030400815400855002541100441c0038000300650086190304201d04e0700d4035512115250082c1d8041100d40c041e03560b80c101e0f007001704507180c1da0685801c800e090510051400280310054681d10134043c40000089a0141c4400c46e02d0707110348424021190800005640c0b1030803640ca4030f29070b40c1c002c503070003040300b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 356351214 1250 356349964 356350013
    0x180717060409020105190516060b1005040e0f04030908070f14060909010611010615020a02040606090b0a03020c0f0105090a29040f0609051906060506070c0e1b0a090501120504 77
    0x1b02c4512078001d6501380d0740a510342c0580384840c0d042260003841c0d050403103801011000405054240144215070484d203040e2441c8200f40c0d0f450700d5401960f000136008030100194004000b640f28420808180986842c00c1e0040980e854861404058000d038036a00740070300030501c401c0d4400d80e120201c0504540e00e40c104010b080400150090040c0364503040245284103a0a5500e80142d00145640481c0e100707039000c0200310384403201600d03401d10344e2260003103425042001c1c0c0b40840c4a900a41a280d900310308440c0303650a07450b6040c0c290341c1c1c00c81c0c41c0342c6260b000d900e0030805d000c8111020041c0311a190013030310a07195160300c0366a940300300401c00b800b03c8000c00d444c1005c018441c1e1082002e42e0300901a948002000c1e0141107514411300010750780503003007680114252411208540c081a4481051000d032840c0c1459a0f40c60381c00140303400400c80c1b154120203281030251000700388400c1c40395215107e4504100c009440381410000d05150f15103070000300000507082d00d40c0c55045288039818003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 356352464 1250 356351214 356351257
    0x515030712020c0604110f03121b01090b01080c090a0605030d110f0d09080d020c0d0f2105040f060f02100203100f0306060608090f1506180717060409020105 69
    0x44007030f22581c0d02451031032240c00b00300300600000c0341d00055020002c54a1142c4060518101580d528072841c0c1c403402004200910107082d0541001606409001400460402d05d1611220b45410b004d84c000c1209403c521010b50300c9203014046142c1c010301440042014600f0140071996a1800303292a00502429100c1191400002c0040d0310004000d801121000e80041d10010300311145481140c0302e500c200c0754107206490004c281d0300c0d03245001810b240c429030039503100c0d01319100071007a094444590400080321200180d850807000340006480c0c0650303c0345004190702001c19290b000c0010403000703022101186501043c009900400702030b0142e00ea8884030310a1603800d5483d40441c2000c60502400001c01000d40c208401319980c98a48145a42c0c51000d0940c541550407014113003500300ba212101242c114080564000002914402d2092411040c5405003d800d41e842d01c04282000344e9440842d01c1c1001e0f03550701400030781d020700c62010f2560000e0681e000c0d000c4050911100000c80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 356353714 1250 356352464 356352497
    0xb091b030705040e090c0301182406050616020306010e071707030608030c0c0a0806070801290f09030714030d082d04030f050f0712030f050901140105150307 69
    0x1034030060440d41481001d2401d180d6541640c0e0091050f840d8000d5003801842c00d160400e48409182d27064209030101c600351512076403c1d050040e0a0406110340395500f101050f1621030001800c0d8821585810b82505041c500406282c144141e10581c11044040104440e80e640030002240e2a1241c5013000ca090b1038aa10507405802c140c0c000300300910002c1a05100c15500040c01e03020710606680c1c1207a8240c40d100d881d030300c03144212200c40c00310b9080f10041002c010300f48410420709002500026007000e0b040d00b0120150b000a50320711032004040348800031498280000c100621410707403c10750008254011036141c1c580043c0000c14408800002003203520816064081c0d000f10040d00c1909031103d00100503494029503080c1d00140c0154598812540a10215600c00b0500d0454a081681343d40e80c0101740352914a80030200740d1215030b2032568060398001c89005400c054008905101103020b4985020030580c8441d11131002c180807149050b80c910b04076900107031a4500011030080e40c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 356354964 1250 356353714 356353717
    0x12020d0609050f032106011e0302040f030602040302131b0302070c170114070e0f0402160f0510180c051c050307121b0308150f04110d0b091b030705 65
    0x4000c1d000d03000b005010030034240044018890400f041e0012040c400ea20440780094020803500c0358045400207007540710601d859042315000c60854a40903240c50b03104d460000000c0001d42c4100d4102d6000b140a00862420810601c11100050001c20207002c0201d01c681000103512800700030305500090403c1031010800108015140c2c0a18220008150310f1485000740030824600e0040c00c0b2030008141031b80d228480e1038102590042c9038a402c55404802c1000039401901503485c200ea040500d48000781601d021610803d0084020b001600c02c1000b01e13006664030540c88003c2c100d43c0b1410a03001507114030803d81902d80568480d80ca41070605801956403090110140091001141c51307000c004800d0f911801c005c0c190b58500d003494141c4000e010a299444000401103106c1d0b600107200030901002c4906000030003084d2289500026012a00701d82c1c0754403026a202100241071425190709001c0c1016200c400c1d01d8004041c40e02c881d0703404120400c07101150180c0d80001c003040ca020320450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 356356214 1250 356354964 356354981
    0xb06070606120b07080705030402040c05160c0501140702150307020304031e030905010e010203030f0901180c030204050612070b030a110d1406040e0d050309030c060907031b12020d06 80
    0x8400c10000340c40d0502e050000078504402c6640c010128002983c29109140c154001c6003192559405e40e12198200b1015140e200b8224040003070a210b491404000040c0e001c1600b0300a060300000c0c80c1c1031130001041002c428a8241c20240c1c20001030005032125429801c14401003802d090f102e4a91145c03c171f0562055500140801181c1241d448011805e09081242c01d132081d01c60818031544c6100541da1014075400050158209100140c0089255080749a2003400c1078000208441100c0f5160344070107040c9802c2d1581c2c1025030042c81113007480d02c43c864101604450403114200381d501001d540b18100c2c01181c2c03442201102064840c40260041c40540074034070005501d422948046200030240400c0c0c0b507080003d5000801c1d0303e4103081c1f141500142c6080040d25500128200546440d80b0140070000544400c06c0140c1c800c910034007416001e0035403000030301200c42c91130074174605408084146210140c481d03401080481400c41150b1084c42e41580d540640d00c11508042c0b00810160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 356357464 1250 356356214 356356223
    0x9031e0d11120307121a060d18080d0e10020c03070f030201060306050a090b06010e0a1509050907020d0207080c06030105040507030b0910081204080c01050702130222080c0f040b0607 80
    0x210030b200e0304e9a08070504400c06000000100418201c1503401182503d0500300c1c0340c3c00020812000d40d0030402904008004291441e54002600840c0d590140e50342c08022170f009a641c0d50100c0da005502d0500890540b080b1714401582005141c4110540300d104917003000b0211081c030460310003018000c0d040300d401150440300421851821500748405840c2c0003604480e8600104001407956002e100700c68403103600a0300d07004100c1d050080c01501c420401c1404800d02c070f02a40c00183c0d50355858000c1c2d200e450709601070950380c5505200030345000e2440d000030320140c2140303994a115448250a4134110b410486012a060b00d80050540c000c0180507a595000031005040001c400e20f0104901c0440b1011011940c0c82e4500229045c458000c138010795000d6000110040307640e620400141500c207000800c14806145161554000c0b40c0c040800b01035005210311111181c83c01d441c620400809034000500028086800080d400d0f03000c4054940c451965001c0c116031a4031954244d8601a502 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 356358714 1250 356357464 356357467
    0x309100608010c0e010503070818010b04020f0903060c2b020c010c020a0516030f0b064e0c090c04091a090a15060e012309031e0d1112 59
    0x100c500c028080e03c481d107007031400318556410b40307800303544120106c1c2d01c0340c50701c0e40d40c5100d503494618a50080480344c40c0031080540d21210008226500e610003040d05420440d03400ba56820520240350804100410b0200380000504c0241c2c1030001d60703029a03501e03209000d4608804d500182400c4007d006083d210041903181c09202d850440c3c0005001c0801e0703001d00211110700800c0352841a00c10040e0000409091100c42048002560400c005801580041540074044060891075031120009403007440c079545814142c0d011001216100400c45192942c9582410311145d00681e5a41c881440b0034010b0b02c403000010404150441030710041c20442c482804212148035070406500700014030548158842c0c80800c1c0c0c028240d03c15062600c041040f4125103a143c0078065030214810352425051003501040b48103c00030b03e4100e80c0140c0b402e1000a40c440b0702000034545032128090640885a080b8000007510002c00500d8180c000024541a208070b00309103201c2d82802e403140c400c0400b40d0310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356359964 1250 356358714 356358719
    0xd030507021f09060506060f07110f0603160f0c0f030e03070306050c04060e041a0d030c021903060e010e120a140301060f0210140a0504050a02130e19150203091006 72
    0x501d8021150310341c06071300244696128070041004074030a0812050742c100f4200001d07400a0003046190b420b4200080031284411091000308240354411240c00c1c00e2058482e54110f000c0b6008805552202c50603d04524611029a660034280c416544050203100b0380369020001e075a02041040d000e5a4441024001804c06c450918000d410078081c00011452845010f401c0f0306003481194411044074030801c2d025100340d01403080c0407019603019001c000048505038050b80f2200e6031700c40c00c2d450017211001c0c40d901e181007140072182003801030701da0750341408801580b841c0c00203540030300c0c5180c5540c11a5501c001210075600a0090740c8143d842c2000030000003501a004100208100a10340a9a0741c204c1800e090b201140d2000349020024400c1c8000310300300203890352100c0d501622460460382c240001c0d0f00041d10000c11500040041c903200c10904500c440c040c000c10300048504030310080a20302a5485022440034412055501e9038044001010500c2c10440302c045814488401c00840742c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356361214 1250 356359964 356360023
    0x20f01230604021b06061212070605060604081506130b090a0c030b09010e090d02060c0a0c0309030213051f060206010e130b01080a0c170c0103240e0a06050301060303020d03050702 79
    0x31a5101c3c03142031540d0705203003801700200e03104c515551a0008c2d00d2510b82d0b0b81d0354060007044040c080071f41140c0c040c080490500c104020840c1e1241044010a4452909404010300211442d07440807429040841c0604541c036641d00c0e003500100104004110000028011802400a0200113034440c0110000140289102c031005004880c00403d40310507900c2d4100aa0342c0701310584254148480c10840f01c5c500da0f02ca00c118550f828401d1500d0035440387d032600029600b007140001641003a64803030611054400c3d031041000303021241070340f0a148518003c4084d4440710305100e607003445d80500c000038400e5058801064512a4411550642540c540444036540c81140104680e94080000c0c0490781420741003d095020000e08000c101d05d4000400440c090082e015154000070010b00032820100721306620310300644000d6070b0340011481c24800100a6484503031001e4082c0e4940300e014070100b80e001c03420220f0807030346080c0030810b80c60300d2004174a0902c15140300c2c00e15140311008688404d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356362464 1250 356361214 356361223
    0xd08090418030906030b150408100b1009051c020402130e0901051b0a121b030b09010b0406080c09031002030a0516020705120118080a020f01230604021b 67
    0x400151010002254000300c40d0034804007824000d0081442640b0070800d0b144a81c021221051029110740f940d0080340d0080c0c4510780007031b0490318141d009034688181c806640e2107000c91170007080f40c0c600030f1440b030840040d011403a28040d6074081e10300c42400b07045d081d14a1107903400d0694050304c01c555440311f03010403961107600c80c05004c09003044800410003191050041902840b200d10681c07039003e0a040880e00d055000380a40b80510031001c1d50040710031041d20490031034880401c0303d5100100b01c0d404c010101c0c2c4403845054401d1a843c0011700849118030151001c1c0c81d61400d0280f1a41c98502a100c52409400c100d10703850310034140e0451400a091300918003441c520341040c49503403680300d00040d0303010b00d09250030010381c88040104110328100d05500070300071407440000b8151000501050710f0884682d070548030428000707401c02042d6810040300f00078031440c01c001c01001d01618260300460608031050070300b01d046c500c04501c00d07070faa55040750300030f0000100e0b40300362808070101e00e44c54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356363714 1250 356362464 356362477
    0x9021c020901121208190e01061d012d1502100605040203190c1205130201020f1b100516061b090b0d021b03030a060f06031107020409030e0d08 63
    0x1e05565400003e010200e88910712245502000c4445407004114085910348801440c280e882d00c84810803d01050203440303044500541c290000ca000d03030511a9030702d2089443c0c42d40845551050340108000354070f882606c0d10049180480e40380915030100950881800380c0c21510305d19494880d5400342540003d411014090f1260b400d004641e43c1c0d40801040340070071101e500100d9442c3c06402c0c0501e0b600d038000414008030382058400c5c03004040025088440132106140500c012700700540c107540e0100b0015046004500033000740d814110b15005900744a24503850148580700d1990f406540208181c51407908910781c202c50002c89403d000000e4443c2800c120341c950360390300c0c0a000c0300f032040b640c680940308120483c0f45056440d40e1040000d51140c0032110300c158000c88141003c3c00240000c42c01484209400f00d0041d0601d540c0d07000c0c2101e42d6004000349407500301403050b003180d84416903a03c1f80d0111000a103902c2e060a05580c0e410001c104290f2104000e4810b1040000d070b24003a061 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356364964 1250 356363714 356363719
    0x10608072a11150901021b09061306170109021c211707020303100e01080c060c15070203120a050106210e0f03070314070b010312051204110f01020c09011809021c02 72
    0x3100152a68944440390b042000750480c188c1c100040b85030501c0c0740d059009144011001a02665460541c440004858601080d0ba51101006010b524044140742080c10294024050306c610681c0d5000b0540000c0c40d81150b0116201e484003940c1d40a282d030040880c4035050745090310b02d4420f000944030351044460003489054182c000c25025203e0f041a816100840d00030240d2500e1001042030b26002190070141c0c1c2e11401040b0808103c0705c84180d80500b640740c0007142c803a03600f4908428072030001001d02c410a0300d030034010024650320106c07528100f2400380d284824201d84000c0c04005d13003a00281f008180c441c8402c00403d50310004002c00049000380d44131000450818108200c610440a0240c14a405240184003082c16800d620010055508005180591075a401002c001c821142a54171000c0041318842a041540c40420317464005d1000e41400e81c0b80b1340c0046e203d0001030003045868907650b0103c90b81d100e03496000014581e0010700c0c80c185409140d180141122351290200e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356366214 1250 356364964 356364973
    0x91a010608070c0308060f0616081308010c17040618030915020303131713090501140907080c090a1a03010305011b021009110d0506010608072a1115090102 68
    0x528461007400000d030981c0e41070b5116000c61b21240d081082400100300e0f6254000c0080290342860707480c0d810100c80c9a442103040d0b0340c943c0005941d244640c0c08079072240e0603d90404d02410306066000d02030180c002c0742c00720034004030380351070500d140202844a201003400b407201d140312052540144051080300c3c0318903051413404145a008a8480c0000d580ca4187d40c080b5903200c0c07000518031500320f0f040c4c5141195107070405142c90701c0801203184940c4a6040720740c0c1c1c0c000610202c5407030301070300000d22015a0080514203000340001c1058000900c10385562034042540c2c103469450002e49801854980103000c010260015005000c1d8005c0c0310403a0076600e444046212900c820048514400c4560094002d00030b0303040c4418041c06030301e103040f203540c2c4801300c1070015651040310003442280964001d01ca00d60400d000035044d0075002e4101320500c90061084070131180b401c024514000c45a090301e0380c102189142c81c40b8030f060112800c0340e11020044e40303000d6641000020b070040907000d0b03003140c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356367464 1250 356366214 356366221
    0x7050109140a030206010b03090a2a1a0901030510090227030a05030406050d061a070506010506090a03020f04090b070c03090e01050907051317030903010b15120901091a010608 77
    0x25a510b0103407000060158000000411507142d5080103158000200e405441c841040d65480190220051840150451508502090003101102d0a8000e0510807940903842441050307100c1c1d09014084e040341c10540c68800254140c012141d02c0070082807400c82c03e43d241d1200b0342d41005130f181710291011051481c1e00c9681c04030302c1e000514210280e0000e020312f2030036007000012035a550105020132000303074507800c0020f0070b008500501207003c4075010500d40c43d0350791840c0c280e04060381a40002c0c41881c0078018640c2e40c0e40c0d440440011660f044411566841c48036000c0b8010b01107004d0081d000302000d104200801c0c2c0c0016000092621990302ca102c0709895035815251030702e0a001b00358000792104009410300f4011001004c03403400720302d811002e079683c0b0b460b140d5100c00040401e0b4180e420100e21070240d41000d015031210b94204442c0903043c1c044000420029000b80b220700310420100c1008106010000c2d07001c040c2e85900000340412045000c1d05202000340d00b845906e00281c00031000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356368714 1250 356367464 356367503
    0xb0906030d080c0d0207020a0303080906090d120f090b0117061605070b1f090f0f050105130203070507080c03120121030807020717151b16110607050109 67
    0x162032188041c0d8640c444103885500e00712805420884c40b680240e94200500000750391361682d50b20046219980305101c1b45403103010107051000c0942501008da124108000b1216040b0950140c0386107038071400113000c590045400040c00004a0141c503a6920000108a80240444d40403100b84440c00326107207a11040740540c1000d103140103031000203909000da00c00084200c00707501c0c0c020703113403030101450455200e030141e4000407950f010705281e56030b544042140041600401e810035003565001c2000b580740c100400c04c90300165040140d01680000011402d034001c1c0281d071300c0740d5080411140c691040f011600d07a240c2c040382039007205002d000000a10794020300b80b085500103440000ca01850860b5a00b514050f40151400c400e501440d880481c090b40c054100d118091408002050240724846031000c11302c101411600c03c0000040a054407126008101c500000f1100c0c540041c07040e16041c0b510104500b519461340c002d50004044080c00015000303039251174060b207028014049030381380 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356369964 1250 356368714 356368723
    0xd060803090a06020706120b040e030a12050604230405030408030409150e24060f0c01050412020606010c0b060112020c01090c1e1202030a020a030b040c050604140d03090e0a0b090603 80
    0x1b04c90014010511540d00e80b002500702c078043d000c01600220380c0c50180d9010509503003046130b50344002060f0513500803038840b06004190300440c090b1020894511050441c41904106228501e0000036000c0031508219003003007110014000d15080e80d403201d03107a2441001500e5250b44140c61462400f0007c00d01c002a40c1c0d08601980642008401c460b588100a90502e0032008810b98000018001000b02d6100c0d42d0060010b15101c13000081c491926149c20502e0f0500c1500880031984040304220302660003144200701079400c006070070165651180100d407201c024810300c0780803a00200c0d0b1401c0012054000c5a50940f01d05c003191021502d41904080000702d00c440e0b1191980200400c00c500d40444002c9030a01c1e0002c0e0985180c0c2c01a50049900503407d036004985c1c45010f8004c210a103c20083e03580c005d08002c81c0ca29241a10703001318003041030401001c062040314400480c000f018003d880341c2d001402c000ca1040c00605e010f501c06c00003401c0c4c69141c0d40c0144840c00008405140208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356371214 1250 356369964 356369969
    0x60106020d09051e04021303051c050a11010608150126031902030d140414030c0607030c0e03010f020c0c01050c07090c12090c0303031424060d060803090a060207 71
    0x90b25000703242d240c1400c105980ca0f038507070015110912581c218003183c0703541c00103015040140e640362262602d1803070300f645451140f4020072514104060072264644d40a812a001e010300d40c90540d42c030300200c18a035401070125030701800e00d41c03003000c248001320290350103803904a8800c8501c903480301e220b0030851034004400c100800c0c140d07001000f0504801c1310401040d541921343d4070440782005034003500c1d10222120007846840100c0140c00b04810132914164459204440c14040c6041210001c0300c0c9503a4280a0007400c28107855030700c0d03901c505214100329a17012800600900843c034024103408002d601c4a584244c4c00d00440c2180c04055024508503458061420b004219040c82c011000c4001d1a0002e118030400031214840b40140115000340c4411a0152428200c03d03490743ca00602164070001d8602403142c1c25900b0007000c0904161140910561070070850400c121400008409220f82190240c1c0e0f42d140c0b00380804c01400c00009030828032001c0d5078000a543e2101005d036a20003051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356372464 1250 356371214 356371217
    0xd060e06180f0718211101020d05030f19090b060a0b28020a050d0e09060d08120603120c0106140d171303080d0b150406020c22110c060106020d 63
    0x4002240f0498815151260a104030042c10358815071200689020721044c42c80c41e401880c01001d40f4424010300000c0d00180c07140900003000040816007001c4c10a0100400c405100c000740b0001440300b0652003542994132114110400403041c0301c0c50205c55480c0306444050088078140300c0403c20800c198201c0da151012481800e81440c04840c1d40c205412070b90f503c140c00c50082980d6040041c1d41084102a400b0a07070310b0340f080c0090710307006024140800400181c401d0801710342e8040803c0d02103040f01c443d1440b20385034444035601c1402007031422152a544440c8003500141d80c500300003040d481001a83c01c0700a030f00d0b030410601810014030007200700c000b030304504003000d40c4451441c80c0d00080001c0b8030030715403075401141e41e626115040d4002c2910080351a441e00160f0a20f4540302d4042c208507600c80b403540d410319091603c000c0d83c9480d03c2c00981e014401807095920190340c014044c01041810400512680c911041d49000b43d401c09929a050f80c4200b100101c0c917180089070442038130165 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356373714 1250 356372464 356372491
    0x312110f0d0905070302090c0a080f010f06050d061e180209030601061805060d0b04050a0e07060f050c060c0403053702040914030a14070c06140d060e0618 68
    0x1000342600041038000000c0720f0078818001d0000041e260b0041385d503c2a00010b5140d601c4511502c1c02a1188074010314070f5400c0401000180310710480d12100509440c0382d0b00e0034545484245550f9401458650044491311a07040c1107511103071400c0c40c1b2002a81d4545d00a0701405900c00c004c5416406442100c59041e00608010702c00c1d07510070a013510501d060f0580444689643d1004503103285c2c00000c10750041600c0744643c002d142424001c541e0401c00d2008100117110710025110303100c0308103019520402011101d60316074640301e0300540d5054030200061345d2080c14000c081d10705a5000f44000c41d510b01441c0115009500c2c004211031207025403480010380d082c400d540e1038401c10382c07101040740d000d651801202c0202c0d0b904450140400c00c00d030000d60761503034140000303840100385034981a04c0314402c011803400198801000d004440560624000300600f008100642e4091042c071120540d1070084000b03000101c511040c0e003e1031064a40e4a1001401d10b1801e42443d007c0381c504050100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356374964 1250 356373714 356373727
    0xf0c0901051002070b07051c020604050709050a110c03030426090105071403070b04030e060a170405071a040e22170d060b0408010609060612091e0312110f 68
    0x20584001201e002c020f106960205440300384034203064000b1942500c40b5400103c685400c43d440d02e03581034100c44a40002c1c565841d2560380c8541c3c480a50041680322a201c8001ca0761800440d04808107416911f00f480d0340740c0f50002d0340c0301d99a8004032000d403500f0b00d00a0254902001c080316082030a000c65030000d16140210006680720390050300d0460b0100415900c00e968000c0c05c2c000791411622076000c1100b20705041c14000c00194618800c10b110301d501300071500b150341c0c004041601130880e00b440c1305055502d60810b103052040c0f0754400c4030400c6210003a038041c1403054005005913028241082480d0700d56450726007980c0c62106280b440712404042000202e003400358229030361032600c07803150701d090006134988065850310391042941000c081410700c051002030007002c0207001c1070101004000d140c000003c086d21003902401c004140e0b9180464140101141c0c407010345150010035500401e51860001d119114041c0440111450031004040c0441020304a48601e43d00341440c904015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356376214 1250 356374964 356374969
    0x1c0f02190b0c06010902040b190e04090506040204060902160308041a010602100e07050901060503060a091d10090b22060c09060f03050c031803070c080a051e07170309041d0f0c090105 80
    0x440c03011109d018022821404a000c0e50795020b0048038600c10b001504485c01c051041c0401d648064210940050041c031101c031003140428500160306400d444c00817880d03240e034101180c4020910442024120198001140c00d503000030707001070b511035465010031100340400903698640c1524010194020003d100410a10f489800656006840284007450440d60b1b4a10001150803070001040f04040c1544405001d0343c0510020f0001a01075600384100005c035a80e2600083c2c005180545e00320072900c2440c004010051144400359121504001042400c2c20141c9004130511031400060040e8020380b840a10074001c80b030182c24400701840c1543c50782e8400c0010941c15425803003042c481880820301003050b5100060060070380001500c44a1410306025080c0030014158215a08640c500441080700024202c021100b28801c01d000e5103284a0f6864110700c180e02000d9031060410071103400c03c00c0d00750244100074400e0800c4400040c1c040385480d4841081850707031540b104482004014a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356377464 1250 356376214 356376247
    0x1060e0c120a1116050c0f0103020f0901050f0706060306200a1e11030d0c0813050303010e0612060f0a050106090b04150216060804111c0f02190b0c06010902040b 71
    0x70408012880c11305022802049442c4059035040c0d960b5404032658646904201c14004039400003860150f14181d20240e1003c080e208548000c0d04018000820120010100f0161a0784e41e43c011000d01540d952400c098025000040f503580b65501c100910826000445040300c2030741e6030b60b4441c0040f80800100800907026000e070701e0014050a02007102c0040d074180300803c05a003401030006252022864014042d260060612041ca00114604808540e000003640d044030003107031610082c0c6d644c00010131840720507542200b100340b00e05c2061059903141c41190382e00c10b143d801030421090ba44d558003118142c880340710f21424080208428407585c6444d41c0c1d0b40000c150180121082c2003036501c00150040501d900c0300001a01c04003d11003001070803841302c0e0007001c0c211981d1400d41c070040c5ca070380300e05a0828001030024100f07282100031500d03207810500011059140c001042a035404806030315600039a040e80d610302078500041030903410740c403d4030b042d541100b000311b040c40741d22000c06468 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356378714 1250 356377464 356377481
    0xd0806090a1a0a0609090f0c09030803040309030b0f070e0603060d02061e0c030403050f01090206030c0717180301060f030f02120c04090623010501080a020f09030f01060e0c120a 78
    0x4001c100e1102c0a450740d0103903000034182c9940b1150402d00e07115902d000c031100d00c61118001410100c5400d48294400c164009598212110076034135100c500d02a07800d002a64001056640c200c0c0801210f210000c10b05031140d4105c0e11840e98042c407817070070010701d84400c0b42d009500180a442050141c28800090f1003412662510b90000000d0b10b45060616005060451030303e078070024082c0200401400341c440c5140403080203122003161503000410034000100504900700d404a20320007417041882c007548803200304400745550380440c6142c0c0f00071080b2010250b406503080c50f400080a5029482480440c0c1d04000350100f075260950030400c60012084002860b4422400040f0aa46d124070444480520600000903c054a0360345440403184035584500d4800068004210990f005104940d20030b1410b0780043e03452031255102e6003580103481109805204091030656144d00c15401101941c03041580956031340d0b260303034a08415100d00100503210584180118942c6031507604402103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356379964 1250 356378714 356378741
    0x5070501090b0406060501110303160507151a2b06020c0312010b0d0f0e0a0314040f0e0a0509030403080f03060a03050d0c030f0c02060f0a030204050612090d0806090a 73
    0x840401d580c0701c0085086081d02e050f02c0c0159900c104200030740e00592070a001006400181d41140f400034480809105004c40c940180000020740000308100c248101c800918000030400040b110144200e211081d122055802b942200d844010340f203a40254080300d0043c001400700c5600440c2d0f0b918030194000d010701e50300501c0144640400b44040600c840e0281410b002d0003600d46540c1c2404909030340d400b05112a07142c0c600003c1017032016000c00d5210806070035080c1251076070111500c0790014072a80c2c0c0088a1302e2140c0390080b6103c00144c40150007412040020320403501d8040026440780701d94400249240820482000c00f440014042c5500c010001e1402c04040d41c0c0391580c41c1084039841c02280010303000200c0c8810160032601d00c1d0034104807031404200c1c1c2c07481a404510f05100380d0030101540b101c04075040800d1803090b011180500f0018040c50307101c21303c2c10040c44113680240c400003458010101c00741844c0348201030140c4a00e00082c00c2000548078003001400800845440e00c1c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356381214 1250 356379964 356379971
    0xf03041b0b0d1e0501051f020f100603050c0102070807140402090a0b12070906050a030f06050303070f0c0905040201120b150f0403030e092a0c150f0601080105090705070501 76
    0x254980840064540c03401000000b2401031003a0044041240700d0300301500c030013440c2c6070050083d0f0316682150f40b0101c00015458510000d0500140e1038088111845145031090a0071900c0029007600b148044a205034100d40821a05400681e00c903202d5002e111440c2d845100c00300000201440b403821040d001400061902c10a0f10200705e118071182c0000a40c01000079020784501030b15980d02e54014003516140d18001d0810310010582e128080302c0004054880c1c00100c1c50b9103041e4000c9000b0800101181e0f5110101e1400c4003c0c03400b030520549041c918440b00040c01c00f0030380039040c0f269a05940d00c52000f002200c01030300904402d20f0f85034001c040900b400034190200c1d0010480107201130302240c0c44500d10f203002030a17841c038a115140160182c6051080f07102c55100078151131060140110900d40300c100300d1204500a0140382d20141c0306212100f110300500d8000180500d80c201c6444560740d58800043d10314501c21320401d40c00031420000582d02910074009003030400d11074000403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356382464 1250 356381214 356381219
    0x20d02072c041401020a03060e060f03030318070801140f07030b03070b07060f0614040b032a0d0b0a0501150c1205031321020f0f030304030c0809030a050607030c050f03041b 76
    0x190032031b0841c1075504017007a610300b820300103414651241588100d0440c2e02001400090000c03903141d00001d007941501c030500901c00080c0d5107003803202402411545000300200724490020b0a100c10b400c2d1540c1c18162011401700d552107100f400307400b0504001500500c441440c0502660603a4081081512519501c0107600329004c214026a401030503842190075001222608000c00c0310706441d00b07035110740d0007070b0b54541303800b415461540709140683c0c0c0c000341010241c801043c040d0030070000080400448908104002c0001d51009041e210003c40c04000c00001c100c059400504214015200000c100c07849040c041c4100c009540c840e035803030007008040e10140d5800d041d800c41403082e50f6080c0b81c0101035010044c2d0401c080b801603012800102040355001401545030303c400b500103010012092402400d1015190841d80c12a0000c1c0844010b4116800c0032616038a00380d550030f0000341008500450b4034420801d13100d4005005142c0f526644940d03448041c280034194400224040c0c07803100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356383714 1250 356382464 356382503
    0x907050d050a0b030d09052112041710090b041407050301090c08010b04020301241e0201051b0406021f060902070b0901061a070308090a12020d02072c04 67
    0x80342d0081c0400c1038049072075005041010b04218240d55244104078020300200081c0c1d40700012600340034540306400131141c001c9820b00d82010084070300a910a04000340000301c1002000300d40c24900100410759024400d040c08890a031004542c02404841f00e4001080200d88000348500345c20081c01c00301c1d0310003aa03440203e07080d9070084000783c0c0d0150780441c003001443e00a000780403407018121411803a541c1002d01c0c401c484c0c1c0261160342d500203203c2075280c031811700500424040b21160104003c0070312441800a01130041143d8504503c41221402002c41d07452105031801e0350b0071034015040801c1c40251500c0802400da490404540d1079243c005410030040c8010101c80780a00c000d040149000704040d400d40e440e65014441e804045080b0904124030305090707581e200d80c1450188640e451300c900040c50003800503006004c00c22022624010142c001444035485803168096450496480c40c84038840740c246c01000001030240e07112559404000070010764841d115001d91010050850341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356384964 1250 356383714 356383721
    0x806040f1d0a0201120b01140c10111c090201050d200a0305010609060804110f0d02150901090501030506100c1e030f030608030c0c0108100315021e040f050907050d 72
    0xc0e0340910341140c0b22071019540d00c011840d0b01c4052180d000d10a0ba282c1030002403603183d90b03001503441482c01088019200380b00303000040c4010101c5c4400c0c450846c00c10107003c8198403030040052681c40388809100700080d81c7c0590800c064058460600b845407680351039015004003078456002d0002c0304001c08801244101900c4101d04640d80081c481d810f00744c0141c442d44c026002a0184400740c0c04001c000382d000c14100400002c2900c1903c0004101d0b408605c0107036070303031800940c407244900d60b01c0c403084032510107070492400036038035201180e560b00c2c0107500722482510702682040c69445a031041c00e00038030020b421141306001032071070710b100002100c42031210240c01300c00098205400802d80340d81800783d40040c2140601a600c0c124802d65010360340c4450b03a02c5241480f0042000644200f20808258000c54012800310481303a42c001010b03009601c0322204110008901e16283c00c0b80400e10151401e481c980c102d82102d180c100010044c0140b0001c0c580820007208000219285030b0394003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356386214 1250 356384964 356385011
    0x204030b16090e0406020d02040504020d0b0f0105042306090306040602191403040b070207170325020303031504110a030c140c2509060b0406080c0a0806040f 69
    0x80c04050504000101001e0104054590303020072450074800d00520350549000b40e009580098016a2a420340c03110101038041c40c0c3c0005c4d4002c1c408641c407a121109138005e83c010380c0d4119003684400d54810015100b130f01840c00b411400040c2000040000c040c400706040c0e030300714010a41810b061080000900d4000120303011105103401050780d03071a44000a00a181e1020a428424080522a0032059140c00001e001502408804010801c10b90007440440060034041d0580000b01400401c440d0f130320b41c0320f20700300841030300b05e208007094551900c0c007403000f0f0380c0e401030240d880c0d92964032502d50a0380880061590180c0d60300e0910f4407d11100c0300400b2480c159850114000404d058050000c4484401503240000100310703e02d49400041402020006041c1e5a00d881c00c3d181041d0f000403400c0c41d00240d82151410070080b850048080142c000c41c3d14595509260f0f617030f18050b42d4603e01500c0d1900010940002c0072030701500d015041034081100fa40400559070211800303511507800141e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356387464 1250 356386214 356386223
    0x20907090305070807150804060b120102180d0f021e06070609050613020609010c0503040504020d02030916080c040b12010906060614120112050a2f010f30020403 71
    0x585080040041c1800f400e03008101d120054035030315150841c1d541241c0d402c1ca00c0b42c410000d205000a0421010f640207400691001d4540c40c031040811302c20600070f5102c07000505440d850710101704031520f040b04a94140c1c540c4600d01021142440d4280811102804100d42e80110741c210400d095880720320260043c280a9080410348039842e0501c50300f800b002820a080d00035051001c02c001d601c64200300c80756150b003071030701c00380752a85405c0440c218022600402d43c018000070360b08084080300d4010f1030140403890251000e900b410b001013000d080303042c0720301c1e805504030444820030f514003580861502c0c280a424041d10464175007004d403c69443c0c1c8000c45600b075894109100590748500018001e64031500058601040001c89010b0b07044144590728405034419460b07004c000c0207104107419281c1c45120340d4044421009040390480401280d40460741095080103050343c420038692002c150941c48501c8520301c0300d030003400043c00d0250407070702c002012140c1e05010320b42c5100800045004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356388714 1250 356387464 356387477
    0x40e3a0c0308070c0f14010b191e060909020f07060c0306090b060405030c10050c030c0a020f06070803070c0c0f060e0a0e061302132303070602060702190609020907 72
    0x4901d400b4000a90181c0110f00f0071150090f0540041c43c3c040605641e2070300301d040e641c064601480c0b8035000d404881c0d070b8141c0024080203070800c0440806103e100f0307205841225510080d1400d0034942e81a620700c40d190003c2c914030000c03c181542580185034031103010040a18081158403078901b5218030011030300c0000d681d0181080740344110311a50600e8a412103403d80342515200c0080ea4480c40d245003544141c610441e9044030134002c03030884041d40c1c0703920160b0ba142c95500c0e81c81602c90440410980c001e055650b07186040e403500d207044408056000c04490b0039a11a102e04440e01061070f20f04a400c40c03a046c901041c15100d060002c40208a0755440d5245640c01707106105003c41c3ca0740c8034030600103951043c42940c2d030355803944031401491814010384920a440500051140c0755204450905100030180603d44000320719003c1c0000c02e80440d0b00d100c2d6079010407656010f04880410050b0010280c034000c44101c0300310f155085000720340210781181d940c0c0010305400800e86000f00800c51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356389964 1250 356388714 356388737
    0x150307030f140705100905040b0402040e041b0603090803161205090102180a0302010507080a03060f06050a1b020109060e0a0305060f0402030f0f03040b0306060706090503090f040e3a 80
    0x1c04000490142c1340c20703195000303600080c100203044082135003c0c0610032134a4002d90341e00350b2a1a81958010075507051348010b40d0519080134158883c12007640500b14600040229425020340240c07148581c0c02003c20349555503a6021822640c424a50300e8200007005488120401d454000c413800707909020001039440c408401450703205500c0343c400300d0145042c4c000402c0584c1e003020075100029080300720a5560345040200303d0007004142c100e0401c060f958940031039000e6100010b40510103c40c0c480d041d040c40400d154007001c00740d0400c000d000a06c09802400014031030f440140f07401001800000129031207603038407400d040c0125004010482d410040005620781042800250b05220300034240c1c194000c03d04ca52284a03a000d40302d514100040803c2081e08e5030700c220341d035080c2c12503c02c0240c0081d51074280d40f40e901290752584200400b9400c80790b070385820b104020320310300310500416a00c030121002060012a07801d100302c00550000c0ca212100240d4031038802d00e0350703595a41c92401742c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356391214 1250 356389964 356390003
    0x1202061b0115120c03240618050703050402030a1202240f060607030f0815100f11030a1d0f0d03020c09010f0e041b080a0c08010f0207030206150307030f 67
    0x2401d0380120442001c0950101c0840c090b64186020750b070300843c81120103d200c03081d809012284c0700a501a9507c4c0403c002265107140400d03000d844469002030040d5250300030200c1c01e441040d10701941c1904080380080014851b5481c0c5554200701b401651500c030352411031103107000710000020b00000e03040010800310030001154580c2c42041102c1c00c1d03007000c8603910000d1000644031101014000900082048900f980f44c5039407091500400c000d00d8800080d00080c0103009440c81c04001c03030909004460011404020b861000c54a580d030f54100d8030b0b500c0240e01e10b07144041034003500b142d020815980d5a440d801500c0310418081d80080c01c05032490028416001c40580c090348500c00c1d603d00c03c2c0070700340441c5181c0d40c01c141c00c82c2c2c410041500c0801d428829604540c0305009034030442c00f1540c10804900300300811074030210000c010288900c002002603105100c2d009006130011000110942c5812001e050007410203011100301319205c2c5d840c210a5075004030705a4818440d110b04c02c601d00d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356392464 1250 356391214 356391251
    0xe102309150307052203060207050309090a0209010e27101706070c120314181b031513020312030402091008030f07170301031b08010203070503011202061b01 69
    0xd510000742600d14542008000c0c240e0140c0301d50120710454003001040300500005215000c2d50708a0070840d41c50300b240c64626607a40c4081c2c0d185002c0c400410002c0c1c0402854401c0d9000c82d24107031124815207441c103003000f01c544600e02800440010016a4030084070b0b602d20303030034800c100007800d51295505094100c0400051118141c8841c0c2c0003004004c0721030f80c440090b4008a5001450b5009908010002d801800c4404034840ba040c401c00e08010b08501c0040070b40e00d842c11b002058400007000140c020500040b0f6804041c0c040d804030340e09142c1c200c1d90455641d0311400550303c04001000d5640001c0c1000d4541503080400b50000c0103110a5203841200180c016080e814064020f501c2c290400380c80b405080405108144041400c03400d00802c42190125601100d800c20b690b580c481c5403100c075260a480d50554048401c56001c04e840005100b10f030b008d010b0300c1d100c0b14150780c03030201039000380e140c045005c0303070403150510138820452192203000030b000e5241c400103d56010f1440191000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356393714 1250 356392464 356392489
    0xf02060c092409032503060504020f120c1306080303010501050903121210140f041a030a0c032303040902070309030623100506090d0f0f030302070501110a0e102309 72
    0x55500e006040c4805c1c4050718607110490780e0004000c00c00b1b41e00da00001e1003054a800c403540c0c1010111580810b0248080740138421400100c484124400c00c030840841190303018007903409a948100010320956008501030280c5450040c219610104045203000382c43d0132500c00300c01c2c41e880e0801840440c070a00c4151001138245039180c800802803c0700001c20064000c054140659502d40442800d1181e01c07001046008000e000c030b4401414a2619807840d060900c020744103810007404030b60a41c0d104028803000c4a01c03c1c0f0003503040c2070504500b80e0003540000e00031814000e0300302002000a00900600c0c0c03903e0001076200c0501c46106017100b00700c0c00014628155051855001e0060355581c0c000d645000400744d0b1030f4280540e01c4e1400e6623a111000101604141400e00e01c9030402d135150b001800300c6803058009000700040707103465412a0055000100c0821000501288a41007108540700c1c0a0214a8420a04010001c02d1400c1c8072000125124001d800603985005d814601c004010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356394964 1250 356393714 356393743
    0x2120309120c10030e060703050606090604230d05060c090625050111090d060f0b040516030c090f060807030f020f0403020316050105190329040506010f02060c09240903 74
    0x341c901c503150f106d181c018050024550b40c0e0020504c0c070745400041e41d0140034054807080e9540e840700b840380300b0824140002e01a82c2000b00c444038090900380d00740044903034820010f08003500c40a40c0004a1b030010342d50550018001d1000d52081040304070300e410304030015290300d40e002d8000d00f010360035241e48141044078000208000740c041d031034600250040c250404030014074044c495030321070040d10680000c1a0300c05c0c107010612030301c4040d0401011420350241c404000707c254801042c0d406180c2c0740b0800c410b4421410b0100606800382d4403103540401c40b032a00081c0318081e01c8846040340c100300c2c0746052450001c02c06008500703041000310491956440840000362501d00000c3c29841841d40d80506c01c0c1e096030103409500e009420a01c0100350f0b620285048a1400e21000312402c501424144101e0030240443c00c954095011134548440682c042c0c0020b42e20f910821400c1c0c3e10001c016a080440c4d910031412031155690329604900501c2002071307a8a504600f0949005080c1e60310f005c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356396214 1250 356394964 356394971
    0x30618061b03060d060e0a06060f080c060406050a05070b01180609020412030f020f03030f040605070809100b15130807050303031006080a09150509190c0302120309120c1003 76
    0x2903031081d40d50603280e1000c004c6400d020010030f07501e40003010f80408241505c0c103105807140e20b01001500c0d0881402c0d21104101c0244460340c808000da900e141154019030440401c010074070525103e4401403414801d2824003604e003c01d142d842c11a0709209a10a5402c96440d4038000705e0440507000b03400c0101601c18041d4206401c040303203404070f010000001410b02c10100d43c807505090003400560010300e20310b01640e0700c92514096403030100c01e00f00c8041300c295180030006400f90740a4078001780685d40e030030000d2145480c0800100c0041c24100000c40d444142d0740c1218000c040204c0080c0000901e00010000c240c2c40c2005280c940002c81d00041e12980083c41001100d503901291403040f01c03140c0c41e1240d560348a0340714540007407804010141100c0f1240040d0481c026642d004240260492021a6076400e658040010752050414000f004112145010000b40c070b402caa030207102250b400c4c01e4902d4248a44001841040e040041d1031064100e080102500d2910f2400409014060304060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356397464 1250 356396214 356396251
    0x903021614191d0702011407052b0204180501090c020607080c0d0504050a0c061d0f06040510110c0d03080f18010c020106050319080901120b03061806 66
    0x70720040030804456000704500312440c4203988541020000800300706029081150300070a581e206000111100030156003040440102410741d41c14041c450207207641c80e181070032540b8242251010f07040001c48409402c080181c0795400e0248020001001c108102a8100550509035016070710143d2219041a00c0c4c003181100480c0c01089a551101052a0448043e91207402030455402900220713094245003404101c00c000c80000c54254090141c0a80c00c3c00658900b01202c0104241003802140c5003011546a120b0502102d10030b04000000c0045003010f443c2c901203607002d00020014800101c034454072a020a00c1404003804da0074040c2e4184040e44050f45000c1c001d6280035100c445c450840000148903020700240c01c441d611080c5000380401c1e001100000d018100c14080c041c4a40645010100c0b1804440d1552405603070003c15681002d04140042d546240841201d540483c1c4a101c6003d8a590034048a4070400401c03031141c6c220003013044851715048004001014100d00151107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356398714 1250 356397464 356397479
    0x509060a050d031106010f030501140601050f070309081005010f1a0703050304030c050a12020f0f0a0210050f040f06111b12030909100509060a0b0d09230109030216 72
    0x3203000740c80040d100c500368840340d0b260440e20b0000706250700005001d8000045014203c950220301202e0080c17000340302e03414400036203003100b0354103540d0903001c00e504103c80c075181d000180240035098001d050408031103555002450030311030b000401058a03540e03103006010034000c50101da000340490303a4101084d00b096821100080c414804060f05101d00400040d0400d4851401c031003110350300c541641c214148910b000080c9a40154070311000d4091009d07440783d2500001007051008030340c24000c03c40306e0240d13020300c600a441c4004001c20080104181c1540c180c181d40200f00826900c84020b1f0032514141d4000c1c0488600610080c03513410090081d1078044d00071000070104c14040760240115001c0321089861403041e80100d0350481010000c000701180701082c400e003280d9003901c1000540d0b80d90b10400903100b0442c003500078400401d000201182070b0701d80c8002d50b00c5118070042c0f00c1c09a0074030500005007010710360105c16691283c40d0581019818844203080146900c24001001c3c10b0901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356399964 1250 356398714 356398729
    0x611130b040f060c0c080f010c02070503011127030d0909150e0615041d0405070602071d0709171c031811040f05160806030a1505180d1206050906 64
    0x5074002c200c240201c100078004c2c8000507400404240b4111f40201d0b83c0306c5209030203450100b500340c1c05805200c0000905041c180140c0380e000d00c0200300c140c500100180000404c04413007821200138000200100785a07101008601c00102590329251403481c070700030380e40003503814007081104001500d81c01080b14030b02901c1034a410502c01c4440300342c0380010308140d40c101d014907808010b8401e0846603c0f411901040340307040c0664002c400365200907441c2c501c1070307a44040b54407440d11880c0c00c078440b49040e0020403440c00e42103102450b141c0243e43c0e031251601a001141c10460541da0040680442000c2040c140d452a03c1528201480301100400340d00b004c400e400d240240080380f244646805c51b9440f0341c07018800800d4000200198202140346d0740000841442c0344011450300f5011a404d403900180706400660b005180108461006003d000500000f501d46007201c07011081c1c16942c1c0c4c10070b101e04c00741880a076444841c00301c915203026013550300942c403103801140100140701107602c8040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356401214 1250 356399964 356399969
    0x30106030c180b0903011401060503070f0e03060a0e0f01060b040603090f020406090912051303110315090d0f091505030c041203020c1f0206040b130611130b040f 71
    0x4001680c1c0700c00c440d0035101d101050205001d1103848a002049411a2001422610b00b042e0000c00910103a02016501450280224404180203000160409108445a05d407031000f600d040701c0343d201ca01000c68a0000700383c9003030380000e8840c980e04200fa542000461004241c100003881440d14000310303408944070760301600d410103031202c644009010448c0241000240c0c0600108810f907030b030b140c0071401803e1000d0211154449075410b0195907114206a0b19500c034011034103010f441c510383c1d500300803500786a43c0c181c06009400c40c91071040441c00000c2d20440d0842c01038500d035400007000400c04041a00c40e6018410245014041d0b201d69404601c1d41c1e001a0506030340d251244002e40c0500d011313540c040750003050120304980825a010951920f15a01500c00c0c8405004913051010400007450b81240140d0040000901080c1c0007809180c124130401821032006400d621508107803149004030607080c0c0400200404c410070300e20f00d014000c080075880c1a0800341802115000720041d407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356402464 1250 356401214 356401217
    0x1c0506010c020103050a06051e0f090c0d05060418050d1413031203090c031a0109021602130b06070b011a0333060706050a0e06090a022101060314070b0a05030106 71
    0x900000b0390012195000c400a07240040200024111036002809052002c0340d0140c00382d4030314ac9004042d401c0c5900490700800303c1e200304504160201e41c03810010300b0001c000c0b03a44039403901c454001d16000861400040c9010f5800fa045924482c03070050401c880c1c90014200c01d850070000034808001d0404000700707a90340b21000c5200c010212900b1005800802805844c5103900d0400004008041500640c15402c111518030b81d6a6105603035012800b90150040e103105030012903000501d46112024198213410f2030001e820038031400801c401d5084000104d60790240440188541c100000c80c05402c41c035a2039800b840d5182811001c0002000e51560500008007054107030840c44081252454922000d855a510394001e8202a00038107000d0340e0f000301061411444448051000c07850610600100c030080180c019030f80d003030000d201e02000d9036a18540c0115940d040d44071007030056000860080c0c0844881000c030740c0c00f03a41054410340c0030600580c000c00600d8101a0030034141e03030444102e13 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356403714 1250 356402464 356402471
    0x7050405151b120a020f0604080a0c0f0b090309030105010915050d0c150e040b01020a0201020c01050d0204090608070303080c031b090103150902041a030405030301030212030706111c0506010c020103 87
    0x1624030002002ca0b140b401c403070080c028480c1c2c05081002c120082c04011803203500304d96481c10050034450301c030702d130580d000790904108100100040780a0800d0b5900e4522895540003010015221150303554401c0e1303000f040e650000a00032000e49001d00801713015090030202000520024104101070094601c5540d00aa01c120f1800d4140804c3c01c44680041c058642440d00e500e030400401051001c00010b507a10440c0303007400903101544001050a03005906030000c081e249000001904c5030b030010075802300400e8003004046040582801060018100c0b00000c1680500714a17024000030743c000c0c00384140d0a802e00070004c421080001083c0b9082c90819869035451403100101c014103a40001410382c4400d03003000103810041c560040045a0f203611001400007404401c80748248000e40b00070b0314952040c0014005407804140b00101c0464800c1220b01e045403a60b40d80041d214510307491481d0443c0840e200300070421854022003101c01d0082e08018500d001d03400681380b50601c90010341016034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356404964 1250 356403714 356403727
    0x9050702030c0609030310080c18090f0715030c170a02031e070e090606040e06090a062313020403020d030e04150b07021201110703050a030b06120f0705040515 70
    0xd0048030b24001c201070694085180c09204a540c0fa4002c6c2c6144221403880d410001d180362000c00e00f101c141000600640301c0d00c84004c1c80d40704014026240c09464003c0c00301c00c50347c483c0d04202c1d00d4000c0c8450810b00000c0e0040c0300029046580f42c0101c42d0070300401d401d62111607800703042d40079800300e0340380801620780d1240d80751540c6e0345503070f5440b41b201004800d05100915400c44c010141c449011114500241c0d606410302c100c5000c3e40c41512034101580d0003042d13451811251042d4400010900050300590310700303036072281301c0715510800842e4441650024803070918405004610706a00e01c25407800c0e15540c0881d08990100784054204400415103508940d2030381c1103503004603482d840e1b81c07548a80700e08075040161b01c82d1400301d124125030310484883c8101030254601303500d0081c600c01e09010441d2026100c0d6407064140104040ea59807400b4569580d444c0a00003442904240d02814900030a4035902414054005070501c68184410041a0f0b1100c10410f600900c05c900c2d00d88601 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356406214 1250 356404964 356404967
    0x615070303240b0d060510120902061e040602070f0f0e1005130e0105091603030f1412060f03160b070c08010203010b090a0623281e18090507 62
    0xb00d90010044005080c0400119140d00c14042c200080070084100702c459a558104603103200307011904404100351200c645078000e210761180e0080c500103807280d494417a030b1050b80e14811902e0007155804001c003040900006038108a04006050351007880b02c02c10342003100349504000e0034030480d00c001e00e14038006080701c040c055021004050190000710340910610b07200010b44030110100c0f81079864140044d140760030000e0071520750706900e4070800308641581c4040350000000e100707040c02d00c08112800941110010000c0c1004052500414018101002002034810031142000d120354020b10003641281f24801e00d001c2169004091103594003100d00e4049000d1480354804d10b020351011000040311504075005003003103041150120303a41ea07240c140903a0850146030310000e80c9010304400f000305110a8009140700c20032002410301045c5030030b80e4402020350541e85000018003440b503800200c0d080200724100d09035103040c440321040a030401c0c446e024200784100d13501c05464001007024103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356407464 1250 356406214 356406251
    0x10050f1b0607110a1103100e0303011406120105010c0305070f05160909051b0d08040e04060b09010303020703020d23070603060f0501080a1503021e0a05060a02030a08040309050d05010609050615070303 88
    0x20991803008c1c0700c1c0010350361160703440c0d0b0000d1140890030481070382c0c1d5104900e8841c0403034800c00300752204002964204401101c00c40914107003102409030820040b40400c014600e0f8551284c4624010004100121140101124164056152142000450000a100071030300310070f400b400d07032038100c507400c41c120000b080300c4c00400010b40075950000b0086440340082002a2150340035103024410302c070044c018801c08100900c0043e00603007004000740014942070641c00300c04c9000e0603041400030040070006030080003c54041c9402c0d404170b00201300440d058003a0b42c00828501109a007454034060001c1c04015004082181d62656100d02c0d00c1d801140c20b1050001e03540140c06a8100c0084043ca9003420054400492040140100026141c40c180d0b040300c0c81034039241e01450170001c01020940c1c4900b00503004905002000070007107a9a1141080444801c4c00b810000c51414900a00c0c00101c0308080e11050107011000d4504414100c0241140d90083d4135150008030030400e043c014854 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356408714 1250 356407464 356407483
    0xb0102030912240603060705160b0618070c17090d03110f1204081009150e0f10020901030509010e0a17091f080709050f10050f1b0607110a1103 63
    0xd03ea0380304004810800d55000642c0700d1031007942242c1c901d0b11626810f403a07078001c192446100220012000000806105031683c1045029251106600c012030348188000400c0f29400001141610504184030311042c0100c0040c101c0078005144c40100d20100301c940c0848030000d41880070140b070b040440c4400b00003569003a0301c51000d6440d6085902a003080ca54014032810304140700b60940c284d01942e0354891000840c1c0e0106032a1048204603413840d0160032107038800c0032a40a0100c94055529003401001c21031984c0040041c1c2e2061150300240846502610100c503a82c540b071480c0c4240c150000e45009800d42040104403c0d42e00c1d081202840d100d00060942c000c81d9140c4101060410f40034103403000e000a40300e07141240d4440310103c0e090020f070f08c00e290384450414000e81040c1810051486601940d2030910300d09480c1111400d00e6601c0200001452022850075180d03100c828020300c2d4004070784c2e01d400e02c0002d650b030205aa60301140070002d01203200144402e20030303aa00300048101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356409964 1250 356408714 356408743
    0x220218060409050f01060f081801021e03070908152809081b03030610030e03090307030f12111c03090b100306051602030d020a0309020d0b0403120b0102030912 70
    0xd8568039040711074080e143c140d40c104000c4880c0e000229200307000d081100c0c20641e1a542e031100c41d554150043d4601510842403281e10f540c00c20204070300003101e0001400aa0807440059a81e003030105000f000c50300e06038016200b6800c1255800e08050500041750b4200c0f00e03025a02051031202c149890700f0001d0009151580c5250990300c00c10000c00c2030240040311103040d030591414440f901c15a440e40301c1125881d0f40030703513840c0b030140760306009078072518580c0c840303070200ca040c14808000709203403218035081600c0382c40d000d00e8220100000d41c881c01031480085d140c4030072a0022048095038032600da900001d00c0302d03a01d00130015050311a03402000f0054101e08081c040341052000a01410302c0f41c003040e982d00e41014000f903500e866000011700e845625078025485c000310128580c2c006e401c40c406040c2056100c01c1110056900d4104180e070141c0210307003005c183e05140c0380181c1700160345034840c103001c2d04000607c0d6590fa008001d40c0e02c1008190341c452103064800e03540905100d09000e0310348 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356411214 1250 356409964 356409967
    0x2030730020a0209150d02010807021e0c13060602070603110d020304030f0807020d020a02090417040320040c09050415031203020717030610350901050622021806 71
    0x400c8590000d0340001c0c40f802501c114070180c0320001050062618400481e0700101c1404c1240d0065100d9881c1d1540b040403841619000c01103500e04025001c074000807407515510030000d440d49494404903490201000c070404114151505c0006900c60345184031700030a047d40d904600c1c64004c40341c0c04584002da0722403c00c56680c03402c0d00d0090001c040343c00100000900e00030000b400c06000040300300d1148015001004000c44541c200200c2d02da0040c01280d1000d9070080d49040c901e0f04602030000346110f41414a100070000b0a100c07040c19810303460600c114109100c40b60102d410429010982e107040c1c5000c516000ba0300c440003541c0c0a82c0c0e000401d031f100c190b00d00c2c0144584c19405803000911030b4180f600c02c035807103500005d03e5010595a00358004444082c030701c4424010b1403e0071300403866a461100d0b4191001220701c1d000c0105500c40014400c240400c1014102841165800030742100d080140201891141e404030315801e654480700b07a0b0010382c110085482c41c2506950403c01001c85 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356412464 1250 356411214 356411303
    0x706060902070312050907090b03010b040c020c030f030418090302011e050117150c13030c030f030807020a0f0210050d050c30041b03141b010302040303020307 70
    0xd000a50022038141d0010b01c00f003840300840e6a250203114000d00b0303182c005044d11030400304460010110107d0b03450340b540d41c03200a0000c68440d0300440060070f11940160101400c2d18051504005600035421090340040105100701d812400b4484071640c419100024594070510f4240d0051403100b480301d510001a04210356043d1140d00002d040c1c610f60050076079846a504c1c21540d80388119503110502c2c800030030000300344091210141c0071800071b0702031742c0810341c0c0d0340e40f200428000542c1098034480c1c01140d03010b003410b0304420103981085d035910061241d122103844610030740250700d20081c801d408035601a200c01d8400e0f400d41316100310a503420841c2d81030104c1120002d40c0000b00503140306d080c03820f04c602400c0e02002012041a80c2941d006002e81c0c0f19503451100202846900f4500d00c103407e40800800d013640f0b80c04002518000c01450320303205141c00b81c102491178681d0141014010001400080d03804401c0e030307050f0b036400482e400e001d8a08150350140000c100d40b40880360b10810088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356413714 1250 356412464 356412479
    0x703020d1a030f010608060411030a0b010e0703050f0708060d03020c060f0c0601090c051e0409020f1b03190e13090c0e010b211f0603090302120712050f070606 70
    0x104185803104404490741c00718050b120600740c170494405d4003100c2e000000003038042010803058640d0008024251030700b09000355a07016603800280c105c01c0945040f5010491600d4041c0315a0781c12400c288100d444134641203000800040e07004040501070f00601480c401014020031821400ea200104010384449007100400119042498020140e1140030300019030042c49100c1c0c0e410f000c00ba569801d10b05000c0100401d505c1c1c07240c000c501d07c1010100000111508144041d0141c41002800c40da99038028034550042d501c07042d48451a16041040344032841e800c12030f02c1c003540c030b11181000b002d00300141c3c000070050005015856401400d00710400301300881402c1e850f06803a510b01000c50315907200c0303000e10100d00610180114021031040d180508a12000c08554002400318502d450510118650101204164483d401082d251000d07141016018810200701c4031407080610b0400c44244c90b2000c24581c151030b0002030082c0040e0744d0741000e40d15030031206140e40200041c000342d6540c0e0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356414964 1250 356413714 356413751
    0x10030b0d12210c0c14070906030305030f160219050106030b0a060f06050306010e010804021309060b100302030433020f09210627070e0115020a03090e0703020d 70
    0x2150040b65031400c400c1c03004009115080036004690b0320090325603210755a016920313000b8414032890b40306080700001d4000d02c902994010798484e640306900c0f820006241c5402d110041d0103850100241d40c082c60702d565002a20051401130080300b02000c0c0c041c1d0400b640100348a400240600c0990300800c11032440b03540015013210b40301011421220351744e01086541307004c19038003540050000708052074690300c01c0b2101c50f0007600040118041c2e1161a03a0502100c909071f0301103810903141d075104003d41c40c2c80001c0200f0b24086e410198074504e0191340d201441030b011248401c01c00c448a154002036466030604000d001c289020465455130300c800d0401917608504070f1984540d040600e18480d42c0e2000f101180010341c3d50000f00340c9500c1d8100c0150700965940c8082c03000b1034039015400c011240810002004007402102440345504010409054001240345e120966028100c091b000a40c07108090003180c0c1030020854554541080c124003030700c2050f001d002003134105441202252400030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356416214 1250 356414964 356414987
    0xf030601170601050102121204060b0306130303060b130302060c0705090a06080105070c1203110c10140a090b0a0f1d06060108061009050d020a0512280210030b0d12 72
    0x1001c482c401ea903610f004a13903e5090320008400f00c1c0c1d043c0010f070100c54544c80041d804c54407444021030707400c500002003890300b081114113409103050640b41100745030b050710030704000d48280441185081d4030340c06070114800c02c504c0000c3c091900011090529601401000045d10300180164035034180002150054901c074000e812042d4a484042248140590160008141d2250480d45c4001200f04140e0051a14030620508414204285a1420014001d400560500c0300c070005010103100301d6121421001044400c0003460000b0010215020b20101580208170030808103003902c454040c0ba000e0003c0c80e03a542064100703080c6024080101081d40d62044200783c0e070300303140d0743c1d41c10042144a482c5009000041414000d052019042c50010841c9107800a01000641651003010904440c0c80d41030407889600804464128409540840da406032840801103042c815203800149515041d000c00da800e00d940c13030300b05055035201c44130528a0b05411840a0b60058000a0040e00c0039180701d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356417464 1250 356416214 356416259
    0x3140106080601031502070303060e090a0b0c0f19090f0312031a06090d0c030215031b0408030909060117040809040c0206150f060409020c010218040c0c08090f030601 73
    0x2400429100c10002e88a4120794002e80c44106500c6481500030080d40301c0d0704164205616000081035901440480502030507103074005203071407145420700203102030001d007048005102c10003101e41410003510907500c00c039103d07191818021000e0802034420b4030181e4040040c0284000c03001080c0b1010308448480707240c440d10b041c42030041c0e40ca00100702062440d0241d5200f4001e01c0030480d241004003148443c0c5100d001e1900c0300c0e03901c0e40c00160a81c1000c00c00020345a070000104005070000b0b440006940042062490410b030030a0170340c80d22409201005800f4412800009a090780b2a0841030850130403034601000a007405d08044c0510b17808101180e01582c101040d941b501c5100064180c82269014a000e128040b2340c0100056400b180d4103069010500f4480410071080c0b5200905190b8075080c001661800710b4645101c11085800003a803196103007070250718503d5008030801d82c09560194800e65556140c00000e80800e01a040301a0188212400800d607000c0d080649407070b01c3c050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356418714 1250 356417464 356417471
    0xf0602030a0e1909110714061b0c061909120306050102060718050d02150c06060f0d08030a0c030608031c0f051303080403030612031710210c0f031401 66
    0x41091240342441000c880044070710301501000060215805180c0c0d000003050441c2c5446c00a0f11800b10840380c84000000680151043c40721104400042c8000c276840340030183d0900300d500c1d15040e1141c2005010300d648018200000ca02e00310380351f208041c0c513680100045401540140010300401c0c103801a0b80c0580705080c0414071003400364168404e8a210315000c0c0c0b18440c100301c10f0007444240f5660072608102d60b000c1c0401000d1243d80170b4103402050700010015860410100400c6d00c0e20a0070460060080c151140f020a511504032a80501d004801040c150301880048000b44030395402014036020114071414105211407200c0a0752000e0302d4280030900880c2c0f2000103c3c3d4003a50702e07068181d03060200d0300009000d00b09599005000341000100740380e440400c44000e5000c50ba088000800002200030080701c41c5280c55008039100b00e280005a0038685158200d011403050000c1c505002041d150800c0449004400600498610040a20784d40d1030180da48111040c03400c1140e508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356419964 1250 356418714 356418737
    0x21201051906051806070b0a0b0f09040b060102210901020115210c0911030117151317040f08150705250507060e030c010306140907090f0602030a 64
    0x10150401801441c92002800c1c03210715000c000e503034680c05100201114403c00e007204505980d0140039000403401101c0c3c2400e030b450001c0c032000403580815140d03489685008440d6150f9121b003005540d12940c0300503081103646039000143d10b4900b180110b84900104814611060a41c407400b80820490a8009015020b140315000c0300c1c1182c43c0c040d44170b5501d0710203c90384013000f09100701603049004d41003c0756500d031255110300554201c1000c0089695001004000b0740740815081983c0740050700c09004a107a00a80000c820600a0040d0308560031880741d410500951807440b0b000d45104a21141d55607590701100d2508408501c600e100070702540380150000060101d1051041c0d4190391040e241c062060040c0009035029542107140c0655644c204d0000355013080040060052504c0c0c1c2c6940030820380c1054640a141302d9403178105814800208400040302403074605041c012904000340707075241842142c102c20507500ca004580d400c1000002e68079000310007040d04c00400e81d0352402a80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356421214 1250 356419964 356419969
    0xd0c0503040b0a0203070504090e16060c0507060305070509060403050a051e0d050304030e0d06140a060308071509050706050c0706031406010c080405030115170105040807032a03020102120105 84
    0x10031078020b0440900c1100095031940c041e401143d01c08080d040c01428a42c4444020342154081400240180d118801442940108284010040c1840c0c81c0c5400071184a640d4280c807140329105080c241500c0384c022503e80c074000e00541e43c8610015045230b4565076642001c03a901c080d0011705a031513000b80c469043c55400240d00c0c1d05640340107d4010280250b039039004a49030303070004000383d0820410f00044403442d075a48103190b40d581c2c041d140c003003105180c41d040840d0506001d413640800c903250440400004120750141c2e803491388c1180d9801e01d040071092400c80503188a000080090246030ba01280e5160490007070112607041c6021240c0b05038075110287c1c11910b40c1c034410710981120200080e21513204035000c2c0842e5100d000c503542000cdd079a04c04a825902c1160620070b118210a8050040c0f91084018202c440b1354100280160304084e140d80141740f04000000c3c081107801c0c4066402100b004d080d000004d18541c0340d84031a032115045c024000e4121a209003000d02181000003200d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356422464 1250 356421214 356421217
    0x60906110c01020405280e09100f02091f0e1c0f0c0e1f0308031305070f061806081807030209151c020310021b0105090706110105040f0213200d0c05 65
    0x580d1b450100d0404242480f0070781c610f031403000705800b619204110f400804005140581025050a2030015894030f280c001045081800a0701c02d12140d103200744024002035014a41c1300c1988425580803400c044032640b0041c2c5e90011704c0008d001c0c0100d2145400810001908400c01c6a4184142604940360741e4945000a01041d000005000000b1418000304519500468000c180c1c080040404070349039076600c2c201101d541c041d1004600c5c00c2170400c01142c0120401c4011070a1540f1058403a003420400b504140b805840c0d426000f48a6020f0800300e8810406e100c003964000346481198a0080401440070710903140e00c60050710309091042c0300d441030026032002e80d03030300401a049085820204500079046005001c840a0909031500300b1070741c0a2140b6806030070418090315860b0b0900303c01602011520202f031303106030714080c200400b03d0070041c1c5100032594111068903011080c0c0e01d02d1000b030003903510114030440c00508001c5102203100001c00c080036000c0428003803480c4209064606 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356423714 1250 356422464 356422519
    0x30406080f090a29071d121009080f030f18010c020d0e01021510051206100302010302091201051e060a061b061d06040b0c0313060906110c01020405 65
    0xb0354488400340c800114000182880821820907024444000840c15101003505903400c501191024281d045041c1c04010100c80a100944151641d041e04c04103c580d9402141c201c0c445140d0344a064408000c00720040381c00c030054280c2c0c142d0300c2e401c2c607140c1103a04820940d1380b00b07103c51224489042f40003060084000660041d0090010a2000750065901c03641c4103e0387c0341180603602c0d14580b14080f0400e01400398002d22100210f107800d003014010480c8550082040b0755010608000703180b44104516020380e81c1c286005038507141a0300c0811010711422049000075400c24040100c0a00c1106000320f0046121070178207641e4076400d003800480c00e0203000e4000040c00c4940c1070b00c442c403c4a21004199442454009110107084041c04000d249140c1103000617084801440144010080b209800051000c0c1c03151660510743c540008000245600030a00f079192982001400303000e61050f18003444084102d551901445411340c000e41c01401a540f0428940c00d0201443c581150600c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356424964 1250 356423714 356423731
    0x9060807030c05031501120612050f160b09010909050903030405100501061403040c0b030403020321070e0108092a011835240f0708160507080c030406080f 68
    0x184d42c90707414603003c120141807009411700441d000d044e03400201c44d1040600519400d19600c0c0f4040c400e10380309003002d510103107100560340160b10030341a03040700043d01822600352070f042595485062005841c0351100750300126032185804104100990084003d5201c0c500c01c0e0141e500c0c40d04001100340c01c882c002c1c0501000505230390700250031418654025600f180c0120001c82d00d0540c1ca4980c2031039070303004440c00c40c01a00089200c4111045d8180e4040c4410b01c45c420410b2607240c941c60041003c1581c40d0001e041005c1e4001203a42c80c0c0d02400503004c84070b40c0c4502600e00307454401c4120700030b803408036980d030018203034508541c09a00340c000c3c0702007aa4402c00300322400c000046d00e5545448208042c514010401d0b0b400d001901d00100122005082c4030380c11161a240d0140402c2c1a034000103202c084059844410041c03c15400030034280c0c0807401c0104513104084a0004a413140548080240100c0001070b60340010240000984216600b50b61400401e50b076030310f100d5040683c00c0d240c076032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356426214 1250 356424964 356424967
    0x14120c090a3c0b03120403111f120504111005030910021303020402070219060801090606021c0f021e0a0c05100e041a041805070b0a08041709030d09060807030c05 71
    0x100e0200d040e001280d601c0002030803120100e00880170b50584da4000c0e441290301c00c006041100c5581004440080740c00c0c0511030710f200d070b83e040c048050003002c4201039020b02e260f61640010b04201c105149a003a00310080d0001d030100c1005400984168819a44603c540c41031200004400d4054021100a00000002d803401ca5186a003808083e41000c0b038100d900541900d840949000c102d4600300c01003046079500c1c146549400421030440d0100e420200454104000c14000048000300300061134410346003000302080c020008904040c0401d4071054100022000389054030400569000a540121030120706959500b00b00b200400c0d0003248040400c0ca103a0100c03a503441c0640c0501c005054034450341c4a0342c0280d01c0013a08940c1b200790140034400012031400240442040280003600307503c04054686031181c80702a00030b40f002000203010048104547c3d402c1001801030b140d4949002d8100c5000e13148000e0090004401b90040200045e0520700003080c42f03200780207250209400303448ac107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356427464 1250 356426214 356426321
    0x9020f0d0204110a0f0909060e1314030d090506070806031e03040509041208150112090804080105040f050c010206012607050316050f0a14120c090a 65
    0x9408001414166407155460f10307049000c540d244010900e142040c0d5602a68115400f4040c180015540140d903110386007420030f00800c0d80c0e0425080e00014000e90544030016a4546901c2076203646007800113901001c05c191100340501d0b04035128140c480c0d000d503540c1d682c83c07000032a0b0284046452680c584d200500f801c040c880390745c044d00b50030240300b0140c1c1e00c3e164072000810314803c0c0c280c030102c4004205402d41c8904503480b902c0e8981001d07441c620701c0001d420440000b4a1004010720050b0501c1e40d07031741400108102801101d005010b86002400315207420706001140c070002d21020b41e958003071248040c40070b40c404100b15068440c80c0104811039180c1210981345448a241c04199a00c40c068000c5100d5604101d070906021a00c16081940f60805051012525101d42c00740d0103802d5034081407003000c0c907020305030500007016211100324500080200307150000c04d02d1242e8000c4800e60030700520070655000082c0b100611980700d204184208100400c8009483e101e5a82d1b01100c00319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356428714 1250 356427464 356427469
    0xf0102030406110709050c0c0d020105100b09040603050703030e190b070b150306042a030503161b08030a0f0c030f0813140c0a08032b1e1a0409020f 65
    0xb02840c00f203400c8031055525510860308841c5d00381ea03401d03031141022802c0400000200140030781135403984000c1c4134904201c4403207150340d1214024100d5040000c50a95955101d99102d540256040070444000c40e6817420050241d16640b0041ca00403d01c124402c00800f401031101c1d002c40781040c031070b54078113100350705c038a0841da20103040300d125640c880c000d00406d56003c002c1c5a008174001d0003011600300f140ca901c010003414020a001703030000c84040410100750040150f42c09003403010700382d4420303a06900c1c0681c440b88440800340035a1302d2100b40131441c22000409410391036466280d044400d4056002681c40c949125002800a9500f1148442c1036124011880e089401004110040300b07041c2e407515085240280000241e0b4054500c5540619002010710018054080a10b140c5141e69400d08180d036103041c0900100d950444c00c4803003a10f140da00289886425100c000f00f134500424801c4040d0aa429803100c0304034019041c250f0501d07041c810140d54a07030080c44403100c1c408481c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356429964 1250 356428714 356428727
    0x9010b060c0604080d0f24050a03020916030b03100204030b0601050f1b0c030109030503041e0305030106140d0f0209040b060f2a0d0c050f0a0308060d0c08070906050f0f0102030406 79
    0x1010b110050300c82c10045450320247c02504049103109804403121000404400d0b824020341e8000c2c0c0c444c030004001000540c032407036040350b0040d4414002c03c008800f010000d50150440340070803900340c410114944040030860b400f0b0410380e0711511811029881d0301d801100c030b50140c03040c01c500d00c0c001000011010b8484030003a070396402922003504c1c62001c14ad80000d0860f000f5100941c04100300004200070015981e281001d00508044201c49513011500c000341180014018401800402803004442403041c0303041d00c80304130a00c64103001ca001c1c1c2011580c0a5003015089901650402000065a282c01c1c42641c1241c07598000072401d07d000c075103040780c0c001c034040d4552541e804411100120703298140312540703404c40c482c1c4501c2ca15100b20b1a00500c0c1030744003c0b0505080d00220785003c0004d07440202c03a42c110204440c444840c41c2c1d541000d400c00c52850744441480d00c01c4441c0000d007505030340c00000403510229698075034114280d060081203642c0d9500b01c0d00580041000703100ca54040c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356431214 1250 356429964 356429977
    0xd091d01061d04020406031401092d0b1c060c03050c250609051e03030f01060c2102060709090b09072102070308061315030b090f011409010b060c060408 67
    0x4039010310412160000c40c0485c5d025412000001e900c680382e0761681e0f00c1c0c1c12a00360050140010401c000c5080182c602c60004102209414014100f128944074116542204044050041400c008e040b03140000351807808411100b01d804509010081c01031502a2085a12604030300c2c80d4240707048116064050115421401d16481020800300f900c04070f040c920135a80d034148200000c0a51410302458030303d0181c4081400103c69004204100d1401171030b214003411500c0c00d04100420348420714242d1100d1100d40e090001c140000751341494400c2e4009051800781d0050b403142c24280740c0301c04031b2409032150a1441e64201c4002c6000c180c90a205208170004920b07903804800720101c60402c01801e9074800003007640006c1c0394a00340419031410401e846400348003541c0c10070084081910a61410806100c0039003007e45100010300c640c0000e2280407880c04c0040020019003c58000c0c5048195040d07910344142d610340301402c1c1d11820044d044840c5915240003d200310b903150b5980844990190 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356432464 1250 356431214 356431247
    0x906090703180c1d1009050c04051306050a080c06040312020a0c0806061302070f0624081b09010e0a090807020901060e190b1204060b120d091d0106 65
    0x2242c0c00303030301e005404481480c910b1050b49a460038901d06215890404c15280083e001005900e050245925a00e96403e0844041480100d212341d24842c00c000c0e81d029036448150420742c0940003050044d2681c1c810026580d04030f40500e03000da1502542e580c2c0e161001603694111001304414000320391901c10040022002d48111828603034150b0310048134214960018506501610901c500307443c2941c1060202210b101c41181002034540708c0c100508000304010b00026542c00301d036050ba01994032188a06c12412045020a0346d481c0e4480d80c4c1c94101515401c000b0516440701c034214504400c0450403a4011601869543c50f0200080d0081800d1002111000010084000144c8031f0003400d074020f00705520b0b4400c941c0f4002003844400445441480666840d52200340001e0301f07040e0070303100801c00e5500307040002d9860346002c40003403506102c00d580c000c1ca0810f0304184a880019201c10b011030390760311444241d80e43e079624400300300c0c0c1855840c00f00d00f80f04010b10006100303050b000d2140b10320703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356433714 1250 356432464 356432471
    0x20c12091c0305030727140f190501081e0412050c01090c08010507171609030506010e06011b030e0f030a17180102030910030b03070911070201120504020906090703 72
    0x240c0526022501e0701a4003200890380c08001c110700e607904004558080d400301080785001290460900b415850203020b190800401c0c0180c5425a0302d0b40d078980e190011002d44088070300d03c250440300751822141d100746030000d18003400203000c08100c0340c0c0d042c2001184072100c01e6561229030746c16108180f21715130a01048030520a03020312150034080c403003072640a0741d0f40c0c8a00074140481c15007514402055103043c058510340342400c408040c000941c0c0034040c8028298244030700501180c0551441d132001d0080e200c1c4000201c2c020582d0300307119010b4030742600d031201c2140040c0d20202e03003500420310241c007080030344140060700d040c00b401400d0211801130603102091443d540d180d030f40902e1031001700000d100204c0c012a40c0040c030f5405a5956a09000031400c1c4840c2e100050100c940a2178980100354a40c40440300c50b450070080e01004d80f000c07900074004481000c0c25002a500132200c103a0000c0e2800320b030301d50054014421b880c0034540140244815680b00c40c103101c0e065601810740b8007015034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356434964 1250 356433714 356433739
    0x91505060105071e03030507020309030601091509060801020315010c2105070204021810030e06150a05060c0312010b0a020a110307080a03080f0c0a05031306020d02040603051603020c1209 82
    0xc104071072050400b014425200c01138203007002030480784001c3c01d100c02c0d0b6104014940c19590001540c0341102c081000106016000480c19404000107500c071111007420520003045c00301d01900a036124010884640c194a142d403801101c1c04240042c000c1c10a964598245081049582c0c0c0d08521181c1c600b40315103084020703070200342242c2c4010b20034078040d80c0741c0c0c000c5040e0745407108c00800383e055149018801080c449240030388a0101400181961000c4610246a91501e03481b0390000c03c40105555101c007005c02035180c481e805410810540e00130000041803011045080c0d0b00105403607030040582544581d114601d00310110685585446842d40024150b10100642c00c00c580c42507a510401c0d0808203181144040d014010560341e040a02c001c0790056400340c00e0365070000d03000054100b03084860410800034800d5100304881c1c81c1c000200030403410f0305501704a004803406800407407480d1400c0d00c00c23400c90151102842e80364111914507034803581500042d10100400802e1b5040604 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356436214 1250 356434964 356434973
    0xd110301090e07060f0e09040f0206040b1e0f0306060d0e03030108012408120d0921120e19020a05040e0a0c1d0601050a1b1103010c0309150506010507 66
    0x810981c41103106680b9a10102d04a0034188075500040032030341000880c07a64401405025801d4a0506600074001c040000b01031021000182d0711040e0040c140a5466071140140c0c0f00e5907110a28a04031034600740e03a207443d61140f80084607103c01244002c5811601c2d18820085560f03c603680b44002c2984482d5040d281941c05d10045000703110000000842c00707480c1d601e207080c4504003002e400030102c0e80c1d18100321044001c500c201e0700760b0030031010559901c0030000c03550040441d0040944507414220303110001103107880140241000c144c0700e08900c80d0f0030580100546082030342c0301515800c500d0484050a8402940802c61403000380219080f076200c0000c60700301c80303000e030154815a00082d100d030107120725608030401134a800a05481100b00501c00d140c803140b409040181004000600448482d2003060b88000070340f20311031505900d4809040591024140c500014803d51802c3c03c0d100d1058001e101b03c0c03051725440345400d01c80d521041000303001410001c0000341444400c00c0f003a000107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356437464 1250 356436214 356436217
    0x8090c030709060518151513090c0e0306070e060a110105090a060509060f0103020d0f140601060801081609090201091d1e0f0613110703021e03070201050f0d11 70
    0x301035000c030009202d45020200620900d40c4929031104407050821b1091a04444000309103c1c0c1058900b407226406000c03120301e07180301e80700b00080c0c0024181408501c030040c41c2c10106e45060710b51740e010300307907110300e010192101016125100840c0d85441d40042c1d0b81044009808903549600b00344060032a4641e8550a6a40c00c9502c0101e03a003145d01d081040043d80d2041c1e40d0010001ca0061481d480d040610110b18903040c080a417081d000402048108080c40c40002003451b0702c100c4903194a8501c2c1c0c0030540c0e9413401e0145030049075160001145100001a115400450009201060750718040450000b44803a080a904000c00901c0100c2d40107003c0040d501c0c003001c685441005442d040d03000310a14544a10030650481c0c001045c407080c0703054441a182c11403000c503061038051a402228000520349080c0701c02000703101046407800d040c1c001c580c00205e020303088235580012005130982900d80c8070381c41009011500902c0684a0034003d40b015141070300680c0c5001030180444169200c05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356438714 1250 356437464 356437469
    0xe030f0a110706090501050d0b0402040f0e0601030c020c0a120c0b1c06090603020f09190c1d030705030601030b0a0609090c0936020105090d11030f0604050d08090c0307 74
    0x110307005001905101c901003000700020401881d00307030111401d00000801a114024080d2038658462034540001c0d40c4640c100c6000708034190754048216078854010031400411650705011030700d03000314661100e0011490134800c00000702002405401c180300c0c80381c2c584a407501903c0001c0003820104201141000502d1501c014000e50105440198640070568500d81c020704401070801038104016100c1160441503024103c803c9241d580d41c0c851814030a18002004114450800402018803500803124800b00c243c3c403110005201d0040d401c1c5581d42da030314410950580e00040c010000710f001d00c5c002a070422120f44003c035409688000150a0b0345024205135026090300b10f007005000c0a502ca400108044506441507480700792000b0800150001420184c07014030780b5281c0e045a10440496805090003800c2d040b4002003402c002c0c94560000840b01d01a1080300c00b502c0c1861800500769200301d6018005103504155900c04031020345000d4074000c4588200342030a1401d64040c00010003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356439964 1250 356438714 356438717
    0x70605010806060a0815190e06010e060a080705030d030c0c050f07150318030f0e040207080309010509070b190908030c01050f1315020a0e0d050706020d0e090601030e030f0a 76
    0x901d81840c0701003001e135620384c1c0d0050103180c0c009590403101041103040140d20200000c0311441c0220350606040242c440603c001c005801010004212a030443d110039004d02400e885c01540c150f2a07801c002e07a5100207000e00343e40b40d0700c02043c100c2c416200ba00102041c1240d0320b0030115106042c0d982ca0725002c0c2c501c0e50100300e600400c0c3c06128414261030340311850201403405010804201648050342800d1200203070030880c41490201100f80104801c1d8455003001c1c2046680d841b0390b0a21810540080e50001c80550074030000c54508000010503505540d010904140b500c0d00f1041d80b840c0078401045c62000b441243c40b0b000031080410300242c030680d8400b40000c2001d2400401e00d0441e02001400c170560a034441c6583c4000c10313035035000c000f968090040010390b107507601ca2050b40c1e04050345814541c0520016000c004001003c14802c04589407a02150349a001d444015240c000221009a41026442c00090040e41c86a0054a000c504030001d59140644440f01d902150307210840000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356441214 1250 356439964 356439973
    0x603020102010b09130b0a0e1b0a0f06020d08100e0903030403031b17180d050a0905030114040b04030306170c1503010b1e0c07140117010f090905030706050108 70
    0x425560203014441c0320741011603201d19903251540048100040c0c1110191592080c440000c4240c03190fa400800c001c480741040f5258103400401d070003030046c0c1001c051400b619000c440000c07010300d40b00444081d9220768016284c1020f920f502142d1115008020303181d06101c1c1c85001805103100c11300240902440400342d50b40b8901818050203607002c010013176581c0744800341203820305a84901e02c0c102d043d02462880b6181c0c1c54440100c0c0174003000540d820700a008284103406d1442e000002401c24012139213482c0f40345541d4000700b60032501d03401c80724070300045e00c01c1c009400680b50800081d401442410002545030b19012002521581002040d01503030225a05407014940003070408440c05c00c1d82c42040ca0b540c14001c801c081c2e40160524401a99001c4084800c590034040941d0803542d07460048800e06661600c0303521a01020740180c03030218003038a1810200003111121705058a644c48800301070b503841d0094100042c0707840c0c2000e603070768081444500005481d5014060003000c1c0c2e2030040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356442464 1250 356441214 356441219
    0x60d0209011d0a051002240402030706030b010206150409061e0b0f0f1908030c1606020c100e030120030a110c06010303083d08010606020307060b01170a06 68
    0x15044240b54400101c0c0755040c100315124036601c294200c400e543d002e540401509400d000140d160082008101c41c04485101c446010136480400f00c9101e14000c40407180304603582c410540480d9060720001d0b005030000b0000030070765200d807803651003a4a0060b00010700307015141c4030341c03080740d001481074082211218040d05182c1401d000300481108100e4500c0c0305080120002820020102d800500595011155240d41684041c080c801400008c1c00da0380e03101b4880700036a07143d144060107420509078080001c60361920004141180e907401410002c80100607030707c20340e211130807908002d51540d2a141e90640c1c141c104600601088400d00b01280ca0307042186032401510980200d01d51010000e0041d80805d40001400c1c50450790542000e40301c2c4d4903890b244bc5101201e50004203901e2407041c0c02c0440c009821481040440c9900c2001d509264480414501380d8103548101d800581c82800584082603c40d81700300810403050401a184e400004070380002401c080300c200403069602c4908 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356443714 1250 356442464 356442467
    0x8070506090106050f03010e03030f0402041b0309051c02031209031b01150510090b07031205040812070801060203180a08300403020904030c05010f36030516060605060d020901 77
    0x141e0117031000c030001d020017020102c006540b400010251410381d4051303c040341c25034a0300d40c81b04500f18000e0311190401c008030240980a03140390a0111400e12900000c001c000780920010444462198080e5103014a4541041100d035000f40c00c0192500003001040ba03100400001e0728602884000045128030300c3c414048814101c2e9400039024111003401e00580350751004021054501c3c051401d81c44041900b0b080344c140c0d04220961017602c1c509011b00050100120181982039010340761941150f07103100041710204030a2042901592060000c2c9051000000340c200310001c01825658030075546990aa140042c0780031070320071500908034841d01518001507a18095035165400780c0ca440c1c40c65000c120804001072028042041c1c140c80c90303080ac0029040050760040c5500244110b80510226450307000c520881c420000c0c80712b604070400300245240106805405442d45414142c400c10010b00e40400c400c01105c0e500e0395400c01180d542c0e102e101038012010f0f034a10040c2c440b05007a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356444964 1250 356443714 356443729
    0xf0503060a020c03160618061b030b100e01023301090c0c03050d020909010f050109081b04110f130608090109020f1c060212060103141e040807050609010605 69
    0x1010750001c1c010030084209030f2002045500300c550003140d1032282c1c0c0e0b040c144070380100954000322000c00316012941042c40032030340000f2541d0140c03504030b085000385a01c0580469034202003c541020407201c05851250284268400c1540180141c42a084c0d4148a004442050140c0c045500180091090b11918130141c0360b40074240c02c200030080000e60303041c040d1104a408400400300040043e0b1501d000d0000c0d01500c0d4941c1001c2c20071707081c2e941c4400030b0311400b02d254000c0900040095030f0015030864002464080b04e4035026820602c8407000e000d0101801a0b68404074000404101504444918000400150880c000c1280e03d140c1070441c01012000c0180041400e0b0781008004000f5a13035040303441403c0b100032941c1582d008a4160500410344100c0c4016004900c0820f42d54252030700c54896520426091707804002041542d4000101d00d182501e060324800c0100411580300305198404c150010b00410040341007c0080c0c2d60649880b0044031024080d035140d241c200101d040900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356446214 1250 356444964 356444971
    0x31321020c0d03050d0c030204170a0201030e01090b0a0c1b0309080106050f031e1002042304020c060a0209030c0913050601090e0309040b0a080a0b01060e060906120a0b0a0f050306 79
    0x2c545200001ca2900c0c01403503070081e0301c5003c400641d610b1282403154001da0456000b001c0e000300c40c03911030020f4003040340c03030b4480800180d0103e401c042104d02005c0307040c8181414558820701c40761154580746003640c0285420202d0700b0921003004800030780300e007070504070741c04c03c0d48070b0fa0b201400c090800b5025400c4d211a03030320660080d60060a203c01c50351b408a05116003500000d017404441240c680040c2c0b038001c3c1511691002c500c00140456124100c041c48440300704942c10712028048044248812440707180c000c41c4c040d0708260301041850146070003c00c5080d500a045070750a4401c0360000e40c402d0000e4500c041c000010301c180204000d0140720460042c541094108010600d614200e5268403a03580414401e507580c0f080b510040c0d9980c00f84002a121110440d1f00c81551071a0081003144280500b01c0440c0309174400c1541031900c2e108a0728021800f0f405d85080583d4142a0402c0020103003d0310120398a501101030f494651400c000c0003440c903080350203103140c50030003454103000014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356447464 1250 356446214 356446219
    0x1104021e0301090e07030f12091e0815011202090405100f09020f0f01020c010e060d140603100e0d0302090d05010c020321010807060e011e05040906060509010c020105031321020c 78
    0x54006c0001c03491109860341c007141c020180c4207050300e2115049980422071b42001302002d0002e00035107031b01c0c0c40c070110000c1580e20010440f080c50554000704c600121003441528038030206104840c0050516144241c0c010f4803e104a4118215800c07502c2e0942e2651a0341c0c1200560f9542130005510304880742c0c1040c03410a494446901407500c000039210707405a80c505050002c0c0718003130305d032a483e88001c0341c4c002488010100718031100391074070030340000054407128401c0c85a804580410a90f070b11650300b030702e0300d024010020041103201c10b401a4010200d0030364400000400d0001007002070080300c4003510142d000e9556054180005001300d44500c84c440c81c440301d204010f2000d03d1002a01006540e414240003408803102401240c9601041d41005840d0315440d2100c1c0d41c3d9501701c8040c20561300706c02400d101030303512030b54200c1d4039008003808140080d40144141c2c0155000b440103642019550008c0244485983c0725400241c4560000001c0e80055184e40065294144903180e104c0008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356448714 1250 356447464 356447473
    0xb01030501061823130f0e1504060b0d12080103121103090f1f0e0f120c090403030f0911120a03090e0702010b1e010201060906050d1104021e0301090e 66
    0x2504103407040b1901e18007400c03072103403005244641d00c840d0507841324406890061000540142443c0f02402402c1060300c0700e103085042c043c03800c1030688041f070b0b5022440f81140500344107940b29194400a00010220542c100403080e0000021070741c5170480c3c145064158550900f294510b15100c420320a42c0d040000070006500c030080c001c940007008031640114100d8035040300e4800e80c0300260f10b50418044110300c100010050700041034004c290400b51000848030b1000c080e007200705001038005802e0b40e5032402d421a6400b1803880c07070010b0080750080d00a240c001041004091a902201d00c0340c041640c000f0964800c50710180313859181c2056401558014025111440c1e402409800090241d0004021124001140c0c18800d5200200c80c0710300401e42424080340035588040b0500d14000c5030f0040d42003540c0420b00ca401800794904070b450260440384120900d44803910b0049460203141d41c0240c081115892004211101c0c0700900b100d4032072141e0365450700d5005402c551840b6030031030306600b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356449964 1250 356448714 356448737
    0x8030301050d1407090e0f06060108040b040b070903150e0c19060c030e10090504050618150109080f07170a03080103030302070f0b070201230609011e08060a0b0103050106 75
    0xda01c04141ca2696000545040c50071407200c01509090071360f000044038600d00360500141d0f2200243c4280c02030b08a20035034000d13440d8480110b030310f42c0c021100507041c2c0ea00c441c0801c000400d805004d036804845031903c5240c280c2c990341c401c1c00036441c0c0300d0300d8062252214130840702d414003840000d10542c002c8a40c0d181c0000030502000500c0020702c00c40c2c1c1404500741240e81414021001c41030300c4c0d80024032070481032040180281c903140c0c290103950300451401001a00c2404c1915402d001040040d0b5411465078071208801600c0140503402410810098000a500c4c0410000c5050b815a6440540141814150f04000483c1e000c0080d191795442100d5040103c1e80110b2078a0540f0380501e070240c0c2e00d2245061070505560a044001c00c2c0b86206c0c0d081149032981035208a42c0c401c2c9400c08035604105c000c20b40580801c3c01e40b4603030341c400c0c4407000401c8003d1452106480e0140e400d0035a126a655a0f101e003418104100d42e51130101c1d88811348030a0669241c4142070150456040c28840e481 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356451214 1250 356449964 356449969
    0x702090c1806120f07140d0203160813060b01020312041406060102060412050702220504030305180705090702190b090d0927061806080106090204080a080d061a03100803030105 77
    0x6001130401c000114074030000c200c0700791040403034910611002000d281c0d41e0403007400403402548211418040c03003418844141311340f845540c546005841e4403400e08049000f40d16240c0003413440b028860f06500c02007201100710b00140c1c1d8818459070255141080c52031240f0810f0703040100081520741150014003c200002c1c1035890170929134206440c007039403184807600c049040c402c0e205586103107400c1218000c0f12103c2c0e0341e0f00100c2c880c0d44284d509104544514580c082401c5101c0d03840103694101800c240480d007403030302d01c0c9070303002e1201d1044880d01d00001c00b40034080c0c000e01c002540d000502c00100015294108811780d0f8282813450403641c183d24000c02c4000c0c0704194010704000300da40d800e91021035221600241d000d0070000c61040c000318071000c0c08400038601c51003040a03550a040303000550740d88610a0702d04658981d80070340040541552250f09540c0085500c1c001260754110216680d0071444608407031a442c440110341e80c3c2440310300c60140100d5640f0860041d07104000500194 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356452464 1250 356451214 356451247
    0x1f3b0906091302031e0105090d020f030406140403060507090305060903190f110607030603151413050f0703080306030c09040804060f0525200906150702090c1806 71
    0x541072829400b140c81003440040e04010340079504040300b03414400c00040160065000a000f0081c1d03504440092009040580e240c00a1403629002a0400e01c010002107005015400711684803050043c41c0c03d032280d136000200c0f0001c0d1101000944800d0080c8100310080161642061444c0c0086040031408111240401c0034000580200b15448410768a96030144090b03065003580002070740d0584c80d000030014020300c0305100c11748003200c40f8003507901c88030700c28843e1a00c2181c0030200a0340550f03a4480c1a0746404c0c0340c0c4802c5855100e000b9613249103250a01c80700001e03501c10078005a803401e01800b0180390082025002d0722070f0135042d080c0000a02e19a0454007180c2c100c0c100805861501c4205540d2402403650108020700c554001c1d40b1b040c01c1802c080c0f40c590b440b9810440010104d850307110071400700644010b8100f02d00300e0100d2007624000140c00315041c05800c01c0c40c0f524500d80c0c0400c080c400f0903203e041000e103000c54800007040384249078150400d0700b507900c0360a204480c801d54030340e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356453714 1250 356452464 356452471
    0x10e06130213022b0b0a0b03091b03070e0106030507030509010b01020714061b060a11030910020714010c0e1e061204140a1b06030b1f3b090609 63
    0x401c1d40021074102c03ca084802c200300588210030602d80003241c4520b194050b00070703044498400c490101c800b181050381c080681e4009d00d030b9400281120a8800c034419200d210140d200d540c0b42c40381c0300d00000c20440c10310905003c0c10070740d5800300d6681000040034050f102c0250000c0c101c0d0341020f480c0b14040e40e00040040448003c8009001c1d8a1040c0b000701d581c0303104468000d10a8070860301c40b41c03c0c0d800006425400b508030302400b0007425207034081c6415540010703200840650030110090300c0d4940190003034691580a000d40c8001741c41141c0309542128200a42c0c030b40441e40440d00061149406c141310b06c00f0704983e6403054900c44684001480b507200d42000c610b20f20f40344101140038400d110b052202d211201c0022545224420b0800c180e20440d00d5900c0710303180180c600041504c42c8240507030988940f01030070b07031030300c003100e655414580443d0022a042080103004200700c21002c0f400c41c1c031040c0140d560b20110755101700350034081d10f95145c8088034019a12801805000c0d114446150350 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356454964 1250 356453714 356453749
    0x210030b0f0406081b030a120e0103230a0605010801060909050c040305010903020a1209050a03021e041503020415050d0222020f0a080f10150c050d02010e061302 71
    0x3240030080c000610040d5440100c0c5400c20720742400424a0980007603070b000300b41d800c0003034000b029505074101940d03648018001007a01808030115000103020ba15007070085401410301043d50f11144180514040300400e48801140d00d00d4240040070440307100d650044c0100b884d18555560400f030f40500380100728403440e03031104d659100141c1c0440ca618282c1d4003455100f002401200030b2402e00070740e0f409101006850140c0d9156015a1507400362141c1d1084a80c0030300000900d42c9550200900c031403c00c1f50f0307411285060074108405030703100d108004190074410714038800d2500b103005000803540c1581e4940281c140100c014030241d034074802410070069045a0841618100e02415114010042154203e0710b00104481d0801c0800001500020b4510740d1540c01030b58400c240d880c690030064807244200911038005224201d15019942c549079000c1c100941400d180355622450407a41d540a240140d540b17000320001c005041c070045411045c03180e1001c614594540006030035082d9101c8200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356456214 1250 356454964 356454971
    0x50a0509040906020d150b070209070c020607060e060115110307060c0512010f0515270d1e0605060108040809061318060503060105060f22050904140c0607021003 71
    0x185107503940d4210700940d80c2c0c000000c1d900c0d40312004203800030b0208840212249503080001280305000941030316003d94000306640c0c1d164484800075554405142c00580e000305040282d00c012420900403041811801402032036250325106240d8030031010608a6420890034110240b44064000280c449082d005000050542c0304c1c0c0c02c041d20f10b8031600307844161240c041000041c4a55078409008112003080d101c040843e818a80401c2c0c0f5032040380380d00d0003c00d1074540c1162803864559006810326501a101c10700108080d1211d10516107103128840112074a200ba400411240b801500d420143c02c2c20900018242696102664002d80e0501801102c0105a4100421098881f1001098030402c0c1000004048010034050090342c01114028480c044c0001154103041040b038a0740110038103100c0c1000d02e08072000c0040c1d0301e4030102c107149820040d8041015134078001280c0c0654800d44148034100000b0302d915040c41c18810544bc4100000c0c00040056200c01c0020240005a0f02e4000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356457464 1250 356456214 356456227
    0x20151f050307030b0603030c0d05030912070b040f05160e0a0c080603030301121110020a03021b0d0b04020d1b030c06090b0409020c1c0c05060c0315010807050706090f150903050a05 79
    0x80e286001c8c10160b411248120a030744096150080000c0d4058041c200640b48582c0680001444510901030000c108400d41000100403440943c110366040c0d10480580f1048074694503036009040d0560005074a21460320b041c400c8603a02403051954008150404803058542140002c3d03d074001441481000d03020b01c0c040b50200028842c0c10070503044003c001c00c107107200e9400001c0d9100d6016208034054800c1501c559004400007810001c072001c000e18071141e0721200d5031140624107002c1c004a030019081d003440c4002400d10a480e0702801420800c211a143c80d60810441341c0b581944600140140d8000074080307030410600f16020b45d609450050f0b170b5450301c2c0c1100c03442e100c01400c040240018062032280c0d260341c00600340340303c2c2e07024108458050310703a05502d22280c80280c869070340058009070b80d5800ca50054000700d17032101c00d0781032480c00d0001c01c2d01e032002a51011a81103916034a98030200c42044110740e003e8000b4441181c082000040030303903010b0958842c80b24803109100005c901d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356458714 1250 356457464 356457469
    0x80705100306051804031709060a0e0a0f06230f06040b010c020d030519081909020d0c1d09031303021203040306110c0106050607030206010620151f050307030b06 71
    0x20742c010100585041e000400c2c0c2c0202421005058500b00d0000f04507000e4189494260503038a8003035401280500259161103403914020720010018280c140a50034044012030800400c01d03030150f00038680414040014011801c0340c0b5030404a0b0004c0074206014050350700d08405900d40d1013001a00c00082401600d001600ea074244008000e61080102120b2030030964494040c000002d0680c184401d2160703220426209284100c8404107201041880c1a42c1c0d03241c2d03a0840096140046d00002021a03035807200202d90302d540c2c0007041c1c46001004c20000c01120300392000c1e40004081d02850034041400f007189008041488040c1c0300301d9a4103ca0010100709000702c13802158082e00804c6541c1ca8502c026000da009421400c0e019480e240000456092800884400560540c09003010341c0c2408070036541140d0b40300140751200c603a1008140388103c10899400081d02d00030f9000b0841c90a0307071000034000400da00c1c104180b45055020400313074800240031003d076a80300d40b149036682c0d9040003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356459964 1250 356458714 356458721
    0x60b060906070501090b06010e03031e040f0602030c16140d02060409150801050609040213020d15030807061d0a17070506070804050d230901020106030c090b190807051003 75
    0x500c0c40d0300200c001800001c01c203055000c248003621618040791640c0e2940019613902403c203040315010b03002000b56040083c5060108003076a54500c2009050a4540b4100c01d03406040c0e0300104050781c000101030709110b404202020220824181c0303403203818100a86100c4040ca90a8602e0040056444074001c56440a00f5240070b402c2192040168001300090b0230408911440b8548107035103001e0128042e801e04a801d58841c85d0003402c42c51040040a0002c8029800101c44c614815078600110200800d02da03032520045020722160364841302c1a08040302181c035050280603041c010180c0049890300b0200e0f40580c40c90300441400c140603140b803201200c500c108240100705001d007104000071150803422580c012400340086900c0d64503242c1d03040e40c460303848a9501c00c40007400e541c00480d07a21110018034a40d10184008601c0d035941340d1303d60600c80e1054101010441d00c401d54a2503d0422900702e0056a9118040302440707460100c4160303c5030040c0c01940c0c040c0210841580d4104d000380c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 356461214 1250 356459964 356459977
    0x110928090f0204172b032c0d080105030c0d03020a0f0c24090e0402010c02040507030e010b2416080a030603140c031203191524020307060b06 62
    0x9a09114400d18181c00c840254040d000d07801d0010f0200c4518038040400141c1e5038601070f07285901c911100d460b168842a0150110804400c064840040d243d2525800c02c1c040c2848201411130214000e03000005401d040d8000f004c08100101200100907a41e0005041441c0c218282c40c40e611201c2c1c0c0e810f04a0600711641c0002d444801c2d903032461010460894030480807600012406103000b0241c845003080c0b1b1003000c010000003900200300344469019042501e41080c0f0504000200720207950219058030310450781500800c0c3d59103540d011010080c00f501c1c00300c82089422808030660034000c40c40b02c0c4402c040480308a60082880070302006400001007030a5040840d8a48500e50b0030381c01030241c02c81d03020844151900000c40c85107107500082c070301c003280801000707051003402402c03420005c0d800003400c2e504080305101d010f0000c907001e8031039104060304280e00004840d05000700c0d00b50008806107050300020300d00f0700e202c1c026503010096900032070780020082040141d2a00190b4103003c0d03030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 356462464 1250 356461214 356461229
    0x10090605131a0a090807121b0e04030201050604050105120a060b03160b1e030c2b0c09080705030d020d08190f020d050a0b0a03170403120909110928 65
    0x1c107482d440c2a101d00001d8072000005070344201d10b090f11481540e032100c655210340c3d0700c550b240c01c0700c04000500c0c804006000041e040e0b405100c0d00c0c1e0700c5480c050398186c240c40550250b55203200340500d03420240240c074050207064410961000d415a1043c2e0780d880c041c04040d003003907a1005030100c5503034188076030b50b115a0540401c0b02d42545a09a44075690f1201002c40344902d0f081350320025010342282038a1203180008405400c0a4103107415092008800d04040508548081c203400220590301c20058000a00d80d2000c0c62241002c458600d4501107411040c801d901c0701549040c41030f4006401d241d14400752411016507103503e418507440070f041107900c01a5900708000e104904005a02400d100170315075000740190740f00d40018400710390705132050680041c0c03541c400303101180711515040c20f99082c1003107561030542e49840760200c60420340804000140003000070098501e0750300994082c02c529141c11458107043c140080c5e076800c5180182d07240a48990814041c07004a140d00f44002c0049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 356463714 1250 356462464 356462489
    0x81b07140708030406090504050103080d0515310b030309190306060603050a0b010f020309010e0a030609060e160f0303141b07150201021303030302031b0703021501051009060513 78
    0x110501c00f6160f822034081d000000f44039090001c2d040c034041c05030394126600501d0843c600504801214054500100648071000c0a4000c414041d01d446581c4400903000d0841589114400407140300c024000740d501041817403d02a81c50002d80d40030048590101c2e044801580d40c0302c0004809035005034641c00546250328107440051425003613004103200d01034070b000c01c1000c24540001541c040703164010b6040141c0c001c0c03140d80e41300d5004600022048a004040b802041c1e5240c2e10300c4140c410400c002c803810b6840d90783c41c00c102041004844591103021401003069410304003ca00c0da0583d0f8440602000b003842034038046201107504548441550071407104640303400b0820700e0380c1c842c6030340700e903020301e1400004030480c4a02c180f09039000e8040c0040054030315440c0d600c1c218003940014000082141060200304860705c1c000004241c928400c0d000342582043c9a8042c0504610503840345000312941d6250b11005a805031110090b0b40550401c07985840390004000f40507442d0f40c00032030040e4078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 356464964 1250 356463714 356463719
    0x80d0203130b0c0a030e1504060e01060b0d0902010e150f09040902041805060a060e0109020c010212010303210c050a0c0606051c1205131202010c061812081b071407 72
    0x1070a0006004c02c4409880600034400e4101100d60754091151005107041000c1000c10009111500002070080f01400007103400c1344c44c1c002505040c1d100c011010b200c103550313895072405c558000b0207512034030000300c50100840c00c00031011859445803400511111200240070103196a56502005403140c0150040000710450002e806035004480c90030303155840b6480004450008900078441030381c00b0540458600d92904600c0d02c0a90004402041c2c0755400744500d024000c06030450500a500aa0381d51511140d807824030349030400d00007000030b699810303c40740c10100b40d00101242c0d0702c0c8035189003440e01900c082c28198018010381d0801c44c0c2c04510081080041d41c0b20150f49403115004142c81180380317441050070b4a19200e4039402820a40c2220800c1041d07480c01c0ea00c55849500605095402510704d503103003030031121070681d0008802c0000710403005110320040c00ba8014071850606035580c0c10001e1040003490840c1c103104800d0500064648100f00f560a10700c507480380b4110849400c0d030b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 356466214 1250 356464964 356464981
    0x2070609142b021e0a05240702030a090b1803101a10090501050f07050d0503150a032307170c030f01110a030c020c09040c05010f0507080d0203130b 65
    0x12900340c04901c120a0701c40811100212048024145203603400521031381c10f0100c44003c0300c180007850349440780103240120340807a80600040308108046905d01c520a00c55440380c40301810050100000c5601c240281111a5040081181a01c0d21844125100c00d0010701414210310400b50942e094002c151103010983c10b0780d046861a440f000c1c1111529001c04002e01c0816412080800c0c00039081e204104070a50140001700040d46030510624540700c940d80340c071450300340300144081c00200c0020410144100010303240b07400c007204030f90840c172203851621030b169014103009548402c054401070305100590f0402044000b0102e58030610030000681c03844944504224440c14061b001300c0c012150700e01010300c109200252002c02c03441c1441c5d16040228002d09400e0000340a62144042e08100c5036901180b851041c0e2003100d00a0040c0e04040004064080d02840001400020711100001a008006903906032403400801038480d9114810300c5804200214041c01c401c491405000184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 356467464 1250 356466214 356466223
    0x807380901260f04170a0206040308010909170a02010b0405090312061207140409020306090601090e0304060c0f0515101d0112020d11121b09010b040303030207060914 73
    0x7601d82c0881c0d0402d01940d128a0020312a8155080c02c0c1100000e5165401001541e000360080d00b40d40c44100c0c100c10030340710740d60018484001680c000700410041507071000d111400b400358214180400e60f01999040704c1d04020a4540c400124041043c84401d803013540000380107240200244120308200d070200c4d80303c3d40560009804044c0380e0001030f40e98100321040009840400008290880c078050801c5a0a0a0300d104a40e01c152140411009641c2c100004d078018100c4401600040d49003007582c0048403040a6040380681041c40100070302c07600081001801c0c1e4003c1001e903950a03191410740c1c101001c1407480b000b000b07020f80501c0013030b01c07950003840d00344c5e405c2c250054800c104075940030314502c1c002d11407903070746201c81502080181001200054894401c481c403074011020100020060300b440d0112190650202c800010300700c0c40810b0710701ca0742d0410394284045506081d448407561042d80000f800740740c0c000520004000f1503501c00c240a82d0441494005005048200e9464 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 356468714 1250 356467464 356467477
    0x30c040f050916030503040605070204020403120302030702250e060a0305072615010308070501060503030a050c010b120303040321020307051b1621050a030309020909030301080738 79
    0xe4031803203240f401208205801001501c0d0400000c50400d07142010456240c1d0145074102d030000d0b000c0c0302c0080020842c179a2203064480320703100540c0300c0c40c21910003413a20159840721800700c80410544100710395030707004010540c1c1e03515a80044c2552030402154140300d0a500c0100076205e00c4400040c0000c0b03a603c080e0101c0004501c0c60844040d00450968495585540d03212254500004000042c80c100040c2140d03031207140049052543c52000a0954003da5690b00108600141c03001103001c00303120f14040b03184229030704c90f0042100b405903179490000610090500042107079880c581ea45903007501d0310380902c50000f03540d2403400040040480d0071150713086460608802151080c0740f00071911410055111100246c01844c02c0b403045405028041e0b03402d0f01d10304a01c500710100c3d00c1803200074141e50003620702066a105174410f129822000a18035900c0d81c0003030006000070040070035420200c0e4040c41d8884500000340c082c0c03150710949086600311201c1084c0c0780500c0b0440e0000a44003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 356469964 1250 356468714 356468731
    0x819090203010e1603020a06080f1306091208070e0919180b15011103030636010314070518070c030e12151b0d0c09030807051c0302070302030a0e030c040f05 69
    0x10300e140c0e9201d05450143c0e00303074ad544030b2000c20500007075514403010044003074903400341101141209803030301c801c28414a00102c0400080f00300081003c4190018010440b561081d03c05910038906801d94510705c404045003a04090f031104241d03c010b00c05036450100c00ccd03400c035464080074245034004400002c4242c0c42c0c0d0740440c01017030340b035035204402106591040300041c002001d03800b4011540600416500d21f43d403214400c401c840c0c14640032400c8801d000e184100b07048500c440c16215090b1412030181c2c4021b1240a038200c1d01d0344000711490340c071034120450f4201040f0140491a056175000400d81d00c9642081c070568041904c04000201c018221810f5003050115445106242c51402c58421180e142d0050030040e9041c0c01c41c2036808100700c0c50040c5040042c1c0d546a030b5407840c5681c040305003511b01d80d000215900101246001e40c1002030160f040c00c5290040c01d5801940b6400340318100801d1040c0040d200303145d500d0a200b02c2844620003041006146084840c00d070050009490910 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356471214 1250 356469964 356469979
    0x6071b05100e01080c0403050c150d0f09020a09050603030a03021602060a0215070206060d0803041103070b070c0501020a1e020111030a02071410051b0c030a060212070819090203010e160302 83
    0x1450416024106e4069075000700180242c0e004580510001d0600010345105c0c090080006c001e005020b8800c05000b90000c00000c60400018010003441c00d50036040421807034945401d110480d517000040b20b03100002c9040150715a41550301601080b4041ca80c0a9000200051700d80462940400e1034159200c18504207501e58848400481e078610b0101c8505030000703035008100c408030714032002840c2d00520598002c000440075401203814890389a200a081d80300105170001084805681000541001e2000740a6035205840d96580c100880d244c0c0c59410384403420880135a44280200c00c01c3c1030101c4110ba40d25140c038038000390307034010750310034507007050b810340d07540111860080030091842c4a03a90b201400c10702c90354250700c0c4228590700070056622851420443d1074405029002103680140001a110708456880704020b105c0100720400300b1030070b02d003040303081c0301380544104040c4d4000d0000145180d051010030b00511401010070082d1040c2c4003415030a1700410a07110a892007603036400f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 356472464 1250 356471214 356471221
    0x9032118070b0406051b0f1f020f09040f02070b191104050f0103051f0807030b06010309020d0308090c0604090603020406120b0f0402060d020c0706030e0c06071b05100e0108 76
    0x90744034000c60040c00c00d200d10400040041900c5200030b420358241804244500886402169290010070f400011007500300002107440383d48003401030614620303020002d61a00e840b01d40b8001c075034490a48820300c20b650b40c2c054511142e003103034141c440665012000d501142406080f01800c40211051141954100010181105240b6050b02e045070030140000110038840001580a0000180500c520000006105002c1903284511200030443c2101400469080d814501c2410400804c01410b140c20071100c0e0740140c8641444a00385600b600c1e043d0101c0e01c0e412543d85c101340b04031014560100d030200d0302140c41c010650003041101e200711410420681e23a2a4060051042e120010341083c8611001404001d00300c9406544144002c25041c9000015070b02c4400304c1e0070403052003030380307030b000341c01c1880f44940511810001018410040040e0040c0d5800141e03503201c0c04400409803c07840940c004a1500052072401800c00144040740240280744020000c0741c03c448103500081164020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 356473714 1250 356472464 356472511
    0x60615070818120c0a0902070609200102060a050f0a1109190906090b0604090f0b180a05010b0f1e04050301140403020706090e0106030509100f060303080a23090321 72
    0x1130400d03914002d400f03c05400d245c564104000e402c074400c1580c1203900c0c0d140f03110000d8603504403c0e0f10b211034000300c2091941004002440c0100040040494514000a20842c0102440c4880e030044005c5d00106003051319144550b61405200c02040e00680c447d0349029503403941038284c805039001c03100304004d907580c1c901e0242c06442c00d10b10707640e420206c01c20040c00010035a0700920a044414840854401c480e80301054a0115220180c81c04412180c103010301000c1e580038260040052400300c43c00c0421400300d05910f80b281c240d4000800300b00d898101480d070224020f0b0307402000c3c024020801c20350109100004000122001c40041c002c0800c00328006010b80181c8040e901c0e64403148041c2d03801c1090070b070000c15001d08031001922600001c3c2103883d0303207030041d2040004d4226000c0b0701e85145203001b915002002e05480040781c14580c0c0e00c452201340c560a08e5402003a503244405503103848221900b140f249d10000446800011141d01203602281c607464007401068a820312082c07000140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 356474820 1106 356473714 356473723
    0x60b1206030c01030b0f0f0406030503190f02030a0f030c0225060306060806030d030b01110f0105250206040201030b040e0304080a050d08070206061507081812 70
    0x104401801e081c024a4103604003800e0a018100c0c2c1c1100050120b611402418050040c051090303019550340e80143c0300458000b015070342e852003501000c0c96000440340e91900410440c0b998001c1d1903200004030b03500c0b4105561782c60055803544a00301d02820403000c10100314421182132a941090805c070036440081940d00040059190840140541d0304642c4070400344501c002c00c005c0180c0707000c148524110703440e01d03000404240550043e15010000040d240c03461080c070310103c2703195805521045c05040c1405402d01c040c0c0030100c05510801c400c202c03410040e0000d0b004940154000d0b0040001f0090040c00451000d041c4a400c1349590025413107031445034402d584400c1402000d01c0403101e80c11191800c0c004070b150007a0003959804014104e14010b0700041d040d085c0e468031100c142c400715070740400702d69a5982441c019905c0d607031011408501c01c0071107a0544035031480008 = true := by decide +kernel

theorem cover : BRFrame.Cov 356294964 356474820 := by
  have h0 := BRFrame.cov_init 356294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 356294964 ≤ n) (h2 : n < 356474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
