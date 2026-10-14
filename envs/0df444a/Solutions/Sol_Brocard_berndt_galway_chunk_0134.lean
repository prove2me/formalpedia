-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:02:31.358782+00:00
-- url     : https://prove2.me/submissions/360bd799-c44b-4326-9593-e868aa3a3b70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23920869 ≤ n < 24100725 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23922119 1250 23920869 23920877
    0xd030207050705151303080310080309130203070302070c03050f0c030a050a02010e041d0c01090f120f080903151515030a05040804150c05060f0402060f03130602180907 74
    0x240059544a0700c40e0b00521410381315a0a07244020b42e0020078504503200704000c0090140072075904c3c90a42180e130011110020798020071000000c0c40c40012040f9800c0d61001020b6040c03001600742a14000c1d000038100000f050b070300744140d40014503443c40080245001e00d00420361944180101b901d0f0880c3d4194050294010340070905c0050000201e10b0783e0f00d40d0909041c001c100c943e501203402818035618960310550900c41907440d0b80008a0b003100c0c07000c001c1e80d400545503120901c0c050314172014030400007001e40040c11500030a000d44040361074244034107440c605d410a888c0c0040d203800300d02e284200c80d442008051200800c2d200c00115001c442c00d80f9032a040c0130704031140da1000e004c01000f4460980d00d903c000b40400012000f10342c060720064240030341544007624010050324001c4411201c0748121404104050442c03044a40b10b640e00800c0249001c803011000981e9420107001d88105030740301c6288400041c12400a000548480c0220f840d511180070701704550710402400240c284 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23923369 1250 23922119 23922127
    0x403060c050705030d020306010507020d1113020c0705040b0a03021009090501080c010804060c11011a1206090307031404050301050403080a1805030a0507021c061e020f0405010f17010305010e0d0302 87
    0x980c002c000d1711740b110075400d001070300ea94500c030050358144141d100095114001c440c2c070008020041030039461106040d00e8116540c0901043c4004038400c80b034010943d54000700c020070651919800290500c9805006900c00036a65400300e4044910749284001160040ca410702618649129542c010200c040041600d1089180041c0c056840600b0207048151200c421b40001802040d01208007075042e8004c00041009a824180003030111144a11400040d4803941800d00c001070305034011101440650f1824010340d8003a14400781034545900040e20a0000003903607075081c07007214400c0b80240c40300c40280c41c0560181049030070241e1141140005010340c1c0011500000640320340c0402400c00c90360700ca24500010300c088002d41000b010214082124608100da42d40054002d40d87c02c420121404074541c0d201000d174000e5a500840e840000e0008004940c4201d0604c40a10960300b4000241c401e03004001c1c0005100744c1040d03401c1e2791540620b170010700080054400040c6240340860070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23924619 1250 23923369 23923373
    0x303020a080c071a041a040809041109033412030e03031c0b03010e0304030f03030c110a080a030e0102070609050c1e06090f031b0414040f0b0903040b0406050403060c0507 75
    0x40b502400e0494016404c5200004080125048503a40390461302d641c222200c2c0b03818500341020340d00041c0b0443c0158101505001204821003e0340c3c001c3c10001c020345140d100f4102c000a403071008080d0754240c4400c84140c01402030b0306103641c8000d0500d55010011403003c81c2809803102d00c00b038407106d019600070010841f48807a01005207440fa20442800b1460140444c0020f000d441c1003c0140e130b2a0000040000400070400485040a4401e45060065285221303055681502020689240c2d4214400400008031880c0050110340e001707080010305068001c0075182240c00119046400710781c1c1c0c681040500404000d00745c0008003c60301135111011104500090a605000c568000d42006c19418000d80d2100300c094442040501100d1600b80310744044100e14800c1001c00d4052171610400d004c2081500800303601c52500320304200f20100041d5036508406000814080c1640003d000121b10940e18000a0000349416540c0c070361950f055007414000c840e58446100207110041040d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23925869 1250 23924619 23924633
    0xd0f0503060d06060f0e040b010b04030b0109020702060412030509011404050604180f050408070b010602030306150a0201060503100212010b0903120a020c04060b03010e1b1b0a0b040303020a080c07 86
    0xc1e01900a8950221040c0e051403c140603141c00d401a9a0080c3e142501103441604070705018840e900810a03001582da94003800c034240d104501000c2c00300003960006101101709a00141505803020b0441e9150994604044c41d1051b4010780c01c80000310009055a010f69100318000c521030f40342210140780a1410001a00c01d206601ca52150a80440d00f6688038428540c8502c811540004003404a07103054a4105000c0c0c1c0b00d2602124501c0008002140840c4004296482107401501c55900c0d11404d04039040c107a0807600f288011507481c0c0e08041001d4900b408080720355400c110f00035849072414003151302070f018160443c0405480c00d0101400a41d070000f034034007000c00342202c012354507401c07224200d007061016a8903e801600700070f40010f40c0b8070204011812180548041d00e5540c41c3c5c0f016424042d540004100e00000381030000000314003032440c1c0810409921811101099005c1c0d0304c841c004507080b01c0c2078000c03a070701042c00e169182e08030403641e5214012807513041c508086540c0f580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23927119 1250 23925869 23925871
    0x10c050432120106080102040e0603070906150804020d060e101a03030403081c020310060807030b010e0603100305100203060901080613171b010506030705040b0f0409030e0d03110d0f0503 82
    0x2c1c807805141c2c0200400038401e50160b006400d03428001e540c3ca80d281c03000303100c02900c1503580c0e5000740304442001810007114402c00c0152800640050411100202c007143c100300050000e0317911040d140d8804001408900c0b4030500514040c0280409500e00300b150002c030f442d02c0740c0989a4140d803203003420b001c7e0341c00310840f0b0075654405440c07030f11004103450081101c540407102500092001003401416045400d8503000c45415986c6d00708250f4520074211f0544c3d0340191b000f808154000510002c6217403440c007542d403041e050b81c49542c0c055940d03104d00e85403058027510403a9081d800414041c80c1c1c18804800340c00761075084014681810031000c00081004002400b0340390107031040e0241e0103150b0060407200b201103c4070825240c0840d00006a00a00c2c0503240b561280c40741d0a0000390f107091900540315090801070440314501c00a8003840b0161146100840411028032410325280c1d94040c52101b40c0c5000f82e6907140012203180c4194640404ca10500b000d000c5038841c1040901e0303107d001c80f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23928369 1250 23927119 23927219
    0xc0f03030507060507020312040b010312030b0904120509040207030c0b07110303070305281b03050c0909060301060306180507060c02061603110715021902010801050d03050c010c0504 80
    0x60b1541d104541207085004c0e4500b04074040c08c02c0424070040c814102550f07410b030307800b45030603420401c10b60100fa006c43d142c0200e4242c00c420f03110000750100d08450302c0c00c00d846440b07003031072031500c4c1c0c0c003800080c00c03a40901802c81c0480c011607103007c10300418400490344020317542040800c00c40d0456003a50307a40402040c401c10941c44500082c0d601a00b41c08030f04d00762051407d443c01c502c9413140180007a045000e41503603054403031100200c4180c40381c0611805150039010b80780c50700321070b170b01488890540101515010b640b50900000007074581e1103254018403850151091460700c914060341012100e43c442800c20481c03014040160340c66104481110682c41014401c11007945029a040f02c01500c02403064041e0a800003501e502442241c034455200741c4c20b80749901540c1d413400168907148600a130002e00c9440050040c0e090003410407015a00904015080c05841c2103401e00755140c0c2803503803001802c041420440c000200107101450740c41c01c1d003c02403180c0b00d9602003941d4861400305c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23929619 1250 23928369 23928371
    0xd0506010e0a0603020303030c0d0c020604240b06030a090b010e040201080c250c050307060503090d03050c0f0c0d0e0f030a03050d11030405010b10020303040b06060d060914040c0f0303050706 84
    0x4100b048031103a00c840001c40e4060140c1e9105e10b401d2010355032a80000c209090100d04100a01c80d4480c80844e20600c102d03402142040c4145284000c008503108200f00d410722550354401a0f90030f56101000355200b01c441640200c1e003204140341100030044103074854a0b00d03600d24014880141c0c1c2100303c0c20340c041902c8080750340350700c00300f0020300b81c103440580e0708000da41d0f00811417428800140101000d9544c00e404031110b040e42c40400720740502c022207610803160842c08843e00110b2084e0412600301200c01020380c202403542003900c231298000010302c3d04c16072000c1c03106209150403d02050f4084d1085411124490341800030944a07154413200800300300e0002200c80364203556900c211145818082d819440303140c545806c50007090104800340c440c0e044c0b4152002d184e480042102d1059900001c020250340b68501800721035001a0520750809440e10400700e1050490b104441c2c800d5400840b9681da03003001d043c400000c0d01290000100164412001e10100381c109080b92001c1b075221038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23930869 1250 23929619 23929621
    0xd0e06010609140d080307090509130b0c0c0106050a12050601060c080d050601051303050304030213090507030609080912030d06150504270c020a050f07120209060d060203070504030507050d0506010e 87
    0x59240f018013800241904030100c18015842e034007880c80b00550b87c040d02c54032901d4480c40805400c0c144000e45c0206034100311400038500031418400381482d038000c0320020480300e03203c000084401000c0d0300410708109800c0801024080100802401401c40f1b00304002145515101c0d40d2844c420305060644158035407010071007503442801154480f00600c84c90306926910303464050f80782d52044c030003684030307120380281d0040da11074610909207060b5000004011846c40c55032200c000d0655441305403201d04082c0401641526000010349121100b80c1c0610342d00c03601c42c4101001c03100250091180e08140b1440003012603008821607040d0b54008030341d03020003c900480a0070422088014004817420700c503000a2640e000120005034901c681d041c0c800400155146503030f030301c84600c14008440801080d4101605010302e003150807840142040b2940c01311500c07240c040e644180c400c0c2c400520000307420000e1000500040d0050201152420228895611140e81d40ea00601908900c810004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23932119 1250 23930869 23930909
    0x150301150e0406060201021201080c0604030f050c0402070303050711061006030b0d140a02011d0303070f081207020706090501051c050603070f0605040504060506030702120a0201140c0d0e06010609 86
    0x410301d507081c100910900c99542c0360071009020350803031040d00c2d000b130810344004100b6040204100c400c11402070201c905062650701e81c3d9070040d0003004150350b54082e0702c1a07400c640e00c550004081c0c2600a840c0440c0d1410070b140024120400d420a86d80140c10003001d210184c2d440d400484211003062801007820001c1c00d000907804468010005c1840210b030f44043c05a480121385407020700d000f625100090300d0040c0aa100c0070f00c42c040c2665054204121030800a07106080587c20540107450280c101205680e110400c54410341c0c3d9030000d41d01c400c0081210320b030310080c2c4c40003400007841c01c5030800d2034440c0c520318a0084603541d00c00c141d45880c0003480e030792400c1181100414101c0314000c0741c190303030303140c040e050b1350040c0035060095081c040302098500304081264040c401c507038024403504960b100d1807005a0080000b1200b15500e45588581e44000d0b807200c90f00032841140610b58601250b00c1d00c03011600203003014202608144010070041d50030441c3c90085440003200005650440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23933369 1250 23932119 23932127
    0x60601081b030a05040b010e090304030602160b0a06080105072613080315010e010906120c090b07080306031c081812030106020a020f01020606060706150b0309100b15030115 76
    0x20030707051418a5010007001a02401030700a80d003e580242980e14640c2d07260101010301820880301e40c02542c0c402c000c00c00010322107500602c0c40410754240108490b641d81d5606c541040280c1e207841043d6140c5000740030040c020f110f820f8000702c03079051507072000c0f400034078601c030780840207948100728541c000001b1581d5020381c1c0307818444d55200c4000c2e0b80d6071412100e09500c400c1d00428035030000b003490318036426550007150741ca01030754003680300c00c403038169451350010103881c82c00d00b022304200c110600000c6184604018100c07052081c14095102d01e014030625150500301113800000000b810410b039611600624120f40098501c82d503251a58a00c2c02142e2815030b0034407a03484082c80000c000640c1e540c0c08203692030181c0c801c95103501c160781000c004a07a01c00c402d45540b980400104003141c0040c425a0029109900d00e00c112940a0340d0755204440580007280d40d511a60440344000e01c015000d8031600d1201c41040340c00740c850700d00340b200041107404140103180b0441c031683d83c001109401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23934619 1250 23933369 23933401
    0x100515040509040b010305070605120103081b0f010b0103050c090612280e0c030703080d09030e0306070c1b0e0601080603100606020c0123070204180503041409061206060108 76
    0x101800035440b60606103008810008244010760b124001c40402140b02c074480c0341240c400c2649401c3d40c4002d642503845071411548001258200341401c500100301d118018410145183c800740000503070690810000b40070345000400c640000c600c10010070f060343c1d640301d0a9a910324078400d103404150380c1c0c12020481444000d98650054040888903440d0302500e0b03000b4034601e106031001d0715084007402c000d1560381d008500000700b10042c01c0c01318074002c880c01c2d406510320318000c1c82c0103215a6100c0000c2030034004140c9172a000101680c1c0340760107000300c1018001e007801c03c60048900d4645041e269842410001d06075a04000b800404911240e80030426a03104d2510b0240400a0799520301001c0d542d240340082d2280400c18206100a0300c0c04526500f840c40e00c80d003044249801c0d01c1d6400c00004002600101010101c0020f07038101140041006d4000b074055040400c1507100300004100e0004030060206104015901c150f14100002140c1c40360043e00a00b000c00454694650a07884c5402c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23935869 1250 23934619 23934629
    0x6030312061507050703020a060503070f0315180609060605070804060305071101020a17150a1404090c080d090f2111130f140402010504120c050a0b0d0609020310051504 74
    0x2c2c082889400d000001c5881c4048920031101c0d41205030381c8030000e43c0c640c0811141e1601281445841c04080d41c0070307420421503400803640f9010003d4840351001c1100040c18028618241c1d107030340a120384071382885824050221820300508018842d13549000500c254000c4000f019100c002044605020316040903445c003000000350340310500101d00422143e0402010b0101c0f00451000c940032540030382d015000404082c1424488600f404402440c02969071685900140d41703a0003440441c40440740c00000d00603680140500030582c40c0010620501508a0f0040d8843c501040108001c0e410b04440e59542162406040b08450305103128a210b4810903542c00002d03070740d440c0c05198480d038441110710404000401024201d4000c0e003102103070844000740420380420050003019603090a541495115005004900e070303c800c0400d040005983c8443c10b121004100050364031049d00030100504444c039411030442c608111640800d04161255a01038031010540002e07161a00e411200508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23937119 1250 23935869 23935909
    0x11030d0c1404060c05060604060b070b09030f0307080f01050117060d020109050406150305100b070212071a09211b01180609030510020702090601051605070605030108010606080603031206 82
    0xea036581018018a04c100400c0b034050040a0016205140030f12400080c2c0c2c3d20032a01a041c4445513451101c1e0b1800030b44060752910040c000e940d00d103201c0800540c403407581680c13001306030305024000e041e20407030682085051000a04000d228440c000043d5640031104907810300c08071a49000698801407990406c0350060304014001c5205003036130341040c030448031664040286968121140941c3d800c24000c1c200e1050007000b080c0301610300483c041d900100311505581404d03649011028800810043c018080000812801c0191801c083c0203641c0198007041121102d130f001c1c40300c9444401c5000040340020704190540c0c17441c2d2146801400000e008040f04a00c9521404007820780111707031104540920176100c22808600c891b001717585030303a64081d103210810303160f91005540710f402400c4c14409070240781c00343c0c0c0c2c0401c0082203074000404107602c6003139895041011040c00d448254100c20f003032040c41c80500000d610000700b22490040241c0003000f568a07200002080c1c94290300c10182c5203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23938369 1250 23937119 23937127
    0xd020d0f03090609080a080f0a0918050412020a020109060f021608060603120a0c02090a0902030d110c0103090302070e101203050a020d03050402060d050603011107050106030204050711030d0c14 85
    0x75812038850002d85010362503094520b070b40c030509941d4800c40e004008002d42014808a2540c004510181c55010058140710b441d0f15140ca04a6084904154032402103644560600040c44400900207050081c14800380c198181c1540010b4107922031407159804001103012950f024900c284009540300342c0d0a120f0707880003a0b942900c0c90f600c401c203648680c4240681ea10340130900d40071798102c550000303a075142d8000001c1107400304040c00000070110b803100f988810710500180d40500c807c07056040c15889202140502d968403a1a1038080301c3c442d414149020402d10200e5000140030086800701d801c41e6002c0c0e40c0d448008280e0252560065264190701c0040c40c080540000152866480710303400c917884c111034594102c09484080d540070f5008001001210044159904481d07408000540013280143c1140c0d01210554001c410607a42650f442c20103008602d0030b406034680207102c070b24005014041460500b5100c0c80750390381035401079649204098009008001d140d06543c1100300150b11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23939619 1250 23938369 23938373
    0x4080607110f150f0c0301030b0708040305160f060501050405010b0f0c071e06020d02150a090302010b061c0f020903030a05030403020703080301090603060e010e1009020102070f0f051201020708090d020d0f 90
    0x803c00c01501c0000b16070201200040d036140ca0041500d0490750026841070310750b107031140c0c241c41c1d803080030b030040d82005010810700301003000c0817144040ba03900c120b1403145244071070304014044903130680000c1e12550034040100007680008042d500090300c4010155a601c0540c0c0141d483c1101c244e1085001c0103406820910b450900c10100c41161070b65002e0350118801c0f1002280c031020280c2c2d17203075174141c0524082050303c00d03580c5c0000d2005100b40000070329003040000140741900425881d101e202e842280002054400c5d00484000b80075510080d801c0c0510f9100007038a030b0180500c04400c000012000405261003003104100941d0401000c5640756111108800074108500082d600d0038188415050b0851051080c10301140705000a402a4840c3e481d1540140040d030000380e0462244c1d89000c0b8103080c3e0119004002c1c9840e5446aa00c04c1c42c1c41c09218001c10001e031061056481403181c50041280704048030a0440200d80b10f50506081e480003c40306a0300c42c3c006000a0340c1006200c003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23940869 1250 23939619 23939653
    0x9061209010219030b01020d36060f08040f020105070c030b0106080f130c050603190f0e0d090f0506070c03060905010e010b0a05031002030c041a090406090204080607110f 75
    0x9003e4142d01c88800218070908041d0180c8024018041c010b0780190221820079210310261012017100003440b081031a1040c0c100500c1c401512860410812024010000e15410100d00240c0000c0c500308280f051a01d0b0b1192080c01c800d010b00a81405800a4054208007007900e030580507640c02030050105513150a0000d040580840704c4c0070340e03030400501003070720301e101111600011640010902c41c41070408080c4030590b0400b800c02c503180301c51140c21120744034450180351102c10120000092a2030f114100b0751800c072031901d0107010300103601001d00c0b640701d8011006045d03a8083c5c03451561102d4614180034900d10030b42c0040c0c000c600c0d04d5030100c00c01c03406400c0b4100101c0e80c074009015520750b500c10086d030f0075054890564140d10442961440700380f0740e005103600101807107038076080c55551007901c0c208055101e400b56400c3c00010b600c0c5214502032113000c018004600045040c103045c40c0403e5616100503003000c040c400341490702c50b01c03000d00304007010300c11034880b0035100040840d000040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23942119 1250 23940869 23940877
    0x8060601030b060c0316080c0114090d0302030c0703030b190605030f0c1602120c03070b0703020f0303010609030201030902040b120106050909062203050408060411040b0301060308030705090612090102 88
    0x540082d007060702059151a0800548000e211050082c40c5000c0300f0641780314107019038200845003600284a9004001c1f002c0c42028014000103040025071f04c1c084142504141c804000002850320620900de144200c40003a605166454100020b064840c400020740c002c1c0ea030001c05c4001403003a9008a1869403000c051405006003020140090300c504000d05c150740980081c1100a504403080c0710003505c0c05c61a070340788101501041d01c0c0003450020209080c18a90f400204041c40000b13015002c15070f04000c400b140050420285080d5410494000c001081030702c8064101501e405081e03055580d40e50090060540040c04100b1011108000c81e010f400300d40303c4c0703a1160a9060000f41358140128165101c0e50281c4040c08007114204c5450701030281001081c0d04108003440b02003800902044080d000d82d0149405101010320b5404120a1342c7c503c6661034001c1e41040000c200127a20001600d8001d40c1904000f500c90b00030502103443c0d8052421110450341002040c0901804194010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23943369 1250 23942119 23942131
    0x80d0e030f09040f0504020105030a0f0213080c0901080a05060711010b04060306060f0801050402060412030507080c0109061a0a1a0c0a0803060102060f0f060603060f130605091006080a0e07030506010806 89
    0xf0b2006071314485543c0d040f26030484019020590400004104003219881003041401d0b1010040c184200e00f01c2d840098107840d00030b81415440600074424524091543d24010140701001b00800f20300c55803215261840030704901d090020920f0800003001007074010a480c100040e0080102a9903400c0007000392140b4402e8010f00c081031400440c1c00c140c1070003030364402c1e9005032100e4a8030b490310442100040842d80c1c20b0301000001d000342d0700001c440400601d40d00c03e4900000c95201082c3c24480112016503c0e401d409448210854545071078281070b4008891a10300382c112004004045400d071845000c4090a09015101d0080d00700040000614003420003a402c69600d42e61741010088160000d070b032070f401988440c10000c3e1080c40d005009583c00100a80500d01d00040c6030041091100c401c10303201d080039202c140500c41418080e400b20f0b440246105030001d42490041c01424041000d0000d01c0490f48859411440c0241003120310019a03001d4200c0f0000e40c1e40d03800ba5900c1c4c050585030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23944619 1250 23943369 23943371
    0x305041212030e070e04020f0f060708090307060504060210050901060b0c0105271e010609050408031b090a170c0a03080418200901030914030705060f090604080d0e030f0904 76
    0x9104083c4200142c82e100303551103082051110f40700d0b9020841743c0410034800c1c0c1e52204802100105545648018282580c4a01081500d03151500300301800c040c0140c002108000c030500c01008555130020b41c00409894801c0e0015154646441180c05403c03a03400c5104c400714001029a0142d10562040b48114000003103800d2070307200e61441211014107480b01e035040e80e0100c3d420000d81001680f440c07105050324400000c00704c5d0380e210a1030a684049909644005010040184000b2154144032980364880e83c0c0c586031410400c002400d0320948e006415048100040c1c03d210030404126040030344000620009038155240740c2080c003a07110b406802044804444500c0300c4004e940225080403a40a12141c940f0100d26200c4007150821903c1504258403403081c5000305824084540c1181c0340d013409907548002c2401c08600c0c2480103480c0a034160824420130120762400303e200c0b80c03c00c2d840303e2081e0f610511a01c0c42c101504910403807207618000050742c1040311003250020240b210003039070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23945869 1250 23944619 23944631
    0x10e0a0506011a07030f090816080d0c080f09060f030a0c020f0f030403060507120f0209040617061617010602010605090c0711010e120111040501080105100219030504121203 76
    0x44650028800790000e641400213000d40400a4002c00448100740700d245824041c044d0748801091a044041d491000300305440f0b00140719407501032207810450a01780c200a02d000c00240c1c4d80c0d0b00d59110b030048050b00c444001c1958000f031b68519040b01c80c1102e020a0050b102d003803030007034880104102070400300944a40345070119410804034404d104c04090401540c2010302c0e40d240d407030242400070a044200100505407008401c060b22500b5941c02648800580300c0980c02c1c244821260301384c22101580d0070b8504c0d201c540c80b100007900d940c0150501c17404c0250303201c45031041e94070420504071501c00d02c40b00700000c1903040c0d0541c0b049044030012500b1803051348600da201d8006109020740a04071540002c00c448031075000310360126083c003000c2d00b40e5001001d20000e260031104001c440c124150000602000250b9000841502415044402081c25409804042d5441c4200b1004001c41040d02c2544001d00d4019025a001054003200461840b0308174a00540444c0145020001003031a00b6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23947119 1250 23945869 23945879
    0x1060e090c0a1802030604060302060703030501060e01020304050604090c0c0f0510060b090102061303020709020705010b040b040b01020a200907030903120b0a0e090321040519080a051803010e0a050601 88
    0x1103034902201c41c1003a000f4142081c0c1241c560203544000c1100340c0180e01d90400000680314078000f004854020b50380000e0650401030024000a58042840d04550080c00300f07006e03550b10b1400702d4048aa5003100044c40001da91400c3e02c0b03440e091140a000020f11607071420070b01c1004a01440d071811020000c00c001510344424061501400b600e90340142e011000192481d1260788030101224000d00443d249540c0e50030b0050f081e6481198211000c1e5101e0400031068146400365041c2d803202103500b40030750380c1d001000075176440c04c840002e0700380010641c4030540c03c5804015220141000b400f40c110302e01e00311502601030920f8041c11400030312160703a49155560b0620485030b19180007031090012525004407450705400c0507006c41c482d030004011000c242e480442c0c00c0d2510340c040411140491800382442d40c10100c0d15204640300b004132030348110019104800b01c40040c0c40504101d522540b0207102c05c1c865101015042d9050f61070050941c0314404002a2081c5151044007110a16a290 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23948369 1250 23947119 23947129
    0x803071401090c05040209030c040c1706180f0a06180207050c0a0b0409240603050402010f02070e010504180204090303020405040605060408070302060c0f15010e0a0b01020601051c0501060e090c 85
    0x3190003d81001180c070018401c07031034190018550380600800303c0f0100041500000d08031400e8030303e800041441040f0126140c014610a507601c00d008640301030307410700c2d10004a5000300c3c0007400145000d044000040c0701c4c103180e6200e5130140c0400c010300e0b400e101c0404000720080d44220707419501031050030034500c4a80741c52500282a502021880e070b00700392401c21100050700b140501c20050401c1300440c01414444404140000c0c20165008105401c2500000d80041103008070318045400198050000b20584a0924111075041d1000543c102c54461941c0ca43c20903014002d50190030a03124005255040c0c014000392002100c041200680d0754081042503c075511031450349400100b400c10240c0f4056020340030807101e100036503070b80aa00e41c20b442d0400340c640c041d041180c040c0e0030040c44468143d0201c030b0f070702c80705016040003111000e41c0080e50741c03501441a00d11a0307071610040e45031b400700588454201644840203105450721500782d0f00c2d82100482e0050010711460040031403500e04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23949619 1250 23948369 23948381
    0x403080f090610170312040c0501090608070c0f03050c0307030e01080601110a0213020906030703020a080a020304021c171225080403030e03090603011e0806070f120b06040803071401 80
    0x32024003d62000d20300307003110310b000418072643c009600084c0030303042c40391046e1810300c0e110324071662100c4c625505090002d801d000c9541c010004100f480010452615081030126095980100c1c064178090f4081c9001c403900c1c4140d140c8000503010204018003015045130981c03191031000d8948901d250307034107401140c0240b0b080980c03400580c403080b42c040250415212120340003680078405031515060202084281e44151741001c00241d0008504460380d6000f003180c0c1c0c1100c00030b1010b61550520303400080c2c00071090b1390314081d5420040d90300d000300040c88294000e904600c4101c2916a1540e0130a201d501e20116a50034910038911072080326074004607400300b0441626110703041d0740d40ba103483c218010310014144c20030307030700c0100100b6100d6616a4091802440c41c140d01c0c40e002203081c00e99260366402035000c060b4a910000900560070340085c0c01c1040c00c409890301041000c0310620710320142c402c4114141d000000040c000c156644040010300d052070044024000e0070600c1c4520390308a0361 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23950869 1250 23949619 23949631
    0xa020405130b0a082d0703050a0308040314030f010b1c0c0f0908010510060503040f060204030804180b0f0f0402070204090f120509031002070510110c100207020d0f02180403080f0906 80
    0x4a06118007110391001810103165845c421070301c00d20b07142c0d0740d8503141c030104180a8008c240c820341004101079100304c1e60b50045000d00480350641c00d014054140300c51040c00742c19891031000c900ea00d414040712620704103c160850041c060340c07a80b00c00103000301182113180000180f00c10000b0907021014000c070b5005a90011441c1480c61409004842d00d0b0809001100c540c503103251000003141c1d050029001441c05908500da50718a40407103101e86110490002c1611030500c02d403083c2561720280e40821540c0166407100c0b0540404000500034443c00c640203510500e0000d03408103000e0f0b014a4800160310a840c101c02d11140030b10f0641d103d00038080c0071a810752242014075858000c58000d081044c0c4034400b1101640030f83c8200e00261407011042039a005408240c0c00742c2c40f40304015440405000d4042185894810707004100d55400312030f406010300d66002186403c41d02c5400f100c1c00d8450401150520508040c03500408000703041c1c5010404400100204d01104004650540500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23952119 1250 23950869 23950903
    0xf030306100309020a150302030f01051014030601090e0f01260d0e1305180c0607020d0b100f0b0304030f090b031602010e03070614070e0114030a020405130b0a08 71
    0x9080010102d02074403c18000301c0e0000720985000510340c40c42448060b241c02147c44c0581c480c030344164561803100059000610510540070048000d80e0005048180c241d500c0c100350b90b495440c000180c40000d040d5202100a4503840200150040d89403403c81c1039403494030032041611115100c0c2e24640c4c0107400104a00c0d080114081281402032401c607030030150103003040c200c0d182d44141140443d91304071210700056141c6440f40c0c2c040502400340481010341103d06c0c608013400d40c0c001c40c078800750301100140341000307640c00308140039a02c3c00c240e802048201c44d81c007a0951550920072082c0c0044d42c0840c0030a145071503040340d1a0042410f0780a0b90102c100142c00d5584d00180500f041c40c00c2c08038803044d9540c500310a41c1c1f81030180010161180140008141203400032076400d6600700040500c0c0030405500d00d81c1103180c0e80000b0300811400e45000c2c0e90784070307240c65010b80001e11403903101c217500400e408401c1902407070503008080e0030102140e4010f40d0316621880030b03458411041c00e040c009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23953369 1250 23952119 23952139
    0x1b0307030c030f1802011101050c040902070611030103031d03060c03070e0a030506090c031b0619050f0a0903050c1e0d05070e13120c020f01080c07020d0b090f030306 73
    0x81442507000c00900c601078940400c04800c8404080300300c2c1d07401800600401005070300f01c070965801c0031007000c24001d082c00811143c541a00308803024001ca014441c1c1c0603400040c030001b40802c5402260303440750300f40c030750950780e503960b260140111208070360810009500500b0b101c003515000c10003030710454174415102e113180e548100865080e002182280d80c4490010004070100d0800c00c0818411a5480000c00004884030f04151420035403021039450103240034200c4809803640740aa8100321896040d0354804c0c00140000e40306030040f5510560105400b103a4510300c10740c41800c075021280500306841005c1e005005001044034241198446c009401840c81c100d4180b844464100d90300038402e550039aa22020300ea1b00030141560034201502041038490240483c010105172020b4960038a550406a240d01150390240802001c0381030241d460001440e0140b2041181c65607607005200c1e9030070030400e00e003c98507050103980303114662290351000a100400081164018400140240c1e02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23954619 1250 23953369 23953381
    0x2031314090403030c030f090503030105150304020d0f02010c0803090c0a080c031b040605040203040501020706180302060f150405180609010b06030a05060d0209040f031701030209240a1d1b03 84
    0x50101c0c900101708140d80c1e00d6400c074810410788240c000044c0b150707001d0f5a81e54906030410442050140003500d90010410501c00160307030714900d01021982c000c4081b00541c60030700061b98201e03410403014003100400000c21400041c04224400c44132422518450460784940700280e5514242170700a8065001b01000c990b0340d100883d590300c107000020301c08120306490788080b60a9800589044074aa1340110f0550104031103405402ca11101c2252003014610b42606c00964400c1c028045158104030400855490420090790390b12028000e04140f00d5420980102c0c99280208070f6000b9842c003812010408106043c020410320100080141e421601c65289141c010b00c005444c550b4041d49a0410a005840e275110392841280241e040c400b010035581409070101201021220080d00080014401640c0d801940381d0400840d1a40313032203994004c070801203080d40030f21a00703520241580d40002c00074100c0704e115503c038482e40701c1588143c0380d00002818a80f104a03608858840c10f000060f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23955869 1250 23954619 23954621
    0xc0403050c090a0e0304030308011701020a0915020a140a02040c081b0c0708011103010e06060a0507060902030a021306080c030715080702120d0b01080f09030301090b0307050307060203131409040303 87
    0x60403d218030300004050038100070740b52560b8007642c4120041a00d902c0100520045026200745081012000b507107044880d21009100940340d00032001103506401c11110304500c00c1181207100d030b07440031800c844028505000c4e580c90b911001c0c03c82c071a03414031034280780031446024014020040d5010317040400e030500301611541c0d00b008210300c2c1d1034031414000050621090086c0c1038000c001e10441542c1e9414102e1054814900900c42030142004114070009181c0c0710013203d103150f030040b50010f641e810358030009050222a200282d03205402100303860f048507041e8014811039201d8402c46040c02c0401003856143d031007500c030388803609212103507803e195805910510760060031441a10200500403003004410380112a1901c40142c2e01e82c29540c0399604030f811f40750030141c00e00848441d07180440c461075481c4014002c042d15142c40741c4d1001c0c900d0700d00300107810103448001e0664076020b4071840c00030760f04d0300300d2242c00381c8400354078070000703998921145a10070428000d000c6403c150341d1928160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23957119 1250 23955869 23955871
    0xa0305070b0a030e030f0a3e0a0212030901031404080304080304150f090204060603050f01140103110706050610080c07120c02030102181005040f050409020102011119080c0403050c09 80
    0x10003415219421199411424170061110004401616865200030b01c0c00500c01e01080d11200a02541000c1d0890444260150600d407003400c0e1241c14000080215410304100b40c03a0402034004c4400480c540c084040032020b0710700380c002a0b0b400c00100281720b50307051404034155009054460100082804180013500940d40030b4003d0b84881c0800325a0513203c0100d45290030760300740242d5200baa500031440e00d405074000030149440c00b07002905051a1180c181c410622a0010501c0c840d851404640d01981052032122040c04004d6203d12203400c0481c080e010446219204d0980700a101062a0256255501035030901c1c80090500070385a076041510188602c408062000a00180c40103907024001480104403403c0140c07031041e0501c06200f02e403081200800c09002003070000b40308511800031003c0840f2001c88012804e04501d00060b4010541301313140d002a504001003031403540150350a40e00f1200072907969038140d5915404060454000c5000090803600300c1da400f10710a1821006003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23958369 1250 23957119 23957137
    0x1506041806020f0405031b0306010b0c033109020903070f03030212030703060512030d0501091e020708070602070803070e010f05030f090709020c0f0106051503240405010906050f0a0305070b 83
    0x1031440c15131100c0000340740886c41c07c0d222507203030b45140c9642d180b41414495103004001c140c164900b80103c0b840303c99224010243e21500118440c1d12210210303c0d0b908400c8191000c480c0d911800c42d0b00c4440c1140a0340c094a402402482000c01c0002c551300e000c0c482004490705036001d09416103c2d104030a034113503c09482c031020540ca807030000c2000e0b41d40c098403100c0d000c001c034010366071100070340b01220664205034400c6400b14500031344000b4098425107003000c0d02d092540010ba80304070f24500b80078640074013240541003c0c80892803008014a5000a50113158543c451800d401c404030011588a02d4030450358000074000d1000c580e0072906080001e400c80740c0300058a01541c2ca0f0501d00303080340c02c11100e609040d448400e401c40612000e2250801810042d00c2e00002d8900d2450300c44214480542110404000c407111030325000c030383c10000704040100620a010f02d5969107a03c00160915001d054481daa0380040f082161030a1003d030001c0701d40c8400034089691a003003242c685070f0031030300340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23959619 1250 23958369 23958397
    0x91503010501170a2c011404050c0d0303020c0f160b07020a090b010c05150a06050303071709060c10020702100809100209031005040f030e0d170d06090509150604180602 74
    0x30307070403940008a408417402402250407441c489200c1c50312825200c821091207480c0e41e142080c0004103401040e207494000050314500540170162404400910a9054505090041c003524118200022900f40d20702c2083d800804460380c3c45e031841e80f0b014401c90b280254003440c0100200304680e125080b007034600d00705050207140c1291940b01c240c1003088102c0b210300041030600c2000310710482d034828900500003d40055080800c40ea0f200c0d000c0d200720b56103903c20715001040e459210f50b90001160020b00c4c010064078400c4800c041407502035040040101c0c800d501c1038400c41701399481541c520784a002c8900061440307080f080c50030402507220f400c006405019040031a11000b0a50240f9400340744550b030044c60030341e00d604000740328855101d60030344070b0a544920040801c0c0360040b00c110205c07100f0380e60341d501e00c614008a40184a00e0740400c8810b818481000030240c030110301c0e03040c0148140d034500d52030b03610340741004121f80c0c00380d40045801c8148076240c404038409034003501210184041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23960869 1250 23959619 23959631
    0x1060e0c0a12060b1204060509010c0206130f0c0602070305010606030c0c020f01200a140307080a030507020c0d1401050603030f070f06090503041203110606090105010e030a1502091503010501170a 86
    0x210410364000f000000b4114240170602041203603d2280560281c00c0c08001c01404200800080d100d48011f090000b5180030140640c0a00802d01400940542d01080d405003091f40d90304040d4440815100c191170651a000001034014001d0145c2c4805d016980e480d884180e420b5403c000400042c0300020b41000345400c8900d108084091001003429064401000c40c0d50152808000a00d214850050190028401c45000444e1407042d1042540c807414085140d583d500340880c03818980840e0980c1c0060040c2c11202401f0344482c02800101d14640248810b075104001d040e40ea104105008031012010030030032020038806010807419600c5000040b64458050310b40d185185c00640240841d43c510322a0041050380008018080d1079095000e008585004c030b0000d07024810501c03895050001000e1145801e41d0140803290806503c4443d0344401000b4603031550094005104070b500812a05035001e444d17070413880949040f0b0340140e60781003810008100b010103c00001c0d00b070032a200d0300d400c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23962119 1250 23960869 23960879
    0xb1810080102030c0405030714060f0c0c1c0b1005101d030a03020c18010e04080d09020a0602011a030129011101090605060a0e100e07020f0a0b0901060e0c0a1206 71
    0x200003140610044101c5079102c504100070035040012350760242c0d200590031f82a81005407142020764880010005045441d400781058a03820310000b0050079901000441e000c100e60f010750449491020f0040030002c000c1e541d0228a501d002c800c901441d94020211f551314442c0702d1103050110515000c841114540d0b20240000c80c0c0352294040342140540c00040758560302382080e210112910036100207100c4a945450740301c562090b0007400141c5400e0000130348111590003078001c10807680c1d0280140002680e9140002d0003041071805440705039040000c0105107150501850180c2c85400388103602e500c0607021801c5294500c6030189060008046684624400a106541400d800f905002c00c451925000f08800d4110ba500000b03c102e14160500c040800c0b03015041080d11000c4a407081c1c075444500050b841c2c03910105800744288981c040e101c0400440d101c1140c09819190001d005481d12030402c1006441c00f1200350403003440034000d1041740b41c4a00007111110800400c00207099071a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23963369 1250 23962119 23962121
    0x20111041211030a080904090303020f0c0607020106050d0b010e04020d0b0a02130f030b040303110415020708100204150c020a090f021b0d0e01030207060212090d0807030b18100801 79
    0x80e03026036012030440d200441400440b01998001c840124040c019030425031352070900c14003600c0d11403405265901c1d900f10400d40640d0440e500c1c0c0310314180e03ca032100c3e494500c0f81d50781c2c4007c03900701006508019001801e41030182d6400010343e401082001c4a0b820300000c5000042e00a000340d0380158903041c20408502c540c0007a501503013039180c0240c0e481040082080043c040e95000410028111200b000802c102d040c1540d0425410f15000c504c1c0c3d50f071000822018020f9402840301701d003050340781c8104203400142c0c41080f91144420f4460640d44d00409208a000d1481500d41070814983c3c0d0410281c130a4103203a942510040c0168890358580b00d0310b0040b550362403c0001001d0340011000b6103011220442d894241065000b13104503c020032004111003505407010b41803540114103030003000742075010307291070140c0e05140342c03190306d0b000072043e60311441840c008004c130b045500803400061017400f52008020700541948009840058207043c420401046852880e0702c940700410b1a0100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23964619 1250 23963369 23963377
    0x30a090212030403031103040b0304030503070201060801110405090f0c1b01020f030a05041b06020d0309030509030303040303090b090304080303011403100c0f090e090712030c080304210302090d0b0601020111 91
    0x101c011600c550944c03401600741e15000000b40c2031036009210070410101e43c170040303903405541032800303a459850740d10050740589010303000320401c0e501780401c0e0341390080007078064402c44800702d409800b561903c80c091860000b003510701a450100420a49a02c0107055400000c140d0911000502c0c0c01850103c03a01c42e5001a682100e603180c40760107100074000440d284640c07460b490000c0c43c8459262007006540c81c0e01100e450380c18140c403003800c503003403501440c142c404445014080d80c5c2c1d03c0c84d0510f8001c0082181e00412642c0c0312030300002c5854000008203440589044000a5140d40d007840c454204c03a0030440c905c1c43d4140320341d40980706100e059000d100480101a22009981041c008000c1c0c90101107400440c00b01881c0700400c503000100040c0c0400b180c0c400c07240c244e0030041a040c00c07160382a4102e0090701c41c140010510042101c40c01c8840103890308208a85a44d00604d4022400c0c0d1103005040b6038401565240f282c08a0200001e81d504900305000000d0442e90f04429401c03907404c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23965869 1250 23964619 23964649
    0xf06030c070c080d030b3304030606030b07180f05040518030705010905010b0d0302060f04061103010b031006030216140c1c110a050901030b1506030a0e01060e06010e06030a0902 78
    0xb0130346401496035010300544040ea502210004408a8080305618491032008404016507045c07000e02c50021000008032030165400800900540d0f440c4e040ca106003103401d071400b40009159014001400314030190140c10303580090041c0c0300035403074442080050017015004030f905011280403154283c01c100000c103151403080d00040350661090411034210346843d103445010740c498056400009034007240155001c54104c00c0150940c5071030404200a040302413a00e4800800000042400d040312005184221545e140f880306140d12204120260b0180d104484020280180c441000078a03001003228a02d45000072150390410600015992241e07120502428551001c604000d000b0034040005800200b96040c0700341c14030380000304904140502c009803890b001c120124a80e0340701d810b40540f0440c0000c0c0410f0300d90821140d91030041908540400080d803030528006144545041030134808c00c0140c41e000c101401002c2802503036400244201030142e920081c0d0310060342e807401304502101c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23967119 1250 23965869 23965873
    0xa0c09050d0b0f010b0c0c0103020f1317070503120406030506030c060d0204030c050906091305010e0109081b060606090d02011101090605010e07030203010b030a0b120f06160e0f06030c070c08 84
    0x1081003c5a08843c4906802c01d40d6a52001c1042c680e0703501d03000901c050f00000070310700186c6da001036120320941400b42c82c4540303030740383d0050100007070201e81010503540d0030003072006a0360701c4c0e5074034010190344015409076000c050300244020001c150090b8407480c0c2c0801c0180c140d600002212000560f50360210301c1c0c510b10036601180610900c90203628050141c0001e882c0c403841e03030078100c000548101c401450350980d4440c0051820410601b90081034007002003030020700200381d40d40340c0f006480d0040c0c0400c07000d0903001040d0482c0342000141c641d000781070180c459030ad000501d2041c40640d1000b1841130341441001c90003c0106882440b4003904140100b000003000e505020801c1115040600020304050041c00148000c188081c201c98200415103030001d51002c0c800d004c5882182c501d010380b040da00420a003c0380c3c1140225065108a00030f920170b42c80403582c0c05c026103480040d80da80340d8203e0880c101c0500e03075013415001141c000c0240c200a80c1010031666134100d012400c0e801c448595 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23968369 1250 23967119 23967121
    0x162003010f020d1104181805030c100506010507031706010203040f08060403030b030d0203040506090d02090702010c1107120210090b0f0405100302031306050601050415020a0b010b09090a0c09050d0b 87
    0xf956201e003800c01c07030202e0b64451409203000c007141d01002c04241d41400c210f46d1902e20640e80602c1c45440c0328920780c010f007030b262100e070360242c5152100c0d40c2e00f49060311241481c0000303000c2c4d8424001c0301c0c2107603819110600b900c144040d03014421034004000c24150300c020880071803e1262070a808005040c1140105038a01e41454010152480244014029400103d015002c01c1d0088140c40554809680d029101d400b0400024601e590000001e50000585800e0101255041d000b4140c4003035140c9801c0000b44804020560b1850103115071803060a020200780014602010080110111072502d803d0a5844242ca2a880d500c00c1e40360b89808100050100b0860411248410301409141000c41c210318040c10485001d1a8004004002c1c9694400041c110380c040d5042d900503203d8040340842d04861a000039640f100300030720a5829459940002990246103011500207080141000195440b252003a5001d804400410f6082c405803580201c0c8070b4807118bc3c0794070814002d4101c1103903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23969619 1250 23968369 23968387
    0x504150f09021f02060a1509020705010b04150501090501120e010c0f0809010501050906010c0f0b1509010b031501050c010b03060a0c080702010603030f1107030209010b091302162003010f02 83
    0xf00302165a511091102c81501103aa42a00450b250358019803191011803103034501402c0e804004400e411401c0303110b00c08140101800340540c004c0d09110b200340c604003c03260440c4c0059050340003d20805000944405040c0460752241102c40320040d1400300c045540281c00c00700500751000054100002140c000c0f05a030140d41c010710098208401d0b0303008004079410300e004500051801090030381445410010030003040001042c44410a8002c2040d00440c03d01c18031220049503c07109040c400c50b4104000b241d4550700c0381c00c8034015185000b509502c10b03071410040d5103d4220310780302c24855503941c18a090341e8800f4414244507980c210702c002131a2071441c2010b420a813028201e0011a85000400c0c00020b4005120002140c11780c2018241440702003116450070440c0c1d040290030160303c0c00001015040200900b08420045461080c5a800180030764202c3c000c0000301054003040081d10340210f40d00095420360700c0340f640c10900703110040c08042402c2d100304002500780341f0340c00582e44103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23970869 1250 23969619 23969629
    0x2130f03060c02120307350a0c030f050c1605190605070801060206151e030a051011070b0103021005070b090703060501050604030b0a020310030c0312030b04140a0504150f0902 77
    0xc0307112a0303511401c6051120004000340b081d030514503a00002d41107000ca180800c41c000c7d088101d405501810a4602102610050824116082c0219040c0310503826034140c03c0c011a0b00c00c21000310103a091003210f0000340480e10281c4802d558600076001140c3d0000070445110100c10f024950100d094100f44500805034801603105c107045400580c1400041c0c241003105c07101d1014115213030850041c8081e0181d081c6001124804d51511542181d4420480045225103400c48425403c03c0481400700c20700c01d4038802c048000789600051001480145480320010a0042a070300d4403038103020980d900da00340c1d940141d0302c160302940700c1300040003000028028540503117400d0740c000c2d0810b441c40e41d814103111009084001d034140c020000a0750102d68004e070100440d04041a000079960300c0c1480c1044488151000c0c0019007424640041401d01d0b002c1c4600f5001c000060003540d68420007800c000f000c02030411500140c1c442d01941c00c41c41e080c0a551b1050324607640004040c06503204101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23972119 1250 23970869 23970883
    0x902010e040203060603040f080c0106180c020606030303160504030b1801060501020106050303090108040f0203060408180a0b04030602070609060e0d09050907020309090c07021003020c0f0109110402130f03060c02 93
    0x2a1103030b40100100421600c607030b400c2d281c20035400044032801c1c02c01b500c1c12400c03501a4540460300e942c81c0400000da2150740e64035010101062400400c020380710044200e0b16001e0407a8070b03e4150f4020004074039050001d07175540810b541075240c00350400e5201e0391400c4507100b0a881c44024030580d46900030305d02d0070070300c510802458240000c100c40b0f454000441c0d16030146426007818040c1c50310004040c4100e41002d0762641c3d50040c103442051801d490481074a400c030b620366185540007404241c20358180400c0b03c000307075003000000074100752a56035500003950105a0450b05681c0b281071600c00540d00c0d020380d4050401e0180904010210700400610b000016031181d4440c10100c0148002c2c00c0e008011210f1045c002d82d0410003030390700d5004003107180c4980c0c030000790050201c0010203580f03039066026041043e28401641c5100000049032401d1341c2801c0340251411420f808058003514042d40100711222021108a03125543d8014031804650150f000b81c0e540c9490780100505958180406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23973369 1250 23972119 23972147
    0xe01030501060e04180b16110a0f0b090102120408090f01181a07050f15060f10210905030903010501060809071203030902120c0907050f19140a03090201 67
    0x4000c00e40c50458000c00795110050102d015075038a001c021101500c0300384080b006500107188000c0740c10f01c0408188004524178191001501480c1c5549030210b0105000403d5504a11160306a60313190725021b000e05c2d0301a1011043d99400c10164840c4210342c520240b180d13000c2c15010303071140b40c0c0380300303116643c1e00341c1d021541006905003181d14a4101d034140d442c15100c40c0e0340400b404028044144406100300740b40079025124041c00b0007000c1400151924030304503c01084035807621040c050180b15105903000c95402008002c4040c2020b1051950006464001050a0b041b001d10b040c2071003215288401616240c200080181d03035820b0034041c0703d0060a580c50700740110300e00410080d8940c0c00a025007490704d0a441410030a051003500000142600202506501c11541240643d21181c2c517010500800c038071400600300d240543c05580f10803003d50003180c50314400c40074101c0c42480c058a43c00a01804111804400d00102d01030039540c1c80f0398500150303c2006000140a4030721280b42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23974619 1250 23973369 23973371
    0x70e04050f07230d020d02090d06020d0c050306180402040612140111090a03030c0602040f121106090102070501030e150103080a0206060f1005030601030b1306030b0a09030918020c0712030e0103 85
    0x100d080c50901c040f04440d0300d044107080060321071441c0300038000070748a00d44ca080e9000c280a4080303001d2100c3c90303005082c02250207004214503618070310159100d00040300c8031a80210180800c14030301c0e003075690090303016200401c000f40844d120b151600e02e0501100042d0f4410716038040380f2034640341c00d110b2550300c410380000c564281803218000404d4090b00c1c0c00010304028900c0003a00030130105406440141200b030440003103054a440203000b12603c000020b80300703908001c07001e40190502c00225844410107901900d18503003804010b402504c00d0501c0850148140c60040440c1c07c41200c2c410f0203503204418150b81c654108400030310740a4041e2040348107000402c5141090f0b034500c40b0051400800741041d68403a95040c00507402030120495194010f064100c191480b407821307610130740c1603a114140110943d129072102c0800c86041e6a1700401290f140c2c07006216000841a0000450000640c09881c103410400c0aa041c03c091358040040384404500d54030406030010b5080c66580c80a10b8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23975869 1250 23974619 23974667
    0xb0a03241805060103080a1103040b070302010f050105062203020d0b0915010b042607030c08010c030905061803070c09050609010803030405060a0209030304030204060f1a120f070e04050f07 83
    0x945580b150410305c03004002c90000125500024018000c00c00900070b100b069a07200c5995001401031648224000c50055290100400c200065031003214180c51001d06000d0500c0e15501c902c4d00001d20903c0040c4000244610002c0142d9a250341060200d11880342c071300c0c0c07c1c10030244603031600390b0710002143c3c4045180018400040d01c28180c408941c0d907010720702592614500041484480c0301c2e10a1038034020141e01206109032400300f23200301c850345002000110f4515008804a600c40c02004015800c0720000ca074446000f444103815910350482501c0c03501034a50b460307408130340d030f1a48200076107074071101001480d03e02290a1401440d41c039015501c0c5140036901c050301c411004003e00c82d407541c0844c3c4440161820401e580c0a07540c01b90082191035101c040d405035060440c800e1600e0402003240d0548902d503c0801e4484000c20007000c40c841c0d4a40c19283c11a000c40100756800700300507030740c421b800c1c1d40e120f0017000c0c0115a8070400c1070181c00c1000c001403a48200984c84452020710403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23977119 1250 23975869 23975873
    0x4210305030f150d060e0d0203131406130f08010f0b0d0b0405030d020a030b04050a021603140d05010303110c0102010c020d0e030102041511010b0d03090302040b0a032418 75
    0x40701e9000c0c10075603004026542c0c05000c030810480d06114942c02401c00c800702020045280c0c000074100e400300c01200c4810b20f031010300b00e0741d03032081c4034400c200e0701c4d100e40701000701c00e81c101c406004680f0002c000c0780c1031006804070b00c503440346a640910004142105e007040b4005080c03069030880840e05506108034880ea4012685c1280b40401c010500310500e00041d09000d0f052003601e076060000d0034295034800c841003008000c1c00c20700d102548550f24040101d10381d245184200c0340c0807180100e140f141c0d60455207085c0c481c851208041803409004102281c941c228070302c600e0f4040c612030703195500d003170081c22601490202c014070040c0c1075a01d0f02c500b84003002d8000449902d059000e08d42003490039805070204c2d0188c02158458041d40700c100c1c0c20740b034005030084e8101420701001c1000304049a580000c001c03044000180c00350100c0c1c1195014400350800b50000f081424001d000680c0e0a0341e20790780c401e15655904140c071505402410b00d00490b5080740a5039540e034190121010580e4119 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23978369 1250 23977119 23977127
    0x101508070518010e060a0c02031b150d09080409060305010b011103180607050601090c080f0408090f04090209010603060f080604021e03070f03080405040e0d080106030b040b030111042103 82
    0x4048072080141e40000d0b94140e841080001100e05019010302d407103c685d8031010348007441e4074108a11a0042c4c079400320a90481107054001e1001c01021109084a01c00500c0c04543c00700702505c50f141c0c3c84040034408200f80c1d900600081020b034800041541c45c609006086602d240100c41c10410445031480c01000300105031841580210360100382651203000140c8540700b8402e00401030b0254200000c0e44100607030025044d600540c4805960356101190340d00d56407400c540040000806210500d168180307081101c4094030060300010751240c4580016208400903844400083c1c1c681e402840310084614104005140c0e00e0020290b900305507000030302c6940100044010310a00729608142c6a508000b0000280142216050300588a040c010501c1d44903004450049040c1401c0710100d100c00594642640840c0d928109142d0800c01c044024012007043c0c82c1c0d1098442c081403a0903030b4280716485510b62100001507445150030342ea0040c603c0d1001d40d020640700d000c070794040801d800c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23979619 1250 23978369 23978377
    0xc06051602120a1a091207030503270105150a060905030303010302060a09050a090c0f080405060609040510060e0105120f15040213020f09040e0601050a0b070503040504051015080705 80
    0x3044900146818000490510b03040301c1d28409040300c0b541d10500100ca45901a02d18085c80f91071094581c4030b8100c0c055045244900f40b40140003034020800558651001201c0c00318004043c0209100c0b1000303111300300e00351182500c0201c98107000d14040641441c0225461008004500b484903102d4940400262a80014400030740107580c00103004060324450151400580001051500c00c941c0350340b106001407041310b580317802081040c14180f22803809400303801c0c880c0342e1000c020400c0356500c1082c802d05407400340084416218442d84140f01003e140141400360030215814102585070804010040c1e80e01226a203154001403c1e040c1c0c500f00c00300704d80e0b9a48912203051902910740d440410121090b1000c40003a1510100303050304400c0f8500b00070140801c048030180040c150060480d078480c50700f032141c56400594031404000880080c0c002d072148600503c03d59041c9541ca6003c03809443c0300321805d50000e4140002444500c0301c5c0e540000414005240460961409550203002d40c49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23980869 1250 23979619 23979623
    0x15020309010f2f0c0414072a06092f0112060609061103090307180b04050610120b0a030f170c0604080c01021606020301140102120306010302071704080601030c060516 73
    0x8690f0440c50320190104601d0380e20f0310001d0000c000900e082c0001020551050341e1000020b151464040004610602e81a08161500c15460490340b165602d10300284030001c4200e0b03624401d000e01000210011031ba03548035002020118803140306070700c001040303003140c009071010702c030b00e03010090004543c00800e007400e46005082c00040d042e40e9404c124610302441446607814400d00f4004075007001400d461030310180028806001100d220400c000640720211041c50300583c5075801100158400c8201a5000040a20000c0d5414000c0041500f40500b034205951841c98101e101d41000a06500b1540d05411050303400e040034905424591106009440504190004115002210380a40c1203980305030580414444040325072a045000e50401d12404040040d4402683c8007940045102c0d51010301220306289195680401500290020382003a074203d056210700e0202c0080000060018000c09002019250b14529120706000036981242041007814400140c82c003158200c1120503039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23982119 1250 23980869 23980937
    0x318010c030c0503030a0213090b03100b011112030414070e0115140309011d0f03040902030405010207050f010b0406050f030607111204060309020f01030903090b03040501020415020309010f 83
    0x44150408035610780c0b0562024116000000c10320108184960041c10f01400303442d100c0720000c1c0c0d1081100c0440c0c901c1c581640d01a0041d00740c2180400160380690280d01701414070811403864441541c0ca040e06025402c0002c420000030b10080c400c03a80500b8001e941104010300300030742843c50f10103822606210341c480010103444a041104c0c011a600f503d9140c0c0d03400401e03160714050a0503406001c810350740a40c01c19242c18142d142d1200890300381440d40340100210f02d85403034650580d009510080c0280e82d03655003030040da40000c0c021b01480c480b12822000200f1200000030030001203c40700d0703109611131a0300840015241d00d01056240c0c0c0000a0704002c202d80d4090801181003411003e04480444c0d030015010900e550558051181c00c0c0c0284ca410003002c90000054003181d04010014010a240660800c0420000001160700c1403241002505140d6180c1159000c402c00240c6200581c00114544049507072051142a0305900351411107042c01640500d80d085449a030400203507070b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23983369 1250 23982119 23982137
    0xa060305030703030506180708040c060f021b12070305070f0e040c0b0304031205070f020609060c040308070804030204060303080402040b030d0e01050c0106080703050a1202120f0a0c0b04110a0602031801 89
    0x26654034410500c0046004400c91241c5003ca60082c4009c0040b0b90840b810109600081042d911415550546950b81c0e001003150306601411207041702007403080039501590007061851040000c7c00420005e41c826801071220505001c0fa40c0554a41500006c03e024091010080070075071112440c011079a1034a605a546d0302c84d0304003142d04401c80c0c0404100c4a04050500030300750391081c0f0b03400300540c0c19825511a510f404c1002ca854800c2901c40303111301402408180302243c0351000401c242d42c85076840e0307454a541e95002c5003c1d2a0305610036004102e80008201c1581007034015020220403c801501d01054500e10107004a182c0e146540d04004c80840c010042001c00d5014030b01820251080721003450703807480d015039103500391442114011083c001001c816400024032281d1850380c920030300c0c01e0420b04400d00540f90403800340c00c000c0210800d980c50105181d1441140154094124070354941210710038001c10f001c1580c00300f01107501c10001c084c80c0f4a0341d0201d030a034a810910380301c121 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23984619 1250 23983369 23983381
    0x80a05092409040b011d120f0d02010207021302031303030b0607060f0b01020c01080103080a030207110907020d031107020604050d06020f0307030204080c0a0b030a051b070302150a0603050307030305 87
    0x1d010310320081d59041a0784401c0954035208980c0602109072084400b4403030480603000440e4040760143c00460111240210701e051440c22210240028103903e049509070b001070403400703141c008049403840141c2d40c000350000035403d00e0840407105403061790013980b540c100140079918080c1064409810140d49208a82042d9600021181d8803600b01c0028040400f0042c60341000708040c103032542c094031030a1b001c6005940104d9803036040b00e8018205500740035151806401a5004040895140c0d6500040800d140e407540781060113655590b0040500440c0e0711800340c00c8907141d9031031803030034a814081c500040c0d40e40c00458050702c400b80d450340b0b15102c4500d03082e17001c1e000c0c6503109909648040b0410000c29070550280c8120b889800440300181500001d0051a04c5507029590f00360504000083c0d005600b9040140c0200d4002603085480565020304060364006000480068000501d14503042d20729040941d005902c040d000c01c2014079555078980d1b00d01c2200401000c2c15210800124 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23985869 1250 23984619 23984629
    0xf1b0201030216080d0506030606010816020304030c0617010902030c0a0c11041d011406060d0b0f03030c01020a03050903040501090e0408070c0e01061115010512070305030a05090307060c080a0509 86
    0x1c0d690010741e0b00480b0b20030f00c0d858100c160360008440389000c1c0e46441c00040b024a40003401030300a13030040e10307000502e894070b501e40c848846075146540b0035844104400800070f401082c8000040081d80d49104d4142e00703242d1140d24014060b40301004060042c018882614540707000c582c0c020a0328181075602541d1b5140c82d039604041c00080951103803030180c40001e480c02010340c1c8040b510f8507000801204800031540ba14081064810542242c0b062064036591616a4801612032800600103039030300704150000703803855000902c40764650350042078442605805005c3c554024102d24061401d190510740001c103110300c5442072003401c09040003c1018062000225081c01e6006161040302da41c0351b003880c59420b502807140000050b007000e000307940341d00c01103644c0050401140e50a1107591034031040144222072a8000d92080c055080d001000800410041c144403045448050b00c40fa00c1c9010141080c60541c047c0341804400d01c0300300000340d040d200301d598400c1035080c419255182c180c0494 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23987119 1250 23985869 23985877
    0x1020c06131805070f03150e04050a020306180d03050603061b040f031101080a09020d1103070b1605060606030705030f10031209032003070e090a0c0e060306070f1b02010302 76
    0x2030022000c1d20840030b1955000d412051040f81a03803200c41d41040b041c0c2c4114100c40d00c0340405961042011001c0c08603043d101901d40c0c000d405041111008140398001a0811506803401c900610081c00b24101906040c003001c202480981400c0210380f92a0300401d4aa0b40300901c0482e845400c03502e408409810030341035070f0180c003503000d903859501d440b86842c001c500084d03503502d80411008000600c00d603a4501444203069406041080c1922540ea9600c0d04410500b0015525004440011a01980c01e001411184244054102d001a01c9003403680c2417030b070040e00090107984104100b20070b058012013100d1708503403c1018074046907550404400f80003181d0300010b1000a072840d0340b6034120380c0070751000140d0340200e4440121000740c0841564880803541001d07095048164108002e102c94060160b103d0780141c01c2d01d03c454113039640d516201025400c600d041d41566000d00c076031800d042240c1e942c0002c44e800c00b48820034803540041d020301403c4071007900540101e41c8990071a407003a0140c0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23988369 1250 23987119 23987129
    0xb0403110706050301030b0115020a142418060423160303050a030b0609011205060a0b1303060e0d0c1b0302030f0309010305060d11060f0415050306090702010b01020c0613 75
    0x954020754892500502c41e61007848140c1e044282d600c004102e1490b51000c01d10900a02d4004019851b40c42e0f459040844a0319403a4445004004404100d0608901605861b41d2058604400b034a4030f10b400c0700700c20b11182c0c1100c8060780325404100c0000d0820b90b1811040326540b212281d00988809114500a024100802c80a140b020004105034000000e803242900350380f41401940c3c0c9210030300101e0f002d0541503e0001d58192101203445003c4e03400150400c6010300b52015681d124640c102c002e620405024020a00074101042408000c2c4682d44011038440003400c5802845800109040d0600c140548070068144003c034002c104d144085004540c0a026030b803150f1039102d0059147c0e08606141c60220b07082c000003510510300308800180d49940310002058688614080c0318998110100c0086408410040800e0001214a007200d43c0841c603640c09550303150043c20b0010041010740207009580c10104500d019070380105800500203802d4500300d03101d0201007099412440c446e800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23989619 1250 23988369 23988373
    0xa060603080316030903020c040207050106120507030309090b010801090b060d0e0105160203070203030307110a080f0301030213050f0402101205090f0c011e03050606070b0a0507030b0402160b040311 87
    0x800410030900a001d1881007500200c0c0c0034103000c5110069050300c140e580010010380108004102e589031641c090091240520000203507140c441684e08a11038480c801521194030803402003041562004a0030041c1c40c200c9410f12800c00f1a00010b0180c1c901809161000b0703440340d041034016110317101610b40c1d60004038003e1000d416a2080c0500910042d10816006130f15820b4490b000382c000000c840c50355a001c1d0003145199102d440858860442200d03403002d80c0102004270000c510707840b0140602040d03914007165294034520401600500d0209440a0282040104110170000014199010390140d59800c072040111000302d50110701c103440e0f25150f0745003c092001c0f084000400d103000e10080400c950700340c1120f5005442c10031000364146840502e26650341317400ca00c41e8010075000540031700001d0074009203640300301c0f024004590200c111030345c43c010002a9581401902e04440090b60110729007514a040b10440100006000c0c252400c0240418101482054480c05c44c0d0940e1013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23990869 1250 23989619 23989631
    0x3060f0b060a0e0a05030703020102031914030109140604060b07060b19140301050105010509030a030e01051c150f08070e060f1f0305060105250c09050705070203010f0b09010608090a06 81
    0x20340600f0024082d00b690303000740c14080c8040351904000074190f0035250160019824000b80c403008643d641c400c84003000410018900c1c48140b084690080e5010f459901c80210b40702c03500c400540810031008060030b104d5420190200b05200c100e008807045e9681200010900121b41c0e00402d404281c112401646500c24800004110400803c2d001c07030014100c1c02400030741d0340c50004450b140a4100703c184c0c5a0403000c6604006070086503060403009040c140181090320112503145410084d0180e00c2405d80c689001c0c0d41c0c010b002d24581c202920300d02c0042028141000303040342e0f42e00343e6401480e40a110390004500d80f591810070b900c5c1c51290081000c89041c01c0044c8410341c6001550a00c80400d041c10045405903004006442c2c0d4006101011035600d940c0c183c100300360465140302640c00101d0744d080859014000d015440c03183d003454407869650102441032500711520f01080e100c600b480d00480d25100c0c0e03036081116045038510300d40b0004507100e10301d080342000401000244810f00e000c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23992119 1250 23990869 23990887
    0xd081e09120a02011a06030c090d030903050105070906080603070609060e010504050d12170105100305060120010b0a120b01051207080706020a021201020705060604051906080c042403060f0b06 84
    0x5003003901781500c1c2c4070380d115014020505000c00341c001980c240c000c805040c407680314141040154801c41e41c0c040d190410343c0541c0ca1300c83d81e003120000e40320b050005000031000e110542d0810410b80d00070000ba801081ca840c80d1440040210303285e40601c0c0100b000d0f4031000c030120f81c80b510941d400b42500414007000101c2e0342c07400c40111000300901c14049918480e0b550456014101c04504940c40030b08829500c03000024210014076009240c0c1d41403259020b855680c08246501d02c038240010003000050f200380c2d4104104401106500c0b00059844040c07850700001c100340c00740303070440b0350940722612400180e0807071070704020058002c6145489104000600a5030005014141300d00960f002c002c003081c10409a403c0c0c0c85021005040c940c05400411030300e042c00d034800c82d441600031070925445c8000d001000181c42603a40319032255030004070390340400e1810380f14940100040d021000403100406982c41c041c02c0040c44050700f616034a06101000e40c009030448040700600400e42030380d8261103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23993369 1250 23992119 23992121
    0x60313020a0b07030e060406020d0305190e06060f0f01021507090305030d06050108070e0603130602040503070603020301140102060105030d0e04110a0c1a01080c0607080c01090807050d081e09120a0201 88
    0x510700550010b01c10170394083e1541050811502a03032201d0340a00140030b07034164107030090031020340004807840003203650039021800b43c4248540050601d001e4a0345081440802400000900180b440f82220090090f03080c0e8000613540c00c807003081001000b80307a84003401a2440782980d40050400e0200141c41c00104210b0361003481030300d03403d0701d5000349620740031000c50b1444035044085810140800109011000d100c00c7d02c1c0310207121f5200546815200c10200381800c2403a0700840101c0d030040014055502c0c104044a8004001e200414507989480c0000340d80f0200d06000005000607100150243d440d0b40d045421802e07081c01d9101da60350506d007002032100b01e0742ca10984070401d0490390300e1500e1400104850407116004018000d442c0c4160400c6000c2e4800441102e0411080180c070710090f20a0155401490142034001c0d154402400c005c2c1c200302d041950070f8100001c1d6400c004441c0403080502c101d00009200300c0301c4a6603403401c01443c205010715001010310001c41d19904a50381 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23994619 1250 23993369 23993377
    0x40806040b040302061303080c090a0902040603060501030f02090603041e050102070f0311070608010504020904021303050102300c03060111060108060603010e010515010507030c0602040902031501020a03020a02060313020a0b 98
    0x40f0390708441281d5140320507031a140840e81d2004002038101004101c2120035840604402c14004006040b8180d030b41d480101264000ea1041c40407175240c407001c03c82c0b5a010b100d503041c103007000a001e5240c410744400240306840018802004803951044e0000114000c5803404801d6511200840d5692418200800720a55002c0101d00090b0700c49089240e41e0b0001c104442207401d43e46070700e160359081101700b0001e50024826640c10503030900071800350001000b1094001d50141c40010780d201c140000600f0b044080c8808114030004812094813040140c00c8029408040380f40741503100c1e01c58400480e403560070800000d01e1403060741d002049108001c034041c0d00171481100208400e01e0003d00c103d0036100c3c2103982c14502400705920f10b2055004200030b10109120780b41810105100740c0d0f030403040360050b0700004c48443d4080200201d011066404042d41802400140a0b105166034025aa04030980f4000c0c0a04c1c00440820346455149211786030240e03004080300c0c0f034a40c541000c0115604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23995869 1250 23994619 23994623
    0xe010614460b09030a0b060d0807060b010905011b0204020a030603050a060b03010b0f150702060c03120907051c0213020f041701060905060a0306020a210f0f020a23040806040b04 78
    0x999000030701c140100203c600c0000041d01500c012881074a9134003070f464000346466040499a45005c0000304008020300c0320600c180d4000808208000006000103c03a4002a050200303400320004486a807919403442c0e5541101c015039118800c050440c060710959000034079510170004010104901c4d034200c914103179410b80c002c2096110303600400c110340c1c040380031035604080c030786540e0f826403402140203001e60760029203110300d41014502c9013495035118202c903441a460f8030080c8404100f05100d624000d1204858610002941c0d442da00c40240c0c1003000240b285c44000320703480550000e07405960148400383d1f06640c44a031b58910f030f060f400e00c00400c20f401551a0600c040b801610501c2070324080d00b009402c1400d124110303641d101c002c1d40704d24800360070f101c240c1000c6801c9003d0b0380f6040710078210314180403a54540049911094820030000c1601003401805004e52007980000b844218603e02240701c0410800509030711644e00c601d4000c2400d601600c0f08004c14090703028480c0c1c0c0114 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23997119 1250 23995869 23995999
    0x30206150103050105062d0705060103050c06041413060e070507020901050a03080306010f02012007060c02010e19020402130603061505190f1704050607030e010614 72
    0x6000303100110b048a1013400b075990b000304180200c5c02e4041403544101c40c2c4240da5000300010741c0b00c41d0350406c0c030351b00300000c1140c4aa100702c0051041080911062101e0741c03007602c080303040074181040c030340c400c44001c0000c0340140a89030a0280141082d0000c4c00100b50901d01e085141c01c010000034072560141c0c401781c0c042e080c40b5000080e2410310340c5064003102d4001a05a0442d15044c2c0110f81d41d19450001408646d22803c2c2150007081c80400100b440040c0b00b0300c40d68640742032038418191404c5000e100150b91400601d02040e00b80030801603030501c0c0c1c10541c0c10b105501031000030000d001c0d075150f00c01108076a94002c00c3d00ca4050b480041030fa0b000c51001c1543c081c00b41c400310380b1441480d542c0c0081103110001d00d60000d0051100c107515a0580c10b284005840031200d59451640c00c440036600c55200f0380900c05510382511580c0b10400a180090140301d050004851404100b04c018500400060404d256041e5120465042040e01503181e00c03408064034074000c0c4880758901c0410742503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23998369 1250 23997119 23997151
    0x301140102030c071a040e07050306040f0504020904030503060d0804080703260a0315090504030c020a090b090c0c01060810020c150f04020904020a120c0816050306150d080403030206 80
    0x1641c00042500c1c11444840300070000c090804020300c0c032200315510804180c10781804003045801d80c24124500c01d03c42650350341d4584c9010010070059591079204440c145241c1b500784070158448000243c0e01070b4141c02d1a9079130351a40c1c3c0c0071803050801031101810407c4042404107036110042541e108490082590368424030f042038148040039201280000c1c210020003181341c0403401713070700410720940c16214021b5141350364a00b80c00c1034640440e01100011001d008a23400c614120244101a004a00382044204800d4010480c1c041019046400c0e0540110704050035007000d400250107000040c1c20385e8910b04041e14180080d4100030b02c581401c0c001c1c2c9000c900303401092040c035482501482d2883d2981c0d2525001c1c40b02080014106903044000001c010039440300349050242001d100d00780312120246080d1103d03041100301508070507112203c060401c0644e500003062034011490308203603450031908100180f010350524400070310040e00460000281600410507a00c18908103442101d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23999619 1250 23998369 23998409
    0x30e0f010201060b0a080403031b030903031407020304141f020a03090b03060a05040905070801021305030609030a020a12090e0403080f060307030c150e0d08030405070b0304030c02011103130b0301 86
    0x20b0f40e0450144542d964002e0029211003803085004e150000d029040004558181e814289152003000740d03410040b0361615480c20404d07a051046400200c2c0011500300c031401c2003c8000e44900c92445000c981c803002c04c00100081d550042d500001d0807030080b0071504103081c4400a51a0403205da01a80801d9440500043c0c00d0030b0401200d1107404010544100c0501300000c1100411110009440c940304401c0003050b140b109100401c50034041e10303900c3e4020b910b000101894008014041d0346260014016107030415000a02e24182030741c0203d855007400040f0108542c13914041e4840e5003680380c00010701040c56040320700705006510004a0304119920442031507136440003803000501c44003600104011004040354040500080c5180010003071106030002019155002c1c0e050b07588a40c00014801003280c1040540024280c0c4020142545801e8402514a84140d840a410b019601c4650716230601e040c41290304c10342031801290320840d140d82d80148281c00034015007001140c8400b018070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24000869 1250 23999619 23999621
    0xf020f0705060307030e0106060e0a060903050307060902060f0708180d1a070210060b0405040b01020601030f1e06090c03030e06090901090f090c060206150d050d080601110a030e0f010201 82
    0x102928020080140c1481c0c901803280680c0300500040030107564907a14544c4100070301503100203051603a10300718144524820071262044507030140090000c240010400114040156140c40384c210301c0c002003d03081030020030894031450620000300d04000807040104005000070b450111045a00c1455244001d000c0c4040c03200c4903a000b81600c0e160304218510303002124820385e03212410b0701c1a036050340c00c0601d0800654080d5000248981e07000328003840a070801e4883d07402c0444091000744125490341e120610b00100c500c001a29040300b91801b050b0700e0725928445811039511040c10007003010942408020624a804102c00055075000c1001340c52904400340d41400c100101400490392800441100606241b82d22070080350b00c81d2018408210b4556145008118039009010a071030400310f40380048850328500e920841c00500050003082c0c0000e911001c617a00340c2030100c4991a0381c00107131444002c40850311200d1245078560000c05510a550114a0340203603180099000c1c50401a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24002119 1250 24000869 24000883
    0xa050a0603020d06050a2403062d1104030b01030b0a0b010201020301140f270115050414120a0b0108010b0906090402100807050906040902120a1416140301080606010f02 74
    0x60f50050f480e01412000c100e00e54000c6070081e050310000902c8041c141024903814001144000322620b0009040003030200c40c1c020300b43c83e00700080700c21031a06503054081d42ca68550303034171207049546d6410420001020400868024540046410400e50303560724000f0400e14080f210015001e04003a124a001d500500903281070300d1074076000c0440e84044506011101c2c102000c02c1e80e0000c420881e6062642e49400c4803030441050312007240d9a58100f03070640e6903030291082c80d9001c0043c200800c026000d480e51441e05191070849080c2c1c02805220a490320303100b110301015100f25203120001412703c1c015489070501110640fa02601ca40d0b5403002c200c5104400c40d40a5041800d440a0310001032007200b03665032081150a00ba4105000703400442c44941007600100d00702e0342d0001c0e1482c0c407000c60380000783e4400d100003014400941081c0200f0311032138000d0441280720703480110b5000700d0b5004810003a004120000d50546a694a2070070595030507055400701c0c08115000700400e6000d1000c01c0300c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24003369 1250 24002119 24002123
    0x2011406060d0b0301020403080a05070c06020712140c12211303060914060403090e010b0313031b051002030601080f040503040302060702150a0c02010801061106010902161502030a050a0603 83
    0x80d900b04001c030140c08010b440100580e59155500304004000610b0034000f4200540c0150342d5692915000c0c6091101d56446820000565100305401c0041c5800c54810301c014550150440700d040d408519101c0c0751030f5008500d20745c005034142c1c090260704070020306015034820608010629800d54030f01480b840c8241c452204a00494180500101d071880e0041008a449999403115a0001c119114140502a5801c400149080e0300c04c2004201400159002d4400c3e00d40442c69410705840750000c40b496100c0040520031548071011817440c500400541e00f036004801c0d130ba0209200c03074258000b176000712003080c04961103074041180c4061018015108562010086141c41d0a6400b000a00c0d00200c4080760321403000d8600103110032002000e01070070101511201a4009244009440e805058003c1801c220710410060652000010150b0442d24444030050f40c8500c2c1e410441601802020003a1254020014070444003280790b0003076100e080c01070030410158807500514820380300e0900c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24004619 1250 24003369 24003379
    0x120c14090609010203070f060509060115020309090a0605030a0501020d0606030b010507150603060204080a0302010c0302030c090405040804050a170f0a0b04030509040605040501080102040515030702070b0706060e0a050702011406 100
    0xd0503080c4400109400d8205004072070802501da550304c1101c07110314204a80d015214030a01c80d840404100882c0034040c0070f0048000c43d42904802582c90145006a9102e030320140080b0b20b01d44bc640e4815006081d01a040c2c421184203420000d02030b50189110611862511100044692180c400c0b0145403d05039649458200e403074481c2141c1540c5071121050040d920380b800000075102e407000f040142101005404404400c0c01e01a08440c0140c850809050040041140c000d481000722600d0200407680000c85844078248410036004a400080d00510325031008107404007020f04844030058038604541850140202194070307550080d000801440c0100d01250010740250b015002244000d000052490f0355000041c0c1540c1080e80039102d070340d500003030522250402100c841084200380c40018a1420a540c00030340e00c054074480c14600d940085207110401005d83c0160005240c4460300712468200301100500400c0b061360f15001662031b0030008a00c00001021091040340d000301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24005869 1250 24004619 24004627
    0x108060a03170f0c010501060f0e0306010506030606070303020403050a06090c1703030f1f0906060e0a1805060d080d1a030d020d030c090803032e0e0703020a0e0907120c14 75
    0x82e501d842e50095543c92030f460324240143c0782c145101344074540c000c2105541c0c04803048803642021300b04001d00c2c42c01d580680c208100611a5032204c1d002c03a1380103002510f00c6992000103082c101c0c001d00840d0001800b6011f100c444105020854001d21105c0d40030748800c0d17200c40d07135451020703032403505404c84004540c10910024101c0c80c61030700d04992080a0742130394200403151208080080e11960816a0807603900c51040c03040e541d22580d48000005d0540d07003010f0700c03800c101428400e04962030102607078036100d100003106a2900031680c01c545030701000050b180c4510061300805081100d42c04c0f42c0c00070103203041c07110781e01e400980c1404100c1c031900603000c0c82031071607c100c01810f07100054109101c0a030780300181c80714003000150b224006541010546111402d0b0f82c0b50000340c410140c0074115259074040c003481080307030040c0c1c0d00324401d41001650f42c28148429610304041007003240c1d001c2d541c94100451aa00203800707400c000d8050004124010307860030152001c030850f1200d40b5180780c1c01d00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24007119 1250 24005869 24005903
    0x206040510090c08030d05010e060604031a04020409080f030609060d15150803040315110a0f030b0f1c020f0102030a0c080306060706060f080706020304051005071103010f09020108060a03 82
    0xe0301100102e80a2100420400e850b102c0c014550307400310240b0707035500e03666400410255491502007500036900f1104039240902d5500e0b610840342c0200c0a550108440700049811983c8550010000a40c0a0b00e1035817607526009080c1c42580007120454000c240b4440060007030319142a41c03000c040e40c44000e401c60a120410140f00070300171052030348406411a07102203503000040025100440c4a00c9203800c20203811070080f802c1d503924060100103c030b014005d1501d0690451407503501e911081c5000030b00e580c46500026071204900d1131a0390841d840808000400c40b2045103072152900070390b003980c100c445030001280c1c2c0b03116040142001403814922040000c20f207030011a040301c1c00516050802041c1c1c1c482c442290f0541c0c0c0500c80c1c98146000030072640c20700344081001032031140061350a25240030045250041d03180d81890401000041c900c0801a110f5800d01040c1d070b019008002a03c028003d410051000c1e4000380d022520100000b2040e2510b0780100c0252644042c41c0440b41200d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24008369 1250 24007119 24007121
    0xc050d02280f050f0c03010614030703151e0501060201051f060f020f01020a0206070908030708030109180515010611010b030312040f06050f0a0609020a08150102070e01030c050406060206040510 85
    0x680401c5816809078103507403011803010081e00f032140c1c030301320040c3c401d007a40c00d003c00d82110b43e2a0b12200121300d84049848056501140710000c5941105280364000c0f00c0d00c0714800142440510719081d1150406003c41d038a00e203a000d01e0680707506030020445900e03650030701c0c054020748140007112881000c00a1007141e10403040c601035035003a4011501003010b84a96507007684c100858150040c9d210300b04109040d68420324100081030010040c5107030200700d440e0415540f005000760840946c41d440480c268240e400f22204400c3c0d0420251801242ca07540c071160b81c10001e100741800100240140140040103101c1e8451500004008518140701d005010130060302c010000d41c2c1c50590104ae00e0041503890041c10310408074540641e0380b0340707422140603040b2100c0e50080000703640f0601c004501207070850039582d04203a04031100d41c014014000101d24190071034000c81806485c880002040083c94201c49083d1103081f42d05001e8142ca40034101ea40b08022103015203258400e2307000e20008101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24009619 1250 24008369 24008443
    0x6060f010f020102040902030108010510060507030206060918031801080a060605030103020904020f030d120c080112030c0516080c13020c03070609170a0806011806020a02090a020d05070c050d02 85
    0xc40c0009800d01b5912000da42c1281c0090f485980180d441c2c0f4200003c0601001030b110140800303091075802c1055a071002540c941380181640d010311010780202c5c444204910444c1c070301100e000c08481e500c0c0688250703018802000100d0b1400b168408012030b64135461400390800303460596980504582c40c40d003c01440b800082c2050f42c0107a8052a03604c0d840d14240300c3d4250414507a115a18854005100e01c03040b034080300c004600308001d410050089070f01c42c9400500868240c506903800c0071980c1062400d00210741c3e00b5610900c5960310000b001c21021500c00090001291409240707040c010b030820683c0b00325506410304e9007040081c140041d100764420780e0b03654000d5050800d01d01216001e514151b12503070810f400705071124100081581c1c8008070041c42c000000b03408007030340c2ca8881d01079610850309100904c903401910024a5000055054814071041710009200314180100054811034907440e05a071580a80035105a6150000070f81d981c001c034103107d0301c1c1171103d100400c407042160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24010869 1250 24009619 24009647
    0x1803040302060a051305010918110f070c03200904060e100608010c021606020715020705030a03050904051515070206070b011e0803030601050a0c0501180c05030f010b060d020702030a1505040c0806060f01 89
    0x9003441401d2f04c40c03110b040a428158800c0c040120b10074103508052003032101c54020410b040e014002ca8040a441d950119504154003040205a14040342c60241c10b00c06150b00c081f8032649400b800080c508e5054100d00f40c0c1320300a40a45d1000200c10349a451918814040c20016900110041149145098669002540c6881074450341c40d00c0c2c0c80003d050601464081d40000c034042030994003071500d8440d158000c000c1030b191011041003800421040c0f000c0071801c00807058080761407410754860408603445184c0c02a691005903842d01040b00342c1c41c41c812100c50b07081311420008600395a0000860b07018450586486041c81d035800422a0318040c5c40360300b11400c2d5201d0115a441ca580070190800161240070034041250400c010b1614000b070a2462103584d078140744c11200380352180d1044640c00724810102699600c9030b0b0002c2450300007081070080c8143c2c4c0b0403008081d1801c80380c1c00140903c1c81500811481680d585965070b0b141d1094901a034004e8051301050010343c040c001060f0a10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24012119 1250 24010869 24010901
    0x30e0114040e0708090a020a050103050a02040503010f0501030605070f0e10050c030a02101a09180f030319050f07050d0903112b0807081803040302060a051305010918 73
    0x30556180c60280e9002640003070034003202e03141800316154100103481d511480e42401000b0307480701d50300000d48480302846080d0601d65140b01103640500250103e030301600340600240070307102000c00a500207103030900c401e848280c80c00c004200128450b5220b9030030855590fa6006a406c110420170600c410456261740512108110489070041c091000e02240c0400d5000b03041d8000d0285a2441900c4050b0b03000c0014140440007408142d49a284031600a911a00d8142c03404400c402d041c0d00c1d00707001000302449840023008021540400c1052120080799110003030200f0740310002ca11011500946000000c69018001c1070400546a13009520b4180685443d1030748412202e0f4031804c05802c4000c10840c0b00c400e60700c0105800c02031004207110501c1e480d0030f9017246441400200350101c040c090f220501249229960070b40000c10a1b100607640080a1a6507003115000141059000a00f0700000c0500403400140c150b01544110003210f5245803164008510303115201d004188945c00e0030404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24013369 1250 24012119 24012137
    0x906030304030312090c031b0504020f0d0509120403150e06040f030c0303090b01080d0206150913030c0227090a031d030712060608060c04060212070501020706050c040f09020903030403030e01 84
    0x101b0103441b800c0e00194094400400300c58072a10f00e50641d80c41d6900124007c500411440303081c2510326084440e000c509410004841e20381003950380c24403e511200750780407080030401000380f00c5402d101000e8001c0c45441000209115860f894640c20101da0141c4910304206292001c6802140745180f440d2103441d001642084c95540c40f40c0c400804e0b081503441d44e10160724114142d4040010a8000f1208150500d4068044000900c240c9000b03040e00740d5402c01c901c040c010940900b68030681c91340c3c020410202c2c4100c0400203d480071040a0b00540302c0b00c0c80010800031030300442c803011010b4240d034500940200061000c00c09e03208081e90350380c05115042e000141000c0c41d1410485140c403074500414031524040005142c1a0040c0481a541900300800c00c00c40d0b800060101101c42c10080064a882560134824020300170420050402810203041007500d0107504000d1003501d1612803160845030300c03510707100124003a030360006030135034030801060000c42e0103941c54078508a4145061090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24014619 1250 24013369 24013373
    0x100f02030d18020316061107150f11070b030402040b0111060103021c050601080609060f070203030a0504060608010510060801060e0a050402030a020403020d050d1d012007050607050c030c090603030403031209 91
    0x180085c3c1c0c0012150110720f10394144103807544038a0080c40710040c8001000c0c16070030b00581d1207007180c0c7c5040d00340038007114014103044280a1a0f1036207002e07009009a51403141d484040914590040702d04a1203189401a20a1998018207403169202c00400042985070300b99828040009621010a880a0140d80c801400114100100d601800941000d804941800707054a8130309a009091642060404010044059070000507241d00c04281440440c483c0c5031428070300001e00d059080031140d9401e0008101d40d1f8041e0810300012168540e840c3d030320703503030380c0c1d030f00451b5030801b0041c04903441001480b0070080c924041e0007443d044425050018901075403036001500e030052240301110160890700c0703020815504032410207107906010a00c020300f0001040000c018124005c0228407400c01d401414000d000c0405c840e80142c000039140d00e40d610a5420625510340c000c41324148603104804c008001420007010281c001d0902900a604041c21540e00b40c078104150061918020795030744403400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24015869 1250 24014619 24014623
    0x1060f030501060e1b1e1303120906030c0e010c15230112020d060903030603080408150c0405030727020f0d18050601140a0302031b100f02030d180203 66
    0xc6108800014006203011074107441d9040c020304114100003040e214801c0100c10604594075444005d88115520f049602503c1d03a034000c01032081c8500042503004410010340e03825003255110281c4a050010b90f80701d10031002d4172905940d090014800c0b02d1b100880754042c03581c8106281c03040c0701d079400e02040c62a04c502202d001d0b407541030b502c0902040d11462000445481d5015007460100fa81c00d16140e6000300c3c03a86c0c8101940140322555400002d400d00d4400d600c46005103501440195071260f40d0130100d45d844030309140140e803000c2207c0101e040c1c0007000c003c9908950340a40580307012031609490001380c2001d00c03174001800142034101c5064266520041203505110b010064071140300b074100204072132a0744201144040b404649001007480054824110344400102d030080400e1000828510116648001e402d4031540c8005c0488c0e1760800d80320302c0080010350b052140580302100c11030f20840070691034405600100701c0c51054240b10b400c50340c000b44041844034030100440d80868 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24017119 1250 24015869 24015899
    0xc02030102070803150a060305090601060516051e10061208072109060816080c0a020a08160201030b0303030c030c090d02100903051002040311040506031c020114070804030807030e0106 81
    0x1241703031501000c2c0c030348107150400700301019100602d020040c40ca06a045190b0315001070150358140840428542d1a105d65440c6d01c0d2402944882560350000710080a460f40070034607d86080d46000340e0811703118403905e500c031f03a0045a039031801016040d0416204c210599000d401c0a542421200703520100350a071000c0b1402502e0079a03640c80d410709190200040400002400c1c445080b10741101040280c1c0d400160f0365007000700c484090b650f810005205074034207004000c004144d1280801d520300f804250640c07210805000780c900740501010181055120310088403510860038040c008900d1410116000d410305400281c0342d00350410040c0c000441401c842c0c00c11000242400605104100342400443c1c1c030703a140c0680a605042c15070384c54082d0100d15400440c0110342e1600007404550b030401003002c2c1200024012050b60001420007800703000b03c0503402c541400c0324030214a1451003041c44503c119055a034140807911b515004401912598070b001e8455901c0741404109206800050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24018369 1250 24017119 24017131
    0x40e010807080706030209012f01060303081902030408120402040605090c032401021906020403170a0305070c0f0609020d02030d09060908010902030c091305060c07050c040b010f0c02030102070803 86
    0x92040c58030340b0701c40c180ba04400e0740261040500510400e68140d8001d00c203140e400340c007001100e2003800d5a014240c810415500d8507400c542c00d1507400800c0c140c0011005000b0b4440340340541c2116401034620081c0e21055500410300c440800010108807420710f00c0c40d40152008001088807681c1c1e070001155810280e41c2c00f400c3d0200002071004e11400c1902840182002c618041c44070100d1800103901c03002c030301c61004040d40004807175108110590341114051940003000030501c0100c07099040454000d2012980800d15000c04540402d002e00c03025101c95034440c00002c128086555a48054500c0c06401c91704500707102800b5006a030f0510010702c060f10076a490241c03142c031740f5031b0040ca82212680714841603407509142001580f000300d83d00010315019101c045464490031051351006201d024050814001d10090089140001c801015042d014000f00c2d142030031100c0401c422030318100c45070343c041034040d9840105280500038071040b05000400060818000b92900c011b1035100b2158 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24019619 1250 24018369 24018373
    0x3060506040b01020105010b03010b18060a0203120106051201150519020d0905011704060e0f0f0c15090a0501080c0d24060206040b070507020f180601110313120602040e0108 76
    0x10029182060b1098007032505092000788059454281000800d101c180114010b132311000548001d84081903601d8065490040e21280d511021404000d440f038108807106003040c0c0031007000061262168064913081070b9090080012646080b000c09099055000010280002030091010032507921042c000c2020450700503103410b45c5040e4005010304460b130080d6050000800d0848036078110700b0300b080d07031055202400003a4140e580601d03616041c0301400d101503d11503001da10039090404259824001400e48580700e11600c2c0b910002440d001d41440c4a80200048204102561042c0b40581e00a00c0c400c10092501110f40140760030384000e41c820498080b80703403403218100c9224084803401880f80c0d101600c09402d15030344240320130002405000c1001004a07802c07081d9980e0b4a607a40401000034030994141d0000303824181d0300c0204968880c04101c0c10088007a05070000b0080743c400c143c41d1080c913040541404508455000402d509550070b9503b8800403c51507180c0e5581c0d4060200100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24020869 1250 24019619 24019621
    0x309170307110c040e030d020a02010b100201091e0201020c040b0f0a03060213060c03090608040812010602010b03011109010906080c070203070303171f1203111e010b0a030506180a02040501030605 86
    0x51900d14050f41e0603410f5026526002d81c101e0075000120654103031901e00b15003da80d0b80103c1078201d0252078003928080c9c2c0000384040c108000c81c1c0540c0002e003024441c2c0b400c0c0508907031524074090440f10241010340035030004040140c481c6826031080e40c801400800c000146a0b040740402d00d4000d0503041121425130000701d442c018a000f800100040555203000d03140d000c03065500038542c01b514400d060500810781e011404005600055448111144a00000c2c56a484100a001c0c11094801602a519003e014030581d80410f00325030380b030300c0180c64150f4004d00c2c00324125114000108140b0b54508103005680048c0e4040c0700c148000c5000750303600b0510701054000100c1c0d000028060a03000d401d400d10900f81600744406180403100c000c07a070707030ba03000380c2e241026503448500030098140ba0080d07a1003502d40542910315980c1000c807100003080990282810310000611500000c0d203503a004000141d803030030f0202002c000c6540340c0020b0301d0342030405a007c0340903584280c2040759400c0e1600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24022119 1250 24020869 24020897
    0x6090903080c030c07020907030204080615120d020d1404090603080702010206070912020d0302010e010e0615010201020c060c1b010c090603050609060f0103052a120108030c0705010309170307 84
    0xc1e4065000403945182c0c40c51030803d00105980340c807410000030300400c00000001d505d94042d50680e80100044000d0712214a01090100000350841b0702d101d114081c3c220b6911a50000080c082c072800740303160010180c041400d241560500039140354404110780070000414001458002c00b0b0065225030b285680b10803003407001904100004001508100b5900c00030066201000b4a841e0741c1601a10003070ba0540c46030404134003400003200c419069600b00350a0000c01e200c00907185128078a40e207110340c25602c542c0012401e07849070030b601000d158041808504400c010100800d5880e643e070b8110301402036104241400d54030f00914500210781c02e98010421f058144c080c00b07901000440c0e2102d002e2030800001003803030030898074146c10150384000003075045403614200b000d00038501d0291303078520000e0500301d905640075261203041d03c10f03030303030000a104007000040d1031400c0460009414218242001100100b0303c07090103803480000c0115820358050200000c502810301d5a542d60032002d105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24023369 1250 24022119 24022127
    0xb0405060609040804060323041101120e0721020d0506090709020a0c03030b0406090213081504120809100501120507170309060904020c010c050c06070309030504121506090903 77
    0x18019409103022000f080001042c5008a50039039201d410300088080b8900c9148010240700e14108109210b12005d00007849101c2070500f401d0182603884143cbc6c0c4c800126140c0c25100c1010303a00300a5401201c00380070900e00160351005540c203404030701c0d207541c1d156000510001010b00058600740c00140500c801170078148660760140441d03d03030652920841d500c0007001030781d0f1050040d08242e51007442ea03a0507074858120704000c0c440f00c403043d5107480c0307071120075103101c0e4441c481e4104c0c41c030030315070100301191740300c0156445243c0000301781080c06c80c65541602c0d4500e0080c00300c2400d00035048034a105100741e1081c01e003c0d00100e0340c00a2421698036186240101541082d5860380e5008882c4c0c41d0241c00000702d07190700d0001d94480b41c4550118000c20043c0c0101c0040c1c04040d401d007003c052000c1d03407281c041c0440c011408211080c0380c80e0008258100c4242020180000c4d0040106101004002c0f4809060034841d40307800c5010740030f0f440701c0400c0356a2608421102074071204200141580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24024619 1250 24023369 24023371
    0x7060203070c0b0108060402060f0d09060f0606091a0304170702030303040b041a04080d0b0a050d0308040201081006090b0304020105130305070603230a1e0501030605010527070315050d0b040506 85
    0x203100000c003400d00f01f68002580500030480c03040c0a16400150b0f040c0042a41d40100c05016800b02007840030105413050400940b1843c0120000140400c4000030f68840020655400e5101c1c0e504051030741c0c0301d40d2280322058040a0b910441c1e000c0c10440800183c03010030040d8030490080f500c04840b41410700e0b0010031403a0324015000180d12010070f1001048881040701e140440d5080c0c000742c9400c03440e01180f117050403540080e07407000e004c3e00d07003030240758208103460301c203a1003661010100d540e8400901e040d400c481c0200f030001000481d092044881450065400c140141401800c2010400d81d03041c803080960012207007500145c6042010300e8040c0a091400b43c40c0800300260803a0901c004a9403000042c54920842c1e00e0304066528841c810748040003580a1071824825582c40b0304100300a000c0a01c145809618110040d217400d00160006400ca08400c103c01c40049c7c5588000320702a00b0150303050f00c03402c90070020000c3d00d5a03c030342d1000d811600c6140040c4843c030302400d1107414500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24025869 1250 24024619 24024629
    0x1403040606170a02011e0c0507080d02060105030706050306090402041b090302010f03020c060c13080d05040f0b03010312030b060c0709091e0b04170912010f060519090504020607060203070c0b01 85
    0x40030411040050780c014000400c0002041480031b094001c215081301c20b81d45250006d0b1242c0503502003c200b081d0f01140c2c038079614509408503440c6036a03c00c14107035294528410403000640500c0440c6042c0351101c4080d40081c0014800b003082807181101d102808a485d001401180c2b20000c10811540c001040c048400d1003810110309203c1d034007407a1522110010198000b0382e500181c0e10644051809008000e081075808a507240035003400c02420990090060f0319400c107810300d0020f0768084140490703058035030000c440c401440050101341d019020a00190f80c0c80b103030030b203e003007000101086017000904400001148506189c18511300c03203994102d8032030a248803103001c54086480c061038180c0156201d600c00e440c10036a0340034442c1502400d07651070381c0038007214522010030700150000c60b8103145101c800c0058944e03403402c01c50a902096425410300b41c0d0b00c2010001c0a1041c1d000300c0d40b2a001a00492034010310b540d42404030b80c021182e2501241300c03282e002080c890490f5409000d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24027119 1250 24025869 24025873
    0x6020412061103131403130e1005040911010c02030a1203090b0603060103030f0503150d0c09051509060f06120c03010e01141309060b0d050304090c0504050f040903140304060617 78
    0x42803505252004191124003d410804405c0c26080581e00c200221910602d4134a02010f200c2c3c0caa00888048540640b80841d01200c001c00c0400c0d28509071248019617036210070303034605560000005407070400300071000b40e0713050042112120120f00b501c2141041d5000642d000a2511914513002000c54405000d01e07010380d0298005200180e08142c114400c92644d05183e602da41c3c41000810040171303440200c03908040d10f5410207041280640500b01514205001401246e80b000c2080030400d0090b0020b61f4002a01008110300d820070396000c2c0d02441000e0441703403401d049407160a0f036011003603503d00491040040108049442641c440e4003406c038092141c050590310300e00080c0c1d00c0310a1a06850404d682e2000401048025800624034100c0508400442c81c20790400986039003151158400007410606030074a080d120b1011501074441c003c2c20786007640b0441d0240070040101c46001c90610060f0300039000d5001000016510a40c40340c0c01c081010317402d0a03210110447c07a140d1010040e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24028369 1250 24027119 24027121
    0x90603021201050d08041203020309090901230709030501021b0d0207060f05030a0b030d120b0f0603040f1704090b0f01030204060c150f0207050a05070e1006030209060706020412061103 81
    0xc51980700c4090446000301ca030072074000224200002c941c070803a440b8100e481c01080182c810590040064070010008943c1c0b101c01e41c0c3c8802903c1e090f181c1c5229600724600550410560f20310785400503a81000f44c5181180005450b542c40368226808804403178483c40c6500e40102103000d08100c4001c0817001c034406801564641100a03000d00e550721641001c4c000302000091000f80c042c0d00c190040800201100c54070b0074a180e000c1c00360036034440d035108240d0400380303d8919030600d0f6507860171400c0b0181c007080c9580d480344c540344404001c0351001c031030844001c00141088580c0318041c1c03016000811001034242031800800294040f0103181c0d034103050052104200f03840e00600d98030312094018211540100319551b441004140b2010490743c9580f001c5400000d0000000d621201d052142040750290358650005040560045a0366008100e09240511191303229402418003048003508160800d4a5035994600ba60441e8001d0310010f0040105842408030b140519a48198000022451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24029619 1250 24028369 24028387
    0x3060a0c090b0304210e0114030606041403070512030c010501080c01120b01030e060130110112090203030412030e010305060f100e040f020405090127090f0b0702030a09060302 77
    0x74124251090b01c0755a080400002d0922200c9040f040c200c035002e581c09407400c504c1c0c4102030256200c1100d414009442c80070b91400006d1000112030086100a00c942e05051078042c000300181550f581440d0180100e03c4005000d803107100c10f480d414418100170b541c8805507406203074215a01680a00c0035540001c80c1d009650760861400c4041c26000d60b03000c141503a50f0001030f406050501e040e042a485080f00014030200065045180707001e605103e07405005290a2400c07030005802009003070010000420401ea600804107001c0c5180e92030340c049419400d580001e81907400c02e5018040d681d0030040010304042c4d100c0d906040c059400d0074208000d05101703000c25911808965074500410340032a0200342940290540360764440018018031440040b412840d02a42041c030906000b10320240021400480001c1800e040d11100803a07170028038601500c1c88090300b0000411349140e40282c0108000c200e594410134410440e9400442d9600318102000f42081165407210b0b0030580b040c8a0707460 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24030869 1250 24029619 24029627
    0xd110703030c030503130c09020301050a0504020f1206031903120506040e0606100203040e0a020c0c1c0204020d020403060504050606120c03070b030a110c0c0108130203060a0e010b0a09050603060a0c 87
    0x60400d80601e8055102d64940c10040046c01c1c4402028018018041000820101315002181650000c0c0c600c2034900d81d56a081c0000e81c010040000340b40742c07042c4040c0010049484105031b101e14000e00311503c650b10a07098142050411000364000f030140007840c1061001030244680180381a01e00f0400b1441c3d207044144c54050181c41d0302d02c211410724408207140e01c2001990701030010303042e01084d03d06082c8140002035108a22642c8513010352400c030549450b1184101c400300d01c030303e0207180503c80240d00300170083d80500380d1050031603403d20000c004074086106541c42140316400424541c141745040000360070400c40300a400394000020307003505841c00308240c41201c50709050107489440e000000d001401840809103584403000c0366a411003180041c8030107400c030080c1c0b506006c9440d00201041c010510b194040e4041d4803640115001c140036502407241c1d4035100000080c05116080040c3d40300032568850380f0040d84840030701c0001d28007401b0300f64200e60343c1c01041000b0206000d000e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24032119 1250 24030869 24030887
    0x11e0503030702011d031f0c0807050301090f0f0c1106010b0301150503060307030210090609050102060c0a260907030203010f14040b090a1a0901050601020a03050f0f0c0706020d11070303 82
    0x904021419080194801488122041710b00c0000c042c0e650110001c0d80c120700c15101d0b4000c5c05641c9003003665000d21680a03075502800740a580d503c0c2881c41e0f0070010040041e101c012a1070900d66600d4403001c0c03803003c0c544105220380500380c0c1c0d030110107601e80c40e4861510006070018882c0b400208010401c10010b200d10f06107185013030400d184c49a450400080c1801d185d50302c0070b90403001743c000d1307454290f40c007111500c10382d0541d860b0340394400e840b14012603507034008a03403101c00081d081029070f0200340525840407515003103440c003c80781034034025228035400f02502e5001a590001005004525082c0038240e0403c1d4614410403603e81c501c6600705061300c000d030018080350038038808500307248001d020184409130084980e80c00f040c45000c800d900f01008075140c0915518000114100d903101040c0581c82d290555a16410210740400d4800c0a034490300715140310b294104001f466140051001384000c141d95000b402c0c03607150004010741108580342a0a9079500700490900004c0e40000d030030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24033369 1250 24032119 24032123
    0xf0203150130110d0921080a050a020c0f0304050411070c05060a02210d0c0804050a08032707050f0a08100903200f0c04020a080c0304020414010e011e05030307 70
    0x1080b4140320108240040800c001d0305060b14030700266661081c0e0031a0040001c3c0e601c100701c202540b441095244c030603071800c86400303000204a40302048095895810454011981070001071801e404078801918084014003084450303000410100080d141a01c01c0d0f003d2114808480c40ca40b98141d074030b00000c0c4505000740c81c030422002c40c2e5208200c0c0300708030000703c0400d0710116020304004080c041d050760b04040740088000c1e04200e0300074829807250400600551707200c4014043c1046a9517280c0480e000208640d034089050b04610906018001c1001c40307000300b000c0500701d500c2c101400c0c402403080c0b0408040c01440c4906080080b494001260b2404802654000889900134541140c50600b00f10807815180da000000e00d40b08480032920a00340911442190300310710101d02400168024821454041810760f400105001c52000085501520040000500d004100c641e04030001d000e80100f84070707a60840050000a0618600f0801e154420050011007483e0400199403031041e0540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24034619 1250 24033369 24033437
    0x10e0d1211031e07050304080a060204030b010b0a020c04090314130311060a0903110a030f0602030603150c2a010501030b070201050a06030b010501030f090204061d10050a17100f02031501 82
    0x84e0207021051041d900075040342c2054419800c094100b05011f5089400262800541d04000003400039040c001c4540201e4140c000d8001404407104120040551441c1a4140075240001c89080c2c2c0161000b032144e1403d2100850126095081101001a100c080b10740501010043d010b18550440517010490390b1100c40041e48003036580c042499a5080d910050081c4040c00c105010010141c0145100701c4041e421102c0141e040c0701300800b00c00040e54440000d034003c11240040c085030591526004110054685458040391030769400c4800076401622445400018003450650a01400e038010445000c00d01c1700038250b8039007060a070b5042c45114185561f50841c03800d0040241c002da428143c00600030044035540e000707846c104146131b4031491010364218002540e2900c600008800b604c101802ca07501207800c00000f99103084019890826078030031036a5403c4180094003504846815034513000d0380300d00f469010021004a004040e50512141e081d0061000c1034200e0404408520240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24035869 1250 24034619 24034627
    0x1311030a020108180102040b0f040303110a1e03030b030f010204260318031c0908010b0103021314030f0604120e220b01050705160608011707030303020306010e0d1211031e 75
    0x4d030312802441203038000b14803d100070544000161a8101510842e4080d03111090241c060b149480d441300c00340d15004088011f208148000c00c4e000c400a1001e40f48207017000107a21584c3d000091800366000d01002d8642e40000782400090364004426035043d900000c01c2c85030323a0124000a17242d0242148500390080140d0002000b640c04002c81c8482800c001d41680728200c141000820391800d0303005c0c18030745609240048295510074400c0b21150a00700a400c02e0f503500f00041d1309812030401c0101340e410b10a2108a504108041c0102030107a44690404590700e10742c500e001d44058048800383e0722420a009080f40c1c25851120000b82404000b90f001803103a07441c3d001682c02c0d018083c4080c03e544213591000c01d0310341c42c0100c080199155900c0e00c05441c1ea0b15401c03c0742022004070640401d0f0416002080024000e0700038581159050524286e52502c4d03070041078002c0e03070503030342640d284503034050300001c03641c010b00c202d81c2c040b094030f01a52824288004c282560061511903c1c24248001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24037119 1250 24035869 24035911
    0xa0305130b040b1005030a0c05040c02160b04030507140303030a0506030709020a030501090e01110708090a0b0c0102120a051b0702040f110304050705040501050a050108100803031311030a020108 85
    0x495400c0c1929440500e21801d81428180b80e42500400c44002d4150702d68820041068580022945061a80104900c11941c01c050503c00a45013018180301940f007000310040307946079a0480c10014003010155581c442d45941809464002154040b80401c0c0b00942c00b04070039100030048030b502000311480404c180d21401c01013403130164a94040060a4804200d1081d01036064012604031405000c09001e035a220350700140c00c039460754210681a500400c51000001c110201510f502c88000340b000841075514800350740c1030392005003601d0103a540080c1c503600640f101d05c1d049070888910202040030303140c904e0840151568000d90341d0718520011654008640c0c4541140c11030444880060028a404040101c400d8205950440f814050300901040d2410148203450407100020300c8a4400e51070840151161940500051075041104070040b51040c0708200441c0141c00e204800c17034800c60241444030030280d018000e40d00c40d4100034200400350382d00200306504282c000e50040030800b80a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24038369 1250 24037119 24037141
    0x1090228020f010f0c020c030609030a140405100c050d09080c010e030109020307031209120b060105070602070218060a0e0c0301050108090304090606080105090916170304030803040807060b010f050a0305 89
    0x102920321520344c20011203e80c0900c05800175030240030701c0e0302122064001701d01010b40702c1008480c12140740d4001e0000707a200ca441000000c1585120461072450036481d0b90100d0b4000d4201d00c50b003000b14503029220740c02c04c00100291196130710149400e2511a00f844103d64170384030b0190038581001758003054038109503804c2d406102240d074000c040711100f1faa20714141003c1c9104444540c0440d001080015005a90003c0a00200d40c0072540c00340c0da0b40c0784401134595400410b000d03039000d542402140016160380c0e84c0701e00389440b0741000420324030300740c0b0410034403001c1600000c4051402c8014070500c02c07081c0c000e4a056034004d0070f0412250f03540c41fa0151850040b58420400281000c0e40001c80305c0d00103031154103a40c026601303460240d807040c040541e148118010152007060100c07013004207004180030340007001860030640b4505540c0ea00c0e08006c1b03800c2030b90151411440042c075042001311030301c2080540c40081c24040030070481c1d66005400ea00802c80d482e801e158903500058810300038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24039619 1250 24038369 24038383
    0x10810150207090614031c02030304030c031403040b01050405010603060305030306060a05070b01120b0a020301030f0b090f030c01060503010b090115080402030102090d080702040501050f0a23030601150201050109022802 96
    0x10030f01d010007500d66138050401c0d0007000491034a02030700420000c1c0b0400c6504280300488a0415002145903850f81e640071214021502000d0b07040000d8060001300340690400214040c50040c901105194140000c003c200d86040e07105405241ca400300070000581c010056035404041194560b03101e030380c903840a40c1d062140c0e11004040300c100f80008a02920703203050801840b07000b83d403c0750096aa41da06401240300c2070001500c0030100100071800147c0180185034455024019203c03070304100d219440c51030f000300d2019a0b03203035110314040c4102e080901c1140300d181c1040b5114810380d490718a03440e480c06000800101003129003400102952400d404980c000c10f800307006001e080009050070420380d040b12100b24400c0c1d0800340002501c0c50301055541940c84001c0484070120728108180c1841c5074404020390110b2480c0c45007010580d81072042078024a40380c00c008032040042400282140c00c160406040700d0b10500c800194042000e0710044200c000c0121032042000700b503000d03868148 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24040869 1250 24039619 24039629
    0x90b0d15060203030403030f02090d020906040908030901060303020f01050c09010c0303020702090a09022404060e040608060108030c070b0a0203040b1c0903120b010903051b0a080a06090c05010810150207 89
    0x54085000200503038000004d40c440c1d4047e90302080b6664002a0306000d900c110040160301c2820321041c81f0251606080c9207402078270060001401a440d6516106540c1080f11300c800980d540b0348040062640600031902c0c803154902c002c001c2460004100c01d2a405203401090421114070003440405019504a45c419900280682c54619111140c40050204100124010f103000c0c14154801070a541c644030890440000303817800c1c02e0400c0d0044030100c4034602c08540c0551188000503035440180006800381ca4100051a92428090071203407518040341c2c001c44580702c0800c41e4400496001c020b940035203200000040c0d031000407480b8094242004007203064201e261074540800c040d08505103100e050050402400080c3c0f21100555006400b0300c0060080d0700500c8900a0050182041d20800c0000502041c3c4140d2226089880e10918081c1200c01d0f6985130502000d0010103e0304200804003403a12004500d4815000c0072100180d110708402074003454034151403507000b80150700140c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24042119 1250 24040869 24040901
    0x1110303090106090f0c02100216020405040c090b06040312080414010f0903030e0a020d020402210901020a0e0405070f030e030f070515010501090e13020315070816050307090b0d 78
    0x10030540720542c02008580718918401e45009104208003113a801000282059500500107030700341844500c01a510080d12264820318001841c030060340d03240305190050b4041c00503001d80c1d40c1001074880c121143d0000c050312600c3c0c1844104001011003c00282d40381541c5840c1039a81c0751890314209a0541c58010181c0f0350030300d5002f1405d60005d50002040030300907501400380c40e84c20402e80e0780354441508060341003030501c2105800350601d07800404840188104060700c02d4800c44184148190a480c10803c40e5000180d01015580c8411400e00e4404112410003071420081c401801d44016070362a04103140d1102280c00142d9000e00c20755401d081030714800d82c1d60708001c3c500325031500c48410507403141c1c500800020986500c6402403409803400e891858a8035211400810a265848103089900d8480c1800203a41100310903c0940211581d844544003400c0010701d01d0179800c0035101c2003081210a0040007440d580c06846030045810b03a805c15540d517182c6040d0040505a403001c00c00c1c03a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24043369 1250 24042119 24042121
    0x703080a0309020d0b06010e040218040e10020301030503040f08010b06030411031011040603051006020601051504181a0f0102060a0929041b050a0501050a021f0c030606020609060a0b01110303 84
    0x20040945c101071144000f6a00d0700c0d940920341c8200b104134050041e078611080d0360343e009160907040030340c8030600110320781d4110350b005604000468140c1e80300f40c00441d015000407404000700420000c5000190555030000d0001c40e4054021800c1800002d001804403181e280420180761024481c801c07007000101014802e0a040952104207640540b240c4000070b89080009600710f41802417060076107405c3c1e409454903901c0c3c50200648802101545411450100000038469980c184007600c5003460300d50200706030340c40c0324120514842206106002da0589010000640e81c00b01e40340d80d101307004c44d20018044189003404e41c0783e040400d0170f000e80e000343c541e42c1c002e1b80441e501c09544624842d005680215091a2040391401c450344110b80c8c00000f00c2c4018409980118054040f0031514811100b030007200d0130803003090050305414030101954415403214101d46c1401410050240f5000414003030070202c50301d03603403610001c00c1032080307595544420000d40c2c45aa9103058108020342103c0d12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24044619 1250 24043369 24043373
    0xf0306010b04061d0d0f050327010306121106030a0207061a030d0c0c061d370605030c0304050106030206070302150f01031208100803070506060f01110703080a0309020d 74
    0x410ba2060041d5804103403800100c030a03418003c0c45400c1300300d10103822411100c0156840c94990030105a040b03c0902050144003102c2c40b104d00c5207000407608503403540c41d0001c03e50024049400729003103000b02081c00d90010340440c405045449921000740da4260350380e61014640f0000380500364004015605100c1300c0b0b02c4410701c810080300720309005c400360b543d0300744948001d4a045801c840001c1541000360010007050340902620320880b5861401c40154400e05000180b0f06640b00c0f5118103100401c43c11900141110a90322440113000c00c604c0c9801c5003400c07400b40c600d01000700078a80000700040041c0c10030400303411010007154081d000c40d458040350f00d0042e48400f40300804401010203480010314560b030301c0900e24100c03a080312203040400e120503012102d03048000c5c40e1801c0e9504007400000c005000f00300038428035004034003500c10307801c1403801c1158042850821078108080c3c8080c9840c044008200348044a80c0f00d00301941d43d5504000580240c501818080d41c002c01c0c400400381 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24045869 1250 24044619 24044639
    0x30106090605090a020c060a020a02011d0a03090806061507060e03030c22060c0b04110a080f07140a06210203100302040b04090308011a190f0206130b04110f030601 72
    0x240c400c11610007800307a9404d0043c0007240240548003a0581c401804100d9114480e40100b90b82c00d820f100108200b01d01001c542c90f005568401111241c1c00a036032a014560301c80940005440001c4c00b800090a1030780001e07229101107602c3c0c1030071500010b00034003000380a610003d800c1514100b03903030b01c914044810445175081400000102d201c90141c540c071016500701c2d40e10684101d91034140005015445036154540005c0c4100d0b0081140a03500c5030550756081850001c03d2010020132081e180720604600708201a0311002c40c10700661164480c907504c1d104040c06542041c5094006031094103072880c45080e0590300c0b00340081c400000c1c0300503104403000001c00c1e00d0003682c0510400c014441880100c0d502e482c0041c0028040303800510007003940080704c0300c032000383e64806c0381000300c80c2e8854080c0c80403103c621400300f4410401440c100b501444840d5201c80071300500f002104864941900e014002000202200e80385100d604c00c035607510f80b02e0250030314042c040756003a40e100c4a4000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24047119 1250 24045869 24045881
    0xf0d0c12050d020a020102100f0207020a030819020c13051b03070e011d010804061a03030310061704030909020d0204080f0718020702180c0913050115090b0a0c0503040503010609 78
    0x65010b01031144000001400007410448150303040c1d008200340c1405040410040240c07150306030780c9a80800c4107078096a03403806010051401030b203102c0d41c1c80350f0794019069091a91412881590007900e400c004a503614540501280300a2070007203181d40c2d41c90060f052119501100702400800802802560759201005009283e820b8031075400020941000280900350810064001080000002d00086264000d2031120140700d40000a04421000090031504200c641d503900c030440e050704010b616404401d541025080560f042203900301500d00034001220b90040060054001a00d8500c41c260340d8105c0300244032540075070340c100c82c14100c0c1984881440c815090000490101c640e6601203d100311480f065004011001003017407a181d14a551800510811441d58144074000d0582c441060800c480340c44014009850b45c1001e41c0c2d03034208200302d1520001c0028040091101c4c50100303003112412102800e020820204078641079107140b080c3e8201c0e0340c15509001000880c00c607942c00c48 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24048369 1250 24047119 24047123
    0x50d0309031b080604110303040513090209060a060c03030b030a0206031602010e01020901050a03111204050304030b090d080403180f0602072c0c03180607050901080f0403020601050f0d0c12 83
    0x8400700b5045410340800203421401459810b0708040c0110b800650610100000010081c090380c0c203144e5140e001942040400203c0c034101500c80302900d00314604504419031044040301d503218860b062100c0240540326a81d401014180e407000001c0d1296820042d1041070303070380280f225940e890900410321019000d0b01d01c00700035600704040c151088a06009448228a060355003500309105031070205c011740a041c100f1024200d04000b0315021141743c00c061841107000303074019650343d455454400b61401d001441000300e90000340c3e1000d14030342d03c080ba141d04190589040303040310b0590791440e00c0fa00240c7c1d004507005d980103030340012516000704400c000c0300c2c3c0c5e038550404000c6041521000302c0e81041c0f080e0b809145402d00103101c0d171802d100615003200c0c4521080c1a056100c0721124580038003a20f0340c0300440c03000700c0c0c807070b40e0f079a0303c18849a4070490144c10081c50381850ba501070b6072660103024070f6103e8464120b584000b0303105c000b9403c1700203400164142186962700348200d40740c0314400e81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24049619 1250 24048369 24048383
    0x409061407020606061603030e0106030302031b030f18041409070501090e060a060f1b08040311010302090a03151e0b01020607020610060e010e1002010605040b0a03030e0d0c050d030903 81
    0x101c50740d00101e001407264030064091403505608030080c959040e00c416089090580e5240d042150110074416000914465002940d4a008000e41d941c0c440802820180c40d540c000c01403041143c0c20881518625036507043e0b00480c203010303000010050b2110000031074940e0005130800c42c42203c001443d004079203080c8c0720808440d8403070300550555001220542d17080b038483c0800300000c0b4841d03964610305000d20f1a140159039024120030321b101541850a96a14001180c1032040c01501c803c6d00c1c01e04002401c2c07c5240200d84c00c0400c12480705440041c01030381010303445100c0045541c100e283c0d01040d14441001081c2c03c000b03003800030b1110480c802e0041c420840002e07030840c000503005004d420304070b5403a4012450072a044a4449544408504110091702c00300d5543e02d40c84076003180c10280e500089660303401c210511003200c0c0b415080750b03c22481c001c010400700780c0014545803411801d941d505400e440d241000144918503903c241d420803d0741d2020800d0581c841c0946087d00e1007442 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24050869 1250 24049619 24049621
    0x3030605040c0203040303020615040b0306010b130504060612150b0c01051801050f01120302070e07020606030d02031602012601030b0703150510120914030408010b030a051f0b04090614 81
    0x240881c0c0e24051400011f026034001030108070301800e000e2482661030001031000c42c4652540e408207042070b80a0b4042c3c070001c080030688501d4508803d0300500a0541554208105440c0ca24000c00300580d50701000c1e080e555460146c001e00000356a040041c040030700d081c5954480c1c0801c414000c10049404002d030600444542c1d14402042c056140251502d46030900300e64213011401c02c540040c04802c070154800c6813800a89030502004542c418246070b00981040c4ca0b02c24207050a080c9109107210031504100502a0140810854112003070b80a11740b0450071500c00402c00c3d5008450380e107080c02140c0850001041181c01e000052003006540c3e024401c4c14209800c0c001d800d001e600510f980148181c1c0d0b04a603152080c100014102d150b103801080210310ba40f50103003090010746042d05240c00000d410f01200300f090103030503040306e0709a0041c20400c84c1c07034443c41c1d100c0c0b070110b2000b0400114903254480003150703504415906080200208403210003842c020380148110101d01101b188690 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24052119 1250 24050869 24050891
    0xc04080609011109190510030e0c0a031716050a0602071e05030306090408090a060201063201081008010203090706090512070501050306010516080403020301060b04060c0602160501090303060504 85
    0x2006007070a100ca4440f4050401030300300e04101ca0143d01380044281c000e4031041c00100b40d0358105407441030b16140d4400007651040c50810908094802031b1303803402007450340b02c03c0000450300d0544068184d4030f07000491701e48002c01c03601e01280c55061005009449586481418001d041d801007418500c240c5241103140507291803140290b4004070082c1460f08280009481e604011030040c1d030041c40303034183c80e00c0c0c64500800584869402e0b0071100050790743d0001805890a03100809981d24503124503804200508890036102032403080800741002a1240402d02d01b1441c0114030005e401032000035034503403802c2140e4035641c550034440c03400000c5200f83c000070f203410709203403a980c01040180507201e400c0c103040054440394800b5144604202d810401a80c444010051012800e0300c1801c560b07076174034503500406003520b9854008044010041200708400340d0001c402800c2c1c42c0c3e1084c1d001d40c40d40001c0c01400003035812000050300e19420481a103007050343c0369021034242c90081b44d041040340383c42 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24053369 1250 24052119 24052121
    0x30315010801030c030303050606070204020c0a0309090908030402100507020303070501021201060905181f090506090901020903060f0601030603060c03050405101107020d022116080a0b04200301050c0408060901 92
    0x78480a01561a44c035003d10200c1d11903000650301500c00f0306441c2c54580d0700d42c00302c2c080380e03c824204030060f00210b00c2c2c0b0040583c0301801000a126540b018044030b41d160300e801c0182d100c0031344028811070303d01096064280c000c0064909035600103007035179100c18842c10800d01035030118030054181d609400021030740c54050040358059401c05000241101000303460100204030181c410742c0800052100b41480361030000e03035840982984000428181001001c0c040d4400700600791400c1640184030000303080e04c0000e00c095020f00004070a00c0c041d102c40300181c000784060307000034183c6820500032201140e0103400c4140907520840440780344034250740480040b02c01c84e100400c404141009403401610782040441308441c00103241403811020004ca0030700000c400314502c5e034580c0140e061204550f42640f0803200500130400076101d80c00315507803001d4050000a100520641c0321200f1114050440f144020070414068020809420000d50031451600107102d801c03030358441c44000030403400301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24054619 1250 24053369 24053371
    0x5030a150605040e060a15020c131802010c0314030103030c02100c05031606111204170309030a03090807050a0b0a0606050f0306040e10050c0904050a1802062a0303150108 75
    0x1903540c40340d0403e820100748940391030b130150000e94032038205d071400324640e0200c298445075004e10f90001c12607044642c091100034003451880c2d10215161807040f07510440f040007192403259091070036100b0710301d1904c1c00761820002181d07208240e031804400031080507000140441680e000b15001c0350781100b4003c0403201c0b5550b4201c003c4c07164000344090101d03e80a00c0e05101018030414001c520695401c5401606400c01100c0480c000c21040501090090644a005020074101d440c140f82d4078054814694a01c5104d10000405545500f40d1341400014001e8801041c0d020090341c003d5442401c200c0d00621056400714046c6d89000d900181c424003c600316420000c030081201e0440c0e0b24401044010701c0c500b00c09000d14060601c0d45907000c490742c810184107140329a0707001c1e21041098144000c80d00b00030401e800091900d0303815a110f11400c0001c2201a504882003a81ca50040c482d107440a291541c4078034142c40c4108d4016202030000c00a98400c040100b0420183d129490044900e604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24055869 1250 24054619 24054629
    0xe010603052d07020a150501060e060703090e0601111005070e01021902120703050607020109030e0105040303050304020d08040f260106030305030117120f1305010306060e090a0908030705030a15 85
    0xb80e280e550031001e0018036040741c3c0034030580142e5002d4400354440aa03121341c219159110550380308014051140c105c01003085454080e14094217002032035401078086007480c010b490512003224002a074030383c8506040d11481c0d8006c416507001c4080300012401815048d9826408101803030583d0039554800100a40002c2c13009503511920300701c940070300c17441d07a2100d42c0e281e03054020041d010021580801c1030502403006a1700010300c0e00952f084c01415003c8031800c42c2e040240404c000c2010035400300c15241c0054046628140d504420701e8040128881ca5114504217101c2400010350204507030381e02c55510f00341110411040304402501c0d0b08882c030501008001c0f640a00c01408507590394020101c0b00d200003000c9503c80c16141c2c4081007160410400d0f0040f580000440071103a500100740140184802c0c2424410700341480006020039107000780d000e0107101540700042108840c0c1e000f5860154002800326601d080c00100140b0300c0d482125180f90031420011a0b0303840306031114590003251 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24057119 1250 24055869 24055921
    0x414090114030d03090f050106240302071a15030607051c060b030106050a020a02150c0d030501080613020301060b18031203040302030906030601020f07061d12070e07090e010e01060305 81
    0x240f0701040c141c00a101c401400da07501d100e03028030800000d50912512010340240704007414581e1302c0400d08031800c400c00c0c140504140c0140401300c001804261201ea61a40c1004480003e03a100c001c030b80210f007c5c2d40c0c840c0c0d500d84112014048126000401821146294828000040c0010000c6003d4458600c92030035454010070040150900c00c00282681550703910503100c081d01e140d000200301c5814a4411381c41754800017003203a40b00d0401c100383c1c88000702a041c107100c90f41c500629031783c4408000b001c1e10f1169a000d030514045560a5014034060181d10300240d844e80518942d03207203204c0c541c06506019115079800c1075240040001600c0c0708071b91590040d4134100f14a010310a1541002c0c0080d81903204054100b2001c400030f11501d07001c3c14583d540c01114110300c81d890f50040703080f5140030b03016682414032070040c1c1001240c0c21302541d0541c08540c4503078452407001c5858040c0d650002415407090400442c1000ea10948207041740c2580d6003d0025440d01c46407513000088030750702820741c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24058369 1250 24057119 24057133
    0x507030303020a050c060403020105240306040305090402040b0c010203011502031201060c0609050303040b0a060617060d140d11070b0a080a0c030204051c02100504030201080a020f090402041409011403 88
    0xd00c42e800800c102d144504d400341c142504041c585107010415a82140076035100c4081000f11710004d0f5010904c0b800081d10300f03030380e00c4c03140010030345078540079101408120000580300e1a50302d030fa8044078001c00c02035540e1907803480070450480c000c4d0003c0c06840340044400d15145881d610010541702d1008500110030303500c0e46422000d1702d80d130000c064119241925014200c01149e42400514451802104100c00900d0640122011520560001c5052003860450f02d80f80604140d1041d074400e10a91341c400491440303050241d61501c40c60b50f200201d1040c041000e0901d5070200f5495644c81d10751084400c4540c484003075070118061151000000340b800c00000d00500d5507500704040d6002207090040c170301500e44c0046082c40f43c05000c154020801000302c241141012610144004210b01e8028109030859000900c454405054412815000706070824010105803c480c124000180219507586d590180003000703041130341140d485000c2501c0000354051035080b1078568560000c0281030b031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24059619 1250 24058369 24058373
    0x36130c0b03070210060303020303070e060a020703030302030901090204050709091104060509010f0c050102130512010203040506040822030b0a05060d020109060c060b04050a021209030702102a0803010819050703 92
    0x1064200030802d1046100365403c084480716a4404c80c0b02440c000d0780a951303240b030701842c050260b082c6994040d010701d00412210a506a01080c20401d8030b81c580307400760313403503c94120440c054074507044060360051030b120920140d81c1c0c22074a0003003201c451040500002d88200c01c1034459003d40e10442000c143c042100b28590741c171604107a1100081402c0c0500c11019540307034142241c0050203000c011120080085c0120700d0308408082d9140c501500a501e50718142d690b080c0c898001910041920401040945102003852020440010304401440b8070950760304214a00e000c041e11205c01d480d141001003042c5090038480c403140d0790f8042c2c690314000b6160030f80c1200d4040d201801a100b480d56a15440e9450341e50b40280707401a030681c200961100307d181d000884c00b400c043c005468a0b4001c01c0744c0c0c001078540c00000c6a00c05054109801c09a032514003400222010203485544150412600030420101c01d0213181617401076011603020100d030355090396681083c200f002d083c0364064601040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24060869 1250 24059619 24059639
    0x1216140307020f060a2403020a0302010309080d0c05180f10080c0412050703030801080a0b010e040807020904051005060303041a0306031603060e0c0f0d02040b36130c 73
    0x41c12818030320494903401c0c0c0907070341e050802c041a10044a2982c03143e140c100500c120551410302030301c3c0c0c90741c21a0341c20301c1c40d0f002403240780d040d00c002414107454100102c28080c0304000d84442c0b02580300144179a1080c064002c0295100e0b40344a0000a42c00181950038201901d40012014ac06070250481d43d188013800e8440b118010800e404607a810040411030880b000110510284604001d0020741d0642c0307070280c20383c1c0e416003084c06c19034041002440482da8645032981160040803120b0b07059100c0d82007020652060345000394004680f10203000422a00041104580409850030089601d40000b0140c9900c1244509500a40c425400c01c1c52041d040c401141c2040000b011100318680c503903207150100c0a15403040c2c6a42d07540300b088641c000c0d803e101e07101c032282007110075510400059000501c810094140a406290303144030410250301e440c0c5540c80f44251071144070300089050b19090450b500350790019100032002c00042203268400e00b54258905901a070780c0d070251410188802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24062119 1250 24060869 24060871
    0x27060f070b0f010b16020f1309080c07080105060d06020c01090611030907060f051b010615050d0507050f0a0809010605090a150b0a0c021c08040b0903010b010207061b03050705030307020312161403 86
    0x1d5000c3c0400741048848d908611803580c03094460701c030107521070ba2803c0c0c4050401140360300418169060408101c00c6079030b2452500009540648016168113054a00300d0061908403c0207000b5481d001940d10b02c3c484260240d44210703510401c2f40d00e01511181c007150200c4103110044007040c0c1c1840454560090070000e0206201d0a000003e403951f80e614103c042c00c4202c1c0c000d00d0100300b0000b40220510030303500800e540400340c0c2c1001c61a085000101c0e02980c03196140240c1000640c90204c0c0361190b00b074000e01c0040400030020740041c1008180e100003008009516411010240d40020314a00307035038107583d000400307921140c000341103913002d0000e5040414482c00404140e00700c0080025021000740c00540021400a5110a4040103140c2140c02e001545815544891810481c2942c000420b08001c1d46000d0030340c90001c0c0c0da140582c0c4500680c00024801d010110411440a0f40000589141000d03498101019120003845600c0c4000602c07024002413905100c5a416945580c021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24063369 1250 24062119 24062149
    0x30403090f0f08010c030c080c090301180602070b150607020d1a090c0a0503060f010306020313050d020c040e0303060d08090a0306110a090512030d020a0521010305100227060f070b0f010b1602 84
    0x12403139480d20711450642c080505012100ec550105521048c000981c08069005220418205910805a0000700036004290009210710340e000030703c3e010040c43c80611808541018448000350529420542d100d4040852043c0580c088500001c0d0078900091114040d4034481650306050b421900d6000182d1303c014105480341c1c60b080314040005804100c40c8045c031810b81d0241100302406400c1006403400030700c25112503401072003884255542c524024148543c0702007215511403400010414601c0658400342240b807500d80b06003003507400c12005040d031203002c0e0342c0c3c110620344801c10007109141c01480c2114903032045c0403007440c1101c0d940c018041c40300c00b400d0550901c4541c0003d0a000d190a07940000007000d07a0004008100d010441e690042402000c258201890121292250861110760440a00c0d80c1d1010b07035000c0d102c040c212100503080010244d6203500e10b003400b12601c0750513900301c46511610400091407045001c2544c3c0c6107200f1103c3d40b2041c0f5020340030020a810041e000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24064619 1250 24063369 24063371
    0x120305070203120702090f15040522080301030b0a020403081b030d1113080c030d08060a1706150307031a040c0b0307020a06050c03010e010308030403090f0f08010c030c080c090301 79
    0x1003005070390100f00c0300008051140d0802d070b8400701e0340f042c80101880504480d1030403014000b80302c90840900242415881e040c0c0700019290344411304040141c0a682c0003d40f4076040040310001d0000000c02903058900800e044c04882e00c4012080d8100e11891202a08001c002c0c440c46041849040b10f41c030000ba10706d01102c1c10580d0b481016022102018407841040100042e08080302c03010415441c01803506c48041c2c17512a00070008603484004c50081c1d801081806400521280d40d035503e4500600850001d07480d0111006090655807441550300000c02d85440f211075501c0e1600249000569500001c80100c40c031080c54078130309220b80135004136881034662a0100d4145000d60145d8030a600d55401000800480d0034010308a4901030302c550500b010400c0180017190400e41440c0c1149c1d800001e10350b495480307090885a1580c29000f2070040030400c400003130500607004500098600a40c003c1000d029001c0c0140c003210000117030040030488070b800183c0c0080c0942c024000758100540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24065869 1250 24064619 24064627
    0x121803020c130f0525020106030b0a1127010206100b0403060b03030702030f010213050f060405061e0408070501080108030309060712090f0b04140601030506040f0c08060403020f0d020c0604120305 86
    0x10400c050325411900c81c400040c90380c3d100c07903802c50101c0b130600c0321700c0c0a0300007000711605548801c6a1500d005104000c915200d5181515412104044806114040807c8403c1c1140c80d9140c0d040c101802c041d42c2e0041c8a200c0124802c4030b44004440c0448060004c81e900d001d246d551654050901a1111036040c0003e00484c409a1003e000c10b00e0320786100400160340742c42880f01c25400204940001d400b8100010718040c5c0358032032000319400c1e0358045034210744955101c0140d20407050000d070401c1c992500814001000680054000d0507a502600d80b013009030780362000c03036a41f404110360f601400c0e0700603000f040c05580240c000120141c00311801040400054131050b00010054004489e001d40b290100018403103400280c4000f1660000034128a51444d21025902d43d805800a4010b2103002e10743c03010091080d40f1000103100358004d54a60b440d00c0d00f400ba48038100040e010215001e00e4502c5007a091001ca1000700300b034001008107041504001c3c80c101d2a01b19420200c0c00d2001c104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24067119 1250 24065869 24065891
    0xb040201090b0307020604050706020d0e0607022e030c032304020102070503010603030503010503010c0c03120b0607020d080304022b030e04021b030301061b03080c16060507121803020c13 82
    0x2c00451088007507400404440c00c20346441841c04089520250440d04a652000820360b80220900c00c001d030103c0d00c85880f141140005103254402c514280d418a04944a00d422600010100042518591020401045800015015a105a003c07440000c0a00b241d443c044075040c8550ba030403a0040c8100d030a41a105c80200f800c580341508160b01040010004100b1031900340503c2010100e2807405034031032074459402424109100d0840364545071102142c60090301c401040d00e2032560003d060b8044480b10b82000109940705440603070160140516000d400d0880c0800803038035418665600000e0106c603103084844030b0328045040d03485a002c001080740305810702003c0b09540c4101c07018503900d524262002d0324080712403c42e050f43ca1803c1185002290304444802d0348003001c8403025035113181e034800d42d554104d2108002404185081e003440880c42d400401d003003490074601c2040241644903047c2c06101004044001c0040c0d00c0005010301c1c0e828080300c015480c0c0c285000100700c0340030306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24068369 1250 24067119 24067139
    0x11030a0f1e06140303070506011a090406030f1b03050c12010906060e060907090305030a0f0c0b0c180f030a060902010504090c02101103090601050105160506180c0603070c0b04020109 80
    0x24507074054030301d0b0700da80302449104080300d0401070030030f030490040d440e00d007580d44c2e602d0f15060305210320503004006219007200e44c0c90141c121104210000c204110098580c175210380120b00b40213040c0d40000146101100c40f0a48005050907a900312000b03001040030f05040121400070f40004100d01e54803490b50400096850180c40c0140048942500c15840c048080c070148083c018203440c100318034180c00300b0101e07030b0100c1100c4a4151915000c02141d19440c0300b6030380c240c11054000c0c40524280d0400042140e07480c00380000c1011480d0940201040d4820080215444510917500d50041128400018102d512021202c5e1042c1080340c00c1c02d584078403200c2143c000c5201180584c2142c0100040c0180b10b1003016001c0301400c9881d0b00390309045900030348d030300c0d014000c0718140680050300c980c2d42c841d040d40c03181695034483d0803615189070040c2401201071200c402e600d01842003070200e5070a8030b0303d03c054030310480e41c40d030300c40c2000101030301c1e80c4180d0200500141d05000300c00320302040d03055035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24069619 1250 24068369 24068411
    0x918021302030601080702060403170606090d0c0602070602121c140a06080c01031a01081f0609030c0b0901080c0711090408090a0905010503070314010e010507110c010311030a0f 78
    0x3000c500140c50f0324140e80058102a0000e01200464000c1002c0200090b080501e030342e060303004600e5850055441c203022a207607110b03072206141e0040780c403140c1400300078402c1d41c000c05076034280d420368290a540e000260b80d100c80b142100c451072101803280569060b180d181400c1a2407803000b010559080464462100440945086a0190700c680c0213200c203501c20007221410800070b04c0c2c10071940c0c01242002015002d01e1522904200c1d0840c04201c14000d03503000f400400107101e40152181d80d9540018004417000e01c4100c070464181a8006001c901000580300a00c030107071100c0f01140d0719040c000301503601034102110010011010181d45031243e03800948520f00c11168a070b60b50752040100706030303a003407540000d0146040a00500803910081a50800c6990001c15860b54410619600380903041650048020707600e420204409103910805e02c8010400e04015101c61500c0b5400440079103a0741c445210880c0c03030400100310745038110f03404020010948480010ba4607817041220b402402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24070869 1250 24069619 24069649
    0x5061302070804060f170a0b01020a0b160908031207050703090801050a09150b010e0103020a02030904090b040c061d060702010c060f0501211a060102120c01050411010f09091802 78
    0xb0000c82c0a024498014220070004e201c00e08060050b815814802d841b80b9800602001e805611381d40440800e0340200040e84030385510281c0b444561814100582c502504081401c002482811001411880106c22285107030803842e040c2c40c039a80c4610b02520194414542141000b8042800140c0c000c030a21495000d00c0740400c01040c1c64079642840c0d80b01700c2c3c10000b1100d1b46860500d00410313580e0003045006086100303080168546d06e071030314240d0850041404650700b05090080c0202000f400c0301c03045110b148030310f02480905484207400c541920004250300482c0210f640d2103800b80c036100002e40b81141c4140741c8102c09140c0360356002d09581035100300b221140d45410042c01400340d10114295070120340603041400110359261000d00d400c41510750100c807604040401c40c203910034040010b5409882009030703070f1018103104d41402440221000d1703c46000f0100040919803082d0009d10010741e06035640580c95090551030380041c400007841e9030701a4803031001e5000685610450300c660907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24072119 1250 24070869 24070883
    0x302070306091104050601020c010c1104090503041403121305010c08073011100b0604030506010e040309050a05010e1e030d05070b01060504050607060e03040306020f030703060b0306130506130207 86
    0x10030360b020b1000380d500140c506c60554010030448281642e1040041d0146034201e503071500e00040e85804030300142003210020b4410b0100143c0898003943c26440944d500f002a0100e4407400d40e0341c00e4041140c0566452001030f0500d401040000e503120304c03110310016020700c60300c4c0c1c80c0c104c490750f85001551100c039a0007115050804040c00b00e4010803007085800c40e03107040418801d10780a049035107505c1e000c141003801c035036074001c0751019880d0007054070301944d030000480c2c3c01035849000ca2040c04004440403000540010710104042c00d00d003040e48101c2c0d2041e101e450164600b002001260141e08041070345068061180c403202c1d68007001317115841c010381d480d01a03680441c1c3c14480da003900160401400e00408000410540e205d0500311440607070440c5000401c0c84000d13640030b0640c411688003500d41800410415400300da070200070b40c0120300035101080304c561355001d016064042159801d9000326900302c001c9085c3c0903904044d9100200030801e58407000e03840d43c084201d0b0800c66043d1098 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24073369 1250 24072119 24072143
    0x80402010f0206150904140a1a060f01120b131a0103050c1305060a0201020c030d0203010e090106050303030a09020a0f0603140f04050a110402070b040b070207060305090d0c030207030609 82
    0x16503001000c414841c40306202a140c0e41c40d1002403c400c0d034a200c411107000d540c1382e200107030a121100300785040300000f54060f2240b415203030422012507130185480404120b0a2030225065140c42c0d40100c0d1900b9041e199240280c40b0b020030440103251040403d038000c03d0003403003145203103818456150395000e0250b01c000030308800b000060848000910101d0080d004000c4050344100b000e0b075030030403a1400c031001c99545040361000c90190090400c14215403002040d1011000203d40145050b00c80350030120300e1a940f129207240c20f90b6038034401c56415030800c1003c503030325001c1604151080c50000c1c01d0044165a40e424040c5403802d20b50180000a607904000024109141c214a030001036000c4060000d06040e20b07070f552074940130711009005203c0210035150a480d1601a20000d0383c12030210046441c1c035003440c010142c400c44402d00103000c0c3c14008583c260207481440c0c002c0c803844009103104e5414610a42d02034441c8481507013580326624000002402500902e912244240201da00c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24074619 1250 24073369 24073373
    0xc050904050a0204090e010212010e06060d0c03061d06010f180f14040501050d050601090203100503030a09050108011a07080306031f02120c19031113030f0209010b070c03060b150a0804 81
    0x1702c41b40303010350640b564010804e030002c903503411b14601d054428000f0b1a0000e500d41d4000520b507440340c426100900d0b4249948160410b070198060301c108c451411071ba803140c00740740c5511720341000125840e0f80812420902a110907110300d07001e03260700350b21100150200352148049005040a07030b010b4440140c02d40103500d200e0034580501801460142d0710030281d142c0c00d6a405460705014010208003950210014410300c25542d03c00b001041c018040c0e95540311740302d50040280d00180901804920640000a51191055122490300c428154298100103695a89200382c0d400500f00c19410300c18581c950030309089918429000d45410032005030740d03c0d0b45490080320820b00501c0307041445800c1c8070705200c590141c0c510107502c00040c5800980e000050b00c40b14128051048000f40480d5580404002c1110540d8031088190007200d4403d5a41e03030f244114442445504002056055010030401c0054241e4120454011000305019600c0c0d0040301a240d8035000500c071030000031904014001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24075869 1250 24074619 24074621
    0x810050d0c18060602120a0e0a120303050906091207020402070501061710020f09010302030702011b0522140d030c06140106120504051902030a120201060f09060303080106030c050904050a020409 85
    0x750940e240405104184c80c00201a4070307401d01d140b414058030b6001482c0d07130312507110344111018440000c1580c03030441d0f11110514061210007000704c010914110105400340000200d10f8403400c0c605c030080a44103a0090710480790f40020070100e800c50340030f019120010b503080c083c082c05007400100d450325100206120074905012002c051000e80c0c03040004000321000d4200300c03816500282405643c98031500c00480c0101000c01d94280341a05801d841c5250b258054010400c140c826541441114541d504450a05016104004503440c070700910340c04508021031802e42a0380a42400684581d00b5202c15050360060012140c80740c032000c0040c0107041d000b000341e0300302d1008804200040c1c43d190380e40179502c40c1c004c294605e006614204080865900308001403445500000382840b0003290500a0f0203003007140180307982074100c10000b00d010040303031040f24100e070b82582d2030340456480c20609800034001c4001ca101082020040c0800716103807401418060f00140000581d5a0300e0088964 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24077119 1250 24075869 24075899
    0x5030414011b0c0303030b060705010f0209010f140703030903020313140405070e15181302070605010501020d0f05030601050412030206010810090b0105060a18030b010806070903080a0810050d0c 85
    0x44111a50b0302e14600129240c40303000d0007074035414140000c1a01481d400219240102c5100030004d600344411452000655000f03030001d20000e882e030103c201c1c0c0c22602a5441c6822200500b0154028440c490103e48a90003020301c0902a0054a1600d2507524030900e9002075600655480800703031a8640032801d152050390341c015100c0c0b400005c081c60f2000019000d103446601e00d0100100810f142030004207070100c0d04500701008040300340c2c007051031803144040c0d005008192080c0e46031000004407540045149203e0019956800d4440f140207801906d01e41c0001c0c00d80390410100744000b00b0404241d00d00000ea150013900101780b650314025050303103440d1010000d800752609046a61001584007103809040d69003c071407203901c070115010102c0d1800020700412985400803000041409101c10205041c0c0b0b0220060312035540e9200415101a6030380c0c44000c0684004100c0041d0f428402c0600a0300f0245a1030b02d2450580d461001aa89100c420340070703034100107070040401c007522407180e401d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24078369 1250 24077119 24077147
    0x8070e01090501081e01021606050402040515030624090406091b050a03030305150a030b010e01150509010e011107060f02010506040b010509010f0905030601030614070206040506070509030a0503041401 88
    0x3400b05606000d0520b07111480690031308041c00c00007211440c40300b001c0d0140c40c0400300381525400c401f10307503042860180000361030981c0614544070220340701103030318940c0a060b1103000e4003c000c0d90315800100099412559144486910300c0c003000d42050391364032030342e0f805507020b0440840c40038a81c0c00c00d95810122882c00a0103016192810803854455882d5a0116505402c001032680d9900105804600303020ba50340e0f070302850100010042020810b1030a041c0c0f03205040e854000c0c1e0700c2c2c840310b0031841d070103018410215405100100c03c66100760b952900502040c5040765038640040b04043c034084982c4c0100c400f089440d440d440055509104403684070388100c0d0240061000b82d80040e100b0f12444c444a41000095050340c00b02601401e2604001c1001604481d09581e51b41003440c0100f0092941d40480c224400c0814585840028400c0c040c0d60460050291915064000e4a0541c002e903902900350040c2e82181010450500c00340c8001e1203000c012540310b90300d890004040b10424410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24079619 1250 24078369 24078371
    0x304050c0f01020d0c03050903070b0406020d05031b1b01050a05092e02030c07050d080103030e1e04021b030c15010e041101080709051c1b05090c130305060108070e0109 74
    0x10304560f900182c500c1d0581c499040c10120b041d11800c00311818410209034580610442c0b000040d1042054001c00445109600346d42241041410854061000750351000d03c060a401040f103841c0118030045c80e44824100e0020070f00442c582d401030035240b0445215059544c1c1d082004001c01c41445040c201d036648501d0842d5084900152409003c0d80402c0e108919030f000c000161540303180021200501d801c40210f41583d10b000384000c01c00e4009000071400550151a45442418404101d6004642d107442840c0c0182d825020300000390404400c1c000f440d8485000f0030415207080c0002d05580e04968058426100c01c01407014000c50181c0c005104012240100004154403031070540b8400000d10b0704a180b9260210119a82c0d031031a041254455442d0001a06d07134604559000e4000f48035010007414110819082d00404407184078081d04031403070400051070011141e006082c61030f01c4815406001e43c60742c40d00c40c501a800d0708491210f50154000b40909480b5101060050400c048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24080869 1250 24079619 24079639
    0x120a050f100503120d140a020a0201060b070f02040e03040f080a1a091e070306050106031e0204080706081b030f04141603080310090c1d03010c0203030417040f0306020304050c 77
    0x2c0840d81d1004055036401d0001d80209210740f02401e550048403d02c640040044e4490600c1e0080e140250f014010740400740d882d2810001e803085415080e243e005401c441d40144080a80c0c080c800641070107070304c92849010810001c6940008400e0f003401600c10070008100d80c000a1804803002c0300100049214044810704201050500051032041c8030300000f041d203d04500790070801d01e4680300e030b00018400d40c207050000c11520340c0355001620440d41304024403050082d41002404a101c0d40c0120255504800c209101d25402428030940044c00440c1d40305049000200280027a00180d03502119a401107007032005010161122a0800c1c40f40d00c0505203501ea490300c0d620f00c82d100d602c0003c002c46c0b0007000090405410f851618010a0903080600ca10766860744c0080624040303150103600080340090807042420144a144844d90180e0015480c689031380d25405c4014008911140ca040010800440c8280032514090001c6108100140c1c90b41000c0c0f801c2c90415581007c21805581e02c44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24082119 1250 24080869 24080879
    0x6090c091003020c01140405160602101104030219060f0302120f070e130e0f01140a0e192405060108060f04060f030f0b09031303110402120a050f10 65
    0x204481840e9412628004801651071003036020f401140064600c40d440c1c81c1501060920018049200ea071040094401e821401c24808002c00302074014000140c0c88202c003000c05000030b90118440444c9408200d040136501e40c0062031910b01482c1408040b00a0001000916085115205a5800f500b0190f003882e04a42c0004000b540041030702003004204030208145030f0103a212a0540c0d440540000503c000c505090b501421a00d01004101d00ca1019071006201c01880f45044282c614000c0c1c1585458501c10300d0050100c90411900c0741c014403034518510500020501c804c03e100707191038440078142804c1c98003004200c040d060406801e0408005880c4c3e07010f00b489074440b1046075100c2c5080c4000c004a0014240b035048001e0038421320b00007105110405000c1e9680070310550f28515250b54200c552612800b0301600400010700707100042c00002c1078517500c69900c00d40a48014286000088a203035044420755020b02e00540c0c813400c7c00b8100c900140b0050740030340810703101c01d4150310380 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24083369 1250 24082119 24082141
    0xf0509091203070309020409060509060105010c08030f040305040b04060905030d09030209190b0301090503030f090c091b0d05010909020109050301061a0304050c030d080a06080106030308040201050c070b040f06080609 95
    0xe5008481c520740000000c0403d03010707500c030801c003030b030040c2c4200f2a030445440d202c002003405a807040c0c140d00ca5000005950740c40b6616000e00c1585c01260181107440d00e00c1c44c08448080500110240b150500000c58005c110710040e0004203115a503240c080d519100601d404c3c1880c03102694208610480f017400503881d482d0842e5084055400041251a0a094100003c041032201a545542000c02ca801403000000203140a20440d64120200e40c0321007480551301d41e20401c6036500802d2400010f003035015480603020700740995082e00d500e0720448140c0c502c11107509800286919581d51040c1055503402904040680000e80c0200304403810812016640d0401b020030031000c080010002e001c1107c280000b00e6a0780024045406118003064003a100c04003c45050100030301c2e002001403e40c2050180b10120b98054071103980540365600110365542c00381001d521644191400042d541c0300c0c080c000d00c010120b02e5100b40f0724030704005000b420303230001601032445200c2000c18008038840c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24084619 1250 24083369 24083383
    0x50702060708181507020103060509040231020403030807020c031209060a0e060408060f0906070f0809030c070312120b0604050402090a1d0103060b0d030c12020106031403040f050909 80
    0x815902c5445040004484400080314804240c0100c503400152400e240c100000e000600c1c400d8078140040c2da02e0b02c0902c210320804843c06035000805000012501003003030a4964884440350104408210440c0c07510280da10541c0210006600d9a0802901d194103002240000508601604007442d078805904124084d0702c401522540c8001078602400b0301401249508207000307082140c8403a035034820540c8900003181c0d4481007180d549c0c00540c500c074010440354442c100c0d0382c03a480a10b095240007260b01e510028842001484104100f00d0304403000c00001004600c550a42c1ea06102140380062140e08580b010f00e580c1c90034484050f5107583c0d0807003664240c074015180162104030690020700c0341c000c0366100c55100000c00881003410510741e07908074181d1b800340c0e2003801011212002c0c41746503d00301402800186800700034000003510fa034030007420b03411244000b1400b5501d0b070300e940d04000e5161032151000c1e840040c00b00286c050360003d201c01004121080d4042c9e180c8180ca450311241c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24085869 1250 24084619 24084623
    0x709111204050d030c020a111c05060c03010905010b0a080a0207030903021c1101020304030b040f0204110a090602070b09030a030804020a08120702030d0f021504031709010f0509120909090322090b010507020607 92
    0x14004501c0e0a500a10040040b109d03810204465007410708001e000c3e1154401c1c000c0c56105c50a103000423540d01220300031508030344c44d50740d03558503150389801d6004025046060704600b00b0160000010140e5508880c1841c4002c52240c4070740c1007011460202c403880901d040c41815500180400c001186040c90344030b03441074100c3c04892804a0510018000b002e072080700c40c52041011442c0b50304140e20840d408140c1304680c089540b0b00e52100b91b00089806406031260781603001180e1803000034403039502c2c80e40091019124000d219101c0b00c50f40d0504490b00d2001601401c003083c01425860104140309000c05107080212090000e8400292a4010b030030300201ca911180000c07508251141110880b0111040d0060f101401d0106080e800303001082507a00405043c04c0125428400c085400394231910b05e0503803903243c203048400f44074003120010a01c040d40d00042c4015400e201d0310a581e60301e0058410b00c142d408a080c0219141210800440241000800d1111800584840040300d070155 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24087119 1250 24085869 24085879
    0x51014060403230106060908060f0f01090207030306030213020d0b04020703080105010f05041203120e01050c0a0e1801061115090307060f0b030f01020408010e0a02030709111204050d030c020a11 85
    0x903c0404054564030141c01d24568658607000c000034007540d104008000303658454080e911191501d00e490000094250303440031568a080c001044004d00c25401880c8540c40307400c010a08030f6498000510342441e83c2981e2031710580009008501c5079841c402d6481450040314118100b01094400400301c800c14002c0606000007001084c1107903028000b5240140310420040c1c6c0b1111851600801106020501c030302000d040003990ba80703286041c0a00c0e4841c0c1c0c148960305051840c8024101d60010421454035041094000a0280440b0382c00c1c0c60343c0640340d640c503080155091030300d50914010034250907049a6a81c0c40a05c2000940401254051b03038116801281c0b880304a0084402808040c503015458812030504450030030064014100300c44146000b006070030402605a61a08280000254107801055062010b0490f40d440000302d0311101181604000c01e00480340c0501400b40e4055510790712408264a03840d901d03020340e00c0c000142c0d101034549506a80c3d607018400e4241c86a0501c29 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24088369 1250 24087119 24087143
    0x180308040c09060303090608060306130b07030f0f02040503070e07020a020f04020904051503060a090201090506071b0b041505070f020d051c03020304110906032a06070303051014060403 81
    0x1020903429050054032200c0307410861140d51780380141400f5441d129407400b0031840400034040e0b283c04a8200e01c1407003110340f0f45841c5070341940d500a0115000303000c007003403569070480d88146189522541070b103280024030060fa0745040c441010326001c6558846200d0785801d0382007101c1e00d0360101ea030482d82603066445120681240000801a02818a20680092618007001b005a0380f0010808100d00c00342c041d110f031615002070340000e4030503803007029010440d140c8040003242041802860524000c420034554050085061090064503034040c446404000ca000d01c40720502695011141c400c03400d10f90b282040035034036254a20b212020207403140c0c642d00e031100207100090184040d84500c6c141c100d81c000c904410301a00070f42094400707940042c81c0300c4458500d4104203903c00d01412004000344200700203403040100415140c08024198940c003416510b09880d040040c0031030901c25103002c2600e05d020b05081c40844101d034082c003c5000071081524003034841d4404c607025260400d0341c41c8a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24089619 1250 24088369 24088373
    0xb0a050d02091507151b050d02070b0903030f0106020c01081302030c060d022101030201050304020d050109020d060504030f0e0f0103020a0314040f0c080115261b0307050418030804 79
    0xe004109505030071041c1880c444969010090041400318441c0c00110194112460744104039680715148542c0381c41c6c0d10f148080400d0066000d0040c601400401500c4e19405607070380e00b00ba030003d5a00801c594000b0060082007a61090300074003500840c801801e6010745000001d24804000e44489500140840440b056407002c0c8103149000a01406199031142c440b14103100a5000c68061982c009160b0300d001885c0124460a50480c0c0d0140c0d14141551955000c12840d107100d50000c4903199603c1280750010b843e081070601400380105000103007440c280c100641440d044101040c00c214060003c221255030b6224441251202841c0060f181c50078071606034014111001542404002e5104120800c40550506084544200a16201159600401400e0766400c11040c42d683e81c00d0041030004031004028010540018020000c1c0d000d4440700441c18810078040030700f100c0e8003003407a04410341010040203000340700644082248540100c1001d01d19000400d000381041044004682 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24090869 1250 24089619 24089621
    0x11e090b0304060917091201060f0302041805060a0218030c010212030c1b030705070b0f0d09150504150c0203090108010e06120d0e010206010f0b0306040504060f06081609060b0a050d 80
    0x4940c0e174440551007a0b03400b001c1c507500c625001141c0491181c1030b000c64036101d248042c054501110040b0721190916401c590030007014004080e07403860f200700102c4400d0081042040180e0103038044100040e5510700c5031220300c17440015094550f000380e101020501099a0020380002203611248000707460b511180c000224520880e000303d201841c42c003015000c000d10100042000911600454002c1569503e54035403500604190302c80080d410b0040d02003400c215003000446500c5030f10141440500400b40004642040d101550380380c0040b18100d6010044e4400d101c81042c0d03500040d4103020342230300000e003030050500584002c01d44001c04644103842e041c2c5207061680080058030005d4500303c5000305140b00410540780144115000003810307a25800c580415100038044591071070303440c2d20601000e01005401100d0721941c070383c0645001c0c0b803148104005420358038007404120707001800f4105c182e981c0707800000c00c80f0301d480400c000c0c410600c41151081210f0b4200b09884405c9034040f80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24092119 1250 24090869 24090881
    0x60905071d0406120b101e0b160b1306050906090a02040213080a030503070206060d02010e04050717010801020c011b050403140f160e1b0f090a1203050702011e090b030406 75
    0x20312500207401c0c034404011246040506c54a400403088a03c9607483d0301409481c140042c03520072030301d01e102d001d220600c0440c0081c42e4141c12511036229075240c960352168482c4080b075551f000900c5109105040000a0045640091840c0020150740c104011481d4070751500542c02481154005004040b00310900f0200008040c01c8041d00ea2244549c100030b0040e50044442d5401401410001125890201c04502606806a41c3c0100101100003071000030310000d8040404d120810030b1026519040e280c015001e002c8000001d43c80e0381c0d1a113021402c0d01c4100d2014481d03110904111000d03d58003405440c110ba0308071990814019a0203d01424120b02c0740500307032103020328404042d03c41c10300800711045032000d1104034010340e03c048040303420414028001c84100001c1003260040300c84d600241c505400c0041c403000031240d559060320b20082441008802241c07010580d0029983c00440506a0800d0f42291042490369510020003400140c000e51281403008408030341071007640d0307000e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24093369 1250 24092119 24092129
    0x13270f02060301080d17010e2e0611070501020102030c09240304080301061706090106030c052506050c070c180f0c0905190803190314130303060905071d0406 69
    0x81d030740ca58550001d191900d4056040001180c042d01c41442221400aa924120742501441041c01d0720380b80e5140d6280805400120542c0b0411800300c0b00c1c0c1c0490403114401018140c0320000c446030740342c0c0c2090030550250300c11815a40f051041148a844100481d00ea440c8212402103981c45502d200080c0e080c001036103c482514003004000400200700d00035810f031046602d94070440407066074030000c1c0350000c80e00c182c0c01007004001005100d0291f08080300d80702990426505042000c020700c0ca9200021141420700540c408185007806540c2c410290030410802c04140f801d00d5a440c1e030b0040c14024070412010360604560303503070112880d0f0f100c80e80150341400c050106000c00c06008142c010305004180c402d00c20b084901c0d00d90104e200c1d4003004c50f8034440140d4140402108c1007150046001825414103403030704220402e8600000d25a4030a040a204007401c400b4181001030072502c440c0c00203042c0030300c0c0c0424044841d07008220102d01a1a40000c404c0b0709580c800402c2c0501070315481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24094619 1250 24093369 24093379
    0x127020109030f1a0a0203010506070f1e0302010203010320030a080a05120a09020a17070e04080903010c050c01061a090607030e030f0c040e010606080105011101060305060106050913270f02 83
    0xd0715041203104951880d00301038082c00c2c00242d84030401103400300d100a124252b0300c005d081001000080e20320a0402c0518040c04100814140a01102062070300301c000480042c4d40c00401442040111242c1c810707420580840814030001a00100307595205190020f0902c00c0e000c50120300c0c9520a9044444218201c2c0004c00207081040001000d425408005c03840b403040f9990200e4107400c441d0759504184c1c282c10007002d00030314206940182d9030b801b410a48440008018050a9440034040e000054030280eaa00d580d50420700b00b110f003129120340010701001c2460103010240c500c41d8042e20b140aa048074800d13514070140c40d040d9801c5516154094241c01000d803031210b59040400c2c0d400400c0001d8809108400b5044011401c0300d285006010114000c40014440b5502c40c50b40031021554882c000141144caa44070b40e45000320990084000420003e4469094140740d000000f0b0380284100a00541d0000043d0449203052840b441c0c210400500c41c443c2171003e0314070054003040d00588 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24095869 1250 24094619 24094643
    0xa0f02040f1706240a0312020703030215040203100507020313030c1401050306100305040512132408010e06030a060504050c0103050108030a0e0d060204051206010501020708012702010903 82
    0x15068006103128582c10451a10b5140e0160840441d100d0b01c07481c1d50340d420120602600031a0416003143c00102c41c0c1100a00801200081031581441a030f200c180d001015800d165240c020300d04440c80303d58034a03580c4100148001070b2030020f4104007241d41d0041c08241561104412031035806207558550340605100000003d0007480007460042d00c1c4c0161810f0a030000e410010f5409100a8400542003aa0010307010f4425200390300454026129100b0750f0103403225034101c500b40c0e4220380b8500c006401c1e440001c00540c080c50310341c142d074100e42641011901c0a0500c3c09010b10405114400c14417003900c0000302c0f41e94041c0805841382e94040d0f000c010714102030805603622500c1802c6a4042440c0c0800407600b0100041038408000c802d031390324015940005d003407040d040b170401012103c85400340000b040036a181c079119100001008018107080d890840020701e454440c0d0b11000140c4d00d880c0c10700c0c0c1da0040e51514945081691101d170119848a88012100e40c04540d02c09400100482 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24097119 1250 24095869 24095879
    0x60d1203090309120201120b01051b0d030605010305090c0904051603030801050411190c0204060518070f030507230f0c0d020c0303040e070c0f050d0e031006080a03080a0f0204 77
    0x15201031a902c1c001c0d511552a5030716500701da8100440711101034040b4480300d01d03100381c00e0450b802c510700001061400c1c0b4246603611a00400021106140e8001c0c1c0c1c109404000b003c0b42d152250100414007468184614200b02c2501c6440c3c88001c3d0070980a0b054413000203051100800699802c51500042c1200c0240e40c1c0c00c000301503400c00c0c000d4510560070195510000008282595000e0180000b2010f0f811842c0d2000c0d81c213840f00c104209d07042a151640080c555460107010700da517509021003200c640c03034000002800b01c1a018032280c20b040c5480700340005c10b68071103002c6030040310444010158007849070200569008005110b9540140000c0c80b036010800030a40c0c02214001d038088031a48805002007507124015806800c1b00007206000103019035100c3c0001031852405024a03d1110140c0d40f9400d09043c2c01803450f0011441e6030184008030300b010400c01d0302c00c0e021010108130302401c1c0301c80a6101d9000c00743c0681003080300e201050a0003c40d5100018001c0820011941c0c0c035916 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24098369 1250 24097119 24097121
    0xf030a020a050105010506030c271003020903010c1d010c020d020a06020106060813030806010521010b040618080318060c0f061902130303141e0306030d020a0f020603060d1203 77
    0x1e5001c44503542898000a024240344080c0da001c1c81c3c40c0010542410301a10805a41a04140c0b4080480e00c507030f22040660b0701c820502c030003802c2055a0150741c1d011450140350940e500d413290320003002075956641d1000850416450354500003480e2241516580d400096052040e111019500c440f10a01c00030300b41d50158800811a20180c407464820303a22604240e490801c1144080c01080c40c200000c0c600b0341c456401461000e107400e810f040c0d549540c048040c8541401d070400510404001001e004580c0c000d903003006011410004160803e082c1070383c017038036401130341907054510040c2d424210781640d503d001e89211800c030f00212003903d0700758140c69545500c00d0b80c0c1060701c040d8a11041140360a80c0c02100c0400c14003085101c1c0c00e501e0b607a02100d81505e41e168800840c2c90070b00508a200e44020110810080104d4440d9240d083c484100750500780c01f5000c3c2d00540d0305c83c200400010700c542c21f18401f081d404407a41030301c81d17440c403010980c1943c070a00d00815081e0001c112400c150b401d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24099619 1250 24098369 24098383
    0x191802040f050102060c0409050c0c0a03120605060a0504120614090607030c030513030f03020d020f07050c12070b030907090617151017010f090f06050a02091309050f030a02 76
    0x5082003008050b40d940c401a80c07191015a07140414441c204020f1241102039000b40350448d80d540621031501c15410109428000085002c41c0091841e22481d102204180a08006800d04648072881c100d145100a4201d100c0d0348180e01120044c1180c1c94107100c01c81d480b01c1281c141070301d8818440e1601d101c403641ca13440103c400c1400700e880c16941c0e00c0018440c0c400c561003403842c05540500c00e80340b6101903816042580494040680070000c0070344c02e10560004e4000265002e082544841440c90001c0c01d004018480c1c500420707060583c02d1071a000054040200c1da54890401c0d92501c409001c941456100d07040003003440d0404400040b0280c0030290111181580d009032580d04080400c030030302844060700d82c49942c11b003242061100c0d1012103a1a55800307840000041d02050b021480005e13078810200030384640101d0481d0800f44400c50058550024001c0811840c180d2500002280c84080315031101680f69501ba42800b0030004000010b44101244220fa4503100244402540c0d211 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 24100725 1106 24099619 24099629
    0x2060423100e090603060f010b030417042c0702030a0f0e091008070605040602030304030f030b0301060b0d06080a050c010e010c0b0106032306030c19180204 69
    0xc0c5a41d00c40301408425242c03201000c001e4820003801d140001c14039400fa400801c100000106800c40880c10358100003c0f55440e0746407410105000030320051504614100002c02042425501c070116110107800010214459480c0c455550f00707040c00e4a0002c0564020710030014094082c0500da481c40c106868003003500b607440701c0080c0312000140c842e06e0b800c1c445c07080c0c180810b903800c3c007a0f4005000e1034102545024603240b002036072440010005810070a01e0b01c030084056203c5d4000096805c00140248003003a214480c0d0a941d0740b00120340c0c4e100f1490700781d0000b00a140882e800c0503042d0072501415491891200640703110000000c800d04100140041a0004009101c00e5000e80041d43d000a6040c2d075203402000d03008070401c884920300d8803080c2049915500042d001168100641d400d80ea445c211400152151030b0030f0700004c03d5040c102c2c106c854540b0481e030140046070 = true := by decide +kernel

theorem cover : BRFrame.Cov 23920869 24100725 := by
  have h0 := BRFrame.cov_init 23920869
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23920869 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23920869 ≤ n) (h2 : n < 24100725) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
