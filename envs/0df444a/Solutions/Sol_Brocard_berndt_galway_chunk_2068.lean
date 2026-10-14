-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:11.442905+00:00
-- url     : https://prove2.me/submissions/f407a69b-7eab-426f-8cbd-ffaff042d45f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371762589 ≤ n < 371942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371763839 1250 371762589 371762623
    0x20d0507051f05030406020f0c16140d020a12021c0b1902041409040c0f06050417030403030c030e030a0b091e0d3204121e03050d021b0f 60
    0x30b011102032036040c4694a000c9a402d0000c54005402500a400c40c2d00c041103103039007005080c031811460040000b180c041d017580020b0007441452610240702c80c00c2c12081ea5400313803048040d03012485003140c901c600142e246c4c04050b0390086544000041c0a13003060202400141c442c203082260300e80704182c0b121491075102c42140b8100c00034a00a90f0110b88203018140340c0d003247c3c403043c0059040000d00443e140300c410350000c182d00990286441c0540a203596158a41d420300030155940050050b000489a00510080002a920560960005505240070b200e0341d031441010030b16012451740010840d440607010000440000507a81a14180343c8800c040c00404e6120203c3c2c0300d420803180790000400114916005400000c1b8503020f400782d11040b505150080c034400356480e0000e400521184403941c03030610600c0fa15030f4180c00110350140301003406012a5402810078410001d0705a9156000310f041d1032451054074801465540b560151100d03c0d4040c2d500726207400c00e040c4280410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371765089 1250 371763839 371763859
    0x1513050108062809020309070801060b1201061b060c0804020f0a0302030c0105091810051e03030703030905010b03070b03091e0705040504081b0c010f0e130e0a020d050705 75
    0x1a40c4161070050168a002d0300568003007420092060401c4203a0848040560b4070032800113103010144015481240e40c1005842040c1c200b800140c25140039501c81a50742801780180200c0c0f41d40e400129044a001d42800c840d4603649064400c3e031466080c070007514142c9040c141365140394102080300d20070741c822909081e01074518420810200c200b804065017540c005105030115501840003810b0044004100e400f0359041240105c4000034112040c00200000050400c15414581c003405a030040a05040d901022504e01080d41c03030082c0c0c00c0c081c0c10551502403210a010003944a0603400002a06891600f0340b00e544c4503009500c00d6858480301e1043c1d0552500085240301e101c4403142503400507041c0a460141017002801c0c001d841070f40c13400010082c1103000a001444a00c15246000192414801800016020080103920307042070200b40116551141d644102c1856951032903400091940c8681d80014901141507800941000300b4081c800d00748031000412034100c5d401291040c40d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371766339 1250 371765089 371765099
    0x15200102040e061e041d072d061202070f0209070c02090108010e1005061f020d0f0e030d0c030e1302030402090106030903051c09150e070b160b06030703021513 70
    0x42481c03802e484c20f22038522041e01c041a00c1c0c41c1e000445070040c1d04800c1d030041e200d83c00160b4148400c0341d011101c00c0b0851451004940c055110622080303090600b043c104038039121000d4103c41150400c810b407540c0c0041c1c8c010403c54441d05207240c1c0d580291402031640752405003e49031740141030003039101d660700200008645c601405514204006e88002c3c004800310b002c0b801c0b000e0100a80001d600111442070918400d48040e051030815402e80d0084c45000e400580103810080d49007050000c0262050f051020b9403000101b54034290300a1402d49030070b00c05414210f581d5951640040e5101c1d51561441041c00c80a4015600a9000311500802e50741c0e100c4094003180c03100000140800d4050001020080382c001340701305d4483d940400841c03044141e42c2d0341f00601c0128122010601c0e541c6880400c248400c0100002401c00c15440c1841e001d4251084500030fa5521801404c5520045c0010308030b450612103003004660146c01ca070081401c074908582c454002c1c09200c0342250b020140020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371767589 1250 371766339 371766349
    0xc06020309101a1e1c0c090b010305060a03030e011e0306140303121803040b16031e050f0a18030501020910020c130209061e04170a02060415200102040e06 68
    0x40a164010401d41070800880446101654000c400c541e11441d49815800c0110007039010401c4507110f880d101b02880e00304110042103599500c4891304261900c01048003e0f00c0b00c2552a06503909820b1440c851109500100d03a031480c00f080140403491102010010282c068200c00300b0f0f5001c108030034000301490780c103040c0d07070b40500c2502d402d080c600306020812400e08ca01d070440c00143c8071001d0300c3c0340076262a0b02006582c030032550041203401108494081c035912030b074031203104100c01202900c076a42841d002060360040c0f20004d40801000a0f03184032480c05040039100358009411440d014640c1c1c0c0c14064000e4100311070003800340d040c51003008003041c4042035035020044000e142d6402c41400001980082d00308214a54105008001841061010300c0c480340a0080d0305140b181d07124240f9085103140a104100703071156a004090394030040e5500c1040c0c40513100452140c02d01000440d00071144081c0082901500034840d5801e48070300c5034190010810f6515021000c9065202c880600c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371768839 1250 371767589 371767631
    0x1305151e0a06141204140102071a09010506030705040f0209030712022106070c060209062206050a020c09070c0807050d1404151110141006050304050604120c0602030910 74
    0x80300805040016841c0702003c1c0b101e0799040346c051001500e0002210310f0329402c80c0e2001c0f000b602c40b10f0344100000d8140c1da420206a5001c02d001000f80024100b08001c6903070791031113001d060720035501c40c07140c0e1f18030403150341c162840190020100c880a50b62801030810f01081e5000c180e004140000100c20008a294194210a12036000820582c0d82c1c5c41c10441c3c2241c60503008440c080e400700300200c00c0f5580c000281098801200e4060494800c0e0303d40321a60600c16030000052000074081001016000724510300070504c2503400007445e941d1140301305c56a1007400c00c010400e010101e4407509022000508070101c140c1c0783c9401d1055240490315442034040c1d48184c8243c0c815601c003949009115440e04224200000100c0d4650202c108000302560500490410400b00110403c4008040c02d6842001003045040c110305e10b04041d20f50a4031190010b2000e811000350100c50f81c01180700e1910039800b150840011500c81c00e01e180001c0d102c0c414540555441801e041c411401c8003080e400321 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371770089 1250 371768839 371768867
    0x6030f0109020901060e0a0312112e020304020307050406030807030f08010f0924080d140f120c1207030c02160b0406120b06040e1e061305151e0a06 65
    0x455580c1e842e0007000c58400300002c000b5600300c0380c0c0f4140040081d00390b140000727210080352128000c0b09401a9841c0c98031007100b04a8001000301400d149001070000e48220201041d01d0f801b50382da98403400070a00c1c24406500c003a0f0060714005002040c070001070b000e420fa6511907a02d00100c0d0004000441b0300b28420701503030b0341000601c1010042f80444c1d502c03a00c4c3c6400c6011a0401e07801088200c44c03aa8080da900214850300308a0b8104201a401001c80291050700d008481c200000b0b41e03808010350096118000360a8095004584000722903016079001c45600341e9660414074101c0d90090190200c20f074460050300c614010b2020343e518160007602a52400b40301e0504092901008586031a4046d9682c4e0149a44001551a03a1103031801440900880c014113911401c1c4013181c4500041180d1181070400c85100600c0f140d1f640b404201c1c05c0d40010b080021a664031546220001c100e540c609641d0f0003c01c0244c00440380895031314800d42c40e4070481c0c200c551155525819160361048a00c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371771339 1250 371770089 371770099
    0x6180510060813050d121409060c0703020708010906150b03060904080a0e0603011d0601020d0c0b0615030a0606030e010902030709090305130e010504060b071a0a0f0f0506030f010902 80
    0x1400094802d1034180d03442034185041640c02251034440c1424008501d80c0c1d080010715400d1444d00756190341c007401d01c08012086141c00b5070714114600540300d86019140001290002405c10145442000400040c07c0c848008200c4180149070520051207020002500d00c10b803400c0c0000c01c1907080b4180c1e8464040a400d03012580e40319990480345d5400740748220280b01500307600801a4407102c0255010f4418902000c092491180b40070b2405200201014110340c42403080b03084082d4440800c0f0f1301d45030b111114403900d0300e88000050300c003902032803201c00c0c105004c020408900420f821a40c1260721989040041c074a86800302e41c26030303070600406501a03002c14410002c14035668420005180a41b4096081086500503d030340e00d4407079030080c4180c445d07150061089250074800c00001b00f2240189925185051b0349002038288a400321009019040c2e001600d2100c03a03410105408080d04c004102c2d1441000185008000075580300e400fa104940c21071442e0081441003110003500100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371772589 1250 371771339 371771371
    0x3120302030c1227150f040210080421120501080d0c170705031b0d050307120203090a062d0905030906030903070501090c03021c17090604030c09061805 67
    0x500c030350f00214082d0501044c41055404110642c40e40b603140500340001c1000b5188281c40301500c01c0c00c0880150074611071070405010305c0300582d603c0c48256510906414940007a585030301f0400a0406580e028090f24001007039038040300c03079000340c2140340881018820841a43c941c80e156075070b03030020107007078010814018081000c00c0700c1103030342c2030038803074100d81285091f00741e82d5070038196003019640e40e204012480c000c080e41241032003580300304082417420030b0031482c110000410140440401000350b03503000000c83c02c40102841001192500440284031881005221101200d0040c1c0107040d1281e207180d07019071451103802150202a0480000c60410680d4001c102c8641c3c4041c002c40440e100400504d400118280200f0032194041d006414000740b542c01800200c51602c001d5109040d080030319040022003822460140d50225201300b52903003601d1002c55920300c120307000946903d800001c0080c48408a4001030140d0307030b0640c1e1030915440d000d94101c080c3d81040da04c3d9280065504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371773839 1250 371772589 371772607
    0x306040803092407111c2006040b0f250914010503010f0e09032106011403060922080414010f0c050d030203070306090207050607200a020f03010908040902030103120302030c 76
    0x5465401c11000080c3c1e054052000010305252a4500b844004140701c00500c0ca007c040c1041c080c1c044a810b1800b41070545810360718000c030250010100c44e206601c0c5800300700d240c041440340801c000b00211503441044d14224000d0301c00c070002d20078140c02003c1825188040d5100700d098074101c4a040004204a0b030a04040300d40d04500100308540034801400300200d0ba02e0704a030301c0b4150114000f003270103240c200316000600d0000001303103808584c1010011700c5903a0f11034602003a80088a44848548040307a02e007030091450a24101811070704020401140501c0c12000805d091031090304c5074403e800000c0d9040e100048407500103401c9401140264154500913002558441060300c1c00050442d11020f8400490b0000101075400d50300a030204142d1980100022040042140481d00c1c07041104400a80d01c0c003107032200a01500400102c843e254400b50400c100d000d50000c861602e171034440d81054001c0d00b01344402e951090170b1042c000c50b8640a442101e0061180000d410f140000d48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371775089 1250 371773839 371773847
    0x501050f1f050c1603060f050103080d0e03040909050303010801050603060c0d0f060b0406030902041a100c060209210c1e010c0c05030d0f09050402161506050306040803092407 77
    0x407030358070310602104014255451106001640c840e40c0390401c011800c41c107608190381104c0201103200c41980c0340000500c08903125005807074481d200c1481c04992214618151070850185520010303000d810105000704010012020314103903030445000300541e0740ca1204255131118282d888850441e0308014134454548250003922400010700304c089620341d518910410160b01c20340c80780000076a03410502c4218a0f09000c0c0124100320802244903e00710240011142083c03018140c00f8009080711080801c10b503034040d03910790000102204c2098aa640000b2042008180059a82c2c06804152007203032500c8039005400a42c010000d807412540c1c54015100d000168005450100c181c6000103503e42e410004100c809081d07a072012a51952008040d03c8c030030040d04120b02c154018401031410240d2070209902c00c641102c1001c0c115031448000728020403880d000140c1501900d0104000d000c010002140a001013404075002101100e41041c00074401d0309126a400c110100491001403203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371776339 1250 371775089 371775139
    0x504020d08030a06051314070e0f1306030b0c0405030f030a0c020f032109040b010e06070206072603070e010807021e160e0916030f021504030203100b040501050f 71
    0x5660030008811740c441c0000380c071460084803405000740c1c071409900d0015007810100c64004815051080341002c01d20700280003d096003d285000707281c6049034200088041d04414015030300443c0f40341150801c00080c00c100e610034050305c4c0c003900c104004500400800021601c541b445070f5107000144046508000b0403408100b2440c0d41071254000400540d8120a1031200a260000107285c0c1da0700b41c501400240c0d400582d0642c14003001d401207848580700e00003100c000541c111085036a0321800d140050440b00406040300b030609210b4420395410040c00c0045000310301036200d181c1d1401e10000110b40303041044408400507040800c0c0448a04032142100002c00420700540341034820740e01c0503040c80b05e41d41c2d114408105480c41480078007002400001041e944c000003400c04541591100e0986a000060080c050040c01281070308800c8101c0541d07000e56401002e034ac1101c50340100c05409400394a03c15407250385424000200c0c0d1501c450303005030820000e4003042c06100039014819042e02c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371777589 1250 371776339 371776351
    0x12070b041a0702010c180501080c0f0c030403060212010b070f020120101505010323061309060f05060a0f030b0a02040e0c120901150b0a1119150504020d0803 69
    0x203050032030301d007095540080303288a5a45076000254000700702400800d00c1c030041010310100031201c503061105991000c280c4e035004410342010303a84e541d002c0170302daa118400c454110301e0600001c038003c8104659074004110505a0a10480099032199202400c07842250350003000120301010a90055000760106070089071304103569132860254044160030280130756039100301166107001c1031500008014060b0040d050070329080040c4010600555003041d00d1030003440807004e0034000a59555149031000031200c02180090220494515084024100c10080c01c1c40380c0c1d0500c4001a0179041c001c844130100c40000f042e041d14a032650312134550644000d02070104840d0201f001154002100509601442e00d103408150b94045030300081c41920f601910a42d081e0341404001141e20080c0701c484001c3d01c1c80b81c40029907030041054261000c003540c41000d2b0650244280c0c03c4e00c401401425074098074007920074141c00e1901c81c21081d0444004550095102c49848002c50205000501440c4d00038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371778839 1250 371777589 371777603
    0x50913110a090e0a0b0903090303070f1403040b27060a030c0302160b0103050d0201061a0d1e0b100318030e120f011a01030c141c06030c030b0912070b04 67
    0x94a4a1040c02500d403030324220206541300004903402c1042041c0001d0303200900390b0145045c400d020380025200d04c15000040d084080794013208042c000d410240b03401c90300e226021255903030381e140050700182d000f003c00105028001d503a03c9401e8030138510000c581550040c41c0074a070140204040e801032903004000b204069082c44180000c0e0400e0050040c058051526181203616519049140031040c118040859051290401c889880c0030030002c0885001d0a189031201c0000714048011b00104a400c002802401d10050b590310b082e0380b0620402c1c0080d82c1004190440078400d400360340388c181c1040b00a04d411f149000120384581c40c1c0034002540200740040841003090640c0c580030b15605019506e0355503c4801c03100c50949942c1c416801001e080901c040505144040c1001c41e00e00102861008009490018480340d901c906c1541078076a40108241c40d2682403080000b0071900084a20286400100b031200f480058089071004440900500d84800755458a01f41e003c003401c115060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371780089 1250 371778839 371778859
    0xb1003081b07060908070302010807030b040507091e08060a0507140301181802030c1002010b2709010b0901090b0d0b0a0b03070b0301050102190c0f030311060105091311 74
    0x510004000d00105002036808192280512030a074180034242c3c1c0b0840600040342e800f00f000c03841c045190421640c0900703003106555a201c45c2600944007030380113240c6c010318200411581035000340254043e600d00166120820100403801c0601042c1e9002700121544841c000518009140d00110ba200d1441d00d8407500e0500748000c5041a600b081e084440d0000c80c0b445140304180c1d862048c10100c110268400da0202c80c12b40209454048020f40c01e402000090f4000c07010500035006203101d030b24050055680203903c08030032000c4060340d502c412005410741010401e012030501039920882c4000f0400d0031a81d1921041304000c0001d4841d842c1c00c0031300c00386100e02240040d11038034400c1c2d064850124001c0390541c10981000025041000c440c001032006204599000a40502001114140c02c0d240071244c18078480c4900715500c441c034070b42c481110201c01c06600454845098100c0800c841ca140d80303c1301040740303590301154640006a17200010b44007140101d1104500314201800350485 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371781339 1250 371780089 371780093
    0x90c030503030103140f0115030f1403190e0a05090f040f15061403010c080c070c030609030201021309050403022112090f0c0301090c0306050c040905091005220b1003 73
    0x25a00268410341d40c0d00d02007070424540a100303000d00c6e00d201b9070030402000002280c000207808136506000203007209a0a502d62010007140d85e001100c0c8005200403241c4441940c260051000d10320680c2ca8005030200d00302c80e0081c1840742e40da03416140300400c0d02151399503000c000c00d0050802001130742c814045a03048030100380120300b03c01c540ba00600011915505141c2400440402d8040b40780c040d80c074106180000e650300611903504508500c454035a200320364141442e161465400c0946918a00328454042540560051811352989d4240d030382c0c4140c2c1e030b800340e204851040b100035000d82c01c0601500d43d03d074074001c0c881700c0110f4181250341c18044002004540c9102c12520a4038541c010034912807413060404c110303400405d04400a00a903909662009002102403000621207a194008507034144e01c960300759000b800c0c505108000078a8440c0c030b91a520004c2c42d001801c001d10740004560b0742e51030741120b420a100040200c0c0a0a291942c0e55800f2120060140c21180c201e0b40005c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371782589 1250 371781339 371781343
    0xe031221010608041a071202030c040902040e0a06050a08060604020a120c08072a0f020333060406050603060909120703031a010e0a060305060303090d060f0c02010c12090c0305 77
    0x10103800b441d0342e12019850586401c0c2c00310200c480708100b05403002c4081001c02c0381e1140b00407820f05e280720400b680b6601c60307010801160103140c214002560010034049203101c002d0b070351076110314100300080c040d0650b00c0061189203400da002e43d207526001031000a100d0b0806800400c0e0543e0b4a10704505c02c44581128581110804511580080c074003400b440003032a488a8900a10101c0c254403d1480301c4100a40b62030f040036040c010030b0034000316503480a66405101070750109500521610000003080b041403002a040c580610300107034404049141030500d480b07180155040600a10b20710f4403040204001d2003401480c042c01481800d0190754200b50700d101070a003844c86034401190000a4079043c07170885410681d06030412541d800d0f00313551360b0385880c05601194010f0070002500d80345c1501190031032017040315954000c1070031090882000510380c04481c0f8814901402c000c4070100c01c2c0200d00381c0e020743d2021000600f0040d502001c0003a1a4480b10005102d507682425842c0e482d55158 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371783839 1250 371782589 371782591
    0x1503020409050303090606190e0604090b0708100f0509010905090a0c170712030e0108070201180c061b02061801020a05060703091a0c04230429010e031221 68
    0x80e90b640010041c0609605c0400144c1e42000c2e0072608001040034903106d1034040c01c9684070700341c6d81c2c42040021406a49a81c0d0003e03143c11f4010030781901500d444480600300800560702d42e8280c126401c00001c10400401b95030f03040d100000d1030100c16901e8410048040e00c8054600c41580c0079803602e400010320b4141c00000108511406036000c50310803503003e8100b04041d0300960150100b8010180040e0748001e800c1d00d035010074208024291505c0c08104c1c010000c40039001042020f141001b000c2c4040c4003003da0403030300d039a41c4120800e9011707080807140341c0d00a6030003508842d0500003840c400341002c044080300b650610407a1000e02690700d0b400d05c1c04a050f00c0c0ca201080d5503030064002d0081c5080108401484a07071803400505003401030f40c42a05c51441100d0b1410503641260210442101c070242c100c0d42e00a1003481840990000818145c80d8402c4000b00700c009454043c1540d4059050300301c04010080c0a011101c101c440c00a403140c0c401c4010b00032000910040342010300c00602d100e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371785089 1250 371783839 371783843
    0x3070902190509040e0d020c0406090905120a05040915030b0a0c020714040e01020d0204090b090403020d0f03140703060905060d080d09050a081b011805061605130602010f0b0111030703031503020409 87
    0x8c00c144246c2c0010b0000320b48080d0029105941802c69040120324009454084011090205075031004490000c42d02e60080b5001901d001d41440c03102002400440d0640080d40d0103207090641a898188a283c1100c165004940160300840e034200064140d1403150071090750041c00100c0c0c06d4000000740d5007203a1100b400950103a80c04102440120300a02c07401180c090f007a1044042414603440c060b50760000e2003404020841511a14013040b44603402c180c0e0440000b6104c0101400c0c0564080c0141115000d10410070b031600d0001100c1e4a03004c041c010100350011415450700c005441e4030302c080c0c44c00303040039a103d119900c1000f0010b0521401007491400000c0c100200d0810351a03101c1c291000c10708003450030714007044d5450200b400454501d80184142a40c4046032080c02419211405441c03120541000240301c0007990079019008050f0040c00600d04100b140e041c1001510240c80290b15a00107a209010140010740654407c00900300000320301c00c0320a81c0c0e9800038055175013404007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371786339 1250 371785089 371785093
    0x304180c03020705060a15050907050a02010b1014030c040e04080a0909021806070f05060a1a151e0f2106010c02102006130203070902190509040e0d02 66
    0x4411008a118803944144100e580340030b61038011a40c0314183d0f194801740c4245c1d09540e840400510041916080c0c400401d0082d10030030041c90184805040ea070410b600b0071002d9401c10204485524100340301c001440b500d900c0b20f5400c4000384241c50801d4000a00b4061072540410001c030307540d00314000e014865480794030016961441c01000610280d140c2d84107440960050141e004021054020b0510080d01941d990707445079000d042201000f8031840010b0324034002c0100f408030310301268108003810842e002c20130407446465024070500c4e130710155400e103c81d5414411504406c040944503180c45100030020b50078036140b41070741240c41d4444a411144440c900d050200c0c22500b090800b68014003d00f49100c2054480d0003090114103181c5e168000c10403407100622000d80e0481288444a42d110300700c8842e882c06e17042c008401468850140d103e403140410005e86106540211094944001e0b034030b810214901c07605450030f030002070600ea40141c40300780111099804201d10b10004ea49580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371787589 1250 371786339 371786369
    0x24010c1a010303182102190906140a05130203060d150204030b150a030311030706020705010203010e010509070e0f060912010516051303020f0a080f0a021305060306060d0204020c0304 80
    0x64050b100102074904248a48890141009241403800301208000500b0380d80c03070266001480010343d0380c100c038050b142d01342e40007d801098030754803503000d44143c40100d095080044036080170000701c0a800c0c865280e1100510b601c00811407060f4001e1754004101900303480c885203140d074803495801440c0041504041c1d01160400c20300000301c80c03ea40200c2c001940c1c3d509410850040744075070805002c00380a101d8914940308103000c0c108120b500440d0401000c54036480300785000c9010754400c0c0f14940ea60300e682000480c0030b180403060280607020311380311042001e80035424007051403203c0601c0b81d40454188214002d90302c0300541038144c8e455060000645183c280504000800302203401410808180301c0f000c2c0c1da000c10b410200030343c1c1c1c0441c1e44240e240c41c000c0c0002c0d80584580c00a141900075075094075405c0400003504a03801d4800c40d40300b4110112101c95004864049400a92541c481030215101d428a4900c440342140060005841e004180940520b568060f40c000e40004050721 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371788839 1250 371787589 371787593
    0x7030c0510180308040507050604060c060605010527013509070b0f0f0c031b010501061b03030207050a02100f0905040c080f1008120301061724010c1a0103 68
    0x400708038111810314100b0041d020001400000800200c4002418480d0410104e41403080400c1210001d010040450751384540301d4000800554180718215041420b04102103480e60084050b21846543c102d900d0528640c035800c1301d071440e62004003032414440c1e000281c105000c51240659490401d01e00f0b984aa450200e46003880004d0083c15643c1c0c42e040000c042c410107089030100d90810708406e01007615220810720424081c801d80e00d940308580b100003500040040002c201d03544039603282000b00402c1e0b80c0c896080d290010380c5518503074204010181000064000d0b030281c40968010800c5880b003840300d0b80420245129120044003181c202600341d94440c2d8080341d1100070346030581d82800315481d80180900800405826008400e0881c0005412a10404104d8004050a0040b56105001100200c0841c2e000f0700440000840c00401c1092000c0303860078075400b0b2150660040740c03443c400c58070040c07505e0070700c045030b0b04001c411140c2102068502c2c02c041002d00c8882e46054242d4954 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371790089 1250 371788839 371788843
    0xc1207032318010c0308130c0f261204050d060b0d08090307270513050111130803070f0611121014030f06040210030f05070c0507091a0f03070b07030c05 67
    0x20b4101410010310240880000f0b82c0700042a070031503042d040d6517019680c2d07460081300740c11b400e40040550031440e2200062510740101c040c0095480150f21940601c42c040b42d00f030321510040040c81030b00004010412035400c00200c04040140120000500d01260000040c6021a901c006807600300003c200900d151500384003600c018207050048030b07684901e0424440c10300403180d400c02c040c540d4407030001c0c0e00001c8035449602c400d035000c402041141c0400c2115003840d04611400001e0f891800c10104207c4800070840302045e0300410250211680c560f12031000e0151400c103c03500c184140500c0b0125004988102d00074181023443d140c54a0034541a525140c1c150180c4900c00d51080a0171808c102010130400c1d085038054038030451180c600781e0250042c2180e01c040404103460f080030031146950080d64590310394032071000d0b20011a502c2c1d903018103503944d902008801d05099000d08000c0e2034800c10024014401074152030342d0320381c0c80c8241c080035005098140c1c081140111180204282 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371791339 1250 371790089 371790127
    0x2406030e07031502280503041101090501021506030304090207111504030b0c1e040608041406150609130e100609050408070b04050f01061503050109020c12070323 71
    0x14010041042a1443c1c46101d207842c0a015a4000207500281031600102611200ca07040048294111800d440038000200580d00c1214140c1d048007800c4664801507204ea200c240844030160700070102200c811841000441c0d014241590502c0108070004800600d03001414280340a2682c07120303a0189a0144078022682035400300004200304028070003d0480594075400c0180003500c5a2540750688840d002c544c0c0035a030b4007002c0c1501040c0082e2040c2e2081015124a10411a15080c810302100b151303070f0744405440e0340f0010903141050103524144000a40990785000f8030841e150351a2044c5002110b8210181d907645401178118560200a58008d0708000d19080504002510b015242d440c0a0b00881c88014481100305011405002d010045420b04000c060000c003c0c40e90b035203004403900c020b030858040c0800d003088000110788410f8800da0300b01c0d11082015003015420514116401e6008401c12803d20003452004910140f0f081c0e01c10381c60f01408031085503504200b0400610b0600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371792589 1250 371791339 371791361
    0x120c051002041809050a12020307060203010f061706010807030e03210108070b070b0403030b010c05060106120b010206060d0f1401020a0c02040b0913140f0a050c1f0905060a03240603 80
    0x100701284040000c000082c403006e040d8008094480310250100d080b4214400c181c4041c12581c004030000c10036800b210019011a82c440c0c95004208820030031074842044201d071614082400180050182d9009400800454000c2c00640e498003102c205980d83d20440e01c1d000c0411012140014006240e0802520021f0280302407098100074403542c0d2070f40c0d8400000c0004080584480002046901400c1c180c400079911400762600f642c1c48550003400545800746003940c041c10007901980c25400401c80342d0052801404072140808180c0ba125001317600e00f001196081c06004080740b65080a10151a0301c11590351202c141100d00e00400c4241c6180314046407090f004002800307400c1404401c000c0d01039a0140410148542d1544414100741281d400b102c0c10340500321f04032042000100d8061045182119005c1140c3c04840e1401c52001c0c3c1860044045400b12406105614080020380f40c0d1603054540440c41c2209002e01011141010174024003c84102d00c0500205c1c4d09400f0380c0f100b0030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371793839 1250 371792589 371792591
    0x2210c0d1106011806030204020703020d0f0c0203100c0e090405060106090905070e090907051c1a0903030c13090e0606040c030b061e0915030f010e0c07120c0510020418 74
    0x40c500c140d1542c540c1010f2040c68101d02202240e060044002c0c0c00403402190010803c40d212800c0d42401380d00c3e242000c07155000502c03201c00d4081d809000e0102d1024458001c1c1c01005c901d1f0540381900f004100020400e0188602c0f010364802c2551040790716807003140b04002402880d4507100010707041c40065002100c00718240020401520307480403440042c6003040b80c201206071035a407000350078a0000e0b04026000003454800a44000402d440b9a02c07145c40b81c03010440d458060b1291101a480903100d2600540042010407021492580584202215485e03ca145187e599000f8412100350b40c610002c02d030441d00130095207142500c3380308845290b60805128601e020300c0020603500c21507006815680740c800c01401407004a41c241c56416401810801911003082d1460700b69802c1200c035074040e1090140089401d80c058440385001300304207500300c0e091015aa850301180030b03000c50f500c0208071044400d2404601c04022080141040c2100140d131142410040c049000038040306094031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371795089 1250 371793839 371793857
    0xf06010c030c020a03020613061407111e0415080607020606010e0d080706050720011a010e0402070b01090203060a050f030d2a0812010905130803060102210c0d 70
    0x1a9811454100100e5407520341482c0d600341c40d100060700200d02c5e03000071b0b4125001107592849000e403070b00524207a503060348840c00450400404200349218901009060b015816038806040c00d0808403054444039500048140c0c00b490381c0030808544140e0021010100c2c0300c01c04020804083c050213411512510241005180c03806c00a400242d810391b030b01d40520b6001c0284c4c030a0040074801d0302e14255000d5014003544c105980d00a1101c12502491404914415002d1040d000140300d481031001e0680511102000e102c4011b440c46031107031940541181e02003001d4400100c4800c1102e001e0320150100584a0a1040070f10202808941055004058542a0b04002d0f0707000034036104216001c2c90444280282d012034000070049005015004e400651641c00810580c02e01611403250380002403001030380d80b4250030301030715001d55100817140d098030359036404924444000c540c000c0301801180d420740030643d5003200d402041002d081d800040411100502039050068443c403469900c1c1c80800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371796339 1250 371795089 371795101
    0x403030f091a27010e0606090f06010c1e1b0503120706020703030905191a06010507060c1b11040510030215031b0a02031b07151110021c050f 62
    0x104008801c1c42d2414144080e00058445514103102514601015419102c00101c0342c0d070b05003e02402012622240a00c00c000391540c10400c425500c55500301d81c000d10319444040045d980d03070003119802d550f0710402d0070203d0b00642c0c28403203980740584122400123484900b03d0b000694081d5a803c4144a41c02a5141a1801040f401900c1519800040042c1c1e103c00c246425070041c040c43c00000c0c024010034550300704102d0700070100c003004ca0040440038075108540e03112582a4038201c0b0800d01040c02030019101040c0d1552010540c2d0b41903003440545030a902c41004d060520074801101e0031001c00031004c429040500aa64010700105255044141581c1c00540041e0f2045400c0c0b10155011002520f56405151485100840c240103243d50f2101958025120742c4202c0490440001c1003030b09400b031b0781000960f001115441d0410147c0c0350040c81c012a043c2e8454200d03404d4606c10001140d80c0d070000c85c402402510360103d036074050325008078107110903620001e000c2200c500d0010304000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371797589 1250 371796339 371796353
    0xc0a050a140f060c0a0c061d18070306240e041104030f06020d1d0c09041101030c03061703040614070b06060a0215040803010911130b090a0314060403030f09 69
    0x28844000701c601001540020010a80324020031600c114540300c2c00d201e1501b40b1900c04528010354445035141960f80c1d4000e80384801e210380d0900c84a81082020300c00c400808070140410350001707418500400c00390fa980700b010b11841c202580c22443e10309940c0c05061102d4010b0b04150300c26000b03031014801c401e100b0b44003032850700852101401e06103030050311a04200d4590304444681c50b82e802d041201541d1300c9204000020305000319040b80c441c0d907811980e10b141000c0410310a41d809026480010300c1c07003004501400d445402034061648078800811102c07032205039001e4402d03c80004684031840c220005001c00080312502741d22090801400010030030428030340d58000819125559501c0b005c100403490408256191a4400e042e20240310400802c1d00081d81215000b500500910340c09103080901840307007404c250b81c8a002a00c0810517028040090b104070b56005086049403a81e0fa210300b80c400707100b8404c80c8600d81045c0100700405405105c0c0241022842d00e042242c851559240c1d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371798839 1250 371797589 371797619
    0x90606020c0d0b011514030405010b0418020901062109080702010201060b0a0507020f2b050c0301020f0d1a0a0e0403120209100819020706020903150702150c070210020c0a050a 77
    0x156100c945d900e10180f41d180a400c0c802015290140415628509400d01d68002c012045515100b1410483e070b04240704440d014543c00140c0041c201e034450303440c0001c103440004501111108044109401012545c118803c0e4815180a200b00660741d442a100083c2103079800d0300030b41500a014001d210000e079003c07007662151135054030398441070100392001541d0b280d855000c10f400c0641c0c07401080c1c0b00a80000404015510601c11244203808a0040509074001c0300580510581c081c40f2401c5411403a801010326492018100300030100040040340b0301901d07a0700021280c0d40c20800740b00806501c6200740d403c1c030381c540104600700480800055060400040e07440104070205c2c000c00c03072001040300c246810581c421800c56a4108902d0010041c1d00050005071007800780080941c000b1810107041c900c500a40d501800390380d2900300c6000311001000c1d0a0711190001400684016154514010300b84910303600240500c0728440c040000388442c54200740d000e6a403d80c010000440c00e04540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371800089 1250 371798839 371798849
    0x504060e16030f060207060e0102070c06050a0203090d060b10050333040914030c1605090105011b05010e0a0308060f18070e030118060605010801121a07110106090606020c0d0b01 78
    0xc603483d424500700000a03000b1290050060fa01e0420703090000c0c201580104000f0703200d0325007109143e41e20b0b001550719005103440400903070400c00104046141c05158500740c2032003100002020708030500403d101e201051440404100f0000c00e02c20600c00c0168850b1150000d00d21040c43d500c13420800004038225400224000c0392100001c1c03041208255000005001980880e511a400700c00c0051b501c60700400115116503140074041054103014200b103040c1e0394103840b0150b2110b08800307040510303d01e01d00d042e1195580c816008030004001c0c4600c419060103070381c030034010b0b0500c101080001640c96070b00303030703c1030940e41c1124190581c210499513204c0700c2420b007000c07101e0900c80031a001d03201c0210170b6500064050301840c20009503a00c4001520300c207a880800b03507a2190001500d0780e50100010b0308002d08034984d0040c080035459000d5121501c1d14101e1501c015560416003075800c5900420107040d159941804850b81c10401d104102c0021962401c681d041500c80b142200011301030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371801339 1250 371800089 371800103
    0xe0103050903090306040308011e050a060f0203070804180f051e1b03090d020d02070f1a0f0304060e0c0301020702060d150308031510030b130c140d0504060e1603 71
    0x3081800c1c01c1c015619403200140c2560414502840d004140c55424014540d225200f0f5015200d5800040c5084058500260001c8ac0c200e040003401d403142004a034942e01144020031101c4002000c4d40041d00003090b4145841500ca1004d407100c0c2c090711048440703218800c1c43c0100700903005114001518000c0300d601d030703403198540b00c0c0080f80c0d0344011a40c00e01c885441000040c8410003900240e000701c0c50314103a096072031140d070004003203845503012321524102d181c00c10418040c0c0159060404040313000d03000e50915085034401d0024013500200c1e01510a56680c21b82c060f5500c1003030240d5035190004070000c600e4403202c0d6000540c40c2c02440245008143e4441015132034130205944c40003e1500651555103a14180800e03074459217140d110180502c040d038096000c2d540c003a01425003c08802001ca058a1001d61300c1c40c001012140d9034241017107142c0c0510803060b1269030060081400304200407805103040d042000560f091814002340076884000381404500c8414000c04c292940240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371802589 1250 371801339 371801341
    0x12171c0902060405060c160806010302030d0f18031406091f020306030703050a05030d0c0206070903121809140f0402060a050c01110307030605130c050d2307020a20010e010305 77
    0x45540c038090f03a001070b5040180046d4140b2100b00020f8000e8442d17031440345800303c050b101e4102d04d85501d028400250540d00910701054454060031502e8644040392905103d2007000442c04090711032294000e450b01d904000c0c542124840500807141c0c081d1030b003002040c0d1810342503944001d5a00204140208660100100c0c9140d502070000c00c00954028040740d520000d5414020345a40c005142e51140070310b01090025134500102e00c1070711034802c030b4031603120182c81d45e1100410300307244640d118100001c1220f40c410510003490044042c0103c61030004145ea85100c10442601001d0400030070303c00e036001040011307901d100460302a03100f5403400340c0c0c8680c00305050a000d805590206a1480808030800107017560540c406421901d048500300f200100f0035100c44110b69004055070002842040340080c0c80c803064000784203483c030640c03000c07940c400c2c8514005843c50f010380701900180c1088008100f840f85400342c1101c0c643d1102e007800d02c1c0080c0100080d18050407042e125042c961544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371803839 1250 371802589 371802593
    0x6030a0b0406031703010509070815120a050f030d0e0609191502070605060103061d04030e0a031b0e0603030c060109150b03041406150109030809120712171c09 70
    0x3070000d10085500c0480c4c00010003613200c403510903800074090b9034055154040001d91803031051580b02d009612050a0101e580c03070f0b5500b0f02803440810031a4046910600b62244005401040781640b201d09410245864016114895060360412000080103034884407d0008003000030a040c90302074295507916135000c1903440c000040010140c09141203070300c0480c9240c2031014036002103102d010300360303410003220341c64411000801700d6581d000700014a4660003e00028000d2040d04181c00f001400107110544d29614451344080302c0d28401c0c3d480200210402c0156501054070360000d000310095810480b41480141d07403160705120710104281c031071402c1060541602407400250805c513078410760324030b01410141240403034181da0310340b24170403003000417010011a022144410b81c165203e030203091454451007155004035984583c440d0440c088002e501c8400c10010303008010072101c00c08072150500b48400042c80e14248000740600030030120700451880e080380060703240001800202c15110b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371805089 1250 371803839 371803841
    0x1006120c0b2d04140d030516020307090c0c05010506060403050a0b0a0f020703020c090a150302090a4214060a0309050f0a140d2102070f0c031202010b06030a0b04 71
    0x800c002c05801056600c1800100400e0050055991280701c66030b210211106010442e0399440c400340014034148003442c00b0400343c2c100b0f407010500080485103280c2e268003108003125254a00d10002c00c00c00302503201004002c0c043d0a0b4841000c0356410b007032900d1034407456240c814540004002c20004400519005036992008403c44900e02d01103456580c9803038065a11041e0042680c4540d0042c400641402c01c1d500a0f8a42c184501d01e082c03050519650901210b040040c014071009911114523205680846817401008900603480000000e425054801c0000e00c0701c280014201c20344d442403000484c40100c2100800040e00ca01d542c1e0206d0100403070041c01c24020040160103071282d0420704510018480030544c0c010607007202c0b101d03000000302d5030b1410782c1303449100803803602015080a4075904200ea400201c12010261800425640d94012800303005c0c0f048610340305c105014001d01c500002c400340459000e00080048100c6000000d809020042005d8029621801100925180c07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371806339 1250 371805089 371805127
    0x603040b09070e0f0406051303020705150d110702180f0601140d05010902040614090f0405100801060609060e0103050907151701080102030601110d080714040b030403021006120c0b 79
    0x1000c07040300d24100715000204006017554252032090400e004070300d2107100d6404808020794150001c0c2420751401c0e0a03c644d503d0703811030200800340c050100e03068124041c010001c84049400c09242e071494144100309081c04981d90840e480c480314800c20600ba26049100703604040c007400d0002d1074401c05d8100103914070404040580032130400d000010a0fa0003078002c0c00a0310707000e860314880f90742c0d1104a403100d805400c0c1c246900c40610350b481051070130f02c0e0303003c0c0747c22000901e2200b4200da103825403275003981d140760312440000d804080d04111003640700c086200f484109103014801d43c00c050755803030340d60358150040b0044036940d0407600e4106400388107641c070501e01d03010440145d90b130750b021a1030003500119a4680480c0e2481c1003403180c40710100c0c20654a220395224882552240001101d505040c404141a002800c0102088601410000d144110b200742c1c0113042c0c0d8010200f1f64402d89806034030400160400b0418680040d09030907030035065616280c04a911400000d01c24803041c50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371807589 1250 371806339 371806349
    0xe15010609050418050a030806010e03030901120f1d0d091d2419081504080d050403021e0109021302030c04032d030f0306080c130c11031b0613020603040b0907 70
    0x446c48882100301038100010600c01c4609895035911a24000d0506480344280c2034642c4c0015003144802010102c15030088020140e4240c0000f40c3c1b91005c0003002070340c5241e0380c401030709910020403007049650003d0003070043d114041500b0b542c503140c840703041c0841c0e0010300803050008081c0e2003016111480c09204003071000c01095510342c90303550100240d4154075400350075803602603109400788070b03044126450301403076001c40c481e03191120401403400144000b5200b1000c43c0613840401074030002503200602c640891100020b01e00c0702601c10003058090515030284c82f58014001c1003e604800b40039181103d0300080800d2200741c1c416044036441c03c03a0180c480c20340c48020070700b0003071681c0311207405c441c0c1d00756440030030840d81c81c1c8081c55903550020907a10b40c8a081a0507080389180c0680041e03140c0c060509280044000414900b42107070402210401d03c1c00380301c40740c80030700c01003008580e4200895007100c0c0c6503490285c002c91100d01c00100041c10114111000c50820302007080508002c0c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371808839 1250 371807589 371807593
    0xd0b0a180b04091b05040e03070c0e0c0705010c0503061002070510120212041a0703020711010c080715020d11070203070620101527200d0e1501060905041805 69
    0x201e584124840b613802140a80740c00b551a00c451041c10440c000112107000341c101200120b000c4c079118450480d00c10003000c81d4a044404c0c010180065000d000e015000011503c940d80c0303d00e80384c001c0c031031100000c0074428110340c0303c01c504009a445108a084140c401407034015041c1c400c3e10994000703440388440c030000504c0071034100400c0c40a0b0402c91001403c0c580444807650b200d43d84110181c0c0030f51031001d8141c0344184050b450540c000c0841801e00d61043c042181482901c0d00c5500c1010f542c0721313907407a981307400040421030007205109040d1202c10307a589290800c2055000b081d6070710528015030051040c040c02070130340c2000540c201c550106444003140c0804ca04003255030007401c24041c0301c481d80e1001c0380001c900c10360075001c03c4a03141e00c1e140304108042407850420024003244078005d4a00e50f4105004180e00800c1c5000745001214500003041003128003640502d4032154550186011050f200103004c00756000005800b1908201d030040707100c0d101900150301d9055a00c2005201c0c5c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371810089 1250 371808839 371808863
    0x403020d050c01020607081006030f0f050f100801090c05040b04020f070606050103060b04120b0c09040e03134e1a0a02041409040f02150d0b0a180b0409 67
    0x80400904242041e02c01e0b401c0c0c40040d180e420f01642c404d06c0903100d10584a414a01c00c1c401c251081d880841c000c09103200c08140244034200d040100c44081d507118507330320104001c01c15035405100100c802410400d00802840c10070b916540d284140c2406014452501d8614038801c0c0d6031660143c4100c0030480156a548804910b40180202131031310819000c682010b10004020182005442c01c40d10040c900d10310fa91025600c12000d0380c40282141090780c018400500292502c1c820500159100c000940e5518400e488014011242e40d000720800d0100100d0320240c0c1c22200400c5101c0400400d41c0e511204d802c5400c10143c40c001c40035448140c0c0007628100078451001c01d44031440c144980c3e0510309854940b60801070784690700808445d121082500c2441e41085c1d411a9440350060080d201c1a41260340010410030084144813008a400308901511510380d10400c0c401c200b0445201e844540350010751440c4168032025508070907070300d80160740300d5101c4c0e81140418551027141e43c064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371811339 1250 371810089 371810093
    0x4120f0c0b0d0f02040510030207060e010204060509010e0d020d081309050c0301051206010e0114040204170a1505040c060804080d0f0c02070803040f030b0c0c011118030c10050a02030403020d 84
    0x2a80c00c1940c82d6402c40e070a00c0b1441c001c0f442140300b2503040d142c2c050402400001015000e801950003900112860340e524181017180d4802840a0b01c040c040d07650358140c1c1c03026600700062140c21680041c603c141c00c0b12404c4001a40e0718003111071140c1d40308180070346400318101a00048440e95001243c65414102006801d901000c01941a03a50403107018a000c002e10214980d503000c00d0040e072000e8100341006100300845802400703190302c00204098030707040e15000b070010f10840d400f40d984500e900c00020740382042903080044680305408002001903240c6511061400d000c54480e0009104402c004242807200c8402124417591410034141b0201c0011600f00d0010081180700c140107010b00071000c43e44003400b104030740403103004800c403402031411030716803640410000d00700c021803640810a41600310428010072100c0f085c070200d6039480d801c6c40c5542c20000d000d81d49103244241c005441c0d103071300c0c0ea0791841c00c80a0103985141c5251640141401a0325600c556007001e07500160700c50723103003003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371812589 1250 371811339 371811359
    0x60c021908060f0c07031d06160b0402152706040905090a0c061112090102030903070303050414010801060219030908031b010606110715140f070201030501170304120f0c 74
    0x4010409845070250a80c0c0e90064500d1170b01915600078002240000300c01b00c1c2c206003100850700003c0003170030340b4900b00384003088204513000b82000322401d19413801040254600600d607480c211030951116441c200502c4d0381134070b000d5151214418805a40d00040d003a689640d01501c1c05048070007030401c020f0616140071a940d401903403089071864000400802d80c00e1064081c200101c003200c0c010701907152140e50300500c98000c409082d04520052100600c0c0790f8042180c44000c60103034441aa0b29030400680d007581080c5c80e001c4038140035038540104032007a03000036150f00701440801000c101d10380c40d150803564403190754401480391102203004128481905038081c20482c0c1e18000b00920365540209a80418010300c0e05102900585801c0100b280c011114144442080c5064181025000b903044600e802040107650300b0706000c1036030703011540c1521a241c054078003120405c0b00d1034050107030f1981d40e101f1030203800c4401e00c0003002e0a00708507041c1440c04030300c2c1e40140510381c915280c5d10100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371813839 1250 371812589 371812591
    0x30903060a2c15161407030909050613020d150f0506090112110d0219020a111309120804020108011d0a050601121409010b19060c02190806 61
    0x520a000c0c0304085801c0d412640304030740600144140304011412a06984840c25400307050b21a064040d81caa03040d800340000100d140318041205007030003102a030200080044059006411848004001c20004643c000c4030510031202e0418000c966035903064080341c0207044121500f21500d002107907800b0392801d603812458071200704022060080780d039503a15189001e140d01c24941c0000c1c0420080310a540719444229181021800c00f0803c45000904030050b58010b00303440403e103a0100f10300070000b0300991006010159407004000640d002d880d5541c00502078a000c1c1c2c810413100740ca11039602160f811182c0410b0300190b10f10072086030744e10302403c2c601c42150202e000400c2c0d4800400c0b400700c0c00044100c80d14189404002c242e45001c2c0c044018100500f6450501090344413520240d6280d02581e941d00200580a15031420050036203429521100c032800e11480590450000c40043c500300704003202c85070300e00001d00e030116002003900e038901c80d481c60788511039080000c59543c000142c00c0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371815089 1250 371813839 371813857
    0x103140a05060103140c07080a110604050303100b030702070501050c0f01051905181216020904060903030c0c11040c0c020a0b030103211d010504080a0605090f0a210e0a060203 77
    0x81c044031058030031710140e00303000316007411a5240034018100802c0d045030180c100c000060804040310344441c00790394030b490402c4804980c168000020400902c1c03840340004006c140c0204070070704500709244041e445200a002d514100100030401c0d25500c0e900704410320782940500020095420040b01c49440c00107040e0b050078130142030801240890744401c01183e4038120700b0340071302007000002906501551104030300e050f000300c00220710000340e690b9500d0036000d0380c400d0000144424641c43c02030103a80748880e07284240940c40304600042500751003440a04803007142c00060b402c102040c162407590001c00d0203900246007000100c1e17034250400080d810b990044d401c0c0b4104400610f5511015038a81c1d0130140003809410140f100f00615110505030314605042040c02c003500c41c110a45000140d050542c0c01d55194410b003c2c5401d014016541200500300c0a80b404080395190a058144020810340c0c0c00039802050300b003600c3c440c05240141c0340004001d0a03072155540c13402035407a00007001d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371816339 1250 371815089 371815091
    0x180501080c01091503020c160e1f060f0c05010615020a051020030603070306050903072102060127060f140405012108070206070318060203120609060103140a05060103 73
    0x810756014188910854a56140e01c3d40c0644c40440110041d400080b800706540c411400d40d8040204040c0300d80c0060070080c1c81e420941d180600841281c40d0800e0501c04603056801014001507a2250203429031010b10300303201c8042d1300117183c1140146640c1d409603003612030751001c02c81c0e071395400b0420103041409581120300d06004c60181c5d40c02c688004120900303055501d0202c8428100c0c940242d603002c000141501e2099507251100d1040d90700880710410f10303800000b180d104102044401d500742281c0e072105402e43c00041a0007960307940c01030140f00300300d007440030b10740010041c450b00369600798080f02024032a40b5507410b4188483c48140c001c28a0701481a500c110543c1818810681242c507030b1900220840c180c4a00400705005008054a13618010050b0401680710a0b00400c0700e14440e5855401d60ba980c0d051014482c0442c3c0c1000045400800103004030355407540c0800c9d0030000c206c50075100740e142c00005038014400d018120b15550407980c10041105501e9021a00c550b000b038070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371817589 1250 371816339 371816353
    0x40305040302130b0307061101092a08030c030d0203090a080a020105070306060e0a051207030209010f09051303020a0605060a05120601210321020702090907140a050f01081018050108 80
    0x3d010760955030442009601a408003070100016485505008052211f20000040c800305c1c5032641100410204541c072119140484091411200103068100512020000d982003c04003900c0944038800c40d60041c0f07000e0703004408500040c000b40005041503a2040c0115641c0c0704076100039010b0f000031901c42002c245040400500240500c1e8107500b100d000074420501942803404002c0d6003130b65440da2400b2885030090220050b119074000d1406010742d4100c420100c0d14100049054030001011100c840d0080380040b00045e0300060f00c0c64610b40e119002103544c1c2c0e60b80000c20314050341503100a62114410061110b901d4002c900b85058407000e00301c40c81c200780380045404aa200318140240003407108910341c3c00082254284090440400001515103980c0f074000850741d02080c1d0b034810f0303143c03c40071042045503850031030703041d15007019640311028600c4c20300040c00e505000381e40d00741406100b80004000b449400c003000017910005000e8403600c441180380d80010f00e424007840c0041d1107484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371818839 1250 371817589 371817619
    0x120702010512180a0308060406090902011b141e0c010309080d050c070209070e03120a0215130503070b10240e120714010e30070b0d141008070909020612040305040302 73
    0xc00350410198060b183c442c0c02a44000d02c20120071008000fd0718045088400c80d925448244800b681e900d031030905075010040701045190625a00c1c0c1c0c1e40e00c2c141450003e02c0b400194200c419901240c0800f00c0c0041c881e5541782c0321006521661000035880000c0b54100105c5503001800350302c101d20282e0494092280e6940545458483d250640025038401d2500c41600e01c2c006121f07940c00441004a040340840a5481502c2c640010400719207410040341006040c0d201000350070014200f040300c0e42003407801840301d41102651211f1481c1000004108a41da6844616054a0340c2210318200c4205a5a40300f000990390a90712040c4e001582c8049809000c0c5002505d00c10510007401c4101e000103103041c90300748003041c111304002fa00d005041e40045c100034141c0103840c075143e5504010a140c120680e441405a500411a045215250714140860340c400140c441c10794a0b10040040e09a016000166590190800c02d03095440040204810194001e000e001100d01c241e9a07001601d540c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371820089 1250 371818839 371818841
    0x51008120d02091008092e0e120d0c0f0203131202010e19061211030114130213090b01020a0507031101121a030c0a120305030a060e07030905120702010512180a030806040609 76
    0x10407d0074181402229604400140981c0403649000001c0300300d0380c01a551201403d00ea070003480a014805d03a850b8800b146040e007005150841c1140c80c0301444c580428071102c030041000d0782c000d018040e2650307440c402c11a4065040c00c00810002007980780c82085246440f01c20111900400001900c5240359006c1c9100d00d0052803410340620041c075003142c0c00c109424100a0209200941c0103444a0141d00840003610040403d200d034400f16104841c00e1400b1002a502c1054866046502c038410000100b0004103074941a0b035802040036074400101c0b00103c901c1209419501034841c504041c80c56200407409071104024000c1c0c05441e011000c0e407081103e03141c003511070001e00354055854040020f01c501c005640c4040c2d4404001381094a600e2040022401203c1c14404203a459062205211080042e01120690300901a00c0d00190740d0000b8070360b0040d103410081714601c0d180481c0301c07406e8012100c4c1e880340440d4100e6002159909005103445030070b54400b40118038080700812075400d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 371821339 1250 371820089 371820133
    0xc0f0a032307020d0f1202030a03182102010608030c010905010b0a150c0302120a03050906011a1606090b0c18030a080a0818060106090306051008120d0209100809 71
    0x28607442e09088080d024031210081c00c0304100d0b852030301100000300180c1d103150008100e600070b5006544030964020054200e420b410f50301d50700c809142250074006005a40201c512000001e6100b05001d48014140e000d1301c103e8005955600000c600341000c1c8405501c0000c8040c020402408171080c1601404850b2809010b9006000d5014a44420503400781102c461014030900c110380c166414401180c107a5086001c110000a8481f4240280c00004000e07242c050400b600604020840300c60b5500910721031484283d0800401101c400103018455102c880201e1300300300d0031100c40c5040082c1b05956400803500f410743c0b45910903454032500b0f0004030401c2040d8000c2e14140343c4022140240c170190f0006000f100030142130031104030f800d8401d00c40ca0f4001d010980310103801f90300b10b14100098907401881c0f600c1082a06800700003441e000207441c943d0300003102044ad660000e0001050280c442d80710b4507504400050049203d840d80240d0240c440d4150009596104400707000142000300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 371822589 1250 371821339 371821397
    0x1e03190501090504170a09030f0602090102011d0d110a0c03080901020607050903072310020303160521040c030c14100e0108040b10050904150509060c040303030c050c0f0a03 76
    0x119000d80c0c4000200ca4000d02c030100c002d08000c7c02c0c056517559054000d1055010031514150046440c455550b024025200302081030903d5041a10820a90707540d00c0703600443c004200003c4100d560402042801400c120b44d41280754040c0f0152a414607280c0c0358000c41e080b5005120700b60004001c54820000d549500078010098a43d4070302c4c0c81c103c1d2510100c1e414681c0074403445041078206580d6100c09142120115402075912407414080c04040c055860101800384442041001c1108415840b424100701083e2645881a144c505103099821182d0f0002085240f0129004c550f80d080144079007d4010f046030f4041c604800e200781114000c3c3d02124042c04a0070110204002802341a4805d902160124075001c10360766800010700b1510307050318281e0300d0300425030404100c03030201e01035594805201402003c0909104030f41020750f128901c805401c0541c1c07044005003072442101290301c1c2c0901c850031030707a03400160301070b03551150381d120b00880105201c54803050341c1013015010419104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 371823839 1250 371822589 371822603
    0x60807140306040e0316170f0d0207051606020c0a05010c0b162c0f060a08070c05010605041d06160f031509060b03040b0a110304081e03190501090504 66
    0x40d52020600340941c1024000e40d5201c2e4a038640c90b0940001040586908004102c0ca0000e00c0c13864203000403a0329014038440c0100004200f01103605a84008071144103000180c0180e036103805080031814200c40d0000003003405c170007002c005141680024120100b520031203885105690786c400540d05042e1075480201b025a8605c000303044200710280040d000e0304142441d90680c246030306600180880b0f08030307030070601d00c000010280a082c840f40c400b200030002e80d415450410860f40c040c100400081610b01002058020074040020079004000140000f6205200c01450807142200001a6404501842c40f50a0000d0340b5040440440d055100c02070b10b50740c510b04040041200a403098986007110340c0205000095400341c0c130700c01c0c2c900410400d802c4603100e04117441c041d00c1050b40036003600607860030410072881c840c1d09074007242c0c0c10030380c0700c100c4e5503440d4207101d0728a50b05d845101d4610061a1301004002a64001c070745000d46480099404214580c5c039030038202c040b1070064501130060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 371825089 1250 371823839 371823857
    0x301030f030e1f030905150711010b04060506070213020f0a080105040f0624090b03010f031a100e09011416021519020703050d06060309110913060f0b030f010e07060807 74
    0x30301d0181e444171000a00070400c1c2d44103420716818401c03880b4015644200002d0080744070040d004003e100f0500c8460003102d05210315450030000038006d009045c0041c2c41045d00c000c03c5046103c00380d0450f02000100b00402c0d4a6841002c03010300152002d100d10f0f03001d0b81c1043c103d01e101c082c107481403030191510040c030030240f1802c0200040c1c0c1301800f10220414801443c901080820925015500a111490001643c1800c5181604402d80410400700e00e01104c10144107600841d0340000080d5034907211543d03c0f6603500013005016202159912152a0380c44042c481c0300350b40512400841042031302102c0d03c1e12268015019403010444031403001044d0080c01c4c800004454004043d81802031501e24203081c0caa070701600032034030254003441c0440c1d03407241e6100401222811004600300d0031503184109242406580c412403807007030705c02000d80b5035600d0345170b441e0a01680072110b40700c005801c5585c0c50100202540c02230483ca409030b40b062058030400a1010f128a8071503104410a55030300f981 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 371826339 1250 371825089 371825149
    0xc02030d03021c0920060406021902061b011515080f07020705211006120f0c081605180c1213020612070305090613030c0c0b0301030f030e 61
    0xf50092203640301c00500740142a106240f0501a251009005801545c41149084014103000c00004001e0740107070702c2072100300150368010842d02a64203501c0215400500701d07100080680c401c00c0a40203083c4624039032040000015032110f603103c81035002016049407100385060546c070442d2203a000090f44040040c629400400c1c0c020b82045060046503c11a121030000d40704c491803e00855000a5841408004040801400004050103001005600c0c24081c001480d0200c800c40a80b42c072543c0251a810801c1001d4442d008003036003c2522410303180c6600b800002c28051003440d20892035655000c8560440e4518107004a1140b16501d02d015001c42d4100d2808000278403c1500032880010305000d80c0b54140101103404c40515406114500b1143c064100d640281801c0f0840e4070980800c40c01c0d400743e005800324190141400009800c0b01d00d0864240280ba410030b40120002000000421064450443c2d04600c283c9079203461440d0b420901000540c15182c44191401d007801040c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 371827589 1250 371826339 371826341
    0x306240a0302071403070b070e011b021012020a020c030106300c050402040b09040c0f1b080903120406080a051302130b100e010e0d020a060f090f0303020313060c02030d03 75
    0x3d00310b40b080b46484e4a001070458818150382145106841060081c1c04015040c0c0e0302c6060500e401303400b403e2060a40101209101e1400107885000703005201e81c40e904403200703000d03030a030511300201c8038000d40d0740d070520000080d29100181c450500a43c20010041818515440c82480120b69400e200380802c8140f44c15507692400c0304030681c1c21080c4109e000c6016104e900040002e071500401640e41c9070300c1402400103d5214800e400c0030060b80600300c89c441540185000c2c4804024140d03442400e0460600c2c0a030340c424103403111740c03501c00e800d20010034400756000707030003140c0300d94032145602d82d5000c1c0301c141600c01c01c540708a60300762003404100042c034145951040c4800303c440300044115a02c40420280a51810144040380031025226500d40c0e104010020300302080c4c03131200c00800140c1c04203124440d00d00070502408178641c405101e032442844910700030006042484080341d5203090207904d0340d0007440d0180d0b1349400b2580214409018000c4000c20750b40c007400500c803201c00818120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 371828839 1250 371827589 371827597
    0x8070f050114030a020f070c0914060907020c0112021201080a05062512090f030309020f0315060d1a040c0f06081905060a180f0e010e19050705150306240a0302 70
    0x88400301800f107200400c48d0703041060054034841800054000071150342c401440402410f8500c10708a104c108088a0360204560a41c2c2c1d5080c2403c0c0e84070801441c02034080d004460485d4220785401c400020301c01000120303a400380e4024810759000751600881c070b0180080d021030b102018280b91004140c401e110f01403036800104494000140d041c016650b00e55840c1010005500103600c0ba40800190b1814685070314001004400912001406542c804109007008010070321a42c4000b40c01400e21000e016070040f9aa640c04c0c084100c0d2529103401850740801d401307088060100303040b010803400e0264251354060ac0958908018070354036612000e028050003014150004184440021a0100c0f1002032401c016040f2010440b10018040c440490741094480c0070300d60705000e0002c007559000b00d684070003d1011484409520316a0606610b0103009521003900500e42c3c1d204421400301100196010f03407011120201009002c1d4603409180c1c182c0d50441542820030402c60840a0082d8018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 371830089 1250 371828839 371828857
    0x90102190f0201140106030914191103030415080f0f01030206030a0915022a060f010e07030e030720010806030319030b10030606120509060a020309150108070f050114030a02 76
    0x40f60301314989407842002c101c01c0e032060020945510b0407004110b0b9201030b041000c501240100446604860000c0c55200703003c40181086000c10469403003920140100c030f01900354403640c1c9548200305034005003030210440d801000c3e080f40c500410b0b40d4682001d0b80340c6c1200d0b0014021030551300e49288040003030050350030440700039542c10507400070707403045d0300182040b00300c50640b89020304010500c00b01000303150b500031482d6400c1003080011240c3c0000c441410b48171000312081d00f44d900d540c400e80081c01d4280d40c00032035200214940e800c0024035404410200303072540b044460020410015140c01506603680303945500107022a001070786220185400425052902041884040002c1028100c805203520002600c400c1d06005d00d42c2c000b401003d24a01e2840c04114915101c01c90980f10b460161400380714036000170104180210820020383c511034800a200059650b079102e40c0d40d44c402c80e00c2611440c03030807280c0c0041c6a41c068200c4403500c1f54400c0d5040d2440e624071080341c0080d803004440e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 371831339 1250 371830089 371830091
    0xf041a090a0f03080109151217040801050c03060f0607031205060f06030408032a090d080d02121503010e06010317040305060103050705090c040b09090c0f12040b090102190f0201 78
    0x90400498024204690480d0180d1205011382d414501c203001660f100120303d4000c80a510010480b0154495582001c942c1200f0b2440b44001c4040d60291103120b0360303115007041e6081106001592140c04021409528201c802101c140d00d07480c1404024000c842d40a00400c1c8040a0105401d040d03400c5540e1081c0011300c01160940c064002a5443d00305650a481c6803001008000301e41d035a0401c0c0381c5040201d0711000020915107200381440b481107114042c040d01554030400d00b0400200107444001c90080401c0d5111900b99551198030003003201d200c00e241100e409801c4250406208040003131503050081e00d420707800c640711800000e9400080200356a01000004003058013406203034084d40c4504d010f400d46070315020820a8074000501081080c06003080200030005401c012150707418030030340701d0500660301c07108107045038001c1e41d00503402d200300000c904040400703060707210b40300300d00c11902d14100d500c0d0a41202d0807800341e0000501c0346142020307102045802141030a0403030b030a070701c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 371832589 1250 371831339 371831353
    0x4060f03060b1e16080c070f050d03050f0412050109030320071b090e030a0e010503100e06010e04020a1211040509040b090a1e02090708070f0c030306030b070c02090f041a09 76
    0x1d44c80c0d0750030500000036102c0c6030000c07030400c0100d0414040b04004014508080c107259040100195410003200070041c140600000d98001031a2140250780c0201070b802e10006140595040250103010307034140490000f80350682c1c411252840410f2070b07c024013450441828541e0543c1c03000503101881c040b50550f601b04100006050181740514401d00c000e1070b015607181d102c49000038288800701c07540c95043c444113100f0084840c002c0460001200c150400366403060b1510001039804014000142d50085d00010f207038180300d9001414601c1c03001c1c0764041085000d001521800907802940075123980007441e800885c01090300782d50504e8020000b03500395415141e031070380d800b1890034031043d0704105040100803040a502c1e04104040d84611903040c12101480d007084010b1002206040660501580089090a0510070707030040d000b440c0c0c0856407401d5800c1240028214441c1e100c0200e125004030300c0004c904112081c2201d000740d91040f4104c05141d014040305409a800400c449107600c6442 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 371833839 1250 371832589 371832607
    0x1b030601050f040b0a0903051006030201050f09240a020706020c061206130f0504060c0807020c3c0a080712021e1806010f0f4104060f03060b1e 63
    0x18010220304411b500c5030b404c03031860f61600f60b0400507041c03624110359180140c2000940d070030108035841d14520320141e660701d0f5143e000181006116464a0105071180756140114114080c001c20b056103a40d021191000d60352601207a4440e008940d4940110042c81090030f81d620900c2c8c115001a4002c044d0320304028a0b40080c402c0320005d41c9403a4000c2e03200e2082c84140400d612400080203110300d0301c91494034080c00701070741d654042040f0350301400700d00c141d540180035204181c080681040444051003000c0c80d00308105000d00034101d5100d2480c2d06030000d00040c0019252084407409984c0401c280301d00e03020401402115402c03800d1030b000028616415964112003418211306504840d289814410001010b02c0c01c032050036018418111802d005c55034020401c2302c485800351303440c0200004103200c0c808000180607450b84505180408016400c1400740141c41076480b245d5440d0303100d4690700c6044080d42d01901c80e08542c50010440c44000007242d14124600010035010340345001f940d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 371835089 1250 371833839 371833859
    0x50102040b07150c0309020d2402130306110703020d11160801020c010b0922020d32010908040612060513060e01050307060503011e030204060311091b030601050f04 72
    0x2d9981102d610301086808039440d0700c6840b03030039420380c901e25040201e4105540800d00e04040c154000c0e103100c4095002451541000110281110030030806644841c4a01140041446140001c0314510706081c0c20345c8203140318070300b80d440d05500b540c002e24000b41501c41c00e584440401c204803e49002c0d0445184400d0b5040444200602c9a0000142c2c0c0b450508480c5084400c1c400344244641c100d80c00340104a8100b511b14021080182c0b119204011280300140304014000c1000f000c9195000086009030407003020444e004852013001445c181d00c05034100d00700c0b44070480081c83d465040c0001c3c04150701c105245400c8404e010400104103403560005a0a0964040700d134a071561611024400c103619554841c0c010142a00102402401c00c00c0180283c00140a000102e10030100300e82494054208c58000543d0041c000f00a4581c90b420f01d55042c0c0051003080740110000300205600d4291a800345c0441c019034000305003151550001161036a10009804940302030600000c40e4090702 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 371836339 1250 371835089 371835097
    0x60a0c0206120103030f030905070501141b07061d1305040f02031c0909140601030216170301060813030e0f060409020c070503190c0b09040920010e0328050102040b 72
    0xb5140700110550316500d801003400711440c6043d070826090041a4000950020f60501a10310908204840f4200c001410a550080300241d2460100f404401c440c01c050120742502958501d5898108502102c0540c200e80250310707110a802140740c2c002c00300740c0d170b1040e480b4540080c07203805ea00807d82c14640009242c440b401c1100300d402c01d00c0c3e040d05100e19410840c0d80000701080d100a10160221688601043e44010b1003541815000112035412908494100c10b0050740212000c000c81c1c0b540c00d40c0c8100303070401d015190101d584140170806111034003180c140d500394140d880040d03960000c424081d02d25012490a500f15106010206a140380390001e80f01011807103009007999440c08082614000d040c8283e01e038281824224140401d005009600035030340c5024503107581d240c3c0c03403000c64002e240c0c004014004031b20300180c0d01e42c55540c3c2100000009030036a100d400d258460070404d500d0b20b40325800e00c0c09160303a10504808608583c5604000c160059000508040e5034000c070141c41d80c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 371837589 1250 371836339 371836357
    0x20f09040311060912040315240f0501140a12110d0b030c0111210d06120b010e191a15041503050c09190f06111005090c060a0c0206 58
    0x2405001c041d4080340403c0001e80c4554041c0050107603103030201c4901e03818840c1e03010107850900004a03070128202c8030b8121078000030350b501e454441b0000503070365280200074034091a402c042114100084662284195250302c45904041d28503040d881740064aa0301c003a07551111050761030321101a1202c20340c2020340140b61071b09002160020002041505101c0c4902c5aa414080d2070240004048400503111021001c600419941c084043c1c4100d400d5008021000201c103003003c0300401c20700a401c00820415100f00f00541c956602c07101d1040d80d000e404c440e9400081c0f000c10007660540e41d00c0c0c020110200401e40081c80d400840b6021520182c402c001620b0004070010b405c01043d0705200c0c1a20014042e80303820801c6081414a500b0207116081285204425a090858404030032280c02001000403062000f0f580da51520b01901c00b83e140d00c82220b46e03000b041900c540c21202402450300c05d41002c0098075040c0114030401c076036a08141d1204040000084000f40143c642d4402402490 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 371838839 1250 371837589 371837597
    0xe030c060c0703050106150504031b1509081b10050702040f020a110f0303130f06020c011508010c1e0507150e010b13090f06020f2203050c010906050f07020f090403 72
    0x20b0450130690f00396900e075840f034244148102401c1d070391107500c401542c050301d070f0100124021849144682480080340e8002c00032000303a0707254106459030010030303c0301205c2d03040003034802c41a581510002d580c0b400d1840240c202d030344c0f41ca001c61312910400051294074402807000a8a80c2003c1038801241c2245048501090003840c905120741c1c000c1028000c07500c101c5004510b10b243c4140840900c40320144000d241980d0a22003d040203465010b980981e14114000c01007450941c070300030044016480750400303a52808504207001482201044d40d90003410551121071001c244044420342c0c440b01003503d010400f1035003600c2000d4107020702c00c5c0817a42d000000c91000d002200704004a2008174185280c031f8038181ca108005501c1c0328080d21500d4001100603140e000c07010036100507114031391141040540c074800c040c0035401c05040280170382e030080003202d0039000900c0040d103a0590314002c1a001c60070030b00500c100d003880e02c001803a2142c400303003900041101d0f400105070a9003094408402103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 371840089 1250 371838839 371838853
    0x1f170601180810140103050c0906150a030b0f030102040e0c0a0c0203030f070204050f131101030f060e1e0c040b090109050a0b0c0c040501061d0f090709080606041104060e030c060c 79
    0x30b001c40e4000c18440340b980c4d02049045514603500c1c070341c1e00c03020081d59500900001000480c0ba0b55004001060b43c1c2da100801581c460b9a231100800400910b1540b0340706800c420003401c01401c05100b40c0d001c1d0f13001e0a080c05a940c60f031604c1c121690300305417810402c000e0160160740040e1001d201038101100410a4241c5440003841003100782d0780c0003825602100406000c0201400030510b6580a807a0410742d440c1000c1c2c9042c004030007920040c40700f11042e60078008002800d0040f411160301c80c00701500280d07010a10040c8141c407040701514030506e034020500003809021f000c1401840c0941c2c05040400c581a9250f01084210909500129500381c0208070696004070034441500c103000100c0d0100819030520001605458100200c002140341491100d601a182c4507690101200001d01000320352405d85401014154180954a0341d40200c4001c2803460905014600d07581641070325035824a41010720844800d0043c14003140d051146004401003170f19188002c0900540380740251040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 371841339 1250 371840089 371840113
    0x101e091403040b1201150f05070f1b030201021e070618030c060f030f0905030d0e0102070606080604020a35010b090702010f0c08061305091005151f1706011808 70
    0x8291050344402c00b044000d8107886d1100e035002c00381c0d00000119003442920303580c0030700300400c0e2211000e40082a4113000744010304108082041002102c0c401d03800c4130071048150f0305906c004900d000101903180d210500c1803241034000c40d84007049020594121607460358a440c0d01c0412140790b03001c1c401240420040348030301135050148000c0c00d01100703c00c1c82050f4265440030390781e100d0b03c0850f0714000c1c0d4403124a502100f003034044072602504450280320543d110a07105031507030400d540072881040c0320900099031444120074424900da015007541808054004503903100b1060501190444d50f07070f01c0c1d4010706031b0b039102c01c054000c0c6c1003507000041c1d1036125001d6908031a901e0750b039281401960820007d003503540f54841036550010100105260b00c40c0c005451500c814150340d29030181c00e00f41080106030721b00300e0303c164240302107501440c000031240c42620381400c40840100015804090180c07844076100c116508824107241c1030042100660754100056450703040600e50360420204509 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 371842589 1250 371841339 371841367
    0xf01020d1506080f01060f030b03030408150f01060507060b010903140606010801090b0a12030207030210080402100504140103051b07050a1208010501090e131e0302101e091403040b 79
    0x701070052828241c42d9800c000011400e280c0e014440d101c00c0140030600300c18554426001505480809011030f501c0d02d855036000c1d030300c5a40c002160547c4078110400030b8074081c034200d10281200c10903128103240802503100e000c0a454126403d5040c0802080000002a650407100e543ea00035480904018180b0000040600e801a0700000300e00b41411005241c644d18000c0010071210b07902c1117070205103582d1a00741c1c18000f961f030002e50b00c8812819140355682d04000814880c0b8421907500c005240d40310030a5a00780102d014601d042d15648024004079406035000e130341c0041c8804000301d01e40b061101c08205640c0018400c41e80d40e04810342d220304100d600d0001c001c4000090500765495810030307000a25060340d0b4490046a8140030000ca03440d507182ca41040002d940100d046215141480c10b1800580da90004c103c0040c0b00310203030740303c00c01303180c5c86100b6100c1000314020a44031032166000c4040c020b40300c0700391460b00403c0e0034200f404900300000c0009007690303a20117890710002c1032014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 371843839 1250 371842589 371842631
    0x120106080718050114030402040f05160324030602031b03070c050f0f060f0a0f0c1710140402090f1c20030601031e021003240b07020d02030f01020d 65
    0x26422051180c01800f032030384c1104c129031030355040e0050b01d41c480d515800007502500100181461040c603201c01d0150407440780f61143c0400006817414002078040380500401009252041c0d406200d02b4181400020b0310780d001150401000142902c0480c40c05000c5c0d000c42d44107403881c5011425461001042000074401d0200b115140c401070300b54165401c00c00e40c0c66400c010001d501da00a11000201d031260994840c0403400c0003d00204190001501c3c05025000940441108007000c10300243d284460b01c0455429511744210101d20444000b0034000a5001000b0072a40b010340c009844189031a883c9070840c8001c88904980b100c4495414084800c40c0221003180c941d2412000ba2512a200081c0c1c950449901802e40300c021010790317103100c04030900c045d0006e41c040c00043e0f00410155060b0003403645040c00102c07801c04040c1640b00000c54000754880e05010341d03414050342001d4689001e010f18a070380094203440d681e680c44a09542240c0c2300d203032000780c21030b9200b01507040018684451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 371845089 1250 371843839 371843867
    0x603060612090803011205030724050a1a12030d090c0e07021203040308130f0309030c1509210b01030b09061503031204020609060a120b19060c02061201060807 70
    0x40148500740d40f22045188014000c014031100789200b45001c00c80100201c4201981209410090221b1101d44110700060000c600b0581410940440d10480c1d00317210310301c030312851080369040141110090285004450818507035902040c000d00002e0b4445010306041030f032140c12128012800c0012020501002800329800c5500a4015952041d5100212a00240c160500c004d9a42c4d5255001c91001c0a915009202c1000103406038205070308080c061301524400c172402c0f00440d89072680c00f00403584d0050384d800040c0001c0010007441070000c081c01e01da807445c4050701a40c0720070b40d120151040700071b0303008581135032100c001c0180010f000c0c449150496242c0c0c4001501074094800a030b900d0240b040703d02d0120b13840b8801f00d0308650f40d1400700e03255040007070300083e00c070001400c001e0b00d81600c1041040000341006d20407545031a1104120305840f40100400b40703000d040c0351089455802851003242c00040411601e0f01080a400049000f441d9998905c8600d207004800280b4a84502e00c0d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 371846339 1250 371845089 371845091
    0xe010f080c100c17071202060a0e0c040207060b090403170609061809011b0c050705030c03070b160204110405040c0903080406030c05190305010302100908060105040f020909010603060612 82
    0x440c8030707159114040320b511040c00e0300d0004110700c02403c001e5403200c05900e0b07298803440001048010402450500d06201c9540d0302038540786c0d40c40d0091141952108140c641c15900b0072040190f240c603240d0301030a9881c0c0111000524405010080340300080c013078500b0f80c00308405c0c1040b10180722100092940c01602603a03401c00508181d4082035034010715039814040000a4400030700c1c175030341c00d40c080c40100031042c00c0c10b005415080c0024044d2090305409813481e002d128004a2182400100013107506000b60090006600d4501298070b1900120511041f840e0041405009a5518001c43d802c5540c031200e160f80d207901c2d02c01000102d41c8103040c41c10510001810030408100c410741660101c6910341004580b602181804850a00c01c083c0c0070300102440b00c201c1017a40e640360b40001d058a100340d1301868802d00030103081c0c84442d014890380183d07611400c010b004c68200b640041c0c0b00002001c90150904448000168140c8401d80101000a646800c00c01c0a2980101346c110740095240d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 371847589 1250 371846339 371846353
    0xc03021e01020703120519080604060b120f06031c08070914010c060c05040306060306060603181515050301020a0840170309030910030c020c1909060e010f08 69
    0xc0042e440c2c1556204c05001014031700f03c508001ca01600c22112044c40e519500203480c0080304000e8020381041c0c90580c0118079100300421015140030413102d0000f43d4803074240690b61076050055450310000d1050740c041c0501403030342c1104030b80a00746c000b12111585a00003030346426a001040e80640741d100740403440d0405402005642c2001c441c1c0200f0360007980c0403640501e03105041e10b00348501d90005003480c0c90a0030000520805620800c240d40c00d0380e9050010904200c0502c0141d05c5034480586050030344400144240626441b54040c11045801e8003036107980c03503000031308903000455204041083d01c030030092040309062151100d80d414a03841100200d48241d626222001c203840c00e0342003542054a00140100c40c152031150116600c0b40c181c0d01c1c03410b135200e40e4894000c1900300d40107505c0304da409000680a0b00890022a02a82c0245501d842c00c00400c47c0c1c1c0c40c5040c05608040165071008a80d24400703000340349c060301404806c0c05043d40341080c12240c0340944d0f4840b48442e04010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 371848839 1250 371847589 371847649
    0x30123100813080f070503071103030a170603010618051609120305030c0d0c0207080c010c0803240603010602011508030f03010b0c030f04030b010518010501020309011101090f0c0302 80
    0x80816002405001d000d60b000700507240c00e1041d807203904401c4140d64004200d80c020020004024100b03130b031060091a95083c582d5007810343e240500200303000416000300c0401c04d00321000740c0041c0d11990003000800c003d83c2e01c140c00441e51120b42681c00400b91100b04004840c1c44213010070000ba4090300c0c0482d001403030503510888181c0490f900804100001001c00c0088405130140d82c447da100075000c02500641d204041d40d29401886020b485009103111402d40d9130084c030500303003031a070030407141803441d51a940041d00f0a003c42c03c0d40600c002c00f8020b4180c2070344440019501910791500005100b4601d00d1605810008030b82c4811410f9000300703c090106800023083d281110140c0c001310b81c50340c1041486074110b01880340002c105800c00700e00001800941904e2038100e40e001c0d1031142e03841e4910390b08500012402d0165a0141e802048085525403003519880741c1d1a03141000041c4001042d82c400c049400310441c2582d480d180e00e0000c0c411740c034001c80c00103407000201c00000203001c03070340d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 371850089 1250 371848839 371848847
    0x90f011103091c0209071710050d0b27010c0e09041a19020a02071818110103090c03050a111e10050403121d0a0302030703020415080303012310 63
    0xa80707102c1c0c0244402c22000a1407010010002056940103020300b20342d26242c040244110f001c0da280340d46002c51034001c90b8400e440c1e00601e07429140d01528840340005661612203090700042c0c00d40d02240610030b082c3c010003209803504000840d540c00007081200800000a0000031000302440c0b0450003503060100054012140e0b4007005102c113413049859450140d04a0244050441300032101d0000400e034a016901040060594407448540001e141c02c041e2000202c0e1121482c080c1000c2e586241e81c0085040030401844a040500d008105044541e46c3c3c0c140c0003401c3c1d40122001d61003c110001040390800460700595401d5074005440886002c000562100421a4a0140c80426450040c03548500101c80c081c2d6001204443d0030351181a0003040c011240c603400107000e01414820b1941d14000302c081003141c0e00100207001d4a421034007000024940c100f8044041e4584030000a1300d40400c1c000755000380004000390b008025650b0401e003846064441c5a071040c1e254201c608101a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 371851339 1250 371850089 371850097
    0x510080109090206040302060f27030604170c011505210601060c0516081506030303092e14070e0d021f0315080c01030f0203070c031209060908090f011103 68
    0x618501282c040040e0010139003901c02d680003e50842400107103118200d840000510101a021541d03a40c1d0145241c1404000e18040c0441541904241c01050108440324a000003060105100c2803602008a844500b1201c017036000251444026108004c181b0303200c0d481c4c0681d103c100040c00b80400320351006ca51140c005000da44144180c0010480c2400f0781084101049403c0042002d000e1f03444051072665220340307400307040e1400b103402c002622900b03011055a0041c50068020b1100405201e442461144100c0880102d0301c0308440081a110007030140240d022005002d41501d8140032a0081c00001c000d9003180c021841c007198400141c40391a101c220b007085220f4040540342007250110060607070382c0150700542c0200500400d0b0302e0004174034440b03030711801d0301e040003042e00d942c1c0460141c0c00210b0713005000c00c640420f81004203002d41c144015035400300c0000922040241c5c2c0d0350044441d080d10640301000301145048180c00d14100c05071100c142400c0c4100d40b0050640c51039601c1c85 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 371852589 1250 371851339 371851349
    0x90a1a06030c090904171b0f0d120b030a05010911011202040509060105070204020d2a1d06030702160f05010f03140a0b04112809030c033c050705100801 67
    0x10306000007001e110a007140180c0340581c06210b2039664902e10202d0400880c030380094807c03805a000245a4588001800140c20100c0e850316641003070400300040c0100385440c07441e5094015882d2020000c4c00c03e200d40e40400d84203020b0500e0104102c8001807841d207004808801042c1704100900187c1d85014840f507000341d0074030307089984008900c0450081d002d08044849005c5c14404102c80c5038072030140000940811580a02e03000110000c101c0c0c00101c000c00c91400b4289a6669240904040b0000c6901102ca801118400501d85c3c04589050300a540042500d40101000303110944c0c0c000e5450110170018034042c07000c040d40b40c14480c0304d81c0010b054118001c0d40c40d100c481c210345680c1c10003c01181600c50f10354842d220541011000480d4000104814802c00420040d040c00b4008003415203030080c4000e21002c0c1160754000d00c2c00c1c0254603c10401141c10b802c1c0d891610650f40340f8580751a0642d0f405607105252030214644141e5410103480740c5020350b4a0754540342d010b00c035141160 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 371853839 1250 371852589 371852599
    0x120a0e01080420060715060e0c0f071e0506130b0106030204030b07080402030f0f0304030204060512060109050c190507060e0613080f070b0f010f060e0105070809040b090a1a06030c09 80
    0x28010344001011442803040c0185030b5680c003117000200409583c808001c54400c942421503507271700c40031501c855100720b084241204030306015840205088407034444203116030a200340a0420280c48191034a04102c51540000c40c403442c160082064044100d80117020500f800d6007414199a10040400d80041004040004a01c00201559800c002c1c2040c5182c107042602d002e41104480e29880381d03c180016401a414840c0004180c00d2209051480350035200c0940b060fa401c05201802070100a003801d0b886140074890880d883e900803002d10041c00c0305454090341c5168078584001aa591541e82c11400d401075000c000f0f02e001c68082400388680c4c0074070800e590762865410005140a0840041d160034001d03010450f80e18208802030f8142e88800301c5c203291980e030f5034030100d5410340c4051020340080c900380205000607901c0c0c07001e04000e02d40240702003800084100400c8c5c1c8040308031083d0307030b01d01e498400380020360b10018400002203100765000351541c506110341407094032600310014051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 371855089 1250 371853839 371853893
    0xb040902010e091e01060314100501020a3302030103060b040605031207032619090f0308250e040e06040b0c0a050408070f03140109020109051e03120a0e010804 70
    0x45800098402261015810030501340d6160721009000340b95101c1080b81c1c42e090f000c04113410707000c1c01000e04100d41d01640145010790b51980c484400401d10196061a0040c420b03004000b001c2a40c031889070340344954001606ca600d1810001c0a0701c4e100c00341d0078010b0b441c001041c000b42d1000700380c0c116010001522180e4466a81c9000c5070311807024440010700d0220030507030200200c10405144d00851520619000b60a00807582108441e9000b60081000c01010f00b4903001900415140390302007a5591107080f55113000641182c200c100b00c2d4080000390824000c0c42c10381c03130a0304c1003098141508000f80b003203241a545001480e1806000e03600c0c40340e000300341c1c8070115216008840c050162401641d0001d0307964200342201c08642e010441d281c40c808210104642d1051140c0415144c0503541c101802e8a40320510000000210707031550040c0ca01c2201c40000e481c10400b1904040741d030308145a80300303000200200403190f00d00c105410080c1c01c8040c000826000f0f03441d5001c55684820540340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 371856339 1250 371855089 371855101
    0x51002030603030903010906050402011806050a030902120a06090309080c010212090613060509030111120402040c0207050607030806030d030e060403030c0c0b01030f151509050c0708040803030108010b040902010e09 94
    0x70f14003803961059450360070000544104209500018010f0b403007a00c4845090029510105090300346000b22400204180001e004461094000304c4200d4009042c0b0700e585598044828100351071024162103594450351001c1c20540d201104000502c0450058030140b84c034080000d48400c1012102025440045003412450355000d049400c1c0c0c9c285190008d406c1a9104400307080da8000c401214401e528100e521a61010201300700c0340855901300b030301d8800c3d60390369081000800e00303401c803c001c44c13203607120104041c0c0310035005000507401382d101c8010034030b048010035123041000d07680b00b070426003004040440c21000040c42d40d0400d070305040100d0017a03c1c1031400c64560f20040401350407517000b200000103201c01c000480451600814030010010342203101d040507100320700030110b20b0200703c1000700301d0810700c0c2c0d22054021441c442180d1414046840304200ca0b0465003106220f03810010040210000c24407414071260383c141d800b4440d90569800180680740615445400f5141103000121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 371857589 1250 371856339 371856343
    0x120a050901030203150303131a160209091018021203040803030723160b1b03070c05010204080d2024060409020909010b030f03040e07050a05130e0a0f0504051002030603 74
    0x1102e00400b0f0122500c4802d14400c00005003101e1080080102480c0e810006000a44080301c60002b00d01d90110803981071a030034000010070007480c2403014003aa41c0c82000390001405070403046102d00b8120072180420b401005208100c6290b8802183d104010400200c04040140d0f03500c2562414074800e42c2120340e030310f600490000884081d00e030b200080c1104091451a4407101c0031402240345040e155103d401a964007150454034018409080c40020b6515220710030180d107442c4541e00260030540c0d10780345a803529001260460105980304040c1a82d50040010028107801c05401451110212815400000300071005141c580c0c10150000b506a1916040704d0383e41076024010401030710705200030300c0c000d148100c07800d031090103a50b4801d588144000140c80607115200e001c00d2068a40303070b034240c8035035000708240010b110782400502c3ca01c100d041500c80040050102202062030403042c1901112010801041c500d460141440040b4078001507100d0010140d080041e520784400001034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 371858839 1250 371857589 371857621
    0x30605070e01030501150c05100603061406030a02091f1a07051c050a0311091909111c09060e03040803190903080a181703120703182006030414120a050901030203 71
    0x11444e42842b1001041003540e60080c03104520f04001030240e40c84440401d5221441c14101942c041c07100d10210b400c40044000989000150707800c3c08940c1340e56a0a00f900c07807910310385918124113011401e803060200c2844051100070200d141728071b41e9220b0000c00382a60094807181010180c0d501009055480b240c411584500030060070000c09280c41410001c110701140220703c201d6092943d02e5010041d00400c0e10101140380d40107114180d5100402001006642c6003912441d844466040419605100803c090002800a195102450b10300c4400c080d0b0788001d0ba8040007292282000400d4001e03068070750751065850200d80c3d40c84083c503c110740c210141c0155242e02c2c1e90310207002111380c0000040490324950f400c0c0c080c40b80c1e07483c203041e8216100c0301d1110b00c48520058900c2e00041131090382c541000103281194101040100c08a020741e0000c40c0d049400e032959100c038804240c4c04210030760401644040035450305010040c02401030146468150515402201107050020710603400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 371860089 1250 371858839 371858863
    0xc08090a0e01230108190e030f030106080403030c080606040b13080303090a1b0e130305160b060325090f0902130c1b1101052101030605070e01030501150c05 69
    0x240036950310740e60b050485042000740f00699014009540807a5405402c2d21485038444040405945400c01c851030040c0c50030080c2a00329001c200040000c00c400800994043e040c15903925030a440c144c81e004c0c3c119840c045c4180103001c017000c03c00060703648207012101902c0741601c400b5250b142245091401d4001c5400070982c5000100800109000004101c00300303034094245191240c0d003030580c50000c8111809907118550700c075000a504204400034000c3c10520a113401450f1001d08000c0c01d22a003810391080f10724030b25150a00205280c00c1040c2034003611070b05640440d400041007440040241407017800010358450310000c3e0214159403040039640c0c3c0181c0120041424500602c0040501d440d491012510100c07029502d2a840000e44030055841a9100b41d000726020056845070001c686203000102c08050300d84801e080d100c5800d0085105180104903400c02d8800130385040401000181003614100c0100060140050322801d10001801c19800ea091282400e9040816032009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 371861339 1250 371860089 371860109
    0xb01031212020c060a09030203040e0c0301150509130c030608100204030309081906110702040f0501030b072a2339151b1507050a0c08090a 61
    0x81840a264034006416805a846105034414404014100d00501c3c10401a550210000a05000495002030075040c0a40101c80c2000d0743c4480005c800241103d140454046c0031004110f0b5980c2c4c1d07240b42010000030304204c3c3c03c21425501261a990504800c2c001035500c44a90141c400d000b507010102511054054602c120542e41d010b0019602c1803101f2800254081c5d0005280c01000c41c040000302c50900300c2881e10402522041c015002d10481d4540f28035082010301e006980d54894500c0d0506000d001080030342c51414110301190f0028034440910070425000d10307405448200c005148901c2031042040c2011a04084200211003032500765441c2062141c0c05694200081c1c0700000030000089022003011220301c404170769201c26201d242135620624600c040e161940b140011070150b07426541c10280d84000210040100340030680158100074208108601c0906c5003da1140c50740c18903070301e0000b46500042c1a1006180c0182012401040c03944081d900c0380f5652005009080c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 371862589 1250 371861339 371861341
    0x60e07020a061a0a0323010b06030103060207170a0c021003061d100e090708060105010c02090f0a0b04180204060b030c091302090d21020105090c06090a05040903031e0605030309040906090b 83
    0xd0034120107030000c4006c041054060f1400e0081104c1400740e21409100500000d0569184d542e40c1400707504001003c648181342107082000e20010000a0110080c0c0c0c0e03920346001503014014000f80d901d83e400380d141050f0512100340b000a1035a4243d02440c11001c02c4011941d444004411416202d6001640c0000990b0240012818001011800c1d40c40301410346600c0d9a0740c3d80152241c02903161b009400110a200281910841c015110f51220f4900c0c03003c04c07002c1403040064126159a041c40c41141a609069001c0d414188101d0340509200c8484502c0d50810300e00300030320b5000300c1e40041c0c400c10810750034913084965034040e101103e4000c0c107520b10804035171a01c0d081d401140d1480074044c1c000040143d640a10501505010312000302c00740030b0550203a0144036040d44000d40c3e894110503c0d05000030325868910491007501d009030b400144144910340d25081140f55a000c2c961810705044060141b5503020088903001e46040f540011552124580070002d80151a0090300d2140500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 371863839 1250 371862589 371862593
    0x80c060a090e18150910091103160f0909080702040c051e07060b030d090302040b032b09150206060906010c02100e01030f060e0c161407050103060e07020a061a0a03 72
    0x81c07540c003c1c2e010a0f007690450b00d14014079205448080301c132004c0b44e40c000c860800d000015540404100d83c081c20000503032550311b1000c0f0b46002d42d00481c0b0b03c404000c9120410400100c29034450143c89003003401e0004511544031541e1a00038000080d216996401d40e030165240100103d40400e006411000c45017030300403104c0406504145010345036a410458010100d14000c191030045044035250f40c0a042d0a54080c4801407540401c5541c044c07140d00c032060000c0034464011040c19007101c10041c600c0343c0c0c2c0b0400804a204a41c000002c8441030381812a07c4d58011840c654080800e8807a2030155440000407038111813080d02c01703504001c0701e84030b040804c0e0307102c1007182441c0340a88080c841c103401546c515080340c189100c3c460101c17010402141c00203001d900105030329078120032030300350800316521f0380110b03020300e42d108100c036505c01d083c1000f02d9605801140c0082c00c9074841440741c0e01d01a040652904003040004100640c0c81414180400d02c24a41014004c0094215280360380c4038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 371865089 1250 371863839 371863861
    0x1212060b191e030911090c030a0b04021e03010f0806010b1209031b03030702070b041a0c01090506100e100f05060a02070803041206050a050402012309030d080a0510080c060a090e 78
    0x4c0016149a030303202403019004d0610307104c0d013800350003400221031540c1c0c2c60195240045c5030202c25142d11036000c00194050ba40502c40140852400a601d140c1d81e5140001d0104d2202043d8070440d981d0b04001c00401c6802c1c907580550344c0a0b03541c0b41601c034180da0303544002800d52244841035084202381d490248590940040075510801c101c0e000c1310304503910382c6648556800745102e10404424031003400c503a800c0a81001e04801c044800c00440c024525607a12810a84204c55814440e201403800700180582d1400c250740000b00d0312a5116610700307043c0000400200c80c0200c50066800081c0d42099601c01c0101000414100c0156915143ca40c100e00f078003010a05011b84205040c02e02003005e06c840b074171501e405568161200c0100d0303004500d14151200071800ba60301c9901091201c0e412603201400300f881c00c4040b41c0c1d80d070740d080c0c40d01c0e2120b0412101c000c0c00e21052112010014841e4400000ea05640800d04860142c0c5402180c0000c0741c058000e0b800a0b84005100003d000076000a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 371866339 1250 371865089 371865101
    0x6040f0306140c090f03030409050a05090d030b100e06130311010207050102120405010f0c0b040f0b0f040b040201050c0a1403180d08031315091212060b191e03 70
    0x4100000d02207420001d102e042c1c20360094404050a0b1802c00c03030a02c86140c244804411070700060309a034141652000c0000464104442c0004825224000c00c074180d1814802843c6a0016003020001c1d60790b04008141d10003810a5610140101e00c800030355660345000940d1a1810b1460001c0da0b42da0700d030303d444032600164005a5004d445003100202e850b41c004650f92044a690140c65410103203800011541d12034070f600003106004203400c41c0c60108103030a400d103208034011030f20a1024080c80c0303040301c0307000c000900f164240340d4103400f400006000400c1027604144c091a00707980768586646594200b104890001b000345402c60044c2021420100141440d8948881c0c03842c4403a21810503c000c007005000700a01e002ca0820015070b0006d0340400302c0184030301440603081c1001065500404448404805481458811080440032a8040b01070240c5031a103403001e2000514020380d4007024040c403580940d05000c280b590400c01481251424804200f9444468401400c104081d008180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 371867589 1250 371866339 371866343
    0x503030703020d02010c0e220e0304120b010501050c100506011b060506030601080312010e040c090507030b120313030b18070b0a03052206020901030b101706030a120f0c0206040f03 79
    0x10803d80010341150107087c041007241d801808000150000c59202c482114030300b408124050380d81d83d210803801d00108042c0000d00300f486840d01e80d05c442030500148404050780500d04220041011100d5107001082100582c0210301002c240d0791501401600c5100c05480c10400a0080c03c150109025071038200301c1c02044203405441080e600e58411581740d225482c0300c51407140d2035800422201460000c03040d8800c0c0036140c0021500d4940c035081003131715402e44555001075200c0c8415031161030b01c15108010804440000d40c500300785680701803021b0f103051001030702100803100042d122004002080e0a8280700d0015107540685401c0c0710003007500181000000285400002024400390340c9259162502d0203100504420050b40c03400013a5000030611410591a5084129a51100d0f52840b019041c0c03601c901c0c04085140c0b02020404c040100300798840d601068401020860b8000350000400c00c5281c125100c90380c040e4141c03034443c1030810007500300c2c00004000500c5a101400070090300c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 371868839 1250 371867589 371867591
    0x20f130c032307080403090b071a06030703210c020301141605130e070513080f0c0402030f131707060518150601110708030d0e07061805190503030703020d0201 70
    0x82c22648401440701c070300501c2941c1040500450260350280307800726403146c424908585010344403040200389403c100170845010b0710a010075010351165441c1c4551107801580100200c0c2e18545403008825980d001c501d40b070b848000e080306401c0b4842c26000780326030b402800038080394184080300c1e81c0c2200d08030741180980030803c0030a40c00c940b00e2003c0743c810202c140c0c480c64295003007a201800d100d80140259043c40070802001c00a030074082c50800080c805c80000c3c1500c4550142420700301401d599000d44a144108104030780904680d50f1603030424003e41c40320542c17402c10b20740f407800343c1e541402d44030164401107001000c10034540c02c107500c01c402494888031a00d200c01c00031980e400741c070001b14081080080025001e54400c1019403440003040e805c450441d9a1402c00508550014002180d0141c450080c0324400a04022000041c03000e4503042c441d00034cc40091a80004450207103078410020314000c1652545000c100d20080d10000301680c0d0340d9a80707858040c0d82d40c190807050304055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 371870089 1250 371868839 371868851
    0x150b0a0b03061513050f1f0309051621020f0a03080702151c2a0e03071502030711010c0605010b090a06031802090a151805060603060f0d020f130c03 65
    0xc80740006407030300162004110710005003040100042c4160707004504c0d03000002c0c1f1030041e441c0840c60480151460f800e4400168265440c1811820704c1c10400300c03140c0403222800c040018554000c9140300d400f406c564500d044e48101e20019002d440c4420b030499000450240100903c0fa5200051600e01d10896166400c42900202ca510a0041ca45880d2a8050308090340000a6180d00400386042d1010401076401a481404241750340c0000720320b20000b22045101341c01810100301d1040680219100e41c034400c25501e4000b552440344000080074070200200010b4a64000c440c85003000c1c3d070181050000b0b42e12800c7c1c0c4c04450304002c603918840c26640d040001c2c154003074030505544020306605020400309a8081c03181903031014100040403a99a0001000111802030740c80c0070700280316422030308484140f1042c0076908040d01c03e80c8554000c2051042e565a134102260301d80c0416650a50341075091b00000f0542c43c03101c03800c6a001081042170794110007095200b01070421083c0c6080101c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 371871339 1250 371870089 371870119
    0x3070b121006030903210f1514090105100f0203070b070507150506090723030403030b0a1a040612180809010f0201050411040203180a08030609090613150b0a0b0306 72
    0x1650150100903020920f11100d41e91078041b842c400402d000c0c500c02c800b04012500c031084000304d81d01c11101e62060301c114881400406408200c801158000300c807408034950401e00001d00058050901906100146840341c1005000b0310580710070303a4002e0510085407800850161142c1d1088004485507080450312403032400f503911845010b60f4001d003058016070754024050780c2e818404030001c1c02c08000c25481072980d2803410015889036100341d0700847c1254154051051102240e04043d110701c00c48540840035804040641e421a1039503d4144400780110a1900051480e040000b41d014595030f20b104c08e101004000304141d910a0340d80c00000952003004a080b00d0080e10010164101d0303401c110314903e49038014540243c0000c000082110341d80d2507152812030284008c4444190200401501d80760400400341d1085480006e00715510344000c26250801d1401c0b80241500051042c1094450440e840103100300c1e0068101882503450b5a50b0105a80044035254412124400240700d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 371872589 1250 371871339 371871341
    0x606051807020c060a1b08120919150f14060108090f061b0f031014060f031303020c0303040602030414060a120f091a040c06030b0102100b03070b12100603 68
    0x1108030401d5000c3c050005808040114942c80720030b600b0100f01e400c0307080d6400c0c02d01104584031613512a0484558968902c0c007040049440100283ca194000f5500600c10a445150f204403156000e04c040704e4506034010700c10020702d0b1506001e07075001d04e40001c20f008280310303089003400340c0d07401d07214602260788031945540e5a280030309000040b40c0068000c1034100c0c142e07445200100c0c1c054003182d03040009010340111182c00842c0c11810b13907120100704000c0002c0c001e03504048400c0551b06249002ea0706101d481a51001401070303404040042d80c0341d41814428488181c19440080179295925610394009540b90414028101740e0080c0c10700c14259031400004494227817143d07490f840003020140220318001e00550000c410500d89030419507001801d1007d0480d20000101e509225038202821b01c2941c03034455030454010b040c608403858044d6a000101c080d051b518070680410054803940209003021050340c0040b4210300042480340c81860001d06052040d44100c21441509607141784c110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 371873839 1250 371872589 371872591
    0xa1e17060604060f0c02060c0f16050d030f05030405010908160201120504051c170703060603050a060b030109090c0308070f02011d0d06240b03090c120c0d0302100906060518 76
    0x1408144c1e003511081035039000f03c090f0001c05000a2156003441c82c0781103907a003800b2000700040c55039044070f2151b00b000c0c012840000003401c0140c0d4450360001030365401405a02509c0c100d0018000701000140400009421508410740d01a1040d41c561269007046400100a058100d0100f05c0125440481d010b442c41520302c15500880140059400c0226100030301000b002030303408101c2d10f80141450800c220181c14000d070a172796000100540341038402000c1301e60251818a0031410f101c0308129512104007942d066625a200010303076402d20f464801c400c030703070142d10040071840080b90103014003810100329515607000380c0342c4080091001000382c800e401d880b031408c0d43c000030080030800460810b0740480412042c502c4641100610002c804104880c2a8000103109200108116201c10140a040c066400c01c1d5204841102090071302611990201e08441c040c071980c400c0031003414400c0003203204c3d13242803203c10072444c022410110302826441c0240d900070f111081c12000c860308045502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 371875089 1250 371873839 371873849
    0x203040c0302100c0611070b0108030901092102090a0b0a170a0809011106040c0603060602210d0204050607050616080c0306190f0f080601050f150a1e17060604 70
    0x31a411907003003160080e0042070302e83c10407030300a0a80002031014810792400824100b80c1c181c8134201032070004c0f042c190503008060140c00c1804411070070b036000075903030040d0f418403c0c110f40d103400c542e0321403038031100801c0c0c0c065400000c4206100301c1070465841002504000d031480c4446079214000c01402c0b1510b46040029603120103088008613504401034600364505240ec164044081c0541501d009001c0e24250f0340030240d6501000040c0e014403030b05008005d0b0b030000d07240c042860060000b80c01c840c0000c01080074400a07041819440c6941140c020f040010020790b159003c0381003080d6100800c5480004844160600300300c407138000c499083c82110503001851940d511030080c00a400003040e111320842e03022000c0410101c071450401c00103090300c803450702034041c90705903802e19011043c0e01050140f020140c0412081d151003000d80300500203120000e580300c4101d40111550324a0204100c58400119141510103a001385601c10411142000d03c01d42c3d29603000f000f94900c2a8490 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 371876339 1250 371875089 371875103
    0x604020102030d050903370e10030f0b040207050f0708030f1b100c03021305060a0503010b0a111c021b030607231306021603050309090606090d060b13020304 69
    0x10258084044e400c0f46512a04081c1a07a09210400f180c800714a10b00c800146081d62282203561605c07602252007405140c5035142680b1005288000b25510b07004a616540800d61905d44030050111590450050708201810841d500c00b4035040941d201c52080c8001c00850003079505c0080c141c2c1c3e0000c01d840c0940ca030003181c1840d012000000e034604400a00c00701080703014605801c9216103480c8503810000006d40c801603543c1c6801c10b810382c105041074008920a0301e042c0012262071b40c1c02030a8905603882e207000c8a0b540d480c4c80505032000c04800e403440140c0d101c0e40100c031013420f2241c0c00c40403414840b60202c4000c002c030514907a131508600011507030154804000294030511401a49204168031207511184418403598010b032a40a24440f40400c9500d207010414940c0c1004200c0480c1e900704d04c22111907085588542c1c4034424a100e59200c0c031040030109200765945da08541c0d001500500c00c0c1c452074020318204c0058007001d04200d10036400400c0c90504040240202d0f407140d503000301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 371877589 1250 371876339 371876347
    0xc050607050406050a0c14070b0d0b061801230c011a030613080d180f02031e0a0318090f05180a080702040906020403020901030506040b2d06030102130905010f08060402010203 77
    0x91704603240f080480c419605c412030314041d100040b078240000d40c045e00a0041c015a19a003404170b05050300d00210b19580103038810401c242c1013018417100145e20301350900e44000c504102c81204400e890042c400700509090000d8011801541540b101c007414521010703149050401c5420551125021900340003600e8002c48040d0000d040c0500501c6100c900400000c0c01e404074421510342102c544004944041e901e451120651908100072013405040d0404503500302010100b0940b913040c0034a0007010301154204248011200307005c900060491140704000f407004160100c0c02806013a07800c05d203143d8813000f583c001540c01040391491160000709441c84d1100d103900313000041031140011740d01c883d4203220100c0140d0301e106410f8003d41c0154010401401c040c200302c0c0741d100f4040c1600000c602620704840c02c0da0741c111190000b1314160300036111243d586801280c068420184403410180040e400428445006d9202c24180c9405c02c40100c2c40c16200e094159541c0d400ba200680075900500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 371878839 1250 371877589 371877607
    0x903010b0f1011030c030f09040b0906060717040b0c0313140d0b0a0e010908030901050a020322022107030c05060a02031902031c0c03050a14061c020a060c05060705040605 75
    0x40400ba126148180484c0e2400c130041245a0864012600409140d503001a1a030880d2405004480800c40110b646800c3d41c103280000441c01d124110300180b510010f1b80940401100f000309403002000385821040da07441e140d401558403640304114494140d0b80c01903000c28109501c240112071410050002d007611861a15480707166000100714031421502c899030f11100f1107081c01844422846264901d0322810161412400d4510051942146510600820604210391103d5400341d040380d17041d100b100e90352400840c0c1e07250611910015500d240e2400e40c3c10281000075104110bc0c050b81031034016903250b40401c81e8900c00c004021005031f0050000c0f4004002020f01c40e49021000d00407680340c905800762551001c1304d061108928542e403940c140c404240c260140d9a8030101713004081000c01e4444400080c0400041c14032401814420b500030348400250f00c031040000c0e0002d18004c0d030342d640e92000030708106010780120383c01e0158401007081d090150054a05841c85608c03410f041a482c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 371880089 1250 371878839 371878847
    0x5010c020a021003150f03030215011a07020f13050114150909010e0601020709090305030703060b090907051e03010b09030c100816050706020a0201150f08120d200903010b0f10 77
    0x20031020800017407441c0c00002c007030860000003001180302c2d401070304501c868a010350300b4a0740140e10182e4000c8094111140c10100031084501c1281d0403a0f550001c0c59550010610819211804c6c0c12170745c0c40e0a0012070307000341200c0a044034010484150400c100e004440958501854002a801448803c01030000e030041141c10380c1d020302c0601c102c0f0342883d07607000c0036000c1d1850160142c0c04a0000000e1210040d41401500e010340000b030452454506004086103200c1002006c610401101181611580c5000d41310314511882c084061600d80d6140d1203c11001d6001e014000c1c420b00c51030303044601e01c0c1040c0d149881e4140c1e540c0c490320301c2a9182800c4103021011900b441080000030040080051403a00c007400c4031240a42c00020b0354581f80d00801c0c001c20f89a0060300300701024074410841ca100020340c41c0704d0010456221501d54100c1c01119020f082807180e4205144d001c4403a030b804c8102c0b003401400c2c0310380c000c900078051300c0101410700c508518020380903604502c2a002626420303020b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 371881339 1250 371880089 371880101
    0x30c04150e0a0b0306040b040606060f020a06050a06050312430317010e060306250c0507030614041b0e06010c0f120e1f020706271205010c020a021003 66
    0x70303a000c0403c003408414002030425000b200c04603001400300c0144003c0c4000340c031480e400b91a5600b05140704114819020b0b60703078410000000c2c4500d8a6000080c101c0c0da294000100510303000d421a2040c40420305051100c4e000b28004c0c0008086460142e00c445041c40c2081d840000507071541e446400e5090802203207d081d8072403e409100c0580e0095000d41e0130301035a103008000e60b2041c41101e04240003014281403000c1c0142d07007600700446192072000c10101030350400352903034145610f00419031720701141410080d50020381320611308403100880307004000c0080c5c4030b544943c1d040ca0500f210b54048090072611400b40c40301c1d5602c5d110020b4015402009199805400742940000000325039803204104500d44920100159060400041ca0b00300511080c07003840c01001f07014101c083d00740d0001c0d6110320f00d100e55010032041c0102c841c6254041d40000300b100c10390b901685c071380b02c1d10782e522001484001c1d0400c82e555840d10325554401840418100750156000300b0a48046035601422005060303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 371882589 1250 371881339 371881351
    0x31911070c062304140103200315010e0d0b0601080109020a021902040b090a0606020c030c0f090606070515061203160201080a06090203160206010503070e07140f0c0a02030c04150e 79
    0xb80180001080b100e000c094130051800f5902c1000c2521602c0004058941704006200c40c0084c203014001c0043c4410240e0b6071045d030f54280240d08034038000040364820b407000c084075013184840355681d00703010326401c50510820081e20b80c0d12450760b80e554202d0880c80f0320040640160000740e85801102508404885128001003011071000f0400001848980003900d65200b0595610f0040101640500015280031821000760036017001e904046001c660000f0141407085482c1c2d800118142e942c00d05440c040d58001003140c501d10303c0c0345ca1a01070746000343e5070284900d410380c4031304940c85400008c03940921018800e042e01c0c85819401034402c0c0c4d0000d41000b1180e500d5200200e031000d11803015500c2410405040c01000c05840c101904000040e005a4041e4003d0102480910902d084e000e40041d0146000d00c03400f880c10f00782c41d1150140d00300f6882c00b0070000504c0256400001150707a0118002c40a80340100950400c1204131341ca400044601c040b1040001c00c400180c118089030301c12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 371883839 1250 371882589 371882627
    0x712020d18020a05060c06010509060102011107050706080a09120f1b0305030f010e0705031b040302040e03030906070801080a03200601061d040507050d0207021203031911070c06 78
    0x51000c40c800425501c034014214020040700040c20150303c3c0c0440c0000003420240d60362864a403012102c25140c900500865002e01107040100d480c1d07900c00d500036080703611510360058941c40385282079a110100c3d07110b10000a842140810404c0d140c9104011a031a407281d0700002522919205550201b41c2c0c01001307003030148000441c900320145202d6889240c2c420781d225640c0c0e20741070101144140040c0c02050783c0c800309208002c1403a801030120380e0000c0208002c002d000b801c01c0360101940c8660340000b900035041040c51803c940c0d000000d07502a841c0318040d03c542c1d80d10400120744009091068403020303402100154042802035a00d161106040c9000305107412207107824074500070003a84448001507421040b0814001c0800c02914292011141800036007441600244107011f80e0952072241e540c00941c0100b159942c841000702032400000341c80c0c0b0391800f40ca8400020300c0e8210703000b92482c03c007007564102080905c100c500b4254440e40416441b420214200c1d201807401218010745 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 371885089 1250 371883839 371883847
    0x30b0f250e130b1309050a021e042a0e22020f16140604030801050f1f03020919030c1e1205010903030c05071115040504110414010503040308071202 65
    0x80d00c40e0114500c4503403500b1804602c64a040050000800101c0d000c4c180e070078078007428003001901c0426a16251501160801c55030002c44550712086c0d40007442d910344c00782c50a100300c1c1d80b401184810480280140b0a402044880264242d8007034111110f81c40d071080d0344601d03c124043c066020400804041080181400421014400c2591201c0b0014080011652041c0e0030407202c01100100b9120390800f030400d904050b0f07809490300206000e00b912900b0b0140100003151a812401240c81161000242041b5000d05000d00250302042c00c0324002c20500c8803070030400e0758140780707281180e0740060003a404a10700620507116628072528000c40e001c40d0380b40001d400d161610304540b030501a03c000202039500c0e24001d02140c283c4003660041c07103803e00c4a400803a12300c4070300380359400043d5040c03102941c0c0807180c16014400c41e0000340d8000d10344102070084e03580500181c0240d40024405008420350140156000d00085800a000410450000f0003141c4100a0403003404207140c0d02501f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 371886339 1250 371885089 371885117
    0x1206040b0c130e0612070b0301150e030118020906060f09040c0c14100c03060612090201030e250807030506180a02100f08070926160807030b0f25 64
    0x2c4180e8800260b490000d03040c003115180010010445c002c100c40108100c82c90805620300c940014070aa0004486020764102054041c4100c01e038401001070080214400c03d2a420070071420445059005202c8000040c03528103260084441e100f078040d14407410030b5440000c01014041c0103590074204040000c42c800007a8234032400d2841d58451401030702e10010804884011071b201000041d08042c1846420080143c0203240c65004040c00030010420300c115000582c050445400c1c0c50030244076113189521031510610141681421354403115a603d50380f1b0708401d588041d03900010304141c2080011541c0c10700000d510b040c0c156992000e840c01440c1f142c001030180040c668510010812120030810780691114060368420b40398100055070904020714119007001c1d46204007120312510b42d480342288820842c0030205403102e20a42d6040d43c4070700105441e0105031004541040b2883c01090201200702100d610902c000f5803071400701885075440e0301002d10090f01102c00d1105200c80000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 371887589 1250 371886339 371886367
    0x6090212010e1005060a031707021f0f110a240e070e07170103150e010b03060a0212130b0a050402060706110405030f0a0b181009060c0305061206040b0c 67
    0x180c0d464180b02a00701a0300c08160401a500000d080d544206a164000d000040060401c81c0c0c040c1c655540701d58503a1814404121401101000203540d0a412800d41c5041135110001411403507656490480c000010401a41c0e2a16900002030113401d0b2142e9100814031384c4883c200380101484400f0402610007013120b8100740550b000314400b6004c03101007000c080e401c144450180c0f0045504c4020703540c91500e4110740036192440c0784410316250078046680361800d40003c0011080242550344a040c4a51490000c3d8041c080c01c44064500718001406410f144262100e41c5805c0103001040390349000710040200001402280e000009005c4600811014451002e59000302100340d5075480c04c0808152030701d40500100032040c0d108800440000d2280b52071160001e4101100c6c030014505000411b0a041180910070801450050008280035058002ca80e010240c1e4a04112a880b01c1c07007841000010450540450f40c8184003140008801c2e0b50200e40c0b10001c1244c950811410f014240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 371888839 1250 371887589 371887601
    0x301050405130b0c09120d020607080703060e0f09070812030705090114070c08060c040b1c24060e060901020c1e0d050313050306040c030609080f0a081008190609021201 74
    0x2c82219400b14483e000c600700021b101100c000d955001700121503107034a000f9907070740c002005c2104103c44440403408260203a041800500105a011005813409180c4410002030485105805202c1c2c04000118490003058080e411858903a00300d1450307940020a1b81d0035442003009904020101c4003010400d0314400240c40041e1087c106104650301d0080403519198000e054854050380802c4108080c480f020101c441800c032052007a4240002e250540009004040030f86600e110b000740ea0b030708038006142c0303c0c4080e21280e03210185030340388900a11480d4000c0461650143e440529060403500d060075044120042d028060505046032101250180c50044002c07141d90380301280303000081001d200c11601901c0290000e1000e0301d490317282d1010b0000d944c070010f804c00313643e40c0c00d1401b072102c00c0044400c00705003106500d81d50411041c00420044084030f00501c817086411000c42c03030100c0487c1a1018021242511110b80480e440d01001424031030001c0342e10061402c0c140c51045403e0041c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 371890089 1250 371888839 371888851
    0x20301090b01020f03090102071206020d0606080901060e0105280f06020a1109040201200703050109080702120715031a030111070b010f2421060f09050c0301050405130b 74
    0x200380702078150000ba01e00310300411000c3c46a002401442e000da64005031160440da18142032052204c01810080004d11410131206020303410520003041440d0085d030f0b003c2c001c00c1a02b00810480d40d440d8010038140c4020701569511540050800109001103181c59501500400c5900741d440e0741c030080020750305820b03840035015802c55040c401c01c0c170101c851140d081180c20741e0388141070b103800d9000034901c64005608403142d51040b061040400e1041103000082c0d94084001c1000d51503a042054182d044214101e2003003000d903050900e800404241d01049510301c2da01023804018810b0f0a8000c2e22180000c032407020040d50b0080d000e96800d0140145108071000650358400c1c990801c070400c414140c100000844c50400b040100c001c040c8800d40d840034614881100c0d4020303c400031a003d144401c56254501c94a0b89180306812403a8000c10407140d9000c00e506241d40da0301c07071102c242c40003250f402042e448248010851410240c0225500030016010607001600075580c148030300e001a00c1e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 371891339 1250 371890089 371890091
    0x50f011b1101020f030402040c09150302280e0105031b0f07030305010f120b130b090606011b08041a1603050c06070509090a0b041e0209040c0507030c111302030109 72
    0x2201000c603081050300d01d5070401e000080d441c20425083c0d40b51544405000240500d0750f80242c0445540b040f440b00000c1c3c00c4600c9034940f461f4040c00024065000440000d420480700c5030340360b81500028049050b244010b440d03502e00740c51501c00544e00c40e00000c01592501c0e0000342c0d80180c0d024401d00500c601c1d880601510703141c00741410b0040896605801c001d051003c000014090b45100d04c508a41030340c0d101542c540b45907a0003898529019200f0343c0148900c0c0d440c420b12014a00c00310340380c2d00c07503d004c1e0b035101c0f074400741c00d440948408200032000d440c0c0c40041200744003c0d06500031000741e00f41100301c403510703168041c1c1126130085c2c04014190000703a008205204041c034148481a0841e04610340b1500300f044103000111031000250543c2a9a50b450103801c1d890b469940002d40001061150b248281e41c1c10403031800070750b020320540c611452600c50500c1f0078500500c10307030700309642650b40ca407503e246503a0b400d61321301c0d00c1c1c60371186c0c00009003c4105806401d07000441c003030546000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 371892589 1250 371891339 371891381
    0x207090612030c082a0106060342060c060c02060c040314070806042006030c0f0a0e03030a030906060f0f0302010f050d05132f04020901271a04030804050607050f01 72
    0x701d1b084a801d5013001040604003034000348008031150b855050b50311058428140190407000c140c950503a07000c8960380340c003500c0c4030004074160013052400c0701c903014082c1408640d0b8454412038644204403240104031b54280418004a50b41011000301780748000c00311103429480300081460103100301d60072240c0888241c945048140390310320400b402c440c141c51840c25030520304105c10207406152825036000c000814038001080c824100d0116482c0003406881da982ca016500401a0401c21006d450310390501030b0018662524030214800c0710708502c00801d0840c00c5034011116890810038400030800b052014007844501031249034040c0c00880d0b0324907000c8000b460400c41d04907000c00010040c441c98005003070791040c588030b042e220070011100140c0c0ea14100005803042605041d41c000600e024032403202da2045100b1024003034959244144284400d000c0000050384907601000b0140001800104010b040c081c0c0038105940c461402e403040202c0d8152010300f1a81e12421494040000807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 371893839 1250 371892589 371892667
    0xc0706090c141c02150703020a12201216084608062106010e010e010b0a020307030318140d0e010c0203070b0702061902010c0207090612030c08 63
    0x808031400d248075480d1003c110700410b8000808501c01c010b0380380707881c0d100022807104161080c480303414080d61004000180300b4008100401e42ca800c170f900200e894030f4881180640c404000b50041d41890352040141c5014400c030800c801c002ca01880840d03030606c06100750300307101003118940c901d0300c0c80740d000004080d000f80000c0e6a0070741d10b20700c082451a00e2081065122540111500da201505603005600a80b1061092003291200b117180e0506028220021900d0096804554106c4221104400c0c00b641c071006070300a14455a503038500941c1c0701300084000640a5040b14000010342400e0440625840d210390440003000058100d45403c00c04081c105039030488010408a4021318005c808039003107501007583d41006014036142d083e800b0030440708540e1403008990b40c9200d00540224822803880010b4064100a0205805406403900c003160b07030078480c41003800f241c00b0b00b640e2140c0000c41e6101500d09031862442500c103c001003041d02402c1520303e90007480744004400040c00740f0846 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 371895089 1250 371893839 371893849
    0x3030e130506010c0b1504090c240936050a050a0e0307060e01020f041706071404051309050607090e13120516020a030b0103051606080c0706090c14 65
    0x103802010103051900080c0030050368464184012281e11814401d92602d4016160b41c10320b0010f00c00035800b60a03c81841c04200d41c1e249032004072090061262041403040781501800c01c02554480000303401c400040109120310480402d160904290316204c0b0031000c144d942c542304042040000b441d03180e2003800b400c9621881171070703400100e0410030016446095000d076142d21615002505460300d031910314044010030340c1124402880c0300c0c001540e4503511051988440601c0d61602202d0003500000f400c02d074044d401d290b0501c07081c1c03a07030286060300b01002c0060300750300c00400e0290320b0f66800030840003d004001d11401030f0b80c540c450010b024942080101c10760b4000b40008500700c407003a00381d07000500380c01d140f10b02500942070450300d8401440304a4100d001404010303501c070b014464000103101240741c800303059078001d1707080c0c07004103000c01d1000c880c031060380c400c20001a91520003d820300074107030060a4590b12401000c60800240c0d20b445182c1d914641055403503003118a00b0f401c246c030704 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 371896339 1250 371895089 371895109
    0xc032303180a120e210606100e030607110f0a080c1605030304060509010c0c06090311240a1103031503011d10020d020409091a090703050c12120403030e 67
    0x16070402050400c81d255603404080d0000809a0144440c60300c103226075a484405492400c4c0002c840001040700c8071403019030b104015074459000d0310000c1c840c00c8070035220f00e2024a0800300a030041c1901d0300c1c0d070882191211540b840707009480c000c0d020076145260061102c056030364001c030845511103481c0c513403031401c0a414800340c903200b0058003010005520081f094030119a5103050040e120302040005031101400c400c0300030300c82520200c1c0840c2d407580254641040da8040c50083d410310030294188503103140d85891600c410002d4140298803502c8400040c60f545641c1e1501d6040d10000320402c0303207140c1056580d40e020982c540c840d036034039040034400c0c2d0f000403440d1000312000c00e06006c40c0b80d4a500ea00741310018640d800142c10f1700040761b107030115001440101000c00ca808443e080030b070700070214000d46098156041c00401c09010000a244061360741010103012960418020040a6010400242ca240c05550200607145180802910085000e40c480b003011004d024100030801403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 371897589 1250 371896339 371896381
    0x90308070213240b0703090308030a1d011b0824040e0f011b0f0522050d08091201060506090111161e06020d0503070e0406030818090105100509010c032303 68
    0x201400305c0400b02c0da00610140840b038018801c0f6543c0e0301c0321003242c0060481c132055404620381d80601c000d40c014055200d0280d602402070441d250000080046034030540a4452440b40810103426200000b50401218141c480c01070000890300d2032429640e003000114820f02c0d0250b50740d0302a9902c0c1b1030107115107080340040707882d0000c401420210058110f010b894900c154100e110750050821000400d00c900c041c1400801d0702c0b4008005281a611a51192600c1d90051102032031078621050140110782c1038a0b0000c0c6a01c1c1482a4540111a01c03e15a850a065440398040e05120000c00000b508080c0458404020701d03c0100c0301d014080000380d078440c10466201e86072610f0482c2d4484140e0b5001105ea14011540c1001c00b40080c026045981001c0e000740d20004c0c040070001e040301d0144c6540d03803041c1c41020460780d807841080780c62607030031408801254040050340c660b0740c0302c0c24541c02068030906054240300c044803400900b82030726628603400c848001041c0102e2030003403031148540342 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 371898839 1250 371897589 371897609
    0x71d0f13090c05030c100c050307020d200307140f01030f1802010f080f06091305010c050901030f0e1207020d0b0108030901081303020706050c0f061e06010f09030807021324 76
    0x351440c0e0105190381d401b600c2c1c010800000010f9041048402d00444000d1500242941c26904050030a2504200400d141d204403440f490810b030802c3c100801e810b0121580310312407a000300c10710418006200320a80b019410103603900a0031032501901c1c411f8182e889250000031441007014030015056031201d0352018103000c03500080214031040c040c0341e65880301050b19244459218401502c40b61a11804020800d50030b245001400381d0f4080040c10b4000000d80c1c0900c964030703100080310201e50310f110103160686c211449661100300100002e0001c6071018042080400e200d8513040c0c103600003a04803942942001804a4030b540e030003250550856588954240340c4e000e180d5000c0c0d51500b00d44501c000b0700101050310121500e051110f20403850001c01030359a1840c0041103000005402d81500c0103203c44031000c600c1e1035103d080002d85480742c1d501c401d05507078115200c00380a6000244203ea0201503203100d039019204600034180081c00201d40c505940440040032014030910f50000b01d061 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371900089 1250 371898839 371898853
    0x60103060506090910020d390518120f0f031e0306030d031d01180b010608070203030133120b2b020301060305070b0a0206010806071d0f13090c0503 65
    0x104d8400320300618801103d4800580d101030a80e069009030019154482c050304004600b1030380380c0d8946040e01118425504003081050144100b500d0b50301400c4110020b108140e508103132a820100ba40c42c46461000e4225156410340518840ca040d155819555036500b0100c1c00381e0f1480f5aa1030428207404146c0c030f58034110300c2c2c4600440c2d41c48601030380482c101900c0d4545410303c2d90092242d4140c002050009029103010720802440007491043c0844000c0c500c2d0000141261203a0301041c045c000c5603014504d140d19113100f0244800b614119015203542002c071030607480c2920f01d505100310301c182d103c4025001540080c5001c0301c5002003401e0003284603113202584002054030341e180f80b508080c0320700c661301c91500100380140705c2908010b105e4480c1035004510754880c40050443c500442c3d080358080c1e0b0f00c070b1003da901d8550580e1164080f4440c50400c6a07460b01582c0030302031403034000e0804450200c040c00000c0502210307030082c24038103070f0f40c059410a02154a00c2c803005803030158014180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371901339 1250 371900089 371900101
    0xc0706171e070c1505010603020418182a0e010801140402060901120e030a020307021207030308040b04080d06060e010905030a08040e07120207050705100c03020d0503060a0308040806010306050609 86
    0x400030005107000304012800c1da403041002859401500380d03044c5090204855038460714054000d50040c0100c600d4484a49411082d20b000ca008070100c10b165000b4940400c9525030b00d00c200c1c3d840c2d810354201e14214070600c98106503ca110040000c2103044091031407545040e01c07107030071201c030408250b1503103850804100160310380c1c2084802410080c0390807500d080c131101c1719600800c00064100000d000001d0158080b56001010b4005503000701c64403070300309103103d4200d680e03a041880000d010512110001e0003083d01104d42e036a01a020b482d1503442d08414051070300490381d2176040400422541082c80c951541d00102e01c80140c0402d42c0281004401a190070107680500c0c42080000210040090a080d00c41d000d54001c0040c8040150340300c50381c80c6446501c404e00c41c01014003400307001c0d04c1000820712904140700160303010380107072021007031200e000c4407240e10003052160405e011200c000f000404c41d400400050006402501c610b50542c50038005460b009000715200310848014802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371902589 1250 371901339 371901391
    0x12020304050705130b04020c030304020a0b03071407031e02250f0302040b0102010e0a0f0219030b16090f03050105041406041203020c0a060203040605090706052106060c070617 77
    0x7056900c1203d251450b44500e6066a0180002076485d580145c0041064031416200101a40c0600c1c400c0310b405484603251903c10415010440d05180011404062001d07004a0b6500802c00640030307190480701400128a020491100c0b00c1c81603006a0040318061400800c41c2034182c0030009001e0541c42c420f103009042c6280c45d0460002903c1181d0f106120002d44c2e0003540720307114400640c825141041d843d8108034030040d003001c0d0240e0003005401e42c405c1d85040080c03081019250b011991815035100d104d4544150790601820609001c2c3d0310070082411010260404002c52044001140625107071410740c0b01440800810b946542c05142800002281c6508050303284415150060f10398680c26406403a0070711016020b09854400010b002c00d01c400c64001a00c500144012981c030326136901c40c03c0700e284c450044056100100d0300c1c0140d07200c01701c68001035040440201000d003800c5844011a040c401c40d81d2218004c03d402c500d03007482d407410003014164410158000c2e240401e403a40c18200d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371903839 1250 371902589 371902603
    0x7020d08461e14010b1b0109060516031506021c0201022709061e040b0429030601140312030601110a110406210f1a100302011202030405 60
    0x1400c60410320160141001c0c08012040380c82140400b070040784070140324040d050842e01000e41c070140c00c01c090455003851100180d03040340c6050054501c0c04408074488001d000c08040c01c003e0075505c41013184c000c125075009003400b030407000390040c1555181c03007005001c9800301841000ea05260080c1003008a07004180c0f00001d0b030844560b4070000e080608101e00a01c02c40c156204d04201e007500d2401041d04580603122100c0c01a1a07540341c03a103441c6d0400a440e19922020161541041da0345003481c20147c100c103002500207030022a0000b42d801d4400325100b01c4c11f1000d9120300400f03450717103001e2a04201950042a8010407541484100700101e0b40303071100c2c0d22005010550000204802c3d034440c150501c145c6620f030060700c0d840100ea00d04001108c08460300507200e18200480480d40760486c00704002400044050000c0100076075941c24200714002c0d005548901014440c144000455401e582c490b9140701400151241148005005891605405080303540b061042000203280001d0b12 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371905089 1250 371903839 371903911
    0x15090a1212030c02240709060e0306060609010212030a141006020303060613030b1f0b040f0e070215041b0902030402240d020c01051803090901090207031707020d08 72
    0x1c80d0900760f2034000da190040d496807110342e608054020602e002545104c003030003003049a803042e40d84c03951040102e402040c00508194142c01520105076140781007801410030341410b00565428004203102104250402c03135a0294568030350711201010524003250b1640300f2640036650b4003050800700c2c0250742e8040148800d00400e4001008150700512a14040042d503212141c211149805d0f40d001d0089108404208001c5070290400b007080701d445401d507001d54400283c82c1440c546880c0c4039100c0284040c01c030707500707500034403680135031602c0070000c7c151040307010301e4155407050495050307900c481c2a1a401060114414000d2100590311080840c401100f51040a0584128030840703580a20604640b500c196200041c5081200419000940701c2c00e8000b41480b40148009a45a103070722418016a40c0408440018000b81d6031300d41c040d102013406860546881c3c00300b41d0b41d1198982090b0340c0c61015038025954651910760010009030311450084140d40081d00351030020403500d0f900306803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371906339 1250 371905089 371905091
    0x3020a030e0f0904060b13061a0d0b030601240f120504020f04050915010b03010b03160504030c03030306050306060a030c050103111c0c021009030203120408070215090a121203 77
    0x340380525038442d140e2600911004103100b4060400c2d02d0300000070150b801340d40f40141c918032180c2d00252110300c10101200c43d49582121094902d0078003030b04941c40340307801c1b5030015a030b90141c541035201042070328082d24103240740030385084200400302d03600b59128034030004100301c88081d44049a406000b250345081c40c1d007804201c6450b1480091491445580010b400a00e020b040240c0e002001071441d0031150f40800c138241c40d90f01d90866030711610003401882082c180410208a0b450407000201c1c800816074075000d07084c251a9a51407110305811350080d000651150414485d43c94180301c2103411141c2201c0041c0b07054074590300d050045160303220740c5040c103680b400020307140c1c0303124012034501c08414182c444600f6584580c00c0010301a00c6e40d0301005204101415519484034807881809580540080d4140034144d8102034075050300400484080d0b400341300d840c006884904005c0c50120750b03400810b49907450781303003808100c200ba83c2c00202010b1100410202040c11000c00303004035039481c0345c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371907589 1250 371906339 371906357
    0x303020c01200d0f171009110301051c020307080304030c030b07030510050f010c02040609020406020111120f1005100906080603070e010902070c0503030705070602012a0e0a080717070602060403020a03 88
    0x1500f17454070741d481c851240754654460f04011034070081c0060703402600c04000702001414048035010a05000c24002c8540100036000d04501480d0b00740d840452440c801012100a01d840b072411750300350780007640101d403450300d0300c40c0901c101b0444c25401d0380d03c103105240c2004a880c1c905100c824580062241c2d41c0101600b0816810592143e511050f400f13030050424400256a428050003e41c4140b2a0500551800200c03180110f02103040741d2180b420031101c1011030301c0391410401c00c9180607000d100f2950b01e2400000ea10784565656523540d103d1910f80b415014542200070380642001000345110350040c9401380f10072800c05400c10b040da00c0090f801a1520b801d440e140300b684125400c080e07410f220210f512402c000c400078a010a9512550081c40721408801c030245080f59800164060a52201c50003514035214000c2210030309802410b1710303040c598560f10707141015a1904075002c1480075600801010304108041c40c014141c6100078456854140c0b0002e4403000480002401c00005034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371908839 1250 371907589 371907617
    0xe0a02040e16080f06010501141801030f09030804030915051c0f0207052103010f050f01020c042f030c16051f050f0906040506150402040f0303020c01200d 68
    0x44408502111101c0107082c1d8658894955900315404520082c2c40b5040c00442da95200e084502d42e011f02000c406414284825608801c44658840903410140c0e41c200a01213401c59009440c0d080340a5210b04100c0c1c2803506005001c04500d800c17a126041440754000940c41e4010100d0b6501000e44100f60490092410f900d4090000da825100b209070000c50b1150600401240850010740c01011110305e2031814a200a03990009220790940080101003c1140b82024403404560040500c160341c0e03150741000025084400841241801d052080c90445074041000e0380ca0140c400342c240d0032030861038040317401d68092003803080070070410f4601c80381c081c100f00003002042d0003580000c28418028600340740c084001c1508441e425191000707080480c8141340040354040c042c0760403c000e040c80da41c0d000c03003c0840b0410b40500d01d4000c1c0d82040005064030800a10382c01540c801d07405030031090300c401d00040c403800542e9042c407194107030b07203072103000c0c91100081ca90304c000c0e001e0034201d800303840c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371910089 1250 371908839 371908843
    0xc070501090b010f060f020f032502040614010e04020313060905031204060506010801140a140d051e01110412020f06070813050103060915030609080702030d0e130e0a02040e 76
    0x4441c00404880c0b0410001c9003480400c0c0c050400c0d10400e541c1c8808095021208907528100501400d400760001c1100801c440c00c003038000100d803580500b50603414a015400f2600300e0320701e64010a05002c07440f030181021f680c0720280715045c4008803015130550601505541030418640710040800f60340307020803810000c00b80280c0d41c0c14409403040e00e209207428209040584001c803003050001c0c1001c0c00200c1c0b02c000d02200c035809448013520b200c03241c6003080310002101d0846400c2c030f40c2c440381e880280740c001041081480b4000030950340c403001e290b001c404003a0a5800c03030001d174140304509102c2030141c2058102218510354040301d40045161620b40464458425440060001c1c1000601810b20240c02c0541c0001c8440a0ba001c2111650f44e1451900f01c42e1080c0300d50781c001c40c0009042011582030340240880d5400f54404610b002e4042e400241f80c850251500004581e045003c8541c910b00440303807003030100760880d061045c2400010302549611174054001d00c1555070782082d890490301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371911339 1250 371910089 371910101
    0x9040311030c010f391707080a0b220f020409090309080c090105101d0a090c110102030108030a05090303040b0a02060a060807051315170309040e0127080d02030a02120a140c070501 79
    0x2041d6400120f509240038012300b105001c60f0b2240c83c490074600415824180405d900300c1501c010001c40f0064070303d403000c070000707410941031a0060a4007440082803400480c401c038840070384a40c5409844611301000c407400c1050f880c130080e01c6141040010041519010f041101004007803a01c101da41d8000c415581002906e5496540c0107407240001054880c8241c5c400400c800c200e456100c000c0310350031203e034240e120901560505400c01c0c85220b00031340c050740140224a034004c050302e0419445408a051541001040000580c00102132024195451040c0e00140142c203024000860904000c1000382c004000582c010703580da03145d0880851105400c05c4007030080701c031500c404850a0740c140c0d542c0b9008001614401d904d00910505001d00511902d1700710710326040703203841c403034024510b0241d43c0c682c1000c2a1000c00c0c081000380b40d4061903100952040000807030058890441c401c0e413024023100149185034892528500c0e90903c000003054990000842900340d59540440c54504d002d051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371912589 1250 371911339 371911367
    0x50c1018030609020f090705090d0809040c05040f090204080330010e1501081e040f08040f0f05010c020112180f05030318060f040209040311030c010f39 67
    0x4040c120100410807140c204600b0140225001451005400104030306500c0681c2c0f00c00210b078042049407028201003004c4001c150242100e103082c91000404181500e800c9051040020300000c0c0c02c0c0180c4404110a401410322914110304240c208218283e5a2060340389441030b07808403074500709044030700401e420000340e110f05511043d545c1d1030b54800c03e00c900031765580402e010303080280c064651041107034612440100082d030103030411041054594140141041d60503000d005140d80114103202d0007030008003000e03603800041d00d2420b0340c04460810705401040c10000c00c4004140982c2c2d001c2c09481012402c8040000c1030781d412651000401c0030135100030101502e6202c80d50901c68007001440c8180b0303100c50050780c041c81c000718040d203c010031241e41c00c9090341070005c540981014500b060b44a03200341480855111070481052440d007021110015507916907459900c1420b2501070b040c0840b918100d00768100c01c00d10750484001030846085205245003c0f210902103200d0354103121014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371913839 1250 371912589 371912627
    0x8070b0f0c19030201050a1404060216020910061e051803010b04150e010e01060f030b010201021605031e1c090813030b090c0d020f0607030e100c0519050c10 69
    0x4001c4030915145a400c0640141d481c00c6c000950f070150601030b4100000c55801e0003001e66650359034660003900255200c124081800e1414401601c0f000790039401520074602010f0000d00d000c2c002400c152450054002182c0141e50031600540c0180c240d031016004005191440042c040200c0d0040108509072036220b4180384440c58925a07100060b0290f030344d00c506001150703803101c07030f540c03011a420710958000440d21005a081a13109510640c100c00051001520b0400d01102e4915980044002600c0a03000001d900300b030200b0b80c2c4071034000740c02e6001c0d21030b003806091a610310503203403a4121009001c4d15416101d04210460045550028102c24540c4e0303055224100101000c00446241c0c0c5144202101102c86152001e080e400184c0e00400a41c00c080031102801015080041d04505010b80c030b054070420b994403562150040c80b1103596800c415035450038030074540141d60f0140a0303811003800060002c2403001c6400d4404060548801c50f44592405040700d0042c40c424038903100c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371915089 1250 371913839 371913853
    0x12070c02060a03150b0c120f040302060415030f091e0f0602030906181908180a03080306010f03050f06041d06071715090615040503010905010501030b01060908070b0f0c 74
    0x40c2e6016031090f49104880e040400c1420b4a41e40840001d1140b0a4000c015034040025804403901391002884064000411541410342d40c0e4003003882600250011040740c0803c03402e51100c1a03040c031406844a00d010420b101d0300600d610340c6403a4006c4000140034005850308040c0034864000303000e0b40650345c010b904540d68940302e80303401e4840c0b400341c800348021640900000c1200c9800100c4107044500c002504001072515550100281c0c091b0401500600030254400c0380351b034070440a00001c601400405a8900c0c1c82400106a00301780e040d10300602d481c19090041d010103d26110387d220034103560021301c010b041e405695003400d10001d0351800c1c1c0714683c10415107543c0800e909124580c0c0d05146885900c1e450030400120345200d1480e40c0061000c80014120b10b022180f5550040c0e481106618043e00d40340400d007560320881050320381e40e448900400402c60b181d101c1074014209850300600a9081c41e03161074482c2c00034070034030369554030226240034541a00c000b192006030583c8125906 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371916339 1250 371915089 371915107
    0x118021e0306030a141501170d031503060509010906050c041406030408040e040c1a0901020a1b0b0a050c1e030d05100513140a020a0e04110f030c0c0106150512070c0206 74
    0x6c1e41501407001203a501c0c515000240d424440490b03004584020070182086003442003040303009001c0242c207042c0303024121000101081c01441103c1c0900701d114004a1050b126042c80d0092f103501902148110004100400480f00080c10f000e490304000c55106079a03456605004d00c160285402c5403400c0c46069042c4020003440d80d429030308503040488020345010b24415003401501403400f000b405608541098800200144602c0204030070581c2203140c13543d141e0076244119000a440103010a10010700d2441c801000c00089040840036a00c106c40150710010280e107901407071800c0300d10300341c840002c00c5000344524030110280c4409005646100010000310010f000804404014042d0050202d00072030114022142c007060315481b601031803407030001840b00400640064891000003444400c0c6c4154040303009600030b41080005544a44095105908640069001d085050072000b0410f03c00d42e0402c0030303120030342c040c0704000e240c954074003c081d0f60b89440d40f00029849080001c900072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371917589 1250 371916339 371916343
    0xb040c05030702100203011508041502030c0a0e0301060501092105030a0e041d120c0f030d060519031a25091e03020d0b091002040e0118021e0306030a14 67
    0x48110307160f608854840041d010054204e01c402e00541000700100040030164038000c051b9682c02c41d200d42c01e0080f079404014118801c9070800d44054480081c000307900805164054000d2980003c01c03002044035a24040011f03024813218400c1c06240541c605010b40701c50085030040038080e4100081d01d64481c0461801014075040c0c0810901c128a000c80d0b001c1c0d42450050316007540c054400c01410a00c07804800c00c4540d80103968082e9051050125181d10f5547c14400780071810a80b817400b0540034102400c000c03203a0380c2a1342c852081d02c007034082000820849060380c6c032100e1034020b026060761100b1b40081c00c400c0d141110f500b00388009040c000520369000c64038030100d800c1d8a0212051155010150100e00041d00c000396102c6c10381350014002c209031100107900b1400c010219a80c01114103d44026600107134014098a0506401001500741c205084a50285501c1c01149000040000b480b0380141d05425030566071300110000c0e0013500c040203a8049141c0081d00b401040307083c0c80c2159 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371918839 1250 371917589 371917591
    0x10807090b041e0b0c060c090a09062c10050d030e18040210020f032a060106121a13110f07060b0a06020309090a09080d060602011a1504180b040c0503 66
    0x3800c00900c83c0e4005074400388801a40e0405810307001511494884211400351900004180b5071702a1800c007001584848a21950000b02107150380c04940004140b0f61502d40f6841d0301080701e410040c40c00b01f1000c0b816140e094400d0341d10440c0d51100245050400322040701d2031340440798004107040381b041080c5450780341661285108640f070381203041c521241241c4170340c00b011030010340b9070091201c8002c0c02900f106214040c089c81550741e00102103d4407581c5000300a80c440c50228006030b0003030f541d03c00c40f40107514607040032601c01d078503030a80070021850a07c9040801600350340e40d4112a1900885131086a52140c0c030a503449444262505000004048143e8080e100341400d44d40018150700200a0322101c00c1d004084191503035420b071049015111403401120307008020820441502e24a108178005040e00740d00000b02c511070203100d4881001d40c0b0204e0340c4543c6200031104034154520781201e041d14020650301d00104843d010120150411010300740e88a07003060300c050b21096012001d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371920089 1250 371918839 371918879
    0x2100f0c060507111b010c02040218040c180e0103030503060904030e0a0627050f0909011413051b0a06050f04091404150e0a08030627150105030f06010807090b04 71
    0x41c51024420101c019031800d01e00034a46c0c0822250300c00000945890350160030780322b550344200b4000008003c000343c100c03000613442601041c1041c2d0a808513560150ba0000901100c04040100c4c2d415a05c002e803ca000c000d22079881045010300013070405200c1d50984901c2c01010302104d01603602c6140191800c0b48401c902605004d05260703900f0306600040101e8101c80300600091004001c1718240b20760084028441d9105640359000c103c0c56110405629100b001c8054008502d1140c5142103030400c01c014000040040002c03230880415607034044c03a942216500d00700b06a90b420400e219a1640c01a6840300811507c0c040031600b8020403a00443d218910448050255054030080705080b601081c3d03071540181c1c05450342a0004402000a5800800040c0700c40307210912500001040421006414501381c21a414003003800212180b8105403082400d0042c00c601c0e021084074a038030001001241000fa0300030114000070700618120380509038030624a50f0b01c541310811107400c0d40201c005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371921339 1250 371920089 371920093
    0x1020d05010f090e011a010309170d0f05010501030b09060603090f0a21020f07150e130c0206070c02061909030b0f010501020607301d0a0204050c0702100f0c06050711 73
    0x918206002d040c490081d444a0100640c0031b8041da030001100101003540c01180c0c40300c14000d0700d29070a48401e020700307100107004102140d888280d106480036610181d0009060505000507007040b40d03a002d01059104809071a11703034883c0c1e1215040307450b180d001d00b01c14005000d0125600180103251441c1c204a10b0984003005003500c1c80da0080381e0b1150600340c0c130b0a094004400a107e10000d5010781d92903100581742c8564001030440000c1c03069181c1e1850184a169105106038400341c0500155900c40c0207401d1240562079150041100c2c0d106441040141d0104c010700280312a000380305610103541c210105403200d2600d4241004050400c0c002c490241c8220000168810b00c034160411400002c80000c1d110720004240d21171360907011134804a50300f80c036400314030f04542c18001002c2084034610300a016003a03960050004a80d00581a54a0298200b2a040142e140c2c50a10a440c5000e890004510460118100d42c409110000101034508010510800907031000824000e0004001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371922589 1250 371921339 371921351
    0x703020c041d071a0d050a0f0606020c0a030b0a1103090a0303050c0403030926031305041a0303192606012d050c1603050102070b0a0204060507110301020d05010f09 72
    0x2c0064100309442c04018801e034003450f000d100406803414404081c2c00040421410b007840b501d10ba00a903207048401d01269603580c242007410711441d0040500528140c005000100d40c0ea50100d044d01145000c041d0130b1407804d001003101038100c3d502c25046520b200300f03616240d090421103603403030354040e000c1980040d040401149002c404803049408495050b142d101d10382d4034190042644404190303402043c54000d5101809903982400144607008082d2680b0400754106800c000072280501d04801d10050808240d0080d901c00004440c601000d0080007410701424030f0080b1240c01808262482d51a006500d084041c2200c10016014205c00d88505400003109000040c034582c6942425240c0d402c503d12030422280980020b0504c215100140c46541081901c01c041c81c800e81e90003122117a500069070020304c490415215000030707104005501d441e24200c001403244c0a00c6901504030315070100849099a8254100c0d5450a83d80350f080c0002d44c2e50300030b1280300030014800c00d9400c80c1030070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371923839 1250 371922589 371922611
    0x4091d25140915010e090702061e010b0d0504240b0f010c0309031112011d0c0a0303090b031914070206070504030c140301020f0f0c100e0a1b05060703020c04 69
    0x49881a4107240141c440c0120ba5039003c50b01c2e00782010300841e035040c000074151014490719883e4019200e00d00b03d400501060900850090316410000d40c00c6020b04204030041c013400b00c185040740c0061160100110b0140c4a9033801218005400340a01c6d0446040d000003025500310740000e400d10108480c2c1980c10000704c0019140d0a4001c0d0000b40021911a0b09100080350743d80c0007270141001820440350442034107501402c443e403e4554540350781800910f1001c00d0410800c09816500580c0c0300c0354518074658010748113620034028074141c454040000790868244100202c401d03e19210f09002024184528010074801a2060001401054002540503010314110343c01c0340e5020039050303021880e102d074002c240d24580e10506d034195001c2000c0740012040c00c001e890701004e2a004140c0e204070f010074461800b52100b144101c03140c1400410488403001280450106801c1020031114a03032a0300102c1c1d0348051a00704035803060001c0b450109043e8005013498504c0750556040111000302 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371925089 1250 371923839 371923859
    0x30a0b04050c120a0e0c060a02010609050919030f020a0213020a02070501080112060902040908030108071706101203020708071d01090506060403140c0a140117060604091d25 76
    0x202c03d10050039880740422400885944030b510a0400707903080c0d03031003400580700080040d0f204d0481c40c0c005030744403c014410202d4500c102a044490f00c401007446444403242450b41020380e02c805000d001d102c2a506800c103000b4002444010f900924009a00320008080c800075040068401d00500c038111003c161540580c02c914161003168401d120080c826035a1100074003180e55080703030000c0e00d071040d850004a10001540c0a0400072000d85032081c103200002294031400a40c0c2c80040d4030a00500070603051148408080e101c03001a182032400150a09919141655102c80075900c03841000281d030720041c1c00d00760f1800c041202c400c811640d85030004c205444043e203400313070b00c40020041000003804ac0600c400014054a081e504c45a60070710014411000d40d50018409207140b115501e000d686c400074010f4694040080c0300c1990800c1e1000ca8079030300075402482c030f2295442c10404003c00c00805050159400101121415040c0024040c01003d08040d002090001101d000c0740102e01c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371926339 1250 371925089 371925097
    0x7080f07120c0c0f05070e0a141605070f0602090307060203070230010501060507120309030c02130e01060b0711010804080f0d020903030c0f0f070602030d0905030f030a0b04050c 78
    0x381d549070941c072840c03084003000b0309040d031803034040c410030b9940500003032681103500030054003510180520900d0008035a40d1107170010080c85060b0300e132080c41582d220320149019089600440c2082100190031000d40d814862080081c1034a40d4031000002003044a030014608860300394181d5940d00c1e541c020503030f50380c041c18200135403007448071840509840300000e00380142008000c25031502c0074408203031401c541e001c8e000000010000511081405207441498a4030703492803904100c943c0311518000d00114880c000240f003001050300c40b0880c3c0265800040010030280c0081258541d10034072143c40d41d00c1105c0c1211002c00703010070703c1c100d98040c4072101c1c82640c00c00c044c5071620360300c5807440b86c2550011101c04480b40d42400369030340d541c60810160003a85040801089020540c9000038074201c0307103954190701e541c0003903001e0011540c00700c20783d0ba4241c0d403120089884025071030318604502544c5901a419a0040708011401c2e0341904445507007030b803c1d02c007048207440b507203048102442 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371927589 1250 371926339 371926351
    0x30a0906050f07181802180d03020c1008060d0f06020f132c011802070f0501050609010b030118050907030506070503161b140703061d070504020a0806101106070807080f 74
    0x4007084c8080c05e03000313030010814159006100d08100c0d509000050a68010100680050340001e51040c1c844c2880c1039500504500f078246240340d0300c0c005e00018046d804212005000e400403a0080d01001159015280d030202084056919990054140b11182c2c20520561a9440cad1400b20203840042818031102c2c0d15a81d601845030503802d200ca822151515943c03034481c03055003042160045408801900f2480c0c0c0710350004955410000100120180c040c0c000740401c0d0b40c1000104130343c0c1c2401c3d07008000394003220404100fa03581c241c01d0710308102d1158400b03406405a5403c110809511100844c41884440c0159058505004045451500107032170440140408074501b0081411384207980c1401a081080303d0f946d50301d96407031400392404502c90301400a41c01d2400198540240310b640b0260200b698218180541100000d1a012006e049540104a1200310551880c0f14403680c1482907000002c503480d90800d070000404201c2c04491040011b035142c40428151000211000c1c0690 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371928839 1250 371927589 371927609
    0xc12051216050106090218190b180108060a0803030703090602040b03180f010614090903070611030109060b070f1e06020301260c010804060f140108070f05011b0602030a0906050f0718 80
    0x707001f04180300c14021000c21040880a07070401c0001e151400030003d1411b0080300400380301145541d400900003010280c001841200b8503442404a0b0b40e00205880d0310040c58600404d100400d404c21500a205a800800100d007000040211700d40000b0f84c094500248201203d405148003082c1500b02c2d0024002c464480e80da18628403403900d002c0b80c2403500f00d071000d815a440d20307180c0d99400c0101c41052443d217003036160201c0100040403051180d01c00038036048039000d1901440d03503a0105c4030a26924000c1c0b84405003903441e0054040a60902c81345030b8003e40456132961940c0d12283c0c1c0c411500003030646104119440c076107050002c5031a03040060180c6032102e0396110750752800c0c060448020014030307c6980f6480700d00b02c0708103942c406000704000030182804e5814610110180c2441e5007003d03052182034041c55581030a400513440080380c1242006840780ca5003010070018050508001c3c0510381040d003800fa01950000381507001d05040d40f00c0103903501c1301d80410b00d088001071192200039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371930089 1250 371928839 371928877
    0xc1a070b07080703020c15040c05010212121e010e0406050c0a1b020415060e090a050903070807020f0628020d0203070609061d16050406030c120512160501060902 71
    0x1442c05030390b1041e00b124003401d0140c03c00b105100b0440c9052080164000e50204e14803d01045c00022000c01000d48420310181510761000244c0c07414512520514844000a031000110320300380c00014408074419181030581503503035400d00e05a1509090b141a08c400d031611000c1100d0341c0044080300c114a81c1620344400b2825051007600101803c510180e170482d85030301e00c2070581c0070940158401b13405651144a11213042400b803100c03d00009064104582c540310078883c00d460000305442c03506a001c0c0400d0b41c1c440702880404c40c24850741c500d403504258041007403410070300864030072000038001401180c41e0041d205422a0f0700d542c00300b120383c0075805c20441007000c903806070081c0423142c0c01850041450741115803902c042d800341c0750500e1440d800c02080003456044e020800001004100c50601240d815910b43c0004412a8841c101c1c040107005808810040700f4010501007040c03010805884d90070a003c10034841c0059281142d41c1c2d440c181c00451031000c14825101d9410011400d4209 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371931339 1250 371930089 371930101
    0x8072102010309031116031407061e050c011506020c011701090902030111040b2101030305040b180d060e0c0411042606090304150e1e0d06090c1a070b 66
    0x3003030741d0308044c0c0030017614a4510344040344c00c00039140603080c40c1803044851440c41c1412101d15000e03540740d2600da0070a6008100c01c59014080100c0d0488211148140c0510000c09840714840c650045241e5401c00781c0782c4800409a02d14031088498940a8401180d221001107480030290064044c407590b4200046c060503034503900c09088180701400005940414040c013002d903420542c0300d240030440000d845110000c3c0c8621107281000429050340295043d540c001d0b00740e0280c4d0081c051000404150703a100d00c2070183da641018400a0074400c4103ca403070814070301078000a43d0400540c801c070180300c2280d081031b03c03481e5401c100b070b00700302c9041c40d0806071304084034586991007152949080800074010071083c08440e0107605200010340e5140d1034000c01c0300b25400b100c02c4450a110044030301c00c1d41602c1d609170a103001d801d00e1500d100c9052000c00000e200c40092503014027a1441d028109007085800c0300450295141c0384801044200b40c41c858000344d2080f00801022200c1060110369 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371932589 1250 371931339 371931341
    0x901060611210d020909191b051801050409090c0e07141e04030203070621020408030a0807140a121503020a0603050604090b0a0c09060806060a0c020a03020603040c080721020103 78
    0x514288041030241c5031551713020021b101503200740c40f00c11028620b10840d00f002c040a210f540004000c49104801405800c0c40142143c01743c07a0b10888045519071242849a02c20003c44002e8128164200b00200d40c3d410414421100d6000d41c001441c0c492011905260240c04c00320f104601c2c0d4001603203440d0780801140b8082180311035501900310184000310040e601442017070003400030342d51030360005142c40c80c880b600c1c00f0f201340451180610400c010b1100800100480e0143c80850904450503180e8990440e101c4d17884444846946002103078880080c2d51080e4401066000744c2828071a06030440d111907a005401c3c03000a50001e581034042201e01e0180d0003140e0b0050006000180c003a5141d210b140550400b200c0138043d01e0755072081c83c0140358200070200041c0a0a1030020914582640801c6540c4a000c480c10180300180c02c0000844d1707140c6049101441d400340415442e07080a2074402440d039603a0007403220314011010b000c92040139100d5070001d603150040890044a51540040d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371933839 1250 371932589 371932597
    0x809010209030c0105071a0f09100b0607080310030c09090c140d0311030f040303030915060509061c05030d0c0f05070c0e070e10020c0a0b090f0616050105090106061121 74
    0x200c1c0c0704486020030b4040c1000d000c0f554808c210904070400c02c1c1c41c001000b2130400c04007c5140d207156140c10740700d90305502c860080e1009603a001c10302644e244c4071440307a000c1074035103640000c00049950002040e100341d039422403840030303105421045005494498512013605140040c54002d110400d1500200c0d226001284448102400f40c038501010002148182e84c411b40040e80440d4407401c5030410407140080d1080181c04c085d204001d4182010005900c0c8080581040c5c403071451b184000414200c0c404829000642c01402c0303e54694007400080060110441040c01080f0024401080b1a0041c02184c3c07400781d000501114060409800150660000c0c0810f8200146480340140035294101520b0400c4c0250300185214200b180070004a4041a00800303599074040c000428140c5503000201e42c2403800711011074a45c20015030072000c3d5002144090480e40c2000d040c801034174010b5010f038096660650310b50015a000281480e95031401e04201d007620600d15403280200b410901c098 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371935089 1250 371933839 371933843
    0x301081b2d010f08090715020c030304030f0501060b0a0c080a090b0703080f1302010207050d17030a230606030718050a031109070903030203030a020306060403060603080306010809010209030c010507 87
    0x1c0500007620103084040804650054907004405030304495103581c0060390011158400e00e0305040c07610f010f92149448480d04c0c4075030001c4094501c1d50050990090040c42c0b900c00000c1c00b01c0e92070720794904002410158049040d1115481c040000c640a4a1201140c41a85e80e079125044030744919036540c00c0c19805501c040d420031000301c0001c2041c4062100030b01e1704500030741d50080142012281c1c00000003014250354510f045181e400700050b40c021444030211403007102c01c0c111405050401628450a15004a00c40807000007003100303010311644003401051140b001008003109ca80e0031100c160000362105ca9000d4030910004c0e1000e07100d400b401907500d03e1400c08640c1603903600c0c00b1a4290500360012121002201e10f081c0840c10541c000356809902c81c64240581842c50714065224407002d8911440303103800200003182034590314101c400650b40030704104a010354a08041e40d880c0c000382c1d40c117400180c010000c03031800c4d8414003d032101100001c000e0480c80068000540c1c140d84041d5003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371936339 1250 371935089 371935099
    0x8221a060f0604030602070501150f05061b0d09030312090b041b030203011e0e0a02060f0d1e050115030b09070c0f0605040501270c05062a0706090b0301081b 69
    0xc401c4007a100c0c1030250000714410480580c071001c07103241c21425911004c05100f0301c0b1844030001c2181000c1a0110703400c880c01550301d280d51300064148515a00b003030310140007591040003c1d20807900c5e440031420701283e00036a9040004016001c02e10140c5084440241602c960311001c1408204555503609028104106500e0160769903404282500e40307914030505c45805104241c0e040c540d9034011070001c00c241802404280e90550300013074140c0188000070804803400f18000500380f200d640145118600313103803902c0d400c9103801d19400c041c00c3c0c2401410740c140f03d020034080809000380981c02400030010300d810502e80d21b540088445200883e0240e4100300219000b02c00301e4035510486000780d00810011440380c0e08040a1003040c8030341d001c5540041d14178901d003004904441ca4440940ea0704444c03065646400302d495041d8002e104050360303880d203546a21840050340009030071049440740d4441d00303140d030395034418000300e0f000900c5017601d0741c1c000600b5060045140c0c800e810b900300300180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371937589 1250 371936339 371936359
    0x1050903011d1005160c05070e090106060905060901020a06110d0e0a02010e01020d0c02042a0201061401050c06041209080303070908010f0603050d0f03110a08221a06 73
    0xd0039211400612807084298400c080d58940c418403d003424401074035014400d80c100316401c0035076910b680c84079104024a01000303008002082c0265401045030500608050420111542c0204854811213000c034031003003000200c5060402c00c1d2a54400b058000c2e101c1010a902c2d00b00162609500c52515240b00300403d0000c10140d101d4003901d094074400400340c510182c40003400e0b6205000c159410340d8802400c004965504c0440302c403141c0d60540d03010440d1810700342d80c001d000009071010061035413620028030900e541544480308503966500840041203115006545030702c40c00f0000034440e0001000100403d0701c140144060058502e0400c4400e940c50398061b0540d0410b07a206070006510003810000c01d00c0900602c04001450038080006907d15528503940c3c1a000f0342d143c00b8024502034412500340a03038404400e285080d0002c039070301c10060074010120750045607090268085030500200c003400000419600d140c2c081ca802e030110324101c040c0c420400004000d141d0181e4001c1d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371938839 1250 371937589 371937607
    0x10030c09080706030207060b030304051e06040506030405061e07020d03020f0f1c0c08370515121c08130f080403140a020108011809020a080609070b0a1202090105 71
    0x10600410740f81c2e80058540500c4d140110a58084a01c482c0c403e6105001c00d02290307903203c500189416403800c0140b00342d440040419507900881c7c0c441036100c1d40200c00c200c11f200c00492f03028425030010b019038404d520840706c861006c0388103640792001a884484942d8800b4081e0b40205407800282c042541012107058480b42c40340e1000c04610505919409107044407000f900400d101e41c5000e00f8410f520b0310304420720000440c103030003010410144090300c003a1034020319010b0241500035001e0500c068504466200034460310038440c1c80c0942c61001078650b2004000c2082880348560304030000121000c0c0a0031102e11001808007215805004c00b4100020205015541c04502c0b61160729115451400e2444041c64000c0c4d40e09195002110403000503a032202440741518115124201c2401d94070f000f82000f0802c80074001e4128007031010104180000142451050009004a40081c2d4440d10201c83d54000e50581c01c0200302242c03200f4480c10001e03000380008810600d0f00c141000134503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371940089 1250 371938839 371938843
    0x8090d08011a0d151d0903160204090201030914010507110a0203070e25021f0c020a0308180303090a060506060406020c0105070204020c1501140301110d0e0a0f0305030901050609040210030c0908 85
    0x380d0b004805e032403004d84600e686240d8050341181c1c4116810080d40c140404103000c003c88603a80340b0300910840c1d07611820403c5a0080e400a0300c03a6800c464291050703400305480078000c22040c1c601c40041140a0f409004080001401149030b9a0180103003810f01c0c40e140c0292000c04024005a0711082442039403a16440c0c3d69003682003044003540104801c40b0040d0007400419012000806201d05201401da030f001e8001504c8254150300d460202c40a42c1c42f08031015030344070000d00d1440507000020510110b044005400c00703000d406802d04215548440040080521540c4114000f40e00004918001c40d800744001d001ca043c005400580340c1b280c081101410201c0790b0149401d0105580018400000b102e009620181d00030b500821601c10100d401911a0003040d4a1079541600c503580c455500000b40000414903520045c1400104010314028000d40c0007121044c0642d841d01c0c001032802d10b01410303014050b035005400c40c03104038800c60f0101c014002d0a413114080c00350a440016a43c042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371941339 1250 371940089 371940131
    0x705010912030c0906090303171504060b0d050f010315050c070f0b0709172e020307020a1e0f020609030127170a021e0a0b0708090d08011a0d 62
    0x1140c0d00081c00b03028407003010303110340c1ea643c11000030043d000001f44000394200c0d04400502d5410740c900c24060b40c52510344184008030000d80398000b402c000001594010000c00381102d044140c60a02485c0c1d91600c014640c210709203c06459100f040c04440354208503648042c0d04481500880752402203e900c4183d0405011041110800130b84c90802425540c4415101c0c060b02c001500d0140c00e4500ea9441995041c80262420140705000d000e0b0090f41481c07804c85200300e60200781503440b0300d81860041d4581da00304030140c03081c6481c5c40d890308621440b54040d07104140c1c0801e03039819401c484e40901c52036401c40c0142c207402d507584004007a10811503031200d289005c502d9464507110503c0d8545101210001850b84d0a080018442089115004252824007000b00c41d41f00c0d08a58a00d00c1d0246040802040686020030035805e112409922003080343c49405100c0845c0c080001c1c0f11800c40380c6040902c02d009050050700421021404070300c0040c00461010500480e00010301001d0300e0082403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371942446 1107 371941339 371941373
    0x911090f1f031e0507030209030609010b0d06020d0b0316061106090c0105161e02040608030a0f050d0e060f15100f23031807140f0607050109 62
    0x900748a094803001e03440c00600017410a800041c000350f2003602c8080c024000c201c001083c01c001406140c403000009008005458003503100c620080d00520703a51022952034105688081c0c6d42045030312110340000c09440d80140c9064400341140921100020954201404105001c03c0101e00032000550a0070207540e100d07010228100c1d00800c00100500c94600341508012403601c1c07030000007119201341c40401c0b95684407060b181d40c03401102007100024428014040002c0d00c00d1000c1c08501251a001203144007940149034100b56003110548180d500e064100840b24001e94002c800303031501650305d03180001d4400d1000784668414400745045c001e5801d402d030030740c0203001d00b58141c210b074856a0135200d013081c9000c0307103001050300203441c101d12540d4400300b035410f01440c1c4d07080070705001845030744100303002d400740901070f000320005544656030340c0b10110110344e01c000c100c09941 = true := by decide +kernel

theorem cover : BRFrame.Cov 371762589 371942446 := by
  have h0 := BRFrame.cov_init 371762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371762589 ≤ n) (h2 : n < 371942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
