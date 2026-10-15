-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4941
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:33.18415+00:00
-- url     : https://prove2.me/submissions/61f18af6-705a-4c38-8a13-2374799ed893

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 888489208 ≤ n < 888669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 888490458 1250 888489208 888489253
    0x30414040e12130905010f0527010f170a020f040f020f0f0c0f070305030d05071b0506071202040b07120c0c0608040b360c0301020a0221040b0d09030207031202 70
    0x4d040400041d81031400810b501940f50042901c2010108540f100e036541c0d80c00d11200003150148420b015580da25042d81c02c03241580100b528403008a0381d10f184400001074a100059001418034070b000d59114107010080c41c00304540d01340907400f0800c200790305001e24014610030b400c10940c2c65943e5415140e00b0b04000b00d104509080c0d0b0085402000861800010780d041c0f00e429007400600c50f150102c041e00e44c2c0c1011208a0f00c0c49100c00d2652003481320110340e8600c01e03c42034035046070040503165864102d1003240100c001540050050300042086035192500c00300785410001803030320007a12100e000d038003203134059400120703c0c3c4100420030003182c42943d00149103401da03010003083d10100550310001626128024071272103503040454581089082401701000c1c0003107503640c80c00c4400035150f0000c103645100107030b01407003580a0441080101e404803143d0f00307521401d060324420f02c82c018000c500010b4045109501000c00868050107100300f0b03c111640040c4412007440c0030705d200b6242c2c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 888491708 1250 888490458 888490469
    0x15081b040f03260c0a1b05090f04120305070504091a0d0804240503060f1906051b0a030e09040602041802071b0f060c0c23031509030414040e1213 64
    0xa040c020703110750a1002034100c20300340e07015000740c010103400d44c03205030007004903400380350f109041c0801c0c402440d15080025002b903009081ca119540174952064042c1c0300181c0364a80000e41c20002001044035940c00401002d0f840103000e0004a10b002c00a81e00c00306038081500c0803500041e040200d006250304120001c210350131100c2d00c0240000015040b40001054a8010b410b42e640c41d03040365640b003c90712415080742150325199078507000b00605d540c01142d07030700840900059280c011510001130040007a0b506a4851140803650000d010742c40d0ba0141044403019000e000c04280d00801812803912038074000d20040e103030500742c2040c0709448060901c012442d070342054180840010711040b08141d031442c1c14000d0708002d6070315188002d00c489902c8045e0360081d0710300c1e40d803a00d6064215280244011404c071280c0540c4e10ba045111900281c61140d11684100001c01640003c44400680c10320001d20001d190310411441c80d0030b02c0c80140c00c1e003003050400901500030341203003e0308202820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 888492958 1250 888491708 888491783
    0xb030f011e0c120c020c0a210303151d0f010e04020d0204051302041d0607050c0d0e0a050409030f091401140f09031204030c15081b040f03 61
    0x30801038890544100742140040e41500d81121160403402900c1c02c00407074441082c00c014900d4544030080d118200c00d201c41340701c0c0c0c20407500040d103510340c2c0740509194865581c1840c3d80250030368051f001020361008002c1450280000040c402080c03600344460480900e0000c15545024810506c903150141c01050020355804d0034072015884004040c0b281c1541514002102d880d58440240000c5034100000c0d4058242503400090280040e007030103100c91014204d440c04c1e20b0700d00381aa0180122403262006a101c442940c070080d11400002c10020400380004068546481c042400d444d000d41d1b064002c0f49000d070b035007000c80b0b074404154401440d45903e40c05c0110300010000344100220000c51800c4000031860400c000780d424121030920800a080b90400d884044200f92142c01c02c1c802514103803010600001d40203130180036541d000d0700b156900c140b0ba40c1e03410f0802c0a122041c1c0c8020703400302c90500003c0381116040490001960042c411001c020030b10ba070442180c4000f410b800c91824 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 888494208 1250 888492958 888492971
    0x10606050f12040507090204180506090f1303170f0610030e070620373305090109021c020105090607050c060f071b150c0501060510030b030f01 63
    0x201c040400c1d01d11222120003280200d4503603091003032a0500c1504000c0031144000b5000840480d00007201c46405a404814000c6030341e0036040141c000310803125100401c01810005403004001e4080101c00e45c030038206035150120000e220301655904941081c2e078032a0b02010b0281610344036401441c0807486103400e100f071001c1c20380001d8440c0c0240c070411092016200b0100080340554007610005030310344080790b8012080000c2c41d0b034038179018401c2501c1d680c000d00344554081d440d14110541c41c0e412224000303600000c0b6417000c1003403007490205101e880c01b40050500d1700070980604d9009088200002c034180080e4010040202c1d00001054a1006641031410050740c00100f41e820070f20040750542e45440b107600301182040c049d4803445a1108001840000900ba00f002070480b09008800602519410003107590040d603040c000c41c0c00e0055041850301e40c0e54801c0042000d03186c030440000c501d06035203002260400103070203003500c0465141c6c1c2503204503081c104500480011300d0390090111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 888495458 1250 888494208 888494227
    0x301140c040605090a080f0604150603050c09060609042a17011a070f0b0f0c1e13170d0f140d0903030b0d150b10050904050a060503060c0a0201060605 66
    0x4030300c29032142c0c1d01489404210390116580d81e110300c0000303003607480650f00e5640d8681001038071441c0444045404000c40c0440750b0a03984035101d0071050b0381e485002005032003203080800c500060014100c55000504000c854074a0b05c9900605850140350038014034841d081026a207809200b20402d40200840d00d203007800d20b4000003420354115007401d18a80710b203e028801000740340c07003074481c040c1c214010b0041c00000c0080000e00f070b0707104208030b42c0761074540c4d02c0d600da10100c548160800c010b03034001400c0110f5202107020703004100a001c034a070350182c4203130f980321040681c1890030000061a0010550b1070840c50300032842001042d400c0c81c20030140c4e903006c120b2103180c2c016600c104440c00c0d0f55812240c20180250320031007031043c3c014000f11501e4240d01d0b2000c004440c00170315160150034030711007205504221940103514021510345900f0500c0300c4050000415008001501d029120711000645440c207011346170103000030b0703455195910030600001e801d450040d441003003042002c01601c2c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 888496708 1250 888495458 888495481
    0x15061804111f02030301050405010918060c21061403030306030d0809010207150c020c090c0403140307020d031205060a12060f1b0e01080903130b03071202031005030114 74
    0x600640c8504011410084440810b1105011681146078801a408641c88043d0000091030481c2ca085505101581e03d0316604410b5501a4001c4e9102802c800500d900240a41d0464841c8a034686000c903061015032040218202c00303540c0e1410410303603c1c4402d06c0162a04503c245a10034103034000d40c80c41c20017a000c250759a10074110002080040804124052000c2d011641c0890700241e8a0100c40503004180c402041d251140c0d10152054503084a11418100101ca01c00c804003015682468038540719840f000c0c01500b20f80500b1b0004119a000590b14807a450308168080d030354140031154500030110885001403c80d82c8a090001c204004480f0013551700d4000640c864000300d9105003440e0303500007804482403034071852001d028810200f6a880244c2e840c140e00d090341d51484030f40700c20b1300094503803052102a40a04000744010701445400b00c001b103801a1031858444008100c20744000700b2a0402e495001c2c2d420a1030104206a2409014482d03114030402c0c0d000c0b400d403c0c4505040d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 888497958 1250 888496708 888496711
    0x40905100b0304030807020a02090403030c080f04080412031202040b03040b010b090a090b0103020c0a0b1b040509070f11120316020f060402040c03150b0a090e010803040302010516080c150618 84
    0x302080417000010392020702c04e00c0022441a03001d004140142014940130300a0040c2e1002c060008914500145804403542c0b4200e00550704240c0041c6010705080d011419405402815020711901c0c0d0720b90800c1403201c1c4000c00007820100595610381c18a8906012040340c107038400d800188050024950f00d540304441e510407942c49100003e040201e090059020b070040b202c04415034001d483d807880601c000c60b0012440344000051a040c0c031100010303809481d000b01d0180607082010f100014400d140144414440400303142460420360150040d031030b243c00c90807070398000c070380001100b4048119034180806003031043d20300240041c0f14903a1440c80d640d21000340060701c22a141c0d0104403801e40a40d2180c214942c481c07131842c10094581199692a81c0a921104005208450000b4000a030100d85074144c494802c05145030030b1031034004644542101018030b60518401d44c90100003801a00104260844c00c0044c003d0910340a0710310302c030700d040186214012854421141180c09850048a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 888499208 1250 888497958 888497963
    0x160c020126310515061816081303200111040602010b0102100207080919050d1103150402030d081b03150901050406060c14071a030405061023010e0a0b040905100b0304 73
    0x304d220340e0b2048002241701c5a048000c00600490030103100000380c00614154400031103407980c80940d160080d485440002c8900050000f07040703120040451542c54282c142030411110001c1140f070400c00071440e00e50300c11760048016031754902015003556018010340203000482c1200318201546030726120303902d00c41c4402d1700d48a2071350701d00d10200c03660f01e024411000c2c0401810348500c80005290418448203480c1c8258404d1003428142440c011110502609c502d9002c0c0191070010740e031b80300584054402500704075030900c40c610b460b001818100065403090081882c810315440c2c0300300030300502d80c106800560165040600a02003e0703005204180c0713080e031008a42000f100b000c03a00c0741c01c1a01c1038000302960403428078545e407001c000d2000f0b18043d50151050350105e44030802d00b00a0001c1c2c500c00d0b1a240030702040c02d40201401e182c03020036614018107108070719038407507000200e144501c0d030425070850700080f0b41404076030140c4c030505034095442030f01d40c1c041c0740c1031000c040c01501004000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 888500458 1250 888499208 888499243
    0x150807090f210c060203040e0903070c1a0412080702100e0915030f010c092408070507050f1516030203041106071b12020108160c0201263105 62
    0x4001c102c056500042e010300741c001a525082135103818000f0341b0381d401480b40c50001004100407a81c00403001c001c550480f030340320001c1c4d540d031031070600012002001150301c2c809204c010b000008142501e819903081c1280308200e4a0f5071000c840c41004004406012040100509940820305a80310701d480c150700500d090100d411464070740d00000e0303c2e00d140e103171005140d9401c3c01011074001d030b040101007003580c80781c0001200c02c194864000440c07048114800c000902c05030003090925015000404480d402481a103280308810580c040c94944901c0720160304000c880100441030303440c144c05085060b103a180030f601d141807139150a940030342202039041c0f0524000540f90700304102c0e41d921581d0041003800e07a142e4541d5510b2102c840241c410310a03404100b0034400203c62214600c01e00c2120300700380e00c800070314801c3c076001143c000034041030881c1c80002d005800010820b000380c2c42840f4030030820110404503050942c120002ca41c208a40c8115011005244002640480e0442190126810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 888501708 1250 888500458 888500489
    0x90f040f080d0f0e071a0f0711150a020606011101060605220806090f0111040e13030504050409060605040e0609060f0907031709011d060a12090b01150807090f 70
    0x641e03000306101461103548a19011042c44450400306445c01102c61030140096581c00c0300d50300b00400d1040c102e1405010008007c08070000c0c0344041c096407503040c081c148c0080d448501100c414642d001c1d448000c0941e00820400105682c00071841d801000e88000a114540c81c1c12806021809109000580d1002500c01040c0c44072040200d0b500070034580d001c0b501a8240521219201d40c58034a03044055401d18800b0704000d6805011036040310000400c646a07940c650100101e1440103502c01c80c100601040006070380d986900034210058001c1c04005142031920041100f00d596402000b0510b800003410010904000304803d50b004107035410142895503114055424801180c0000709050726100c03c100c00c24200303d02501c802d010170b80b244442c0d25240306103200d02174681d0b0a41030703000c8010480840302c203224010580d1100124400032030240013503504d07056540030903040f94030b4803400e11812510107503210021542003042030600c80041400c11640014060a03801a041da4110145 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 888502958 1250 888501708 888501727
    0xf02130e041a0103030804200f01031a03031803010b100507020904050c1003060603200d0e0a29070e0a0501080408120c03160311070308060a030b010b09090f040f08 72
    0x107610b60181800e148828a6582c49143c00780910700c0a68098406002c02c0207060b10f8690b001c181800c0300d60713000b04005100340f003800044024008442500600c0c2c50000c48500080d201007000c0c20030750b25440b0120360021524010315084a86802c42240308004c200106011203030410304403442c1c0350f01510040f190b5559402d01d20b107030500c55a160f9800c220741340402d090159056012100742c4502d540c00f03220307000e400b1800d5814200b507054480482c0c03100b003058900082e1580e024440c0c4811020035118070f5011a180c0e142011000c1c071150000c1e855150340000d0f8585076904444d0b2244003800c01c0304d408407108006c40d00840050044506004d00f05012805004901050303c070307184400550090700e031410004c4050380360426070301403008103450200c600b02c43d4080d0151014249404009500301026a181152201c9010307103107613040580b040c03010012940079440140a00311201c50140c2d81d452000c14401d140d20000c01d800020100c40d01404005010b00c200400260340004e4040e03103c00000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 888504208 1250 888502958 888502973
    0x9141902030c160f0c080c150c0f120d0e03040627150906141606050a09021f090b090607030e060f0d0b121c12090204110d0f02130e04 59
    0x160710141c003d2003212907200401a0303242c2c0320000b0610600c580c0d6005030703460601940c1c406400e1110b80d0f010f80c2142d600c441306020200034000b0b0740c031039604443c039122800e10342509042c402521a40e0b481400950001f004100c1c4c00340c541c80c110600021890540f0b010b10050061541303000045054840d801600e2409400d80400c00107040d00c3c0c0d54502c007200e1001c0b0050301201040c070820f008109803842c0324107101141800d55807005103030385180503084c0c81076690308014038004220105a0390b403400e101003d41c460b0120b244003c4088956896150400180501411076503070002c01c5504040068001607264001900e08140c1d060270400c0c3d11401d100b0001d001d900a11305020145a0085032414910b80c1e140c01480f50401e0030b50b4642d031040c441811654a401310342c0b1215060012000600d40850b10841503075032809011000003500c0d803515800102030700d0740342080c20070b00080440d41c00c5d03071800c1600c2404060404e803c1d04600e040d424103d440e06030040e03403007081c448545100020341448440c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 888505458 1250 888504208 888504217
    0x6020a02070b04060c230a0312230906010f050109050d15022208030307020618070909030f020c0109030302060105130207050307120f0302030103020a0e2e09141902030c 74
    0x4441d03015116515458000c040300041c090982d1b60071b070004109460011903c884200800540c0c028201407400340d1070540c2c060314416041c00011382e132810601ea841c40000b503072040300c42100350070540d681480e003441032500c0e206800c0601d001d440c03980104903582c0c01072642011954192000514180c0c141024000d000640c140703059a2800054a0707441d0350780f140740316483d2011a164048083c1d0701c2d400750315501c1c081111400c0241e407000002c6008810500244148203603103100f00d803111500e80140c3d005440100000301c01080c01da96491000700d0b01405200341400702071034a0b030000384c07035914004e507034110610509001d06a01d0480c1240e00c0703240e8045039860350300708084a41c0ca0304149007000c040b09028500324000b070090500050100c2c8a0f00842c0d040307a4004160964081c1480420394640c40081c0c00444903d6030508070984004d0b00381070400030314018800c400300583c540849681582e2418a4046440640b41c00300a00c24408645111008100800c016100c0d030302e0507a0541d06109 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 888506708 1250 888505458 888505469
    0x14180915010b0a110106180b120a0803040b090c010206070503180a0c21080910030f0c110601150221090a0f060e04020304110f13060b0909070e0a0306020a0207 70
    0x8454008902042c0c0e060007000b61a1040c1e0310301d80c2d03c00f0005126800c90f5014020544014404c10082100c43d855030020507070486e006001403914141c040c1494584034119600b11905a4040b08210034400d40200d0a94002d0541d409000c92090180c0000d4803118000e10700d0b410f1050200100d9000100340301250040c4000c2c02c00c8489040d40b0f0308088030711454030321800c10824048406104070110f070400916949500200b95820040e5500801c00300061640c650400c140c0c0d130300b1681e0381c00c000320300038032109036910f072502840304612030740d0780d410000141c01c0010101e95110b904c1c0c4520303500048a040b07640c90b0312461481d41c50a40c0242042d441800300d41075029000001c0071070302d0507629010b0380c100c41058681b0413416440d08180402ea001c112005840311500300958a010300b0610307402511001c00500250b60488012503c1084030364036000412068008100d18540e400c3c000815074001d141402e241408480c2c1c0d40014a81c940d00d804000d080e5500030440b04900350013040f005d4003508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 888507958 1250 888506708 888506743
    0x20613111203030108160612020706230a060801051005010309021503071e020a03080a0b0409052a0402040f0501140d0515010e01140a0c0c0503060f0709141809 70
    0x315441c1d86940d0b50400c0c0030f0780c8814052543c0c400c0c01e100014142100f00d820341c0d00c5a41d403001030079216800942003100240c4210362604d241d00210040071445112500600024140c03604081900c4003c44083d81c00110490303141c0b01c01d2150300c0c040000c441c804c485003480c01142c45941072003c01e031082d01c403640a80e81144080248420760b40c03c011181c003040d0078512000700c0d480301c4003c101d98406118502501050b0000c0100e01060496005642c2c6e0382c0b40030300b0209002840c0d940300e42c64040000300c10b500343c2480260703480c40950b9544003144500e4085900354281404c0440798003c0d00085d2103041c0c1844114016110401c440c101600d10b50f004051040005140445210341112201c1074500d0000c2d04c0c00c00160819070180c5010403040a0310300a16041c0f0b92280d10a55240411601c01d4840100d4400005025542004010f1040c80700f114065603070f0412000242641003030380c01a02c00c4c9541401c2c034540940722152131007407000103842d412909498078441c003420300c0c1e030347c3e00c0900b202c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 888509208 1250 888507958 888507979
    0x911010807051b03090d0b010305120a0804060209030109051b0123090d0f080c0c090109140601030f0609020c10050108150c090d02120d09090204050901090b01180e15040c02061311 79
    0x11121f4031041c0e049900070400d0315205042807101c00750a20400720100b01140c0c0352000300300418515030203410700c4403002d400007400c070303049031a442c0c0f03041c240c881c0708810b0340000d004880c0b465a100200c0007445050080325210820b1082410000c0c2c01454041d80c0200d0140c41641c00340814045600346594100410580e501421580c040e21041210b9141d030094040d0b4000041d0310b4018410013644000c0000443c03120307291500114040c05181204c1500707103407591408610344502e0310050035007108010040041070011244402540c138145d00010032500810004039074800c1200400e5403046084003510360307d0f10100001981c00805520103034015103810b071816851140007824550f03000403500d400c1109683c6d20610800c0e48101d016091b0054070f402c0042150107070325001407503514414104903c40001c02203054400081661005002d81c3c125802c1c810818103204103800321003030958091004501c1408007a503107076406084195a00c6500c2101401e001024143d40400c400050050160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 888510458 1250 888509208 888509213
    0x31204022803060506100807081518090c010302250c09050a020702030f0f0a03140f1306140f0703050309073605130b07110601090911010807051b03090d 67
    0x1d400207408115801ca16110106410746000b6940240010581d40c9111315652014000c403106040540718a01c51916900d00c0041607490418070690011034a001c18000d20301015081d14202c03843e0f10850605204200644411041801082c0c2c1c42e4684c41400140000502e0801c10b0ba41e200d52080403000d19101c21300c03600d08503540040030984d0085040b5040c0708a0b01c500e85850310680000c00d54242d1003012010b000030300a072400d400c101c61a48180b030a142c51480003601a62000c24407183c1401928024428150084483c00c0740d4068401c20b28140501c80442c0a01442441005028000c0c040000b400141d4104480e60180102c1006100900001361801040c41215418507051205c00c0400c014000c1d500d100b01ca00c5403100c0036800325800b109454281101e00f02408074010440c04c28800c4169a50411015000300816034000491030305038103180505000c082020790401110b00140b219181d40501a130b0b045018080015124491b1607484c0352451165181031900200c41c0c6900006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 888511708 1250 888510458 888510529
    0x9040c030905010c1409041a09130210080106120e0a0f0605010603290d150c120501270b0a26240a021b030c0a030905011103120402 58
    0x1401e900c0340c4000d11a03246001c0d800d070344000009840200d0668188070b210725038030741a000340040742103c2d408d05a404000c23001048904d00201c551101294114903403c0441c142400b4441101d040392500c81000e5043c100f000b0010701c10311542d102d08580f44da1001c10340303280911103840320b00d03842240c140c2d900700c1e54074225020b41000d200f03000100e0700c0d1021828040c602a8079500d08101c00d13017880c9080103103100802c121a128450180c0310740701c4c10f40741803250100c18071920092004a456001c40260b0046030401501e2050300102c0c0041c520704c0e000102841c050400301e40c10100c031000404d04a42c41c40c003041d600c131000d40c03180021280c0551403244409008880342613031f00c80542550410800048103042951305a82e04218a14400d8005a10300c0503513805001c52405c00341d880d5105801c031005051071030b0460302c0600d074690400030545080507006544203009000a0903c2d12821220081094507030140c4502501c0b540600c1000404541d1401800c00c800c800360259401c2180084881d40d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 888512958 1250 888511708 888511721
    0x7030506040e0d020312130b0c03041e11010f02120a0503011e0602031617040905190b0d02060304210918020310140117070c110f2409040c03 62
    0x18011854203521800b161030124001e0183c540c00c1e002140b1b4031048107428030144a006107506210110144050000740300d01c06454007a0794203640894403400c01c0c6c244250080d0115001e80075180c400300e01c600001d1486601070340946002d082080402d4180441a07081c0300b03802c001c01603c02c000255016501e50000c020354140d501039410006802a21112001003038101d0007050f0141c0c0c400c2c0048003280c0d41005d8400303003203407055805100107100d0f040461040d4105400c51138483c0d4452003044080850040d2405203194160340074441c0041c124041542000d02e03074000b0f0f004a9000001170140900b210003505a9030300740702c074240d8040c4c813010002c014610b64000e02c1e00200011910341c09050490003601d000700007000e103800100c2d290041681d045100c0840c40c42c1031260407035180741000741c042c410602c9122a40c035205030030102846c010040301290034500b48074100520a4110644501001c404a0070a016201c04103d4841e00001c409025205880b64410304140c00c1c2100554140c01c4034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 888514208 1250 888512958 888512971
    0x20c130e06010b04210c241b02060a0f031811010809010507090b07021c150b010801030f080a1e0906030515010f0e1512011d0c160309050306070305 65
    0x16045643ca80015010303900c00e0744118000c50300089040c0d8001c070200740e00050b495200c0c41c0e40740d00c02e5907181090980000141010407060515600b000002900007915041c2c80c41408440b00700d103201039000070303030a001d8190034070200050070504500309800795004400e40516081c25044800040c80c02007070300e450000240d8001488100800c100e80d070f050044602030616a11035220850800410f0900d540010301e0030390303200e042a1020044140080814001035000e803890b0310400d1007901d090025200f40040503410442e080b401017021514140813a00380c2a884081169549a40d11003114004104050408501041403101e4040d41d045400c640c1100c006072001d00c8203644807120380641c1004040d441f80403408860103465084d10034048048401002800c0000f150341d85042d0300026000014821004582d0400510843c4c00c00e40a034085580a084142840d00c4d06008105070b81c044c95440c04000c0845040d64801c0501a0400300040d1038058100c980b60724150320002c0144c903064459 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 888515458 1250 888514208 888514213
    0x408010c140703140703030207141b0102030f0d15031a0a0515010c021908031602090109200c070e090d110c010215090a080f04060905040915020a020c130e 68
    0x201081c220040c0140c0e01155011340b1001030780445820115215407002c1422020543d0802c810000100c0000d0541300c203000450040c120113101821030b0407084002000941917510520894048a100340308031410459848000301d8281c20705203402c2ca805c030058000802e440c000d0210b942c4891541c4009510442d082d1105004586580545402451449045500080d101503800c0c0141c1804080320421641090745080d9a9958210240c20f5800100c100402410907140300020743c03405500c454050107150314100704000c0f00024240c12005482500603c0240204100b001d0b46001d00413040105680f01190300d151800c007000540b10031008006401003216100200b6400200051480400d20f041c1c0040404074040c04c40704042402c014840ba140d44684448040001c2190b4081c1c2052a0305901007a1200d051400c00b604a61481e00b090380200d240040040115118594524543c0c00c0b001c8016915141e142c0102d04141e00b072481c8581004000230000c481004030b40c000394105a81406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 888516708 1250 888515458 888515477
    0xc10060509160e12011b140301050604291b0d0c020306072a0317090a08043b061e06041a040e0109060603050705120403050d0609020408010c 62
    0x104644000c080d6488030b2824030300c000000702c4a0260031900100c6400038003000d02105008103807400d66100d104800340000c81501c8004416402c850588591110712001c01e00303540c10000424601d0280f407007101d81c10000c90207400e40e2101755450a0000400e100b04450f95071078034240c3c0e543d642010351010940c0b07100d0084842601407003500840e10841d401400f0708590303216035604685181c2d102003d9404000002070044c000082420007500d6907100e5203800303020007800100c00302c480030020310204840e0800d040030400134424908840c1501c2e402c01003900001302c01c010284001c0158008511400c4100b4808803800c40070000c0d60303219540c1111144000109580111b0740c0d80c196912294100909000030b0020a40d409150058100416091401d10780d031802c82184200083c1d009180c1ea5548070818007145915018084d8404400e040640c9090549039500e0700310003004001404014001c24604d80000441d08010003c3c0426882551140d4441080c240200040508000071503540315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 888517958 1250 888516708 888516719
    0xc050702130504050c22050117060618010e1b07050a020909011505120c030607030603020f121b0f120334030c021507030206090705090114060d0e030c1006 68
    0x541d510031907106001d07001c1702400805002c0310b14800c10900100340104040c00d0a5196144200303802070406581c1c50748020704c548070150405401034640343c021410038a0b055807440fa180c01c9141183d04003040c1c01c0241d50b8911110441043d50015240c400e00c1c0003422000307105002030004c600900031690040c064440920f0a800c850210500f070720030380c00d5548100302c0c0f440c22001d0f85114008a40589840c4203d40300020f04040c41203540b400440e44c1c1d03034018010750629800c000034207901a10b40703500d180d4a5000090755254144254200c8140e00225072180741c44900e041010710501402ea02158484519400c0c0c0f250400302c60202050029882c0e002c91540340c0c1042001080c40780c001d840b0b800c0050310100c50740c8440031000d98002d96851480c800c540c040500618034075000b940600b03100d0900c40d580f54200030065010383e21a079a00d90041c071403502074807041100e48c10700b10f07803243d40c0e10100e1007032001500c2044040380b614000800e02040701680407a8081d006501040c0070400030343c540707 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 888519208 1250 888517958 888517961
    0x1807090807050f060c0c09010e09070602010c0c0b070e10110c030106031a0a02040302060301031208060d050d030b12010501031110030c0e1314091e0c030a12120c05070213 75
    0x520074160302c03004203e5200300074208007000341485500350042c3e501108040000c10b10961007139008240b1490001c0402802010900c5800c3c003420f5240300a1004920b80d01008019149a00000e401c1d12804000305e698079004000c5018400c4000d0300404a01c40c188601408104414000403458004d5810360307002440c061044c40282ca0380001ea01038900040740043d41a100002d02e4001003550801012025a540c400954001d500c1159201c0c10017101e0000201400009005079010304004041a0001000803596500310a81c0d40b03030005150700340ca00019515098040b410309594600340c004000d201d80c090020644030015a11400c29050211084040714807070b0034000009606074041e00c555150256440b450803031410004543d10311840e42901940700180d4000545910003010011000040010207541c0040600a80102084d00000c2604e95008140041480403070099070b0f048a03004840041400010f1700007004802d884440150990784040000e901c6030310740511401c0407030a0f6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 888520458 1250 888519208 888519223
    0x9010207050d08030f071101090c090b090403080f0c040302090406050f060a030f30030506130b06030115260114150d051015020709051003080708071118070908 70
    0x90199180d580d170480c69100003100a0050001c105030200b41201c580c3c82400380010060042210580d001d20340a5840202c4030081c1d40309008007155130400000c00d030002c0010fa030000860100c04241c0e600c01c02c40b06014841d80c1c000035408065041800b05018483e0b001d00e220302d1a51140840b44c0c3c9a03c3d0420882e9020b921004028400000101c400101d51050b40350150101c1c0019500e04001650017240c803004007074a400005e81e4402c1009158582040b030354000f07038074040b4204101e02034403001c46e400d4401401581e441d800110040081d65101c0d81d1890090100c030300440002242e8599064600c5c14280f00b41d0300e20002900c400e840500c3d1001559141568816095140445540e083e2026200007041fa00f0319100140001030303001c816601102e030b0400e41d0350141920030b080040080450b90060b02400c03502c10044014000100c0c064100c6810640100c401519800c40b4904a0340d20340d0603e494503040307034292061400b0751754049a0385014441e142c48480b022074807112010b40c0c4024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 888521708 1250 888520458 888520463
    0xf0f0f0602070b1b1e0f25030b100b0c0f010c0e1804170408010608011107080f1305130605040f051b0c010f0203091606170103060b030a05070b09010207050d 69
    0xc08010780c412181c521030450013511200c50030b84011010901c06000c40c52036452001e24070380c002c480710311072003c000d00103007001c17020754401c810080d41c90b0800240300807480d000c020b05002c000d00100308041c0380c8511040041c00c0510100350b6a0709110015900c2e264178098400143d0f00340014003259078017804d0b0f06805031102800300300b030201c02909907510b0740300003401c240c65818401c1052128050114000c0c0b0241100d40008140b05241155090840e00c072046140035251041c401c920000e602907040b161480171950320a6168000d8556482240703086610581e40700f0340d0000d09002800c141d42248046403000c0780c0c100101000c1d59101400d0b24800c4802900b20050016800700518040f8017421000c0180000010740e040707800401c80c201d030b1081d5160030031580117042101c03e4181d080c2160018080358680398210790314880b07056000040601000b08403035184c4a103485542c6082000c000c8131a040411070740181d94461350b1106607841202c1d041d0041c051188049142d04080024100c00340c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 888522958 1250 888521708 888521729
    0x332010e011a0901050d0c020f250326340c21061514060f09040207140a0c05011218060506010302071703061009050609010c0302070f0f0f060207 64
    0x48010301d590442c2c2d0f2003040583d0610000b408400d00103c0d4520a200c964005a001071400150701c1051034a02a0806070b0608000c101542581101000b4502401100c0d41f120b420707086c8180300100943c92042480300413140040205200f510654044105034072180382c0c070b4007449140c2d0040c1e201d00e400e180b0b1420180c440200404104030049144048030820340c1040b0242c84207070040c2c4e854000799030041e000020f04610400c81840008040b10591012400840c0c0140c074003440110001d200e401400e40d403901c55035010606401b48a0554124022480d400f400d4500e108820710b0a444940458003c00b0700143d01c040040d01c5185003032044000180040d0410051840e02c2d940d59000b41800070220f50404d602407044000081001c626800c415014601d400d85918082c0140030065030741c03030f84131410003407003600c200100e80305c0d00b0486411040c20f01c0c011703000f131150341016843c00c02c85034403a01079104c244000141c900b0020b081c84081d40d1400150480039540c40d0f004a98611090042d1101c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 888524208 1250 888522958 888522989
    0x1e0c14010806030d080c0904090602090306060316030f05070504060323010e070b13050a0807180b090c07060915020c1207030f12090606031a0604090c06030c0332010e01 74
    0x440c024424198072070960b000d047c1c030703061044011506032602d242084a0740c80d00481c04510901d010701c4500c1d84440d00341c2c02001810085810400810454400900000d103000d45410501106101c110082c00c401b07401884039603070301d14003645008100c1c04103c51101d98101c114104007418000c01006c1c06c00c01c1c008010103800e0150150b05984144e40700903200c0315821001845c0e4845486c0034008218107005040614a040d0004141d001e41d0800d4101c201c3c0350907080c1305256185031039a03030440780340c44c911a00c5402618200004215081c4040c0401c00c61249940010349280c005041034070749501507960304150070080300d4450040c1d90b002000300b113440b01c40c030070454424914030a0f040341c0032174045084981600e0348001c88030160000c1d80d07030350707800c000c1c0e190313141a983c0320707150414800e030340400c00e001d019115000c050303032035014800402d5207130030964420034880d0300b161240400407400c609a5010402d20041d007410391101200041041000004040d10340d1502070381247c44059007200324 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 888525458 1250 888524208 888524233
    0x170f070b09030c0a120516081f090f0c14031c05030702070f062c030a0615030b1f0b031308070213090b04060b03030c191e0c1401080603 60
    0x7074101c819699014401d41588850b5a519200b1010060400004140780315460307082460034a05650381c106110b00035080300b080005000540215035614012a2109541070b050900003d492000c8010308454044d2680a0500003040d6003001144c2c080c0c1c15011601c55141d041c90340307604548030018203042e5121501030712180240015584a003051068840c407075100d180000c0002c83c290494070001e0b40d43c085004501843c13010984240550440c5111204d007070600080d903410a001c0003c0c041c68642ca8040d45141088a01c00b001e10381c400c41c1c400507858040350000001c40c0c0ea0402041c6207954220001304810403e003102d0040d82c03a0301000d141c441c2103840e41c3c10980d101810132600094200c000d002030b0f0700b46100b81c41e52144140c0558400342001e092980a0314135501d02240710380c00030096003042c0e01c400600199900c0c038481c088c02c100c10960601c4c118100700101d03060401c04018420004102d4240c6d44e5a080d60b80001800d4402c5001000465151303c0486941c3d405a2151600909 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 888526708 1250 888525458 888525479
    0x7061403060f06090307090f0b120a0201030c03020c0f011407030603030206040807031e0503180303100905040f06060e181203130c091a01020c090f04020910090213170f07 75
    0x2c0c440003030600c0307103880c200001107890300e10b40791b0141e54100c0c0c1d03407001010700801d00d0140c0b402040084411032141c00501d20400e4075402c1607000241810381d070b81c0c001d0380c0060003501650f04500122041d00c007042c0b000100e041c060a08005c1c8150b10140c01000a41b85070b019101d10030507070742c0550050402d680d480c2c3d540921588108000e4081c08076516042201c20b2440318080580c6040c4c2e502e00341c0704e08040d403401c4800450100c124006800030300811489060703120110080381c0c1013000101d1a52950704060b942002661005000070303081140c00f1964041d03944807280540c0d20786d905000c06c601132524040e1284101e00300e091400e10704202164080340c1038046150898001c3c503014809a03030f9800c03104c04a45280f291564010740c40014843e5a41e010322040202800c2951078280c145410703540705142d203100070030092007202d50101194601410200c41d030043c1060301c60442d50745000710007100c0c80100d02e202d21402205600b16240c0340440228400b00500e001c5401080d15034104401c209 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 888527958 1250 888526708 888526729
    0x19080133050f0417151603020a03181a090c09010302130f0c110f0106080706110703050109060207060b1e06180a09140c0403030c02010e0604030b0f0106020706140306 73
    0xc00c41c080c0151102c500100c8018070007410301c00c0f03158400100540354039007840e0781034035400f020060070300401070b10701c0300403142030038408042c5401130751005030b400168001c00ba2500410030f0707240400101800c000c2e641c0010040d41d148024101760b55034807207038215520341803086c4941e0071440c18001000142408516121601c40c40d00010030b24000c909018003c64000304400c0001076085501c1d40c24081c070030b1041d244480c40c40c170700904c41c66051803560340e0341d11001d124800420000710040300c1007942c01d1029101865216009114402d0035041400c0607411a031010784105180c1600c403c0c0760f141020200d5542d404400d80e0700e08140001042001c10341102c0c070b0074509003a041d005100b19680341c12810014201d0b42500003001c100360b048850b40420020240410041d08200510200b03801c03884030040d5580c246407000d5a02d8410700403034214003841c1d100411140094041c00b0300d4044902c4800c2c183c2d4441d82c00c0f10041980c4800494200304030400d4150240401c1010407918100401201c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 888529208 1250 888527958 888528059
    0x312090105180310060306180b011206020c0f100b09060d1103010e030c0a0b010f0506030f071206060f121e05040f080a09060306080c012a050102190801 67
    0x30410b941c40c00020a0410040c00d052103501071343c0f0b000c10300800415108480080a1010016541030204d1b03468544241e818011a040c0c40f144140740d07410010319804036501c01d04141c080d1120b0498243d082513450148914207219141400304010942c1000d00c4501e1045400400d4201c10303a907541c4414001542c4810300304c0c0c065483e0000046030150400003010040f59100040804000c54141074070300300b80603000f902254400100420403981d031041681d030480a800d0b050384154680744816a0702c894403000c1c3c44040c82c1424000190f0540219149110110a0312203000c3e910400c2194030459108004d0a1200e00d6808410351075000341d640169449803144a40c915602c011392501d140940000c00e40ba00080d01c0580c080c0b0200e0740c5401040000c20441000f03154000c46100003a00645403603040900841da8401140344000c070300013003d83d440360410000c40d55074000f40040042c0d10410b50124002c00e80300d00002410428411200d001950301e00303150880c1c2c102e01e0005d0401300c407684104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 888530458 1250 888529208 888529237
    0x20115170115141807020a14030702030706170f27032a0f01050417032d0a060b160f0c21020f0d02010207150c1a0a0b0312090105 57
    0x600c0001c0b4200b80018068102c036160b04609082000401588000c4400e05061403e04c610070300002540014552040079407102c60711582e0f40c545140e1a1440c003603030320041d5042c455114000340b201d80019984015208007000441c0315a903c0041c105941000c0c3d03a40c03201c0d48207138500580500c104190003643c20071007400340e034034120320083c5502c00c011418140003404400c000341840702c010304102a640d1003859a00900ca145419118203202c40606401c404055100100058100786047c03400128a40900120b0f4500c100345102640100e03000c9812a198038a000b401003441d81b4200151910510f100110115103151950b40141d50401550222002c010402c0046288050062540b03040708088015541018150040200905905403898022100c804240340540d0b1b01007454001d0b948880b07011070460414040c102d80c00003144e01c000e0103001c110320b1a40a50490801c1e500c0c05000000030038850500880f042503228031108921012003501000b070039005500810103007041400c003104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 888531708 1250 888530458 888530471
    0xf04031403131103011e0606110a030f0e040609020a020105041e0b0a0e010b150a0e1806090c04090c0305040b010b0a27051e01121b08060310180b0105010201151701 72
    0x48020380c224448102c0c0001940743d2030140030127980304880e0801e0217040c1c1700a04000c1001d880182c100416900c07241c0400c14507503c0b0104a86884d0480070040000500071950b030402c940c8000d000701700076901107920303010028151003440c019502030210b994002d4401e024a03122408800c00902d003503940c000c40355407907241a550076600e842c0ca503400d0b89a03c260a60352180e61070001802000742d840300f03622230758a906440700c00d170103007c1e48142e00150a64140f0110744411592105074020f0798402da02d990b017442ca80700304a03a4180c00850140e80704031440101d40e41c91340500107160041d22046c0d0001001e484188a46480003809500100004450024065200d00200d1001309222108102c803940000034042d15581c41480c440c800171103c0d008000c6204e984202460b241d420140305001c0084050110312284d9042c400d807850090b51138000c021141454550444500700600e040d100d10521100000d11765006024440300000c2000109000c1030074005224180c01c0420304050081d035030b444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 888532958 1250 888531708 888531731
    0x150a2114070e07020709020a1d01030e190b0a140c131d01080d0807021009030e0402070c080f0f19033015050306070302030403170f0403140313110301 66
    0x101031400b40200707035410501d6207450400a440c0101e40d40c080c5118501c104099180d20f5800343d40c27180080300c44903280e02a840341c100101e02070705060309465a9070246400700c0c05000000b06030000001e1180200e5030055542010000480c0c801e41000300c0410320740c4000400201c0c3c844024099041030300350b8201c07856250165460b40418280505044002030070060210420400c00c4842c100020310f010500762501c1c0384025104d1101c00080c0c1c5606880303035081420235000302414810400003400454a0320b20600b448400c400d060f104150440c00344550400a485000c1890480140c90030010f003031a00e001a0b0000c03041c81c08840a4040201d003510b26075940a0301070300486040d0030004800010821030107100c00b00d4040c600e600d849883d070f4100c100420307240400c1c0365070b02c1302c601e00300180c032a965400d0541d510024a1008640c0c08a0b82d0300b000a01d241900605001d00e000740d81e59604038101da44604c0d42480141d4a01e04d000b1401e02854002030f48072006016900c60140002c83c0541140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 888534208 1250 888532958 888532963
    0xe091203010303020d0806030c0a0501211109013504080409020c070918051b150a0306080706050405031b03010e1b030c030a1a04060213030308150a2114 67
    0x2c1e003044005801221841c504d15502540190b000780e4114098281c1074655000183c00e180320384512414018101c022211801007100412010100c5104c107101d0841c9103071507005194040128075001c589203001c9a08007211001e807a200c518a40c00c84040746846120340c0d404015401082203d0307070070041002045180e65400036018280c0380d1402424950b040582003400d580d8032015185840c4410303440603011920010301068200c0480640c82c40703409003500401d01c0710305840801e54014000148500c8007540c1075014030101c52604095800c02500c1e008112a02d00c40c0e48101949644103108040b00702040c40c20017411003030020700004100001880150a0200c80c611900c1c081c1c5007824280d400b410140100314174454110050512000740d41e840c40034007001c00c07000c00b10403c1c8100026040142503412240707801500205250520354900c2e0003032050703004468001c00411400c02d07500c81c2e030070000c00c07403002c0c0d80039120300d188038108006082d00244c0c014401502e8a5034990620000c2a005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 888535458 1250 888534208 888534211
    0xf120f160609061103091b15070f05060c0711091005123304032102120106111506041a04110403031b120f020312070509010314100e091203 61
    0x6030501251010320b505003078080310602440075540321810010403110104c0840c3c01c4103003010142107042c40c4202c51010030021032142c404aa4941070010340c410520003980e40d1078003000e1190f011600240d440c010b0507040343c001e6002c02004512000c08025152a00100c1c6551040f594101032800f155124001410f880600c842c540d815000000390820242c010408141c8040c41c02d007030159101028040c6211b544c1d0002d00c0601044000b000748500c86641007d41c0d024190214015500c4101500100807104028481c100c08503548a8038034481003400301c2c030074610a00a01001c51650b640c2c0061002a0420681c8200c1c00f08620392594515902e41c81401c03e0b071100ca142e601d4846045203006000802901045070304503094840e045d0000d80c481e64142c1c10180d9928101c4214101e100b426484d50050390003036130b4004104c0b0100071000e0b9103c009003010031401d9030240906a05030103840c8400f8402c1d94000d03c40040c031442844078010400c5200c1d00b26050270215441c0d21180702d0703ca01036400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 888536708 1250 888535458 888535463
    0xc0105271e030705040b30030a0e0f2403070c0f0c060f0507050a0f1103031902062d0612030307090504110f070201032412020907020f120f16 62
    0x74001c0310031116050403c240c0780a8003040d1010840952910005803103080038204108500c002884130a00a075000c201441c2c4400000b0102c2c1e031201c07100700e4040c00c07500e201e0132498082c0b507075404100c9661810050100a0000c6100c003143c983d00c82001401e91755000030300080901c0303480c1c0e04000c00211401802c0e044d00e0300504119001509001c00105010440244c0100b0050240201804a0030118080c01e90341c5d0302080981c10081189070220081c20340f181590352500010070820a41c40e415800394280c00f41c00d0b07094400703950750310380c02407000b03c0703044003c0009402c002035110100b1141800e40d41c00000c0141081255014180e0041c030b194811120b50740040c060940c20440307801c1038001d18250b182501e1916082c940f41654420545c0120000681019265543c0300c035205660303040c03404039500360b481d12103880d5111717826500032540460040b4000c0d102900090039092000c01c2c1102d4406420000d0920003900300700ca10125004203c1d00b0400c02001c0242d0031007101c11044480a507407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 888537958 1250 888536708 888536749
    0x311040e1c031a010c050d26090f010c11030702090c04170319140901050d0905100902090f060906090c041503051f0308220302040f1b020c010527 64
    0x1800c0140c010040040310070303c9040c840b9032818000080c9000c1200c10b04008146482040c41e4140c1440e00d8040e4010681c01c0c41d0b400303008080c8294440c01040300034142681030700038031620301c0c00b04003121158040003866001c1c2c0c1041c402c08c00103240c2140c41030303040f9410b9514281411f85074480011040585e540c0e81246170f2000034020119480741c2c4021126a03501c1c240385068034035103203a04200c0d200c0c14050604000d400584414088001c3d400b207020380d504142100c4802030f030501070380020422100244d01c5034620200140100d220104594418100903091300c0300b90711502c06103c0d000348080d00090800106020214025039000c01c41220081030303a502088500f0001100c01c0209264854140e5512000c035090010070b40c0001101e081443d2207081000301c1d40701d01e10100403001303150402540213040c031492140c00c06c803e4000f454085d03540101e0701000488200266a00c0d00d01c1c480c00c41c041042844200c108401c01d1074664180729402e921a98411100e100140154500c0800f554025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 888539208 1250 888537958 888537971
    0xa1802040203100e09150a020c031b1b040b060405100c050109110a090c021506030106081204031b0f0e040812090d0305010f06120903030b1302090f06040311040e1c03 73
    0xd1307804450903030030411480c05000f0340da482051101c45900014545161643c00041008002070208212560074162030ba001010107201c04000fa00d8880303002102054a0040354101040c0c41c040c0708000d0a10001010940f070140703480c061040d030f0b8682003481418882a0284000800c0d828004c000140c0d220740004043d1074420700411496566075003001e0324241c07070000e2030303099190002481180501c009002c9d031034a680300da0000703003d401107802604690041c03001020784c83c2d4000003d0005d40e40719a810703042c1034200106030941c040082c4580182c01c208850204840d0100d807003007a80043c052040e40d442c2048820a040940d0b4040d9107402c5681e001ca82c488006541c58800e00303002d08801000342da002e91920300001c1414050100b5a2501d50b076500c0180c08060095010010580015061480640c40f98004100942003515024000c00c214490040c2500d0810101c0703064a40c481e4040251414030303018070000342503401c0c1c481c2840c0f00d401c011603503410f4000baa013101c0c002c05030f4012840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888540458 1250 888539208 888539219
    0x120313020301060e1e1803040b031006020a0b01060302160f0f02010206070504050d1b080616090b070c0b0c0f03041203110607020c100e04021c0c170a180204020310 72
    0x2192480c0d8410340407110700505000d5041c809940307017450a10344603a0b02207030b51104c04207507200e407030044100040c503c000500092280c400401541c03254249810440a540e42c0b884160b0f105c83e032124009140d82c00c04001840b6840c0a6070203028031213800c8e00101c1d01e00800395036000c0a099001016210354159900318021903904104140d40b0102c246480f5040c1031808001c2440140319079070040c50029500c00c64100c4032048680c15005200c020b00300c410905264480c0d04c0c6041c0c03020003180005e0001180030540b54131075000c030b401c550751040c000e001c030516001c3c1c0c55181d5002460f401e0141e0086502c0000040b600f000500090403051000300344690302031a01811642000b00007a80b59004901080002a004101a0482c1c00140c800003884001c03070900b198000505800c1540c0b052000c100380766218079104002145880701a800c1280c4501c0400595400304240702c1204003200440000b03050440c25008000906000321071068200410f500180903a04101c404401032134010804010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888541708 1250 888540458 888540461
    0x71d040921090e060d0302030c0703230f030a050904090c09060501030b0a03020d02150c0f060106200c060c030705031209012702010302390106151d0102120313020301 73
    0x107801c0a00d04146038003500e0300a011181d504000c000c0c03031044042c1c0b1507610601d8028011182c2e25024030303007503a20260b200d1821250f1100c0f000030200142d000c9445451a0850000f10174449a02c0d0718019800c00e665100c08485aa000c950080e40203611003181c040014160a85031010304041000400c4050400c000102143c58080080e403060010b014101f015848407510f00c2c5540d03805442c600764001480f80b100b4001d11071034034914010302c14048041c41c0c0c244042038113070503103030703030b55a00c1d10010182e4125506502c19400b140d503554219100e000c090707140c200e00404001100405072030a004150310340d41c0c19030b00809205000100301d03804025003814284650030b81101c1d0240c10401c0303002c402c140c4a402224290009041c50340c00a000d05c0c503140c0810345000c4162001c03d5000d00119000c00c80c004002180c2004103407582801c0c4c0105d040b264510a0020310306c0d1076590805601e0440d1030360110000318541880c10740c080d18205400c400c4200e0000c41c41011844d100c0b0724542c03643d105060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888542958 1250 888541708 888541763
    0x3050415030e12090609092e140901051c06150602070306060503372906040e0d050f040f0816060801050f06091f030903030e060f071d0409 61
    0x355108030030840b807003040d174462041d05e0b10719030180d444040c1a038410002203c102c00c0c1e005d0410074080d691100aa02d030118a04402c02c0c1c0e007443c040070400d2900c040520041140078080c15a00035650054140118011a80fa9040c90300442c00816011030003802001d200740780b038101e1001600880e809005020301d900a80f0028002500185892003841010b03000091031540c0c0300c95542c040780c610011581d40c8000640704540c00100544001074903a4089466003c030440391180c01e1803086c0000c00501c1c042c41070700601c94001c000352200c840c109004880c0c40c0c0c80000c00620b01041400081a00303440d488101c00501080c4004280f0640014090800e6800c9584898201300c000700c01405a41c030b4540200004540603a840e5403141c0071400007556500c514110180b01806588041c650268182c21004010b4043e8a0070000c0010f03620109407107503022119231715010100c1c03020850080c840c0441000e0307005104a003055a40c0000c001070161102c507081583c01e8880f03d441040f43c1120080a43e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888544208 1250 888542958 888542983
    0xc02011d03120c0a02011e0b0f090123060d1a01120c050a140d1a0f03010b03030703080709030b09030a03060b03040c0303110c06030c0309010b01020a1104050403050415030e 76
    0x114241000340b4641840c10718000c0c0000c8604034081000c9030403034000d4119051420080c07804908646200b07440030003c06904212601c1050500c0f040b2441d41800b4100c1416150415101e040c0359204010700c0015407202c03100640c001d1420826107110140f14410489104891401034201030b01d810300041c84c101700c030179108644030b1901e0a4800240d4018084416942080c14102c41e100200036050146e4080c01149440b02c0c2e044c502a0781104040b118152011642200c9091705540b041c07040c1803c844a05030303102d403d940308010f4a40400d015000d000e5000d8484e16011461503100d507100c0d005104281ca2102c142e91004c910890900c0c2c16018041c041c0200342c00301801c51410b512411000c40d050300c8041c041c021140102801c00c00140540705403000e010700750fa90b407400c01848004440c2d1048915142d030b5464180b076032600b50304c00b1070840c81854003d081000407000d400100030041c2030141046050140401000402034001c821052800381c2a07103001850140a02500e8100306205244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888545458 1250 888544208 888544213
    0xa0c021c150f1b0c0b1b0a090302040e0102071104110c12031509060105090108220507031b06140307021903030b010e0108010605040b091903080403110904021f030902040c02011d 78
    0x100a00703c0ea100816010040e004a084415a00d075030101e0a141c0d41040d80c1e00722003040005901c1c0f030950300960710b54100c034401d50701000f2000f5402c4250b0708030300075604014241c0c20f100448204a14054008035900340e00054580e20340303514612000c0c0b0b0507a82206115140c4008010403e950703140c44004136403e001550168503524208000801d540314503642e480c1842080780208014005448551010707404040e150414010b0341d007400d5541e80c4092200311909000360848d200d40812840d05481217500d19107410320080401040d01d070180c1c00081110701144030700410148250300140b1a445054041e440000340782e02030400041000c102d41150905101402c0010041998030008071400c41c3d04007040c081c1c4405600e00081e20b0910008030448040d02000000b10521800341d006100b04c074442c2c1c1e6403000c030385480000d00c1052442140c0195011445110011400d0345e008648405d1b19a1481e0010350786006500140481e200045903900503995005411140360154202240041c40d1100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888546708 1250 888545458 888545501
    0x130b06060313030c11100905030f1c0c0f120306050f0121020a03090c030506100812040608090c1801050102370507090e060601080c0a0c021c150f 64
    0xa00c142102400301c00a04000b00e80c0641c0c024805c032000380030041c1c20018101500c0c0601088000c120b40c0d920f02500b4840d025800900d140104001021003e00d4000c2c51040d51031100800c0030f80d51803642220503a40550038070780010008040b040045480c0c10b6545001903418186418460f5402d00b428466052188110680b280c0340d8400c005141011040300c005a540c01d10b0b200f080300509040940105640400d050100410601240c880c0c8074040e000303000c2c280c0036920001103a80c1c240c49905200766582c100000c0c010700e80300301d03007076903210012400300ca65a210b0940456090320029081c0700100840038010b11103580e040c011320301401040840c6c501d52203c1210010840089200702244401d107143e200c80c100141030020303400404800008100416200b640c5d10b0302c82008894a60004070a00c0010340030030389081c103032011074465541e1740100d0007455090141c018440701030211601d046015040001d1100e5100164621281c0b0001c11100461483c2d1410748026400f0001c0c002e41501 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888547958 1250 888546708 888546721
    0x302041a0901020a0818091501020105130309060f030605090915060303070312020a03060e0705040906241110022106060705030d09060f0f0911010518010e03010204090203130b060603 80
    0x130701d12a00c03076004402c0c50340c6c525454078903252400060300107036005030204040025040003203405c044803000c00e800030311156079030401d89102810394143c010b010450801042c13020510030b40250b04100d4040c103001500b25210400076000c5c00b03040318020815809960380011003d84020000d800c80303030940003181800b400b0364024081510b190741d988503190780484c100c80c01d50f1084d01710038010242c004440341c9034104024018116130107801003040d0141004800144040c0d0b1401d0307100c4900a402940004100d13600c012240c01c0e8100c240440a8880c3c1006100d40094610007008001d501700e0b21601c00410784020b0b110710b5400102080e08c190404c2c005000450004400c03a920170700390180c0011450f800c1d261010040c008410020305062422502e60b84890300e5038040391565000c0d140c07440d200c502d04401110389100e442c4100e5814280d803d40b01e1040d5000e4554844000001030015041030744656002c0100c2e082200d9007118a0342910042c0284180118010b402401c01d83e00113242d4680034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888549208 1250 888547958 888547963
    0x6091605032e020f0d0b0916050703020c10030e0c03010e2e050a05190e0c04090503040902030405030a0f09050d2a030c1706060f06130b04060302041a090102 69
    0x4100e032141402c0e1051441c6002e505859a5007620b510000c0464440000c01603020a41e0031802004402c0c0b032401c168a5811300d0803440c000d20549000d0309210f2241c01d505e50444280e008210304506603c21f05402d40c0c01661452443d42e200c1c0541d980c00200d1102401c50245170410380404240640d14145003010209030208107550541c03010505461045039240d5960303a64101c0e031a8a04099241c00107108210f0141d40145004203d181e2400e4031183d400100130045030080b0315051502d902070b051141380d038100361b081159440c0c0508140e07814a990b5821030800d070f034800c45003183c160f000025244105504000106040002032603c44251410000840c640f08030202000e002840030080d0265068840b20304082c020a42d40700450010b0350341d107440d4000c2c58203805144440207444414102c4040d00050311031241c0c000410b0581450702400511909600101108504286061021404035512001840100920f9500690701c900c0e111540000400c400152219001c0c100020304c141d0307900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888550458 1250 888549208 888549223
    0x2090f041517031e0d0c050a08010509100509040c08010c08091b0a032010031107080306060708030403020d0807080906180f12180a050105220f080609160503 69
    0x6a4401400c242444421491030048001504d4000703041850f00754842018000303084201500751007401030a1001c2c0e800d841c80e000313000c58603002a8403400100318600e441003015030404501c041c032101c11034481d800703c0c01150044600703442d00c84448004001c071074002d204068564245180c07031107032420412405134486100111140744116145450600350b074401c1c105400440d40a60841415901c54074800c11021200100600c14203040c24060940340c02030282104146a10035a00e00e845c00340e558041c2e003a000541100d400650900c0b2150008248070300450140b0301a80040540144a000c01810600000c08030010010740300b0500001c0c05002802c00e03001508001800000b406610751503162200d0000301e8a142e1040f001051803582c1820014240c8001d4500c454460040d13010500965030454828140003c000300104a1074071480c1e03d0307102411403010360b1060340700e0741c401030307143e40204641244d11140c08c0072042c40b11100c0104208250900c2c8013481c6000c0ea45050f0000e40c84508 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888551708 1250 888550458 888550469
    0x702120c01120c02070f240e010e0405220c08010501080a1109070c2001090510020601300819090e0105011815020c0109080705060d0b12070902090f0415 67
    0x40321542442d00f68003d0140703201414040003122640c0e03554480e21300111081702c044a040e0301e500200c0c030500c180708046282d8045410f859440105842c401400010100100280c0e520880300e0030190385004801d40000400e4010b0100c0307a001403d015440b400c4030810703031040803075520400d044c0340000ca180340c410345642400c664000036540d0350181904e104180b8440100550811510b980d100c0040c454a40310824003aa150140369071101c00b800000f01e911007801d0f01682c0500f0042004810030103c4050200001c03c12172a1002c1004189104042424003107410000100c2e0401840d040d84a14514211007440e1401d02585014603c481604040c000c1c0340c100b01500100007041c041c9210742a00419840001821200c10100000c0d15408040040c40c0000e050000008800000150f6102590001008a0320300b0091074050001000914800c503000011a034500380d040c081030103075000609001201507610407642042040441c22640e0051041c0d1070546200030b145070051440041c0ea2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888552958 1250 888551708 888551711
    0x5041206020a03380901050310020c0f0d0201050417090d1103282a0b0702280e24060c071a070606170a030f11120702120c0112 56
    0xc81602c002c8025024884c03072124100070740090388a4140055440e040300810340188815100c11303c100304400780030f080c030400d5496402440e249040c1041940204203a4004000b101e07513a0a00300c080c2818888811140340241c1d5403841000144001e02c40d80040d48142c02d008140381003c0e0000146d07007000560030151a902c01c6080341105a01c04200704440c450410795003c040c4035001404007440c0201da00c08039220036640c00241d0207491103803001381c200c07202c2d141c0d4181c400b414505a124142c000007020399100200a00300450101c060340e038940440c00050100105034204200d005001c00d0140804031581c840100c1c44030603456000071886511811241c13a40e850a103c2019450980030341c00010100202031200d03000c0a0030349004188d00c610410051010325030b03c04042220032503140c040030860700100200d04c0068070420103c441303901c00e4142181540e02c4602810b1400c1e09841c82145045400207017402517150141c94501145010002486804c604000007088406810280c10105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888554208 1250 888552958 888552967
    0x30a080702030f0706050a0f0e0604140a0b07030c080105031b040b0a1a04031106070c0312030905072903012607050d0321151208040e040c080601060504120602 70
    0x52003801202c1d18801c1003040f140c0c450407181840402130005444404c0003030714008800c06103c180b40206c600707015041002e02484c0c0d41c1e0b030715200007110060102e80b8070b5002d40242c0b540007c0d030050925000b0741081d90300040b4240e4481001d05083c0c410781010b0700c01c1c3c4c04200700c41c4002025606051181d00d041d9004545a003009020624440e0302c0d41002200f000d20b040402c480101c200094030881c0e014004802c135810142c0d00340080b40c41500c90142c45414128411310203c1e40312450695500703440e280000d03e4044e00c0d101c0c80c1c1440d038240c0000001000c202c1c0c5e0003802405601d42d038001070890b0707a4900e1955142c52100542e10401d004409041d00701c01d00312181c06035060052400030480588035020251442c90300400c1428006410b181014080c503460405082505c14044030360340040403016164140003070708022180c1c004003240c41c1c034010400840c80c40c0f2241443c0d80541c1c420408a0151401d100d48203050100c160002002c00c0b4091100b001134011695001205070341240005948 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888555458 1250 888554208 888554221
    0xa0215090103020c07120201080106090b07020108130515060a1706060f03150106030f061203090e060316170f0316150219110d020703021305090a0f0c06080609040203030a08 76
    0x41e014a104d02c0c0518003510030001103181e5840c00fa400e615100341d8070002c060fa01c400c4255271186d01c50142262020051000c14010350041390159003196140313266400c04406591034034540441030b081480040141024000076042100144001d0031600600f032083c0c0845d0056165140360003884070303106509452038411a500c060110507400380c0700c890620b8283da1a2000034000d4580c00d40c410340c3da00d190082c0040d040c4100412403040d243d15580300314540d40741ca041e400e0310690103404d036603050040f00c00100724107803000400001460070402d00031901741c0c088221810301045e243c0c840c0e440d81080204450381e0312542840c01e101c5510900319451403410003869802401106218400707066007211150300b89400605d43c00b140710002040301c8503044401c03400c81e1a92041c0c400290021240724081c403018002d03804c030641c440e0009040b42c0f505852910740030f1500c40c843c80d0984a12414000611500e0750213103802e036000ba400d41e2072602c2d03070a2640c0401d03a02d22402c1000f000700312080e03011803038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888556708 1250 888555458 888555461
    0x100209091f0509040b010e011a1206060d0207031e0224040501020d0e010524010c020105031801060e090f060705030c0703200c0415030b011e0b03150306090a0215090103 74
    0x7814001d0240f96a910f00761900c0350110764280540c0c0c0049851000015101c0204c40340c020041810240392405d11201172564140100d0185c150383d40100d06200c04411500b8a10142c00ca55000342c2d6403c00e41c012800c58400f0324041a2080350454001a0b4000403101d54417421040c1c07100e40c07040782c050554890400e60300a0060301164074401d401c1580b100031110341500160701903603240c441d22202d0300c0c2d8103001c9501441010501808a55122800c10140d8000c00140d980000c0e003110700c020500d442280142112299040302c99250010014807103c1e035000c0200b60390100200005040c1800c0c04c000c05403041c0802800e50032864000120713402003500c915140081c9408045001103c100040d1044d03403106a600c2c03c0300d000342d107480b95100c85559030308919011a604040d10314800c6e400c1217480100d544030f801100080303600c1182c00060b8104280e00440c4240c0d0242200e207603100c0507004150070042d003d81411040e0303211003802130150361000403d40108500d40b6903990340701c942000507070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888557958 1250 888556708 888556771
    0x1d1005011b02061803060f150d0f0b09031e0c0a0f03020a0b07120c090b0d11040305100506090c1920030304080406080105060301080304030f020d02120a020310020909 73
    0x20341081c40403561030740c00000602004c10400f000c8003601c0441d5241c007041e1000c1c00c1c0c11036605c030b41c50f0f0700d2148040890800c41984240a4000d04402c001c0c40d4403600d82048250007681c0009041c0e000040c000309034403040c044c00302411804883d50340703494900d1152580d131740c0e44102c0180c168404100301c802014000c204c4003501c1a880704100d030311850301c2c0302c002e0014a04d142402040e2810199907109a038801c82c0c0e038605880300408103504003861850480d004108070350700c45200010402c008400304400b04495401c00c01504030100b10f502e00541809031124001e010410204001e2018030710250928801c8003a100e20f600d4001c2c201a0320384c0d0104d0601c0d251030313500400b41c0400410301c01440f620000074801d5441c185c4032040c007070340d03100c0600607180700034403d80c0080d4000f80301c1800029034001c1418030407800103002c2401910981c0004450030122a000d0740182c2c4146440c508500b414000f02c21010301114045060090304c8001c42d440c0c410080c01031440282cae0a2240b40040c64072807404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888559208 1250 888557958 888557963
    0x30103020411042105060705040302090f070306030b0109270b040b0c0405040204080f07060e0a0303080c0d05010602010b031b060913090506090d140a0c081305030f071d1005011b 78
    0x1418241c0308146803000e122400d00291018001d1b00d00040e1a140140103c0c0c04899015200c2500c542d0b03000c220341c5000d000548a44205522007078000003140c6038034045400f1b00300000700081d40034140391540c11038824601c02e07071035240304010201000c0b40081c003401c1d0b400f0b50082c40010040d50344075803070400c034030683d044650301038404100170981010000c0c0629070b0704a4031084588094945c8001d480f080340b03075594550300000701c26043c00064403407400650130580c0c44102e1802d007188810a40250b82003600040c0050b9580c282c3c000007440d0030400028010000c13a0030b1170408107250046502485070b1554a4003806228100c00d0106c01a5448181101d41003000d560243c2803e000054036406140701d0a4000340b001181510340d145004c0442d60007024989904014803819501c030305c1940c001d010941c41d40311014200007030b02d44050011200c5140110041c0c0b1070075092404600805039480c12407804070001208121004481401e1801a91300074200314420320404461b0411002840000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888560458 1250 888559208 888559229
    0x3071406071e0e010306150906030605040b030601120c051e0405070f1209020f0303070602070c14100f110f0102041a090a031403040902040909020f010203122205120405190b03010302041104 83
    0x11f007500d941e8010070900a4030900c1d5401d125a41c1d03074000300001c0c0c0e2213600d01554160005001005840c0900c911840f4080c410180344ca841507031400010b6240c503000060100c990301e0703800f100d29145070900c0b88030380c000d46c503080c0051032100000740105200703002c0703030507200da5952800c00d5001d550720b1150700c80003001d005085941e07a11581c908200650840c05003166101650480400c0d0740c2e800c0c2c1114900108040c011075000d00c1c00799021aa003c103a44000c800748051940c13800000901409007040801c0854005031740c85140045a05a001c0d4104c03920500503824003038010107603a01504802103a4100c482c1c0c103070fa5407460b2412401e41c4030340e13442015039a100150008031003040c1e80244281c24000c4030340e00300701098600160384a108031403d000007480030200040d00314494481c80104c20750030156511040c20641c0c3d03014540040c040c1c0b40c0c0a1a40003080c10446446c1400e21400e5801c0d01c5030410b00b810346405103030822800103000082c86241c407002c640d8110949034098070003c0000060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888561708 1250 888560458 888560489
    0x417040902030a060503070608072c06030f040b130317071b050d08100b07170409110d0e0a08030103060c05071a060a090605030a030c05010e03071406071e0e010306 72
    0x14010004e0000d0701c01c01c2d0190064001c009400c41c00b4804080c401e452a03101c2540c0004802c2d1600a01059100d50000d2040700c006121405d488800188d44074100424115405041504002c0284e00e0003c1822000062040c2c41c00d0000342d000480f02c000c2d5000d68411039072501d5859055804984c4018020124560b00925000340440090ba00c041b428160312416015100c03d48040c0b4004054004c07044207001c200841e000045415142081d0300c56400c4685040a440d80e0301c413001e80e003003c907811042001c0450702c2810988a0310403503602c0302d403040003042030500d135a680c00264041480b000d0300041e5500440300c0d070303940142c04440303501e503020320580c584000a0360041e00c0342c4001e41d0070724014540001c012a40c00254812001a600001c0003010400c0305680d0031508603c403400704545554031004251415802003020f442c3e218071400b080c00003520b031322400a2801c840102510100304c078061441c2d1910101001c800c811882d6890701c19a00c900325001a409808564011401c11a0116 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888562958 1250 888561708 888561721
    0x61b050a021c061116080904141f0f0312050c1c030e0607020105060105090d0201051b03041a090604050904030507020a090507032f070f06180b0703050f041704090203 73
    0x12054182a1160408100904000e00c804510317004d034800030400300b140c10102002084078040904a1804024000f00d030008541c00d0703504450700c06680c42c80c04041c0c00a074041d200b401d800c0c80350700078003100e440d4415941e1941d00d07807524524281c4503000038068002111001c0c10818056507108403811048030101d02d189080043c01440c14000e0f445007401804007240d5018810300540703003c0ca205a580b241000d40d040d040208032024410200c1c10b01400700301a03002005a107110300148440c10340a50340f16890440b8a05800412010064168108019094040c1d803030304140d4042c0c030400d981005060703890b4039064030784d8850355038013950010752034a0010744003100d60410382c46028565802c0c0500c0d00c400e460020704a4003413105a283e12011450790300c0c40c10040008e02856402562030f850b00c244580c8410f011209268445080320880c0c0a0140c24800084e00564104406280800207450828100c080701c50703000e400106070b00c00500c04100e211044500b030f98003802c5c8002c000c650740c5c01c056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888564208 1250 888562958 888562999
    0x6091703090f0631090c14030a0b0d060c0305060303130306230a0501081207082d0a0309020306060d050604023006012405040b070201020a141e0304061b050a02 70
    0x144000d030051302851000c18256640c1c0901c0d1000615a2140c81c46001002c504070250b800c01880400904d80c0c0b8080c41c2800d42c2c0e1104190300507070103220001582d5900c090b00600b0313581d00a1185000782d00030806860040a454080710441760081d00000e511444414102c903000303d07640094000300362810611055900c164040c5040340c03030300001c440f10300c0417400900d07015006140000c1d018500c20b00c4030581e41c1068100302c00700c4d1000340c1c1c0d0b0030076040f02c203400b42d0060350456031120000a0b0360380488030031070600b00161600003108880c00c2000140c9591025551040100000d02801c00c81010031040400c10b5040311600f40c202c07082464070345403204c6031556441d0034410041c141030405004485d2017100c0100014440444e5540707480c250070f104c000c4019a00140c002ca045105542081c0c002c280341401e21075912000e00098280c01c103020003a2080000ca41000814603001084100095038006030070000302c81080e90310104422040c14804e08010550380040e4100700c4959140d508100c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888565458 1250 888564208 888564277
    0x73b06041d010e0613020d060806100612060b04050111101e200306010f140301230a06021b010c050f030a1205130b06030f010e0706091703090f06 64
    0x664066164503030b620310380c3c6003180c141a501d035038224030b240c4075940c05800aa001400306c100e034001c0206242c0d44d1154244d2811001300c1d4510b005800c0c080050180b2a400b20700441441102d14050250702e06002c0380d26214429841510b061003a07110211036440c01c14000001b0040307200c00100f04c040c0130b81500b015840c0c03211600003100c0d0310303003680207454001d280c032081100c10f4003116150660741ea88005440000400210b8000e225840c0800c00100400e040254041c000384685000000c068003040f0021110f000e54441c8034503010a400d01c052580003605880d2510048a2080324400110040c1c1c1d605041010280c01da0052042d070034406070340000146070021280d42d50000441610b811758080301c100b030307440d403600035207081c003080129444c0c3c40c4068200c440141a11105060032814908450503070212203580d80041900b00721858200da0210002c0420400c1405012042415103440e4880e45400318402c50000588210580754601510000c1c880c15a00d290a00c14185840940c0a407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888566708 1250 888565458 888565499
    0x1030c120c030e0c0a0f0504020702060c0615040b10080a051f08030307090f0e27060411030c030726010204080708030d1d210904091505073b0604 64
    0x500302d90100e5900b44408008120340e0010401c01d02c00e1f08200400004e58409a02643c1c010014000c4829441050206038050042141203010700007907001400705071200c0710012445a00e81c044181c00e619007100ca01c0d58800f4814200245603540c103018820741415202e000790700c410900001149100700000250f009684a8176501c1e4590303070700c40410301115528010007042510000225411815002200b84505089183c2c6d54034071642180040c0b0380300c011603050341c101c0a00313080c8105c207040c2400280c07240d2509501901c40541031052030160580780305c000d00c21451445d01d9103602d0380400e50549018100007800d030b50703103981d4032000555243c114041e1140304602d0401510825031180322180c601d51080c4000c0c00d8085c9994032401ca840d00e880764403003030710001082031110079a80c0b4130070300100c907216010b054800d25260600c0812a00c00034905414800040c2145500710b801405124100790300010b14140890707110411181140c005107590b401c0310000c100882e1010420400740b00d40e0381c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888567958 1250 888566708 888566713
    0x204030c0902070f03031802120d030f0b0d030c050309030f1b0f1c11040f140c0424050f030a0207020f010935070b0901020f06100501030c120c030e 65
    0x1501c688004040340b04411000f81000005a400d90020340290058141725000781d580d0060002c46801045684001d52030501c0710750461000a0480c94145c800c6900c4054188e0302000202c240707001141c0d68162200c0c001c0c060184101024007013060810072980502c9016041d2140d50300e400e0581ca80c0d41d02005410820350340152120916414510411149054010151902a11106007405a00c2140a41075034000f90a0316440429121030080808180000c40009851918441c500a04004c05031110320315910030030040025a1031301c1c2007043c01c1c2c06003a42802e4254130078501601c0d640320b10740d4440c6440781c0210800c0a00c0075943e028150060081d1207640c500315199004480c503514a0007416203c0070300c0c4010b00c500102d1070500d03c44522811650340030039404500c44601d4286244e2000000e40e4001401100c1541c0c144489203d641850000b000d183c02d01e800c0d00a501c034640d0083c1d0b0304150340c0f1083e20b03800e680701c0c4241c4040c545040f00101300d91b00d024a8000c01800f0500341e03245891 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888569208 1250 888567958 888567983
    0x91109060a23030c03010b030901090f03020616050408062706010602060105010e09190e070e040c26190827190e04110f030d0801080106060503090a0b060a1503020403 73
    0xc15000c07003141c4c0301d003886140d060f24503801c2c80c0c2101207a0300054900213541d0760310715017000050110200c071040903020340c004104a2030705008990f2a0300300c90035624200042031104111a02001031100c4d080341c0324541907406650181c0c070365000b0f80f8124041c82070511030280001000c9401094550507600c003a6110008c0703d0b010307c00e00c400d140d010398070b500780d081d888202e4a00622540c1d1203200902d10f0403050710030a5a59400000d5080303c01d81d800c0d00c452424620400081e84180308046544200a100c0c0200082000e0210b4070391510003544584040000199800c0000704800c446981c150009a10700c1015540590415076020072007940c0580020502c0c00c44400300000002c0444c4d41805e0644c4031030b562584c4031078198643c40e085a8100007143c01c10344031980d00344084c840016980e50780102a61510007d03500352069640404244042041400300320302c3d000c286605800d812070810300c2103840342000b180091140e03034004000c542c4610307030000e40240e0640052040b00d0182c80c2c1c1c802c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888570458 1250 888569208 888569267
    0xa090215040e0a0513030309050c0d03020102040e0703060b0301061d0a030303020304030206061e06131d0406060f03110121050114090a14040b04080405130e061b04091109060a 77
    0x413940c0c15544400034101004568000034481d4104000c0c0e02d10800030b03079001300e40f60300c0401c8a01040107005c8000d070350081014001c1c20861082c0c0e59000310309180500c042d518121f0501c110740b1042c01100c3c02c004010742400001c90003100401c02c500f00c05419112100e43d6400c0040c000c1d0000e0300d04030018042e010102c1d183d49410f4038009195400418840d40c24182c200070440b5560120446e001144094000002d550140d003000a041d00e034440c40304c503041c4c0741a280c15401c50350345401054264078150020700200d20300c034080441d642403c4c02c2111200d42c89030780042400785800140d1442c64100300c00400e09103907568515403056030550303901044d5143c0c101000700f511054006400318400c0100000c0200303000c2084550802d011b038070070354981b54940001c80c4130b20b2041d18841c40110b0325207010f030021003010004281d1080c00303d0040815442ca2075602c80c0340f80704d24400c0400f4244c8030407002c03141900f10b01c2150012100101515925080c4080c0604105042c48800e04003210b07580c0781c0300c40b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888571708 1250 888570458 888570461
    0x50c060f060f01030903020c0d0317010905040b0105010c031b030f1805030a06110705252304020c0c130506030c030601030f020103150b0c06090c011b08030a090215040e0a 75
    0xe071000030704465904a22000440040915202c19401c52150341c039581401d48070544040f2065000741c1d5036281d0071844910680306d000e8107a2018080c58546420400031449600c0c04a05481c400d01e84000402580e080c2298034036030700b548070301a40c0c001c11041b00c20150841c0c08002c0e03110540c0c0394410b19030501341e040c150780811881840d405801007140000003801507403100480c0d200703074848903060074029180e1501e0544500703600e013580e0300b0600c6206d140c003c10f25810300003024944050281030340700113503030a981204811983e018030b03000b00344851282c40602c68501c0d43c2d40301030445c030a41140c081d0100045d1009650640c02801908600d8855041c0810081c1c141c94100d050221000e000394011001003516038032400b161619180040384400c0c2c8040144003da28240080c980e03818000845402e00c0c03464901c075414048951209a860200c5000b1892140c2d007001226443c0c0c3e07aa80c1584000c2d10404000941c440c90f0300160360208002d070806032090360b80340c80b460043c41e070b5040020300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888572958 1250 888571708 888571711
    0x705010e03030d0c03021306030f15230406230f09010605031b0712020307120807140c011b170106020109020117060315150f060703080c0a0e030d050c060f 68
    0x760560810801e50f0300030800ba4100c409258050700e801490f240c1021440744c810010f54118500294035400880c01002c0305004146c070101c800f14503c5081032506022400000490707041540684c400f400d0070383c00b65120f5202c0e40c0100180c0d101e0700b40030b80c0b24403582072602c484101c00034844e078014500c100050601c5400c0c0f906031916510360b14a1074079104400f180046180c17a000d06101400c00c030141c001000142e140c078000d48290005c41c1c0b100071600d840c1c21b00400346140001000030101c10000c5a96101070203c61a5600c13080882e50b40d4001840540034003101c0d4050344a4128070300c000303080258010746105d510754209205c412a640c0701c4000720309a815800300640002c9140c00003054000c007003c1d00d03d8104070003c1c111503408100d291100200c05007110711202180f42142c01d50043e080444100d00c0302141116000e1910005a9000d05008005402040a500f01244482d0041e006079411518090020121003030503038180b40040165100d03140c8107200303003d05000f00e60140f4035901c1d0503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888574208 1250 888572958 888572987
    0x612240108031312051603080304060b1e011202040314030a0f03050903030408180409060209120708030a0c0f0804180b040b0114030601020703060612050f0a0503040e0601050f0d0e070501 82
    0x410740f0502e0181c2d001c459100140040d1014000c2d8001c03100e81410882c041c40003540f0a086c66501c81c501400c152044442c940c161501a6060015503210700c00c3c1d040c81540002c0c402d0900ca01600d0b080c5a20320024040c603000101030f071030350b0f40740500d442070700101078110304d440307542c5085044005100407010b40c1c2c8143c2d018051640700b0300218000030780c41c8009d400e40d6442428061184451100080d06644001c00191540742d80011a19201d0610118120070710749504001c0140a00e0811160b55070311030460031108000034078060b02d0801880c0d2407e61840c80d00140050340700c1d51915082d000c40d00c500052184403c0c503090000d8068280b5004244048405071100b6608540040401c0380d0307130340000e050b0f50440c02440d4020001558078451140504040c22002c4c000410914100d407a04904000200141e1320031485030380001c42c00002c9805884d80103290700f0107520f40350010f80340340c040d6682805900300049550082c0b41c441780d00ca026403194910490300c180743d0718001990301c515041c040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888575458 1250 888574208 888574237
    0x103c022106040b030f1b012d020d020109030503040b0402040209130203090606040603081c0b0406080c09060f0a18140f1b0a1d0a150c060b01051c05061224010803 71
    0x100761450014a040d00d0180010f048c84500e610101c4050415415504140144980080c2d00d1103112a8100234110001c64240001c128071102c94802a01c05c1c04001c1c00184030b01ea007400000c00b151155015070b00d40510242c001c10001c1862030300c2d800650400c5900541c0f6101f0180007078100c4c5400e000322411260170816a038034005000c1c0311480c0c100c0703031040305407001750f221410301c40561640d01c9050001c1001601620301e802c043e1040080014001e415180708040e0001c243c2080c0e40c2e8105944103d440f14074403154450300510300400901201c03a02c00a0b520200004c1040300d144a0680c1d622860302a008070603034480d080591500e070300582881c0e10025140300708086e43e501c10450030b01c0c10108020420005a0364070b00701240d1590850180800280e44440c00ea010000a4094462038030000d0810a090180500038418a42000071101e1960364607000411560340700c051562a500384210305503001c030840a0002c017904201c0100c118000d040034400064a40c03004801c0d1040212500b01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888576708 1250 888575458 888575473
    0x4051b030106061d0f15070501140709121b030b090105070305010605180a08101407030921030b04050103061b021c03051008010e103c022106040b030f 66
    0x400100890050100d00c0d0040c00520948105030b0382d10f58106c100440340c5281c076665000505d099420740700c051030781d00c07521581d48052280d5141c1084e101c5054a455a0302c40d40c811000c0c2c100780d00c9040160481c900d0f864003655021090140381d5180910610545000b071101d0b80355240c00720200d6909104a4000a005001024801050b14081d5411718070082c507100c00652950000b500304000d0792900c001705035a8600c05080c44452a0381c4950088003407d0400003642c0d030703031691301a45010a5400f05503405c8000b02c9130f601e5000f40d22040341032030302402c10009581c607460994001c00910040304e001800301c09020000d980300044980415582c071200c00c4880f0001c141c02d07000707010040c00003040d500702004080b03800c6c08240300c2d502c5c0e4030348032000502c000d45104013101c0840c1da209038500d000500039200074220300b190103501d01240d0089680c003802500d039034061070002d008540c3c11589400f10307483d4081c440c8124509540c002c42044908022001c200c030109595100c0c2e481511b01250000704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888577958 1250 888576708 888576737
    0x60e090402150906130b1b0a0f060906020f16060b0a120803060409080a0302070b0f04030c12091d040506070306081f1b0c0302060702030a0e121504051b03010606 71
    0x700607060f18440900803509002810b000700da500c040a0b00845003140c000728a0340244040400c03540280322659002d086108070030340f034608612140e00381c00b61003030ba00c52411204004c0346904a6046000203190707641c13140c160150005074511202029200d25013403007a0405a880c0c11a034a204944407190b440c003854186030b50b25805900020040e40d8007980d11107004c0e001c00c3c04034009003600c0084d41c0d0010f9681ea00d91500560540c40075010290310a4460208000281c11189440c0840e4000c3d010040000c4c003d1022201012150420000141503c0d081c0c8800740b850b403aa0f6008911900c15a629036641d50b070b0032011550340d80714001c041c0e48030024900b4044c040c0d8056200d02c8a5581d400b0490031421680540504100d00f107040005180c001c050080c19414001c0d0780d006075491024610b8910348000060443e82d544000c9841440c12840c4680d4120702044112300441311040b0424040c034041c2855900e841521042c90110700151a40c032440e0701e01881882d042c0c131a1a00c40b030030001d0818 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888579208 1250 888577958 888577999
    0xc041214070e0f16090b0a030b040603050d0201020c0c03010b0d0f0f020616030206060915120a020307080313060f21140108100c0503041a090703120504060e090402 72
    0x44449032540c010740d01c0101d022200c06010600c1001605880320060030600840d080d09402070700e0420070030100040030720150160400303e0310918440d143c04542040c50000003002045141c5c4000c040d0b10903e122041070301e0301074000d010005d2240c0c090303c603000440024903099615042d140c0e9403080302420081c00041d42d800c0701c112050b0080c610710540c001503501007419075110380d802c440480c030001000000c01d981000525070084099905080b141402007524059846110700c031803203071000c2c1c124016048420440f04140c0d0350010221044140e641400c40e03140d0344110500322503915500b00100c0c0d4140900011080e9140303513a90f0030103e00c250500151b840356044c51416a060325403c2c04800345503812241d501a000e00c5029001041030141d482d02160b03401d01c00f060a01c002402084042850440c81c00342010814a84460760741d0703130840007401d00705141c00c000c2c401c15545541092a5501c1000342080d40c586443d00004030310050204801a0340407076000b940414201811070220180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888580458 1250 888579208 888579233
    0x921040e190603030921030c15110f12060108040b0708070903080a031b03091a040f02030303091b121c1206060201051e040b0703240e0702060c0412 65
    0x307600c032034640100202102040c1e03200c80c1e00c19000200320020038001d20940c40350fa010030380c02c00425191280030340e03640541900031504c4003429140103641c2e20700e00c0b003030140c2000c064040011440e0396101c4220f001c58241d0707001409160503c1a9a07000101e655020f0900c842c02540c000b910341407242d50b0803004032004080103044d8804c10001010000020b090303d40508100c1c003d0b51004142492148075010700c10781345040030003c1504111542c000b0a40d40c4642c85580c48070400031084aa982e801d102c80f0900c1c03200360080d010302c000401c211010b8030125162a10f200620144002080300c1010080441d19003122081c65820800b150380401c55044507034000701c4043d060910700e043e40d80c4c0c5c80f40115550b507440100542d446a0400c66483d281c55111600507902d1070060300760f805c5c10b81320356008110043c0b4020906036290303003100b0041c8005100d1240820a018940011500c800c00ea600150050301c0c1400036100c0c540c041000c100c280070550382941c024200c05040f42c4c00076259400300c0c0e140c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888581708 1250 888580458 888580471
    0x2705090a060902040b220b09071409060f03010b310905060316090b1302070305040e0a0e0115031e0b16180602070602240622140921040e 60
    0x45ea41d6810f50940c5680340c0b601da4503034154203d84500c000c03e40f01c40041c1c0b0340c030030141031042c0c1201040041540e0441010a000015030070041c0e200d525090214145216500b003009182001000020300241882d000b40b08244c05c10403000351103c0e100c44010706010031480074600309899030300706000c14100c2d5402075900000c010116030b28240e41e62100100b035000c1b43c02001d41191111402c04580c00e1140c145420358112180440c40c00b001614002c11a008600840f040b8007503180214030602c1e10f80d003020091a44a80080140104103121210030803003500c0200c41c0740150703050380045075290400a1400c01d4000645100320790340d00c2072040700c000d44204041c06001d2030200601c0c019940195044c05001c1d40e80043c5502ca003403000c00b07071814441c002142c150303e040c51075201c0044007281c3c5032a048072043ea0f804445d80800b00441007100345c10444880c0e03542c07802d2403130598411103242c4980615400f50a80c9c03c800c540807a25410500711800911034003004000401505010380e034526404130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888582958 1250 888581708 888581711
    0xb04121511090312090607030806120102040b031b07050a060b420a050a0f0c080a0c0b090c061c140103030e0a240c060e072705090a06090204 62
    0x10940440c404558100c4048084a20081180880341c101001201512108101c159040c0341c3c07481c00148103403064800041c02c1140d804013103030ba191507008030f01c240f8503080f0000350b4846032265005c9a89820031181e80142e0384141c24094005403a02d0111244290403002601140800781c65180141585002d280e81104944014042e01c041d005c50008005105251104048175411403203441c00340f00702c0701c00c120304a042180d1071000d50002d04554502140d801e104414203034800c01074035110100400500102400541074641940c040c1e01c01c0ca60602c41e0800b040c0b10b842e003050050740e0b61138102000d508031030f0401000b1441000510441584450254085051102d420305082c0421080c1d00c104d0100b0040d14017403809190443c11200030b00640204900c10301c0d510307600840d619454201d524180300421142c0c205000d0a500902d00d000c5203070007103405075981c4002d041000c12940e00e040442d102c0f02c0c1459800583e25000d0240507512240c010203140816441d080000d00580b80300320b9105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888584208 1250 888582958 888582983
    0x712121d0f0d0203071205010b040516091406070606060f11010c0c030305220b15061806070309080105010b0c070e1006120f05040305030a0e01060b1606021c02091201060b0412 77
    0x19002a100402482c81f030000801c007042004144415140d0207000921001031034034202c160141d21403090f00880d040a804402c0781900c0d0004203030603125115010300300c6170030101c0102c0e0b0300d90030840172521b01d8020b50364501c1a1001305c054500b00d0301b589110300c00140303a1140300c0000c40d101ea00b041e900464806007085210729203000d8201c00c10386103031084039001e50300010030a420740801c515a00c0c80f0000d0ba8114030b00084294802820107028030b00900c510404202107080c144200d001c178004e030001c040204030558680060f42c0e542c0e007240040301e03c1c0303200d0030001180e80c0d280d041100340070b00b01d500c8008c65040d0608500303552400000e0380c4d08c1c4030305955850920b90b800301e07800b074280901d01070f8a03025901d0a00c3e00c040019200040d04000040e17040107000c01c105c04040c0e045031030034182d50341ca13640300d00120325080010707111310300e104140030b4072081d03442c0211403090b4000c001c0c0d12030458460486844410385030b426150644035a61880106200030400c82048408c0d02c40803d00c9001540e089 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888585458 1250 888584208 888584219
    0x10b1b0c03071d0114130e031611280603020901020f101a0603190b03010209090c0d2007060c1103120103060605010908030f0c0712121d0f0d020307 65
    0x2400382d181c0c000102001c89012880601c0c3e035840ca12805002000a03001091000c1e20100720729015111072030055599032080702d10000030600988810143c9444524405092402c0050722803a1080e81107224004102484200c9480b02c0018015007408a903014403161038850150001c0d082170315001d0660042543c1c05482030018029000d0f0419110400620810f08004031440354451869280c0200000c205105d072000b1881100c0e041883c1243c2d010480001082c086406800750078107440d00800700e501030010900840010b40505032442d0030800c6030030201a4015030f000b13080034070302400900c00c202400105400b900300c6d101d1001c95052040415110311402451a40213070401e40d81e000c01d42c80180200500e42c012080240800d10f80310801c1750508a105850f8480c2005202914200040c03080e00110184410801494505018040d0342c0b4541082d8210001043e2408001a52030f08003e2001011030303d004042400034001c9a007000c180c100340308000c5085042070340d05200f05000001c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888586708 1250 888585458 888585463
    0x618150e03030706060807060302040810091112071409011d0c1e1902012d061d0a050703050408091e0301021911150c030c0403230c09010b1b0c03 64
    0x1001c0344140d00005c1c003036140c02e0f441030500941d44c11810030540100b1040040b8440000e03080b60003038009030009004803803458591001e08000c0007258103d2128411104000800f040e458100c1c2c9502d4450480c19100b43c040003003460003401000d01c801500c80d4000c0c5460b9200880310f6020a44020b4a440c1c442100c00b441800e4441c4808190303843c100044a03201030b40c0c200c02440112226000a02c80108914109104040072407660070741141314402c040d0400095401c13000c010140203c13015003101071141c00b14084401201c000081c00d060001043c02c0500c2849102d00c03075a080511941010b00c80c2e8200302c0c2c00e82d000310040312846409440007419583c20710080c030705004600c20381d0301d4030005894085c04044440e5844806900112080c0d44c00c0404a804542e00c103c842e0031450340ca03540d2210410050013607803c0584406941300d181101000b41280c1407a025030b07900c044481c0752040b5802c0000c4050240502411804144040314149641a03441c0301c40070840d50540d1544045000401d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888587958 1250 888586708 888586717
    0xe150301066e190510080702030d02090604050901060c0201090f0602211215130e030403020d0312050709090f05060d02060310082d032106180a0c090618150e0303 71
    0xf1101e0301c400000f007085141428864801e0452820028510700e4544806510703030007016643c010362500010aa90544d98840c1190003900004005143c956120140240241d01da484204d010600700c00002c00c4d15600440540c045440c554014074074021480806848442403c00740d407150f0200788124620041e11070485889480c4100c910503054801d2010000000d402c0300305090b10626140c1380c0030000d00c02008035802d8a4042d102c03000401e10794035045a400b4100d4000f120070700d00e04014842403c1c2d00c056454202e5044070000d220450303403900710400300e807c10b42d07405500c07050705010700006003480b001540d80840e181400000d4507903100c8020703041c4040040c84c84103100c4081070114816001c3c1c41212021003612008505105084040c1c5012000078000240017032010000241107a0710b120702c0c5003446003c9544180a0708040445401504c01d1007023103c04504030700c5000c141a8465040e01580b1085440040d114624041a084035514051100c07020003100882501302920204000c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888589208 1250 888587958 888587989
    0x3020706090f050d09050d0f030207080304060c0507151b080921071703040608042301140601051c050c0d180c050a0e150301066e 57
    0x80c2c038440c0e1a0403814030340710240d003200340a0404030506c05a143c0350075141042d90701014011915140c5c0c01c059107010080d5122040622000801048903648002c034a049144a44122940c4944a0f206141104003480740c0c9000a240401c9a18514584124090000340a426601e142014410205112269000141c2c07098002c590110310084002c01c048001010300440c0032584003e504074040d224400e52049100304205140440c0c18040000e03010380c4a0480c030118000340744000c00449020b844445040c818504e0000d00146107540100100c409190381c058403004905582d1007404003c100c0a0044141300e40c2c1171203859413940030b9120707403810000d44d1600c01c2000b5420303161030141000d407600705a029010038001040543d142820450300410700340c0002c5c52034202c52000c28010708241d44021040e4900900343c1c00c17042c03a5004903159030845245025054611f46014001419100c07800c0d401c50700a2140010300d04803201e51100d407501c20a0031709064030030340c40c1c002a00c1040c4901b04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888590458 1250 888589208 888589223
    0xe060a0b0a0b0703092d0608180607020d0521010608090618060604020706140c041d040807021002030f03010e0a050f090601050f0a0302090f0a05061c030e010302070609 74
    0x3444030a1400450070401800c2e00407525103480910ba50082c51002c4a120f1000350007141c180c07410900002d0050070410910b0110b144c04580c3c5c0d2954000c200380b2080d0740e6028a455003400c0f41000740e070701240c0c1600c80d051035002004141c078048812a0154001e40840d1500405456031054502000310b000e40200b07644c2d0380e10300a904200342e5042c1000c1c130141040845100012620181e42000700321903500800c01c4400580382e2140341400000740c19510b001001d035081c00b0041091001000000c2c100b0b94a41d0f404240381c0300c4101400c2e0807141d800b540c02030444d85041c001c8070010b10f803040200e4051203040c8150703820034288052046180d00203800041c4155040c10810030701200302c0c42004c3d40608044907a90b201d080482c1d485407920010301030740f03005004c01582060180c82d50b458080044d640a0078a481c81e00c2c107007810f05120031060b40e99003000c42c113000200c0c01600c2c0ca41030030304195144c071074841c101808540d030544484c000c0071120381c1416001d103d80400301c2c00c24072810042e42d0040c0304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888591708 1250 888590458 888590471
    0x90201021e0c0609121009120e09010e1b040306020d0f060509040b06060c0f15072606010e0d030c06060603110a0c0f1b1703030c09010c060e060a 64
    0x190a00075038103103600e281d0007928a11000c4900009110310203200c151912a03440720b2440c041020b2514039040b04545110305400070b5054144c0390300410065005030000200d00002c3d0078204c41800601450075440b401c90801445000c1d000062542c20000c911a030010ba4503416040c01050b81095100303654140c4c0c0440d02003c1d06100e4007a50401051485007000a0340c18000003d100440103003002c0d01e90030342074001844c2d540b1124100c8101c0800c02c812500b08407a42e00c1c034030340d40e840d500840c00f0803169030401240c1901e0181035103546917842640421351b00e88081799000304021000704070b035040220820419800c0d07102c6044070041d544c040e540b0020488030b1070404000ba83c86550180d010540350080c0480e21844840503503c0f2000d9600d41100b80c4c00d014107105035402c44a550180425210a171045951001a221841214100c00c1c0031401085464501500c0c1c0c001210004032031002001140d00c1588500410030b407051142c00001600e480041085207000400c40d508405642c0d07441c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888592958 1250 888591708 888591713
    0x30d050318190818031f0e03090102060c0c0a02090f01080d0c0521130b03100909020f040507020316030302091e130207140a0f02041802090c0a090b040909 68
    0x4001d44840c0d0311400515000d980c07829280500c034000c1d003020707141041c00f04d03003042d070020b412a00c50b0101c1c00c002d0031243c40d26009007030034043c401082c03664581180b030124031104d2020044182c41030390744160003400705a0340791074088103a0303803008446040c40c0c044c40b40c000c001039480400c102c1c00340549a40c0c0400d158182101c00e49015444001c04090203520000e2100094002a101d20010014905015080301c00d844204803030256401c10710104c5200000800d5100502000d107116445d5170603c01200e95440812504540e0040000380d006940c2d800762058a050581000340c0114051048074030b020006588011681d44040c01140005d400059540403807400503044810200040000c21006007090001940044050185904e0580201e031000500410b42e00c004003400640d025100c40e0302d6245400f007a03e80ca9904100d224030b1800c41034003980140c00d030040700d050b640906100d81301d8659512078071881e00b05503c40c0040254002022802901aa0240c801800c040c0000f054101091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888594208 1250 888592958 888592981
    0xf0b0108011e260a050102071a0f0a02070c0b130801060f061e0203190e03100203011d06132a0302030c040603150914041502040510031a030d0503 64
    0x103078030580c4a10100010101c0000d28800d22500f260b4202d0882c00040844500790711031065140c0015000740039001a68040c840113400800510344941941044410b82c544103001201041d08c416000c0f00001c40003400d1420240e0007411014010503441c12843da2315054124141c0c007000d003081302e0041484040141c06800d00900c8050004c4001c0c64031100d083c1f80008201408007400110005400b04515583d03a000b441141d0b40510f5050100410840c2d150b00506161201940b060203841007401400d500740c41313403094a050b110350700e400c1c514101c1d04a04441e2170300701c0a031901d544202c4074401541e031031541d44a4842c0c2e1842c0046101907085400780004800b4044440c10002e241c010010040b038654880c0448059800504000070144000d10109402d01d4454200c4100140b901005440745880c9800c0c55109a100d442a40d2010108840107000c0c0e000350310a0f1600075640c280d071302400901903000b000304840c0b45020050441401d80000345401504507440740410000030601c180c40f03565 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888595458 1250 888594208 888594211
    0x271006090f200d050a090503040e070908010207110f0112150311061908041a33090a0b041401060e012705060702041e0e15040804170f010f0b0108 64
    0x8440b80300b002ca041c0c04003402c0043c811621942c81d419910b000044400216501c054841c81d0800c2c21203445913282d0842d402881c000f51070b00404115400000200c40348140210b4640691080e22102c141e4800004d010640c41c20072030752414030140002001001e1840d00c510074810743c0c07809004440629600f402030481303900b6000c030f80c0160010407016110110442c110780f105400f91074255400e45e6a41410101981c040010041c10390700b000a00104110100d4600d071401c08000201c0c1000d010201c0031001c1c0080c03081015080288000014200f00840d8006103020744050701c0807920500307080005c01c1c089070036004880403501c061074440855912003611401207025150f803d05c4500c0203401e500e0404d110b4868035100f00400036200c3c0441d01c44c7d1300810001c89a44a10f80c0100c901010f060010345050200005944a80c0080070341e41e00d90304080c2030103107070080502e40c9864200b81244410500b20400ba4410780702d84416602c03840800d100c0d8090003800d81c40001000f46e074440004140140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888596708 1250 888595458 888595481
    0x712020d1113021819210f05010605040606050c0706050a02030403050a140d18030f020105220602061612110c0703030503100b03041a1801140405011103271006090f 72
    0x907591541c01c942003500401000c6d1240416241c2100ca43c41c0064403c403410450b00a00c003001c0d14540d20204441500300c032080d00c0c02203d00f40100d5494101c210f5282c0a22108425542d02104d4200009801280200070700c0350b0340d106580c5820788030744440b450080c07002011a0700402402e4440c4902c40300780030b00d1919440514280c10f4080e10100447c02d10310882c00702410b440361599440085a0040313003201c3c00411152a1203840790b072003108401f0030200501c5500007501801000800a0640d41180c0010b401952900c40e0042d047c890b0fa50000c0100110003c0b0210003008941e118180422841c0006c5100b07549403a40c1e071801c09108aa000e090341d10415038007100380288000191340c00c81100c610f00000070721b400556240b0703904046a5101180040e400c0d40790240c1d940c0c1c0e201c22134560700c0c802c034003400c0240104602410101e8252200715070740018004222521300102c91903410017400f81e00070004868180342d441001008940c4554440c036000782e66020a600107918501500c0100c0c1c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888597958 1250 888596708 888596719
    0x6110106090603051005190e01051014180603071d150d0816030311031005041401050102120a0302070c06091502060105061c0207050124080712020d11130218 69
    0x1843d680d40d00e82c0c5c036204244602c0d03225840b030001903100080740c40030100344c1a62000510450144460b418001c10094490225070a0303414404201c9024240d00b10001100250001000c0d240c850001e0840140c0a400d1a07414020f1010000d03c0c1d455800d8030800488000d607544500703040c125078802c0c051120282090058018407911404a03041c82c096503041044c2d4000005502840d01e003c07002000750540014030840080140b082803510240203006880040c0c5040207843c01d40c64004d4203a500900c21349006a00003a054105407201c100070341a981d209040150800f1400e545881941e540741d04100700042e0402020490400340020502e003200ca24000f034801941018007203220740c800c00d03100d0380d04041800e4002c28011507e504850b071980c0c002c00200081e10340e00060031280000e55040c48030720640c0c1ca02c040b0b520640400c1d42400c60382c0802150003d0201503083c80515607914000b5500030f2503101c0e04a001da220104504440f69071304400581e2a24940000d40060400006090080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888599208 1250 888597958 888597971
    0x112021e130509150d0b070516050610051503061002030c10090c0905040c0504240906050111030c190f0209130c080c0d060f23040c0504050c12040302010b03070611010609 75
    0x161101040c4205051708020f4a1b01650303034001c070a58041c861030292003514880b9000700360500c2000f042170350145242d240c80d40000303540c0f241081030b24038200c002007031718034001c1004c02d0041c078107806480000e00c410300650b07091550755195103003030a0f00b81d8000440e00341c84041040400c0340410350f1101900300f001080120b401d0544940031010060700446001fa035880b007501c0d07680c414000210310340e0000122428059500c55260781c01270f0640744a1140451b01c0030075150346080f0040269000c055015009104131090103500013420b030b0b0500d80a0703801030240016a005602c1e200513540c4168010070008040345142d1501262007100c0e82d01807040758000300c54040c201d544078541481e05c250080e10110b07445605070800390080c1907003503861801e44040f10421407803c0385100860300c641d000302140328080d42d07a5410b0105588081f240130307241c02c0d4100303d1040110b140302c01c5a030b00a4000c3c40000303003c10a800100f440e01005e6001000401c01d030211019091100740650b5001c0c0070350000034401d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888600458 1250 888599208 888599251
    0x5010501092a0e150a090812090d1203060506070602220821190f02120f121b03011202040e0109020901060f0509090411040507030b0112021e130509 65
    0x6440421494000c000882441203551342d2070260840008125884565558114440103010120a885020501e020f20200300002d18009000c0e03c101c030102802aa0074000285c0e92085070740748030080070303060559545020603203407100c030007402030344d44160001a1303540c16134001c0010054481032a810102400c040c20700000c0804641c40a2401c8a855894002044842c4250050007110020340742a9420281400c516900c420500308590007030302500c011a0345040b900ca25803140d44804000040b040160b05008003a07101915030202d2014510802151150402c400d2035201381d00000c0e920b0007400030402549800e10840c031440a4100007080300c80d1803540030524400b0144038480c00d1044a00368451400d004a08591807044010710601079890300f4540280e01903e416485c90050349071000082e5640c4c060301c030351207138014161146802c1034110035650020b548000c800e103089405000c2c80360180c041c03100c0589981d2101c0561174529a0410052140012004201c9140025000742d1a951b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888601708 1250 888600458 888600521
    0x15180c18041b080d091d0615160b1015030e03030f0604090c08031c0e0c010e1305011511010506130c0c0c09200711101403070206041709010e0603040203190501050109 73
    0x8e0030a41e0070250720361040f10000103000c4580030001d002c50248004001441403803100e0b5805944400c4c0141040490b002c500310f04a403007a00303541400d50720410114101c8070300c211001e540810010400726880c800c583e240c017903006060b80030351120390000c40c084e203051040d15260b0b0314030307090744004004800b8440d980a50320716103100480e041c04006a540b10054942d000c04647c40140c4013004d111a50390b8001000010178015810400184030000200c1040418040e59000f910300a000c0780d52510f240b540100203080074100c0d9401e006901e01a00c001541550340c130801003102c04000200203c1c915081203191504170035074028441c2c1088828000368a92048495401050700c8942006d2500d907819181001d60014489081e03d0201c05c2048a507800a4620700c02d5200d4543d1420bc9041d071040000340f405480c280314042000302000004030704165026550181c001401c548120494815007410354400d00c4060390305075140c03c01802108183c0c002c2d80c0a501480303040c900503941c9200000c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888602958 1250 888601708 888601729
    0x6040903091208160302030904231801020c1006050a090c0801061407080f0702040c030c050403170d15061e09031415180c18041b080d091d06 62
    0x4101c2c40d0b0002c2209001100b030942d04d60020b40813180e050700c00c0074100070355213400040c0c4c450701c5079040505a20b500314090a0075144580c00001c00581600d800c04000054072110711041020345d800c0c80240b003401d4080014506601c4001000206182041c080c008000741704e0300100c03085424030714082443c507400304c1c403d030468400345410140da00f0800c0480c0b00034481e11101411410002c03a0741e610394410000100f600c14401c40d0100503007100c480c1e098098519400e070072004140140000c00100c0d0360b540a4405110754065483d00d450f1114856000f05d56200c02e59624203002204e060005980040042d136000501000c60030301c1c0d4901c100024400c91003400010100180d0303800b880c644c001c081168081d20b4510203a020443e00d402910382c4860301c00407404648502c14800410b42d41e0400040700314800030728407030b0701106035295151700940d09116240e007003035261487c80000c0ca0460600031690359024503950711254524040040020000d00c1201072400384004040c05030f44c3c0c0e144511070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888604208 1250 888602958 888602969
    0xb0112051203011a0f04240329041d01330e130311060403050319061a13180c090902031e06010302040e0405010902030607020f030409090c09090b0106080604090309 72
    0x17960f03449000c05414141c0078036803048100810000c1021240b180069030340134403044580e0108a8000d806500c1200312501200b800d04036821200b01c0e0410b420176410070000940701c80b003908000c0740408031140c03c48064481001c1d2a4103142d40100300b4440c0d41c04003002c1c0b1680603800d040c843e81011481c1c1941c0c50007402d001100000308903107408150207940301c400380700005401d4510615103402c000d0483d034001c5031250300030842d40c42c910315540074901c61881510072003240620750f44900845801145d004c05c41001503503040340000504c880302c08030348488042080b0008681c501c0c0c1c0b43d40c050001001c40d0803a4071064018010880018100705642c1112450564030300941d489020068000307202e035030415010010080c4c104002d000b015000340d00c0e550301c02e400303c031807a9a074014103d0703c070001d00d41009680c0e042040108501201c0c2e070040c04166014004d80c0e00216512020542141c07441d8408495000c1044010400f9907048010b0070362215083d0b5040c8040b510a80d0018441c16660261 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888605458 1250 888604208 888604259
    0x30a080105060a03061d01170106080304180216110301050f04050a0204050403051b01021e03041e0201090b0a0f030e03040602301c060911250b011205120301 69
    0x80c0b1040741300303810203401080300d040c403007100010610840300002800d004055000101c0039100c403507010141318040c1114814000356003401d00340044000c4001c1c12421080600c1d40170710000b91b00c0d04e000a007840d41135102c0e900c80015180444141401d4810040c480d140301c007800c104220106401040422584e80d044a0010381303070752075103030a43e040c1c01031480e074501d0041d0628141d291081c05500603d03601e6140f00150396013100c2038000310f40783e1204441c010070382c203001d040c1d0b60b8440010310f50720010584141030085006869810100c1d15800101841000645804029911940510480380c401034450041c0d480e080c2048070195540700c00c518a807024040860502800f51207035003c000354803001c0c1070110703510650700d4058208070844200d03560801b460074000249113000c40c491040c4680c80b1101160505201c0051402c003c2903454060703030340b40c0310602c1c03900004075401002d5018217140b40008001410a00b00145440307c0014048042041000184000003d41c1c0c404042c00d5086c410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888606708 1250 888605458 888605467
    0x801060c0303090501150302030f1b0d140d090e070207032d080d09171c05340f0309150902030a0b0108030d0506042f040f14040509030a08010506 64
    0x3400c4000f003da4940240403035103082c08042080c0300000d11102140c2c0200e040342c072000401303101c0303503202c015039043c829070311020b159441c5071400d001001600722409601460f0000309299491402c207034040100000283d21800103210fa20044000143c05c2403042c0700818000703007503645440c0d094a0a400120942c000801d050a141c80e800130380f0910560b120400c1a2a80400d1000c60003529650342d007210300c40030823420100200100350a543c42410403108940c0c80e0030100c5184c00c0203120150980010303041e0200c5d0001d18010000120905142c1c00c1109039a40040150040050b461021544105400e080100002c42da039a501c107185816000710024513a001480081e181c0000803400506954607031000154115012010709000e0004400620143d61030001308801c60b90b00e10203c0510b0546c40b0485800c2c01c2102e84070501023001036100c24039058480300b02d01c0414202c1d078005030014400f075040c54824201800380c2c0303811115400065040c5882101d000d00354078814015580503040109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888607958 1250 888606708 888606713
    0x50f0c030a1104030b15030a03051e0417100b04020a0c12021e0102040608010e190506060d020c010203010f0f030b0f0c1315080702160902210106080a060806070801060c 74
    0x144240311006103034082c141d8483d940d15240819010031110620807002e56001c0c60102d09010403140c00503545a40c44c4c515142c0f9090f10380050701800080300c9540c107820300002c1590b40c2014040045030310090300609072001d98a2681c81074407003104000f4013560052003281505904444403c100950159800c240e60a521500302e18100102840312204642000d1f000540f40046d801802030b01d0b481d0752201496a00ca43e20058511400c0d81c04041120854001d00b00c0100180d01c007a800c0000180780030304d0315101d0300ca424180e0f04125030b061410395002004001b40107035245818020b11100c40101c6c0030701d181d40c0300c20303260300801005451350f001c0550000d8004a000fa08491400216030a812122a1283c14151458844112010100d0154408541710070700001340b400c22002401b8601c3c051506001c208006504840304032400811440d89100099181d0344c89903000e40348643c2d80040e0340c90101d1101c010b507a41c9a00c1516181c04c080203202250313034011040d605503612400c04115284a91 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888609208 1250 888607958 888607961
    0x30209030c0607140f0118020103020c0a080a05120f010b16060204090906090204290f0d02060f090114090303070201270e150423040f12050319050f0c030a 68
    0x40022542c804800166031040000c604002401d0803d0b80c000c581c003034405085017034229403201584c4030030b032105041e01500540c401d8006000b803108020075600c403540a40d46035805500940d094001080001c00c1140c3c0700368a5407a681d60004010b00e000c800b0b945081c5e213903c250b00c41e0064070300421402601420038402c5a8040b600208481d4004100d64801070405c1c000509150380c080744114100b6021060840b840041444040b10b0a40c00041d480e2260041001c1c2c42040c460883e044207080d801a130261340d54002816400e0030000c20281d85110200005001c250300d0015041d0240c0140700481c0e41c1d440000503102400d5081c00c2002406c0304015160a80050040402103c92454400481c01003454207116004000710b02c6d00b101201400c0c0200400d46840480c000410440c10400901141d8000707003864015000d02d0308003140f600141c86507603050903284456400304500100744001e40320441e1108100d0880901c0030802800c1188400740010341c00340032107030006008004901d024059 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888610458 1250 888609208 888609223
    0x615140f0304030f030614010e040509011e020711060c1f0b0d060c090b04030f020402090613090905150f0a050403120f0921020319091205030903010c18050103020903 73
    0x60012030703182d1a0a2400600701d890591103d000241020720018824132190842405182c0c161920018803101c03201f440001c04008201130007030b42d00e0341c24200c080d03148a1044d2401c80e601c41c1c001b6a4070441403c007200c8084002412900881d410024071009880229040f511911020382081c0025a04031028019000c441501580032128503100c40400100d5484840811150f850700007002d07580700329004413400381344000340454485640d81e500601e09075004141c843e40082c94607080a00301e110002100d4580e070840380b99555110001c2040c054200800101e01c081d0780c800307003510310b0010482540c8050141c42200c01c0c6403101c1c0403400b00350042c0000300d42d02007000000c02c2140c0d442e84038080501600d41e400d5918820802d9a10804500c002c030050a00f00540c000f54507010b94910882c01d41401444d0080c2045040c2c000800c043c2620090030b40c5050040c0b004503102c500c0e01d002c25007127861183c0b03000b080c01040c2e480d0303081041e060703042c41d03041381c00c02d0a005840f03200010201e401c01c0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888611708 1250 888610458 888610477
    0x60f0904060b012307050c06040b04090f02160503040801050906040201051215060f0a090f03030206010501050708040e182401180e15070212030408161109250201061514 74
    0x12406418155240c04ca80038000c403a00a104944002288030b00340301891080d030041e2119402d08101c1403003441c001d608400201030b0484401440c1942c1d40c0c002660001003d68100c8007500300003000c020200b024059103801a00503001380103e42850703400a44103216264200740d80c4079071080000c02c00c2200e140d11045108018090303a5660440a803a400c843d03100d00702e014045a030340c50011464800010301c00003603da00d500185605c7c1d00384401500c02e03400c0104204d9a01070100000308284101a0003103000e050781024207130b0900c216009803824401180092405000c601c0001c40c00d07039030142c0b00b6504441c2143c240c071001c00324502000001d0a540c0b96019628422099900c1c0c041000765103c900c00c6400d0303800c0c1c17a0300f205010380320541488103a0380070f040080103001300701c0a03101180301090014800c0303a0040f07518039071101268001004850300c42c0c014504101c1400892400011041601e840e44000c04c00b490a191100000142c0d0b54442d60411010001c0202184d00c048110707aa65030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888612958 1250 888611708 888611747
    0xf0c03040b09100f020406020d0504030b04060203100906151202211b13080610081b060c01050403090306051303050313030201090212030a090e06091501020c06040b070b060f0904060b01 81
    0x21281315000007031b40c007034801c02e40144139400840070494070401c19201681d6020311508203984654881202070b401c06415140f880e001e01e000050401038510800f0b004001d003421a01801030102d40c080c250702007004013003040c940104040b070b0904160124001c0a01040c40c1c01000d00d4030741d1403214124142146a44d0f011040014806080780a40d5004600300c803840021940d096480941c40c00b0b00700123610401c1115030008031811702c00340c05106405042a005040c0c1802c08021020040c00c4d40c1042d541034000c201c11101c148184076040c09000e901c190100041c02c0418400d980c01005440000c2001d4003586404c428081054800c0d0400e24980f07400401c005041b00c07034500040c0c0c60b58402a00680410141c202c00213403410701c050304038400c800c01480034205a6400c41c0310b181038100c00303a115045010751014000c5540c0e40b040588082c01c1c0340880d403501d0306039615220400002c09131000c2d100d503880031180c0c8040d81c1d07803032780382641300ba8010f00100f031245805005a0311f04035200c40c0b105815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888614208 1250 888612958 888612971
    0x103020f0d111e04050c0c0a031d060415090602010e0c040f090614071d0f0f130513020118080a0f06090816050c040c050a031e02070501140f0c03040b0910 68
    0x80000f429441c0341c650490302001680c0b1102a0043d1912580b20216000d0304203071806804240a4040038240c02c0b2401090810048410000744480d8403d030000b04101d044156a0b40c0e02c16800720070000544680d000810440040300c11080d03441c0394a02e15248651b80303d540c0000045415004071700f2042c0e02403414040154000217615044408640c0040050500307029007005258603c0d2400d0b0010026225280ba09540c400340250f01c14001c2030190407140b1010801d03c51012849440c1c032885d40c1030040003d101305480010702d82a0764903800740c01c07135220210522007020007140c00c10a4550105e0000349004080c6809000307080c107010003401055002c241207010b180c18440c40341c56240b0480607182041c1d00101003004694030b5000c1800090310034405400c03c00e01940c45507807020035000d40e2074211101c030b8021406070392017410304890a944a4002503025043c40268a422044070013007855103180845a02034039000c0100080c1c20b10300c445020981a030800d0000342c00c160035501c1e003803011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888615458 1250 888614208 888614239
    0x3071106270c1c150209060414040905070905090709090b070302130806040f0b0a0e0c040b0a0812120903122d0a1a040b0d15140403170f0103020f0d11 66
    0x307043c1c3c0d05005071600400c801002c0c038414050300c02c943c400749008010b03a05050910250148401c1060180c80d005540d40c1c4021020420070001c607002484550008034180c40c14820302070411100d070303000101241c141105940041c48005030300b0b03800140c07450300503199a030b8900041c03c8040075a214242a0140d40140414403840a40802c2c0080c002d0382d80e00b00603241c500c0d0f01000c40c1e40f009000c4410f500040503400030f601d0f041d0480303c200180100754841e4240c454040504281d101e00c04980c3d1010300080310824030641c01c544e5075210b44584c0c0554200900030b5080000c2e0100148488180d8005240c1c03603511035040031003c0b0503851225602602850f00700340c0180244000034244032141d86246544c00a4a40f5000f0f6401440f0b0150011380059201e940f0b01d900b440400c0401d0141d1078403003c41030b03082941961898401d078080d94034503981c1290048641000c01c0d011703110340c0c1d2903000c2c200180f000d0f0b01c0c2c0390450304008130300340c4201c211900241040d406642105150961015450061100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888616708 1250 888615458 888615499
    0xd0c020d05031c1a0109150305072006011409011d041518020f0406081b0301091a180c0127091503170405090c0a11010c0503071106270c 60
    0x1014080913116142c1c0ba4181001540c540c9902c1c8100c103d12001d05200c000300c24400d42100341c0182480c05c0649880c1d00e10402c20710b000040100001040d80700e0001040103542c00744061344025410b0311441e0321541013480342500c10321303001440002400548080f03020012442c020020741d04032414108007002000801e1040b50014850580c45020006241c0711b65190038440d002c2126040c40080080c1240450050021840980d50350790656940c0f8030040894440901c054101a1304141d0030154038080c04c2c80f9420002da10594004d41d404042a0b25903a6049001c20803415524550100d0019080c1ca0300480c02603607821102c1424104041040d90103078410420007a644910040c10b40d50110780c101d0504c1d0b00951085540c01709455000c219030340031100040265024074600400c051503000845800c0d50085031807080091800010400303ca40d000f0b10602450b8210310140120b824403400ca040554045840c20019010315000001b800808102d040424503019024840340201e14410f00d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888617958 1250 888616708 888616721
    0x302101b140606030105010807140604090c0e0a09050c0a030207020f18010f080f070b0c07080d17010806160518120106060f0206091504080d02070c06110d0c020d05031c 74
    0x3500c2c842c200c0414014601801802d050700d04201c01803410b286054110500070000781c0080340c11034010040401c0e5035000d8081c4510b078a58a40f900818072000409000070b003142d540c40020664a0070040c00f10800c0d04504039403200d1010320303000d41c40d01040c0c0001b41079400f050075860351104ca140e41e035448c01c43c1c0c410200da0494101c01c00041e00319075030f40c22164940c1040c0005050603003002c1018058401c0100247c440101c1000031107000503180d40c005854441c1e4420f492000c180000d40d80e415107418901d507107001d040c1000107000103090084410038a50003409100341400800b049030400a9010040c5a04501c0018160400018000b06080c000d259900403c0c001850455041c03960600004840e070260a1500082c81b502d0050f50a1f007040810107841129602410803213000300a40c1070000e0640d4a000e0f803182c0c01403625005004e0040d0901002006164100d8241d03001c16a0f0412460400070390181c4061100f4003c501e095421441920b00141117883d403003800d22203200744d950040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888619208 1250 888617958 888617993
    0x7030905030318012006010e0901060e010e090d0f0813060b041e0f0605060f1c3914030411030105040510050108030720040b040c05072003070302101b 66
    0x84071170000040b0616181450144050650b88004010410103107a091410350001e1054000118280c9803c8a90b24110082e404450003c414809100d0790340010b218034641031120382000c01303c4503481c01c009081d0560041140400301440010001448480d170400f4812a80c000c000300040c00e50000070004a5054015084890b89488117011200c4503601c1040203803100100741030700740305282d1a0082e840d808440c0d401d0202d20143e8000340425017902a220404140181e00e1130721580070107088a1032074041c0381c00c2c4c0401005480340c0c08081c1d08480c2950325504140c140c88d0b52643c82d2b0a055040717060109400390150310f400100400d028001c18401103040c2d1020007403200e86d9031404059940d024500f070240081100c2400310318115201824601d20f400094400301e1074445850001e01101c00030902400403440008030b071003c012413100111030942d400700114840c00000c00200e56104441c1c00000d00450240c20700850300342c003a00d020003d6814200b1001040032040c6800c0e5034540c480c9021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888620458 1250 888619208 888619217
    0xa02090921120412030e0a0308010e07090b0d0b120703030302030f070804030f080603150a1a060412080c1603060204030b160206070e2706090105150307050703090503031801 76
    0x654a001601c8021110803544582c00c0b41d501d5141c81e110411401130048841050640da8142e0350007002050101185041c040d03200c400b4030758505003810000500c02000e00007084401a030a01045c8a90425074021801c001e0000403150300540c04034100700c10360001d0500314400c41380e000040503032540007548200f158082e0090540c950b40c0302507a940c8400e4500802281c02584400c44030b40c41078240ca0751041000b4121241800c419009407161380096130303482c0e10641c4130f50407060070914a8205040450085d22110300d8145800340011000340026001801918009003901007090100300030498040e8400152030255504e00d13004000b58000d06c02210030407465000680c034008a809920320002594028207220754400b00200c0c1c181e82d01850b0154806a85030400740e4280c82c01507641789801440c001c00d452424100100040c451050b404284940841543d5801040a078010740e03400102c142405602e46030b007480d0a0710007a8040d00100d40520001c40c1d88502481c02c070800b964080d4080e2107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888621708 1250 888620458 888620503
    0x20d060f060c060b040b040e100c1103120702030405060a09090b010801061706041e05040b060f0a0e2a0d0606050c0304060e0310050702060106020d0f09050d0201020a020909 76
    0x4001460340400d11441002c6042a45854042141d13a008070442690080c00040c45201200000b411219514005104d60348640d0b034203203170001c00d849070281d50469802c09000603030701c4d4200d56683e8030401110000003510307d00070480300e500030410b0f0787c041c12000f0030366600c840c0c02c41001060840144258441542007951129440d4000e80d0b0b414140d401c40d540b04160200d0805101258040192605e900f0075a500956628130751600c098044038400140c2c0801d040c00c05082c00d440ba00d1000d02031354429500c0c040c1001c070b0381c5e43c0c04640004499102144440d9603070b400e003204c40511400e03040844401d0304601038078105030000e0010507881d05000303010019161107040484450150302e060a80b1a40100002e00015000b000003034070500000741201c1c01490096803260690700161400005644604014401c0c503030103014521204a0b1817404400060040000034491503d40c4075840c000c8016001c942d066900c01d1100c0201d0a402078801c0400d0f0904180e2541e1b2000c0d464012038031402e2014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888622958 1250 888621708 888621719
    0x1031505011a040b0a0c020406090b180c030412030e030a0503240604050d080f1909090902010f0804050f060103050319020708030f0f0408070f180b15090d08030901020d06 75
    0x81d0540c409008100b5060919060000a10031907000504020512088003112401030b52140076034006025201e40101d90f40011038180481c420303200328122005103001003000749030f00007030b416030790311a800401c0310545010503070045c3d00412074854000003d005c0041c10600580c3c00c40000e6000e60304643c100c810900951988008140e13001d041d2aa1014040000b00098688240b041d10001d0054007547d140c00e02c0c100440040341d10240385101c4e011302045200c1c442c15001000203005212000080c4030100881d80000c080c1c601b42d400001c140416a004102070040402080a4003104c1d54101c1d120380d6180d0804540d2504030740c02203890410540d886c6480e80c1e2000c50a2812039985d400118146210a1036a10081e00200e8940794050003d11001030006402c00000c0c0c01000400848001d040c10841311130302e001c8030490480c04035410100c1048039034448818102c0d044000e0b062032500d42080701c0004e1460303214003070081c0003070f5400f0061005000d01940200110101560208903035955107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888624208 1250 888622958 888622979
    0x9060c1b01081e0f09010f0618050606130b0310090f0f1104180506220b03100605100c1b0807050f10080a0203280903091a091e090103150501 62
    0xb140c0c03070480c0300b010000f01c1c1310030b400c0a40250b001002c03c2c001207144000c8a800384111001c540c00448201c02ca1030314034465003210321030b1540204050700d000f46403a01d500100240d0010b68410b071080d07200008002182d240080c12550090328000c9400d2110041d84107007000582407901c0194540f924098601064415442c1282c040350b40f550407191a0503041181074005141c01820031b07420085031035019a5565031340526a40c0c0c3c6980010026034081140181343c50101900d210820107450721906200070340d00e40507488503407462440c20516600300f519000a00b41c82440f44156100c8540300c01242d80100441c3c418282c880a80e50808d050301e2090801c401e03000c82400309404198010f000c00c0f800d0043e44c00031a80300360707200e5900b01040380f000950b0b8102c8030540d1100000656640c07800c2c003007650000400b4000c042001c613201c0031804200c0303440c843e0300c00c01041d548241320180307501702d40e450844c0c00800c2000b0000c148030000e40e03603800c002c4c1e040c0103004019841c5625000000c603030000038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888625458 1250 888624208 888624241
    0xf050f0304110a0f272003010305010609090206090915130c020f012309120703052a0d050d0b090f07021c020c06090d0b10080c010c11040209060c1b0108 67
    0x1400043e2032105d100b9026079030001404600b08070321500d80c01e40c04031041020361320301c01c419180a6081d6803503245003416800c582e8141c00801409051050040c0540c0d1041e0603190f032003504803880300090722140000f2100803005500c0a400150103244500b110456600403a4800300799000e99090400445016088440d040c08005410800400082402801010465009141c00e048880750350100070210100c0e044454114006a03000915404039113101c000243e84c882905000b0305031044442031244c81c0c54801c05403100308003001ca40040030001c0c50300000400c0f40003401150190401c1341404000c180110340b0032015104038501071141580300440d54146c400710350302401c0c038019038008015956200c0000154008490f5000002045074030300c4082c0a0003481080f180940c0ca040c0545060070386100105052000d10f01102e404104102040304000004460050345c034500780c000600705000b0361640c14440c0c440d00218040320403410f03010041024090701c4030f1141d550740e0000107160901c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888626708 1250 888625458 888625469
    0x50408030408070305041706161707030b03010605040204080c01020706140306013c180e06061b06070302040f0b0c19061d1c0206070507030f050f0304110a0f 69
    0x10810004000c0b403007603006410010311900c1c1582c5482d942d10300c040070308200c00d016800700790044414080000200c00000c140c5100500381103460200340c030b0305258030f41c6000b4581d10901d0b4a1700e481c80d009036002c2d40008090718005004540303880c0c662800d180d07138403080548940035105091001c2140c078061040e00b80c494001c205440c0c60750f40e40c2001154050302c074000c01500c107007011003079008820403021032402c400c2801c0001c4c0394540300d240004281c44041e40c04004070030354407203090014a060141e0a603008405442c19a174422503d401801c0501d00d8005042d8140112014094040c0e45900108200c4007800d0001e04d206072501c801402c80d21940103060f0141c1d000c040201c04203010800030a401d6800707020001003a1014004010010000d90301c1c0c014582c205041c140b10200204000d0300a203055031008104a00c0c00c03e101604030311404c800078040c0b110b1521141011071141c00bc48203071740b54000035641c580c201440d0a03400941003240d524071481031603e020a4001510383c0b0030b401c0f42e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888627958 1250 888626708 888626723
    0x14160e010e040c03060905070e01030809012d08091903021e1902011805040c0507031106090601031b080d080711010510060e0f090408190207030203030a0f36090504 72
    0x61540d901d22008211b1410201c0d40b60250103400110421450081d900842c06411403075507615584000404c210a00d045032440220311405c401c6882c2c0303403120541d0f170340a11410b0031402926202c004a25040c1020344161948080390784c40c8c0101030b40850300c0c426000c40700c8803202401c3c59119401c0d46442800000c821280c40301c0140300e000d5031041d030340252807a00c4645078503a556112004613041d00d64503010f078004034400068410170142d200022010358015800034221383c0c14070004241d2030304010321001e40b40b0401d42c1c06607142c810080c607a5200510258003100c01c1840040342c01707400b504040b211003011894440d40c07070a0118060103014071802a801c94000303010309006040c3d920000ca5610380742c1208054070120496200c1c40003d50145010750241511007074180803d00d6003070f030701a070b0300811074000c14010401600c001007903c901b4034850520300005000001c0880f502d95a0a0464038204501c1c4c0c00070000011a520303510305241c1c2021120380140d11444d4240c10754078159170003800d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888629208 1250 888627958 888627983
    0x306060a03050604090c0311010e0108091209013b01020604050601150909240f0e0f041e1401060f06050403110303070b04110901060c0308060d14160e010e04 69
    0x41d00c02c0d4011030f800840203100180000e1107859030062402c95400450f21140d00c5642a100c42da0400092a5250310918103455185001c0303002c55118906c0140d85140d0400116100019071300508142d5480583c0c800000518401c4600c080e1940c00742020840900c6c4051400c1e041c15440403402d030b171103140c1080090500340d182001c005400010014040100404001c3c04a02544140500e1042c140c1c1d82e403000254804680704690302540d5584580700b8195014020800768880d2000703079600202035503000015983d1400c2c51540035120f80d1015030100740121700c00007041a07050f50304003801e50320740c000c101003a101c4000400120761805400040740c0140800c000040e9880c00d00c462a00303001d4103890800d100c551390b043c0303c843d00381c8003101d016241100b03000702803c1c24200240144594030b0700c04034407c0c6c00d8601400e000c9001d06414010759400c24404148001d2003503e940302e074891012110b0941c3c0c85550800c01010900440c0a01c41050000250b1107015414080c0525007110204824 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888630458 1250 888629208 888629227
    0x10f1d0f0c0408010c020c090a060e04030309150504051f0c090314010219020304092a0e0f03070801020d0b12030f07170a20012c010b0405101a030606 66
    0x21a9802030140c007034094200404901c0e05801e015000100c84250010082282c8070001c12042c020001c205280091801c141008040c1e00c180c1c5071600940c05040001e415007da0502c02c2c0d003001a540d401911508040c01d0008000000610620044012500d041e03160010492101a5481c926018000403030a41d81840424070687e1014000700d0303d45c7c00180b9012002000101c80703c15011720300003617040400d04001440b120b01628140143c004c2e01c190764501175000801c8a000d603000d48204020308810540c2c00c42d15101402101101c00900b1944016900e680090107544403100321000b250074909401068203080c625840385032078410103035081000c20100d2035801d80041c50140c40d100c2c03114160580c00d000c460001e02e902c0161b0f58541d8040164010200501190702c54903c009030b1600810f14081050003107034440c03100803080d10101c800c00c500d1a06d40980b41c01001c0c2c503406443d06c014059022400c0b0841e00c120f0f0110780562030184c810440480c81400200c4d5440d410810411203001d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888631708 1250 888630458 888630481
    0x7030f0b150303030a240909020a0b030c041502010b0904051e150403030b01050d1a010915200304051e150406050919080a060504051c050d0b0402120f010f1d 69
    0x80c1e200542d081070300302da05080200d8402c400741d8095507c2e29510f1851406500703001946c0b20140102508007442d500307012000d40145c0c82513210300300206400d00c01e07504045100303401070320248100502e070700198101402c1c41b60700c41909500c0b04180c400030a4030401c24140205210100c0d00030300034003041c60390b26074a040c3c02074540c3c00c402c1c50401c0070030070052084114074890440c22404c04011020080c152030300141010409400c44e0408040760303502403650342d91240c61031298901500501503036101910b601d5186008a40040354000e880c40c2d80b601003000d401c400684d98010880354416a0f402e890071407a5248510701a0100103001042501d60604040a8011030002d0004400c3c01c0280c1d01c46010b402d2824240c0c2c101e941e95268424041482420020150385a00c0341740d104415804045014020b40300b00d01403400e0298890349001c410390344a905843c0b1042c00700b194006d00e494101001c542c90b0360240107901c07020321404008214404a40180030314821812002040d9840c0d0060800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888632958 1250 888631708 888631721
    0xc0405040c050901030f121d1003110f0d0c030c0912050705060f0307020d030b03031c021b0304080d0e092205120405040605060901080c0a0207050307030f0b150303030a 74
    0x507450825040009029290350300d0b8907000314000c04619000f4400e5103170001403085140942d600b001400d030807001400d1041d003418014540304840f11700c683d081c400d0066000d00724440102455482c017050f4680c81440401c001c1c070651740020020408210b0b41074080c0c08940c030b001e84d10030028103403060900c0442c03a81500102c6c52400b600459a0071951b550000d0070680c0300010141007610040103000c6072540400c1280c0c2c034042c0c0d5080910038006c000b00030075940d0084000122031308080000c42c10120807180e04980f03400d08034400d031602e40c1a282d0480d950380c0d40244114880c0348141d40c150040d01d84246140c3c40101e000820000751501e0f0901451841d48204500e0103050004c421b1b101c000560800041348c59603da1041140c80301c0c605010003048903070640c412802600200600549684d202054a91040b50440a6600c0b100303100310403442c1c0122071300802d8051042100220500c00d4003100a51000d203e42d1007051581e54121501e0300d1840803141d05030705035006202090080340c043c0c2002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888634208 1250 888632958 888632963
    0x9120a1103120a0b040f060303080c0f190906021e0a031d031501140114092809050a062102010e010e0d060b120610031e051c18080c040504 61
    0x102d041100c8280d500300c0c04002900d08140181e03031601c28002c54100340c0900300544120220401c00700d40307541c070090300083d001400e003220040001824855000c1c00b8007a0741219010f006080c145611148019004901030f024190240c810800c40e141c0100c40c0c1c10052403000110405005070440303a6806840d052070240280c400c1c136220b607950b000d441c0c4041001e40030300c1b80400c0c07030780400b5450445001c48201070b0459060402510b14030541c40240504111481c2c0c80094031010000400c141d0328010600984c9a420003d421041d000210f00290341c01071402504040d104005031644c1c0c0c0c5a120300c0891000c4c885100401000500000d98020107003031504941c10305041254100c0f030030004820608181d4215070055403110110200d007800720b64007802d41d03824001007280b401d10054001c644a11880002e120304e0344101c030300303a50500c0329007241c88043e07100003200c1407958400c9500450000e0b00812500041c0441c40f00a81199110003441c02c6490540141000c0d400480a010142c04000c00c02e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888635458 1250 888634208 888634213
    0x60603060723190903030f05160f0c0b12070219030e09100506040803040306050c040521010b15091503161101181a1b0f180406150809120a11 62
    0x3c5103101e180c2c4561021004002c0c1da10041514103601d03000d4404404004004100602030001c85190640301d5036049103c1c0d04a508a0741400a40c584454445c05540002c05180000304083d0340b44600c40039031a000308071507002d8603200108103904401d514901e02d00603000601e402c2404186084c42510302d82c212a284114104054442c030101c0c90302ea11652000e40203600004040051080c0ca108168001c050b1035911450640b5080c0040c07400e80001c0000803c5c06550340092103451310941c412003008e0005440c0344001841c06895814a81042a2650081c0c4d15151080c0da104c4c40c4004503407180054485030043e402005004481502880022840d1903584403100300ca0030070454488a107051051020726540700c1981f400f0609804050700100402d00c0c0100c2040e041910541540da2880040001c42d0325001c84602c020765855410408540140c9050404070700b40782c02d04100001c1a61a03250b01d034180d1548075030103680e4110005654072041041c080442042c1c0301c0d02c0c503054281440000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888636708 1250 888635458 888635467
    0xa0f0803060f21010e060f07050a02070302031204180c1e170c041a04080309062209020a0e0f0307091107120806090c1c1e05041202060603060723 64
    0x1150551020a4000042d00c8410300040703900c803001d00840600c130145c9005400c00d41000000300c5800c4c00042c003080c05100300451040c055034401c00c0723003030021030300201115010403148012810303640c018082e000d00b82c03000700300440804903180183c1c1d4043e00c00741c1d90a601410b40c105110a024007070990a010000d00d510306d2440021644e582c9802265119035959640345042c40b002c245420303c4080c004540d105100401c00000044255003202c4011b4540320755031080c0003000380c5400b800309546142e9050040b00801c80a5195001d01040c085070f49079011540540c41c10400c652001680c5a90f1550080ca0240403001454001400c00a03448409d641400200d5070307250b00e218804022200018411000c01105180845c030f219040007900f50340c83d01d00810105c81e044001e80382c901d203d03041078030790381c40300440440e01040284507039018508000764201850501c040307494600914005210b42c8021501515000c078015008820365182c48108001441711100c80750042c103c2001d04c45070500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888637958 1250 888636708 888636739
    0x1109090c030a0803070e011403060904080d0c2a11060a0306030f050c0a0f08030a110309040f2405030a03030e0c043909060804021f0c140a0f080306 65
    0x4010114407503103e56442e03103002e0100500381c000c0054180d0410001440ba407802c2400d80007266000300e01a22121617a90715401d05c1142d0748103c8070007000103860903034014182980521842031400c12502d00441d0203030508840c041c0740701100b501034404540c400c4134003a0b6217052402000c90100c242004a100d66803a00c40c0b0340c03091410201919160040c802162017407038840c031903030060400701d072150403441c1c01c00040c51303502e000d520210014070281c80045d070300d0828100b050383c4240c403004206105401800342d13418042d015850b050703080407414035102d20b910300c000400710040d05e001030020301d40ca2900f91030440180408a140124074041d081d040300a61f140c9005080c1210600d42000190010b074607255800e403401c0c844134030000080d601070090742e1355102c5080000c07a034076491b00f109991642d00001e1080e41c01528182000c2d135070f00c0d00e0403032071a40112070340742c00d6400340039525019251607200b0340d00d8005d2298024a180c0c40d514091000072203410103140c1040380036004840c18140c18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888639208 1250 888637958 888637963
    0x61c020d080703051902120d0b01030e0f0d080a0b0f0d0c18020306010f0804030e190503160e1501080103171c1e06030b01050108090307120c0204060801091109090c03 73
    0x60820f5001a00015892203a0785000e6080010341011744000c0c0320900f804614101d05014081c0e60380325181d01d58800d1009a842134205009000c010000d4035850400c0c20216507660041490b0840031880318400208943c1c400d02c25444050405000304000180c230500304034101d48452801c03a40090150800304580000300c1c81c0c0d01c0300e0708440e1001a940c0c144600050400c422101c120800c00201d041004006503024115015401083d10352049030102ca2122045280994201d10303054400c6100c0440344080c080a00303811031b4050418582c0c0340c0c0b190f000020020a14641150201c1d03e020300410002d0644100c0c82d0b19240d440003607508003884a44c0c820800421603c40d01212511051018143c80400d10106848865240e0421100380f031691400c543c0b510502c20039041c0500e401c00151880c9040c021510025400007540107049100079001c0e107150804003084e4000c619100011602483c14401c0013449a0000d1400540e48403800801c80e004000400488060050710b400601c0d0b51002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 888640458 1250 888639208 888639217
    0x6060d03170c1201050d0f38060a06111c0309082b0204080c0405060f06070605011d07201006090f0e070f06030c0306120f030f0206061c020d08 63
    0xc10503655114052100c05000007410380100e84585003684c1468001800c0c109400141d0758040401c0290070744082c00d42540c801c1107412351500d0040c012000020f081615002441a58100c0b0545841600c45c94203c540c8803c003000241564003140001a404411b1480b51070a0300203850003240144042d500c103415500b050010503084030100c02221070340d2003641403a84c030300600000c085042a1a041213566078a507452105800349540f0b1000c1036040c2c40701da1007001c0040c00034005545e1101c2a00e00403004282c00d100701c60f00c0185111003007500130503003076240d400b1700e80c0b95844050102d040c042104080513004e12055a6201e10316100000e4001c80c01401c3c0109924403000586900e10382600d42034903448182e0b051150410030003809103107010340761039003607484520b000920b80c408804164000c0c0180c0e0400020712002c07810680400c03095a010700704043c4280d503540840d00703c000d02a6650003055a03140d038031014080c0c4c0b081d1201d610030140303680340780011f00d40400075025880d4412b20740d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 888641708 1250 888640458 888640471
    0xf14070507051e060906060306090a1721011809030903030e030a0c14040b0a0503030a21051612141602070b1201030c06050703021f292106060d0317 65
    0x421303002c11403500400e02c0245c0d480441500074207082e20303001080a03114640d2820003800e202d11040ca40c00d44d81c04440944105145890900b020075441e01d9402031164000d101700e109010384c3d091181e8940e17086000d01e0f006c0950680740c030800f15096690545000d0480480541c0512a000441000c240c0600c0480010070580c200e0402c07581038a4103000076034045c1400c850042101d260104010707100041203031000140f600c0c2455030381e00b58038145c590301200610040583d80c1030100740701c070401011030b4001040c04192a20400c1900b090940c0c0c00b500c154002c145034189814001440301100000c2c01c1c01d4468241c416503822944070a80748000350000202134428600c4100103100304001800340c40e000d00142d0401b0f42c103124080c0c0c1c001f0745ea8483c014240001d07410400c181c0c076450300142c1000b41458503a5140d48500032121181a2107400c00031115031040901c0442800f07841c106003002010005501d001d042d203655a030090003500090342c0c40440c1085120b45006070200d4807040102d01484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 888642958 1250 888641708 888641713
    0xc0204110a030b0102030f0a030209010507050708010212061f05030604111306020c031b060702040209040c031e1e0903111606031b08040f08190801090f14070507051e 73
    0xa01d40300000c0031030320400343c40d034103642c4200714070161705851000ba900c185480c0d00d405a42d511246004a1700c5020300540100710388074840010482c0c0701d064001e4107400c0142c0c40d0910f810380e20304082101203000c2c0090b01203e0390b0022201c807200c070b2080c0000c503404000504003240c9000c03c0c00000e9155401b4000b501c0e440200060140202a81031041c0e000c125011401003c07100f0300e5039440c12111103035105c00d038440c0c2c1e00001c2020840d20340e60141e80c007410004204105051107560050b000c1c01d040c01c1c244c049140e06881c44151101e00e4440d072014000010070204c0e940c001180340100500d81e01200742e0500440940d0001504002c00040c00500f40c1d24145ea84c006140a80c00340554040090b9400303145100c080f9030807140d501c05901940140c00c03c45185100020f4180151a8072070039118100081500c2c0500014a8104807110f040308d18403d002c0080c1000328040b0001c03152a401e11150b0000c0d004e012404030f0707100f6009420300d14024016502014400c407810401596101d174503803882e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 888644208 1250 888642958 888642967
    0x141e0c070602030c060f040c0f030308100b040f0909080c01090305070515161b1b23010507033b01080604050c090105130503071e140915010c020411 65
    0x1210140000d2005002034002141010081031880b9111640241485800400440000c3c01e10983d010f20310003e008035440c41c08140e40342c1c240204812000c507140e550504024000060b0040b0041c119011140c42c3c0c554103d03124101103c91014000300f4909690718034081c09103511042083c07142c0203400e0312039100c03607030385100310b2500038100042c1c11002546626500c003081110312070080c0007158000d19260180c07601c02c400128183c0041c0b170301c80180003c0c800940c499220014640c181007500d20001c6103158076036200c04007040c0c0c4918070302034034002a803d00c10140044d0041903c1c004400145682c10b029a00d40c2e00440505041984c000c02c00c2c000303410681555503007040c0e02603004501998140301074500f07580840e031503200b2000258100000003490300c010b422150018030113054028151499150740300a01000308a8800c60302b01c0600300c5000004041c098150b03082049000a480501166036072000080240c0b10b681089040c040c85003101001a07460380700346407605204614040d03c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 888645458 1250 888644208 888644227
    0x1320c070f1208040b030a0207050a1b050607150513050a0303060e130507050f0607020a0f080105070207080703020415080312150f0f09060111060906090c010c12141e 73
    0xc0c2450b58048100321503101e50007400700d881d007000c5074207071500f505040350749440e0600b00320000c0c41448000741c004d0103085481c8042140540854030100c10a002201d001600c500402031984a1590002d010404803145006003504075006558004501c84002450700180d880d200d05040d100340c01100001d07907420050011841c464481c54000c4000791501d0031044103a552a50f03100e0190107a40e00c103265060017207449684490455001e81e03409080c0d001929680c143e420104200c6000b07200d0a5402d2000103901741e8070020b0b03504102c2c0c030544024428070707165809100081840c2e50114100140d0b144001c1000304040004103100c00c54402b6480130340ca031000e0907070a459000c406007481043d010842509a946802c043c2c261402c00f11040340d11030f00c550340180d5003070380e41107507440882c02480d0800c501c00c6000b00f0f005101d408914141d818074441c07000111b5541e5151747c002421004441015401580b040c0745986c40703024600d200c40d00d0049000201915068120811030481c800090311104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 888646708 1250 888645458 888645479
    0xa15080f100b1218010f0603050c010e0306040b0c070818010f050a05120a3306022e0b030318030111031e0c0409140f0906010501320c07 60
    0x500c4080140040c1d452030501d00614810300c1001c1c07842c2654090880461130f8081e080e00e10b8008400c2c0c10000300803131840e100c809009846280300541d020b00848a04041c25401144242c41541004005d0640c645c3d5039520380e20140d00240441c0501132007400701400041e10f9000408142100e600200842c01c015800108034900400410301001401d20440410a400c01e050786c0e9482c14400032140b4507621050000b00612054107503450000040742046104080b0f150650085180070302a00c500365220300c000da9448c1a5031003004004000c003041c0c90383d161080010f174402c80211b0003010030a03a00940c0040d00d1b64100c0111140c0d40310f14a50300ca4501c0c86c00b4420036061038078040c00a800d502d0250801100341e40f401040c00c030040711940000380307030f0300101040702c0140207902070030848042d4030501c0060246c2d048030309424481144010501c0c00c8400245c49040380c00581d120362810000e4820040c0440350b48103c4003072002180417138001480050082c00e003d42c1030400900d0254601044080f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 888647958 1250 888646708 888646711
    0x8030a020d02271207180b041b14030609040803190e030a021018021011010606030906060b03063613051203011406030c0409050f01030201030e0c0303180a15080f 71
    0xc1c0310361510601000c3c00c0030b0129000d02192108181403200341c20b11410740c4042c0100c400305030b1f48a0f1030000002702a41e4581d5140c85400c15a80e40c080e0164540d000c404d0051005403005588240c030040080d00040c41d8500559101891614002050031406001c40c00e982e81004406ca10350030125000240c00e6041040032f04502a0400c103020343c100603038070701d900c0c00c030a03990190080449410510196000d485030701e04104c2d2960080040361b076903100050050803003800c1260154101000002c111b01c180d0180da014040c001d00e00724018014042014800980308240c840c3d000d6501c2103040c01d00c0202e03003910b11400e800412110ba510040c90103a0500345049110480d0a5050006111441d80711842d1000003030144c40301c9650f0303128000a030340180107a9105240340c1d4101030030000030722400c120f414101c80c0300383c070140328418902415a072240207040d81c184e0554000c1c004400112039100b070130090b946002d49681481c54450701001906011450b0041c082400c01c0240240381000a501c117 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 888649208 1250 888647958 888648037
    0x40b01020d091502010905030a09080c18060103090204061203020303040c060f0801031415011502120319021c050702070303090501090302010909020a030f151d01030b010308030a020d02 81
    0x1050803440340e40015095080380e024950034801c580f0711494079039000350701200c89583c1040840351140b0420f00001d188041d1800b80f503109001d41004c2c03580c00e00380701802d11444030990207000b540303560340001100100000101070340e000f038942c0e0000035107035910082e40080d54000d5003d1513903442d0500b050001d4000380c2d407120040000110301138002aa00811040c19240d0290483c074414400c07448291512452100310010901100000108441c010b4100480c0001640a40d0314103001140804541e0200700c42401d9040803860385841080361603030041c0426030700d02da1254500c501c00c100090469004841c918090303407288000707106060b00001034070018002480d181e0306450450b0f000070602503944c0703d1700c42d1564021400c200708034000d03000907203103240031235081089015091061540004030f10406800b0742441c007030725a0301d41150058034180c90300b107414424183d1035540c900200341d00c0180100c0c81c440d400c3c0251301c0c042c0c50340c1c001270580d070351080418000c1c1e601240600d07020802c03003844c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 888650458 1250 888649208 888649213
    0xc0a0803042402070b22060c14070503031803030d050a0504150b0d0f050c122104050d030813140c0a06031b031104050405040803010f151d04060b18040b0102 69
    0x103242c1519400983c0070b0a94002081d02901d40c103092442076860450100380d860a842d81d4032011441030303407000c0709144050107084040001d0200e041e010380c0b0b4038150701545405130001c104d800c600f00c1e9542603008645801038102c900e001712208031201140c1c0d00f511481041e50b1a10184024003254132401c1780800300020b8208035022030300001900e0726a011b000207001a0a00191105121003800408a00702014041c041803652401502e80c035404207841120042081d40003001d041d95060083d81c0c1511400340001041c580035407000c6d141341a00805803094406540c030801c0006501e42544010007014400604075004400100314103550710390086020103103400c1c080d40d05509034000020b0305400314203000a2202d1041e426400c2d40c030403500213540250901051100700180007008504a819103900d14100c1500c1d4034016a0461440312440000742c95480304841c010b0740d601c040c095400c0014000181d16564041e040010b8100e00c1010b4040e80740e210b003882c0c07142424094010b00c507000f44003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 888651708 1250 888650458 888650519
    0x106090f120308060d0506040f0204060f050108130512040b04090c0512240423070809030d0b0613090c0210060510080c0c0a0f03020c0a260c0a080304 66
    0x8244031041c0524018080140d9240461056150071180501881d044800e5500c079150a0620040001c24010101c3c0220b10b040d030002103172868104d803a001d640d01655001510f0300c0e00b4409420310070716484d040d9281e0041a401205a0000c1d03402070004295540e912929207141a10180c110b0314040d4001081c000d08010801c1041e14261205500c26940b081104400c0103c840d820540034905882c5a001450700c40003248002140c61031000c190860060b08080d582d52100459040105aa403010158001e020040d408480c58000740c88001001c0c02c40d5043c48120181c2000091166001c00d114554032080a681c969040c0212006400003080c1841110318000115070504441c611110802491030041022211044121419000b002084504002c0c0c44d0400c0764403503001c41000c03000742c814040541076905203030f41c1e00781c02c40305480842141002c0852025020803010b14003256603014a2518804503640c030074800c0060103640004580380c1c0d04010580c201c000c803a20001c040240f00d5070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 888652958 1250 888651708 888651719
    0x5100501060507030302130503061f0807050315041b06080415052707052e08070c0609020d050f0607030c02011e110708040b18040e1c05040e010902030106090f 70
    0x202d074a000e50505d001640c0b94102c52a00c0d10500b419046254103002e20828091000580d40700c42d40e0289944c2000e6403019503c18074107540768098492140c2507008494130a42001850000c0341e44240071f0203140d40c0401500c4010000d0038100e07001140421614410700c01070089800b0903500f20051030000f003000e0b04000c540100c005803885060b040c448007000d01c103801d0f071800f401903000628019044550041c041885009240c909103807060310120100c5000e01c115100d0802f49025621549615580e2440340c2c4666028050000080e41c009031001e0702c0b50700203881000170302c0740b092404000c0d110302e0801000c02000c1d12101500c45085a040003003203510059845810520f44515240014075403e081070f8001c3c1a000300716000e0980e4070301160006041580000905002c1035525001e28180d000d08100070131601250104d11040d8071108070740b510103140d008079038140c403018141941000d0340d400c08151550744c04d8018008264003c00100b1203d5003107201e00000d40751029840580a0804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 888654208 1250 888652958 888652967
    0x3070303060e062d0d05030703141309020d020705060a060e1b12090703052b0c080a031e020c0a051006060816050f0a08060a050910050423070c0510050106 68
    0x302180c0e00d141320703021041d5421881c0741e25520074001c0080d10004082c010f80c1001d9840303801128041e40442c0030708030880750f2400e2020854240040d4022600c0946040c40d010000940211108041c1c0e80d0380bc02c0201d000c42c6041043e18896008094007142d854241154006030042c041c0810058440c40b051711202c070035600041c0d41a4003036030042c0d0800d83e541d0716485440c0440c42d510142c000c0c0126941d80c81d51307841641c0444195019020140c0b141c0746011021107000709480e40160135410f09214001820344a83c0001c2510000c000030031001014204118040385e200c0c0c0040d01c020341c0110749034810028288425011840d031b111041082619000f009001030200800d1120341a410030044400a8003500540782c05a100baa07403a51110f0b00c00c0e0024007040c900b5100c00d4420035211500181c41e141c0b8064840c410140c0b440c00002d120701d1b00043c0000351400351440c5400c003070b18198001d5800392002500e4880c03c19a40e4245501007039081c41401c14101c000030314241410080180b1139207400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 888655458 1250 888654208 888654229
    0x60905010f021801230403050304030c0806040f03081003021201060503060c07020a1502071211041d030405060d060e07210911060f0c1b010f03050f0c031f060203070303060e06 77
    0x5e080a070032950320070394940c0b031980c00c1c040c1c0c071203c2e4000440c3c00b100f03101d000006041501d101d41d100d06201526011400d175602c07801c0781c1c0200340541001e0380c100002e02c52001c160b00f00310508010144252242c0c0003503050b02550303100c080a40e64400c0200058a020011645c00048000d016440c0c80203e40120b08080b00900410040e4020241ca011303ca5208100790b100910440700c0e044010040e92400180210b8081442e900c65810044420240e110055080ca0707a14041c4d001149401d25003400d01843e5000b408006c440140d881000103a485d1124049a21407103046c1d0300c00d4060041400301390490049012a607858a01e004800c500148403011150050340301210a0390302c035130311001101168403c0c0507054185005a40f50015007156181d45880e602c48241c80d0110380740003070311048044683c1254038a1112250303001090001030136100640d0440c14001100207184401454040f22044960107c40141c0c40010030318241503051040b4009001700d9100c10300103003040700002c0c3c100e0341e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 888656708 1250 888655458 888655507
    0x120905150f070213020a0f0905030328020c0607110102060c04030f030c151b0905032a0a030c0807050a0f031101031a0a0b19020f12070c05040504060905010f02 70
    0x6890b00c01d5540b40c201503038003154051029035880810a070000d00c2d40282001c420080790080c60003044500d804800d070f42c61411000552060b03442c04085004008941c14407800550092500f03082944d11380b04018170041d0301038444410006401d030002131405074020011240101d0500043c80000e0700101421a41a010714010003881c9007400e2060038111040314043ca402e01d81400022801c11035000c120201c0b0840d29a500300c5039885040c10303100d0082c801c00102e8010000e0340f00740c840d88001e040000c000c00c01341070140c00750b48a5480c600b6007411504a6040b40d032105008002030310340b030103080d00604510a041c03c41c031440e507910303000b801c00640030171418140c480c6000816414000e00f0222070020090503440ca095a8131146445070717100095913001a0500e18104078110700000326002c9131a080c1000f002a011100d10a134580d8205800480c1e6107589601b0000320ba5407140580c0f4003e5002d80000142500e4a241c02c03400c440c41503202032910340c01801803018a8100c0030007040740c800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888657958 1250 888656708 888656737
    0xc03020d051321022b0b04050a05030c07210b0c070f1203020a02010506030f060f07020703051501170604120509041d0a14011b030207031106010312090515 68
    0x411210350008212425000710200010180310480100740f220300d40b10090303000741d9068800e050101503041c181041c800a40c4a80c165841800001600c0441ca107903010340290203803000f41100f41e5941d8116400141806560f03442490288030f40c0710441c5080c10940301502014108866541d245c80018000030504404c0102c0840c0f4941407180b10742d15001c001d40d0290014940119a5201074000e400100c01c4100540c640000a14035041c005951131603420820003d01e61551a51514071100400401d5101180a60f480010014004200300c0d01c001c0c415082c0014503604002065207521420b40c43d409607603001c40e040c04040703400002c1c00240d00e0703070740e140c615500c048110209020b0001c1c1409811484410390740380c841c49802003106001c3c11b2082c00080041d01104021030f081c0c506100d650724400071040305421045002c0d03030045c0601446800d10200b50038055101030b0034050244c0c0152400f4910a900c0080f195018840c50041e00040341c0071801e907020756058105030700407080e8000445 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 888659208 1250 888657958 888657967
    0x1061b020306220212010c0906050c030d050601050c030301031a0601021606030b1207030f1119090c1e08190c02060c07050a05060a090210030c05191e030603120c03020d05 75
    0x110b000f000a500540001e4945c0c80740110a402040b448041000103410312101280961240048900405180b030007542001d40307084015000782401f90580b41802401c0050400300f002c00d1000d14001c50192120480c0800e42920404004000400490454101e045924114001043d6913020f4503401d00d4006241180c0d18080b680085010120041c144200580003040082c88455010814494002c461151081c48180616120408142d04d005105130102784841d403484d82c01892491054600400c5503007940854640d5041043c00c8107000404c004100002e81c1c18a050781050401900000c00c0010300d0310f030000b901c0b40f80140040303280007000104901400010000c607128103812100b914034904100744090014015024121300640015944504450007440b524203202140e464092505c100251429107007044550404184880040b402c0405120540882c160700040d840001d05142507041161052400122600400545400820002c0d034003041d608021819801c040e600c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 888660458 1250 888659208 888659251
    0x7020d210519080403091805060310110f070201051e0c0f0304050102071206020c030f270d020d050a150e1506010c080c0319090504050f0705090f0a091401061b020306 73
    0x704140ea400400440415551004000c655238410380c01000110308840a94900c004035209807a100070103860482010b002612004170040010900680305241c035a03e0008841a4031040349079a616058a2210228201d1001402080080c80044480c8002d6040c2803401c00000d5550f405400344103a400c1c02640603004000c070300d80581d284058414244c0c3c1d203a590307400791038509812038034107011002400ba0300c0e0000020300e05550350f80860081d045641c50702040e001d10941c950349001c1143c5074030500091b600030401c42015528106070250380824010070840d6060710b41000980c299a43e543c4400900c05142e8000310f20040c0103034040c2040d03031540440c1100a08500035450030a0040c00c41c64a0b0103080c40e44440400d0540f901240c08000903240c800d18110060811038035040819410054102e041c900300200c9000580024460024191a80303041c40136070721600404034810b8100b0b80103021503034001c0303010040344480142d80315001c5038035000072f5a03070395014110b02c40c5c58807040f10a00c0c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 888661708 1250 888660458 888660467
    0xb0c18040606080601090e01030809060a0219030207062a29010305161e05040b0609061b0c0d030f0f030605030d02060405010c0e03100c030207020d210519080403 71
    0x58491005104120980d81da07070010b414540304507012400603d114801080c198030604800e8181c03600102c100d07080401910a01400ba840140d44005520404480501000c0600000d1500b07601c00c2d400303050000e1808101500e402441030400c41d450b003800707441e41d462011300b005180100d50800c00f0264400c0c000b414010840c0c03917056888100c044070f01d0011003030110008458041303491180d540880903076646602018a0f00140c01050a880340c110700f0045443d05800480500030b004108030718012110000541540c0507030880700704c040f01000c9181c1515400c0c002140c0c5000180c2e202c1b0718460340d60750300070605002c501106003807001d0382501240307542c030913030003040030b0300001d01100c40310031590704007a6031031008a408031001c0d030030035000607032580c802c0d803181d064024064000d0800c0c0307411142c0c00001c2e10062010b0400c1503424003240000da03440c1d0030b40328219400b03880b02d98009052981d0707282d00c840c44824904144541003140b030500034100c030303000c04400b01545048049502da9280444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 888662958 1250 888661708 888661747
    0x3030212070807020d140d0e0f010836011a010c080c100207110a05011407141501030804031a240f06031512060609010b0d11070b09060708040b0c 64
    0x940045003c5c21500c1046190449120414421401c0340c07003068503107104507250a41c4404003a04500341400102a650141070801c2d0014442e840c0243c0246a814801090f200ca25071201e038100c4a000010068100030b01c01e0400212540c25655900200c1000182003512103160042280350001446560054140903010408441040941d511142c1d42001e204100071a00f005105019a01c0002138030342c02802020452242c2242003410301e109619048600c4046c208104010300554642c000f45490740540f213070185219014498603030f411b60408610f04c040d11422003040d0000750003406a0800c1c1e6503130840880050380c0d00302c01648407450208902258048155410103c04000d1011510303c00c1c11540c0014402e45000200c0d000d901619039039800103440301900085408018419510310000074100b070b5040500114000310b10302e107401880d03404118261680d5880c5e00501c540c452081c004290000c0040c5800e40d45802d154a88038003900700a002c0680c0d03100006103405002c2c00045401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 888664208 1250 888662958 888662963
    0x1518060e13020f0f030718020c07030b0f0a0e0601140315150414011505071a090303040b01081c03020a020c0901090b121b0d0201110115090e0703030212070807 70
    0x4601d06003038142841d90404140200c1c40b41c4015404100a030501404c040072900e0000e0003004010b140448000503a003500d00c0740b0300999020007404981c18810806900190710820443c1c1480c41c0c0400c0b000c00d175103000341550020b136050030149200c204001481c1c43c1551a030280c0c1c180b24101c0c11b40000e00d0883d00d0b070306010302603100c0e41c10011100345100002c81c4604007610240b200149000c104040c24409000d11000c0c3e816800d40304150b0380c03141c0041c0811510400034035410900e00108010445000c8442d0003842d4800010401000315032501d203401031001500900200c0b8418400395070a115100091080541c081586844c680c4200102840c2003000780c001600c5507114012030b00681b110740c00c11409070388211540d020b42c020009038148000042404540b031143c0e46402c10040c40c0c00c000c4c0682c10003a51200000300c0100030701c65000403000841c05400324500d880034100988805d030f1202040d9400000042021940110305100303140550140140e0341d90316498440c030f160080d000d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 888665458 1250 888664208 888664229
    0x3150e06162a0b10030b1302010e04110301030b10120b04052b030f020d09030e040b010c0f0b0703110f0304033e210c2802040c14030702150a151806 65
    0x284003454999a1f0f001d80014000c0e610200c030a10700c0b60030720059410110450002400400042000c2061a84000d03004141c000c811192941d40e5050004856111101614180c62110620081040c100002003070854118505c01500307102c082c0f800380b000161080c25043c951038051b17041d001c0071580d044500c2111102c008000c00d14843c140100801600c80d170b00c0740210325141000c1c1e225070042882410044e0f00580000008500303648404210001910b080181510b85c54030492001218000c1c00f00d9180f030091064480c50b203805c00601600c200780a03070700b10014504424140c1d20091400320700d00500c2d1040003430b034070f40840085441c1450040001c6403a105002880200d00e00340f20080046a204c44200e50101030010340c2400e0400003155481c581003001580200142081d4102c20101d200c142070917040349120841c000e555600403110540141c0010b240c4d0044d0002005a00d90030241114081140840d001340b0b8143c10a440d0003040c4031206180c2c0b0740310500701180c00c044040c1c42c0040c00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 888666708 1250 888665458 888665461
    0x40905060d021c140706050d050108061005220908180a210c0b040603021b0c0310050603012003060120071a040308130f060507020a03150e06162a0b10030b 68
    0x1001f002c80d00900321510800d4100fa00000728450000fa4040c081c661020131014040c0c80d0108012161031249a03046c0072042005100007240c006110340c540a600900301c1c20358070724420104030340300e0400442c0940b01c0c1c07196040610021010300141180b468554039038000490140c02d11007084409503000001600340000d0104840d075054018040503007040f004001d8001100c015291260400d14113031340c041d0300000c02102a5880e40d0003054011101600010380c2c07403050460043c4640585101d4505410004144401940c0c08800180180a052000903405c0c203148075464031041c00c1c2c410480f8040e0100c181c070800c0815481158001c41d0b0005037242c0c1e5861948004da10065140718401199000280028015010f40c0031240710541c000c040c03030303a900d0131941c03030000e2895121004090107507180c9160049103010800140070742c0c04040040d0825242d040014543c04138480340e001c40740011710303d02c0e404005610402503000d900403050103150351502d0152400b881706520241c6807214010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 888667958 1250 888666708 888666719
    0xc0f08121909110f03030403081c1409060a050403030b040c030e070927021c0308010504110a051b011509060302040b0d020303120c0d0f0b120313090b130e03040905060d021c1407 78
    0x8405000302c8918031014010b07132245032f0600806940445403181d040e0460340008240396455031000c0d81c400e100e4200000d000c10f03136001107070480700c0102d00d00d000300303503115001c030280d190801c188002019000814407440c0216400071001c0031441003222251403640424600b150340340c40301d400340007110841000d440c41e06410001d020306030a20807140158605102d201101088104440300445581ca910385000005050525511202d20710712265560f07a014100f07808800520708001888800d00200b4440c2c2035004100c2201d448840051080010031070303100043c0c80210030354071400c0b90705540c40140e5946a0442c0d000b84240c041c840025480e082c15840c60315110752000260640c156403120414051090156413071140a5002234044038078142080f000b94140c00c5030b000601e001d4905c0360201c2c015086102074610741551304030184c00200e401c0c080c44c14581310b01584200101c0d1203591500740b036000b08004841401c0e01641c98294010070200380410300e400d51070100402400c44a5081d40e80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 888669064 1106 888667958 888667987
    0xe010605100513030b01080a05151528030f140d020c150f0c0304051207050607150902130209010f08010f05010c0f08121909110f0303040308 62
    0xd9201200181d500a85c0c01d000380200c00c01000c000500e45070180c01c120321802c1ca9a0800546420071060a00c00c203810251074106603840100c041e11101c0e5040d0306581040001d541c0b00c5510400010000d0f4081492803050007503070380e0502c085680c20540d495400b1700602e14016401b0542c0016207213031203111540e8000e01203c4082c0351504014595220703030050740c4403100c40c5d0000f1808000d0b900304407185800442240c03000d0030300e2a09000005801e170050503005090b10744002c44886404145501c90ba80e00c5400a001d00380300e40404030342030040d42c080704800340002d145002c030321085030291054a041c3c0345c8261a40110358182401101d40400c5e441d001e96044040308224000b007030300200100900c002a0407501201e1808140700d183c0040581094890b103480c00c01500e020801316100c00610350b004890064005140324006407660090f5003000d1f01034040010103011850b8030 = true := by decide +kernel

theorem cover : BRFrame.Cov 888489208 888669064 := by
  have h0 := BRFrame.cov_init 888489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 888489208 ≤ n) (h2 : n < 888669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
