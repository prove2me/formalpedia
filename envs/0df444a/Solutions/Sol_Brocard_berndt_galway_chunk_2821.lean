-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2821
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:50:29.821757+00:00
-- url     : https://prove2.me/submissions/86725c35-5783-405f-9863-25f5200ee2f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507194244 ≤ n < 507374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507195494 1250 507194244 507194287
    0x41202011409040f0e060f071b0f020a240c0213020a021906020306040608010b0a1412010c032012012709050c010806061204030c0602280f0203 63
    0x7445203407480c049502042520520b4541904282811424025100c55a10000c0404200019070b00140c03140c00302e200d800c01c02075403c0e400103403682c0380c002803440d0050043c5504500c02c110312400071640c3c1c0e0126a00d40d0781e5900050204800740d442d040302140d44102c0c403015041e180340c00401401d55130700099400d4003201010005d01c8d40490440040f90003000038080c1300200c1345408407444254036004010354400c46605002c1c5082000004904005014030b0003d000001c0c40fa4600311304080005505110301502564040e94a1b80019102031084c440d11513000c1e0695000b103900b4494400d0002146007803004610704203400c008046100003c012146c0c1540d80c0803030b1072040181c0c943c602c942c196240302c0d000c0b800e807850701c00070204200000541541140003a00ca440300b66171440200303e0035000c0d41d10701480c0700500300c00090000e849204a010310500c1200c0040c1000380310a0300c40c4424103c0700080600d044070181000160f40c01046540050f01544011481d200130b2100390206130351900b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507196744 1250 507195494 507195497
    0xc051507030605060c0d1103120f220b040303061d070f02030f0c070801150302030307320d0e062506061a040603110423010e03061906090204120201 65
    0x124046100340d03100340c004030700a100050001d42c03211203100c901612100c030b0810350008501107203490569110040191980c0b800701e881941d6072641c1d1401c20b00203074103004100010000501492030072001a881d00300c00028022440005146428580603046500c55080700c2c2d48061f681071012a0340d40d02450301c6500112501d80440d2595090070180d155000f4541c903503a034010080348240c0e0490000402c001115180c00003072228071016000350f00d45900b240070103501a0820424800032440400304e45003c0c1d42d035103004070404284501008504007286980b024650000c1692072022a813028080d20441d2003102c0183c03400c1821040300711280344440252030301302c80d440501014090141e04c0440208400c20031684035170f841e40481c1c04035900c180168000700e031800441e8040d8800b50000d940a40700c09600c451024844051100c4542060503291410011003010000a50728140585409820180b06001e034502e4a400700b00150741054101c482058414841048160703680c1902d454010780a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507197994 1250 507196744 507196783
    0x11a0702090a0207140304080a0501051305120a020705090a0905010509060906070e030304030b010e01060f1704020f12010c09080d0c1a18010c0c0215180906041508030a030c0c05 78
    0x26103001c80c17100c101443c10300060b020102d000121600089401400180700302c0c005c02442d03a03a84060440002901005800b5a200700c0c0008000c1c80395400070030040e803080c01100c1c1803990711800941c01400c100c500c6c0c146a03845601100401c002402900d4102245101030445403030000305e400c0d6607030001090441005690a189241500c091044602864010f002001c0c1c83d80c650102d82c098840030301c00c900001d01015004120383c0e109583d04140000421094052900c80da000c010395010a400c0465018003a5810b032043c4d14400d2041d864114030588690305054039040f241c0d070520003c48495000c1c0520b41c940b8100180344002e681401079004c3d801d0b40c17a03603160101d00034031104961520348a151306e80542d0002d816082070403580c1c50b41c800c0340c8161100e602240444024000d00282604034100078038550b8551508403041503214101420002d80e002c0c40884000d4042080e0f400480981c10000394152101d5250207115000d9900341414140b14807c1e41e9015540c042103281c0110482c0c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507199244 1250 507197994 507198007
    0x10c0b07091a030708090a082b090606030501150b0f030a0b030a03020c09060105190c020301020c0703230105093408030901090806061c0204020c06010e011a0702090a02 74
    0x500008014001242107803400107030b00300c040000380e8001c0e0342c60b8010401c0c40c000035862000004461010903880201142021a50716942e904941a000c0074a110890140010b059580e03601c82e101c0c0090142c2000f1a00900d18106142100c5910340d10048858000d14180036003025541190b40d198160283c0c19034980d18084240c000b4498544d85c180d2500502c059075052503400100481500402c8a0f2140c1588030000155581d02c00d0407480700d29001c1c810700481280e401401100040c0380054005803600102028035420149140c1040b03071f1815485905034046074050691900c4191050020070823401c1c00d0090350340e03600f0724410054000d040d80180e0344102c50341c0d000d00c031f01d40340210320322403075403610b40c0420364486d041800094001a540100020034500c0010300e603015880c090005040c80d428055010100120304209030f8005030204070084a41404100803802884481811012035041a50002c1d0a20a4629141c9089001c0c0842e01c056903501c2503098003c650160300594400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507200494 1250 507199244 507199247
    0x71d010f09140d0204240b070c0618080f100e070503070e0a06030c0e09011401210501061d0103050d03020c030d0203060f13020306190f052709030706050106030209010c0b07 76
    0x607a1080c029086410b040100d850010307034248080c80506c00c915010300d196110b10110501d802840000b60220002d0b03582040903a00401c4d030b43c91100411214542d0380c0e07031545d403d68509284042e112007141e000c0382c041c1a103681c4600c1141301050142d40901000c0340380c000065620905030151100c4030b406540840e4202c00075501c02d60086901107003000707105a03101c0d40b8843c0c099088511019950800139142c00b003070882182541a030b1000101011001c0050700d082d5041107900408540e01d6603150700206814114032294124007038841c40c041c2c030a42c1103261807818010703070750044014140180f0070099100408400d0310480c8d00c2042e401600c9544400c00180310041c50400990800700b00180d190410400381c00032b6108050a81d1400d01110101c10308802c8502c10303125024254580c0304080c0004d01c1c01101c00322180d65584c904020209003c2d405440d20700050310b03d114a40e000248250801406024580c0109100e0804600b00304400001800c01c00040310010101000300002a8805 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507201744 1250 507200494 507200509
    0x110601051005033706290a050d2a020307030e0607020f040507031d0a0305090f0d0209070c020112060602030a0f11150103051b0607060905011103071d010f0914 70
    0x44e5591244800044041c00c030310f034510301a40095003050030404045006285201c801c0c14007910403a0f1031815840038603680e155600000801c0040040c00c202e00c000014081c060724010304552071100c088140380d44000342285200901600641d0414001300c00441d800c201840e950340c0e000d0f90002d98400c400d100003182110071507003242d4003e10344030a1190040d41a401030f1102c84800350900103004a8154850b41d940d481c280040004008004000d4242040e81904052880261100c01104501e40c00151a4001154441d001940150705141990303440030b000e03d0341400080b410400c041c1400c400a41700d03c135801810060000b05192110014412041912001d14400030b540c0301a5440550700003081080c842515603210310010a151002030600e51380007148010b219900d49076003540d0f00b1000d80305a0f082950507569698501e462908210003d40c403d8186a5900c00462800030b403091403441c0380c0107898101309000807074021580c4c001c0b0740d00c029200840b05002d0702500010025462 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507202994 1250 507201744 507201781
    0x913020d12140c0114090c0f0f0607140a1a01051e0307030b0108011508010c02031204050102041203030e0d020c0604120501020c01060b12010b0a0504150318110111060105100503 78
    0x40c0b500041d1049100c0041d4017661841d00310111139001038651400c029602c100c254003295001480c02603003000c61900c90020300208a02070801ca09210180c0c80b04100e0300d50380601100d6a4000651480030040c4246a046080348106203052895040001084411221001903100760b1198a044210382d0307400c2041e40019580040d9081c015a11021303098040c00a0a1040700c10f2048908003058044060140015012007a030056052540174115400c0b0391001503c00e990656082001041c0e62807006c1241d8aaa0b000351000300d032030078004114500c0d181c00c05ca4007200319000030003d41455030780c0f03008440c2155580c4415a201d060302d803c00900a100d0a44013204540c640340c4002012591100900044040c4000003429681d940c40031840c14440d5503030000001344104000e008080c0c03039001c8010044414580040d159001501000c185120540309442d41100c0000344c00d095a408449001044510b03000361145500d03240c04034000700000c035185400d10a002c00020340c411701c07080f0007009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507204244 1250 507202994 507203027
    0x8130503030a050915072105091009020607290f061f1106010314010501150210090c050907080a0f02040501021e0c06210703020a02030a0e01030f14060913020d12 71
    0x1590b040611010b0039901e01c03007000010b42d4403034900c0c211a1f80c503a40300710340c4107050781d60213420510903410460005106665049070f2140c028003484000c514480031080c3c005004001c6981411170800c0f000d00f5501001300150308502182042054580311b6000a0350b004007451100313001801c2451f01a038000d0080140b87c030b0648150320002080c001001e0100310422007150080210f070342ca0b40d06412015414445040160303101c0e02d00d5980b14101c0d9801400f5850003030b90f001348110340303500005603005000e031003c40003e1061010300c8901e5a03a881482c81c8140c0310401145054588070020307455170140d108400707a4581e400c041010b0110240001c054503400181901c1c1e039040c40b5000c402c07603041141610392005005d440003401c11fa0091088449101d8190011814001c00410032917000050118050400d0340711a0b06800000075402110600c00300b4802c16080c43c0703080c0781070000d450801441c0441ca0b62003200c00201588450b00c03484c100b0b0b904031410004105c3c40082c2030f80c6200f200000c821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507205494 1250 507204244 507204283
    0x10f060f0e150a030504060c08010312110a080406051c0204050a0504020d0207050102070b0f06010215043302040303030506030601030c050d05070b0d0501150e1e040e03070305090108130503030a0509 87
    0x11030f1960640c03056101c0c510800d010003210880020071140b100742408010300020207902d0f0710312030314010ba04040800c240c030400c4400124059a07202000d810580c885000f02c1d00100d80d00c1d003480c490015043c0100740b025811130810346048005080f007140341c89010700465000031003800380002a011a05281d800c0b000a42d5144940c0c0303401c41e04078504407031003201c00ea02900420000d40c808110000001c03410712041d041610396031100c0c50035404424040b407103104401030002d00061041c101a002d0091000b00580721869428003805079440189401e11941000e001400054429106c0c1400d842c07007070741c000381c1a130401d14040b0303e000f00b030f038000700005580401c00703580100307580c1c0003a0b05171200e5602803420601c0002003519903e50b134800c22540410180700041050b4011207007440480402400030424904003500705096510006090313002600000c1c0110280d60060017098100700e40400001060f1501d4803840d4403800081d00d041c1d2600c0e15500801c07034030307203003003141c00510303800c01c0b8148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507206744 1250 507205494 507205507
    0x50408031905010b0a121b0f020f07120f050a05010213091a101b0c0b0a03060605030c121302120718020f0301090504020d0524010f060f0e15 62
    0x1180250400c90300c40a20802021614464090a01420b4100c0b90038803481414202080020703501100e00e11a0581c42c2035961140301e240c2c80040c400c0004010075512030b00295442200003e04144440810302d80552042d030302044204041d841041034641c2002c0f030300c0300941140c40d16078140781c62200c0c040c0c52580049801c0340c1841c1059021000c03203036134032010400c1d00c400700202625103160429203035002407100d2880b030400d401001910420f24000752903011084040ea0350340402601500300025401011448010560301445020003074170a506000d03046207030100c08000380d44940c030304064111003082c02158038048284031a40316954001c00c50390108400200c000c0e960801d5100d94400c039801030785070015981e06c41c421038407035008410300c2524582c2007040320b034090000500105e80000803440070501040003800000380e0014000c1e11403600c001a902149942241a001070000d0031641104100041d004040d10040c0078090900b040380391000b031b000800245d50405201680c2d42d001892 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507207994 1250 507206744 507206753
    0x50f0102040518010305150a0b0a060804020f0415030609051218044d0a110609031c0b010c020a08030426031e0d021602010806040e060703090f060504 66
    0x282050303450075200503c4100400c801c004407181c2c00e10020f01280c001c2c805d00104000b942c00c16a0f0310410040000c42c0202d20708001c40d1142400c0d902a100062100003407104514bc0082000194034045034180400319a005060841d80300d240310041c22595102340302400c1090900402030b031307820310724030494070346500f00814541220a40b0031144524980105107841070292642e03080e1280111001c0702c9481607100047c807503c140b110003000c0680b0100c0c00c14840e040340c0f40c000c152501c1269205000b220134034007101e141200280c03214407d90802e01c06c181041d08850320040c10140300c46000b14000420900607500c0351040c00e030194224228000c0413811000010007001140c0c000070041480c110013903607108142d000c00d05481d21540041103000180000b011912980011403030400d03180207203400200080740c0c0100e16040d503000700c880116084d03603081203000d0f5100c1c2003940c040c440e401180300a9901c40340c00610010600d40e49400d83c00078000f82c0300c2d40c0120320b90702003000c00090500307052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507209244 1250 507207994 507207997
    0x1e040c0302030610140f01020102120103062304020d0b1806040308101e030201030b01180305070f1e152001050609130530070b0103020118030528050f0102 68
    0x903030003881040080b4500e030310b90303104d10821120030000090451901404009059407030007441411507400f4000001800100d80c10140294420306000418000b0400c905040b51103070350030401c130040000d080001580300d09280d0071746294041c90b030702001c0e95040000704030740301c1c13046c84180369108170303801c100c01c150b0401011f9010300140c002000000d6070700d6221235811b50361402d9503048003290740030810055003e42c0145010343c0c414140342c2c0c420303a600f1006141580d0664015203040d4004802001080100040203000c4d020180b030686010390003440d00a010101440f4400780b0030881c480703114a40e440384d0151001202d01a0851901c03c02c0551202d0180000740c42c42c1d80b0803c00c0d140030030341100c3c600d0a440d051a507c800544541d8011507854003045900300325403290092003c400c100110042401024268070031501a1050350440c000144581c802940a058580700c212007800813500000f00c2000c02c00c0b01140c56510040500d8545081c1e01e0030b610700800c00d00c80c0c0c084100d400c0e4010340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507210494 1250 507209244 507209249
    0xb1e04020f310f031502030417160b01050a0b16020310180605060612011502011107060203100e1909060b03010501061707080123030717100605060708040506031e040c 73
    0x41a000c4110f403640410400319010348001446900440000c602c06004c58000d50340c45400780c04020b070100810004070401c6c2c3d00841c00e114000b01880341070420801e6109540e400b4103000e5a240e8075990401c0960120b900c10800510460b40045c000c1400310761b000c2200440c62800144c0600a0070300e4441070402840c00b4490072141517081000040c041d08062060745c041e204d0245460050340d19001d010141f091120500100715501ca2502001c0302c0f10300001803108911130a40180c0c2c0b443d1801d40301902107141c0d040481c11000440500c9448551100795a0007080b0030f1600142881c190701c0c1c42401041e02c0b0386d40c160507500b4000001141d42e04820050089029000701294640d00c036107048521000901460038444003100c201600c80c00000409011800c000e021034510a440e030300340c1c03840c1e090348012009080d80001262030090201b4020f1000078501074501d076040920075a5042030500460149500600d80440000c990301c0b4200c18108126207803011402042c28181003400362080e860 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507211744 1250 507210494 507210577
    0x140c010603021509031e0604081b0604240c02120a1809090507090c1e1b11150c0c0613030b040803180a170901090f0b0307030b1e04020f 60
    0x114002e5000d45031200361881301b110000140885550715554000d15800c518200c015a0b81d64007000c4808141c1007221a001d41d00503c0c80000485903021041051603841c42030580b254209450001c52a03000190b081200020400040e261038914004403814400320081e05030a14061034009407100b813681c4411010b6002d14140c4d42001e4031079090b4000c0e00c042c48034250000e2080200d081e03884c464580342058010725850509903600d21054002501d0204900503a106801c04640f60900d1503d0b08044020040042d00031341007100380b040345916500d01241c5180030f404002120b41740700040c0218400079541c000c814001c41d0901d4200f220564000b00c81140c8a5500d0314640c400e043c00015160320130a42c42180407003828400f08202005400c50100181800007800e40403549214044502001d480b25014060722450b050380c0080942d803030304441d24048e842d8803110880c5403000701400044040c06480243c0e03a50030015812805116007040c1c016601101000c500e814080c280c2c0c408000c1c200f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507212994 1250 507211744 507211753
    0x20d022d061602060606070305030126160816030201050714030f1201031b14130b0301090f0b0a020a090e0c0d090f0c05040501080705120a020d03080f07050a140c01060302150903 78
    0xc0c17000340b2440c1d22031040090085a01031004203d0613841d0000c1d00d880340400700c00050191803030f802492500080c020104400346651800380440c2500304011556040c44280600e03042e46950006400740c0300d0000c024003c0f0310079a40a4809580810440e031282c480d00020980d2007082c82c80035443c501080c001110b00c501000c5500c050a008010b41005440c900001d01e6a005c0301300c0d040001009542c40700d8400c2c40d80f2195005600d51b030a00c80c04a200d03004802c2e00041000c42c0c94480701401c8010302c02c140715441802aa560399034441d00742c074181c83e082d02e000703c4641c40b005006480c60160344104044035050014000c1080b40e44e12032411407521403d03844501d00c1e1144200f20656109026035846039100f080200001d1500910200710404510140d0b096210075801080f603140c011344065010529013414048a0302034428415444034075445c10758145a9280802810252140303207841c1700706030114042251490a500c00707002182d00502c00d41400015541c9c0e0381c2250410103405200e40074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507214244 1250 507212994 507213001
    0x5030406090602060709051e04021815070515040c030b0a021c0905060604110706020307020703150c08060d03170a0b01030c080c04060c050f0a03021507020d022d06160206 75
    0x500c5a005e02c42c0d070384425014600b03000c18030a42c01c0c41c00c3c41001643c02c0030040404a038031144000c20a43c804030f40c10103005400001401400c0c408242c0c060700c055000c00180b4003050004c40c5040400490040381002515075091552800000d90405404402c0480900c1050b2040740c0c000c090b41110699030000741540d1640007401c07100244000b801035040180003d0701d03840c0c03681c40010034051035034440703080c0b0748103841f214201d8008807910801b5034016903003407081c031890402035101a45140c0040c071000384151030050005001802d03030350082e0743c000e400a00b014050440c50000c006160110b200c9842c04000140c082c00c40784990310302180c0340690030040107101d1040c4601c0f03030300701d250b41a140a00e0401c00719004809014150790038010712043d421180800d0000c205010702947c000c0074011b0182c00010354501000e0503840940d440404000d51164020514010205070070f800c0300998081510050340483c50408840ca15001d148104900c51100d6084020054042c1d400c9a0090b80e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507215494 1250 507214244 507214247
    0xe1e0307020d030302090411120402030c060c0307080912010c0e0a0801060f0509060604050a0b03042009060415091e060605091513150305090d050a171012050304060906 74
    0x114016020350440c41082d489004280290000c20400a01800c006090501e440741040f058000160010001c2a140305000a500d03080007174000041040b40c0f4075240c5004028141ea4038810f1740c1e0014012400400d8035181c998507060b03c072019941000003801440008039009120f408000d181c6841703190304407008100074905200d6003040d02c2c19110f2036540c2c2c80c10081084080d90f001040d00794406000c100100b82900c1e0400004000c040b041c0d0303c1070701c0742414985260203664060ba00f0b00c0e810781c021040040750399503400e01604200300f618000b8200045284059026000b40c0008041d40d0030030080ca4042588100703110001c00b11200704010240c0c84031b0040301c0a1140c2d05106a000480b60301040481c1440c0004144160960202d0940715907180048141641c503200300b4400700360b6440030003000c03c5041c02400703107014040c9800c600d40601c0d003034003030b0901c2da00c120701120b100000800601a440c1c003444020181c90307820f1180c0da401d4824a8400c0d40ca0307010340140d0300040c980d14000609107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507216744 1250 507215494 507215497
    0xc090b2206020c010c170c0f060a0c05090a050f0a0312050c0610033201140108011404031407020d020a081e01180b0c0d061401032d15090e1e03 63
    0xc0c0145e5410041801544070340d01120000031000d91540d100700300a1440100421007020401e0a85015001c01c1c9810700101080701c00119004044c40420040b2807032700d503280102d0005a41040382c0c01c90501e540d00b4042039901c825504024604605c13090380c020107a400c14042c14464032600101c1c0c0140e9115442c03203803001d610b41300040001c40d03035015000000d20400c148038079516146890f00244510044918290f5540a96075510004140010712440900780100b46c0342e80740c07000446806040c150780c014100d0a001490002010f0003049a804541d541e03150400f2140d002070004100d10f4864140b1500d420045140c0030b00c410012459a0ba400e5041c000c68008000c034584407030040c0c0e0301e91507485110304010050485440c0401550030342c05483e104040c0074080400300246407141b018000b400b12501c4501c9030078982c3c0e041c90315039144031800b401d01100c42950440818420000303509981d0052598000b070048030b0600324111240040010701201032082003441c031074041817a001c001e03140d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507217994 1250 507216744 507216763
    0x15060c0c04181a060a080f0c040c0e03070f050a081f1e090b1017060c0708070c1215020406200c030d08010e0f010b0d0c090b220602 58
    0x1940c00000100c1800e18040d031108482926003928031000103031941d5042c2039400d8603410503101620080030302c090307400c0c0740880101410780d0100500150b5010290142d0701e4490014181c0314585403400c8080f058406c02e486580030b030001d0200c6081c1034403181c2c030018030642c5000f030b1400340080030380000b1703020070002d0305100203400d400c2d149660350340200301240900311310385042405650f25202100ca0300014410744084c0c9000c0c011007442800c05600c030ba02ca04101c2d42c0000510400380c05c801c0d8400d400410300315080450703491115501c0c251490f00c1d01075801011809000d0070105d00300000e008410045c64464644564a8285501008583c000490007140140c00009030b80b13201d41c1544a40180c440c01c46101000c0c1114143c1c6010700020f840c2a070074000c91400a004c0c40300400c40e40307001c0056250403d8011841414540c102440d0240d14090220200c01c0151200e4080524500031000720010b000e41c40e80d003541c3c0d044850300381d50f480c1441800c803100308075038010700158061012560804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507219244 1250 507217994 507218017
    0x30e100905030a050c0f240a1b0501050403021b150904060e0f010609060203040b120a091221110703050304031206121b05090c25050c1c0506010608070c0203070b031506 74
    0x1f0081012003e4254036080300c10351100713122030340d40c4500d41e413240300e650464002d10034800429103141500c0e0090800810080c000c0c1a81c4001e0003008a6980d03603419007591110141c0341507141e05da650b000074003800301a405040c1e4200c10400b84550508100c103405d05032241031316501c1320f0ba82c0d581402c0381d491107684144081c003001481311481c4a03500882140d00240401c802283d060602e444041081030501c0002e40400c040152144200003d102400221650300b00104026000788249000078813034500c0007000c01c10004006030415000f01c02c25052016421700c200000703501d40c00c120000b0b0038036090655440c0c03180c10503043c40b00c041c400410b0039110040c1200819031101060b4201039004003850002120100c00744ca1101d51002d000503001e40e01440043c25215031503401d01a0000c0c584d03c4c1407101d03148401c0c80788041003001074901e04449151070b10b040325544100381120100c9030000002d50501814200260a08071000a54010019140440d100030355002c00c004461045009904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507220494 1250 507219244 507219289
    0x1409100b0f1f091a040b090409060c02010c090902040e0106030203070c0b011d010b161412120f0105030304080c010f0908060a06090c020f0712080f07051501090504030e100905030a050c0f 82
    0x109564891000c7c007001d80f00940040740740301d0256a19410742d0308941c40040181e546080d500d01c13040d0f01c048400e00501502e50214945800c01014000d031860500510003070580000c0843c90103846a50a0341c880ca8003e22250460350f115110b601c0440100e4000c01c10882503240041968042c0d64202d522618040d03540051441c250740e504041030342c203880e40d05428022600141d00c001012001003004041111400f0380518004524121403030041e0000c600992050009002d108400141050024001d00b003040380c8842d104000c90f403500700381d04580d106001d044240b10144126401010a41e64408414406030145190890303075688482100320f090341c03099204018201c2c074989041c0040b40548080c0b440c0c442d144920202d6903115020850721503100e80720a0405094107800e90307016003541c10050000b42003545000b050709040301c200b144a512010011074006000300075081c001e0102038140c0300307040d001c1d0401580341c00c07005102c14018440100540664580f84804150b031454140304e4030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507221744 1250 507220494 507220499
    0x30b030a0b0604060b040b3a1107060609051006080903091909020a0c050613021f0306240e0607020907050c010f060e04061409100b0f1f091a04 63
    0x45840ca140034259a40090340c0d1080420641d041c0300051016204581f66990340350741c44480104a10300c14903212404200311080ca4035031a00b04904017951201c1c0d18000304841c0500341c0202114841d01c14010007082c50803a00103030100940e0840c40c1309000401c030b085d418546e03508060b24000801c0f1100015071f001003033801460b00d404400c10200081083c2d00702013280e02d5901c42c104a174820742e69107000c60890107125040280400c950755001d4121000d440f500da00c580d02049c401c1011103040c0c40c880c5298035001c06002d05c26480350b001400c2c0300c0429110700c242d48142600a07401d012890000403904a50440517041070421141c00c1075000e00308408942c0d44c440c04580541054070740c0742c6c2075525002e00829064550048001901c440c801500840c03c1070b02e800b80480d01d4081508541c204810300700502c0080200c0c0c030103580c08030ac03003003c6004640c52002502c0414000d801940c0030389840c05049941076000b0248821100649407488010746504910803a0191112184601c81d001c000030b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507222994 1250 507221744 507221753
    0x51005011206030f051507030c050d022b0203150409021813120f11010912030e070905040503070c050d080304230607031a0a0e0a0c0c0813080d030b030a 67
    0x40c440c1c90141000e00040e065182d9a40102c800c07000181951a0350000c3c061030307001c803040a851a00442c05081c02c100034101e1031000781a07402912130200b0525400b15412600d484040c2090344880c1c1032115100240b401380c0c1a0070300075042911381c030a0612460081c041c413820716101d180c41c07541e0001d192042030310004180524941005205010b400c00b820440301c0007a0490141e200d0a030b040b61510113900701d20910040080e40d0321038040d003840e070525031881c2c00720389030880180f8000d520740b030041081044540d1081c602040395000d10b10305440c213801c1005002010015090652151601415155513041003003d0300c0303079a680c0a030030050200301150004a10340260303d000c110b001c19003503070100c6071010b103400c0200840c0d03220082610352605c40f08200742d100d4810318003a011501e80e01030604180311014098001881d180ca440e03500d544129003140a11040c06036154080c500c0c2c2d654065040158030b10007158411a6003034803503403001c002c40c1402401382c403078090390280c000c0c81114901c1d2035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507224244 1250 507222994 507223007
    0x30506180304150e030606090411040515060c100b0103021e0c0106030209150901080d02100b0f0a120b010f050f0409060e070603060501090509090607050a1206060905120105100501 79
    0x1084040ca1004002c00940f24121241c1c5401c1d401090715a1039034001c60b0410316003417582c02007400d40f16211480800c0700241c10031100d03000c0c0c04801e03503000441d5a190080e54024035120200183e010201064604003544001560010401e00c00801d000c00707a5010f00660503409220465001240361141d1a01c3c2007010340098010b00da010760021680c541e40307401280441d14155890400e100c006000a01c0a0400d07500042c014010a401480b000038402d038000c1d1501c8121740e10301a900e8032030f001c480303943d590b110442c030680f280181a00581d9070b98903407180800707000f1881216540004000080d1072000005550304a0b00c002e420302070341c44021410480100300508080302e8280d03a82c0d00769130020400708502d9011301401d4400194141c20070001500c060000c0c0d0243e48200f50140070441c60080114260b80c022400d814003d41ba103020b24001d9070814018807000300340358648080042e9640e440060503089400640e100c20100c0c2c4203019a0b401d88104883c520364441c2074410402031540b00702c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507225494 1250 507224244 507224281
    0x1b01050a050a02030d0c080916080303151801120b0907030305070b060103090c170c03160e0c040909050304090e0c010212030705091807031b023309011b030204030506 73
    0x41a21700e04a1881d41034401c03108002000c000042d2000c003080b01d6a1000c00c90b05942c00708071000c642501380f070021401e1307482c031008103445d940059200190045071111464495141c11520044001d5a15801d00c203000643c4030310306940d40810315011890702e09000c2198402c1c1d9415035203262400c00262618008180301800e100c0c10140c1e2119441c000c00d0710001c2e1403001d030142410039401545503e440510f4013403041d002034403036000310807400000702402c1c4401088540c80107003805d060340c4040c00844035004940c0700300d03641c504103400401003040c040300078019140452820464041c1c2d0300802c40d6510700400010780075a000703d070800b00940c94a00910380c8408203291451803d141200401c0354031540301074030080303590714005200c601601409000c1c01e0542c0342010141480341c1d00e1009685403030b809080d60f0188405540c241c01090710000d90300102d0318520540a40d410500a218020130001910240741d0907001c0c030515100340719008840460390420000c6c4440e0f00c90842c000c92400d40030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507226744 1250 507225494 507225497
    0x150905040203070e30010b0f0d0201030e03160507120818030709090804080607140406120b042d0c090e0924010e0a060b040306090609021c051b01050a050a 68
    0x40000d16045d60f031348400a24429914610a032142001c001c0300c084400c5003513001c104607418841c034801140c513a08041c19454074101ca5121075040700d4001078004006802c00d2a040c1e00002595803038010002c0011a0240e200d1412548050742d81c0a0081112003000d40c02004804c08000f41c4809804008904501d040d00034203030303002141c3d503001280450320702030000c40e454032010400308850b0009004403580110316050061181c00c4c0c001d0a00e81a10907401544184145034446003500d45a43c0d00075289550b015108002c001c401d02504140c20144001240c801c00041342c00c4403034580e035800348007a1042c00d500d441200c0341c00c1c0492030401200082048120344500d55100d8200ca902d400c48442484603c0d40d40350003075061030030000107501c006094604141c142901006041c0c402e400f1541280d0300700200150303141c5d852a00d00041c02980a02a52000442102c0d9072040503c1c40364612481c0300303a0440315040e044200e2a41074584903041a8086881888208006400f0354003c0414502c203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507227994 1250 507226744 507226757
    0xf08010911061e041502060f040320240a0506030a021e15031513271e11040c0809060615040b030f06010906080610050f090a090b01020715090504020307 67
    0x400705001c1903900140d20103d01d00c0f4003003010301761003a01440400c4d000082030070302c80c000d032419480c040c00800c40510701641c8e110842c06c203065118030601c0400c2c0301c40c0b400a0b03081545000c9440e001d402000a5560028140c035200c013040d490b180000741c41700742a07400303009040fa0310b600114400113090290001e42d040502c0e44240c441416944000b18401c2841c40b110916098070031003807040b44a0031a401c40d10192030070414401c100d50700c9803110b2018408015100004586281c024001d0f00a100e45c002d2040d150140402001419000b071020b856040d10b00700140c0d050390000b104d1007a403e0b070f45404c442d04058003041007400d025102e1581c81c3d0031902d0b41c0b454035545407003c4a066004481c0c21002d944210140300040d0b0f030149009009029610340000c107030800c0e02c002558460404010b009116000501c024a071028005440d03034030030001c0540c4d400315562001c000c0038084440e40746005001d050b070b020610312910071244140440300d640ea0181c850030300341808000d40c4050804c1c1d040c00030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507229244 1250 507227994 507228037
    0x9050315010b090a1a030a271704030501090b070239010e2706010c0803060910120b04171905070302010605040c020a020a062a08070501020708040f0801091106 70
    0x5000080007401700b003203002903920300c0e000404204560b050030002c0d0404580c3c0010304902503400e07442c1c41480f03030040c0d0284c4c0e100c0c1e13244e40090524803d0f03130720092155003004e03015420b021110035503030310a039015025a562840c440a036940c0c00c201824a0032400450f070f03c1a03c14250703003005400f4001d1418100740f002c2d0f41014000410031000140c1d8001d60f4041001c10000245c81e014036650056000c1c200f80001e041c1c15944d210450000402945c0225003400001e00f40a41c48034281c40107100c5003200c000340c00308900b02950750007022901940c8a40c0042650200e034401541100c64200d400c00c1c03054942003c91804071a1940031850a504541d291940403c130b956440c442c038040f4a44030340003440000454814440c165080b90f1020003801100c001e03a8901c40c4c6107008000c150704840e00c0b902d8100426103062080c41c016100050005c2d84046507041c10403003000c00400940d000000ca0103403456842060700d003070320040e1000074001122407a4144403420800d010704800c40c0e140c00d00489040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507230494 1250 507229244 507229259
    0x1503030c11040e0703051b0906011b0813090506030c06030f251e17011e030b0703020309150910020c150c030709090905060402060309070f0306020a09050315010b090a 73
    0x32110441c4804941013660300b0003c2100404c05445608002510f0702c0e4111005c00008082e048010050b50501c170f03001c1446203800c5070101034845840d40c40303012262101221123161491522134060b000e0b00702d1404000c5002d601d400518650400c6004103000d00c1d5030703500301c4803490302403025041012703217800e0408103107401c0c2540305001202e051507038030140c0100003c8020021030743c5811240c2c0034050748204000303c60b1400d249540c1074415100464001c000420040508900729910292603510040144868994507400a60040c1d44a0b400c650802200e030201c40f040880c29030b2411a00d500130030790f0b00d07580300c095009000d04520040613a0811085000600c80c0880c003150400b0444800000300444c3c26000048000504001401000050031175598256500e4000e000a44920030200001d020300e0070411092018006c800d4103031007495501c0c030304100a500710102071000308184100228541c100050501d010721295111100703103910b03041042e40582d014144090b08482c0c84413000c101c80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507231744 1250 507230494 507230501
    0x30a0c03110109050f1e1915090506040b030127021c1d031e07140705180c0313030203040503030714010c030c0f0f0e09130b0a1503030c1104 62
    0x55000704000786000d40d4000004140c03440c1c680295100b4480d2202124698440107048601d510407000d50005804c0d01200040c103002e140841503043c40321190000c0b0b03405202c1b080c42114955144c8030708100a403034604202484c0500d01801d1402003007400100003603c6410540303802000c1c00e00d40d0904400300c0b07174403c1060341d03c0149030780ba5400190041070185e944a2060b05052007071900001d0501840306090354070b0b48101001050480105106402001c4800040b02c00d803030b511801030084911000c0c00c0944600c090b100f20f9103e00540c0001c65107400b03c0d00c0c04c65200e1465400e1231407644c2d442c10100c03c11000740316800d0b021803000b4400070803241c0703081004040590151301a020324640040703610b429103148202400c2010304040050707a61a401490711301880c0c1031400c18420000e0420030440762106141001544400740405015000920b50032179031065000e460403800310303a0340d0040c850a03a11500c100603040c50304084100003180c4203104000181c0d120701c20041e10440088005020b6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507232994 1250 507231744 507231749
    0x2a0c060e010b010f0906050a030b0406090606020f0d0801030f020d03180f050a090b0907080a11070803070305060a030c05040c1b05031c06062c040c090501030c05070f060b030a0c 78
    0x41c0e5441503081d18540e00f15511100440c07903440c1600c80b00b8201040140a801040c8a031002d050701c1d160380800c1a5140d4110f880a0304124404004882c0c3d02c4900039900d40c00b00c02146100d018000041c98107034800c0c0c80082c141d80d0080354020481100e5401d0041d5607000e40d06c203508202c0c01c0144400351030f1001d031030304000f454290b00c01d108513801c2008101c01c50035558002000c0a01d017801c030440948030307080c009070700040d22700b03101a80796202d0403040003909048000070f01c503440008102c010010b004d0050f500520013a42c080049a80b804148100300030030f0b0101a12003ca10802000700746020341100043c01d2203480c00040e0300c06802d882c6600c09154010880300c0d900702007902d80590758019070f03119901e030050b1403d1084504d0500301800d000c450b8042441d182444004540c10560a10461011903001520400c0304000c0790307070020304501c118042c0d540040c2c14403109951143c8120701341d580d500d400098003c10418240c0d5030030002c160801100d42c16001d0302001202055441010100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507234244 1250 507232994 507233021
    0x60123040c2105010305100915020a0c030e0f0901094109070e0403050f09130b090610050f160b01240305090a02090c0d0204030f05102a0c06 62
    0x1042c668014400a54080c0c2c0a5401801c51500d80104007180c400941b0100120344520b0004001c256402c010644143c803840030440c00c1d000291045815500691030721a060103642ea0481c140c480d441000482e2442c000d00d160700040d2080140031402542c0c0c000740800c40d611101d8440016100442c2940d04540142c0d40e044010301c0410300343c51030200342a564810407000181580506103110030030506005030025041113030200d5407508050183d0200ca030121001080d0341395455084c4180c5024001409003e4051711070340c000720380141080e4401c840f28a51a40f42e940c100480e0400241c1583c001c80810204a10310300880310201e426140c60501070322250035650304000c410700020030003103000390f409800c040c42d1a01300300c9087c00c04250075903100d038110340c1c00000b41c41d0303085602814060094072621051000400000300403140f000791202c01e12031015110740e4450311035810215005c00c0b054418440e00360045c0c22645803a040d00a4107a42542803000315400c07075888020495010303069420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507235494 1250 507234244 507234257
    0x609090f19090b06130b0108070f023a020111040302130906020309060a0c02060f0402210f15010b04300f080702040b03060c040b09010e10030b130203040203060123040c 74
    0x8a54201031710086641110700d2402d00415128000081504ea00202100b007002258000ca03c20356100340081500110440d1440b0350408207101c081184009030102000c45506881146925074010300903140d03881404600e04e41414a1074090080340d106226a22002e255221140350016955102450084240c1401080e107450001010001c880c0070503200429988403504100740030340317905d0320f041c1d00c29070544e0389441101ca9403a00c00341c041c00074425181c0d280548803000001030400a520310070109924180c010590383d40c140d0419030700c504e007c1c144458400c410b6521410392842091c91080b116102d01002e00c001641340d95100440c8200200c2d01c4030f60000b115001d40c0b80c03502030780090040442c060016410000f031320298030f104500c1040e420060100b20444980c0c01520340100700b030006031450310440c0390304000800616030540441d1190f592680c024a800c1214801d40340300e00e50190041032140d080c55441e007140b50849038400700295140740c4200d079940765402400d180c08a140c41d040d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507236744 1250 507235494 507235501
    0xb06040302131d0a0b071215080d0f080c090d1406040602130b090d02010f022103090712030225030f05010c020c0319020d0c0816140609090f19090b 65
    0x148100314201074a03c01c81e8480010000800c0c5010480394200f440c41c140110400340c1c51020401078183d0080c282c041c400c2c15200010008030100f0308141045142d52182000c0002c29420740320004140c80c80c1d88900f100b0f00090b007041c1804030b404c40c0b203240546242c40180c030035001032034036080c0c040700c04441031900072a15145c0d2845c44420710f4050009000400d0600380e8403004140d52500381c0101038104001d0307034034030441607009201601c0d03800c10071180540d0b07024601c00028a1540143c448882e148945c440000341081d0351a45e003090300e58590302600030102c0a650101541d01081d43c40304141140d8100003000500780c68070741010a100c0c2002003855456031002904010503140c680d4043e4100c0715100d6078202d4405840301c074903079040312040c20342900d03030500302c1c011511900800c80b40c0c400c580c00340c00e6200c850341c0a18129404101c1d0306040710741901c1402941c3c041c00300400d0b04034400300c010038482505002e800e903000c642400c1180c40d0020700c1105106030307441e0520640f10000f100050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507237994 1250 507236744 507236771
    0x1080109021806030d08042d05060f09030a0c060b4b060d020702090c0322080414150a03060801050a0204080c060a0c1a1603060605030601030b0604030213 68
    0x42030b0a10440d26400c2c11518280d004261110303500c040d058100800400018200b2042c5545100c4809040000300d45103c242080310303040c1900103034143c405100315400105180c05001c80e0901c1803500101450400e440e440064031001c061178811121a40c8400710786525403501b10a01d0b03050003902203e109540301f819464404403c0340c0c84141e80c0042c115045881030100c070b1740441003034030042c0e030300070f694200700d01400000307001e001c40095000d07110f41c1c14030148a00003000366005200301024001c44071203104a140c07403d03200c803030010070304041403000708010001e846045e66480c50182009807840c808411580c0140d00c09030081c008281c1d2180144499a82441103652191162904600d0141451301c0556a11035030840340344119800118900f00521031003808518580c4040780980c01274541c01940c1c00c001046403540c40310900100700f076440a1080c02000c00326842903c41e1490342d02c5410044029095003404550842010440000140c0300d4018800484079003050001c1c142000307440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507239244 1250 507237994 507238009
    0x20d080c0a0c150e0901061d0a1409010803215103030d111b030307031a0d020405060d0b090d08010b0403170304020f060a1d040e060f06180108010902 66
    0x228404003c0c41d407544d89a00d4480703024031410740da050f0a01c101c48000003c0410256080e021219400075110740001800248496075004015002c850707120940c0e80307a00d0410398902800390014904410a101e01c908203040c0e011036608100c0000c10600103000110051043e46c0703160b8810411000100d020070481e4000b04c0c1c415080d103a4440ca111424041240060354a025078165804510382d9500303140d040b050818212000f204060325600d91400c02003134401d03240d1f04116070560200c1c0c02c1000041030342c268014540b0850350010b204a4000b81c95400348070042c0303001401544c2000d0180d641c200860100f0321030500c602540c200811940e1281c040c0140038100c10307402421407038000c0c04140009040503940601c5400f4940c0c900d40ca0760b0300c074000121010381d0300000a03042100002c00003083c6a01502c10002491114a1080c80710545030030320007200c840c01c80300b0351150800d501054000d48410040f81c0c0008009045950060a1500e0182000000c0c1c0c060032150b07540e800c5c104114104086e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507240494 1250 507239244 507239279
    0x708060f03010b0a091a09130501380a0933120b09010603020406061205010b0418050618070f170f0c16080406030207020406050301020403030903020d080c0a0c 70
    0x10000d02c011040f100c08203241418500803c1d8115131284100302820074000004200110010580c0459003400e20fa0645d0010034290103035119401c101d418000400c50544611072055030062040c84003011100120315103849242a40e4800c036800b10000310792100c0d00a840300c0030701200025800d020410355000a25444a0059192288c0d011007041120050300c1c07010211070304018405490f6945580c601e006200300e400003076020f494100e012031401c0c1d00c0244c1b80c4007800101400c01560362901601125030165226000340044201184290601150130141c0c000c80007814010b150070880c0007040704490100e46810000d00d2013a50f000039a43e01800c03583d940701601e1b2240c0514240031010007000701004180d810303034000015101d46401501d005600302c9a4018200c0c80d00d0340e0300c44000070069401180c0991040381028404107940c5418800c40b0110b070b07415114a0704007882c0d81d080c00310a1500f804190b603d407201b4040f12035600310a01036441c502e40b040c803282d0315041c2492601c200010144 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507241744 1250 507240494 507240499
    0x6040b0c06060f1c0507030c23120309100c0f0809090c28020c0a03110301060519030b070c0803010f03031134090e0304090e03030403082403060708060f 67
    0x10240100781c0e40b204050405410f90a464404c1c2c0c210031030078601d2500c0002e91004088100c2c0410004101c0031a44004420f00101000ca60000c01359100700500f1241850955205410401c1064050326140d0550005500ca07070402e4100c400701030b2a10220340001c03280907107416038009034074942c510300841c0b080c0c1d00a840351107485c203010440d10100c0d4a00f81c40340600c00b100e000348000343d20103802008448003255005280110440d22032802042c1b410340c0c1c8511a00070b600b040d0020581d403a080041080c8030107800c0165840d80c3c5152100c00d0304c002c003d4588010b10018000141c042450480158081e0902560200da01031031443c0c01444072040c0302006045802a0104204c00924803a124544030340e204001b501400668060303107a014026404805810b250542c004101c6001101410032141e203010304204a8403540c4407a91a4402203070000c001410200002e5064a190f0f4107142c20030000d014054a0640b0ba100801d14100064070b5200c0418559002c0090914004008280d11f0209 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507242994 1250 507241744 507241759
    0x70c060c0803061c050610030201110703170f090a230607020d0f0303110711190b030a090c090203070522050a17010905150f010e0f04021e06040b0c0606 67
    0xc58544002500000e03140307602c561620450448028011600c002042c0e40220543c0c1d00f6041c1402c05660450440c030003280412207507005020050360114100045a421120f4841f4141030340c0c81f1404550300c48032409811340010f01030800036458000042015144903c2c818a031119069200700c619101d80445034446d5504112040c0140c843c1003031158059070116824020b11020718040c0c016001d1100c21210030540400e024091080d40d0b85540a0780c1e07020b507544601140d101e41d554401c0b5500d0b00400c400c4070403c2022440f0801d0f00d5000f00040707800b45412541c80d43d201c0c0315600c00d992060b5400000607801085031040c444580341300a031a01c15256600c20014a072002042200780d05200b050b0b0022844092032524040030b40001644030350150655441c603001046030a070100068607100380150000c800450101c49c2440010b000c1c03246c0b40c0004034070384c3d41d0750300b00b1190380c2c5141c079580e9110303004094409184c1c0300c0401400203000c1c184641c0d902d03455000f0b40c403454500c0040c40141b140c2c42 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507244244 1250 507242994 507243017
    0x3051204031a01060f050306011205090709053108090613140406230613030b01030b07020a0308040b0c130e2e170708100f0f0902090606030717040602070c06 69
    0xb0017030281c00111446041c440d440356a5440166000341c040e0381e4544c8254245001c0086c03800d07010030441c00303440142c401003206442d044008210090b485495917002c0d00b101e003040c0c10700300c2808401c05049208074034040c6850700702400715040e80c00148e2001b1900400f58000c2c0308100031500c841e1070140007600c0400c00c013450440d401008502a24101810340c0711900c0d586110307180c0d0811294400300346d00780090070135904d281c0945070300800d200689500b465080400d003111b20200700140d0307850b091355030000f15460b2503c3e440008000030b400403000c1c000800080010444441450b0010030500504a20f20704c1c02c1c41e082103140848540002c4014004042c0c0000910a000b4a4050701c658550b401c9030600110000380c0b814245821001c4030384143c41000e01c0c1402203030001c0e01e072907461010a100380d600e14001072080d5050382c800258000162400640682042005507138005458a402c205848610b4400401e5910940d03017991050b400041c06000d101c1449142402080141b812000e9580c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507245494 1250 507244244 507244247
    0x6162f1e030a0605060a031407051018030b070509090f01050306070c150518030316030f05060f040b0a0909081b19030f020a0602030106080901320603010603051204031a0106 76
    0x1c2c01c1c02801042c0590f54808100c241d141c0b4090400916440b45d1241c64402480c0011540c540c014450b242c4102405500d0311011485200d120020b82c124201044080341144c1d2a20300c91302e00104050200074051180310940c1d542d0604a034041d07042589241002e5042000b818100f20000301040103206a100000c80081d044840111111118440000311601c801018400405000c04541802c0c071001c014480d1004142d960080d040140d51402c00c001d82e9010b10080944504881c803030303072084400b071051603070b404c0c983c011400c0c1500061103190b00c01d40b600b084404440b5404015100c070980412030018200e084101415090006002000b495590707480c211003080740e850006040184a440c0580441e0082012040587d07104006540b2580c4641c0010700c24a001c9407604803070340c01c4c00c6507202c03801c10312a000d0111656400006088050b100c03115000501c024050035050b658030f80300000480d100788035030000a0860405180e440d031441c10b040c803d21403504040105621440010845d86 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507246744 1250 507245494 507245503
    0x2120f092109120a120203030702010506010c030e19080303150f0414010501140408060c070302100905102d091a090703120225080f0102070206162f1e03 67
    0x420b0200c03680e215044050081c2d6007411040030000b024a400c07480e401e40907540101c0036502c00c502d158000c000c00c0e5541401110020074585000e004200d00440012182c20521203141c495000d0f00013003500c8a0707648c0301151460f40126000f004c1c4070340203d800562460000340500980c501203c06001015628569421182040c0f01e003905100449a1059610055105460060041b42c09981551812050321503159110b800100d0050055480b1f0007991482e83c4038007804640c00900801041403014a05001041d000f9915420300380e050135010304008940070041603000020030701185030142450140c1c0c0d10baa030000070500500498003008004400000c0c10320840e030304905042d00b540c003050016400c081c1103010003003981e0400f011070543d806451401400b120400c030b044804032901c0c0007456080307000e1214002d501507001c1001c01d85000300c1d2105152034500800203280c0c0039031660114420b078802951203046c1d1800a040d941d0381898610044101402c004800c2c0341359001e2040000e49a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507247994 1250 507246744 507246757
    0xe07150216180209011107060f0e1002060f0618010f03030e031f020f091207180605010c02060a0201230915040206190e12030304060c1b0b040602120f0921 68
    0x9043e80401d203a00b990303108003140d10501e142c07003081d40d4000da00c030480104400c0407030900001050a02010700c95508007001940b4044d022903000d4a800c5c0c5914071440d94000018205c2d5070f1103182c040f00044121990843d183c000c1118042e030103c031510b03524000c0c00401040015134842d401183c5460100c1c203104c0d000344980c80306280c00507a40c24004c842007001d801905055500101c0d270758082c54600e03000040c5c40c01030300c0d00c00807440b40e24030740041c0b8002907980070300038a40010001c0c556000141170901c003a2047c444c3c0d80c0008100d4000c3c0c05400a0780f10744694032000c502c842001400100c070001d1041a2110001c1d224500303503454a1f0b004152103100342081014095200c440722071100d40b0604202c440410000c0c0101c84d405071503080c083d56038105940c00c4d40d10501c1d011a20058034050b00b41c805046040d00040398002000e621049813000c4024410780c0d03065000c000c1d40d500242c0031295a4412101d10319840e185040c4000c1c254a40900c6a00e03441c0f0008820920381020110b10090304e90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507249244 1250 507247994 507248039
    0xd030c030c03050d11070203010b091303080a0f1b0f08011a03040c0b0a030903031a10110709020304030504140301061a0a02120304030c03020d0f08011403010e07150216 74
    0x1841c950340c541100c25100c0c001400e03078654501444003c51480e44001440c4180c0210001c1c03211070b4490301040042c00303040e207005c800c4800109400703000170300a1104942c007a11003100000c4030a1200c21110070b882005c20b03004500340050302183c00309900002c90b0306001100e403405003255811310f20904c0f00302e070b14204030030301002020000074100442c030407086010b00b000401e01521000b402101401401e2110022004030381440001005403050408150910b40010146d20b00340c014040c043d100f8441b07000b101c840030b0180281c0483e1041050000398000c0340303e030340d0310341d0354501e0064850710480d0001310141c03080e414000304200490940e00c58180f0800640c10065075201c400c0030591928081c070052601d440d1010007044245600b001c0c0d606499806034003039920b02c881403041103c91401d100c0f50100401e80b00c00040c8070200b0001145000b03110701400000e00d041e4041c650314034001c1d244d07104c40c4480e0445800c220070039a040c44040f10201d058040b4201690130546604559000301e9000d05 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507250494 1250 507249244 507249257
    0x2f0d080c04050105160515061311070b041b0602030a03140f01090c030b03100b0a0503070803190e031606090f1d06010c0b190b120a110a151205060d030c03 68
    0x2440f061715400c1e0800515841000c5030010380c210f560341c0303205460449503039201c1e00c1840c00c40381c040c16072806854002102c0c0e0340c00c5172804945641c0d1144420003d0010b881d0100b4001110000c0c1010f240b900380030308881e80045460b03080703849005054440e80007124031120701c6031003405151040340c101341c1d040d079020a44c0410100510401140100091184039516206208800d481502d03c2d82c011801c840098030042c20540c0c07a60309155461100c0d10840f103c039841004080c00402291100c0c10080c401c9282a100110300c5c200041d01d020710340541ca5120010810040100703076044140200100300540c1d910505c2c0d89009001010890b90030482942c825a940000780181c0c85081c0e084100395204951400b03500300b00c4148080d0003141e04c066a0101c3c03804085815600c2e0682400d02c0c45040f0300000c0000e00d03403664079240d0340f81c480034443d03411144030a008500a5a001814106c08685660328880c1c1c541e040c00780700070b0301c0300038000c50701a4559850301c6011030340c0000803004080d05404e015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507251744 1250 507250494 507250507
    0x1c0b0604051c1b06030b0a05030102070804210c0e092808070c351504020415051c03180b0a1407050304090903021b1e012f0d080c04050105 61
    0x800300c104020040c40d00325940390f102042098241c0c1c005c0c81110b1050302c003080c40343d0f00c8100b07140c00c0340300e0400701400042c4203020410181c0540c4903a4502140340c010340e071049109550b0b031254240d0040e00400001a085810000000c100b000308000103046101c1c80641c80540010b462803c12201c00080c1a513900010f06000340042d1142c000e000b0045034058550381c12010514074025240c2c03a500b24001c8034018524108810009107811381c1c0d003054405030109490b01e60030800240002d0b01c1c0e50110b81c4080b440003810365100c2e03486c0b4050400d480b148000110b10303032400502c050030b01d82c071003c0b00d610004418004e80741c041003a1103e841c803c1c1040000061495082c82c450701a04500604074440041e010900d64410740150000350b12076021143e2907210b1401c291032401e190580240c0045440b04000f12009498540c110b800304107050803c1c09888012007400300320300c2c5001c40000058602c8106000031820000ea42903c01d00c0e00e001d48507414800305400c0e03640b05512070107040045c00300d0350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507252994 1250 507251744 507251753
    0xf100b0a14130f0e0f0906070c02011205101d15010e0312040906060e04021603050306041410051011030a0305180604120e10090e15061c0b0604051c 65
    0x2251212001071542c40314840c1d42e001003155140c02400303081c0f081016000454606190990344501403809071000d40450b41d40c2c0392080740c000c220090b081e410040b040c1000100f0356080d12806016103040200070b8070480c01d1148052000b40040f109540f802001402c000000210855106103050709207040310303030b442d00c1c100006c1c60701260340e1003a8046500024001056800e590000f02283c020ba19086806031002d030810040703010f001c030001440b21402c2e4600000a1141004540c0054000c2000803e280300d040e2400300d080302141c00c40c4000004402c14001072424150700c0220f481d06282014400012001c0591240074540f2601c041c152140c001c10340034407010140c0f02070f039420312045940924160403d82402d400142c1501d001c00c04418160010382003901c155114560591aa501d5551408414510580c0002e0581492060309000d001180c0da816008002041c0a020812a0945000b0480040300e8090000b280315880421007000a615034100e40d04400001380315000c02d80a075401d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507254244 1250 507252994 507252997
    0x1e0d0c060209040204170c09010909050c01030545010902150d1103042906062a0d0f021b10050304050c0901080f070f030b0c070501060b0d02030f100b0a14 68
    0x8440c0d26034801c03541121b405200054003249a9500b1980c0c4805666102174410440d4403498014010750005480c110880d4003d403c43e98000300c6120b060404031111220790302c102104040070740c0a440c0d0f00715812040d95600c00c0124030707118000000f00112907081d0300141c8802c043c0b22514002d1b03100412503d0301e80c8101e900c00300341040d6001650b1b90b60319103850100130f05040707031080050322400b02040d100082d12034002244a5400600036615100340c4109580803041c1481c04a1104440141040200e0405202c00c02041d400c6840300701030040c0302c400103410f0200b0f100c0341d0804107011040180c15903986e004180c0320b62819007440f50703498945060041c2864842d01140b60441040c10000a411200042c0072400000c44410750390042d8481c0002c450100c1c1911010b003821200300041100c081108004200310380c41a0000222590b40f540140340c0380d080358924005450b808000c01003ca4500400701c1d0340a0701041c003c034030440c145030711600c0703d010700030000042200c24109140850340c400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507255494 1250 507254244 507254249
    0x6010620150103030e1e10050714101d061b0d090f0c05010f0201020f04060f0c060504060b090618011806050904060504050c0109060c151103091e0d0c060209040204 72
    0x6490007101d40e12070034081c0c40b0031002c0c040310740608014006043c80c000380102d071601c614001064151005d0f28540d0855254000380c500342d4640034070504400c11502c042003540002c4201c01c0f00030640c40c00141000140c07142048602c6950382104d002c10400400d14230702e0800791400e2504085e15a20b1641e0402c004010464006180c0d240c4488801d00b841041107000b0700300c0d10241c0c1c03000c03140103103448100d00340c1c05241da0b01441d0070000d10080c4200c130301691507501d0070981490806554074207500c5201c00d0b65010b860945da290307528184200642030282c0410351192050718102041848000c840788800f1052040300d0040d0420001c3d80300654641c0c10903801810010b220001d01d0802c6d0505400610042c2c400315440c0c030075030301c1d0500154014400071089400a03110b0741ca28940907116032220702d620b1000903d107603a41d24001c0c1c145c120020003a50060001380001e1011a035000072130800c41c19503500c01003259204160300d06945034031507a0804e02d568480300240c1c03606041d4001c98060b02464 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507256744 1250 507255494 507255523
    0xa0309031b05010f15050d0f050c060a0914010f1709012d0506010e0306071b0602190e12120d02131503110a080105190305250806010620 60
    0x224641030510205402c07604d07031081c10700c00810425060050103450700b80e940c4211504144a00c5441c0c01003190402c000c1c00302c500600c16942e0416100c0c00007400f07603112501000100d003280005004100c030000402c0c0540c0b60030700345074109a6045601501507280002e84103411030050340041c030990000e4001074001c580005c14514104c180c10301c14524500001800e015042c60940080c02d50b6219136401c00001101402500e030700d07260040d04541c2c581d8180605801341030384060010000b245032000340b41880b21100d058005804c0c8400c01000710200046143c4a1130042daa156030104001c5940b4240e03405201c411966000c11310082400381c046c1d40420220542a0040080e41304200400c0101449043d40c2c1040072544042600e20a400348894110004000074018042402c041c05440c030075224040585160941c0c0790b07035180c64141c2c01c40b56a2110304100e890300401624000c0f00c1d802400e9040003a220341c0d0306110008003400b0715424a540d501f080c1ca04002c01c07524080c003140040500d0f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507257994 1250 507256744 507256787
    0x1505030402091f0807060809210307020c06071a150f041a120114010609060e060d0b131b03050906150a090e2a010f050c010b0303071109100b0a030903 66
    0xc4d0703400a501c4100d24414000414032500014070400800300d10481c0547d068100c088041c02080c2c0d5007035903500018001d5055100721001000e41c7c1e513841025246251060005102c00019403068480b8104040e20f00c1c29850401020f00027079586180e0200c100c040c058034000f80102101003000ca1018103007599031742110207408415070011064102556010307903940320111903681d400d0112030801c4a8461080003455100f40e846040c0b8103200202a0100828404108130003904009014944410245110340343d640500d100084041c0a24800605160808004500c0e010700300d0742d11450028801d040d5808090386040d170503514824910b003d02000342e81000003032242c0c01a180c3c1d40040c00c1c40250034619801d420b000703025100900d410300d0441a9104045510000340513591030b00111a0032485540b224403a200300d46003000905985030040300307548041d03d03491083c400480c201030100301800c0d0500300c00b88440b10b22481110000046881c00140100441c1812a01d039201004140100e000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507259244 1250 507257994 507257999
    0x1d01120b030124030b010501020307050a03031a040c0305010905070c15020708120f0f0123210d0509120102070b0103030f050702090f160509030d03020c01020d060b040305071505030402091f 83
    0x90f4200c02c0c2070742d109020f01d518598a400040e81d803401003080c001c2095004010050005e4800c4d0099800d04800041700b04550118100003801e0302c0398507000c180003a41c0c410042000c1100b80c0030340c540150303842c20580c0380b000c43e43d01d803410070807140c00c0703403821103500054000c08109044c0704840c0090508d020000c49800d1501884030646401d81d0121840040c4c00e0000c900505c2940c00382d4030507040f10f035030381e19152101014007151150450415100b42ca1144040740f00490600c010a15090b1550b01c032507035000c244080203c0942c000d00f440100340e00c1444804001b81c4683c141a054a0701401c0c04d02c03014a00d1030040341e162082c01d01c0203410a0000c030a1103803243e040325075940122255440c2c5586001030f1f0720b040f0b03618000c0305078940d4168440034030001c17903c2c00381e0300400c1c5080c0c201d800035140007401c000b4401540d00990008a0444000078100103015043c01200702a06440445030b1580d044100003e14600000c7d2005c0d00c500107500115082c0c501303082d00142c048204079100902c055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507260494 1250 507259244 507259301
    0xa090e16170c040b0313020d14070504020f090108190f0c031a030d0c0c03051501060e0306061e0406150509030f0102030f0118090b01150e040608030a0c080c16061d01120b0301 77
    0x4249c0043c01064440d40401154910b011b000b42c0f00b2180400ca5064140349101d40119008500a030004222480300344840381c0350320300c0340120200c400070b00c8000f04400c041007100608941403000141c441a90600f078120540d54042403810440010b4544011100250b0401b07200c544030399803006245100301c0440400c0400e8220190741218841d0300d0783d1303544070307100d505150b2540400c68039194481104c80d0107024008606540c000c9130400030300b0014000d91605001c098480d000b0410707401155011404885a1070104804a5141c00d40c600035030550810310001130322010103018110b4660700180707210380281002e82c0a0104590042052103d40d60360f0080e0500c0500d000e200d60000030000b42d500682d908041c011541160003407c01140b4201c803841e401c41d800082c00d101101d10340d0040007421100b1004002205841c0142115480802d00c0c0600243c135400740d0303140345d900c4014940d0501402c1da070003584102e0744510401001c11050f010a000030700421200845c030b400c00d40540c00180091 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507261744 1250 507260494 507260513
    0x703080409241e120b010e09010f020d06050319030e1c080a030618090f020f12151009061401180b0a0806090603030313080a090e16170c040b0313020d 66
    0x1a010b07803c0d0705094072203c0c000b040e02001c0401400c001c0d80c07000100329007540983c0d5264810500000011846440f5070054141e03840307090161100f540b21101441030b45030500884846808180c4500480d102956015100c0005503000074811603525044415100862807110b10351641300d8615507481c120200040c005144070b004000241468103100b40d51103030940700c1c045009401000c001c8440005508001c1c44c01d2002c10290341010380d02965441e84442081701800030000c0300d000002a00d402044c511941070316512440c0740c9401c0800c00c00c21040001703072850606030286810400e0740c412020071582d103505580401103400000915410303003075100320580d01517042260304c13543c2030301c81c00300305070b40c0740002c1d94206014001c40c41f8201c0003c0322840103064990040c10050010340d6194803250907841e0441d2115044043c444109140c9070744410380074088030003040b1070100c600307000c002503809020f5801014180100000400d0b04000240e1000d4803542d8014006686001986045002c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507262994 1250 507261744 507261779
    0x403021f080714040b090f030a150506010504060f12061503020c0106052418041b02060f0709120501020c0d020d080112081e16080912070308040924 65
    0x3407100e4081400180316a5000621410400c00d15041c2418a041c181055000c4101103910072410204890661028444001c0103401004984015100541c00704c00b65540105000c0c1001010401403006580190390400940e0745860000030200780202e10710000e020a4210300300d46010050140e0b5010780c1500140340d0549140e000780125991101807001000010400700d9002003d00800b88000d6800009400351590380800d0062001c0800e0101d021540c1103209011841c02d202e0203820b080b50104086a08480030454101003841d041a00070f0500b141c60003403c001d40c1504801c0e0091140c25016104080c44000c2642d16900d084800a551500d0400e16000403070101c0700000b4103190312420b84002560440d03229443c6c44100c4c0c07405032141004401e0039016000c280202c07440d0030300003581c0812441c8603040e0700e80d50720000d03810844803045001562200fa40300240500006545c401a00c08440f021803001c80c4641c881d50701c440703000d560030011804854009000143c4001c010811020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507264244 1250 507262994 507262997
    0x803070c1b1404151a0d0e0c010305060904020d0b0702010204090e0c010f170103060b0402040b0a170a09020d061814060a0515060a0e030102090a080a21020d0e060403021f 75
    0x20ba030000d41c414841079401a40c2403a85011151030b0030007042c0c600f1444070b00400b40700e10b002072904692903c44422148007002180300781c0d00803144500156007501c1480c1c2c01c150100d6034400140780650000f0010b4040a4000344500000070100302418000d405440103070000c04000e20042d006010400e07035405041762103074006040302c91070094060003110307519510601c40442280c1a800c40d02c4550262000100780c9412075400c000000d90400d2090282442ca10385684804007140584843d4101c140003603c03580410303151400f644010313981c1c20070303004840368490741c0421072400e4460300b4000400c2c985009000d221015090140504c408990684505d0140404000646482d085041242e42c50208183c10140030081c040c8543d0040c051000703140d20090025140542c0324001c1581d019050340715100b580c0c0500c40f01001c00c110f0f82201000340e502101301348a4200420002560b608103442000103015101c50444031f55202c0004032005150050140c01c420489846410313000c140e1118000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507265494 1250 507264244 507264269
    0x209030d0305040b040305030c1905090a0f12030e0607060501030506090f010603030f210c03090b0606030705090d0503070206030f07020d0c03020618010b0307030b04020a0f080a0803070c1b 83
    0x855900034482d50703000701d4016040000d079aa550ba029182036101401c040320100c0c060082c42c003848820031088900703003940d0761181d4a400c070310814400311750701c1604011109102c4600500c03030502d07480450a007040e01484c000002d42c070b0907004100f0303e100e08280900020b04120010003808000203070603010740300c1807013190200c4030101c40e082c1c00c807525400000c00141e0341c003031920107413031140140c500240c0b103c040c0500c1ca00881c001040480d003501c1d0109000c281c50ba00702c20284900140c01036404541614401d00e94500614028500d01c81c8662084c480d2564500420a108040003500d10076540607208e141c0c1c1f81840c000e441040030080700c5040051042c0030303910a141c2d115000007422154180c00038203042c2c540c029803142c0b107154044020195980c0e180e410010b581c0411001005600800c90300b0941e0900f070040c40401800303900814180320751410b00304014000025000700c10f54001421a86135203a0b2141250700c240c1150300034100300c03c0d4021b0307501c0d106001419007080780e001308582c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507266744 1250 507265494 507265513
    0x70b0a39020a3203030c06091c0e060306190b030a0203041101050a020a0602031506190e01090305210f070506010501111f09080415030608120c1b22020903 68
    0x2030728596046411101400448103c0780c0c031810980440203840a801403e42e400d04601280507403030620b085075010b0f1554400340081e818414441941c1540701c40601c0c0c80c41518a664010800e9031201510b95809058110300e03c80e0142402444480600384000c1640d81e40d0510803070000c00380d00107860644002a241624400d01d60107102253b1071100c2c19005003150044e81d41b038140c000c1d000145400043c0c401d101c0d00c1604d5586004c000d14180507012400703400d41c119240300800c81c100031042c6030306010420320144040740000030012408198113500744141130568100c908680140301d64842c0075000482c1d000e04200021600364169039003aa10400000002445a0303954041d00d6a048090981e000c102c4030720307404a0300510030041c000c900d01c600d402d0703448042c90103100c0c1480b241c0300006c2d07540e44c080c0644102401a101c621910b50700842c00c11195080850b29030062002180c66a80d90403081051074541048003515880d00010203a10004200e0201c0040e5000010840c800d0141c603e60 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507267994 1250 507266744 507266759
    0x50f0604030f0306033504061d04090c09091104021801020c04020906160203030903061306060b0a081f18060608061503040201120b061603080702070b0a39020a 70
    0x46a0891b42c221000651070220001d443c11400c500c1c04017141070340c0d1a1602000e940140340b00410041c40540d840c00500b400b0046007400382900344280d030b44602c0c03d18030880081801c080289050b200051400140c11800349070100880f8001700105801c94004500c210010503004243e02641d02c081e000d60300c0f068000c0007003000724802c0c404a107074042e1052041d240054640c1255010b040d10203401c59180c0000c1100203480d241c1c0c2202e00c000d1500070000c0060401c10540a803c0040c5840c0d0728041c100854040d0160a540006000407481c02a0321a640380c14602450350700e009010a04420103a05004e940721000740c695030146501280002010642c03504000ca440c0d5805c05c20a4035280c03c6803101d038011500740d55240e07000700905840b02c003004602d65489006004000342e0301d002644046007850043c010a02c010144820b5401c013080401424018108a503502c51540c5000c8001440307107000710001305034801d2010803035540070010f40340d10801302c068509000d0084900d00d00c001e03900c112 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507269244 1250 507267994 507268001
    0x5090609060115020a0615080f010b03030904022809080115030f110303071a2e05010f0908030f031506130b09040f0e0c04051008060c0c0a050f0604030f03 68
    0x80e9401194803507801008021561000a11605110b1040d141c2c0c409040d1100c4003940c0b0194000b20480780c401b4002c1101a000704001c101e0007100030300030320003440c0403000179880740203c07010903000d141c0010f143c00c18020031204180380d488074281801d6024816120061440145024040042d8a0300d124a10a1000031300204d0841c0d40c481038000325000305c1d907502482c1d1858015000d416100a2204c80006003a0300c1030500c0301401c056440c43c0c10b1600e551b040100740303400380e40c8650700010344007a0040801940f008405581c0c0a003000e088101041c8000c4680104c03036404190a03010200b61598043c0c403550040d80140003210301c5800c1001400c1c200285403040b80603450340c039921302c4010402c804101c0e000c0c1520b40c000034000520031400c80c0c1d00d10150703250b103003031036002c1d4002074200d040910b0144a0580c0000020040c1800503051440b5a5520300e0050541c0000c1200402c140c4200c100c104072800850b54010140c0705211510034200d5901c0d10b0070349084011070311488032091403c3c4a0310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507270494 1250 507269244 507269251
    0x60207120c1b26010e030d0c02061005011706030f0a03031d0f0312070c02220f02090604090515120a05060106021605041d071d0a110306010503070201021908040204050906 75
    0x400082001034400c3c01c510a414181900c100e03540320a4000795021050000d8034a01c10b01c410302140c0c289009400038103100004209240030800103a09001d543d9000e64601d5042021b02c0c10814203440d0f1100280c030780781d401c2c18902c0c414413031b0310b240e82c0402d541a046169140440902203c25216407502603454442101c0c0380440d640c41031202420f1500c081310070f00d03000710640c100184040003035008520003065050366014100f510380f52448400c00b442c8240041c3e0381d00000c046003070590020001d41315118900c50b0f143c0c2161104e01145201c6c0c0701090f50300180d80001c158888a1711101500d507113a00c000d20040d40d49011300000020464000f00d6064a00341542191011541c200420440208101211207240700d10f640c240d442d400e0020025500130300444040c02c2180341030b15104d0052240024800350240303050100070b07800040c0c1c190582c2e820040c00d082c01922550346034800c80c0280500402000000c217409000d00300306030031000d00c1d80a50b0007581c0901180d690048255034440055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507271744 1250 507270494 507270509
    0x120405091302150a1b1211010b06041208042301231b030c060403051b0f06072003030406022701021c050d060f14031b0d060207120c1b 59
    0x4903d0191aa810400500c00250f050500c1c07150300e02410748540c8554400081200c1d242c20607103800903c240c004c0030214240318014020b01c840c8030802c0105d00f480c01544161246140f808544504220b82c48040d9805842c01c44032006507a0f601440b10506494103001141c04101e106000f80c040080b0700000311a0050b540b80c1003442c7c00e8600001001d03200d01040910b07603e00040c050714404540501c407080c0600d02a680310358072a441172440030040007071103c04064540c01072042c0d981411000c103000e5405280d504003250b280000d01c082c50f40d00300c4034601007016808000100400c20003954003500300d211146100c070b4440900c0d555070300020902d01003440e0244c0d100b000884646145103420700050315240c64580d06042c2c1401483c015100180c1188400c40040c8109001c030b20358000800070843d40490042200b0100320329102d0343c0340c1e004043ca500443d01078140000b407260361303011605c8603903200403a4140d02e0280f9800400c042e0503104200d4900c3c444401090100880d40012402d50382e40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507272994 1250 507271744 507271759
    0x519030803101205061b1c0b03070302120109110612060d020411040305010902030f2116080313150c120e070e0f09101e020a0908120405091302 63
    0x255211015103400c01060100e58401405000c184a20f00c000d003188454450401000c144c20312002500306e10b091001a0b064000e02800008031040c80d030f1000c01d0b541094800001200b000100c0444d0030010580c00280d000325100420340f6010784150b01c000102d80c010644014442b141c0401c000161244110007401c9405141c04241c840c6000001c503926188002c00000320f000c0c200d00746038440d4100ba44180c0d02a5907440200c0f05508040c0990781000304000c0c050b0021011101148030008040054803980f84030200f02c00da28030800340081c8140342d0704030f00d0305600c0c3c0c5807551a92480042a032022166142c030b2004038038104d2210b0040303000c1c500a03601d503681c40740440f14a04004000189140c4030a100d200000140400b001122900900540002000074030300b2012031880c2140d00e80c00401c425190060255128240340030804109841403009640c844040508a48580311900480041c0c015803942507109540d1a00420884000740c0700211940d0f50004400680741903918003070f400551 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507274244 1250 507272994 507272999
    0x110c010206131e02220f11070308151504170c01050a0c060b06120702060c250501021c0204080c0f060a1107170105060a080f120c010b090408070c0519 66
    0x56401c00d01425030803c04907603000340356500003e01112103035800c400b100700e080c2d03210071908026020701103601c0c1100005104915402440d89124070542c500a810020075030045080c0c2c0c1d011095608a541e0000d0001000130003109110110354001d111381c808801a0604000c810400400c0301042c4620586929041c210001c0c0c081e03500203181503086595596075404840e081c0d0f15400640441030740400070311070b03524003250064a003e50180c4001c1c103c032024406100d0107200c1042400b8000100c400e8409224131900e40540a4083d041a00301038200e00c3c0d503050100a450b9014100701e80103070b000c41e20f1942001040c06110242003101d1234000d8020007083c50000d000b2030314090014251402c580c50f0320340e0348045103a0a44c1c12410a03003140d449405104440c03400c1100071001c4d1000314042c0800d03c040c881c2007560b45a00c004684400140422086134548007035200c0d01d036504c00504401c5540c5400d00e45041030354012075044824011030600480c150400324110a111840c0c503600e07454590 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507275494 1250 507274244 507274253
    0x1150c12081b0f0405030106230d020f03010911030601171b0a0e0f0406110c0d0c05070914010503010c0f2102070c140406050418020402090f10110c01020613 69
    0x400d507801d8001c05080a8141c036854000900503e002a00c419442e181040c00301802e64089510808502030b000c1c603409012030032410400345d811421a01180c1465040c0b012070b90f0341c402407981c254594a03000003202030000a001036440200100c080d11450380e25040020100b21714591013651960007504402541d18400401308416203004040d43d01c0b003542e07500f11444181c8100c600351b9131195100140010408035000329091001721401c101c0c2460b0704113000c240d0310081481c4140c100505100f00006203d41482000c000e01010801803000210b40721803181501d03000e01c6614040e40c6404451360340703140b0502c801c5260848582d20421032400f0491107180318100d030f107055000c8540c00c01042c00011034040a00d00141084000c14001e034000b00300300400c840e181d500060240d0b0928441560103000303120341e410350310b904840043c0c8039031004003c00d01c1c4c0c00403105202d400241448920031a10341105250398150021021245400551300c01242c5a42094030303403400ca100d54449140025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507276744 1250 507275494 507275507
    0x1050c18280f060e0604051003090303060b0412050f06160825091d04110103020705011b0c0c06090b0d050a02160c0609050d02090c09060706020d0501150c12 69
    0x414041c104005100c5140c1c0d0400c0c980ea02003500503003900340810126030407101c500c0c140c034012240d0360b04251411020580000042d03410508165417841003104240c080c3c3c0c8201d02400f12040c0081d216030300d5030246030020701407400580d03032442102099036a8200020f580c510505500c041018052140c0c4415903406c1005001c410405448030b808000210440b14180d61003c590b58540c0c9059181040101103c06103100840c602023107241040702040d4208847c103c0f00780b0170700e4016500c4100d401d00c1030050100c101c80c2002407156191003910306500c002501c0440740031704a02010180e03104810b4501d20118403070181021030038400b42e0241110350b80210703408000b0400151400001d410305c0200420143c1c0c0071164040d00000c00e00045074001d0503000901800d440c01800b00900303030001038800300000c0c40d07950b0a250000310501a0345841c8140c545803944040255195001c07881a030000d1301d02402681000c0b4401e15184110714484d5140c2c1380701135040b05a0708441e101043c1c00710f904 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507277994 1250 507276744 507276769
    0x30f020a0803090109030e01020303090d1b02181f080a02040c05071407061e0210110f070323070803071d03070e01091805030f0d0612110301050c18 65
    0x194040d8058680105030514000e601c21484040000345010461401810a8412007030160443d442030003001070408000501c0a082e5240c0e0408200080019194600c04032204500942088079101e14100458041c07202c0ca004400e5810000d0010082503000890780904d0300c2040c5090b40580a008054206644540d084402c00c3c030788140340c00c00548651101035114a071050455010f131008211040c0c3c05242e142da541225403003501842d0842030002d540c2d4130ba0000441d2100d41c0c0d0201200703405403a104603135081002014040c0c842c0c140c0d060240c400701004d1464091340c00c0d50091a00c585d10311404807110a0351100c0c5031030640c2c0f55000102c82c188014540d030500c210b000490505a9502048883d005021100407590158105440902031f19490440031194151769068403000920110544a61042c04e2704441c3c2c440c03040c4550385024042540c0b0000c00046402d0071700d8280000726540070107007a000e800901080d15202c02d907070840d1080488096010310b04464400403440c210f081c0c0c2c801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507279244 1250 507277994 507277997
    0x50105030f0f0a08090f0d082a151801060f150e0105040e0a1103010909030e03010b150a12050408090117040809060a140f0903121c05060d0f24020301050d030f 70
    0x20500ba44c0045001f8410140d4181e680401c0440c072294401c440c81112000b900c580e0866079103150007079461598560030140c140396048120717400102800001c1047e040c00601e544020700005580e400c0406030441e00e030003515401d007421204910124042c3e1200c02010710b042e550346281614051800401402c060412110385403100c01c0700d003480c5c015602075030207404040d80014a0211a1801a15009414080718007036410082c1414070b0b90745480c442d00000c2c0d4030011980d0355103118601207400c06000f05404000300d1400d0140b20038468100088d0810360801c1e200c2e042c48526540b0310400c0110f00b10340061800304100303c03810850514101418841d03049081c6080000e84c11805101103800074500184001000300d412034032071400304411400c1c0e0741d200810a1a02440011107818050381504071181213846002040f07040d200c031038a0480064100080000e0280d50b807510258800c0300089101e003552040e0103124405899100711390403664028030640d4800d03895901034070b10710082c0c06040d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507280494 1250 507279244 507279259
    0x50304110409030905010e0a080d0e01170702031321120306121b0f061b0c030203101b030c021902060708030c2505101d070603050105030f0f0a0809 65
    0x10425141d074000c58000d6442501d550074401d060400040456141619042c8240c8440504202440c80802c454560300144d00e0141030084d0102c00582d00b01202290901241005804211207280c0c00b00c050b00c0d40f43d11900154070450341d43e07000444c0c0c1202c640b0141031039030740a03605000010709a070180c0d80e0384052400c0201d07145940d41821401e41045150503038200c1c4801c880300c2c2d170036129400800050304440785a030109500b00000100a003c00983e12003803001241d50080521185100d03101c0110740c0141150400c551543e1140301514a8085001c00406c080140c5404140203020b00c00e12113100b45e0080c07600b200c86c0fa100c038201041a034010781c0c02074810410240032441d8403000390302c11020052550b54403258401101481d00741c0d0b1300c0c2e5001d903540040103400000d9022980c5000c002e0749803404030b2a13184107202496200302e250005685440341580004038030f90544c1105049800c100c05460110700c107000c11075150090140c010080b0b4002c4908a0005085400030305501c540190603403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 507281744 1250 507280494 507280523
    0x303080f0a0e10060302040c03110414060f04080d0306080c03250b1b060604020f0403110109080f010b1e15030c0708040f0302091312030207060b040c0f1704050c01050304 75
    0x10b0501c44800f1029844581344c80c018002d5040c18061744944002500d000c002c1e941201e1461704840c02107010308110301b142e80440c60200d54903203080d10002102c1c0c41d019a5110358920380303190303502280f40e030301400700b81030007030001d046100800e55428402019024103003d07002e1034405d0403400d00b140204410504802c2010902c0380c00030000d000564114110424007102c03440c200c45c81e000000301203a01c0b03035004101c08006040141e069408482d8400302d003019482da6080140c8400902e0341101c1e42c9407082c0c90500b80084c030150805001440c00b80c4003000940300640e040b00800400550082e0031220302c04001510740f000000840e0301850319038845050000503500d0504981c49903001d0b5000d001d0900c0148150f1501c0c0000355004400c076500024002810f1b0b0340c01c4000c01e40301a00c0d03024181d001c82c0c0e0760103112090300410241c02d0000c01c00c01c554200000050300c4840403140803000111220b40001d04d120049883e1070140d41c0009c000c00700c004070400115019403004000b11144c000041d0b48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 507282994 1250 507281744 507281771
    0xb0f010819060e040506061906120207080c0a150617190f05060c0d05070309200d060509010c08070f2f0a0c090b010e090f0a020705030406090e0708010303080f0a 71
    0xf003402036104002400c510300303100e41008005040201040d003040340c040f00802c08690000304081c10003801e01800b580b01c1000d402d11241074042c050400395035009805502d8100070014582c81a0b14505507010404107841d4843e0b140071481a41c10b0070b019500c0070003098a443c442100310302c00903206406803000c24103103035281410300406031a42c0121200110b40100c0c015402e004240d881040c41c4ac04200480035512080148230181241c492825000461000346843d5513441c20440354115905004908110181a0003029403d000200141c0341101050010b88540c0603000e807141d40b9519074903000395584003500300c21000414002c5100c072515400242000c140003a407516401f80c20790040141ca800c000c401070382d071241c41d250b041085051607001203690704a842500018204030344140d035600c20070070000034414008060014440440c000a500360311400440640c1c2101c203140d14103032a41c00040d5100e803401e010083c081000c0400003120b082c1004403d82c0c0c4440300e240042031800740c9800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 507284244 1250 507282994 507283019
    0x9090e030d0e0f0a030e0307060e030a230d0c1406190c030f24080705130209030321010306110f0d020c0c040c020a02030f0604050606220615030b0f01081906 69
    0x4044002c40c070041030413001487c003807140300000e00752030500002c1e034091003000a4480400a034000e1000b80c0324030842100d000c04450409070840300404488400d044d211004c1e180801d224012502130359020b4072104600c001003241c80c0a08002c2d45039041c0351441c994140301402801400e24201942d4030248003940c5203c3c0501d003007221407a84444484442164038020841a580200f410303a880b4140c20845611030b80c0c83c440300c5001d10303900186c540480e500000d0541c4280e80348107800c083d80c40302610042410010b2b46040300d110b450100510305022074120303120b0050070003407090781e101800421205074040e001001e100c620385040c2e8014a40c45400a0200c0300c0c81e0881707400503848140c00d0750850408101c503139105005000186080d203407556840d80d407030320020496805100f00091000b0010103548a8402e4055249014800f1b0b0751a40800b03803009841103a480006070401e072594445007480340c0014550780041e5942e4400da0764050050f19081000d410f4410400d070f49140006e140160b210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 507285494 1250 507284244 507284263
    0x4050603222f010201090308070507020109030b1f080118030518210f030304050a0611070803190c1d0f06040906031202010506031501210506070c0309090e030d0e0f 72
    0x5048014180c203100c207644402d080812054196071400c0b1160021035004020160311004a243c6280c0c1c60038203200403152501180d20003441c0140c148280158036981c07500000581d81640c104c00c03103441c0e855500ba42a03c066035000401e1509004100b4003203442540245400141409800c604a1515021510100050340d10003005100301d180c3d02c18681003804180c00680c000001141541055114183c0b1040c042000070940c81c1d40b841c4001140e40560300340c0e40790b40e030024002c0340c5030315001030b030204652078a0f10341c5c1641074603100c50a040342d40107101003401d441c00c1c4403040948540c0e881c180013085100c000660340c080001d1000064900b1580540d501171407044d0000e4020740d04184000e030950300098401c0f44260031411048054081c6003042ca41101c0341c041211042040b008a174a0039034010260161082c0608000c00c4106d81d0404408140580700e5554491030740c1c4d071200010100c542011784600240c0040000c030325500640d80103041e5082c219404c0e079a041504d14013186c506070200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 507286744 1250 507285494 507285533
    0x204020706062606150a090e012a09050a0b03070f0207080f070806070806060a03230a200408150a11120703050a06060527030f0718020405060322 64
    0x40f6500c4642042c41625080a1060b014909007030180c40000c0c2d5141040c01031028180d9600c0c400c1c07500b40e4007500301d000458241640740da01c1180c15a49003940354841c10039040495005d0344001090b04081e15050201e4820310040f0b415501c0e9044200c0701500660b0190045104151010880302010310404690300c91a0000b03042e000d01e011082d074146000205180c040c0701d10081040b191782c90b030034115030218403d8900001d0002c0340010031585c0c1186006480c0c0c034240a601042030f000a107a0044442000d17011103208ac1007240d203031303949580c41180280080780d0411002c40412402c0242400d030419815070000c26680045c684854581c1c028108040c268541a030a21003481d8051144c540c010318101c0003408140e04061000c3c000d0702c01c00503182c21a081402103c0f101004544814400316001400c0c0c0d0307443c200e4100788035616401c50051204254002058000d94401c070301c21982201c070f0141c4000e0031039031241e0710982260380c9140d01d108803c0c1c140c3c80e0440000c1302c812084a030040c0c907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 507287994 1250 507286744 507286799
    0x20d0b011514030621010f060f170115120206041208031b070b0106080402011b030503180a120c03140a02030403060e0a110609120106081005071803020402070606 71
    0x3800034440c0412014801514408100b1300c566034440d242641c030700c001d6900c0b42c00f00a1585020302401061000c0e803c800c107a140840101320b19950300034000031200d014202070018070862580d6400c80d20000617501c1280d005501c02c00242da0040c808401040c0010704440c10180e03110014880c081c0400c00841d01b4140010801c01c0031140101c42100c500348140031181804540c2d0354190300101c3c180520818041c2c0722000404680c40b8201c030102d559601d08000740b590141d443d01030895001036440b50344101400455039080200041c9441c1010b4101d5840042801188000c0da0030100203001070f000c0100d40c110710000306108078000d1000b06055402540d0b6913141d401c040c001c03120810110f50b11030304400d40150100e06200002340790130714226403403655101400b0001d80070116240180415500b86900026289804a080300c0c480c0d20480782031100b541c91a4045862141c491044440600e0810041c0090308060f40a4002e45108030400144992a02118401c41c0d464405044e02c034000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 507289244 1250 507287994 507288029
    0x2102071506031a100b0d0204090207030806040c0507050a15180b06102c01020705040f020301141804110607021509010f0801050d03031802040c0504080715050a0c020d0b01 75
    0x22050b800c003e480b05100114011418603140c0c0ca90000410300c1140c40044000c5141c10b00704c103050341100c00070030b955081199a81114500038142d41421204140b09600e0310750301d0746605004904070303048503034004044e203581041655103030300a0005a205060640c1e4a101001d140400700001041035401201c4140d49850b100c4100501919443c010404000700300700310480446090700e4001101c582000394181a00c1d5510040340303044482d07802554841d04140c00110090f03400d84c000c1d41607070494049030141103640c10038403a410710411500c07a8401e01c1300c2c001801060b55254405004900100000d05d00302c0c454000450426860031902c3c4644d600044a0038290b8010700d2903042443e003400c00020a40c546000601903108254011b400d041e00c85089e0300c84850012240c0f03d0066001300100701580b900000141160007030700400c1001e04c944140410103861210700310580704003695501d403801c10385003000c4804a240704000c982100d071443d8420009981c2c2080e090103032613441a0081d070b103117 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 507290494 1250 507289244 507289253
    0x706050c0a023313051215011512020f220e0406061404050601020c150c070801050613060e010b0d09050708030a0909050f0105061b01110702100807210207150603 71
    0x11a9803c02400c0c081d08002641e20002001248022240216140801c18119840711400d01c2056240781c00c48600c5c660000c54950401c2034a041120120794a61003061a020091412481a485044181001484416118202050003080d80044402c100240300e588954068540c00144ca0031504643c0303448080c400b841107200701c0b40c6075100440d003d00840c103000c1c3c0080c0d00c802d00e19502038003a20911680d0348000c503c001c221005d013021b4108540720b050b13a0700803541c000c15060320110320800198a242c1c841d5a85401103c05175107003c5040d60342a40780c5003001e4841d911500b081e024098403149a0404140c09000b400c1c000d04150028542e81c0081002c010980c0e4070b59080400154503210511640300801164903041da00251011a50b440c403401001c04605c0e1406082c400c190300b0094030911843c481d802400020344251403031070400c4404441070380d88680840c0c525001036100e034051301414908020340c02c104d46440b00018940310441d156100440e840000a100311511144100b0401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 507291744 1250 507290494 507290569
    0x12150b120a0818190e090102070c090606020609030705030f03070c0f231f0c030b03120901090b0a0f030902060d0908030417070201170402030c0607061505060c0706050c0a02 76
    0x2800c110f58041689046083c40341c13409113a800303481809520341c0001140d080b0300f541100d50a54221210506090741d42c1c0201d00039210b2809090018002c10380031541d00480041034448050b1311002450030107814851401c01c640005160b0000c203d0300f045803201081102e42d0b81c241070340c00b4075118114a620321070100c284008410f4048205c0c1c1c00386041d4420001c2c000720107c980f4180c0300011030703040d80d03035a022405403040b2101d840d0b05000382c01541143c03840050003440c80110031380781d4400716030f03540403d05a03502854940c2c1c0c02043e040b44411101610907400b403d0303014401425a41064a0001600201e4540c4507040b10780c00c000005100c244480328204444c07610314501c0203407078080a6400204403009061f00100b00e50000b60104045540501111429110103480315072606502e0034194007800704882a000141e1200c1008125810407408490a0222481c02000000e02d000c20403038881d400200662064040c0710340e10320041e40c41030ba2030400c441d01d2020120b03005500360044502d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 507292994 1250 507291744 507291787
    0x60a0e0a15051c06030203061303030c030203010f05060703020f010510140616081b012a020105070503070507062a0206010905071b0203010e0f0d0912150b120a08 71
    0x72076007000229400240e1100c12180c1808458000c09403000c1005a24005440160002540b43c051102000b0b00d4119640109100300d001c1d0342c0a02c64a4900741e1b0680c22807100303000d480840c02d020354040c8922f05240c00180080e034403074411954244180350b5040d086403400d540420403040402401c004150444522103d012811510f0900e010000c40703581e4000420120001c01d5900041044003581d009400344034100901d040003480903100295403544030501c0810740c008488101c10503160302510511840384551929142d0514640765840140c411381c2201000303c03401525103015074526002d048805424074042c0564014405e03103128081d051040503007000651710b00d000e00f007001569000c05540b04c502040201e04a602c0302c0c81c00803070302401240c042d20361984264210300061007800107a0843d401ca10382e80d20344038291528401c04c40801500009800e00250000c0961144040e5004c0314000d071000303100800a42d80826101e08061500320140d035101d0340854112458004429000311 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 507294244 1250 507292994 507293009
    0x61002033108010e06011205030c0a050304030209090604020f010e0607020d0803070f0f050409020f2101050a0909150525090305010501090501080307030804020a050411030105031e15060f060a0e0a 86
    0x1507044095444c0340d4464051040100d0b20303614100c02e1003400010710484490201032025681c4910150038416580d600a1008901410010b0000b400081010840e0b03800741d64000d00400344d80905400445580466000c015405030040082d207006a40300e50b601c05580d4803842165403a4a8030804c0039086810740c41407a02444076150b036091600d540b0204a500b0b45070329120040e09d60611141c00ba095009442d075007000231346110000081803d828480904a900c100c84c1010b0040c4c5400e006815581b0142d0001d011410540d000d494800f030540201d54050030212540c0b20820445007096100d4031704114000c0400d000e52400d2003803042c04e000b03403405400640c2d000c2c8840d500d0700304501e85d00d11804002034100050500494215031741c00c16403e0091030028020700c94100c05907042e0045a0081c0720760b070721a1140d40628501d00d41078030a041058001240500110741c41c1c0300c00c1035110300d40103102581c05003040420902c10360b915005403004a040d40d403180d041d09024414484000f03900c4d00a9107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 507295494 1250 507294244 507294251
    0x204180509010e03040e130c1502030705010e01021306050d02160b040606060c0b040b341704020105041502250303020d0c02211903020c01020712020906100203310801 73
    0xe0a80e214521f401c522080d41703142d0500e000d030602110354441a0025440305807075440e19803103254000050702a2a0041000300040d9600d102011700300d1143e120b45040850003c0400c21060703004801800480c1d4001101500d4800d02c07013051400102000e0040700c0c0c280d2000184410300c0424419031001d00072a041960180d02e00341c8503e0200d520082c40181418140300014481c100d80c510522010000450f00180c03140440c0100b510104503548020006254500400c21103400c0b141410f004036010384520f442d1a0401104c640d444d61096154010761042c1070040c80309a01000340d240100b40b1540c1d1750941c00b070135031400a042002d03955070352041141c00c862450240c3e40c1c00c024086411508503101c0e503640f0310740c0b08413400c20907620300c0146142c4c00c0705100d1050640100381c030340c2c416070240d09813800542c807031442413040f1086008c00b9402c0008600014158180804d900782203030b080c1c0c01141d04000710941e0b44c20203820000308451070f4040890410450b441008541809802d9020090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 507296744 1250 507295494 507295499
    0x30702031504150507111510030204020a05190302041502150601080702250e070809030a23070f0204060918060908070512030709050103020405031009060204180509010e0304 76
    0x81e036551861950001c815070700201180c00c0208400040d28201c807a60020310503440c24174006019104001c010032224020361380c91680d036603c9111641c0c803941002450a003031764110307003e000003500018642014030108000038000214124101e1080407625a0f02590300c90a00741c00e61460000304e410181954080701901580c43c488003117080c2d1100e028a0301e00e09540d10214102e180c0309000902103841c00003140300c181c440c081010b41006443c551402c0c01c0755a140c1c0d40e001c9616440803100354003140c00521035038038182d05c41d000c0e0311070b07a04000d103042c0e0400340c0800301052039510904089516181e244202c00450505000358002040300351401c0101c8540038041981000c03403030750028002542e0750b2240f03007008104c03410f85241a401004680c3d071340c82c40141c48000343c3d0054039010042060424001002d41c46402220141d03000500500440d02c400f0400502030058090b013280c00540a12002c82c52030806150410310510644000c5010b0130720741c4203242143c0c0407074160007a580042005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 507297994 1250 507296744 507296749
    0xb0d030507030e150a0c020f01080f040803151f02010f02090f131b05030f2203080a1b0c0209010504050f04031412154b030102030109050711030702 65
    0x141d51290780c1600380b003140b00c401c103000508580144442200042000700340d00980640c084044034081e0300c25a20070141c0c032040e00045d034444900700e600b00c01104520340010000303040100a1074002020030740c10b51003003a40c1800240309920241200c10003094513405010400d509003e03010000c0c110600840ca8920000080752400b921400028060300e18806e2441300d9a41d10b03441070381a4414581511007900c07841000625581c400d513616040b2040d10408603074911140c0c0781c02402c1d4140701408100d10f13000c40d41c00703490b0105d0040c0b2100740d55503103000c104580304260500d41007106c419502d101c1d0017100c5d80b0402206207030607003141c0c3c06549008100b20340c0200085e4079541203905410020f010b50700c000091800761280842c0d00010140c0070092008104d181c03003d0014441044031046440111104042a03050020300f00000050744501c0d20382d456a481c42043c08903808a208105c960129100403e099920030fa020668190340d030401c0041c0654031040c0f0740d18035100d12025601c3d0000303a800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 507299244 1250 507297994 507297997
    0x131703091f09081c02060f061c0201111204031415040f11030d03151e06032007260c070e070504030605010b09041104060905010e010302161109060612010b031b0d0606030b0d0305 78
    0xc000344c00422249d03184095a00503403059080c2c07802c44080b0b498924160140042e0380e00241700071034201c01c05040c09440e9110200d118413003000c204503400f182d0f60322070710780d524150328020054425040400100304192818400291810344544012070804d22441c1c401c101d50044d40d00401c5460308480c11468403900c000340c25811140b1502c2c2c003080c02d98507620b443c9040c0289400070400e10300c3c00100c1d0701c1005089038148000c0c1d90000104a801081c103002d2178802e100340010700703400d50051030080c00a80f5020703020a4010b81703a454018145512560303110110399003038005c942c03054404980c01002c0d182c24081c0d0a817003800c80303412030f003040d140a0303024140220a028241c144519030100300703400e0340310303074141ea00980c004c4038007a000301400c0c100728031802274801c0524050348001c00000c880b400e0030022540c0d403502166152005a2038003c10041075080a0504000f410780c2e0701c00040982051800b9011130b0481e05070000b09185442c02c05806c4078120178280d4066070042c140b0a02082e0401c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 507300494 1250 507299244 507299269
    0x140d02030405120c07180501050f09040507090e0606031b0105071e0f2a141e03070608070e0a140103090309030602131703091f09081c02060f06 63
    0x5038880e00c681ca0200d0034400840070b0100712081c003144610a1003000205182250952881c02d10f4680c0c0c1600c3c40020b0716806d00800e50049194081c0c05214100490440c1d072050080c01950070680e1034008072420785822459401165208070103110440c80c0c20b1111802c021402e19866541c0b071011400a800c0740111300010300134000c500c181104190380104000c00c503552000d0b800b060708003a031805041d90302c05003021140060300f20403c1008003c0d078985450030703560704002410b201d902c10380410040325138880000b00000c901d0301044180c0c2d2410410080504910341340e040d0709280112f07004001c5008550010711805112004104401910054501c42c500a1a02040041e200d00b0250346080b51588010b002e00d200058600000407800720310401d49454160350f01c05031950119450741c0f80544c2011503800002d10a5210f414903600e103c28200132481d00300305800a0740c410710182841804010210420500400280404d6042c80095031045551504100500745400490344005811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 507301744 1250 507300494 507300517
    0x90c0e01050927070605040e06090103020f0402090105130b0301051002060f0a091b150f090e130f0b010e06090705130501081906080714010f02030a080a06080114040b060114 76
    0x8402800220104060001581c04120100e40c0019511a0006d000e0f0703010744240503010a00701e01051407403520074207060403646c0060003c440d000c200002c0000950051041e107042c4042008a0403c2504241c05040280101d009080d1298035000078068001d02e0244000700715003000c0c0400510560011180d50060781d80440004c00421518200c50854504103070302c0c00e102620752000500518101c00582901002e50341c0c49451141d14005840c4455503025841c2c81c920301000294184900e510035542084c06450748041850840d2984580307110300380c0180c4002501c0804004040c101080c2c1035410401902d0000d261107203046a01141789110302a4504018485c808106031606606002e01c0003c4035410420105545000407a07880489210388590380c0d4140b0700c1420303690b0040c10503d0074001c06401440c988034000c5401c584d004402089001c0169442d00c002c81d180c5004d11450030401082031411b0364501301070610f00000b00c0000d00040c100300d038400c003401c03810084001382c908140710b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 507302994 1250 507301744 507301771
    0x3050d0b0105091c060c05040302090a050c210a0b0f3019150606050301060c0303061d060f030f0a020112020706051306050a0b0f10020f10090c0e010509 67
    0x15100102c803244980c00c022580300b0710340710f03041e9000d0101941800245204001c1003040e42d5049909448034061440040d500520a00001e14280c4050700302c0740d4000d8888030490710302041000e04692881c030401200e104002600b081002d450320a2103a50118fc00441d00c2c41d01020303c2c0400a1464419024210624000300a800c28980100041007022801b81d10944c0c412100508021141d0b0990341025038110306902d04048841c042c0740b040100740c45555948615681c01c0c580103a500d6030b502401201015500d04001a1142641c00c804443c20040c040c00d070b80c03c1c00c10344200f000445030140400d00c03a07000090401c040400c00034903500383d2503080c2409000045c01c0600e190003030055410103800f0ba82418204481013002e400101850340c411042003040d600c0d00308501c07048401480500e07400103141d250300c01c40d910b03201440d0b501071105407040740c0c4800011f410040c01c2c044100c102e0428141c90b4002e5004001c41d4810700382c00b41034020209405580342c90000b480004029000341c840d80407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 507304244 1250 507302994 507303011
    0x91e09020411031f0b07030219051009151d1f091a1b040e190219080108010e120f0c030f0a0c03170f06100203091e0f010c03050d 57
    0x8881c1c1040c1d00c24641c803035289459103402c085001303681a00f588000000101510007040007840707441a21092501a40145100711b960311000e0000307000c111080e0b0301c612400c41180021240c2c0e010320b40d04070b4410742c05503200481d000104000da0360814802c8407071102c60348032140160000070708444035940002c0c15002c025009140a0f004150950001c0d002d801d1a052003242c004501806038058072182c1e814400c40f48030310040c240140160300540003c2c0043d000400c0042010405080e1001101080107180180c02c5e00321482d00054038401c40045501c06004005052081c41000310410002e8064905c02050500001c0b80e13105801440c0c11024012505200f0721908000f030714080741c2000d2041e5510706030510081c102ca03200c040102c1c00903440c0b160340303a00045c0700180c0901a0541e281502d402c4e4499130708001c4045c203012800300862000744440d8505555510b02e00d5034142450704840102255602408080c0c5081c960312030502c40c0169507400040c0d44a01118281d54180400048003131 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 507305494 1250 507304244 507304249
    0x10e061e120102040e07090e0415050c090d060506031204060801050603270106050f0604060e041116150e0f0a0303090606030c090510080c0d02060d090507030b0907091e0902 76
    0x5115a468603550b61001c0790201c1c08851165406000d4180343d00c60500170740d541c81400a20410880300102102c40d244c0b00203001c801c940c0c1005800001c1481198141003004c004100300b4078002100382e03020f54071442445130b20f042c00d124100d2541c0c40c000040b4a002c0c2883d0003e44151010300c10180200c1d00007000695410b203a003003e80d10070900100c14502016460645406030403140281c170f20032514100c486010349054030071078044170800e48404c600e0300d0031481000000c003c95040001e4511041280405200030694000780c0c040c4164100c4100c55400c070103000480308105110120381e801503007403104002000413024000340d498038010406002518000d8043c20107036000410303060102c07401155907010b98100310300c142c00c1c80340e1480d80300799204440307541d900c050f004c0603812030391079941c2d80003500f411802040ea000c0c5508011238080c0c80303542d80901e8029a5071054441075010b2084c8890501c05219220080810f40c400348042d40003020481301c0185429070302c421940e501c101c010110f4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 507306744 1250 507305494 507305509
    0x5160503030a05180a140a1b091503030e061803070b0a030536070915052409010c0c0e0a0b090a0c09061d09070918152603070807030305010e061e 64
    0x47d580480000a10900c803404100000540d00460304003501700803103482c51700f56503040841142d1701581ea0110018404041c40b0382580045c12880c6d6521034100420403640303080081d030000b80300d50864a40d8034404050020111203014207911110004031200070b120900c01505469101e2154803201e0b00201d050303401520342055540701d001100d042c918400d000100717404229085400542d03080300358070300428140b0310310030540d031452203c0c6c0030078020720281c3c0d48602c5000030114030500610002a8950480141c0c1080403a89550320300c0c1c844110300f1305814103900f1590010280d0005100398240301c00e000d001c1c0d5a09024130b004110310a0500c10000301c0c02d00850b201c0d000060110903240c2445c6100406001203405025001000b269802d90300000511818803131030b4200218084442c2015044031550b041d1800e210b00c90007100f0031210703001030180000c00a00e0302c200036107a0784d2645850003600f83d502c164400e40d004030241c0c0803c5451b85a06004010702481b07643c841c6403641c00c4200040343c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 507307994 1250 507306744 507306763
    0x812060d0c0330021506030304031401061a031b09010512040b09060108160311010c0b07080f0105090403082e03030504080705060319020a05160503030a05180a14 71
    0x1901a2004000144203041c141c91101646030b00b04108102c200f4500e4000c19400a415000181c1c0200d203582049000003c3d560340080b00201901d180682e06d44800160010007030140d4201d0750b481108201c01c4d869258009089040000703a00d0a6240202e0515440308040031508070082001480381c05c1607200e4011184001c40b12030a05d6440c1c2040e00700b00c141e0050450f0840c010380300317803000810b1203000007941300c0d07040295492071440386003190b644442c1004604601414805444907900015101c2021144260510b68456601d8941010821440041a84164054540082440f0110382d01c0751003aa0302104000d0f0000c040b00f107100034680b01c030f00c0311000e00c400c100324a8800300c20554401300810440e840d00c401c03a45865161380400410b480113803092103082c03464600441d03001c420b64000d08140b5a0b1400d00c0c50401001d08c06c014450226010102c5541d04000100f204113071240c46602d421440b80401000790a01414403190b58542e41000549401044401d00c085140300b0041ca503030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 507309244 1250 507307994 507308003
    0xb040b0901090f0b1917031b1c0801060c0209061f030902030c0a0509040f0501060b1303121409040b0607060f02070317071706030a1407210812060d 65
    0x9540c0d40c2d244100007001c400251411803824801820b5079440e140c21003010044010012112103864031050140002d000c11500c2400c0c0003d100340d0681e05d07a2445514030440c81c61700a008491000c180420f09411000202410712241ea0014007060394013a042c0b00d005a41954004040d403110f000140c29080500c42c013040e1180784000c00c000199140d00055045031003501100d0311003000d20201700b52111503004168000200c04002804544a102e09070407441c0201c0c00011216200c1101d403499a01000e15168803000e01682042000011007030420350411602e022000e00208120b2401e20b80b046c6416503104a80365103e141855aa001c111109113501801c204030300301704420792401a400c5140180c020442107070607026490064040c0754030038042d13070356428000300030590b0424803901c000c1d020035003500c03541d8801d5000464043c0f0281c50740e034103a001480c4051401001000150701a286161241240c3c092803001038695826036001144003c40c0480360741d01e15002c40c0303001ca2031120140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 507310494 1250 507309244 507309259
    0x4140706020309040e0106030807170c012d0b090403180816090e060c0d050a0b1206040b01080f03040b07050c060d0605010801470a030f0516120b040b 66
    0x580160004001d00f0b4000d030948080c062091040101d9003255024440035020000c00c001c00800541c0720141e18281c5a01070181e40d06105c2c0c2c403501d0358211006281c40806c440008440e400514100b0155104501074210060203010b246001203003070182d000d4001070501440004880440942c003000c4400b4006940441c0c0c2c2c84500403140095050480c455116000c2c9001040b51851402107100703032080c0101b050341e910340905a51104020312000341f00451150b501c140064440d5a20800011056100d00c001c1c03603141030a0501242a0b8010313800328205500c064800d9204280c0070042d10f040703400560819440c2c1c0c4c101d081c138074206402101800e5010b080000c1d60001010385d94040c4064034401c0e03884209607030300c40a103a02e0700c00d140900c948400014208080d45010001408110521000c101142d0000000302001480d00310421902c08240c640440900c040310512440d070b4845c02940d843c010a0b1601007001d030034a04007400080700161146440c0c00c0300c2e192908030b4401410302600c1c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 507311744 1250 507310494 507310499
    0x1b0402190e040f0903140c120a030b0a14010c0f17030420090f0a0e0c0405090120090603040816050304030807060c03090512250b06100c031205041407 66
    0x20540085420400c0c41580f034075060000d04807140c0f041841d0700d9896168926250300441c4510700c140c01c19104e01005103e0483c101d61925441c1c4003404100310140c4007c901c8440312800c11050204540064484541c0e0b05a10f00c0070ba0b0380101c000b030310607410080000c9000400e06208581c2412030b0341c04083c0450000900c000c02100c0d139440700200006000c00610070400d20100900004140e9403107100f150840d010509111080d40000e84070300541c42140c0c0d44809071000700e0191082101e88003020795444070f5462103003032003030f40140610443d02002032030b1080c0d18001841600001d030000c1c00110011501c081480311401d102087d4582003821280c441c0d0b60b0b46044003007a070201c0300449102d0308250105000c18020301444480b40d511102501c3c51303030420300017201070750084103c80c6000d000001c0c0520b14070030401030740b181d4580500a08200e40c50080c0600c03c0407003140e8429010800c0c02c540413004203500ca000c0c500031095001c0e01041c41d07101c90a0551648074103c2413400c4034020000d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 507312994 1250 507311744 507311747
    0x901020a05190b0c030c07060b0607120905040e01091e020102070f0803030103140c010903030f030f050412090510050d150306020c0c130c05160317040b01030b0a0606021b040219 78
    0x300120b9034032403c1452015541c41c550110240800d4581001c10201844200e0004c2d0440e00401000380000e080e081c21709045491342900e0411000b00040412030100050046060600400d1007142c2a0f0340203108581d8650b54403074510712151152400341d040c00070103071b045a10031b0200c1c20091076003442501c0d1254588080c2d42e100e504c00e00c4100c2d452200040b0030200c0039804114480c4402c0161a04200d051640d2002c0c0c0d101c00342c01c0c910f1001c1643e11084a82080310302e00c141801b0380e015410301c00800b000600060080a61034101a00c070b600403203d1800c105038000d00707c032608840b0300341c04a681c5201800700e20700c4a655401c0140b415001283d001180d402c0001c4a452081d0105d5001c22001c11300200d403401c80e4101500007002500401041c0030401c00403603552401031181c6402c0c03400101e10a048010004103540881d40000114010803d10164451540c2c010020700000c0096514114001c0e550300d1482c4111301d8084a00700f117081007542c80342e05480002c100490420072231203d0000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 507314244 1250 507312994 507313033
    0x6070e10030605092a0a050d0c03021c0911060f1305122d030408150c0f04030204090302100e0115080109050606012a08070312200901020a05 62
    0x502500401050100d214064440e015000407a00050001e900a449240d039404007075100e20441c0d030320010420040d501d903402d443c00500c0070600301e035603481e00c50340f4212030342080c1c68148409008150052085010204120760f812541c0004a400020b840405241401c4241c20707406015a102c4400f0030015141402040101070702120040c4c1400c2840e02e640411000403140c4032174880c55030142c044c2402002c820200c0702d01504003040c0c4164101071540c46103146074400d8115419580250000034140c0440b1a00e45402c500040b98840c10400098031201003800785200180c800c079140da6000044c14005d04c10ba04c2c43e040c50b25000c0c40b6159000c0c00d164041c015100c03000e00480f0040c400020060011300c6049039180d444000f504031900c606004480851100004050802440c1407006000d00302d90000840d070340c40358441680780c401c40d0801038002031524603e0705030a030420410203040f00f1044a203c582001c01c090a0341c541c4010741c0101d247c40c9203500000c1403842040d0721044009500326 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 507315494 1250 507314244 507314267
    0xa02101406090901053112020f0609070510030c051204110109050f0307060807090b031515120105091315061e0807060804060905011e0c05090609090a0b030607 70
    0x39900030483d1a00200c3c0c5007260307000c4a4598803102180807440384814000d400700e80700002a0165680c0d08119102c651414050a881d0310140c0d00c407a07420b01da090070a002036035021000380050304160740b42901245100300f042e0001c0007096520040e811440b4000c0c402c0c0c9805040b00021042d607441d20f49001c031a6120f54106450100f0700c91200020b862810004a0a103658054003400101c0d01c1c1250560300080090070107800c6c01505c00d800f1441d84118000b03184204025480049040d500d1828080310b50b1100c182441204001c1104040003410fa02e900c0f0304441003658040860754846405080c2d6180541c0000d2604808803c1d0000010f920b803c48001e0300c001d10840e0070b150140d000841000701c0d0900c980880d075000f2850400c039a41c0035030030155000b070280c00d001c2010000b503518182140d401000341848546a0f0505154200c9030740b06510b2101e801d42000b40c60001a0030002350140115694a4070498030030000074918841c942000c0d800034405000c440780303402e1050b0094401d84440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 507316744 1250 507315494 507315499
    0x70b2203020a140313030b0a020c03120103230a121202040b031005040501080a0605060f060c012c190f080705150a0506060f035a06060a02101406 64
    0xf0000e000c6082d4003c4125918007110b403c42c80c172003a00e95601d81c0f2000d03000801a40c3c40903400d200380c0708131010138002003008000103492212203604500d4030002104000e06404003a010304030404400b14400640c007661182c014074007640383e40d10420b0855180281503010222617001060000b00703220110040d6015240300180007034181d0b00d440a0200301c1d40c0910594040d6840141140040b61269020726003049014229180c466541c0d004120300f5408400d0803686699500781c68005030803100700d88450152210b0880030128032028a440d80d40044a8400c901100e203281001c0420510512040d1495400940c00303440315414200f0310b032201da422185000c40d0440031b00046112400340305003403084030020117143c10f000110b02c1410b5a42c200030010740a002070729010019103100d07040306071803038240c90041c4407900d014070000d03488a1001c64245e41401c1071400661141c0d1800d881040d40c06601510300988900803107104910b05411580c1c00e00d0b245180c0398102c10385c1c41030611604c0c07294005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 507317994 1250 507316744 507316763
    0x80d0305015111010c0504050913020415090b04090308161e02030406090b040e042a0b031501021b06070819050403060608191e020301020c010b090714070b2203020a 72
    0x200c45211342030b0b402d814042c50005408210034001481c00da9500c2d130b04100b200003003010320866071b40401c04031103040c1c40e00d882c41c08130580104050381e5580030f00440d81c501924144070101040d5006045104007800d850794508400440c4012075211b17400c0c590098056400d0704030115204c0c1c001035103ea206008041c0041c076400c0c8041103442184044804035510007085100d142da50b03481c0c000e4181e51944043d0384651103000c00c0c0c0045098010241c000d0801a00c0144e9a820301c2000c451180c203ca150807410349d00001064150440304400c090054101a41c0156a07001c0390f280c0f90540e0b11424110000c000f84950441c48116800b0010b08203807845207408000050300d504646a9482c80c18003070641c0348000c4047c00c0002800c6540100601059201d81d1101d103200b540000e099800c00411002c80ba90b59244d03c0810786024060150048070380d040c6959415000300254046129107074001d800c24500c0d0010828a00d0411211400150307003070045158036072140b40c000c5d111a1483c1e0180c4081c1038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 507319244 1250 507317994 507318017
    0x14040611030f0a0b0a15020f0c0d0c03110d02090a0603170c030306010e040f020c010506091305030a030b0109050a03080304120306061d060403020405040c080d03050151 74
    0x384408490081d00c02da01a0841c80d528507510b0005003802010083d00501041000254a4441c15010507040025001341c0600c0c1d10f00e008261802e1000306104c0c0c800c010700c62090f000700b03114624846c00d6a4011001f4100c809084000c21883d0b1010400290001d4441080003141e00752a4400c1050741e11842d0541600d4906145005260003200c04d40c8089400800c04074000b50300586041d10303407603000741020071940708480d6420100e80003c0341c844240d0351250b040110710705d04041e0241d0f000c0d8040d60b149100c092181c5869503203001d83d4151109256403003225440756805065180020304008000e4400181c980c586a43c0c00d80050341d044410151a50b000d4034890b000303004a20565209a45412080e01000300d0a00c0340070740c24116035008001003001101580380e500034248114060348854136030f01d11b894842854003446007140340415190800511140c604252900c20104140b801c4410581070b0503812003660303813102070441e42c0c603010741040e5103c00c46aa141d52986c2e0b00584a400c050b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 507320494 1250 507319244 507319271
    0x3030405010b03033c040906050f190b03071e0c2906010c020a03050304170f06040c090209030c10030b010207080a15020c100501031a0603010b010c110d0501140406 72
    0x14008002d0728012401170200340b03140c40d4412007404130b08450640e03130100e0103020140c1c400d54015004490001e03100c04040c402424501c0340324001203c01d40708210b0b000e01c00702442256a00b03901070a00b100c040080804c503002e10444050079020140c0100300d820011244003c0c2070800091011141404100010380c4c21414882c0c2c0b1300408031041085005c29070f40e41f001103a001448030b0040b0b900420b00b40c404000320f132040010f00003510000f50090039250049090500c2c181d0720248140d42584648208000103540820a00407109500000b6071244811030009041c5201081c3c0740c1d4011000c40d5964080c658136400441481c2000c0c1c0a940c000c0761600c0e4100c2d02d410301c9000103400d40c003c160340611003481c29401030040e0701c0900140c4258004170303a540c405903102a4000e452140607030705109000e54410040c141c000d10120005c0010f9000e20001034610a030321400500854044071b81440c05032100103108090a50140c020000104520400f044803102500d06492207480c20201c8044034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 507321744 1250 507320494 507320497
    0x60e010b0c06060907020a0803090a030801080318061615050703061703031906050d14010c080f04140708030d02030f010b030c1c091a090105060603060f09040501061703030405010b0303 81
    0x3010500034012543e9000240121444042c0488045110f80743d80705012403080c0c2c02842c013541c0328a0244c6074088007030800402124042c1c000802580081007035000d040003001000c07000c0301d000d40c0e565031645a0301c100c001c1541c1b000311014142070070b21012202911b6441d80018821025a1010049242c595a51500060640d07200909076482000072401c100161005210703900000d0f540480c10300c1c1c0b80c90100d5401021064100d4a2000c24050804c4c540001c0c022400700c010f0030f28000440d072074080071010003441e024001034101c0c00c00a00c1155003d0050001c0d03400b4041c041c086a43d160040707100d01000b9407040310041216080781c130001c41d000e80c1c841c049a00822080c01c116080405280ba103221142841c40e000c80b815503145141400550b50400d241179043c21100d4034030b0340b407502811043c00d5a00081a03644503010400c10061155200024031001c900143d03070002213943c031413900900416030340d00041c40102440f403000c064601d0000c02544200c1c82480244140010442071660b00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 507322994 1250 507321744 507321757
    0x30a090b090d060b06071704031a130320011505030c040b03150a020702040603031d030706120e0f0a05010c180303050301050607082b11040f150c0c09060e010b 70
    0xc82d00365030014020440c0ea4100380031408000703000502c2e0030555610011155001c1d4040c1459500202e410000e0140201024032180300707092000003545007025000412024000c0020203108440b81074058005084240481085121008000e0f860700641e6418080416106452203881602800380070707070801d0f02401007585000350040c844080c680e10400600e1000900480200e80d09001010241e680c0d80201001103020741c948000c201c1c1c0c100c2080344582e038100001e901036407242008000180d44001520a6040e13a204002000300d5002c014900b80a00e000b072f480b10b10701c101841c1030140141944126200c5d141616151200002a011070b180100340c1e100c003801284044c80108003030f0030a8130041010910070081285411542427082035036810824050000300c0721800b060b40001e00c0342c441c08a495030410242818140303090a0ac000f000a2030180000c001d014400a6140302d011350402d9041c2a0301c84805030314180c8908000b0020300852048004500e55500001103d0f490358048412 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 507324244 1250 507322994 507322999
    0xd052511030901030903020f0105041a0105040510030605070309061109030d0f05030a02090a0b07030e0405071b0204090c08121207050301030f0b070216080606090609070207150e06070302030a090b09 87
    0x780b944000c0150001c5c652540250154050b000d0f11004c10107080c4946842180b080d00e50000403640602c0c01c0b08502e105800c02c50003546004140014000010038400c00c490b4404d9001c625542c03114000c80151174030210040100741044000c11b0400000703c00307860342e0001030f01103401011020704d00305e4000e81d0100d05a000701d4400c00108000c031010350010a80004040d01400040b070350742c1441d06603944640310980010f01e1210809050386002e004041c1c0091003458400c0c2c0100d107580b40400c01104ac03840003407003190b5503001403080091050b01c40009201c00029202d0701c44010500c980544c2c801c001c4d00d41c01c4148240000c83c0140908140c1e170603680c2180301c01492003007950b10601c2084024100b0710540c030643c0303214207619480d020048058840d100c00740490b4101003007880b01c0842c02901807403003503103d4800c10008943c0020b00b802243c04e103110494001c03000e114161224241d201c2c00542150300094580c06041e0000010302c1291503c0c1e4651050641c1c80d1b0b110710190140e46026039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 507325494 1250 507324244 507324247
    0xf030905100c2901150c0c080c040c030501081e1908030405010c1430070201060305010f0203010b091903120804051501030201020303181608010c08011d1603020d05251103 75
    0x3210702000030209416140c6411b254242d10700a464400003012103502c02500c44d4441040d03000035007001d00030702c030036a00300341024803281d4188501e07962148805c0180c4040c0500c0c052030745102540800c4448a049802e00c2144280d0402d410b05034519842120309441c2503081030030000185200708400a5012000e520250a201c10656030708524400f9004003814080c04803124010060b410020500810098000052a500d5031910390b0a46485001c0303c1d03117840c070510041040300d501e041210102a0102c5d1080301001c591155051988282c1d04054495000b80c501e0418603500607054502a6002c1c5003101d0031088010b810b440c9007142400002d00507081030002c54109161307500c920300c9169841d07043d00e140c60b01121101005d1a580e510ac869660f440d000a440f01940050b02d09024001070020303902514007180b141c410f0303008040c0010340c00010300d07c01d51803014400d80c15540200c59500c000c0c0000d00345007130f50307003540c08000b050250000080180d06514900642c05243c5071800203002d107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 507326744 1250 507325494 507325499
    0x9061106070c0b040303090209010f1701110405330306040b03011a100903050a05030414030a03050906090a05040203150a091e0c050c060103080418180f030905100c2901 74
    0x300c0000720f001d0011414161240700e0b8500581d6001411f5028080c0e64042819907441d1109102640e024000380000c642d00d0202000c104003080340440e01a50f0040e81c0081505500c000c0800d0100d1b80800d11021091004040d007401450301002107004020031070303052049804c3c01c1d04142c01c035900c0d03051901c1c003181c08550f145540e080c8000200141041c6061030250b96aa0b600c0342810501d05500450b01b40d0130001c0d00344001d540b04088603501c0760f410b4005240c4980b20f6038003c0c1040c440c07901c283d8480c40020502c40020303a01e00074100c0240a01400554680c03d0010800d000503050050691141010b54408283c0300164032500b400704086c45800300c0e424a00f00b40d00740c0200f010f86803800c03c00900f040030410024081011a000754070031070707005a90f1403800b51591054424441c00911146c105103009200000b500714a0900540250a0325402007243c907098403480807550015821082a0046c14245600a039031100220f0040c1500000d03031020309a404942e0301d000c469110114444c4005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 507327994 1250 507326744 507326753
    0x6040e06130f020f1308120d0509070512030c07060302160b0c0c0a081909060c03050a09051f03142203050c03120601020f1612020103110a09061106070c 67
    0x1404503402a501c00034010546031580700580c1d10400541c40e10100c0000c517101114861021071000b4552036000c4c2040c0800e041c4002541d101c0d9805a01c2001e48840216048800c2400418000d060007050615450368020000d40c881d00403405a8886005030100010700500a000f01c07420341e00d184c0e04803001045150380e07810f400c1c003024200c030700d4881041c400009964000c0140300c0c5640e0140c2d5549846000c00c641c00000d00d5480e000510412640c01000c0002ea0f4101030226840b80e41420300b00d840d0403040d5400c44010216611081d8000c03000718000842d08000040c2140180302d503542880700c00b48d51480350710140340c01c2d40c4510428001c62074034640c05600c005904c1166220b480c02500c0d00c108a00100c2c916004010b40400030300c0064103004056804200c42c8118040c910060001000b040019407040170321071007000303201640c0d144140c0031a882039200c03041c1d804032501520748802042000030942001c030700510010405041c01900d660780000751a501c01c038042c1e501c001c0c5c02c4196907038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 507329244 1250 507327994 507328009
    0x708180705101d0a06030905100606021b0f030703060f1d0c010806011808011e050f01091505060403060c020708030708190e18040312021204080703110f06010303030b06040e06 77
    0x84800040c500074224207030f0340c2d40d514180d0020480c0b5500407805007021f0400c9070601424000026440e40b410034104181500880d022003441c104484200d452500d040101e02d1078810070100580c13502815002004020099020107410700810908000e82c0710003001c030780c4031170040940c42012584121100e204541c4901d840d80e40c0040189095208400321800b8904080501d40014482d40d440e09940c0300c0e030340e2040c00d05070b41d41d02c5556000e01c0135090071858202c0444042c011050a0b0340c4842181450501030b00c12400240313005410300d540c5d641d4038284100100709050502c401801605000602c1c10320000a0b07440d6503405c08202490f00001c0b03280e4840703489a07003e2503020f11203021007038100c40d543c05040d4984c441600f034003010245042c2c0340c0109880b0002041c030310050320502403107401680b907400341c0c0d62141d4040c0da503540e1903005090a0311164014004c0b01e64500c1403a044a6a0314070204a20381201d100361014018403407240e040049a000d24052500c1c0880e1500001c0c620385000300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 507330494 1250 507329244 507329267
    0xf0a0504150806010909021504120f020f0d03021516320c01020d1d030a08061306081506030d080f0a110a0512010b040f0e070314070818070510 63
    0x14403034956a500d120341d0f03003404030903840302d140941e40d260740d1019410021680b00031400ba128640749418100003588414000d4032502030030598446000c407003151038005072800c3e0060011305844404006c0d1034029078075011300c80d4000c2d8080024000c5000304c459040c50b43c211078229103484045074020714907016076040b081004941600c000f002110425580c60007081c04c0c0d01c0312800542c0d41c00b144900641502e40030020040340d44680250740409403404015923107525038a1601840e1515001d0000f00041c01e44100010500d142003c0001d04290004211a980103460f40c03030a07082c1d44003010903403240b02d0480d22402098000d00021140c036541c0c02c0159120600c200001845200a48004019082400b03124003050700091425418002c811805006000081016240a040210701c05c041403aa1080360494036441c804915014026009803103a2550b8219403107071032904c620010300120065880e81900700801c00341007240c06000c150390050304d0000d8001d41c030840c1c250303d040700c0710303024403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 507331744 1250 507330494 507330521
    0x4080a0c0f1505090a05070b0c01021e1c09030c060522030216050a050d2907020c0112052a12010801090501061e0302040b060c0123060f0a0504 63
    0x10301000020300303558010000c2400342c1d0b007924411400d11103075021282c000e88260115406144c549000400000701401551501480b4a840345c50050349a0b01a005008106d004200c0320948400c1d20013066010f030031000910003c89054541030710f100812107454400203000940101f080c1800314240d50002a009040b5001c02550310140c8400044844111401100182c01c84603c0b0301032000c00994501c040c2c0012584806054581400210f004075404c800800d400d5880382c80304c1405190510810003225080d4460009182c48040251120a80c00e0f81601050310048504d505140310700c2034620410040189407042040d2030048120580703604e094810405c010005808207092491900c0e0003030500c0e03000070415414a1033700b03509580d6149c00403c55034580c203000c1c00c004c0d1030705244a0110394045e02c0c00a1004d101c080070410510411900c9000d56007040d40350804072246a800e0b4142c240079850110454031001c0400031800030f01c55186a02c96091a81071000e45010f611294007240b81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 507332994 1250 507331744 507331757
    0xa0f151101020a0201060305071a1206031603031e0809100f0f020a030509061e1603090b0f060a0e0c0d0b0a03020916170105010801170703080f0c0f0607050304080a 72
    0x1109800da082e40d201c041d0710401070b51100380801c20014100b01c150090180f4144d20320030034022101c0711000b809048020346581c0395002c003003a5070381c07014803005003010858510758440d9a16800c0c090614001c6d49102e43c50f500038044800001c40c464625540039500038000307003605480c2010100040c0182c00c60f031185c0b080d99211a880c07441101e01c02004a9901a14013040518090220509244c8000c2a440510480040201d43d280d00340d1803d031f5009031444d1a07802007884680302200104440c09005002400e11018445c001909900c0c81344901401c40b039807884c0300d403540480e0031500400e40c0c8010b59010188403014401000d80c22101c02100043c003100c1e4240d40e03c1c2c00080381c0c6901a542400d0343c4800d0002030b44441d41c02181c14000c80c800380a01c03a11945800002000c80034144601c5002d81038603d101940f0400c00c0c084e0302d0045800040154440c03540559100c9580e00410006015101e048080c00c549100818030501c81c0e41c19403100e60565071039032243c058903840003540c2c5040040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 507334244 1250 507332994 507333017
    0x20a09060c1104061d0f1003022211180102070302031009030c0605070309140c010801030807060e1b0a090e060406050402061b010903030b0103050610140409290a0f15 73
    0x7100e11813140100342c48001d00a40d200810222001d03840060000c4da40c014030b90040100a01052400804032035060341c50171600071101c3d081001ea1500103030341c41642ca0420b05250812150a005840201462820f086012505000590b500c2070b482c0700c02074151b004852050321b00411540a03080f000e001c1d080c80c5040704810350b100b070100c800482c0d43c0300100c1c3d80d404060007404500344158003441e00103801440d08083d4140040c0c41c0050501c001446024001540e0040003655008194444c0c1c007201140c441c0c1450380400400318040152160103903030300c000c00007200c49480c0681c2c8401c0e660200900200d80b55a142c5001600000f04183d03088503040000c04010000340088510a514100c0001003052a524004003902c41c00d418242c100b44c20b060a0040655450225516281352030074035030840010610b01031401c0c00307a94407940d42c079850607026107a50b0b4a00000d074950310a180700340c01111402e0b43c2c100404c5100314010107c0e4001d07900c0c401e01c10007100140300e0028a1460918030039014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 507335494 1250 507334244 507334249
    0x180705030102040b0c010c111506130203240402071104021809090a151407030b010e100e090a0e0601030f02030703080315040c05040503030f090a052e0201020a09060c11 74
    0x2031144c0d101580e0554001217040483c1d01c280b140030031007030385460149034281c1140540ca5461841164542c03001b02020b0204480d0f41d10302010a15181c40d2020035501c0e0701e84281048001e03940c00d02c84041c402191100e0300007515251084656003540b141030908100c81701c41c240710080d041511000b017056243c003226207803130f540c10302841d110ba0800001000c42c4a180d03d0400c2e6135440c44440303a01e02500f80b14078582e141250500241d07001e4200c0c0390000716900041c0040310869030461880380c101140b026102c0c00144c0c040c91541d904401540c0c408038070b40b12002c0120450b01104610102a00101c00602c0040c00740305810b940940001c044400998032070f205c2d801140c4c002d50b41c00840340040300030110740781401d000b00c2c44503d40741d084c2a03040030b14100c0440d4070792195121480d1807280004642106590380400319000c3d183c081c000050596060708000280d0302c1c1c3c00c000716840002d110128503040d1050003214a050919505e10403140d180080c00d407080030f84640100c4103c00507040310800358 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 507336744 1250 507335494 507335497
    0x503310b040b0108100b22150906061107031106030414100209041a09060609030a120527010504151b050c0a06021506150c0d091703030f180705030102 66
    0x20703030140401d07058039450010518a0840b035a10350a404070309000c05413031641d50300e680c4024190341200c0648954040d0384c00d114004c00350400044a03459000d00045181c4820f41d02400c292003540c3c03154200711031183e058030b0b501c1c0071500c03005205e8040040ea201060500e50301442d0400d10a1192070305076030800c02940d00784401151440b10550303011030858481c2ca018010384100c01c0604502d1140a0428004036220b0840101014000e403400180340940d5142080303149012a0064075042071028460001800740d40540d01b440c06500c8500d11030002070540c00401003500300c05840329441d240c5042000500781554030502014000c2c4210481559080b00180c69452445a0b003d0301c8040404c90802c0180861500904115440002d40b80c3c0c02c00f440392811904100121410303425504100f80d00c40301880740031181c504600400340c41049051300050a08240c40000c02011403554004007440e0392404111040320b01c90240b5004186018500c0300146045403680701980c0086844401107402da = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 507337994 1250 507336744 507336751
    0x605070812012301050c06070e06130f06080633040518010602060c16020d14070915141e010318050708060c0a051e0d0e0307120503310b 60
    0xd0b400000c41000382251480b02000c014000d0130f245042185101b40240d407084018042c20600c05c02110000c45642d43c901a100040005024443c0b042e0319501c202c1b00d24840c0d8414200460040e002080f02d51070204a48101128030800f00800c40b2000b0000d074503c81800c1c81c003000d03480360400001c00c1c40c1c0c407500e0b0011a075070b2031980c3c0201c40d545000d00080ca028001800d0394901501801710414005044450700303145034040716000e01c01c240d1403c00801804003607621351920310811100194424032034000040490340710300c0048a0700d40c1c1e5080c0c01c500c038102c0700b01240d2203051130742c501d900362502d484c1c4d401b06210b0600d000110f081d20b00e50010010328107440107540f01e0348441c4080000b110b080283d4bc0c0d00c0070f00101410f007012030048000c1c1460140248603208901009042d001c22240d080949001c00381c4c0c0c4106202480d11035aa0644941c03001c02c00f039a0b00000100701080b01401002200d00542d81c6060300d0851004001c0c668845200d030325152141060349543c0b0a021900d12907101b8003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 507339244 1250 507337994 507338009
    0x6090703170a2309130203071b08040b190905011407020103180b0112140f0705010507030e040f0c0e01090b090409020111061509010806060907120e10020c0d090f060507081201 77
    0x44d83c510240070002c1e451101004121607600400410040513030152201c16100030120000b0b05511481c0b42001c038902540c1c0020816580c08a0030315007198502000c15090340d169258001000d4503400110f41407208103045d008001820805840154403e03440714050a40071008006c6105055441420040c03003a8410210054120240030521504030301a40c2c01c3e900d44c800401d41c05110905003600d54107144101414440c0103d082c80505000e001c400d6207110008004001d4104207034050401040d592010390000342c3e04030b04200c10741d401403504600391a40301c0c40050030029881c0411000d0068000124100400e0480d10300c01500c040141d01d018040b1000507501428140003030100b081016880300710305078842360a2280c41d8403109001500f2880a1500200d01c8001010150140401c0c4c0501d25080c031480c024503240b400141e0203044000072880a80e503445460311000c42d004140380c0681c600d00f8080f40820001d050103030006141862081001c0c0b420000340b074030010343e4842c00340d00c100f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 507340494 1250 507339244 507339247
    0xb19020a06090b01140a050d0f05070909030906110d020604080a140706020333010f30050709051c050c06120a23070f11100e06090703170a23 62
    0x110303c0001701407039060399000b9684000d07800d14000004840c03c00c8048003401c10a182060341c070031700000303202190160044031814050003600f40340040045445100342c00000f14000800c465000300441c000386142e0300f1341c3c0240407a460f0303510b50010310f502004c1002d080c00401d4500000038a01c007030280001c00d01803c001611780c07034500280301003510382c5805c43c25000c038218004002d803040d0004c5103042c00360a181c000a41030300c0708001d0b5204403080c00d0124182d00210480c3c0f0031501891120210072401c511f0074481034541c01c1c41501c6104141c01815404500f842d441160a6030300b10910385620f01820449041c051301d6008501640e104403841c00602000000f0068521b000b0700440c0183d1800c1500c0c0d407034806422022a0541c80b025201c003041000d243e20800c8168850040c3c141c0d040000c1d0140c07408514040414030040880d030a440c0014014640000c140603804650310302120740100c0c02c2c4541c0020818582c040f503100741000d4062151041c04800480d154042e0110342040603510107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507341744 1250 507340494 507340499
    0x180f060619021f0203070804060e0a1e0302100e0c04050c1e0c07060c0213020c070e090d03050919172104110d150c050f2107020105010b19020a06090b01 67
    0x450315140c1c3e920a1800314010400c0c0840d06601030016503101780c0007100050307007070035160326103080c00e18000d0094900001d03141c044a80c00700252143e1035040c82030b000c5400c020ba01c1000002560150780b100710854110307031884c030f0450400d40c0107241e00001e0344466601d440d22415004003060780100107074104040220300340034090000c11401c4058005d90401e46004a2586e0001c0c0009442081309140550049402194028100200300181400454800592400c0241c40390b41e8201c50340c0070304c0040e042034086080f4440208005408442410104031032582540302c0da0b2445400b00d940c02d40803101000003260b10a0301d003007112403440c0e82088040c158200750608101c1040303044121485a0106100b250016242084a0007007020680e03004c101649485800e0b6418052145107100c0580d0010380140e5050014040b4900d80b03294580400242e142c3e49030490072940709028000c15030078100305c20002c0fa443d00d07414600308200e07403044501103e11540e411081e5411030a04803034807a100c2005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 507342994 1250 507341744 507341773
    0x10c03032304020901171c120501030b0910020f03060405070c05030408030307140c1e07050406081005010e1603090f02060d0501080706030209030604061a060a05090f180f06061902 79
    0x5140140f04810b42c40c009001d51b007000c15260a442038045030200304980111102900948419018140012040142d580d50741400480700404907200c8031203028a2280319003541880c425078000c6640300c4205411030751084144002000044c202030188600c50341e40d40c0000300100020710160583d50040d48d01e07404c1840c00601003256000410252020901414080840002d60300d00105014074842c81c480038150789075400c0c4a490303006940c1040c1408004a40c1990000e05001581100f101c00c00c200e070f0740d070118030081c1101600c20f00e1140351485070300c4104070b109402c1a0801406800740000711f03050350303000070035a9112540910042d40c54000421200c0010b100c0a402864103060940c900a81e000010b61507500080004003a15642e0804c40c008500e1690800307004071002c0c0a250303850020160160507504184541849145400545000750800303c2c0448010b044410b07035448183c5600c0764460314150003d00107604080103000f01080c40713010715016040c1c0c3c001038010f0104100300482 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 507344244 1250 507342994 507343009
    0xc040b01030507081f051302071101030b06030a0902061612080c090a03080d0e01090b09061003110d0311030a180902070c062006040305030f0f010302010509010c0303230402 76
    0x2401414149800b0811104a40118000b80c0c040180180c48900c030084003551001d480554200f150402000814210000003507402403184500440394411080d0688004400f034a100aa6198000c101480403941000307107038210700c949030b2000309658200542034403d0b65000d00940c5040e5410102c1c11034014540e43c101e0040c5030001c400324402d510b0b0101280108400d4401d901c0300524950002900d107160500c81d503c114059000c40c40240030110720780c14086041081950103003201d00820020880b1102800c048000b1a51700c00e9140b19029000c0c1c0030012031912500055050000d80c00c2e2080c2400400d1004018009058494440c490241900b00d82042443e42140c494248104203a001148011a003001264454078203d00700151410084c60b0610426450000c18420501840100b60300700014610030348103c0741441081d07465012280c100d29080c403000c0c2c0499420466680785500c28040100618041d04000ca240100750041c003201a004103a86032100100f8028842107252852 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 507345494 1250 507344244 507344261
    0x1b1d0d02130e0d08010312140f0a02070e130c080606010c110d14010e1e0a0b040302100504032a0c03260705010603050f070303082a0a03060317070f110301021306020c04 74
    0x5001040501041203111052089c0d207803640180300040313270401506100b0803160003e407180003c16501420154000c04040d441c1c8401102e04c181c030442c012070648070024030588160b10513034a00c64030a9141e00d602840a0445052a8002403062240030101c2e010303c1c44440000001c0f40001181410303500c559007070803803481e8001481c00d401d04500c0790344140080e001d01101d0704440400001d80716450140d2400d4640460400c07271a04100403c000d040e0003008410f400c0c216028034400b110640d03400101c3c0030090110052036180c00020a0001c500c00c60f80c000400e400d202d00c0040c4100700100041e0003034001c0102180c9581d102c007424010410140942c80d14001410003e045460543c0c0d0702074140140102000303001070342c6000404c5400d50146108240c0000c3c0064181d80f0a103100c0010082c3c41940000d40c2d00540c003100ca00344000b5903200311003030b040c5c1100724161008910b42c0c810300444496a201940b40d0f40034000c4009102707451150400500c403a40042052024180502c13040d5840c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 507346744 1250 507345494 507345497
    0xc080f0304050a1503060e0406151502150a021b1c0c02150309030702100c02090f1501050f09030105010f03060b040506100e01121b1d0d02130e0d08010312 68
    0x81c08108520348400e08480f0035520362003d506202c0760f103090114000c04003544441e14402c02c2130f0a000600010783d0003900c81038511086000015214482c03105000241d245000069001d0070309503038000019041c0725003143c08028013610303101004081903da562080d0340b0324016000080f05101100b00d040782f0500500e00c5003803411030b02c00c0b5600040c0b80c03109440c60f42103000e840040080c3d0403880900440d00c81903402001c03507000b40c03c0170b14020b00d091260380d070480c00f45400d10b02043d4842408a46140700304a25071a1310322203070381c41c2c00446140e00038042082d4811018401c0c119103690030b00400d070207050b054600f880301500e0350404000b96031019000c0c40c0901d10305018084691100044101031460304e0910001d0340f410040105da05a030700e21602c3c10207910302401000400300c8403a08800749142d0b076450788000481402504c0c030140400f01e03002c1d80105020203050060500c280c80074001c181c0e428000592080d00703d07010381401080c41100c5c001800381c00041c4204003030100d182503031001d10b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 507347994 1250 507346744 507346747
    0xe0f0312060d0305070f050102040f0b030618040c09090503092e05070210030b0d020a03030e030c04060815071e030507111b0f0a0506070803090c090f01060c03090806040c080f03 78
    0x41e0b483c09041c80c401d541c00038000520910b0740b10140b00c802d4044a00814140110040b000d82e0350203112030355041070302c03940c3c8211005103c040080e1003d60056000303540115800881c1880e002c4820014010807108907400c1c04140403c080319500c90640b2b003c459640418001c503041e4800030382e141007602d01040028403a0501c100001f613120a4158403114043e0300740003d003005100e000850041b034000c0002e600c40d24221001c02055071091254a40ec2e005030200c480b62105a0200070a9800fa4040c0b413145600c03c015034101803480c13060f00c94001503642030002c1d2803403480303810100b50070300300c180c900229494906001055a01c41006401412404050702c024409160120305400c050b104943c400c040884420100d5514801070384010035000b0300d030580d526800e1400c501c407904101e0300c0e107016000345090781c52107041c241e41c4980700c1d5403840040e00080c2e0910202b90b07259800244c042d803c200d410300000c504000f0800c059400b0b0340c01620641229454004d41600d0207220070b1000615410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 507349244 1250 507347994 507348019
    0xa03020318040609020705070e130b04170f030a230c120702010e1b040528020304150c1205100b0a03020d0b060a110c030303190c030e0f031206 63
    0x6011080d01d40c40c50104640ea680011404006000b42400d60401e5071118400181350341000f20010798901140e04511004145a03a00080d44c46c42da28803a001624401e095000540010051004501c461490040d00360400310703001d080c0c80d087d4001322901c4c264503a48079049011038000703040c141c7e082860106035410f40d28000c000030200e40204c03c0103000da91800d002041c0014000c0d04641e022440070400c9802d460b07103c0c01201030f60542c41c04410301441c40d08000c110348450843c07103410350b021880303082c4501106c401001d6000750310062043d21850b070b50540001e61031404d03000707203290350b011527070780d884080c40a2200408507a005041c2c500583c20f4044108032460780c07081a140e442c41907090058030341c521111600c0c09011541f06ea1544424002540c01c58240c200300110390b00e4116101701c90702070b840d190070b155582c0b100b0703208000c0444c401d03000354034107100ca40c101c00d41c000300c03514011039200c42040c0c00d94900b050582c02442e06800204280380c052509110b180d40c000b00c1102d01140c0c0700c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 507350494 1250 507349244 507349247
    0xe15060d1703151e090907031218140a0605070f020306010303030b030607030902091902040b041e090b0102070e04111021110306010f05040b070c0303080a0504350d0f0e0a03 76
    0x4260f01c842c502030317001d03040040c1c011481400244000d54100100a084688950009100c8044210080c0c2c19062111001c0b5661420410581e0400d07006800d0a050740c0c140803042d5642e80240e0300851349250480d14080068401303002950003503110342c40100d1840b001030304040c1450380081196042500d480f1003080940c0e9039106c7d95401c0169040c061348601524500344010f84101e4010b408521000200061422102d4481c205000e8070030064030100b80d10740c0078040c00e8810300a01c4500680c0840d10a000062090030002c0e0494803491072400420604408140c056910b400c440c00440c00740f510302400b50112018040c2c0305420080c080016901d41d94001942d0700024102a0402c4406072005251600440449000d8200b402d441500c52a0f076140103003852011f4017044002030a104049012096a4001d40d401280e0144003c40c1100e6a0311320310710040d9400300b51940303d41240c1c1220b0313070480701b141c0101503842410002055800c564844075060f04d2002104ac02254411076208000c603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 507351744 1250 507350494 507350539
    0x114090402120a0f110108010f061d01120f09110301060b041205030705120d14070813060605060d020405040b01110d030b0a0b0a030e0607030e15060d170315 69
    0x40da0480b400e2407880901200d040c070b04407856000a140c0c0c11800c2020007403145844002d1040341003640c54030340503038aa40401c000500c540c03241c1c60201d2160103035907109111401030303410b014406140085000268001000a0714090016003140c1652038020200740440590307405c1c800700c070aa0080c00194a0b00c004a40d0502c12442801180c4440800004c100082403080352080d940140c02c9034080c580c1c176501c1c0304c03c5500c400490100c051510402c141414443d4030914801d072a10340340e0381d8155840d101d104075038a842147c00c0301c11035034905000c92155900c101070500d1029030f050068449080c0000c9c00110b8415000450501134107034916079072500d00090000526a1504c2c0c0800c80c5511940810360130006604500c20400300440c0c42000241c0c103a000f142460110700031141c090325040b0041c0e0031201d88024482050700010a65000380310f40b1080a9080680945001c90110f1030762211301c40044000e4103804c0c44800001441140061203000700c1d03841000711980400001c5418a100d01d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 507352994 1250 507351744 507351751
    0xa06080d02030f1305061201080c0913030e01030f0e0a0201020f0106030c050d081204030c211e18060c0311011413060b19051809070303080912070308040308011409 72
    0x801d480020303807020302180a4013900003054081d2285482d11310305841240b401d1024007482c0040d02c03808418148a00e4201c0083d030080f410500d0700c0e003000910740c070304071890701181400314181a150701c107111985219218202d02904030401519281c00584002424180c50a0364442c45038140182407002c40c50184e482011a64100c0304011001c1041c41e00403001e00505031001c04404a85042006041e0405d507840e4680d0701c2400040c00001c1c0303105100aa44940c2c4d8038800000360107050f000c0341c0c0b5031014a000d0b10180981845070b0a0782009540c0c2d0319649903a044240055201590340d0105600903000560344c0d032040c0d0003402103108406aa861400005082078101000107040d0010303c00940d0065460000203800307005005030f811240d140100c0d1511a6a0240191000720f00d0a042c030b88115034003604014015100007072540d14116502e44014240310072900540032000a42e608150003040028440d460306e8240d071419007400741007514143e10440740c7d9007444110010326511041080da0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 507354244 1250 507352994 507353017
    0x132060603040f0812060906060a0207061b2009011521141e1003020904020907030b09010303112b030f1d070302030c010c02090a0908120f0a06080d0203 67
    0x440e5625420700812403020f1680251a01c0e80001d501386500024402d0140310720003d44d44204151162814056140b046900c61030041e0004903045c80820b1280d0030601919042c001c8804818a05441d100810484113506413000030100d591800c07a410189809030040c425041c2c80603c195903030070060305140b01c43d40e03030ba00140281c0c003803d0007241490380441d1058014100d68080c9180c03604011210071403030105040340355680400120813940706803035078003541ea0146c01a5801c0e215036007400181c0202a060909150322461000d8032601d8001d4114000c1d4080e90762103a00d802e5042c045800e0071011400c1c1010360070000c407070b99074001d0128440a08407072903150000c0c1d90b01044214400500040fa10081d000c3c113154140f020751000003401d40c06490084003a140c10b140b4a0005444081ca5420000c1d00900c2c81c00009044844541c0000c0340340340580ca00300d00c0c040d60403810b114a010101c80058594030403406102034600b85210310b0000c4c24400f030003000c04002c4003a0217907581c01000d03000103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 507355494 1250 507354244 507354247
    0x30105012114010608061801050d0308041103010c0206071b0f030c030e060a17090d090b0a11060421171801110d05040516050a140103180501320606 65
    0xc040706a0700c00d14203000e035440c01c16142e50312118001c0072140c05507090352140620001c0f0a0718201d01702d0b5554100e8500a100c00d404179401d036410b07907030108028804e440030000b10740700c1d0515803004e025244c001e5529501500040c038094401030f06036068100e1503581142d1207245940040c1401c0c1071085055054103190080050501d4101c03141c182c1c00f102c2a402c400046604c8121a4101c1c95010304200781080c84502c0341d5800112640d03c4102400110010703080700002c21203510b00300014500a0300034030700210b11903c600040c0d8a403e100b602c080b900300b004404244200e0403411800903128410b172809080910a01604441d840c2c40a007903400407440583d484820307003601b54400d18106c5118010304d82c6400c0c030140e00100608048405035030030700450700001c2c840c83d01c14990b407040d03e600400300c4032400e00380800e000c2101c030301e544c20074103241e0780e00404070070701d0302d25201c0203402842070b40045920540a010581d01007038107101c207010009006101551a041c155505a0018090b5500d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 507356744 1250 507355494 507355547
    0x50307150506060f0c0f1506100206240a08010c051b0a020915240c0706080c18041404060605130b0a0312020a08030f0703110a0c0b1008010c050d0f0203010501 70
    0x1b03040c130610090503c02c502c686103645011001541e03c01e445900122031241c000c0080750400d0783c580008031800c070942510318615200100c0c03020011a000c0d503002e0306100c0200c1d1103000359402c5801c0316200c08086140481c0781e00c1c43c5c00300e0751114a28544850b02901c00072030251301080069001600e050000041100038280301c0d03e60400e0108402c8490325000c011107000320500c0200c0e40176000b060654001e100b8045003c500842c05107000f0265850b81c0e0385848085100150400c0c101b00a0035805a06c0b00544071a8040441c81e080c0140c1c02880300240080c900020070000301c014541e0300d2001402c009020404e9583e4052100490340c11211103035030140d0b0914201e050021a61700240600c01c0401802100000725002c184542c034207803410000070503100901c5c001c5008421042c070002c0c054401031400205c900d210143c01c07520740c51070300d121b0545074160765003503070190704000002400105219007045240d0198910b1180081811451075040c0380c0000c01001d00d080314203a0074130b40341000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 507357994 1250 507356744 507356767
    0x308090f03120403030e030601050109080712110607031e0f050706020f04081f0501060801120809040906180204050a050606160305120a0e100606200106080703050307150506060f 78
    0x18865004116801c0c0c0c3d030396039101d01d03015101d00b00c00c0d801280a881514004666035009964a03426251000018003040e444c00c45405543d4121160843e10040013010b5408241c9a50b800307844050b10988481b80000404480031404a0354005290f04014135465000d80703164000c400c480105400a0300566900c04c0070f100510184101d0b886000b092061055401015500d50038142400a03911028005d41e66246c0003244c4c401420300803a04900118409a0002499200104a014009000400c499030103403140011a02c1c4500080400d820402c804c10842c13401d403090a07802100800c080110b401e101e0b011078030714084c01c0d5586000500211340041894020030031340e01071010203c140c00c410b24107054001c0141900c007184100c3c0303101d155024110300000e800380c00141c0b0300d0f40c1e0b54100c1ca00c0e0080001111000c2c003080383e100c155079604001c0b900c0354041c825400594041c20007141d540b805894034007503800c000c441c0c0f084000d10f40001d012450b0303528001c41e40c1c4100810204e0342c51740300c00c0e0702 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 507359244 1250 507357994 507358003
    0x1503010e01140a0c0c0f08030108060a200c0c030f01050703062702031e04151109010f0318150b0102240c030705091008040b060d0c1701110a0801030203070506040308090f03 76
    0x101900c140d5a45030f06001f08640c01d80254181c5c0c04260603160b00f515000d0b0f90009848d40828141000604d1500c14020050501c01038641104440300300c030ba4030750081d0f02190800c4c0c0001b940b45020794494042080c0c080e01400f4101c02008081401c04502188101d4203141c07009034030f140704010360004082854084913014400d03540010201882d1503082903d1320301c040160304613801070383c1c0c0d061001044404440c03030300340c961040c4103854860b029040c11070100c0c000d0102d56103070070b441d4440c128140007041400d0341c616891082e002c000181142c440001905c3d280344441b100501140c2a911402e84040204640b900100000d001c140c5a466801c000c2d07403107004c0c041c80580c001c1403240000c01070f194802d017110300807801141c1001b0640c44403028811588009080a0a0701d483c0b030908100c0340700070280104018003448000140740c008081034982941c40101c4407000109000018000c0d0302d8240f202400420741100e000d1710f0036242d0341d28082103005801080d4814546c1d0050311030301e91000e10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507360494 1250 507359244 507359267
    0xe03120d0b061303031b030e0904020a1e091512060b0307031a040c052d031c110d0302040f0e0403020c060a05120a0212011e0e1503010e01140a0c 64
    0xc2c5010b459210380111880c07082c801d44419800101205e8080b1901499001e8111403150140d5407803607030044100a1240104016000703e0b000000c280b4000340504d00c800e02114508a2403803240207161a004541d8240d800e50300c040380180a82d290100701000c2c1c80a0081c000a9004c01e0129482000d080000c0c2005031990001c0d18008035070b0103004030408000ba88500c683e11610480803070640311400d11281203915098900068110749444402040310224200d800500604a178903891030f2080c400000340c402c0349900c010984001c240018154103000c2c0070211a0070703140c00c40c00d00c3d150132150001242c8038070a03030131100d0016021400345071003807000510442014040c942d07220f805080081460344000c0806e545450f448012400302c4029000322268608401c0031a003007a402c003000480140c40d06a04000303030007a0514000b0f444030300e00c01ca451080101c0320800035a80401d80c249800d4030258007010703100e64034140790b0303030890802054490f070800280c007000900b66120030401d51340c01c3c0107075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507361744 1250 507360494 507360499
    0x61012110a122405060c0316110907110606010c02011e020601090c0e03030a1b060e01050610030c08070503060114030f0603150709050f06091c120e03120d0b 69
    0xd0a01c0481d038218000e00c1140c10b10410030000f15412494001c8511040840c510b02e501001000b04010b00d8030101030002c5030850302c10f40c3d113018031015940c8a644001c03e0101c0780414a4103030313100149440c11400354880c100341410105200f0300c0d104282c4a540c000c00c21350600c000c0c07081080c15648502e04840f68204e401c0c0001059510520019564080034441d44a04500741000c04101520400e21304603404000b600950621450103400c2d100c0100e0030621400e4040400500c1001c640c5c0c50182100f9041c07038800007d183d00b8248140103402614076100c1e420b05041c00c007010307041d940c003800c0568840c070a490116102e45075400101e030011004004152511401300511101d00c010300e14490050b9021012607988007c110024001e10b582101c0d9071010030f500d503808002c1424280e20019000b0002018585006100d000094041000114400185034118401010480756040005403180c00341410303030503e1100d4000075590700380c0f0001212a02004a000c16180314507400005986100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507362994 1250 507361744 507361747
    0x14060405070302030105061005040b0a05071205030417040530010e070510020f1504081303030203090111010203240409050109050303190212060402090f04151d06101211 74
    0x58102160741d4086800180c0c0b00b540390601044403803400c400c40c00c5c284641a2195410145084d0013100d0350380011040c103040c0700301002a90000707141200380a0b8452555120355489040c2030809aa0038880c140120700300b6401001b00313101c69543e18541030701c0d41060600350980700c588480c2440040308c62000f400120760800280c0254054007043c10300030345000742c0701c0c1040f071016903104076a02c03807210304105502d030420f4104d0911545404e4400c2d5005008001c26803400c0700741c03294005051916401680141c001040301c984070760744664821812207800001758118248522085c050f40c400c0b03440030b0040003602c4020202c54665400280709550008000c02031350082d810000d490340d0044030b1300034000054404a21856440e8401c0da004e84c07241c4861098180d4078102400020f502c0145001d503c0042258400c1c525a903e00668204250548089250501e00501c0d20180700d0b00c0f00f4917484400d205400c01030292101d044103c0144042e28016403864032945280c030050000c500b011900100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507364244 1250 507362994 507363001
    0x1a04050907050f0906010915020f060708150a0e0c0d0f0e0304031704060c080f072102010f090203062d13030f020105131b0b030a0905010b0603221406 66
    0x800714201d021540c05580740b40800583c0020482161802c41d051030216115290500a0b05501c0007201d81078003490040b115009804102d1074070700030088030354400058800f8100a03200c0103045840d40c0f40b0000788c911091090a00449002e61032000f800b10a5490340801d04860742036660308242070003208810b04000c0c1040c284099510795001d13010540d440c4112203504040c2e0700280c41207a0403141150703200200c01e0240d41da02c008036482540b45024000302400004c01180c4c9241ca0690504184008a0013148925101a003075603088401010b0b042e28100541001d610040713851680f020115070081710403140c800e0110320b006070001c52009680c40c03207001c000040c1640219106402e00075207501c180c2e046030440c00c03402e8a008595120011881c0e03200c880c00142a07213254002d405452a0f00d0310640d490304024201c90700200e4045010703503102c804603c14000284104a050101a11420700e0340c0b41c0094400e4201403c230b1b04420b0414020941c483c01e1214880c0702003094844170003035800c0c606 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507365494 1250 507364244 507364261
    0xc150902012a080f120907031412030a020a02150702010626030912193c1101050f0406030b120303130311070302061c050105030a02131a0405 62
    0x2015110403804501c001d40107030b0034508032a80300c8055040440c40440c1901040e91400880c0d000601c904002240a1044100252641d961684948000c00090400350710b0340c02d01c06403101d421900d1882e290003000c84850310200060860f98416149140035075200e02540e0101c0c5014071550542180082d410107009005da810340040c002c90300d5988100520340490300300c1076101500d01a414041341c0c000c1001007082d04010b00707201700300d0900ca42075a50644850718210102100040121048904080d4100780040c1111021741050b410310f00881c1d81400c60007003245440d101c0d440c040c5c000780401c3ca035281a6807040084a0043d103100c903945031581c0d0b96500c098007800b9400d481e90701c0350301d102c0715507101280c1c00030a8030701c1405198001c0c0c01000243c0c40c1660715803c103801008050041c1e450120160700ca031402410039100c41003440400c0d49030505031800329071041c0c009912a80001408202507560454a000101c4505c4000101d240030044a081003c03001216650003a00b031204201c101e1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507366744 1250 507365494 507365501
    0x913150807060210060b0f04150c08131a0910081305070b0703110c01050922020406171806041403270406050306010b0304110120100b0607150c0c15 65
    0x2138054020601c1466190280d0000c503014580260221786418481080b010141c010746d50440f20042c20403010725186500c40b981c490348900003880c074003008881c0420404250120000d100d1405060132410200114001020b020a9070203403c1080310381c901013816112201d2602000c03071360007003c843c03420b656103a14100c941c001c108154041510b10505c0001450045064004508169100740c0792481003402c0001504001000402d44207000c25108070810075440107002420b02600c0b4654068003030600c090036080c00a052012201c1400c0c4110400c0704006429a007291f4802140d4015004420110b031450054030640c0900b0303041102001042c0024501d03019280d1003d441c1446107039211806e03d643d8800a100304542d500007000003d01040410000c040360302030526140c140240c440c5242c104d041020120300d030301e0b42c211082100751a02c9601c61000d0300402922414100122920b58180380790b1942a40d40306951980c0503d03e01c0c52003881010045079100b018080143e20ba40c1011008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507367994 1250 507366744 507366763
    0x206070e0105070302121b0303010308040f0803070c0b030c160c080d0908060c0904090209040b0105090a06030b04110f12010504050f030403020a1811030c0705010507030209131508070602 82
    0x45120034110940e254812400c50742502d0700354005007054180c0c3d000150056003c1c900caa5a032403c960307401d40c242401800210f00860084030700c15100c43c1018418000c0c1186507012a109500402c11800012015880740c0201e41d5880340554480c1d6810001d0a0705d441801c0d0100074500104901100b04607100c8841000e6511708400c40d01e44509490b402d441a0346031707000b00900c40d800b020001e000c804201005100b030903c00380c008034041c1c0303444c1e0100f000c20000362811a962001c2d040144a54101464213940c03044001c802031043c0e0740b039526601c0c1d505001800240030400c100008896580741c050b03000f5030005000d00710517a11405401c00300d00078001524110b440d401400c0b20b000c040745000081d1000d13203400800030b241c0030303241205010a14000c141c0e0703915060348500e50038920780064809180320b80103023680559100410701d003d50840d10014070340002d051052007244155107820002035646c9070381000000385110101d4408000c204194803800c0548581040451202c1d070100340d110a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507369244 1250 507367994 507367997
    0xf06021603030e010e21041a030a0e010504031b02032a0406080a0302030405220f140a050c040506090406090c022d030304111908060924040b0402031903020607 70
    0x1140540340c07452800d135031007860b11700b42542c09594001c1624660040303040898809444443c602a628034400300c1e083c0c0d401142d4201408080100714086005000b8200c815424900810040c80d0550780a4003011341c604072204009240c08a060454600700000001032030403503e6000d80700d03803007000ca0120110410006009034105032001420100000b051140d807075140c2c001d5410a03040c1000c0c016444449403c01ca88407050340e068240200640c0300340b01040148074408184c08504160076000500080d2110304420300d04020003084100390000d031016030300200c5801b80d49011140004001e000b15400440751949442040c5e40c6083e000240820400b814200d8412407116004805070302418000b150003c0307400c04c100007000036449011032001010024045c2e10030114a0700039000f00003203504607174030300d5210105005001004025812400c840b488046100031410b1084411000000e00014640340c07048020404640d002d224600c41090340e400c2080e0b101d50320f1304000b556044169002d60 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507370494 1250 507369244 507369251
    0xb01030e1605010507050312010602030706050f060108041b0b181f05030f040204060e04201009050906010e090406020a0e0108040203062a070b06030c030120070f0602160303 76
    0x31600080860325450040070301035080101e52801d40156881d91010764100c2d45404100704040e4692042c080c40e0340a8607240d8000c603128070b5589092021514050074600b00e06454500700321440e1790161070585e103e40d01120304d0480c4550119001c4402c00c00381c002e450403500208149a4115a1410f0141117100854000e61884d6080c11071610088095400c0c20000c0c0040001428501d14464001d030020f201034000a103050741d503800000360100517201101c01904000c0c42400385081600b0541509a003280c3c032100e14294100d02405070000d5104060045920800150b0668007655130b45100340c40160100d400d510f03091a1090095110841030804156030b401180f0455101c0c0003882e00c202d038094002c1c4582d454004112102e0020000030161741d410b4284004020384501d406080f58610840b00c80350300d41010700401d0300740a00010b28600980c07404c2040e401204221122050402e9803154480c1d5904c01070070700c080e0781000d1000c017400ccc0500000c0c8005012030803141072180c240c002e83d8100f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507371744 1250 507370494 507370511
    0xf070602031e040e1819060f0606030507170c0904020a050703020f010203040201050f3f0c0a0f12061a19030e0303070302181206010f170304060e220b0103 68
    0x241c0180c01240601005031401c007001510b914545100152410150300884045406c80840300c2c4d504d68501ca012541d80d80c0300e11400007000307654080d10014000605003031240317203442c0000503e401006130030800c0604607240030500b00020780f0101c2d0006040a0025580c0f001c80344e40c007400552000314120014420360301c0d603e41525041c42a240200c4c4d059680920741030f5501d660142c0d40c0c019004d0404282c0c19407103010908208500d0744244840b50b0b50041a40e0745030a0303c11201c0f050000d10103103012504005202080703034011800c85400555040c070036103668480200c06c008100541014121124402c0040c2c500c03030900000d8854034440a4100382c401c000b28004a080e80d00800718001250302c00e0010642d843e0294014003213041142e0340c00d0022a020a000458112000c460032242d0b410a40043c002040340c612443d025161240c04004682d900300f1f402aa00c1c45244a044200120141d1000682e6074050b90300f1340c800320001a484403042c0700003125000302400c41150780482d02d0174442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507372994 1250 507371744 507371797
    0x90f1e05061e0105060a11010f05060a05010912061508070e1b1305041a0a0906030302010c0507050303041b09020c0c1306060e190e070c020906010305041110020f07060203 75
    0x705000c24001c521100540e46007005014854002240d41b0050140e204448501080d00744074450f41034100b8200400c550030aa400d11820b0452600460304220b407200c800d021080e12006010000340d0f0000000461441c41e012440c281500ca070810040782c011614001180c01240800b940a5120200031034507210390400f50365450700c0340c4500035007540c1d10580100f245162940c4480d101c0108071020071410000a03000074006c20060b0010440c56507110303418002e00d90709100b0008004010f041c280c2c60030350252501c6569000040008080410f0010aa10310024603401c03100200041c103029511003015260f041d07180c1030458a0103018a1041480e100001d085016803030454103103841e29031810000c10244100b240810240f03007200880090002240203130005143c0c800c100543d10340b030034012148100401118044c000030704040c141024070020030344804800c00021001c130742c3c865440c482200264146008030710f88400324080d40b100015219004002081000340005203002c2c0d4903101c2c4038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507374100 1106 507372994 507373021
    0xc020118050a15060e01120602040b0705010c11161403010e0a050a0b062403071806030e0c03070b120a020d0f090b060919090f1e0506 59
    0x2c1c04003d02c000104602c2d48034a00c01c009101d09441c0007400503c440d0107014040d40045600e85d9103041007441c0e0304850082542d0b00070551117090a00700300b030080202c0013004d8003245d54807810140b09000032a11a80d543c2c902c20211040e02e0405172444c0b020794211500c142c0541d42d414450307080040410602c02124401c01c01010980b0091038440c0407041e000d0b110030b00603100c1083c0c5441d00c8004011a00100089059498a0f0f03a04c090045682d40446d04061000e07492914004c03c0d801d80c10707000075103407000c29000c41e03408107082000e150f0b075419244581e1550040c18403126441d5885105410b13002213103002c000d4207040309058508225200c0c42d8151100c00d503584110070030040c03142e04c1242e000204403031791710041c0303003076184141005201020709414594684e0610104001901c240301080e030003049070080c000c140b1002c02c0c1c40c3d501c0060700350f890703204050002e28070f075000d0706 = true := by decide +kernel

theorem cover : BRFrame.Cov 507194244 507374100 := by
  have h0 := BRFrame.cov_init 507194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507194244 ≤ n) (h2 : n < 507374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
