-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4396
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:28:48.188041+00:00
-- url     : https://prove2.me/submissions/e9a23d63-36da-4640-a36c-dc1986de27e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 790467625 ≤ n < 790647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 790468875 1250 790467625 790467653
    0x20d090905040206090a12140105040201050a0810080601080a02150a080705070609062904050702030a0e031f0606091707090e010209092a0315010c081b0d031b0c 71
    0x1001c4c03424062085980c40d03109a88000f003007c889008610902418650300c2e0021031540c914042e410a403c01000d82d0b0020708403407030030741c0d02e15004803d90358554544011b00d600340c10030044d80c064640006014000090300f8500300e4000c503442c080300d00b04404d04451503c9860501004620200009a505030081c0041c00d0400c2c010b46011900c0392032651385c5000c40d015034420700e8034120000442c440c00c032403510740e400621001b41d03820009401c041a0195503402907510f05403c103e2560f12002035510144003800700003095800d146940000c0c41c070420702529260140e80d0018001c4240013640c0b03610040303c402082403410252240703d09001050000c0d0890000c2c026040d9000c00482000780c640d4201d03588603644468030f80750200041d0f03910b12460484a80a580b140f80184144507140101100220840c1002d090070315082419260048503405007188180740e50715a24a4111403100108069a440086079130411484004000b8100c50008040c140320009030101101c0700002c0c14414a461 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 790470125 1250 790468875 790468879
    0x309241404230f070807170609070302091e010b07050105070c03090303030213080a110f0f0105090d05070e0a0209040b06070305070b07110304030507080d050f1207031107140d020d0909050402 84
    0x418440c01c0003e06250801c1c540c05038003079038000b02040005681a5848014041d10308007d46446c1c00c0508005a94040318040039100305d800703001240d4289810700d05a0001d2202408a501c50341e07441d25007581c182c00c1004161419400c0000040115115545140b905a85501d45600043c1551012070007074015048008115170140400b1079071010801c034451200d40709150f9014180350b22402d110042c8510464940259031655a440b20750b03810038299a601081544d088c25000d00c28182545020350980c02008004400024041d402900c0d40042840d801c0c192802d1000f50300641c24403501e44140c03000500050011b00c600000240f0b401c05058100703d036450841c0380b100b200e040041c11a41315900482d1980d001000400c6412403d00043c0451078441c00c0041c03d10706d4000d0846900d110740521402d030342084d0303000902002d00030351008803804800c03880c00b62a42401c5c604088100c8071f40942c12120b200e400041c6014a200140314080e11103243e5403852080d140c000680060070000c3c2c8100e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 790471375 1250 790470125 790470133
    0x70b0402010e0904080c070e09120904090f030914060f0a11150a0c080603030301030305090603040c0b03101d1005010e0d06020c010b0112020a050f0307030924140423 73
    0x4020355104079110f800395002d101510b80c0c80306c07081d59451a014032a03000b45480500708003080f506d8400031410021401c8428040c0340d035102140c00190041901400080c0007400007030004041c503034070034002c800380c5887c03181c0e81c1e00c100c035550308204d03a40c02440e4186601003420030105410354481c1c1e03807045001042d40222402c07130030b0f18040d000c5011402c803030000c0c61965400240c802560710140151300300800754040c40c59541035440c014200e20841c4c000038003c1c24008045010000d600c500000204a242111912402c00603084c000760610351144030b84440300003001e0140ca180c040441c41c0940b01c61380a08440f50720301001581c2c44031540600d641e0142840c003011021546900040c2600b0100900004040b14104005010051400d01c200720b40381c41849806083d80d00501251060f0312182007260f1295a0148110302406813080001c1822605580c000b11070794107207144004450f04210b0611848800707c02400000104546c080c061801090050310481c1142602842491043c420340e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 790472625 1250 790471375 790471397
    0xa02190903200319140c0a05090105190f03060903031a012f030c0c0a060c050a03120612060603060b04150510050f04060f0806040603080901030b0f040903210908070b040201 76
    0x80520f68034244805d8503070a21003c400380b010007045c05503004800c8101d5408060a00301804107582500501407503003c3e01c030350401d4001c1c850490030760400070300c6480b10b80d442450300c0e0300d4030b0b1001d4070302031904034042800c200802d0520101c508040540c041c040e544c83c1c0c01c0220341c0a102c4007005541640b40082851080040a2a0800c1c4000c00080400720000c14035545048240300c0000c0c420b5104200700f10104100c9000140041410041c1642518005204800c4c402d0303d03200412040c0c2c046036401400e8468981044000c0d000107040703070300442c0304000345030390001440241c444011040000d41411a006d110324607004030040c00e035248501e071a074240016100c0700c5806034450381044002c204500328401680c1ea0014070355610a030b069400b48000b82c91030303551205030b008030000c903414540c0322011401991284010981e54600080007484105503505000c5c040361f171362090b40100201e2106107001c0130a0b036405500000e5a001c42000d01e01070303c50700c8610801c0720180c4103c0c100080c0c4001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 790473875 1250 790472625 790472653
    0x8010b12070c0206040b0708030402090c120708040c0f0312030e0133050405040f0b06010c0218130605010914160206070c03050408031215101b0206040e0a021909032003 74
    0x1c3c060341e51090f888c0550303a040c035004201d03c10500901c0a41106400c010038074056458088042e00407481c0e0030140907503202c0740b8054816412503003000384076490a40e000001d0084030309035100c0c1c0d0005502e007001a03046808981d0309880365106140344a031a013031210b1090941a009030290742c440707150001005501c500014080c0e400980d010781c1c001041440e00c1050040106c0401d4118400342030a00750748459a0101c0d810074030001d84122070200ba48002a601e0000401001c00c05902a100b0031580d80c40f03100c20300040030741d081c01031180391074070300002c0c940e040405602400c135005070014042562021000c44100130380400850801100303001c001200c410030000341c0b0035044110111141d030729011070290440040c00c00e00714030070000c0d001034407400b5070070441c4074071200340e900048070407036000d800030417031510032680080060000c002c10040d1055282d40a42070700c11030803540c501d00401a10081b20380c01c0e15400040c007859551008041080914a222140c10001406942d408404415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 790475125 1250 790473875 790473877
    0x3170d29040c2019061b05070c03060203040f060e01020d0c02150a0b0a080a0507060e0910030303230f0103110d03020c0402090411070b012103020c0402070f02100e0108010b12070c0206040b 83
    0x1008a0340d042c0c89050511040a4400c00b801c018803031458050308040403038032502d680081d27510002d440d240c1e00002007414448242c0c1e0a00c02d5030340100040c0301030120b1800c0103000b94441c24076004c95501e4520f8280016101180014402841031003601940d111492a680204130044001b68850401000082c910b8010f001740000780d4044c10150846519010000d400d2038181c280c0d40d07214541e10401c0010326803007044d000082c0ca405140001d100b8005e0150720280500d0b0039440c0c000721503c0c001708103007902d8001e00c0506980c0b01e41c1c0d18805181116040c010410071110f40100541c11580781005613040a602410303180e28001d0012820455081ca9008160b000c00e00c00d41c0c0c820440c20052007140c1ca00a101c2c1c80200400b0322400400440361002922580d028400b00c1c81150009110780a00032070100031046d05800901c0c461010785003040241c03240c0c2113004038501155100e4000a885002842500d00c40020803890704182e5803011422103010080080072079205406100114540b20090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 790476375 1250 790475125 790475173
    0x31e01090204080709050603190312090b100501030e06040b0c130b0901030c0203210a0b060c030408150f070f022503032703170d29040c20 61
    0x3440c0140d603641480307902c074100950380d0003686009040800b801070507203000070030961010944038002c5061302e00e8030301181c0341c004c180b10740070320300741015251410320143d411399134003c3d00c07208142090166503a0055040e07a0030046030398219000400020701058039100c16581c008400d0500302d00e449080b00366451641d1898000381c04015000c2802801960540304a0007100400d000031802c00a84c94468240c8203003060404405021880219100d11442d0300002c0508200400700390f2600d0072018410350340c3c1c0007442811282c1c030403808041d000034002c4070114002c00b81c410f0011890354400e00240c68045080e64007104500c120400b03080380c5071807441800d6404a44201c0c810300e0610714180102040400180e6640000204402e901c03050341e108030b0b01c42201e5000141960000b1710044e00d84c0140511411031115a0800b10320a8001c60170051290081403000c07410190425070609010845007001e010700b000c10002180b41107018440803560140c5054541161000f807410004406240c03800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 790477625 1250 790476375 790476389
    0x2301030209040807080d1a011803150c110d020105101a0307030b0f0a060809150903041703130906090f1407080603010225031106070c08280c050601090c02060c031e01 73
    0x301d10450039030342e44008900d00c543e0304c90800800d003502b15100e00201e89078806080b0f450f159103a56100c80d4502a15881d40707400d09543c180c0302e0120f050390029005e000205c40c83c001104c00142e001c03d14060802241109030703413a450203400c41da81d280e403d80040094a00a07030348048028031910131540c5c1d04000101529040c0e8a080141c10205215490040801c00d00700301d481f4100c00f001650680001950220f403041d03909600700c950f0202c41241507100b0380724854018400d4200110300342c40250001030803a01c1c0307c20300708401c062019a03802181c1a041c100f40904030350704040f415451292403d0b40c1c001800030001891300b40c000303004a0a49040241c46070040d84070072860b006268010b104030554043c58005020f061829200040501c0c17107081d0000d10740c6002042d1402102007818000d0242d82c04041001d4980f6a8000c019126103241e0004658512401002007000d0340710b409020382101d4203400504080c1c4412060107029080140300e40c084240b0980503203e9010401d1015008000c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 790478875 1250 790477625 790477661
    0x61e050a0606020d0f120b180a020405030717030904050406270b0c12131a0906040606050609011d06090a1d240415182301030209040807080d 62
    0x181c1075001c4d04180001c0852828892001803001007190002024140b03d115180c0005114020800240b0030741014004104030071081002c101d44000c26074000d105648049085840c885d0380e9041140d040301c002210003001e41c005110308146414a9001540c01511900340480d00f100b20703816051a07400c2c00710140d902c600e90100d0140c1030016030030555800880c404005440c20b102e10075440084607026100c4600740d82c002c0c0d104d0040c49102e40d805070301e159038031500b0325050500c880404c6e9101030680d41a55861b00d0b0410001d01c61800100311890b4a1040c1c6400c96411000c44004140403040e180082e04100d00b08003200b0143d84801488001d4041a81825100718909000780345c014002003440e1601d8500c1420100713070300c5400028400741c00d030031580494a00201c02c1c804850710f40301d9010480580d00d101e40960045040e0700b000e45024040d646480c0e03041148803803041150800c2c48080c1d005048940814086400d48004005a900074040140b41114580d030366012691007810514003018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 790480125 1250 790478875 790478879
    0x210021006091808030c07020306070f022422050609061f050f040b0f1e0112200a1103031e0c0304120806012001050403080609040f061e050a06 63
    0x554801c1001a040303582e0100303c1d664904420380c0f030384044403802410900001c400251240400340c00c039601194003505860003800c0c01c81e4054883c038840718203400176016450040c0b50503000b220604144841e0455141c80b0b036100ea0043d4102001e039444001c0b41c44100c40144000f18008200d05402640380b035004100c545407481e101c1132840c621103001d900e4051185410049591141200c180e01c51044600084440c400e1000510130183d0107481c0c4c0d0081080081401006440c101250001c41e080c0c0b1000c0c03140d0700c1c010828048071404050320320f91011400c0c8401d03c80c524000034050944850a01080741102c03001ea40d0b10b1038200b1a02070b5440a66001d04403202483d1401c1c494010340c1c441111400d40c200b40d910405014005d801b4001004807107800520540c1c4507182072440c684402e4507001c2d6422a80c03007124082d00c411541a00803d014101082290402d01c001d1172149e60040003611880c42c850341c0d02d03400f9000240d800440c114281c040002c0c112071510409001781500400015041c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 790481375 1250 790480125 790480153
    0xb010e040e03133b012102040504060507020f0106031e030203040f14030c01140a031113090902090609060907080a0204090204090b0a080c150913020a09230a140d021002 74
    0x3a610000c03500b11020224000e07040d40780c0803010a0550b62011203840000c460001c03070082c0d0f64080c200c003a500500b270100340014000f150788241c1c080c0e5a280e0039204100ca1820180c0c0c2a10505d100092409080303045902601030300d00f0b00180454031920699140ca0740d208450101500f49400c114101c100c591182001031408201e1920b03541c90a0a0104903802c2d2000e01d0f2080f0300440590100b41034460f501045134540b05821181d00c070082c031020121598a51b403806004040200089010355030030030120703045280c00301e411446880004d02c0b0442c2503607154011107840c44090480f8403095003c1c0004109802b4500152001d04240c25002541f130304c032001008021171055001c080242c1014082580702d80310480c5002000b0040201c0990b42d41403d070200d00358a01c0880d1031f03034000348045a102100c90b448813640302107030141c3c1200d000310080e00d082c03001d034501440d0036503034080c603401e508000346074141144511a840050503441c3e180d140b43c01041c07442885c0c14040006801031902c501c211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 790482625 1250 790481375 790481429
    0x91809082214090c03060f0102011409070e10030c030213091a0402090f0c0f130b0a031506020316122106150810030303051f0306091103010b010e040e0313 68
    0x1000d4101e40d183c446003004019600a80700c00b8214900840050401d040c499001b50030608000502540401e810300d002a1111303220b030701500407001c100d400e09011440300c5030740c00999000d698101640100c181d14660070080943c0c5064001d818107511404c40c1004180e884203002e000f4101503400f03060500d000e03c10009200c0b0b00520000100d44000c1c10b015115611405a6a80049040c29181d551040c5000109954803551082d00102ca0001d88800080c2d0305410005c070240946000049240e01c070801661131f4010124a11000c50708a01d203000829010300442c1c1c10307040c050a0840c680f501250012103081da4900d01030f140e09403108010000c40207008001c601c2d1000314035050301c0c1410035a4242441600500c80a801c06884102060340803040f80039198100040c801c0380448140d680c6000c4018103400351040c0d49610071107036040264281801040c1c614107050f9a68605070940504200051221541d04071581c401808105646001240e40f10050140c14000d4807040801000340094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 790483875 1250 790482625 790482659
    0xd0e09060103230604090501020c2b02030702060d0b09040302150702071a030403140a0e09010b070f0b1015020105090f0c060f0a02191506060918090822 67
    0x1007501c0c0c204a4501e40b42501020706030502c950700c2c0c84006071291390020f400f804920780090300951001581580d40c04001512004d00300380c9440100086100d60300092000428ac00c58070050303001001148014070b0000010903412244030b000103122100c400c04100340810440e01107000d0382c0b10408644400c1100a91503034000c0003403004040d11418048145444009a0b921008150020012030205401400d12020b201c0054603015220350000400400f1100c440141c640641c1101c4008141d100d2413400f201c01054120780c24204000c070540d81d000498100401101107806030000126011086400d4505a08420342c00400c0030301700300c2002d5003441040b1615020b194488200841140c98120540d0b60410b811003069884074031001c001da04018401950341156254211580108081030003890341a0788581820042c0c5522000180c3d0b0481241c040c810407202d500503c515941e600703420465005100d1090142001c1c14082011541e4040450000e011200d0b51018407141e1308424001c15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 790485125 1250 790483875 790483877
    0x903050304021207180f0605180a0c020c010813020f040c0e0310051e0702012c0f01060602030d231302030f0a020a050111150403090f080106030c0e180d0e090601 71
    0xc81249410955415410b00d42800301a50703444900c01e03020080f00717031300420003002c025004a06c0c21801d041c0c400009c0c1012603840240916041c0d41c2d07078801348001140e181020040e160111a0740319022011072400d101c4c0340403607100321284040c1645468900904e00701e8540c40e2031b54a135400b080b104242c103095000404074441881c00e01080306000c80c82c40602020070b02c81041034080c2d00c0b440381c120301520700c47e00b10301801090400400143d40b5440c42c08a130103111725003950000348008200c10301f40d684c60310501c03005134810300c070103000600c0075400f6004154060040d40d01c1c031031601c0a0840c480100b04c4002504035032000c54801075050510000c0c40c1c6240d80341c081e2a05200a50005003001800e00030a4100b0042c401000307400c110030441e003154020040c5ca100c40518183c80c0082c1048010300440241d581e5444000411100c140501e80c180c5c0d6200c4042d070500ca080c46100c0d1807406008048641140c0c220941090302038090084c1d0240864030380d0b84200280702c13903045c46019000500058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 790486375 1250 790485125 790485133
    0x5030610050903060c070203071208030601090e06090126011d06010605160b0601090504050f09010b0d0b0406020c210703030b0a0b07060903051b010608100905030414011209030503040212 82
    0x8940c1c1c0c1d00464410f43c485e44c1c02088580720012800464a07010242c0c104181d102048043c1b4001d003c00007016600c00d0300d00f6614401901d0300c80c01061000401a24a075412890400050044404181140400407556804a101d01d09007450140c25104c4018a080320388200041542c01c0c10002e1040343e01401450804a25180008030038260340c0c3c550b20b201404404400f804503200c1c2c0e115074480340051000030002d201d18108804c0c00c044100c0160362441e0035600c2e001c940d8605040800480c5030742a0020420b50890743c850321510044d6001c01c0c4410803d016005505105481076540c1201000b040d141181c1c07140d100c2e140c05030440d0310305068113200303404a000c2041503c0188040f60407050340702d0000f080c240260700d0141c83d240140044501100b40c60000030007207650550001040360036060444855010b5000e040080721034044000c1c0c4150810001404560880c4010844090b81031400d42e2219100c00010400c654802c00e007200021700006c18041940343c8200d1400103084000094 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 790487625 1250 790486375 790486387
    0x90f0c021015030605040b0f1006020c0108040f0209101d1320060414131b0804050c0d1505071103041a0405030102031312050415110f0d0503061005 65
    0x303991120540d94034200292a019105105800c0c0320749200110752240041c8840c1c180b0340f030300c0300b042d4070104c0d1060b07918081280003031002c0e000e0008410882d241074000e4503000000c40e0045681403c020303c145c0380301410100e030000503240c11048521882c0c80200085100c0c1c01e0440014030301555904010002ca01132080c4002600c1091459407007503404400046940504220240c448150000382544500003040000e5209405010200001c004032407806032040400740020444590740c410000e03440e0100c8024900714080c40949821500030000c540810140e4000039811010503031044a40c490541f0310320100b174149000f415008401c83c200820322a9103400342d03d650340554414401c0e007031161210b060130440110200e40140401800956585c609007586501540b4a03580c01c481c0429102d0968000e1032140c0265016a000654945c0c00c4c41c4041c1c808031100d40400d015083d00f0701602505036003811081002c0ca00c2e15841e601c1e0103440f450700c0410400c00c100310041110601404100d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 790488875 1250 790487625 790487627
    0x30f0a02030705010305190501090b040b1905090601120c020307031d090408030a020c100b15030c190e1002010b0a0f0b030a02070c150309061503020915031c0504090f0c 74
    0x1d28001d41c0e000b885c0001d000d0344c500300a0021102c851a034505460714080000c522541a600f000a503400c0c16141403020740c40384018810880c2d90846000e034400d9001c4400e0042d86040030340150018414034210108034001c030041d01c01c0f1000c100100b40580d000080038000c0541200494103140c120044d03500810030b1040c04101c603042d0080c40204030311400000100d1030b584950644195460900849104c034032640380d007130000c00c03092031014403545007140c4010080e00e20000316845103103031201c568180080c2c2c42941030403514407a402018414220f40c0350801d62602114000740e51038640c00410181c4c0c1c2c02051140c82e00050b0024004002440018400c800340c00701220b40040358000d0040e500d2055080c4400030001a41101c80034184035060240d206030325811903041280034000810008407984030610700e0310401c0c4802908042c0c030701c0004804414059114180042c0542580c0003040040003180400b440011988040303038000c903090100e07404078419038403090741d1080100b0024100c448 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 790490125 1250 790488875 790488883
    0xb072901081005090606091b0c030309101b2102030424020a09030f14011b09080c1003090309090c0c060f05040b01031502040801060f05030114071d030703050307060902030f0a0203 79
    0x1c403150040b082c51f0040341055000c1481101c045460280c901c0e1910000611641c0303e9005031000f4010344540e5050800004a0b481441c070f510100c0414201024102c44080c0c50400001c2c800c0c1201400c0d0f81100044240140000d5204d68440e01c842a1510301612110740c181c0d030100c0304046001d1051240350700d1640c0040c0240292604401400d602e48151301e0a50010054070b050861607500b0402e451400d0000b589010f020383c001a2284856261241c0505d5030701c102000310550b11540f00c0d2102c440a034081d40c0301c1c00c010340c06490000c55954a8402000c1510029265080060301610f0030500348a07541c820070219905031041031143d400c042e00c443d1408a010700000d001034070303103140150f000507465041340c00400304030009114441c0d66002d100482c6009114243c025400d00c4600790111250b04101841a8940d4135004c45028088034940140401d03c02015003501c544040480824410009070130a54414030012400e481d051061505181d074482401e5072550002800e0401a81c002c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 790491375 1250 790490125 790490131
    0x130b01020f0114130c030609030503010e011505071103101406101106070323010801090b0601050a020706050901030e101d0706270905090c0102250b0729010810050906 73
    0x9403030406403134039070800c0381d1040301660006020034034010821081540000155040300d2210007181441d030307600d0704012000116201f07842c001131010071514001400e40700382615808005012140102100450402120910056012007610b240c00700043e0b450710324200c00d0790828905e089a0800010110103039154000740c081002d143c2c4903440084100c081210302c802008030300301440001e5940d0312069008020400d02654866042c200150300d0794082c608480b00c08070240d0045c0700032442d001c400c603010380100459604050721900b041ca02d200b02005651178040115200080c444801c040401c40110400b2060005411490041048079080207210249c032078000340f82d04200b20f00841844114070a82c00000c455441e00c018050030200001c1c4910100c4000c2e005c4802c494890a0376841a030700a003150740a40048802c24010201c0e500007800006204240d00b0f01d0714078001014020400100d11481d0300e41c0881e0004000900003000740808038900403034200004d041a0000039100d410007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 790492625 1250 790491375 790491391
    0x501050a1407020402090d06140109020705030703201e07052209170304050c09070503060a1a1e0d230606090d080a05090307051503070c030e130b01020f0114 69
    0x101e000300541d104c5070102c070001c210040502e40c4409292070030500504e20041d5030040b20803280000320300003034180300b03c5000a4010008606001803540d0807a55140780c20040e480b0440b019a038007407012030810210500e80b41801020180d0204255000d02c1c05910303500c907501c601e4450361028100c0f483c0c40320000c22103141310004a0400428100f991204010520703940c070080d0300000300418040045104440702800702c480d000d02d0b0f1a82d00088905002c04d86007941d220000420800001c0340d001e501a55003200307540701504020342e100c00b85a00046003101c0e654110400107003451400c205200c0e103100e40c2c03c0008401c40d59444034035130720002c0c240104400c0c010100001c07004601d0b81c42d10706030380c00d4952210107203035140707100d070001003e036049103103514040e2003240c0c00442d50f490101c40520a980f180161b8604542d20584100c0f1040e200c00c00a4041c0040b642d040741c0141c03a4030404881502c0c5000c004134401c0c2804e800285040a030314480c0c82e00b42d26002420b60704601403000c4982020760 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 790493875 1250 790492625 790492627
    0x6090417040b040303110c010801050913031202070c0e09010204080c12031303050c120102030c0a0e010504030507150f030b09011403070506130302040e03071113090524010501050a14 80
    0x100c00803585440c403654200715200207021400000301036208010301801d000381400e4a44100082005484809007030081ca82c1c040743c070701c00050290310062410f030740c0746000e440c0c0300011800c5041140102d91007000b0544014005610612450081c1c0b114590480c8007000210700c2e1502d0490031a4913007500c10b103518400c9120412403904d200003007003526801204c52131240d100b507070f591038029520a18014928090805030100c040400418070a59103d51065401d070303882e00c500308a048580c1d00c140520345060201c18800840414010005070001d024407030000c0f014075400c0c10b00a0651407011203940d08140c200705d00d0442c20b448442e4418111000507080b0045d07800d100c5c0c001b82c2440141d4020f540c00080108149001104105000d0b0071a4000d0751308010308141ca11015850f84910700c0f024094111444030b1845906200540911015407844001901c44482d951241003603c400300c00d440892415085a1510000000c0c550051500342002841d04510390006014850001020440d80f60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 790495125 1250 790493875 790493903
    0x50f07061a04140109270602031e0703140c070201170c19210509070b030a0b1302030a0f05070f080406021b0d0f030204030305030105060d09050102210609060904 71
    0x1480344a102507040c00074002d104420190410610b111024460302d00354604200710003651450328841e0b106108a00203000e41d20b41c81a8070b03a0006980050034066a0025a4444001c0135141101c05409490655004241c0400011008440d4800075092704100c4c8810055000141c0e04040180100c0003100d20784001580c4101c005210340c0594a2020480070400c10103030300f110f5203c0d210003281d450b5001d6058902ca01c000041c403c17100200c81d4240036603c0904241f00380a1110b01542e4002c0601f00d01080482c0c017480130074132170940300c0440c00e003007500841800000d014600980910380010a010840c82c90300031401041144150b41c0c090511482d80003080901c1000c0d01200c0e550600d52002c45202045204540d43d00ca03074410105000444d15420305219510a008443c22a500740d03407424156400c11040000660040c8a560f03041c40c1e50307448940000740700780080d05003d0fa641c2d00d1018111002c540e0f80090a0008260741c0c40780e02d0301307002c02546071b480d02c2e2002e03007003900814441d034a10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 790496375 1250 790495125 790495151
    0x310030f02120d0c05063601020712030b0f030a02010509010c080c0a081b0303190b0f0a06050c0f0f060f06150301121406100303050904110d05090c01050f0706 70
    0xb00e00c60705203419400765892000300550450900c1842610800482c2d40710b945103450200c80605410a42844108046241d08920401403080c9002e0401000052131700c0c07c80e559410b003800200007903002094840010030207501d03005100c4007150100f40c0291600001c00d40c002405445413044d00742c107000d1141d02c81024444410161010503804004540c41a24107040c924095007060880c00b1143d5010010b40c112151301109032800344004641c58000703a00d400360300342e001d8007080482c2078100c10351500c00b604580c2e81c4030380500142100c0d1991a603915001101c18100941810203450b243c1c40001e140c0040c2000103641c940c820700458a020580d2103a01c00100b05621060040101c0d003008000030030300001c2c404004c602107106d2043c10202040f0580d500b51103207001c442e00510648691400c2003c60300035002408044c5001340002405150f0000303149560300700c0b902c903a03c101c0d540c0c01048001c600420820504150908000c0e0074026001d0300d076101449a00002010540ca0707880a003010b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 790497625 1250 790496375 790496389
    0x10140114011707120e010e0c0d1e0204111305010e0103020a080c0706110315031504110d030201020f0409020d05010f0f0b07050304090f0c03051501171504020c0607090b0310030f02 79
    0x440003810b042c8241100781d1585c5010b060207a409a005000d0710100001c103240c40614402c40e542c1c004401030381a17005141d0a4111500280160b070440c0c0c6a103a41c7c8003110311400100345180410704060804c40c149000100600340c1151444c1c141031041060b9049280c20510040e80a4940208155200b805203080f0020b40304d000400141c030f1401200b8400b404000c084208440ca5082d01245e071550a0400484001d02c4140c8000e05568100101c1201c80e0402c401c08201542c040d000151504040c0700420303296601a0380548189640401e01c2c001d12840b601031a4010070071110102c201c207082c009002c1d0f0301c10487c49030128501c0300148070b81c204181441510024117810404000da0070320207803a400940442080440040d24010014030640313402e8082900700c00341a501c40c081d442d00b01003280140d0394040e1005a200200943c0098269201e00050510380009070182c80380d0301301010098540341e0342d5042200070345000e0040000141100e03524000b141d404c01040300407000c0c503002003600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 790498875 1250 790497625 790497647
    0x2030c0316090e06010f0915080d0e0103111801110705060a171e071808061602070e060d02060a030b040f05090c09060901060f050c10140114011707 65
    0x103000740c00c0c0d99184561141c01c08070803508000c005001d40000c000a480e22550309004088281c12000020f22080400780d100e1005800030a45140721240c03102100d6140007420850310000030070303a203d4070380c1c40d590501903a10850040d200030303424159000c00e00c210303036030308440481e04104180005031050381d8100400fa00510b03004d855240d4030001980003d03c0080561602c1c000075461602107454000468205404aa003e40d81d1070559242c1c01c3c0121025080c112040880b01a03c2e40041804d0303800b805124082c1c3e4207008039920b004065503001e0f0070301400b41d02c0071511082d008100300d034030780b512200d45500990488610b913035910f1880082e0004c16400c0c2200740c200780303400d5030b4195001c1203070700440c02031010344101c8107000352460800051810454000b40c2002c40c4d8001003000d1070041d81000c0a4440c1e81c2852820180c25800992030911440340e5000e086894004034403480065049407030140c0302c0a60494964258000040c00c402002d4250070800380195000407680f074810301c3c511709 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 790500125 1250 790498875 790498879
    0x1e0f0c0d020303070b270a0c031b030512130e0c030a09060e0d0309140c1e010e060a03020405010f111b0102100606120b0a0f0b0306151603081b0d0902030c 68
    0x1768500703103100042d40e9084206488078a00700405000d8048104c0007421162082e4808004080c860841c0d640400a1034440c04401c80c0c106010f0000c000120107100840260180c01c0340c240d1518500d002140500e1210340c400d8200711641c2080c044040300f86404c481d03002c2c1e0344d15804135007001546018002840c5403140b0304528000c0060152005a054001040c01030055104203480c00417001c0054031070103108500b5910480124103a03110140d202995084c00c1014101241602e6508000c00c1c1e00c1d80c8082d00c00c41c001b0f03500050038130840da0000000040b090361890300b00d51014404000540d940c10400c001c02921444100411141c1e00c200b00c60500e00c0c1c03d501d01807000031b50710351f00500800c0c1c211800704406400c26405280c1818910010000c9900c09e13000500e0480c9049a40661f9900140101d50043e180e03090760710b0703110154801008981c4041c0ea88400b45049400d0041100001030b09140c8420030ba4a801c1385000340c068240c1c1c0100e00030403000a00c8640718070010340362002000c0c04c0c50b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 790501375 1250 790500125 790500143
    0x5041e0509070503061f02030403020d060609141008030702010e040b0d051c031109030c010f0201060f180e0c0f10090f03080301050901080312040822081e0f0c0d02030307 75
    0x6095441000344d0301030300d0141c60300302c0422034480000ba545000c607040c580c0183c0c414030041003d45032860521440900407140011456100d914100556808860b00005d0207209018801040c006031000700080550901075801c0103a143e0000b460012a031420740c0c4242c1d19100c0584d91950b501e0071111b100c90340f1204454880c0c0900d200c41c11003411102102d80401e00d09608442030300850030455600900041c05043d012150703000540303010300c417284200c045640c3c4020101f05c50720401115009084454054885000e81c128004241e0319080c05000c0c56402413400b42c03030325840da8020719805140858010220090a1070304a44214844c0d2114400c44841c83e40003061069403030045042ea5020344508000e03a8803400125580d01c0340403582c5120018010014002c20600c202078011070b400f40c3c1a000301e5501005626010306030f5a00b04d549140c12030319107241c2944005403d2240ea100d850041c2c0700050b12840e10640b01c640380ba48040c0071b1400b940000e0304655080c802c40b02c00b030307501119403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 790502625 1250 790501375 790501381
    0x618010303080921070303200703090e01120b010e06270702010b0603042f1e010206070c020f101803030e0a0609081b0f120606040510050105041e0509 66
    0x1d0511900381e5014040b4011050800d00c1303240008105051808001085032400026540440050038000c43c800c010380f140301d41c204200d1540c14010b12440d40a551075414003420120024240b81e4180d0015400c589a1100c44001a80c0308a5050445502d44d000e22950394070000400c10700011840b900c5d80c091201410008251401d0442c24000c10303640e8000c00c0074000702000d0040d548426140a026010382c182e01c400781e58110004080b2a00403081c10340c40354046a008120461005010f403102d20400001301059960f0421900d0b0b070215040c80c01031102001500801d91405400e03803445d015041081d0601111360003598802c20f40341c0d010421030601d0781d407420300628080707080b90400e1240d010100c00080142c420b0007030703134241d0f6102400381c4051032000487c140c074001341c10700450300f10311690381440c80d60b511100030a0651721480d0141a05203040b404000865000801d00401c10090b01d5084c07040b40d03401800d4409a541d4142c0445400d06910380703001d00c404c19948544ea01950724410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 790503875 1250 790502625 790502627
    0x20c060a05070b07080103050a06090c0302100f0e090606120a11040f0812030c0301121b080c03190f0b100f090615032f0f0c07080f030702090f0618010303 68
    0x10300065003c0c244000050f1a41c4404071002503084c0f101400d294042060340d00460395540c000d80d0028842e40b402d4040903039950100703030480c1c0304110590208207840741ca51034458101e45040d070160b00c1101c11100d00d103402000240c0030f008140314681c115038042c000658407072650340001003c450120143d92a5079440d821400004514000c2c0c042030700640c80c6905480c2800015030303004200750010642141c0c28900c124400e440b00700029546040250301d1520500f24000300d08001c1c00904025080100001040c0351601c030580007140749d01c0744640c2040010891070107a040d5501e84c8182400905d850340c0015410122080e0880b40000c0d204a000007445001ca91160381204d000c0c1d10300c103d030f0412a4a042e011130340300c3c4503000854402c41c070120b200380c1002c0c2400c1c0c0c02800810807041c20003035014244080b90b0010300d00701003a9803092405202404040100f41c0e29040c0283c015850f009081e40812030003203004d00303928440d454036400704515540e800c04101c11200b07078030015002503030f507410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 790505125 1250 790503875 790503877
    0x110a0308040f0905060108060d02030a0f06060602010c021203010b0901020f01060608150418060b0612010f0503151b0708070203061501030b040b030a02090c091215010603020315040c020c060a05 85
    0x704030803440d070b40706400091201d0a030290a00c2080305840741450703507640d074090107100d11840504a0345401000340f220000360750100800000d038000d000001c0c0b10760518202900b19010842e90341c0541d402850842075007100d050072a815074060301822510350b00c0b4103005034508074001401400c00d50a00d00081161031340b040c4418492441205104241540c1c41e00f0b001c1280d20070041c104494440d00000c6000c00c04c1a00882c800f11000340003103140616141103038200c1a000e80002d550300705045020010381c9010880250140c610740c400c0c4400d0300340400c030a8140c62031710329a031007440004204401032156400640396015006402e540c45482d22035170500d80345400c00c080601107480d045c540401410f01d481501728071140075000700228100d54003005030140e00140605031040c01008406469282c1c9807005200d604520020310109101d41a078030810f00058001104041c418402c0004004507820942200501a01c0000385000c00141c1281416120484207400c044001000308030b040d4070030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 790506375 1250 790505125 790505129
    0x20c0c03030730020d14130e0108010b062503120f0f0e07060c1b031718030610062d0f0e060c0a022e17060301090506070507110a030804 60
    0x4a00040002001c403140e00f07209429001d180069000744d1503810b005008802d40b45403000800012400d01503d00104a903240090b001007803207221b007200400020b14240181343c0144000c803009070400d03050106a5000004540801341c003454044403100505026912000140d5111103041c0b110010465528024055908864030749038a405070340c1d040b681020a4403016618550365590405d41c1c5900c405401d00c460304440c0b06001100b00300080081d10b4840c07a055441d03221140b07540c0b80c0b000c0c849404034003050909418001d401000070406140800d000c0304045e685281801e0300300300c1514905985012111001401400902407d6000941c1000140c1c5101962356540c1d18500040c9040c4407003400745094801107940f01e084000010315080704100e004415018004810710b8003040c0180c9606000b50b181804588408c1ca1040000404086030394002c1050300248202c04940e600c0564800000745210208030010840c00e04204e0050288072000d2001803942402d00e8490030304448a5003e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 790507625 1250 790506375 790506413
    0x140103020108091f0b0f06040801050106170103120807030902191e0305120307020307050303011401030b190303050d0207020d0c0f062a0c080607120b041a04020c0c030307 75
    0xc00900c0c24200062441c5407141103240c10300c4a0400e000b07000c805003044190540d408200703002c48500c5511f500d80544000c2003085c00104807075241400191041c0110ad144020395590b110050020514204030440b40400501e05840b85070384040040340200201d40d80203510194045c842941d03101102c10300020354001c3c200003006504070940d80d1400480900c001051904555440355025103030001542d4030600c0360055034a00210b40d80c483d0304583c000d0b00055201210349501e80420b580c03504c41d502c801c1d80300b41d41c8040d1400a0b03124000344121030348030050030010300155168040300190103030703854554007501c01040c684a500e0200c0e40c140d200d004480c8060381d40d050006040d8865001d8140e40750411421900440c1c40480303c00c2034500704e00c0241c07900010604000354400d01002110300c1803407240d03900c4a5002280603d0400d40300d48601d054031560900c0340442c0200d40d1104200604c42080340c00607580c1025240d085d0800303c030000b2143c1d041c0804180b400a00c0160004810a00c05c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 790508875 1250 790507625 790507637
    0x3060621060a061d040b0a05030a1a0c0444010b030d020a0f08030405150106030207030e030c130b0f090405030d0608060f011503060812120a02070206070210121401030201 75
    0x101c503021500c00614a01d0f41c680380944a60202217802d00f0390143d144a00f000c0c00c01258240c6540c0460b1805192070021a003040c44024405200640c1b95441d54015034010304084c0307044c2c40d08031165910200c44040d068084032528070301e080750880348986464000342e11102601903006030345143c02040600e02d014028047d80b419560241c1c400700d02d50342c01d02e50211240c44140869100c44580c0e400040040b10240300314407001a050a00304550743c0200070350382d40503070b4801580c0b40062500003000e00e12400780d4400b000e040d4480d40d41161300b02000b0001207000a110182e5030019400c4203102802d103401c03c0c4800148070600c00003000410f600b0260010a011305981c9007011075031001e04407500300307407c10504018425809207010a641c030840c03604e8040742250700e543e00c450800d0080300300ea1210f0b0b4070000d052012a507a511080e81e028040420443c02c110554011500398818610700034402c0f200701081140590047c40c82150035808ac0c0820031100503900d41403c02c4802c20300042c1e001c145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 790510125 1250 790508875 790508879
    0x110f161406040503030f0f22050316060807110109060c092903130206070c0b040824010308130801230a05090d050315131401060903030c030503060621060a 68
    0x10321004030780c22a9400f1340158a49000b50884c0f02c042c0d04030201490b4054410400c503120744c0205110b510b000c08054508400140c981400c00d03283c040f0300b020036084d0424803001084015000381d00280d00140314100341200035228001c4c140108600711004145510300085220110b0f8000200026501008620f00d041c100f812845401d900c0c54100d6030500c0ea1041001450280414400c1c0c0b500a201804950602030560348013500c500712600141c0500c107001c10100000300e0308002030602514404910028945e101c0782d0055840014080a01001c40000740d8100d0300c40701c0c4c54030300300600c84640200041c7c10250840c4803410307914101c0d0b00c8050030450110b0700c54500e0788103240c0034172605d400400391071050740411f13a0346c1c2d080141b600c01d10b819a58103000301601d80300c90140c0317050041d11002a502c58801001c242481040c0c103c4c0c0d04204000c200cd00000303821585051101d5014142592242e589070300141003441a80c0c0c002e090105a4844200020703890503032240558821286411215 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 790511375 1250 790510125 790510129
    0x501020c120606150c03280c02012708030310081c050d05060a080d030504050105150904031416060b0325031509080a110601050d02010f110f1614 64
    0x1807031040c0c0396482900403602241c01c5141034a204414032080e00c068604041084200740d0564002c6095a03640d0b85450700003800401c82944041ca071b89004e41003100b038815203034000a02c800980405941043c6000e0304981c421250a2545401490110205c0f41c4d41d182c10518500f07140814411000c8031b00c548000e04030005215a001c03100b0302501c0e51f4860504110382100300280002902d0b140c0c010310781080c003182d500c1080c49182890b03101a01c01141905051400f103003101c0d001481c1920700041091618a140d50f980c20854106401d0325180300140248403284070b5622441d1104c2403c01a500b50340c10800495401226040b50100c069400400b05181000d00440001048890500c2e070381d80700380b000804003001c0e05c540c592203c5000900c040507550310340c82a0700c07941d0180003107068414603400c01c250820590703014002c1038604024119141d80087e003c81c00b200405800c3c410440c004407400c40003001400c5814881e44121000c039820074a1000e81e030100ba001c0c603e02c07a9491a2141c82d14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 790512625 1250 790511375 790511389
    0x1e03020f0a051303060222050f06030f091603030c050d030608030a0309080d05070e1509061c1b1d0102060c12061908010506040b01020606010f031104051203040501020c 74
    0x21844940d2998580115980110b50301e901001807160b00590f00d80001c00030a4507440a0400d80c40f402152400a40300b0103644284d88615500003403148a003030300c4000039030300c400044c0da0b0045407554040c4850344400d180c50307040400510710845107000d254000400e255101540052590094044c0d0b1004610444200c0035aa10350081116941c01003100c526031314440c0e404803d0040c082c100c000d00300700101c0400c0707065803416250700d00051085c00841d0001c0c54902c02851f03046000e074040510300910040031402030701a40c2c0c91404050840d00c81320341c4120040e04401110390000c0503440a01c506d400c2e008c1c00c1c3e0341181d8032001f1344152218943d10700e03500015506001c3e14121b082203092091850032002101001845560450300000034031542216525581d000380c00c0043c00800e90b403515600740011a040b03c3e204a04540c4600184511039170484803004144180b882d0124401d40722100750303030b070070712450f44255085104455928030740c04e4088080c1042c2c078001da080d03d050341420740400411b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 790513875 1250 790512625 790512637
    0x150f03010605031902060c1c120b010903030503070c06020d021e04030309030602070c0909050d020105090a02150c031e04090b0405040f0f061805070519081203130c090b01020606121011191e0302 85
    0x21031033400d400e002090041d80650fa00156901c0c0c081036802c80c0ea0342d043c0c142d030800c0100b411103d070081281e202220304107904c1d1032564418601c9c20304284c074546009140d04403030303c00a4800d60740000c0302e80c203003c402414403000d890754203014464400310b450410358481c85400300e08015481c02c2e004c80d85041c3c011424850f1150010504004e4044215100c6036540c44803030a10264071041001c042c1c140100000f404180f40300d000d0441d01e4606d4030544905403031020024501c9249041c0030070000414001782c403412140c105d41900c1100d0385a103041c07002803000070300031118024074403c4402003010014441081d6103094400c4040d41d03840c0c000369004003900c2d0141d100b042e04a020405400140c2d2400765a02c600103880c210700442d19510b95200c115080d13004103c81c40d81b140c89030f48403940c04010094004600b900c055901e640740c244441d0320b4003030011000482031348070082c1d05504010716040c1ca8000100d0344040c3c007501044040a8180782c10031070500030882d1092041440c940c024030950301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 790515125 1250 790513875 790513877
    0x20f030111090909030415020a03080c0313080a110304230d0b040213140f01170610290c01090b240907050c06150f03010605031902060c1c120b01 64
    0x8100b0041d8420021440002824450544014400001c2d041a0b9201f40250b40c100d5070060405802c560030000c154242c001d1039010850b80410500c681c0441783d04c90100000d4002c003e458454960001c1121050310b41a141d4040b8030000c5070108a074140042241a00d420840701c0b55240c5040005000000c900300102a014010603000240503041444030b4000010003105e00080c0310101c02111490140156000031910016000503c00301c80c1405400300c3d1041c20200038003191a1020046509035407602031802c490030420b60311107214510700f004050001c64402410388400c00c1e0f40d0040c0c003e01b525582510404500790214400300d1b240000c50328008074550b0038540300c20001c414451480f002400d40c1c800c2110070004640c000d002030111600039120f80005900c03004014041041c00c9000015580c4240d140040400c00c80c0d6002035030800d0101c40d505034054150a50000480d81d00070600840e1240c0100b80300b40c005601d82101c04c10340107800e03484404054900d010004119070420034064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 790516375 1250 790515125 790515127
    0x1f0e011811040504020c0307080301080312060f0f10121118010f05030a020f041e150e03030712020f03040e190902091513020c0a0c060c0308010b0702060f04030b04020f030111 77
    0x3c0031a040c150010300c0e9080c42501200d29029440d9104030395079009038005006608041242c1d5600c070a0407103201c0d0001c1c401c0b034070707400108003100012300000c180c8090503100340d003035945220703603280104140b19003030741004010010104402000040b51f400308000022501160540c03004c913602030203031083e81d1034042c0d072010704558803807030808001d6100490f0704d0382e188400c0c0800a1401800701c90004900a49041016124504800ea20040d4030220302d130790501c4002c85860b80340d43c40c004252010240c0080c44000d00083e0701106a082000c0201d491803c2e0000280c00f0580340c001010241c010200e50081c2000d030950b40f0402803c0702c24142c0c00942c040c400314040303072408812030803140403601c0060014500c003141900131022a400040f205503d030f00684206002d00103040b148800a2826080a445180036035400034410801401008104080418030502303640383c42007968288040c8a1519540d181c07a03042040402c00215001ca1056421140340c001c141018011070440000d449025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 790517625 1250 790516375 790516379
    0xa03260c21040b030112050f0f030703051e040303090315020304080909040218090f062508130203060103060b130b09061c0f0b04030216060c0206031f0e01181104 71
    0x150703500300d5054090151020080c08041000415140114020901c81c089007031003000038500141001c5807800c00c40390580107005a0700c0d4a10001c000c49001030f6140c9070640c0d80d142c1228660b04220300e15401c040c16200701040200030150030a42817020349000314910300c01580c40342140c030203030320085400400ca4581482650928104145c0341c036001403004000404026100304ad0f1844664215109255070b0b04c902841c2c8110030301481001c1d000035a90b0190140c81c011966003000ca09d00b00e03070085040013050300c006190030050304d80c400242a40201603c4076541c2d079041681c00340c400005024842e04611070358044014061047d84020350000d444100d480d582c0800308140711407698088803503c00e0182c0c008002940341114000b080c3e20641000459083c5418001c1ca0b081c0d80d51041c2070212495030050040076001042075008546c1210119031302c1c0d9444102d2222940d040c0041d03032001d541c4c3c2070084ac4542c14102c2c04c6040e030720849034402c1c0134030100c22214140e600d00890344200c50030410003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 790518875 1250 790517625 790517653
    0xc121f0b0306150312030a0e1024030c1a07051203100501020d17131e060c2d0521090c01050a1b02030a050a08030a061d0a1a0a03260c 59
    0x203180e10003645140000d50402303900c0c806080100c03105040d00c1d50342c0d40354407040c104983c500e44034000002d5468200803050a40e50703488400042401180c91100f600b0300100c0350288010300316007402d035110065680d8004031003641c05154000b03071900d200210138906c01260319440052002c1c0c842140e5950290990814010703118100005024502c800248140240114407a07140c105600700009440400e20f02850500300c0460714055421010070400064080c001440706040c000120841c04180b40e8003c00880155017030300c107100c0c848085404903555820640c1c402101b95210740d05c0718065808549220b00110bd0382c1c41002402c4000c10488800d0050140b140380ca504180d40c03000c0c0c22260082440e4449c00c0c940a55401e08480113600041001030010701030003200300400711000f4080d060f80c2210340942030410300038040c0308460303030700e03907549841003118100505042c101506d40d032802a05e90810103040119005901c4094034500d8511100c03a10f504e04403960401035030050b02541880e548 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 790520125 1250 790518875 790518877
    0x904060506031510020f1204090507030501030206040b0f0909090a0c050f0d060509120c160603060b0a0c03090302040f091e050c06031306050703061809050c121f0b0306150312 77
    0x1c4201144201b40304a080070301e00304414080c00401c524000c0d00c0b1860491104240c0d00000c0a00d0101401d141c01007005841d6802a0b8003503070b51034100701d0780300c480608519001d8010761114591040c0c00d01c4c18000c0f0600d0105850201c0350160905d0b2990603100e50030311490800b040300c481d410614158106020456551009402a110500350f0b10385014200d090205600150340003a1a9003203016091404040d0303c11000003003440b03082c140301551600c60141407074080d0600020901103034021f10700416100344038102c05164001c00c100800d04820a15400a0a040c0021030781e003031b0705144020503410180d00100c00c056100008151800f5110244031003030300050042c0315002090b245820001b00a805514840d43c0c5960307000a0301440e1211701c1502031400e492050388140340c1552030000c10000b0618040120050301c120214000300c00c170603880c000e0045401001c0044112042c0540441e03a0017840850604800710341d0191038070305e0010b21001c0c2040084e80d05500612001c0b000c0ca1038a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 790521375 1250 790520125 790520149
    0x1f0210060b0d0c0e03030d1401060206100e07051611010f0819090302100504061401120309140105160609020f0303032401120c0e030f03040b0702060c030c0a0809040605060315 77
    0x324140d41d944d403104000c04c2c65500031680c125505d544a190050540340341140c028014030861004108604040007441220b103401d000d4400070940400000b03400c5805a400c0b00c0300c0d90900c00c400911400c842c1095444074201d03148250003d14020aa040c0d40c40c41a0101d42c06420840740c0b401808240c01481c500511310b03a0030407010b60040c43c400035018840c03441558400e5014041c00b141e44034028210403003510058114200030020701020002207540101740c00103427403004000041480d14038005076240e018040e0051100c2c50008070040c200481c90700151702191007070b80c203881008a260100b58890008840c0c9051000d05c0900c03560080802e2078140c1c400d807006040400c8100d16003400d0106440300152980c0111701881303010f003a18141082080c140d0345091000d141401d00b0403018007298410340d40041d1107584023042c01c6c00c001c0c41c10f0040b210034410003811036511044500e001c600903040704544038411464800000380790b0510380c0449114058084500b44000320039420840c0e844026 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 790522625 1250 790521375 790521377
    0x50d0201090f080d0e1203161e0303021312120f030213030803160305090a11040f1401140d02090402011d06031807050f0a060c030e1f0210060b0d0c 65
    0x4041c000703080c0e00030b0184080a03099820280411800b00000602128400c111080c044c40d162840030410b12000700a65a00c0700d140804000100c409040016098a801c42448070010002ea54241015007550041c06014242004884802e560306030000d2003841d141405081444d0601d4041f078040e22a42c038503251040242001401d05490a035034081c00b18039908112140c02e0000140442c2400c00510603603000746ca403906204c1362030490b4466882e40c4403213030000c01d5101100c0442e038556035143c03c02440784020b100108112880d0003da6452aa02842540600f00d21621004203a0505826000c0c2c42900a0724000503a259030b0b0046a8002c2c5d40b0304080d0510b034000307051060b00c2d83c07000b0007540119149140035041c0c20b100c514071810400c40354015072040d20340d01e0000455803a046242000c440040c1031500070a4a54101aa1000034000d48140d011170707403d0b402c5000e02c030b402c1e580300900780701c0303070300321451183c1c40900402240c3c076074003601d0313422581400141108034060300210016001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 790523875 1250 790522625 790522637
    0x60801031419030c05060a0504050706030915150314060f07080423010213080307050d051605010903080115030b0310110904092907050f130302030d0f140403030207050d0201 76
    0x8030104804034040c00b11400c40024050030380480078030108001c59034000140f06401c02c000d050507a03036507940c1e800e0741c400c4105040d1a09089010701c03214443d091600e250f001c2e024800d41c112659000403c3c1c0481c0001c0b01c0024400c0028011820300003195485002c0b1002c000740152604981995071070380003442224000c1700c001d884003203041c0c00144d140d100b003d0540056250180d034045054821515007007025640d00c10711000000c5840000e4001054445092242d92904000710000b4240025103006d000c40d0700327080b0280109640429294104e5400c11402d5410030009a42281900c40801126502d903000d001040700102440d8040c8008002c900582e501d400b521001240035940c2c9142c0c151108015182c140b114881221440101e01801020070f101e80c1c90107030006481130061b403103c224622808180c0b030051001d6011030394061a001021200c4008051000801c41c80001c0f080394001a1940306c81c001560301c0d10300340c4007501e40c1034020300309107820710007848483e401c6498181c2c10000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 790525125 1250 790523875 790523893
    0xc0304030308190e0f070801110909040804030206030117010b06040509070f110712060c0c03120e1204030b10060306062003090d08070c0e010e040623131106040608010314 75
    0x603034802c00c0522a0038001400e034241c9405c5201b8109615a445907403142d042c21000d0b8102e024040c11100c0c0c16100319505506900c0d1410712600f107020704d80000390032090010010070380304170f100c6a1503080e01000c80280505590401880341d90b0043e44151500028101c0100314078034000d02840107000303528503058a406821554181c03038800c15610000340000301000c03040030303c0200e0203001e01c80074181c10f01c600b40b22800d540081c05d01c000c922070410029078940301c4d0103007040c092143c3c3c0507110101c0005601c45817070341402113195105892040301110058800078980f0701034000c0a04864550301e84882c050000e510644400e1002d020f00796960004000604499603508150000caa01645895849040c10300c3c01001080e46900111404402c0c90010007011210301c0c01158803562104010036240d007007030364603c46d00318129502906910720b041003183c40104415030a0345180a41803a016001015062100c148201d005e61030014564034018400300d019120f41591100b5450100d42d0440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 790526375 1250 790525125 790525171
    0x6030109050d0e01080f0f0105011b05060408090111071a0706090c06020c130204050a060318060507081501090302060a0c0309180603030314091c05090406080f120c0304030308 77
    0x1030661000840803954400f100951540e004846a81c00750304280c03241c060b410070544e0030310030107014800c0c0f504001f203d614201d80c41d07696404e91110350b5440000c42e482070030240750200450b0804040c49001a0641103101a150300005680c0d0441d003803030b4040318406041c000c26003aa540301210a0b200142c0711101e50001a11100000c001409a0b502500101e07509004011281503400343e0510703143d006010074406a40d69101100460b040fa01b00007070214960000440d214030320709000b50540d450801000200f68201d0741091060043c14002d20048a5210054483d0041400301039007140f0184042c0281c0d6000d1141d01c0019400fa0911250141d035511000304480b0070301e600c902c1010780b0340c03004008143e0140502c1446a980c50800307105032a21103e903e076120369004460440a210584901c121800366007110b402d18000346c03080c030589488050031340c7d807000003030312007100c611135012507420310503000d41600d4140103060042c5140c81d146841c100c640040c0a082c2440ea90094122002e81e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 790527625 1250 790526375 790526383
    0x6120c18190602010e2802041b0e010e0406060e0910030f0f060b0d030507060f0605120a210c060c020111030a0e0d0809070612061d0411011d0105030603010905 70
    0x114460940c915070841c01e2001c0282925845c900c0c03520701d54420703050095100010039000e0920f004420841101351030b18000900940140a28021031045114025960a074000c109080308a002c0e260f203500c940d010414001124004e124110015080b105114100d250100069401420021403000741369109d4540b034032a50943c0360308540b20b00741500c0b00402c001c80c0340180b1481c82e0003201c01801141e06520060017a203e003605c01404c066898002d0041c0106950003003000c1c000c090804a00285070419140d56000c0b00001540c0041d041001240754902070341c0f151120118580e01e0720300e121a00c1ea600c1018040540100c000d42d500e450108071481d90010195220340c2040f80041801c0301401c100741d0030008558640320401c27000d6801c110311741a000608904680701403a0031140c41038040803110080c8441c0e080b144c1110700f400007001f00d400c202450f55010300c0c01103460b514240401001074a45d40c02c5c0c40740e040b150b1200f0161b846035641c01080a19070100025001145412140d40c5042c14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 790528875 1250 790527625 790527649
    0xf0c120310030303290405180609030a020120040303050c0703060c0504150207081b0d0c0611120702031b0d021f030f110904050403261506120c18 64
    0x28401c00480104141541030082240d405103001c030402c2e465100e05240e1440c69031003a01c95008645070000310f2382103101c0c0c00c00d9800c20410030060b2015410090441070312644005103040c01582018548010105945041211400c03000c01c0c2c030785421300d56903055078590000b0f01d81c140d06005603200000411a1401401b0942600ea61140d42c1c4a040070b000b034003000c03000d0f80c40804540c000081848a202c000440c120342100c4e28204000c980407110010780c0882c17400c5001411f0038005100007481c160005800d01c2040703480e00954110768084a200e007054042d6080c003079813540c844040359220320524a495220803801411980ba41069900410000c45401e480e03480c1c40c00d84a019220342d41c0c4d0521902045030280c1e44280668540f4008206042c0240c000d59407007180c0c3e4901190425000342c4050031507007900511f0703c0480d00c41c11300410b1003d9003211403d00c10190340383d118029181c41011510945143c00344030103151a04541da0340e080e00321424294002400c48010502650b4000f24441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 790530125 1250 790528875 790528891
    0x1014060906060d020315101107170a0503040b03090118110607030e031f060f030b04201005041a070b18031b0f1009170a05090a0312090e0c0f0c1203 65
    0x10406409401380400d500010360301f01e003004001900301d144210003081c4a0308856140b40c080300d207281021600f904144034260018000d21001600040403543c4201562003080028001c203c50840780301640081000d1840040c803002a20a08141c21b241050140c08950300030b1405d207850703591180100f440c1c49540c0c0d801b504c06001c10f6140315075104c41405014050f00c01d600303d01c440c0300e03e10b5403022500900030f400101a485c55045000504013022034088544000030a000700c0e0000d0401d001c1c28560040c01940c245046020150b0904100c00c821181100c0d8410481403007a40e40e06861a1030305a842e031050b141d408204100d02050111628040c0d02082040140c00c2c0b1401c05d81c0300b2407408849a21000c6600d0900103c07002040a0040b840541c020b0481419030310700c000b0100729614481c10030411b6100811180200a00c06000c440340c43c001400c1d11960445510b803a0360154025003114540c045000401003102c1100d2094040e100107540b0078200d803601c101ca1505200b5a8004550000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 790531375 1250 790530125 790530151
    0x2060f0c0129040c050c07140315070525020f010305070e03072303210c190f05010b0d050303061207090614010210020a0c1e0609080301081014060906060d0203 70
    0xb59985400d101e8410801c0381818160300d459181c414482e02d0f42200c5c401c47d00048003000d89004151400d11100c403900f9102c24070901c1c00e15200c107010b01700b03801965102130f50800e900020b5084220b40c4071245512030300240700005a90120004602900c00101170004120340070000480648003000b07003002900042081608402140c101010b02003240b2140e071344031781d1040d130700c1440c07040425103502c0c4450041e191081e0340e0030800e500507281c80b901851b441030900000e0120410b00201088900c042c1d485500203100030b0344030780f0402070f101da03080101912941080001c500a4500141c07002d003040c44080c26950b4444d96840e40d402140d10715403000c1443e10089061552542c2d0500285030350910030700c8218104000060010007090f01d00764021300c0360508508180801090309041142143d200e0424884055180360541d145d8000b803003416281d00c60560642844001809a40c0843c0d0031a801403103165680400c00c120644050040e80d0005010071103801c80700c03001d000541c45082803520300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 790532625 1250 790531375 790531451
    0x409050a3b241920070f02130203060f0d120c031103030703140c0702181909081305030708030a1b0609060f1d03030c0307031407030b090112050309040b03070503033402060f0c01 78
    0x400700d330a2070a03c01600c00c0cbc00310228000041c01141c1c0e0f07025481000c0c42d000540044a00d8183c0750608070181d869028803000c002c0010065064002941c03140e0b0742e0681100d2510703902e42d005080c0c080c40200a40c0b0030f031540304000891082e0f400c1164402c092903050245020480b90706000c50309010310030f0300c001e00d0000741c0241e007250064005d40207210a0b40217010503850301d05d02d242c4034054418103604000c0c07880c0803141c01010f145101040c05030070100c100700480541c64040014045202c4401140d0b0510030080c43c40344d0200d661111808250b00514074690780c24410340403590005012109055940b4810480460b442366401d100702e005480020b00b442407002001410b100590119280803008800300700010b2010047d075188101c01d4602240c10403003d0002801c1503415003000b030f014400030501c0b001d010034030071291030301b00b900200b0b08032004410130070320041d1000650013071b4001200f00310301c50095120800400b0310452000000862190380748a41142c0d105035a5440c0208806081c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 790533875 1250 790532625 790532629
    0x30305040512060708070e0316090e06010915030f081614060a0203070f0c021201020c1b0d050601180e030409050a3b241920070f0213020306 62
    0x9104084414040100b1244c580404010b1420a0040413103041020102c644c014070b88042140e10b82e40c0000280700c608064a0b01024001860120344460301842007100000e001d507010f2107407a6001c002c00c4011410141191242ca243d10441c0504990003001008104800f0b010500c250340101d20034400c075081e40d50703840c4407980741030310141c09010f000c2e1041083c408050b40008074500c82a0107801d02c0c91032441240000b03260343c20080c100341d400754000100011035070400f0481041341009051030100d45901c034024048003000301400100389a00c5000113000003000a00c2d90001090042e402042044000c9074903825a0003a9105d418055212014059116000e010746070b041400402c0700c2c140c021480c01041d0307030791211803c40c142c00341001c41010401384041c07040c00c1d03800b845884600030760700c010040701124000c00c483d244400c2190014246010010b40920740300c0d0f06500f400910207496191070380f01950b212860845510300c654900e10b00603140c001c1548034241c400440141c03a4980001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 790535125 1250 790533875 790533889
    0x50c072610020325030219020105180606090408031f031b1202180601020111040e090f030406020d081929040b180903041703030402041505060d240303050405 69
    0x141118006006004000500c040d41d4151100002d13161814400802007290a5000b88030b07401e0a01821544110030a400b2601500000c0c001d1a1030040052040c10b62030309140c58480559403581d03c4653b51000c039020170b0144015507001000400108140702a40a0940462480ea841250201007035402e482003150703c212054000c00201c1c042100080301c903400030302e99482002d04840b40324040c02c046802ca903c00d50100010b11454088142d07103d80360f51007221030003c100d41ca80003034820540074205210021060b20111a400e80041c110f070001c050054038000c40007081085080c02c03a80c81c042142a050240d4052801d81080c1008007030350802c51440e0541c44403403064000c50401000a2054403094902e0400842c120403020481d101c004c1f00604502c00d0742d00c0b0601c2040c0d9a44031072100d49020009502940c0708132020000d8030400e40c056105940148502a4080010701410880c0c200c540c01084020010f11110b10400750040302551080701c0307a80050340090f001003014491030130016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 790536375 1250 790535125 790535143
    0x20c03061014010e010e040f110f1308030c03030103030311090a0b0307080601051603120612030807020114011505131502070f09060e07260103030e0f090c0901050c0726 74
    0x320f05007183c590980c2c000781044001d044400d0180360b86400522008600b0327130102217610304558201c0e40d50301200e882641140c002c3ca00b1111200402c0301c002a041c00300204980c07402e40304501442c01c581c6181c8082d80140703030744041030320f50210408c0500c405940302e0410307402904102100c0d81e00e07401c1550000b40103440082009041c0182007002d0340508290301580c1c802c0ba68145802c404400d840306c1c003000501160761110341c070150100b010000b05500422100d104000c2c66000f0130640c022044c2551a541080c0304080c40284103c541c001c4141c800c0300105040c07400040301cac003541c40e1740d4404007402004043d140710050700140005c1c0030590000c42c0890007040061000d002c0d56041140100b01c1041c09024102805420492206118070b5a10301100b2594000c041000f2580e4906024206080b07600c5000c2c0b14201c6c0184d00d04561a054095601440031201728604000c43c000045d03d4541c8906480e451032b200c4d00800150b496410741141201003582d5041d0841c0c1560710b09c41d503140801c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 790537625 1250 790536375 790536377
    0x70b01031b0509040c230a1403030d0905010b130b0604030f061d3003070315080d05121e070f02160b07031e021015051c11060901050306040507020c0306101401 70
    0xa2001c000d83c3c80060030415200382345031400150b0000340c002445c42c403503a0a110030700d41c2404042c001303011042d071000318211815182101064402a0a40101c9507019405544608144802e10100345440c44a1007101e10a01c2d0024400b00c49100c0501c100007283d0072401140d21800100784018080445604080e940b01c408090121607a0b0821390b05010042c20f0408050f5610117410640c40020241402090070074180d80604ac41850001c0c0140e200140c0040b10b03c842d03101255110540e001e803d100914800c18010044d01d50100854080030300035112000c500c10600180341011280c640d40c4d0003010704c4c400907a5102a5481c2c09012145c216100f81c0c40911988610308a5075004540c9032602580100000f4004c6401c04400185640580000340c12010210308203814090420304803202c9805a12080d0107401d136441040176a10540d440c00d800640244082505410706801180e0040e0050065a001d1304040000ca8a1300008a0b0f0720100b42e0940c0720104903461014000c401d2803502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790538875 1250 790537625 790537679
    0x90603180f0f0714061207050a020c01090302030c0904060b150c15010e01060c150507020105061509010c030804170a05070b0a1112040507090c0207051302070b01031b0509040c 77
    0xc10a000b40c0f5041c1521584000d1000001140301a907280000c803442e40d00e1495840350141401d020041140e0484a0500003510444990300410360041f60501c0459a000f8010035002c070030759017804201e180150040390600d8483c21020300981e0b525181d410b18040d40c240300e94440071030745411454449520040741500c0ca40c80018003514107c100460306450941c1003005015625140022194110801540031a4070301414010324503030642042e0701490040b112081124605e00d1f0121b070700c4c800c000c001408100c6c0b03c0040400640620485940180100b0700c2c10060324800c084e540c8998800040310001035000141c00c0d04102c0101402138002081c1751040102d000d02c040d0602203486414401c0c0390704602200010300b0828204203c1026005c090401d00c903040c81010f02030f56545603401041c1c4a00411031004100704183d109030f0f203440c0c1d001070008040c0d034a181c89690310701d00210b40e81298281c80041c045503503199000640d00a40c0700351900b2440510f42007000e2080c1c00b03400c0d10b080050070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790540125 1250 790538875 790538893
    0x20a0e04150b030105091b0703080f0907060e04090501020c160f0803040b04061d04060e090106170604020f0109150509040605040504050a080c16090207260f0d02090603180f 76
    0x200b2005484c1904c9003582d607206c10383c6a040380041049a007058401030080001004070805910001d0540142c024094451003034581e034556a032965100c0c06000000b40d154490040c5a15060b00b080b2203283c02080014500030807062982c1c02c0c913000c030385080040004e09a0401c2807050350020a00105072040140d420a41407448070b1020b88a41d110340000c1080c240d108081241440320103a02400e0020f004002480c3c4e610155600c0b000e0440d4080459440c11400150003800d00705c40c1d01072604590058610390741c66134200860000e06041e01810003800b2100407420b0904140003100b4001c2e00e032202034a071180c207020002541c141e9000a4001d50802040c040054400200c5800c41d0f03a01403002910f50300c18440403890080e50074043c442d5016200c100003010902c903030050642502030b00007084a0803076910000c407058400300403940c07696010402d400c0a40c500b0400751441c4220400054070384030031140084c000d90019541d020315076200607901031036444200b0880d5030b8150103002901c02ca80c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790541375 1250 790540125 790540139
    0x6060910081b1503090a020108130b011511070e160e10270e06091303080f10090501060f02070602070b0403260a1d010203040308030a15030204020a0e0415 68
    0x10003800c003402c00d0001091a50345507a484006038144030000703488076522854001080360341c0320042141030780400c655102140c100040d2040c8249030540020b01c15440c0e03464040000305c010060680d0004001007240074900b602400d1000c407000b0000900100b61506012140320344441504030418288500e881802c1540c0c2c8031030040048040050401d0720020941e12000355010310000c2c050441640d60030390100d140f1030200f142038022041a80c460b24283c1d20307a65070581c4400c00c4980a40810f02141c0050f550202d900c45807035010081070103c2041a699a1206064820a03082040802c1c01d80e40905410355041244030001c000c2440180955480c1082501c820301c2640800340075242c1882e01006402e501c0d0051101c00c1000040403603981050300002070070700365078081b960701229188920301c44c5580300005403400d49800c0790050380355442d54001440103122a00d60540001c0d091840040540d43c2c07840035081034000c945440d2131400403042004204c0d139950f20f03007005139080540c0900c40c80f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790542625 1250 790541375 790541383
    0xd08070203190f110709060609090c05070b040f050d0503010305060f0c1801050c0a08070506070801060e06280f090504090f021c1b09050a0203040b071b05010603050606091008 77
    0xc8512414191120f03c1074840840340e207107106900202c0e91242203400521b540507940303c2000c0720f449503500d120346500c500021040d10806403038040001c0d000d104060110300e1507a60390b40c00910038070964445410740e98605091a252403900c0000c02d41c04001001484802d001c06075008036503081240c0380d842c000c448143c2da070059034440051807829031078402c01d50340100100e411008425048441c03100d81c0d45001c40440c0d00c850740440c0c0500401000c1107182d8000c0c00c2050580c0c405403600c81c04407141c441030100700d03008440c4030700c0151b01107080d01c020508065080601d0f500907a1b00c1d035068041d4208050f1000c507440c1e00c914001c500e444001d4022510000418a01d2a0b044070026217102e1050345890700c48002d00c40280c40705500590070083e50707901040b420110380e8440c206001a070390342803142d0101d001c121405460030307202e0305c0083c40c2d5511411001c81c0b40d400305080b403802540c1548586007114030641044810754031070414880144cc00300812988503011040300003113181045011030311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790543875 1250 790542625 790542667
    0xa0902010225030b15040b03030c030307140918040606150221041a07022b0f21090e010806071d0a05040906050411150a050c01020d020c0d08070203 65
    0xa403411040c164209407100a03030030030095411040182131410070800300300c80c00501550080c843c030324180c410020782c1004010340c1c1d400b295140145003960f40e01a016102c81038002c05403440340c10100030610341c40e500d4448042804213030005101c503601d840c3c90400d04480703da030040e049240c20300042c4601d040d8006104440c2c55a210000d52a100c01043c240b031140c051a00244a40d00c00c0c10107014580451002400b13819000703d4194003228109046862001707400520b00e40103281d0300c1400c1010500484c0403844c6d6511401c02a45800fa8031254040b201d0220200000000c10281003000310340312105800f80580710354400f9246908107075001400c07084210b140399004086d1140700c0c09499403010145c0d802840f01500034881c008440c44c00c0801004200c0f81220442d01c10082e00d003550034001d0020700080302c2408440c0c82c1000c514415111900240f01002d080c0d90208480b1034030b5000c0d80040c02c44901c40400500c641d000c1c0642c0540b103c000249403808541c001e00c000a84140500d035000d203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790545125 1250 790543875 790543903
    0x602100b060c0c044d031501050903250801060801060506031602150c07030809010606090504090f06060b04150f09062604080a02162313110a080a09020102 68
    0x601030b4560f0640b10800c4a070819042e841c0044090034004202904491008010014403000078158416481ca507039000590b03010340342c7d0301514140c040c03d50140c4010101040c0040c00c540c00400e1980c2903100f510b078820710300c00d007010b0510000c000e501000d0040f040078012160090200d51b0424000c1100ea000042c110207000c00700300d01440c00b146c002d00c00707940302c0b00c850300890080780b84c807c1080103c1da0140201310005481c50f000070f41011780600c2260203548803a5070385e0044e685031200700400380c00002c006482075910a0b400b100080c50714424000281203401517103444d28503000791200540c810480250910410072243e418055206101106503035050914112003984402005e42e00302c0714a0074807680c0ca1070201480140aa102d01034101c0b9092982115010745031045104e1401a240c814060b03520000440300000041032540f040250750301500c0d9242c0300c0c14051030a82503c6240c80c000e82452400100218003a40c003914050344550480c0c001d028061656000039503d121808a0781 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790546375 1250 790545125 790545131
    0xc0c03011e05101205010c0f08130323031302101403060d03091805060a08072702090607211707080910020403110a24031a0a0602100b060c0c04 63
    0x35036980f00c00c41440e01800c4c0e01d002c0b8188020040c40c015000740701e2529080c01040003661125440c5100380300141c80750901d155681c00042c80303550b040d25000503941440c2d1010011810644009100310060f510907a11825110081c0a25005000040200d40c5950040041e00da51091464000074101c0b60801c20a40c1d0503014544d05040403214074110741c02240324001141141080b000442c2c22440c0100740844082900b0395030b8096613555400300c0c0c0300342445081f001007404c1c0c400d9a0240c0310f4800720300f8503001614140180740014800e81c4010700403a840c0c00c0c505003440c07141c002914000b908600310b003041c1800d010740103802051724500501210401407600000f030030410050041660441c0c800700107640b616140d10b0b00c220391400d0091002c0c01401c00900005480041b0004150381202150b10510f010480800407009000c00c080301c40c102c0f044012040f5420744550b5810802803100e54040c0c06c100c042104c1d40c5003511000310089124000612904214020104406101d510112400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790547625 1250 790546375 790546381
    0x1060206060913290a050601030b15091504060f09060507081902070302310c0c0b0705040308071505182e020307170f0f060906040915020c0c03011e05 66
    0x994605684124400302554001c1c20520500e80c2480c4d600e4010f40d4100b03400e000329a190001102218103200307019034130014042c0404c0030060340c41c00600760504090000c00c0040c01c41d101003a242d42c0568050f00c0092006001d070000507600004c040003034203d41c60124034084040d11501140d0103890074401c424021580800200d41c001c1000034021075020706404c0141000c0807092001c8541c04440300c013064041e114000603144640b090001f204c0c041e417a48001711080b5211003054081c02010601400030800c00800401d40903405030103454400c41c2990b600001c8000c410381504ca0240c1001d4030706006295440ca4a1130104565407200914204004002d0241d016225105004d41402c3c0c0024800010b100c0d40d540c1c00301c0c0101100001a061260603100c2c0021001d8010046840056075404800404c0203860011300b02a00428028070218411403692500005071011101c5498515800100d5000b650414012034840f840e00700e008101a0184500c3c8815a81402c3d0a02c440155a1300c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790548875 1250 790547625 790547633
    0x170c0313080a030c060f1808091c0b130f0b190c0203030717100317070201142b09080307020d230904050a0e03030109021314182a0d0501060206060913 66
    0x10681c82007801e1f07001c00095045509000b4282c1d48910300c1c070b03401910740e5041d807150030f01003c141c80b1a944c0c1c8400800134541d035030803059521074460b6004641c12001c10809001080340428180c3c02044c00941c055404052040007504803a00f006d581c0040d50024010095032603007100d164081c0081492340c005031a1b40d07002091000380707a9070b00300030405042c0c1c500e1318442c50960005801c0241c03003078030380c44c040c421905000400b1340503540c092000c030300c10800d2040a00301e0101500d0030243e41d1050204044905e681c03244070f55081111a280140e100503100c05000340d020060004152030848000307400301c5840320440e210301c66400994004c0c1d85a5000c16160034850344144140301114094030303180d58440c52484041d41c0701c074000448026400340003061050800c10020705844c4010449850704100b11075414824400a00a48603020494041c2051079080e040c8031481660600003540e0300c0358800050300c100c8506820040456100c00c0170080942c0310005a150008030301c405511a450191030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790550125 1250 790548875 790548881
    0x171009021c050f06100f14150c0c040605040b0a0303030e03090a0e07020705040b060403120c02040c0f11060103020d03050705011b0309030215070207090207170c0313080a030c060f 79
    0x4080400032009807510400d1140110300700e41d01080d1401502c525888440c20565120094046da036107a400342c00d410859020301050300186081c01909030046110800d2030740c2025000303441100c0282d0045038a500c00d0303150620501001d0001190104500c000c281b001c1102081140001002c2c596904503078601c0450400641e0051400185009809510340d01020034156080c1d6800d4003600c50700d0004140d51515014490040402424240c206859600d4040c503450031f6450708002d0100f2508150090b840c1c2d8020780a1241241d1980c0e10030243d280001060043c5081003400d0a4204400600c0142e54600c040c09840c0d80501d0200d4443c402d6040150040640107070301d80c1080314002503480c041d50103406c2a103981c0c0c0203800b030380c514a05410303110055220131990b00340160000d030420711800095a000d010400d00078280d802c64583d170704161000581c0100c17501c0c00716500210f20101d40e003a101c030b0f004010703100100c040c1c4486181ea950241400d14140b200074205074036840040d861111a034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790551375 1250 790550125 790550149
    0x160b0c0d1716021023092a010e0307090506030c090903040504110f0307020703021305100b180402070c210b0411010e1c030306081b0d0c030203061f17100902 69
    0x201708804500380c0c2c034100704e103505d052503800c0000315000060072005020980c03408141c1c03001d1611400c400c50040000844480c0c000c250305011400300c081c44039840402002c2c0161003221000141d5060000c1094501034039803281c03030f00c070307040d00b00c02c0210102010003507904846051314089a454000d0310021040c1c01400b4402c0c0e02800c01000304223245500090010446c2e000361452650843c03001084001d60f00221350641c0714032883c0c182000000c41c00c1000b03041c1c01880c102e607011200003007800942680e100b140300f51249600d044041c4110011540303070030360322420035003000c00004455a555a0040e80108040d04100d940100c3d043d10342d0160445101080c4000d10ba02c6c02c00000550030079045100803016000246008004a82039000190419034441c12944020312000c5007010005846810a4111014a0301da540040141c6080040074010310a101001405042d01002d440e41150f0030390100d0741c202040c0460a940c0c0c0f1000c2480c456189210f0307008140000d031800440c3c4404080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790552625 1250 790551375 790551403
    0x307020a0e09031b03070209010e040f110a0807140f0301020403030f0819060b0a120c0c0f17040f090c03020f030c031f1205070e0f0711160b0c0d171602 67
    0x551021130352050040002e00d50103201320381803400c59880301c1d42e134070040004580080100e43c2c1200c154010584481c80c003251000020a0344400030744602d8020304040740e6511071620b201c4203801c0007039903140640034684140810b9008609091460304c000f00b00c0b031400c035591400d0103480f902140c5c0d400221011040482c021840c148203580e502e5685403015448040098000341c2c80c2444c0204030440e5024144000000e60b4410106007401d0301d402c4255441400c040b47d032030120304402620340f0107040c0640010040304d184684024503018400044c3c90041c40040205441081900605200c070402c1e00d40000c40c10046035241d68541160b6202c0648c50300c0035400110480400107149503145e064185947d100b9001c1d184840c2d5200181503c00c0c07c1516511031010390741000620b580d1288252018440e1110110340a00d0070102260302b519a20b600143d03270044000403220718071142008038081c22205072500440b140c0700d82442000b01680601010b560404e004d03800003080b442007150841c81c10702 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790553875 1250 790552625 790552657
    0x90f070b180312040e07030b03061b070609060506011202041a1602040504051e031303110303040e010e010512060601080412030204050a1202180103080a0e01031e1d0307020a0e0903 79
    0x10100c00ba0f4940043c0300749408a0100700000c1c4e0f10520030700601d004018046d00400182d100c01010b0009000780602c3c0044000b8180415804560079000b00d2070424024600014913003040340c00103103000c680e40c20304c94185004100c01c000010820484040311404012040d0f102c034500c0348492040c0004040196009081100340030511001180d88099601a0400011803130540b10150fa1240034404906181450f550707030402c007084007814810f03043c08008080e0781c5000e45580d015205500b086e04820301c8000010b006000030f0600403032600340c400c0050010069490004002040d010f0011700090240c0b07503448079586540e010381c054074041c000082410050700d46072607901040f140744280680c0318004d50011602c081503110881d0781a41c3c0c0280103d03181401c90f0340140c800340c1c41000178504140c0e4490580c903260b0380031040c1403c9070324440360201d650501a0300d100803107402c070300f0054240d0700204006c400503650000d0300b0084546100c211841e039602d4800e124118010780c0305120701c1d159 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790555125 1250 790553875 790553893
    0x15020304060f09150e030601140a030b1e04060b03011802030615120d03021809040206030112170409050405010e0105060303040501080a0b0411071209230301092405090f070b1803 78
    0x85c0000a20403d62000d42c201d1324141c0c0da6161070028560894200c541002c00350345d040c4045003101c3c60496000304406807007103e00d0180410251803120895041c4c03030316a0380304c19068040c5828040c486202000c10520618140f241d00040d4035410b010700801c1b040401e0709000402903c811400c3c80a920300705c41030782c078240c1228401501031347c41100d84c00c41000514155a00610340b07004410b010382c1d0040e0125086038240201c407410383c401d00c84140c03811f85007240b01015a951450051002c1e0081002c0480c441c01d1a00c0c103030742940d20b00c04000900b81d04001c04c00c1425140041607e0448a00f40303007141c0307181c03508154100103050b00c0c0c002075082810130344002001001a0005c204140c42240c59601e200d59144080f180c0c2c1265000d00145411503019901e2010391102059840ca2001000007444d1003040c0d0340d003d0390707000d05a140303200040e41c01015520541103205082e8031541c10b07005803441d005501c5800341c946610b801401111040801d82c04507420b5044004480f5000c06001c442d0098 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790556375 1250 790555125 790555127
    0x90c010519120f15170d140304050a0b0403170609010501080735040309060906050409020f0c06070e1504120206070c1802072f13140408031015020304060f0915 70
    0x10180c5c0c0110714400320ba000c11014010000980313805c203c01195940100c18806800045107548090015110b0b0301c207038941280452880400d00c0c1c0103a200fa11000040305030391220002c00c80006224038804c05150300100800d0742c1101c84681e000312603150000b0759038031840c4daa02c54008004030380c00420191212203079410344803039034031800350b0f00036101c00b010107588040849448400c1d000e00780c00501d00340820020150550003600d01c1d0070002e40d9290900c90516241d030700c0c00e501194124009902c2c1c00d81d2032041e09000518412610149442a00c0c283c00c000000e5620310300da903802401020005040401e00886900c10320103000e06210240c10030403c5021030019400c034450999603078210503070781d000500184030143c408950b1840c08841d4481c60804100460100b010745280c040d8540d40c01c1c0c01000011184507224505c1103040d1600d03030a00d8980d990085c40035070081c000d16500310703029000c49a00041541e0440321140b03400b043e414403081e02110310b150750760701c11106101c098001507051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790557625 1250 790556375 790556411
    0x3020d060308181804030903031b1e0c080a081605030c03070b0f24042a1709010618050601300b030d050a030e0a05070b03090c010519120f 61
    0x5414129240910822000184c040c0c0d8102980c0042c08143d00c540300f0030000340900c00b0b401a0341603480016900c010252039070120130702e030400c00d038612108460f0002c08104402040b48050400200104071001090b0790b40c0b4141d2045450511001700420018010040100121404609800d050706e454941d6450022094102a00c158800502c510300160740160750760948014103660604407030b03040e44c040d000c1c8401428182c007030b2000c4242c02c0c00c3c0b041d0f60840d0422010540c10183c2d0740d2448002c0c0c000b41c2015451405043c0c4402c50341004030401c411a160904201e0305a4984000181522000016580c4814203c911258400c080a0703c0c8000301c0c000b00c00c4001c5482d244000d00100070440201501ca6588203032070808580d06114194850b40300b548240d012107400c1003250806070003030311083d140c906550f00000c0080000010072500f50f030b0a21580c401e041081c01c1c000d0034600880250122903060044800c01c10038600d108540508241d0000c00d500c1400c03070010010450725070640c07910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790558875 1250 790557625 790557667
    0x110c0f0601031e030c020402130503070617160c1b0e010b190201060b1801030e15070f0306031e0204090f11030111090901122a09050109090209060103020d060308 71
    0x100d8443d0400c1c1803909a801000241e2a0f64035580d00b140065440e82008025008001840c00340881c1c00c1c00894640c030204444006400680c454440e030940b12020b803011044001d10b1042403210800ca200e0419402241c1084905c2d84464403600040709074402c103881c0202e80e071203900005030761000010601c0f4840002c0a100f1482c41003070b003112103032080c143d00f41c60551182d2600c10804210114080e10512102c64002405140115050070007840480c9072102042510886080c0d003801d0089440d00721141001d030500038101804031618584940e804c155030b203a02440304008900b01c0a0031503980703a00500080d030340403a03400140e0500d0300b0180001e01403000306c00e00031343c644201c140104d400b2506480707503288002d0216241c0da00304070301c401c813440d1038110440d4841d510f085064404540e800d03100342e141c0c440c846101c02c640d00c0c01d6010340036680c040c0e000040141c5020007000140e203503a40c58980c0f000080c20050380d1840030361040310040ca52a88080d0941b4400701e804810380003d4000a80c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790560125 1250 790558875 790558883
    0x121602210601090605101b02130b0a03050309010807020f07060309060b060c0c0f042a0203041805090d0804230309210c04141b0702181f06020d03110c0f060103 70
    0x1c03240d4164807054856034220b80d40c40018070744001f840001407800c50030910042d20f8580000c1a025000f81c04105030360b005410841d9141c0010403c0c1d102543c0c4114519131002d12803000307100184000410948410707160040808041d01c4850f40b5040c0321154000c9545a1005004182d0b90780d07101804540740d101a60a1a208401c203840242076403405000708241e00d2a50075113980e00042d180120391242031103002c001c055010074040061003042c029024454810381100201c0c143c5004142d1a0500301484400b0090081510034040400d02c85400b00e25118050003004680600c0c1403000741c90350040301c408651002117511400381003080391314200b0101c6584030840e0309403d000010482a20f80a203001160b03080c203800095201c0008900121003003031441c100904d040000e03008101e40c0308481c3c0001464148170340034068140d2501d04a003e00d200302c0040c0080c003c1c01e244000351903203109001030301010340369034030540801141422110702c174105100315110700204030101620394800744010780b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790561375 1250 790560125 790560139
    0x30f051509010b060904090507080105010e0406050a020a080c091f090f0801020c0d0f2601080606011103031b1204050c010210020406050412030c0b040b0108121602210601090605 78
    0x40c00c8544140604076083c80010300041c208003070b55003404000c0925a40680d2640b01d8040d0000351844284a41030282140050391303281840c00b8208441655030103880031100520400c000c40101d40e0001e440390304255100340840e030303030022040003414110040c90100d03501c610242e010a481c0f41c10031380c01030031140c00c550100010707940c1d00c408030301301e004441202032303d900040c0d8003000302c2d8801d6260000d0102142021071490180b503401c0386500b0f628580c41c2502120200041c0008001004500c0d4403c2c000d107060001a202020855100e0001800030004e0480308074485500741138020a44a00448001841e5040c1c5010300f801036840700c12060700760140c019500707009103082d05c1c2c7c0212002d42d0744a4980c1d900d0a40f81511b0721107030800d200c90503000c03c2599908440002c4240c01170074060323402170b102004c0e2941400a0355040002150a00040350010040500c5e85c2450710300c0800c16980442e05100031790509a0300945d0150f42c3c0601400500034500040381345e00c10366102c401941c4040d00d40c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790562625 1250 790561375 790561381
    0x1b0309100503160c0c031b0b0301060306030312290102010e01140f010e010b0403151b0e0102120705060f060f03030a0305070e04091a041104020f21010e0f070504030f0515 75
    0x1502d0140e11513401402c11804500c007407000c600102c110b00700405036200c0300700b1340c00c0d55403106450035002a00010000b03034848400700180b65210303c4040712008450f500304201401e0f03d1440051a0548145036544014210300c0403043c1c0c002c0d030004060340080c40c0284000c1c42c4054951003141c00480348150880b51f00c400200715010001e0420b030507202140012450541503480b40c40c8079600c0380c0c105a80745030b1940520364441d42040904010000180c036100f807010030240000e800c0c0b091040c1142241c10050009c500803d100081e046d0300680c51030120541c0e0f03114440440c0c1d0700900c3c0090035425100008800f099a0741c580d101c2032041400e5541c034100c180703031f80e0100015200e032034a029001d244c034403201800b4514140ba000e40c00a2013140003030684034a0b81e000c02c060b80c100e00414000b0300c4000c00e0741100c031a8450f070000101f4401074003070700c8c1039030429030301c0544482c024001100411207140041ca060780220100c8000d5a042040010001c94a183c0150703940c1c507413901d0600310a004408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790563875 1250 790562625 790562627
    0x906130f1202010f0c0f020a0603090606050306060d08090f040608060103060b09070804030f02101e060b2b0e1501090b09071e02100c03060314070501051b030910050316 74
    0x19080740c1d0769059642840c615502802101c07045443c00c41559905605500d41c0300680e96021007200a21407601d000c501081e0a007461030031210715500c0903020303402c040100041a0385190500f000d00764080f11954031601e0785804621844000d91485810074985080412030080005d1558102c1c2d1040c0e04c14007400d06140c05001c0c4002c015111400401c0c004008140000c0c0600c40c6120303d20418412511501481c40685050700c0c4070100c0307001074401c59907613000c1042d5140240009403410651007440c08400302e8036180d502d1308405400510342110550164541c0654101c400e0071426070007103911585407000200c2c0c08040030b101e1805514a81520759080f424095a014400d6100c0d80b138240800644981060711002d100a4003001c5018920014003442c80b5481414800d0030a40d0700050141c0c00c40c604a010100842c8d0b140045601c00741c1e080080baa0b03c43c040312050103901c0c2a0b04400210b441006182d40a03080310709602c480c2408408507203607031020180d4803628900d5140400f0007160340b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790565125 1250 790563875 790563899
    0x4022d040329011a12040c0f060903020603070e03102405010e03120a021f05070206010501020a2103090b0901090c050d020603041709030708030702190b0d0c050906130f 74
    0xa0440760110300c5000421403525086000400b0780ca440401070320f000d651a40818080e80112400c8031f00c540034a4007031203801e000481d00e03006800181400303806541590001010b81c0401001034013001100304844031107480c1401032402c41c2580c40c0341444100c03104141007180c6d102580112480760300d149000190b640c440c12038030800c0e11001d005800308800c0795550850b1580703c2c1520100390f10980c40140b14280025000c9941780300510780c00922130a00640080c01c00b00c06130310060455102c01840e0f00803038034500103425503116210100c41039610400043d07002d010800300c00341145181c2c8080100f1000c0640016071801d12a45031844201e403070f10700b0000c2d10448010060340000742807000400003042944032414040b003406005042880c20400686400c0080d0054a0300c2c0d08041a18001c5003000c3c0020840ca40c0c5031640b11902c5410b041181100f4000d5510141d800d0b9103850b4000e07903850199048502160015001994440d9196107049a0342000d04c2032410344a0064400141c0407540b038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790566375 1250 790565125 790565183
    0xf1409041103070609090f1e320105090703090203060a0b0102120721031811061303051b06071a1003060219020708030c0703080c071503050906060405060f04022d0403 73
    0xc1003401100c81002c0441c8c0040c526081c10b004426502041c0d60300d007107074010242d00301c0d400c0b829143c8410b40c1400c06010810102410300c0b418941007005074030040c2d60110b1072541c0840000800907002510900407403030003003d01c404201c00c0200040000501c044420911104a4000f00c15203610452072000c8007202e03464a5612070b00c41c84105842d00107241c06070785030f82d186d800404180c2801201240311400b01c000d940204c85c1903011215a44170f0000541c01100340040c2245d00134100412034594800d0b1107440c0103014214250080040c0005400e40401e40144d030300000110348031100140100403051a2083c0500075103d03402d000110b000c0e0010894800030402005001014510794900d4010341103030040049030702a102004c640e0700e58907502491320542c0741d0b40c04126800d050b0601410f2100107807400d8021801c02c010040c441d100d0400e03100308964250350060380c0700041c104941900d00d00741c040211240d141c0c000a81c03003103590300c080d2050741d00540e4a1802d0110035900e08030024404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790567625 1250 790566375 790566401
    0xa020904080a0f1e030f09080d0b0a1409040303020d0221091006031e030504090213030204051f05060c160f0e091603062007060609060f1409041103070609090f 70
    0x1c12241d44000307210b601b200c034100400c1030780804d080c0210380d01e4150b190003258001409941c0e4100d01c644030b14011309880010305c1c1d04000d003d01c403018074000c070728400001070015040c15000180801307013002030f0b81252021600d01d24000d07084003856003400c2c80c084003030b40e25181078483c00d50031445070f80461064000310f9130300c1140c0f0300c400c00024020f1b45030682d13080b100781c3c14003405000000b03007008203000420407011524409070010b03003548104400c44101600c204981c0d90072040d08103030b1903040700300d5100341c0d10103d54083d154000340c3c011518007810601002044500c4190000341000440d11840c1600c0c0780d5034000c0c1350b55a03903900b026030b10a0711a070314034490300e10080c0400c0410300581c030540c0900c42c680f004440d07128644418400b141d120b020211030540d6680020400022944651070180c1000441103814074030781820080e14604500540344155940c5020800b000202041002c1d902405420340d8511559888080e04042c510f116070800c80b400c0c40d002030380001c001c4c8108003e240031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790568875 1250 790567625 790567667
    0x20f1b040b010e0d050106050316060e0127030f021c1a04080708030c0a0f08070c020f030307020913031106040816030e1207031712010302060304050a020904080a0f 72
    0x1008054007044034240d0501000152110312a00c03038424200c8164055000491b0440c5800c05161401c07507000c0f0f45000c3d4242d414000d200c134039401816208080f1091801d94034500c80304081d1962000f00c0e0f07020b0141001c402b40d0002c10002d0050140800a008a6046603d407402d0781c03c2c0c01c00030207920401010786000d07a41c00d440c52aa010f880310b8006004100c01802d0960f82d0799070380c1c2070781d000b901c40c0e2580c0700b008a410409164050041812144585411021400c0890014021a40300c0d10300900c9040e000d8602c03192500c0800940b4619030b001408111603060041540752a01a00300d001e400044060b280a80101030000d00c0c01e004a61000c9810301e4900080001c041ca2009110114200003c0e040c81e009540d96a1102e00043d41542014205070b903d5850501c2c50544015039010032618207103c60b0700c84002620183d030440e501650015520fa4852a01d68100305e80510002d5100481600b40024000c82c2406445040e00d0b580b652242002c03044001d80b502c1000d828912140c9075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790570125 1250 790568875 790568923
    0x1207030c09090b0c1b0109140d020106030c2120011101090201080a0b19150908060621030403080703080a0b120a03051813050f1b071e0b041101020f 65
    0xd09080180b0203001d0644180845004245c030443c29166036081c207580320f100b00c0d401d508190809101c115401407e60000b0804180307996915131000c00d142c81903800b40c21100c5080507000313068040c000a10366001c8120301d00c140098030030380036515441100300d0000e201503620081400c41440b8100a041e0161030b510380643e51000400007a103449001e42d40c04c030130b40c400c01140f0b078005c005001024141c030a00c6000700c81c0041234010819251035201101c5079004906204280c0c4030150100150303000010050540000b140c002031540c0310319031005000c0700c0c002407a402490347c0714001c1d5018001503402802010b0086007000a84c6143c9803040c00c44d908141014400603025200070700042d10341d25109032089200c0e50004942c012000a00402c064440c820880f00901c0e1200080e40150410803c1200e440b01e031418101c40d003c2c0690040078400505869403000c0e030210360f410043c40d8400180502c47c9024034007403480b4410003c00501520905c208801158004038142c95500403a0240c403404003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790571375 1250 790570125 790570141
    0x5060a02030a0b0d0c0305101808300a11030702150a0b100806040e0111070b07020309060a0507031701180b040b03030310141c06020310051207030c09090b 68
    0x544003400d075062203a81c4003020709060304d5072402d00c0c40f81c0b80075560b10140203146007406818000d2400c9251415450300000c088500f168041d01c06006400000341d5440700200c60140c0003000c510940f004910000b222128024802c454155100341180c6009200603203001100b60450b002c1a5400c80144e0000c150038140c1c180b0100b40568000c21962011440b03004040221746407685030801d074000070b10300d4001c12480e81450300442c1600d41e620402008550885100500c1e075006e0301c0300041c1a01c941101007004940b0801c182e030781d04100202055640d00e000c00000e00182d02482c01240854074401500e01d41c01c041106003812902e160307210f00681c02e20300440000030b0182120513a406542c0e0000d560950301c003080034522500c00084200d04150904e075810303c88080c034040052003410101c020000342460407a2000c10343c3d52140b0050303182e48075106411004840c68100715004070510700c842c40340407400240102203134082d43d00b40d4013480d180e200d11810744401640281442179880080b0700c210b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790572625 1250 790571375 790571377
    0x50306090928110922110901060e010f11071206060e041112030403020102100924020301060905040501140d0c0b0c030a0305090309130c0c0206030c0c0d090305060a02 73
    0x880188016501c0481a00c0300c490410103a005400a00b95181080c890070040c08903000000010101c030182c50b9450006240588541100f0528040c859006007031020050f403180f940342d04900081807003940d5070b19103400605c22041101f000d07000074140200713031034154040c9401600041408018122950404442d400c500702c0b14041103c841e98be072080050b00e25000300c9214011480341c0140e00341003813410100003103640c81e01c0020030107810030407080006030b80009190b28010003d140105d6926000c0c1040204d1001200c8134810104c2c41412500c1201015030085041e10003580300d0b038078915255000d00c01142c0003405a80344400b80030400c02e01501d4040c08199855200d1500c0c06a800d4030742c090040103030001404200c19500110f009103031580c01d4011140e00c9104040214100720687e0001007003051003403910203101e580c405d00c2001d01403169601c2804c1075006000ca50342c90500c0da40b240d0140d80001d42400480c01245103005c0c40b54803510035807049a81000051450b034840d00c00001c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790573875 1250 790572625 790572631
    0x40614150f131b03271e05010f1e0c1b1b06020d080a02070b16020f01021201030506090d080a020310031e0c060e06160f0807050d02071505030609 64
    0x100072900034804848200d20f009035646804462800e043d2842044009002d450102d601101d0074a102280521070f0300c450380001d162290002c480c084811035010382c1c103002003512031000c0c14550034840e00004c10181ca411444030903c020114143ca480041d080c4021644a0801100010745803040e032002e0690910140c031226000702500c06068213048a4540309003510341c443c40141e007010640e404481e82007a030403a03011202050541c545222039544800b000c00c000d21315840000880c483c04103c3d4403c00100305020442c030000c40d0384500c0e020050030621024070040312107100f1500004c210000204130120304520700e845407030040e142d60014102070b4200410300500c1c591003a00020101d5000c43d0110001901800c800da1281414200181003120b9500b2030028080703007055000c05a105c030421600d1004e0f14943c000c2404240b450030050f00c43c80d0b06005000400086248030034040080741a0060802c590203d50245644a80d201440d0011035010000f00304188005900c072300304680b0340c46e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790575125 1250 790573875 790573879
    0x11030309030426010509070e010608100302060c0a06150905060604060804030807111534030c0201090c17070905160c020f040903020c210a020123070308040614150f 72
    0x941c41d00c03c40c1120700311801107865072025401040200b1441a0070284c5602406080c50594002d25044a099140082521009008200004403c505010305101c00501b050f48000306100641c14a250b5100610150080d00102d030700d42000b0408034505079084400700e807401d444030185a40c0c2d030b031800d80e0076900003440c0c039061010411050a10160074404c0302c441075103600c2482094203003000800b14185c0111040c40f19941d0704070344000001c00307400e07418022020514012401504c0400100e000d1303c0700102c000c242c194100004190308025065070660890640101c454469540c00c030b40341a20782c06d4074018160314089002006c464400c1c0341c81500d807400904807001080c60003000c1001c48080800c2a00181c21130005122189043c050710f82c150f01a406c540c640001070340044503100c42a0300070080c1030200401d10345051000c464244000c2046010000343c0364641c50501170b00c10300003101c04481e0700c0c1c940180c003541021303101c1d80b56009000c0c0d501a810b0108810b82806010901800426 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790576375 1250 790575125 790575179
    0x90e040303090503040e04081c09030e060d1d010207121d040b01050702030a2003070612020c070b130e0601080c0901110f010f23190b010e0603090d110303090304 71
    0x4c1102680072450b940114411030234a980d034509894060340c1d20000708401544071f801c18002001007a4043e81c14505800c040714160b40d11800f16604400034511030502d1541c08503041004100450103602506116000d00090121543c503200101e03050b83c02c42c054203207103401c0a8903040d42401c15a12008602006042c060b140c6491600004c7c6001c084030001c42d84002c54440c6102c0403134290144034010309090f00109001420008040d0102420b040c40500c666800718001d98200010480040242002c10001d40e40b440304c400070040808140c01041c3c2c0c00000ea6020907110352003500f41522400f00e801c41da5040451020044461604440f0403809510130701c156a0340320b102c00e1091800154840a001030620b02d0119401d2801280070f03225010f10b800c6200700031844404a000c1103451107448000a07035a4200d4005842e030010144280c0d400ca1030120802c002c180c00000c40015500da6600c0b1a07050001a05001c0e642e84070860f401c81864006100400912404002d080c02d12645281d80d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790577625 1250 790576375 790576379
    0x90c080a0e0f070b1e040b0d1a130905070302210601151b030e460614070804090b120705030d030b0a08032803151406070b070302130501090e04030309050304 69
    0x442c07955000354000c7e030309039917001a00040e407036440e12486120032a0503a9218400091000013907091500c1011242c0302d588514a01c07041020912843c00a55401090b0341c4914104c0220802030048291860000784a607400100d4178490506008600b54940d6450a1500c0e04240d04c00a5108201c80114240300a80c2c48940b102d664940b00c210f8034160034200710701c405604c00c1c180002a00044900740035460000100e1240c924034485090a4403d2401c0c140c84206400301c41c1e02c40c6108003c4041c05909000c20082888852600091100c83c4200c48140004034000e030a1915070130701d4800c2e150f1641c4410300194000340030340c200000d0340070001d041400440d65840d2160a69106002c25901585294401800c0780c01d001c105520402036841d080042c00180c401c001554200c900401200c00300021401230a0764501044400c01c44e8014050300e0389007860040900690009080d008040b0030360301002c1a0781d4032980800f001c80300600c400103000c1c3c4444c0c07010b42c02000e4605040c2d420780010000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790578875 1250 790577625 790577677
    0x902030703060c03020c1c030b06030c03010e040503040e0a020a08061f080604020408070308040f06110a0f022e080105040e03090d0804360203010305100e0304090c080a0e0f070b 78
    0x1000e585a41000500c07c016102100d000302203682034076940b1710612062080c402d0144411054078151858104801101c0e1150300b492459401241c3c000381c00c01d4810300400c2000842030b006001500c115031148a241c3d1141000c0000124038041038007000450301349101c0200e8802c480440c1c10200c045d10061402c1d417685003503400c180300341d042a510b548000400300040020140e40b00000d01d0285059800501402d81484c0c55104e541c001520300e03034221009100b556503101e120b403052840030300b0078035414109014120b102d400d4001010041220f86000140c02e052074040e1b80016008840610720301800441002525214031000b40c1d00860103000100c1c414805a1020803204241e600041100880c40b030b03440384901d80e4406d4203008a00600c01040010000034001254040f4081d002c111524149026071841c003840c3d00200301d20781041419048a41c01850040c000c251000c810b21411400105982d91150f18405100c8540e02c13120041090060359009400c43c502401901d104c0c0e5500700314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790580125 1250 790578875 790578883
    0x319020f060d1e0204120b0c0f0d1b0e060403020118030b010608090601090b090a0b040902030105010b0a110a242a02010e010501030512070f02040f1e0902030703060c03020c 76
    0x80900d2642e90340e9a20814440c000c2c090b2070002c0c90f030441540b40c40e013804150480e0700d02030306004041e002c40da000700b981100da030020f40308410b40034aa00c0340c031032844480c0030010700701d1001d1842140400511241809100d0340c81c2d4081e410300544440d1904d4515401142c017218890040d0245484c810710100025121100030b50081800f40d0742c419140c00c000318000d003002d0042c0d00c00030b1098609019a0002e40740c00b20110303844000c6850006507810f03010003080203007806c0354000f5499441c180002c5042d41e0740d08003070800b10026565440440f03c03015402c035070700e0540750b07805011280c80840e8480c00c1c4100c85c410105a6404c0340c00400c12251220541500c1c10540708070b040700c82d01000c2d002c0703240340d42445084a402c2d0000d00038040e40d4510b84401f0307255079a1201415921f01b002406074217002e900d94481c00d10540c0680200885c0101d120094010316100c0483c240302c00601c030040c0fa005507940101c0342400e0b001005044498030f0369560400a010701b0414105064007031000c264442d400740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790581375 1250 790580125 790580137
    0xc0c0b070c1718060c01020c19050a35130e0408070609030c060c171608010605031003050a11040e0a08030703020304020a12030237060b0402070f080415030b0319020f06 74
    0xc00160b08c9500910308141003201c0503401d60f44454a416406c0e01003000002c1200001d50801041e092031011070a00034480d03004401071a0904c24450105c5d1004500745000f0b08480310302d02d80d04e00640340c40d4585c0d8491041d080d9405024000c09018a001043c0d0540c03042d00f00e988a4200200604625564241171748c40342181c49001c502c0c205070b07001004c0210b01d0f410307034018025800040503128a0320041d00210042c001d0100b0484084001481600b11070421000340da000011140d0b0b0315514a000c1410000519245014904000c05901d0304140008ca100c2c0842d803252896045a95401c0d0403002904000c00070381c1c5c0100344181c0041d04038102c5903254400e034049d07400b802100c40c544421002507005880b59060507441d01041c21040c5854003c190302035944040301081c06803020740000d01a0040000c06014003140c000c02000300100303500148103c0b41c40b4500b000e99003e0951055045a801008854260304900c030090802c583e02000c0e05001480181806c01004d060301c0850407030381001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790582625 1250 790581375 790581397
    0x41706040b06060306062a07080f1605010f0e04110d0903081f030f02030f0102161104020405060d0b030f030a0f0e241305040c0c0b070c171806 63
    0x102030000740060000010340c0400203461503440c500700350000c18964466031401d51610905201c08500c01482d500c1c1050200d8070700303000c995103103442d0a0019100d2807559444489031042805200c02210701d65010030443c0d9050711600521310844c40282d402d0300b103145009a21603a92410000d02c40070b01400b80907569410030000520018910740600320482c040c2c080e00204080c000c02e03008200a1000d0042600e078460b4074541d0540f0b0034800b01e880d01d030305007085940b1540041403840c43c507003103a500c070f42c00302c6c2c05045020070344980b0500303020403442980150fa403c540c04000004003041c2540008844020141c1110314102e080c200399411500402180800503c26617180c992041e404800c02c206d00300c0132240424440e040181c3c010700b16180c1c1c082d81c640340b00b0108080c04046001d11100000300400741c0700b80030200c4506001070803014038070022510100d495000ca60b515100b101c845180076807040b06005c0088403251034410725007202d0309604840500ba00d41c10950b407100c5001e09184192 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790583875 1250 790582625 790582633
    0xe131203021c0b03030306120a0506180d0504080d0507030c06110a0909060b03160909051303080109140408311d072f06070903110a1d0c0417 62
    0x4942c51403501841005141c0c40b40b603003040c1e07841002d0750340072041342c0d0043c104549200f0f0f00001c540c9007d0038071074110405402409240c0405c0f0300361204440f07500c118000034041c0c991800c1c02d201d003500c05004034000e0b0200342c0d0101d0304013882c0301e01800c014100c141c0a41131043c85a80765548440c01da4844800c448ad8102000c551400740e250400c02190281040c60020300149080c640322011a001c020080e01d910350084d001d20708c0c02c038050001d0001801ea080000d00081c640104100785040c904a412000500010000100903040f40300e8148007503190004c00310283c9a41e00c40c80e0315034000340c00c911028242010010459101000c1c4503801c0c002c422291014540341200812407100c0304c8800351403503200c080402c1a41d650103500302640d40c141060515a2281c1d8908402c8942c8071141103420911580d81402442d94001045e001141d2080c0703030011005248806100b032001030b5102d0711030301c46502005142c0d000511100140d219100308211402c156503031040c02d0418001a952946c9504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790585125 1250 790583875 790583887
    0x100512150907050a140912120a080708090613050f150a150510120209040c08090106080714060315031204060e18010902090a0b0a120509160e13120302 66
    0x4003a14156488003180c2810f41c140f600809002d42804d00140c2e151070b00110015100019030380c1c1c0d205003190030b8010800c581e0f0b02403103c0d07403038071065000c0300781230000c20400c000042c070151050030b11510408009010b4011034030313400619000350040c144200d07030b1070040c8111440e0f00e4404014015519448032178002c01414145031600c1200d460010581c14070420042c10701180d10350308941021a0300303903c0c0c076801d80c40320300301084000e010f0950400e48c000d040415075001158407203411400b0f24401d2008100240c0e44a0605540d0030079489107860b41d1404442215280c035020000d5a80041881c46840c16591060300080c10400b00040b22410350f00003040030b01c89285d012030300101d00b45007035504030000e030301079032620041103014810044080c3c0c0018200c0c6064580c8460740000b021404d072140c2c0c8441c003010028011450104002c4011441c0c800004d100c51400a0004050300950300b0f9004071505100c3c0d080cd04200041500143c061680c1d60780b00014401201c0e903200031003550300184c4400f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790586375 1250 790585125 790585129
    0xe06130317160f02070e1021020114070201170f040311062206020c010c09090c0804110910081014061f03200301090608150c0910051215 60
    0x2052200c900c1c0c40100300e00100851034140c1446400b08007080d0800910340d00110303800300d140400c0d82e00302140c0184c09a05010038006003104000540d140c1d080300446007410000c8100303000d05001d90280c001400d025880d441300ca50040104007442c01032412294003042c4403a8030030605003d4400b403c0c00105d030400c00091603804401c9030044044207000e80113a052011444d809912070030b41081c801009003883c0401c0102c6941115000d5405000034007040c4142d540180004030a40301304982a401c080d0034030045071042c9692481507030b11802840148402d4000c0c025101002050000705416405001c20303c5401040385c500c007001d0040b07022910303001301d8010b26504a0090074050051031a89106078511403802d02000001460f80780004006820200c0b000c09404d84444c102086400040040340c46145030300304405440500d000c075240c5081c1040300b04e899103803c07650f20914030018800d1f4507443c50800000b03045003071189030590400c00d5514640040c0b8905071040c174000d0614801c1e403ca94 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790587625 1250 790586375 790586387
    0x90f0603010b010219121106070c0212190609050331050904051903030f09060f0c02060408040311150a020f0f0309060d15080102040e091b060a11010e061303 69
    0x9144284050042403580c41c45c0c2110f04000c05000801460101e50240301d02403051500200030b142007402c80da1541015000941001e4100f0b5080e805503400c6511594007002c006090309003407915403d5020003211a8413480000c24084004031000e000400c07041101644000283e21242c4422103081d14024400f20500d4204001c1d90003180a81d488004000114102040d072005000121510340624042c500d41100107040811400d2180342c80c044400045c800e43d644840036440a001c0100701c0300001020990761582c048030014803200d401c020030310014400c04005003030248091310704890030810000c0881690803041c0403800583c010102c18540c00c0040000709001c04446000d1460464420003007041031190031540481181c44440b041030100f88840f042c40102402c0700215120b03600d809d0310703202010096808803402d110f581c18510791fa00b003880c4c03e001103001c01030015141156013007041d19111803204d81803585551f81d0400c00070360031080c843d4920891740104e840d040c1008618025000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790588875 1250 790587625 790587641
    0x50610091a09060406091a010206010f0f0b0c0709050a0b03012a0302070201210c120506060d050a1e060f060503130605130c090b0108061206071805090f060301 70
    0x210306100c11040c00030784804440c0c0700d51209a605560555885001c54064a41c1d68804002203140850f002c03011400400c5181c6083e20076420348400b40d81c1c41e00c101c607642109005000512201c1003007041804241d1000300902c9000c501a580c00541d00c1440d0380840c0c4044a41d0803c041e00d0306e24411843c42c1c01e00c14070801c9440342c8904c5220f02c2c4104e8440030300b40380740803101c420306600181010945e80079940907140000c4408011001000400110014104940c50000424441c04448490b0115801028400c0d10042d00c40d03801c3c22000411007001c4d00014011400f5540d60364080c04500509000b0315003aa900c4403030100340117140424120464100b64049020085c050050110801d201c0341081c089503040000450b00791a003c00c0340c003901400e00fa008000741a58200020038820326040f042452009032164006551030000380000c0d070701c542c1d18a9086400103400a030400d802051500c41e030907a4658003010031a202e401040d0440c6040c7c1c0d040d0b01c03000c050020017070f5501e024064600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790590125 1250 790588875 790588889
    0x110304020f09090607140c06090d0816080a15082b09050d0609082808130b04031404080a051b0a0302030a0821010909120809150606120103050610 64
    0x14242c0f50400740c3c1da03200c00340545850200072406c4d2813030301384d81c800d40c05603644001a1030075960f441c14031403950b698404071581d125005c109620000780c501e41881103821042c40054075140d881d42d0381d0f41c907011300401001c0320244c0060a0a080421052410820382c00b41d80d0341200d50f6000c2801e078040c03095041100442e0360b0300300900c01d4414803583c0c03100f400403030466902540c003040c1d8005500c1c201c2074900a4006d40310f10810003000c02d0300100003246a040101403d901c41c04400e8072a03003404408203101443c0680903810036000300b40002c0c8111200703c51001c1c0c801445041c02e0701c40071200d042821000054400340d1188940b0403c3c4088006084880001183d00c04640c52951780442d80b0b07000c1c81d06d0b01420600000c41e40d040450441c43e016060180904500101982c44102c048001d165026041d0390000e506052484154001c0c03503214091400980140042c07092401007a400001c001c0185402030010301025080d04541410703140a1071162000e0915464480160007018180790302c411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790591375 1250 790590125 790590139
    0x18070503040203101a151608130501230c0a05030307111c0e1201063201210b03100c090e22082a011d0120071401110304020f 55
    0x120115a01710004218940141c0d0301e0050041e51a1002840340034084132820079400c55543d0070104400000181800741414003045481500c0d41c00440380c42c0c1c0041c50301c00c0b030038030416500400184198054620b40503a242100c80c00d910594a86086030010394091000c40d00c000c0c070220702058140442200c45240c0500a48031300f02e000c0d40285080391f500c002a010b06400811540d0340303082034004802914400200b41c6089050810030726500c0150940c00c0062440e000a2040304c2d84160b01801314106800c41d8080303d14000c800361401031240320310040d031602c1014403801e59812940142c0c0055a410784402c5061031800f0802a440040146019840b20130165868100b02c00102071814494202a6481e1184190045000b40c13032007880900708906a01c0d9003c44820f80150410080303202c1c207180440308201001c5142d420380303540b50202500ea0540d020704088200106018114440c02038015141d214245c004450840f00032081d0360f005100000108070a500f407281f000c8250f900103403040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790592625 1250 790591375 790591391
    0x1b0616051006141305270d0e0103021204080c0c04090c0303090608040302031c020913060915030203062412011a0d03081305010608030f030f061f08061807050304020310 74
    0x34030b0701420004c0030400720750b0318030106051003215152801c0d07102220280c08030010a090f0310315034546000d581c1400007010f040a001c1075500c203000b0380b24428504c0c0300386079160312190345541d580d402c40480740905214010740003645950f6401404022409101d648010605504004140b80003541184052010709003e20000035800002c440c80184002c5d0b40c1d562409440307080c08003038415091240c0c2d11629520240c011081181d010000b240c0c1c007900100320341e45692111400d448200d01c00698190002030003d404044030034860704901401d50480c16180b136410b40082c1280e15003001c418180da543d001513500c000300c55121000303080b40c104c80007019881c459800811201c070082000c410f2140f00184402040341c2500444058080441500d4489241d074a6042594004a40c7d0200030080080403844509000b04600c5040101e00901180d68040c06015116a4030151440f5080070f808569001e40d41c0c58400c244d400340003590344a40d03a9007024010140740503161031424550a181482c0303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790593875 1250 790592625 790592629
    0x1020a03020a0f060902060708030a0608061b0c0307170c10050c07120e03120a080109020a05091513060309060c0206150121020a0206040515091b061605100614 70
    0x910309840d43e028015640c0d6008a00c0e0901c0502030113080250001c0d03011034114104421000554802c0445440400085548500980c0d0b20f29081d034082c2403841d11900c1c81d041d03100b0708a004288504403030b021a880c1c00d6a55070b42000c0b5440821700002440310101e0b400c00401d02c14010f182050440300ca05000c2c41c20214180c5005210b043d43c02050006000d007100b0903203025404000e051400201590381300455940c410f0402d0340581641400640c803000041100c0390f10740300361104040b017a0f8541b428811100144104000d8610700740251840038801008a010800340800150101d0313600822109124506141a103070391601c5007081d50415001c21416014421045c148100c0918080e11008840d040c050169034500075501c1402e1300005295988075000203026004606c114100c4480d004000e03001c0740c24020588200d04103800801e2040c0000341c41c001300800000000380070398039003072400803205420303c0d21f584101c1d4070b904103015039403001043d80328410007030603190814802844c003540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790595125 1250 790593875 790593883
    0x209090a022104050a12020318090c0703030b1c03030b1003021207030c14120f070215060108041a0a0f200306210a030908060109020c0a260f09030c01020a0302 70
    0x1800c80030b11607003000240c00c2c00000c004000c3c0058001015400c00c030a44c0d03200944941c080c246d43d90901c010b01c00c200c2c484d401c048208610410140c040d080c1014465a001c074084c04161061650100000542e410104110441007440da0310a0300c0014034203c020051001301c40444850300141072041c003050003910141480703194030009601d80003070541e00401d410b40c3d00c40103500d40c41ca00c0703a50104504c400c00c83c0d00000280110b614020301540c550b1082401c03a95600781401d840d21111026020402550140c6521a0458825004111034855540f10720303074a98002c55402d50b01d07584650310455001181d2051141c486c0828402114150448020189030312024007114016442c400906510004490b01c1ea030803070240c101610f00034106424000d108003500d0060340850f008032400011990703294800c8034115840b1402900740c1803610307100d9480480d1600e10241420701d8500c503480001c0c03038801c014000401494912501c6d0910b400500d072820255106a030b0656101444000100350005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790596375 1250 790595125 790595167
    0x1e0207030305060d1208060301060902042304020306060d0e0309090702100b01023d020a09090b0405070e0d03090b0406021b0f0d0807050a0605160e09190c02070b0a02010209090a02 79
    0x420666031b26240c40021a00420180d4011040e20b03101180100d00c2140c501ca81c072103580c5443d02907000d040820b0782080200d1000b41c919543c086001c03c101c45138052950400b2002c1c40320f8100780c90802d400400800d03030032181254040f0050300009000304100080d03104100c0d06840a10041012255803800e2520b0030070f480740c1c5076a62100400d05554540c0ca04691130304d21221428041d515603424900282c09643c5500426901c0c84c10705540c1c10036400c00c0d100320b6125036883d0f62000f07080304242041c8003480441c0f01044ccc0402080070004164001018003e00050516038021f200d100f403c1441042d120340c0a200c000d2050703a0640c2e09044071394440c080d0b05602500403079400d6440a00d8540b01c1e1801c00c803100001e0400c1d06243c10400c0380c1c117210030700c85650916030302c03041c0c00d0100c5401080702c81c9404440d006d84403161300300c040007401116440541c04518500444450726100c01e14a4040c0d000414240c0c0141e400140039120382c245241c1d20760f0400c48100d815410900b0f050b01e060b104090030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790597625 1250 790596375 790596377
    0x1b010c090e1f12120801060e03030f07140105072312011a04150c02120d0c060c05070209042303180d020103093905061c1e0207030305060d12 62
    0x301e540400300c801c1d400b109900a0401c052101c400d01e12500d06080da4640b4820200301080c00d40000203101c602a504042d9240e40042c003551420000e80800b00281c0c01240040e203400b10149080701101000340701d0310340148280c0e210b02c86280032403e41c030400708025511840c1000020300c0581c400e14a0300c071055041d105039040d114a046403803503a40410740070f294406442d0204010100840a0b00000100d80c0d4074002d4070100070020081e403150750b80d0342c1150044d4000500c19990784c004030f100c2d68040c980425062500d985004034540018030300581c00e07a0700340c0329441d48140018422004e400b8050a440d813080166040004145486a4030800200420300802c6001001000c5a06c80c1e400410350660002c2440c2411040072006d0307501051504058150389450344e0490450f16500701c01d81c08446004008a103425117801511414480c0c410421910940b52680405485902d80c002032012071043ca0040c0c580c641410000d00b0b880c000303040c0500030f050560b555000310720742c01d040600000d45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790598875 1250 790597625 790597651
    0x6030a091106341211160608040609030905030a080414030a120c0503070c080c01020c1504030206250807030806010e13051017070503070b030f13080d021b010c090e 72
    0x420254140f4103540d00014441c002d0700303000c001d0345900040f0f1101c01041810895600c01c5c4014098401c07401c0500828020826150001e4002100340d004601281c0c40781c9000c0350846c0e581c10100c0d14100c42c4c2d5804645914000c03400340b12041c16050b1010842e0411030040c031580140ea20381c0d9006580c00000003080104060080c814004100215125075504c0341e002c1c0640c6644140751529071560081560060086041101141ca410513800300074644048050789080c6c0b443e030811101768841d5030b40c0c0010b8003101e8070311183e4141d003001c54840c0340d003e803c0d800c1c1e07a211186401004d03d50000c0145042c0303c0d40380e01c1640640c0700c07501100340781d032a45000001c99450314103640741581030a91018003501d401580403000700e2400301d030300782c1203410690031a040e0710b8845c4a40e4180380000c803403401210b80c0e040d00150301c03043d140c0c95071950f80740a20545c5140c901d41c501100e040c0c0c2c2c070071054600011015080c0082c03000c800d00c69842e09621520386508001d04044030060344103405001071060301d403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790600125 1250 790598875 790598947
    0x3024306090b0a0b0f150414010e090106270e04060509011410060314090a0201050a140301140907110a0308070201140f0f07020304030c050607080906030a091106 71
    0x629038080498030380c00281c04125460000801c6003e0185001020f00401c401d203c10a81801c0034160041480c0c280420f0a00300783c100712310744031159642008941080442008103800b83c4401c66903d019085503590101351030040c3c602520b1140c1c1c01568080e00300c106002c01c0001a03e20340c0140d400582c02900401c8a440c1d0343c06d82400341c2018075120303030800f50320818403050760780b80070780e400844805460900c541d29244480604034081200c501586810080c112401584240010107090760a810010012a00304901c0308260b0030903000340718080a00035000302d0754038180f1021903000c1712900e804901c24520301610750329004c92090007000c1c01040400319034007600030740008440007401c5111500c5441c00c2992103d00c0c2d002600d542e070024803c04082010648080201c500784c0760001d00c0d802d0b80341c0ca88420f10140d076201d050191070031002800a070a09070b90384402180981c1056034089602e4103076042c501e003455507605600d445034a04100d04c820591250b02c40c280c81c8125400702c0b4441c00e07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790601375 1250 790600125 790600133
    0x281106070501020d0b1203070506191103130507050405280605030d020303160e0a0b0a0504090203040f02090901022109010608010509030a1e050f0a11030a030243 71
    0x3004004000300345500100e20060180542d43c018102204221010b205142c20000e81a80fa0710480d60050100c1d08000005515407a98040d00105d0b0320110398000b480c541000d21002e03036600155005026a860040c0540601c10f041008c6c00140a088038100910f00b85519006030324215183c807508800d00342c5505603d800c2e102da204000404015080d01c034405503d5074000d450b64003c41d0403c841e5010002c2c1054440d20070f82560900001c0505071240d814100641011035800044580301005001c001c0420001318034006117028a1250882000160301c07031040140e00c01c0d0050400c10140c2c07041c44290405c3c90b09080c03d01003140c1c0c501721070a840d168552070a0250601d60010780b0150300301020710100c800b000001b052000e0280d903c00400c0001c0b02c1d03082e50003d2032407100c50000b600c2484080301c1c0140510081070785004900304058405c110b40c10f034600f5a0040c5480b400030941c00704e0f028400e0310640115030101007441402c00c01360380056600e01d146180541450001c1d100c1204900100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790602625 1250 790601375 790601377
    0x90c010206010f060c030c020604061214010b090d080702041e0e011a04020901091a1e090d0201110114090708070902070f060c020a08180a14030a020103051306050f0108281106 77
    0x87c0360054102690f66864204c043e01795410407031040b0905d49007400c00d11000305020f16080c1640c0200000520b040c05150070408403000f490f805072036901042010b240103030344c0c51041200e56044c1c40c0c819107140104a10701821a01020031551160341021801c0c5030042501c00341403803180c004c580042c0c48100780300040324000c2080e0004403071203a00c810096409411b1001600d99040f208000302c1c03182c00d50400c1031030280202c1d02c5181e0043c01d00c50070b4000640c040c5004d905801c0b85030300000b8a00010017200300320002c0c01ea83c450100c2e0011f07902030051882c20b0113801e000e801c29520541c601440d07507540d0b0684904244000d006584e45400e425140c030b1007800402201e80d04100f1164031a01c941e00c04a104401c9400610f2080c2c04250000a0919800c1e2401c01e0b483c03802405071491191580040d4040d200060410018070540891400040c00c1072083d1030147c0c04e80b0381c1c4040f1a6051040300c40c500f61646030301c00003501800104001c0201000520b0a9150340019401500c001b0b5402054175 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790603875 1250 790602625 790602647
    0x3110a0c0522020d2013050120030a080601020d110a02060f19090503060f0105010512070201060b12040501050105090f240a0b07170c0a140309090f090c010206010f060c03 75
    0x107502d000054079071301380070706400025600700380360003e5100c905a101324103002c0c41441d410342442e0500100402031076004400300e0003255031041e078070400c02e000000002d0075036001000000203d40004180405941d0402401442c030240341420302c00d05103000103440d580e00001c0402445080300103520b41e0b240f281c40059903a02d5030904080714410403070800240c0b0103806401268041d220304400140189022481181261030603142c007890302d4035a030580ca406000040c03000342950340785c2d680000c0020880c1c00a004603440756418a41d130341030924106003035030f20603486a40304d216410180025800c6d0141a590003065481100d00b040f01d0702012449030765800d2000a500c003041503c001003040c00d40000307140342d500c10304102e0f5103810b8100b0100b619000e80422201d840c0d104901101c0040d00c8003810544c1403100104030303400c0150303400c00110408011505d101902d280c150600c00c80200401941900072002d002501c4030b9030608003038101d4206030340306100c2001071810900c0c09150043d05c140c12 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790605125 1250 790603875 790603939
    0x40204050a060c150b010c03030b0a030c1e0b030702060708131a0411010c0537051f0b10080c16030e130e030f1e130303110a0c05 57
    0xd8010750796040606401d000820030b9410013203090380a20451860700c01c00582100584a0f001000000d40b4214000d002e14540c158005140b044080046403040f44100001e11883d0f00380d0841c9070300c0101c202c5485c1031070390201040780d1052040c00291038002c80c2032075020259262245096690b1003401241041d00003016100300e4803071450141007246400d046108a0050700303000b06084250004440d0452035480144c2107820581c01d568284941001c2c0d8840301d5a5501a501542c0c01035400400035440c49900303c0b46d591060824600100d407401550030f900442c400b0400c900c28a14002c03501440c1284045c5040028aa000800d01c00782c100c280e5400001a40203007203003040c54030b000340891100c070403002c2c071440c80108000185a0b190046104d190301a8001d182080001900214035070800341c90b613020000145410100490820041c0000f8103100c91100ea020340340d800c02030000c203000d401982c080d820001e00100440c8810f42c585003142c00c01d407075a000d013032064100000350f4621021441 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790606375 1250 790605125 790605139
    0x909021306030b10060f0915170a020408060f040c1206020d09050c030609030703120b010e13050a1d0628150e010503030a020d03051009050703050708010e010807031104020405 77
    0x2c024001c03500d40703403031040303c00b003000600d06500c80300d0070b40d441e001749a0010001181d0b41c1051141c00414500e25403232160504047e00490407a0300c1c12900034100f108d8520150ba070108040006d030504001c00c0d0380090590080c40c0701c3d400c00d505c4050104015003c0d0502da10ba036014110100180c940c101ea00c4440d000300b040000560310f1410a455610038140503100e40700c0c8101044036940048115803900b54542c40d1621000704000c3c5130390140074600c8805042c04848205507015885a00c00c0101c07102d21184002800e1801103c01c00441e2144804038440d00705807803c20120b0030001035880e420004000d4408411002c8000c00c81410080304001c81600342401500c1c003070807419170f6a95041c1c0b03020f40801c2d0340c940c0e2a1001d00d640d80c0500c401a00050780300e023210400c0c46000741d1100d50004a44040c2c010181d4031181e02c0c0d025108161216400280e80d01c0c10840019030284106015000e640d00c0040d01e94034080c1602d82e58011400041c04801d405008c004140d59198111001020302415035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790607625 1250 790606375 790606379
    0x20708040b0d0f0c030204080a060b0f21060106143c091507050c0111030c030304230d091a090d0506040203061e16030e061f060c020a0909021306 64
    0x50b4014100a555180034a800c040f03400010728003074026030701980d0b51a00104030352101d0352641c0b4045c054440c1e0507a001080e0fa4415aa05d07129034810403515000c0a034100c2501c0042d0401c1032070b18005901c40300810903405075500610f03404004680c50242208225240202520707403201d5140b0000580d2050440b400440b03041078080400904012070084030501c441007400d4107481c1061050080c0105107802001d2204110760080d50000880c0d9148400c481c100504801c5591541d88262400e0300c412024407540c080800210340a0741c3d14034000c5000d440b5500151300058082c0c109800b032903450a2400c194001c43c030407542c041d02c6003450000d121030038600305400c103035859000c240d40c10b9000b402820300140c40710000e840001303041444482d903240550f032104c041c1d8500007110084681010341725188110822000c0140d14000c0501d8105d8808124108042d0088001d50f640308105011802c12080d016030b59071a02c0204a17194480302040900f0144005070703039000d0460031b003060340e8075003100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790608875 1250 790607625 790607647
    0xe0607020124120f030203070503070b01140f0109060503090a021809060f01150807030f09051501050d05031606060506030a020a090504060e060d330f02040810020708040b 75
    0x40c00384140303035444405186042c2c2d250381d5101c200b607026044000001506600010782110524080c0030b000740f043e43d0400e41c05035149429944010400d03154070b418240140000d00e1a141c8e4414106000c0b521000b0040c2504d001074018080c600c2007409100c800300c00904044414444003004a5008281a003140e000200060b130340301c810364000c1f15503c94130000801413480038603260b058030800d10303082409402c5401c040350aa403004014000f055114800c84542d06464054007007010311a0000c0c0240c0600c0f00600100c94030141d02251090b406442d50801040c400b00454903802c51955916080d800e46040010141c2403c0d8816508800000f00700441e0310030301d0380949030038101c0d591003c0100d9603600c208000c1d1480347c000c85001c07860b0700c0c001c10b0480c07070f01e0341c40d00070132901c1040060581c04031891a200318a1141c00a002200340c40140d0035a401910b01c07511464080c44042181410700f00503034a0b87d24290fa51144240c181e000405e1820300800b8015100103008212803540d030b070903100d03003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790610125 1250 790608875 790608881
    0x110c0f2211120f070905011d06041703070203060619051c1208071101150b13030c0b07030215040c03140f0d0309150b01080703110904020a020f10200d0e06070201 71
    0x80c40510018203c40450415442072040108862050755410300c080d00506164450044400713401c2d5105008000008038440000401d1491000340405503450b02024014141402030040060b4450f07650401080c0d68031101000301000c9d07403016211f1412249502800307000d00701c0c4421000c0c0880741ca900d05100c8032640f10040901c101541d65418042c6200c440b040e030300740c0c1c1d4080030403444038011520a100c0010031101910f4110b0002180c02c002c16070b241c442c0c0c0b07100350326a080030125403000070f01d5000f4990104140070000c5c403009120701083c6083d8a81d000c4904842c080200150704007108602504420803402c00010100340541d82400380400014009182092007110040c24280400c4160805807041001c4104107031104c4141d5500c802089000b00080700c4d4114030302000740014180d68699201801c1c509009070010140104d20620081c9001008000e2484160418900b054640300d0103241149200c1c4512010b80ca071260141448041c05042d2081050b038420380081281180d8150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790611375 1250 790610125 790610131
    0x4090c020a0b0c131403030d020a03021b03090f09040f12051306091505070507090b13050f010303031d030a030b010512090a0b1501051801090302090106110c0f221112 73
    0x84c0703030000c2c490fa203c40c181507086541e132106915400034002c1c54030030305050f001081e05140b00e14005141403544080f102e00811804540240f0707510210320b00f03155082003504038818000844400314540740070f130b841c44025070010a006052403210300f0720384441c034010000c1e2035807100f0040714061200d440740401419a03500b48502c04010307216a4891400ca030080c4100d82030180c0280c090001e0a0503c104800a03050661800b41c000501c00780c408135084161158900a50074003034040110b5255003802425034401c01c5444150b07200313980015146940000444051a0706404d01141c030300900001662140144850b10304a2416130041000341c074004030319409081e202e0002d4842588038406a80555550089000c1c04100d0030441c02108446031280800c0840c81490155078250722035003c10139069081c0d10510114900c11134030151028244154001000291490b86118020100149520204d016400203044805840340d11244240c0c011171200c1c0200c03081d0070303650070450b8030b000c2d5420030407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790612625 1250 790611375 790611397
    0xa0203060103180203100c110a061b020c0d2a0303080f1006020705120109080430030818120315010801080601030b010509180d03060501020c1504090c020a0b0c 70
    0x110001050b00f0310f10031032001803190058010b140b80c3e00d07580b000728000c00d0381003501014086e9081c1403d002004c20420304c0000792281300085082c40b0700070300041903080718070350b840c0540d00300001d034803225228285c0b100b80e0b054118070445180c4090f4401030619005d0050a4404a40190300100a264101130854040c80c84160185d00701e41e0b505c150441810441e010307110040c0c004107410456443c1c1602d802500070122000003a01801039500d0188a610030f81c0581c4080c043c2c01c0c80c500040d9000c14050010110f040105844031303549641c01062044000c000d0000208842d010300100c0d04100440c1c0c1000c202503000c02d5503414450703e0461081999841e5900041c090300000c1004400401c940303040701e5109038581d030140d0034002040030321031004105401140039001500100803003040031681303141050b20f00260850810000a007001000c08a0901a241266046a03000b0b1000c04450440c1d4400200080320b90107400102d00b481c07130f10f0501902184410003404203107a038100003010a6491 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790613875 1250 790612625 790612631
    0x15030b0f0a0506030303150105280f03020c0d030c2723100806010216030b01090e0d08010303030b0325051014030601180302120d080702120d1a06030a0203060103 71
    0xd107090107040e19001c44100350141c00c1440840e00214040544070342d20641414114141280c00c944004a20009013500c020400720006601c4000d802082c40790141703200e0700c0d0541c901548150959950030066200c40c0416a45190389122203101c0d080c010810b14448600c0000c2e1503090300c0000029506000d03120f40203403599285070351030407884400802c00c070001d040c080c10415099400d480b455401006641580103840401d8022185845076102441c41600d02c102d0782c1d4104402d41c2c0446203c031541e0680c1d80c0c403400000010b1364008201c1c50440e5071510b0003085100250380840c0c18030300c402040010344034140b00f00203104044d044003481030b16001e40d0440d0000c1c2c0740900c219241e0980400e950002c690030404a500c40d4481e03900700c140c404c1050342140035140c0da0b5000c1104118180e001e661950080e18051250541c030006441d0845c505100400701c151113141818503520481140d108000e81c0c6842015121154500f00c3c404c03140000e04568880c94940f00800280d4021982c1c01e002a01e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790615125 1250 790613875 790613881
    0x906060d11040e1c03060f2603070804230f1014160212011401060509150d0c08010816062105090d020705042007060f0e1605270a15030b0f 61
    0x8806c2c811001218500e4904070500d40c900021000704003c01c00e41d40640c2c101e540a09095020200018580b00d171041d0720139552103182c41c00d11102a1419202c846903c583d05008800659990000e5440c0e10400c440c0021071440841c1d095891541090300c0c0c03400441c02080403ca2829181848803046000741c81d000d103540c0c501c01d040ca080782c20151550000000f8580103102036413180703018041680c00500103a106003c543c03a509859001101c0740c05c142a190f00d680c610031540403103043d00400c00c110003800241401680d03c401010503005003400c2100d0304803a03103d07920007207503000740c0e40103c24020840d03402c015420507103d2454010380740242c45008000100381c00e00e0312a541d1088208108007a03501030004d01e0340603503400740c0300a0f02c0241d01d030f4240101100c4103218050400607068003c050090a02003014040803166000500c1151042051650700d854445954a000941a5000082d5981c04490300c001c02003c541100d030003c09d00310100c20840c09014550245801c0300319014595 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790616375 1250 790615125 790615127
    0xe21010b031005161407020a0905061c050c0f031e0a05071d0a1e1104051009050d03030e0a05071d22120c0803090606040c02060906060d11040e1c 64
    0x10015030301941320f40015041c800881c0e119190b4180b50788182e40500340b40080c26000611003040c2500036802a5680300140301041c940902040120070801607824802011602c3c2d250b2680300c0042100d00501c034855842401d0390b018019641240b00c0384600e440c84c180070b002c6150340e4680d0303000300316141d11030382c8004502e100c61408414460b10000b84d002c8420394031001c544001d0b10002a6019462005a2241e299650706020b2511080ea40303502440c0c0303840ca81400c01028891207111482406012401840703140c81c0c1c0c800c0c03031f400030341c160070301003039020200101e00d1415110a8000d480c0d030140c10340100b50300341c885031403010f58401c007564924940c8550300900c10096000c200c04140c910003ca41c540001c20911380e001b1081245d0800c4009030314aa298030485910072158001c1640251041020b1840d0510a0f003801d40424070082c0601d26000c030020b0f0382d03000b001d0042c40c41240c00000380300c100100081001c1e64440050010b2280d0140c4098a03039445203401400803410f080590189451 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790617625 1250 790616375 790616381
    0x10b0313140c12070f0b0a0c150506010210150e180709090201030515012c03010c17071701180207080706020a231206060403020627011409010e21010b0310 68
    0x968050b110a00301d0700d00d007a0304011b699000a181e0810700a0516090010604040381c028000907020b1001c1402e15003080024140004140c0400d442407034525540c50a070301680c02031003959004c2c0c140142c01d0f118a10075811104500080c00a00e100d4010041980c20f401c1c0c00c105604c40c0b0130b0b02c043c8a582c4440d103080c8440d80480700314034009034a0165003000d04003000903464281c050090040e44000c5402d007c2402e460b100480e407800308000000601e08d02480d14002c0c0d40c002c00300d240c00c0d182220240c000300c0c613040b8107105441c2c2c4004020300404401006504031181a58400c8807241d844101e8907050300690800072454002c6000c4a000c20f0398008903114001c01c00d034801c83c2c001c1c6003030f003400c00e1400d0046010740201e402034020b0101200603100c04c1c0050800c140c0c107040c00d1004003242600c0300380c0c040d80181103604200c28100310840c112000310a440c0c04038000d081c12500401d801011810764985000442d542000c048146034450f42d0643c0511100171007a0b05441038890300c4002c103015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790618875 1250 790617625 790617629
    0x10603050a0c0905070c080307030608010c020a02130b0609120f030a0804110a03020f010c050f06040b040c0618050f041e2003040503040e07051908010e01080114010b0313140c1207 79
    0x2040100b52410000f44d014401154071420072b00340041c541e600d030010b07030b404c4940015007440075a2018070b00c1e00c107501d8180692840070a03c0c2c44140702c1d0004110216005000d8500e4580c0510301c1c000700707050300080034440d11000d4420101140d480e40140d89000705242c50540b02034400d240e140800036510f0030540e145c00e050703070340103898545800b407080011154481281001d8a25004010111784800000d00c101030190340a02840c0c24141403134280054500c030140d22820a0020001c500c039103603082008a902211310403038140041d480c0c0c050110f40a0321601240c9681c45440942010040e0103660124a014100204950101c88501d01c5c51071141b005807005403441d402070008001849000240c641c0c000302d90702d40306042041602d060b0309140000481880030030040340040c130100d0260b603815801082004001d00a40064480d400c007240c9041c01800003d000010001d20a00c0365541e0580340c50343d20114600724a0b5101078940d8a41c00f804c010280301d25090b0440e03060f014000524041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790620125 1250 790618875 790618877
    0x120309020f03010903200307020904110102060711060f1506070309140d03080105090a1d03030103021912060b15040b1201050a05060a03050403120c030e1002042114010603050a0c090507 81
    0x200c01c1031001110782d041001c40a2402040c03100b00008c0300103884219030303c3e0040d44980c00444071110307401c00180c1003040081c10002001401403012890850000d030098014000e190422040c1e11506200c00c10b030601d82000315000b100004101c820541e01c4003005040700c44900012618000c0341d01000b15402c015140900091542d03030061065140040500342c00075a406800213900e40d103850310303000e013079a052200050b07500040010015402c150b4004126603002c0501040014100071070812408107400c0050030b0b10340e072020170504a1b255004d628010414403150243c4036540d80040e01015030040141c6005201c8580c000103036801c0500802c029284010115424928095030840083c0402442076080003001400070908000c03a100320380c012451030f6400b04840c07842c00700d0b051800c821300302c104030f040c0d104200c200300c1e10b200400d5160120849050400e004811401c001805544402e61101039518006c8000104100020009040d0380700e84100c0d200c1e40d80e1403084d4000c58808440e058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790621375 1250 790620125 790620137
    0x219050319110d0e0a02102304150e030f070f03031106070f1d0d15051623040b0c0708190b060f06130603020a1403150d020a03120309020f03010903 65
    0x4003040c2d540da0030001c42e50382c5000448144005d16000a000d400d1b600e20140081080e843c0303d407840680c10f08940340fa480c81445240d14080c035251440e501486010100700801c000550124003568040c0040d600a00e220b004886000b62a208074a02001c01c5110850200b007a4500320104960302054062141606885014100d55041015110212514460071400c00007490302d84580c1c2c0e0b5150f29802c481e029600441700c00300c40b20b2540003203440183c140000103030381101040e10740c5d0b40440c00301881a404207078407900ca1241501c1140c03d001c0c1d40c0043c0503011000c02c54070a010400601e120840d03643c4000c6841c0b515210b99a803041002102024080212410000e0030a041501644401720005070038240b0b004800740c9040f46003071703058100310300003500081d07042c00d441c1c3d02c00c0d4200d42c600050340e1400c0c80d500b4840e444c8a40c20500c9054140161103120a00741503544440c1944021608003002d0416192001001801415883c1003203105603150326448a00b8101403040703104080d410b40b101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790622625 1250 790621375 790621387
    0x40e010b0d0305030421050d14060a0b0a0909020309030705070b1c02031801020c0a0c0504061d06030a05070321050307080a1515030203010f210605040303021905031911 74
    0xc480e15400200191b44000030000869585000e44407110741101e07007566507039107507003424815100796008140100e050a6115040c080d40781e82d6413541c20200c5803040e105a40e10361170080705680241c2d80358803c403400d520120401001c40340100c01861000d02c22801c1c1c4a0003070710340084070094007035010480f00100700382074449803002456000715008040d07240300344c94204444004900b640d00519803054290022112132003048501d400c1280500790448051001500b4038410201c110103010010300c070b14441c1804030700551030070301c0462071140d04003007038072440b6490b410015411030800c1140e00b003041c104582c1806491280c002d8900840e00c60362403145076254076042d00b0113004500b0050700000828840003400b00d014280d40949841d05407030141c1c40b0741c0741050048150b001ca9000c2c00c0c0c0403002e14100415001c0c0081c81c43e42995202e100014151103d0400710000d0203010f105072841c13004001c643c0f14090300500a54404d16506454001202c0d070700880d2001d441011b800c00c06864428002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790623875 1250 790622625 790622627
    0x60a030e06010b120f150a06170604020408030702090c0909010b18030a0803010e1b030907060219080304080a17010b031f060f050a1e0504050a0e04020f040b0429040e010b0d03 77
    0x506900405201035295a12000500041ea07c55040e4800c1c404a00b81600d100c51076510304001a0740140c00300ca08500301880c2c00d0459850f482080c20084c446c2d600740000904100144040d1081001c02808400e2150786503200d120301a030050310458080c0c40704072480a100d1800142c0104065804280c6074156403808001d2620502e0140c4003650100d5408002103101e2015409944200381c0c10000740419441c02c0c002a0070544086a03040d981c020f006030a00100b81002e0450f90840e0748500d880e580c1d480726520841d9800700c9c9101c03030400003c00d00d00029080c0d60300d00166000358130140303000348104001746004125456510031038011a23440041c031021580504040d10820485091031b070240b082c800300e0148041a00b10820010030b2002c902030080341048401c0c80003506910461314418203180c2c0000d441c00208502451041d03460b20090841516503800840007484803849a00c0e41c0e080340202c20444e050311005c802e0040c4d14010500040351014024203006140241c4150000b6041e070710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790625125 1250 790623875 790623901
    0x152103112e0e0a05070501030c050c21040b0a0c0b0109150e070c0203161502210d0f140f060303040506040312170108030403050d08160c11060a030e06010b12 69
    0x60200c0c110781c0c84008100d642c405000070421188180080d1003050708090002d0101c40c0040b00b920200001403240a15007140002c2d80c43c00c90781d0455451100507100710a9003000d208540001510b0007021800070807042c2c2000000314618458240d1550613a02d0b0700101048401a00301c4030040107288200f000201c1c0c40c140495007000d079500e04070808048a401081c540b080314000102c1c50184e00c001040b4000b101118450103200e144080e068040c01c0c20707500c0342c41007031001d08441d40b03210008043c80c0c101c000d540b1404065440c02004d0190001c820001050500308485103404940c480c0001052440e002c021101078650040281c1d041504589a050714050362841160600000700c445007076811849030118000d0100d00000c5a440741140b070041e05002803452680306000c010001d0040c40107040d403142e00c0341e1301180351000318081b1a0400e00000c088140340f59800080c002a01c014040d4543c000703600040000d811a40705999071055040341d445421089041082080d010866440c0c0f0a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790626375 1250 790625125 790625203
    0x923040f03030f0605042a0806030703110a03060908031605040609091104080703080a0e0334090c0e0f0901060c0f0516090b01030509060702060a15210311 68
    0x3c0002d03440e80300d10115040380c00031801d01409121040b85034250054055a076403603640720340340401003818103c0c00319568035a1404020102c1041d181e8448050300c0e8026000c00031900140140088002c0d810148050b070b0081d01d040340b90b901207005501c80180103004950444050ba9104003090b4039005240c4000c05140e4030405070280304110002d001c8804110010142d409115903d5032000c0c0070002524071a1601203d502a401060051140c40d5004165041d07000c0f0741041c2e02180020101485211141e1f42c0124200c94035103440c60440782c0c1d0003c0070800088054031040000d943c040d0400802c01c00174815400041d442002c150700103604442214540b900c1a001c4450880b8000c0f01c0d521010040e4100142c859681e04800034690fa250003072582046000c00a800c1c182801c40d802074481900070008030025440300802106010700034007a9005203030088940500d5851008813009100b05402c00354000f4240403094002c0d13542c0450741525003003980540302540e907903d0340510b200704002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790627625 1250 790626375 790626401
    0x21f020f0d050a0210150302010e03011d0d0210060b0a030209011803060935032208191d0f040608030304060e1b01050f1308070923040f0303 62
    0x4600d948a031140801c21040001a50707202d407621410f881c04028504800000c1c2a0b41c007608040d45010a150303100309000c00d40741c0a2900004003e440c90209024100c0d604603076540543c5e04c042c03891070160124101646d00e4541d03081d0750901e0701090802d4103a45e100d002314040d1000800000004600941c01000715480604106a0403030075604c510318540300310f034816200c0980360b4104200308929400d042c541e0241d0003042080b80002407950098450081501c80c0140c000000840c220881200e0f000c60100511032006400301114a4200d1040d040801c040304201102e5101c8012507028100451400700102004410000090104030f600100f0744001600719951b00c0c030100d103401c0d0604c011840346000700030124075401480505881d2800b6204a25821185400d6000709a03a00c601100c000204600d8043d4a429444070880d01910385640454110301c13135124006860032980d001007200035810450001015905003110308042c408840041c58407000081d49000a40258068407840101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790628875 1250 790627625 790627633
    0x30a1d010c050708060109230417042705070306080613031707030b0f040b01170606040b030f10051c0b100911070519020a3c03021903021f02 62
    0x940c07507a03820041c00da080722250703410480051160a04074041c1803400165044040e90300c41034203101030b0300b6150149c4020080e900d403080c50005242d4401c150f502a0900c9642010340c1880c1d51a56036480d407800340071b201020300305000a88110b0092182c882141e0800018198594400801000c00c0d20020022018000c084608200307032404080d005201d24583e8030f00164404851040008401c02500b901d03104d5400d0141c21081640c0c024040d11762458006460016a150100010030b540105c3e0468000010b0210411071801004000c3e60b01072410060601141d54a0b0024405c101d001303500c9160505000b031030600005415048140c4e0300c901a4114007195a4880c0e070b4045c02d640d04420000c04003040442c41d41e061180c14030200da01d01c1c0103946102207241d0107902003055010107100c1d082e441208100c602d20288070303503080c990307256007407aa140c820050f0011402c1c0c030161150100ba4003d40d0301c138100c1600759000803128800c0d603800402c3e4001514015104070074801807480d40300d0860107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790630125 1250 790628875 790628897
    0x14010f020a0510060e0609040302031903180317010909020f060904150b0c010c050c0601030f0f06050c03100902090117070903020612070215041104020a1418010908030a1d01 76
    0xe0b0900040900030f00d05640420742902d4180d14085820001d403e8621669004060000203078000045030700001c6042c0d00e500a40003018016002004c2e5603001c09425000302149404256011040300caa1304546d1803030b500d403a622080c030304d802c41b100039100a4219603603900c0c100852629038064a00407200401c0801c0d500280802c90940d544c80c4c0d4000014114081032a4403031000a00540003036040b2480e10f03508280720308000b540d540714184005080301840703103561410b0001010204a0310303070304280b00b4019400c004509030b61550084400100d210004140400c5a820074000c0b41c000460503036409280e40402900c030080307090094545000c0c4468140000010b88807000940081c4000d124400284e140040c0081e08051080d0030102c01403162408100c001402000c078082c188500355030068841050a0081c0c82e01c00003081d58000301580882c00d0449a40c2000014009204c02e80c0c134203142940e00c903502903480c0105003a020100b01c48001d88c800d8142144440d000942051500e200884 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790631375 1250 790630125 790630133
    0x1c051b060d02120708060f09130f0c080d031103040b04020f0a080111090414044b201309020f1c110a03030f11070b3114010f020a 57
    0x41d01074420f080f214400d4408008400b50000740300f550084040e640642e02d4402c0070005402500b0041c40110500402e00070b0400f440144600403100642c051880131400d0b40715840d050f035a00c1100b10300400039003402c0c4006110700b0000d05803030003141d000c24511001d880d642d0030042c080c075404500c680c00002880e00002c1d102c109003e941d9000c41000303070b800d41e10000d10082c00b042e1340005024070326000e5403405100025a031900c6044590740c2d07030700403141c0703040ca2a06c00201803030b03e00c3d20a00d1f09160061903880c480350b0b1140c240d8682403040c070450b80320404040d100700e040c070070050156031300c00000180781c20000940c0c1c10000c0100e00c001c1c280180034241a0003d180c910400c8001c0c60242c002001030030070019025030087c0c10940840310103444628641d001404d25402c40a03160810190001c03e02000c0c60030040b00700600050045136448410032074a0301c10610300e0a0200e030f400d6602d03030008640c0c5514021038000359040e13406007422312513051005580000c00e0704501001c51140081c888049 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790632625 1250 790631375 790631377
    0x60603091f060302090a111c0e0616030f0516030e0102040905040b100b07020d032616031103090318031e06040209070512160e0a0e01051c051b060d02 66
    0x341e404400002d0300302c3c00d40c010b0003881d48008010301e0b015464070401e4440f00e1088001c0c0da050049200d58003e0a0a1000300d000250140003424003440c4200010b0201044989041c409540c1640d5420007000443d1030000c400d88200352030000d1042040780c81403407000d1007a0400300c406045000098940741d9500c1001d401c8071000c0358260b509100c0001801801021654038400500c0f0003051542040070743e80002d01d45044c203100050510034441941e19100c1052031502040811001c00d24a0900e0051030b403103c030130544190340c40000c3c43d0016041c1c40c058010705490043c00c0460045060002860031014641c511540312981803041d8001440c1c00c0c058400e11406c205803140c00360011f81007070b00c14060300103005004c1005101092040160032800c0ca2034650b40446010104440c10f00b4800c42032318401259005140c1021581a01185064030f8035000d03170480e0001d075185114010700e042041c00f60440c0900c014115006221002d8030007444200d501b41a650041240389007031102c07002a030032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790633875 1250 790632625 790632673
    0x30f030c03090f0d09052e022514060304061118040c0302071a0402210a050705150712030617160621050a02090604120c120b06060309 59
    0x318000002007007540542440079040321480c420040400b01c0038281c001d01040042e0160034060030110003d0011a0744400304440400d22052001100d4a4103500081d141c1e041e00c00b0015000d868a003c519001030040d01d110100c2d22000b000320300c02c1c0904020840554806002520348a44580040c41801812001003003c111844a03081040030207000703000c281c45805140509142c4140041c3c0f010a81d400a035180314011586807460580e030f603200186c03242e50040c0c24100d0781102080300703185a1b40002103648200d401101110601039540e07003001009001741c01a03521294041c0455000030340151240080e44c401400c02149480c0c131a260711500c2540700c82c0100700c5034019903661744440e280f2881080507103100c1c40d105565070095521410446c2900010f03500159480b800129402c04960595040000040c001907641d030b5554007101030b100101e0400d03240706203405d0001820040754040c510286031310501d0f0b1145035a801c4c0c1040002e420051905d19903000c0c800c609072404000740e0128036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790635125 1250 790633875 790633891
    0x3060f040c0801031b06090b2b0605120705010c0b130803040308191119180803030f0f0f160c06090305180f060301121502121b070c031202030f03 64
    0xb015603d94142880409982040d603400e0009490082c0411540041c0040503100c0456406980f81000c0b00480c40e40c91072182030f0554407810f8030542d00f076500290403820807200100c5801d080448440700a40c1c561401d4480c03203010900d0906078000045d0640400e035442820f161010080001640b14801c09074000c031022000110100e0070031841e42404105803200148040d420002200c3e101c003440b055110318030200d001d104031a0850410709108005002c40c0b04280312041030f8072981c543c5902c1e0349410036142c5000c1c003800c0f00700140c940041925990b02c2000030309404840d9444044c1607251051804110b0000c100c003515400700415a94050626814483d66801d81e594030042c101401c20b24044100b41e100d1140480c25941c955203140549040d2921100040240341051410a0000714003480020400d4008600360925280c0c40e050070f40301e10351080c00701b0000b00c2900790780c0a040c454607500420b4009081001e002082c000072225410702c0540c0116840d22854031000315072034004440100f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790636375 1250 790635125 790635137
    0x8040804080f100f050f0a050901060801020f09011b0b0430020a0c080712061a1201020703031a0d060c0e280915060503040302010b0a06020d0e1c0201030203060f040c 73
    0x8143ca00c502c80c02076030080c404004c11030350800706a840102c43c2c4c040e01d40c881840d111008215424020342c090310042040310000c540c0d488c2c2c68424030100b41c001c2c00d1740c54041208066101007952019042455055000030300d02e400c4e60f5103070b55645e4803285003000744107069610368034000d042965400320310740711903540c0040180d000755240c16000324015411492403604280c804015040039405c0301450241d1140b00400d8500c10014921000100402c601c0c0d400508122850010f0106500601c02d081c025a41800910030410b94641000010315025030482640890340340070840d154000c0c182c00c5414a081c100210741040080c07050500076402d500201c4c0d6034180e081501c100000d2210082480000074001040e001c1c54803100c108040c03003400180040000060101403003035002600d00000203007801103280d19440b009540b40400d070805d0011a10120700d07018145441850380ca84c03220744c01800c0c07101248550044000c1d4101030801c6410640e1441c40880c9a45d403806414401c10003030b9115 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790637625 1250 790636375 790636393
    0x210110f07060f0b010f0c0b0a090b100e060108100e130b1f1a030103020111070b071208070c1e0606080d0201200403020f1c06060806100609140108040804080f 70
    0x2801184e0000020506000d0401e42000c011030b00f00e00504a0f0306c3d084030006095543d502181005081d0b0180c000b0b2802c0340d02010040380d4402c544020301a60811054000d441d82d4090065030044029154030010a41203041041030800c0a0440e5500403040c00b640903443c00d103070351061154a8143c610700a50150213104090100d0200e01d914010300591080255009280c8034070b00d1644410302000e81045031a2040d820780b20700801505c00200f26881070161b4880a600300220100911008600001c0c500d40101d0009485006504811030f00410090480440260a80741402c0c0042d4125291901c86000041d41ca006001103220311605400124000d415513004c031110b41c4800d081080d04440620007440981c40b280030710b080048040d038080340c00b191001496427401040200080042e810900f0210305064042a6140150400c0c0c0224040c4d40e00c50380b0643e14201a0700810391407047c003800d210070b6503218070141600706015092003480d16407201300300390901515010011150b4444002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790638875 1250 790637625 790637651
    0x8030c1b1b010201230606041509050f010c150e1011030a0c090f0509060d020d0c1e1a0706090210031e050702060601030b0303041706010503060a05070210110f0706 72
    0xd40c40400740248020041008540010078000c1d0600340703c007000d82041c0380000e41a40310501110003500001800c0041300041040041003021140034483c0525030180703200391594043c0003818800d030b40c4041210304400d807156022008260088044901e4440c1c0e5552003000e00303540c4104000b0300621790129681e803410403441001e580b510444101007140244080101505001865041c1d5100b00c0e90680c65840300340020b00010700318030001e98085014038004003008144e40c07a041c2104e5048900900c01d4505405151120034207108082051f00025200c040c100c040034010040c40c0d22a5a00045004090300070170312025581c8102408240e40f031810400500e0004100c03c0c049109490038030640c608200002c0d1a1080078040d103040c1074507001e200d04217903824010350b0041c084090f1444a40140100c01c981e13590001e01c125402405a00c0125101d00300030701a4a205080d660010011519509401001011029072100c001702040c018003856559020040400b203019202c045000810101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790640125 1250 790638875 790638913
    0x60512070f05092a0706020316020c010806180606070b101403010b0a090f0e060901060303080a0b0f010c0303090b0a0209010f03050103020f1201023001080706020a08030c1b 76
    0x1061040f203610041141350b0901c400c1034040100160480074402210600303021040c02140b400a000d54004010824042c2207071280c618201c005608031070141d0301c01401035a59060645000b50400c40d20380480807102440030f807a9070405c01c0031349030914105036a19003684004040e24900300c6842280070410600b101d4117030122800c2400c8001f08030b0002d1403c006010003c85110310030407691906a40088540c40368040c00020f00000140c0e0000e19115101c00c0c0201002c0c0403c0b80419200408074480245030700c1149440302019051503a035461000054685410303038182142090340f5280e00f003000404a480d4507008070a4000e0168503420f0700e0001400c0a0041d0000a0030103203403200400250341c520383c0c00d043d0381d80c05803080a540c940800c141400391003401030300c28482c00c4824000d880e40381204041d00b00f407010100c4080e10b40c0d80f65002a52500350b5403003102c0c0181d0003596280080ac103100b00644d0808603901c07040b850480e01c843c8028807110a281342003460b4211b483c0309080454901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 790641375 1250 790640125 790640129
    0x30905100527010c060b030a021305091b13110d0c080f0f090d120b0405040807022707081519060f0f080c091c06090203210313020103060512070f 64
    0x1072030510340032034900700081c804d114040010b0300340c41c0c840c814000c2c2c0c1c0c2c030140254945190094140c0d120002c80c130f4940da0152006652000b41c85c80361250205401c0d458007030342d883c60a0014440303400038021450407000f81030311042c6412148810019010819100d00c56486c0e51a081e4403458070516000080c8200301800501546035030b0710031130070071011070004903c1c1d600101d401c0c14483e000d241c460401c000140307d401503140d0401e20704020301041c000c030740c0c000d801658401c0701d441b5400c00d14a0241000400c03e044280789540742c03040071418860007602c0341903102018181c0011600403200000f2408000d0480d40c4440d89154002440300541c881209490607a03242041001d5045181b402000300c5002003105c40c1030500403805007419030382d048000c002c50004000d0406c0c1072080741803400040000030012442403049107001000c2c9080000d402c02001a41c80c1010309650312221506144220210f0480c10169542408511076071901c0c01081401d400380001c00885082034a1031040381015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 790642625 1250 790641375 790641427
    0x30305070e010c0308040503090316080c010c0f081813020306030f06130b092113060c0f03030b0409060c020a0501050108010501030c0b0a11011a0315010e0109090309051005 76
    0x10031006501d69820003035101c00da66040c58060100c2c0d4031410320600703601591100542c10b0040044030220061f940134040305135041e6809a8480c040180300542d0071074035189000300031008107010007003c82c0c8a800542900290752304450780f640480b400098020003840d43d40e00f103c5a010051000c0c41c1801c110f40035142d03101200416480c2040c180100001d114008010072003028000016500300c0e040c44004002030280044e08449a0380e400700480701d030482e46601a001c00002800182c2a210b4100314208035080580c2005003008c0d502c00b100a0304071081015009911002800c0c002602e41c840c04c004460581d0207403182007080c2c5002801d40f07006034040401c5a04100051000c10300041c0c1c98001c49500d035281c9981e0700c07694030b001e81c1d0000700c102924607030707501c0d00000d0407104100d002d0800342e4081c11401d89231403524100946114610a00a00107804451b100500840c88190320500781140030307062107501300ba40d980016252070f40c9410b100000030004107640807440090b864081c04010700d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 790643875 1250 790642625 790642637
    0x1030603020f1c0203030c0a140304031509080c06100f0f0e0f041a15131b03020f120a090c05090705190c020d03021e03130312141603030507 62
    0x20315000100d602180030002d510440c1d00c07500d0304000050700c20600710003940c068190303525201013600468468103800015660074082580f2100028004400c840a0304e5025056052081c440070541e0001c2881c400e040700c03115810407240100c0c40d01000900d10400b0a5007a56079031a0615810850f100b00b030b82d004110320000c048041c03065400851845900c0005103968000d25a40e50500c1482e91075139100d4030a4100c5c141007442031a0401d00f50300b03880c0703d8003940e899010100c107242e55411240401c280f400d00000c008240409140310344c0040c03641e0101090f00070304003000004240002c007415616241c1c0540e03920648400c00c924412000c0c02003408441e030500c0c0c0c0c82c0c1f0742c40240151144071414106801c0215074613900d14003c00c1001d14054003d40070344500906d51801039660786403103041003480384240804107503000c07002007164407601e4801c01503000d442c0340d5038a5004942d07007040c4240510003031514140e072428690b0064102c2420300440208400726500f005000c0361005400b48040101c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 790645125 1250 790643875 790643879
    0xb19030b06071106280905090f070e19090c02011d0c13180f0b0402090603010605010f1107090504050a060b1801030809030106032312030717100f03150b010306 70
    0xa54981003045000744d0300039581d649030b062000b10059001481e00c03080c1095a020f00707074440d48200c2c46000e981094648008540740d40b1004010318108a5000000600c20400081030b810814050400140b42010f003040e81a102d00c2400c2c1502e60800407800147c0d9100a5285560044420401076a0704070024103014010900896603180d18030180310304083c2c0b0f0f0504080900040110a484a5003002c4c58000586181c940120510400e403403c1c1d124105620100b1554a01071041404640c0144c4401c841d506041800361100011817070203c19034020190f002071008014018103200d903200b100544002c43d074038900740c3d003151843e151a500401f802ea6207001c80007641900241925041030410b134580c044000005c0c0941341e2500001d0a030652604c002d1040d903170880300303222201d80d4101991030061079240042000c0c00120b60300350000e10180e469501c40c0d010300300d0254116550500150300103403a4111720241c0007259108681101e440c0c5100d80d0001000d1142400705002481c00744810b43c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 790646375 1250 790645125 790645133
    0x90a0c180e06010503091f022205061b1c0c1a0903030402040b04020c010920010201020306030c060a020f07030c231305130606030f03020705181f0b19030b0607 70
    0x40c0149124144100000499006d42d0104400310407540b400c580403070b03400040b001c4100a50041541181059801c8a010014402c0c929010003903c20162109042110b0a05040292080b000c80003646010740c00110b01e052100c515200080c0503251281c0718a41400e1501d041c6140050440340083c03403c020a2011b404004402c0b0b03500301e90111408180000a44c001600a21501c846045190b20b006103400400045043e600c1585a03005402d034201c00c2c5c7d403801a42030344030440e24a41d15800410810003549001130140010000910481c3c0c00c0034a10040c172858202245c100b076812407032a510800811403054801098918a800c00317005013641c010115880b1000c5d03083c040e246a48400025000c0d941120501c05110303003015080c00b0040d070f6404c0201c0200400d01d0240c0c01400b41a00104a90070814042240140c400c0b0900080d541e6084298019480c20851f40300941c510910008441941d0005080f00480030040d094010b280218094200c9020248441c0584424403402000c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 790647482 1107 790646375 790646399
    0x2106111215030304030803010902031b280c0206030f0a0f1a0405010509010b031501020a063e0403081b01140405060708130201031802090a0c18 63
    0x460000500b415128891800040d01007001007004000c640426030055502c20700f0442042e40c1c03030b210786228000c40e0380b091014070f0511130000c40c50220704510010300c443c150501d050190f1900c1daa075011628900000307040e0351840f00480d00040e40f0710150381240148000601c000c22190f02c0c0704507500106604d0900c9070780110b10f800000b0410341801c1c16918181c0d110701341424115900d90340700c4940304080c4e8607070604502842d20305070001400e030301030f0140700813105449503c0303041c0c40d004083c1580269201c0000000c0c0352006441d0070041c410445080d80d0300701b0012503407141a411507061460b200081d01c1e0843d0310300540c01e840c850020b00228040c034402d0099441545901e00700701e448901c00d84104545809093340d200040d8040c4d030203460100201e5000e000d5003125500000d5400100b201c0f140030254035900d000402603400b440d85800084000160148141003042c5640c0d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 790467625 790647482 := by
  have h0 := BRFrame.cov_init 790467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 790467625 ≤ n) (h2 : n < 790647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
