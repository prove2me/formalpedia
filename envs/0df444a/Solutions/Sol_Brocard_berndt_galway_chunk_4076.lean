-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:07.676643+00:00
-- url     : https://prove2.me/submissions/4e68abc6-92c1-4e42-9b99-f520e63d26ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732913669 ≤ n < 733093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732914919 1250 732913669 732913679
    0x8041704060315150c0209100320010206100608011412010911090a18062d050a060603021804050613020304061d0a260408010204030b060a0f1a0703030204050d030207 73
    0x8074401004104c00c140c0c0341c14004074604054030300115000d0080c41840854006401c20841880e10380146801100c1441c7c100b40300300d20102c00d0607102c54a43d016105800001e90040000c10240040d60069075a84a9903440d1031020745d40000c004654a03440203906885104030340d800d11410580a0240d040a00c0c500c031040d040c005032100c041c02d00160241402400c2080000ca815810410313a8000c0d8001030951f0030460000da0381613039903000e18103000081c0010703801511036008140a0446410100401e65440109400324804c1005400c12200e1000c0740a45c1494550310050307000202800d152418200b0307100c2c41080342e004540c1191010b60364070360300c5d14440f018505148903c3c60440281010019901c4090303100000c00031901c001222010748240ca2402a0291030040c00000029504e9503140d103807410b080002100c002c0c1c0900b03200400000d40491010070f410449200b8810601d0103404010740e0089940301c600d064007456000c100c0000c43c0e841d0422600c0c0d02a01a03406084028100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732916169 1250 732914919 732914951
    0x80d0507030608030304080a0e1215040b102106020f04030f0b10061d0319050703020301050f07140c070b0403060e0105071107060804051c021606020319080417040603 73
    0x50f81002609900500800001480c0c4c1c104680042c81d40d4140b50120601c1d0000140d69500306c840741c1c91040c020032000003c0410b040340054001d500c5024503020380e42c0c0c0c01c03034602c90044a600ca00c02400e890403000780f080140c09400d4980c828021000946400a20410071210358801d0b40300b2a61040c0c0750f040d91084c801030b55885c0f6001104c24901113441460300308005e10903443e0380c041c2000c008401c1d9008200d0717502088000603d09080a8109181e04c4034103005880b1160f51000341c0c042d5082000180c41390100340d40c464450b65080e00c0d001840c1c18039071b440700b1007078009001c03040f024440c000011409000d090007030001103101d0b0340e01103125803c2081e0142502c5010781484184582440088000707040424901c003503c0c03043c5050845550340c0e041c49807a204020170380c0841504140c410301c0d000781c0e0109020710f0668040d14881c030150f6480500303e03541d2007440380840d040403000d03681640642c451510960084d0103640c860f20540c0500746240c810f90f02c107a02c21008241c1d07c01c41c0301203590072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732917419 1250 732916169 732916181
    0x9012610030b100609090e01091b23150a020703050a0b090f010c1e030b06070c0f08031c180605010b0a090b160f03110303010306060513022a0307080d050703 69
    0x10741c1d000f1545145000e0018003c900c8078050403012946032410504615800d501041c05030303422032600100c0080710050004001140d00800c4416526140760b000121160682c004030440081d100d1074202c0301000c48102a60803014620086005407500000031480800052a007030340100f071070680720704110054030700d0f16030300e500c648006d030341094103550010760030420702c0120b0a00341044607610190110105d0003010354507480ca50110022030003070140300c1403001c28070036110b9903045819910b84404003250780740130703084001000e011030410300304500c0440e03004524889d4104942130790160781903072400d090365000d03004034980e00408a075900c00503901c000b0010041003002051460101a00c1e28400060503040340508581400c0b80c5100c1018480c82c2c5403005a441c0400742c0b070312561a4640f94000e040541f080340e114440c101c400da801c0000b24401c46440304151320303e010305600400006041c4d08100226031900b800140014000309100c40014883d95810b0240014903151104000c4c0403182 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732918669 1250 732917419 732917431
    0x80a030506011b0b0a020c0106140405090304210305091810050109080a1205190512060916030b060d061e080a0305030114191202010e1509012610030b 66
    0x151000d11140307900003d0108036030040c01c1c00c0410340d205070807080a4410a00380014540c41c2110004504140b80019226030504039028441a00c032003105a56074080e0b40109886844200c0c5c00f40d81d020b003490140705140c2d01c070342403841c200380320100042d00d0001d12403020004802040104805141c0140910700039101c00d0034410402401d0820031560741138001c1c00140b021140c441d4505441c0c2c09482554501c8a500c900c82030300019018000300309410031201d26420111400214a280c5413000107584150f04021040094008261048016001c540c1580d50804010016000411380314010080a8121882c0e401804280429000c00348009580305551a40050f200300d0700080d0312408a0341110131030003185601c1c40e61000001d80d02290b1603084048049003070703800101188008a0101014000d803030300d90b42c2c000d03000c040c0000051012600c0c1804001009014030075802030307100b08040000d606100710000c21aa400021606c419a401c1e078490b01140001c100300001034151a034415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732919919 1250 732918669 732918677
    0x402100311090d020307030804080f06070c2d02040e0a02030c0301020c0a140c090403111b13090602130305010e2a011b050106090209030d020708150907080a080a03050601 75
    0x1860105840308502403540c0075441003043e010042d0655500700701600c081c0d42c00c0880c00d80ea07260f88000d4a680d405103e5008540381c0688400541107a000701181d12000d030f001410360a01c00b00c0706924185440024111207400002e1418601c05a1a1480388404950203080104610b245600401d0310740206000607074482c0c3e0040001450f5984d000c0f0b542e105003540840c504034031001580b691400d11180250454201402c04d00b0442030560008080d420300300d4020507584483c03058907604074403011503949550441c680400c0814140d003160b128060541c01080014101103418800100c50030140d403080e61240c2d11010b0220910005200001102c461308548014140c02817480021041a5410850510020180c0c0d4040d620801d4000002254032100030130081d030300d5090b098002d4000c007503203030300a1140804042c84079000140c8182a20507100041525503c01140c40c483d60a0007401103499004004000810303903000c10140c14440d1040080c5619112000e1000b411244000c00300f82c104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732921169 1250 732919919 732919931
    0x190614010e030a020f04050c0c011107020414160e0f030a0b06090708011a031513090c0803070c090c0509030f060a110f09090a0b0d03081b0c25180504021003 69
    0x1a0390380c01d2550f40c081001d031404641560b0302e42303500c8454081c0c41100c600c80e50030001e041d007020702c22500505106200300c1c0e040000040348540d00400100886800e10110b00340c52401d03996600032007260400c000010306a800940624002c42d0400841950403258042c101301409054641140d41c1039010304240f03859000c2e907142000c1030703440c41c180d00d5a0003404040040400d1240328421003810b44440040c01110001c01c10306615001444100e5090320b52414101d4041850721022085860068010307495540a90a01c10030000402040110b14140a02080071b4020340d103050012081d501d24880c0a00581d182c50038941d01681d445001070008040104040305101c5402800d650700360000340c0e0b44056580d500d80c0144010111308a00d1a841001052210201540f0898461007600403144041310140d8200d400303001400f400009480580201e8101035229028925500e030800d51040e00d0910140d83d01e121903078031a0304000d146c25040e100c1040101358101400e21000c1c0001130700d810012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732922419 1250 732921169 732921173
    0xc0e0f060d0201123206100c14010b040e100515010f08090c090403050a0801050a0e010303081005030f03041403010515010f02100501060503041a0601020d12020d020d14090115030209190614010e030a 87
    0x23408171440c0d000f4656441c0500301039010364258449055010301510800406840c4180b00d680c070f41030a51031001a41c1048001040407070210010a4030041c181c59045070352803105010b4941e1280108034488a1040021550b25aa00d503000c60740034500984039a581d9000c040801400c10005130030050041d01041420400c0b038044006860440390145030038529500c8186080541900552100c4c0e40741c8504d1403a40d06955003c80240304480b807401c10807140d120100241400d0780c00840c3e003450300041b04800f441265001c2e50310303c840b0403032500c1900e00316181280d9650172148203810140000d08044100402c0000c9400301400001c612503041c0043e1500e000001c1d40c4c0c0e030070b645400c0c003008403207000b40303440d074080360155421482e03002d10641d2034095004100c0300030b01003003095191511007400824440b00062080e400d4840a01103a41e00303ca0840e000d0201881014ac520210323540c0e6a900c4100c101050300c6000080c00b0080081c9901c00c0000000500d4120181a018802d400260306000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732923669 1250 732922419 732922427
    0x20f040609122301090c0305070519150e0d0b090a1a10060f03060e0a140c1204080901200a0212120d090302010b0d0c0e0f060d020112320610 62
    0xc8090f8241100303010322034500e902405441200c6005205680300400801003150214005050700c10903298501c0f00320302c1c107500c01d00c404414441c0c0b030220b91407000c81c5501030384540782e40f2041803405811100c500840d503a86501c072550490307041502ea0003c62102c000c01000d0006040c2100c032055619070342d4141406007a044003500d01c104d2013800112aa0021028080c0c1c00035001412040c2d02c101861804c0c001b801e010308020340c00b201c02c60020000003076030185050183c0300d440d0303903400c9400569139490f0707140031050b441001120705001d902c503480c0b00700c40100440c130047c8a8281020300103150316441030104030641c1040d01a0103030450006031122071400c406492a50680030300100c3c55a6060a0a9006062000c04280c22004a4910b942440340c0804a14102c800c3d0f030b00c030140c0703541d1104511412040242d400a5001081d6140b1001640c46400d60132001e1303421030400644001020382d149400900c0c110084014481c0300e901310a000c42980400b948554156000000d0310a1000010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732924919 1250 732923669 732923693
    0x2104020a1203080f1801060b1b0d090b0706090b0702030c0c060301050f0904020414091f140112110a060309022d0d080c01020a0507120e011e050706020f04060912 71
    0x4084c0f24080e100144901c10010b01c1c200038144075000070004651123040102d40d50b4031500002e2000c20180e40e000606040000d807651803426180d882424440c10100c0e8800d0590010744107030341d040d4445a844001c103c20241150190409800075556030041e07186241c2080940450f40784115400d00041201e619017240c034803d03c03002151201070030350701c40c8000b0300201600e0b480800a49402030800880c8000040c03a02c4881070122892019040301c5000c0e18195000024401c01100b110b0300100282c00a03c40c2c4503041034030802150700683d1350341012075040303c42e990040001944840030081507061a0131108100f407120078414111000e0440d214030341190106a030f03400ba6070154051810f010045055940f0030380e159009541d200300c040d00c02042f541120320140c0710038484440d00c42000b40110b800c1404a031068607911145114454451020f0140491135800d22004200030f80005406100415000b01003c48042d2640d041680c01445582642c03c0f81590440d2100100c02180401d0466 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732926169 1250 732924919 732924931
    0xc38090d1e05070303090b0f0405071505040e070e0d0305180603040b2805010e0a060902090f010e0d0c09090606061103030604020310080a050d02330c2104020a120308 73
    0x1c2d41d9101c40c01c0c07030128010f115245000e84803075940c4003406165a842c41901c0e0113235005400700c400369504c03401d94043c08040b88e40c82c5404180c0400081181c8070f1a0402107a20880c0c9081c543c1403051688040f80c04035800030800c4002542c0024080d610155422400e0f18003401910014110329190b07544489000000e42040104400d0201030103500c200c0060302000c040380ea0206101950b500c1c0408011100700351822003c13142020000308020209100762041414000d0039110741c00c400000648048003510352180c1c00183c1004420302080360012210000d01d0002c0b000185820300c0d0804108070b513031f1a001030082200350480650380000c0003090700d41010046400690782d495a00b03000004400540c400581d500909a20400b440700128a1041c040c0c2240c080d500741d84800d140c1c0d0300d140d6040c10164400300450010070780ea00a40000c00036840502100302d43d2a0049804100d40000c0708110300410108101082004504140d0380c518001d200100000f800b03808256000782c5680130080807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732927419 1250 732926169 732926177
    0x30c090902030c210114060a020a020918030c030415090b07080904091403030406060f0506041e0b031008120304020a0b0d1d15060a060c38090d1e 64
    0x4a0070f034200c80c01c200c8a213030000702d00d030a034003049250400d0f588940c00d00c22010741604810104515040c05411940104803503809405c400b01544e0030042e0825000e005900030f8001508556040b110800092100d40500740045489515010100c60109030480108c1c0811622810402152500308151000c40354041000d0762038006900214002305040d0b44040c0c01003840708040410303200040015802035010310703020300185440c6d00700003020b56600e1042c250850000c001c00c01ca40c48006400c0380d00e181c20941000c240310341e10200c0c00f070107810540302c118812040000812503d181040041d04d1840c0d10030031030b0700f94505900010004c1040d480f0b0200003d60000302c41c0d155810f41e40c455001c210645160244820035165540e5689207110544001710800303802184031440c060901108540c81556011040c21541e40d0f02c40d070340d4444c01c030380e0101c031004c40c110b04040504480400d8040c03540d40840080604e0003102c528908200400004103110200d003980c0105402c07901501c01c03100017410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732928669 1250 732927419 732927421
    0xf1206010509040602190e1207150e0103090f052b120903030e0a060b0a0501080c0315150a020105190b031203070c080f030f010812040509040f05010c031506030c09090203 75
    0x140100a4814100d6115034900201d90314007015030002c480c0c01c00303c1d1f0180c40d5503100701d5240c000c065a8051a01520f003140403d00c82d0710b400c0c64411900c3d00c04c5c0321810b24010442d007140b503540610702c0400603001c0f1007941120a0303a0401e2000b0b0340203003211080d4000604c07c3d0f40710b101005840660400c11140c400380c0c0b140811802c0c140a03030041d03001d069200c01114103044250401000038080072110034403884402c0b9000609612841c4a180240304890106140d52a41c20b00302d511102d040c006160020849507401019140c09070240410801c25000400c1c90b00d08005c900e8481954204002407051404200d4985500d00040f51101c080c01024000c0c2d507602c4680041c0c1d40c03d40c0781c810051403120001111039030307502420061401034a0010449641c0d9803507400c00d58680501041d541000c3e2400c0c4020800c3d40b13000380c10142c1241c01112521440c5016803902400d44107078603228000b2a448207440303095800c2e0300117604020242c5103810000f014220700300034014281441100860350b0048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732929919 1250 732928669 732928673
    0xf030e10170c28260105040b03160b0c0d1b0f11040e07030c0e190903030f020d05070e032a04020c0a2a030f0807050a050106080a020f120601050904 65
    0x40440d04014559039000b060b1819071030360140110000b6014100084d0b00c6402c1000342c507104040c1d4101d100c004402609942c0c280303020312006000706174036203078544141d50b228000f01c400e41411801900c90104095034904001c580c1a1800c0c4a0103520410800303110548030780d8505d91910080e116070300001110141d15076040a51450303015104855115160440c0074420302000505841146d11a000703c050050f1366401c1c0f1801d0301e00c205e90042806009041c1c600c426442640100e021078440e0a000070400504180c060488c0c00003800e401c1e0041e56142404440c5070801c0d0705210321300086000740140c01c141ea2480e80c1588502c2d440a20655028094894075030f1a601501c1111a046003101c0e0202c40a00b040b001000c1e551100d00040e505900741d400c0d0301020400c1d807030180e0390006102000c081c0b050b6540e1340315510402060f0780600541a0310400a582800b44c500284920b0006104503849401081641940d140486114170280348440b41100300c08114203045801c1155440ea1903505c0b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732931169 1250 732929919 732929941
    0xe030d0516023007080303010803030c0c07081911120d0c05070803070503040e07180b090d2102072102040c020a140d030612020f04180f0f030e1017 65
    0x2001c2c0c24092031580c4146601942c10100c0c080f00e840152200711071086584002040d12440280144c0c200b81c3c00c2000011141450f80004000400b0a5002c8903085651a00c0c11401c180320401000136040ca840a01c500748110741001e80c2000104071041020070180907501079403042406016001d11411010f5174060100c10300041c002410040241c07641c0b4101d07464143d45950290150707000c11161500171945a1380708043c046106040c03042500882d40c141005019950400ba8813582d0000021104000055030303030b0007941e1045410110158407407802a0b0280c1012400d4200c1a04030b418004600c01c20104c1c0101416415010780b03000541031f010050481c14414402e8018180c01540e404c900b01a00002614001840e82c65800f0880c0c1c42c1c407441305229203815082d01950003101c1d42c0400ca054a85940210702548000030191280c2502d40d542c00900d141100c070039031f9200d0703003040d416060540145000d00c40c0a003c0320b0b240300d19114240094036100309500c0b0030211180c81c00c0050701c0400700b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732932419 1250 732931169 732931189
    0x180411070b1617040b04030305040611070606030c0603150b0306010302040b0a020309011d100315150503040506070921061118030d090f0e09010615020a030e030d051602 74
    0x401030004441c9845071502e95498050a240c00004002001c03108070303065458505801107030b2001d0b61200700e8841e82c4048000d02000f620550350391342c1c0c48400b02207003035016009080c030320321947d80030a0071440c5040a851083c0283d00a41c10f05003091000b0104158100c8018181d64450200710b44946910004800900070780c2c0041000c0b21001500c02c0000d600000504100c00c000d0303031b516441c02c160348645002041030fa42e00c01d0300006048080c0e51454000c6c1c018000ca807141c1c0f980c002240e65103400081000d86581d5001d8042003001042c0302c00e000f028032a1310350000700b90500411507413502d60003107403140320141034000c0404c030a01c419007040140d07080100c95480303409003151140c060341140c0f5a44034180303284910030b1040c0041541003500030080d40040f9280c203240078200d01c0c58000d0b03d4526080040c2175400d2556035200104400d0304c510f9502c010b645080e80200740403222440c3c05061124400040c0c2c5c80780d0b01400021050a038803404540c04401d80c100d00b140c0300c44a41c4081840c200f0f0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732933669 1250 732932419 732932423
    0x7020415050d0f05010c170a0515091018020f0f0705010908031005040b040b0112090c08010c020c030607020718020f070204060b030717010509270714100518041107 72
    0x2e10106224144002880c040d0500b07070240e030007040060101301050b203030348921045188081904034000f0349030140e25845164003c170101400c2118000c2900002d00500341180d641c552405030700c80a0200c410341800c0c092401044420462920040500354074190080da1443e41c20713100d001444c001040000c1d080920030580c0b043e9115140e04001000848881150151601880c40e0031715070501440c0501440301e01c0c1ea0181c5131842000c104d001c01c04c0242600c0300c41915049044040002d100500340300e540c8501140b6405072031510402c400701810408040c0041c001c540c40404103102c601709400d0309412195400384010307036414a001c00494180204640a9031144c80c00f82d0005040214200440c420350aa03a03030014068032210200058140a010702d40e00300a1241c001051000311700d44030b00300c00c030b0104207102c41217230310014452074550a9044404a44580034030754125050445210707148580070305210381440448417003050b0590304c148e441c510854a0312500802d890b00c4000311061a5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732934919 1250 732933669 732933679
    0x909070b03131505070905040528020c1525030603060e0601030c1a181903050c100306150309080f0a030914010203010303020703060e10180201140c030702041505 71
    0x1141400210844400102e0140c51007140d4506000300d08405108403403184255441d0118024103000c1030000030310740107059402120190008102040f420241a001d0388400600581e8401829400c181840f803440840c03903204c5d0484003480f25641c0c10f5025001110000030006d4007000c0c10020440151038168400b8041500d400078512540c103000c038069040e40e010300b0060342c0c025941c14040d401264440c81e2111a000184000400c0340e48140c030750300780000d001781312480e6185955103501350042c43e98001c41d030544c4405055600c609241c03110402c042c049050400c4001d141c80000c0800c60340c000e103143c1c105030b0b49281010030030440c94141c3d004400055140b40e1608541c0001500500703082c4015102000c5400000513001414000c4a05036949580074156141c0395079110300241004901403e61801000f0a540504042c2d20680182d10402d428156904819000160881114811075951844200007001000e403000048132182541540d0010b8500020780f00d0915081050f00465480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732936169 1250 732934919 732934921
    0x106121503082a06091002070c0e130614040f2907120f0c170703020c06040803010302091303090605090d060e0a12030b0108040201050903010902030a05031902060c090909070b03 78
    0x16070100f4a0841c83c040451030180e81c4103400e120055911103003201c28141030ba001000441140d86180c006d0140d162060350b809030351580f5842134008a140898000c01060072601c450030610106018501608100c5000071500b82050b45030745040003042c000c06400b40c0e20558030304100d21002c6c1c04140c0c108240f001c1c070403807500384400300421800400c0d0070001000c0c1484c80003003d038a0f403441004c18000d5075450742010803d4024040340c030304900810440c140342d0309211440e8480010310146100d81c1c803aa80107036596045204000d4941c802a0940c0c0b50041c40b0100034000079002445502039501505100d5294106100054a9880403030001001c141c2040800040610005605150184a0051000e0100b0300d540101c04488403a100540000c1507400402c000d540124000d10300c8100240010601043c5900840e01e05115084100c8007507000181d05190003c030707070040014201c0355102070310a50400445c00c080364002d140803144180e0040001c40d000c00400c03c00071009021b090121038032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732937419 1250 732936169 732936187
    0x20f030607030b010f050c030a0f0c0507091b03021e25120825050a0c020316050f040b06090f120703080a09171e030c071202040605030303010612150308 67
    0x1901c00f10740c006021604402c142c0209a0040d4251140c24035000c00039030801040302001c0f940071303110940740307420300008400200220b403081c4819009042c54800c0807413898030300c21500a0508240d01031104043c03050201c14030b40000c802c0c200f181e250006684c151224a18040c0720f60340050390030762110b412200c00381c107001c11035a044410070006040c2c0710320400360b803001c0e040340d1800c03904d114500340d5004481c005c04200303006a01805612040386020136280b0120790202e8900058900e45111446000c40d0400c400e20342449000c100f42c8090303c0c280a003854503004034181c1c1c012811928411f106840c01c1000030b0300c90301083c40300401e00754101c4128958034104400d55902010407880012070004020480000070000c0000c4000f1030b6000b0010070b412102440209070030308465455500041003628826401042803802602074000f200340c140c6a2441000200c6032158060350290b0400c1c001007008d45c0c2c0244440d10b6004100e0404a41201d092890640c45412900000c180407400b00e42070319 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732938669 1250 732937419 732937421
    0x6030c050a061209052521050d18090509060603070503011104180213030c090c02070e01050105160b0c1803120f0c0304030c0b0306040b0a1a0703090504061d07050a0804020409020f03060703 83
    0x2c0381c01c9907161840e06c00000313207c0394500c01b03420b4003d04070f03a00206c0e100081c603100710004020316140d4510101215298500c0e5402c0d52400d4460184641c4004203101241c903090003008006c0804070002c000c8400c055a490f0b84a00640c4501d080410f552070700006480110b0301140e40085c1404414200e550305c034503044e6107204d9680038003034030a80b40080c06100c86000046003400c0c0d41c91103002d1103131030786070000450302035104241c4244030444c80d101e4070f80003811400b001401a210b031244140c90340a00245a00b081f0a0400000d101c0d92007006107017107200d11002183c20490340c9040c8a5959035400b000c4034510312480c1c2c40100b420301c0c001d10000e2480c080790003950080300c0c2201d0074031003031600c0010004810402d02804d9103040840c07148405c032111040082c420715200b41441341080d80e4610000d0115800395000b011600c0b03000c09012168034085440c664808402d04085040402c0001e0003881610000c00c020701a5540b52032810035561801c51021203000c0c01000c6803000c0c906154018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732939919 1250 732938669 732938743
    0xa020a02150703180b030c03041b03060515030601150f050c0f070302120f07170c1e041b021c05070f060e280602072406030c050a06120905 61
    0xf80005a05000080605500c00c210804131501a03104a0031500d0754001600c15034406001103d1001c4840341d10202c08628062041c010740c05101c0c00500303440c2c420380c0f0031020342c0d666615130701c690002c10050001a1050010307610f812154500203010302c0403101c041e6200d200704c0900018520405101789031000700099000207a900c00c2d62507031484001c1403100b50f943d4502410580954000d510107020086180c0e502400000104c02100c0380748034540e02164480005100b40c2c0d0101000d40803584407810301e070141e03522444140e590b000400c5485003009440303008580e03003519400303201007042080c1c5101e4000e13079820a41240030700f901c68240c2d1034100002d0101848080c114043d40e5508100200c0c00010400382d819070400200c1229129a5200020b600201040301c0d10320660344e0708021602003010102d94064441d82c00900c09081d401c0190a401a55228902c02d00040030306100e8030341d1145e10700c4624503044c88003203100c041c940b9041e410b107001d4004240051401c85249500c03028504002c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732941169 1250 732939919 732939923
    0x120207080f060108070603020a02030315010918050414030301120b13060615020c060301210c081f05010e040f030807110115030309050418021003061203090503061003170a020a021507 80
    0x3c031171140ea1840706405a01803220780380050f800510005524507000552503000c064149041e045481d2152401e50720490b492030040400c90352241040704108409001c10044424107004605541c50315480c0c43ca000302a28000b80201e0754500410174004101150011183c2d00100074095a42c440108003030740e07990074240800610401032040c0c1c1c3c6080041c1200c0c1682c5040e81c0c400342c001d566107502c4851607000d00048401403d80040040e0000701444001284143da2074a44401c230703d103010010070f0f02c2c01078011100594800d02841b00080d80b0515402819915050090250380c5158059402c0e0200c9100e50741c065003071a406081c1041e9240d10003069a100f500d07480403168030b6800380011160941d41e8141c00c0c16010840c4405403a0500189102020710314003c40c02a0b00c0b541c40306500148520205d010a00c0060180181c2c501403044992003030200e030588100701e145480c1c943d04824000411480d4400006005060600c244910005541c0141a07004e0458043c0c250250a900c40801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732942419 1250 732941169 732941173
    0x1208030429011d060405041716020d050105010e0c090306011401020c0a030305032a1602061c05011a070308161407050d020c01050c0307150f18031101021303120207080f060108 77
    0x106189071906c10707a809103030002c0f988801010060080d980c180e0102401417002107402541400607a681414a003134244140300104055240c82c00d901e1803106d0203030604808400910a58403540c0b40002c4042c1141d410400050410001c00d00507810a280e000042d908030000010101c03d050b08140214040d02140c42c00a01c008561032901520100c0744200b52003078003040041c13081c034400c101a0210b1290000700920310300500081c502d07121014402e01d801c07100303451304010400030a0070804c0b4040c40d5054407010f1b1810402d83d400030440300c40100300c510500e81540040d80300611a0240724801c2c41d655601c265100c0032414400d80e2680c0240d900c2005105180c1c1e42c07841544150292146928090000d40c1030001c1551011041015003001846155031610b21206600085c007500c0c40c100301032080500404007a080090140340c0165640c030303041c1e00401072298242c0000352140c1c100c6c0d030020300e00c820380361441c2e80484c20503105a00c514030074484d6025a00c0c801c01c0100e5094126802441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732943669 1250 732942419 732942421
    0x50a14040f0215120c0c2401090621021203090604030b04060f06030f080a0512010b0c010e1b04022118010b030c0604090507020a1b0602071208030429011d 68
    0x150703901c6901c220241e01014280100101c0e12010170b10001c0c00b01412408107490154002640310b110724404500300382e0060300010010010501c580c03140c1006000d0040410360000540c11854014862201e0003e01942404c146110014020b100f507a02c00c400082000e96202d0745c0e4100151010b5080e1001e23035119103804510740d4514158812001101da00c04900f00885034a9145c1324060b0b00320320012028000b080114924005590034094064400c0750700e43d82d01c807011a0708044c03c484102c41000003941c080100d10300005a1210300d124418000c0b82d0140c0d0315980c1034985541d80024001418ac050001e4090014024001204030300d40c030301e16002000000001000c00d56203056814145030071150400090144051a4008030b0740840c560040310b000141c26540c3c080d0440340034002600801e5500c400344181a810b00c16030f002405040c440f220a14401d48401c5d00610001d8001030105007188507142070000c2100703880d2880142010f841000d5070351014140c928201850640101031580d0b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732944919 1250 732943669 732943699
    0x5071a06130e0a0c0902030105090711071505040e0a1e09080c030d0b031203010b0703030f0b0907020106140301020f0a050a02190b0a05060603091507020c0a0b0a0207080d0c0303050a14040f02 84
    0x100c21f4904840001304100060b4440341003d42e0b0010018180001e01d00820101103101044200a90000d01095407041d698a00c0c000c00c805680e40094412840740d0300744200c00e81010507070101c13030300c64000401d00082c22200038580038000340300f50b50b488040d41c08041818500c554080d070007502115010340581d5500045881444024802405403607a404c40520203540030078030070303031141c0a01c0c4420748000551941301030000d030100c20110f0303c000060791101402d10103000e140141030480ca600341c0095080c0a410000a070081c09500c548400b00300010454000141c820054442c20040c0319000012070f406070304150328108070854610903018140f801040c5a401e000d8100ea01c02c00c07946024040c0c04d01040d0001501003005021442103201d01d1400c0c944540d10709006000600841100d151782e50202100130341800c0041d40880a280c100d2040c0152045c1c205180c01a1580d2500c1c000405030b598408035030090100d00383d0781c15403040b841d0410080192465039100300d10300032501007003544801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732946169 1250 732944919 732944921
    0x105060a050d12080406111602040b0109050303040e071b0c09061203082404110705060f1308030a18030216170717010b041b09050105071a06130e0a0c09 67
    0x100000400020b803d00703411561034841c072100303604207200d9072020074001100350040080e0303000801401040c3c1c00d030112100c114905071165200d144002c3c00c000b0641464100080d1700c90146100300050103113440005001d00d8840c00f181559520820100c00281e03800c0d0034038246120050043d4920180381c81400720f10450050400200e0a9040e80ca50300a552400c401907445c08041050140d211425860750075280e480f40140c8620710303140d100003901c07240141061481d000004d0100300002141d141801424140000742c00c0101e50840b241d203a41e030300c0b00c140c00310040146000e0200004000b540f090105940800e410aa28219180e00071113640c440320060a00f1020640340f2589601c80a0100003507000d08088094a900881c00082c9483c101d0b030201e400d984501c0d040c41032000c41d0301400d919164106403128098130081ca811414040c103680c881c0c080e0402007001c0c5900c40030310b000180150b900c40c12000303c414803011301802182c11251a05550f01001709084804900070000400c4400c00307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732947419 1250 732946169 732946189
    0x21e030a060b18040c030e0102160b06090402010f080421080a24060e0409020a030c0f060215070806031e0309010f180e06150a0f030b03030909010b0a02030d0e0105060a05 75
    0x20f600780c1c9810344a2a0001c22000300100d4000354141600c507560700348008001e1014008485229a6592050940749049203a1002c001e1183c2d01ca0b003100014807000d030340d06c880083c01002050803c0c40d400e0300c45d030034003030101d1300d1545028400c0b54907040c42d5101d182c2d001403458040c0b000118180702d40400500d548040005020300812100058001040750510940c1a608170030005080003c035008550007080702400c81d90010b4500408907007080100003041540e48004090303500c0500821034480d1100d18445801a05600c108040305002c0f0f0004e640511110110150003c0c9503002d9040381c0e0766040c1c40340c0200180301e0110f102c240ca01d00381680280c0210722408030068034117440b18201801082c1e419030140c0700c2c2d60481a03002886420301007020050a80118940702d9a8004810610003016941403041590080d04140a40c1801d42c80b0060702905648440c0d1005440b5442004102e02d14020321140821070340c100360307101c0c03904030f4103510040c0182c04c241d82c540800741c0c42e007081c0719070401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732948669 1250 732947419 732947437
    0x5030a09060215070518190f0506030f010527070215010b09062502060d0501030204060515071101140d06031112060f060619020d03060e09070e0a021e030a060b 70
    0x80e540019480b107101703400415103c0391000f0002203070340d415400300d404128080e112003040381e4150000e2004110f0380d078801004160484045146107400d120711014024180700703283c002d40e4a8101102c001c241c142c2e6041e2402074008c030b100034515202c00002d545400c016044161402100e0000c1940f00d00300c0c0840e02c039207602420a525044240b50546041c081d8020b6038600c0d00700c4100080010396442c070043c400442880d20100312941580100012200d01c0e500c02846402a9064420704040000c01e80f030209070040084d0786108044001a14683c00c500c40060405400095082400920394408410341e8010745d55071088200c0322080c050b1003164a0964140c50748800e00041c0841d075140c00c81948400007400761810304203a60700704450b45e100c450319400560415101c2c001500c0d450300c1044020704001d0300407022810000b0403a6150200b80c094100700c0401035000a0700101540c04546580b501ca1010034000c1410401c504c000c0d070030658004072110b04060300050300381904004d83d60104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732949919 1250 732948669 732948703
    0x3021806091b0f2503020a031b030f2f0a0c0e07020622020d080d1a06030112021503010e040201180602062e0e1801020304260c030705030a090602 64
    0x440340f00b2500c0c01d802400040380600c0544904042e50803036a02201c1900d4840e40060000004602e03001d800c200044d0290180c054004062502103a4041403010600026003010f0003440c6030368030380c2e5651210341c0300c00500c840c1e443c0310034512100000840c42030850041d02007004054444140e000e681c1415944200180e10031000b190a10184c032070a20001c150820780c2c0180c9507a10fa010641d0080d882c1d5065449000200344c020a04450740a00142ca10101c0c00d40b4141084070340004056000600130031070a01c6031100700c6001c548581d02003401c0c444401250399125a56291803c2840d00c0c103d5003240003401d4498801c9190660313058420a03240b01c1d8025220a0355070307010300112504a85030301c05604040b280510810512a0100f0001e4100203010301e8407850701c04d2903000c0d025a401221401e580c07040007000b0208031903501041000002c812400031011282c02d401c607080c000d501a152103404009407c40403c4400402440d02c0d8100e0303110100069a0391800340e0302d80044400280c411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732951169 1250 732949919 732949927
    0x180a03050709380a030f0803011d1018022b06171002030a090605090606010216030305180613080c010e1519021606050903060f010f170703021806091b 66
    0x10340d1524901404580301810a48011743d0b20745902d050b06003083d10a5030345840020050107c03603182440740103c800f40c0032483e003031400e20000c242c100801c075104202008001c103012007044107040e01201d640d41765110079011249802c0861240a00da4005124031261800c04001007511503074489040d683c0350380c2e01030a00c1c1202030b201103000c0d5100a0007000c40b940d8440d1106c0024010380b1486005204210081c0f0071407811a0019203801002c40011040302c0e240c0000f000001d501c6021a600051a54a0310035500100000f05030680501100003190607081400881d100200283e00012030400340e03215600c5030014001c0c410340c4003900b194148600c0b0700b01305102409518020085142d18030748115070f603085846001c01140c440607040107002030310020786c40c03c06217003c000d05034110700c00040c0c0d110749514101800c01c0d040000d12a404050991003000c080212007803003400022f6402030480e010140141c02d000031017400c120380390380c4656280c10101e05400b0300c0c5602c6400440d0651901860 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732952419 1250 732951169 732951251
    0x10e010b041116030309060614040b090c0a260405030a1412150109030c08010f05060418030c03210207022805120f1009230d0302180a03050709 63
    0xd1030a82c3c0044d8289500c0b40b021070005030f6140301d2075008020248a4860507060f210400040d00c400c2c000e058800d5000c6030a01071038107028002c807880d8082a042c04844504d4061015862507031307150b0841c0c190380b0724004000512a0100003410410302e25a51440078406407606000c00e40100c1c034110410886a10004401031901d8401d150401c2050401e8142c1e1641c1c0e9a4042603541c168110030643e94443d501c540f10180540a00e6400c000104e074180415040b48840f2003000c40102406010000d03d0300c4e2100c280b5000301c54501d4181c0520368050003005900d4400340c0a0352000c0d9040340101c0311a013440c4000081902441000360444140c0095249440300308100c3d41012043c01401780540011190300d2a8100405124001d02440c007040c4101c06061066002001d04440c0c5c00d07694040c520310043c52004642c000b000e80c0c1c0ba00700181c80d403061030500c240399038452658503000100d1100120500c4030000d407076001c03078801042c240720a11500f0f4005031a000b85070410084405a4140040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732953669 1250 732952419 732952447
    0x506070311090409080d181716050304030605040b0106020619020a0203041205010504020a0f0b030f1012111509090c07030c02030601170d0e0306041b0512010e010b0411 74
    0x7140d608040300c01401c1c02544000101104c001c3c000480f15000c2c00501440301560341d00800d43c40b0040411003440d020003d80381c0700202080200070403202c82c00010844107002c81001080101a000000c41307444a0b180d01d804401000305440c2034030a9002c081c000901e5610009405100b8140401c000d014030108a803940040d4015a4a42065001c00e00002c1804100d04510681440c005d4001060508042c0107010820703001307800900e40c4160202d02130244101d003200b101e4102500400d0850780755112200049c003002d19800124260910141600500050400c0f850044c00108ca08003840106250301030558814100701e15080021500044c401440e910082c0110781e0080c202900b03181d009a00080c1844002d0700522042145900e0109600c03904004a8103015010f090494081c001c5100003035035070398010b10061080000c511040112148030340f4090003048080c0505520340384c0c284516000c0c040708101c00429603e8000d11800d10305d0706006000a5030104a40c003454540c074180f500c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732954919 1250 732953669 732953681
    0x50c0a0c0318170c0f150720060a03090210050903070b03091e0a0c12110d02042009040509010b01080705072a0504050a051009020a0e0d030903020315010305060703 72
    0xa4100c1003820004411074095030010f002002070014110f5482c03441d080001000005a01600503c41c2840303461545250004443c43ca85c1c01c5803161655210007040c0d611204507826041d038220b0f00c04500340c3c01032505601b004001382d10071990202540071101e03080710b140c004d040c04030794994403040c0100400070000d802990440c25150650b0300b03124451808541c07c41c444141040141e0202d443d4109006044803c3c101900132141c82d004681e0060321002050355442144520420102205800319610340c2d21902440e41a0b4104e50f0011034481c26103165a080454500d004030b04040015000c43c006100b040765001c816110340c03441c0d456114048030300d81c0000c40c0407580200390582c0d50780000010201c00c10300049001406000a080605000035550090210b1100c9418402400043c6040700010015147ca1100060321040c82410803030304508094200b0b42c00482e40c0d0b022005040d40b044e01e680961340282e044030b0f07030001015841d001901c0244409407103a000040070074440d27403203a0425 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732956169 1250 732954919 732954947
    0x3061a011d130e152a091507170a0e04090b0f09070905041110080f0105010e0d230c0319152a030b010201021e030402210709050c0a0c03 60
    0x34450f40c2030340c031403072070607081560200c0e5100e003080401c207810000d074407942c6004952482c2602c14521055081c40d071030080906483c4108241800b54401c070b4000425118502e40180b2869041660790312050515404150b071346000170708461400c1c207941414001c0c841c1c4240d000402c00d600b036440c0380d84441c002002400d01d00e00c6001c0c0e02c0c40000c9480c6039014160084e80100403680a01c4401c10400a4040e001d40050b0280110074080004070625a1180ba0440d8400c1c2011030340c103410f01d80010784c0f03501900c2e4010306c041e0000034189042c540c4500d007104c0c1e501e012012100c214429508040d030f1444041c050401c6072100d00d1103403000800341d05000b004001e80315030205500d0701c18080c10780301c10310103600100030b0603403070340700b900115414001c989501c1402c3c00214900842c1c0c40c140c802605124002800340140000450115240c0e03e4005660346d503e00641700300720b2001042c103500c8891500c91059024188030208080e2030090080342c0a4101c1c0d81c071503051314003131986e081c0c03440b8400103a9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732957419 1250 732956169 732956171
    0x50102061311040b06040f0b0a2a150f06180b12120f1201060314010e1308070507050306090a1218030b1e07030617060105010f11011503061a011d13 65
    0x4684039401f412001802c1500c40050301c03800344d100700400c1c00181e4242707258000f8204c103500c186900080869031103142c2003280141c400c01704d0340c500f1002e0160424003a548030f01c0e1030340010310324810110002420f60001c4041c0204c2d801e0b401048981c100003200c04580c1e411403049080d0719200080240204441c10ba0f20a0502c1a403413840d4401030b00980c00040402e031aa141c90f500b4041302241035000d480e600c03c2141c0582403510f203e50072000700c800c00030701400d000101c580a00c03c00308031400041c007000301290341f503140c0400740f00e032900d441160413500d49080386061282180100e1907426403940341030112641c0e0f40345480f800d004030300203800000c0c0f00b08000e0420340802c0280000f54410291900c021803004e10b05141c1c0030615800d07012120040e007190f4014030003680d00819140d512905840c11103103030159030032842d00420300b641c6d05014403c1541381c00010018243c1052042c200b809000c000405501401500c485140741c00305071503403158001c5a81035103040c9903481e000c0a500c1c50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732958669 1250 732957419 732957427
    0xc0d0c0503010504150b180a0e03040f062c0916122c0a0f030c02011b030c11060307021e10020c030c06010b1224060d06050102061311040b06 62
    0x101e82110420303502560050800400f010365a0141e00801c0b03219003050381c9034400a101100d0800d0703038140150011841035203812070000601740c01c0007030760040d0000e8061300c019544d680f81c0140c4512111848010103400703848801da81040c001e20b1040013550007800ba91050342d583c0172114001c1c01101f03900b0042c031201000820381c4811b03030300c074200c11000c4007520004440c074005500ca441d2103c40d00c01051550213170030b50800003130103172030b03866040c0e81d15041064141459100680e034402141c40445549180b2015041c103269215101850140c040c660350a5410060020310440d8071085036003401607800030584e41c5120100840b0804c10386c0c200003d03200c0340412841c0c01c6050f60320200d000441d6074004212001e000e482840428014195a0101403600000e000c2d1201d00722001403100c40182d0480b04000341c0c0c0d0149080e004642e0314010511595214846900742c0100b104e40100c81c010300c10500021007040102c0108001d454010079001ca910f0310032800c01c030203001c01201c03940d00100140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732959919 1250 732958669 732958679
    0x10507020d1a0405010f0603080d0f060b0304030206191a120102040506040602100c1b150908030901050a05280b04060503011103070e0a0f0e0405011103150a0e01080c0d0c 75
    0x860100700b0308030448001da41c103003450700f0110300752410841c0303440300359180c42c0040000464510444543c0701d51440045408105000b000300200304a9008010300c0304000200401c00d0741c0031601d24403039102c6610394190031101c548828100e5504c1902031414040c42442d841881c0741440d40f0340c0ca10034041001601d059181c0f00131038426005a031006000d031344484440e2030101100d0180780c0090503140703000c40081201d890303688141c03c0d0005c40607110600302100150120650380203100740c69040f0500036500c1c100034040b58000c1000b11070368552940740030040341040080114151000c104503040d00000b0703c80e031070544d00803d101c000c190750240d56198001010388080c00780048500d00b5503401c07902c070f02c0d1060b00a03180410a501c0e0910880e40b00c0400c1c4080c400c84503610044d9144211201469903c500d4540d0040118402c0c00400c12004004c00c0079400301000704a87c0c081090792003081e00c0384ea868108441440030702504c201e40d0042e620307203d0309007400b0100c950000e01810583c040d1650314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732961169 1250 732959919 732959933
    0x310060803040303030e0f0715050706180b090d081807051504212303070b04061a09060a0603091a090709050619260f0312180c010507020d 61
    0xd501125080c0c1022a0402c241501840f501c02150b0381000038000c62540c031400f264a90140e8003501f01902c504c250783e820344500c14429100a0f9621041c10000c00841901c1128803480852045a0348084c00001480c4900049004500c0070303119180d4040795207600710303040541004403110b0b4100e403141c2c0c0c00000322a6100342811f00010848140d0304d94950900807043c25000003043e0050360403c046618000003150303c5030305400780c4a4000e4065800c059a10141d0440c420721070003030502140ba10500c414441d440e800018030340301c440072031030300c070a014800d000081c002158000d0f441611000d0070001c46000340c000c84045403240712040e03541c102182500524034020b45a442c016030000d6814010402c8900c034171900154100c80d0524060440d4682c0c122070341250140c00300b05101c0104850100d03410528101000c4842002c0d00c0407a480800019500e4210003030840b4142204400f18558280f50340350740c100e00034604003a00011611400645440e07001032400ca07007103101d5042c0d5402060381c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732962419 1250 732961169 732961181
    0x1021e150c070203240402061305040e070501180e150121050708060d20060904020f030f0a05090a170f03010e04120815041107050d05030f0a05071d0310 67
    0x19150340c460721036002e40149407a0210f800c8500c54254284943d00c02040c0001c01440c1d07000794101d82143d50350100c088401120744541e40400c5d0003a09180f0708481903080401c401081e100c080e650403d100c15864613040c0b803480144903c60030f42c28094003003001014000724803644410181021080c801d442c210340405280c00050031600f86079514140450142e02080d06908100c0407200b00d0710b007002640761040c05000c80c07070700a0311548407805000e1050f110356003070314002c403001041191260035140e6800c0450f80300315030607110301d40703420300041e0403035500e00c1051300032500c01008282d400416035031102098580e0252000340c2d081400405907200c0d1200c01940601480210a005420140750503140c0d5401d4800320014030803d0020480c0000340c1c079500d01d811260031074000c40e03658440d10701c65a03036210381c607000703400c601480502d200460740200c0250702407034030103422909170b96524458404031401902c1e02000144103103a214031190f2896403032a54000002d050320710500340f0700f42410445030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732963669 1250 732962419 732962431
    0x90b010605091801062a0804180e0109030f0c021f02010207050705060301030c1814010f06110a08031f030b04080406090815161b1110031a010f090305100609060603020901021e15 78
    0x61600e400260110300340243d030341104040ac001d001c5428180d4014250b2500b0000d07010070000000b10318001c1d0340d40c0d60003048080540d5070500303458250504009010b03510503038003a16a071050000000e03039805c00e001140d0403244c02c0580785003e6401c11a50800c050341150745c2156041d1210f03d2800751080402c503444c000e00c44000074022461401d10080c062164100c03240c450b0b0f0b040072803e03801140c1590103c17588409441082c6070040c0569001901d41240ca4001614402c242800c01c0200f140c8480203205544054880350440c542e9850440d581e00001100007610700138041c0420030b0528107000c110760a036101d05101c0071404848031036075180c0490343c806844401040700381d10354900b0310b000e14a40d44855494244001c540e1011000561186000524104640000c2103030f485842142d443c00516404029101203508550030000941424040d4007030507443d0603400070740301d8020720071100d1078401030700903100c546001ea00c000c0301072001c6121601035004e6250f010082044106405101d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732964919 1250 732963669 732963689
    0x14010f020f0616080c07020a05101b0f020a15090e060604080f0106140d0203031c1104030c06080105060403230f1002031017030409050a090b010605091801062a0804 72
    0xf06402c10003410508081c065450102040050310096104d100d8a541590010b0700c501011100480707040f1401100108914030720210226148100080c1c0d14242e103029000b101c02c01c58540d100c00b2540070020300b0300808800b240f0028010440c040d500c02c51958400c10080c01107091503568591207081c100150406a41a5920102804040c40802a10180c020240d440b17121000840d40425542c0c45400c41d050725003840c8210301540e10352207410020240401045141d200ea9480c9480b000307641290241c003001c12809400800d00b401c040003664122600078600302c801358481c40202c80230500302006590703039009803102c8115a902c100035000a00710500d500507030300d280c40990b4000002c465003100010303000ca1948045042400011b8038141d5510031000582c94460380b4203040180765810000b8202440e65000044098000029000d890341c00e490a5512440010380c1004001d001d00640010030104060641102c1006040d41c0011105402d2000002c00d60303202c0d40103642056014000e50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732966169 1250 732964919 732964951
    0x60b0109030206120f09030412060902270406050a0b060d090311010e0f1c0203040612151401030b0306071e030906060f0f0b04030206070b041a0f0601090f14010f020f06 74
    0x2485405030b610780c0c0640144c01441c1040d003040701d890427161100340c002d842103846d0b2030b1120565440d03603800f41c010070541c80c004545214a1036081c20a5900304d6003559014075050005100b904075000e0340d4050300c4024081803500610418a900622203400290100646400c4028200f50240b10785103038095030000a003030419035042114a0600c031084c3c8415003801c0981c5502ca11900041a2070940388181000410070140a11201c002c0c0400100d0840d4030310402c00000d94420300742e0707800300501000c0c1e1b014840044a9020b261740c0c0c2c01d017500d0342d40c000b0360310148040a4124950103c02e1390200c178a00810aa0f45030b484000c20790b01590861050340000b01001c1064a0307032902c1440042031001c0f2298142460b64000416900440390041c1040724010300290400c0410f4500075902191540b602109050100c402c030000b200466185001c40c0404002044c000d140711142d10407a03200b20901c0e000b003030503400119541d0180604507800c3d0711513011015403492060066511604c0051048200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732967419 1250 732966169 732966181
    0xc04030213020c0a031107170a0b0615042c130210031e14010e010305060f060f061303060b0316122306070305011502031803100204031a010806070c060b010903020612 73
    0x400803150301100510308c0c03064842900d000041140843d250b0030881c074824940d0b400d0302155003d9400900342030030110009011034000405035a6840110042040800b041c1c100c200783c01700c980c016200d1004c5500c508440e10700519110603800c9142c11a4a0046042d0b919002c0009047c100c8030403004200c0c1d00d4041600000068200060040600c10b211303818a5145407291a02c42101a000c03070955214440085d50580b244100c0d8400084040c2c0340c20b03a203185001c903030100c204c1136000c100c42a81c100171f03600c0807500d0001000328001900d40c400745e00540c5000060312020100100c02c0754040c446a2004200800319540e02c01410241c1d800b900c0140360001c0000d00701e40050300011201c9182901010105900009961040500d03121010060110b403002031b00e0289440340c2020f0ba00d000040100c00c201801104000d03104c42c04020380d03440e0341ca810704141c072800100d80d034000092240501c10f002c2503403a000340a00b5001030400008041c1c981d00403600ca5030248001d407580d13046880520003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732968669 1250 732967419 732967423
    0x7030b0a170606010c0308010e040516081501090b0f2202120414030a0c02190f0603020c010f021603120603021e09241009090c030b03150c04030213020c0a0311 70
    0x42c3c822024644040b44090702e64005d00b900340306014450600c00c1c2035000400b0003204000f0004000400800004c9459480c0c0303150340c0da0307072035225441403030000d090002070300300b0b21400b420095940c01022500003564030000d02808605800080c0903000c0c2e00700440610030400e04c010700c1032a0f030414000035907281a00304a1250703116401f595000340c1c82042400059540560f0350a03010b0750488a048030100c41112002d0034000f6a0891021040c0c1c5040001c0c1c000d800d58000c10710320011000034800d032007441c10800200c1c014440310001d41ca20a44010300068490340790780d5659045000c2c001000c640b242c020460048115040301e140c0007415100117001d10740500c95076848011240d41c4000c107010514081081031403040094000d50681c100c010040703015240c1c42c030150103046004c00080320701d58170040c0607040b000c1c0c44a019000313000d40405804209902c00d0b1140003201c61080c5445e140d94203000080142d84d281240385542405a400001000d202902e8420b010740e85003032101070b540140714 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732969919 1250 732968669 732968671
    0x60b1210150e120105071d190512071802071103010e0c0105090a0e040c03060e0d02030a05160213050108060c09150922050a0f0216020907030b0a1706 66
    0x3415410804010041074001425240302000310303140480810348100301140d894516840c050506509010401115941c04040b500d420303100d150030146961200800d018600c4401c2c00b6a56040803580e0702030126003001d0078140450361544040b00c54455071080181031a101000801e080c0c1500007900e0401d2000921410300413280440080100450202c20a035660340840182418440c000c21406c01e076545074025840100446810368a691070a840c0c050150001c034002214003602e0303d04500000400004c80c5202c141c000c0e002107103401e00014068a0b290811030b00c0c0c8900140704402800162900f00051004404a510110b504d506000703005081038030003030010049010034000c2600e5682d07000104031001382c2070450745644040345000700e80680314229076000101d81000d14100c4134821b0750302c064841c0c91032800c00c2201d01c4e10000c1c00410703481203a9074810031501950408000d460a5a04a5000380850400003045000b400c041082284203602040c91032003000c00220040c0e1081c0101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732971169 1250 732969919 732969931
    0x20c0906040b060901030903110a060207170c0601060806030709060806070f030b0303120603010b060a080403021b0108040813090c05071109040b0c0a0923190e0c1606060b12 76
    0x52141c02d00300808500e2600a1915807030401da11003a80c0d0052500038640744885c01d4051003035a00c00000c40c01c118000e54080304044441400342c070103a1403203101c2c0c00103079000320501c903000d0b0170182d2820070110340302d6034081c00c15580740c05140750028294115105242c0108070180203000340b417a140402504508580410805050804100141940c2c000c0212140740d261000140541e07204e0344e01190040c0301c01c07484150131100020300c9400103500300502d1480389219500303c0300e0000b0752001c071900f0310304049d00f424085807450700464001040100540b003800c100d1158187c560390760304240340588039041c1c9164041a000945031050050baa01501305022058038011034905040d541c1e0882d1090041907000050b4020891100580c0300b1420380700185801100614940420459080030308924040c2d14420b02c905142c1140c01e14519130000201c4804541000103565000b88900b0745903c0600c001c040442416641400102c07a4403c000281410110b40754490032108074040d02a9009004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732972419 1250 732971169 732971171
    0x11418040302030d0c020c040507020705120312040308091618140f0a0b130f06090c170708092e0c090b09010c17030a05270c0907050712020c090604 65
    0x10040072070b4000003112241348181400203511441c200e0101e0078512002c1645611074181001d0000b1294000384080644400300c8152080e03040081c020b9076244102e800c1d580e40b8400311310001d404280103541055001e14010103032100c07003964095069010301d0581009a4500841e070036503640484901c541101000849401c41c410f080181d0300740d00d001070040030390792001c0e12054110440d0f1603c400141000c01c0303117030060050840f241c0381200a0701150141e486141c1c540503014401e90f00c1002c00c41030145460508010039102d413141101e95a40040c00d008491080f14103034456030044118124100c49803080c44140c02c186400740c8010380c1c10b00c040c520100218a40c0500c4500d64500271200c2c502824200300a84610603c0c28600c2c005006d4a00d103e204030201c200001d040d1190045c511901001032410300d21085160040c0503514420950a150350003214003003c5400c00f034005580040507820300a00b066240d61720024004001410500160400104104d140c14151009500a40c1c1114 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732973669 1250 732972419 732972421
    0x30c05030a0809100b0d08091206010b0405040b01050901050d091b0803031807181505040e1501051905040906090b090a1a0106050304110d0203030a111213180b09011418 74
    0x10000301b42001030013000e00002d40014140900f03646940009500b280c104065480b290780d41c0c6807402c002e801074422107004a00708103400032190700c40c10441e001e2050584566040c01c006801c040010701d4103440c11140d003400d5443c00030040d5002e082e80f0b002080050029582d91408101d4080e034a120342e016039605d94090002444035030802e996a0000d40704c0c07101c0002d44404d02c4111000d00021990260780c00928240409a4030400410441d624402c842e1030b00c80c0340d0b6030350820701040050b00d10052224408600c0c041c4003500d0190042880c5900409000c514136030030352034407000308905032500522580005509401c0041281d491070ba00e1002000b044010b6241080c0079001d840001c100820031000005c082c5041e0340c4003020707645425000340441b41ca518240c0340c0030700201003200d1040c545110b0058800b42035032444007100c0030541400703d4081118946659519020500100310120507124a44030440d0340300c41d0b0b00381d070080c80700d1a10742480c0000c080a000884821000c2803600c015228 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732974919 1250 732973669 732973691
    0x31a01020604080a09090c0816360e0a02130b040e04021c0c0b130b03040c12031418040f0b1e0109180209010905060a0f050304030c05030a080910 64
    0xc00d01c00d601980221600c2d5035100c110300d00303c40801d81e9070000d0301c00c54507000e600d40b1040d0748200c0b9903124002036000079594101c031030b0090b90203410454520070500324001040702112040c03900c0460044010034095021911002d8814000100301d4001c80410750100e8011035000402070244020301c5500c012078030b0141040a0b101046400420113400341200c08240203031426078420348c60300b0503000039981400640b00c5d07650303410079072100c800000880020900803520701ca94a00700c2c3d000300d501500400d1142c0c500020110007013500c04060301800185c2030758006500302c0354010000683ca03003400c0410031000d0410032088860940c8c01c034500900d4000d1124003030301e5408070880c12520000c0f240c0d40c0700c481c1000407110090035812055001e15401d01034030001c12a60050a81c0d903d090b01d860502e107072940309100144c040caa100c1000241c80e14002141c0c0c0d801000116040f0380a0310f00343c502420170f0388816155501200092001842e40006c0041c0c500040c0443c0d003003040c80039002c1c0701c124469 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732976169 1250 732974919 732974923
    0x1c0b1903020d08040b0a0c020102070f0b09090417041202100e091b16060e06090625090f0605070501050a021c0b0303090a030c06080a02040b0f070f060e030703031a0102 74
    0x50000a020b0401c0740c5103070090101d0603050700c0c010b003c1e611045a0700c07203a40200520314000c00c48101e01610a4120125112072590703e0350081e00c145001980c2822004020070031044005001a41c02c034071480c002c0428240100e0060000e4055070f04d49444500452050085580740d110004d0104034405000105565980c00d031b668002ca5040c0e01043c41411203407002d1140d102c3c0d9039051880380000f1071844100070b0950040317015100040165049540c86580b000e8880b10125040c0e04403814014100341d02c0071240c0c000003006401d0b40b8080301c0003a240c95030070614104540207800800c00124403041009000d0080b1070b484040907405500304511900b8950062000800303071f51142d40c45141c1000c0c0e5803002c105132000150020481903d4a64a0070450180c0368140900e8001a04030400500019441e000b11412210022096864901a004501700f00c3c0c001c11401c4500f242d0341c03282000456400e0084125180c0c0400146545404600d0301404481d0059601c2d440036949001602c0182e0700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732977419 1250 732976169 732976219
    0xd02062203120e0927010518070b030105090c0a0c0510050406150501090603113702010203040c06031109130e07080f030405061e0a050403060e2a010c081c0b 69
    0x70004c0c1d480700403050b0141c074a285e9500b403050810325881e2400304160928000280208650041c0948621a41b80c2000040512090040c01d820418400110341c6554140d00140100103003854460600c1700c1c60f80d100ca040441ca00219543d00e0b032a40c0902050001520440c0781002c440c00c4004455441d000c0041c080c45260700c20f01007899610002e81e65401c8582c011943c03800b03000420807a80da1107207090300907150480c00419044c0300321103401c8002e880c0144200c9000da5080b10324130074018948441200036208400c52030501c984180400a0107844070092002c528691200104100c800c0e03c0b901e03443c141003544482d01961002c1d00410322550088221010389405552655407010610900c03440d22040070440b0127040300014819502c0340e8406d0141080d07900c500700501156050b64103031655a450184400744002d04099500e0003020200c1c107840d4148418100155034401c140c46820041d0004000f034140d072000b942c00513505010710b20403148045821a03210f0060034060200c040304681c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732978669 1250 732977419 732977431
    0x5010c030b09091e010609110d0b0118140105040306020711010806030c090408030901020c1501080114010e190e03131a070b151804120e0604080a020d02062203120e09 73
    0x1030001065a1820006c1d080500500407081c4107202c000c0c0070b061a00c1e01d9600180807807201c146003402236840344d889180c005a190b1020350164064608001350343e001d200c0c00450309814403404210000c0024401d0020b80303d0700d801100c1b4800500d1256002410f1641c000301150b03c01d401407140c01e18280d940000d829000382d00644907949030f0340d840315120700901c0b03040c8800e400f0b84540b01d1040035104c80c03950001c0c140c0e800c0758024054440007190b05c106101081c090708000c041c1d1100001c16078454580420b03117003195202d0200f40307051048a00d504540c0a540410794803100300c88141702512500c00d145103019420046a460117905880c2c0403440c0e040034041160000354102c4105240d5110b41c10410710000203a0785201ea4180303440d24000001800c400741012909902180405203006001e4030110b03841074000e080c030381030603a0030044000404030b822039101d803045c0700c0a4a208058805284c0e05c2c05506511590780d4154241450301c881040c0c200d10400007100b0811025032251100950800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732979919 1250 732978669 732978703
    0xc060705091c1406010e01080f010b010507120909050a0603060605031212041a010e09253f020108092833140906070806061605010c030b0909 62
    0x4091883d000039148882895200b80d8440c0c04004074440a40c0500c540c120b49640e4105c03012400040581ea090314040902e5501003407050108002040038240034484250041c50010185078890103070700215042992481003032907a40009104000c110f101d0301010f448201c00405c06207a100907121960301c01d014840303402c040a000800d0820410341c06e10b0668555a0042d44415a1560450340e43c0c440121480000e0f803148403d0510350075040855602d100200016000501c0d04001681b510744075482034071110314000003501d40710200ba8140007402940304004204d041da40303a0000516000c07003d00b0714495034202d41d011812060444103101800506088910714407842424540303888802881c4940040684204a00098150188244104800460801c4221134415001954540490f20715003264422008030354014002c000c1a0382c86030004020910b45204862031112001c03055108035883ea440e8100030351083c2d0140124401d0001c1503aa01c4030515101170803695410301d200080e0380074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732981169 1250 732979919 732979969
    0x110418020f0409140a0503030604060501172e080d020120090d02011710290d09060209060c0304060306140f0d110d150608032b061a0c06070509 63
    0xc0203c80305560113084010641d030b00c4146506000707442c0c1e881180c0c0d2a02c1a407030000042829130085d000c0c0450080c94a9440c1041d80e140a024007504d01c200007008216001040301000c01c825050b4040d0140c400e0030040d1400101420b00a800c2d81e4031591001411910400c20745040808141034070003160048a2a022185250005031000b01141c86a5041c03ea0740d202085130300d010450403c001c54002d0b6105800349654035001c140c03030320401000d02c110f005081005408075901504140040360041e0300c01481c101607040068140d901404280c00030703400c082800c21807503426200709001001001880400e415203040000e040404400c8a14440d103500900c0038203102c180c501d4010003400c040c1000c0010185420280c0c424a0800203100c0800d00703122002c2840c140c084165020403801c41180a45881000d800b140c0342e961889c8100040b03035075200c0014600074000c0c13030044004500300c1c4070f540e29072030321540c01e0a00500903d000705009c0100204039694598100801144500315204a84 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732982419 1250 732981169 732981173
    0x30403050403141c0f0c1b05220501060e010909020a0c060609090b090a02031e031903060302031605091314030703051b0d05190e030a110418020f0409 66
    0x10034000d41d00b0160290a4000084140c4030000808200d24542403054012140d8411000c0360b1586200040785c1c0045c031b00001e04030001e448108030824074652085a03080b41030311040461b0400c00c05c011100c000b560f058846080b40310482c03190034058426840c0c002d0031205c140b000605614400e100e0151116400291040c04601c40c14001c038600d540714109101055035100c200c00034140d964020340e41d4241190100e6841d420011300800e01a501030054400712511143e6000440702212641100c3d003c20401040d541030520f1045500c403045440000e149030442c011316152020802101084280e0709a061100c2d5442110b00c1d80e000c242001e00342d901c01030382d03d8920800600911a4100c901c0301165000c10180c011001d0041c465243d00a01d1402c43c0183c0c00b103989585114a04010540420500884008130041040007440e40e003010104e000800b0003081c500100b20310181c40421120080280300d15040c0a20106240401004506054190000b4240c0400f0f840b032140b0076540c890641007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732983669 1250 732982419 732982427
    0x1e0c03070f120f0b041d0613020102030c0a0c0e0108010c090b0d09021806191802090a0509070801030501061409010b0a020c0a06090315020a0e0108071b0305041514070602030403 78
    0x44036001414403d01e00110441c0c400303080184841d070301c0740b0705041c01c0c0140d4940c3d000050402c624105c00608107511240144082501c07188400c0c2d046000400003081c00040c00c20840341c01d948905030750300c0d81c2807a00003000140481a00301081a03414422559072481c2d01154a80a442d941e82030035a59485000d210801400c0580009410402802d00d4003421443d0300c41f4544645000d03074541d806000a1340c41c05070000c80c1401401c04100512100c40204e41060340685442000900f00109481d124000141850000c4418000042c1490018000c000003030041000421070140c180c8203c442010005074840d80501420003200c1d0301041d80d40c2024401c1014012500029104105e03c0391100c4c4000c00c041540d00082ea0507006000c030031002514103200312241c0c44210f603580d443c0a1042c40046444a001509810070001d03810a9003d041041c58400d0040c0d034807d03152582c0d80d51826200303c08044000d010001408004105086114501e50803101076652000300142d59a0340e914042e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732984919 1250 732983669 732983687
    0x207030806210a031106060102010c0813060204050607110f03010e070b16140307140307030804021e04110a2604022103030106050c060f190b011101020a081e0c03070f 73
    0x60b24816001507405041e00045032402010081050b0f4289a440d10010381c20f07207080c0c41c1c11100141d51b03080020b60581c3d440012070b200c680700381409480d00b43c2d10400141190010402920b000c02048100c081501c0c08180701d20350180c00750b00074000203071400d40c225100c105501c204030380621700081558503804135480469440d90f2003a0070361075000c180410580c0e01e42000c2012102c0d05402c5243c4009260000152118140e0541e02d44c140399487d6402c4c40b551407244000800e02ca20520180080b40c1e441e4007907200d20b5031505002645840c94203c00410f00d405000d10070b16036080414070f505100c0c0303405011030382c0140c0590307520400268080b1000e80d0f046644522903481d000110011070a82d43c0b020007001d034036031802c0444005031110001881040015100003203407065600d0450400c1d100b60b0403002e5400c4050519a004000804031325080e0790001503050001112070f020001e07482c594040d43d42c4d00140003000394610740742403051409a8030001e403401c0240002c070300c83c200f8118400c0e0a00707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732986169 1250 732984919 732984979
    0x1b041511010204080f0f01020310140d241104030203060c0906040f0803070b090c0a1403010f050408340f020406120c0807090902180a0b220f0207030806 67
    0x2156116660180291540017003160120540100d080194001e001402581d00550b44d101c142d07046140340c048a1107520301c030a103401d500301c0c01c24003030180451108003200844a140c1c2c44441c90140f5081402c00072115048841181650180018005a02d000508d168004000b0b2a0140d48508000c005400c034080c0d0340c031280821101d414049200c00e404406002c4041c4901086005519615006511003600440d02030b000000030348200000500c40301410712403003014000069006812807010142ca0040341c09484485000440040c0d081022107140b031480219202d000500e0009610040010118071014200702d0f10050324030207550b9603174052170003030404200b2200c3c1c0d008107142c84103840781349118040302070044420010b04000c1c18028042e03010341c010b1181c22440f4204c030f80400030b010054400100315658840b20002d035110f907590900c400245504040d0010503103650401034482ea21608041c85005000d00c10000e5017015200c0d80204045841d140c05001004080d0f0f00301d1016098 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732987419 1250 732986169 732986171
    0x81b1219091b0e0601030204050d02090a0635070605040605130b160c05030d230904050709081b0f040f11160b01170703170705011407081b04151101 65
    0x100020351200b805850111285401c0b111202d60710b03840190f04a0049115042d04502120542c80052400111142d8071001035400052803540b030f80410040703050310a0030105504e42300031840508072903480c5042d0385c2c1d0b00300d440280303183d42c00c0440060060040c0d21900050100c04604d08401805038002040500080800301d6255045440800d0714010a0b030800d5481e1700780c0c402c0100b41410f0100d440607000c00b0750340b606c0311014950031103440c11861135200d030a01d0680500c40c03807007141e84500034036000740c40300d0f924003d40c103003042403060a154400820241072400180500007948801f4410035458804a400203044000d100b81e45015222411201d06034950004140380f20883d04d080d08581c8601485060100303a0b22005607042c0030038401c0300303a07550390b01c002c80c20800103075594401507070a41c62282090400d001c1da6141390944104113904d0540d941e0120030044200e81c8081d1040c0d000709400c00e02c3c055100400501e403406e220304d000d45012549204402c1042d9401640e0804010701c100d80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732988669 1250 732987419 732987443
    0x405040804061710141318021207361523030c0603071709031c05331305010302090112031b0c0e07081b121909 49
    0x250402099020b4003442001c5030880e06445801d440c1c600f0681d1103590540b01002215013400681c2507014900c02e020b0740c0c0082c0c3c205654000f10058060103140104483c10300407000054410006c011110301d416030056400703810200142c10140c402079445c40e000c1c4c1010300481500c0c021030b00c004181d240d141b1035580d081100100340faa1164204800315003030141e240044084619090060340103221045038141d020803240405403421600542e0000c0c85400d03e070000c04035810300c0003d140800c450b12403454101040003030060301c1c40e482c0b111076962511401c11091600e400348610101d175910382182c4a10706540405001360550740511503568004245800440d14000d04201800b400d00040b0b004840b008000500e24262040380c1c03d40703a0389600c9200d16100c1c4100103500c0145907500554410076000800640d0030300710700c06035028280c00d545460407440d20444011070801614805612508108000842c0c862002500d681162050343e414085100d01d000250150041d84ca001d024484018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732989919 1250 732988669 732988673
    0x506070e0301110901050f03090309030a08030a060504060308030a0e070807080c0f15030a020304170f030f1f06030b030f030c0609060106140412030201090c080f1006151805040504 79
    0x60351038260a8400c500902c05510001c034005030030700a204485011a40c2031014820368480c040246501401c04803c6904240f206000a0f1903d0000c0400b9610300c0350010030301c0045034590240c600606802d90302403251514642c1c03805020701c40101801401d544e00c100b1681c0d10300302406030310000c1c00400c0880d200f0135141c0341643c1d21500c001070700900c5105800c01d000c010707003402100722800e184070104050643d0b8603119580003a51004004980040b68020f03003001c40380c810400382140020f242d0f642904c80c504840d80c050310180150461a0030034501803104a000c01061503030701656150326005c500d014049010034a070126a80c0c4030b219a0002291800307600ca400105144078411440485590340d85c8c40c2030568104003107500d84040840100418403102c400a00500b007074a10a100028954000e80c850310028031441d040b001c015004074640f2804903400b00982c00701c001d40c01c0c01c200501d600d419594400f43c904441e9040c1803002880020404010408940c00100409002030010346054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732991169 1250 732989919 732989927
    0x2103060f081509010e0309130207080d0203040605060307030b130309050a09200c030d0207030c20030705060903070e0408130b0301061229040e011514060a0c11010c050607 75
    0x420080d01d400041000246103c0b205014050b0203600711005140b400d135101e400e1105080c03d40a00c840416000c110180000d807801c4000e221038072107044010307202d00b09440c00c9004e803030303000d23003194030983c0306c03007018800f26800004841d040454000e00000b545507610702940c00c4603450303101581c807480e51000003940070003c2c0c00001821007000c4001c2c4440c051040111102e01a41031822400c4c0d04c280403c240528455000f460418040d0030280f141c0c50090380c0e80c03504140061b40c1a252610910201d5015080c20000b02024140c100c3c4c40a00b0300e00c91002103692050307544904500306c03020303002040034050f0600881d48180107607500780000300d4585c4500d40c03003036000707115410000f4001c508450840c01f40d03104581c04203885030700c601003074800d00862056200d014043e05600c5a079a42d42e400202d182403142c060425404c50020410a191907501c40c003010001c50000d000303000400c2120405c41d407047e0709450682d8080c4000c02a8121080100c81c074419844004255104460074080c1c09600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732992419 1250 732991169 732991183
    0x170603010905011107020301150803091e090a0b0a0902091c0309080d050304030e090103211107060201050a060608010e0703020c011b1e03060605090904110402121801092103060f08 79
    0x387e00034800011f241080f20007050282c42404c582c0e40040c0585502860036035007440000d16212010085542c0d034400140d50305c2c2c0c2c00c2c5e50a0300295510580e20f80c1c58100b161500000301641801103040c45205404144a0182c191080000f00401c048820806d4020566680500070040c1255908112114040c201e0340c025079065002c00c00751500700c0000d04d00205194141d1340d2048144c07008100112a2040d9070000c0781e644401e004040d135145119080420100c2d0080119038008a42030a102c141c190840b8100d41000003042151401071140d02540500b0307039040005440c0040c3d6030300c0e401100354018003d40c2400004919014800c00400740c4c07241d500320107454000524405001080010340c110b5800d0701c2401c02003103040c0300c00040c0749491103080d54094001c01c54085a101810001070481c0d100e00030308541c0d002c0348014400f2095901c1c400c040329025103802004010003d031a20005444200440720100d0000c40181c1c42c524440d070088801450250307050302c12152900740d05529550 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732993669 1250 732992419 732992423
    0x60503010305070510201e030417031303020d0c260f010e060a090227090d09060207051e0a0303020c030f010605100f05041a03040c090c170603010905011107 69
    0x8543d101c04105440c00000241e89850107455a211000346944190385c603425005010743c0a000b1198a0f810000c2040d45809552110101442e42c3c0c5c0d0600480e881c40c50100e4014400692051001404103003034a1004403d0365011034041007100014038100d5861849608524504016250800030f419441031454406005038425100301c0c400d10f070762003400c884162039080030581c0004040741012016620622110f8000303130441c201c80304500307035071100b009054100042c503414220401068031701c2406038100c21800ba240060505182800c000d6032880d0034000c0e00d104450004103a0b452400408000d981114064407020b2a2541c90501035102c20440c001e041c040e00826030005c00000041c415001074a200402e007903c12001000e0860780b100744103c012040c88400c02c004200199086540025007214510403070362440d151820780340042595100381d000900786034015071441c0d04501c010354403090007078240708556a00e0001034054110340b10040d025518100d95642e10206003402003034000c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732994919 1250 732993669 732993673
    0x7061505090f010b0a0309021503162d1209060603050c0103140c07060e030c07060207050105030c03130203010b0a0303091a03090d05090402211905060604060507140106060503010305 80
    0x80d0355102441000d5004035110300d81d00810320010b000c6000ca80c000340c0840b0440380381c0010f46100c26400304019000390704c2c14075110400401040404620462016100825450005580e510816006488014901618406030070003070081c1d4a103842010f00301502c07000c00805101c880210b0500b900200302500003511540600701416200e94080c0c011010362107950010002250340b840440c00c03c42d00400401ca0300e4680307450300c1110202080020f400082c0d140d402600c44945082000791601c02c840c0d00c43c07414444207208101c100788814080c0d03a4054010742100030307203c070b035880000e004140601030701d64458030029020003415801550f0905032032041111445c044412860041d03940001c50700c5070b105910044605069920800203010310240103071025051039020315647c0f410f0518a07c80807141c495120803c9501030a1000c6502004240d100c20049403c0a20112342503120302e016030707802d2100025030345d001c114041c0b101180210707112008224a030f8842c80014001d51080c070003074540d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732996169 1250 732994919 732994961
    0x250b0106171008030a181a030a0501090b2803060501060201020904051b0a180302060d0e100c140703050408030f032703090919050711100e0a0212030409020706 70
    0x22010080104142c03072100740158100110020100c404e000f40f804e4030106d500e104e03100000d40c0075620205401c0f6090f40201c3c20385902d07000041c0d10494605038400e11302c5030305081d0600031980b14400300704020b846503262100702d0544035500618a15603a0300c01041d1301c1ca0000001402c56066010346003890040710244030310344480e0812201080010f0811140140400c842100d0078020341074840c0c61844122542c0c0300303a55030b1300080d1484e084103084034201921001440d02004c420f000511030807242c42002c006001480c00c008040074000380400039905400140c0800f418083c0003554001c056180032295034104640409505400607152000c5155984e0700c1d0300040c1c00e80351003444c0c1280d80b000040d41003e07800020441204006070015845c1c103da082c400207101554060b59200d580c0e02c0d1220718044038155400e03850400401e5280c00c10b98603000400c4052a00800c02d1a00190103c403040711480340d110720b4608503c10359014818051000680c0820880341c0c1c0c0041148081f003030014148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732997419 1250 732996169 732996181
    0xf0a0309030f08162f1503061c0c05010305010605070b04021509090103050c030f1b0f040b100305101a160516031a251d04230105011103250b010617 65
    0x400740c001a8550b62084a003032010703a05619100247d580120000c048440c84000287c8442d01405503100540340104010710a00280d48c06010f42030040105107082480e101c0c0e41d4031000c60705076010780028444c1c0e01c1701e2040c0900180d01019560701c40340c000c00381102540d5a00d00f803540e0307051280d9000e0103402041e00503526100302040705003c440d40c0420342002241705038200a455520000200d81c8580d540000700c0c10f40c1c03646d2800f5200b00c16944c8000070607041105800e5000c5e8100d5102076038400d2481a20340714480644107603258400000c451b000c842582d40b620a0411000720310119030161501000001c1c0303c29020800710b151541304021417035456051000807120b42c0c2600c80e0081e00c501a541c0c14500d4403400c0340508044986410301d05545e500000602910341c102040c035044202500c00b1f204d5000110352641c01003d090800090102d41c6d8102d8a4076402103094104040083c079400e070388004500c2d0140440340e40c4c44a402c0d1520341e11644003401d00c6009190725490b00103034400040c1c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732998669 1250 732997419 732997493
    0x40c0302030609040f15020d050a050606040602100b0409050102120f060102160311011202181c0b060d050708010204030311101e0908040b1303050f0a0309030f0816 72
    0x2000c1c0001030200c0c000c03135456445001ca00d20903400102c0c0c0c25405010480c03544a03240c805030060003610350700420b044c2030011f41c01042d139101800e05480740e00700308001c01440343c002460601c1148607260108102600b103000400400c41c0c0754000e0295400021040d4030801a2050b80b171080600410b56130b1070b500d034407004a03541c011550700e10a406542c804280042040e0100c4400d0325103052404a0b0b0128403600c0c00c80c16600b01140d901006459581d18109034038000d03a041d040c1c0d101c6050524211030a07603c0740100110040d003250b0040e4101801282404824000795000d4981d01c0700940d66183c1c0c91034000d0882d410201410001e010714078020200e00218010f0710311031200300e640402c0195151440c80c0050001903403c88580204010001d007840c28000a00481c036040781075508414034508005080213001d0040f45040d03003190b400c4000080e00000030070162070704044441c40d0b00c00ba0386003850341c600c2500845152800c008048000b00101921030721610462072000008140384202c082c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732999919 1250 732998669 732998671
    0x714010b01201002030c07141b0d050303281125120f0306031a0603070b340f0f0501150302010212030703150308041e050f090702101a040c030203 64
    0x807907183c122107400f940080c80342e0040e5030000c07410a5110314000e46a0394008083c0c0784074029400b1070b00504200a0100303d029195003803246d058422180809460341c505450b40b0004240308090303401c0303520b6420061400d0303411494041102504020590f00845591015040240c10b01d5192a4481c0383d05030414138000050358195209259000803405808240c504d2120407200600301582c680f0300001150860702d40c9540000c86440c0003250781000414141486919002511051000c11030b82c00a080001284403c0800300443c4115604a01d140848504441900940820282e9100c00c0174000020b041e0b8210a100382c00821004d8004000e96007101c00b20b10020f4056040844039003102e6080d44c0085610034500c1c03400040c81042040b41c0e000341c902c640c00c01c0d251010017050500040c00c92002c15991008100800710b10185004001200700d54282d0105014409070b80100e51018000c1000340e6050030008030a01002c0341e1040c030300058103445606680310b80c4c10070705185891070080c030860b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733001169 1250 732999919 732999977
    0x150604091b1b03030b040e010f05061005040321120e010b011806090b030a11030106051209070b0a0315051302090f041a0d03020f12070b060a0b031b0714010b01 70
    0x5880c03100c10b45043c1e005020ba130405c00c0c2c00907114000c1d198140020b1040d035005240780038002445062803014003e503a03408991180c140b28013004240f010400207804803070f4100c14a8800103426110043c11244684000694002d1a013410b1088045030b070190070854120314203076949810200d03805466800020749100d0400130901c0304000b44150394900700159801800c0010204266030b80021000c0d0503402640302a0018501141030b5401240c0b60701d050340c120b000350700145403150030280010814824006614103042d80c2c0c5101240c0141650030000040800410401403488945000e901940c0a4092b461081c44810001051841c0c035105840884000c1c540c18581b0141100c1400149600d8030740550641c414040b00c51003242c0100011800c00407040c034040d0b02d51040f0720f40000c40301302c0030301414890220501d0500001180800383ca900c144052007010a80c21808800c03640c80c8510180602015250040c0340c105e4141500031140c145001e0303076090034843c0105080f00c0a00003074004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733002419 1250 733001169 733001207
    0x61204020126130302070e01062604170c0a0218190e0a061104031203020711222f03091204120807060b060304050703030801090b0603010e150604091b 66
    0x10070103070030a0704443c55110340310f401202c648580b40d414164169009034081c00020b1145041420160624000a0074400142074030491505090b51030590301d204440b4030751100030002c110888926410003214207000d0700901340e2594640c1c0d0b6039030204007030130482e61180c071444004600c0700814401c3c412420b406502038054000d0000d01d50302e01c0e000d44180003001100d4903050001201261840030b42c004c4161685c0c8006907039410620340107160241c88210780340319408074070200310605443d101c5138042c2421504005140600d0444100c3e031075401c030604035174030000c0c40068841340003170790002c50140d203078403007110f90b110400500800c05100d14065442409180c041940000b030300d42d00a801c10b0b40c810f190206407c0350f204040b444a402c1164240c5907a0720561040040c1a04984aa809082d02000501410b10b107440407a02031310041c8201c954200f01140028000910b190f03440320300c00d40052045d9030f6240d46110000107031103031400e2031544601e4207980030801400b803c4240c000c0118051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733003669 1250 733002419 733002421
    0xb090c031612110406030803070c0309051e0f060f0c030310090902031203091207060911010f050f28080a0c020c0d150e011b0315050d02090411061204020126 69
    0x6500a0f4401d000c03401c00307420589641000c000504460b0141d44520303155510400e003112641001000740b40c0743e90016002e0540c2002c10101240c0320103600708000c1056589194410fa00400b10360a440b41c2c40e0461040400400c100c2c1076248040021030050a01c0310f15162031640700c1c00200201c85402c4030081d415406000c05040c0300c0c030388002540c1d100340c0000c29502105440002c014080d0f002c208100c80e0a0f82d6070810b40d082100501c01600e90440038030b45000200c00200c4060268031410080d0b1180000208540018110007589016205106007101c03042c100d0582c005440d1240a0b1800321000c1e081c01121030115200041205500d10700819001d6441d070903460306000000e0150440c200035441c2d100303410150740c00f4007400c3c0381c480c1c440c90f0404101d0448980241210320710300007030340d00040c01e100c201b0443d96030700402d100e459011a290b040a880764503082060708007032103041c0d400c0340700400e40320165050a1842d46c883d034000e0321744056003002654844000ca00c040e5207603000c007040030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733004919 1250 733003669 733003673
    0x60806041422021c03120b01090b1e0a0c120f020d080a0b090106020f010e0313030b0910110a030506060304030c26040b04051002030c06010311010c0b090c031612 71
    0x324282e0301040e190901c04050441d5500440c15602d1156116003040000514a0301050303403000d402e07030940b41004c070b0801c094010f0360002440c44682d0310841d1504000841d02d114040189601501004500c2058590311926031030090b1800500c0c8400369880d060f403d5041c880180941e4041944030a41d078064060040840703415100560080d142c0c034949130350346907030200a494091800d406019140c008010011740c03440110f080d614404813009080d0000d101c80001d031942c000380703003003601d40c0004801110341e2a540c15034941400f4444c1b1085050074040c0400c0b8103c18040202056152680c09011a070b4a072424407440d44029200103001403102c1070040c01003070b4406455005500c1c42c03114440d01910948044015130015000014071407030000c0c0c1001070745072000b00c60611441da80003550800413184201511000e05200240840700c149010240c11386c82040240700803540180030744120304224184e2541c9162203229107000388a508554031b0040c0c21602c807036046984034204800045896 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733006169 1250 733004919 733004941
    0x7050405040f060312030522020906062203030507020415030b0f0603070803300103020109290f030a061e06121d0a030239010c06020c070608060414 65
    0x42c0c180154016a1001d01100040d8090069200c000c482d50f0040340741d080004402c1c007403103141841d140d03201159480f101e0040e02c41010b8607601080844500741c651500c0982c1c0355a500800e60300c130200c40040c14010041541041c09070034198000c0e90100090a0a404144140c55844c00040c00c00088100002c42001d8040324080c1c1c0142d000d010744103410390381d41070103280d81c0002c07a0035030202d102010384804480c60302d0f051181315144400b071001c155241d41c0011b41701178101d0141e00b1516920118650140300302801c81c4900c240027401444c2e4400c1c200380d400c10355400a0b03c01a80e95030411000080720b00c0000c84401d40d07e81012071401111f840c0c40c5081c0c1701f0114800d03004450300e07141e084480c101103400e4819120310324000b0103882c5181c88c5150090908141404a1300e0445213190138281040411402c1c10116403005c86081c0f401c000d0340300607103100b440850010b14444c000110442c0780240840c420301200c034151035040c82030f01c4100402094904210007001600f00b000000740c140584 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733007419 1250 733006169 733006181
    0x308120c03070c1415100815040f021212070f03080907030c0506091302041205150702060402150c010608030c0106090204180c0c080a02071505070215090111030c0d0908060705040504 80
    0x4071307412600315040114502c01c0380c0c1022a1007004405c010041008041e1082c4564446e85210185881142c03800c0d58810140f0500b424010340101c004450703c6c102048100700b07808094400c10251a100c0b0414039000300d1420b01c0800440028204a02041072548001f90007400d4a910221460302641003206000454114561050740186284000c580070301c150300c01000130300303840107128188040c0c0f820050f240c10f103100a1141511844820014416030201e0201c0d0407660440d1049400702012030744c4a41405020700c0001103518000002070304200c000018107124403841d00900c1243c2e41d0f2481101280514482c43d24061b51010074038000d41c00c65403100c01e03045c48900308604520000e446030030264220b0101140544e00c1000180822a40341000d15050003051503e580340031007a50104c6c1c14440340c0304015259100105204200344e00401b4400e81d000a0441166101d8040c01079491750307a0901c04120000c03400c181c5011582000c007081c40381c400e0b011030b16a42e1601d440d141c20f0000503d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733008669 1250 733007419 733007453
    0xa1104062c0910020304050f061f140a0806160f020d050d0e0109080f030601080a05090307031d030a05072d060e0102010b0603010905040c090c0f21060308120c03070c 73
    0x3d0015070100b00601c510146004900400c020480d841020400c0c0d4070300b4101401d0014400c03604030f060940d210304181c0c900140c1c0c07881c01e800d0040001c0c803000321b6807450b0b43e50002c2c1d02a00a0b9010411b042c002c0d4941c18480650301d644140081440000c00c3e03884541005129000135404c104020806049030400c1c50764120b1400005151392080c1c0b00e4000c10b8210b250918a5580000140062580d10a07800d075040181d0704002c0100c1d0421010b0290340340300e855402810700c41c903c040459001d0086c4034400780e007000601501c1114080d8034210b611500b040c0a842d0b0118020100300c01450f0b01c0c07108010780149c0251011440d20300309035081d82d8200c01c10f640d65045648a800c4031003140c0b1050003940c020000120046014140b91414119040b425001003090070300c2d101a540101e039000150960f1154142801508000c844c207400f070080700102e6074404424240715000040040da01c1c0180003102209410071100d448003602ca00c0f0521003510b403600082c88000c0101d021480340c10010007002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733009919 1250 733008669 733008673
    0x7060c09032a0b2110120f060506010302091e0a1806081b010203091908070605030a0b011706060706060b070b0619050a06110102120906010609080a0203060a0b0307080a1104062c09 79
    0x46c5e81d070500c0040303403105000456111803011186010480540070b0250002c909003402d504140e44840455485c0b14031780242c243c001d000710b03030b070502c1c030340f074000000c0c2c0034010300c200004181c800a039908028121031322410000344200c84200b00700d040080c20f4000804816405113240050540c20012070b0106d0386041c102d0ac5403640000a00c400c42008010010705454032855103a1030400310f0202114820064241404040e5602e08030b40d00310b00510561102080301e00c3c80c8c9802c55400c0940051180742c2200350041800103080c824000c0a40c2042c0c0319140031942c40d2010340000741040d103445400d108440e0000a800c0d800e200413802500400d40c0f1102b898001030600314040b041d50002001507551500540210006110540c0d000002e000074001040003009e541d189940484c1d9940c03001801e44172810b03038a4000c1c8203599001d00200c0d00600300da80480707030305412030300b418400000f140f90320500c10361401000141080351030701c500e051007008618146003048c40890250000d6030080c072841c014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733011169 1250 733009919 733009951
    0x10518060616030206010510021903080705071a0f0c070b010605030c0d1404110103020406090e0603010e16050a0e190c1e050304050706030e0307060c09032a0b21 71
    0x5442c841078503030814002d0b801030080d94509401d100d05613540d0f020010854100c445820041e112143c2c400d0110790b4103280505042d0f0b03a070b6a044440e80180d00005250354240340194084050200006015498440303160a082c0c50380044601e680c46050001003500c0d030740100401c40c00d4040d42c081c5130722207a200091840d0882c00003601c402c0300e405000c000d42c11105401400f080c050a80000f90301800282821490503050403c09058101103214865030070318000c0000c0c5143d2801c0d000208608511001c6402c60130440c01c00540591107070040c01d00907500c0e9100004e001d062200010301500a40c08201c01c11807900ca030020181c6a10300510041c000c0d4405541800c01386904041e071071689555443c1c0d00c90078140b400d00d09180c2c141d8000c03010142802d20456a00a002c41100c501a52194001502c0d454600c01a0390001ca04d50010b0000b410140f2120341180031070100e92084404000f00304003890703c030911602240181040355006500244020300c8401d40711603025004070130044180301d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733012419 1250 733011169 733011187
    0xc05013b0909030a020708010225020303070605160f18060c060e03030106030b03151620010501150f0903110f04020d111b0706211d1e060105180606 65
    0x260020595558020f0b80c00054041c6409505100100140400303070300962501d020120b207944104c138070042c4000d5107403500401404641e402c00442c1c030001d5105ca002e0041e841c02c500c18903107104207515103601142c0320034851100c280c42444100306080380c0c003030014012401c1c00400c5440b034080003008c44001c0d0384c0e101410b0780f0038420005140241415070300843d60315401c105060810702c034003c0b81011003074110240700711300c600d60040d1414240b507441c0c401807100c021810320740e80c0a1500018081c551034200040703075912010034000103620303564603020310415001600729100f1075180b0002d02400c40d054903c41720780c64680614105050014000741c280711104088208907080c0c4101440500d23800264030302c0c0c25400c010103e81800c01d000207030560924004002e042a402e107990f50f02040c142d02540490390410741d100000003d0107504c203032280364601c80300c1545c81b161a43c007561104190411002210030010380030303050351000b610051100c4940d2028200300070010700050f502c81c2080c014454 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733013669 1250 733012419 733012429
    0x30f0709051f080a141002070336180207060e0a03030e0d1205040f1b030309080c1e04020922290d0201140d090c05013b 53
    0x103040005000a40ca05088022209804250000e01095000458104211040481d441c02810b8000c0007080c10300344c008141074200308107010700b00c1c50325201081d460145948102a03402c10b04003010075501c80c049140c1622200e900300310083d100321040c04400d00032007401200d0151140e40c00c2c5409420b1103401e41e500c1054480f460309e0b050240e80104001424158103000c4e445d031190003d0040c0c1342103801030000420309042e16800d841843d88a8000c02c0811189500390403100da007001c080d0110031501d41c05035007006c0c943d01c8280e00040c1c0700e1344080f50b852804502c80710140001054052048c0210b01c41500b8000620111035001d0350030b01a65445e900c4070f20702ca09174502e80d0401e489034800f0b541d40100c1221151420b00340f5851035603240c558841e110080c003085c1503004448503041561140f00403101070f041645445542c1601140e1809881040d402c2b1030f1640d4812a0001030030343c0c42c0c200440d141400c95642815024203c609145c90b40d840c00c204114800d00b400721042d992020b400030136 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733014919 1250 733013669 733013683
    0x1802240c070905150f0d0305031308040e070e06190804021f0c1b140613150c02010801150507020909100632011d0303090d0b0402091302010f0e030f 65
    0x1a03103042d01c60040080307000c603550807020070a04c200c9068001c08400000302e00380105814000701806000408114291035200c14103682c6540800e25558a07a242c600d80400301c24141c590001044400d0039070b030f480e40b03400300c1613528103201c0c2d00c1d1a60100240040450355070a005c0d0040c1d8100352080e8801d40b8036074600400c451060090340702c16030010b80300d18007030403405e10207908581500e082a00a0107540c18004081e03507001ca0480701c0645800e5003d965001d8402160b00c4410054941303000c6421707007030700201d0004c402c0c1d0003601c2d00503181c0c1c2d03101200c1c1010b2612803034041c0021030401110340140b41c080740349500401070008440c50340391604048003c0303034107a410400d145012a00c0103030900003041e2200c008140f4a0806001d210b0b80d01001030070788620815030003a00114521160743ca1b0301c0400c240c0d00710303060003407005000000c2800d1000e41700070140c506900505a20000a104480c0c2c0540302c108194103a41c2e080082c0c0d10700d0011601088280c0300b40e03a140c0240001c1e4250404100704103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733016169 1250 733014919 733014929
    0x12031847070807080f010e040303020c06070f030b0906030703060e0a0519060c02010c0f050f070804090f0c0804080307120b190e06030a0c09020a0e0909010b03011802240c07 76
    0x34a9080c101404040c0404400030102c0d801c0040c0c03282003001c005244041d85044500c151491039494031186011360181c098106415140d209100404c400c1a41c404c118101c0d040040e1401c00150000390b09000d001102150480c2d010f41c00603008000161165111546000440040d0b031402116551001c3c200310300111b52154086001000d1406e01c04684145400b4402c140000c00903075a900324044d101c0c8648050102c00e10502140780f2050100d2441112516684007582907039031074940c0211070040c8000c4d2513a4015520b480305a20308180540d441c240141d80041c1d002e811036443e144100c03040461240718480d80c0b503ca002e40003560b100e5a90f89204180700f20095a030680c24440180d08048000700158400da0003040444d01155131409182c043e40c80c3ca11000d80d031503114850a4800c9441911015001642072040003a01d0030190b00c9203400b004210000e00184001c0c500763341308880d444101030340c8041c074501c44000d0356400f103035009601f02c40040824200540640030a080c680e03130703600c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733017419 1250 733016169 733016303
    0x3b030109020d0f0821160302030402010219150e0609070905010b04180605220515010905060706380d08090607060902030d0203090306180d051e07120318 67
    0x240514418240c2c0c48102e10f406e2072130110b00f1031400740c000035500d43c090b149104c9814a180400f40510400800076034000000d28028070170100f801e214240e403000110340e00881d40c0112400030405440a01500d41256100c810842c146800c1a0341d0001076804c41d000348101c140d0b16840050551500d500341004007256120307864548850041c4002a18401032a10520f951000c4051a9981c3c0040c40074013641c20a6070403940f106010b140c0100140740d100c1404003c901c49003040700503110034a940c003170514080300c0904a040c01c502c013804801e0801c0f54008065030000e1100c1030307150400d040501003c030300608010a03a4010b071303000300e0b086c01c040c5492140142c20000d07a4400300c1c102044010307003100551014040c07030603404001c00d842e03081d03103103c0d1010840c0000e80000410f40c40881c60928060b440540c56407565107291002018484030025001f2a06201c140480300c24088491441c80e13400c40c0200b1030740582d8541c039000240400800032200c0c1c000c0c100040c0c0c1340c0c040301c002044013082076003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733018669 1250 733017419 733017421
    0x615080606031b090a0204350d090909050a06050907180204060509060a0216030b090d050708071b030c0905190504020a03060e1203010306060806010b0708193b030109020d0f0821 78
    0x207130702e08107103c0201a0a015500271201c07642160707401044007003103c2c550240040c00312950318240382456007182c0023510003401c01c01802540c1340c0115020b0101c0c1c034054140f105c8a03000490716001da000703500c01c03007020490500843c046802d000004140140711403040e6590303020310041841042c00950000c2d107086a8100030030048103810003c4541244450074001d05254803a036500c007080c80b810800404500c6c03040346040c2001d44122050000c0c640c01004030103015202c0c20350f0b1005010440b220242103d40c0b860403c00348bd20b9215aa0003140c01038003900c8494207549842c006401a0035440c0b204d40f068090f80e0f00c00f03c04060245003e5441070602080e800e26000c56180740007010381042d034030030901b00711880005001000b10b03035800400060104091078103000a42e48440d02400ca445a00b40d00076001049040303200403c40a00c0050b0350781d689055040c1c060500b01d901f2081c00942160041111501103100200d0740e004d540e00c10f07805580341404413015001413403842c83c1502d41044c1010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733019919 1250 733018669 733018739
    0xd05011809020904080f0906030112050105070306030b040f170d0207050105060114070b04020402040b07030c02030d02030c2d03121b0f030613090615080606031b090a0204 75
    0x5480d0a4044610420038400551107400085026002400083c107501c0c0000b19086c1211303800301521400038005203481e84941c1d480d4121640c51504801c111915460320000400c0c035070292051105403500042c0322015541c590340e442601c101d0160041e54035401854045500b1440341c4000c1c02d00c0c08070f500e809a2a442649006429180058103d5041c0001d5a010440f0440c5e64015210800c2d00f0021003032003a02c0d41e0010400920423600540004440002d0400901d03800402c0d51907181c2c03082d03040307405800403484126228001c9a040b00c006800c00241004c800026280b10500380d241c0d4843c02c40b465800c5c110140c60356000300e00c0d6941c0c800d58501080b8031003078408640341507080d03403041407450051032030100240d500c0b00410307a501c980440b0040541e0744c2126841078150380d612003420003454a162200d200030345042e11030f4075128441c00c00054198180491a940d070b41e4040c1c840701840d001c01ca0100000c1940c020003a0442c59070a010000d01c90400702010030b04d000500d2081c2394003a1101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733021169 1250 733019919 733019939
    0x1106010b070201120e0c2214010e1305060a0906063b161b0204061712070206030a0b1c03030b0a0603090b07080c0c071d07110a030c0f080d0501 63
    0x104d40d01060480c41c08450420740312010070b240302031a0007142d0030103003102c1000c441014030303806030f002a072004c1c609072040e5160001c0c9540d03103050758440b42c904507039580e4219100c1c01118a07a10700400c213801007008941c40300c900360000102c1c00c0c0702d101c1c08144280c031400041440c4000d0204096002a451980c003040201c3e1203802b1041c01d00c03040381d0344507850a00340703135050074950350340740410084640c10151a28019000fa200d0140d4001d1060000caa0340e02c8030782034200618400380c0c43d54040c1c1040705540392415011a19100d40c0540046e0440d03913900d0444c0700400e1210b4159410183d071303d0641404020842c668103031503200382c8000520014070018014803010740c0d04850140b51904c40c02d81c3c003055240c07076000d0b406805494403510b03942d1030a40d032880d94051204401c505108501c000310342500f01c160351030a10101304060502c10303a00d4040c220361025807403411019942040b1012404a4030414031817807260f0141c80002100043c0c0d554420381b540c040b515030854251707614010701c040600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733022419 1250 733021169 733021187
    0xe01030e072403240e1b181207050d06050a0207020310020a0212040501120b011202040f15030513030c03020307020a09090b09010c120b031011130909080306010806011106010b070201 80
    0x10080f03c56080d001c820801c0c0460a21170041071a05260400090002c030218a07034032900b008040e240584850308000085007009a80c401144a611303007400032000440300007448022120f0041149240c1c034150b89800005002c007070b000c080354035001c101b40405618100b15050750749280075001603032144201002410030740c5c02003800405080401c41080715030303031003e5031401906289500160300a02000140c444242100d003c00000b40085000103007418203210340310441c0c0207022540c8270309d04010301c1102240e008039a0054810075803036628020a100310782d401074061190040340e1910205800198144545902a4840548881884081024440d1031580000341c0800900c080c07100018007804c228400c024060b080da5070b8480e100b00e2954100000c403a10034807078404000240303590005054030341c8050001030209030400c00000f4000311610400c08003030341005520381951264001100c0700800604294100a500c0040103a502018880d0500074500c162000d82c1d2078032144005003607100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733023669 1250 733022419 733022441
    0x1050105060306090a2703090f08071517180c0301110912030708030406140903040f090b300d020c0d03050702060c070603051008030306010e01030e072403 68
    0x4100001004a501d0703200580b41c1121080300c41013540da030b9040f40031004140c0380d501c10301c440d084807102d20151b040d81031081c0d94041c0260b032041c030f0060300c170444c0d0100207450384104405544110030401c103c8a8404815610f80c0003807811281d01180300040d0200f9100554150300c51102d90821364414640400460110030000d80c02445a140024030308142030040c941c0c4ac0d40070b046031511030365401c1e10605c11241555441244192281440d0920b40002d14114590700c110f845550b010a024400000503078040350410f2140000380d030b062650b01005450030303401094002c89142c1e0030310031100d40d000d204444140220360035504a401e551018aca8810300e001c18100755040008c070040591101c135520110f1542500b02a0780d01c0d030552020480e80c0c414084000d486d80255079010452381d5150300f204e0b0040818551035402c85403501500350316440705442c00b07400300d540901c803900d0a5000340c00040a01c06130300d0666072030310303619030b040350b00d844a0407002ea14081401e0545551550148200b5610300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733024919 1250 733023669 733023671
    0x91506090f050a0c140a020f100b1c08031501030216050a0b0c040b030a0b060c1606080a0e0c090402130c080f0f0402010903080d0204050a0806060a1e0902070f08120a0e01 75
    0x1d44a001e4010351601003005c2614a000558000d568002c10100285044503401c40e20818094004003000f815a800d038688209440c1c1c4e00d0000030140b5401008400d0f07002420300d403964603042c0403103000b0341c0f000100c1810302d0380030701460310000c0c171106c14209840d002e41c2c06032850b8445480d0807080114000e1100120007821320042c0306801001c07003500d51007183c1c8100003501451f1100091100d0280d80034000e128428100c4001d4211528003d080444030203403100303941500d46511500560344004059021503200c0001e4002c28a080001d1641140c0050501a0070000c03204040007030b00c19861580010881000a0000340e00e488a2410383c082c0240100e2441ca0030240c1c00200752a0182c4805014108003140760340d0781054640c1242c0007808000c0c100b59030b16a4500f40d03a900e40c24211052841400b1041c0d00141c8600c0404100d040c001c5011105148035040c03a80f15002500100d005640c203c103c100148002100180182401c0740760500e42c00f602e03d044402c0406944041048945903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733026169 1250 733024919 733024931
    0x602010515040504060b041b090b070f110a05060409060509011401080103030818190204050604060e011a2226070501081503070902031e040213091506090f050a 70
    0x65000d00850700d001240c200c2c0e0114840c1c07079504007400504000801e1a0b4068584040b03031140d2003060044400c48401c94407000c803640d41d90344c0040442e00942d000604a1064004280b00040c3d480300d00b11081c980007003024006c103442d00040381194002e0740210544554618062103245004940c00b401845001a04141e100200000a02e1068180f00c02010b03c80c0100102d00341d1682c0c0b28444200468080c00c840c441c400c08494002241c035a03410584c05540b4203000314049040c640902001d41d0407100d0340121907441c0c140d100e04401c024040401031354005108002034040d018212803a441050b00700043e00e80d0405040c001c5488000100541070644102078203484007000c01c05d102101c01c00d0908400b2641c510783c41c40c045c103040b280103076854041d00901044030085036000d540102082c980c554200d121960341c0314038916003a00c02a601460030000340000c005690001303104984602c40c005841c00c103504a002c262445031308588000350b00c5407600300c0892071905c503135039010400580500407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733027419 1250 733026169 733026181
    0x1803020f0f06010b19050403080f030402130b030c0f0d0812070f050c07051c050d17010f080703060507020102090d03080a230a0b12030703110c010509031b0a0f030302100606020105 79
    0x1445513404400d0325404041709411814010030543d0001e6400c18010355480140810606259000b1101284503820100900031082114441e0004158014008055004181040080201d0028005e69225207000142000241043c0103464009450f00c00c100040c02c003c0d40207404004a141c500042003c24840550200c10003d40e460880d001911740100003040c0f441040440d41040c00080c2462141c40c403590011742d4007041c01c07852810311690600c25039885100420254030284248410366000490030300c00f040a9070700007500041a0f000040ca00049800803401c840c16046094012480701001c00030742c81c4590141ca03c4e0040440300109440d00300340445d5100030300140c5030000c511750f40d010002803030711f5143c0060750b000303421000c483e110b40b02d03454001c24007000410040e4160044032140e04095010304152212001d00a01824013080d01e403e21100d00c82180d40d1a540c400d610110000e000072101c5010405180260b0282002c940406012000e441c3d8a51050782160725240800c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733028669 1250 733027419 733027439
    0xf0b060301060305060f1e01090f050102030f0904090f03050c060916142809140402240702060d05070f020604021c03140a03020912120d0f1803020f0f0601 68
    0x41994043d04000541e51988404121245204541284c210540340800c000d80c404401d250503003002d007642c86281598690207000401401440b8040c0507a0003440000e8001c0c1071440a010b0201001d040001d2103081e44d2a02e205015180d4019800303d1400100c5a04e0000c007032045039440510030005110180360801c01d1035900b07002d4400c09100009040c01240141d440300c1314641c0d803010848150181712000350f0030100b590b00c40d10840300c440e417a00b41d80301401040080810f2160340c0040c03400c2400544655680c20b0100f501c62840c607030490400000005954000c040e14541c0c2e42400001085d02c0c290034040d05200401d203a540c00e55001c1020000160340b2888082c0b45400c500d1542030300203502c8d01e001d80b8040b40c4003004415490004c18801d24840d855405001c0e041c1007201c8040b0821111005603489060403e08000d60308410000040085801d81100041244070b050000b12510000704040031a8840c0e9001c4005800c00d0050b009400c208100c1070320a810564003030038140d4500820a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733029919 1250 733028669 733028671
    0x105030d0c0201051908090705030109080d0c02030d0c090303080105031b060f09041d070b120402060714061003061a010c0f110d050a03020d050a17060f0406080a02040f0b0603 77
    0x40200240d240400046901c13807400d841c2100200c262481403d40c8400c406005000210f594213458071424000062624050103100c40880d004019246001c3c0d000c4e07661009400d0880c0d030102940300c00c0182c40903081d041d1045080b10040c2d661000a09800c0d4a001090300b241070344658841d902c141c00d98910384070600c1072402050301c00c0b80c1495854401c007083c01504c2c09412200f6034060325003441107051140c0b8407410010b40c52148103850100d904e55030420701c17500800d0600a40700e061034000074018100b00c40100080381c003030300d4848414100c600000345082d00031210311a80102250003003040050a0080140401782c000180c40c5071210540020520010f240e00908600b44405854007842000007400401102c050480c01c0c1291090904507070301d0f01e601800300d0052141031030301d100043c8540180e0b40c4c0602255101080c03150b041200004408001d0310040c0d02c421003864030001556076210f268000c080781c0020b00304140140c01000101c0d01e00706610b0307403120b0030000419201e030b54607006c42e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733031169 1250 733029919 733029943
    0x916051206210c0411040602100c030b0406030605061206010305150712050106180f061d0d020a0324110702040228020f120a17040c2c1806180f0a060c17010503 70
    0x4ac0c049400a045000c0c001008006800c54903020000c810320491b41c10540c4540c40c15540d081c080c110b1440c1c0f040c0c1e0b0304424071020380550003100310b03144000caa141442d42c00c88194a4100403901160181c0c0d801c442d400c1c1d1042001c151204003014080e046c070010350000785070a40d4021201881c5c03040107008a002002031481110313440d1400e0000d40ea45210b803100441d0041d1a0740b034001e449241030048010500300001408034000c40e09580a6010b001c1d083c0b60400e5000c8050500d0304940c02e10010b504140c00c510b0041e10b2200c041e80d4600c034042c0a05528980c0c5900501704a1706404101c1d044c140d44d02e0500f00181c2d410401016902c0d044111088007800c41e81e0541190f689038142200c440c0c2c00d58001c080d40b4198240d17003040d90030102251a084200c0d80885c484035880d803403400c10078000c10684091003604160009006080d0007040c60815104003001d5503641088a15a02c0c144007102e01c046841d03036650000c00440030391150f13a4088160060549030115410071000980e500c0d00b103000307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733032419 1250 733031169 733031171
    0x319020c15030c16052e020c0a030c020d0611191b021009030b0103080913090b0601030c020114010f080c0d03021b061b0601050916051206210c041104060210 69
    0x129203040010101c03451050303034205040e80c1603146074014044d0907080540d900b000301e000791040c0c041581b03124800c0f00c403c05103010040915003040c0d0750580b2102e01200081c0d902094543c0b10101003000b6000301000440707017500c82c41c3d88106032500c6c0132204410303005880421071041d00d6602484c0e000d104a804d030a40440301144002c0451034116007944164000070b24047c45040000304000d0301c04042c6c80c2c100c82c02c41e003980b180c1b6401e0005a00715024290302612281e6030340b02045565020b503011441d207040034800414040c81c1c11040344445a130070ba110325012144040104a030394024040242003000071120b0f01c1010000d0b4400035a036464640c80c4221012328140e180c0120f540fa0812501c81c68290380c0e00301780c10b010f8102415103c0e034091082e640905070040004401142d030314460b166280a0340c545d1070034840c1c84004100c042d00004d110580024503603001141c10004a2207a0444020040c000c11101569130180000e4070b500d29820700c00781000313000501520b6004030340d4114480000d50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733033669 1250 733032419 733032427
    0x114040518060d0519150209010807030905010e0d200c03030a030c05130303050c010c08070903081c1b090506041a0a02210a0201140f07051b0319020c15030c 69
    0x10010303040070003801c4001c0085c4203c00c500c0c0800d5500003165212507004011000460388003030350290692141824080c0000e40302e40020b079881c0d020f94400c1c1c0005001e0350000500500f001405840d10010920001c04520540494030000e9000402c05024525520207000f0012000d80465a82d0240c8411441030644814141d240329106001392290850500341c032500f840d50707900b4064165402005000c42a50800c1981c0c40c00700c0c020103116026034070507078828580034555110b914490700000f4040d031007c0c400300440ca0140c9a50b00988281e502071018010f50801f2401002d843c0074a250f11450050b80140000c10000da841e0154401110301c8800490350b5100c9858201e041c0031121048160181c240000d0041c3c01061802a1020410f00e03002000300c0c42172a6080020031204951f04a030302c560810004400c0f522880282120034000c104620302100301031007040c21600460004a410721078401c810540e20ba0400414240080550300250704042c1d42c004440c1503c0020442855548002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733034919 1250 733033669 733033681
    0x34170a020a0210050d140c031f03060504080910030507020606091e040804091a060a111516080c1602040b01021e070609080f0705010c110607030e0114040518 69
    0x4048007081990080c40c1d1400b40c4641c05018107103030001d0400100070361920800c0303030b0402d6403c12100e008214401aa0f0f08680d50090200391084507c0d1142005000d034820000c00544e00e4051a80507910a8003c591601802000c0c82040101030400008140c01d01051080c110303008200c090300180f043d19444030340da558040b2000020541242c03168442c0000c01044181325454025200384c4000c120140449000c0700004001806035542c55613202c2070801c694405103000d000110880c0c2d0805083c0c3e8031880200c003840075191001c48091240c02565820301c402c00b80e0040d005540801584986414400b03400702c6800902c0900100a02a075035520303a1805a1313000b004501c8113219a09010211070580041d201c0d01e56140e88581d101041518001144600340891a40c007c56078400080000070710b400011502c0c10b28a403020b962081c41c0c03c0307400d043c03612002d0092503850700035211040050420400101012044840301990800c144000c1c8580d1382c42054100d201b20040001003c107440728 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733036169 1250 733034919 733034923
    0x60c061a03030705011a04060303020319021e01091205070809090c250519080a0f090f03080c060a061a03090f0303240d0309090f090834170a02 63
    0x352140560500c0007150b00c0c820400150440041c44940051034002003100c035040c0015142d40307010081c0980c0040c40b400540464010300300200c000c42c6d03c1103c01d1906a80b899a034103d05882c0c0a0050b80d440301078541c1800000024801c621806282c440d280ca04180c4944402e8090354040903c2040008086121720346d810301952055034451024405014503403c080a82c502442002c0f9124000c00700350b41001028031041004075500300848034a8001065001c40b00c1c14035480c1440184903140001184010030110034a010f1481108900d03622000c042d00549450b00051501c65a181480f50600c60201e41c8001604031102d0144196100d40343c11400500b000c000035801040c40c4008800c00240074880030302002904000900d403d54900c00c0014058100f5210801602080380901c1c208261505684003691003945000c00241180290b0382d2030100e42c1c0140e00d12043c0118207c24412500c41903440b4002411a41d1049a0341d54110b548400c400c403107580c3c08032229400810404856402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733037419 1250 733036169 733036211
    0x1704180902130c030603062a05160c0b2a1e011d070608010b12071d090a021806090d06050718060206071b0c05090604020c010f0b0f0307060c06 63
    0x4001c000c1c0403004290b43c00600411052100380c0c0d0003401d180141e010300e008200658000c07003000c03044002440403840c1c1130b10307194401020700c142d020740c071000d02c804507032071402d814081c1141c0001b4580e904040108d03050f901812240c00d209004400e105261410400140c602c00d2030351a24030b80c0c0036170700074288060041401c603c43c2c0d005800c025070202c0040001050b000140e842e45d840d44c00859880d9070a0038001c1c042c884000b1240c0480c10013181185000d8400b020b80c502c601c116003074045034400c002c01c030f04c0070050301c1d01100c0e0740c0c0100b100800c1841511021010180070b9501030704220505001469036112a0f4020340b519640d4404100c2a40c49402d00c15840010001d40c58502540c0700002560b8090850f5484005031030003403c1810801d2080419030070982203050b5006817030402c000c00c075049002801455001c2e40c00c022a0003040028000c0c4900306085d081e00080b41c58a40082c0101c2c03456007a5520321a8204230300502c90283c2004c10b07000000d030804d100140038803008a6040140d07103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733038669 1250 733037419 733037449
    0x5090a02040902030a0b042f07140321070c0201050d05070504030f080406020c0a1811090d050717010501030b0f060402091e1f1202071104060e041704180902 69
    0x800013041140c0721072290400c004440e000d44041108429106a034240900c14110481101c40d56035041b01d045e41c0400050440035010f060b81034030000283d05014a10340c4503850100c03015407040c0540e500c2c4c40c9184080381e840082d5044c600c2001c10150300082003481040c3c003101245070344402007071000f841f6506880185600c01480320414a02e4144268143c00611500005204000e2606000d051452914084406186c61710100350741101210001e080c00108208415030b0038031080ea800d964a841c2024000d0007600500142c80c1024400442e0203081080032038a42e0420b07004000041c0ca042e4456404000c21035107500640341c040029000c1e101c0c03e10030680c086001c0d0b541044440401d0707041003001e4411900c1c0b562802000c00d03810a114010f02000c0007180c01201c80048015040c0c00401c1090710038103040c07003100c40181c000f80c111011030f004021318604d62803c000402c040300b550009449208a03010742400e203000f0003841d01d40c2c8402903080600f51180003035011502e81401d00e1480074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733039919 1250 733038669 733038671
    0xa06091230050301030c050303040f0e06030c040f0204060206090a030206071409150301180c0203180414010801060e07032d0212070e010e0103090206030c070c17151602060105090a020409 82
    0x3090000b00203400c280010345264aa1001c00641450000100c408403200040002d061760f2410a101700300c260004c040340e8040c0940c4110f80e038680d54078403c4001d1f600d0050801030301c0301e0078000028030b04040202200020ba10040300c2c0c5002ca82c000924580c01070141c50301c01c44507a02d020300000c1c5401180d45094010381c0d1a0400052003240e02c01860503260184021030103000c2401c0c2c0d400580e045a0302c0c600158104000204100e103140c1070360005620f0181020a030b050030203840c00d00545003603001d83c45a035950102800b50491248003940c0104007840e0501c000c10684080030a010b10001111864402020400300305036140d40503202003a0703450031028081d103081c41003d88102c0c880c1e201c460008000e650460384541c02403103040111900500164116680c98030200c0c01513106000542d400b10401c0c00010f11703a407288000309200250400902000350315032041c802c015001070131014003818145017031002542d0001d8400d045840451702102d0700e07101d155002c0020b10468205c46241 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733041169 1250 733039919 733040003
    0xd060509010212220b07020f0f0304080d0903120e1201180c050102030a08010e0901090b0901060e240f040b1e150306100e0f0604060e0a060912 63
    0x381019805025907500d0202a00c00c0f03940d401004080c40b14100d03422081c000d02d924580004500c019019641c80782d03a0780120352440344101886454040c0e0b21022a00e141c0c000a014400000c0034000c00ba0148464141080224256904d01c03039219441c005100402c1001b8411544980c0c1e05036002c0d002c1c8040400030821045400180300002201640566540c1c050000015065100000b00c4209a80c180e4401c1942c0c1d08101200103d594054550b040a6484840d50800302d420320348041e001d0642e4100004400e445c2c001e59016580000b01000e030050455407006170806000c00211502d0b240c01c0700c65403840c0c088103000a000b0b086c000c4890307400c10b1400710756440f8400e400b000700640c26004c0fa40310b800e074442000510903134413044031300740e0700070344403241d01c0606902035607030780008810040c900c015020100c40407403440d4005c0d80c44600052108241c0e02a0740c20244268000b0341000d281000b02107007089032159034282c03c52401407000c0c0c0404010003404080c0b40da540d00c0300a507040d6030004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733042419 1250 733041169 733041181
    0x1e28060b071401050606250c09050c0c21120a3b0a030903020d0c150f0f090f170a170a0801081c03020a050d050c04090608060615090d0605 61
    0xc440481e01c8100d60b650b1070440441d40d580340504c1562a01f8282400500c0b100e001420a180e0300307000b03890308840000000703c1c0410304940718003c0303611440d0818141c5441d0300c8440c0b00302e40350507406030300c0a09c20f00b620700c4a000307280b03a103100f1070f1028213000c105c280307007504c0740c040701130041401120650b81c0842e41102500c203602203021410a207414810550800441003404036281d80b8010402004210022010001810104440320117a030113801e00d0120a5a2003502001200002d80c070f180014020142c034006060300711181d400908414503086159509003504450f02411502442c0c1121000b030792040920503040104030b06041c0e001c0404046414aa0070496942d000a445c400108a032031001194a0100044254841807000d910680c10018680c0c25070007503100b0341560b410423004004503103e031900707800f0750b50040c41c2c1196002e136940d00d00b40100084800da9080707e145900036170280082c99440581400902e03101c4011a551172001c0e00000f84008002034008100500388004c02c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733043669 1250 733042419 733042433
    0x1060f0602010c1706010e0d0b0a051e042307050a030b060f12120a0e03190201030c03022d0712090306060611102c061e28060b07 57
    0x100ca03041e40003448000c41e8814213441c2c0301e0020644100104480c00000c4c000d40c8540c26032004001d0141400200c800d03940c0302c512028208072440c00b10700b51036505100340c0004040034013000c07034800300700000a030400340e4940c4001050f030340c0e111a444400468112410105005800c0207000040c0032146455403840c080c035070407800710361061040741d60390041d40351401d20b201c881e100a803906028090400f09410110090f0b0084408036081000005520a0707a450420441310340c0b60b80389503600480b00380b520004041d50b6610343c00904060050058041780e0b026404030a00240b031000d410784d9500d81ca051180514010228060655100144481d80054120200e102680c3c0101740601c1410b031255016200704c0d0a40000d200541e104a41d0020020710035440a02086040740758120b40142c0c1660010011440141c040840c2c2c00c89802d0100100074403491584642d0512040034542c82e012444816882403074250210084400c0d00190404130a913102d000a0205010031503141c00450810034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733044919 1250 733043669 733043699
    0x50a0807090e1c2d030f0f1802090402060c011d070e0f04062c010e0709050c0301032913060c0804020f060a02010605060a030b100804052a030106 64
    0x41c180d146414a03411551602084200d0004001c4031498a40e88041c2d50481e00d4140b80e07031280354249030840c80c0e00951104006070140100f01640d01040520b1005c4803c1b04442c9111220003c05d03240880e03191610030440e010214135901100c80340340030760f0f450001c40c00301d204030b502480c0d02c2e518002c80c0007130345c49900c50120000028002260b0010741c0b1048002514141518000250701c001800100025019081100c180703925042c1c9080740c5034600c0034408100c48070070000d4030750f0351149160020781f00204100e9000341510070060006040c40c0b15624050303c41070001819912003001407150f00048888a207c12401221541400c0c3c82d028000c40030303104100030200c91071401c1c90004c844181c4185a4980902d4000b0b140090185031002040116840501401c2c150354071528009400d6444c10094400d07610142c0300803580740100707000c2004c41d000e0212140e084c0b000f440c081c000400c100181050406010040c0c04484410b01450910041c09000b103c3e541503080100c08206103846412007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733046169 1250 733044919 733044929
    0x122808010e1810020702030a0c0303051809060a03080702240a200601062a0602130e04050a0809040b060706150503012a03090b090601030b07080603060402090709050a0807 75
    0x1169580c0382c0140800355038801c9190140035900282264015014a40c000c00059100900315402e425240c1da0b00021000310b03900a5000c00da0108003c51003000307031011400a40021100b4a82c80c0c42d1810002c3c2e685500350101030103032000420b6030421911160304101000e502104d6010500400300d450080d00d5000300190300002d1491103800042119640c003103200c106904001c3c080300e07802c042046500320324043e4000759400458181001c101c0600401a5200b800f070180035079140d81c0e05a0350004c04e1000d5204020f840d04990401c4003041c0c0108541700402d0b0310900403507aa105140004000d05140103115501900c000b0b048410080076070700c0b481d01224180c903090381890792841054221070350801201c003881020101c078045410009520645c0540c80d050024908007a0b4070b038000030103400c451851540c0d10100044c8180203002c2c0803a5841815485c103820140350650200380c5544002e04000d000341c2942d80480c14480c00707145482c000d080c0180c440c0d00425a11000556150194454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733047419 1250 733046169 733046189
    0x40c03020310020c0a0308060102070f120606050a15081f230901060f0c051c0f0206060a030c0311012a03030b10080103200d0b010302040b040e12280801 67
    0x14850700102c49000b42c545410300f0101810080215031025a0320b040b0040c8a18114004c0c0100810311240e5102c0d240054607010101d00d590f44294a0003c0403a100c0350043e500c248440e800c10403018010300100d00e0101c06078984030605480d1101c002811810130188894180b400e0000401c0031141134003104501c40b03080201c2d4500420b20418859016401e020b5070380014064000c40c61110301441000038003034415801c54041d100c4055440f0580741080104070300084495407550101c0e94100640d9070403480490301240325501d1665018401021840011300034503902d600c0c80060782c010000b0540c050600d0900e078945891144202c81d40202d070601c110080f0789860815030150921018459130300a8035203950510b6405c40d140c004804901c2080349460780046240803d243d16581c810f00082c82c803610710040c4a504610420080e100000301c5c42c0d0255240840e0b1100003003000a8120794401440c0541d940d8855080d03e8088207240c0d10f88200b298114404498076040e40100018100c0b0031000b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733048669 1250 733047419 733047433
    0x5100c0804030e0f01120902061b0a0c0e01060504171f020d180803070806120f071a0313030f1701030c050901061412062701080705030a08030a150e040c030203 70
    0x4100b000741080d84c0685400100e0070070500161410f150300c09208140014101d9051801450080d9a980200b13001c070080f54100c1d8003002c042000c2840200c020304050b6001150540c10a040281540524403030712045140808003100e4400e01403110041080c0d00d40702c51540c0c0c0e82c402038410701951141001080310340c40c1c84040103a9a0302d600501203c190b01c450f409186454007641200c4061003d4006544589240f66032405208100815944030f08a200981509460101000032000180341b91083c401003c0040145445107000b0b20a100366040c10031042200c1c02d400102d4082103022440d02501342c14200100c28801521411000c4500c01c403a40540c0f130703807500412070b48803603440e50449100405000c5600400f15042c0c035541c0c005c07000b40c0080000ca904c0405000400c4030948044440401040180b1220b641482004040d200660040c41304035040c6d40c0341c50742d13844010411545030350f46021514104c1c0d205980c800c02441c103204072000c1e606040c02c0481c0509007903c012442031280340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733049919 1250 733048669 733048697
    0x120304061b081f030c05060c0f071e050a0315090516030c0801050c1c020a0e0d11101103072003030a080f130804050d0222060305120c120705100c080403 67
    0x42c40e00350030380350305c948a096170516140034440c068110304500d10480c0101e0750031295801042242c200103106000880241e0f800c520024000404140c0000340a09096007091000c00c580c0a012100941c5420f0002110b504504102d03050000801402c9041504140e00205120780c3d014154107503031443c0000c118039113a4440e00d6800744600382c905501d0305100c0c1501d80c2015000d034003801c1d20300027070705001e010b240880c0d000401d400014607085851182c1c400f114142c0381040307804a08140881d00b0030404540100c01441d680e07021340c2000030728810030101e01d4000c020020098a44000c8054103d80d11121145005000c2d01c904440d4034a20380003610028259182100004221681102031589400d00301014884942d25520069800c6003d01c40356400620300c03501c0707200300054580400241c16007146012400d18501c607941c501b080000303118084034030764040790280b003d081480b0070300c0d034481c0b451420505104411503c001c5440c9040c2c84107910b00c2d00b00034814407a503c82e6484050442c404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733051169 1250 733049919 733049971
    0x220614030c010f0e0a0e0f0906060310020a0e0907050a110309010e040c05090a08030d0e12030105010f09030f03091a0a1211070f12021608120304061b08 67
    0x4011180d040c0e0200c0401c14440d4001d81c1104010086854500b18502a85010441d5281264840740e2200060420031650203926000107401120040240c01c8905124000949d650008180c0812403a40040c61003a4030b03003c1c0741c104800354000742c80510b4910f00400e001d0441c0e0460749080c008550414141c814005c1c0c08402c807841c4001c144c48006180f884441030100520a140d034400902c4010080011140d8551010b00300034a081001140c3e1489507540c1001902c241d09005000d80d440b402a0001d540101c1c0140e80c1074500038600407021001c201c008a40b5000c8aa0010f40f1004000300c100060543c8103c1c414180c4240c0380020100643e1800721039014450504040002041c40c0c1401840486235042807991089034001f40d0308103840d640b0703a84030792180fa000031030f1540401c030304003180d00303070140802042c104144111581840ca0038840f980ca814143d0398841c500200000001c003000139541c4808078030300b91000c004034003403800d00025161742002d070b540c030280c0048203000403048106 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733052419 1250 733051169 733051199
    0x212030304031b03020d080414030712020d02120d09110909012f271201020403110108010b120c07060e0105090c09220213111309060608071b022206 65
    0x10580c020507446c1180d81084074102d0300981300320fa414805054130142d0f50380403c003814055016018815250540742c1c000b914003505c680c1410150341001010301c0740b40f80100300791070414448071800f05014406107400040e0752040503110380d02240c41014000004d90540c840422812161400c1516104001840070300c0c0c0e0203076100100042d410040e107000c4800d6520160240e00d01c60540480e41c051860000301403550705000710420313030740c0464100305200440c20f01c13028040c3c0c00e08005555504105075a1036510446941c241149c402c000071841110089084654941e0001010003860b1706910030503010341001d0310100d44d07510071042e001d1040e160510140b40101101c18a580e40d02e121041c428082c02011601641e12171413000018078510041c2c00341c800301d059040b03a41580e80301d8030700b005190050684c0000b40300e646071131028000640c01002040d000388450528404c07205030f8828050b006914290000e4020ba02e0326011805004c0e43c1e0300c5010400708800703003441185e4885d00d0304104490 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733053669 1250 733052419 733052423
    0x150705060903030f070c1a072106080a03140f120402091b0301090c1e0302040e0109020403020105040302061b0115061d2808070e0a0605010f080a0b0d0212030304031b 73
    0x1410310017241c10580200c0c2c44500f0503101d44001c410340008007c943d1a0b01108656000c0400c120900201a43e20020381f11078010b412007508220290030800301d5135442405000c000e0900c00c0807000350015030500340c140d6140c5040b15204581d9054144200d8400e0141aa0128000c404e0080400c0301c00e01403240040c0e00728000a40c036825a031814003450068140c2043c1c03541032092a001116150444452990511100e903d000d039807245030500300c150401c81640305440e62481400b013880180e034410704072001c0340d070101d80040e2100c507500118251801d041081d694158604010240e003d0781014681d022914941c40302410f4802500e0050140035602200581c4003c000c1e403803d40b040d88204103419a11500d9400081142d15a03440500c0c021082e00001c4140d1a00001c10507140c03042c0c001c3d140601020306e0030314000926080007500000c00036100c062140d40b240340400458507000c1c8440b00381038008090709075041c80c108040703031a940282d80680000d406042a00581d0b00075481c280817444e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733054919 1250 733053669 733053691
    0x6090e0604020a1403270a05060c03040c060302033301090b04050312181e03161508181203190b010c0f210e030d09060c030c050a0215070506090303 65
    0x1d02c0c00d0542e804036a00082c11850b01a16070006c4800c0c8003d0b142407484a81000d40080088820a041071849e010000b4443c40c141d001c1041040006564520002c0840d145800d0247e102d44030502216040d2540c1041500145480f03075203094285201e200b00c112440003070702d842000ca074685100c420035100300d024641d01076100c2e11794100c0b540380c260700034104001180601d601c1c0340c060000064250103036034a0040010154405080c1d18502840314080b00c400c0c0b141201c80003440c2005600c0748207c0380038440c040c86031600004441c510000865951101003209079460b010028a000c4110782042c2e40107a010340c2f000000b0f4031142c11a00c920b41a4040c142c60300b066039011135480340011403d0103002c44041500346d05110b2071000c00c00c0c0b2400d0b4920075445100b0340f25190340c2458078041a47d1400ca0401400318020099160005807440e14103801d8504054994254101035250650840d0700940040200111080c4032a070b42c0c01800349280301d10242d80301c030303107545600d20790f21301040d1185030f600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733056169 1250 733054919 733054937
    0x908032d01140d02061e0403060e03130e1003140f070b04210606030203060a05010311011707050c030f03010608041205030c0307080a0e010507030509010c0810090518060106090e0604020a 82
    0x3881c0a9030f00c0c00d8011320003428240707002d080720500450b00c80e40300300240d020369001ca0184100b000c01d014a90304020f15600550404110075400102c5c0055172058044030300035000840e4030710041d075010201450300082d0701c0850f02d002e8600140d491404024280a03400b842c1008a980c003028412642180c0c40307989808041460302c400401564518101214000e0f40e5980c0040162024010580702c1c101d045400030345585141841051030b4212a01981000005000b054605034030041060f00300700a45006600c0c0c0c1c0e181d520140c03551103840a40d0041c02030110000841e503a22020381c0f449075110b051151000780c6001d1090b619804240d62016040700280002482c0728881c101169104904090200745074420403403440c2103450581e40c000009490343c0400c42504030034007900e5540c102e2454200764034030307200960000030881ea01461002c60746038804102c80821601d400c4c910200306030240d60341569250800392500d5650710070442d0101a5500041c4a840d00d4403d403548050f45496140f41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733057419 1250 733056169 733056209
    0xe090a120203040f0f060f11060f0a0b0901091b020703111003140f180c0612040602091c0b0a0501052101020c030d0204170703080a080a0908032d01 65
    0xc1603030803081400440c40180000180000d01c0300f041c0700144544646810140d0419800421b00c03c08454540c0c03e010704101d1500300c1e45000902d40350301081182054010b1345403201d80c9805451030f40c03a415440aa0720700045507100603640200320200070400741c42e440b190030710001d80e140c0c1c81a02c009082c4074486180d503019400c00c0e035009000b10304079203800110703d45c030030182c1c0800540036100c0c1e030003140c100c90420030a0110802c00d500601e84079002006c401030084001b500520803400403011084205011074100a841e4040d81d44400000300f550041d2990f0141408254405031015102080d0707040115650256078840c1c541629405002084120107032101c0a0303003006000d1074401c0e19942000054940380d07050000e40906d0900900169559180903021490410350410442c07103900940030800c000780d00c403c200c45003d84a400c11440b03d070380d0005c190005018082c00a4600100003080180103600451030364450740000468203c050b4041c07003030140e091824010a04910700d04444c00c07913 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733058669 1250 733057419 733057433
    0x9060f0c080f1308070210020309042a18050907020616030b0109061b051605040b15040e040602040902040b03090f06070206060411130303090503060a11071106070f03080702070e090a 80
    0x2102e4052044640f5081700c03030740030441c40c03010501030380d0040e0408242c0b0140c5161602a41800d1400d603140f01503a0f20b62040707800341030031441ca456014400070b0310f400032030400c1a0b07039403c0041c07034000c02d6802c080c509260b0203074450034116a01d4400c1441000e02c01c43d15070091180c0a2002e1040e5604107019003014819540c110101c2116564141548a0301000810400c240e54502c40c030f40d90001111741c5410305120550f042c01100303511448240d03214a215810b26002c2c0c034110317800040c801446840701c1c10154024466a013019036413500000307010440d10003010055008a50394011101c184698807141625a04151402070058200740041140d0f49055044019101188640c0d00c0c40c000e41c0c0c44100200046551084010811801041015240c10310066034429070140c4140028066070f00b03c0c3c800e52080200041140c01c10010064403030b01c41e14151502c01e036020195030450000c2e0b08001c1e2000300111054401445070b90408640150702402d001e000340700900060040d1440e17599014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733059919 1250 733058669 733058701
    0x70b0a031d0d0207080105090303060603041406010807050a080c01120c030605180f011d0c07080903100605040b0a3804150f03020a0203070f0c0909060f0c080f 70
    0x208240e211510020100303141c4503145251000d640061540822541e006820540c0c180e0107400180d02d000708100303074110048110b0780d110104843d0590b42e070303849203030114411984420059983c0326040010411200000e0200706480017214008620740ea146d524a658098815155001400c05001c2408a04040d0400d0220304040d05011036280d4a80000c240b41417030140706c1d00d88115065040c06800700c28415194054008d0039030148c440850b0074030300c0341c22880c09043d95036400400078048050003682c0050380c15a00b0010152054400c1a02c05180500f4480c01030510a61601a0146480c0f60442d0780d0422210348c00c810600b0f02d01c114001d41d00d14031800508030102186101a07980340003614000f8005811940341c50380340722f241c0c03401c01061003400354443c4090600c100196102e140e00002901c3e80c4070b511910f01243c0e01c03c64603100783d901900c7c2d0301c5010181c0c100701c0a24100003280e0003441581c0c00d942070410050000342c0c2c0864440d40103440c030000c03c001040209014060b090540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733061169 1250 733059919 733059937
    0xc0308070e03010c030902040f0e0714060403060501090b030c1f0c021306030308071805060712090b030c04080c03010908030c030c040e040f020f0907050307031a03100c20070b 77
    0x180c44862040d00100f0f00b991200b0815000180d56000b101c0c086141c90700c41c0284080d4007820810807c2c05001c0300c560384e41204d000e004400403400d0450442561040d0440d000f070f41d400b200038040c0e0359403454002d0103401d03040d40085c072030302480d01303025160308002c0303a00208000c45602608121b64103003816207040140050998105040000710900c44200e4064075000794030030b5031601010314010000610481d4414540f5000c1701c00da4404102a81c1c944003a43c0360320b9006000c90799a0042c5420945002450350b02c03011460a0100402052000034400b07001200d1110701699400d034070303407020903007201c21540c4000c06440c02800452a1410460051684481a43c40c1e5a02d0262215801500e0007070440e8101c4151200d0010b4074114100165244050f00c41a1a03280c020f0a00241c003400710302004200000701540e481c1049141e0719281c1c07000d1188500901502c001078007c104c01070144c100c200030440890104440010002d01c0d1075a01c00c840b2505801a01010342003000080c1c440d8841010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733062419 1250 733061169 733061177
    0x270c27090e060402130204030f0213020d050405031308030c0613030c2a05040207051f06050a15030606050a12051e09010614030a0f0f0512030703020c0c04020a0c030807 74
    0x102050364400d9109146403012090001d00c010318141c410440061217282c1103030041030040c8000c100040120f4807062940342d0480d110704c407281565028500900903c088079200d603080001307020510101000608410800d403c007600c0d420385070710f0819982d2160405158450f0b01480001d20b0706122111001a400d120b407a007464054410345031401000b1541c4c0183c449008070400300104c0c214002605001003405407810341c00c103920f58454544550200100d5a400307050707241e501d101c04e62642d015801424004140500190300e400b0640c0180002d07a444001003071515202040543c02001a96107500655803101c031200702c04604c070405058040c2007229149071760186425000c00c04041188954242c6000003a4685040040d6040079080d0750007901030741040088002207407a21464450072600070f9540302200c11140f503c10714264010464690320500441031144003036040d00240030750448141210141c0c0d83c4002000100d200d2003911101040d003404107180041e0141004aa0018860030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733063669 1250 733062419 733062497
    0x90c0b0a020319020d091508040201080405070b07050c0405101a07061e2f1b0a0b090d0f0e011e2a03090b09090103020d06020f04270c 59
    0x1404450b02082050700c407003d03821141888054a80c4400c90030000d04600004600c41f40c0343c1c6d400504445405000a4100000c00e00080c080c80000c1200000030300d41400305540e90f042604041d521207006408041c8600d061801043c1c200c64410440d03c107558410045814440100340086044ea10404046811039100d18103019411540c0c60342034000280280d0104401c01035800074108080041c0069440351a02c0f4001c003ca003c1075000d44001520251902108030300008480749006400c00000340007001c528100719803240c020441035409805901c07020805036220b5801e44e01032000034074a600203082400c1241c5c6c00c00001c1c001d8521140d60f81403a2481c0b011003c030310000034000302e5803030400402c0b40e0094010507a10030485401840401901c0307017810510700020360904410710000c1c0c40b507111144a5410b00925504448131740144204281d41c2ea03a03207401c02001403031000800301c8400b018502154040b4a01d000300b01e482040f60b915211440d00304070039000c620f00d081c558110302e039071040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733064919 1250 733063669 733063687
    0x504050906061c0f1b0920031302010302070f0f141911010c02030a03110c0301062105031b1c0c050709110705061e0702071a18032b03090c0b0a0203 65
    0x4200d00324104a8546020001e07410071801b08280c50180030b02c002200c10702e101d0400326660341810340e6009011310346c40c03024510351030004070060300801c140036103200c2505130f1400030000424030b0280780902c1400e007840c81e0090042802d4843e0144517030748040220544031640015a039094a15006805040c004c102d08070703540200e8640281e203403049010448110f80c4e5041c4480402c110030b66131004030000d000071404c042041380c440c1e036a200031103007101480c108203041101c01c3c0259441d16806000781d203d008810f44080c2d85e202c400701c22140c04901303450243c0d40348078451181c90090030303003141c024402c3c64a404140d00c001d04041d004098200403c2c042a00014803d03c6054003911002031014000140380d02d4440503402c002c1d0949082d9032090604001000c081d429009001d844500000c1d12003092540030b030114288801e440360b00d40a19910088090b000314078030605c241c02d48040c0400440054800d5044482e180340c0901450001c84c401c1007841c00c2c0740001d104036005841aa0708040b111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733066169 1250 733064919 733064933
    0x20f04031a040c03030c0c21060b0a05011b0c0b0c0714010804021c0606051c02040b0a0609030b0903071e11040e0c0621180d08041e020109080706090504050906061c0f 73
    0x12050140790b08c16900300401405414056a503102604032481040c103480e00c80040d090702040900a265418499081c0003070004000f14a8003e12080140c00d41d00d1503141d100580302d0501c0e00600f0290541d03410083e03100d5115491b254420b40d4060248000a40b01030400d0b454114003800480e40e860f10380601241030348901c031400a21841d0210303c05034030300c080e01c108002e49407000c03003882c09050414810005664060381140c201c940281400225071141c4880e1403c501c20784001030130b04035402c12601041e540303104111034094000e809800c1c9a804a00c1040f09880745d042000195603c1a507192a151504000901802990000198840790802c890111035001112041d01011207950f011101c164180107035400d00541d80f61000e07880c9481c0d81c44e07001400094a4541c00403002c2070007002103900401d08003000e0880b9104030780700160341e00e00042c0380c084240142c44c021800e01c0c01203039980b20001103083c0100c400500600d02d4000a041100c21601c00c3c1d8016a000d11900c0c0117600840c5c24 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733067419 1250 733066169 733066199
    0x170c130f18060905040f02010503091903051207090b09010e0f0915030f010c081b070f140f030f160309030605010f060e060c0d050c010f020f04031a040c03030c0c 71
    0x1c1003100d010000080071520201c07101940903601080c1050100000200f03030501d884c030030550900304a038598841c481d5442c40d0503030402c08821807802c1124240305054001004c0c0000a800b80858442c964405c04115075500c80e5100e801140507050005103495070007580d0340340c10f210f00034205d020200c0c01e2600060701c848090f036880d510350900300340340324050600b480704112000d88a0028004036649035402400b0703400003050207032121265002c1c0204541103508884000b600044500c3e58082c840c200b000d1007441c0c18075a50001d21500c1c40c401d81000b00801a80c2080465540041c100059804041c20401c0040380031020094481804000a441881075a010700b00312a4200d80745420b010025001000000342c1d6442024180005a104040090413404103085898410b495a258400d8580541003542c0c960066a00100d4204082c074015030240044038051610007002e07100300000d0f151401420381d0054005c0518640a1011901455110340058801c09840349030560392032074001030700c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733068669 1250 733067419 733067429
    0x1002011509090b0c180402090414040615290c010608031c0b01080108030a030e0c2d12100203090712060b15130302040f0603050105010b03010f06170c130f 68
    0xb56407410981441a6525099448054030301610315001000c045125007074095007441c1d1080b07800081100054859821080080c08000c0440b1454201458054064100c3c1c0c038025000100c00000010702031160b280c031101c070001e4001003c012845441070502c07681c0c07010080b0710241d9258000007405000030002000c01882d84508540e140c501d89800c02c05031001040654100071003400180042c10001c4201c403406070303003030030002644640c030030009040c03034000c0c0e13080f035809240042c3c901100085200315910132071030103c03880c0c0110f070140c042200e145a120404030041c2c1c42202900d02c001d0440d0b0066402825580c12900001e660320150b040803030703200700111402601c031402c840703840c209014910000e4001001140c1042000c4e0510110030940d03100281c400c41c1c0307071444080120400d9018102658101000740155078541c3c1481b03a00764000e216510100030b1000d0000365040c4610200c4c00b1654440d003125801da1242600d500e001d801c225511103a06440700c0000440c2c5c4d01ca2544580200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733069919 1250 733068669 733068671
    0x212070906120c050d0302070b0d020d0e01020a08040f0c09020f09090a060b09010c0804050405131202010b0d03080a1508070501020d110604030503090708031204060b0d0201020c1002011509 83
    0x50500341050240c03040c95000350381c1903040c010403a000400c1da280720300694a0a071a440e8880080c2e04089280c4001135101034003035500001c101d04846481c0d0001c00010580020078440c5403071550001d4200d200c0c04010800040601000c18000f506041c2d00703580043c09503c43c0c0e94020380301c580c0340b8120707800198440303080680003e02e030100b4200b21681c558800740c0f91500300012441e001194080d8801d48181a0402020100420030080c980061341d0140c41d02800411141ca40071200c40748540e9480801c1e80d00203402449541000e00c140150541d61201421075030040c0c0b042e6400b84d03001da002402c03901d0380329165900350150450000d4103200400f0f9940c000c1448524040019060004010221003001801c1c00d40c04514640000c0c40c0b90800d0349444c1c840c0e81d0360342d41c10702c043c14182541c1110955000005c0d101c4403606680f01d146024500604082041800c203104200701d100d4181e0b0000c3c05600030b131040c07400e1441e0080190045d52818000410298501a0107041005194204a00d85 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733071169 1250 733069919 733069933
    0x506071e0e0a03080d0e0f0a06110c0d0309060f05070305160207140d050f0f030307090509061305070306120803041a060102100905030d1118040c1215030212 69
    0x40c024188040c02000e0034030006030030360600481c03800d42141c00302500203100000c1000c1300d19101d520150b0782e50b4840007514012400c0d80141a1160302080040e10500d0030a0134280340020340b0000c840400b8211401003485800c1c51209501500e00c000b42542c0c5507580f00801000b220302401802e104c0d1000d55000a01031600d4a0300500b59190070081c041103511a9406000001000c030840c0d8004008460280000e400b40c5022b91624400340460b04540c001c0c0b080d001c0c0f14550010184d800b401c0f1a0b03e0704402c268507070083c001c82003421a419648100e440070f540b0890809230f0302241d001441d500d404107185488010348501c0004c90002217800e118000304000500603c40c1e000c2250a01e480d140c0109420041c000039a1500804040c4161594030803480c070400c54100101e0b01d86d15a4980c00380026058900700d40340b550041c030641c40400d1000010202c00d490300f4403c50b00304030b0352515494090504d241c17642c0000c020040b03110300220034512000c005681c0e12100c0702c08094075a4010025 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733072419 1250 733071169 733071197
    0xb1801020706050a09030303090809060703020d0e011b02131b0f14042702070c06080a1805030d18062a0e0906090c19051e12010e090a050607 62
    0x141c03440341e5000104100c01030002c48000c40c0c1c0000e000080343c2c0c151902041c200c40e541042046403080450082e0b200d070000503203008240d00070801d055031016580311029030700d03908001900c4c4850303c03031200505800e8540700340006281c101c030750300740201103100009540c17030060500b0394443d46511382c02c1c00810703004021541010340c0544946203080c0d0240c0b85a0516103840681200581e180318036184040009102d03400b41e5100f039040e683c8140c0c00400c9a180d42d5034a0f0005090740000350741681c035560803c1c200d1003040342d02500c41148280d005005524124500e01c0040003000704496600d5200c0700005400003003441401511080140500b0704110200e03161442103098001c0b2240c42c06021030758113000c4a50f92081c5a195024000b6a09058a5680e65264003213a00c10b0811001040c80040d5140002d598030030007800d41070405074000414040c0c03d03c1c01e4007041c004c4095240400c1040303030051000304443c5070125000417401c411940100305543d1601e040603011a44503000921405001c0c40d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733073669 1250 733072419 733072423
    0xc07020a0b030a15030b041e0602030f1509091c020f16090b100206060910080604030f09080705090103021003090b041a25030507091203170702030a09090e070b180102 73
    0x4807554011110303c11503817031a6101e80c603c4500800140580d00c0401500000b0710304060030880b00c0f82d020008665910b02a800502517440c1510480729050240040e11468200343c41c0e032a00605841d801400c004084448030140b031860b12240000314029a10301c0d01541d10104190303030203481d46110741002d003400d000d2000101d503400e204a6100f22100807625803d1038000c5501c94104c0310540781c00390141d61380403060500000326408003e0324803c2000f000140340c1d1000c0900001d83e010707505c240d0317003d80c0c4980c159a075244038022560301035000c900400c010320709616030310f02600386130502255850716625010110107040741d003512180e503040800520845030305030180c0d00c441d82c5040300e4000480488140010026803410f00281980d40c0003107029540102008030051409118020002e4800c2c5001002507640702443e2240440282c0030a075100e00100580d105e6203410350b10041010315003a88600942000008580c0d180180040442c920601034020160810101c502141e040c0740900024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733074919 1250 733073669 733073681
    0x609060a0209060d0c05070b0f04030e03060105012115180c030c050a080a0b040f020903011b1b1401110913050601051c110a09060215070807080c07020a0b030a 70
    0x100d0300510401c220302c80c5507624000e444442c80608000641c034900314805840701d02c00c4c154007030f0400401d0800c0106100b420900355100700d200b5070320b0f0b03907600d140d0506042d5100400e004a0303001c10281070070100c424521171401503c06500746400f050003440c0e050b44044075034407900706501c00860100d40c0b1208543d00c1c0034004462405280820840854040040c4a0700440d1002c1d410044d9810208804c0302d0140c0080200400080041200c3c1c0611350300e00000350b000c030030314900950814158821040401c02c2d4500c005c01903441e04148800044882172012200650403105142c2d04110b450054209214083c0401441a00940e860007134104220301c2d220941c480002e05d50901c4200031260745c0c01402e44600261458041c8204050b001c50314014003605503a400d0030400200c0c08007241d903800002501103a08640a03204064001d041c50308440108444040102e0100804100c44034400c855481e44100001c841c2c0e420f00c42c0c1540020750b900c2007a80001441038012003030000d0144988105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733076169 1250 733074919 733074931
    0x3030f07021c030e1816030b04020c010606030b04240923100303170603100c0c0b10141008040b060d021c0501050901090f0803090c0904140d0c0201052704020705060906 74
    0x17044051901c000c100e0040f81c00c40c0725640c1050748810600d481500c1e240c040d1030854210000078807189490701c0c0c004008207018012603204c2c50403d40034001020000014404000c20115804202c1d0b003013000544c0034184407030142c0c1c10300c4000d0f02545c0c2e9400113011068050a10411800541403540c01e0040c000d20b185102494041590130134048c0940d0700041075202c2001107000405c00b110a00010707180300c081043c0103800f1408210401450243d82c104a80c29200c0f01d000d5030400301501006e110720b082002e009600421200e0000c01c0101e4403c44138182d2001e0020035001e444092580414601800d80e00c40c050381d650a80d0226003085000e000d00760744011500c000300000402501c50600300f8085407405000c21800001280307148106000300302a40c83c0141910302075040518000c503002828251145040c01541c040c154540d04c035a9000004503016034841d81400380c7d01140f440060350407581200089140003012000d0344880c00a80420303406079002d004149010031005050410040203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733077419 1250 733076169 733076209
    0xe012306130503150f060d03180e01092007060b040f020f0909180c280807090c03060f21140114010f050d031d03071211010e03030f07021c030e 63
    0x4106529036400b03170076540880100c0340141c02c1c8500d03003001d0312100400322001840400055002c64001c031500c02e0b07181225198002041101c0c554034081c004a4030421105400340c1c010810000481d440782c0140140400060000404445961544003240e02a13104d02040000206641d40d061030803d0800d9840030361500e818404048041c003040d143e480819405c1d20940144d60b4059942042d05803240c0035000501240520540752803843c1d50b80e442c107108200301c035030408100721a030511900604080310030103012a2162410020745102c5075501008080c00d03001c5510296020801e6502d00070700c10714060340005065418a600e000030030005070800c011a6800b00303001c04c0740d03448101b45030640c690103180c286080d900d0112902009a441b4201300c1d80347c4224000400c018604c0100d501c43d55124004030030072010100300644101c101c00a9403a8103400600c000e4401c5090040100201840146101541e98048041c511803052195041d00002d006c090a182c550030050200c12441c1c0074218 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733078669 1250 733077419 733077421
    0x60503150901061d09040b0a0e010603140304030c06050c0601060e300c090f0f0402010207120c0905150a09020a020a080f031e0f0718121a0606040e01230613050315 72
    0x4405404160107084c40d0b426527a9210300e03905003002980708002071079002d00320762024a640b03100c243c0d03290003500041c1c585820b00e000c0007680500460407240569175000241505078680711064a000c2008012107800900702c001d00c10903003814880016481e0700c0f42511084150410044615100380c1c040d0b12401120113500380300101c000540382a500144107400307206541d64910040303060550b55889241d4008502c40c00c4810040c202070100251000b100b0100f28665443d0340e03040300c03040210b485541105113010148a01d034415001020b4408960044803036104155807006c425521400b138484407400003000b44144c01c5510101d02c00780501c5880e0415950921488250444801a040105000f101c072140b00e400d10001d9002801071032110011500e291003805c10303070460081c0305e681d0034010411798005249864160700b0b84043d1028a0400703100d503070030111507021002e004002c0001603542d4084409850791241d0080440101a008940c2e801c1c0ca42402d02d49800d00e965100246a002c1e0b40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733079919 1250 733078669 733078673
    0x6031b0806040605040615170d03112d0f04030506090c01050d05040501140c0a0207170d0e03010b1005070c09051918140705030c0a0807060503150901061d0904 70
    0x1401d107800039004900015951241e1800e80f006281c0c0c4a001041140c00071000101c10355008092180c00881c0000e44800320f020f498114122707030030700506a410b2070381440400e2001841241c0d12032500c030603041210843c0e0344071084e04910341101007200e103901000202130041000510860390010200d00040100320880c0001034200e000314200c401e02142d481c000502071007400d4204203000e50740c0444a8400c1d003480004015280c0c80398220101501c92000c0c00116280640c401001030110322014251100c1c0700d08044800a5039100c0007a81907480c0c00c80000c60742d84040300c816690802ea00c0d659503401c00341c41e16000029095100c00200c614000c204803000320648181d02548a1403100001c0002010044844071140908090420621107601c0384c108000062940d0998808404a502d030300a4081000491121400b560401e40c12509040100320b001c2e00103107411041600c29403042d14841c6000c0390146400742d120200084011185214050000380209515001669150350601e016 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733081169 1250 733079919 733079923
    0x1a0103060b121303032910090501050a030905010e0601080d090602030702060904050403120e0c010909090c120213020d1b0c020a06140c030d0e2406010e010309080a0306031b08 77
    0x744020f600c50020240d080816200380e212480b8004183e03008529401e140c2036049070300766a1402c00b409030b6180601f1408282c0603600002c21950b0503505d0510308104100d044026000030102141d5564817244880d00065041c06458081c000c0c103c001c003020002120002d1004403298002402c2d50400c10008000d41c550a0445010b5401130b180400c1503125454121515409141c1e11904bc516104079451184030104905d030f0044000da0392a410561100c003080c08485048100400009008004001d20809203031319201c9640000c0c1042c5c4411070504404007a6404140d040e04156035982000010802c4c00c155101c0341e4082d45003065810480354041040d4000c03e0080106000c040c3e407048048010800844101201c507900341d0303494021880054001e0150714800c1140c5006000010300d090803403000142e00240c1d16150324010391140c00c01074903e801100b10090403d61160140f1001c40d44010080c16040d1942d0f5001400d10b203182005140c80c0b0039481c08401d035000c3e60904004007440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733082419 1250 733081169 733081171
    0xb03010603021b0a14010c09050109141f0c050106120302060a2d14011d010614131710051006050327100608060c04060e0111011a0103060b12 62
    0x2180c2001030f5201d140304000c1614103082412055148034012a0318104068000b2803851288040c009000e03030346c6010016a0b090f00540550381c00140c20680802100703550704100f02e8064005400e03600c422a5103114000c560b003030750031100045100e036120102007081c248140c000901c60540450440c401c640d030000e44908003d0300c800d0825441c4d52142c843c01120002c4166031007423003101c030801d4006a0000030050260350a110400000d01000004c0341180c8017000e00c025404040c4103d0182e003407a0b0107032690b40b401c140701c1d900040c00f80031580040615072498409052203142424200c40005d0b60760780303400c2aa003805d140c0707942011b003445424595041750030180c80d01030030429121380d10188000340e0300310302c0c000801c4103441008075480100c801280700030500a504805018040c1c89041a95458200b601c141c40c420310204010840701c0c6c400c1040c0c4540071030514080004c0000850618255a407a41d98200506824012400300d580c01d8815036000f454054101c6003072072840d0307041c0a440c441c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733083669 1250 733082419 733082429
    0x4030807020108041103031c0605121203090a0c0e040203010e0a050304140d05060703150f0501050d020306120105010906090e0a020a03021c0501060909140604020f0111071805100e010b0301 83
    0x75004013040030081d60315614440001d0140449440d01c22442d41c07840600c135030a4151400034038142010a850800c00820800b02030110001d1400f801025000d06050748003d00c0028140590580700700003c950540e020f0061200ca03032003010904044c0105030071910b05884004099010b03d071003100040000c0252003c59809040c003c01c2c1179280d00105000320352540c0e009240340140c0d8108083c05405a1141800e10002013408180e40e85401c0000c0301c018044c0075440c04100c0c24800b000b480c8880380c005507070041d405000051503102c000c0e001070035208282c00581c2c4c480c2e1180c50034004003040344915041608413400611080740e0540125500030102e01000e400350b41000200a4207864000b09448100d500400070002141e50720690303001020401ea0458049e0320f0104d00344c2e542040001d50324060790b00200980c07401d103502c2e001955860040000151903000350040010035101415100b00c83e107848140100d014645400003418281090f00710148061070f1100500201c00341c007003502d041d10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733084919 1250 733083669 733083677
    0x1b0a03034a0f032205013605040c0c05010b0123030a0b0a080c0f06030403050a0804020321040f0b0712030c0507021020010219180b12040512040308070201 68
    0x88881e040c140b1215801d52450341c400004d40302141c0c0854030006a011112120102505807034800441d5201d85031004109250001c2c60709200842d545c0c810440341f0310b03110f28403113501d0703690f40082810b403009000313100003150202082d842405002c0c0142c4104540c240307855080110410004002000d4041600c40070150110000d01c0322010355000c0728100d14020701c604003c66507482c0c910765030480303041c01034010f6140d122220300500302403040d00d0103540c0c1500c44609243d56a4003c40d48402c000380140da06100745072a016241c150003000d8980f008a580d04280c0e034500300b88014410720929031006009010420000c00030580071202075401284604e00403800e0130003448210342070b000e14032000c1d61116180c0c24a6001a402000c01c010448864600907181026078040c1d17401c038040c200c488184411103451082d030451040c1c0d58240f50be1080c110402845460301241e55180d00160b1030b030341c020200d80062005000d01000070b030091007000340d041841c040c119940c0300d149000d80740c0300038180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733086169 1250 733084919 733085051
    0x30b06040f0b0304060f020f0c010b0d0c03060b031e15090a030906120b1908011d0d050c030c01020c030406090807060905040f0e0d030b040f09050309061b0a0303 71
    0xc1d608140700203500c0b40f900390b4803001d23844420381540c0e000a03000e522561902e90036821030b0a03d800796009140c1c006a00c9803d41c0d1441d100e080280c4008103e003503060007060034a0851600240c03600b030103200004001c4c907401920200381100410701034000030440d444500c1e4400040d40c00794501c000e8031340c3d61030a01140c0400302c42e83d0303025154503c08603504c01001000304c0650b80b4001c1c481011184190700074064140c0c2d28212032614568000c131030029030804100d01c1007160041d4004d02550f8000750403246444500b1a010342240c00c120070840058000250402000e80d00002d001c01400385d00c4050055a0324060003c0c0c2030525a10034a8001c50302c0c0c00c1100c4030210f503030744804001c000031425160451803071400100100301c0c00241d0b62081c0d2801e102c80b0204282c41c4108002203901500a6280c6038050080060540068400751201540110031040c2e508052001c0d400d81071098402040f6034140d0980002c0001c06a8403919821030060b5151810202c040c903034019040c0c65100a07524 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733087419 1250 733086169 733086173
    0x3030304120207031403030f01291c061d010f240c080c0a150218040216021c050615030d1d181e0f0f22060c030b06040f0b0304 56
    0x10f101980d44003910401c12034051408451020000f54450707008040c10408a07078980501810007403244980c40c3d054200b20214440b07080b01e070300003030a40c5240f80204179200814072007007400361075041e04110140b041c407038085120140e000e421030b80035005a6030850b8407230341450012455061520184142091080580c1c0400d5000f03a189905c51030f0044c100701e640f009041c6540e960340e640102c04486140004a007001c0d134035410310a941d5000821184410482107941c100700194000040980d8200a620b00401c0141e66412203441e102d800302c03056013580034a60801c541041e0000340b8204030500c0c51482000203a0740400e50103e00c1c46d0ba801c2c03080c020700c2403e26601021446c10046600803081e58029400d21450b20341d0fa622030101c1c00c02c1c8007200d603081414a0001c10083e00d030554207580001c04102d81004101b0310300e922000a0ba007004644d00e4650410501d4580300d2000d461150791025904403480d1f05004102030300e44166925484c142c44c0415040c60800107220303050f2035034404004a41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733088669 1250 733087419 733087423
    0x5060f1c14071803120302030f10060c08180405090d0e011d190306020309010608010b030f0c0111030d14071d03100e0102121006080f061c050309040c260402030303041202 75
    0x30103950400b1030b9980f03000464001074000c0d40140c0709c4401c002294400100d2880d00807a00c401070b100c070b6585080307014031240c0d03c2030115000548800d81041015468503000c1d151441103500c505403030303c001d004580041c0e1001c1c0011480507a03150402c8110440c1050111503c40304c001e680d00b06903031000d07c20030706500790444107006410003000e10b400001071052803501500800103a460280003040040000c2e0308150ba10b05c8c080c2c034610b04d00d03002681500902e60282c024540c1061a01080e00c1c5000200c01c0381e46c00311410160b0340850000c6101c10701040940c030019074240c440b804140c7c0314020802e800026620802e28032268030807031b01c603617000c9204a003c4d0140d6990207403194440c415414040005001c01102e801000d0004400ea80041c1a402079a050a400740001030080d886142600c11004110070000b28180c507184800c10000e00c40e07881d20712a01020140d243d0710091f40e01d441d103400480d00c105c10109440803081c0007083c000542d50110407680c009a224180c0c00c52110741d424168 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733089919 1250 733088669 733088717
    0x16050c150c1b0f041a01110102130905060112090c030b011d0103060507050d0629030708060409021c03090302090a0b06030a05061203040303030c02061605070201140405060f1c1407 79
    0x641050501c00d100f9118003505c1c02407250070100740c0f280d07002c121140302c0c00c81c00c03401405100d07400003124407020071070a0001d902040d00101d0600d48440580c0c1c0000c201400e94611100403200301c19400410010f102500003042c0c054910b00110390580a119600c400382c212040c0030103401643d451001c140d0640c00380086a1040c0f80a0b4000e0104a42d690010008100b030340103030440394541013440504c401c50040440307108188645510685440b0f40081c04002c01502c00300700e80103a103002c078101138908920b1080704403620943d2000c002e42d045105000ca581d5014090808040c2801500e0110303980c0d080a0b03035031143c0b089000003034607a1034500068981440821003180c0e8040000e02100341a80b642000d102802d1640880360242c90741d1050400d013425448034500051020700054005602c6011007026030b540341c52075582000d445000152455001f100d00507080000014144000d2225034040442520303d09401c0008003510403002c004c01800603c00010002d01900315080b4441c024010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733091169 1250 733089919 733089949
    0x41101090f0b0c120703170603070e1501140f070308101a130608010b0a0f030e160303030605030d080127050403030911091b0c0316050c150c1b 63
    0x2100c51503555000841583c00a11108418021050203900380da08050440d0f0f04143d0581c0d0300340e03010000019084550001030210351303041c000d0610020f00340402d8030940b402103801024429444c150040003518008030500d80028075001072004d00c1c000e1035003038142d6603010703054148112540e65550400040b0b0010b40c20201d400881e07050b04c0c1c036a5011220103400c080388a20540310b112500e488040d20702540034032481d42c241004200500a0070312440700c0356034440c82400c001c41c5410442c10f9075818004030702a0300b0550300444404000303066160040300c009080a40180401c000c220900410b4032605000c0c8150101b080720704c100a880300300380b811001c1c8414000800c2141420f240080c094900f220041e42c545602e09441880c62a05408a0740035030303890312540c1c41800034500b0b0001590000c40201c0414082800000c0c0108024600032040d01e200300e02500b2203c0408007000341c41c242d451007051424070306010803c00301c00001441e5858580300f010014070b448482c0c000811907102c00c100303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733092419 1250 733091169 733091189
    0x1020d02040602012c030708070f061b090f0f060c0512120f06030303070c02100e0306011205151e0a020f130501030b011b11031603050601050906120604110109 70
    0x80090b41c0d03a03040d0b00c0b19032820900070000c54503c42241c001c41c0c0c000344c100070502e4183c2040000e000044d1a400040100034800c0d25142d407104080e45600045036605100d00101e00c0d683d640c4440c250741e1000b082000381c0111041c03801000e007172071240c20804ca1103004813001d1000040388034042c0101080b00c454002946640381d540d0f0020390795a11504a0705441aa01003064107000c40c03000c2c80c1c04400d481c03245000f9510880e601c02c0725020003880b1240c0300c18207401e0240c900c0341440c09803800c1c0300a502a054040f01e14110340d099281807480d0003017030710304501d40c4030300b403030138486981200c0c0e03480181c05507d00010303203450704c50404000c000d00c5002074410501e01c0018088417040c40065109007284d00c240ca0401c002030f4a1401034601c07691141c00b510001598000300000252019100545444080c00b102d260b001002c8aa6480031055001581e042d030081c801001503241c9407007582c0c4e00c000180d526001c0d003018160015528540a04010f0104080c18070b21403217644659445001442c08503c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733093525 1106 733092419 733092427
    0x501080603210c010207030e0f2e1b0f0506010e10030204180203060f04050d0504051011101b08010f1a030c16060b030f06070f0c0501020d02 62
    0x454002d006400d002a1030030810174805480710a200b500c954101200c4c13281088013000e0030501c0e0510078006691003403020303603051410004603180480b210708a402980c10580304e90702c1d130350085405804c80003644418070150000401045001d00181d0b2203a0b40c0714118181400c0c0112205022800000010001401c1c6030344440e0040c222900da940c091100c641c00241092415200076840458500500050120034014007416002c20b00301645880c3c58103012034042800140c680e82809251a08460544401c2c082404140c00c07183d01000b058600c198089200045440340d0380004020700004103100400110318000e4801c58805810760824004041c2e205520082c43c0d00c00380c501c14082700d8000300030314408151062050502050f2030281c6014540f6006002c1242c0000343e00c4802401591074021808504144042c0790541501071503082c094003a221703803003400202c58400070b = true := by decide +kernel

theorem cover : BRFrame.Cov 732913669 733093525 := by
  have h0 := BRFrame.cov_init 732913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732913669 ≤ n) (h2 : n < 733093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
