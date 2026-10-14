-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3734
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:28.418549+00:00
-- url     : https://prove2.me/submissions/aa01c595-d9c5-4ffa-9557-a57f647ffda2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671402877 ≤ n < 671582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671404127 1250 671402877 671402911
    0xc030e0705040209151e07030e041514060a0215010b040611010c080406050a1b03360f14010f0b040f02070c211707020103060510170a0e0a0605071214 66
    0x100151500c240c1354240b00c1c806540c0350740618002c9c0050005200d8035004910341010803001d020614050000d40c0d29803c001d4050001030001c120050744002881c00850280034400070509000a0903a400b8100700c01c000e546650a104005100101480301c4100f168182000044a40d801003150340d0043e4200300c02080c036540d0107170084081e084080c0c190440300d42c5140340840b542c0e855845038a0cc00001080c881708a2844100259031204002d4040340021400d40d070030002580c954284c401c054810a22100740c04992001340d4211081c90280d800e615480b0310b030580852505119000c082c00a07910214144038403a00c4500050f0301034016603000d00c0c42d802e010306c8412070074a070845090740d0059006803006810151060550000e0b44100d01181c00d0800104080c81d00e00703130b24030f540001a1750302c400107030b41141c245414102c0a4030501780240d50b4600b00060340700612180d0804d40c0912008030f064100084c000309140c0e07003800991078607031030010091004200002c2407a007103034032541914440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671405377 1250 671404127 671404147
    0x21120302030c07020904060f150803030c0702030f0613050106090c1b020406080d0c020a0e06100e15030c0a08010504050c0d020c191b0501080f010905190c030e070504020915 76
    0x2440f0341900650701809003400c0200b002415044000e008201c4a4240b200005440a40c0343d50b141d41d0080001c180c00c00d100140030084440080c042542c00202141c00581d6140501410502d0941d00c01002484c3d80c0082c0c014400d0901a8200812030700b007041203c8010450000c2954281c403507594010107101181c4e40540d5220382144010749000f400751020503c80900180455940100c201e000740c440f4000080c1001044044501c9030b8801341c40c840b044800100f007200c80e450f25844c600e51000807268075014010100c00910b10a0315000d02d441c0d80c030207242802904406050f40408e1199040000700155070000f00261400d00181c1000541c9480c0f2820513103060211240000c0d100901041d42401417040e4000c07540101695420305801c42c585034401180d07007100c211490340c82d14070984010070a0030850382c445507104103001c4880130034030105001441628404c00400300040e072100040c481206c405d21440b00104412101141740100f0b00c00400e079030350f442c9210b664880c036001c242c180322 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671406627 1250 671405377 671405401
    0x30a03170a1d010b0a0e0603030318160303081e100504020f0c01020a020d110a0f14010b2115010815070c0c08070f05060c0c06030703090c0e012112030203 68
    0xc0c510303003402c0601c0814050394464020483d00c0b1920703105500740f10700014440240d034410790180e02c01501951440e0742d8405a41d190090001c140e10a5200d112010f00c480e001144482001d148665584441401c1c2041200070010112000f0354840f11342000b482010344543d0300e054106c0f42d05850140c0c9440d5204103507031050055000c4100c05500010b082c41c1070541c0418031134075070211915042004d45245032042d544040c2801c0052259031140c11503000300e00403440303030b41c005001d0800209068a1b03041c0800c90001c404c112240b00750401483d1111b204070300348221107462100c07000c001100c1d850078540c80e5440798035401c1c244025103c940441e43d0503101c1c2581c460413035000014141c00171350b0745610a5881d40301d40b25a1402e00c0d0324400110b294503043c0304503000741c0d16000041500c0c400f0f07442000000e60000d0889418155105100d00000e0f0103a0081c0f0014003203814210081d40c50000200c0032000301d52400d00c0f99201d040c40e0711000901c003401180d40310041b403900607165a40c001c00c05a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671407877 1250 671406627 671406641
    0x90c040b1206010b040303021c02030702040f270606060507051b01030914060f011203050a0e0a051c0506070302120f0903130e191e020319110408010b030a03170a 71
    0x81c1d03004182c0040740c1110080000c20460f846a82100c0009011400b89001107940301400320041e00104043d001516080d007014503800806540081c0c461031048002c902202030002d00e42d601ba9107000900244600b52045000401031030034280c1c988051a2f48050300c1c4c5807050f5041480089100c1800303216482544440d050700d90240c1c80402003850304210700e03510801142c42c004c0c8040c401300003140d00101c80c204c22041c5c40d13054071a00e040808180048c0d403048071b0381c02015081008245c0009150351b805400da69440d2110040c00c500006506119041030350080c0010107040c01040818800300340301001c181d11030030303018100450340c07038802e101d500f50b20802400d87c152401e50180071515030940b141e200d0242500c060203a02102c00f8119000c282d484c1070620345040740f60800c0d10000350305a50002c55218164158401050a80c460b00a040320989042906081ca012038180f040000c00d01c03d1406004003200240109000d6a03401003200044000207111030001c6c00220b000c17060710740c001c0c075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671409127 1250 671407877 671407909
    0x2030a0c050c0d05031b010c08190f0f0c030f11040510091e09230a0b0604120b060306010603090c23040606230f04060f05040e01120c0905090c040b 65
    0x288282034142490740da0b070f0b0401180c6d02151442402000800a41480f40702d40304e1030b19441c0c1222503500d03900a8400419100e00040006440f680e10f41e040207164440c0300308513141088005080034002d54024100c505614034481c0b000c3c60407003072460304030100c42500c040307a1080f00c1c4810804441007007210011141ea1000811500806090030100071841442050316011902040340400101617005e13070f604071480c070304101b60440c0081070350600142c2000422000c041c0186140a41c0c8484c0b100319100303e440107555800c58078040c0015440c0070302c00507004008520702441004241d48803c0f201003500c0c418149090310042060a01105168150b1701c1801c006104000840d50381d400548a42ca10380b405551005404081302d03824215401070316005070210041038200383c00e010043da808002071641806200c000d210000381c0182040485000c0d02d00680320101511051402a8460505800000d006410082080341c0c40100080c0d440a51100316400b258118000012a01c0032001c4100c103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671410377 1250 671409127 671409139
    0x70c030807060f23040b07090f12050c0a0305120a140d0b100c030801030f081c0b09070f0c0b0a0605030a03030b0f0103150e0618010e091c02030a0c050c 67
    0x24200703109407070f4405415244103000502004410504076a103100f04030030032100c40c410034008100810b4000d00c0c0c0941c050b034541041c000c1981c8a00070b110401c6603952150710054490544a41009030074801185103c40665070150b40f282980d0b511516081400d8194031075420201d6886405072140356070035100c008580201c0d80d42d00034516034402400c00784006900555442c62015034081c800d038084a5800c0e0980d658006907400d6944079a400d15000f9801c1c1e800e50010f1000d01d5207a011044400c510a03181e0b040051075124203c01c0c0244414000d00080c144522210f21075000340d040106801d40503400020703c16541e0b649070340c0c540140b8039500025014810f10018500300740c3c140c0e005c81e59013001254105e00741d900490044050320044840c42d103528103070345402c020b404032030064140c02003402040d4041441da50000c0a060360000d0b0300010741150740c1400e20002523424010807807500c50520740c0010120800c0d40103503491092131a20010010b140e4400d90900c44140000100c5050003050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671411627 1250 671410377 671410387
    0x207030509060d0c271202180c1b0309101808011805190f080304050a05011a1906090522060902090111191205090301112a1002070c0308 60
    0xa10402484440f644070b02041c14041c610380381c3c40d0344121402c0840710180d1071840d031900b0f051a44191b144580d50403600640720b0b170070204807201d00c20b0045201e0383d0710400c01611494aa444094a440d03400300c09500368004000680282e00c0d1540c0420b0143e516041c0f00c0c001250860360681040758960148440e5441c101d40c403024042c140f0350070b0800f18000c404684a14110140708140400207103401429000500201c1d000500c446d00510b60180c004c0d0305842c0e41403c01c1d00d400d429190340740780301c0c0803c0c10703211118900303480c00e01c0342c41d903020b60340c4070400c0d061900305040900141004d01a151149038500e00640b10b00c00c4a0034485241c1071504410b0001903aa215400043c1d002400c00078041003503984a16201080000d208460a02080c0201400c0910392540300c0000802d40f500320810004200b2018280c9090090300f048014512030365a84610404000c2e2000030410b000742c4120100104403a0500d07800500344150044900b00181ea410103403404a5410030980d1005202e0100815 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671412877 1250 671411627 671411647
    0x6011e020303240f1c08070c03291b0d060308030a0612050c0f122b0215041205190f030614060a030b03031c020702040f0b030a06020703050906 63
    0x101650055250421050b044030f2070b503180080703d00c0c1c0c01d022640c2004a03142c140007149007041d01c2e1130b6510102d00c544042040c0f02c2c0c4450780140d2080c842511005240b003030800c104420504440b400102448441500d02c091529100d40504050080044200f0100c01010714000070030454540789070310102002100d0743c4e40b85c681c0c0b40350011181c54844610340382c1c002504403183c4a482c621580d21102800300c4920754001c01c0f01554102645e29045401400d40c582a04010052100c0d44845410f5580007441c1034225060380324990384044003150052040390303c125010f04030642d00654400100444488403807411a118090841100241136106915020198208003084002c0e40a44d6050052030f03211500380203184046803855401090800c0814543c034420f41c03042c00740e404000d060764500490051300903a140b6005001c0381c805580081c416003103241500c107a042403410f1480c02c0c05426030503c0002d031a00a2614040c21031030b000507414081500c9101100e1210100030801500c0d803004c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671414127 1250 671412877 671412883
    0x81b0715111506030a0b090307060f14060a0b07021323100e0115080601030b101d19030206071a0c2706030705070303060e0c03040c060e03030f0306011e02 68
    0x1032115800e80c051985002500341910b8200c61042c400580141845002d60359490061070005107151400d00080c44650006105809914a88440048082032130201e07813503e441c40c000c010308130030310905100c0401c0206104000580d090b054045400e01d03089028040ea22003d0074880e020141e00085000002510703107441c4d20010b00402501c0c010303100c0c0341e854418284c3c0e168001c1c040d12034800b500070721550642e44070f445980c0c1d01c014180b4020408400d0700c000f0414540c0c40c1c07810103021070000c404103d410301e00103400b0b4810940480c1c0001840c881e81740082c180000c04d0001a000c0c034000180c140610203842200e107000c00902d080c1c00440e2900307550b05211500800e492507035441500640340410b40c412035102c900c2c440010100e40c60341c0c40d51030064803030f6070048904030245500c039000041c1510090704241d1003100c401000b103a0300c0c613007460f280589440c1508080e081c0002e4040103c0c00d80c41c00801c6d184038a0340d0b900b0041d501d413142c60059403120906100044010306603100040155404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671415377 1250 671414127 671414147
    0x901060f080c090123030d030506040f02090604260604060218010201051513060e011203030c02030a0206280207110901052e1404030c0602060703020403081b0715 71
    0x140ca52180580d11840c00e6034840803007103611a0f008107510014401c0b2580030b001581e40c112450300c0724094940c2c2d8030202e41880c4148500101196840041100e03506185c002c0e2040e400301910114500410b0702c00180306030195010706094102d8250301d140546031446900729000c0036510840b480c610b480e01d4030101030742c0000c050703803008400500c04038180d5005000d41d9000721100050800ea0429680602941548501c4811041e0fa19140b0019242c21086421401307403100c4240098601030780d0074041d00783c8582c510301c01c08540c020010444800c3c1d0210f041900000c164403001840524603004000c003462007111002d00da403000810008006006814840c000d0041d02c0d0410980ea03102c040040280d172603c00034403c84602e41e9150541c0d01c2d0325a40c44018542818900e020b0762501100c80410340103500100c03500a41031a0520505804000d2079500c201c4600e0306515090544c0d40d07030381c0c15010300c942d4800c0c06491220710048102040c41440003800c1200d045c1c4410354183c0200600c00b0403d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671416627 1250 671415377 671415389
    0x90c0b0712050f09130b0406060228030f03020a02070509190b12120309070e010f06230f1341091311100f0305070c12050c01060509090106 61
    0x3507645140305a8064010354400891000c455401c14925809000074100a4800724076400c0d40c42d030301c1000304d0b5258841c81c4050070aa07402004440c0000ba80c2c640c100002c003203030072400145a01250002640300c2c40500c3c004116260141e100c11041c041a46000c03095080f10b0380c0204454104060301c2c4000c4034441d1103450040c0b00380040340480090240202072a40c0d4910160400c074400700b006956040119004214402120320302c9543e4010580071140c00c0e001045024030301c1400b040041d5010041e00e40602c1490a000351800d561501b5030424492410343c50f402040104140c041c0c0d100e6204000000e0952010000151900c0d501004550384080070030803041c1c2d0000121081d15491913003900c8002006464060b83c0d4440e00d04540c42051118400c560b00b45803810744407003a85820300003280403000d580750300502003400100501602d00007031070030040002005108010a003903414030140900706081c8075649801040340d140c00b42580350051a0444140020710601d424158400412249 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671417877 1250 671416627 671416643
    0x9110c010513080f090a05030105090c1905101421061014030703050c0403050d020d090806040f081b010510030c0b0301060c020f040b0d0c060311040308030118090c0b07 74
    0xa114120200d062041d000301401d0f0500c00d0241e0104803102030000c1241030380081100e000a956100042e0030346800f01c46104040d080012206100d0900c64291804855020b50024a89080c80081510500d82601d00c0003000705407001a41c06400380e0045811400c0d040f540c40b42d12307655400106180c4030054490600461040803a01a0548a0351819000800c411015450741d220100210013820307001d061221003130810032000001903400c1110030859021500039150080800c60090808101640540c0890300140d00300000101c91004110300d080e07000401d0350710388100040412801095800081081d0700c0c01c0d0600c80040f0012800034101da00c00c1100d800420b4a0b454044d03200d00080c8181c6021445d000802c00040c98007109084043d01c0190000801905802c0003d4800400003030948041c0682d29050110302da0501401c115040c0b0303140c00c507152503c0d41d966406103110512031002925010a492290700c03882d5001090302c0754011092000c5141c98800008050788604402c6038408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671419127 1250 671417877 671417881
    0x130507050a0b1206060c070602070e06060f1210210507081203010311013b060301080a0b040606080d0210060e0103110103020901030f110702040b03010b09041b09110c0105 75
    0x2260803000c0a09582240040500380b03480724250040c1c0c510013502e8954005024408207240c41c80c10013028000b40b23110b034000c124640c5010480c03502c584001e850b450040c10100a04200400c1c624111040e91550388648203a5564160382010050a5504a40d0040220355200f076a050700b079a03005040540078005030f9044603030b0341e40344540c0e07048160041c482d80041400108049001014a10010700060500d003111881c41c411101e0080d00e00031400c04121600c90205451a0b07510f809854402010f880891865042a801c26628202080c000302140340c000009420808250003050040100c0c2045074508004210042d4075100c0c030f401c000500301d00d0403000003041603c00072214102c0b50404c4004590800704c1c00114003a5206091190525447d8406600042c105200b06103c06d024540d081c2d448220301d1042205a44080c0c00c03a52007607052600410f8103640d2148041c0e005a40704140440c00180245e0513410700034036074000d030002480c090a2110702c000282c0105202440c0707100801040d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671420377 1250 671419127 671419129
    0xb04060b0418051005100201090812040302190302100b0a1206270209070c08090a180f090b160c0807050a020108161e030209210d0c051b060c0613050705 67
    0x30383c001c843c140f0104c3c40f407020070445400c0641241c6440300349440041050511030b1224a070b80d03071210f00b2030000101e140f0100420f1580c140700405400c41841442c0300344641c140c40095444420b04c10800e0142e942e4441c0440d2582c0d0300101c41c000b40100c01d140b18860707905040210041c500d0500682c4610300740c541017400300c42a400c0da4008258024420006500d4607081240d110060350701c101c0d202001003040e03058030703520710b21400c0042c51502100c000520101d040d0070246c0d5041c07810140c5a5003002d148400041c4070300822640308000203501944084052400c0740c0380220711001a205c00070000b140c0b0240320001ca40520018004c0c0c1300c1d01600c0d05d4846903020b41007581d2407010001455015810303084483c0311010760b81908145009805c10601ea0b0004000403400e40710500e00c140c81003401d00f03e10303c3c00d0000e0092064141080e241c4c0c00030307a031109034542002c0d091024802e0785408102c043c80c2c0d03504c000d0300e0741c070707154074080760000c2c54000000c82118640d50016109441210000929 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671421627 1250 671420377 671420381
    0x4051203040f18020c0a140f07060507120507020a0f1a03070806040b2419050a020d030513061b0e1c0201032705030d06061b0f03030b04060b0418 64
    0x460b000c52615003111481d20320099082c020001c841c03000141c00304104c0d404098200035a078202030242c0c0101c02c841d040111020301c0c00700242c0c006a801d400c000c204000d00c2d40c02509079941c1503040120803104074482c0e08201da443c420260300035440002418041107502071040d0520584c0c10100264000e40501607605000f0b000031140c04002403a140c1c0000c4040c10580c001c801009005000c0b44081c2014452500e445000c1442480c11420081001c4070060303901650800c21000505000d0304d82613081200a40b1650090500d0082c1625030300400d0b00d0160700b44d049040240c00c50070410101801c40e5084000060700d41e1100700044000c0fa654040e403038881859461481002108170310390055a0054016000c00d4144c030f0b00c142800d00f00c072042846414880507800303201d50069640d40d40a000030300102c6240b60030902c01c00600050f08469040e900d419080340a8000c2289008561075180860241c4100f0740500d41060070068006103080f000740c081c0c001d1700e50b030036482010241c40983e00e0301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671422877 1250 671421627 671421629
    0x160c05060711120708100b01030b0a080c010815062b1e0e070e0f1b0f031b0702030d0f200a0605220c0e06180613020c010609020405120304 61
    0x118810b40c403800205807511031441403401d0700034030540b4200713a561400759017441540c480c0b59003900e464070001061580e05125106414070122045220281840c4c2c0450f590f0034440d083d181800b20a40100c1c030000d90201809524601c014001d50341c40d0303180400d81c03490100d90349022010040100076040094054090340002d02080306ca8112100070104051014060903400085540150000403030b0007542c540c0c80030700c030b40e0110740882d038142400700089204800344440120310b03050a001c40c22800c903240c81201e4001c4504070384494011543d0040c8061445042e5000358103100b07418400c80495048032016040356a55200c2a50181c94800c5a45030107800603a008060303009100d0080004040794003850b00184840d0102c1003c1081440c03548038600391200c01ea4202d071f1491401c10402e03803003000c91a807110041c1d030224040081c0c044040041c02010b440c0320f01c2072031f440e141e800d01c0c1d184545c16140040d02e084000d001450380d40d0010f0000b54003074010369018440881503d4421540042110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671424127 1250 671422877 671422883
    0x901140108150d02271012110a050d05060702010f0e03070b10030b0a02030108011a010e241314060702180a1d0c0907030510060507050111160c050607 66
    0x52560b9414884203071072114840c102c2d805410401c8a01c00750b150042d40c0b491982c6a01c050a6100e1904c11000e1155a40184090420681e100c0c2c18007000c4250a012254217900075040000d820078000000c25104158011703581003120101c0e481c040c41400142c880c014036050300200183d80d001e0b54013209807042d43c0c1b02881950300401005000404200d069a070000c0503a4101030306944030341d07821000d490f054909200030380d0040014032100b8800e01c100c000601d510300021110344001c45c0044c003001407a0801a20503002008810040500c40c91145290300500700c51aa450310464036202440f451070082e4041e410082840d1100c504182c0203e800c025001000ca00006862540701c031043d9000810b0780c0d15041e02c5000f00700c2d00e0a8858240e0108072030308809000b9a10b036503000d02c900f0346002009102054206002d02c02c00314622440001581d0103440c105a803901c2505210b405000031600194031480b00003500300d070b40f20101000980f228803e4200612150b80c510030846a0b0040000c0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671425377 1250 671424127 671424137
    0x190e0607021908090301020f0406020f06040c03060b0f150706231f12140c0108060609240a0e030607020d0905060a111203190e060f0403020a050d0e09011401 69
    0xe50700da05032070342d500c84941d00c6858441c2c0f8151010010909a0708a0f0702c03042c60070100450b0520040fa018412240200711140041405180a8a03030803d034000707a10011300030b6a03450101401e95280c0b01c406d1805001d014210660807070f28038100b02000e522040c01a5101464000180c02e5007915005c120000100c4c400001c030f180d00da0489020a01086100d109011060191300103140e0344c2c00c40ca40e517103ca001c0c003000b2150503002030404e424510b6004103141007024081c1004815907450082d51243e04091315420640200c00788078035103119003a03d00302d40001e00400d840351035a80c010000d8036140d1050b020340300a5150710381c0907030b520311031086801c011846a030814096401d04001800d0001000c0c50100c001c8801460441d00f05407141040b014408030000420500342018000c07155140282101007041442100c4a00e49480002c2c0a81c805440d80501107001d25100300429205960020282e840e40181c2071030180c84480304142c5240550308201c000507555010510f150001001a116 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671426627 1250 671425377 671425393
    0x40e0106030f35040603050703090c09150e0c13050306040c21020402130e09071a0a180e07020613030c02010c1b0b090f03010204050a0b090f09190e060702 68
    0x65803000c54194480103140d140c40004a90800f4454107103a0296a010881d4503035030380c10900c2c01800d450005041000b45424409101c0c0005d81c001040701c12100b228000040c12445510b600000722403641c05401d102e0303885070a02030f041c00700100800100920030003a801082d540e0080c1502d40c0d20403280509048061402040460401e02c0a01c80b44403100380341c0881038166500140c12a0002d41c014401000002d50500c0351083c22001e10f9000310902004012691400c441c21081c500d691140da40f4145001ca00d460101d030203800c009c0a0070520b0060442d005841e500f04d80c0302481d049a0200040c442d070400b05c0c5032261004851140d00750196201040c0651030380040d00e01c3c40d901d04040782d440d041c0706102c40e10007091071810b8029000039031806603114000c80401c41012001c4081e00c0c883e900c10001008540d41e100344800c1115201d003a07030b50f11071000100040c14010b60601c0c850300510030a0130861407140100c0707800322030320780c0700400c00040890440c041ea80301d0080703d0240150b402900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671427877 1250 671426627 671426633
    0x5040b09011b080c060609060604141c080d0c08010b0702090702150a090201080105040c051e070b0c07060e1204090216021f1709030d090501020c0714040e0106030f 72
    0x4040c040d0040c149540e07940808640038103a0749040009440c4140080340765103c00500b40802038110740101c805107414200413000403411710841c8541c0c4a4011004080e0440d901c4030189080401c078480b010500102450070300d04110391000340c00c9484507240554080360345000d401803e06a032503640c02c55050010950900c0b51a80c0003034a8002544907209550400b0212101014426003500001040d10b06403403001409245040c1c0110b4030a9041c0500700c0301840d0300600ba100d4600c1200241000075800300401c404c144a486000340404480030b08105070740c00d4242c01450070500c00c0030104400c0b4150b410031500d441c000c110500700c190080000b00540701064003d0210100040014110842241d0001d5180c441702e2045901c4001c8441d5400550750704554007030503410303140b43c94030900c1c0f4100380c0d00c5440e8401d04a503920703001c0d03858046a060000950544034400c101750110340303e041d02c450304100d12003400d07802c5511030743c03c0100c9144d580106001e00c00441350300161607a44040d680e6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671429127 1250 671427877 671427899
    0xc06130e07140a0c3201270209130602030f0106141822021204030807050a1b032c040c0e1305040809060d020d050a06060230040f05030606100504 64
    0x160300341d070f8022201565607410b85d034140300308050309498241c1c0d40da00c0502200ca1400d46038034803a01c56240491007421841d00d000c4284070640103a0443c2c40784065940c142c81c000150780f5200c0080e004600c048204150904c1219085050769441d41b2443c200202004c142c24151207070400e01510321b690850342c0001c508283c54030580741c00003a0b4921002c0454102003000320f13000b80c0b0195024504810901042c107400080e416000140c916040d490200d8205028141c11070040c06164000c441c81c0d80c41051500c52203401189005981e695400c1c41c560f81140001c0d00004c244261040c0c0c64400c00c4188603028900b07403003005101904440e0306c00000800c00e00140303402441519070701d0041100d12019030b00c509c010b210140184200688030391a40c00080c04460000300070744282803a1101c14032400e600061080710038180900d400800040502018480300035505440c110408040390100e015100c0d021403600b50b81c801d504962032940d0b90001c001d02c106d40e0b041da0300c02203074080000340700014034a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671430377 1250 671429127 671429147
    0x30a0f03020c0f0102090a06090510110a0b0901150602010c0f0c02040204031704030b09010603080322060c020322061413031b1404090809040e0c06130e07140a 70
    0xe05005050403151007078036080450300a01d180140c0d5000854482901e8a80c11a8016000c285092a00b0f00d0034440400c5445050012420034004c510340e00301c9500c5410040c1e81d4505500440250942c1000e00001e40030b0151080004000944030130049140b610520405000e0012aa030300041250811000d03a211407078414240e80081e000c00000c4007041c0c46151042c05c0c000554070ba50307500c0d403550404d00c901c01000350143d9100e034100803041004c0344c1e8103002d03a034222303141c650100c1003420703828460390303038102c40b0000105040e0800b0344441400d82c0200140003920385184200c00c803548112402d05203600140030380030104401ca244150490000c9001d05441868804041d07000c3d52a5150803c6200d40c208036103102ca00807010a21004207400c544107440760381550184403410003607840c144039002d100009030249a8522040d031201c0307000c1001074550030014100c9a41e070084100c103c035070346140c0d000720281402c18138040b6101038400c0105001402c620b460060070b080c00100100c030100c1c81c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671431627 1250 671430377 671430407
    0x90601031d1203070f09060206010b0a031d010e16150c0302101e140f060609030a140f0607090e0a1104050306070e03121201051c1e02010e090108030a 66
    0x4500c03001d088000308219a0700c2c0140a252503220700e00400018001d5000c01d0400c400c00c06c180c00100f29003900000e03411b064503000b90801703880340d1010200720010309014000110758606c0d2460131000c0c3d44107600c06c901030100941502d1400b144090f03481c820b18010300c15054456411001c244116100b0815100b000e44079205481540e42c0700c2003d0810340701101c00d41140c20404801c0224a00400e00c1542240d9070319003000c0e6038900d0310941105014900401c458080e039000100625180d42c1401081d038540c0e8060046c1e25001004000c09565100080c03241c0e00500c2440d000c200301c1409030b80b00004403501d200c420f140075550401d41c103010381002100e815510760144004607007590244482c0b8807038142c1e940c0300d0341c0c0e44002c041003600d00701c0d480740210b4052008014050085001d113801c1030540701c0544003822100e1301050465801403000202800841d0240c0a0003c0725200c400740c0030485000b42e0b2240800d01e204000c0000035182031140070722a500811000d00014040c0009041d1500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671432877 1250 671431627 671431661
    0x1150201090203030703090e070816080406020409090f171608070609120f1d0a050f0d12080a0c09060c030806031e0a170304030e120111070f11040b09060103 69
    0x14160b020900d550480d0f20200c011945400c0d091011800d1180c5240e4460701c207280081032428182c20700d44c0300d0729444e0041000c22403c07800041c203003c0540c044400824000808000301c0d00d032400d00c540000010711088921414864440102c4c103240802c0e44c1003410b20740032002201c00c20f55500c44266100ca030040321001d46809415001c9080100300540311441501c5e24001c5c0c2c1210540280159620b215209404803c2c104808890704e4000c14142980c0003601c24110f0040b1090018010841e0310000800d1003542089103110140e00004460040d0b02658080c4040320054506075201c3c50b0707501410b80003070000129140840d201b14280c94016002605840b02c030000001e00080043e100009034007540c6c031080c0b602d402c0240300e4066501100855050034150705140c1d400400e0741c3c2403111b1482c4100a0300012444072138082d4810034021b0b04001c030099541c0400e140c4150627409002055076800b1b20012054114140f41c05013001e4200001c084e05241e503034550054004055102250720160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671434127 1250 671432877 671432891
    0x117010b04060e06190b0f580501080c120601140105090607060606110d0201090812100e0901090b060103050f011a07020904061a1206010e0604230a0c1701150201 71
    0x224840c0c0041511340c1510b082241c0c1c440790b0151118030144540d5003000c40e86113002d52541b50f102c2c1c40e078041039104150000300c88203003400c02c00010011203080e110548e09180000000f141d0000013101c40c49500c042c0d9440d0700c4000c1760880c040e2100300c00d206228510900340c000760941e600c83c4004142202c03008003660300380310a0780c031103008481e141d801003408150030840d0051514001c220350558220148001d00c0310112655452105000d281a68100c801050000c1803160b50304601c0100580700010709180c003450306420303140c060039050000342d03540c20450703003c03d001d5440303030040520651100d01c4035100d41e40b8160116034000d20340e0146070741e00c0ca030900600c0010b0b915141c0141c0600e0003041c0124610041d40030116030326115400091166500e000b00706404000800c00e1811a140314094508683d0f403400070038043c001d0541c00c0506003402443c11180a6507030404039004900c001c03001c020400c03107800103440b80c3c0703034050ba0802c40a20010040003086091420b40c03070304121034030021070b00c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671435377 1250 671434127 671434139
    0x50402030417031303142724190305010510110c030115050f09060904030518090103030f02062202090402041d0303180c0f0d03170117010b04060e0619 66
    0x107a00265500303c040c9800113280c6040c1640149255070958020030038919019507002200b00c88203003001c801139005080070055009948000c1c018412100c050441c49441e10004010340c3c50b82d2080100c03074441034040e50243d003180d10030302c030b114103039800a000c419100d5242c050030b41d110740000b250703450144a00154890961000e000d0300c601202d4407000c03003140a0401c810404103170742e0002c1c011f006030806410000f0b140d81d080c81003508240c0506002e6541c420700c0103070f41c000410380b40c2140d400c810000000070800d82d01480c07188000985030f00382c5d034140d143d600500e5518028440031101d02c26142d08143c02510340400c2c055000b82c402000014145c2172b6030a60b4a403a0066500481941c02c040100402c0039040c9003030401800c0c0c10005041210900e10008000003140640c0b02c3c05105110103032010913000c1c5c110b0000c0301c4c9444c012034030b43e980d5510b105e00072684041e02e0f08249500700350b0031070020305041c052001510240d0070f49580c00e41d00e03501409a000c9900e0417000005030344007400580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671436627 1250 671435377 671435423
    0x30109080a0c230606150c011a040b0405070e040c020c040609061d011208030717090313080307020d080f0f120a0605090f0a1a18180d090504020304 65
    0x210081c54407060111040c500702000342855080318295203251075616504421000300740d40b507001600311086082405c0d12422196a4020000080010740c0303814803043d100400d1010204410300102c3e01030242c0300c0302c4018003040d5141a100c2c807010a0341b2030141030561901c3d030890301050b011403044546c100e040000180c144c404992181030241d694200900811810381024941e992003d006006903500d0003250421206154402600d40000803002c11004c0e880303019106032071024100c004005080c500c0780942c0725441406101e4101c08001c10000d9081004019109401d800030801841240940c40d001ca00c3e03400503a034481c203080704010109045051030080d06080003961344542003803400c1e000c2c00d0111a200c1e00310343d202c1c4488500b003010b5821011314859014100d62400700b034000a01050070444003884004681c040b41540d002542198090071152041c010725180780003103110305081b0341c0c843c948003802d8000100d685405010a0a29800441d08144989042d030b1a60383e070701a43c840 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671437877 1250 671436627 671436637
    0xa022214040b010f0803280c06050f180f030d0c021f0603150207020303390a0501061a04030b070e0d0b18160302090402040e010903021f02160f0203010908 68
    0x600400707003a00502405490104d22800b40280c3e1004510700011142c442c0c0f00ca403500d0004d84101c0d00d0940c000302c0018480d00c0074214103a4001000d018500789142c021480f150101d4172007010003051a002350700c81d01c00040035107078182c054000e9840c10001c107a04c407002d0170080602c1300035885442c00d048041220300c40c826108020b43c01000820908528003104440c0d401c164104110340148820000b60750007104a440f5800011080701002e1540008104040000b00f24104004034681c01c003c080030012403035000301881200200181078a81c1102400c1c0c0600103030f903002081051006000284110b8070690300314020f424081911581800020314600b0780e10000c03503501400e002440311100c040c41c3d0b055081031520002d080343e085201815101d00d50103200c0603100d00001c40c080340c10754960360310011102800900a2024551b941000307560740e0a070a481c0703105c420740d4000b25046030b2007510070740f2000400a414001d101c0d0349a00ca6a001c01c144850590341551f07100d0b2403000141d02c80006113 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671439127 1250 671437877 671437883
    0x200705030a2102010506011b05070e10050a0803210a021204030e01021603022d15030118140612152505030114012102120a06080a02221404 61
    0x8040b40c0b205102d40900304802107006003560305000501c411683c020201c203400764004030a00d9522103a81c10540c0c03070041305600c1807128001c1d40080c0711400b11035401d550207650050b1010546980d071040c209540340b18126028505886d0181c41042c2c0304003042c14950402c0c031041026051445580043c501003c1c00d0310110b0100b080092484020751b0140a50000c951101800070000f0307246801090384c5408007440700d203003c0480700c04076000b100390a2401601d820080c104e078ac021440c0607001d00d21948207020711415410028850699485039000b170088a074814880350071243c40300400e00483d2411002c01b1030b458010080c02c210307a4248508132921500e09124407002c0721144c4400344034000a0600300000700002000140305048288030a070410038000e180180196400d02c0c00e28008208034014964094000540400400c007229240da008a0100e0410003000f581d4426040e0340d0001020300075084449034083c006031119076116285041480b80380410241d15101d8400c11011040b0b0f011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671440377 1250 671439127 671439143
    0xd1122060e07030e0604060b0a0b030f04050708030a17040c031b0509090307031b03050c0304030b1005180604090615060201020d0f14150406090e0102030a0b010f200705030a 76
    0x20001070700000d208a4220607a03003001c0020080f000751442d12403200078009003046490b8001081c103600c85441d044020846654810384074207100020240c3c118060700c0545a91080803000b1401d418048200c65511200d526010b4000054061884035030800500950b103040180da800070110303030240e102c0d10701c0c008a107054540d068107000412004c894060030500c0b0550080c04107100003500640c0f842350103803540e62540101c10312460101c0f80c506c561034480f0740ea40804240001000384000c200c1e0300642040920b40d5265072500e045c8201c1400314021010048444404142107040c02d902804026000e02c2c0017143e405000c3c4580e0a10224583c40080107079800555050604400d00c0f480b00c3c4040010b409024110f00301481440d5440c0151403500380340e0251802035010b6030385a002c10001d084400f070500c484032861000c43e00030b40046580445a900340300a1076025803241c0c5040c0c01850068540342080c0200b2070180c3c11380d46000201444038800c180c0b000c02ea59030304120030055140303c0c2d180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671441627 1250 671440377 671440379
    0x140715180b090604180e0a05100c050a05030c03090726060f090d080c21041202060106080a020a03201315050a0c020d120905030d09050d112206 63
    0x6031110440140e01c9481850310510048915654080c1120221807191010001244054111200420121101d9081d51003640b500c0c400300a000305099003010140c8100300f0801c0003003c0190740c1403003041d5844000400410000e808010704d040950342000650b01156038031511900700b018518000c404601c007020980410f0701c0d00d040200f104d198401c6100142c80801c0c103000712165540c0002100c0c4c0010f0000d0a000525428100801d503094030109200c1e000c074603207004504802100c1c055030107030788a19111920384a040e00005800341290310b00d546034075140d920070300d521b00250010043c80301095243e00d8950302c40c1d0008080686d9220701480c0361580c1d40d048004c180b520303082641c0400b58140c41002c0342c40c1c10355003200c01c0d40c02d144401d007003a0400e002c1600c00a285003120000041c00d90b860540022100c0384d00c00b0036902502c01c00d50403500820b0342c500c2d0035600c0207040c0c440d05511859004511000034003000e203040e02d84401134092100c0e0030490100051810305000381c071054036501c080c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671442877 1250 671441627 671441657
    0xb0f090409051c081801020f040b0309100609060e060301050405070603180606091515020a02130e0d0e011218020609040e03040e0603100606020307060b0619080a0c081003140715 78
    0xa4404522080d00021850501500443c034910301440c80ac11041510100c009084070905006007102a00e080204115154941060b80000c2500740680fa003480b405800082940c14144a40d500442d00500200341061130a1000c401900d1018604007414840c541039400240c07540c02548042d0503102400300b10802140b8901d81814800e502400c2d003a04400c012019080e00030403100e126a4050300d48082d000044c4010602a10f542c1e00d0b0b002d10b51191b903094416241d800305038504401c01c244d0f20644404000320500041e02e4415810a074502501040d1030014602040202101c041c080d00101c0c118050004d005e003150440da00405440b040403080102c24602440410200002c0a41c100300f92824403100a51301e008400c0010541d9903100e4402c0d03009e540315070a50b00c00c41d4229400c00f4402e18584002400c20700c087c0d404c960a40d05040c16500282d02a010551203050800c4000003c9461921100b071901504100c0c1000d5016004010a072805402c3c03e508883c20307991280320003009108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671444127 1250 671442877 671442901
    0x210020d1d06010b030414031c1e060515070516030b040c0b030f0a0b01090f060f110c030a030f12060b0a0f11061302120a03180b0f090409051c08 64
    0x1c10300d600140c021100500c9551a8031044e2600290026800180b0103802a005445c0d0b11034850b4400d00140300640c0740840c0c0d10b80390400c078452a05d02d8414041d407842a00000c0c2a141e43c0d0003103940c004240840c1410f00384006000c0d01c000741c0074000322404050380d0400391448010306d401c00d0756010202010801480404024100245041e0803103915620b8144882d42500901400c0e129044d0388070000300b15036038400c50500003c0e2a00481c6d0207403a50f0f076003801030308500408c4c8146020403800c0055991400e404503140d0030b15100a805050712215603a001c60701000721244a03014001e4488400d07c20090314070650000e4080d5820f0142d17550f16045020b443d805418080ea0100700c01e06008040d280030102e015038002d040341e0880b040000e040c0c4006001400e0340000b0300d60714440c0d5000700c01496400308500316105031203800e0b00301d91902e42d003400949115a10400246038800c00032140c19040a03409000140d00600c1a50940382c0501d80d082c081600d200c4690000845440900c0040c5c07101c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671445377 1250 671444127 671444171
    0x906040f060225171f0515180a020f0409020d020304061a15030a090602031006032003060d0c0839030c040c02071e0f09050123010210020d 61
    0x724200d0300303c002c00035009903a8200d601804629100c0c3c040e09440c0c4540c03c00c9290320041900d940c003001034083c80668401070900b218601290012001042c44500780040807001c11030700003403440c1030b81ea03401c00f04601a510041241c0e2600104020010f121b019506c060195032b04841d001590300c0c100303410854242d4800c513081ea040304040055000040d40c40306081443e554444507800c2c0c40717070b940e4000f03d07009110000003e803455000108110440c90042e070310720b00355100d60b01c0402903203850524251200880311a0700880c190200040760b4285007940caa40b1900e8032851030065100d4440941c0c60511403038104500b010700c0390345c2d0a522090500001d44000200b449e215915001c02200001c0d9201c1c00c03c581c030740c000d41e656050b079070213140700b40700850103003408000704d003003100c603501c1c0005030b1110324030407811048a8802c001c01e90707400f18015541200c8640004d1040031410400d40b007841d030086444c850661082c40034000b0344c50030900181043c10740c5808000f60b0004080c691080044139 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671446627 1250 671445377 671445403
    0xc28020c090a05011206090305090d03170708040812131a0402090c0f180301022101060305160c0201030e01060f090b0a05040501081c0c05031c0c032d020906040f0602 73
    0x3d240044c006a4945030300d000550f60000004205e103201810706950512602c0f2000380c10a56000101d002c1c103810030f0320444d4619542000c0141556000c1d800c0b1007481d0240d034020a084801c000c1010b22403d2000c019400c854844000c2c0c0200c09940d6880d8800311140b030014010443e120100429840c00940c070551110300e4140c40d910781820b03801c110308e5920444000702a440d860b1001071026460941c1a02d8000b0070a9a1001c0c0b24100200401c11440c0240308000000307080c8030010b01120300050020100110640321444c05800590040d0040c14102075650072541d607540c40046c080302d25241034401032031104000948503240006225103041250021400345007010010402c041d40019031410401c0c5c0041d8641c001004008119544440072001134000e10002c1004007040b6000e5100d8954050701070b10400c0521002e160903011751754411308000b420140c0701e034156002c0081d6501e504101e0141d14005141c84110400114590000c0c0c005032100b11443e0401d20440740c04200901001030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671447877 1250 671446627 671446631
    0x70b1908090a02012c04090302010617011a060d020d050a0615090e1f12050c090a15050111030c1009050d02071211060c010207031e090602060c28020c090a 68
    0x442c40d000030382601c0801c4020442030f580162403414409182d0a81442d1040003403060200c1344260030002e01030f01090140010b1a5418942001042ca0520403918000d20340790010b00043c45c3c41c02000480e030048104400c01c00e8013045400d6454103148585403044c041e246001440a062a104024509004810390207120345540203006619040c0003066019102106904100d000e04040c1094130080383d0189410400ea828070104010b4041801510b4030001d8401c1111030351603440e0941921120290b80590721600321041c0403d51007a44071441301c40445049a20f460001101a45005841440d1200b80ca50714421801005028442074280c8880c500c01031044904000c1d45510059110400030701081c14000007100ca501d1320400d0f500240c0b5980300840d160388642c00c020300041302d150750b09116520040c0d030154000380145c1e80f00003610056402000c40c1c2c0d48100529059902c41008a03100f14088031400b01468040c01c054401c2c001ca0f64042c01c007407001c00003441001403024000040e024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671449127 1250 671447877 671447893
    0x9060e0120210403020c030a030801410120030304200603390d1d12071103070b0d05130f0b0a0902041b0806090907060f02070b190809 59
    0x8048070301507902c00090b003000d0440c26200d62500303901e81544c440c001d58040c018000d0340000d040d00300030040e040759584c460b4401c0c19054a212180c1c1c91042c1010003051904c520322003c240c2945142c400301152040c1403070280f408694540030b89021801c031030125142d000000b0031003007181c1c0241424032070b90051081143c151034030300006c04500000340000381d44040341c4082c1030b6070709902c4c00c8419151045811901e10300400400203007154000044c800c0528244204103070218070710200c0702c140360072000103090040c8000319012025401600d00b80d034980c6982e1301c4071710959018440c06000304809048150fa9070450049002a40c500521100014000b0044100440c40d0f480c00400c0e000c0d4000c00503142aa600700c0d0800041c0a12400039400034507020b001c0c2b5515101140c030010f07001d41600c600613a5603480c420041062401c580b017048940185104001e280e00a5000b48928809801036602da1070306e40e2400b0b5055004918100c3d9140c020064400300b864001404c00c1e080118039020740484 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671450377 1250 671449127 671449147
    0xb09010f092a0507030309080d05010302040b180a20120405070905010b0a1115041118040f0b0402150703171503070303050310080102070c0824010504050a09060e0120 73
    0xe030129502c107000d00c80c000410104142c4641e010748034580d07020048a4941c84401441c2000300400d0008900032807070452100c2a03803a26030302045503c0354004035540950707940d0702d0301c2001c0c00c0380815104110a40700c552202c40d04030345001e44070004020f40c0c1201d20346002c1c00c0a5103001c050358002c0703455601d0f1500500414940710200d51020505080004800c010701c0c2c03207185850300c1e070740045030034440c040d05000400c040ea0809100ba2201295514004074081021800120041d2001008913031007408100001d1001010700307901c14002040c0d0b281d916001e0f01d00740c56903404070b00204d00091b9101242140e007400d111040d40c10044010b0601e003010044c601081c1d84542c02d000160520901000269401c081211540d000e000301f0b01c001d46d00e80e40e852400c1c6103140d009005030007160243d06091604140780b0107100782aa00c4000d650a1315910300402d00c00107101c040d14400c40c0f00d48a800d00004a000c50081c10480003c810001901508031403210300c02045140c00350945070001c001007510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671451627 1250 671450377 671450441
    0xa12021c0b0c090a0305160f0b0a020705040b0f031905010f0b130f0e0d0507050606091006080402061303050c030c10050d0e0312070513050307060f030506040b09010f09 74
    0x1c0320424100c80e940c3d420307102d000101606803640c0010850310403c0a400440d680c4a200d03101103e02000c10110308030b40b03505403081c8901079100f0302001a072201f50104a41c0c40d1542110b82e00a8002d4802503810241402107420600c042015880060400341d0540c01c10009200e0042c1c3c0032542c0c0810800768000c0e83c0080c038050740ea038124601058543c1051101905264000b00242240600b19000020f90440c0580a900423000940707180c0118000101d181c03c0c8107017002e203c0c03407008003840c10090500b072050b201004040c0c02170b0380001013805003004100e50380001c41e018500a03401040070700000b90400d49452105072045010312000b18804c2c1040385c103c800c2c1d801142d400d840101c1e4003182c0322034542c50350003041c7d82c045159810f40b0034020300c140c003d0700901d61000b02c200d183ca01c281c0c980080c5680e070302c0140f01c4c00c00000c102a1000c6401842640140d821800c010800700d08001800c000590030b12081c1c1182c0b01d080d103840d8041000941510a00e80c40c1400d103541c11000300320081c4442c403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671452877 1250 671451627 671451631
    0xe1e12070201111c0315050d0203120310080714040c0212040b0c19060b0a0807051807210b031603051005090a0503040609212109050a12021c0b 63
    0x1040c8010b0f040f00f07210500040c002da40704c68100448954628000b408000c0c0500203a840704883c0da008520041201e0030011801d0350815005001000205240d0706202602d1344002c080c082d04600505021407800414050351009112403c0600340381a004410001200d21103050b090a643c003282e4420030b80e900040c00e40b022102c207141c0310343d100c18080c0c01403410200c1a0301c0c00a005400d030240744040010030b86c08058030000a031b9a00164680390070456940f01c04900880358000c01c0c2441e44001400e213441c8980c0d00500628110100180c510507040301000c2860780325441ca52500d41183c1c050808100c4040281ca006000414540c076689502d91074241004150010030f807600000388811008200140d8640da012007101e55130756842e0380c001c090350150302803809004054240b141c850340c03541c10802003454215500f07052140a2903034000580541908010500c0801c0c140007070f1582e1811400740040100441c00e510701801da00c108000521b41040011120001c0d130040d50100b640c06010031307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671454127 1250 671452877 671452879
    0xb30071811130311033c06040f0204020702010e0612010305012007150b0d0506060405131a06010216060e030607111203190203090f06070207060c0803190e1e120702 72
    0x7600400720804241851400600600740f0016030b00c0c6c09410a411807000c0200c5443c240095540c1000c4003000d82c1c581009480c040c009007158000b1401610f00f0303500800b03a09205040400d4803c8080d00450030a421030788030010b040d20150010030a104080c0214000c0700625081c052103040c1401b09818680103034203001c0c200740007d07000f00154400c158403640c01c04400900d4842004031902d00107076901012119203006900b400085104281c03d5008600303007075440501d4001030700c1109003850606400070401411132080d4400c1d101903003442e000b50710142c01241d441c03800c030781d0000061614007000030300446c080140041c19101520400b1a403d5840c031010344000d076480c0c40e9044003501b10440c107a40d00769514070000c10300140c50f10016540b0200301010040c4c4099960b43c0c08140e031503464030302c00c0700c0c04144545004400500004011640558a041031240702482c124107241268040c80500d00d042c7c0c403604d0794074501400507902440d18035105c2d0013001ca0860941020100e80140e00c002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671455377 1250 671454127 671454143
    0x2040e031215031f0e030310090c09050109050409021809031e1323100c0b060a0b03190908040909021201020406020d080915040507090605040b300718111303 69
    0x513840c0004141c02074100508020308884d245d0502c800c2e01e03403104c88244100c01440349807012107847d003806800d200084420503154664400d1406040c04003800300c15108980c0289190f0502c09084c0c0481442c0c0c0c003440c10b25008645610b007100d90300c9441d43c040c550b5050001c0050041070a42056034104005035048120225108400c02600004c81c580d101c42c047e40c0005211030744991203600c181c00c440c4030790043c502030f00180c440d0000e011007aa2640901c00401804200007240d00da46040d803980f10031078400c0009482034a82d22001c0d801e0f002600b00d41c079000e46400608095240c0040c1902c40449200002c5240606d090302c081d40e00c0002c0c0c60305000703110460b00052865a424071542180700034070b103c0a000352400d8a48139440369510b02a00140704d150a03004100790506120b00814100060405a05014061001c0f096070022800240014240c81c00703954001d4024400b101c01000403130600317240c42844100000960b00310210700c9c504002c0c2404109080800034407a032040340e41220784 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671456627 1250 671455377 671455423
    0xb01091203031d06090604030906080403120209030a02060f09040c1e140403050610050316051e0f060f0d050a05060d11150c030306030c030d090603020d0902040e03121503 75
    0x403c000d002001c1c60039209000b000c0070010326800100381c00384514881e80e2070207849900d900c4c05952070201600c01400141115040c0460303480c03194003c1034820301c010111208a5065400203d295000c04c040310380e81c1b1300125041d0903034105405034044102443c1494425443d041000c6142c8003441c400001c20000d41c0c00103001030b412203208880c05540c1090680341300d89458010f40702c2c0c40d901d41c4030703190107486160341442a09141c00c00007800c1d10402004d21110b41c038a03100600d96903079890607043d849030640380c02119940d111401400301e449003407822a02d560146c8104411200010b114a80c15403c01741080069980c5a5002c1344299000f0003807080c544552004c2103a0700d034107248041a8a00c00280080007000002c05103206040480803514100c19140515480e0802c4008400200e10960020303c419030080c0c02030481e158081d000007030184080c0d00014195060040740c0400c0c0c0c1c00005840e0713020030b107803030042c0c0d40260664a8602d0340020100425521510795032a8000350001d024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671457877 1250 671456627 671456651
    0xb090a1109090a092607031404080304120c050a15032a1d03120906070f05010603030c0b0f0114120a140d18080601090b040f09030801090b0109120303 66
    0x795400c01e030000c1c062050901d0408000c0c00101040c4d40c00756444040300559000c0010145400d041c0c1201341c031a0241003d0781c6a03010380d16001e0390f000c408003680051002040320001040500b0040a0030482014448403500304000e0300c40c1c8542240f800340744890360034812503103100300340c0e00a000ca03407400103000309410881825105010f081c0d800c003610720303142e0020309a07404150351603480c9880349991244007041003015a03500400030281400e0500340148034440c5083e10180131424020750b8001e000003400d540706070071614160021008902220707070038802c2c4800c0202c2a544181040c1c02405a541030030904809000d4060006d440f071186c0d04a02502c2002c2401041c07400d035070000801842d00b1038903d126480301881d00c2001e000074107601140e001540c2d00100702040362400030240045900302448480a068040f11a5400c5910b815a24442d001d941c843c900700640250348035000b55040103114010303200301d402c0c1d180c10000d0800c410702c10041190b010704416a4113007400112015281 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671459127 1250 671457877 671457911
    0x41b0b091516080c0c01021b120a0602070614010501030c1422090c0807020a030e09060402070506280b1503040501090803010603020a022b140f0a03140603010b090a 72
    0x40409200c0031120300d02c0104140f11029000d03c4182d84103803400b0700c0e00c0400481e51983d100511003810184582d4107442c1c1d040004611011b40c03c0e00003610074014503622204280d9109000440b6403a50340c14112107818031a8030581e0140c00300740f8003070044502041c4010621403145000c000701110014910840d41102c405003103d541d0756a0300c08051030354071441c4d1001807040d000284003142503000041c56041c03012071540300c266816210b881043c1040c005008158030010007144c0c100f542040743c1030108204015891069039a040f07590b164502c0440010360000c20352500e10046130518440e01201d542c0c840301d04598404898007540c5a640d01d0400034090508583c2c0503041e41e6000001040f069410303001030086c108541c003200d80d02c0080c1608604900e02c42980d240504202c0d44580090610039003d0580210440d4040c0e400c01c590f15146031115031149100c500440d1751185405c4030550f01503075031580007900b10020807000030228042402c00074000c0c160113507181c3e01c085030501e4661031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671460377 1250 671459127 671459137
    0x4110f04090507050307171b040906091202070501030e0d14070b0903040306110f03010b091f0e010801080d0203030c1303171b0a08090d29041b0b0915 66
    0x1801801031a03010308000d43c40303034800d024182c041e019100c5c0100d00b0351150303608010018070000061218081018940780362490010b6100d07482078a880120f0041161409001102d40c0100a0070124071101080a403400030395500840c10b15041100c1a688104040303034051920b07007107040c20081f20254030140800c510420070000e148060311414082c0c0d0540000c0a402680e102c8c21302041b0030070512083e00218011104d100078640c10801c0148518124500a4030805a000e068511440e140c0c5120306900c0d20020850700000e82407407560741c03072036034844112401443c505020305103000d01d01c2402501d03807100801c0c40748060400036181c1c4040c41d81c4421207006540055030003c070844900d2111216501411440ca500800705c844034810400100f1600320309135220342160301d400c4c4100180008024018400d81d18644020f240945071840308403050105100b0f2940c018a61600b494811038802504d9045036610070b04c06420b00c001541513044440d071704801c50348000542d07186440359555100d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 671461627 1250 671460377 671460379
    0x414122a12070e090f0a230d08071713020909070b0309011b050307120e030702090a020c2103070309061806140601050a0c06020702030304120b0a0513080304110f 71
    0x8a4494006401c8001c00d2000680710503400007141c640360300c4c0c2099900c1078141c01140a80e08460600340c0052016561901903003101100808404a10000c0c1f508181440c000c00c0081b915441c200030103507503c5241700703c0c62000c507100c0140303e083c640c40300800120209802801000741d0340224107124401c01004d03004207081081c495603490040d0815000c1c220b070445a2041180401518074010300400039248280169580c3c2c07006509510084006410402c3d0301d0203003400304110140141c1c44060000b40310705003100c400342e5210000340d4054548040081ca010f00194071004180c0d5400c80c840441e42c010030386140108098000781030600003854081d0220118a0b20080010200105500846c1391606a5032294a0b560385820064a840c031a01078104000b5a0400010000900075806030150b42e002404480c103164413241e040c0b6103010810010341e21214043c04000828089005007940200d0b058440d039101c84030359603440d01500014200501c118408110702d101d035110451040c01c0d03100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 671462877 1250 671461627 671461639
    0x70b070e0a09060f0f080303060103050a1503051e1c0f021527010c0c060e070e0f090706020c09070f0e090c0a03060e04081606061a0414122a 62
    0x260300d51450b4020880340c41398070f60740d00c050711001642141302c0080204448a4030003452131503881c44011401814010091090a41d81e00340b4046a0b2401c00d4500c0c01442c41071001340014581801000c540c105011304504103a0310444244014a1500488000e0410f460600c000520702480c0b06a0405603c1c0c0700704092801654100003d211004412040d0402e0700c0d8210301e116034400c603100303007a03890008404d00820000402680082d4203a0f116114005004080c2c0341c07200e4589024000003c03080d1450b00b01034401400f4098441024800f50b0000e009030300041601c2907003840814010f01006210805014030b81ca210801180560509003480f04000c04800d41407800c8001908241c012181681c0024030749280841c800d40c900e001c40d070085030020846402e1659004a41d01c0060303880200b03d88880d00d66800242003496080d1102c0c4010002e44055200d6041c551845014410506014841c1c11081c004d4540040b000c40c070403000100f210a060512881c005440c40b004c00c041101c103400031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 671464127 1250 671462877 671462879
    0x3021903050a060b01030b0f03071e170717070e010515190201020307090e0c0405061b01050a0b0411030709090209060403020d1208070207030c0e06010c0f1203051308070b070e0a 78
    0x20510394459004c10000340c0f010407810f110321082c854403003040b01a168040d40710320b0080c0b100d0700031100c116100326241c2000d08481d603251015160380d0781c008080c0c00d07805c3c0c1c4841d500780b043e1403540c41ca03c008980103000510b815440d0074103140c0d400340103106960003000311032007100300e4030300840803550401d10b25400800c0070ba1907550001e000350300464040380000c4000c2000f00c3c0e054403078903880b409880810b0489042605010030407415910070242126070400c1401ca44a820200703000c0c141c801e0218800001d28446c200c42400140c4100413400c0041d40000c00c00c000591f600041c4079001d07943c080800507103842ca0360020952921468101030b60042d03202c000402001a002c0245000c010903a642c0f40e455112004c0a030383e910744078080200844a4540e0a004d1510011010b550000c07051400955410254444d00e071030310058441501c01c51401e1000c0c0d00020303094020541c0145427032505400d642c0d41d40d00c42d045580039801e001400315010001098a2078031030308601d241090005d003401051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 671465377 1250 671464127 671464133
    0xd020f042c060a12060213030c031401050717070309141213060206091c090b0703030e010522020d02061b06040b0105040b010509100908030c0f160f03021903050a 71
    0x5410510084070a024500c0005205401d0464500003101c0406040c0d180e1042c0c40d50b00d2601940003044858446014004000b001c6041d00150f400114010451a420300714290005800c1d2440101140180021501c0300b841c0180103450703440d8800e40515000400600c07901d006074540d1998440442e07644200003c0c0d03040034403402e0043c44c0001080a01101d007664078001641c94900440d00c10449400042c005d0b240d0915990503d9030700d401a1402d0406262a16140000d40c2c000070800c4c1d0000343d030b038541205038250034400c4030f41082016070f94000b25103a45858104011200c40d00038011400280074a0440d1100419a0250b03004042c0b10b03122044041881542c03500219410740e000d100100000800c2d0a0500c038500d00d000c03042c3e6072640303424002d201f401040020400c03020304000c03448000103000703407090002d050f07556800e90151224000388070190b032070000d0b0001902d403806058441005440b50081c2c0e940c04990b41a2041030b01e01c1c8500c4200781c03c000d5642e1000d04140520410f01b420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 671466627 1250 671465377 671465429
    0x612010606050903070e131e020405130303230106110309150c1b1c03110105090c3d14040602010501060807030504050d0806150d1a01050705030d020f04 67
    0x4061007034007100d045d40d55981e50766021600640e0100e0204a65075109000310391000c024440000d040380d5035655070040c903030104081b40c80c200c4002c0c20303410760701e0001c004055160280c001e800001c0e08903c82880443d82e5084242001031049409004804c5522250f000e030500594006500050441304491008078400c68107030301a808090b054010198802501204d87d1994081d80750302500302084141d505800c4003000c3d402080640601082c00b00c1085994001d0081030300c0b42c008240500301d4461840c0501c42c40c13a0100c07a50034401c40000280b20707442c420700c0c113269013441d025140580351414205c209031004400b9003010b480300d5000060218070a90150001d0303049804558030368066030b45c3c0c200110100c13181601e0082058010040c6840d280344241c5059420450042401110b8103201c242100076a00450300e00000076258801d130090f9404551240c4d40c50342c0700782045450407210740ea490751a4800c169240c0b44459010414120b001c280070207130b0300503107803404005044201a91403060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 671467877 1250 671466627 671466637
    0x1801030b010e0f0103030f110d0306030510020c0316020d080406030207170a0509041e020403110f010f021908040f080c030607030605010504030201030b0d020604151b0b0708061201060605 82
    0x1002011031000103245000308510500c80c80e400801c004040e400d640d401c4805c0d0701c0300044a01000511802c0800c0380f541401620222000c0b5180010018918949181055803101d041050644140407040d41464040101d400b40c000c10f085292210b01c1c14400211540b640f240041d20805000c03c0201c0d108d0b41550040851074001c0900341400e00003c480c3d140c02c1d1003414101c00c000744044c0000c98080c10903402c00118440400c1d0151403090f48400300b10200e0b0031561080e034030741001d0346011110341400c0c0c1840308204000e10f841e0780220301c88107011b90395900024084e01005144030180701407000d407a06540180940103042c0f000240c0c0c50240940d1107030114803d0b03129025010226480305c1c0284030700022200103031583c90400746150010340c0280030805480b6004810b403110240140d031960000c0019103002141503501056405000b011104d0368a41030200386604045400407070400c2001c0c550044503440c1038030316503854001280442581c160000303025800c2a1f8081081038002020349 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 671469127 1250 671467877 671467883
    0x1104090912080112060f1b0c2a05040906060e07180905070503041532060f151312030906180305030d0b0303094c050c1203010308070c090507090605090f180103 70
    0x1c4040c0e081e0509d044503200c1e401c00046000d0810100030445420a80c01030b428040c081d18002444a0b6183e840301d28911089503e18001156144c0c1c04185101d03184510005d80300d183c1c1c003000140f03000c5130050a180b00c0640041c0a18100400c6041107620381d410a009843c0c00c1401c182440c09015000800102611411103040e00800001455410810b6030781e00c1c05000100081d0100c800891055100c1e1710104207096544007002011561031076568007250250321a9848594541c941100200040039072060700070f04084880c002c00105000005a032182d2401d4540010940000c1000078030754170410a040c0c0d046020700c40714400c00500e0041d102c400c000b00c020040d02403040100c41200c445107180c001c4140145030395401804612035400361543e1948041143c4215503200010421604260f2003114901c1e8001601c01c200005041c8500082880e0329050055050601000d04000b00d58000e0301c00f080004105810700340d494910320b03154004040c002081004400303108450b4480240415 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 671470377 1250 671469127 671469143
    0xb09090c0c0c01260103140706110c0613050924010c02130e031303080a0905150306010c031b050703060b010f140c011104090912080112060f1b0c 64
    0x10401541101198200101180a06802d41e0381500540d10700c07900803c40302d52140703000d10300748403800d81480302c9001c0c1d8041d800300e810078908901e0300c40c940f0065800800030424007400340d200b02d9100040000210174119202a21010081d1070707003501d0a00b5601c0b0b03e9000100c101800036441040c81810f201c003000300409141a0700001c01901d200d40ea002c00290802110780400f2078842c0c00b540040100c4921030700b9a4a07250700c08400e01030050141d0015103c0010018045030226003140c0b004008103000d407071070b69240c0c41480c40b80d040790000401e424180850ba66a4404061140a00e409040904901031590b98441c2c205960303100080d0004941aa00d001e1001c005580240034200300c0410641c1e034543c0324196045041c226800005484845648a005045070000500e0190001c1c0030403443c0040e0f02c40e00780c1840300503454084180c9081c0000200180140100c50b4003458080350406402b00d000c045000c0c3d150010102600700318044139401d110116456480945840043c2c000c0c202 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 671471627 1250 671470377 671470381
    0x1e070212060c04051504030503130801050708041505130c08010b010212040e01050d080909070305060118060815060717040e0f060f04110d0507050c0d0905030c01140c01060b0909 78
    0x2040d901d41003680c11100109081c4010802d910b00140c0003052042060045810140d40395185403564000410281c64408107410a100d00d031001d103e10340e88000c5510348401c40f414507031188201740d05941500c66203d45c80d04005411000880f02c2c8a5032694024294145c03590b43e00c1c0c000d4000e1175480c1000b80140103610305010341e8010881980d080c0c585483c401445a4644020010715131a000000c5603d40c4060000e14640ea0b28102207920400b17a84e01d003c100380c03400c0e00c001406030b90600034544d082c040a42d014404541d0003400541d1080321450b5100b90000f03c000020406d0040050040c02c150125043c040780301c1c1ca100203002207a01c40c400543c965203880d418540710503012690385400c000e5007080d8002625050304000c403030000b425904c42c5070910741400401550401c5441d0400b180d4009418150054208804000749601c0c0c600410800d0800000903120101707040c1c2581000310f0018030001c200c281104030b0b180d80700c0c210000c1140550300d504d00510707034001c0800248240d080b000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 671472877 1250 671471627 671471659
    0xa0b0c0708010e0d0f02070e090106090f020c0703350d05010815150d051006051005160b2e03051603021c080f0d140105030a030819021e0702 62
    0x110511101e2102c081c00e01004c3d481011207452203240d42200451103000800107c503881590503034040c050120000c42da86060002e06020b80d0607007426000d100c0e2042084520414012412800b43c4c0d070b0080c3c0e00703484018000200e42e5504080074a0010701c01c0d8104c01d40d000200b0040051900c20003484050240381c3e650302d521500e400400b8400c1d0441786000000641d0041040fa1a40c00004000c1c880d8802e81082c0d10744c5403908420804104c0c000d5640d003401e01c000c0c9042140420101d8603807615a00e01480100e2181042c0c081400051000d462840824a10614407120240483d48090380749000c021002d07181580400c54401a5014020900900d10041802440000707403500640300100404a084600012010204d0300360b800200038880e502582d0040401071070003103000e0b4004070310045d001440d60441003040e44602c4c0310354003600b00c000010740c11800c2d455000d85506480a06400352071041c4000c0c3c0b280d2050001d150b504180025044a10003000d007460b14000d07142d0b4042400c80c54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 671474127 1250 671472877 671472881
    0x5070804080706050603031903020a0306090e280f120806010c031d13050702030405040b0901063c0c05010507020105090613060b031504120203180d110a0b0c070801 72
    0x5140078045650410081000c583c80e90070594122001804481c0b500d00f6900750440805d22026139840069000184640708907071501681001c1c289180041022030410221250740d40c121240b804004104801024917402140600c01c00035900000203500c5054145018480c130110920f45402141ca0344001c544a9482061044c030f0300c0e6416150000d0342443c6010080c004030b060310904e58441c900c00000300b8000710380d004007401020241c0046440d02e041c0000c20090341c0d41400082d02a046400040000c0769000c1041c00c0310300702d4180b040401c40c960056104803105034519980d000102c0404c02c1d0710302d0354041ca8010200d8040c000070400f81d00c418a049098402c20f6400d900307154401e4001c10b01008141c60100b070081d11601000030010fa40c1d01c0400c1c141825007900340d024816050030001171101c89000542840c149201030f51400c200c10001e425505014102c0ea4010700b0701c030302030608018028000c1c10038510003c04c5008030301d69400e03001100e0391290010340200d01545100180443d014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 671475377 1250 671474127 671474131
    0x702031c02220806160f0e0d0f050d3b0a12050307120203131a0c06151519050904060b0c1b010f170a0216030309110d110909032b050708 60
    0x1d603109145403c1180c8201c80040c01c0411f80c0790300002490119001500f40038483c81c001c1e124002800d004c40580c40042c01030b42142d0b4091481d800b9102c071070009030190140340034000740700070ba82400761a9900c01140440c10a600300c180281c81511548080c001d00101500e0000c1c4281408064800ca00404030b880f40925060701502e10318201d401d0020708c1054500507c4813203421009801c240fa103201c05850400f05440c42e150070b20740e8100481150422541d40740f0380310399001d00745117018049160350200622080d605400c0001c0400c00e00d5403662640c11800081415410450300e450f5004003d42c0c851036030410502003622003100184540d4000c0a03d91094038054813144a01c0b07840c48800d40752030300001c24003407048e60308104001c01540d944150b510428041d903000102e0700000d00e0007204200e110a03005105280740c600c03800010315507520585800005a0780c50160340c94024040c0e1a41c0074024180508811841c1d254041245101d4400940704030610709110507180c000064a0300501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 671476627 1250 671475377 671475421
    0x3030e07080a2312031906081b06190815010203030702190303110c010f0e06060d031d031c11062e030c09090c050402070b0612120706050406050f0702031c02220806 72
    0x4103081440480c5071058180278043c0000e88024503003200b9034445201492040340300c601044009007480058821766400820511081c0021851800c10f510080d5075440030900d40c260350501c247d100b604040c400d400c403020b6861085020340d15801c0301d0b01c0f528041c2256400c22480a40f8268074070020100008816002ea8009003a4294035000d549040710740100d0b410044105001c0ca84115200751000c01c2100d1a4841c00c11003080c5040a21100503e2801001300b44501c1d07a1000e428040c00340344044049c0300038a405501c0c90075102034aa1000c8802245520240210300d02c0040014000c0168126280d59480303110400d020a4950b01004128000c004002c1c02d030081c0c8400254440c1007201d03c00c55048615001c890340140845883e003800d42c4888021650750b501d800a0208101d041c4c0079441c2c010030300d007070405068944490020b50b640204c0c42c0070728055903944c0400c241ca001c5941164403101c0c84200858802046c0502110616001e1103030071902e214020000b0340c1c40c4803002d04200780c40d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 671477877 1250 671476627 671476633
    0x40806010f1404200703140304030201140711062d1807060201050103170c0a123504150b0307031407120b0112030e0d03090303030e07080a231203190608 67
    0x2400801c4d12074000100460911070845040d16103000043c0195208030310a03400441c0c083d2114540480c150741c060101010320045250b5107651120104140b5844186140c050308a0800c521070159203040c1c800c520000220ba840031320640800d0524a0042c540103001180c10707040d600d0200300e01301d0f4000d100251442c0a9442d0003682501010000c041c5040070780c0440f49126450380f40c1c544c0d90a0046100390100d0041e000f02980d481446c61564584a012546006c044e2400301085500340c10007400100f103400060000b030255184d61703114042c00c4001808076640c1640b08d14110035800b2040902d074580d8030912000254101c00074550100441d880004002c90f03034a00103180c0c0d03032010804000c9041c0054500700035404c0c1c4aa420390448035000c1e50b0342d152100c0c61418041e044175044c2d0072180c1203030800c0d1010300c154840041c03800b624aa115100741c00c48dc000b00c0440140b203680307805150307ca00030b64101c00549900e12025500075502c405010001c2c1060000c0315048542c60700c030718501a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 671479127 1250 671477877 671477921
    0x207060504050402070305091012050609040308070f05130e01030213050c0412020409060c0e130203330a0b0a030b1e01300f0e0f06010e070203040806010f1404 70
    0x3040136005445da203032090500905080e41440002d00c0c1d241e00d10464400035040944071030640307003607014040c2c00001c10346144059007400d46000b000c942d00104008140300210807800c1415118508603401100940500c2e44e1160715210303038100034907007840180e22814982c01c1000041010384109406080c1c5200602d28061420100070104440b00c00180d074400da44041c00004601513000c4c40d440340b2003554450003040001010851700e406101186010144180100825040011040e911031001c002d42c514261040c1d040d860341841024103100e4004442d00000140d9502c40c00180103603010545003030022031046001d00040310604000121000d0325039841c0c40181d40946401e510641c203120004440b4031030703041c0968800d030103048078490305580c078034032024591014030601e031110440401030300c03140da1045845961000103009048240240c80701182c41d081c0204202e07001804248141c1d400c1e580d55a0495140300c2180c840c1e516207004d41804500603240c2441703144203c2c410300c1c140c84060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 671480377 1250 671479127 671479129
    0x708040b100803040f320609040f0c08041203050f0112080c0a1511030f0a0b010207090c030c0e060910030f02090a080109060c1e05090d080d060e0106020706050405 72
    0x10001a000c2150141e05820214180d00107000400c094401011014242c3d03103065100411002080c05131107940884044030701814020034891200d0f9201244d10740c0d00e074031081d8001801401024000001ea0740341407601ca4a003a0003d00070b6102c3d5014840142104941c00d0040e401d5510132a1f0911641c4441c60052100355400011280c420f03020b91206403e04000f400058502404080c040c1d03203c2240e5011500360000502441c1840b4040c0300100b4114140036000b1880700704094040300b4626101d500600c5d03141d20030440c100c014040004c00740264181010007030002c1039031041d4440010b04c00112150301e810039000b110200c580250400c00c2c85a44094102c00030800d44040541c41602044403030007540d00e00c0e03201c1c2c005e891110300014a40d100307841c008040707604040a55040c41001903200f09803d14118040342001042d007809651448002c0c0000c0c06404100d800904609010074590481c102035403000e070944e60340e82c40f0030f0b5070b0f0303600e032001603a0f54101e0f413248100042c420801800a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 671481627 1250 671480377 671480393
    0x7030201050d0f1416030b01140904020f0a092108070f0c17030334120b0d05060703290f0f0607050f0c10050a08071e020708060906070804 61
    0x200400801d00000d1200d403d08404050b1961a08011040da441038180180c50140326640072030400603042c204410001100043d08004d6150444818010040388072b42040d21240c0481701a41105400703103684a42051024061308214060411980c41103ca04519100d010590208054001c040746042c1016544c40d030415003e000c10484400921078400505a000648000e0740209004007031900ca2403c0340d0b00700900d003080e8503c5600394000d0541080e0000d130a0131f19070020215494905128003000384610040c0460000e00e0390410941c0c0c81803010300201040d00d074040c001941d020b0165620942c084840311246000c083c3ca0054116244c0c403084c50405514060200c2c06003189100e940088001180c43c0c02152050710950420f0f0b24000960406200200590904980c2000c0181e5048401031003400f541d00ba030703414010324a011404082c006c85c041c4080719000c100e240c404501c0c0f100000d403038410900c505c46103132186e00c0200e80c21f058003054175071254801e03a44205407a0f03602c0d111f1440f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 671482877 1250 671481627 671481637
    0x60c02120708031e010b0a12200c030408030a09031a0114210303090618060f04080c0c0a03060b04061703030a090f320123061518010e0607050703020105 67
    0x24035405150b14001d10425041041802000c1c000456078480b40031f074001511880913801248001854400781400b03110303007543c0440c00c0300506890b280d150b403031615100703203184259080f0036030910022030203004e65540244500140d902c00d068010044031102c200d03100d0700800703000d20110196030f590031403001d0500c80d5080d5824400d141941c81c40c0500600c0c02411070348245d50520135500100104004510412400700c00459114010002464041c141718074151000d84000d01150740019402d82100c410401d2103040c00004101d4901540c0c1ea10f40f29000b01101040240150706022000400c907144c0d1181d68a000342e1440910300d517655072448035001b80003c0d6000c854800b030701e0008002082d1a041407546c84c410130302c000051310f00782e4003200170008100040300300d180e030502e10202c050300c115408240c09204207a1704410340303441700c1c000100c1611440b61001c000100c0400c40240303424034030b03081109244c02a22452039035950801400038034450f0004c050000d40c8060700410055105000520b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 671484127 1250 671482877 671482891
    0x90f01030f020708030f0109151a0306270703050603011109121f0c140f09010c0201050c101b03150612020405060c0a0203010f0e120702060403051504060c0212070803 73
    0x180f07080441d0f80c0314091a00190b400783c1502c0d07900d400500c0341c2d420500c11041e0b1024494040700b802d07032512001624007488008005441000440420b01076242c000c0c1c2401c840714481c8000c40380d809500c0c1a03503883c0408540410000341008049200c0c2d0906100d08000c03101a2030300c46141c4102d00c2e0522101d8802031079a11428841c41c13100780341884100c103400360417240d00e0b400440d40c1901d500e00280310b400c030705601002640d4104142180e007a90402160440d01080c2040394100c0e10500041c3c3ea80d00a40042d00007a006043c110041407006501060b50038481441c100110340c0c4501c002c4007103403110a1007199400d00000c0c188045401054048410110300001628054580c404900560008080700003141d110a0602046203400c0c06500b0844035161030802000c0e5520003196643c41409204d210302840c000703000c1c4250f4541c0c0046a010310f0300a02100c600400e1140da0880004003201c00740c40e0189002c00c6524450302c0414520780c0000b900700c56600b000c68544464100b50b0000d0080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 671485377 1250 671484127 671484131
    0x930111501080d0f03020f04051c080f040e0f10030311010209031e0c04152309091609020307140a020118030e15040807090513050a08040f0605090f01030f 68
    0x14040100481841400381c02c614024040781140c484015203c5501e400d401424140103200c5010514064010ba40480350b0032185103048094520344c048000c41c400402400c0d81c080002c038010001d400740e004004642e40e4062008080c3c1e42c0050307501068130700380c40c04041e5020010007040824881c0702c0300b00010080500048c074150b507540000e0329041c0340401c49055421024030310040c00c203060024400a0303a0558050108040c04110941c00e940c1a0183d202c1d064000c100b185105150749030032044489000c4c013031b10000e051812441ea5103a4040e1501006090202000705c0c4030001c500070b0340e00408881c7c80b80b401001041441d82003540084512004541da60b00344120750403088030b502c280080c02a1140103001101c3e02c24001550412440f03d00e1481c0100710401281c140021400b0407114804000a0340c1e17194400281d400307a0f50b80c007001e0881e20620210405100301039000f00700300d4070303001d109411003590b030601a80e5a015881410758404010302104000d9400383e0041ca69400a400e80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 671486627 1250 671485377 671485393
    0xd03150f08070e01060513030b0c0904050c190c080a1d0907030c02010e0f0a0b04021f080f160e0906010221040305070806010f1205031903093011 64
    0x1404040340c141e804040c0c1580000002c0128050024016000d4455803408070724120b00c441d40188100c0031352100900301c82c00707200014800030568003039a1618500410600c014103103040f200e9081d401900800d180b0400e00c00006040c00c1c0a0010208001d90220407142020040c08058032080010480c1484141e01d81440c5881c80ea0380c1d2151034070808180c2c8000520502c0418020b084441d90b0040c185d0591000d5103640404400081084c1910790007050b28900d96624401b08010704030781008a0340d040c207402e00c02072406410059552150700c2d000607441155940c95080740290000c0020705000c10b001c101900310a003401515141d0156040c01110348a000014034038503403181c0220140604030001c2010300030800140540002441880024461941009010b4454103180c0c031480d6071040013001c8110030000180203a861346190414204078501240401501400e10400c0c111505c10358000c04251504110390300c100c01a080011001c240e102c02d20043d210303025a07010012481c483c00710 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 671487877 1250 671486627 671486639
    0x305090f0f0a090c2003031b0a0203040b13090c08076303020a17061305150a06090b0406031113020c0105041b0605030c0a03020d02070b100f05060c0d0315 68
    0x28170034903440c506074001c0da62840c0c0b801c068403aa007141c1c8a418070604041104440c0700d603001082d98282c4401e21542e913540c035914032504440803101c1e80081501800e10403800745844c0c10540e850712401007504c0e000301400d00031020702c170340f0015070030304032030a808502240003011040c1d034504c10409410400740000038040c1440d01e1420340c07405140200c01c240c8440500442c14100880002001103a0710002c0a80d01c0c3c500300c54440ba0001c100b0354920721012500d0782445001c1001502c200740d40100440c1500f014034000001d010f480c0a8480f082c0d04180b140352690400d8400e400484ea004031a002c4100200000c021000000c0b201909a054080c80100308001003803041d9402240b140c1944001d106102c000909031582035448101402018802c1081c135001c441c0031545143d40038580180c0d02d1001c1c0740640001d0180d41030103801601828204a07440c5030501c01c0d1020340380041c40082c2400e0b6550b04000c128494000c000203e500240d09043c000342c041e03000346011195404ca50030b07541d51504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 671489127 1250 671487877 671487917
    0x3060b0613092c03070f0203100501060f20060a05060109030b0f09060619030b0a020f120603100c0905040509010209060a0203030f0a09021c06180305090f0f0a090c 72
    0xd002140741c2039440074110382c403440351081030f01c03020200a511240d4526810405483c1e029224028046c00c903200e064030210b41e421302284000c207400031020089940c40d890000c0c212900048400d02083d0684400031401069002035002d040d8102d00400440e9580d0400d840500405406981401282200070000868010303006215940c2d100d2101154509450030b149484009801c660141075680c4484003c01110300e154020781b90800001c0c1c0700e545602d00440001e21411411000e403c9012a1480c0c2c8891214070190180c0070490403038100d9144810303044103c502d11041a404501e100071300b00510308240d00710980c0010910001030602480401241c01a841103070340e6030041c0c00010811201c1c07243c424055422020f00c96080141900b0b070350102c0d110500070303440410759134690f500140402a03030f50070101c11000d20030030703804450885140141031a000716030b010b4840c0781e5890042015007030103403501c0c491010042c11304c1a00c600e032445050040c034002c454101000049100456040f0f940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 671490377 1250 671489127 671489129
    0x2010f09050a060c03021e07030e0901030614010503120901120204091503031d131527230403050c0309030304230a0302010f0e0f03100507110601030c03060b0613 71
    0x81e40107004248290300e001421240030302c8041d81403600c14400c4107001050390300c40f00301c601480405c0b0307a601c20b400c1c101a607440700308505041e80050b0840000c0204207954104e10010282000c0740a80e50342c99008141d1a0320100da4001c1d03154200b441400080d6105401604850882e21401481c240d1152440c80595a01c148007410403590b10700c08008040c0d101c08003102000341d920030100c0c1110148002607480002480052a036500d0745211a090303203030080004014070740d05805102084508600355141c2141403038103200fa600d0004215100c0080758000d062150240d004140a5511a5016039050b0094143c1c600d40f48410300400400ba2070801c0184060324803c0e0f94003c00030800105501e05400300d01c030070b81c0208001c074420001030343c210101c01544941c605080b01c000090704003040c0584142c0300c02c180e0611681d402c500c1041103d5102da80102d80e00c1da11280c015040714110f9035501c3e403c0c440204441d40450f0100003040c00c552001800100c020f1190f40b8102000103541154451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 671491627 1250 671490377 671490383
    0x11d011404030614090a0510050414060108071d01030c050d080c031303020406051f080901020c1506040e07030308010302060a05220e090a030813060608030307020706020d0e1f02010f09 81
    0xc2d031200c148132440d00e903814680c44254100102068901a5a0b05882d0b6480005120107641c4440103d800c020140c0c0c48240e400e08528200e82441da510080203a48400c035105001000e0340d080c50035000d000c1103008a40c117817600000011192881e040510111816418040c5e032002c1c4103200c06480504140001c06498445400e85038016085004000071280140e000ea8418508405002c220280700b0502c02c20101680c11301c00425a0740100c101c0c064814103c016105010b003a0116104d5405602e90034001d040c2507804018212529011035510031a600014000c25140720042005151280040200441910b800e07400e2100311907121080801c40c01802a8020f40801c0900c0110912030f641644944403000400d0b2172405903d000d81107600c05001103103148202e09440d41401100d4100740006c04d008000c59540341340200c002500c490160140c4070040c00b5106640f10307858450040c95428140c003c108085e40b5100025512200003042400f50540d5251440f40e07010590510500d481180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 671492877 1250 671491627 671491631
    0x6030a0b1c03020705044d03220206070f060f09050c0415060c080c0111040e090607022a0a03051014010b040b04210204050103060c020f0a02011d0114040306 69
    0x81c1d51074041d04000c2d40e03402450003035140110540310740400441c2a60411600c0c0c0308003420003144800404001c1c444070a12414102640460194105a000561003604400400d007424800010018100a01e904019621040a2040001007045202004100c0c0e00c40c8c4000a0f40740440c5691406446c51080b040d1000c0c0c124071042d5045e401d09014104a1a06640e640d01d129800c0100180c200052140d02521904020070200b00c6103800b507022135042000384031515200c503541d00441100c0c3c0d07001c65000c5914052940030803a1a0f000181c4003602d83c0400d10200d0340024141181e52070150140521584a01c1c0710700000003003542845141e941800050300454003441c0c0d0b1b03601c0211f0140613885074614a20402c410440420b040c02940d090714000c3d00000c0d5602c000405207092811601e80c0650f00c10714040001041202d40c0c0e004c180e031315581e41c007500d01a101c090461600d445a03200301901040106000050040c048511500000c1050505041d61010b00c18800d0340c941060704202c58072340d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 671494127 1250 671492877 671492929
    0x11206180204031101230f04080118050d030c02190503070b01080c010207062f071e09050c03060f0f180a06060809060717061c05160f0509040206030a0b 67
    0x58801c071103004001c0c02c1c0341c03100c0080c00c80c1c80004d000d003005501c004103002103844807203417034147c08480007022542c00a208488440b0100b04045001030001c44480c4105d807841c0c000b0074082d0099003038002403500940914126050800710243e401c0b6001c81c0c0f5400104500d000044078038074018080d00c4104014450002d03540000392804c1290b4000380c2c20710a03000044441002d00b454440700c40d210003445a40d448440c04142b40c0340c11600c3d0440711045200130302d0040c14810355030261b003c480c02680d0500141d119025804243d101c1543c5954100d41007901e03e0000e0308001c0d03200c0121010140001c101503074104d000881792201a42d0140840c0d48030b00081120b2907020000541151b1702c20050f20980c00d000317070041d1400b400e9050240c41c181400000410035a0b504a45002a00c02ca0700303a84a2058075152007505e60750000440a10384da8a40400301e20070348108198002e48001414542c02a200c680801c000d0344c000419499085456001404c1c0640b030398000c0551041195980394003603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 671495377 1250 671494127 671494133
    0x604050d121407020303160f0c0e04020109172512061a03030306060307080406090c032307050d020d0c0906080d0905040c09090b12062403150601120618020403 70
    0x500d2042c4035480700040c140400d00150b680482105c00340c22540342d00046440803441d207010401c01204004d0594180c03184005100c400a2121900c1503100740e0324010781940310600364211310000900306140780d0240500c412402d4900c980480b82203040b074403109000ea60b50140400c202044a011502c55407100e030000301000031070b10717628103d100841c0a50b0451803c1d00100700640070081c900c1c02040b1a07907000c00c0c1032003955440180c01607000222604241d0301c03810560340d00c0040c555001e00412008116000c00180860404103441c030080c0040c200084c00e400308038900103843c80503941c1201ca120f00184000c90380c13043c02e008004010141c41d1075085040050700041c001e0340414040c600f0107604d6041560b00188d4601900e040d0701001a0180b0582c000c2403c42c4442c0303e855190388500c1040c4044080e860a0504000c5040e1000030904c407608030078143c44000c0c0003012048100308001185d40c560144000d1041c2541c1c9800002e001caa46190f141c01409107100e1072940c0301e90010f424428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 671496627 1250 671495377 671495387
    0x611010f0507031a332104110108040c09020f0d0606020d0807020312040237140604030503120705190806010e040b0a0b090f0d050c0f1905040504020604050d12 70
    0x4440f800315a61140b68001c0c01d05c402e01550181c2c0c80c205a800351003e030082290800342078031b00740c0e5200001e004940102c0b40001400341c030280c4041c2c1c1d4048181906444540c881c11055204640c000d03003424180340342c914590007075049410984117000c428800f03001140800c0c07050300700400c903550040059001c558009081c3c90f03030241480b4119081003089041301c1081030340d13054015905030f41c0c11b584002c2ea20340b040b0300610018000e002c4800c0c03044400380711804081098050324900c146c2c44e6640100031040051900c5144001840b82d00103101086004046114083e8005003d0820710319000802006110b001c400e8490b0b500421015024413809591000e00b42030207120a80e001c03c20140954001884220244555850304800181d079070300544805003101a910005080844d9404840c03900c291524a60b041e881c3c0114124501003045162601a5103001040c2a42000e2458141800c1c030001d01401001642c201354200400500c2e074039004517045001e80602d1f0f00b070415601c00070000300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 671497877 1250 671496627 671496671
    0x1103100e010803091005040306091a0601020a2a0803040807030506060f0d0b3106050705090d06050411090705030f0105030304080d030f1d06041118010611010f050703 73
    0x30004035080c005015010001084070341c00c8204035903003042c00c0079160084034144519000105154204014001000882009403003450f884100f032043e240e645d0310049941c3e440107039010340403a503480940b001d60400307404007003c8400504401010141c8605185155a2055004c40329980c000c61040040c401d0a11896400003021205541c0381e03201d48002809041c4103800140c0b9020303015002c507040040164104901c0d03c4d890395800c548034000c07110304000074500360b030a036401070404e0300054209204a01f150f8081c1e000400035a8440c42d0350301c0d41d200400c0b00030011180c0c4203090b400904d8507561024514802c05807941c8966492070081e1558402813410b0340090300940c030501090014400105040e00f548085180003e601c0340d987c900b04000e0180c2c1c0c0d81a140150000b082c812800402090ba180b04600503007441c50400200c3c024060501c20203110428440395010040c0805072192a822483c00d504a0022810303e40c1d003490002190702c00d840a8020035560502a0380d4443c40c40c15401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 671499127 1250 671497877 671497889
    0x5010e10050d080a1d030d020f1b0105071506050d0f050f0c0105042d03051c050309030d0903050c1b0f0919050702070b0d0605090c1603050a030f110310 67
    0x418400b40564410060380920042c55044c00001c165184c80c3c170300c1c003050080308484020125139000d410860041e4540090481581c1c0c0c501400381c0d2180e180c443c9415203c002e21060391094509805519602d280d0640008505da5442d280d21000465940c0c001d41091005c0c0140c0b68070091178218907041e807405425000d281c540c0e8001011941c0b4603a001410f41d070848041161154640c01c18a0805c7e01a220703514080d0b22195042801200317014000940f03001c520301250b5903100d0808550000d0306c0b10b02003110f510055600403c81c10301a041035070040c240040c442c0c00c2050500610b000e280e030420084d00541c0342da044e07898180991510b08800c1100c8540c100303031944071039801d00f07602240051595100c290b080d02d0315000421909031080004000608030b943d040b588403c1d045840101030940b0b031141500c60101140803031501e03a2440200c404d041680c4c1422003404600359026591604003060030400e15580d0b035000034042c0943d0040099402c1100c203c01d0b075a1810b10289240200503030031907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 671500377 1250 671499127 671499139
    0x501080705010347010813140f0a06050a050105030a1e0f0228050111030313110a092a021b1504060c0528150908120702070e07020322030605010e1005 66
    0x48440b441102c01a0101f558005581903407580300000601c1c42c091520300341c0c0215100342422202441403941c412405456054001d00850340c2c0c0e6803c041c0d0301c64540c000078100d00a0700301506d0300001e06010300340c1c43c14403c402034040f40c40980c00040c94546074801c1e544ac9440301218941203114421a81c034054103090078120706540c0084d4840d070b41e0303000082250038a1164951640c0c01e00c130203c402c0fa800c83c2d100900410b0700b103860b00c0c400c07000b421003022403842d070122456041c040b09070805245d085c074440b80c1e4000c01000002140101d000140f25201d50741100d096002e00b116143c0c010000c1002c1c2c10980c6603000d070103130146425850083c3c0c07800c0c0190300283d00450100041118403180708070640041d00805489481c3c0c02500080c94001c2c8010503e1100107040407403a1400d0103002d10a148a03000c0e100c41c1c03170b603503110058005022900080140c0041007511503150b02c02c4000070001c04106400c0041986995540e02140d000782c0000040451100170003015511460032000505019509 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 671501627 1250 671500377 671500381
    0x1d0a0201230f0c03090918011134020613030506130c05060307030e010c0903260a110304081b12010c0f0f03200a020d0305010807050103470108 63
    0xd40c2128002e18090561010700010300710032240040060b101d100e000104071040714100141e00003d541000500d040e582d501f0416103072003150007035041d108184c3e01d0031140c050704800440c0070000000d8080c041031440e085030503400056120040580440d0490030150038a19085003070240c640040200000c40c1c480701c0c03003203c00010b03007190004000c031382040d80c2c0151683c80300c440c298050440192051165881c0c80c10208030b0661000702d0108903800351090441500c6003011402d01100030454030006050b04000c1d1203261842012400c078501511425a07043c039449071120717802d1400349001b1049125200c80b0b07022081c50a0054019100007a0000300a45019144040d01d80280d95a0603c140031010000c5121207000e60408002d40112122301a049148145030f00303241d80101e44c80000512541040100c010300a00c6000c1c182e6060384010f103045460b0000440180090f58020741203402c40440e0070034000d00e030759030090b8440f5000c031054100c0715502c0e20130b00b008022441c0c200c0c100018402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 671502877 1250 671501627 671501687
    0x611070806100e0622150b0c060402091504050907091104030f0f0201030b0315071805011b21050405041a1804060e0d0c1203050c0307050703031d0a0201 67
    0x1003040704070346060800f009a5991100000c1c1c84a20400c640c801c00040340c1019000181c9136442020035401300104180c442e03480f210700c0d0400d80641155010151f10a40214000d490581f00d03507a404076180002840610103280441c1c240ca41c1a82c1018981e808400284032170034041c01441080101c98101c1030419246848010030380c05200c03405030081c050310161400b50791090b0840d40c85644007604403044100c0303040103d04580303002c59100002400440b04d003900504207035440340494405075240b10300c01c140d0180c0280100e004000490b43e810440030144000c0303d00d07041d0381d05082043e0310b440d501c56282600b03000545601a00407046100004000c00240c0d54507001c11400705446c2c4c1c14102e440d170325841e2490081030410461103803481006211200c140e406007030503810030b220b12003004448040107410b40640b802503450310100c0c1e0b028400203c000e44248080c0000038040d1a0100c2e103c40742202000e020001d41c0080079441c0c200039903030419941c024814008072a0300c0c50900e400600400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 671504127 1250 671502877 671502901
    0x20a0507030b0604290109140a060e19031407150912030306081204170f0c06030408130f03050f1c0311120109021201060906051207180611070806 64
    0x4000100b6044021012822688480d8052817000090080c084c001c43c4402c038403000c900040e00701240c002580114041054666600d06003042c1c2c5020701a1444203092203001d4030701880d90710440d40c0044540d102242c4612000040b4801903016060185480f030280c00c582d030815441d50004801d1040c2076080402040d440702050040703424240c07083d005029186411000303048075a10a0307145200f001c1210080c00c501c0c0740100304603001e0300e0280151102628069032201203070b22607400749400913020244d050070000001c552191003900c00d0380c542070310140800c200641c5504050f0003002c0c0d0040901c10448100419541f581d8441c00400b41586808040a600b104070801d0300201754031155100000d070403010680300c070b100f03000b50050f90f190703101c6a9990080d00168100ca1403000c144000090407030050b41c00a05903030541d65094a40117106600307a0b0280b4024010208011605245c6c0c1030b0102c600c800480500960b0b500c0341c281154906842e80b80c05010f4001d00c8940d00f1000501050800032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 671505377 1250 671504127 671504129
    0x90807020906010203070c09061502120306040b060f0a090306140402030d0f0207081507140f040608060a0918051006051f0908060712051605031305010e011a0a06020a0507 75
    0x1118101c0d210b60710000103d0950084090080a0700d010f404003254958145d00540160344078080d1240110101c542c0032a81c0d074101c010300131101d10040000c1a00c90400e504112451b180c0030b02410310304100042e00c1c1085500210071800002d2542206004000c480c0c0034502044000b20101442801c0540000ba01d941d1844030300d1007813100108000011900034404000200410010b6580209901c3c45800c01a801180e01b4400941e40c081c440742401c3d001002d8940c21200b82c01461f04042c00c2200c10788400310702801c81984609e400000084400243c011141042ca0300701d010744400c2080e25002d442d10041141075042942060414086a1180c035135915144516051440704548441c009542c065807070b0704240e58a00a00082010940d00300110050404595408000590f40c2584003904050688044800200c04102040d0008407254002028a000c0c03400060f92a00052881c2e084500300c480825903040c0b1210031101e18981891407a00038015400645003020a9070754140d221542 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 671506627 1250 671505377 671505379
    0x15060908030904050a3c090302070905041115090f0901080c090a02040806040c170309060301030f11030304060e040e0a03172a18040c0905060c030909130c0909080702 73
    0x161300e00140c0000150b13000310f003082c103c204500d881030000e5006614140021080711807244c401c80ca854030b090503a0700c50104180e4151b40035003565800d00b80c0750b0b005850301401c140c40300b401d00110703800e05641c0d10700c03480c01855400705415514001c2c4401c1c81000608807002a10402d5030100401c02040003103148040910b00715151005a59111800c034000d000701e803c0354106124544c108010011340c0305280701580c035980100300c2407810001c501d640c0c03442200c15058104809000400004180d1841502e601c0d1040d900c80b480344a0b01000b0a10715086540400001800122003049074106807180c3c40101580394050941030340140c41c081c1c10351480d20603c1c0c181822010002d10300000e00002d2154410b5017a58061032284440f0f03401751103400c0a6655200d2605861030f00046180500c501002d440d4a86c4442020720301d40b60800080341c0081d0741d0000b80d40400c00080030117a9900e0750043c1300d00740c0c0c0884880303c001107042c00425032030550070055401d0b1520b8079075000714841500742d0700300580c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 671507877 1250 671506627 671506631
    0xf0602061501021c0909060e0f090703023607030b100203120705090607060f0c080921030702010609020d0f15210f06090b0f2a030a06170115060908030904 68
    0x4131107036080300e202c0740b25480140044d25210012800c0311645517141d00500c544141402d5945801c01a10384503da58480203521030001c00c040300d460710148101d1908000c4140302110b03840680f010102d140d401c200c683d100047d654000c51a0035181141140c05014010b01c01981018194407110050741d4014206078248607011400d0501c541c0c44004845100354481002d100290401c886803002d02103458110b40401e01100002e0149940040e040c01920700602803444c11444001d5118034560000d802902155281d401c0814104c0060000b030001c40208400040d42c41d00050b0080210b4603144410302c024200c0c80b004202d10309115510100081b0301c0c40d4005400794042c80c1100e90b555880c140181800d0600c40d10105001c0d80c803801c03d10034104102c0f003804a9880825200c51501c0340c0c00100c0c22040ea0b18606459030021002465108036110f41c0061050786640d4125041c041c080110040c030ba4450400704280c040f0009018010442030400200140c10407040d180c07030340503104295004d26 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 671509127 1250 671507877 671507923
    0x12010213051504030c08060f0105180f0601030605030a08091014040303052b050411010809030715140f01060212040b090f0a0b0d1d19030c0f020a0f060206150102 71
    0x140000440c1c00443e444401700004540d44c5411342d8550408641200c001da081030000601418848000c09055103400b0955440e680c96118560b490b504c06810107040595605000c915070f241006509440d9004110750b0351209400c80030030190301b81280322a420010750410014120b422031081e101030766814108035848607800c4208184000d5103000400c001c52050210445945996102501aa008241e0101400f402c1c00041d141400240c46022003944100940d001050317041c050407450501101012403512030328240e07401d032502d050310341016040940d030040040c5a0100004500e00c0d0185896904151600e48455611f00400e1403113401f1342510412100956204802e11024280281c4119164a03410510074020404c9900c60107007280400800c105c88280050300c103031100c800380700d070b8000062071707950490b40c039280c4500480742d6040071042940142d95401d0980d01030084000c003120361034a80f4100926201e40a010f805101d000c3d02e100d182c10b07980c0071501585032444001f04610300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 671510377 1250 671509127 671509159
    0x708060f04050307080a090311030c03030409180b010308031f0806070f020c031e010c080c2b0f050601030612031715030a080705061f0317070b0a0b1201021305 70
    0xd03201c4e07008010200c01000480c0c03820b01e50070404860030303030b80601405c00200d602c10f428107588a40c0612925410f5000f4030007000350b003941e50803201e5030078480f07000c001c40c0826036615501c0100080c0c0048801c3c40010040000340a07401c1250482000900e42d111117841c5000081c903226a00a40180c04014808200101e1356008000c0200e02c00d0001d0300300c0d591400005020031a840c1c4040110545508120440d40d00c24803e2500301c0c0140d0807481c05900d010f2810f00c054034001801c2c5c21134102c521104844076215a1148070314414807401080c0401c0714682070000600311041a000250480a4020141c0100e54050f01e0044450458401c410098440085d8059900d000902403645481003100c1401000071031800b07808054070503000c0302e29a07111900c42e20003105000ca050b00c565402820100041213281258440540c419089945002c106482d02508804203e40703c054450b142d01c120006824244455079000c0c02c600c00840c2000c03100007203004604501d1042d28070071a0601c4e068146 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 671511627 1250 671510377 671510383
    0xb1608010902180d0c0e09031201140d050d170106030204081b0406050a0b0403060c0f0f030504020f0a080c09062b08090a0e0108060a1104030303091b06120e0708060f0405 75
    0x14002d186515142162412090741d00e178a01410090040b4000410045400042038071000740812581121513030078000c482140409009280d58410344031040c400c0454008c0c4540070460036681c0d504c42c1008603c2c150f91044c00070603449281018030400041160080110700f0303400c15401615210724180044000901510761500000c2e84146056000032740621000c00520407244a400103000507164050305079210702040d13483d140484c174015002c65030345200364003c6602c944020082c00c0c4800311034010421501d2141c1100d1403991000d02d8080e40c0307103440c520090b84000103c8080107140c0a40c015001c4e050140f41c1100460712100121800304a081415183c00301c0004c1c143c19052540d49444a04580b03082c4100103160141c84083f601d043c1480c0504000d040003890001d14082c0b95a07001c600800c0031201c1911125624040d8400060002e0582002401140d07030300070718034481c0a01001280c070780314038402d22584000b20810003008007003541c5178030095903001000251380d6403c00742d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 671512877 1250 671511627 671511667
    0xc090f040e100911090105150a09080303130b1b0f0d02041d0106090605030f012d0e07020705060310030f1703070f120905060a15030b130b1608010902 66
    0x101c0d00844000c803486010a41c80001203074020941c1081c4a50640b040c081701340d20a0103829007200c0f4194a0504000e4000700505c8803140e24070300201c004c9c2d03031065030382d045130001d44020002c41c101010400a01035003680341c64022110b80b0015405120001008403607201d44454010306502c04a182080e1281c0760703040e1001007281000010052031501c03c142c1ca0f03442e09000b104080342141d02d004c5181403140c000c6e00e1080501c0f14444483c3d90801000704c44925119150607214881840d009040c00100d440040c02002d5034000071540e41004c181c0a41044030581142c4e000c0c0000340104105061b03030198101c12280c00084441001700c60341000386400098100c15880c0301da0000a0242c2558014900c4028a50954030090400f030a0b880d04000ea40c0d80301700240c51544502c4c045400e580e595402102059229044c0800150340c80d80c1d80382e107a40003201c80140b1409100621000d00c0031501c5025400f10346d00c04100765454201c0d1024160560600440e800c8990108440c0c030000e103003009400b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 671514127 1250 671512877 671512901
    0x80d080705120109240e0414031e13210618030c060c02030f04080a020a0608090c1908240a0c021f0f0905010b010f080108070302060c0a1e03020c03060c090f04 70
    0x10307105a854419011b0340404c195012282885560750a07400c4503004005d49030590290b06480b500005074134188001a00000c1001c0c0916000607000182241c03400d40380f031136100007006030300700365120b41c203003082280c24880501612850680d0080002a4410181c040555000c40300082040701c00f00124594003440034030031549500040c0208844000082e0303410140d100700c480789a000c3d04d5400407250b511007038034805c607194804820009a46840c1d02d08402080d4480d094080d84c035130b07448a0381e240c20040340010010144034010b40080d40000341c3d0041c0c3c031618071081449401140c040007035a4103140f0380c44814100c04020790a4110655400a1400e18104901803013180502e041c218000c10b00392541d00d020840c1c0d1500b0394844c40c0a071711a02d040f54661030290212034a95000d0001c0c90b80050450000350060301c40d50705c00200d41100011001c040c0d402107101103a054900039180684800c206440790344104200070009001b54100c4000800688452000548440115018118001d840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 671515377 1250 671514127 671514191
    0x1201080304080610060c081e0d06061b031403132f0a0b0901030c20070303200601050d0519120e09060a050108070203070c080d080705120109 62
    0x150114000301400c02d444804003610340584441000c00351100080c441d80c40403401000c210804511154094080910030170780b40c003c01d80e20120b07242041d512071720341c0d0000540c6e5011309009440d400b881c4401081d010301c40103000d40d990790b00d018020020100c2c1400318070900000040100c502044000802c660101260981d149600311080130564903e0911160000048103a0140e1a010340e0300c40440340903034101850514040f00440240c440802e1f600d042c041091002c0100003d04c8060011480e04c0c10040c0c04d419040d442d005100b000d09000c1d010310070003802c42400700034401181e190b044420407502e4650025003440d156003002104481851800020040d05040c001542a140d01d50f829031760355030821141200401c10b03041070a0324841e40000c2d40304000c2c4965402039005640201e02401200e083c50300e6503840340303141c0c500350f00000c0454010701c000458264200c468140c03c807406d818118200210703000001030005051081d800d50315200c03000d1081c00710348104071028192220000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 671516627 1250 671515377 671515379
    0x1061701381212071e022404031e050d0c0b0109091106130504151208070809031006090506063118090c0b030403050a0c1104020d0b0306091603171201 66
    0x2070f01415030040481a10308802a010090103502034500c95070b00e80307500800303c00d0703036041010251101002d20000c2c500c00100800000c404100c43d1002110030411070610741503008190b2519509010f9181c00e14418040604022000100303100322140c1907071080c4100040c6602c1600780b030003482594900c501d070000c500044074190418110205c00507207400343c80520100448001780c8500e0141882240010f006070081e003000a61040001d2403102c0c043c0d645141820009000642015481c0d001d06805698034070080000000034012213070300030000c4940f54244204203c5036045194419200000c503001c1d09450b1001141241e6040c01504030b80c401d41903040d20803841d04004000a19041e21446000f40340080e8052080c0112881340b9032507580c0c1c9003400c40008003a02c0c04140020110b441c010003400011031a266880500b01c03814a40384081181005038050508100300905000001c0d080302041d03a5102c1d400806001c01c480e400714403a02850070840d481da1150003154801800341d010500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 671517877 1250 671516627 671516653
    0x80706020a110d0915031a04060602060403030f051b1c0c0918061a0307050f03040f15060605090d0c0510020304080d0801120807020102010b03010617013812 69
    0xa94460b04410b0030445200100751907041e500c0742d00c10310441c0d0042a042c14080b09091003604044403070307040740407989040841500024240c0c3c9043c0c000c0340050f40840100010b0607414080e00b1840903000d80c2c104050b09040c03c040280c180d5071000d40c081d44600040c40d41488101b0003100c112202104070402c403960410000608000c598031810601440d060103100514807240304040c1251320010194241c55510003890b84140c20041140c0c052007414003604c03010040301ba0086100340d10030421080501c0c07252900894409401404984080c503001b0b061048035045801c9076001c0f40211103081c8603d0b010318000540b180542c0001d41c02030709103040801100d030002301920644010006680035186152001c031035140c000d100d0400101598603101c4007040c200d03002402401e0040c400421001100c074080780c01d441ca41e5010b511101d18030070b0300810900081c403078940c114181036401d4900d4102000d4003840303101090310b030000f0918a00c1d4280880c2c1d5495a5000e208564141680d0b80c414105e8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 671519127 1250 671517877 671517887
    0x210a0b090105090f010219031d0d0e0406080c0a1e0b131716050f0d1209181104090509010e0d030207060c0813060c030b030a200f1c080706020a 63
    0x9101d0b03e0441c030512200c560514018002e07500b802d030348400b000002c0b1958a004070054200191198030b1645000c0c1080c004401c1401860885c0c4581c1d02c0f208001d8481c802070108441c110352014400390000c50281c0a01d80d182d02d40d01d000c07540c04034007050182c11040a241d10300300c51039101c02c03165440010547d820301c003085412421500301191942a4036138201480b0f486044100b0810880302d004d03c010721646c64030484941f04044090000001e4800951f0340c031800f01d1410324410081640c84104016901c0f030281c2ca40d11891016009100c480304004581d41103004e240910b03965141c032040040d11301c0c07034254005c4800139481d104441c184200c04002a0007503000c13440a64100e800c02204603512801b60722000c1c00f0b0b1400c0d100d14080304035030b903c90703000500c454840c0700d0070551121001c45065170100010790902e03001d01c450310aa00c0304482841c040048051281d8010111000d0441040d5039800c80d016000304a54203410306004c0c0340c40c0c054a54070441a000b000e852000c104507068540c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 671520377 1250 671519127 671519131
    0x31608370309080618030f0d291906090509040f0b011220150a0905090c040e0901050702120f09040501090b040b040e03090613171515210a0b090105 65
    0x24801d132001500d41000c800128043e500010415910030440070f40b510000900a00701c00d903100c036000841c804454903403207600700000502e5502031010801c0450a240001492403060f1640d0746684030ba620b004005015401c04d842154443c148120015051189120900741c1840d40160a41200d6850307182006041e00342c10410341d80b02060481d2040c5440d82280e00c40c0b201e82d0000c0c10358802d090039a00c580303105d43c03050551004105c04018001502e07240e040d4442d02a03d6480c1e103007500c1c0c50401d004201c544078000c03c3e800003681448240010705401017000c0c01c071800d0300300382a9a90071211607440341501c6017100e9140c01c185800000103184a466002c00081d140441d0b0902c00d9006840400c025030b241c0d55a5203c40c1c1c1c10030466000180b520318010031000c00415044040640d4480c1006880b48400000c00400c1d000049903c494002c00e4104a074007402d2620080320310414000410803940844501036040307415055204451941089003404c22980a90041071a1800306c0c4202e000e0030302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 671521627 1250 671520377 671520389
    0x1020c0904031107080d08010b0d020d0c0201020301170105040f020f0d050609010501030201120b0a0e060a030204020301170609070303021507201f0618090311150105031608370309 79
    0x5a008081035081c2c02144401c509030362079a87e10000d034200482c1d00d099900060180c06071503401c11520344041d11a01466144001c5038000684947c508107031030b44840d98000b0410242c1c0d16081c03c200002e01d404004032100f9805850394100c1101076000b0501c02c2000107006441480b03060200011040150030050680f4400c0c0d8070003170100030745c0103200c040c2c85017202c80701d80c040911142440713045a0b00b00d502c1d600c520300611854a1968a801107012039000380c2060101c1c101d298003c0e010b181c0e003048069000040500141082031864400a40303900c04c107d800008106140c0108550342e01c9818a0b12100480850941c0c0c00c0b652642000d40c0c0b031010f4140100e1500ca0745042c18000420b5105a030215400400f10040f010400c8a90340010300e2054401c6041c000c0070384c00e0404e688800c015010004802903c401c10b2941032108151805165501e505200f02e1051401c1c480710802040c0994001080c80c004000064600f401c0c54845a036440208221240e44001000789940050740c3d01c21550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 671522877 1250 671521627 671521633
    0xb010806090d03020f09010305070302090402210105061303030806031c020c04050f0907140d080301060818031806030702010912030f0e030717030901060e0a020306011b0210030b01020c09040311 85
    0x1d505050701a8040c0170054400100240310000c0c180d4003d402699001303503149001460035100600080c100e0300400d00623100038100781031121030301c4040502c45000d010201e4400c2d040c10901c100404080d004c07404000c040212a03004103a281d00c0c108203100c0c2640340504118030800701160020f64521950040350305c22410f0901040b40c40000102d02c9028609600141005508001c029070b5118201c0000c0e0307421020341c80300800800c074800c0140d400303071a00340c0e00c030800c2e0700f03010102050582d10b054044466400c208100c00184070007421400c04942c0c10784070f8645a9807443e0040c0d006002000018010000381200b080c007071a410b50080072080d04807002003002081410102e5a28055240003c003525142822615620214805113600280e441b001003101a2078880c1604036080c180d650800341500401070180b9903800c600303405000c180040c035140e0100d1031034000640003420341854006060f950740c02c00c05244d2081c41200010200504038100034100b5150050a468001030045044c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 671524127 1250 671522877 671522893
    0x30812060906040c080105010f05040306020f1903020c2d0109080a03060f0b0723030a0f030f0902180717040b0f01060f020a0303050c0c190c05040b0a090c020a0b01080609 75
    0xb00d440e20a00c68503541c0c07135617040d03400e0b03082c01d005444403e11200c110040c000240800400298240020300b5019000c0140c29203442c80101c41203600c07043c2c09449420b050052000180c0848001940d00e0803680403140c40c0780103000c50300d0301030754240c0c054030076290f0354208926042406441d000900d480e00484e5001c00600c0c4d42c60f0f0489a240340709010700715036100108000c002160f107564030b0310a040e080030000040c030748100031654a154004a0004081005602c00c0d14265802d849242e418254035801409002d084e036000411003803040101c1c81c0805a950041040c4c20f01c0b44a00150350400d0b20500d2004d400c10f0b0816820044080301d180205960260000c681c203403142c1d034215941d1300c03103400810641e90f540c0c3d0143c010b085c006182d000f07503100510030035000e0007040040442e0b03c40701c005110514260390810f0303140c02c41140c0000340254245600c4c0c8506480b901d100750b040b90b80c004400984121103502c01c1741058140032002e04110071600001c2000600032624a0107000a84102c80c550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 671525377 1250 671524127 671524129
    0x3030227120d0e09061c1a0c03010b0a0c03050f0d05010807050312030411190326130302060c0a06020304080a030605010309030906030b030f0d09060801081b100504030812060906 78
    0x60702c20782d0581c80005503000414120340c1400b84506070007a2004003038034000301c20384e1030708414481203e00a80b401c520501403001841420040c0a40003001100042c1c0b942d03041580c4800c440c45000c100100708205504003206140c8200107079243c0c013214626032540e03000b200f8203500c09080b081c0102182d501503000300042d18500005c01038501ca00700510075045540e80d803940800c01c1c0d030354507143ea0449003440060300580740c01008400030314801c92290400a1042304030500c060202c13000102003a008100740c1c003071103c82c401c8103012690b0407a80303203030340e000040e0016007000344901d8010039160001c000e2004026401018200c00f038802d503020441e050740d560045083c4e070030550f40076010a2280e00140b003594070a401134409017a002e001c940c40c00f40d14100840c501001e141c5c42c01d00040c0f00700c405020040d030140c205070040400c0710040910842c403110100356040017016061148540282400b0507a0003002034400568100b10019240c0090f80340181101008503040307441004220001919 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 671526627 1250 671525377 671525383
    0x20307090317070c12030815060405270403030c1209020a050402030a020c060703200c030f09030a050d0c063801021203040f0b0117190303022712 64
    0x114824594414851528584900b048039030600401c0016100400600d804600f010120000030113507044112454507a50800400500317000e00b15040703041c020124000c1556501c07045c0c4095038011035000350940c041d2007805220f0443c3c0700c010315041c540c034410070081c990154400b61140c07149403108600030405480b00c0080701e848400095000c6903082c800e000350304250b0702031035001402d101c00526007085190032902d0100300320381c40c400098440c10352000e10b0581c000d04000c41124905000c5c1015098102d0076100c1c003602160103003128020950790f466075800c000c0054540e03007001c00d842041e01000301c02007280c680da040540340c150900243c0c2c040c10301e01d450741028100d4030311401201030148400780290038030040d00090444c850a80a6034000150400541c0102c0c0310b40040210f01d84285000703850018168000e00c40c000b000b40391444090070205400710040b0310141c02180e0005585010380017402484c1c482c107a01c542e40c01090291605c50780c0110442a400c1300c107000306411b00986107035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 671527877 1250 671526627 671526631
    0xc0b0a0f021c0e010e0402030a09150623041808030f0c030402010e011d1203250203061f03080d05240102071e091b1403071d01031d0a03120203 63
    0x88012020818030503251203950b807044240f5052501c4c1c0d4810400000041c1640c03c107440020800344d54050b6041000041002c0300100079a0001c144140b5141107c0f184800200b02a80301902c840c001c83c2d99078541d101d0b481a00707200765010000044003524242104507401c1202c60900480c8070310049103140640b44182d034031960b8160f44880840c01110011641024046041030f444460800d50705883d9a69100c9140101c11107001103031079007904041c1542c010850318920362102c5e03c68050401507103010400c45c0e80700034504142c000e07115000220800410ba80e0703001500d600c401240d581c542014540080e4056080b1500522608902d6408416001f5542e100b240c05648019410048048402008030b180a050003402070856501c01c0c0c00c006a07494901e050b160b21440081c0b074901c103a045202016034403c0c44c1e1080b4254074010700054150021081d822807100d1404400324200c0e80f280d046110140b01d01501c8051141660b401150355950058080340410505501301c50512018806d481c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 671529127 1250 671527877 671527903
    0x6071e090b0702060a0306051f03060f050a0506030c0d02030c0c0c090c0336060601080f040c03030c1509110f010203070809040b03030d060612050a0e120a03090c0b0a0f02 75
    0x3518042c803540c00c0000310740c8914032000605860f5030f40000c0d0340d680d004c59600e40c034001074046c0301e6020107040c0c020b00312401a0490012801000005e00040e25511450700c00d440003600c1c902d50700c1d181c056400c000d50040c92040c0340c0650001040210341e0302900054002c0c0008101100c40481c000d070108501960210781c0008806c03028000946800c203011030f51060f040c0245ca9240452800c0d40034030b500c07103207070303000444c03059115801780145940d000314001d60106a224000b040ca0900fa5120700c88a400e511010302005515031060050002c0c03403911030f0113024400800c10240406240c28032801c6082100c0700d02c101c208031680c03001380d400481240e04c1a680038858038600400f0b00e0420000b1b0a003411810380500c0140018150502c4d01e105410140001e030310303080c4c1100b0300b00c070140003070f41d90052040c61a603003070040700c500c0d140c40054911500c2c4e914421590b01c03840185070850041144040150400c0301c03001000901c44a4807004020701580c80c0d4071400d010702000402d9a407141580e06503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 671530377 1250 671529127 671529149
    0xb030109050a1211070f0e0705030112030c081b0f0d0e09180c0325090603050303040303110d060b070215031b07020103020f12090d03050915100806071e09 68
    0x80740000740392207284518400c650403c500244c100502d00c03440d01407181c05c90816840700140510107401e040440b1a40808645004c41c81d542c1402e28a40b000300542c0802402d22000e0424042041114001d5230b03800c0d40c088200e40ca102640c0703001e059940341003c9040489000d1707204117a140b207108130203038000254098000c0c82c00d6243c65010143d070891611410320a030090300c0b0224600d80d02440807071000b43d50000980000c0000c210000078804d0b055002080c0980b50980402c0010004410f0700c7e802074140c2000a4128a5a40800c11901c1014107840340e01e403405e60041400700d8140702410005000f5201d0480c00d40021303114140d00c0c0302c00e40340c2020750160303440c180d16613002900040645500c1071601501748028014520016003000903813400c8071254000b000142c013400c0210701c01e036200502d024041070521090341500c0f00310340d105480046846400040008a010310344d0070091148008a9242d45010a801015020a00300007180b60300d00c0c905201341c440c801e1044d28181d544400c11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 671531627 1250 671530377 671530393
    0x5010503121e16050d0e0907090603050a0f0c02150a0209060f031308030a14090114070c0501060528080d0504050409060b0d050708160e1b0403170405040b03010905 72
    0x9010890b0202d03580b001ca1404041290100401d0300581607440d1900c074400078a24900401c00241a40f01c1c4000180d00031002c880401c44510361001640c1c0445000b81030000d52614ac4410100260409106044146081000c0e05908540c00646807002519900f21202d0588441e41810705070300c0707210010b0790f0221086c8841c10381304000d41e00840e0000030004c00561800200d5860428540089079a0001d099450f0200c0c003002c2c64004a960303210b8101c0002700850790551000c500e9000010380440c003000a801d0407c0100242584988068100213010b844044003030800408480b0f44014010a01c2418030400a1101000100700b001041d164554a05003810402408010050000259400c0d519400032800a480d0345400e4a00c23103000c0c80140c01c90500b0300c1e450525204000c1591403600b04c1d91000ec0111000184220307400c0242da00c8002c400901e6507074180ba40b03020f990006004400c400c400a1800d90304c0c04000c204403136086d1018400d1002000405080300c0e06028060000d4000d601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 671532877 1250 671531627 671531647
    0x8040b0913050f04060f0e07030b090717160501050715050403031103040b060312090f090402012c0406150206040b04020604080706050702040b0a0b0d0e0c090412030501050312 77
    0x1910301114003400c0d000c1004507541c024030a030341c1c0903100512418425814002800007901499402c0170100000303000714400c010400f5682c1006201c05042e828012003c10030b88002802007800608040c54891541c02d165041d940e1620425034095070a280b200800044c02d500803015580d0481e006246c042500c1c910b0940b050141c000100b0441c20140d540100102c9200488080c500490040308a400c442c905102854075180311000705c14048041400000190343d02c3c211601e400150555003200d0544980c40182c541c0c2c844140840c4101201c4e4441d001c00c2001e12114519200c1d08640030311040e652809980c19084106c400380b00143c01000c00680410316022242d900684050725883c601a0b444507650b0901c06190002c3e130014000041480a40ca421b00441e90180c80413220204030342d00d050304145651186064080f5051b440b031b401034080c81d10a02c8001c580c8030026004518030b203002c0c5171443d50785d20007c030303014003280c41c040c00840d0600700003845560b5424840300091500005070707 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 671534127 1250 671532877 671532899
    0x30c10060f0815092a0f0402090f0d0807080c0a030f080103110d020a0e01150e0306130f03050403020910050909010e030a1d0a030c05030607030c1409031905060109060b070804 77
    0x402064645c42a90495603940705080c41940781d8115035a8510f08890302c06081200401035614128800c0380141310302040c540da40c91490f280604103c450300e441d03540b02e141c0700042c0d000781003010301603100c0480c184651401c0801d5a03403415109544400030f000c20f0704c03000d039061701c02130001404040102010f03170700504000d040041d1460005041c61a036941d030300045201c01c003003600002c1c0c0c01c40e981c40c1d060310704942142e021080e5407001c030007800842c41c0540350443e425500400c00b514491035070a08400b4180180100e03030203581c001c0c201004c149040403540d11030034203d00c5500c1c0501c6156001821264041c03049800c00800340019524102c03440034116a000c81500d02c42846040104420301c03559a680c00c00c4e0000c500c220000d02c0c07120300d890201810f1040c020860300500d0b007005a8211300b1039020b03001019124070340c1c40702510389d00054003003807522801d00c00300100d0078003001c5c6d440140301e0005120750481c1c031400410b110303040e101e000c0c0c0300403405140d01c000c207840000d01080c0110b11440c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 671535377 1250 671534127 671534131
    0x10302091e01030809190e16110102030f04021002012c0f0609010506030d0801032a03060905060f070207030308390c16030305030402040b12030c10060f0815 69
    0x440034a803600700804070301c540040c6003070b4000c07a10994001001c51071130138610740c11034034801d0301c031100071946203080c00500221000600c9902d10080021951100038001e40c40d01c40d808e002c0500864a1386807070904c4080c4084140d4081c0e204000c0845140c0c40c99105000702264041c01c1714000c00c07820b08034a04504100e00c98080c1d45070500420741481d0b20500b04102c2544100880c500100e010b0400c2e4041c5814014080c610030104004e8034018004148180d01c1090386003180129031000d003115050b02c14940c1c88580009000d241402403802c140f02002440314000e0140108080071500d41c0780007a40c1c1c03000284030080c049a4903900003124043d2004212400c28803568001c950078070190051b014480d0259060f05900001040751180c6020070450b00039000f0341c2c055000d28044c01c6031030140c400d0000600017803150341c43e0204201e02d901c4800e8400d21000749a000c581c2c40344c0c0c08140b100d80398200e440800d0129850070301d001911030a841102021034002c200980541100805904124240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 671536627 1250 671535377 671535391
    0x27050c0423220b150d0b01060c0f0b0705070201030501080102090a09020c0c0d05030c1506011d151303060b0402033d0308030a1506020c040e070f08150a0903050301030209 75
    0xc000311082901648441012003500c2001424943c1c0b50030040350044d801d9105906006940501c10500080c00f000482da041d031f0716506120b4011a5145005602d14081c039200805810a000c144013220f5080741c0a4001c09100340c0b01400180e0320303260068201c3c0129000c10f544080b40244c20020848203030300912880c9401000e84500483d4800810050703049010211919440000e60010040051002490b80070348103c000c0d0050a0030300c0020055640b1071120910700714220400309042d603074185090317003240048001a44402202d100000c4400251000b56291410141500410f2400340b007100c0c40f4040c007051031040c0d42140202907a52002c0000c081c2e0048842444c05107091240143c654000c40c818012542d680c54803501000503910403214042c6103200048050024503000302e010804003c0542c0c0020712462001d00103860220540d1004080b10b07544900400d0340100070032410f0828519060300c440a03218160418201c6a4102014000500c24001031006282403800141c06c850 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 671537877 1250 671536627 671536651
    0x150f1308031201031a060102121c0507020304090b03030c12130b1c0b0108060f0112020d0e010c021c0c020f0a1e1a0f041827050c0423 59
    0x5200c00395140340d0b03032080500d001da1800000040080203089040c00109030407480840ca0760342481c000203944c401c0c8401859552010105080003005a403020041035854035038000d0010f0b08044001075100c0d40140103082d05507060106051440c02c002040b03c044031303d114003e0450104101e120380d00b03a00104a41c1903c420310603000180700300c0050107001010700190307841c0c0c06000c840b0501405c6949002055043c1320f404004c0142e141c4e910007642004107401c2c00d00c50b4182d0f001100703002c02482a8418108a2450110903c9032080305500c051494903e079000c450060252104603d0401981a0303107100080c05110b5040040c03c105259040c242409050820b1041d1942401031242c0d80c0b804c0140c00313035410000c0400505000c1401810341140009a06141c46400c00022140b0310503070180d01203068210070090010781903540403001c01d80c000c0b1844d69000001040040c60050000801d4403980b04410248503507142520568400143d658589400721691054140c90640c005001001800d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 671539127 1250 671537877 671537879
    0x909080f030c1204240902010e0409021c03020606040f060e2e1205070609080c04051308040b04080d090506093114181e1903030e0c150f13 61
    0x440704a03426409140b1502441e100c5403150803408540d517030f0380c103003140c2ca0328103110481001d41d070011440c41c80c03440d0588000c5017100e09070000c03c40040c4c2c8240c4404100440041c020306059000c00c0e024010300c003c440038440024000080c4040c0c59031030094101403e0480c0100b500414102103051800300c50b26800c100c59000000d0301518450294082e151104201c1261000c000043c0500c402805580c102290102c4c1420303410342d920012310008900482da514003103080b08652030a001c1180364031466159403a6154064199103030042e104010540c8518081025050300841100056072809001d01d400c201d5540100840e0ba0045a84d900c0da0500c446d4102502c400410058401d0085041c4c001c290b004036040f60765035400c80100307030520a030290b00d04aa5004004904140d6007207450803c140310540012516061403045051584020314142d000c4e410103801d0b80000f0100c602c001c055810300702c5010284031604121003080076154070200205452001d1201c064014001c5450f0010402d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671540377 1250 671539127 671539147
    0x70506072609030c010906050d0e010b060d0b032413061e0209010905010903020d0f240b0a0503062a09030111072a030f150212010503070909080f030c 66
    0x105041958412001c0070000307511115040c00c10001880100a00e054503013980b170842c00818038000d09600c829200d44a106e88603a0007400d4100022007840105565511100c518040004000005890b4001d019210030f40c4030366841c080103038080203400c000d069450799420b526052041600001101c1c3c06603500407011400e03805200c6202040c440003001a07440ca000800544846511740c412410050300040c02c0c80140c9542d80002e128a80c030150072544456985481e0120541c504107100308441049501703091309440d07400c22449840300303949401020b0740320024980c45034030489500001c0c0d18810034181d815096808a46015080c01034941d0400300448006429504168907084208602107880010320207074a07075280031800c02c0c04da001d001c800e1050740701015442034030024242c101e22002d80700a101710b0303e0301d050303121a0003042159600c80c03003501801c07900c07000c0c01554041d2280c2d000101e80c0f43e000344100b10f40290403a440780d040c0801b115841280b83d000401e0301405031400c0c010308101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671541627 1250 671540377 671540423
    0xd020d0b090c01121518140705190816081f0e01170a03020d080703020f160c230f0303070606060504300b10170703021c0507050607 58
    0x1c1c007000001e000b212180000041c0381c4022224000036151078403080c0300d000342c0d0080c8030504407201d249204030f041d4030484011008255080003103a10194450030451255070150040c8240740c55078104210441c0400c0b001c880d941d008072031941c030301c00b12940c441d1070b5140a281070541c41000c501d00994010b000e01046160034103240d21400300f02000c00010b100c180ca81e00f640b009042442c3c4010804002e10f514002e645a00b07107003003030083c030607100003046d502840f80e0121181d002c1002050742e07903a908040c81c0c6e002480195000d8802e998854408607202c22002d088100300c48041c0981c0800800039404c0090000c402030710598540b004004950000300c09009060040c000c6807103954445251560f101280c54244620301840070701401040201414616480b41d0503400c00c0540d03400c1d5882c80b000140a1801b5040080b0412442109040811002a0b00030136284290f504001c20505a4190f00b0100304482004046402607034042c08181080c1c40600b40d564050302d14240032103c60f0440b144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671542877 1250 671541627 671541631
    0x108061906050a02071e060c0c0e01030305070b061815030a0f0f030801060c050d2a110a1403100207050a0c0806010317130608060406090f05060a0e040b04020d020d0b 73
    0x1c20ba010480d18001c54042c00600000c098502c240c0d8940600303100380500100c03403170203140c05115071006000c0c11f02c0283ca8009000e00059010078045584a050217040c40d0010b042c100c0303c2084810002c2e1075402c2004500300308007405669004079440c0c82c44020032101d00e030f0754501d41610032004800040360000500c41180da01030342c9034201003182070030010030380e82c0160403030400d00c168101000300141d00021541041c800301e1030002c403041816445280c1c1c0340020080e1000902609403100d040c04041140030550b0b03082161070360300f65641c2d14182c04070308802181056044d0401d944180746011a0303001821000c0c8181c0a41e17108007411390755010500c400340c10003840c0f548000014010403544107030b00d0401050400360641801d181050000c40c215003409018104480900801c200d51030340d07044007010348908074052104e61174030b42d0b43d84002c0c030f130403101d03030340f0800c084035000901c0104000114001c0390006140e40240e55581c090003409412104126040b1803510104804145c131303034508034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671544127 1250 671542877 671542889
    0x92b02031f0e0318240304060c1e020703060b0105040f0e010801050a050c07060b03030c01020a0302031b071e110405010b0a020d09120b09030c1c031a0a0501080619 72
    0x10081481c04030386022141d0b40c1034100d0180e8810400c0c004940290b881070094000c049850480501c00c0150141403041840000c09443c6404824441008080d410003204034000ba920402c41c0041800800003c80b0052510320141e041072200b8408a502c03a00a21486441030408074039150b130f130b074a60307001e220400d0f4403071145d83e40030380010301c081c030420300807150041da0f800001d2000342420040120b003031107070007002000c6596400030622191000c0c003e4401c0710040600843d03c0e038055140180103903004840111107000f0b0341000c062401481420740e1400b03900100e0410100c00c035651000c400480e034000a4039114000f1885004075a254021640646160400345441e60b0109a0203490070941449407001c2c041e6a00c4144030707840141e0700c0440e0f000c0d040200d15943ea1036410481d0704620800002a002e4015074607208a00000c40c152018041095501000080300701c00340c0c0c0c028440d800381142d510100140d020801d940c403403c1d0302600458000e0440b01d0b24001c11254072100c4c92558822 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671545377 1250 671544127 671544163
    0x61805030706050d0612020a0e07140a031d03030f04080a11031314012a030e061204150516030207050f010e0d1206030206220f0612060b092b0203 64
    0x1100884254007600004020940f00806d08012560025240b44107601603480c060f8100d400040c5050f11503059101d00c0d03108810207d9403a03014003002030140065141c082070304045958415078000d0004201c920406100e00315100c0781c1c0701e03665035a007142e01c441549820481412003100550406100402c2c4e1000c1e15690902c90618000d6192840e982131840141845142101106401c0002091050302c0000c031501c5814801c5c0740c6420b850b042041e412650b0030060214044103030700d001f010780070b00440c00340398000071900c0000401d0b415100c3c02c5a42c1c111110202c2c10b401400d80c001e40141908500c0344059900416520540c01d08440c00e10713005000c2644040e40710354119800032200c448071903c840080c0205400c0d5004102e55100c8c0041040c0d00021019151100e118541e10301c0c000350a0401201c2055036a6880017403040c00480c80480100786000c0d000901c0f001c030501100e000800240001d8508185164084840b1407182c01c03128504000701300300740060360b040c41003103074562102c889 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671546627 1250 671545377 671545387
    0x1a0f0a1d0403200102040e06030307020a0317071515050d050307060515040c170a090302030f16080703020c130209030a11030313060201020c070906030302060408031302060a0e040b10050406180503070605 89
    0xc80347c2070b1070f0142c40140a40c20810120000d611029115403d43e40c1000d01c04040c4801c03c0c45044142c4604e03a0050a80007000c80025182c490f80d0700314541400036107280004d070540380c0041100580035a14014010741c400c012070782c0000d00340c0d0407055000880024101c2d21200a8003c2801d03034440e00c10040014001c800d41d000d40801803104540c000591290422001845a5010b0f540b4800c0d400d0441501c3c2d80490f44522114554a50120243c0e100c04140e8440403c0c2ca07002c0e58038551000b1146c45949242d84901d50091907200391800c005000b8010501690f45880c0c040902413500841e41d003500081007903914011703a500c0b180f0028210b50380010b90b90010240e02e01d0401070181c200841c210b081c00360400c082680000d65941080d080b01314550b99495946a840d10a404410300139088403010406001032070304984036454681058034140802026041000040b041408801c004294140300521949200e054010840200340980300c031203031b13180c2d40040d2404000f13a200304002100010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671547877 1250 671546627 671546639
    0x203041214031c09330b060d150806061c0f17030117100c0f0f4b090b0703021005010f030219050a0512101a0f0a1d040320010204 57
    0x80c06824207a0384610300d100691103450016501c92075844900d4169890301b00802803960340348126401c015901c0003c010b184401c200580b141c072020700c00d0180c14003030900000e5050506050098155003001144010242569100d00d006e940c4824243e4284a0701c0c0340c503006030410003000f036001e01240c0c50005a21104400010300d8004007551401100707080c00b0081c81090b8010b5209182a116070910042c0241d080d8022158214402c601c000c0300c031100e00e094586120030321181c1c02030480d06160b08540142a010703240107510f0035400840013602c001d400f0444180040040d006072842072069594078842d0703289020981c0e1081c0c1106504801401c410401c500e00000c6e103601010301c01d81c0800c03400e49003e00242da50001d0340304c1c50b0b00800003404140c1030f40506010311008440811010480d11a2032082c2003951000f001c1c4640c000d0701d80c0e003036410f000c0c94212848412a65001094008234820302e030070070050200500118144030003403a0700100d01814480403400c941108000584991603c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671549127 1250 671547877 671547893
    0xa0c0b0907210c06030b03150c0a0801080312071d060f0901021e0601120c1701090309050402071104090602040e010b030f010603090b0a09050c1201020414010203041214031c09 77
    0x32003200d00c03500d00d00080003c0c0d01280d030100f111068200014002c1401020a041c4021000c2c40c0e02c1348451101084001c8590002401d1214820b54514000c1d83c1c98420386039580c8200500100310700c46920004071030510400e0704603001a44604584c8240b01502d01043d15070700030201000c0300303100120b0790861b03550341041102d074000031024002040504c502200d50700e44006006a607100200809048141305d810282c02c001420308040001c606841940c440d4001d2000c690f00718001544008000b81d145814001d4440154004181c00001d102c103004000c02080c1c61207044440c3d507024040011050944010203009141d0141420341e00d107049014420b43c5c58058000b201418945a8190f010551060380350350b0002141c000012200244d0030081e2508990a005560020805410300c7d00b03600c040d00603108840601d401d1002ea24080001a6103a020f94002d4000388800c040c0141c0120706c402111740301448094085e02c0c0b43c9084183c0750a45030301c100541c0420b107501c070100c02c802c0140701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671550377 1250 671549127 671549159
    0x10209060d2405100c080708070506072304060315080d17010e0c070602031e0c0c1e0a150212040b090c040c020c12070e0108010e07080f120a0c0b0907 66
    0x420704004590f081100151300310080c01103010800030705070010000c00c991601140c050541002110703841c1c8000b40762aa0351100d00300d03020400603444622152544001d01e6100b94103020720039605003010306100045009142901a1084d0581c003214001080d410074420381d03060b80d2a6a480340b40b205d10040c115030103d801170707200d0403080c000300d001c01444031004c400f0340d8082e55001d4005641ca884442e0038901641045c80803443c000000400d1102d02c1c4016001410015a40001d54041c83c48040b2601e98541905030703034220a4004541e41d00005540404451b208a40680014145242c0b643c2d1000064400c03107045403a0030140003409400c0d64200180c0e0140d11003258240700d20b4030300c0c080c000c0d103800502c1c03c518083c034900b03038400b90010b001380f00d000050000200d103036100f0740e036605150340a0203080c2ca1070304407406940008030b002800455650700000005006181c203138420f0810707003034175484411710310100075600c0d41103000522080b200078000c030310300e6005200c5c850820841c0f04040c646 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671551627 1250 671550377 671550431
    0x6010f08030405100509120d02071a090d23030a0e0109080105040c091a030f011a0102120307050a030b100e0901090213121106160b0f040302030714010209060d 70
    0x20b01040100c2c3d0365a803850340b10040f8078a413064441280c040818440c1411000444030b90040070109568180c0c001303140d0303088406c8051400f450110701022800a0701c15034040c50380207085d468500307011641e04010f00442d441c10350b11920007040012091420768118403843e1f00000c07210300c240c042540c4e01c22501e00243c0344900081219080c43c0e900c140140c00c952080111180e100d000c900c125600450703c46015060190940390340c040207104640c000d00707155400b14406888200c0c0c450055100044046420740d681e1302a61664403010020356503504052500010075031a040c1c1900301c0d8807403030318001001c8025101d0a0f00751607e4000c10014000580103526480c2c41071003105243c5d0100c400d031004a40380c6a0582440c1e004038145030180d01c03842140a500b10000040d4520b4103002d10704403807240c038043c1c01460959101c0c45c2c0c0e40403007584117442c0540142e2003400110f004c0b9052021185d40440b15030001407420603003402180f507907041045050b109540d200c00d00c008540740320905c4205407030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671552877 1250 671551627 671551633
    0xe0a06020a1430090d030e073b0c0301030f0c090c02030903011116111f0503040c08010b060d020d0932031e0c0709090b040203010c020a0b0a0903120e06010f08 70
    0xc0c210340310035551855600c40504040e00c40c001201f84010a100d0f1101426601c032980d1510303d82141d40001103d13218104100006504a00d0740c0120981d5200b0350080b040d09540c0c0b0324691854440d1092194145400d03166541c880400080d2220203125800e030300d0705c69030003441d180c1524904040c00c40c0c800c4080071049400070000110301031450309403010360650022480701025048008a65041c0714100c0c4c5001c13041120550800031900034028522451090000350070207034640980e90b003615920310510741c100300213001c00001c00ca5190054950118851000666072000b5101d070b85205004400c074110185c0d4041140c07812041481c211107140c86801c009502c0d05101ca22184840b03443c1c1e906c01d524513100400e0b001d810032400c3c0300140c01000004414801108141840315441c0c6060f07034224860b40c40d10203403882e02800850400881c41d00018990070640e510324600c07000e0301070000e0880400241484409020f0030038822070400c1c030230308402403041d50304010003001e1140c3c094002c802254 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671554127 1250 671552877 671552881
    0x4090f12020a2612090c2707030e01020c011a01032a0f090b0c07060908150f0c0409090b1b13180b0d0b090607030e0a06020a1430 57
    0x184800d01c2c0c041004040148450f03080c0d1000490301490003402c55150b601d03e1380b18240300060100050100303640400b12903490700c2840a0b940120100117620060441c00300790780000717070030b80e020340c0c06421040010700000d80303064810364000342158995203410f5004010030f48500c2080d6454414105070ba40252005900800044c000c100c9200040003010b0400c103001a41d00790b01449000c9500041224461071500c400c803130110719445420901032000002c901c5000090903907000a0302c0120078441b80e002880544421843c000c0e0101c0040018100700d508010002c5c114855102c0c00340b4042c0182c400da14541000411555120368400c81030006040501c0208a0390940340515011102c440000e150301d6481d51003200040c1c0410461240d01000200144060100c1c4d18a4144690610300548000703550b250000e800302d1710010762010141e0701c01c1c45048000b9403a5030040010302111b081220300820034000802c0198041c00c85e24542c0740105003003d0580c2c01c141078017a105070800610003268 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671555377 1250 671554127 671554133
    0x5030a05030313020a0806010b09011404060f12060503150901051024020109021201050403080105011b02060d14010f08151603180803011401020c150415050904090f12020a 75
    0x70740000780248440c2040c02003410210b64460381608000e0014900b941ca20317603074840940a2a42041600c1c81c0800d1006180109240200e0100d5050f940d40d901c4865207401c0c1100222040181c0c4020020026a9401d0101e4159420030007150042000e0780642d200d840d091250744e094400140c401742c98604810014000042c1c41e401101104094164100340094040390072070140c402e505000e5044540102d50740480c0c501900140e00c20b80c00f80d2182c01c103990340d0794011101c8d0945c030a180485003207048100001407401034000d1401103001000800c0000f0020100d5a603c40c00307a100b00c039488800401044098400c1c00a100149415011130010346803d51120039540c0e900c18503041099551909803000c0405a041c50340190f030444086900c9685400d500c03c2d5030404081c015015100710a2580030510700000c00350f400382160348072181802c0c948000c40703401083e10f03c0140140700d01402034828030b0300c862150510050085c04607140300390302814000344138202c2e07005610454002c81000c3c008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671556627 1250 671555377 671555383
    0xe070608010b0c1534020d0f05040b03010821040302010c080313050d03050106020f0304080a08130b1810031404110112060e01080f0303090705130612050703030905030a05 75
    0x4482c0b21100e0250303540070103041c3c1414048602283c4118080c0d0205000c000c3c0b05034440c21045220300000651001c00320284659021141c18286006901904410000346d1003501004034607400707400c1840c1010744400420b1003d42003608021415481400761007032007858880d904505950b10311903d407034181950002010002080c00c0a07104517000404100086526610714500031703005410b94900000c012001000303400d0038400e480040c42400ea180803188000300c110707812210f6000003040384c04d100c0d0f0b0b20101d403a0002d240e010400f480820300010a06614402840000d80000314900e504600b04208402081b100e683d0204061420500c1403010440d91001600540c0000852002650325401240e00b2029401003202c075038101132001541051100302d56050b00d040c141558a070541c4910026038900046a0082850f441550100118140030a1800e6903200f400c2002c94810740355030441c000d916400004851560000c5001c0061640c80990f0202821048000d40443d5509840e44c13a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671557877 1250 671556627 671556629
    0xe0f0912030f0a0c26010513060b0d05040321020c15070e150d09060501050a080a020a0312020a020a06021b040e07050114040909140124060c0f060608070303030e07060801 75
    0xa074081d9125040744c10380d8041c5042601051a03010b0b151156029480501d404031000e20030395010b402452030300c21841c207090261900341c906807181242404810114030780a040041c1050f0140303c03c403168502d124600302c2d070050450800c20400b690350500500b00d9440e007010304a1105104419105000e12254400408580ba1504907005000074000c0340d0303903a60074441d0408451640f440e00d0140420044540c01c603c1c1200d200711012140180ea6012450315140404802036101211100a100060503c000008d0014052040300c9841c075003a404100c000d90260840c41c0540e100e0b04c417140c10420b0b008008200c0c00c0d41542d080c4010204500403903501c3c0710a0003200e040c005d81c100103c40c103041c2d150540e002001124810702000e4107e0403b64a400603140b442c40a550803c03000041d0301a1300725030071140003a61846802c6051402d003045807241c10308a4100d8421303500c1e2141c00040307005801a04082c000c501c000d03104031842c51130301804440b0b075214491456007000401b0810305d904072114038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671559127 1250 671557877 671557891
    0xb0f070b04021903302007241202071a0709030506240f0603011505090301111201060c080a03050a0207020301050a1505091603090f05030d02040f050405100b130e0f0912030f 76
    0x241254000103540c41c00c12201d504684c0503003d23401b6840d1081c0c0000100d6000c08405a104c09440b0011660103205030b01c01c520f40a80b509000240c100020488401c0c81640b0100c20b19100c4a0207441ea074929040c6682a91884400c0c3c0700c81380c2000040300101101000c0c01012990011400148070218409000500c0f807001d000090004048601b0301400c21240440c0000703000b0052381c0e542c1c01080451350031208090740480d0094001141203402204064001a040a00581001040c16048000e00f100500300c21103180c0a208200040c0ca0900602d030041980d290086280014a0380f83c407201c1903d54025440740810000b40300351480c0c040103c1c0010390092801140c0745645e03003050302028041c40002843d40c4000074961101420550251003590f803500305010340603907550f00300415a041034452044024a83c3e1042219201c814010201651560349842d075040e500c0c0a07400301004221440c0c0f401110642c10000380e18000c0c0500140d0b501041d03095421420651540209210014600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671560377 1250 671559127 671559167
    0xf0506090f100308031906150210020904061707060224150616030e2106131103010e01020417030307091715150a0b0f070b0402190330 59
    0x1c80e08007100000100040c68006060365035034100400d46c100c01592010080c0c0c00300e4500f5001254501d400100c521613030505030f0003801810701642c041e40c001e61050303205070b50041d03480000280003610300c047c5110440114014000d140c1c60400040c1c00c00720310b00c0c88200501120300b040703001c1c840d1020f135880d040301c0300701c1040303c280800b80d0201c0e12a1203040c4142d81c01e04022500c41c4201039212201c1449a13005595690a00d88068900c60b503060020707100c0748694111000203031004944002ea031009074014940050100f54100102e421504c2c90f40b85050a42d40028043c07046000c15181d943d08101504001e514510300008006c003210305a002d14001c02203000381202d0f11804c200310030000004012400c02113030400016950003100d15004007809007045a0700054800d4071107080e01c2811088000740740c50a242a0b86280c514040100126404443e98045864070005050741201841c0715524220804803010464499500b2040000002500880c00c030286194419200303a19400d5078502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671561627 1250 671560377 671560381
    0x70b040204021b0a06140f070513030c09020904110405060f0c0327010f110607031d07030309030b0c090a0302041d0d05090a061704020d03021c080a0f0506090f 70
    0x100a88151911040d82c1c1004400d07103d04a100441e02002a038481e8a04020303100c1024680418001c0444900c1d101c1c042e1100047c511074050340c0100000d0200e20b040c155031580b246d880781c584e101d164110035255540480d449809080500c60f9080703061040d40034900305490400000d40342d2144c0c03481c0c0d030540c4001141244011070104140c40881610000d1180e10001510102d400740d080000c1d00e50000303074180b00320b1074064000d1602c24007045103000500140c2e910008141c02030010016104000b02c01c24458000d032010138030007130018500c02d40c1d814000130715500303260204010160161200071820080542103a031409060f00803203a040c3ea011408071103028000d186c40002040441080c010546054401c079070040040c8901101150f0400440c0d03190101118840c000c9482c5c4180110780e607011601600e040180082060300c40d00c110b46440019110328100248040c0031200070615080030f01c000b80c8100d000728540c080403440104014548070001858000c00501656040101240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671562877 1250 671561627 671561629
    0x307020c0102011119200a060b010503160f110303040506100b0406121503060207050706030e15180f030a1211030601020c040e011b0c1b0f06180905011508060102060c070b0402 77
    0xa446c100c200c00490540b5028803400403490711040200801c403503051518003281e40641c010401d036801520b000f04404140b010100c810740f2841000c1c0314640c00c0c003505c00114400f20302c0400007103124501c1034025000c60b0038140e008104060480d0031981400106110070b010303250340015400c0203040300d00c4004c100044406201c550b150038035003015150311f0002920340d0500c9000a0390104032005a50b0400c911800c0d203071070a0700c0c5c40a00c03c0540f1540e9208000c18840d1510129000e0300050410507100e6000c0c203240c250340f03558405c2c600ea03030209820800b40f94452550388a0441090007003480d00c1c2c558908800000c0d100c0002c221400d108943d10044090307942c009602465903080d100c403107845008154180503260002c0704030101d49401c4100603420140c40c02441e0f041c01c540303a91640c43c0380d480c2048416a401111161240c0f0507800300c240c0002c5101480c05540c0c02048102c1d004816900395410051001030024200c0341554403607028029141040c504445021b6004500a2a0754450784 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671564127 1250 671562877 671562887
    0xe120f0a120608010e060726060609060a1116032d060204060e0f040c05030417090316150f120b060d0204030c0e07090b16020315010b0307020c0102011119 68
    0x84029041860b1550100b0340381815070111003806480e8044502c00d50300c0e41000c9500d09562460001740710b001c0042004800c22000f0301c99042100240706504107106403012850941100d00088005003d040402003618414171156004000304400040d640d400c61716a0302da1066680040500740e84803054200000003074840f590355856105c002955180d9651030004c0c9060540000b092164a040ba0254254034040c4181d441c035520381d840300c074103503075450b20340b160f0003074010b249a008803c1c10004411240e0b028845001c1003c076828461f000f290402001e034030150401c800d21802e101c0c0740310424030000c1c1c00c00d2030030780351444c04080416882400c1000c10070601440000e000e149001090100420009000e003105840403032400b07811659850204a40014072403060700003909003040011111102c500103002d00d9800602181d40c00c0b008600c0300a01c80e01c00741d1018560742070100c144682180e06000c1c0e44200b031b100740f000b030100000e185044d000503c21180744481105600082d1001103000d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671565377 1250 671564127 671564147
    0x40e0a0522080a082505182403071b0609120e0a05060c15010b0415020613020d021203030a090516060e090403030e1e07092a0201020c0f0705040e120f0a 67
    0x22215071200c00400343c20307a0081960701e04540a03020759801c15023092614050a000c107180b4031203225081c0b03504940b41d03a10242828003040481c0400081c80d682c440403111400d48103a20004501c41d0324182505503603a44810a02040f820310f0003c0e0300c40c0c0c0c5000c044c4054034002c44000d90f8415140754481d1a040d0980307401c00851088000004001c4030140150044480314050f00245207003060041f601e819045540940f1908582005400740c1050210104012300c00360a1441c40c10180b550030385036820032200705505a4507002250104a010711003403110804045900340d80030f0070010050700c025506110680210352440008003458840c1e08100c1c41c507003c0c2030540301850942000700c50140030040c030101d04c601c00c2103c002400c0d24540300740290a10500021821515102910a0701c2d18594400000715074081c4401c0c1d201070002c1c40b1103108040c050009000c424580390a02c02a14110914603986821980c0e80f1010180c6402c2200e01c20940d40f61040c1d42d84040500c103071214002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671566627 1250 671565377 671565421
    0x2070e130201210c020a05100e060a020702060706020f070c0816061b020d0308040611161e0213140f06030c0d0303140106030207111f0c020402040e0a0522080a08 71
    0xc10500c080080d40100b0b85001c068050700c00c2d242500c40c001c0d049000d827050405a003101d070b0721903030004400d581d20b0350181c40ba0920003071a0b40d1600d0026140c0000780e030403085501c03909001c0016074208000d10006008002d00d03008020b071600c8200030602e80040806071090300c05004580e05800300310044200c2d501c5940e0390040118800343c42608004081d0341e0100c508541c1c1504c1d151421807010b101d50141d81074003005000303040625241e5680c0c10020840c14040b0925064020882401680d450305110001c1c5206d4400040146642c600e8a00400c07010b0403110059240d841803041d161000300711a40401d0f02a5290448101d0900d000c4000b0446001031190900111001055181d4950024000d080c010360004a001071404100b02c1d410b074401444540c83c520500000a2841c040e1424014240c00104010708090392070384421a4094116969211156540104a0242e44c0c81001c100c3d8001811004041c130502a40c0b40c030a203100d103040003401d02079064000b800c220300000b200103440c82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671567877 1250 671566627 671566631
    0x41104081b0108130c0b160b01081f09050304030822030f021f0903260705070f1e050415091d1b010234031202070e13020121 55
    0x80d00d07444086400c4800c0360b00152102001c100407400520f40448810f070006100400c541c500340040f602513025015002c1d420604010010100d440342c20480e008108400142803800300d02c46049199030038504a12160b40d00d0015902c0106a00001b41d0f02926400300c2881c3d6504c0200003141c080d9040c55400303001090500c0c070048108510000090764941c0f00341d5000f5900354110900705500c90002059000041007442d00300003091910040c0c40242041d220380c2c00103090000c1c07894221f80c0c041c040558a075804442c00304200c0e14a4079540c4018003154000c6d6901c81c08030b4500c46914034042c42054852070f00c643c4140c03881c00e141d4005c0347c020011944100001000361040951046806002e041d40340916507842c555501d0101c0c010011810503809807a030b060a4540502c01100b03801c00103c0201c0124211000b2148030b0200305004e0760003054880c2260a48010003448c0c10760316040049011202d105200c40012002c212505403a42406c20420701c210b010140743c054103000035190a518 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671569127 1250 671567877 671567893
    0x1a1c020f0c0706030f0504021f11010903091a0f030406020a02031201060e030d030209030c010c0609050d0c060b0105091819110702010912020d02151c050601021b0a0504110408 77
    0x103000295002101d0076031310300740105178501159100301c800c2146c01039000520f1071003561981058158100d8a8840d90034000502c0002c20310050844c0d40e004021030115070014024012032820b002e280414203000b90800c0e20b400404c0395034105501000d0030080c00c0c55008a814800b02d8024010345082d00e100f000040002e6a40c0e200040c00205200030181c02401824198004c4034424002c4440d00a4064010a00101520011a90b4600313540096a102c0d0741d441307020000407428407404038041400d980b20780d40a40107060080844217200040350500804010514060716504282450030668843c2040d095a4000c00c2e0501e10441140400106240c40750803844030301d1280207070141e070f0300130baa420080300d403a110302c490100d0391580069131001b03070a00103c0043c038015241c0a08012000315140c200681c03020002c0034007411400034400a5212003c1044a590410078a1045607135200004201c0300107030041009480c16004080c019903d900440c0001c00701c020840d8028079890044034502c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671570377 1250 671569127 671569147
    0x6050d09080f0d1503030813050a1a0403080a0501050913140a0c060e0306040803010905040c0911091008040f0b070504030f0b43030b190f1a1c020f 65
    0x43e8041407800368560718020804031410700c0a00c0140549174542c5401d60070f03461311081070361010f28614040720030307105008111000441c00c1c20341c280c4900426901c15024107103880c1c0a40184002482440c5030351415004011039503400c0700d6603400c64888035811032058004d05241c6001d8210421541d09072142900381000c100c8210124021518541d8070b6030a0031444070704241c2c0300c3e5000e40c1c01910314001440144940301c017035800b1540080c480c204840c1295600c8061000742c1d18420000002031304049840d0a5074140680c1020326400f00b03240c40350352441d00e60b40c1e00c02c901d456080d014002c40d17001030001ea2103500503001c1764003179074008249050b42d420b545485a0014401c645800c08580301e030895804108083c160324215510000c20101c07140d07a5505000001c1030048021400c0685070300041006860f04007034640c0c00e1015a686c40d000a00700078001c2742c4880141e03c00c900040025840440c000d1860099552000354030b02d04441c0c0511950000307020340101c0013018020840010761a041d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671571627 1250 671570377 671570407
    0xb010c1e03080a140a020d061508060f0625031107030c090c2c0a050a031101020601320d0b070215010503010c090b0307120c03020702151306050d0908 66
    0x4003038800d07500c42c1d074182e88030f6032040c040d60055070014900c181d1407004203080c0d25158015140821044200040140c0c0d03460560104156222000c40440c40e00414804c1c9414107040f00034610100f038443c1c51822044034034012100781c654180010016601c81081e08051140d10303045140d10554085800d0241c0700d0600300301448080c030a181c1c0341440c12030b031044002e01800c40d004070720b2a0304244101004004070341495030311500340c003150300556005020480d99115100e0340050b5000c3d500a01c1d4941c102000a8500001a00a0300c041590031110902030314440c0180b000340c0180300080110100d030700d004107100ca00c404a009100c010600100301c0d40660000b895028005160b0641c0440e903a680181800c03075510b011618006011171130180a060200030080d5002200351829143c03c0d808007005504507070f5001581c2c400260001002025850200103101c00400141a0306140c0108130114240348042d5100b4141030200124510355403140c0d03540110841c42d041012540d403071803046c0300940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671572877 1250 671571627 671571683
    0x11010f060b1b0a030e19080303071d0117150a09020309011407080603101116051f11031305031c150905040309060e030f010204120201140712030b010c 66
    0x42054207014468802d2036001071005040390b016111075071000e09080504c09880c0c0c41000045c034980b481180091807500404c01175204041580d034070103224440e004000d02071010031800c24108540034807180a0a0014031403130303800c01c03191003138142d03403186441c042400c0d14500e07408640014404010030034050819002a00c111001d1092801d9039a00d0718001c1e52400c070159280c86e0194490309081c0f030860b10383e500041014510004060a04c007400d442d002d05035004e41001c44054001d80c1d0040d5140c440c0707540745402418151424440940001542c000c00d0000502282030381758600c000c0000c0c00814011512010001e043c40700c0e2542c40782032154003074606e03408400301380700200c140011140d0700d5120b01c600460341540c0b030041040c6022021074218800d1000191b050042420480c2c00081c00d1009100410032a950030366090000d000261400304446080101144108076400000d00303440512550034680c1e0500003082142a00100c030808281e0340000d01c0c1d10071149821900310300200c2d01c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671574127 1250 671572877 671572897
    0x917090a0501050c030304151d010c02011a283f0b0a09020a170601150201020a02060705130510080405100605010f0e0312031006110d0f11010f060b 65
    0x600c00301d0791000112041d10807000210542d030003d2000c0340c001040c52a10540341007100c0c2c40823601c9502e01c41954540403a00045a4460703544c0c045c4c3e14413054083c01101190310945110101000860001c5800e44031905484850030101c000c0c0360040c0d08141040ea009003c4c1d41d20480091041d81054603d400e002100c180c4240d140c400c02d0035100441d8950b98000740f0f901460300016a22a81240c1c0060400e440c0308a90003058014042209400c0f46c2040650500d03031002040b0f21b516010541da40700c64130400040c11640100b010491054001030140d03003194680c13030300750340c3c442c03000808111050894002a900125180000701031035841040c050065021f60259500c6201070f80c0c221003120114072985020880080101000c180581401148080081c0a94451905814007000c0540c41140e80c40745015901c203040c06644e901c4403006400500000040168003c0c1600c040c10000c1106041c02c2003005103030444200d820203401400c0c0306400c0b004284210f03620341d0700b40710301c5070003d00c050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671575377 1250 671574127 671574139
    0xa030207120c05100e040c05091c080a11160b0c0c0d120302091210050f0c040e180a0c0801050741070b0c070311010e0c1201091709 58
    0x8600071264808202009a00c55603030420a0f2902d020702c90441c8402c9409070600009400b209106d440e503024002c9140c01c00d030744903039a4100b000f080100030300c44500b00040c41070500b03190b00b00040d00d8104590003040541030000e00020300241031460201c0411440d0180d00c101400000c04002000150898114070002ea07102c660411041c0312000d808504094049000d8040030900300340240d000b042c130390401500e13160000b290a04441c0c5400340903103010b488070703540760204483c0315014032200390810800701c00d05141c00d1800c1c061390b03130008001d00885035000e080301e0003003000c00c020040c1011181c1d00041c2d0700c09407030361407500d43d000740f40c00c5070408049008880c15040310321401d400c03c0c2c00d480429580c0000320117400c0d000c0e01c0000300f079020401219005c0201102003902019a0351003000c6989006555460524000300301200500d03072000345a04242103038408020100d0814401041560a940c0b05c044101026001d4028407001911a5081d00c0301240541200001002001c0c410344103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671576627 1250 671575377 671575379
    0x40e070f05031005060903010f05090703030816020703030f350907031e0f1502090f06030906040b2805010807080f03040608060a1a090f04061401140c010e0a030207 72
    0x10988082c441120090a0f00001000c188850300e0454094407a0303040c041d00008603800710b003544604444054410740242c0d80300031001c0082551281d400c0340e06c00070180400c2d01d005c002040180d0759159900008040c44400b030244181c3c0c81c82070320a0f070782181484012010031034272807884c540c201d502d08008070340009460f030005603c03031310001d5400d080303e40c0004280c2d1200185141880d0b09940e01c4811201d01030326248810116151200e01400ca240322240103075100150010099860f0324103120500a0005001300580ba07000031680700c2c0d019400c0240d40c2055515403049105110004a021004004d444014403045169500c928180c1c2e02c240c0c121942c117900c5614203640c50b024001d488105070300400003404401c1c41344106e00d070000e80146c000c05141d0340b01c41144602100b1a290244041000700d00741d41145440c0000c2c00021005443c20404075040410001d20805c102414071305101200b0440d1a40c0e5000504940705c0e613204038020894040003a000640300c3c42c050b40180c2c014812440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671577877 1250 671576627 671576657
    0x105040c090e07020118231207060b040603060e0709050714030a0903120510081e061816030308150a05150a1206080604050f0309011e02010f05250c0b04020402130b040e07 75
    0x1250101d1041c0140c92314103044440d50f810001d4122845401e40298440e90004001400c0c1e0107100005409403025003001401c00c1c0704041280d80041c02042040f00c074031030322519035005508403500300c0d0740c10344040f0340204141003d851880d941d10428051618110410494982038403510341070380c40307550584248040752000403104910480c8500b1054201d8808540720000c60349544401c1c191b008255042c510040c0916107004501d40d2081c0d002c00d00325030400c10501489003035080030f02c000b1034161846500703040202c0c2c00d00c1c40310007200070300000001c1c010715054052480d40400d207140354018000d42d84c40e54001031310f84005440031a81031007225140141510040700391030100380c06a460060090360741d035070015242e484032540781c155540d440044841885a0103801e115003141e40034900c4010201c0100d04d00301c100704e440a07007041849004000050502c01149420540480780540c4030891540c03c1c00c540300b804d03444030140d980d00050000f1003038940d0003410700c01c50303080d15100b4a605182d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671579127 1250 671577877 671577883
    0x902030a0e010e0c0103270803060a0b1207080a1418150f04022e0201061401030603030504230d03020d170702060a110f04080c090105040c090e0702011823 68
    0x181d0f440243c1d00043c0d282941940710350302c0790529030381c0380c00100400e42180034242c00c00a241e80c41a500040c00008000e494108003217900d0041160300309552070104c2d1808900800240036081504020030071001c40c02c415080d800c009045003d00d1440103d40c10100b0754420900001c0d000400140600011020301c01d03903041e01c1d20b110709900050782e20313641d03555800c0185884a07400c80410341061005540e5050704002750110040029800000396070b414100c0910700c103c0e0b58091141010308041041c000a50b0200c01e460403102c40f00d00206d07008aa1000340b08505072000c00440c2c11020651400d0f05056001030b007514002c00302c0e00c4d0480c00d105116040c1250741000ca52003001741e8000c40110704041050380c4043d4500003940d81c005e0800001d001d407004070380d010380c5c040701182e400305c54421210b140000c0281c0c0180400c0f9000c00050030f4134003028054610030712880840c4461074000403500c50003034001602c0c06001102c000c07000e80e818a09003401c2c41611492090b07520310207826048a503000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671580377 1250 671579127 671579141
    0x609020301051f120603051516020c1504030203120a030b040536160314210a05042c16020615150a0f080901020a0e09060f0a0902030a0e01 61
    0x280002c070b0202c11003c0121840a03c00283d0010445203200c51241090709124502c051441803000d88030201c09803944e18207a400203000c0545404040c2c101d081e5998001811009020041d46d1810060410325001034050207035620180d054010000c100040a20103001050100002e840410002d4400e8062004407503085644000701900610508100070070684001d020502014121282c042c602008609020300280045400c04441c1c0c4140100480e840b84123502500c4100140300c0b415070078503d00040100c0340c0311044844c5002403d0f8040c10b100d0300466018003114407544030201001d1048140d1001c5110080c2001d8007001c022070f0b01c4007402c42c010305040d40d15500a02113500e842a2052251007031144e0164001c4803c00c0c00c0b0f40b0014050081c00343c4401544600e0301309080c0b40006091040000d0680c50350364410404d01c0340641d0480c0d04801c034200d05881102007607131100080740b00714031034200e2141c2c80040041c0005195200350001c0d481800054000d119541c007040307240b0701761200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671581627 1250 671580377 671580379
    0x40c0e03100e0619090c030605150d11010509130c1d190608090f0703060b120f0303010e100504051602010e0d0527090a200a1707020c041e060902030105 67
    0x71180100ea40d00d802e0320310300304c1c401c1c0000c940050400c00d650b0b0791a0580ca120303172088402c80d48410170801824aa0000000d00304130039500107030740204503aa040070005914000c0ca050007008600c08080c1d1700c44460314a01c03079a00410401101c60102c00207013011641c3e800351104502c0300a030484036030034200c0c050351844202406148070582400000e03a044680240403207418490701501c008440010080f18004600450b00050b0417000d440078004c000d8074408000042c0d034092040801211000401c59044641d02102007500d92140d4515156242542e401545d1060a00e400e20412820710170041c007083c0f40b6034008020700030f82404125107807000e484009000c5403060040481000312030070242041420601c540401700d2082c00002d030000380960b486080b80381d640f190101c803611218032805182d07007a01505420880120300042c1b800c03001680114052008001244c0054020007024a044500501c00d228602244445110070a446403020025a0038070301d0000e01c04860340300f22070690360 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671582733 1106 671581627 671581633
    0x6090b0f0402070317150d12022503030c060905062d0103020603160e0a0803131e0308030c04030b04110405090f06060f0609040c0e03100e 61
    0x3400800c0d8001d0b03104005180100390401040f00c0b82032015140301001d540c5020050300d080c0351440020303030498804440741042080c0b89500205280e00c0d44d00b114540484c003100010030b02030002109103400c00e025014800b10b4802e403d2405068051280828444055510315260080842d00b00b00b2020380400c40c0d140b04c28402c5c110b14002c2102c140c170b54650b54107540004074103120203404a002e01c3c14900d01c0d00201170252482360000350b4000d0516244d02c0c0d03110550707500ca43c01100c0007002c0030340014010070302190f036008143c4031002030b5000100300c038259078a2640a92018090b545452400d210000010341c1c2d180d80c80f0f00c02c0348244030b407052403c0800c2c01d10041e1603000d071403400700e6000341d450120132100000b11941e0100c4101c6120700204040008640d03644241c14026800c1810904180742d100c0c0c10070058221b00900383c04942c1d5007503032030140c50200c441004811820350 = true := by decide +kernel

theorem cover : BRFrame.Cov 671402877 671582733 := by
  have h0 := BRFrame.cov_init 671402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671402877 ≤ n) (h2 : n < 671582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
