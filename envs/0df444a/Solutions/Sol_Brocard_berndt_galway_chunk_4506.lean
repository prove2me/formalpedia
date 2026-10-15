-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:45.544727+00:00
-- url     : https://prove2.me/submissions/0b9b51ba-958e-47fc-a5ab-6bf87ac0aa94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810251798 ≤ n < 810431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810253048 1250 810251798 810251803
    0x1f090e09030403020918011107200d021504080102040b0712081e060a1205010f05060d0c030602070822151119030e1503060909030c100207033509 64
    0x80300c4026481c0c20a000500042ca4901e80e0580c21281354010b40c1190f2299850b0381d42114248048043c1d8080002000d0040105c110841000281d50300c020120701c4800f034000c03440b464180c2c0d0009200b00110318803414501c000a083d5005420400c1c000c40d01c0b162a1020142540d0240070143c55100c0c5010701031180910842050348240710090b041b155041e80f035030b25981ea601c40a004258031140d030201c040f0b8040b18405410030502d02980c00890307a030030508140001c41e0400340269004032071006020000ca090402034208582d4814401650b42d00700e820024194024100311424404c08000a183c0c00c4030865110015505084140245406c00c448151032181914482060a0f040139814800300300c650f0000000c0c5034000e08266403042e241c81c0000e40d0707244034000310011200d4044140840303403c210440c2940718000b4401180b51492410311543c0da4100300e4034103800e07160000750400406220b4801c80c9100c1c12608003e00703142c148142c04924000c12021400141043c1c00d00092400000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810254298 1250 810253048 810253051
    0x18090203010b06192f0c0a0e070c030503150a03050a050c0a1d0712151409060312160818040c0c02093601050f010b0307050405040e010b1f090e 63
    0x3400741c118002020f2400c00e030303a07540d01c8800001754840c64050781d11040620080c030307890f03003108000545021014401046a880401d03040804040d1a4904201c151a04007558406803a0941002e030340307a0341c4450601c10100214100e0580120b940080041006800034410b10f10274482c3c0181c8440e140e400d0b0522401d903039548540380b203034aa0f02d041b00081021800c10690400128a03040c00303a034a02180001c25141480201041040030101c10000001524400c11020b80d0882c0d0401c01c030304001c00000d54840c07101c24a20700384100010340113944900c180c8640141584640001d496012400c2090009055502c80600840c241110030091520a0b00050f0a00340c0c0280a8185600c4d407064000c01807420391032640102d003110207220309404400156000700b600d5000041400d182180001ca400311060f885124480d070700380240626507410000b61829030300141c1d800079501c414402280e0142c03c14500258001c01d80501001c0d8409101460641c180010703191a5291a0354103095005e2600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810255548 1250 810254298 810254317
    0xf13080a0524070e0d0c0e1b1c02090307030c0b0703030501060804151a09040501050105010f050304030203070f020a05061c0c0f050904051b0a0215071e0f0918090203010b06 76
    0xc560300081c8043e03005148000781d0150140c90010040c1c0740d980d555000c20402d4000004e901070038400c00080b50781d00c03410b815514088502c40c5041520041c1050b82c00e9400265000070b064000c50101159101042522b00441d004100910b2003030350342c58541450f901c03540703043d000030f41840b0001c10340c0c40c0501c0c1c126000340d920000c184803980344090401e00400c514000d8a0044101d40040b200c0d6503a0060b0107801035008400004940d4980f00016185042040796041406824400c2001194001c4280c508081d000000c41016080d02d02c00a000e0010302c0c0c0015a002c04013040501740d101000c1c01c103440251404004000f110291041520300701142e076940350009100300000a958205500265003007020030448a52603d015410100d003904543c41290051384044049030b50038156144007074210f015414503400390304a400a440c03d1808030307140320060002c0120008240d5101d1f403030b520010003c0510700489090703428a00c1015082003001a0b1081d0308006185d500d0341780000843d0403640 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810256798 1250 810255548 810255613
    0x612020607032106080304081501030209040b040c0306020d0b0f0a15050903031603360303030911060a030b1f05031605120c0703110c010e060f13080a05 67
    0x107240b0796040743d0400498106500005914019a0040300f40340030700000f400c40310000e036441d142090101031514401d501419140c0f0f501400400141e220041950380182d0408562a2150750700d04004284d0440c503030005001c41d00c0001c091404145590104d40e24400c02c4607101081d10480080220105040c00389078441c1192210240106000e14018084000040c05036030920052b4540a810302c106040254003041c1960b281b00c40c00924118003c00c4840c0500140c4105050341c0028075141600740001014513954a0b80442401541f800710041183d000b400d40c1c0d40c40480400c01030280c100310b11410301800c00c96515040c1011880c0034002c103050307195901400c6036600c42d041080f983c822400c18060100c10030400100d9103809416a2003210141320350342c2d5032089894020043c1d00c00325110301ea642c10251840d042c0c0c1c1ea000ba59120200c00840f8850303110101d2114038156803080b04040040b001064030b0015042c100803a07403074030803130003002550901e80300346205a008000c4100f0105480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810258048 1250 810256798 810256807
    0x6090403080a0c020a0c08030c070618060c150501180e011a090709080609010c0e03160306020a090801050f07031407022d25230d1403031906120206 65
    0x2a80d400001e943c0707110f10495003a031a054a03248140700f0780b13406c5540305401c00034203010940002c001c3d8034000c007028508000c8500c40c5408074480e000441c002d89080100d00860b4400303204186e0300c3c4002480c1522003c1000d540c2d240d02d58a143d480c107940c2010780c1030411104420a21381031055840d00780800071450450012082000100d000040c050014402041030103d4400c1c404c001042c03040e4092000011100b4500f140500303074030503441d001407082d405620600c066000c214a054212540090050f89070484c0040070345095080f41c12401d00c661070482000341a422218012740030300c0c400e803020082e0000038105064460030440703406002d0380c00440320526049000138400516040c550501ca1155110840075040c01c042844011010103003d00074142c1e10640c1c5520402440c84010200c03030a11419205948419280030742441526114800e4041c41141882c21743c11141a02c103072581e0b4a4000c40d480e180c081c41c9811464210328258000c82c0c4800c3e01d04030603c0168000b080d40e42003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810259298 1250 810258048 810258061
    0x30310031502040b1c0e0604060c17040213050604020f0c01090c0504050402150c121b0c0102010203270c03070303080a0b15041707030c080a1403120403051303051e060609040308 78
    0x1403100c0d0b17000d000201030392010700c501d44203010700c46180100d11907400842c2501c60048014800c028105498100a501506002c0140e07984100d140034000310746004241a603400340010b009024001078910703071050008001c1d041e10010350000201c14803448a044040f41c5031000c0c00300301c2c0c0701140c00a422003440054800e4680c01c607800f40120381d0404040743d00020040b9025400c035000810391800c9100c444800221081301070040700c040300c100388000c508620706502c07007960404c0088041c40f820304261101d4200200c09010038801050041c0880b0340c05035407032500429075035080703441000703082c03400c00f843c0c0c4545000d6103685113a900381e204c6503080a05010714214046000c441d0b11f80c0c14450f0240000010b0b240c000d00078001c04e0380402501c080c040605003081c0b8620201c14011484e0002c00950101c203180c90521500183c061070000c2e1501441c10201a00300b00d1380c0c00244c6070748540e03800043c000641c4a04c00d10200c22100548040e516044244550a90305841c010080707003001c40010103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810260548 1250 810259298 810259327
    0x3030601051b25090507210e030c0d0809070b04080a12050c060f1803030103200112020c01090212061605090f092d0f0601081008030310031502040b 65
    0x107041c60030191211282252030a0210f000402441c01d4203803907440c1c081000c0f032080d00c16103500a00703d060507480b05026100300c0c40b00140640d10f488050b0790b5070814010600041040c1e50500a440f011180051101040540900000c403a6211240b280e0741011803030210b40e07403d4900701c80c5080000c00c41c406043c0c0d17404840305031180709841001014007408045000c1085058020002c20710582c8850800909803203118400c0e0b0404810769200300010000a807882c254038034060f5608020540910b902c1c0c004941510101c552155403e00104410091190640c001032025100b124401c0200d40c90f80046a05c0e01d6044038841c106150600045800b035001e00020604403600800601e40c519450000480300303c0192450b071303194007601c030207813028910006110b00c281480048403002c51521000031035040030001d04035030400c1035800c0801c040001011400300a00010303001c0e00c1c0c9a291100d6031015415041c442911250084040d00d003203501e0a102303e801780c0d6000c041c41850b094803c8000d54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810261798 1250 810260548 810260587
    0x1050303270121150501090807090c0212030f09060f090d0807030b030d02031201080601030b040f0c150f0f0504080a110a08030f0d0b04020f0904050a060e010605070b01080303060105 80
    0x40c14003461001c9211621508030380d144221070030354000164006180b00241030141350ba003140d030500c120070f4028001c202e00060408100e94101002041c1050713100c40403401d000c10606c800180c00004400d1183c40400c00c00308601c10168041100c0c07255940550380c0303401250070b582048043d0401310043d103400d845000d0850740310307405013004905681c4480200c0d00e81410740300410010f80002c50358084507400110080d0041c9a01070080615504548a111101002900007080c0d50b0b90f01c0c401c50200700d0040c0c1008020600103481c090001080d580180180c0d4800e00000009a030200800c1846070007801a5410349051a00408418040742e841482c1241000c921a601c980820b200144c0848100000d18005d680790303c1c3d00c0c4d01d070102484c0084c156031150483c01e1085005018180c400d4108500765580300700b045a000c40c407510b03800c01100040134903810081051103600004180c441d0400014a00e25114007030400d29a80c0e250145a100e0006803810b90004800700300415900510ac03140d030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810263048 1250 810261798 810261877
    0x50402030705030304092405010e060319020f0403140708280602030c1c020a05030f0a0914011a010212070605190f06090b0906010804081602091e01050303 68
    0x780e0380182c54000003032840d040303648801101d5403101c130070040700003504401418803880a4075084050382003100180069100800082c01550003000107248903005010140070108801800c41d6038106802460801c1da000d80015956142d00070b035000d1061030002110307412900c19034090702074070404800f1300b2585010500d0500c0101d1030442d00001084651004600980c1392040321a1340321840151615864410751624801d07138414000300d249240c0100480740d022224100c070103410350b0340002040c001c1000d10300250031203d03901c240c51000201507004611070300600c00840d2588028100499440c5400c6c4042e0550b82028000003000a14541005070004065410f064050111916001c1201c494216078044181c40764030401c0003c40ac3d205141d80782e0303025100032910703192460002c1e01e002006040101704c842c0c0000d1a4000703414039542c40d8076a50703000b060700009041c03400004030440240364104400190326400042c41d460000308030392240500741c49110342e50781840c81008003100145410b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810264298 1250 810263048 810263053
    0x307020102070b10060f02030703120b060706050a0621020a050d080915030109140f190209030a030c1703040b0a0902011b1a0901062102064302100305040203 69
    0x90001041c614400b803007a00a65000149141742c58801000e000c8400c500301e080d904100041030209a200f0301c2d0050501c80c07041e0101e4201203000211359140b080c0280900a02c0c982010320500c050300b40c02c15800c41d01c18051000702040030b1b08600e08409c205c100c0c000d52020303454000b00315500b4546c03d0300411901501c012030a11080d5004540c07048e40310502e503040004000018071020920f8803a45000d900402c06007000346c0361000c00c50050707040c094501c000b40f00251022084280940c1c0449244000140503501402c01074a00038049141d0f41200300d6001c010b550300300300c00c10b40140540748126005100030815845802084000303002140041c3d041201581100d40645202e5010300c0201e031043e031034050b00014411500b0000e040c058100340c0c1c030340d04160042040811643c4080c1820011000940002c05d0718030004a05104400c00030110a4029410300c05688015900d290003a14150f014091028004c000202e0f4060300c0c0700080d0300c080300825299145100ba44200d6020b44040c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810265548 1250 810264298 810264307
    0xc17040203071a030604051006090e0606090a2403021303030e041d01270308040305030a020c0102030c0c0114060312131806051c0206120915042009060a0308090d17090f061c020307020102 82
    0x12900300341040d040542d151580c0714509010183c0400103003240390c8a4501141401c840e40080040c040b81d0f1320001d410881c031140d04030503941d2150b002e480004011004007030036410500c0e10038060a840108040101c020201007407a074031046811a080179410350700d05070641e5a50380c0590b80343d0000b0b420380b81c140384c0c03e1140c0d09420109200442c06030301ca0503825601e0342c20107040107081d60090b07a0405400e0442138140001c2d9140010270034403141c00d01505075282d00b848030010401d103010f5800510050300700e440d040491a1564420410341d50140c03008554101c18000c5103800540c242c4009402c600d00f0052603c601c0442c0e9181c50b0009400004d07209000412001c1080c2e0f40303821b403402d40b61000e070760000c4840c2d00c1008400c09030007030f42560004480d1801000141c00300d95640300c054840140000d8404e12540c88041d070078007250307020200122481c10b41d07120a065400c55004580145201c61145401c0c1c13400030280c0b144000307100c4c0716021510200c09854081d410261000080d59000e00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810266798 1250 810265548 810265567
    0x51b130305070303032703020c0f06070507030c09050705040807050118050603072c0f0603090a020a06031a0a0341011e0c17040203071a030604051006090e0606 70
    0x640b00460107540c0200b8001445016404c0c918000d07203c14100e46d40c2d440e16800001c1d004078245104030030860710151202039034404903035144542d00005100e4040c2000100c1086180fa1618054500c00c0808102ca41e0391800161742d5482640955180f941c000003007048290311030040c0c0c1e880204505249040b45542d034001c46c1c855002982d0920201c0c10100c0700b210054031621114014024103426030924080c1840481c0d42d006100c00402d003c0e5400200280d2181002c001080c9559030180000302581e80d1800f000300101030303440d00082c02140880689003071780781c59420030041d25046420b0320240e21403c0d1a1101c070880301c003070000e40350b5081c01100900e20484000058002d6000c0c8c000728412031141e078441204c44450f2401300e0001e2401c44804c1c41e56600608a000c540e60b0314466801e15201c60001074508070659000b00c5040405201c52000d002c886030255010348000e503428046515404000d2a401d1540d01a0800040c0025401c1041c001710003500340e00410302620651a04500c20b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810268048 1250 810266798 810266803
    0x601030f080d0c0507020f1926071512110313060e0303010b070314031003080c0a050102030a060303020d0f02060a0f1b0c0c1a040302040e0c03010e0d09060201051b130305 75
    0x90340c3e0140800d101180c40000c0d41004d0301a00b4502c0d004617055071070304d258800982441070300c80c096020280074400600c03121241300030010354480049000c0b00c022666940c8410000a0340402140002d1407000c1c20368602079080c042c0344824400b0303c9140d82980e03034405c002c81489181800940710291500c4210500500500086000e01a0b9982490340c034185810007404e4150040403d0b4145d0008004000750303501006008000e50764000c402580d19000d0000d1302d442c00004141c0600f540d4030010901c4400c100e65030001007264800e400f038a002e08880c08003035486945501501e80541c01c41c5001802503000c65000702403801c40b026002440481408606031901c914000e12804a001c03800d02d8000e001e8106802001000c1040302c0f920700c9111007500d8040c500440c80b009021700c1d21116000c600d00000d00c8088008100a00200002c0816424240d80c58000140420100d1b09aa00c089082d43c418000d0780c1c81801c843d0191704002d010b20b21020050350011402d603000c2d2040078070100005106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810269298 1250 810268048 810268061
    0x1032a0203030915010503031602270103060b030c010804151410031b0b0a08130b19050a0c091202010521160504030b0f04061e0e0105090f0601030f080d 67
    0x640c000e584030302d4900c0d030035458401c01c40e203503566411502c0700400899030004201c03910045849584002e54041c2c3c40450030000d0501183c08100042c40d0345040c07250a50f03001035040304d004200504c0194a014141511000e032031041c54009102c0c0d60004001c078194100908e00d00074500340000c0c540090402c8592640d8040d513011200c40c410755004c0082c4050305980d00100146c004180f06414500070303240b000c921511070b080b0309208140000030028221600d105004641105844420340761940c00c445880c054288501c3d0618034080109199107030720310801c11a15a40d13216001c3c5035040140725000e4900d07804049041050401a0307030300200c0340c041941d0994191141840e003e007000704145038990f0f40010800c04100f002d000400124081124081c3c010104511010280d141d40c01c040014100105400544900540b40032040311041e07400f01982c155000300030490340e2615000c030344e140c0d4035680c2a4003c9070b0045005101180c04010180b990b203129804541c03030b010034042c1401c180c41c1d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810270548 1250 810269298 810269381
    0x90c090307060c121701090c050f0406030c032d0e010b2805030a020105070803152701121214070203060a05011d0403090b09030307051c140a0507020103 67
    0x107500f50420051080c1c0013007500d0600f42012400350461034224240584148141400c070b6881e40352007001c07180070703008036459595400d00d901d0747c0c2c948614010300a84445d00c68240000d18001981800c3c032015420040c41c7c0c0c0011a5010302e6894401e83c1002034103038030301004a195615080b0480b241d84d2032802c0c010f5241e90700c1c5a031001603000c62411045118540c041806500300c4583c141c0180c0e0305c10112155030764409140750300e03900c80200c1201c03a00500038801d600b18a510b409402015012002640c001e0441c0900d110075a0725601012a007140d000b0b40144070304e556a00d0403107214080c01051004040050080d41008001d4000070318200341622120341c0307956a070f40103022078040411800002c10f0101542d42c0681400d95006108406c144500a003622020518102c0c95a05100711640c8a80244c102c403d0800900204044020410040c5c00070030820130294000d02201c80c00c0e200c00a001d51501ca0818040f5001900503089881d1508102000041c500700c509110756000003071401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810271798 1250 810270548 810270557
    0x3090f0319140d14030a0911030a0813080304030c0e091203100e090307150e0f0601090c11150403031a040f0c0f0e03480a05090c09090c09030706 64
    0x60b2140203810040c181c0100020860300720810749040103100200e9070000901e803400075890b82d55081066010498145055250180901b8881070250000c003074510303883d500100310191a5240f110380d03a03a110380e100080c6a82428502007140c41c81c510903e80c0d00c09184810b071054210480d180100b00e5104032510781e00d6070304c640c03000d011050f007809440c0d0307201c41503500462504086840f15100d14151280961006d034070345d0506600c0c4207040c402c02c0d00e12100303070080710004c1d43c40708015400b030007049007400001030103c80c40007081c0000064440495a05100c80756194886840c201d010b48045141f4003040c3c450916103c4241d02c0324840d0540c080645240000d04a0390054010820902e442202c42008040414071840b50340c04120b031980729896006c1e460f420518540d09400d54000742c05998400702e12180740d92465000f04c003040d00008021104078a89540714030800c400140140c411220f01d0209004035100c0d0305054801980110508040e541880c0c1500b001a01c1d00c0b09030780107800000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810273048 1250 810271798 810271823
    0x5180d020a051c0503060d1103010f060305011b0c2a0b120105040b0a05040e162c0103030e1002010912030204091112040305130306090c0e150303090f0319 68
    0x1c06002c0003002c100c4074220b0383e503444038242c0d00428900010703081c944071b40508000c80d801c228102c0174085400304050000c0c00100d410909000082c40c8074403041c2d40755401c1c01d9001c61030b18840610407200038070726280d0b1081c645042d19004624017161002c01504c0804001d04980440c403120040011f00c1c094511b07541c2d81d030030505018003004d010303032007140078900f071940c4070b00c4c2c3c2e80d1600021420340300c060714001000d5240700d0009207400c40e4102c10301e40440c0d00b1100480d1041101c0440000400300d04124218041c2901c540c01c22440300744000b40010b61502e14501e40d40ca89180001c8034000903200209140210380c8840307150310f5802252101113540050100b20101d1203005100402c41d0340d00300c0c42d0900350348d40a14600500000d10080400900264001c1c0707141c502000100607540242d03041012100c9450421480815802002c0c07210004900040806800460468480c90094081d504190444060000000b404a40c0981c107005d05805100301d4050182d615201c0c0c0c3c09500d0201c03d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810274298 1250 810273048 810273053
    0xa0b01090c02070b0f09130617070e06010c110d14060106030e01020c0703021c060903050706050f04031e09080102032e0e07080a0e1504140c0108040605180d020a 71
    0x101c81104952105541216000704800c1020342c0c140c50007101d40100e044e540f4401240007951200c015500d800500e0b1401001145d8084560f0069542010640c00c0381e03482c40e225089088001c1044034103500180344c5409150000358000c40031100d006000c2d041d0b080da80b03419a280305031030304402d402c00c2059201c00c00401540c0c1e403600840e074211140d200210b25140d046014180c44513820302000c1c0c066100a008444010001821050b4160b08190f00304510522840d00500c26400400e0a0b00c4035420040450403042081c02541c0c0070b5a896125104240984c401d0117211600b00c800e428244543c08400042c906400c0c0000c501c02c691000c020402034040304560380b038001c404101000220000b5a081c8101d008540c95107030405c2c9a414000301c2c1da83d40030054405445403002d03802d401e0041100c280300c25103d0b0020240260701c1a00c00c00254020401074a98a1001d801e45500048c051004140800d4250b4011b5402041254442c525002800c070309a16240040c4429001a403119684c42e05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810275548 1250 810274298 810274301
    0x50a0605060301060b1e030601020a0831081b120d08220b13050a020423010e090c060c1510030606060302042610050a0f0b0607080a0c11030a0b0109 65
    0x140202c0384641d801d0040a40040306d041400d022224101d103c000003080e500d0b03000700102405181d0001c50b90b0342d50302c0c0a0fa104140f42c450b04030a100c0482441e041460b16039050040c50003942d004038002c091030f40c020000303501a0740c0d1640070f10303420540410703410001c4d0000b0310003041d000960b0380740d104003810003000619004c1c045a00503080d89207940c400c100024040d400c0700790480c000351000044c4500341d081a0741403210090f07000b54030618280f080f9034002c3d441201006441807021404c1510303a030f10000c80c241184116584103c1740c1020101c3d4250346814805890011400c3c800c07a903c4c007032860900c4989607019070b011807007689400400c0003044514059140545000e04e07042d41080d00d4207035444940d45644050b00302c07540b014075000c0040b120030002031000000031081030085040800c2008014001c1e03081c4001c500d0305180c5041f206041c22001ca55080390f1107440030307107841e4280703404613000005600211643da4404145041e40c2e6400c20044d03558501030081441e055242a22240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810276798 1250 810275548 810275561
    0xd0906021602090f15120f0d080105040e12031b090a0b28140721030209040c020307020d11060c070b03150f131e02071109011a04090f09050a0605060301 67
    0x4c4040b0410400c210701c10070200b142c80340b21060b946d01180e403002c03002c440d06055400f1050425889400400c40415030700a690a04079001034404000500754801541d80b6000a0b03440f90307550302010800b14107426030b40300040c00c1519000c513010717090512900c0004c8000240e50f00c00c200ca840085001c14511004010300e910120702e910003071000720a2401f002c1d01c0c410000311030354241140800c006082c002c1c0030006100c282803502d4920141031161002800030740007a890341e4001c61500030030801740c6000004690401d500141060310f0b4004640c1c0b00340e00c06c4a52100380c1c0c0c1000c4240315903e80000f0400503403002d0841c03110155228a40400007020314044111040e126441010810060382c640c214034094411b0710301d202051102c5c0d91403442c0d08d00761408282c00c050130b1000500300c040c44080042c86507515000c482504050b680c806050704241c12841041d00b100303804000400142c25603500480702c104190102040c0840151141c1e41003c0d00c0c902c1c241c4123940c80c0c50400245190078443c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810278048 1250 810276798 810276811
    0x2040b0c070e0f04030c06110c0105010e060103060e150301110408010b1f0c06050c0405030a0f020310020f181f080a1409030f130b280918020d090602160209 69
    0x428483c6010144019001406040681032118441c190f400344040c607040344241414021906503161141d148960080609124547c140440100412000d603c6030250600303c2d00840c0c0300112980760141ca4007030748609025056890366035000168014525000984000c0203000b00001e20b04056400b804240c004801060000d1102041e5000c00709400103c42c8081c9600601e000030f5654a000d04081e4a12a43e0007269241c446d00300060200401e070f034443c00b013052080d402c1e100282e810049240c203900406001248440c000d000500424002070a4424100801000340d0104c01d008188072900c02da02145000005490108121b4140c41c3c50254008080315292204240c4c41e010380201c0d201e003d8503003c0511107400050240c6002e8103681004003508011001541d94840008a01105801c001c2c0752062401d0310324501e80c64501842000741120708803030b005d03e003051101900034000e510008501800c65070724044240418850310141004402d0040038415601441c010400128802000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810279298 1250 810278048 810278069
    0xf070e0a06031203051509090c040f0207022b060204060c120e01080606070206040806010902070c120507090c0513150e2e02030c0a050304090e0f0604110103060902040b0c07 76
    0x10030000c0c0b00400c0044080d040c44c0380014854880c1c010242c82002502c400d81d910580da002404100c21012400070b0208004032170401030301550082c200705a00400c83e0295100044200700b0074103003654808a10003240198481c0d1041ca15030703603190101d80044d0800070010320030800764801c20004c0318010140101a05000f100107004000080c80d4040c01010940110400303e010011502d42a080d10060000784080d9a01d40d82c6032000c0c58020340214a081d00d00e0300c04c040000070403250200940403e203812101a000860810004001800c40c1034030030810070208022a01c01d13042410340120251441c021480c3d4076540b009001025402c008030224440c030651411450f44000030480241d1489015001000b0075600200a0b07085001c1c005d448080c5001c1c80c1c0e804410444044010000e5800300748040041d1398040e4180c2c0d585194030100c80c450f950000001ca404111901042c200a220501d404a00644c48110410a0ba0400c0d80b086013a0680031171500e100c03a1040c00810054100c007440d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810280548 1250 810279298 810279311
    0xe031b06150111060114040f0f1a0a03030e010c2f030d0201020a2007080a060501091a09040201030f060f0603090b09030a050a0f03020d02030f040201080702010c02101503050f070e0a 80
    0x800e13900e400c8184260b5603036000c3d5070b50100c140d484641201003050925402001080051045034003e0514400c00f5003035a01c1d00000b150702854078101d5103054135010341d208140c1601100054843c1c41c1d0320300301625078011b0602600e5000f01c90001080c0302c04091209c0700c45e02c3e04690103262500d00c00d07400701000c0da40180002c0c1c18842e40006a840c0070320041403890069108000706500748120760f002811039004118001060100c19080581207a4906404001803140c503440d108040e41203103a0250720088072004100950b1094004a8400b56590000130b039660743d0b0062041310381d2203640002c010a843d0070131101402403c0c2400782c1d100a44001071441e080844000030b2841c0b05150f400005c0c85850030950240380e10075410360b01c5003081c07981c0441d507a04200e6441804050111012400146c40c03000140c584e80c8180100290825590001c0c181400c007410075601400034540299410520140008003007641084803460300d40c1501c0242119905010544040c050f0042520862604140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 810281798 1250 810280548 810280577
    0x16031b081810020d0c0602130e15030106141e0405070309030e030f12071a0414160f3b06030d141b190c0501030c1b0201030e031b061501 60
    0x80c50481c51303c051800c5d070344688151400c007000b801203c152185c01006a0340c0440c2403901045003a015412020810030451010810103007a40c4a90248182038001d01005c000d140c01c040030307080f403001e008001c510310780704048000c601140c0b8100e0300240026101c4c10300c4001e140d0805006101518151b006d040361022030441150385038400400d00c2803030b1200280c003005104200000002c1e2a9000c4610010b40c2043e05002c1005046414152090700406c9880c0700e15100c1410b45a0032284410255a1060301d0a226094102a0702043e480c141517442096139905420102e40c43e900b007007843c0c0643c12800c0510500d03103445803a01c54042071040c60f103c00c864080005d002e413240005804c03268148050f04092107801c00b410003900a03a40d070039007581e200070011040101e070203403242a6800c001c0014403c9084654040c1c0140407090080c0041c0000099403007500842c440c007403804200ca1070304a00d261480c242400000d2201a42c0e04000300b401402c030407010382d1031102c1500346094100b40c00d491 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 810283048 1250 810281798 810281803
    0x70908070b03061c17070c17120c071a12070203071e020f090a090b060406181113030c05010207050906130c09080706081008011116031b08181002 64
    0x10b00024440d49103a0340142d005a074280901c00245da200c031448004100200300f20030b40b90000c0f40100d41d541007050000c910320700c45201802c40809031000524400300000c02c640120340c02400c90342e070305000d51600814038a0054140d15078920f42450301076a2000e24180c4c3d81d0710880b0252100c82190010045280443c482454400d1080040f66550b02175003518070000c0c1480354480060754110301c0300d408025040c03003243d0000d2801ea000d420103810319610710040004607195070180002804010405620308250395004030702d0b5243c605041440c00302103602ca5054591980e004039502c00102e1801d0005580c144031034070060a0541d001c161508011000400035180f0700c161580190707449602294041c450b5080388020210742c815100304584a040040c400d04044a96040d24609450b002a940c1b00510800c4060031a02c0d800d24103007451851400c030f500c81e5810007601044107000703c07440c6103400707022036810741441850482d58588880c4824400803070345007030043c032a180b040f9141c1c5d20b10303401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 810284298 1250 810283048 810283051
    0x90717120306190608060306070f020a0807080903070b1308030405130903020c120109020909240723030109051803042d090509060108030a09050907050c0a0605070908070b03 76
    0x68414054490762000c0102d402c08984407051200d0906503540040c0131a00f094140b400741c00154107443c00d03903690000c10307146000300d813001c640140d0000340344101203200c007006800f03a01d00c14a403017031610b0f207210002460002c85411106545000003041016840010b400320000e011101c00345060500c0c0c1000110b48000e030150742d04489031181e0700c0d402018424080e40001000081401c41c4171030204141500078013000404078003416500300811140e00000800c142d0071010302c490b20182082080c1c21040e442d0000c1c1201d02030181d05c6460688580d29005403a09101c0b000a40e941c403076252891190076904040c00c7d8244410b140c1480e8103540d400441100e0946041408650248403180140c8140c803440729420303401c01426a00108400b41c0303980140340200d07591004c44841e0790f22003d28503180d216a000200124a504500700090b0034009925603200001d401c101d42486140180305080607801300003144c1141d980d504110905820a108101401c1c000000f07000f41401c1803504115840f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 810285548 1250 810284298 810284323
    0xc0201050d14101505040803030a0b030a0507120b34052107030b09090309190503010914060c1c1116031e050a0e0d03091d090717 57
    0x4002541c1440140c054201c0081d212549510030502e00d032901c07501c00ba1264a014a40d030b0001800400d0310014884c0c02607800b03484550010b0740c0346888503404c40700148240b000b07854040c0264208900415002c0c0310100061144d540404c99803081483c12400745c98004100c40d001c0c503201921035903500f0031000c85462815014101c0b100c3d9085d505401c0d5610b0184080c0c058042d4070a8484854000425003000d000b411691000c0c0484d545140c10440071020803155001198400c4c00a06058501001500441c00a140c8512403a50725500400e0035201c030400c090314500001c00031500d1400080007441d61103c001c005281c1005038400d07007110462004200c00c0900346d150401000002500012210a081040e003426030010451030302401034441e5516011002401c03014508103140220100c0b46075090fa613945801c0d401401040110740c0d000d284d0241d041000264000c6034411810030b01d09007541103158000154a042c0d000686004003507001401d0301c8280004224a2480015a0289005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 810286798 1250 810285548 810285557
    0x703020a12060b1209030d020c0a02090702150f04020f040e011b05030606120c0f042409031e1406090a1103150f04030315032405040309060c030513080601081506010c0201 75
    0x4417004012861070180c091001038507440040d412051050018070401030300d2094407024420f0740c826405a880700c41d02d92035001e020509100103203584640c04681c61740700d0301c0100305a10b040e20141c042000c5411950401c0c407e40e565503102c1d0103d460801a10b2407804452401915528019000c90560700503115600383c0c2c0c9026001064490000314143d400c0d010302c01c900546c40b541d0354020090b2240040313141d806210300d03000b2043c56075442a036a10007921b4012220031000c0100b40700c0c990011783c0f11182510110820440b00c6840001408017a0042641d0401000000040e09205116907040850240300b03611864500d009818205505070703109030140311600141d580c2e41803d4016103c0000316001c04104d5010110401c00c40a40e120040d85d03050480c0889038148a140744d0031140d0036a0302038003182c21070b40208020f41c41030382d44961b140d2103460880d007032070314a4a00022a0b42a50041001c503007280d0010700040380d0400030303509103c010103200c10f1542403070380020709065000f6a01a0411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 810288048 1250 810286798 810286801
    0xe06040305160c051306060810080a030e01031404080a0f050304050c0f01050d0e0d1e12050604020f0706050609090a0c140d2f04060b0913060e0703020a12060b12 71
    0x10038445440300007040098240554903811219170700080029000b04008100d90b500400c0850340c040c20600d0907039100304001c20155003a07031805d6600d104c100507800c1c101510760111441a211a04619004510550034151074440c82040030b409040c402c41c00c6810800240208400300b000069034441000d01038509551410150004031072034810003541c0b012540c00e014000001000001d041020700c0629a0b802e02c040c03540748002e555a0b004900c1480008600c21035040141c2c056522080c5c00410082c0014a0050180162a00d0360010181921556981c170204035142c00c2110b01158001443c502405920307000c4c1d42d49098032501401a440c108001c3c019200e43e0703442e05140441c8064000394880900740c000082e0074005451066640e28074a545040c109503400c1038020070003075a06038211b0320300b800414400d0007100b45110842044031626604005500501c1000ba5801904666009039071821103d401411203450171010149040c80d00c0420440d40c01404240d43d41048644d1890800d17 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 810289298 1250 810288048 810288053
    0x901050607060219050a0305011502030a030b041e09060605060301152327011404050f2107030c0b03130f020d1403041a04150f03180b0603010e0604030516 68
    0xa000b06444d004600d028141542011030f0007a015026801d003a5034103210a070b80b9260444011075040300f140c40076906c1400296241406a00301d04081000a44000f4030b0f06006071000c0d0303e05c007e200180041e141c0d5a04d410040c4000f6000d0400642002d580f903610355450440100c0d80207101d42542000c0002001039030f040d4800d410b2030440442640e220300c5850310400e0b99603400280f015090300384100a0255004d50b65402010202c0c10020516940c6003028988424402c4070300d0909289507000119103a01d041140700d20464500d44114000105800360451410100080302c0340c02c034003142002401000000e816001c100a10b1591142c000c14101c4000e102141074046551302c001c150101d2001c0403103404000001401c215080c3c0c1342080e40468500c0349020a80c4554000c00d540501407841d01c2811078013448944214100038500004e0325030071030354000b2800001541c12281e140c5480c0c14082d0710310b800d0140754030030b001c0700d00502041d081543c0e018005114900d10100710700540c441130010f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 810290548 1250 810289298 810289301
    0x11160215090402041d060d02060409180c030c0807080109050d03020706020d0e03030a0b120c0d03020304181508160618080601090b040501060906170c0408100c110a02090105060706 79
    0x2541c81c006041503442e2070f00d440141c0780d8812007a481e008000341c4030000a002e460301d031010307040040c3c028001d180340c103080c80010340150220702c3c2c450b0001c01600802d00e00141200c1080c1e4000d5000c0e25460b41254140f20041d41003845642c03001c03445a041c10b4a40700450740c04501c1e6641c0d2225400c0060341c1c1d05c10740c035210000c2e000f042907614000b403919075841140d21000c80294440c0001050030000300a034207007080301601707441c00c0c52145d50b800200c982d00141860052107807258002c4c011a03003069902c1d800d06030401104400c00c464251a4803081441c0441010514050818a0003030000d058164150600075010351141900b00501c4000c0140c01500302c5542101410381c640c16184139603100d43c55940a000c0300e5a145000314a41000056014850040c110a454640d0b642e22404106004980c83c42240a40803a810510070400001c80140030803022031700160290000c6a00d40300002c0203080e1508140c8000090740002580c803005a070740c1400141512011590b19860fa400e0b42000380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 810291798 1250 810290548 810290557
    0xb182d061030051c030e03030105090a021c1b030501080c0103110c1005010e0606090102102a0f02010614060403021903050304030b09070518130212120d11160215 71
    0x101424205802c042801004540c1d042041032103480c00c00300c003807a10011811121030710820300d803a80041c001403006141040402d90842e001a5015050000007407010306000107051031038604554900d01d101651010032440126054142800c020941c5041d40709512490140d103811b04044da254054040b15940e001034030042d03810134080320420f042144c03260006040078080d0310443d071804000030b00c4925080084540034941a40039020244c520022074000c3c0503607404507010405d400f10011401d030304413600c058410415941d45207001128080c06421a0071541000f40f400e040154021f10b40d49404040320200c07607040c1d403400102440c0450024409c3c226400003030082c00000340c00421300031104410350003072002c00b00703440c1405e5032071080028a075405000e424401d5400d10000f01d41b00d00082051a901c4c1c0003030700c540d142c12107980490b070500038014001c00e400c1c0404240828041c0c0d132442481c01e80d003c1c141c01980340144030024044118640580244591203000d503902e80a031000301920b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 810293048 1250 810291798 810291869
    0x1e03021c0501020a030b0123160314070f1b0311010509040609060f1505030108061506091809070e01050d140f0d090510080609040b182d0610 62
    0x21504c8072201c032801000740458106e0203001540191318244140000010410b2040e9540310107864100c590b40061500a40050140e050002e828040311070040d04c5001458141c1c400c81102514030854035000c01c501746403c4e17041c0a004243c401c00e000144480010488200c001d080164851907030100280291505030420001981080d030700182e11070384030040c441500c4400646100c070b040d04141c1111103000c00d1040c0c4600d07a00040105a213454210103110042d0300140900c0d291964003008a00c108441d02c0903102710b481f0420411219407820300c00c1001505a0a49424040d45460005900c0c0d4403028070103000c44002206201502780304002d04140e103146407084d1031030501c0244002e08240a18441c3ca80141200400608524461500780d44100002030801855850ba9220b81e01c0b030b0100181604040d41c4403142d1211f100804120700c00c1c642d42e8003c0000f00c0d561154a02030410030b84881e201e80c4070b42c806c506014640200c1070380c10f02a121104154a40402030310182524030802c410007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 810294298 1250 810293048 810293051
    0xc090b010f112d070e070e06031005010e040f02032e0305031b1507050c16060c0f050106091d011a030a110d02060403050d020d110309090907032405011e03021c0501 72
    0x81c04981000d4606d101e410355440d9940d01801d00c9091180e00c1c8000c440745040745070a00d40034040c960140b0545c0c10f0b1440c020f44005040c41d01d20043c1c50482e84241c44400c20f041c0b0001601303101c600f9a0260b0100301541104040303503a40345a44050762030042c0e820000502d12621041d600200b0104900c00d400040e58a420155040c0703070002520503404a102031260740075031444907400c100954002011202d03281e5900360390400b15124501c030000300390b000311102e540b20580002d49046900542002c01011100c201440240205031030031100b00d41c0b080320340441d003c5240740a5035000308210500c940c2000001200214910000f0782007081180025072142c0c010401105011000030b685000408079022074121850182064840348018000718400340d1080041440c917044c5240b446401005400803070300c030543c4940d01c400303000040d503d40f00642c0741c280f103c6800240d038501400e070042c00e0000c0221303606514038990138800c0c20b007808041d019030351401d0a580000c100448419005420400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 810295548 1250 810294298 810294313
    0x150301020f0d050a02030105090f040c2d05120325020d03030207120207050f04020c120f0909011d0109021b0d0203040611150103030e0d0c090b010f112d 67
    0x2a210541e8014280c030300c1d110b038a0600002e000c0f0360288200c0741a5600208000040e035070321326084421400003030045406074a0090001003034981d01a02d46944000c100741c01380900c1c03165112100b90700490340030310f111703520b4014503028603c1c0100071603108031001e0300194413030700d40030061160b64405004001d4103d40092020000c2c10707410750152000902ca45c42119040203c10401ca90f181384a0154a40c0500b59000c2154140b070198000d2130728110b5241552a40d00d070700000d0000d03580102102c0a0005c100080141c1d0034030f0700c2d852140c050580c26100055064046050100e0483c05004200d040c42d80041d4080481c1c00d15a40e21110701103800c200c89900d80c460f480207403079400501c19400440c45000500400c010003082c0d070300c03424000000c110126803850710300b10364501c401030040750040e04894100020614002c1300300082e081c541d070003081482100000400e0100301d01044130810088405e645107141c0701094408141c0c107101c0c9007445005410130f041079031544641d0102c03d90b100303040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 810296798 1250 810295548 810295567
    0x15090e0f040605060d020f281e0e0f0a020d2c0c120a02090604090231090203100e10061d010902030709061107090203180601061b0303020315030102 65
    0x100d4880c45030340300d00e01c28032090302d40b501800380a03509007000079408810401c44c0c40d654140320500743c0d03513800050301d0380c40740042d201481c042d900c1054020a00c401038501c000d0b4501d451081d0180700401c0d0f86004184c0910382801e419a403010040c1841c124540c00281603c58a89590030118205011300c442c09078500070240751041428000b01d00040c18018841c0d413039002d241c0780360207401040100018004d501000d03805c02c20290f5004040035441036aa0302c9a40241c1c039070600648000701903581508540042e42a8102d40144034219003401508103040307000181c03004941040310680203240461412210880c084c141030b00c003c40c0c00743c0c0500d4000d001696540b035070b140c081070110718000300c50281d80316a80d8400b6440b048405a021a010700c608209641c45004001d0081c080c0da41690913081c0c5400071842030707a10644185400503007110060409150500a06004010600b04000304c2955180610000d0714292000741c00c0c5075010001615002d04c40166149015008008560320500f42 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 810298048 1250 810296798 810296821
    0xb1615050702010b011e08100f06080f090a0809091509090106050f060a0903081b06100305160f090e160816060c020906040f1b0206060114120115090e 66
    0x440380d0750010340c20078250100c0da500583c0c3e98000366807840b540c80d01880c0c21020a03194050082c142244050241400190b03568a4903040006000580d48020040c10810381c074103510003000c1d100312030a0304440d07403c0001030350100c00c42d05840c00564210000341d07100e6580c40142d0014800749904032410204001c22184198014401e80e41d0448030603d03038030802414000b5901a4011a10104044d94000d05c04100e10b00098040301c6c542d102003072224114051850b042c2542903941e04004020741005204112090090060034036030300d445046242c1c070700910300003805250311600081302e6942c4d00406c3c51200030300451aa00001814241e41561f0350b0306940d03a11000084110040c504108011031031910030102031154076002000c0c0491600c0b03003006c11008101c1c00c504a01a40c0d552002d101c80003c002040c000c0140113600a84018038080d000074080144d81c980301c0180450400c501c40f80e000640400505481d050380341c500b4000c4080c0000d40b0341410795002a03e481701204100002c0510340c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 810299298 1250 810298048 810298051
    0x3020f010302070b091e01020f090409080403050111190224090114090607020c030d2c040f0c030507020d0507060e150c09150c0c040504030311040f05040509160b161505 74
    0x1041014141c40c1131b514a107401c0b4000c42d040d807820100c1c1000810340a1400b07400c00305d4100d006142d0300745865540c0d60382a0031a100030150043c000382c00f048464010f20640e051084166550014001d41c420401d40d150141c100b101035401841009404542506025030103102c0d070b6002000540e0300c5d0b082923101c1c995560402c58a90f00148152000681305007000300303a40400b8078098641d0b842c0030469200316686034800c1149030151031190b030301c0000c90b562140110f41a100c400a4005840080b169004081c0c90b4020081020340d4040c00d01c5080465010382111070300d58000360009030389502034101600b400c41030b005001510300342c5014420300200e113400820b0030000c11201c1d00482c0c00c411041011501626403005032603040b42e05603000c0340c00d0940109601502c240780c0040c00b8460800b0401d07154202d600a42c2018441c6102031046052501c02e00380c1260003413000300000c1401343d4039100880703000d00610741070360808111105981d1000710f070f07644000e502803154010440c1d07884c80c5000a020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 810300548 1250 810299298 810299323
    0x1031a0147091002070b070f03020c10030b0906011b06110d02030c0a031515081003050d0203040504050109180210020c0607110f040504030f0f050f0415110c01020703020f010302070b09 81
    0x858800f8201407500025000c02207420700034400e401c05665880320320740002c1074141038007540201c0f048103940e5a52840000c250070003a80b070020303107240782005000c802e00000300407505000a000c0c101d880904642401c1c014554000c001180b141c1e52a10b8440c5603002c0c0d00180040c241c00030080c0030981601201908c031580096a082220181008101c020351420b880740c65500c0964500003000144a081950351142050806040d4160f6980e0390038600301e8517000400058101040a016900d0b15000f983e004222001c1c0c180b042d0203542904180c0c00d291040028410b400000141c40598024811406038400050030607403900c00c1ca0034401e180c511341c0b4000a01c40c0158051001041c5800d2003020300868150ba5201045a50030405654014282d165407040c070a0038403242c520103032858000c2c0094400e200e00c02a110006c1e00001c3e1951010100c401c410f500300384c01e841803a990000d084800c0303940403103001041058040040e0300a1203010310182c00e0000c0541041019200015010039014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 810301798 1250 810300548 810300559
    0x71703010e13030503040f020f100908011518051009060801050402040c02031201060e0d0b01031505101a09150703090314072402070e0a0501031a014709 67
    0x90b41c010400b4141403180c0802000300380240040390100e252981b070703035500f541b0240402500a0182000911806208030b0703600010790341074000d1165000030f025003410054200c220001081c1051180c00718989000420440c0e02d64642c0050301c03464051a80f400200140001041029120040a400703024112130690040303052038207074205944004111071803c001004034401c16424440308440c40e050800d8034907848050b1821100102d503032012060300070351003000c92200746d440c2d040418058800003441e044606000c1f0b40c040103000044400d0441400c0c0700202540d40c1c03012034000483c1e03843e004030514410a0b004c51054101900140d40b201528060500d040c0610305c031f070300490303607440c0207000305d08020910b5020810300300041c60a004484040c0d0040d0382d03616031141d40940c98031008680307183d8a00d880321300400601c104000c01c03e6072440d241d0300c3c2124560500b601200346989860a010541003042c0c0c030202c501e02c1004280405030f040c1c55081e040151414100019604002d140c0b91046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 810303048 1250 810301798 810301801
    0x40f090207120806091803040515030618010b07062a030f1410090b0303090d03230a0e10020708190c050f0a17071e410105071703010e 59
    0x1103000da80c40f1440745000a00f000740680d10792040c0c3d060046040c0740112188400d1001060035a120714444501c1c50386800d501f81ca03890700c0000c003e459020b40700e100c01c0361034410005002030455082180c0c41c158001c8408581005a1140c012a41e6600d8066003c0400a0030399140ca032903260300882e10740f40360f100c0103209071000b9400510140c0c5050b68111818210043c08000c01c42c2540c0082c4500140101581d042c41a11400310319000100c2400310005014281040c44e10580d0440c07042002c180f20801c0b90a1821812014040c1400d413010a4402d038030300d1b0341d2406554820070500b4085c240600036121030010300d2480780c18010409508641c1e51800b0302c8041180e0800c10f407158020300005007048105441e10049005018070940048014003d20b4070202d032508084a00b01c468400ca5160220b4842c0707002460190b400c140d01c240081201004140e4110f11118124140341c04500c804015041e640900103a8852050500041820b1a80e60a580100c2c00342d90240d4100d4100340c170041291f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 810304298 1250 810303048 810303083
    0x1c0c1203082710090606050d0b0919030504120f20010e03010e061f080303040506010303110309090f2a07060c1112071103010e010506010906020a0b01120602040f090207 74
    0x14800c000b2245186502200f102000f05040380c10034041280203000c0016202c1e11080810002c810380c2000361244c1c0312540c14424440010000180400080d1200b1500102140e40041041c407880c07040421444580d100c260038007048800351810320754011f408800c801c6040d105911440d983d4000715000c960810182c00803418180101e455040c0200041c0005a45686c0040201c09490340107507000d074519103000c01e107034008000031402a0f018034020a02d541c55171030018440a0403140d00043d0350011300c013140d10354071800f803000e8024024009898030399441004a5489507006002e10400e07501c001d010380701440e00000100302250040006104065004d40c2c05d4420074000e0403585155400000080c0414507141c01070300280f442400c03201c51511440c400682514401402da402d1655200309101072582c0100e4820300420460026203010503a9803a8480031601c14401e041c0d03104616040b13101080019412600605078a194490041d900c07520300800a400194080f036074030581040d003290 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 810305548 1250 810304298 810304351
    0x90106020708070e0702011d06010504320a0f14010e0105060c03030a050c0d05010801051807050a09021305280609121e0503041e141c0c120308 63
    0xe440d2048014101d03113141401000c4058030003007110046550fa284145a82c038030039080940d8020380b0400908081d410316081208641440d081071031100146500b5415012140840d01e4144008101e040c00e9070380c404410740013030400c1c0d640744c0d04407920f011b416810b4110200c103224143d968082106281d680c0361401e1043e00c0c8508003241090b5841440059210710b29074000a5101400b0480603051580c0542404141c030400e07040341546035140c0041040b000c00201c0c00440395540000106415840c040200341805400d000d21503105800050a5100e070030308200000040c070303010b0080042072040003c6002d00311070401800100034049030340002ca042c403c41c0782e08161801402001012800e507551113411040ca43e02c181c16481840c01402c001c2170050018000030301d40030700f9010503d81c10350603010b00c0c40c209800692485522840c168450380f80c201916048010085031900300a1503400c11118a4956074810101040c1e0002042c0805500403001d5010b0010881e86482c1903c02c40d40545 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 810306798 1250 810305548 810305563
    0x110604030207051e03011112130308070c03050910080f07080417031e07030c0306080102030c07030809031c0c0306081903140d050a0204030c050a120803220f0209010602 74
    0x500691001c403050180e494244c00c08a03e400200504d12015500e41d40032a081d11040c04402005000c08200c107911552007035002c83d4400700368444002c13109038960700584001d03000341942007000704402029040500442c00c6a200040041c0320000b4140c6124004020100894214840c6490340c1d000c2a4081c1c02458020300403944031034005010003044802408030b400c001c1210000da80d503d0300c900c1001034050360850080a0a94020540c5c142180024059400d168000034031a0b20400c100524170321854142d50070250f00d4071b4407000703036203408030303400d180d800380105915481c294030101240e000b00c1c69001d01d003484002e89007842840c0d5111159521150f0181451030840c0007074010a0010780b2030503c0300400c03420107241c142001075142554044900480d0810300380c84d400241401030180841c800001000b003103811500550422139003d000001621004018000100101c0c8070403000030701000c0442c81d04403680c0c101301d500c0d007803000d10031070304020584c040c481c0c000003c02e60610210720380307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 810308048 1250 810306798 810306803
    0x50d0c0f060504081b01050105090115021b010212040b0a1b0b040f0201032003040515060102120a09030204020f0316050a05090d0c080d050c010501090204140402030702120415110604 80
    0x10400c0009034580340e0250100910403a80c6640030400031400302101c210100c00b10041000015041d0b041c402800507602041e00100e54034103015050030111540020b541741001002405040c06402c0240107074546640c8103500d41003188080740208907952504c0140c03000000a41d40c2d080d0300030402084004010407800c010300b4418110001402180b1000a034064940c07042c580002c00c0e500c2d4a546030382403500c07154403881010001040c4024014200480680701160300e4404000e400c021002075130341c4c2c030b55840005821030301080c442c14041c01112070100440c0c000d001550f4400b2101504840c1c0e0340225005003841d51f062a41d082007510400a40b641601c4a0703c0d200d1500d80e10104010303d00500000c100d803280404400422a46014042d82d81c0c6610300742ca4141d25110541d1803542501d0050700b01ea045288184020040526a8001c15400c00000d440060ba00e07160750380c0c12803c01c500b448403484005000980002c15009500c0ba0802c00a410f542d0908000002140c56031942c4095401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 810309298 1250 810308048 810308063
    0x2102070b24010c021e03060709331101020f0a0c031806080105041505060d14130503030109231918170c0a061a0405011410030b01091d04050d0c 63
    0x103d00060418640c000b400144500000c0200040100041c1c80c01008407440030018032140300410680481d5450800020340003d01c240d188503a00002e030703460910401070346003000781140c0201c060110a50440310400070102200b642d500e084403014081518a8404034000360f59019920401e20456201005403100d40e6201800c0da4a44810440030340412072008400961000c0005007994818004107905110004c021230720038030158048640b89401060114013070071407070082c000118040116410368031070717445c0040d484420140030f003075500003a880c807007005140e8418001582c2410103440b000350300c40c82c000d10140c00c1c220040041003046410040030031108440e80020103891101600078486500c049900303803503064903003009032914400401840e4800c45000c1900e82072902616000d0070320805100322030080380011a0404442a111004040e59031016038111382c8078003840d03001408041000c1c0803141442f003610300b0111041c0c0d0110342e103200c5c0b18442e604a9000d241146c0946400c0000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 810310548 1250 810309298 810309317
    0x180b070f080601020619050c0c100f0b0907050901030f020702101125050411091804020a061d09070201110d060905091c050d0b0604030506040b0f06060a2102070b2401 73
    0x80c04c000c7c00c40940002103a02c801d00810340d450f10100000720050b055074001203600465607010400b2140810344581c046d43d5260200302c20103801c4800c950140a01380b80c0050450606842d86d0700a000d040402507014140186202e101c56000e10158000314805050740c0004003c0d407480e0210100d400804ea40c85051b05604010354645507010202e05001c4110709840c0480c1c00c000540d80320350480401702c0704038400043c0402e41c248081d00740c000c2c0030035040c2040036020680700009e0700c4500c024154400d91003800090780440c400e400011003001030920300ca4440007000b89070406030031903004807640149403500040000b035000a0008603121260580c18407950600b204a4243d0b2061a111442d00d13280c140d0011282c6411004000650054024100d07505152518804240c0041c2824a141d1284010f0106981d680c00c122001c0e10414141902c401c014070a44c03903402c14522201900c06813002c202c8000780024a0400c92240222002825414207008285050704620300219800241d42c41c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 810311798 1250 810310548 810310591
    0x30a0e0705031f020c190c0608070c021309060e0f010f05010b0f070602040b0304061b0f21140702060603070f06050d0203190603051c0503090c04180b070f0806010206 73
    0x915810036110f0b0000251401d8282c0e4103ca250140b00c0944050348004403007a0b00034404a4803148020344020700d843c0c20141080704000b40700700c0e20004041d100f82200110710461410560120145070740c030081c14454a016409002c1d210580e41c2050304a075401c1c00700080b00080e0710f01c14141643c09aa08080c109003400301e0a80540c0c00c07441007190b116608110104101c417804010b503100b41e00c140c0e404110f480320781004940308c0c2c00e1141742605100300c25144074045a089180810102032660749800d90110500442000c1c1c10150450020740c6c0108043c004059400325000788544016011115016500c50010413204542d220700320000c0d005204050040301181c005540000a0a80b8400980c403e0300d107207800c80d03200c1d03030007251180d0010480d0001c0072010240583c2580840c1846411850980315064480c800384440302d101c0ea54031107600000610700e2010010340d0b41c010b41d540d8030a1400c0070b0b0180c0404503c0e0038410100c1c80800004042d0741c4001141480303440348050a92801c000390 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 810313048 1250 810311798 810311833
    0xb0a1107171303331506030e011103100305070524091219050c100504030210180311090c210606040923060f10080c040e0c030a0e070503 60
    0x4091101d00c020340380001c04105800120701d80728044600c249031a90100340380402d131041500301015218202010b03500c04450071942d14040703590b94200480c4c507030002c950306401484070031054420140088148190f800c0841d0030f04066920a504451046480d08100700081080c0d02c60801900c8401050b064120b52090140c9103584018050741d0000503032500a0342850302d40f40402081c0111480f04c682804410403c1c0380b10a41c0560300322030241e51040d00184036200d130b808007070301a900b9100c3c2208900c3c0b04d61030804904040541d002544c40c0c480c600349962245445030103102da100e0700007262204000704205e1f2018111000400c0107204e80c2c04200100507802802107600103020302c00002c41c46c4842c019180307010b906440b0849003028140d51000e00da03070060111402945000b00b100c815440311080800c2c80b0000d81021003842d925024220590301c01d039004034002002b25001d20000c0d80f02c07000998040d2003414014400c841c111410301d80c0d100710902c20503606a100034441c60340100107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 810314298 1250 810313048 810313057
    0xb040e0303090730030809150c07081c0213030311010c050910230a0801080f031e0c010f2309100e0c040905070302010f0906051b01090f0b0a110717 65
    0x3ca48880e45011115103604c20010781c0c0c829008140e0040030004501c40c01d1000d4802c240a103040d007411410240ca290390507005a5030008c041c00710000301000c1d02c2d211150340c1e4000300c00203030080d55110306a00c0f050444602901c812004a61104800c8901d100c06000e10041a070242e43e0b8541405088400c0040c00d100c03100301c070400e01c00f030416042040e58001a055100500510380315588225504000b005444140d02c1080a5040a448040303d413a01104030340d04840c1c2d105454001c942125122061489507015400e0356618001c0b56900700b40090300412200c0d4111702e07020850300382d225886102c2840444000003d80c202c140040000c880f150f00c051008a14001104e141c2c00300200414200c0720702c49001e80d05603110990800071582d11070360901d030396041072502c0000d081c5070440103019809518140825030410618420224400358840022181c0002040500c1c401509010900480c103580070307009141000d0b0340c2030b40756082104452525611000210404071750a440c00b072190031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 810315548 1250 810314298 810314339
    0x50703231b1f18060203091f020f160e070f09090c031d03070209060d0b0103031b0203150f09010c0518041404031d0405010302012313090b040e03030907 67
    0x4104a08904001c9422409022454546a40700303c0c4044407040640301080764041021544100300418158607081207c84400289540030407012590000c16402e00700803880e0442948203c0c1402c0c8407203840c14034148115900f09101100d907440e20001140d07900101018100800c034000c808125206990b4440e4038000020315001580c101010301842d0800c14440c0a16203070f80c03010480030190724060701d1498100d08212084c02110440c1e940300c1c500c2840500c405401d210348014418416804802c0300b068069004050700c0150300e0071071400c0e0882034251010200000c02c82c00040031808144511440303210940c48003400c04600c01c00c1d444407501c480c2c0045030003940320714408400c0d214552030140920312a0710380343c2d0084a81d000210101002c1c1c0c030720f984624140703001080542d801a00d0102042c0030700b110107521a04807003004945108515030b2400a16005000041980300c0f50701c46022980e048406102703420030b100b66142da0340815120401742e40c0001100700a01d040f1420250143c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 810316798 1250 810315548 810315559
    0x40b07020c032b030b150a03021e0c011a030a060506030708010c1e0e0f040f0e0304120c0911040e090703050d05040e100b0307030e0f0604050703231b 66
    0x104441e001c24108411801924280740c2d410b81620025091202c2d030020701501d07880e040003072422400001e034030552680c00b1403040c01400508160401d03c40e8044a0b0500d0f00380c51121641840c00c03201082e01e41c4401900100381d441d0010f140001014000c04840e1803400400402d104038458640100400c0b000d040350740c1c903204030390300003030080000e0040c80482916038491160300002c1d103007269412501010311404004221100700703415075a2190f940b01425042d1030010310302c440600309100901518640c0802480003090004490071600c1110034414481d1910f20700f91a51039083c002550014009050400001e01c0144130002c01e03001101d910466007422030709001c1d6251900c41c10941c0c0216604000780d4000350034480002c0b920031198100405805406666151a10b074410034040035003c1000c0640321201c1e5021008200400a001c000e140b00303480640c20186482d681da01d080c0d100460b14400500c1481c8e981c002d00e4003030384401903150000b5050061002411400c1d441014071040d5202 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 810318048 1250 810316798 810316813
    0x51f090513050415061a0a120504050c01030b0105121609180f0501060c050a060f0b040e0706080618041e05011b09050d0f35070606140603040b0702 65
    0x6550300c503000c25003070104250006140c101400d00f021074920360f041131a401400c00e40c0400045100b03c0c1024050322802000071307160a030340700b0100c079900080340f440c3c0b14a03410081440140000840c50034100174007601c0c2002000540710042d80c00380900800401c1d00000c0f1800100b001649510844050b0309078a0013040194407220f4048405400a5403050401e6444090255403d03180c1304450240040f4117000400d590b0503540c40d5a0350140c40b00c001e0803c0e456036001002503903542c01120045a0042052000c040c880400301d5854009100b03650014405002196990602ca010031107880b0b04070010b242940e40c0c81e110341d2400c40072811144001c400301541a0f01007002071003440401110b0043e209103107006004010408880c0790000d511038040001e408000425500c002c01c00651303c8504001a45400e50309100d0358444181b481441025804032200301210840c002c0910911603d8100210f584440881007486c01c40c0c1c004942080040000c02c000c6002019495800945441151600c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 810319298 1250 810318048 810318059
    0x23060607050a17041a07260409060e090607090302100f0c08030a0b031507020c1c0618200a21060e0c04050a0c02031b0a0c031103010f06051f09 63
    0x80912481083c08640080fa050240a865801241c0c00304003d00b40741381804c0303054491241440d01c80c6101d65600d4101e0341401140140344003503400405c0040d070200849960390f000c040c0c500000b00e40003c2c160060328002032880b4012141801903d4003c1c121000c003034641034059a001c0300203080101880911002580083d890700002c41c85420451800715542e001c900c07d0520301019224190b600340c0d4407000304134080c1e9000540344100401261800b80c620b03003401c0c0445071800107600c09460341e804e0210001c024084c1d4004007003206d21446038030103004608d070680c446250540714681d501500c941f008009000e0140082042c10344118105ca07000003a607691007040351580454154981c0002c2052541c92401d841043c2c0d01c0350004000303005050034032400035160311a402c6a251039110700115515002c104202c0c205000f03a00508007208940c490426010840507014003a109600349003003800301706558017405045031005407002900c0c540d44180a060490031160041c108001c84000050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 810320548 1250 810319298 810319313
    0x4050a0f05031e04080d02010b091f03020d0302280f2904060c1407350f071e0b0402131e02070b0618040b040c080a030207050423060607050a 62
    0x46104455201039611464255411b04280d1180000001c1da450055001c40d0703070b00c2c3c09000740e034011040c034100ca001c561400540d003400c24044d00043d40017041e40c3c100e002095000114a41c00c0d444030440d010382807000780a044901c0c00d09000080900070044800380010324002c42c0b800d400c840800c003680c0181d02e150011184440204d8081c0c0d000785d1128546010070b03030040030b10302214007070940362440d140c01d9480722020154401107074000f030801c0e4001107103000400f13031100d070341c4c091509641562a0007080d8020055041043d0079601d2002810252100c0c01a5025800b6401d40c0071080c1a0690340302d400300000d81d500010081c2c0801c0d11071000e0318201403602c1d010b000c03000f44160010b0b150704d02d506100d041700100404c1c00b401a0b643d010789184030503050003090f501652140c0340418030b035501e1070b0402c805d00c50b952060005209410410b070401d03401144180c1511010b550801c40407840b69150200100d0303041009081d400716602007821802c5c024010640315008004031207010f41513036208003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 810321798 1250 810320548 810320587
    0x30c0c1c031d0a090c0c060b060f0313020402090909070f061d15040801020c060f0a0501180207030207030b16032a0302070c080717010b032e1e0c090e04050a0f0503 72
    0x442ca034040d0400c007d858420782c84803803000d443c0e880c1018106903080c50203210117061001c240a40102003011540d41d90121010f143d00a03295107124202064480c0d42c4104900a00270b0710784084030081003c9100c2d40514a0110354800301401146603107082c40440c0c0417051f07040d00700b01020440841e41410034002017620100b024000c041c90b1a0a43c01e0500f4110050484000241824010007012040c04d032559202a000c031801a60b40b04a450182d240080c503610052202c031200c4200040885c80c0b0b103104102954646041c050180c108180940102d1300000c0420640c0b802128103180d13074400e50282010500c1040c078242080d132180e46031854581c2e140d100c3da10b5060040049030105401b2b002e080c0b00c460f0158024a64445141c04243ca80c000180b000c0c1080341d0200a9040c001c400c0f0340008180d800c00b195181660148072541801810a0146100200c0c20415001611a0960282d2441203400c0780240c1503270000e6549112100da01e105043c1c0d403601c010b100903c086490083c440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 810323048 1250 810321798 810321821
    0x702100f11071401020f0d080403080705040f031103061609140a1809051605060403031b0f03050a11070b0904020325020307121d13060305030c0c1c031d0a09 69
    0x252440f00416000910b80040d560000c50f00b0b07000040c4200496400c10341c001d070041e07450b041a0342161b0b00d0b000c0850b614013859003d030800c030744101800010300070300e404205d03021082602643c0140c1d83da220f65100c001c01000e101400a607486800b004181c03880564152102001070004041c41d0f40c9102c25043c0e1441860810545541e80201e903003041010800728680003103440000546910340740009016015501c80a0144010103940c00e0070840308030025a0000d91020704c88260107102c0c02d0040c40b80e000003003080c000c00c0302e004e0401c1c2146000a1020203e0302400ca40303900d01029942440080e41019107006208600c00a113255225080c10000a000d00b165000b191100b1039400c000d9010081c004401080c0000c81e48020412542e503200154461815502001c00c210010703070501c014203880d40040e00c82e00000c1600e0070100004607059122b50f400302c03407206011141c030800c000403458440740140400d00c1801002c15070749442d484400320f0301c1c0003030408410755521007042e4152003205400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 810324298 1250 810323048 810323069
    0xc05030d05060f0a0f090207030c021003090311030f0d020a1b12030f0b0d11010e13020405030f01050903161e06150b03010f0302090c1312060605060702100f1107 71
    0x10068035043c00640b464561104994502031039140210506402102d070050389000c0307800040110503d409101d0f4400c2e21540600000900c1e0a0400001c0040080c0c4508600150781a40e0110301c48800000307494024082c0380d5401d1074980a111004003e40c001820901441118803030403500c1c1481c800306100c900d002c3c2e101c5502c07802e40510002c080300c00e019108a40a8035260444005403600d40f80744065550000b0840d104110b154016991000c116201603802501d01e43c8042c505030040d000790044030010790848003a0300b03400c2c51841c26980107d07840c41da80d520520454007419050404007018600514864448628401044a02d220071443c1905c1d07494480500e076200d100c0d403544850007441103004150441d4100301b1069101b856610000e4801c951803000700742035104410469030220900484030705510785c0c2d1074001541c00045c030070540d4401d151070030014540c1014411903000d5540200303400140c940003001aa00c07625002800c40806c01913030842d140c2840c04019004c00b41c10030b02031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 810325548 1250 810324298 810324301
    0xc080d02060109111603050d060906140316032402070501050112030f0206090613031403180d030501050d0b1305060406020301090c0507020a1a1312032a120c05030d05 73
    0x10154192135035103410180c0c100c001c001e002040d4500ba481024015890320b042550350501c0c00c5500c018002641041128914043c00010346414100d43d0301d14246050b01903502180082006075207402076403001500c80302d82c4628410b004016040340d1840340500d03040c01070030090641c0b505421154260044d503900b0103030185090615801081000c1c4a8007103200900780c0b0f00c0d00101c002e40b200c038007030043da9084800d24005801c142c001c1001d205403a48402200341c481c54410443d070007841040e801c41019010b60b5180d048410310174090b9a0580f40045d0200e1704024259580b000c1602c4024000e42e84060150020fa00284081c403016001d05e00813100944c032941482d81c80030480386070504590a1090400c03400c001616842c5a075000c541042e64084425038060300610051300ca40090640c80b0082548081400000000a40b6032980217681e528005404200603280c10700801c200c0409141034401e00c040081c8070701b2f54110002c0f22038030f0103001c50031059035000e295400c808682002962100e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 810326798 1250 810325548 810325559
    0x1030f020a0e060f0418050a08120702030a05031b090d06050f060a06080c16080f0307031121070909020c010b130b010516030912080c101b05070c080d020601 69
    0x1642034002c0c2c0190b50361125a03003401c0700012400d00d558141c8a006581701e160000070121080c04101d01c142c0c204040d500560001d2502c52000c2e408001100029020b9902050110348000140c1e808020751740ca889140d52100101540d0760f5407000c42c1c0344a1920101305030341d101e450340301c58014090712a82e0046071900b003996030b0449410000b447da9000d040f1418040011a42c024152070700302c01088070159440205012031807200380000740c041c00c8100f0004000141e82680b40c0294801c04283d40c2c10030216840c0602d0701c000740b0407521050041a07070151991580c001104a06402c264241411013905a0740e150240590b0010300019106942d1801400441c0c00d00c40601d100b9640b101e01d04000c800000000a0118081c0320100a1303203000c40c1240c902014003a21200014103400303600040c0031821852b210030341d81d000c0518039446015038101070100034481c0c00383c800d200302c4e40c0d5040760282001b5501254240c022003025a0000c0402200145005c0d0502410245641c29070140803a0760400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 810328048 1250 810326798 810326809
    0x804120c0b0f1e07020306070503040309120b010915170f0106050303030c070f0c08031b011d070603020a020307061d070b0702030705010e010201020d0e011b081603020a120501030f02 80
    0x20381c000034a400040104014100080088901159203403a03060f0328400035000c458150b010b40a002900740c45040d091224590f042406544214402c1d90f8480701d00b034940011250003043d40f000205014004070040c8400040c58028103003c9841d0043d2000c1956104415110454158464011030700070202c0c4205010083c0603034405400143c7c010352541c1082141403030103102d8120094140d1011350700d52410460541520b0000b06400e1040300c3e15200811a1440c1c80f56110500c54402c0d0b02e8540c030580c01e01000c03030400c40e01c40340c4080544200e5103031100950103540603600d940118002088281e00207401489041303400c820942202404507644440c4034603003801ca422080e601203062007040016900011140300b0380e0820300c3d000490444403001071340640070341c4806810060038050201e880c04030560100803d00801384841002201804043c2c0e404401520258a0701c0c0c0300081d085035060007a0000c2800b0f0115107080041030381014403860442d00e007a0021600800180607510561905 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 810329298 1250 810328048 810328073
    0xb100e0310020414040207080f0406180608090a020603090f030d050709080f030f0702011b05011b05090916021515040506060a0203121b04090203240d030e0d080412 72
    0x78140708524003420548640c010180c07114105200d070740c000502e039041282c81c2041c0c89040281030310b400c2d00c5a40ba40006090444502c44848020301100000180c1d18805d0040c6d0b030040d1003040150131251240c0c0c0901c481d6920081c081492441110380c0700d07000703c5003003005002c1c074000c1080c00106c0c2d0910150003081e000030350740a60100d0303100001190078100e022040f90340c0b0301d401d014116076036282c600c016140f8101c8900e105147c1e44c072a0760140107008041d0883d00f400702e4403024042110801d2907043c2c8090040010103074000c916440003910300b20614651800f09011070046500c60180c161990b0507900313044803006001c42c007200d40a0800d0074240a07a0746c0040c400c0b2059400d141c101c68000750f0ba805040c0008414441450100b1300301e0300e08560007800603100494803035032035031501c0f00040039500c10b071401c01c8100620100300403601410841203004150040190784142100c0e01d003121112442c24000d40e0111268000c00005000c000c0100300030f20401d9580e0305c542c842c40c242141801c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 810330548 1250 810329298 810329323
    0xb030705030a02031507021c02030d0e010501140607050a140d17040f03050a180927021c060213030606050306070c0b1603060b13030b011e0b030a0b100e03 68
    0x4011280401698003044155100303203150000c08586d668003200700c1c0341114070700c003161003110300d01c000c180350981c00710050140740d000300d07003c0c421060401040342c200c032024410b90a0345580013058501e40d2800000802c0c049003d44116a403800194444034507504d000101e81d03e490384100511120701c4c4c0c00c09640c4490310b902c0240805270340b80584461010300344545005007000000200c0c68400b81c000c0e500320700441c81480081e01483e4558030f940303000b403001c0401c40e100b101e44640c01241011404554180c2c0b203502802d4004513242c0070164080101d030400c2c007103d0050b0244510941d80043d814540c0c0294000c0b00c010031a203141405040c2441d00150030310b010080704003003504c0424401a84180c200307a03c08031501b180400004100d00901c0300703070401c490b0380c080040c84030003012203156004203681c003854520314140d0b41d03001c284403051840d0100b02c0c1010303103495007089000340200155a0007140c0a1000c513040c1140c4c00000d8607800c40c0740c0d880c401b1440264000c0c680f42010041d41501c0d48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 810331798 1250 810330548 810330553
    0x16032d09140102090f10180b040801320408041706010f0b070f14030702060c0d020c120d0f1106070c051902011d03032203171903051b0703030b03070503 67
    0x200e1050108103074911751004c09004140840100340583d2082d0364a001c98080a0000c94006403980402e030311782e510a00c2400410b40c01d10040030340c42d00d2000c511011810b030352004d4141403880c0008003100000000e1056034459070a0000151042c522002c00f0b0618804001900140d0f040086030080c0c0001760300700341d004403418800000040c68a2860001c81d42c0c022001026800a0010041c91031156980003504043c0105100b0300c81d201c0024211036080443e000d0750381600a10080c400c00316200f8002d43c015502c10080f032201107005480c1c84018040d10300d01507140d500c0740b5a803980341040c155051000141c19010060521409218000da14a00e640030080a540240c0008204400810012101c2c000c100d0a9160b26941003085414a41c481040c2d080852000c41417401720034000d20080d80d80d40d0b482031b203104990800703030200c615800c1405402039000c0d4045000700c1c02004010a020403102e10300403051555500000641100d500c690b802164902c000d00034581024a694006400303603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 810333048 1250 810331798 810331807
    0x1b02030a0f1d0f030c10121d1b210309031e0a02120a061d0607050a08010909060f150f12120f0315120308070816032d09140102 56
    0x16480c0c4011420390012a9400e521030003443c0042c0c1000650011607600030704503021005150b411000841e45110030300310410081c0020146072070b43c0200b0107041c0744650003000c528440c070380c40a80b011290010180508902c000a01c0344001250100c0002852550000c40c3c0ea440c1031070108000c164586501603000307503501149040c2c42d95103000700030003407007444040103100c000d007810440c0141858100b0814003c46240080360b0041610b10f9200c0810390064000103080c190049044800d010140e030344544640e840d00c80010001c000d404c13030489025881c0c082030440448035000c0c0100038621004900c0b1441d107089240b040c5001030751300c00b09681c182c00d0282c0012441200c01c40d08028200d0500c000640700c0184210f00a20151a4001c8441040c070390108030440f00d8083da104180c825211884551200b42081c0d88000084890300500754074000294125880f03500407441260020750340c50520380300403138922401d1106c0b1000c61162542c400c01c100502c00840d062001c0841580001c5290 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 810334298 1250 810333048 810333077
    0x8090f030d021b07060e131103010b0702120609060403030e03190306140301060e060603040305160804032a17160b031b030108070e13080c060901050a0e0606040c02011b02030a0f 78
    0x300c1184440c841c7c070901104400c0c0400f55080d400c50402c003580c40301e13110754941e11031041100e6038000000c16805104541c00390340c440d800005201d8000d41d40d8a008102c00c2c3d849030b8080340039000000514210340001d001585804e441c04031001405910350320041543ca040040c01213034041510940c0c0e210382c0c102030b0f040055a502c1c40b21541c00901c1500c406540b80c1d281d003400d48440c801d800c0780c40b2601408a8160080c0300300c0e42c001d0415a8801d071b103d03480c1150030810b04070700c3d40b4440100d01040610300e203041201e9030407071a1541101420500740c550f40c045034030359030780c0210556124014030100042002800700b8544480ca0006e028204458119414400e107156545024065081038542c220045104e0014180c41c01c0140741d4042503a6903200c0c6071640b81a00c0d03510584d540780c0150b084c08003141445006014140c100c0c410500100866601c4100b00030141030444000415556140f00c2a52902001203c05810030314540007140e80341004800100404180c0110340100903520551b801c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 810335548 1250 810334298 810334307
    0x1080d020a15020d060b040b0901091a032e0801090b0109020c280f03030906050a050105060706020912010509150108060c04030f1403131805040f020108090f030d021b0706 75
    0x104040b60020058440844400b000c0003094a504500417941c4003060020782e100c205001000c202d442079071904030160355074000100040c1401040361000740c0503c0040c0707400400c44407203214410360f1488039408000c114001b2a200c0d220b5000040c00780d440c1c05034101400b00b2807119500403e8449004c62805170100042c94684984044251898903144000e0b869490326a4103010100c2e00030000710851102854050f005107040c0342c0460b449410b00001411548240c86268101d400c0903168910b00b50095850304000e611288003203900410f0211481200d000c01d2040078070a12042008005600070615002d0034070005a01001176540032504010900d0b040105490440340d0010a00d1641c41c110310700000c03802451122080d1030300c008100030700b07113004082c1c0700800c46010000c117a2040c00860301c001c082c3c5008540107441c84403800000c10055104506955014003020165a852840b03c8542421607002c0e28011207015000b09039074003092669030b0391482030000340e402001e01c00e1401d84081c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 810336798 1250 810335548 810335573
    0x3071119030201081317091f02060c0f07050708071d04111203071209090c050304020a030b04140303040b0a1b02060f100504021c0b22021305040c0801080d020a 70
    0x2410081c2c0c2c0001720740c400e170903200e24103c42580b10007601030320f40c0c51141c1d01c281504504040d900c1740d10044825208403001d50b410307499100050780504519a110907021203140e01c5a0403028460700200505004200184420800780c50041c0161a0080c030b0300d020030003004036100e42e0300c80c1680c0f0b241c24800010703002254003540003010303a00c141d0b6051031104a070b170443c09640b03000b9003003001d44103002c408903038407044100c25a0361400c0c080004500000381200c0034001201e000f90000d40c0f1140c00d1003c41c581510701c40d84684034003501201003a010f0002411500b0030344045880304000410b00510244500071401101010700480c481704e10381c0b80009545450140c90751114046032008524002d204054601c00351102400965031000140418002e41d2034a00016089520381016600c081c580324400406442451030706214907107034204514029400801040d4000c1c196003400603c40e180e9016a603050556034680c0081e0358500407102c0e051503403001080046422800b50000050071500d000d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 810338048 1250 810336798 810336803
    0x5010815010318080d060e10060203090d060b120a02041d0c0108061f08011d0112061e0606030f1127030a0f39050108040c170307111903 60
    0x100300042c0f141c0c0e442140074464500a05510000134614500d0341e00390b0807001c04c4440e1038100202d142c4c0c1706024071000c10428094040182c00401a892a80c58000f100702c1c90b85003d04000915204c041d000a180c038004002a802d20307402c003107085000d41c90b1038030840f041c0d07010b42803648100b90003003c603843d1500095860343d03040c0003800b03000c41e03520b0300e850500c00f07419545459003241c29600c0620140008409210b591209150306440841c07607642c03c1c40140c102c4404d000d90b840c3c40c0d4100c2c0e41c0c2602420088801e40c80021001004040041c1c8074081e800c01445252000180841c1d10280741307081e02c503482c810110b56442003020000d040307805000d1100b0f0401c01451142e003649003600003810400d551402401280e011001c0c181800b200d0b045503040700400c0c06940d4115040401c2400304582440c202c20000c05000c01b0030480e55000c2c06449034428850059010701680310202504d240000c030a0109285d4004034860741008459150f11100791007c0354400540701000c0c0c24a602c1c01d2090000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 810339298 1250 810338048 810338051
    0x504240221100806091506040209011709160e061206060609010e040b102d0f0804051c020d0e04110306210a05031201140108010b0a0e060c06040507050108150103 71
    0x101c841d0340c803440480140a0000c2507030664100050040d41d562511350341601c4a070306c0c50780410b04d0f502d043e20803151a4881a12842420355001490709054140246200028011004850508800340d000c0d0b802620000404042c2c605210081c400e1401c40c03040f00303110700e61028050190f1a030360306060b60701d0000309181010303414142001050241c411030710708c40e820021000c20241d026400c0090301a00101051031075540011524070b0140e04584029558046245003144450700b61195221b280e0082c05802220b80a0301420f002c40d070310171100b842110050b000710a40010865000e80781480b003000c1103c090081c400305d034196101920000c0c181c00c0c80303802d1141070040242944648181c0807949501038400244660a03da07413294401e00060401c042040004141414900748031005160107039039003c0140c0c240004c1c40781c5a4401c0c088a01401001e48252440d55146401001311060040180020342000c1c6866881d0003d260003031070510003007208001c2806034002e4504c480b1002441e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 810340548 1250 810339298 810339301
    0x1a07170910020408070306201207030e0f070501180501080604020904060509010b04080d0309030807030b0118031401110c030708071a0a0209030708011a0d020609040504240221 77
    0x22550328080750100e02600e164000b19000920720b01c042011011039008150920030084941d00740c1080d880d2803824011200400c1c40814009a0100314650b4040711074100001c0361240c42c41101d2a0151801111085610100042c401940e0269880418504d41951500c034981002c0028211180050800b809070368041800205c9a0f9179030400002824040c00d254801c1d61075404444056001c1d009022281c45640e680c2c0c2c19241c802d20074500006d8043d5120451502c45a00c104c020f0f00b03810b0b600300d0400c40d9069541606480703581200c0000c61244e40420322281600c1026400d407080c0f109195054101800424403036040481141e414a178401422556001c40b42f5041e140c1c05c0940c074a24291583c1d560821520a805a00924100e41c00b01c00b1241190381c2d6010a40c243c4d62100585802e61281d414080942d0400d0b5840c25200e0303100605460410b15510027140441d217044500740c5041d152829600030714200c0d031800a052106190041d0314010301001d0314000c6449070003551100004400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 810341798 1250 810340548 810340561
    0xb010f020601080a080c032203030f050a050a08060310020412020a0909030215070203040807171c14070305120703093813150e070608011208070201020f01181a0717 72
    0x44412050154101600701180e51f0120200c8d4011400210041a090780b0401096400ba20940d072907440c00d50f0b42c851400301c205e0011a204c0e08094620b94040c07241c1000d0303c002c183c403030020303102400003d04890b021414500420107043c0c0a0351042c40050b00d03000210b00800d9020504025241c1411221303c03140d280e22008924510039507012409034001d503040810b5404d0b018510890480099044420200a140c00940c0600e08a20610017040e4204000c454084410300078050740b9009041c82402d00d000d017149411140310440301c01002036510102c0c0010060070320010503075a01c46020141000400c44500d542c00302c5282034507003480c0c0b46500020682c0903c00b014101c11640074072410310a40c07001546402402007000403912a01800c100880c00611401d4114120f6011800f05074490041d03845e103148640c0480001e0303045001d01544c8100d002424010084001c00c0c80c0b240d4100480b95003001031500080c81c0c1c4141401c801001030007a0075a014180c00c240a4480c41141410384581 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810343048 1250 810341798 810341803
    0x120e04271b030b0711011a0418080f03100e010806130204060308130e0903091c032007090b090f07031a180115031b0f030209130b010f020601080a080c 66
    0x2040304900c103041c200710200410142000740b500841ca03940302c80c410200308a4455003a1a0b421450444a1905140080351441c05070040c00342180d80c08480baa000c00c1d96210401c4690018000a102c06000001c3c0b01080c403842d4200d8000741034118151256504020790349498500250078103403c012160049030655440342d104900941e03200c07403616a504010100d00140600d24481c1c01617034080c1070005a00d029000c011a42d071000001c01103803100d190948a881595280d10b810740404c02c030850303415080d00504100140d19503402c402000c1591074103001c142942c1503800d0080c043d600a0083c8480f41c048458090b800c0603c906003c1000000150240d080660300c08445d40c4c410b88610002e05250300301480141661900f103000380c40f032002a04180c040d10003801c00301d0040042e880c41e800312103204203100118a4001d00d00036180140000000300114030740410901e40d04c0d901c0c0720920b07180da0460810003030034000e0f0020b40340c0356250060003a1550064103000c1d181110000b540100c1d690207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 810344298 1250 810343048 810343073
    0x3120e1608030c1002180d0302010b0306071d120309060f120109060f0902091f030204060e0a05010c170f04090b030d03144308091606050d0b0904120e0427 68
    0x280005100381e0503801d000b8060809030be101401390140c2d80100304c009200d050207e1403061740010600c5102c58100c140318000060031400f41c00340c00180004811a40c44000400c06007140c001b2041c1c640c504090a0a034028044c1e008004052810108001202c42400300d101183c10003040140c0f030b180702c84041840800b03012806d0319684004129842d100b60154064000c4d9070461783c0e122002c5038814103000040229004550110342d02603a80342c00144100320764041710703002d5510f20b400d02e8940b010074100d13030304141c02c000301d03c54440a800c003c60034204040c01300c01c0820300d001e00500310341c006c80f03640503800506400562302c4003804040010340008181035881540d03460341c00524140d2003482c00d4407010300007014005425000859004200021064084c95140c64641081d0703240050a03105944444c0320609000c0d191700c1050740030358603404000d00c5603010300c0721301c1003013960300000914482240d00f82501c918600002d03815440c1e003c0c13150140c0070100f9031500398045054142003500f01b08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 810345548 1250 810344298 810344347
    0x1b02040c11010c0503060d060506150301060306031101080411090a0b0904140c100509010e210708010b0a080c0d06110f0403170307170403120e1608030c1002 69
    0x1000080088103038090039a0361044501c00007041040f0409004603910b11060715110b60104106d009403010540c541c2c0929001031000704111180242c404480040380c10907070010001c00e0b0b850b0400c04c1403010704401c0d03001e200800d03c0c3c4a02e0034039180e0b46e00101001e403403032080c0c05034141c1c80004085100390307442500154001801c104440c50a0b20388507544074500c80ca41100d500490a01c1140d0342400304036001500300c03e80780c103030811080300011500220300101d01d40e4080c0900400e10345502c042c0d10150b1a41c200c140141120f107080071140742c00c0d9110602c40750700915540e4010085034030046000c1c03005540c100d60000b10303a082c6041510203420801d1b044461803000054511908600c480140202ca00c41d07449101c03c1e0118041c2c00c20b0380d000440e0ba074004680500001d003000c3c04441c03a155030092007420541c4040550325450fa08441d001010046c0b990711010f14140300041d1007195000914520b0000c5141c1019034403c1a21410004006c3c8401c0c0d8001c18200800120900551144a03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 810346798 1250 810345548 810345551
    0x61406070f030e060f071502090112150b0a1d0f060a1b020a0b03070801120206070201120e060901140c0f0a050a03020d02030c030a0506042f070b04050609060a051005011b0204 77
    0x91707402903102c4c00da2144508860005541c040c0550641c2103000b03032130307a0510586641140c820041c5a50001d4040c280300811030003801000454a40d1180c005442031004560f40c1d0312801110046103480410a02c1d078851240f80c40f0809145d19541d07440440f0b4009400c0d1a05017071821500f10094510688d148000758000c41401e03000c01c103200713084061071095041ea41c035a200759988111011204000750406901b10400300000c10265000301981c41d039441d000280001d40c000f100711710b0341c2021001c3e81c11000994643c0c1080141c3c00340030910503000418001150302d400030b00b002800c0301d44148080c0d039041c414040ba03801011400b03a4180c44540c1103a442c190344d00e02c1c0401182c0c50039442118540d0309186410b021840601f001d1141212003071080c50074009651107036018069111100103030200b0301400b0856800018401440c0d540603a1003940105a00d0502510207801c4c071000400c03503000b49160104005881c00c17101403510881c2c501b8280b82d03013842d00c004200b00c00d0302d51040c0041c1d08203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 810348048 1250 810346798 810346807
    0x105061c060b15070c09051027060b04080f151b0d060e1821091504080604030206070c0309050603130516090b1002030d020c0a0507080102030604061406070f030e06 72
    0x88500400c0c0a6205682c0c50720780369242e03804082110410740d0780214403c18412300f802681950300d543c0d40602c800d51142008c0c035100c0a055400e1b100c05401126590764046410403180000300085090139145402800c001d884941c0f000300c051000904850103c11a02c02c810303440b850103011074041441d491410b100680d03c1d04500302441100740c2d42c000045141c4e51185424800109080b080d0004125000c00d040846c22290030b02504041d409a50060f00104060065581c040040c40101546009001c10380f41908002e410320400400000521a007500ca42c40001e43c000d03103420070746100311410358890b19140080c005540600c07400030310074803400d0010074500c0790054101044944801040c02102c0c0d280c03080c06034800c460f9044501581c000d01035020610180d1300a0b080580244c8100c07403185126841740c0b450070140e54400245a54000240115800c260203107402a00310b401001d1681d451071408075905100b83d1074040e02e85007060014608061241c541b241c060340000700300d00e441d0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 810349298 1250 810348048 810348079
    0x2060c0109020913150c020106080d0201060312170a0f091430040b1b0102131806050d0f0317070504050415120213150e01090e0105061c060b 62
    0x1c1ca1015000d030721818481c0c0c0041c100c00403100360031035400d510800a459690010101002802a140c900010340d52512804101320408000c102d07082d650990000c1f0381240b45d030620100368084501840200400c540b20500c040620003081c6070401d603141340004a1484d54000c0d9002002c01c19402021440d00004410000d6000076100c051003101008003607042c90541264440c520404010655007070f4180020024000b290380500802402202c1c0a2081440c1c0300589003240c1c8400158a80c40007101002e0118000000703901c10380c0d000d240d00810119003890001818890b42c0040241680075554101c002c0500c40c1400c2412000381034207801e050705010314041d01e150054000c449c011890040d00c901410010140401200e12001c07040c08401d001d6028800c1818039040010119a00c03003440741040790640803148000c04c161b50107040554100f0701410706454035107250142c2c90303051405010999852500d400100ea078000f41403040f14869151002c040c0504020141e1b0200c510382c4040d80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 810350548 1250 810349298 810349301
    0x509060c030d2307030525110102040b120c07030c02060f0705070311030d0201090c0501050304050a05030a1e020a021315090501080c190806060607061113030605070c0305070209060d02060c01 84
    0x2c03a0102443c1c04503540c41d0034040301246c0e0112694401319000f1340000c62210340b0301c81c09481000e0340e840c05e4285201c081c1c401e41c0c266400340e84668485e000c0007542000546154046580140100741813a25041141d10010007000121602900c40c620020351810300155900498a1080d8440142c8107c180d8030704019142185211030140207004a200103a1440c0c8184910283d4641c013808180f0114101001110117400040c4100c2d81c5100f00e04480011a804101802907000c15a5492451295404c48082000d04042481c03055501ca1629400103a564840e0b8000041d449607001504403030107000b4a11083c0075910801a0510388400814200340c049041c00c80700ca0142c4002449040704151450004000c0c400c0c9111904a030b008101903241060007401241c3c0502d001242c0c02c18044200c4001e030b806020969020180a1010010040b0501404d40c3c0070407281003c5d10722a62545014001d80b02d8900028441ca2140300010346035a28046c21014194000e0090760b10b8040315500c450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 810351798 1250 810350548 810350591
    0x40c0c02011215030609140a120906051c1e060303080f090a030f03050c071a0f0907230316030b0f0105040c050904090212060705121005010509060c030d 67
    0xa0001d125004100d200d00414003d010169481201d04204903255032541c85c020040c40500705e036240c10180c140c400c540c808008034a0a00d00801c2c44401200c10007002a00d26441c0d980a10203008003401041c19000030060328413061190701502080801c11500a82e030600700c171101c081456032400101000f450b520801e06840340410310341241c0103884a5049540e98400050014002540b4040000301715110b41c1205410201e1852228180380d00c5035140d030848928140709821200c4d8282c04c101e8505505101aa04281510041c0081c10b080801c0302d200c7c1d60300481040c035900c03545c0c002d08030f40341c8040040b481304d400080642500c00b501e03890212440201070b04c00f03201ca02e04905c00403403145800e03c104500800f6540741c1c140351619103024400640100c0c1010b0303131f028416040f00d194842e01842558410119907417040e5607a1030045614041000c05005140d5540c0104c0090280c0d1740c020013111002d00d001c0399034507143d41c0d82d11b1001d031031440b502c0d49143c1c2081c00c080900a000202d0380307040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 810353048 1250 810351798 810351803
    0x9150201020c061819030e04110c0d03270201020a05030d09260d0b030f2d0f0304030807151109090c030417030603030c0109080304060e39040c0c 64
    0x40c0c0c601c0e1680c9045441040520680010a4010103c010058058100f03501d10301d0b4400e003000c89591103420000b0303027110071030050301d114144c0000b20030501d66401d1004180518580c10708200c2c00309175201034401c10b540c0020031410f950b0481300c400c096a00030024622601d5014084943d10791040545070b006d44909502291600301e04580369154552400301080c00c09040600720341040040741d009000741049075841ca8260144007414211110700740400841d00800e03890300c0d00c554401850714210b44c400944da80348541c0000e0244900341d030380802101c1c00c0320781001006465039041c0c140f60090340c0100b1213055140d0702e40107000e0b11280301e103005011507074811502040700c1d65409402c3d0074180300858008020141c2540d40c031303500c0c180789e4001e27642008010301140c6c18015185802421104d41032420740d00c0b01d00100070803080120754065034100e2001d00e030107007424104240c040030703d4451042c3d10003103610b4101810240c0211203a040b0304040c00080c000e004020441c0c0000d44a80301c40d4005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 810354298 1250 810353048 810353053
    0x603030c0f30190302040b0a021609110301050d030908070e0402091e160e1e0a0501051905072607050c060a0203090405090703061e2304110109150201020c 68
    0x1e0400d03040c40314510350802e94498103141486031102c10880660441092060650030b01010500400700e0b0080c0403110040d400070404414854056100b1074110b6001c036120394240182d5124094200f0f05490446505440800344c088040c0b80681d41118950000b80051190a80c0000d00003e188422806170380296000103240d16424000f140e040c046c07448000c603400c03003800420381c0c0000075103540070703c05218588088400e226100041c0359030800000c000c0700030001e5094456514200301d48100501007400e01d2031402c8214600c0441441550410005005002c41c03054180400d02c40ca001210051116080c2c81c030901190001c078603044200291642d1054500411180c1461411503403510b00b5500110308010700c0c0e60401c0040d2500401c0c1c1420b5000d680030000002d0351a00407090a00d80044000d080440310300107417411151104040456034858848c01182c5024140286070019000f12100951000a80060701c54507020344c06518608481829001c0701641035001e0302400300601c0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 810355548 1250 810354298 810354343
    0x120d0c03030b0d020a0e0601180807061704030806011809060b18040908090d080c1207020312040303051608070f0303020903070f1d06122a0d0f06050603030c0f 70
    0x34885181201030f0300075008410f055081c0400420b200d2001c1e40000b0524005080d00c91948880f415040240d01000700c5510000080c4009900001c241000c480c545454641600e01030302d005003520406480d490510800529141000304003006201c040c081d40401444029a5001c4c01203160344000000145200021f002158030f02e4140200c8140607040400c26007002840d40410411140c900c9084070340400030030002940200500429050700d17489281e45032100d041d1f005041c00d252003180249000c600400040c030000340c11009813665107503081c20ba040e00c0071285c9410b00c85845000c00180103428200e070005c042540c5600141103868064058409150355041e006030104030074010b00248001d4100d9290000032000400c950022005008140d09150308141c14107228003d400e05001c200c85071a08038026540101480e8001d40c00c1d981c3d10711032285521440300140280d20020440c81c2c031607020a02681d001c1050b60314400ca00000d4510030301e480c50b031107680d40f0848000303010404070406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 810356798 1250 810355548 810355571
    0x309090415050c04030c140d08211e0c04062304090914010e010603020303030613180305040609050a050d0b090115230904030203030a0b0105040b04030b06030609031603030902120d0c0303 82
    0xe0002c1e20030301010741004400740c11036031801d0704c40e0400d02c8817071742c0e090043d012b69158809601510b401500d80790301170420610380d2001c128030041d005101000038003041004201f00c9031b11618100d050018292101141c0c0d505046000c86031146500400303d5a003011000c00074400d500d40b40c4100c21443c3e5008210017458942c106080e80c04501c00030b54917400c20300008606060504000c681444860340000702ca0140c0300041851141c1d00c0010750010700d011400b03125468011010101514003102c21003944d601c0e10300083c10740118920004d103552400c0d1301040d002402500194406a00303000c1c8421041d03125003070b6644103206107100d0403c14030700700c040f010241808218280607641590246296a54030141c0c0c4c00a400756880450410104010015080b050880600040c620507400000241045010145800801342100400fa0000c200080c90705000001c2e042c0200c4d81428041002141800055801c090102c224000ca000d08005a5041e9a12052510100e403190300c04001005001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 810358048 1250 810356798 810356819
    0x210c0c0c0906060d0207060e07080a0b01050109050f0103021810020c0301110304030801030b1302040203131a0c1e070c080c011407080307050c0a0c0608091e0309090415050c04030c 79
    0xa49040d80c0100040207418000104da400900905002c1ca40101d00281c201201c9880c203655a4806521604180309580401101103070141c0108401d10301714000c90300b00780000300240500303140c15041c540d00203030501c02220141c002403401440107007481450a4502c0020752030751a1b50160070b00c65481c025940e840d0901200c207407405243c1660f01e8410f280e08503a1084940c1d58041d000c500c0c580d10080c0218010381d02c074001540b09140f51022031000601c0c6250040704414200e289001c81d6148208100c51002070500381c2d00072076010703281d424804580806c420820b114540002d84031403030006002c90049000107100c03e011400382d981080e501510080081c550192050040241f101000400c2d10548154080c0180b5031088003038514061560395a0006414140d00150100d5014030400065800c20b011420003c0700900641b01046984c04072141c69108250141c2c3c400c4070500b01080178000c4540e030446032803c4140040040c0c2c10489110b0b05039810a20003125000b026490100d4441902c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 810359298 1250 810358048 810358051
    0x9080405010201150f05040e101a0906032b0314010b0a1b030905010507060b0d05010605030d1106040219030b0a06050f10020d030f0f150905130b0705210c0c0c09 71
    0x8104111712040c100810480545110303450700c80c0724820004540030110f41031103154511a0318100c0c0d5001d010080c401d0003182c0c41c006080c8c074400d410101807070010782c0a261144503440780c2091402ca15048103801500182100d9109055840507030001140310b2032040014082440c0e1074403071094200603c100211038400c00c401c01400200d5245e4200640d50041001c4c140c0c20b480b9100205282204c80c010400f284140c5500b0f48417070391108001c20450a09012401c07000c40c0070b14010841551904050741e0b0780502800090140c40c08125445034114004e82d4107028540c000c3c004c01141c101550590081c1c0310b80e001d5640308075040904240c80d45841c2e00720028030403041d0090848072000d000c0581c02408442d4080b51850b41340d100303842d50100188a400484584001050300b400d050408a10031503e000707102e14820014003643c0c0000c01c080d40c1d080385d80204039217406075441c1c84203003000b411191171540d95054008080c003400407442151002d0705100b00c0f40012195092550020890003180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810360548 1250 810359298 810359309
    0x70c052e0612080a0c15240509010f0b18060a050c0d050304120f0e13140f01320319031e08010b0c12030403030b09011d150f03010908040501020115 65
    0x410880e04e20528010b400d500d29003805207954240c100e100798500000d5400340446141c0e085c41c0c00c02102d01180715080400e014010560306a0515070424011901c1a8001d008a03a522600030510b2000d1185000100041201c064111510b60055440140042d00440d009010324060b120ba00c141c0e1911801c00d072442183c00cca10310107092a050f500b0742c0c0c40d856050200c41080260425500380391125042514400340d000c0c0c002a074a00c0e180c070a075000b018090071800358076100000410842407201514580130042100340800d924800c3c0707944010300304800310f030b40d0140103640c0192080c80c051014002045d0281d110303422201c1401c40f039400c3c100c9948a001001c541d115006101d000d004101038030003d14040d08840c9011081555554250421941240000d860b822000054204460170341e00400b039141c940302041e84440031000c01c14600512921644024038030071040c5990701441209100b80180082141071810b040444156019004a90142d824480c82010301900c0e03014080c1182c2c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810361798 1250 810360548 810360563
    0x5090703090b07030c2f0f0f0706050906130f03200a03030f0203070605011412030412030503060f040f1409030a0801030f030309080309030405030d1106070c052e0612 73
    0xc0e2408800c0d0020062510f40d6170400ca64150707042d00c10310f01c0e44070494052119111954100e060160802c1c03600c1d42c03111082c441500f040f091a6045600001c00340c1c00d603070480c28115112102ca00c00f068181c0182c18000c800b03400c10044c00100020a0100c10050340e014908a8074550702000d22241c103900c00f100d10980210341c40c642000402d10540490325041890710640340b8151150b203c100a80c2d000303130488640ca840c2c02e84840d50b545013049004910360640400b4500301440c0415440014446a00140a2120000000394940d950381d5083c149034500900400821400384411801010340c07000102d222084000491910800042918520201ca560742816a800c6d692030041c0344450140c01c406243d00c0b0106940092030007c0a50b2240401c10001c4d9225440d140415280827404200601801940e0011040c0c03800d021405a92043c141e0810752030b401d1061400501c0d0130284100c0347c005003515075103a4081408030b8801e1440900450341840301c952100381c090301030400c8445c01008407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810363048 1250 810361798 810361801
    0xa1502061918151b1b03110109030816081303140904060e060102150603120f090901030f150510170a0210050909010b04081504050f150108012003011e030602040f05090703090b 77
    0x5c0302420001c0c1a05203c0d1402a46c1d80700110030143c00c0d5440700c0381c00c4001c0b0300a4000c0040304283c80384044807521306858902898240301c05c0c4000c034a102d20303d001d42000b8460a032a014051a0340c2203c18081c4050000c0001540d1440710348038040e01a1520340c010701420040180100d60410f507280101e5004008d0404420354070391101e5903a0040c0b441024042c001d005400c42a900c08401c4e500071800713114031009078411071500c4019028000d14a0308103525020070b0250001e4a402483c00b9182496681d40c07151204640361032604240c4030b4000d5210742c1c0c11160102c655031141c080d000740b003025600e1030305590701e40100c900c40780510b004440142d44040e02c00d416140008481c10381081c01113040c3c50016618505403400c00c2c000100c035080c034031000c2004101d43d000034803074405601041801006c0e5100c90926603038080c401885a84c0749000c03038240d210801c2074110b54040003154040002c565032540c9001501c07131241280b04451103103e49000059809009000d120a0240c0c86400c44289 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810364298 1250 810363048 810363077
    0xc060c1107150c02040e0303090d03020304030c020d0212100c030b0109031502070206130608330f041e05090106121502030a0204031509020a1502061918151b 69
    0x4a0404010002c01c00c080801c0e80400b603140e6200c0c40021030f0703804002d0b40da04e1070469241840c2500000c0340c901014810410040400d83c4681f14041c41c0360304031020018000b0318000a80e5503211140460101d0150002501c441c410f280e000c4501030146450030710580b8200401507410b600f06100107000300b03507200c4204616142c41c0d4006c24103d0301c000c10341c605050400004559201040e00407a0118081c281440740c5941444100440300501d5215000c0400c6148481c074089001c00030303c1170107900010801d274600e84c1c070707a00f094034400001400482c0c40707060789600d100900815101004207500c0c1c410b002c21801d05180347d4000294000807410005001c40401d00c000354402002c01850641c2400048001a41c180170030352640c01c540e0b4040780c2e0880c0790040040c0b4a54907408041e80c6002c1c1c175020001190046040c9501c105035155002d0411110850301029040c040c3d2103043d10038074411201c08020100c225940b2017030b62400c00300400803204e41c21341c448801c40d00c40c04012400d0840d80090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810365548 1250 810364298 810364319
    0x21203060a0b070305091309080d050901021603020c1810210c0b12060a0f03080c071205030d0f20160b151305071b1b060c060c1107 58
    0x400403400707003441e40307050b54502d0240c410341c001c0741c012000070305c1c0011400603510f807410006904184070841001104030072381d20540310344268084462199118030014410702c000398103468050b10403a241d81241c2200e458001c0d1100c0111100310711030025440203400d41400d052180d84903130815a1019621402c00c02c0d03810752002d081c0b2b1511164194042200d000440e2021030340000c200b203a0f191515400e0340d01101003030170401040f440c0030740f1030110100184014000c40c442140d07080300700559200340c159451801c1c03041503049445602295004801080800801800d070741e5001c4508100c04400c5d404c140003a034070354140c4c4003038200d1044441c80c0c0100e030510040400040c803000115983c04c107030b41c072306c8a10034080781e400946205e045403546d81d13400d0220094883e003034100380402031132602082c003500006d4894100c1c40c00e4103071407000c44200241599007100d00083c842900030b14664564000b484940c003528203c0e005400d058040c0c2ca030078010105c85e20b0003400c04c0054940681000095207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810366798 1250 810365548 810365551
    0x110c150c030106181508010510031b050904020409150614031e09031b0c040e0f0a030305040f1e14011a010302132408070207120f110907020d030516021203 68
    0x180101c210a80000c6100c0ca17010152109181034403142d82640c03610040005284034208090145404c06006420603046481c108804403210b04000392600c1c00c03100410020301554114465242c40d20400103c1c03c50818504001c8644a69a40100c900c04d01c0510b035007404141c50312403e201c0b01c85081c02502e16958040d40d40201040e044074108041c00d021420760034501d076106540d03030b0040b681384012400c4c9405030340c0f604c0001c0402411052581c40d100343c0c1c2c070441c0b0300d00034041655800c0411704008040208800036034018040c0b1a00c26200c071032022804003007520860300c550041d807034a0b403400010b024500c204010500c4582200c4502030056010354011f030310344240d905009001046038040c058200310380707810328208000d10150281003d080d40d0b00140000c0155844800308010003000149555111944000c0e10526404a031038003040c84540034147c1580004143c041010981e8009640c0780e0b07910300c9950510203611030404a440c004406800300f40180c212010b2400081582d00c001c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810368048 1250 810366798 810366827
    0x14160305060f0403051207032a050d020f0c0f070609050f0306060d02040b1e0a090b03031603030b090a02130e01060c030c020a0e040f0b0603240415110c150c030106 72
    0x900e40061881341211b0319a080300c0c194086941e404007800d200642c055072100d6110100140c5204a20340b08015142c0d00030390389160b10060300002c0f41401144aa801e6440c140e0350036080300c4c0c050382008103c684540503400350b440010341a6900140c84e117001000c50240c2000603000d000c141c0c81d80340501c4048100c011041c0d0f041525032810030350780c0e114281c0d90000107400c4d40c10305005120710b07010030040e0301603a4171441d051403c101c819642540c000c4102d82820070950444055110305240c1500070f44070f040c0032198480d45007802c004071100c3c1a00100710b040c0081a10b100c115447d808501e9040c0020701466001454400b900302c0040c0c014007541c40d400d800100000c400603030300d942801842c101260202c0322200c8a074180820041800a01500800f00302c000d000741c011292a03103089070034080c241c4d850102c0c01c0b01c0481c0a1090501d001001c240001c01d0038403841c40d0103005000f00c0d5011000041e07140c8170700188245549c04c408410703800380c010302c541e9514503449c00304101c95498405905 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810369298 1250 810368048 810368057
    0x6120c09030807470c0301050102060f04051203101401090308040b0d290a0e070c0605190c02211204020f011b151a150a03090f14160305060f0403 64
    0xa61529041c90341c004c0348000d02501303040d50010004e064100c40e110040d103840c00080091005120f01c2e07030080340f1251b00c0140420001010f9540b03003000c5191044c1c80302c00f2980710b0000000c0c000500304285e00c1100360b81180d600709400c40b00603001151440321a00c009480c0003424003040c020500198020008015859404030348142204070400d49008400041032480c2101c8151100c0d900701803640c00b00829141010704d21500d00300001501c900ba003850000d20b17055403440040c0c900034800103402c0c1070200c1e8920801440140d820040d65480c2054100481c5981e042c11000a111150049941d1014296021841a1255800d0000c11014042250705200050b16407000007095446480d039058082c112000142603954040300840e40d82c0c0204981c020107100c3c1580050b01e550004030404800814466982c60500d80201c005111307007800201500300c3c4880d88401c0c414008c0e400002118108103454505800d078841c50305c0301e1054800104190441c000143c01001c101c40c5640c0d0290007401c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810370548 1250 810369298 810369353
    0x181a07020604120b010b04080709090303140f040201030509030903071503020f120609010902030103051e070f0b040f05010c050d11120304051509011107170702030706120c09030807 79
    0x181e0160403a800c46070303003c241071160100f48a48006500d005181e1080094135041c00d0116941e01d0f948540202070f50f244e1111020030401d0311a52020b9418040e1100010403818803070501d821a60703040d20140e00190a01d00070810007440801180e0040e03100800402c0c02c07600c1e1810041d2552a0f8400f04d0007495400c2c0502106021440020300c600540a0030885a07441e202d4100012424107030403000340310348107100501c0007500c0010104011a80c0100b00b4807421001078125141415507003040b8114a1081c000040320704924000c0e0040e204000e040c100342c552510011515090140c10140c2a58801c0d0804403845024480d100c03c105110000d0302c050000e04404110380d41c0c13080d101104d442c0d10030068074400541c8090740d0743d0041801c0c0000d0040d800b400360100e5079409030002c0a80b03003075a050103140060030324108072400150b02078143c0340780c550744000c040c0860103201d0710f81c2071041c1400d00810700d20303110b141e400050b00d81c00100c5500b001899195180750040409481160444800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810371798 1250 810370548 810370553
    0x2130618090e0d090b07030c081c0c0c23060105150c01090c0302090702060c1902030405130501150f02100c05131e050a030209040609080f0a08010e0601181a07 70
    0x248000c2c04400304002e1400011601d801003816505520416102170284200c000003680f0180d20420300e90080c0200d80c031504200e41c0300780c1c480c00c1d00c0010050540391120728042590000c7c0c40e61007181c02282e40010800344203241c2d041072a180501d6170301e41d0300801d0040c030440c9820074090004085414100d414010350b01886400c481c010401a03a141d210354004008601e803a4214641c0041c091000c1c00303403402e1204030b001c100e000b041c000c12008821144801c80080c402c00696004000c01071000f014800070003c200000c107821301801286000030075002c143c2e90f0240d40c02e02d0002d1865070052480d2004a2415801420112000d20030414200007070b00101c0c01c0200200c001d0004a0b035035103281d0000e100311890030111940a0780c0134107041041000942d4560680039170082c0c0044001c60700d0710252808105a1084400000c1c1250303000c80c0c28595154040c05485c140e854602000c03001d0784030180103641c09030100110000c100384100d410300c01c46c0040780c0301d003854481c1a91803504020995 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810373048 1250 810371798 810371801
    0x17030f0f070c090c051306051c0b010e040f1a030f0c0405041e0b19090203071401021212100e0906061e061c0507030e0601030f020609090109020a0f02010213061809 72
    0xe20013800014008580c01210705411349400f4024180360800c20329003580c040c404c01c0050b00051001c81c0d419501d02d0110166405080c00c3e0030600350040080141641401c031800c020f0101c01101180c0300c018221450361420001189542248000000c1003501003003803c12000d480300400803038030706c2c802c0640c0704030400486043c154541d100320f408400900d07140b9004041410006030a8080d103040c038a00b82c0c05a10040b6905064401e00c00585100c01e544000503480c00c080e801c018604d040d00021b00a945407403095215004215660700d50f9605a0744000c0e00b00d000b04291547d06880d044140480c03250303d4901c40390b00ca08504084005074070020000020210340210324245420441030400c0c0c04a01d038039216840d807080f11410300704910420070503201c0d941c01c01400014140c44000d94810159607440d0b007541c2c2400d03401002006690f07146c500700000b035045801d4410214241030350190085006000b5220101d0884040c890040c0c41c000048550113240410000c54444194020491b400346 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810374298 1250 810373048 810373061
    0xf061b0e040b09061309080903030412060b061c05060117070c0201021c0f0f02030d0f0b100c2619030608160810020315091017030f0f070c09 62
    0x140d1242440c108284003404252081d1a50b068030405482080001c15921702c0c031550f444100320030000581c650585440708a503c94a9400c681c10b200c0410700190742c80d075104417080c2203803041c0f5040c0300324960070061007107a025a0241c507402105050f0014501d8280d07921056003c1014501070700b141c14118034601140d43c0c15505034000070140c9500009550b0104444e01e001c680d00d16060f14685503060005003500070b05001c4c1e41c20002800c490380c4410340700300161140c403c4100030800501e0403000407003004004d108a001e008540c1e241560124a0140481c0410590490328055401030403400d02900024110345c0c60040b1907040c480c061034505500c6419002a003a0380f000603605003071001003407034105050000344c0c2c20240c8a02c00d0180c0c20012442c0707252901102005038a988503803141900703888003486002d4210415100b0041c001107510000f40846035807820740c000700724205071015103074800c075120b10703082c40300c100102c02e180e001020061a4050040d00c000b00c1c1a6103542c0c031081540c41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810375548 1250 810374298 810374351
    0x106081b2a0d05030f2d0106030510060305060307030209060112020c0a030212131a16230c091306021c05041101030614010c05030f0d06080f07080a0f06 67
    0x80340d4007984000c1c1080005481d40001410310344c1c15480c100d14180008040200080601c9010203014200c250100d02140940141d41c4000d41080da110400100240720440d818448040c40c0c0c278000800601901c65240101070150190140301d00319000c2c01004000a001d0310304001c21454030082c0c40010340302804101074000003a00d00903090341002031414074000a041c028030001c000c1045100c0d219280801242d50101c0580c40880207a4146512400358800e00c07100c6248504c10b030403c21085158000c0f4100f000d4280503002080c00c0c8000b40e075400981e102640282c018408220402c1e074460815075124444d007805031034044166680600c0502d01c00075840700300c1e1200e0034401005000c1c01d000905540a02c1d0801c0302601d071000c0500e0b026240c0700443c2c1401045c0c0d4817581071100c1481180d1908107900071140c2da4240d00f0035058003c01c010700c5140e0480c069102c040c49202804100b0b20b04071154070f40100807450321519211074101c400c9008999090352210170441409014100c49080c56 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810376798 1250 810375548 810375607
    0x7111e0d031808100f0605090f2208090306070503010b0f1b0118060b010509060301090209040f02040f140607111504210b06090f0721090b1e0106081b 66
    0x122125901819107002d11501c0d0509803d01300300307206646238880c02540c030041c0024070758159120080400706480030750340e500307507034a003195808014400590300401da024415800c6510b40d50b0b42282c21203080c0428060031030078160402080520bc0061400303812010300a0401c112040b44d280728041c06c54200c2c1621400c1c03520001c20074030901c4414800e2559041082c02c00700d182102d03041c0003603600c0c40140160f011a07940404c0040e09615a41e001d40045028460219600c03900c5604010385038195200702c3c00c00720807044062010342809401d98840580c08503c48a0031036107242000341502400102050b03008050000160312101c00e030091840c4442d0442c01140500c1c1030410584401000b001c2c24004c4900100744a01003001140150744452946403822140030012400301c21108422082c0d440d260521a00c1010301c1144224907000e404000e4800104018150040c400020240f04600100704840b0025200741009007882c21008041164240707480e08010296805d07218040c2d6454014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810378048 1250 810376798 810376813
    0xe03031f0909021f051c0b0a1d070c020d060c050d050a29010923040c0206070e09060a0e150f0a080a0204090503040503030a030207111e0d031808 64
    0x50098403800c0c009003809040602c400d00064002c500c1c15070712040031a401120140e141118039118506940e130762040c4283c4040d0a1030240202d06c0540710b030340d41c5a440b40e45d400000188c040b1181c60711175071161018a920855580f2030b001070799a00b42e698405e0b070300075420020b8100001e620380304102980c0e80d641c8405848900031040601190b00003010424281e1401d51400700d460006121001c180b0b6881e9184070900e0410001202d42d00000c3d440842c0c24201e041460301144940592140d1260080d00c08000b15260034000f2682d80d1802e652020100320f106030380d00e0399400e041d00019030010340507103801042940c80d41e03042d8210400722074050350380c000206116020b140505004410917802c0b030311001c0180c00c00d403143d5100c2c0304103800244155a1048a4002c1280c280203a0300140f2009042e207443c0c08038080058040e50180034100ea248604042e0303000c140c035103032030446807400c481c103142e4514a031303000c0912031900000762054081c0011420384140c501c00151071500500307548005002032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810379298 1250 810378048 810378091
    0x6090f191a030108031801022508060703020f031501210b100f09090b1215040309050405100b28020309030f01050115140f040306140a11090d060e0303 66
    0x40e804040c1c0740d825070842000100040100001642c1c06030204c031011401040150b40143e02d840003200030442151040d803403041540b0f00c030f502c4039401c40710b98000b070f01c6107940c2c1c0c26000c8003244a0380c0310f03248030030a00380080380c00c00c041003440e810036001c117040000c030000c0d481441c40c6180c040202141c1c0d0486d12041c41e41554100040c10035500c0b000c0e400c001c4134499901c0c0c009040c4804500540c0d0700107540303021022032980c6004045500d00c3c071440035039030310115424041c01440821542600801da200c500042c190400b803081602c918107821851a00034148022a02142d0000343e16581c2d0420001c0a51070122940075621404e907425001195900101414503040088580030140140d14000c0104408091034600d480c1030305151920aa50700d944c180e9034540c900461134000c00700c81c0c1c0420f01208005981d0300070811516060100440740e80c1e4000240b040c0ca101d1401041322000074000c45000d41003200d080301025111f4800443c00656201c1c0c0649150400c5460308200782031807a90121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810380548 1250 810379298 810379319
    0x140703020423030706122d1b020c042a081f050d080d150603020c010b030105100e040201090306140103060b03010507120b03120f0a03150602030306060d240608090114040206090f19 79
    0x12380c58203214080201a904c1d50010b1f40f03c01c2d02e4800680030310f03102e02c20001908000c0c4201c0304042181d1404c0055515450401451b03020304807400141e2075a07a0102c1c211080c6200800c40172200002c001d8682c8005a40c1c49401c1c0303400006005031503648401c0703100c00d4680004140d002070080343c0c0c2c006841d8903c00d810030342556804003c090090349043c040c8a800300d81d0400d1740c401e40700c110b80d000c40c15890380d1004a40452541e4000741180d8038200e40145180b031980e0095040300d000f2401405004094410035080b19400c4d10b40b01e010440000795103503810a135401400c80c00b003005040d03404000c185508100d45a1101c2400003548000091410000f501403140640b51942c00704010b0102c2c0c20107201035503a2202a245178420320000c02c000346164096007104140501103848540340e12100c0c54ac0c5100b034900da004100100e641200001d0001005120741015002c040f1003528582e140c03502803040302d900c09140b0a4208601c4801e07130005480782c2c1c00d810342010030220004a003515020080c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810381798 1250 810380548 810380561
    0x31416060c0b0402120c120607142503020c03030d020702090112081b0a120c050609011104140f030a0b011a0a0c0206090301140703020423030706122d 66
    0x3418829000d041d80081400000290351141d419103000d0340c4403800007059841c260b0b00782c00540d40540100c41c0c11510350b40101c1c24500801481d112003c401c0a8403082c41602c0c06100400090208010340c00c006d109524913601414a00900555054107000e9010071f08580c800c014006034680c00148400450034480c0700700340140300b0908001c0d5211159074880d45e0303c3c81117250341600c40c00c070341340c03c1035004e5018031081181941c0101d840032410880304014080d01f03001c5c04195001d015140000711400c03811700950b08c0599071003a1041c98542410740740b00c0400c1c41c8400c99a04401c1e0994041038640b01080a020614047d0600316003a6240141607140e81c40c0d100043c2d80b00c0d4405210400342c1c5c540080f115951140d040754441d486103820320101e40100340740c1d08400424485801030007007240c1c040e4010401c3d900704000e00300f601c030740c503900c518082c149880600c0e401d544505402c00171917100300c0301031041c51520344010400c982c0b102406180c0012000d40d1028030210b260950340300359501c0c030410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810383048 1250 810381798 810381809
    0x50a08131b180b0612070513091e05040201080718091d0f07060e060c1f0209010318050304091d07030302100e010b010e10031107110f0d0803070e040204031416 70
    0x1480f25a110308081402401111842c0d0200341840340403e2600c0d0241080e1114103120200021140d6580c01100b40a082113111020904000520000200d9458041c0a120302d406840b03021041d107549034122400922441c01200000c009100480c01c0c070f80364081c4001001c1c840007201e032070352032100d05e50b810100b491307022070031580c00300c0b10412040f42c10050035000c110003111a291501c0031005c0d400c0c00c01c01c03410804078003c04122001d0704000d0065000d0030a124080c2d0302000300c28207034074401e9aa146903d40c007a0041e441403104100c20141500032184801080346500d40d03003440d482c1c01d98503150341074008a02580180001000d082450b2180007448091800240070701e13403980c00040d0032544180156802010b495284c0003c17507020380c001040c40c2c4240c41c0d006a6480031810410510700b5503854641c03051805031403860f050f10b04401040d01880c0c1241c04075141d900ca60340b05a0349840c4510f512504a5002d010001c041229001030030400e44d241000b805980321613204482e0f800c10150072a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810384298 1250 810383048 810383051
    0x2090f070210020d1b180803040e01411e0607030c020609060a0c110a030b1807211202010e070902030402150c1e03070201050a08131b18 60
    0x10400d4a6900051016504050a40c01603840450b200e00401030328481c0c442c209050300e804001112079034000e85440c80160307140078219115440c0d44002c0d032244a140b1940c1112441c1d100148030313690318250a080c4111a1714140d500200380c8804072000d00d61b14240015001d49030683e000300e6400c054054075480001d8206103070743d240040000803a41c0c003035058003404000d80350030780fa000c544640d0119a21620000c01160302e414154000800e00130324840f007159226000f03982174401c5d090194a0605495000c5400c0c0e541d40d85445541e2241c107844241c0d05007511070700d503000130486c0d00520300402c4000034085600914505043c8825204500c0c0c0003c0f08582c90515855080580442d840c2c0903620700d001c015030341c0d444900005c0c804900c00d004d41000a070001480c500007090010f8034645035106d000951a100d81c55001c070760345034022200060b012900070804082018480d8114540c0a003001c0414409000d050300e0300a82c801da11003801f003003024044070038440c0d20110300c04080c1c8000420320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810385548 1250 810384298 810384301
    0x1c0f06060f1101050f130f1e02210a081804140f0601020606030c040c120203070f0f0801180207052a150c03070b091905010f062103050a0c0501061202090f 68
    0x8018040d01c0c3d00422550300154002821010032503841f20400c6001d4015011a03544600d11601408002000740700b24400c03002404d401c0181c0c10650204074064610001401060707010f1f0322030400c42d42c003061412004600041c80c08038160740304d100301d00160001c1000c00010385000c0f00014041030b0068427241c15540030100300b100c0e40da000100701c101220141e50105000c40944c1c810341c0c9001000760b540c8a1140040200707c500e0360705c01300c0c3d03410704100e55980c04248110b0310340070b07100d840081c0a9141d12620840041e2166001500100781e035600c2002104c6090b15584030b00c1c1118000366240301d003502d00703070252100c1e9458017408001d0407070100c071101031510100a424560307900c6000401051401c10307100191b0300b080103000c8100f5583c8440d000080d00740040c60014001d00f4607100e1000c2485c504000482c041c81200e00c51011003800c203400320080507080d203060301c0a0304281c11140400202408031f1000034028010305005000c80010f0003080342c910710400c003400700010405103a0104140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810386798 1250 810385548 810385561
    0x70e0f22020d081606060b0703090f0f030204181209030219080a0605090a0807080409060f060c4106060613032604080f010617031c0f06060f110105 65
    0x842e1580712039809414180e032401c42c5540000c4003001410041c02003131030224002500c8950100030100391344aa41d1f8048110303142c0302c43d0200980c5d94001c42d1000d004109040c00103040642c04881c030690403d20355904280c0076070b207040050803486403410000c0d0040d8070400860620092180d000c450220022481504041210b40e40e40a10b09020f8840b5844101180f01340d2130a029440046400001c0c480c5c1d9812142440b444a42c4075220310003039645032100005002c0c1c0c0d07000034802611426034551002c0c00540c3c541c0440c1481d60620252a03081030b42c40d40d80e40d018110300c8503e108a0504c1443d41d500b015152031400c00000424540c042c45040041040001c104168101071701c1c1d10003403500e025a0824600342d848440c01e07500750046500050041041900091803800b220a40d500a004164460044050400fa00c6a01c080c0315417081c0b01d0307144140040c41200d19050403c00c00001d48840e1060008144c0d84036a200d600400c002c940d0b050089a030001486440c0111000248150f04185 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810388048 1250 810386798 810386809
    0x1401090b0c0a170c010c0c0302061315020a090b0a020f0c0603250e0402030a0e2506030c050c01110a080c03010b09040b060705101e090b010512070e0f2202 68
    0x1102c01000d80d540003c1c60240c000b2080705960034860b02d60001c00402c1200c41c80a043d00e0071402c0300307034058410300340041e10704d49840d411042d2301340d840704611a0111075004110701a401c4070154605001d03c0d01c40c0800c4001e0308002801c0a081254000c058510603a44050300b400005030415006007001c03c00c00c40e032401c00c42d1010f00c034001820a000308840d01130f4000c80b484a2618880c0d64814000401d104046c405c0343c212204c030000d440300782d8200444030800d001c001c980070300450140c2402080e04001c2075019034011076020700c0904015291258510206084a0503140401c40ca540c0201d2041052580200265805503074041c01e640f45504001c6101100d004140d030041c840c0b516039201400c50340758107050302c070202d50010894042c1707840c01c01c400c0c0c0908034102401806801400d40000720003014000d860030349070443c40003201131f421b01e81403040460f1509410300d200c0c80388000002c1c3c0d0402d000380301b503c105418840315180d42483c18092035080480e01c0380e101101e404620741c0700076a492 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810389298 1250 810388048 810388063
    0x114010915050f10050f03040b060907021b100c02130c0305090313090b0a0314061503030a080a09030905060705070806151c0c0b0f09090603011808030604151401090b0c 74
    0xc07a464850004011000c841e0b038461ba030101c0c1880c50002c1b007031100f00706802c4440d81c0118401c96204115560707140040ba43c3c0c100d4003480001e001c08400d4541603508124444240702c401074904039010f40c2c0950042a582d03041c01140c0c0d20415612103100c003e4503894421140c214010394082c0d032900804400080380703003960b40202ea0006654607200e1542d5540c04029000659004030320000c807041c4e6015564650b10200d44007142801c0c001d000464070f29001c000c8591094407910741103210b45425940740e005003513003102181413086e0100c3c08240c0e0b640310720103400507034410340003000400c0c100031809081c200d02800b01c400c1e0b10300d040491041961100c06508100301301604000340c6000b00d0514030240d00196200001180700000c005a4298060000702010380003540c440040c0c0d100c01090508035282d030b03101a0b881c83c584804e9000040c442c00011500450010404117031070030841e0740b015250b09580e001050724104401a641c00d940c203c0b82180c024400042d80700c0c103000707600320360540700c2a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810390548 1250 810389298 810389329
    0x110c0c0f091f12050309040507031503110d08070503180a060507060c020c0604090608010b06090f060a021006060e10030903140a0311040303020d110d1b02060c011401091505 76
    0x2c0020526203071840a08840c0003855846100038403800300e410540d40b00e80c8406c05031030084c0c0c100400508107500074056401d010149240030b0f42224950f407104510502d40700d200315440041e68007684042030343c84000d1b00380240200c000d10741e205480190326116004c42e8078040d0191640085c1040020317040f400740c44020f904210045050310740c48034202e041000004809038460780c041008114420558032120641d007a00000300034007034010082109501508025039406404080d04411034200100a80000c01c002e004503896100119020700585001c0c0d000040040c3d92244480708a24201120b0002114503060410441080b03403401080c5001d0a8002070340000002468502c15203c0e900031041d241c13902d000a030f2500d8a91500030340300e58408182d8000580303454044050903101051b90031109450340c4030b00501d0410000120706021800c003050340d02c15010720040c081544207024002000001503584c005560400c555003046841084600d4011002d40720f00340115111140d420200d1007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810391798 1250 810390548 810390571
    0x1050d0b010c0218090705030a020307090903180308070201080a05090d03150b030c04080105010b0414100c05010e0705012c09061f1206091103040b041104110c0c0f09 73
    0x204040040e624682c404000039040307980483c05000e00e09501500b50701400c0d4500c140d17143e495030b940425603100e840c0d11010f5455080780a08011019003640104040380c4281002c00780b412210078078000454056005407040c06000a59004541e8401d01c295800350041008011030300741741e851195520b0032060540141641c40810b00501c1074920304900043c0081152543c0d41d10b002d074030082c8203070030612030040c2030340c24000003162020a400130b032800d59111600c00c0d4100c0000f042000001422014000d041c4200a401d0501054080c02401b52000d1548000c022881c50180018007181800142d04c4522051000c1d004203450304000c085212001107a148286440e442c00050508941110b40845444c0e241c10100782d494000441401c1e01448550810640c0d5031032020405a685502c003070050740504100007000140c41c083c3c441c0e0450302400700b411844180301c0106040b40c810140140401101141c035031100c0b68100440070800c001624070a505043e4800030604601002d4054920300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810393048 1250 810391798 810391811
    0x2505031504050c040512031b0a0210210c0503150603220204270b010f0f05040e280b1003030203070209092b020d0e090c070f06050406020405100e01050d 67
    0x3c21a10070350b4040c102c02041003101881c092040d6950354080104011741181c000d003007a03400d0b02e01080703583c0200d4010b09030014441080d0411517810702140000114183c502c44844501152481400486040c6031500c075601d08103440c2c07a40a0300030705460f1071301c902c0e0104200080c103503004d4210381070150580e41070010382c6070030303c0001c0143c41c045008007482001d07030682a00351401740d2000d51200303002d840007601d26600d800f91089401c00c94000e07580c4008180d60100f050342000e81c44490b4101c0e1031410349030102007007074000c80004502a0100f100c0c8040d50390002c1804803070040c56400c10104240d505440380345680280d104d005200e0064419811140020041c2c202880002a480f8810f8038150304200e840200d480c180000c01e4002005111b1032000802c1c041c010340745e07051105170007440b80150faa14444076090742d50051004071449880c0d42c03440ca0016a01d4003525000320b104800150b1260300f01000d0100c1129031400200070000080310402d07090740c0140441e202d20003004400701e0355 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810394298 1250 810393048 810393061
    0xf030d02120a0905073c1505030903030708040f0f0303050106030b011b030e0111060109021b06071d06120a091b0308041202040608030307031508070b1902070e250503150405 76
    0x2e4020803000c400641300070801c011010394100e90a182a01c1010300780187d083c4803000d04407150b01003100d00b030509500800101c2c00c0d00b802012550b038040c3c4100349070196001165070b010f001e8502e50f0412400720707880d6001400303000d8040c003608a40410070310f800010f1145202e80006885d01c03074500601401994801c908890340f081c007255000c10118801c4031003e5035101e080400039400500074801c6a103008044020507800400c289000d1006035482030f01c1d04402e000c6120008010500b42580118100454042c1040c0100c181d403003148202d800042c000170b51304041d98850f00800f400340c4142c444000c28030000321014183c80c103540c412500107103060528400300f802805c66402c803280c240300120030015020b505403c0400b410700707890b81c00000709990700d034003541d1000705003c0c5042038071040c0310b24940071000c01d009800f401044c0c4111124070765a01091502410150b0329a1562040c00464051809250001005e65851498901d24520388100c110741c101907400c08091090351654007180340d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810395548 1250 810394298 810394349
    0x4090c030605030a140c01032906160302070f0816091104030c091a06090102030f0d02160b0709060e1c02030f01020d02130909170c0f030d02120a090507 67
    0x30341405000c48a1320341c084c0c01c02e000000c9031404801e410340304a40032840c85511a00805820000e01040a00403805d21400e58024411504c00107404c020140000805411005c020412603402900a854403506103e13410401c0d001c95045071903180d20400c1c0014518003030080300d004803803208400240e81d10840c0020003980c441d80d4400b4100c6a803403400440d83c1c010650000014013803070351058505031f031440144a124042c480c00c09000d40c000784807a00340300e1064401840c1a0007688401840c06d0001c10b004599407110000035207038500d100b803c0100302904030b58120090405824221012448070000908038000641c2d1850581c00852685013151410080a41d4481d0250000e54032407138681e00c00402504121500018458480d00008081c0c1c11440741c01c8540350489d8203000c03000358844070302003107601a10199a46100d1200d07030959100091015002014003503601680d58410310056a1505001a2403184058500700003400000d800181000444900c03010803c100c060082903041d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810396798 1250 810395548 810395561
    0x21b070819020d2f040e0f060a090f0602030f1b070c05011101020c0706080601230304020f0a0b18010f02010c091a0903031908130807061d010e010509011d0304090c03 73
    0x100c0d4448484c0f4140c00d019202101c40d04042c0d003580e007040b0010992130916600d000d00b0401070650b42101c03000c038041100540040030600d0042e07400d1051281c00d40d49030380880c0d100302c48412000302184103101001c1d01403003000507805284103a2605040039034986001210003440707547e0500c0144403821348062001c1d01903030700703001641d000d68400d07e070381e1a0040e1500074101c41141c0040c1801b01e24100d0581024690300001402d220910b013990388036403e00210f0f401ea0031016602914540c40064441401001080307003c150100142640500344005814410117440c900296418126120a86035202004504807078030310041e0102039802d507259142a100d910342d019014003000a4444079420030f91105071104455070307541c5017240d81d54070800c0042c5901000081502d007003000300c000802c0554104100343c401150a46040d80901603916007169031864548000365100c50030031600b6076083c420f15443c0c0b1800b28940e02c4d000001c0718450b03200d10440c0030340e1021582d200014423825109070b0041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810398048 1250 810396798 810396833
    0xb0f150316170304081009051c0201060501031a0d02150d0e03042c0408130e010303110606120d1b050307050f0115060905060d0906021b070819020d 65
    0x488081518422490031005180600d45a0b210110055600300307030008101e40841e0303441d40c050040740d24100141d002070712550710b01340c44900c2445c5580340088000408034444502e15000052181d2412002509843c503103240c940201c685c44488003100d48405480d0064190704480140c00c5214a85052486003e005035008400389443d520f1200c0b20340001c002d0090714040e0015907950a0b00d0700a50204140c18141100b10301c0017000840c0000b00740c00050403c40410403881c900a507154150b04040b0f6900740d0060f400102a140200710340e8105111058104c04180c0f00c500f152280d0700d021680e0340f02403040c03c00420504000118420010218000406500c03c0070349036540c07520704102e82e0759882d507050303c240d951070001d07094080c0300120704403c200c41c1551035085650303240000700001c0350040c03008011100e441307854100005841e84001d002120125500c401252074a0000c1841c040a9420088490b440520f00c0900701c7d070440e410468242d811105010032100c217103800703000c4040a00c0030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810399298 1250 810398048 810398053
    0x711100c090312030e010e01020a0215010815192a0314150301020415030b03060f041104020703021f02130b070f141e15061807030f020c030c03040608060a030b0f1503 73
    0x10007007500c0c1c0c190010700c0650914bd00326106e4014614000f501d0b02820f1107204800d62004005118580382c8420080d4003402d002040c3d407416008045c45ca00395100b9143d02050030a180410141c03080a1000303400c003882441c9400c0140f80080001c050810300d015003000b440010907000180e00b5070702501241c1c068114450422000c24050902070094402c03684d42c24071902407400051019403070700e52454850ba070442c5684500c044c802003400700a6200c000705504502070300340030061461020841c100140e552483c0160344000500e00300c07116000ca50845107030701008100d00700c0801c42009000c60b21580009440f84065160350b03400d440c00d50000ca8150403d013202000400420010034041d240e46004580d60385952744000802c9a403003071400c40550301d0040c90000c41d00e0b0f50310a601841c120005848010301d04452051414516001803c0d4108140e000007010f0190079804455507410880542e1801802811540c03104010315004207035003204040040061024260701c0e02c01410303040d02406 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810400548 1250 810399298 810399311
    0x1914150d0807110109150906050307110105040506040b0127021b0703080310090c0807031a0315090f060402060a080915010b070308150a091a0303030711100c090312030e01 75
    0x3001c40b446040303c650140410f40c400000145880c500491004003180b59aa1110b51313130500205645580000e02640108220f034600f01c003114400348078590203640107038020a418038081c03138810921134050f08a042c4400000d00074015149112441131a030004c50f01c40580c540d54440c0b00f0b13108594403000c00039010f00c5080b80c00000d1002100086004104d401400e01318207840310b90000a50302001d4000001030b0055000801c1a403299102000a201c0c0205203001d06801d400001e00d0000ca0040012040968105000003103904001c4400f8800240c2c01400c40751900f83c0014880f800b4200440042c000d5841c000348180009005812180d80320700d0b85600da40d61603905900594125803002c5020840003404152140e85040c040c07081914010038503c0c9060030700f580c040207048180d01500c185030085910015969082c80030350302c954400d40d10a500640c400d030b03d0900d44030b030000108031070924000d140348200303038041c1d4100162038200d050100220000d0504070000e00034060a0401c6500e000e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810401798 1250 810400548 810400553
    0x40f050d172b1103070318061109010201050619050607140706090302030c0108040c0b0c0102121302150708040e270d0f0e060412031107030302061914150d0807 70
    0x4240c80c003a0500021103180b80082d00941c1e044680e14001030f120340e5424400200105c4c4070340c10078285010601d50414040d02e00750b0325001900c0701d81520741d0040501103584103107942d092203125440744e030407605d20345581c0e01900707580715100150141d18012000042c805040c04107150f40e02c0824070b142e404030340c0c142d035482c0801000c6650a0200324403a01801c418850558440c001640c00790b50408215841d0614001030508540d100e44070840d0306540078061440405041c42a99100b00c1c0881d000c04a545820f01c100140307024440d01011042c4030512421010450718004d0b0b40035690408034004458540c803480e01d280c200e00d0755540c041c007c042e0304400750255011901c01c0c400140b580351750151b003c41c0c0300d003941c2e104605a80d05801c002d09100400c20b101700a2820008640a4203001a500307a80245043c14083c0c01e4000b80d01590200060210700400302c0d400380114010b901c020800480c1803d070203a1030300805019200e81c003080004a007003a0750f8107503002081d164002c140c01d54803089403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810403048 1250 810401798 810401827
    0x50630010806010e0a020901020c1e180a06060813121419021b1302031b1603080a0b030a0b090f0114060a05030a050706080c19030506030f03040f050d17 67
    0xd01841c81016114004140c81c05c110b4002d881001c20141c01401a980789002880300481901a803504141c48900d0950364030b407a054a4070807807424104410b5040d2504a500b401528241d500c1803082008520410440000e914580b034015540301800c81185010301c03000f00c0b000394248030b0b074000318000000c020001c0200480800c04642d003036000e441d080e401b84018035844810074510070740c0000c92030b046608916115030086520104d00110042440041c95a1080316081140c07424810800010703140207040e00511aa41e102441c104181301582c100808261035110080006007158005000701d0141541070105818035100c0c10000c101724410030300180b99105083d65901d004e209540004a5642808500711044035000401016594584034080312444002070026040203410304c0032888015588145200c0d87e840743d0380100d02c50070114101030a0943e100703021080c50380b080004100c2d04030100750f0305040b82c004654500c03030101c59050040503100c034024455144540080d050340c105040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810404298 1250 810403048 810403051
    0xe0714182d091c0306050303070b09030c0a05031c060f0308030601020a06230c0f03010e1801020403080304061a030d0c060e01050403181a0f250b060112020301050630010806 76
    0x40c0880c0f11003070f810204190b0446005005481e09a041080140003203111300075116082002041107915000b240700ca45814070114040407580303600300061800881c80079643d0200a007141110400020307161400c0114211001c0c8401003480c180800001c05aa00078010b000e0016000f0100344043c40798205c051840a4040c007030002c00a464201050000c1107010a4800c0c0400d1203182d946142d003881c80341851a00003c041001041d84088100040482030019100440c4141da0050303d03414589400c170151400340c4c002400d401c2229501071004d0368000b0708561085243d0405e10310b01c407102d040103809401c0450f1241d00640c05d102c10700040560001c103200e140f841540802d00002d40b9001020360482c0741c421901b42e020740c14810320307102e41140c0004003100802505010804000f400001d801e100704050262108030019080004c41e5800c0507590052449000301149598106000110180246080c03190788410b0508000049031140b50030010403683d034140301450390303941c024295071202c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810405548 1250 810404298 810404323
    0x40c09050a2c1b04090906050112030e01050a020c060c150c030411040507110a0303050108010b0f06180d080304080d0b0a0501300e0714182d09 63
    0x10140001c0300c01d9100201801034040c1d0344942c00160b15803000c05104000a8981a00008449103408048803090000d000810784208003064250450400b042103800503030100101a052040700d00c00258050b10680c0d070386c0d900342000e544030301c17420740c04070720b1320790f00110894010100140c221700402000540828038852202c40000e2940c4200c0100d80900013514003c24005056210a0389840c090b007040b54400b100b8075001c106400c0c01c03500113140500302981507011030795032801442501400c0c016107035015000c0c5c40b207155103522980414414861000a581d00b15020035a80300d07590b5410080b0301d00700b42c000c5045a26810f05013480c56156200c041120003ca183c42e4815000707041881140d002c4a00503181c1850b5040b034010950f82000c40c03116035a0a030000e050303c50f0000c160501c601da44588590000b401c00034100300d05540c2001040c00400d1054400e0003840c19101c51400040ba400340000c03161015031082031125030354501900a4203000c0b0b4402d8020030605040000c1e8291407401d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810406798 1250 810405548 810405559
    0x11040608010218010c031d03030d0f090c0602070501120b04090203031b160b04030b07030b0913030e06040e011e030506010e04110f0f0d02060408250819060905010b040c0905 76
    0xc540d0001540d9105c031640b40103011451504001708089055644400c01c400e002e81581d1a0082c86031000d81141c00e44181365140599400200052020250b5044043c0901b400100f05903414400045c01200080450300c88160710744110043d80c0d121500070300c020b5603000d01101d45800e00b10421390000a2080c0d0615940d00c200e030402e400c02d411000300c0600b100d956107603c0385803d040d900c42d4541044010032100c1410703110504c50300262900000d1900c00e620341d0b0503608c00f000c11480c3c010180b000d00c0440c1c41c40b0b420140024440c0038201d280749411124040c4080606042e07011612244500390f503c0a0064040c07580009555800c046005100754480c03030101131144d0300b46003000700c044101406a5002081e80740c2452603410500e01d05070b6035500042810f2b05195a5282c0d103031501139241100d502d081504002600c000600641e260041c000d040c000d40714043c04440030110260f400d40000d450b19072904c00c89d1092040c00c0d480041c0c80e41d03000d0010b201c40d064003e009443c0c40524801d050295 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810408048 1250 810406798 810406837
    0x20c2d060a0501030f110319150605011115060d0f0b06090c0a36080a0203062a0706020408030a0c0c06020c1503150603011508070c1e110406080102 65
    0x395881420b040e60703801300c48a4000380d4030313840d1700c1d08400302205490b070523106680c4a04511100004074018561003440500913400114403100140e07805903001a050251850b1000100540401e84103600aa0701d800c522031030361488000f4101d05400355014001e0f0a60040100900000c0142c1c14800e00050707038103843ca51642202e2032813074030503110760a00241c000034007080c000117501810728182c1034050703200e08000100da119810815441d440320900750304c030300010021818140904c80e40854083c0e0a21011a0303400148044082c2c01c84a44c1e40f59800000c04004001141d4152070160201d482100e4540c0300d80030003c0d20f0505464000d40d50f41c0440000000c05130700c005010021000041e003061043c90826081800d40c4d01b026001c54100d404081c401c50503600c0f0b06000c0d50080990510b0320bc19040301040280921402401c0c50041104c03003420321012400e982e0722400c20803600ca00c56082502c6c0b6080031031600d80344038000c0d80c2c41420414001101201500501550802c9407180e1102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810409298 1250 810408048 810408061
    0xc0c0608010302011215050618040515090103080d11042309270a061407030e0102132102150a0305150319080706090b1812030a020c2d06 60
    0x80c0c5001d1200900003100c4a603010b02d14941d540101c0080401c0c25000b405468550b00040d070705412883d0100c002c4040a4505091450517005890700103c940b61030500400072a408203008400501000d071400d0130001d0360003062001640303c80620580c1099090f115622025080e00207045504040601032001d005c28a10b0302d080d02d2003030700654984030090900604030f0318924580741001e224042d6030082e0700746140803038a03e00840d4501c50182254400c50714010f500a070894401844503141a88144401036103246c407030510354181c3e40b46140d005a10580f115900d016120311801c000d402603143e40e407541d000101136010b004d104096840c1270203250343d03003c007003840e00700c0c03104c1c040e0342c160301482e10402c84d451041c890079102030042140500d00310007510b6560a98006500481d0061026400c00140030520141c01030f10000c00ca01900f60a8413000342ca43c81070001500c0302c01099400501020240410003010b845855800142008565824407291030000c3c0b0008002060103050001800d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810410548 1250 810409298 810409307
    0x50603010e04022103090f0310060801021903020c0c040f0b03011b14120103020d03050714062d0103080d0605270912120c0405061c0c05070c230603070c0c06 69
    0x114213030040011030420b8001802c1000c041000203a2503054042e40c110012090300c18000d40f000380c4040000580c1d211035180c10094008940081003041510501040c00d03203081c0801c841c1c080200c1214041035242c820b03540762009004c000700c42c507415840c2002c0c80d45102c800a49422441354651210f078501217140714012420302c01c0203050080340110b90010b200501d804585145500d000385030490030020580d5402e40288084450a40c0940c46002004071840d403000740031105900c1c0ca00002c15031401d0510090b8200fa06020041a00001146801c0c0d8030145501080003020001c040d01d44401e0742c0b10114070741d0b030401001100841940b9000030300b0b40000203400c011100900320102e01d00790700002d040783c4030301e80a0091030943c601007000080319030751840581a4442403514905c4900e50400018007107a0440040106200c424010040411150404c41044413250b00481d800c034030303440c00c500c100503000c02005c0f988071700c001c01403101c45039205080c40100d920419215040603180c0e003040c1c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810411798 1250 810410548 810410599
    0xf1409100f0e0a0302033301030f0b0a090b06010e03010e0313031509030801090b0a12080306040516051803010608070e09120f090d3e1509010f0207050603010e0402 72
    0x81d016400403580c7c0e41c030f4800002c2e1690896101021903807414140310400c02e0044c400fa8401e9074000307140d4081800b0300010100841c0c004c500003008010b060042c1c1e85203012034078001e14181c1402481e140b03503010380d01d0030341180e003d4015000c1981d0f030300c0036158412285189140010340b41c24a0350882400c4410769840741440ca5501a240c2841682c030380542c801c0a086090440d030b40114110380b000408002c1008000da00d1031080040e941c480c64918140011558020503000700b0140c080d11040c01d0386c2c0c001003210b60741445030294805102d42040840c0c058500ca501c00f40c1c061040d2800003802424280d101405018054241d032500d00706e0041c4c40d0310b94040e0b0300005000d03160820031500d0138035200303a40c40e00e164800c5000704641822702604003044203450b0400820004804e000001c200150080a101c1c04001c0303400c800001c0503442d070080300d4020001c5481c1800424803071001c02900030441e5070024000140142d07500c2da1910314441c0c8040e419201240600c0c0c2c5d000f22012036018904075038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810413048 1250 810411798 810411803
    0x8010c031a03251d0108010b0d17070503040e0a0204050315010f120f06110a02010b0a0b030106030c020708010929130204150909050102030708160f1409100f0e0a03 72
    0x104818802c42c55010500d08021541030744141c0000c9002600400d44440107022103084d9143e08015071401e4055401c2d110340c42c0b81c8621581260050000080d55016100c2d051000081d03842e032030780c4e800d00d071491651090703030490130782c00d054282000350010880d0014000c0c1c60b4281c0c25904001e90071414a240080c0070302800314207145d20003050020042100c403084e10580582075811169640e42c481e10204c400510102801441c0001c0c01c00001d5024050902d90790001da4004103140d1408001c075259000601401003010344400b01d101c1e0307091080000c1405001e800000704404072080c50504a0f400c01c2c8103681240c00c030740309048903011a51a00003071040c40700f0680c141d09507090790308100c024804840384400d141c104440c040380c0c200185c480d0420300d500c504c2c001652400d0800010700b15a00003040550030044890600c044a541300075020398100351810b1a480000c1a601258003038000d110503180c005030800c406810700390b4845844448442252100d8030149424004d1043c030f0310030b90002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810414298 1250 810413048 810413053
    0x1a01020d02100c0c0602030f01030b13020102190f0c0f03020114091e12070902030a1503050a03030e0a02280e24030a2a0501020c18061908010c031a03 66
    0x80c64150380043d00503442d40d070b1092030308202e100e0b81581c50204030b030415079400c03002440c01e800601c104000c0b960301a400480094000c05410600e82c0002e558841c012003c0807a0807000f00110200b0400203a10f001850340700340709034903054880314194401659448241d00103a0075510211121225508881480718050304c500a01994a07100302861912075040b1604440300a229940710141400b400c0e000d081c0041015959041801141040c0d45251240302c140220b029820000034000040741e038005070b803606011607003000300da20136401c20010402c00782d04020001c0d1a406407100c5100030000e0303100c0c122009000203889010007c11503c045079044a41c010040340007559010448100038440303c024201c904042d203039922902146000154012204007401c6146540310a601110002d01400c1c03005083d0403159030001220450303082c0150302e21400e003d012520984500b06840318240c040465003080c150b030307008042d0080c2204483d505c0041d140c03109144000204106610144400400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810415548 1250 810414298 810414313
    0xe0a0312170a201309111c0b030601061803050d080f070804030203041721040e070302091f0201021204080c010606170408031003060e1507030b09040b0a0b0d061a01020d02 75
    0x3680c00c2581c1c44030005200345011350500090804180c001d503003d2020780c044607601c41c540c00030340c4512603100980c40300c07070b080c100140140c003910001142e504440d114540841001080103540d10011001d41026003580290480c0703485140c0c00c401c4403070142010160030f038003d0703a401204403000c1c1401e59000340160400c1004208048141c51003500c1200c048060ba00d084070041c000c100840d45280c004512840045420004d60a5500b1040e0744200c5a00382540b9110351280000c03c1d07020380340c10042e07000001d1080f0031103582c801d41c140c40c04000410325581d650b04160030242890f41000c00d40341c1c115800c04401007030888c4140c0c0000c22004440c4916202500c41d5502d0034600e81000b0040d4000c8160f51000002081e031500440c401070008801400da5007161043c02400810001c001d403040c1350a0003900c072100d4036040c40c1e0540c070517040301c0b400304691251400da002400d00b000d0f00301d90041180401d403051026540c0030300a604d56003004404c42003404001641c4a110424250340903070000799 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810416798 1250 810415548 810415601
    0x303031a0a14030f0f030910030e011811010c0f0b0414030313050706260606161425290d020306040e01020f04060e0a0312170a 56
    0x200064014030100e00044084250000411100e060781d0703001c0c00e001442c4680207031040c10284091414401041c3c003030030300c40c00b82d641007659a1040440342c038003d0081108112203113100e43c0c8075109200d13004000384420001c41c6100800714801c26000d95410031050074050305980030350781e0541e00c50303804808201c640000e40c0b00c1080d600802081941d50340692740010700001401c1c4002c51180410107402001078405040c204c2c501150b40e0445801d01000030035842544107210050400000681c240d00d40c00c0d510b50340490151b000360401009285a020102d004110742c0e04031400740201400122240310200c5030115010081740409030780c1c90000ca0006000341040044e807521101070b400540c040d0031031100e048426942c02140102e180b19408814090646818041c00008204500003036080400a40400401c1d02c51841102d00307200040011440d6500d880789508011604a140e902c40080908006000c0401e0750340b0020064010200042a608840c810866000110603001c50205021b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810418048 1250 810416798 810416801
    0x10c06050406060e040b0a0e06010f15030605030f0d0e1816020c0d060207020907081b0c0c040c020312010b030c0406210c0201061502280c180617030310030303 70
    0x9801a2241e540f50240810b0142c3e000500a0146201d643c120829140840d0324a041350120950300c0010381010004201e00000c00581605407034003940044140d0074200c006400038401a072005401d0b01032000a0790381c6040205080d1802d44035900c95010030040c510401c90403440c44849802103441c000c01185100005d00d2800b862401c040c011907103100d000b84001f8031300c4d20801004031210f5400044803c210b06143c609140c0040e0705040424060500c0703500c3c607400a0040c2250701c6141c3c8082880584a00c04200030700d099038024004000d910000c0c0d070f00035200d03849003101706410a601000003070001007070340440c1e205840b815083c604003418010211080f80c1c20f1000242e07010310103000703401009214442c11290400c0703500005945440c1100c2c1c240c03054041d40110065410220040040748100303040400013610707107011034a03c1c4031149048004214150455810029411036020340984e03e64001c1c8107558201040a010307451340b1b031100384e0301e100403200846912808813040000a009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810419298 1250 810418048 810418051
    0x91a03090a1b0305070b0d18020f01050309120d0609051b180d06450204051008030417060c040506120a061710150302031b180a090c05060405010c0605 66
    0x603440c25a00d0b54036121307145010101e80150350424030000741e43c00a080544110707624a001400c040142e00744079000181152150b500041c184000000000d441d488148400350043c1c81c9003140c3d0761501580c8240d10001c043e00e004031314000e443c100201c0c00c001e0303400083c0500204d103840614607000810f000054020101034085400424800e54040003c03080c1c043e0074440350481c0c81c0e41a814004c155194418406014072440e40e000d848120008500c1450580383d6854068801281075124903000c031100e40c0e0940c0c030041c05801701180c08038620454094040c00000004216820f540740da4541d400b01e4440ca00c42e06603c0082000701c80c00182484074460351152200f80300103107090380c4400c008240880501150900c1c0c00c440d04988a5118030b00c00c070442a003455110343c0c0300b5130559010035514604500b171400745003004d5800300303003036500c030203140444030b10300d00c141c08050508543e80d801405503020700300d81c01c2803030352004501d90a2603400d9400720350059640328405039031900e076900203000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810420548 1250 810419298 810419333
    0x605060712030b100e0907092d0803032d0c030a181203060914100b030405100f1d1f09080d0212040b01080a08030105121c091a03090a 59
    0x100c4140200c0c03030f43c0d2a1300e690b910a94054445107072180c011010072051a00040044051202c642e000740011090401c400a403519030550070500c1018400d0700d080e4036115640001d0682c4000000c002c0320301076400911408010715280d40d000c41c11001d10155001034112100c201c40c040920001e080380015400ca05c1940480340743c2c0343d20315071140d2608d4852021810701d44002c42d49496042100c00b043d44103005102ca4295980102d9042083c0c04543c03414161045071200100480032406000c01400151100d1000e00410410480c01c0caa840300600200d0034031000041c1e582c03031903000980300442c0900001c0700c40c034540501c8148866030138008101e1000141d840c41010301c2490406203480c4024060b9030380b244a001080d180915000074108416001040310307400103c0444000340c4000180c80c1035900c216600a10b5903d10036071546812a03a203140121103901048003031003142c10440040a44084407601c900c19441150010035611050b100f04465034402200c0c1800b041c40304103d10720075103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810421798 1250 810420548 810420551
    0x30c06050918091906140a0c0906110a060209150d1d3d090b0603070501090b070305180d060c03050703060e06060a05040e09030301151e0e04020f0d050613060506071203 74
    0x1c81ca82c6050301c6d412400c80c1e251003001e980b2200021225001941b14005064514098080d80c0a100d00030f80c4500c0300e58130007070256401241a040540d91190f60861a0340160017444e2107444610240f406040381c00c005440c000940d40d0a480060800302c0d50540d01d0001c1c80040c0c10b030440421802d400e4190f1181010900c2a110400160344170050041da000240149202d01e11030804c10201818100d07a81e00480c103020003135808101c548030f4241070f038050310742508249032100d507690710501c4060408110658000e5901d4108400c0112590140220048503642004245d8405000f5800c0b5812401602a8003047e080014014134100c0020030030481945401c130b0601d95580d400b00280350054130307902007540020005020090718032110481800c030614100d860054041c3c17500c00405e82800c5048200143c0000465680e01c5039011a03120080e544155070350340c3c15a00502d001000103480d000e20503070340f80507003508040710b500502c400da801c01007205142074440d0350b4036070302110201203107018513 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810423048 1250 810421798 810421811
    0x201020106120f020901271e06030308090c1c0f0204020d020301080a14160b090d05070b0a090f05010503180a0605040309090507030c080604020d06030c06050918091906 74
    0xb582c0820701c15803541c3c4519401c1c1e074403542601c100110306105810050b45070b02c602000004104800d00110107001480000190031521440e21400810103821810359150070580300000301603010420b03604c074075505402d40c2c1600046400300b0690352141c58007651040101e070b001c1c00c003040146001300c200620080c4014a015000344620090382c109174031032842900111204c2040c44400303a503e00820081d58081c02910031402018200c81e038150003407070740c0c00002080301c41c0d10381c4500252181450f0400102c920895441c3d515845580c4150600e8001921020b00041e0400d8a002241c06545058450328110784d15107400850500d80b101f400c00c000d10600c2d00450100d4007034130480d0300490080d0350342c1100b142003416107000d4403009010304080504d031103209005c60f80e100e81c00c95003111084174003507502d441d82072500019041a80000e4460354990900140103500030009101c1d0080689503003031284c00400c1080440340c8200c2c1c2040c00c0350414034032031100c4140d0a4259801d1031040d1800100ca = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810424298 1250 810423048 810423059
    0xa2903010f110405100203070203100506130603120e0406080a0f080f0d05040b06010e090c030714030a150b0301060c03030902130e0d0816140307110d03021c02040b0304020d0201020106 81
    0x1c2d1000412012020080064184103a040201c4500c0c2050b8403400254035101850f0b01007a82d410400320101c1d019035640011420503580c80b030b600d02e110b2600702c07030601c0781949a05040700301004142c0c5400105541004400c81c50503c2d0003140c0c01ca503c050042d0070125200d4031464a01c010000c001c490010041006c02c80720031501e0050200c0c601c540d14002418a041c1c0b420030410540035050b603041c840704035003c40456481000d102d40c0504803103c400e0b01d0742c0701c00205650928a1070b42040b01e0000100030006400c0d00344d1700c244002000c5601040c201c56440b42d0807440341c88207010744400501a5443c11b070109010750440c5521501c050301500581d000400e070242180c281c0b00c0c0180d8150031003010300c07818651045143c0d4001005600c15149000b041b80c020b0100301c2d0510215a01c006c000c17001500880c042c1c1c014824101c4004241d60b00314840d404010020f500140c100c0c0108010441c00c00400e65240c800e4a081d162011070981c03560b21036408002080c070303003000100d04542d2104070100300b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810425548 1250 810424298 810424301
    0x30714011205150a080d1823040b10020c0f090723040302040903020d110c060a110309040c09090608190201050d2921120c01090206030f04030201050a2903010f 70
    0x1c03d5031794050b10006040c50030040c190203d910300d900100480402c140007606107c200c103000140b5038840300d034840700034070007140186c01c200c0c148641c080701c1d0700480302c00f181e0081100e0b40050750449811494206010801c03181d101c0076207120b0006000842000b542c41456505441c070003803161511420b00b80d503540000d0954604a03c1140140c001000b0110320b01e030170061801f2118100d80c007a0000f0f0032201c000c209103000e00c00c00c40c1c003003000c0b007902c403c03105605100711078000d20b0140c400e01500d0f011603406044070000d80b1407400400d2500c1070000c0d0700400407d5203540701203c011008440c160399001118550080782d261003c1c00d690b08403170365540410101402c684d5452640b1085000c0d2808104544461811090390121980940c138103003100300402c00c2c00c120824070110a45504401140b240142005c20002b900020008188039144814014003881244a98000d000680c0c404250000745c0356810750a5030100c0e03480e211507440b0004202c2c54022020090000182c3c9540c0e4003940f030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810426798 1250 810425548 810425569
    0x5060f1306050103200d150c0509040212010312021902010c1506090b10090308030f09120307050310090c120e01020c0615033a140c010b03071401120515 67
    0x4640701d0044980a19140c8807031841a0300a00c00c8a106c04071100603200c504c29402c90b91510824542c3e0343c00d1080342c0e58040c1d1705031a00b4030070241c411500d49265040e04a004002030100361500d130b0780c6542c42e041c030501c0083c1e0f060b24120310300c4040d00800400d50041d01c22200d0880100d8031131358501c15441421025128202c002c2c0004ca1004c1403e101d000c0c10b00100c0f0f900202c40c03808002c022401030002c030301c0722400c80c1e42145855800c0f204590303d2101240c00c08041200201500100005109a25500102842c050a80442e100041503528030b80c50003210002e058400114410b400e848182000560081c02c44800030720015241c4a030070840e480c2440411599110080400300d0200d5641c00c04205a80b0041c12146030000c604903181170031340f840d0740201813007843e0036400250b800e1400c2c0318180001c0c0c05442c601c80c00c1c1d220007031201c1c094064032415448500074426144001000b101c803e44c80549481d040c2c58034440305024001c1c1c0030241ca8020500da040d40b2441201608a071036000c0d40300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810428048 1250 810426798 810426803
    0x20607050313180204031a0903040815060a121e03090933080304230607030c11010e1503040f0b0403080a0e0a12050a09050604080708061305060f1306050103 69
    0x50742401d0501500d0308400d03071090390340c2103203130f1042c481840010610107240243c0f90880c05a071001d84d6508036664134501c100c2d0011030890148201da00c480381c000c41140d41c081c18040b1501d0340f03402d860f01c0d02030a90400c042005055840310707071400d084810031040964403c501a1500091550302e45646101f034071850040100600441e4140981c41748458a0b4120369082940c58105560302e444800c40e90b0303004901480e10b6101c41900b50010042d0b0423151052003030070240c99542c5074006420040c00d500451201528a0f05428595008135881540d102e41712040007006078484e107070300645409040e04014003c0707a0300510a540d00c004100317079007030007880313617100340e070b41400702c0c81c210701a402a241e9141044002d640f112032a00001031084007400c040b29200e181c0680c0b189140c41c01142e500e080c640c425500200c00080210310b2080125001058030b0b50300c1c00303d400030f4840480d07000399400c0c10400a8419000b800108506d070030001000c9030030a4041041c000c1201701d03070716624101c920a9004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810429298 1250 810428048 810428077
    0x406120b12100b0a1413090b0a0506040c0206070207060c0203010e010603080c0f0a05062d10050103060807050a090507020f030307050d0b0f1e04022701090512030906070206070503 79
    0xa15182c801280541192101c0644030440014074012411822030343c024141c902c681e8003610642c42991850b4002020702c1c2c2c10800c3c003407441c103201c10340f10002c100a13241580100c0c20542d0300c2c0b80840c00011141d0240619500500304603203001d20440301d81149000c1240d05540310718074400600005d014801c0603502038041180c0d41c2d06443c8181349815080c8040d080c00b9004000404081000411101e6011455804011416440b04000000c000300d01e910a120541390100380042c0356880c1a20f10240c80e001e0302c0400c802d54546040d50b40e540154402c1d0740d44907282c080d00b881a411945c224a401c501180100d0311802151500d160450300100c0714580028000700d095040900300303015500300248180c41c0c2000e10400c120204681040c41482102d410f5101003814641c0e445d59411186400141c0c2e100740c2116418414441e00c6009001c0210300262148001140740c0c80d118800c5400b090960009520b010442c005010746908461000da902c00d405021060201d40140020540a500703840ca = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810430548 1250 810429298 810429313
    0xa020c01050a140f09070612090f0c050310110712031b05130501110a020405091c0518041b0c0c030209011401080702011a0f060409020a0504150f050406120b12 70
    0x400c030380500042200600044e21024007200d4074004c01d01170705483c124038240002108100015001d41a9070320024900c0d212090550140300541118205403502141a40c0d40b4885648400341079411807d10740c001a601040740d0000142e05050491529005080109110f04088540001440790301010303000300c0c0340001e4408540c05e51080c0100545002d007461542285441d045550750006008002e00031035540c80031410a034000c01c014443c100e120041c003000711100400042060300b02c482c000c8501580c50781a16411300e42400340c2440404040c41e0700e00e5596800c1d400701c60218911409a0b560315034101c0101c056100d48984a018191001c6640c203014140742c001064010000d00080869140c0b040c0d5440900070032030b00c0d505030b0f881241c041e006a601000080c81d00c4c440e0b035100aa0301031000419141140e04040600111303080f100b1000a150422403069400c00800b0540034001002007006100f840d000c0c0c1201100311184150003d95408a0404035028072a101040ca443e035001c0300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810431654 1106 810430548 810430571
    0x110301060b07110f03060705180a05010807140c03070c0311090c0d022802010615020606030a08180a08060901060902090906210d0e01140307170a020c01050a 69
    0x8054400700e0a0247c0302801d01c0d80701305400314100c20070000206891500744070075000ca640603150001075a658130401c44240707802c0100001d210005011034021104100007401c0a240301d02d507201d11003410760501540300c4004591881c41003050400700110324540340e0503100d082c404150056102c241203210289907034002d0210700c01902d4841d0348550407550540045003143c1d420404072480e00c0e4100000c0340c0792041151000c3d0140d10030300c1206c0004103414024411900e00411a0031811411000640d00b80c46551100c46594071010a20142a5003845030000810070074104518100f4040042903460800509040c440c01c80010401122042c000d00046552648025540c6000d240200a0300350402c0c0144280016a20810781500d00d07250001c4070300409007a2240d00038801e943c91041000e0702c00400e81e00c0c41c640c0070700456440356824010140502c1c0c52000c0030030f0610507031 = true := by decide +kernel

theorem cover : BRFrame.Cov 810251798 810431654 := by
  have h0 := BRFrame.cov_init 810251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810251798 ≤ n) (h2 : n < 810431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
