-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:38:24.998614+00:00
-- url     : https://prove2.me/submissions/744f3e22-9f1b-4ed8-b595-06c5103a68f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10971230 ≤ n < 11151086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10972480 1250 10971230 10971281
    0x30204051e0c1603030209030a05100e010f150608090f061f05040903021005100e010f030b0c03011818120e0a0b040e0c070302030c0a0309050a050406120f0201021906 73
    0x80542d500403040103d40c1903800038a070303401e4000e9046128200e4240c8184004080410010040000c550310303010800201c0a402d030f0100f50039034142e0440901d0060828000100e1801501d0603a000c540c1c180c030f001c90250300e80461090a26407003110602051207004140140380c0d41110720460451205840355038141c0c0d0f030b00d06010a942800f180a80580c0184180e60560941c94110a603c40c5080c040019040d4a42141d020100400e810079026451f03408814010003070b10003c40da03004440d45503400c0c1103600d000c020b026009894883c0103203c540b986e030356a00802d0030142d942c5c59950b100f03802e00c204c0f50104000900b03030741902150a100d00404000082d0b003c5004080320161180564410020754a180400100d5841103504404501c02085041c0d6904414808190480d100342d5a1020b41d603c2e040800c01032041d00d4001170301c81c130b00d0160300700b20f40c44c240500382070b0f60f541c40449a5082d16543c00103030305044d120781c80c013003244a110f80c800c001c0101c1688507820101038005c400107e15980c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10973730 1250 10972480 10972501
    0x3070905121005040305040b0c010506040b030f1c05040f06020303090c10020a0201080408040b040b0403030e100813020d0228080105040302030a11121603020606180112030207030204051e 82
    0x341c01c0484442d402c04000c0c2d8440d002541c0007503a0182c000c1c1001860183d4544c8001c81991194a0081e92a59a1000d2009c0b52030305029001c40c00304203c1c02011100800b01070b103030310b9a401c981e440070460200e4109520082c000e8040d100100721801c28901c0d800d41c1c031000a07490340e104941403501c0380955000c1d04007030705c1c0030303c07000c10301c8055a4020420343c00d041c1d006458542c0c014100780c6070818180400104d01800348000d00c041c003849131400e92124918a405401411359103002445102050360600b804c1c0e81c40f400541c1d000e620280a07546d07042c118004030b01c90482440029410082000c516000d42d099411039002d82101510b445249641c1c8a80d014200c3c1c00a440050040e001080142c207940d00c02c001c0c02842154050960300e480b210000001c0340342e4003000507404c0005041340108207054052251076808101514171445c6c804d5940c03035031000c411050007041142c00707100010b0b4090500c200002e0010315800f500402043c100035404104803a10601c86000c0311154400141c0034605 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10974980 1250 10973730 10973749
    0x30720010219030f05090c040b1c0f030206070206040b070806180405030301050a090207150e03041706060907020105060f1207050a140306060a0806040308180307150c0903030c0b060d0803010b03070905 88
    0xb480300141c2031303540002c7e040101901281c0f002680c000003030a11305403100212800242c605100b0b041101500d80c2e84e04e4007034144030006000c0d40954012138100804280b0510b451a48204c0341c1c5044280b07036035000002151409107954180c00c095480c030401041120010045041c0c9000f110310f284119036a00148040c1e20074440d000f04070560940701b0301c4e40d0f5011500403041510100c0256800c4c03580301d58116042c0ba007842070105540c3c1c015401d00c82103090000d07417650060200d20003808a45040d50101d11241020710b1100e000340311540e04000070110900ca140d0280070000c204aa00365540d5400b482c44001e080c01c2070f4440c1c000c16002c581c551031301c1905d0104982c0314030081c21081c0d64607101640d16680051003804108404910f03101c0d00c800030300052411740d2040d07403003c0303a44800550020880710751046140501c0200070302800400d41102c030f24170b0f4042c2e20072406201603850b000031400c40d030708030100142047c0c03010002080003000030000e940f044546580d080402795031b80080007842c3d003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10976230 1250 10974980 10974991
    0xa02010506030c15090f0109080f0102040504050606030f070807140412060b010807080a0207020409020a06080702010507020705030a0b04060608010204030f11060403030903060911091602010b0d0206030720010219030f05 96
    0x7001700a59141800c1482107240e90480504003900010382d00c201041c00c1030000d0002c1d41980c1d500040601c95850300c1d102d02a007102c8203030b908900354688500030702207800c009482101444400310006400314498003140501040072007000d03407a00c0d40c6030307035404004d050355108a03909806c01c00040d2065110b01030640c4116070303540d038052040d201e020b80000250b000f101c0590300947c48140d070201684440c0070f02c0700140180d1b51104d03501d2411740b0300242140d00c0a0150300841d00454010012540d0000b071003291250480d498498549a0385003c5d00113001d10341c0914100c1d40082030010a01c0001340e040985140110703684e0300c0c502545030070400c0340e102d9800001c0c007044918500f480465120fa0005112070300c00c0340358000f24002c1000059036010300701d58020440d800c992605011070b0382030050400c07204042c0ca0704452128641e0029406000007840c180400c02d610005007411848200c00480c0d58100390021940c591011070740c1c0300c0c668600b501440221f81070204100b06000207102c2d40344240c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10977480 1250 10976230 10976269
    0x30305090a02130b03070b031012050f01060e0411040504020f0415030b040c06110601080303012714010503010b0303030103020607031b150504030305070c0f020f030c12030406080702030304030207090b0a0b0a02010506030c 97
    0xf1401c202035000404511200bd8859101c0c2c1d01c0d1900d9810024407400c4058502d404440c01a071409160803200d05603c0071a03940964200b0041c080142c841090083c2d00c100216800316640c10800b051020f54280c030ba1024049100700c00c148000d0042c61a500e2054404582d91040d10043e2605400e554610030711981e402c1c5e900800041080c020341340d6541290108844030104c90600702c181600656122214141c542c401400040003186800d1055101a92041e800b030b41c00e40d89103800062050183c0480038050082d040c00c02d5001c1d00351042a414010351003506055210a4039008000402c0101c1d0700b02c011030300c1c00d4003241c6201d001e1032141c030007194009040540c1320259400d108070446d421311350941620440c10451030995600030880305006104004540f0b442c60708500501e41a03000d4040015900304006000100e6404580c0500b40e40e00908089641021748011070305105495010500340f074004580016841e5041d0040c0d80501c9040b000c85046005060070401012408004007000c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10978730 1250 10977480 10977511
    0x3180c050906040603050f0c040c0f050912030714010f15030b0406110f041716030206030408090d0b090d02061b040e0c070501060609031205030112030305090a02130b03070b03 77
    0x9441c011505982c0641c0180000c2445940d03503a41504d8424034117480405030700200c500d000d090410f882100c0342c140281c40c002c18015482107002c0c00390b104882d100342c0103804d0024100d40d9034104100b1030396080d81c03000300804216003002c40c0b58024040c450603214414148400203055400702c41c10501601d41140c00408aa212030f940c01e0024040f4810820b0b00000602048003101421809030004169181c401964442550f200c81c0c01d000041004418003180000c05002586503001a60b178881c0e4848031130740d600d0301000c001030000d2013020b1000340315084800400524150110b00010b00300700d20f80840b5503580b01c5400c054102c845000501c1d01c0e000060000700f052009042c3c9c920341010140e9002c6252860b2034980310700752031560304910042802c1c3c2104004002800002401114051800c1401e5504006a984401400e004080c041603142c4010480914003802661503942c0d0041070248150172403445200509000c0c58254401d0047d2000000c1d4441c0741002c60384600b00f400c80500c0c0307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10979980 1250 10978730 10978739
    0x10906050a1d090a0b100611010608070302060703020102041203120b010f020d05070309050d0309030311010903021c120510090605120c040c050c0304090510050609100302030a090b0112020103180c 86
    0x81c40000309050503d1080e90012030104081c80c01c598019510802d104106ca410030030050318003942e25044400c0b50380760080c2007109034800328201080e00c1d811a407159030f40381c0d1400e080b07002e409950005100200c0da01c4580081507000f000300c0c5002000030400f801106440001911320180d90208200580c00c98030124801c0c070b125000414015100e420301024564480e0081703107251424220803004a14881402c1c1300b0305806c402400010305991000340985a02660000e40390031003500c25444080090711403c0381c55004034007140c010065841c041009142c00d04d440c4100142620070589040d01d401000300c2c090800f1003807542c0b04403107a8014040510700e04203004c02001030081d11810841c0038448402080b000f0700c000c10041803041c6010a013414540d92501c2540c0c03042c1d00961043c1c0c0100701e200c0d0380f0307261010034041005042c100140c40745d48141c080b001034210088000e010409080000c1051401010040c220740d000782c0e000c01440c0c0640c1d074102100300c4460005058410070510412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10981230 1250 10979980 10980029
    0x30b010f0806030321060a1502120714030d0b0f03010204050105070b060402071a0103020418051011130308040801110301030203060a050405030d060e0711030414040e0a050312010906050a 82
    0x9030400b1014040380c4c07400300c100000104028220405514000201c03052260034a44110f00401500c402680d8039101107052002030754540a4201d203050340362000c14210107100105030014032444410090f00d0b9181014110074009003140504a0710135840c00c0c1047c08a400d0502c00c2d2000d440c0103071155494150300e51a030101c0d441000302015881030302005000005688031300441d50b00c4d100c00c08081c0c05541180b04010a8481000d8801144003a8210400201c0e42c000350500c160802c400e400076201d1700c480b120300c19510556202d032409040c0c8070400030400c240c080042040320460002000f41d03641c0d560319060341c6d00c170a00c03020358140e03c140302080701481541d0046810034801c1045a15200380000b540341a00c543d44e1240038608000300405c0306103078008103122284210000994601400c250402105a40d207483c018011955a04101c0f4141c004003c0030414542040480c0e4407502c0002841030000e200f4040c081460341004000181401d001d02d40030250361311071182c03038000034142c608807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10982480 1250 10981230 10981247
    0x415050702030102130303050717030c0a030203040302121306020f010c020304031421090906010305040309060e18040b10080a050303040201080c120103030203030105030f0f0d0509120106090b040606030b010f 91
    0x740d0b41950300b04902c8154460310301400c4021442900c500d51500d8850030b0040e8026404030b44e5441d60b0b0010001c000c08138444000322003152805060042e03e90305c45081c12807503d0094040480c0020000520440400840d681102250003070341c2218102100d036001d45003a5110742001c00b0259005010500008150301c03d81010482c0c49001c03a001190040d408909403141e000103114895030000d00c280b1641058940c0a9000e48207080600c5941420b980c0144110b1007807084030100071180a06401666580404030807101d520702c04100d030f038181800c0291000800b0b403450102c0032554600000c8401020410083c1e482d0070401450641c2d4990300191901180100051690710b020004000c603c9654002113000e98043d60080d030f165814901030501d0305414148070869079018907800e45120f280007402158001c05881c3c6142c5034500440800c0141c03d0f07840c8590000d5003080404642120f41d03520504440ca0212000e20040d1394803c0c081c0d0480c1c68809201d80040e0704c090090092900900d02e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10983730 1250 10982480 10982483
    0xb0a0c050f0a030c0813150b04090501050f06120613030509010c0501021309051503030301090207030e0607030c050712111e0a0303030207150b03030403030810091803030e0304150507 80
    0x1440d01541c80a04406a80000c00760004607549080d00c40d111070348048242d60000005040d00e4101000c4d8442240c0800a0b00f810036046840703d886e4039003902c407900041f940c203503c90000d01c4207080c00301030303010303100001c8400c28041c0d03081e240300303e540c5e040c00602a07009040002000c0155007290718100e485034030500d6218180900c0c8242d10001070700c2403000348961056060f8141c8003d08069940782942c00140685a07184251041c100030342d07034040101c90444600350300050780c40c040d0f464103a41098403144216402180400c0b20402d150b00010300540d5144a5402c0c1c4240a0f102d05032909618201c590280640d03101d0101d008241c10500d101d5052144801301c00104042d03100006117a13284240c10850000303402007080d0042204441e40c01c4280f107034042046c0301d040c0d90400403a40d40d00492201404111061000c101325036000503c01000c0c0414282c10b1091850108901e00d504c20001001c40010f4508685c1d500c0351000030042d076055410b008080051200301310421030b00b0360041e040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10984980 1250 10983730 10983737
    0x90109020a08010203040b010b04050618030106030605010e0a0c0201020a05040302010e0307030203010c050c06060a06020a02060304060e120702031005070e10030e0105131203050106020604080f13030516050a030b0a0c 95
    0x5460056603540d0150001000310310000f581d03071702d03040c901451842c2041e44240903070003050000340002e6642c58190b83c4203440c0d084120010004010009000d0328180e40082d040503d040d0000c14080b10905000d0300c1212880400d101c0518191b20803800c030321940440c0000030300c013440203100540c4076440b08880030760020101d032000f03500e9800007030071035081d00141c801044000685440c00f02e810700c5400d522030400c0714001482440d0150103500d810000c0c000030700c1220004001020010300e580010307601d6201900302d401d0b00c0451f006003007841e840240141c1c42489810310122006a007800759611686080c1d845041c40741000381441080f000a003840001d240c3c03a0852152821000d1058500c034807415800304190080606040d03207200c045a00711401c1504001c010303c41582c0009056401039400212242e032900d520500d0707071031400f4403075070194440c07845800001440000110740103802c1c904800c0c3c540d803540c1d502c00c02840b80d02074800101100384000000b0098601548403461140b01c608 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10986230 1250 10984980 10984991
    0x70332030a021e0903121e0306120307060b0a0e04020f0907020109051014010509010b090105031015030605040b0a0513020304080912060a0c03181101030219030203040b07020d05120901 81
    0x4000000c403c5440c90924403030b0300e01184001d1145000c203c20401489400c554902e403100c1600010713180d96041c0b108840042d00000410400c0c0c507005a81000740e412442900c2c1ca60003e4500351024128240e030580c4aa4031940d8003040011701c240049000303070341c001c00224204600d941400908800200500155540d4a60440100e130060001040d05469010b0002d00000c02c071071980100c01040e0415070040c00007a00600001600e00101d8600c040d090801c00d4880d9a1840e801c0e40d6401543c101c0c00c3c0100d102501e145403281c00d80c000c40140c50b821917082c42078030310044c03c0c499501c0d142d03c01d4985c0300340440a46015031172203500450300103000d8000c951034541203201181004d002d1050911072644030b0b4080065800043c41402242e101928061203210410354102000500486015000c080700d0010454160301035812144004080308043c400d10322441ca020b0029041100e0503641070f4000c90004401c1c902c042101c1d80e10901301c4d00c40307500f0810001001036040034002d010b80700541d40c1c0c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10987480 1250 10986230 10986247
    0xd06090302070b0f040e0a1104030f11060a1d03010209060a0e0604080a0b01080c041401060806130c0906030609050105090f040602040b070b0601020f0a05030a050c190305070332030a02 81
    0x100052201010038044c60703036168904046200711034401096501001e103403c0200c20808241f004a40450350007071117486924102d402c090780310700140010258020000107500b400e95412050f40780300c09110003400c0203a200c031982850301383d11681501e554080d10410403101c90074002d06001d60215000f40885040c02c0d00c4150052902500800039508894504010032009030200841c0c80840404d980900100210b1036400c00300400601510080c400c5903000500540c40f41e81c00d412088041840500038985d034103030098410102400380800180c24903d011541e29070f0b42c0610750484602078148801951b0340c00c0c4582c4441070190045034040d0b0200400101c000001e40505400f900a40c0003a03100e040c818006403a040c902e0740c200c02c0c150802043d040c04542c0201c150f4010030b12a0400c0707656000b144e00c51314100210040c5c0052088100301055003030540c480040c0c040c1c24881c3c0c54840001049018604c2e21502d501c4484c4020f500c510b000d071701c00f0313080d440c003442d040b1000c1640542400c00c81d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10988730 1250 10987480 10987499
    0x40b0c0f070603050609070908060a0b041b031b09080303130f0803010e0106090e06031507030f110d11040f030204020d0e0a11040605060a05030a0c090503031b0601090b0d0609030207 80
    0x107540c4000e0000703480b0001c0c4280c0e45010800c00b07400c15800d040030304105240540558450400034030b881c1d212071745e039000d075074160712039810036510300c0801410b010350310f40d040c44045e00034119112941080e011070619010058001c022030f0054440c48001541195668100d028140124141c220348a8002880c000e002036803e102a5001c0c04840307480b600c043d0704208004280481c0f50f0301ca0f0401240e0b8405010b0f050324041074080d003541c04000300c01016560250150f0240420403401c60415161840ca920340c1c4000d07001605040c0007006003405504002840202c00e80106d0089002d68425035404100600d803035402840007042d01500480c03544542d51841d4141103c0c80c0042d900d8003c00909581ca52600e0b103d40005007801312019402e082d010800103140e804020188816666a80346110504c1d005158200c0100790003421030b9695401d9000d0f8088040a800d9030781898843d40c0300105040e00d09004d084403518002d0401000002b6940b114001740014803020360035070144c1407011412409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10989980 1250 10988730 10988743
    0xb07030204090b01090302010e01140f070c09150807151701150207051c0602090301020408030c0a0308010609060503060d1a010902090f0a061704050c06070f050f0d0203040b0c0f 78
    0x1464400503151858070340d1042c10341e00d40c003a400381004840c441c1480140e80000300640006402c0c030b84000cac0f0500f00550003041d4464006510b110f0140070440004002040940c0b40030b407186040306000600c28601c0254400c80d00d40141105604410010700c100d2030343c0001c08114202c80c0c0707800c24805043c800e4170400700c082a00700404410007051070350b0744640c0400142c07008040654221824424040ca1140185500d8000400c1e8503000186d607581e6035003d40668002c5c000c3d42040d259141c0150503010341c2d450114400f01c01082c40400001076482c060304800003120b546845031451942d40008000c200301c0101e40c101e50580880d0f503801035070324613514001c0c081c2c03808100069039100000c0c200290640d4083d03e46101c0c110282c400d10215a0101c0240000c0c3c0810054483e252240c0c54400d0500e440390564a4009401007032820030b00c10114040248940110192403007041c55000d401c0d120041440340502580c0b00308820841034143e10700801001d1120f105803501d01c034079003000320b08208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10991230 1250 10989980 10989991
    0x8150a06090303110601030b0703020906040512010504140c010e040216061b02010f051311010909020f120702010b0f0f01110a12180f0e04020105091201060e0901020c06010e090a0b 79
    0x1c0c8215800c2c0209a04541c0010304c10b8101c0005189941c51070b69401c0010100a0820081503004035440320940c40d800c4c140c40103410020f00c03040d8401d03100c0e01414000c00b4101ca003620080c6003514020001240400d0f40132224406950302e40c05144841e003800003950005800400c041c1080751882c0101c0c01901c1121118140800e601d00042c1003c01e009080d6000ca4882440191804091140c60002a502c01d0f0302e4980c0020b02c40404251000103880c035000a5112070103070380c0001114107480181100502d00744030244400c1c0f09540b5816401c900b22845001615000074254001032083d01c4c12100c0a02450814944540d5020300d0403080e0381003070405c000464900422a1480e0407964101440b50500030314403070740e000094940f241d00034400429124480d50780554101042c196485401140d040302c81c0541410f94034000442e69900820003407007280b44d2018104d005ca48880010f001729180840c0c044001c0c1050f900380304142103c074401500450003441141303a05000103422241491284 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10992480 1250 10991230 10991237
    0xf04050d0302010906051f050909030f040801020406090f050303070204090c0801021204020f0d02010210050705040e040302030903010c02010203070c110307030609051507020a021e040f060f030c09060308040608150a06 95
    0x3244d0f07074604002a84c5001d0405014a1960384080c0d841c2000a010382c011034004a0b80c01c9096190b1101240c118031070310000e4580600c00040105100344150001e008444107544c400e00f9040c0e03140c0c0499041051400f8030b5516800400034140985000d4004000060003058200c030500d0741c0d210107508a0f800201c8025240c0d05a20800c000c4d450300050340c911001e42900c40000b44480d50340003e464880302004111180c2c5c1e5000482e6503244280290f030b01030802c0c8001a0200d04003810040c0d41c9400162110b8825800d003200000002e01c180283c038081d222640f9840d0840d0000e607101c807481c4981c4004181c040c820b5a4002012612b94021400031a02a002401e5a04031100000f0360780f200050100080d540400e04070720060700e41155a0107a42814411502025171480028000c3d150b403014042c240c0382003050100c0c3c25400052040e040b02d210301500344070305668181800980d0260b110103410100d00740010403401e4012a000b03035102c6100006000c4291001c400200c05800319001000007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10993730 1250 10992480 10992491
    0xb090907050406090902100f0507020a0b0306031b0a090b0310050a050105191503090317010305010c0e04060f170a0f060501030c08030c07030210021515040c090608010603020f04050d030201 83
    0x1641001e203d072201400c00d0303000601061070a40c01090f4581e0b5001455030412030304410100c80c00380300303a0a0b1202070354004d102540300c40e9204104c0d03c0c0d580081e1071462007401000d0082d81d0b50020f180464828510103054140102d01d000602d10003030202ea010382da003601038402d00307804004a620405108149a5030001455414032007840101c5c1c40a00102100c484152400c0c0100c0e040380200d140d5003034451a001c10901c003140303402c0b2429080c10584c80141c4540d8030000c002c102041d00212a00e81e1555500c002d400b41303c40401065401c81d02c1900d002200544061002081c0406804031000389002100e180600c80e03130301d0508840300c4580640340c9503a24030050041200076500700000780301160046060050303001d43d141c2c40c1c4a00d071100070f204404500c020360b1a203000380407100ca40000606c5c0ca1180303140080c895403488000c01101d074440c625050a520469006950030003d40303da5559001260382455401c0d4003d40c03000020b100b40c000d050000156a0340e0b01c2d8607018940d4400c0e40007242 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10994980 1250 10993730 10993739
    0x60815040606051203030606031003060507020607020d09030206070204050903040e090a0c0504020a05180102010b12030705071d0a1a0409030e0108010b03090a0803040609050a030c030e0103020f0d0b040b090907 92
    0x80301c0b01d5800c01445039081203034500c4289400010b40c1e811060444e035182e62500d8a10b13a81e2070103038250344010611410300301040205a00030900520030207280d02551a1124041d8003240e010805e404000d500000902510300542001e1b4401c55200004c1c0d003c6030b1516840d4141d1019a800072102d40d20f903980603c4030b103c104040005100d00a110544065003402d00b451409001e5028440324050f440350108003504250b8400d40184013000009815540355030383d207648c626100da0003040181c4052091810010700100301e1110441e07032400c000c3d40c210b41502e61000e1a0302034400075071402c450b040a0354829034035075254400c0d410b2062280e250b0000d2000c03110300141c91207005a0052002c00030900030090840b0003c41d21949040c0d000c03c42503a2640e4900e441c070000c10380004003401d20f00c40d1041e68030800d9041581076040c00d01030f80302c00001d464802b0046040e88920042d2814003142401041c020b501c0c0c40e04580c400150041011130321740c080c1c82c049480c40d00d00301c802d16429400540c0c10071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10996230 1250 10994980 10994993
    0x140307050418140303070c1104060902030c040806010f06050307050d1413030f1119061d03090306010b210601020a050604060c110c0303040308030601090909080304031d0108150406081504 82
    0x40354038483c8000f03181503141181d409401c2e91001d0502524008489200004640e1198802d40c09082819011900c0e410421042d0b102a0054003680580344100da00200da83c074a013141d0501121075603500d403459941c0c1e03104200d607250000c1c0715040362503071141141c25002c01038104107881350000024034207001040d4200182a0f002010b103040a020301204c3c7c1c0380441d0800b00d0113201d0a13100c420a00034210042c40c0c80c400400041c90b001100604d502e00122240d180400282200785c8218101c3e096662110084004c41c4515441441e400007407002d041500700d045980b00e6480340050041d501010440c1e115207050070030455084848940d511400301020390011400c90120b00302c40020b20a107140e040120343d0300c2c401c5000150039007a0200004019030b118410300809811252814440c0d040c240c5410302e010342041d2003c40105001000000440085903050b080c1000c0c16502c451198854031107911c8034580d50b0303091a4120b5203510010640341c100300404079242c941d1000c5000d2a140608141c1c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10997480 1250 10996230 10996253
    0x5070303020a060501060e13020a0905061309061505030415020702060706060303030e072303030c15040501060e041101030b010e0a060905030c030102030f1623030708010b030907140307050418 84
    0x1100340044284647c440c0e0b200e5040c1c0c2441603141d20030046c1c0d07a070b51030320088d101248294081c0354441c0c0000b403825030282025054108864038268103000b40c80c1c8904403044642290f41c0c002d000508284001743c041042980a8100100214801864500d01d0380204499500039941654500c0d00c40e04104109941442100c10001285001c0d0404078202110345002c00c24550381a01d0003025181c86e01c1c0142e5041c4200d5050054007401c4444840d080f8000203a0000101e90548036940391480006850707003544201403161307030321028071121240b440300103500404144503418100300460341d81400f9500d903641c0c9000548447c0e128039080303911304801c00d841d1000f802d228a0080e4014824003861401c0082c12541006007800d001503008004081203c0071262030070311100d0074100c00c03c1d04540244200003140954126941d400700c40c0c1c0ca44240212900c010b496002c40c0341d001601c2040020f034844c5c0081d01b0030a00400b512011a030320000070301071b60b01d400552a0320300c1c1c010300724008028046802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10998730 1250 10997480 10997489
    0x190c0b01030605090d11030904051b0301030f0302010e0c0609040c020c0901270207020d021e040204090218040b09130204060f0b0a08100503060f0403050d0507120b0312070f05070305070303020a060501 88
    0xc401201822006d40c3c5034056420302501494403070011880b24003506510b041c0650a4010302c80d01d96a4038100394a010501890560155181131142d407410400030500c0307c80100003808151402200c001800014130315000c0366811402034640d80c01e125a55000050300900c22418040400b10000201078500c0c06010340e0f81401c1172040245e007006881d081c072802c1050307804403001030b680c03110706004103d10030200c80525806840042c0101e181c18283d4003410001c1003c09001303034044d9509082c00101e4116101c050b92210142c80020107014254400c031200f18400b8102088085d62070101d60000010f40d0440c5041700c0010a4410b0540e51014141d40d005c003522030b107041c215160002203505c0d4480600181c2c800c46000c0001130505010303004591200e051080c0401152402103002404041c90341040240d20703090610400d0140b400155001d40f0007028600145040241c2c1e641c043d100c85c001038201e4550081002c000701058003800820015030094000d061010503c3c5820310448405810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10999980 1250 10998730 10998737
    0x10c020d0f05040e01270504050304091404030c06050a0b04020706050a15120206030606070506070e0a17060a0504050a0c030303050109050a02190c03020309150405030f0f03190c0b01030605090d 85
    0xc1088001c40201c4d0090440b000d42518141a64110f965940080c0410990303000c1141041e00f80010464004024012542168000c01003c0c80c00088078014110a9401038000740d4881305440110300369900507508003100b034100141003540603000c03c00380d0700b1005050f1035546c0d40d2410010340560901030265801d84486904290a06014114a0000031f41c480a03004240c00f1000035180e843c0c4d607049030002a00507007110340da1701c0c0200004101243c001144d034001e00c42c520f00021008504500b550301000b11402928040d030707804030300c07500602e0020002d44d0319201d58081e500100d240e04034514080e42c000d640c04142c0f0341c10324000d0001d484000e0301000200d8810822140d090400020b60101d054451030203440f1b0036541d041c201d00d17500660340050303070102c50141c41800c000030060041003212025425903805246140c01217480d01c0e1713462141405900204201024400e040c030a001e008a01030910008440254449200c2031070240c004641580d910b4050002d900000c00400c1100c004515 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11001230 1250 10999980 10999987
    0x10606020105010b0a0305060d02040e0a050c06030903070b060d0206031009060b090a03060203060103090204050a0f0e0a03020c1023030a0b09010303020709021803010203042a050a0512010b03010c020d0f05 90
    0x103450404d4410400035000300355440011900660302c0003034000040d50000e100b03201400360b050600340c5500c03409004071410700c1a02c140703010342d0821000340d070700c00c0910601650401c6d5440d11951511980246019070004a00f8001e10040e5103c1c80510b006242d40428170b021242811060707001c4030207542207551001800c0c0850f410a070b40328034080341070301e51243e000340c1c40780c55400061700038045001e8025807141c140f100304100d40c241a803144c1c0005d0322004082c8006403800090035141d13181c0010180c010b8200c070a09074a1400d001c440184082468075013511181840f00400035190107142e02d88821800000c28400782d1402c0d401458068102250200000d501d16a000b83d0340383c1c00c0d03100f10120540c0228404415148920310603010200c041d00035541c07464249484d100c0e4600c0b110070480301600605489124a10780c0c0a01c01c1a50800343c00c82074210b00341001c10001c5c48595483c00c0300c80d03484005003036198900703025861442a00c0d07001060801a180d0000e0203201460901c6810050140b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11002480 1250 11001230 11001239
    0x3060106090b0406110c030f100f0501050a050f060f03010f0518070807120905030304050a02041d06070309020f0301090b01060f020309010804080f040308040b070614040206070b07031d060901060602010501 90
    0x2c012141242c010f400d18170311806650100c1410024207903440c1d43d05014945c4400724081c404030740f00c4410403c00d40704210f94030b444615801103800a0103607581007a0f801c8010b0080d42030400c0204141030f40205003a0801d044180d5001c1c45034000d0f04030620300c00100034100294108000e12107183c2d40700c038000c0e00561030b105000914446000380700604000900c200c2c845207442a90144002c180c01030252641c0e0314260920030754820080703204a005500d40810760020800e212030a60013010a10050040d0b9250f0000c110040c001c2c0d58401e80c0c2c0300c2070746020504070340e509100f90101390b03101d24100001c40d0303d004806400c0d44000d1318018199081080070b0131103a0303404103102e948194046100c5448090200100032075020382d0b003006044100c00900400e082e00003002800c101441740b030041c09900c8a4100b10181c4c0705080c0c5000303401000070300c4079000280200c260140e109410b0704d8005000350079081440120f00e0b11500340d966603000030013800301c688400c3c041c2074050400d6000070f10995261 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11003730 1250 11002480 11002499
    0x702010507061508070602030912070609030807020a0e0403030f110301050d08070503041a0705120f04090209130501150e09040506060613090f0209090a0b0901050409020a0806040b060306010609 85
    0x1289001031035195240c1c0f4403000300d441c02c10302d50058a140030840d192107072103ea002c3d40d00c0d031050f240144500602e12114100480009055098800503030b5280359180c91a66000e034145c00046003264080d0501c6804030381010584480340c451400307940c0200718081e58103403040c100c81d5400328040f8000340810040c0126143d910f0040e00a5602410b013940d101e0850818a00394011504021542e5200d158440e580c070201c8030113802428003800643c0d518a103d000381d1140e6200b000340c801540722040c4001c000901c0c00750301a00c11003801a1041981d0001c4068207421203409801070140d640031590000b0009901407055643e500c002d58003101c4905040d120182e40b603200a003050f01c603020000e0250710801e60342d14280000c0420700d009008601e01d40308600080e4100050107400b5290304d5000404002c51400382c80b07150f80c0f02816500169082800388000341285001c141d0b006400518001004078003085064400c0d4000c04440005040030300c1094103004040e0310120401440107000e0040f07581 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11004980 1250 11003730 11003737
    0x1e05070807090311010c050a0b04060501030506010f082107060509010c120b150a11070608070f0503070f030c0504050901030f060605060a14090a080f0703031e0207030206070201021207050c0f040207020105 90
    0x909280c40e281b074440c6815854154000c0008100b101000e080c04104040707070304424142c074070813030645543d6a2076242c11500c021583c86038070b080354001100c800c02948414414103000d40d200444a10349140340c0c403000181c0c1c00650310b0916603956000f5200040e60301038121700c0200c0d180f0100b444958044000981d40102c901c0c2d00103c01d120029400030070501501154480c854801c09940c541551f030800900820801c848480c0440c01d4460b40c0d00c0761038480d804692041c08161a400048850b5940450041040c040d109040c030030200300106030f83c0e445000c81402184110004072403c01c0616080044e24907a034800c03070182c134050240f031981c25000154890509200140c1c0360b1181d091a0008404900a900075000c80c0505029045148000b0901c0070550b80603440354400084858801c0041d51504090030b001a002844140010b24000c0700904603e8014411140c0c202500039034400300380c0c0480300880b480e070b000d01c2c000e1070079003040c40c01d602c8009800c8504509141d5075400180240c807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11006230 1250 11004980 11005013
    0x40c0e09042915091015081b0417010b04020703020a0609150e0d09050a06020304060c05011103090a050c0d110603060102070b030a0903090e04080f0a02011e050708070903 75
    0x342d44828039005184804541d14810b4070b20780b800c1020341445014018080d1040c12038601500c4807400041990200440400468401c031001703c80c0c03190001011a84030300068014031448070b030f60514480c1c601d00c80000d00007905010ad41c03100c01e0000c01940600b16003552181a01850040c0080004240c0200340c4241ca1a04103501042c842c03424a0440e140d2003d80841a01071442c1071003274400e410000403103401e1840e1946581411a803034108014200d14248102001a8800c100c14003280740f041c0d8402031103900c29000031032075180014408100782c10403114040c5d10342c001c0f141d2606124080003165011388003543c2ca040802e525403031740100034000c5d950003805860004080742d6964401c0044000030400720300c2c6241c8900300403280c000500b1340500280c00083e0700400c0030030340a10040c183da005592105460380f4001240407035a2580c1c00522103d0159503072a0103848007038030481143d05501440700320000c0c0354604408c0241820401404100800c0880c1d8810300010b031000c51310000e4503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11007480 1250 11006230 11006243
    0x170705060304030e030601030b04020f2e09031e05060c03010608010302060c15010e01051002120904052502060109060b180609030703060609050708090a050303060904020f030d0e040c0e0904 83
    0x9a50300c1c10213a80300d0024104081d09449540000014010b140100380e029074402c45046043c101c202c420000118000b0f12120402c0c0203460100340c103482c0e44080a001c884850500c0340b92959a0348a007607800b00b030750ba03c828074804031303c0c50003080143c28081c0b540d22440b490329160540d4188900101000014040280190800101480499001c000f0340f1050f44080c6406d08407583c44038501032003440e00713210303040c01801081c0b404204030303002082610aa440d00a045030134114028100406014054101840c001d642070603242c1a215064001c800400240c00402980d40350800c110201d40c616445400d440009000303840b0507500c80106162543d1040380c2d2161502c0d804400682010040c0e800148407602c1d00d81d0000d503c0806030003480c03240d40c0380d8a543c032603580c031103d00307544900301640d0090003600104009485031070261449504140044c0480c40e15207103020109151400ba280904041592040b80c610b60349454050908646101d04e40301701d0fa462a40003081049102030801080e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11008730 1250 11007480 11007487
    0xf04050d050a090b0c0715050414130b03030703020d0206010509091c051606061401090b0f03090703080a030902030106060f0203070b13051c02070b03060a090902040b030304140a17070506 82
    0x1a280303e000346901900070401c0b282d6075080c20706200765a0340d6980c440c040b50340100c013410901050003a4150341c21100c008000504440c028410000e59420350010105503da03620b902c407855407010006000d03c130f4442d800030f00b981d5441c088041d14045050340030a100e0140340703042103043d040100c0c403d1002540106600070904d0701080681720b03030180c2d1044040094642003100c06002c91a04140c04503114400e103140a8001d00d401100c614502c0c0c056020031441c2088810140c2e2040b00c000c50307120406006466910fa120354848641d64009484100029280e40010b030541c038080c071800c001012203040411513028580b6000c0d407280502e1030050048150f0340d00056022101e122400c0c2007650100a40c2c8a280003075400c1d0003810481c010701801071040000119414002d60101c9005170700081c0701000c06460840c0d4403020b01101807080b07801c9501c803000b8203101c0e02c081001c0e0005e002d00c0000c2000b075046040c00c0c441141059070010340c404a0040021a903403802041090031b584080d40c0580d074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11009980 1250 11008730 11008747
    0x403020609030c030d1716020304060c150624020106050108060d050a0203030d1b090803040b09040f0e0d020123060409030203190203030f010501021c120609021305090f04050d05 78
    0x300351481161a07014010b170f403ca000c0c4141e010034802c8041040e011107101346d4403914809045079411001e00c0d0050780c820031040c00b00500540025500320b00c9040d0450040151380140d805a4009512070441004203003860b10540c9030200210421024900c0200083e03481c00000801d416400b030030031400703150328955820a002040c0280004a9005000c40c1e03514909850b840004044c82e10f00c84140d03126079002500300c40d02c107840c090121100a0025030825048c0340d080500b603070040c101c456000d5941c4031503481c48141e40c02071404605c8800c001d84542c20351032201900b55862216040c1c1c0b026903074180501c0c402c1100385a203402c9403082c1e50009098a0074517086c2d11b1132103500035a0540f9680700c1480803150b903000000314450b2a11a42e29a0640d80e0f5070011382e0380320f21071075100d10108540c0007448852841046804222041c803034000c540c107a5101803041c06c980c002d0249064011041000f4001400e142c900550000343c0000000c0062626495403600e581408e003c0e5020014001003058 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11011230 1250 11009980 11009983
    0x7020a1410050103050c010201050907030506060103020d0e100b0a0b120a05060609060c0a02030d0f05030f060a090609020304020306060a0f0608060d1203090c050103110906030c0c07121b0b040302060903 89
    0xc0a041e030705504210035612402c00a507100d5422846500541c203060014004407008150719003140d034080028044e5854910054000c2e400c03907000081d65a903945c0c03e0510141040140750364580605da000036100d40c42000b03111503003006400c90b402400c000c010b164903d40007114038a5000642903000a0310f62581300010f0384611800043c254840780220b59943d4035240810304140d001d10844c111203100e4400041a28035a42540d401000b00340244001194403809505c0c41e580b00c07000a14213400f5586880c0017804803480c64105401c0d0f1540442000114142000000d40010b07040300d10b000202c0c50240b2201d440f010134020340007000f00240c00b2407860b4a0b840d0454085d50380c4004010503141c3c00308801801491006401c0d114080d01319000105075001c1d1241c6000c10b00b0440d01c4501c3d102150040c03019591000d0b00d1401e2a100811810307409060621a0708040c01880c0c070162481512030925280c008400a00708001441011040040f1390030305c0219400c4030b5040d40e41d952206070364800203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11012480 1250 11011230 11011243
    0x7020f040b0a03080d050609010e0c0c150108030403030212131203031404080309061503061303020307080a050a1101021213020103180605061c0203060106081f0e01050a0501030507020a14 82
    0x1541200b0903400200c1001420300190410a800e458100320750381d206800c1000c41c15081c41455080d24041001c9010555400b000304015000201260501020880d500252500c2607105800c03d40001c1414004c065040c0040e0b610200103200c1c0500b003c80306074030101c604415104902622000b1341e1503401300b6009402c0314842c01c0610600c01401d01d054105a03803070b0f6208860b04200380c050341001544185030091003004005024004290030b5462980890f070840b20600c00f6019403200f0b1001100290b0400d0050218541a03520140c0702d468280e000b50015110303d00000b03841e4018081843c0c0e81215042865000c2c0020030340a40307805003400141d008280c0d080c1d002034801641c0c0004014000990469805804143c0d05500440200a01c03504594107001000350f01da004000100225449404d4007600309240d0728900070088090011072544052540c403840076840044010008d900d08008980300500c03080c00d00b4001e620f41080020344810401000034400a007070101c0549448080210 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11013730 1250 11012480 11012501
    0xa0c021207050304031406040b01090f060503030705010911060f030a0b0402041d01080d091208030604110a0201050402010f170609040309080a060515150a0305090a0606180510060507020f04 83
    0x400781d454066007411030301d0b0751180c001a1082d05841c56460941440050308601c1590070000000d00781e400c002c0d1a402820150010050b41520f4600115003940c052006055aa2240d0300002d00085949800c00e01034001514107840780c0c506102601e41441201c089a5004002c0400010046681d000040c000e0250f074201480d401204561007050030000c0150b45d05842e5a18100e80030310100c10b5003200c5901441c000e00d407a044940806400007a04200030b10307003200c802040400c1c1c0303400d000718604541c1c0022980c040181e448406000655810070141c001030442490300c90300580901003901c545103005042580104c0390f080002d014180b2032114240034156481c159080181a802e1440280109a5010202107184442d1603e1031030302040440b4143d041c1e804403410960b00d01301c00c0d030003000010b0003800c040c0a4026103c0c0000c100707108183c090710070507050141c40002120b5550445600910b2080e01c0801902c050116642010070b40d42c0780d0394101d42c3c501c28120303c3c101207000341402d020f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11014980 1250 11013730 11013763
    0x120304060905061f090906020d11040e160f080403170903040e0603010903080619051017060102151501090e010e010303170402130b0303160302010b01020f0c090a0c02 73
    0x610081100641004001c1c9004004550007625000700040b003212000503080160505039030704001200964100d980914000c0c100141042c108510000035030303023140c0000f2040300b07000900740841d4039030743c024940090402c410b0607080b085c442c0c000b03000c0342440103100084c802042d001404052040700c1d040b40b4400c0400c0502500e003400000d455982e00301d8040d6071401811b0000180d001e0605220f201c00c660b80654407446a030315051705000c440d511500d0200c1903e5114078010a558599800d010001c11042e540c2e81c6480000c81924a400c179405881181107402843c0603240e500c000c8402c40d50420f555000584200f64003000680740944580e0152005544503000042d000c4130540e0000d048034081d8450004c20140248400320310041250b000f07500508451124812180307903406032084c040041e007120301d4442030182040c8401201d040460041c1c0d107810600000c0d503414441e40d0702c08400d66008108103a845800592600401000758000ca030340c8100c030341e201380d200700320508180e01c1205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11016230 1250 11014980 11014987
    0xa09050408070611090a0503030c1015210201030b0103020304050706050f0c1c11060403050301120303022115030a0b01030b060d020901030c0905011703180111100f05060409080a0507030212 83
    0x1321403403054000001c11403003410720316000920741c2404400c41d44081c040d80050a00e05820b12038120050022001c41400b20141c0040411038560703a500c032680c85010718072040004041440010156400464030702d0401d401071041c040099400a0300b401601c9070740c02c01c1c0340c443e818402448880c1c016906058403500c07569454003810303955100006407601c09591000d40d44079138007002d280c2d10081a100180010020401084094806004001040e11902d00036142c00d842100400103c2c4044000195002c0d0b00c6044c0f240f142c4124403120741082041d030140001781a40c0d221101205d8051002a0125001c02c000541ca41e8030b1402650709243e0081103600f4a507107a090226800340580036083d80c4515190020070301d1406503181c010740d804030b400150b18106207180c5038440c00111850031410320182c9100b202c940c120600000410503145200000c0d12034504481000b42d030b10190009004900d058144004281028101e82c0e02d0200d504195540d415189000c0707180c0a48192400b02060010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11017480 1250 11016230 11016251
    0x9110a0e0a0522030e06040312050c07050103060b1608040905010608010806100f030206070201120509010b1905060a051e0a080402040506010207050906150c0304150212090a090504080706 82
    0xc40310140108071081040080d5a14034440340880030000d8a1518a020124800f034006849100783c6400034001501090a1550b6566168100c1040304005e5000c1140481c010031022010031007000101024030b800e1204031f10305110690640321f80b1000000c1500d03200055030a1000c072900302d030010418080100841d6944080081c00d05200f07010b002c07568010700c004241c02000380a2442c054692510008480030300d150b00f00907503503101c82c104a0520540986007418270200e031140d075100d403400e100003007103a94100c82080000b14481441e001c141c80040801c0c0000c0d03c401d410b95400021900b40640da403030f0b5800740d9005921854150b081c903c200096841c150320350141e07105000b940300390740502507a15a2001643c58010500666421024401c0001e03404c2c500302c00300d00300f840b017030a0a590cd054480b15170760341982d1241d0418400324045d0803c410065904100701d44c021081c2c440164105603103040002d91007041e030710403800c40c96212401b0030140716595040b80c80065100394100040a001d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11018730 1250 11017480 11017499
    0xa0306030201020d05130e0703090c150e010306030c090b010203130902070b0906040f1104090501050103080304020108161b060219030b03060603011404060c0c1502071709030c0409110a 81
    0x203404220b005000c0c03403900180c4140030310141c407034501c01d065050505905101100c10000300042c05081017603180c180b0803000c100b1340c0c0c00b140050001000d1a5084022641d4060090f611201e0640c0c10146044800c10120711910010800e5030030480000c00e01c51900c00c0100d20f94050080000203440402e540041d402d0b01d103a00408a01d8420801d441540d50390050341c035111802128080c0030903500444a6000541000f00765025400040c80080d0030076040d2949800c545090700200c1c0c60400020500c03040d503070005031681d881134000d220f107518100301e803e00814000d441d803101445c0d40c0442c40603208110b02901030704d803c0c0c540014103074a03c00310f00c50010060700021021500a01030340c8003150060406003d140e01c200d000c4004c400c006d48450740e440c00201504401c4000b0001442030078400149114540100306048400150325890305090030003030f169000c24503840c141410030030b03440390b6180446c1000d4015411600000ca40900f0300b4450b0007044410b502692017001d03c1008642001d070b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11019980 1250 11018730 11018741
    0x100512010605150414150f0408070302030f0f1e031e030613020406020c060726030702060603010501060f08100801021b06060604030804050d050c03060a1b0206070914150a03 76
    0x10440328080d90f4200f25080484a20907800f80510480b42130141080d1030400122240c0144800c4101500e03004510165007419007141d0409407a9400c00d110820a510b404c005c44c10410120034050458041c143c2072465603211800c1c440c400c15000800918880700081c415124840100c803144a2220518031403003a02c1e03402210fa4070300c542c0c0d0003002e003201c1001c1031080d035041e02c0c15a001030030402195003c2041075005404100e9031340d02c0003041040481c2d80e6901d003c0c100b08903180d801d0340f2800c0c428070103800c0c844000e0625020b40c1c1740c1001000200d600411031080300900e82810b20150315903036a02e440d4100160000c0d003096000140d400e80c10300d484540301c40e049983c3e400741c4d559521807208210f054400d0f44009000400d0510060000340b03803c0d2084c100c0340b80b180c0e04031284600f0100200f1704140d400c40304103603556aa220301c1c9510008a15a4500002c44c1d071001d40682d06c3c0c14030015000ca5a507010301c880f45503440c2d24440140c0c03210407401d4039164040f00010384070403016200901070070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11021230 1250 11019980 11019989
    0x105010906210302030a0c020310060303050301030b0109020703020601050105031e010602030408160803090f0102150109050406110c0a08030901090206030108060702010e030c030702060307030902040e0a061a0a09051005120106 99
    0x10001100b41101c241030342402c2c81c216515a01075850059114400c82c1c0030a81c83d24144da160040742c40b904814002e034480d21000710300c00e1b00c0307907501c030740c95418801400f0310f05078445000030f0b0041201c0c20010b60301042d0341e810b580003400c0164403500c511a038030038003203032072814000c0d90f00300c080000c00c00540000140044603071500448200d07949103036030a84040101d204a43c51980184a14283c0d85010010b9200011061048840709454041c00706248542a170001c443e40750b031001800f081c00300c0c60207040c482e51410144a450f1501c2442c4040c1d0700c0550b0100a0080c00d4040081000400c0c00c1d00020080e603001482c0e5078a81d43c4030f00c00980c581005407400000340d031a15502d00a01f140210580f10604404070141d82825134540074400c003075200620b134200b0580c0e5035600700e0059482e840341d069505400802000a07030068508a0111134015020f40c01c0404040c0440702166503190705402034a98600010845232146601c007128003805402299100001c40140d00104e44158050022103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11022480 1250 11021230 11021249
    0x11060a09050c040c14211302040c0806061204020f040603060209030f0a0f061505060403060207020102010b0f0a0302130908070302160b030c030414070f081f020c06070f0c050105010906 81
    0xe05007004010465440040902c041410807408000d200b903c080541805a001e11240901d440d014008406c42d130801c8809003158452a6002401e41c00c0610400f05014402c1c00d00242c107081040c0090490b00440d8100500102100005421520f440e5103480898401410030301203580c0741c4c030b0184041d401440102c0c1c040e1043e800c6d810704144000403a454200c0e0868003088601c0415181d45028042c00040c91030303036040c541c00002d5151541002080118000c010060b2519503610009081d50f9110001902c215001341c0c0440182d034464074580101c96040b5201d103c41c82204841901820b00d01c4406004030001240f0304e02455000700340e0103802c004041201580d203481d0400032a031350105443c0940000002d2002a002032103000f480300a24590078100e0f044140e980e07490b14001852500542c040390400c2e50190425142002c0014415004280030b600f08403c03a400283d440000500300310800407450384450380d03a8003c80110500c03070b4000c0024032056031255100b201402d418410b05c880e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11023730 1250 11022480 11022493
    0x12020d030e0102070c0e0403050c070314010c020d020705011209060501060e1801120b040f02090910060902040503100209150309060411060901020606010e1507110a0f0305030405040c11060a0905 85
    0x580410f2003100c2040d9401a020175801d03040c40403407a4800c02c0100110180002004042c1010130300b0020304e0000d505c00d01c000250940c1102842d403c1d00d202a120b941590701c42000700726981d4001c1070240a681c401e02e02009034003100320116000c0d1440c00c6014007140d10345400802c03c641c2c8000308062000d02501c0703c10420390380040140c80c0240911480c08181e6940c0d80550028442c52802a00640901000c02c01d0100b680c002504050007501e4116081c2d20114201702c14003041c1c0103082c000e240d2500218107281c9000c022035260b241c0d421000707041560000b05507a481d03039005c10b034040c0e1020b40c58107185c60307203003800ca4266036031700699099800e422810340b82d68044c0740100840d841403006038081c003200d44a980054840740c80e4a5502a404041551005526002080039048180c042c400d608020080320044c0050450980c010075141c1c02d881c0c0b018004500004101c40c1100c0003981c0c0050340409001303045440294503100341d401c900640050040403205500845004c600400a9814 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11024980 1250 11023730 11023751
    0x503070501020304080304050904080405030f060f090a020d02061e07060603050624040f0204092a090e0c090105040504020a0507110603010510030506040902030d020f1002040303171312020d03 84
    0xe0f2405580704216143d40104414000f50808a2840360002e10420580d800c294407800000e003000002c50083c00541d008504020a0300e00c1c10070351640040f01d0402920303003092a600800c1c40c03d50031920180c007900002031940c521803100c1360b540d500b03002d041101984400440c90688050400f512068031a4410740d800305101510140b4602e0b4418080b80411000f002e103907007070001615280418020f240c0d800c2c40700050901c028007034140e03821241c1d000a81e800c802ea4400c4040d5a02e941110070802c1103500d000d0102c07030080100c0c507410000341d6903081e03200c040050040b00d09204a422280d00540003040f040c1d00c80fa0418040c0160601c25112212480321705418490300c1e010901c10690302100e0b07042c008140306d010307600c02c80e0000009000400c00c6401d580200e8646078040c1c0401f40160f101c240303910b00d4004140805d0103540781a5a0a41c0b41600e180c030300401115641d00e020042120040200301400c0c100d54000c1c1125501045180c2c0400005601075142c00401c02403101003410b0002429 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11026230 1250 11024980 11024983
    0x70807080a020906040306090609081303050f0304121b05031e100b0f12030909130308090f0a0204050c16030503160e0306070503130501020f040303030b0f01080708070203040b0d020301050307050102 87
    0x1019003c0c050145801c183ca152501c1c4060200148141e44065640d41818040341c05540102030780d400503109620114510b01e04280703014070314001801290020320051142868107611130600700c0d040550132081c40d13101c070416000898241d12080d418400d440443c440721601401c0c2c505800c09140070741d4100300407070f800300096401003544070391300115840300c1c8038480ca001544800d8041c001802c032818020b004000c2900318034180e49240b4408800001101016844844c0940c80b241620181c021004015002944d880fa0100c00174410303522200020308100f070440642d82c0c2d401d410303401c90407070301d241d42405400756009880c0200030340c2031203010750111800b444219114240150040190741d03102c803000c03155900041c0400b40441e500045400100701c0034000380c82c07030a2080264a603218510301e000350441d03c40c8020640504240401915143e070403403c4a5030001e26410708210301e50310800200d05500c03841d0440350707160502141540340c1c00d407a54080c505031007041c1c0407104115241c1006a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11027480 1250 11026230 11026237
    0x1d0105090601060f030b0405040f06050105030a0f060903050c1605040b0a08070b0f0906040e010905010e04080306130b03010204030b010f060c080d0e0102040308030a020a0810080d0c020604030b070807080a02 91
    0x400941d807100004003c0103101d40d0040070300225500d4001500400c6800060a5030310903074080d500068048652000e0140c1885201d0040c81e08a005000030800342d55203814104401c0e0004d09065035418145040c54002c0d001c44a00407008426940041c012720300000d21200d40b8001c01e40224070b8440100035034108040100305462006005080107450802c108281c0d070300418000c11a860184941142e070703110807000d00040c00e04503036030812660510342400d0441c2c03070507032242620300010030500c000314240d44200c94104005560041c04001c2d0b048030080500301080781c40d9019840050000240480c007400b09043e6403102e2801000e1a0742c1c0c2ca07085854545c03442020303040c018100250503243d8516802014083c10a400160900d40d694075440c0c11900200c0782000e420380c0002c4d0000701d10398860b040d603604c0b80300020135850203414001c1e01980d4401ca002003000f440750b44090744040d9030341e58082d500190790081003a4903a28000300c000b0020301080d560f02020540c10804298203540d5070094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11028730 1250 11027480 11027491
    0x60c031d0303070e0f0307050d0b041502130b03040507030b010b04061d0603060108100e0a0f0f290103090506040602070201120504020904111f0207150507050303060d0804181d0105 79
    0x500c0d03c0d0701040020010000c170104809940f5109900c0c0005094650801c0e400f43c0710700a85040b4154a0142440c40c0169100074608682d0351041003030201504032030010700d0603104506141a20381d5244d1408500d400701c181c1014117a5240600001512070300100104182e546035664043e00300b1030304080008d10208025066885101800091700c1544142541a40010745250480440741d491803000e203c00c00540302c0c200328507203c43c00482104001e005445946410010421403888814031141046030380342c2c000a000348203030304800000da21a80011040c1500301c001e03a2068106071611200079403044c48100d000c80c02c0c10038407504244141c8031f254071480e00500240115a0fa6695106400d501021b042d60f1207581c0209400409400c41c6031030135052010340040c00c0c09810700c085030f501244030015140801c50100811800250080162501306c0010764503401962181e01e403c11043c09035070000300b660b81d07181c030707403512842e03d140c0100b020f151150300e003c070f0706102640320142a103004549 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11029980 1250 11028730 11028737
    0x60901050f060f03070507060612050604060b01050d06090b0a1703030115052a06090a051005040302030f030a050103030e09010302030d0c0618050c0406240c0609060c031d030307 78
    0x10480c03410040c400300c822510081c0340b10714204081c4444962500140d079000005480820418200b22041c070860001d080b94140b43d202b40c1d0700756a205d80e950f500040004000a407682ca4403511a40100305843c501d40c400303d0309101290700c0d0f010320740080148024152162030f18210000d00c490f44e141807202c140300150041c525680c20f05e00d40c101192998014401040001c0024210308980355007000d842d51483c201000000180d400c1071890000301510345c020a801481348280040d40c0080c1c1031050050f4860302048956560078140e055000d062841004882d001082056a40d62944601e050340d110380ca03008851840712003480b07c00d11013404000c0d0140e002c0c4500c009807600958406400301d224540205001c400804248168005200103e44541c40b443d03200200385014003601c4c2c094142d00a416038408402401c8205904140000c8014401d440030032809101c429003180940707603044142840200c0415100400500c850030305007450700781c9405d5600829101000700c034001c401c0d075a07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11031230 1250 11029980 11029999
    0x1a030304090e0309041418030a0c02010e1206010e09060702030f090f130c020102070312050402010f050705010906110d0e0a08030703020904061205010903080906010302060a03110d0e0d02070e06 85
    0x16981d9006041c0455007070103d20003803000c01c069a850303028440c3c15501052001c0110f0404a0001d0f0450b00e00455a0101d60002d04c042c20100d64480b0380b51070140d80910344900c8901c00000803807024080040c10015601440d07001168004803424001e00607a400c4c800c540c1c0a50b07603014126124010000f01075551032041044021529143c00c1b03c01040c2c60080001d484040d0502100c41203490343c10401c0050303500421028181600100c9940c6204030a0100307000da80b4103036000078000d040c100b03c4101401408140c460501c4001d44c030056150b42d00c9641045100d04510060505400c041008550241444114241d441c0b0109001241d50f17488800c59003103860f03156055000e50401240039400503990b240004103280641c02c11004503000e0f03c0002500e8405090040008100400c80d00069000c40010001030710f9031400c8030030405851034000317107980d160006030745544944540001060704018400000310000f003480c0c6900d8615400b05e40c00d15990b046031540300001290020361120f02c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11032480 1250 11031230 11031239
    0x30712080702030c0706020d09050d0804030b0702030705030c0109021003020a0806010e1c0602030708130b010501050d1d07050301060807050a18060b04090204050a06090509070c0606080717011a030304 88
    0x14604160042514010307207003450898030386103103170008503804034005a2041e908a010141c219450602a042c01e451102541c0007544600711944a244801490002100f0005040d80c1c400c0c010707103a040e907000007520b65400440041c03a0207001c1d0014180e101d55001c54454940500074802c44840c08915112807070259030300b00041d54100303410703a81e864011403e9060860104602c44007032210b940f10f0000140c580c100303040001c02e001c00051107070f00f0382090015600d000c504142c403a0381c1180c5003440c02e10342d202d04402001000e0482081014814240b4141c0d0050031368003c144402a240250000c200d0306594141c12036840d4810321030f031900181c28681c2808182c241051500b4000c811502c0842d919030b5410303044a041d4032590002d50620340c0405c0500c0300340760034a6480020405854681d2165082000061041901500300800e2201010302c1000b002440d4000000900d258415070350a143d40710001e545c82d0610203a41040c035440c00008000c45c0300c40151041c4007110240066003010f051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11033730 1250 11032480 11032487
    0x2010e010c02060f0a05030a0501090c05040e04030c080a02060403030e19110a080609030d0e01061d1b0315010e0d05030901080405030405040203100914070e040b04020d020a0201060512030712 84
    0x400d80aa80100302080300302c494a144e480100710709529a03a4696680c54250201c0c011540d040c1c1180d950309040c0b42c40070012581c404140d80645140001021490700c942c907040c0d402070007800006190303200c08075440305015000f04005120b18001d4406200f1040410b10f180e40320740005c00ca03401244000e0700c072103012812800318143c2001c0c01825080c0000c0d03c800040b843d001040303c1f104c0955200050200392009140121541c6441d01d400900246040450340100800c51036140c101e824805400180202e00d420821424100a030805541d01d040036444580c3e10a001c0f41c505021450004114610f07081c40e000f255100354010002e0742c10a824000111200035020700309580d035200c14800441c45940701d00c0114043d00d0307840344c0310384803d2900011005132000150240d2100b004203081021060700b103060b011480c1011200081d10008040014000f0300451072840c00941c80803c03130400080e015400701c8255601201c0c1701d65480002d0f07000f00d42d01d1180000043c8444801110000000d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11034980 1250 11033730 11033747
    0x8131707050c040906051605030f070c0809040501090609060f0f0b030618011401081501020c06090103060e01090203180304031703100e0f010311030d021f06030222140402010e01 78
    0xc0350081d10742da201040002401d6a00d00c1400317407a529501c03820b0102c0121201088920240207081039402e5150410b260750505200501032018413000300004820090404119407001030014010403455846801d103100608181c0038019144d4940038004c211001000c003c0d02c1110488141e5503a142e00780600c0f240b5039000134104642000140b940a200013101090850182c000080207085060740b0200040126001500c075843c01280701907000d010741d0340410800a01041524955a12484840100d009240704c0d80310307900b415511800410b406603603030002c0d4080d5041034002c000701d1400b001c6140d128400d6120040880703428005803a0995900809990b01a84c050481c41001e0355441c01c1514000041304e10711f44030200c0c0bd00500c1002180300411414060640091848646109e40070350782d15507900110014002da0380c00c0042c1d140d0550800c1000e944d000e042001c074640b072000c191030010080b6440601040c1802d0350b041d07548c511142071030700c5690140d4440041e0442c017001502c405a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11036230 1250 11034980 11034983
    0x1d0609031b0117070f020c06040806130213020c07050f04020a0c0b0901020d0606020f0601060906020a02090430020c0405040c0504020c1203100303020c0607020105070b10080d05070308131707 84
    0x83d5030303882e809509501c5105a0b204015176140c41070105803501c0f000781083c112a060a2281100780418091600001102640003640030300c84c1ca8400d15900000c1c0007586c0703a800070300c5a03500020b5206035280d4089600b4085072402c3d241601403000b44020801a4000c2c83e5030100007810540561012400100c1050703040034002c0001841c0219456424060310019000080076a0000104210725001000000d00410140c0360102040d030034450000c2d164620782c480a48240c0404000c28240544002003124095401a00c902100d2010320920030a071404440e42015004c0c0e0010715003181400d00030303540709550040e411503560f4204401c00c40203411102c005102407048140c81c0c59a2581c80b40114042c3c1c1000704064403151862900910f802601a00c05015503001d010b90710060b60410140c58103a40c0c0000020034960340c2c0620072541e01c1d51a4403111080c840d003d030290415421800418005020750340b01040340e03a54404c00318102e442c2010080160010410030260085a82c02410000303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11037480 1250 11036230 11036237
    0x30403030b03100c08090a02060d09020103060f12050d0306080303060409050307061d0106050d0f0305071403071505070206060a060503070c0c140f0907050712050405060304031d0609031b01 83
    0x41003000046490040d04080a4016603500c8606540b900d8010b215164440300e0040201f040007043e03804143c0d1805801241d00c4219207454800b011603000e0b42200000d001009010340442c1c5c1c2c0c1e200c1040b4204800784050f00e0700d000b0b0807000030a55100e40161016038002070019482c64840c0006d0100600144c0e44c141da09001c20f01420000030054050300c4640c000311032400d07040a01c01d494040c21a000e6501080c42040644124030004a0100072591841d400d4240561166401d041c480d483d200c01d03010311003135400000380c500c1c1000142081607500c481e8000d8100101c0e076803504e041e6a81c1d070083c3c13039007580301e07101c41d108005880c841c500865000c01c441c60005c0300d4001da941c0355040100150882c441142d08022040035508100a51540a44003292051b6190034000d1020780700b4411800c1c0504034078038031181002064003c00c102c80090401030501952480c0509008012496600c01c40d0442500c828458140745004c4095480e0701e440117011b0100d0031114448007804400120000703041c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11038730 1250 11037480 11037491
    0x302060408031003061a01090f05030c1302040b0708180a061205040309080106030501020c0d020a030903080a02011805060708010806010614030a0608010e0706030c1d1210150e010b0a020c0603040303 87
    0x1172614060140e1040946c01900001d40034140090034524058205039405003003900100419039001651304c45001043c0c075104101d04008510710b0281c852130b04800ba01c803100041b030310200070001008150080392103042c0403081d0619400c0160201c0c95100c1c040000341c4090021610016952249401074401e0800b0f420607955400e04c0c03401d483c0e0035030003070380e00703035400308008141c44005d2100c003032004070701d2024025001840e42c010305202200d002c00342c100280481e224803018001d60100b21007512031245050054000d1078490758486046581800081403a800014043c03000076085050341e2080c0c81e50300f2030040c1001c4104072a08000c00c020801c0f030701e80c900064040700a01c64211007000d041c3c0606810340c20310902030169075100140401300102c800c44103501c000e81c1050f82d038405030101c950b05050b076103000360180b40c40400c81d0901600b41c038000c044140c40c05100ba2840031034040c0e0044913902d80c1e039100344038064021300c00f5440240e04995509065403901d10000c551203442400c00080c4c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11039980 1250 11038730 11038733
    0x306010309120c020a0b0415210207080d0c090302090a02090301090807060507090e040201090510020c0406091a010203031608070203041d07030b040207020102100b0f04020c01020406080705070302060408031003 92
    0xd880c2c0e00c200c182c0012a4a11104100750b0529180e00c1c0d014240b0408114689440c2c4401e198500c6510a040e004000b21000915075040660f0f10750440b200030802d0954550200e41068803250f0b00500141a02c1481c20a001d482c850041d10410102c81d0018804002c03030b40c4200c501b42c042d500007501075a25542c0c5070701100003d01c001028100781c1c0d0007107070001041d00e05041d000d44000350980020008810540030000142ea01c02e52035020f690341540d10780c2056070641070aa2501640d10758040d44503041c10004030f2014241c1d032082c0d043c0081d004d4894000f002e29001640c403440140c542201180c040c41201c403901c0c0c05075102c26001111792048030315081c0d039070402d507540040128216071006000410b2000442d4503000c0c0421a0004031401c516050352a070000c2d580c1c1049110882d00c80d51039079020a101d41d941140c120201340050700c1035642e0f03070000520600035401401104041070510012800e4280b1510a49500c0d0340c2c03540040240e91223540f03078401150070041c241c54021650000200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11041230 1250 11039980 11039993
    0xc0c060301080c0f011707030218090a090c0603090308041101020a02100302040306060e070215071e020703021005120415090f140607022404060209090702060a0608060c0a050306010309 81
    0x500030000b80d4080c000ca28088030410609a82120040e41080314049500c030000c040060040d800450b2800d0060742c5002c941521814425080c0b949540650100c0070054107800c1c40c4c104036212441005150001c94941500b541207841c0c03604c003e8001214040020002075035007507101d40b403030070500490300e10003802c1d400241e418030541c050743e0000e90081800c108221490080724094182d10100980914018a0095131140665807a038411015040403401d414014000d42c0801030010039130403018080d03e48044d5650b441d51200324042c840081c1c41e10443c501c10016a404102c004541caa000d031a184c80d016100c01d41c0300303a0090483d6031144100300058801e0480440e06106540c0c84139210a02542070381030040c000d28100554210f20040c00103458048240c1c42d0348012a5054030050b112403d084000b40994040e8940040c3c3e00f01c1070000d0b00b500081c0b40c038420061a10180581900e03018a5500c1c0c00741501c001103109030a00c40041400c0c061b0001d03617448001890009900202600d501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11042480 1250 11041230 11041237
    0x7060f0906180c080703021513030c090e060604090f0206030403021002180f090c03011e0b0a020c030d0302041202010e040f0f020d0b04060e040b0408070b010b0406030b090f0601050c0c06 82
    0x2910700c0254500604100301c01010f81d0060079120040d01c3e259166030082454070760990810140720034005034014582603031072000d001864100094185081c2c4402ea02401030200444080041c440c2100058080c5403078094603001603440046500c01e21070030383c00d000b000d40028204400303501888201000c01720302d40c1301608400c40d1001610144102c01000e01060000c7d103861103010f1040c09c03042103004540101100e0445007502001c5240f0381d81a0420745001c2d4003608480c0d000e08000600c286903982c00581c403504020300310b0079120780400f0040190300300c0c80365200b80c01141941e0301c00d0308003540c0200f81e5680148000b07000819648200b000c142d080b50350b0007200551040d404110b8410f404c903a4860002151000ea4082215a082c0301c201c0c110f0b40d0004100070008076001b80020100044075041e6400c8030ba02c00c105941958564848103602d0b0008d005540000340703044000a10303498480c0755140550011550100103403100401107070903030300a80c10300d41a4800c0106940d41521840000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11043730 1250 11042480 11042501
    0x605030a0611190e09090102030f0606090a03020411030901050105010513090f0609020a0c05010b180a02030c070c0e060108060a060806010c0303020f0a02031309090302120a09030609050606010f02010e0307060f0906 94
    0x34000003410711420445c0890000d80360b4849680b040c402c22003010007600d609504404121007403501d440000001a0800741c030f5401c001d41150074085084450380a94001e0360080300950001d001c01c1c0c1e2581c0044036180110b10f405d0b4181035294400300403a4070039a21204d00040391890105000f40c43d201182d00381d134003c24140000a8040151070305110084c0300d91182114215202d05490300c1c901c44c1d00d00452400b80004104aa0000116584201e00b008490300b884e4000c2c0104509590790700310600c0c003803046032118081201c1400041301403804282c0d800541d00c968546100d6034880d0f00046401000507401207050540c200240c01d6030380100000307000c8608450f030003190307101c1c142e45000082e4115903104088003810b188902c00000d8011401070710300c11a54508030703200c1d41201c8003100c04c0007443d800642601d1800300c441040c440c1c040781d0144540d80070380741c0b4802c011385200120700304c4200500080c469001480800009400354020210300d8840c03600102e810401a03c80c02e0403200c1d400003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11044980 1250 11043730 11043737
    0x80415060510020f0f0102040f18090212030301031110050a030b010903020406080c040b0a05090105100507021305010608060a030b01060c0c08060f01030302070e0c070602030603010e0a05030d0b040605030a061119 93
    0x20400c1d00450200000d803103880864000b542001d1420b60f0000b14074100b0700a83d2404001c05c03003410ac1c10030160f8020b800541d00100b042c0032101601404a03107991080c042510303050b07846a001c0c0802c1c10106044601c0d040c660340e410703241c4081200201c0c01060341044580c10003500719000005655603000c0c00340a0300702da0002c0c284a16070441000122040c20751041e02401915a08215030350b01c581c03442e811108203540006940407040c02c1184d842c414a100250b111000c032038800e000c241d240c4c0c8414117840d05610346a440d515400b080003050300e01c51000034000000e400051004034402c18681c000284242c60550001e40c80e011014144442201c00100c2205018010410305030704214a0f40100104104080350303050078400c07007020384101100607210300d40010220790240c50941c0842c0644480109130f5a103030801c2e2802c15166480300baa54000c040c1132070b8610b0324a16040c800c07441117480040c02044060095564140640655904a160b485042c40440d0900107000541e0a10804556 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11046230 1250 11044980 11044993
    0x90903030610021908031f0308030402090105040902030706050d0f090f1a01060207051e040c030f050a1404021003020c060106080603060f090a0f0c051804020405010e0708041506051002 81
    0xd0a00c140b03034980700c0c480300855000d804070684010800300300148442c0c000243c41c3c2d980da0b0301d1000c14170000e1403080e0f07614040446a000001e010150f005140903c1c4219507400c1540d86e10340400040d104094130107035064015031400c00c00741e4003c00042c4101441c00320b0204000e081030508104a4090709030583e0081c20000c816820081c21070b80407548090b176008210701650415400035a690000c3c060b403801400c0c106154200c00d2101d402942002c0401070060088840c8454010054942c0f55035981c0c8450071b00003c18011507443c041c07100d40c80900b8041c008242d569800700070150054891a0b000d16078204403160048805001e291b02070309280d00e03101c00e40c1c00c0030f00502d40350400040801c04414038180a21100308404603800c5941a003080c058a011807003400d10342d41c5d140c0217902140c0c1c8242004044c0c4e201d4940104914403030b9000700c4042009030b0361000f424a9524003280d650000031904400280042e5950781c109800300080d1100149580d200e4010406c49422114640301690205 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11047480 1250 11046230 11046241
    0xc060903031603090b0d0b03070501020102030f04060b01020c0904060c02010c0201110a081009021303050f0a0c06051b0106060f03060e0402012f0102030c0304050f070b090607080c0304030f02090901020a050909070e09090303 98
    0xc09ca2000106030a1000b14650b1500014102541c20040e000801c800d480382841180c5038803c021140b15018000e202030b1041c18103160040040c00340201d150003550030217541c6004030b03006120f5100a001400604d5140c980001000c40322001d004112000c09180300a0214900f102c0d0b10203000c50760803044030076809508600344513240180e040034005040c1e0000c400c41e4000386041d0249801c949982c1040c0d038407a6603c01c1c1d1718166a41d102103081540d880c200c400201690300240f030003422001a1410040c02e80c035414201c0a070002141d002e0301003440a2102c0c140e0040341c8034445051700d45104000d001d141050031090036603009640316202040c010041c4814400184040041c000400c4001d000e51850301c0107601c0075009404003a841490041000014401c2803c12220313480000c20540703a90707a48074641100384000c1003d059000d000c00d20b000488013401482116000c801c01d1310346606180400b02004000c0000800e18800c000030200100380b40e8031010b580f14000c0c070b03409000c0c54036854003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11048730 1250 11047480 11047483
    0x1092003070e0603030706021809040b071b080f0705030c0a03020601090614090c09010912050d180602060a02070f1505010e06010c0201200106030b04030203030103050c060903031603090b0d0b03 85
    0x20b500010a41c0c0c000c44144070325598004103d41d9040d078086005070302c41c0300c10f4040c842c5200b1100503c42e0400740520821041152040000d4810405c0d40c50b200140d840c010390001503800b2a0000425480080082d48104c800013400340081c580300320112481e05e11240002420a1006001107000d64824401800b51481501400b006481000c04204141d41000002000711070b000c1e0030b2600190000480100d980d1045042c1406484081d030505081c044c4c601c3d00c11b07030b035003003a803403800010725550303e1542c0180d9103144140890702aa8010412900c84000c400d000f0361200d041100c00300d103202c02081c005051110038450403031320f124000038650301d0001451082e110050501d070400c50302c2e000001c0141c0c0c21405440b038a80005809405403002e0355101d034010616a04043c02c02c2c10480d04010805a0010055040c1e034820740c2076841080c0003009101d424005c1c00712040e455041482134950700c0758039052842d8118040c1c82e290740320070f03070b00d20311803005a201c00c092110261b2074100e90301d483d060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11049980 1250 11048730 11048743
    0x3010608060121050c19020c030d050702310501090902010f020705100503180f030304050c090c0702010f090509100914060f060a0309060510080f16060e010201092003 73
    0xa007820f1004102021144000c46519a0354001802c1640d580114448855500c1130303a2980344c00c0d404c1500118407040c0065a1000e2071316046210b07225080402031013600c580706540d1101d90140202800001b04203481130048980c00c80c0d00922244c2c0d42040c800308003103018a07070092508410000d8801301074000108074180d2640647c00390340c072000b0200040d8444003400d5003050ba603443c149840f0f888450402d8140208209103d442c0c0c0300380000301500d480040015402648110111210501c0d20020b000c0c07032001c1150030303000303000c0d061003e030300554021242100080040c2c078180d080701d500c5a00040f04110f0039260121400b02d0003030203128012480c0b240b912411141e800303910061a0072000a006e030384a52000340d00820002c28143d007418044c1e00710501c040d500c2041803200c6d03e4441020401c0103910311990006100b41c012640220713502207520f5046040405c44051910700f08203040e20b5217241e68840c541103642e40d0f1006130110b003034404070701040d10900111800c89131017070040514080303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11051230 1250 11049980 11049991
    0xc0c030e0d05060703020702010509040207120908010506030601060e03030c0708060108010f02030919020a0801050a02130e0402100e0f030f01060806090d09120305120a0b03060a020f040e04020a08030a030203010608 94
    0x65801d09404081100010001da20000c40d01e009a0b6580d45032004994500400d0445a0850300208443c0c1c2005070710060f1521a42c2e05e5615440741558804505003600c0054440303942582140005000c403e208145807001868054201c80c83c00444030754a910f840e5543d840120309030000c00050000305400e000384131420703000401c103509509000d45940c4d1030310001111220700b19840190750045454103011580108103220007007001d07241c6844510301a51200c40090243d100c0c1150204d103803001d40c002c2500541d00540400600329406000ba0b82620100c409142d000030341c90f40844155808000d00c8102144010001c26081c3c17414206515005003d0201181a00b03c0c0900095081e4231041c0982107d01200d990500141c1c11708082d2168491806180b411040a004000c94500c081e001a50750000c1901195186c3d640c445c1d08408034020380208140c001e20402c400c00240d0440e20400d44c101c0d0000306401001c90f527541810741745501000301d901c0440d80110040100e02c0e0482011540300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11052480 1250 11051230 11051239
    0x403021c05090307050607020a030803010603050403031401030308130206091309060b040501060f0c1104020711090705040b09040509030c0f1006050d0209010b0d060b040f1e1212030b040c0c030e 85
    0x2ea051070010b42c8541c181d01070f0301c1c040c08012900005554a54501000a46d049407800d641d035612008010082d150854042c0c0100c8d0400180c4a6900090300c6000d04a07030300350395040b0341511100002c00d007010401106a90001050180c4111682c0d00c110b01d584d668400f0341e000500101c9403404405440b01005130301e125915080040121a4202c0c200e004011410b1515881204541c500104891a0454003a4001d440030401108100310910250800345040b22800b059039107940b42140d19105602594442c02030903c000c4046007880d400c200c0e0041c08034070549040c450f40011262810202c010320101c2c3ea4445018844864407921800d005060709503141050440190041034416030184100c0015030b20009a0b100010102e0388200c014011a20803550740341d5807030700c1000c4c1d004814002c0d111300c2d040c140e150b42c0000b106099280203c603001a806038803050a5100d0310030000040070010705240d12040041c50740c1e900c504c2540140349850300da0340e850020358100100404918030038203005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11053730 1250 11052480 11052487
    0x7050706050109050c19020109060603030c0b090601060f030c05070b13021017040f0203010b090a060602010b1c0605060d17030403080105040c170603070801020319050705041406030601030204030b0403021c05 91
    0x5d00800b58200da0000783d1a442040382d50300300040032801018605030241005280032804003c143c0c0c8800985030840c000c404c407144035141d0f091070a403140400e02c01c900210300070b003003503400c0640a41c1003080800a82d080060501c1c1240d00d500420741c0d0304895500d16040f072a50701004500c5e0900c0d001a03011502d05d00620800e10301c0601ca1039074000600060f004404058046046513801d410006220701e0281a0706c101e418002e103000090041c6004420265091406540c400e0400c207007400b4040f0154480d400c03648055445460040101400c26508100b1100c1000003145031082c0c100b005907000b030300043d039a14290a0081200e030040c0c100503c26410680544070103030303024070680281800c20321100802d40352100040d14045059000d082d42d54004020082c0c090040541c00c130418801c2481030043da0382e0079108807035600c0395006240c0e244a405000d801a070921201031075011006040040c6048c1c0c81e5100d03440e82c0b0074100c9040300103070f00c03001034503455031074107117054a10300b281d801c02c50704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11054980 1250 11053730 11053741
    0x501060e070507060f0608010c0f0306080109050303010e040606050307030305040305010f020a2f100b0901050105070c061404030f0809040c091203030504061103040f0308010b0315091902030705070605010905 91
    0x10383c454540041d10301078031400e110100d01c9260b84a0401001d650303000b0400e00715003a0000c1d1121160942c6035000c83c0c40c0490001e041030040c001c16003402d43c09400303185140e00340011024641405402070b1b40740d5968a82c0411140c90030461180034500a0b01c41d1034445246181490035184010842c0d8081401031218803865500a410041e42c4141040c0104c15010210108e9009441d0703c0c1e030301079183c4101448420b000081d0780c0b0110f000a400d6407003ea4070380c0ca4200558042c440d10f40000c0c01a4948801000040d1058070040c0507440d21448e0645020394907100c0080308c5003600c00580300b00c0400039214100e85024441c80404598609100d01d03607614004280302203881042c0c0c003506040e2030b480040c04003c140d620808c1c1c00248420b4031500c905040c2400607078102c0342d92080700400c3c4d80c0750001c41e1048410b01568421010398410314040310741c0e075051210200d00079021070ba40685440404e40000901d002440c45000a075413040d45401c00380c20b010042e1401a0300408902d40740c40c1c103116 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11056230 1250 11054980 11054987
    0x50c09060a030207170d0609060e0606070f0f2112050601050d02130f030c060207061815020a02030708030c10060e0606090a091107110913030e010c0c0906030501060e07 74
    0x6001d80800e09005803582000c0c10001c04035046031404031440000003076003200c10b40c200e03071112003501e66007082002110b1702ca0025650700003081e552144c0c482c0b0207010aa0000c0c440c400840140c1d4420711174a07480342d0300740da1090032034400b00307249400c11001713030788003e50042d8805006141030600c0d002c01c0c0075904050001030940c5c410106400100c40d00096a00039181903106943c00034103002140f0300016503242445503a0701c241d80100801405146d00004106100f00300b80c00040000780f0200d05494680380c0c1c5031007500300070310142080d03004071111040566803d000c420006c14000e000b840ea10101c041d1418104050006112050f030710302013090000741d00421b4165445a03081e02c0707641d502d40c1d50300c0014141b5059680101007890401c00d4003810901002c000d000e03228811042500c1901110303003040000b480448501008081e90fa5840c0082407049840e40201c1d241030400b004000d101d40c0300c3ea0088500fa403c007400c965203400d030800030007c5c248601e0004210043e41c500050405c404004e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11057480 1250 11056230 11056237
    0xa0c06050307050909010f0303260105040504020d0203010f0c0905030708120306010203090a0602010209040b0105040308030402090402040b1309020f0102120406080703060e130308090105060105041208210a050c0906 94
    0x104100071000400007801101103030641c01c0e000f00718060719a5218a43c8000b0f41d80c9010483c0050912aa1038514010840c2a41d0103107801094a0000744c1c00e1030709000003044001c2c41a85d0040c071755084080981c500b84140420720207a4100800c96803640d204c007400100762a40024081d40c040001000b8608010804500c0302d889002080e6894980c0d000407071540c0915030380c06600000c04070002804940540c000c0104c40c006a03024045400348000568850149200c003804c440341c01c00000300103181038648185d00038401000010740b003070428040703a040800f50b507210b0a09941c1d0103e0100750f140c03030022050740803000d00c010541707520031003c0c40d29a400385210700c80c01d100b50320011070300300340c0240c00050192108540401c400e10303061410f0400103a02070b03020340104110340301044001c1d0040c0a42c0b0712070030041e10b405150500c1c1c0f41c2a040707407800d00031050b00d80300c03410700c03090701403503105448615040ba1107003c0010034204107100f18112403002c1d000840322035080040700b04030f455600a8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11058730 1250 11057480 11057489
    0x140702010513030c0b07030206070503060a03020405070c080c030408010509010b0604060f11120901030e1222080a050105180109020109050d05010921020c030f030405150c0102040603020702010e030a0c 88
    0x22610368050b00442c00030071075030381c00080807040050404a002d039145005400000d02aa00310f602c40c3d1242c000554040c40f098441c00c3d0000031920702440503003429000190030000764500300c0408281502ca642c041d030420f420545068100060420040768240a8560411825070080103080350550008180d072055101749410710581c00500f42001d40208406410403600106580388948081c03018007240d40b1040ba600d020915280315080419000940102c25400b501c401900e004040c040d45654164500d01c01603c1e84046400411102030030300500d455107115100115241c1170408105031101c011401111050385020b20140250ba8021822400c84906940074002080181002c034094000741714040c052010b0b000ea24103e64801ca00c6a1030840741a5007661070358a4076900b0541ca45803240308101e041c2d07101f0302c400e100703d02e05002e090b6a0b00e00c4010741d00c0d181902034690942aa001a40310b2004251b01013510001e558002900420b100d43c202d01410342c2d2a0141e031000c0524685004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11059980 1250 11058730 11058737
    0x5061c030c08070305040f0b13061101020408120409050708090307080702011b030e03061f050f0402070203060a061d070203120907050a03080405150307080a0c03060b0304060b1014070201 82
    0x2405020305010786140c2500c25001501d46940b409642800b9002d41e00c6032044002031011b140002400b00301040c15501041140c0300702104c030710301d4140202c41d4845401454107095600300000203000d0003c120350300984407820101516203240009910807580000e2504041c801c0c0d002c00c0005861303004c421585629800000c2c551100143c0c0012100c1b010611241110601c1030443d2600b416007040044441240032000c03140c050791025620b070120f5803811100a9040d0803048284007510309903070100309015001c1c10050400c881500080e141c0703d0196184803000e0798441050040045000345000c0c0007005020351540da04007101e00a503684a00502c5650001c048000f0031100700e0113018040c000c040c0102006100761f200d0500e8905980240305840c401c04d80740140f003010340c4221040c0c03441441681c0b41c400d11991855070400190211040400c1019079803800852640080360140d40140c0c050b02000442c5c1a80000f032040f2880c550b41c189090010801d40e000b1104a01800c6407000b640c2880c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11061230 1250 11059980 11060029
    0x603070603050702010b120c0a15020a020915090711010b0d0c03080306041104060509030606031603030f0908100606030b010c05120702030a06020d051609050609060307020f07030507050a0503010506 87
    0x80f82240103050451415a001000c4a04220a40c0f400101b01e100300d03030110340740c0c40321a03581c07403400d1001030303e0b08400c00158004144007005480e202880e41e5108003010003000350762107001d000415401007240d0100100b6580d0306008040042403007488070b6002e080e2410b83c4111100d4441c444d004c81b40e0712000700340000000c00039045031982c0d00512802100082d032951615220038001c0c0c6590004000c080c0a48240d0001458a250006944c0303c0d202c05030002ca0b40e90380c15078404a0721500f1b80d4181501b0b210712104000b40844041046031903284ca09070b40003034030600340a801420f541510721300b2810000703008108008540c003c240c8014038400c4075003490382d80c1280e1003c0f03400c0c44040ea00c05048240b0204889801d000301d03400881c411040841044991002c440f400ea075100c18500815402510034003440c20030b410228025a017004141c0122901c880740640410702d000525001107039079401000e030401071800c207a01c0400c05440c04400138402483c000d00070034401c503045105603003c1c08845 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11062480 1250 11061230 11061241
    0x8070b07020a060f0219140a0c02011106072114060f010905060f04051816030207020a030b04030c02090c040e0a0f090203030d05010509010603050c0a03090302120a03060f06030203060307060305 85
    0x81103902d8a240d48540180300072081c45031001c0007504002030070b154200d010949001610310034a929808141014a40c40c1401480c9400302c4800520510407070501c00c010102420b008410455580f0601c85942e400c0b64020700c98082030a4062400d28070406a0f0406421a07501329040500542c0044259811800780e0303400001240e010101c2c1d481190041000140c0d02d5a0968003c020015510103a07085404010340080d000556182221109000140b450810030003c0c440e4000304441400145240c0b01c150300c039102e0540c0440240e500320045070f2030380d41c0310003181400408541c4c8403060f041040d0500b49401820341c80c012006000b9150260754507010045003090b50b0140d14525009801c40351228800382d45680206801c4c060940f1070702d080c0c000002c01510900500d072044045090003400e00403103020540280401200480543c05000180c0750305810031400390179055550717a00442c81783e14026440d0340d5504190001d004141c0104100100c64030000343d80b208840c0340b85800102a0f50b003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11063730 1250 11062480 11062483
    0x1140711030304090212010807060215010306020a05040f0602030903060601031b050d11040b0c012a0509030705100e0108010503010b061e0c03030406060303121a0d03050c0a0b010e09060408070b0702 87
    0xf0340e00000348003840441d5620713140c4204804a4140d0301070a0880742d2442e01c0d010203030703640e20034041c0e81800210b06000500000780960098040100f0500b8428103240d1950082000b001854105400581c800700d00e000702441d04005103038101c1c00a00307003048840030403150030300400417850440082c0400002d481c5c81d075064950003540481140c050140d1202c0e212441900caa5003c030008560395070800c200101c02000020705205031811101204070408a0301c072040d50f80c0e820240142c0d9042c060641b0009841d00d486803520380c2d4650a6545c0e1585200280014194002c181c0007940243c5c034000d05000c2d10f8036020201e0703010301ea199505201a09520b540d5407128070407181000941c0c000031060004100c1c50f40c0000d000d5a200e5101d107100c1c1c007400011002120441c5401e072a42c07400d09138140f1480d06041c2e0280800902a2820314034003c07c55000610b0400207482c00c0300e02000388401040300d00d030b141076182c3e08506000086c00d05801c0c2070301c0ea60000d0003140005803900c0c0060000c0303040d4600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11064980 1250 11063730 11063737
    0x207021302040303030e060f01060915030f06031104110c0c040509252409050103020901030603050a150506030a080703032c06010303030b030c01050d0203060d020d080309010605011407110303 84
    0x15400c1d540ca64503803600501602050111304400d2044902207903604010201b03a50580340d00f5520744c03407061324182040801c0f8202030b0701d003000c3c5540c41001c168100040d010303c20242d80928401840c01101e0307010300c41141c07a1f00d41d440c001900140001009030b50042491664400d04650120b05500c406030340364100300c448800d8038101e00e40781c202d04400d0808425500b080302c80e000c03245160440100071801c0b004d41c4140c0018001891a40f0034002903020364045c4c04400310606d000500c09480c0d564580c50140c0c00a81940c4081420b211400030321402c2c0555a88510700b540033300340c82020b6503190217143c02040702c02000e041e107034140000c480804002041c01f4061040c8036440a106140503030361145420f002c1980000e0500300100740904000070342c0b4031010381c103a4600d468038458a480c2c45c000c0d0006400f0a610a05851444002d80c1d0303410501d00000c2d0255081d16a0307420000191803c489690388106d0522070070014283d62010341078259200c1c281c000c904002d180101100283c01d510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11066230 1250 11064980 11065009
    0x90c090913050d0c030e0d0302100f02190201020903030406050c0a020402041502060114030a260309030a03060801090b0c0307020c130606020c030303010e010611030702100c050c01140d020702 84
    0x184800d04002004008441c8041c0d424042d82c15034021081c802d90031030b07844000100140100d801c07424441c8050403c03002840640c4d0207841629000280d5900322001e45200303271126000640c002c40c0c00300c0809860507041c9050f1100380002c519045580001c41e032240510b104100501c140807030078039110b18082c880020800e600610856607207440f060684150381007103998000610445c1c1c000b250110710101e042075014401002061020341360b58070720b408403060b000c0554445184080d101110265070024500504102c1e014680f141440000181110450ba00281c02d40e0305006188000c1124030b04c8041d009500300b028070b1765a55800400764079200c0c0440c5000d40096492641c0c0314070b8441d0b0b6024400b0703100b0304c0c2c4c240c4020a040f802050743d00e02081c0211080308904074010407000c4c6c018100b20b1900200c03001030f00e04200c1c030ac0d000555880c040780300880222384407240450412906212034a10070f5803d08000180e80401d243c440481e00490005600302c6500156450540d600d03e004d90303050703a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11067480 1250 11066230 11066239
    0x40c0b030a09061542020313120210020d0504031e02030a0c0807050607080d020901140301060201060e010b13060503100902030a02090307080a0f020405040812090d020c030c0a05090c09 81
    0x760340c0c45101c2000c100305441803455601d41c2071003000601d50300851031816130000807043c001715001d000071014501d08004441056100800065800d50220000c00c0e000f0410b01403891580e44442c01404100c60b8014031240864206941134091207030040241c40a40b60800300325000000625038460400c0c2d00d1001c041d6261040c42d8007201081401510941666107000c01c0c2c0d40115500d1081c01600e003d210801051040203000b11041c1c1e90f03080e409401403000501d008081403402001c440d0990f4020381142c0d0050351200000d204100c0a54100e5004028081019103000d0008141600020081c0501d200300880080070a841c101144020340181c000308104543d1381c240761012030b0003540100d400718080d00444800050407440444d03018042a0044c0201d00041d08903403c000060400400458800d24244000e048080403480301c04c4c0300b505244028055040704910103403403c00c0d9801a64840e0f8090300618001d03441c0d03d0181c50032031710107a4000f0080c0d102c00700500c1c214012103a60a070130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11068730 1250 11067480 11067491
    0xc0305120a050402100e010509060d0204030206070f03200309010305040c0b0c010204031217040f06110f0a030b03070501050417010b06070b071403010308090120060106020a050f06040c0b030a0906 86
    0x11004603030300c0036000c3c0307200b1146041c450602041c180c07503d00c0d002800d46d020400038044800c0a081c0080209502141c2160041c03506071207034005085c03a0070956082e1400f0120340740d250100b54000094203142041c88240d035022802e030b00405656403150190700c41c101030311080801d08001c0e900008401901150211544690b800c0c03a005000707410900c81500c0e0352a0442c00d611400d401007445071240ca0050710303590480c0ea6140c541c0c00044074440d034215407a030f581e0245510140110000385c654010300e11566550703928035842c01401e40340040d4115209410003901001302e6a00001140c049031560300707503034040c1c8080618060051100d41c4040b50032090000301074080041080c092031280c0c24030340f03e41c1901024003800080d0750000340030052071420200110081580902071984103140c06061410b180d4030401d24182c100072080c2d02c004050b82c07040301c0d00420803a0901a94022300072240003800186025100c069540100e403103a4912800000041074400300c0c00e0b04400f02c2c02c1c2d0000300a004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11069980 1250 11068730 11068741
    0x50601081f0212010b071401020403030c0203011508060a0b04110f13060905010207091a15030a0e010203040b07030c020a0605070e01090512060601080a09020901030c0501020c06030106020d0c030512 87
    0x11581c261401c03181c0c0010601050001111481c0700369000b80100603650f041980c20140c0748041d80c0c2c4055402d8910b109506940d800740c402c01d00051000c1d5110380e0b41c22200e0000c901c140742c00d450403010107a902c43d0b0625001e22103403000140c000d6009241001c00705001c4041780114008100840b644462128001920340301d83e8609401407031030789910510201c032103540780400c80799024507000e0180140c002e1070b410005040369401407000c070048501e180e040c43c040180041c404a00250305110f81c444d0100401c1804019842a010300c03204c1c1c0c6000358914030302a90b801508000c010f1414080c1580c0f142c00c5060207108010700d0320003130f5020600b0099401d04d02c0018207058810300e10300e40025604032002c03526061842e404203c815012004007ca500d40800640b54960010845107600f80c1ea0324115000d0b0b074131440740a00031402440c8012980341044002400d040f400d400d840c0c0514020801000507640c00140d5880e05030581c03030101c00340381e01c0d4601181c13680300781200840a401e02c1c0c0b06102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11071230 1250 11069980 11069983
    0xa051302090a05070f0807020a260711030705030d0909020a020304080303070314130f0b0a0b04020a050301030b100b18010e09040614010f0f0b09041803080a0506091909030c05060108 80
    0x50155516880d010f0341c0038101d40b022503440204461f090010b0b0800e4450a00103469050480103403006208034500300c8040019400803604862010355543c03a10070740d00764081c02d0a100d482e0140c042503025186c00d845c102c402500000c036501c540e52403264000f42440c0420301c01c1c0161006018141d090ba40d4a003007486005025001c18400c4d2440c144000c404524005501084514200d510030038003802c0c58055104d9044241c0010440d03030215490b4034004440766900d1000782805100380d102d042d06ca50444c10000c4001400804238120b52081c01d00502407810a4420b4982c3c450b1103412032007581c091000101e89440b101075845070400c800c0c1e0240310400c05650010014680040104001aa03a602e03c0c00030981482c490740725425040e800c10321410003100024a200003020b003005c9041070142113400c44015056802b40c000034203000511007016504e0283d260004802c0300c400555050001001949900303108003140d03a05d070350b15071000825004d6210005803a800200b618070541e90b40c028903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11072480 1250 11071230 11071241
    0x1050f190c050d03050106120b010c080a0306030c0b03060105040302060c01090c0902040302040b190504091e03020c011404030312020313050a0302100b03012003090307150f0f0905060a051302090a 86
    0x44509005851440c0803c034860f21865049642c0e5541e2080342220600302c1100034424091000d04100c2e071444506e02040414005140c40c804035500064105d00c3e40c2007040034140302e6000894020070070010b004440c0e901c00c050386d003500e40484006684280082190b401801ea145000741010270000001503040b80a5010b00b00700c83c005d941c180702a18402d0204940040b8100c000d0400741e0458805002da82000ea104621042c403401f0039003c03040709141680395240500e8400c50040c0c0c801c04d10b02c1c00c04d59202a0300d60001c00302251150805086580160400c0da0b00300c00c1e40c18850380440018070440c41c00052902183d08002901c8092109082c02500c2c1c0114070805020075040c50a81c000d275060500c1514401001402c8603081c0c64052007185844e80d0001e42100414802800b12502041e40c0b1100c291421101150000b89409004c4018095900080a10744032500c0d000c14080828004114039a001d016221300084554600010710700c00c02860801a401403440000c00640060702d0380007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11073730 1250 11072480 11072483
    0x50a020a060f0903060513050f03180102030307020303160309020d03090e0c070203060c07020103020c0708060f07030c0e040c050409060609090e0105010f061103190806090a050c040501050f190c 85
    0x1030041e11000e003078a82d6006281000005500500c041002c11202e40c011174004540d06214a02e41066403290303450200e8202411056030000210340300e00b800d072248080d44041e004c0c0040c6082d403528010180d26408001d20180c8070480315406008410700c20782c00f41049545c0100051488120350a00a01a5295000d04141c412410020503000b1400600b607518440e03000340200815518001442c10b41d0300542c0003241032580a1200300850001401041c015006403001450701d403034401ca03280c40035070006d0142d0052500d400c0c030b040c41c0960320100400c1000701c16603000c04d0080d50408112864800c5901000c00305181440100328294048820812503190110a00c400f0703011703c840a089074000e00c5050f1284082c4001084054010240f00b115507140380180d81c1415158034000350180c1d040030b2940001581601001080d00d043c0f06600e0b00b00d600420104114509280710b51000c0c840c5000d40d506101010400001d0245c48104440c0c0c1e6440310158480c44290b411b2001d01803100e0900c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11074980 1250 11073730 11073739
    0x50105010503120703180f030b0921030703180b0a020903010501090c021f06081501030b09010e070501112404020a120305030105040504050a0212030a170105030a020120060103050a02 80
    0x2090b20700064040e400e010702510340c0d4034000e2a642c0a80e0600d541078050340c01d1210401c03001403d20810341d18940154020108100d0b00c0c601400380d181030030042143c291080d1007010304001000b15640560741d00107007034140020343c2600b0202415520b148000001e084a94000401c070040f03249401a141c0c01c08140c009100c903980300d03a50341040d205603071880c100680c407a0b0302c2501c4280c070505c2240e510100b9901300092250301c1f086124201011072103c03100d2191800010030403c9800450254401844002000b0000d40700c400305440781c64600c02c42e8104060507100d90514441801203c00650824407440030400c210404e00780c08242c120b80980c400d05c800c0d2000a0101c60480206c0e5159a140c2c2d01c480c6581e00340401c00c0020680600140e940784603441d600401a100d4100c0040c1164111000790389801003d04000c1030b41e85401e80d0361890208034001008191000145c0e2600c4690900344044080e580b84108148130a81d003a0302c4005110722400007003804008580c54113420f000380c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11076230 1250 11074980 11074991
    0x5090a120f0e030c18070c08130302010f05091003020a021504060905060105010807090501050304031101050f060405011203090b030703020903070608010906170a02010e01020f01020a050c01050a0506010503070c0c0302060c0a0501 100
    0xc10151513040b0708440c1c40d000342c3c0e041c011a28001c102d0310816809445400c3c071b106461100d440304003507608840800c00d045001c84c4400c3c01550f800102c8580c5004083c0382507860b241500300420410203031100c650f400c0c10707008220512064000c2c40721402c80400f507884003a0901e440e0070a90050101c0c0c0206030b400380550f030f001080552149035254414a0030740c903840300c03072031401d001128a40d000500036002c01075003980d202040d110a00880d40180e242c13040d4450f4031b0410804000490700180d0198081d20700d40e400d120000f90304026010103c44188291507100c1d6500081503002c0c0c07044011042d4103000d1104041046600101014180d41800c0d2003041000d4072810080803c110a2101c00420750020003800015031003103450456904040c0705540e00c41110080080c20780c0c00040700003010840200351030030380d03c109120f4545e001003401801e210318200100080d11038403010306440b080107042d080540c14003468801d0303440295800f400c0c4555949809403541d40300d55401408480380d50810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11077480 1250 11076230 11076257
    0x3020f0c03040e01060c0308040f03090b030703140a020405130504020a0b040b1803010b0108060607060f0c0c0519080901110106080a060b090603120d020a02010b1306030b0f010f030605090a120f 85
    0x26046d240000d545512204103c0e12035854074040309aa4071421400c1150003000030460200240c003450040c0081c0d10301280074544a0010316001d00000c10303041002e031050008100030307034800c40010620708100c0400901074807280081131a80700320f500080c4c21fa180004000465010250040620482016800415030050400c150070303030f00700440d1580060508800300d0201c1ca000801003a4962045900151a142d4411104140d548421141d000f09851044032402d10005003c030031003c100d10700013030880c542d081c0c0d50000e01d401140c41e00c0341007111074512801c2e0310109500c0000681030420490740112894500900503051b00d0461600a12403900800c0e0700b418005405c22211006401c01824141085001402500950501c104541d02e0304c246c2890b58503603042c026010361a03000082031450540c01e1200e61842c000e01a0706500b80d4860040040f015009422000c5c0c80c1d000b03030b000c0b907240c517003652842ca13114007a5000f078030002d1030380c1105e956980c001c0f000c02650030880c1c4920170503151b01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11078730 1250 11077480 11077487
    0xa050c030408090622180203010308030a05070203070501060f0513020703020c010503130c0b0705010c090f03060f09060213050906010e03030904150b030c0c01110403020f040c03020f0c03040e0106 86
    0x6850105104005001090000c0c5540c0c0103041072041c0544030381c0c189514007448042c0c000c0ca5101403900c00000c100b050102010010040030b00616101003580303035524560341c00009100080c10440c0503030769000420300c041e03c2071040f40c0e8196000b10090040c9070316280c09000048492003450b100310320351100310400340740b14001c0e07507813098040d006446220060001592141c0c002011442c800c803c107205800020710703002c00c0c00301400c800e84035507484400501c2c059084505480c519000d00500e02c0c0100300686511001c80143c9a00403c00b05500c0c40b251034100140040d250024402c40c000710714511414460024941200c504540c6d8580e107495503001503400e1600500f005030580c004103c20700c55030516410400420507000030b07002d9850754070034503070310660025074019640340030000305a03990820074000d2540c0c40314690745607464140342d0703800507200000c10b01005005940350008100241e009905a61880d0b1203640015039600b40c071140d158403680f10b8001d1a43d503051480000c10700c60711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11079980 1250 11078730 11078741
    0x10e0c01140a0c0303061e03050607080103170904060f1202150405010512060607050703120e0102010b0108010e100503060109020702120105010f0e22030512060904020a090c0e0604030305040602060a 87
    0x7100d00a07180c80007469084989101c260016000c1c5a01c40f44005a641c102e00f0142c802c11413100408001c4c2400c500d0b0682c00c085001d040071040210200c014000700b8010000003019a12456501e039071041c2d81e0300420041d04055101c86101d117081040015110202d0203400c0f6454404c03100d1118140c01104011a140214090580028004d000c00803628800b22030450b041400200030314285001542c0d201e02d850b089420407500400b0018100003602d8100d040742003400024002400400c10700c10000b00116014411250300070809070200f1500840a840400030308070140c00d4803a00d6845000c5200130b988100c82c124029607038a034462034140e030306126040c1680c0d1786a2400005618080542e08034420240940404051048200e503500c14160801000c081c8252036160b12504040da400c0d0700204024100fa020f644400c04000c0140c0e60542e240c3d064868030038001601140c505000c0355030503900000c190f04114001004030a064111000d481256034941c00c80c0c40d6a07403948084011f41c3c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11081230 1250 11079980 11080007
    0x604060803090f010309080406020309130908030402010e0d060c180902040b07021504090212010512010c021002030912040e01140a0b0a05030c07061404030f0c0c090902030c03070602010e0c01 84
    0x8000b8080345445183c4124040740e005814900400c07541600c2d140c0301c000d680b0070340c818005030340002001070550901c2548010905000c050400c41901d00b5292516140300c0140000d04008064040307940c2da5813400301d45070501303421a004000c0c007034001d13201424820406156200b0012181c0703000810b44058000c65007036800540310a401c0c00c4403035007031040c0d1001300200c86064038070602011403031a10340c1c03014000d10b008400300c039407155141c00148000600c681714022056410400c00780645500001c09600b000c10709103005959035a580302150400e0341058042d40e680c040000c3c0041c01a10228440d416204211111100b0707119000401005190794811151040c1e001e008140d035060180000c0c640c0140441c404507e080031980e80c0008480c5054140625100444180030616030f114428419408103420420722204194480ca180c4403030a11401d18031903110f0004a0454034103220343d440968014003103840160721014007a002e0101d0f500b0711180c51044154601c0a9845089081241c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11082480 1250 11081230 11081233
    0xa0605040e030703090e1b0c01150b0702100c02030304080d020105040506010801050f07050f13090e0d03020412080c0709050405031206150304060c030e120a120b0a05060a02012301050906040608 85
    0x91500c445144c04031302c000c100c0064480c81ca600c042148201d1001000d4048c110000003a605200001401403000d054102001c0140c09201c03050060b203d5030314220888425040903006d2803554070000385188103940040f081406007401400c2c107250150860f9000d039100e4002e841250303882c2d503981404c88008488429800c0b07142c4006c01c1445000d80000c0008141000c2c2251501c1d80c803134052410100c0030307402040034554402c00102c41d0bc00c21b001984e00383c84903142c05e41c0742501c2c018140341d103102c01850203004031000007406000c030501000388100a180d00c1c00e09000038505403c0080d142d4100c1501d9140d5038080e030001a082d8035000c40021035010200c4412821615151140001054980c20039028940d4581d00c0e4440b0f800100144155884101001c1e42e40786140c400040c11009100742145103a810049c4d10b012130350321402194141c407800d07184c0d5512040d4610049001d001e65804564031490600190100c3c00300c071000e4581661400d9a80c250a506c4041c1030208131441d038031034000c60707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11083730 1250 11082480 11082497
    0x604080a03020409050c07050f0601050102030415050c010c030618020306130504020d0b040c060207050a12141e0a0b0c0a120c0203040503030409050a0e0f0a0308041403030a0605040e030703 83
    0x2a200005003448403154500103051940700d003c1e81048070004d03600340103504004981c203c20414100841020078141038081d0605514110010b0368074040d501920881140398000984c10602c10300940d080181c80600a00c007984201c8000750051030766018050308a10000610500d101e442e008590080d00c1c05010b05c01d85500b0110403000808001d04120f078003c00d00c01184020480142c0c000d80100d0040300d038400710500c1d100000e807500c403080d0700150141602010030021480c2082040d4203075500300501074102281d81b0001414040c04a5108185884216052484a01c00159100e0a62140c0501d841396140e4980003856800b610303040d18009070b08a140c442441c074141c0c01000c1c1e4480240100c0b81850349440000c0d0460300150040d4000e80d0381c03101000b0100c840d0b80145401c00300c00c030002d4900c15955000043c0c44c0c2842007800b030113110321900402c0c00c205803c18480400c18141307003901c1d00c0313040000c001000340c9030307a11409126508080341424801d6021085403592541a01d4400c513 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11084980 1250 11083730 11083733
    0x1030803190605040e010e1e030405060d060b071103010c090b1c06080d030e0c0109060203040308030c16050303090d0809030d0504080906161202030a1202070c080102180915030604 79
    0x1503103007000e07050015103444920000b42911640034030840880010004030b005501880755030b25284c141c018641d06081c09a00c400d00301e26010046400350307075081e108145d4072001524000d01510007903205100c80c00d400143d240c140700b110b0b48091490b00048009005021008408840f403140600524201400401068000885608460511060820300800c41543e11b4030303013501300000c0c0c3c0c118001081c4c440c074515136025000c1c80030014090007400e0082200741020b030000e59034001d60000610301c1c500080070650304018241642c0e080725015001c0c8520004d24508140c40fa00b00351051f0b01d072032103001f485108580c084c281040c170a41d4000004d5040c500744008003c041e00024200f6150000c04212401880c1c444600034032100550000b009841021440c00100740d07403002034020110741090101b50318507607000c0001018500c81d5400540c85241500b030000d40e00380c0c540e1000c032141d031001950482040c0b1540c801c04c5180350480745100d03541d0343d00381d00c040e960070202c00c180e034180c108200040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11086230 1250 11084980 11085001
    0x9110a051c051305010608030304121b02030a031d0409081602040b120705090106021f0b01050d0507020c040f0b030d0311070b0103051e0102090307051003090b01090b010e0901030803 80
    0x1080d026010804095200341a020008490090b40c8840c00060005012400d04c9024018880140188002586189016101d411003180c81e00900020410007640c3d480c49003c01c1d242d000e130402d8008040d0350f407050b40b0b0b1801502130100360314414468154182d82d05154a000e120710142c140d007100010303145c0581041030920294034008201c4e405682c0324805402c0391070f460603103101404500c1c000c1596500f00000c1003055001648140304551000041441c082c1c0c0c4001c000c009a00c1800c000302c5d1390700306400141e43d01e00442e4440319142e03181200b00860b44d0b90000d04d1111448058904002d603042d03d00807031054607114040079400d94000c007e028003180c03081c0d00c00c3d09560300c0035402a0410035140e580c031103000020303881a0f40035800351041e034914030002c00f030011450b05403c00031450030a070000842d807034407213501c01e15101d0340d200001c41060320700a82105030346a6216080030030030b6844454010080090420243c0003451020144030942820240f41c3d050340c1e0802d000c40c1c11907844406a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11087480 1250 11086230 11086237
    0x1302040e010e10020a1704031d011e03050a11040608010e090a140601050108010906030f0f02010201020c0304170601060807080c03060105040506160b0a020f0a0e06040f0e0106020709110a05 83
    0x38041d641c0c4070303000c80b1101c5007400705118030031500d50051303543c4290207002040000742600e09071070304d900c9505100003e90040b40302201c032281b440002c0326420b1010010384031002140c00443d0714010421007024415495800030740705000c450801c016400d103501c114519070203140079840100711040c006100e0b02201d815004e03030104009046690030f840b2070341d44000b40a481604020b46900520041c8115038002000c203002d000c860208206042c503503210580101038051015241c0b480303014507013055920070f40403142402446400c0b039554036a0380d42d00d0316a250040c0400501406068000307d415403003919030724014115669000c00e980c68a0051808541c80609620305101c400c10002400e9207a0001400340c582248003090300c40720442c01e16506d01a0300070015482a481000f0712a156012030b41a101c201481d880c2095480e05076402252551080e41c2103605d08054a000000b50b5007400d01b03100d4142ca001e94291030a1542d10404201981e8160750140c520384018880114070798400e0019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11088730 1250 11087480 11087501
    0x90702011a010e2103070b01050102061b0903010605122a01020c011103070f03030c0320030106050d0e01050a02091203040501020a0f0f120915080f060402031003080a020a03030605010305130204 85
    0x3c84c045024582035401410040340041d5007241c00c00300e440c030700f8490818003180c0140300a0000d00710310305c0e00303164441d86101250503146505002040b1031107640c5003580b00e4805440050010042400b59151481c1e42c1c40d10340c45164a00307040b412120101043c05004508010f20680051112050600c010b54505001c1030b1860302a00c4140000300214031903070320340b055460003034800240d1aa4854002000e13035060028600079801002950280b0588035011641180d1452a12030785801c018054440900f0011001841544c00c1005100d65101e00d64000c0900c0c000485060400098110361151240036500c50140580c102d240d8460205014502c0b401a035403040311528a107240550b2910f010440a9450400141911206000360712505254400b04a030a0402c01e400b8541507240300000b50008000354000c1e50080701198002c0b4029035400c0245a001c686180c4072800c000009660310304003c001d400081c10304200141950103885081d0240c060541141034840c850340a100150024100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11089980 1250 11088730 11088739
    0x90a050f0111030304061407050c0a060b040b03031c0501050d050a0201030c0c020904030305010608060d0c0b0a1808030904140c0702010309030207080d050702040c0e060d0b0d06020d0b090702011a010e 88
    0x4082c1040c03000b03501c9035100d0303040010707201c50f0b007809110540c10040000301030040402010002801c0010904e00c200da2007400440ca03902c0190100c7c003d06540c108003034040c8404550703840d60401e02101c150208440c07a104000c1e5a998004020001c22400c101620320b801038007120380594800d400c2451b00801c2d5040c11040b000e02580441d4403150100c3e030603000a5174510040c0030250b881040c590300030340110390303014001e40903844281c256544d42c414412411000a406840c01380141020712450307116031366618100e582c03510380c0760301d0b60301015a2a01c500d00c0e10510164204035456100d014041001015040c40802d070b0041d4005c0201c6e500c10780c10b505c20000c0009010f0001c0110030148141e5603907180d211119481440306507038185070034101744132880645a44540300c080a42c1e08000c40400c004c41d000d02c0d40c80c089800d101c41c000b03010300180e00002d0140c02000b0281c00031303000c0070026244072042d82e480360003c0f42207a112481220041d10158110200c0350b208810b501c0d0801d10080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11091230 1250 11089980 11089997
    0x11202070606051503040201020f030309030d0b030709050108030406080a0212041506050909030403030e100c02100504350a0203061504060504060305010c0f02010e06070807020c0d03020c040b030102090a050f01 92
    0x40000c00400e0710030740c0780c04c030301c10300004010465905120181d60701e003c00e0011811800d0040c0c5040d1280140c224101c1003503501c24514040d581c04108540041c020b00d201041107503191048551240d2203801010041144040891541500c0d40708980c1c07030100e401240c1d800c544940c0e48003803011100000d6103110b148c0b10100403d90307540d43d02340c0c1e9004055480080d42e03514558580501400b8a09201c68810403410082d2852541c2106142038025412106c104074410402c8055880303000f6500074003101d81e4100441c4044440d00c2c00600180c00084c081d204001c2001000c1c40d030b4440c0c10001c000e41503000640841e42c0321050281d51010030000500c00b0840b151250081002c6540c070760300aaa00d030391507071461060250005441c04400075a4802400329030605048140d807200003508002c2003141a03000207240314800e000c00c0180c60001040c82581c10003909000355200c013410030fa248190b180c000e000350b817850140708035025802c01400b010961450101009260401c3c0070b5100c0c107210348074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11092480 1250 11091230 11091239
    0x4030305090d1a06040c030207080304060e0a0506040b0f060306070e09151201020301091506090506090109090c080901060b09150c0f0604030c060f0b030604060504030306080a150c0201060302011202070606 90
    0x9100d180003003c0101907828441c07034942c0802c4180c808a03201c1d0018180704101b040007050004c000c42e54013580050340403690610700d096041c030303040802c44040c3c4180144030034481005448202a4050044144410b69980720102016100c02066a2503030200320500401e41d0035003410100d456000441c00450311100c80d0714001700e200c031001400b03100d10a0354000b006010180c080d10440000c00d03911610283d282d400e184000d07000b03d1003801201d206007008618452240c1c4242c00c80c00103041520707411320840c0190345001c0c0140f20141c42c031110550a02d840460b100d0321000a682020b2001845609014101c0800400ca03602415010035030340140828820b5500d03080050178042d0b8802c3d0b848150110140c00d01da408c403200356034003030030441c100810388004e0750300002e1240d00150450f40001e126159450305800500143c0d200c1e1000780514818030040c46007400d10100111000348003403001c4600098101d080711800e010007030102c3d4102e99882e9208071154080c208041c814140000d500d9100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11093730 1250 11092480 11092493
    0x80405030405031e1002070507060e040207020a0603050601140306030c15120705030a0c0206010302090601032a0c0506090c090403050a0e0a180e06100506070302030409050a09050607050405030304030305090d 91
    0x390220146281c1900d502c1800c00340c03041110070f005c4074900000b14144070403962410b0701c40c052442010100301c00741c0b0303000f101da03540d9074100e800c9144d0050811002a41d40ca81c080d020b468102c0340140410200c0701d2088020311a01c0440c0c0c4034880060103040445003000400810000c001c1244003100700a020150040916511540c0642e8868440729160f2a0290059069403c40c0608030700310340140c001003005880b1a50340e540c1261090038049684d01d41100c001217071a02e0b40c8000e0843d010702000c9603c8040d008001c1c00390450140c0e090f05c040e075603480310b569500d80654401715044840303080050042403050018001a40c1240b900e01c001070403220000e000102c464020304c64841c03100701c0f2800400344610604130429411000b8000b50b01d00500701140c6241079124843c0188000900542010f20a00490340a032000345020002c50600c2061040140460801150b0724800c017004181d0345801036082c0e404644d4010011894242103940445854111203821900201c0100c03814000904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11094980 1250 11093730 11093743
    0x53703020c1207030b13030e03060106080612060c0a051b010509060609090619020a0201092f0d150903110607020a0302070603090f020409020319050309010801050405060105070308040503040503 85
    0x258000c007031a20003441040303070944404401c4003050380000810000200c1034151a64403c14440d581c0c0300902032401d0a84292120b140940d81c9400792000104145030002039041c010441175400c0030040e1001010715544103010b45400f94410f406015903103005204100610002146c801144041c0074031240603400e55005032144072180c0c10140402102c1c0c1000040c0d2688004988000c01d440c1c144180c40070350380100c82d02c01d81103507031f000580c1100c801c0c005d40104c20a1035007c2d50101d015030031048114002c4082c203d515555441c0407029030b206181040c40741242c03907041400e024144040c007034040010401c8400032001c1c0100c105140c0c0c0c0541081c0251417064142c1c2e00a0b20840b074442c5002400d01000d03030006001e152030500208085141f02e20300d04252035041d900003c2100c03850000900d002000c151006c03280100842e000100503000c4098850b2103400c1c2c030744c0030090362203008110036200304480d11070000e4814010b40e00402e1041c00e1036901700d0301450569113082c0d181e0300480d00b00340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11096230 1250 11094980 11094983
    0x40f020a060c0b0708040b06090a1d03030406060503070f060e1302070302060906010e0106020d0503100b0307120605090105090c07020109081c14090a030b190603030804020f0d0537 79
    0x148008070310401e0181d01c03009264091810705d030420072071402c1da0b0343e6003110310094580d41c042c00e0b1020000b44507581680c818141d00f50348044560040000001031550395100f01c40848656061100001e4035081c001200802d8800307550002c1d15190400500321045a40e0f000e805500c00e9404242882d40001c034802442c1460003940a0300c3c603071420000e200d02e0300340b041c0d005054102c0d120004100140c0d0204249001e16100d20f800c075038035100d6540d4820751202e1900140c041c030b64000148800160005d40401a20703802c10414407040c0d69030320800010380400d1103080d40141003800010500006c2c00020800c441c4141442c03444180c5a002080c5024640d001042d00c2c0f066801c042103400b6005541f66181d19043c400491400c0c01100110315040c807180f100400d81d903d1440461031160900c60002c1000c03e07000010801150b49080c014072a0030140e805038000e40e010f0085681900703143e54210500307034110000303016218030b0403400c2c80d000c018041880e640c1c62411200c005010f103101990900e05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11097480 1250 11096230 11096237
    0x80a1b030f15050a061409090f060a09050c0d020d0905070902030a0e011a04020703021c05040306060b07030c02060901030b09010906050405090303040c050907050702040207050f060901060b0702040203040f020a06 93
    0x200480c036a800c0441d281005100c074a440000c2c4100804da035203541c900140d82c21441c01002d000140a0310069602035921a503a000030b088080050012030184964410481254480b90107555203018204984050340c2c6869140c0d0100040c0c0480c100c2034004009100340310f8000946c0004c00c1d16402d08141558004100300d42e000401c1c403814026074028549490380d8480208142108004c1c02041c011103c80b400c2e010b69004034079003003458028805412485c7d85c80007501c40c902e01c0040024041d41c45400f08442c030f50300d049004070f00195050140d4050560688484007403028507020480740d9081524560304046d103d80c000119a06c0d000ca01c5402000c5042010030300e5070800c1c0810007039590090070a0710961007482004003280b480c00e8480c0c11078005941003007064890b580101c3c1c03070344910b450180d04140000b0f08401000f4001520008108101082da003980e25800c0d030711801c0c1e40051180f04d800040c06c1c400749001d413609034029a0818410348020020500030f5010807110300c42a070020021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11098730 1250 11097480 11097491
    0x20c101707022a030c09150d050105060102070905040201021e010605030f030c010e0d05030c03040f02090f0406110406090603021602030d0807083102040b03010e1b0303040305070501080a1b03 84
    0x5914007400205501283c0f200d031000620107000102c0e0361002ca400842e8400c40c0011b000c50051351802e880200c4c0741c040540109403091150038100d003e040140e4032580180b040410000301160984250341c050b95050380541000001240144a01c14010b10ba694255698103000911650300300a850170340c00580d00990340303881d03021241c05e08454005400c040c181d040401c1c3c0d03607001948141100da03c4100d481d5542d8807074465003000c88150301c007048025080f88140090041c2408001903c0b84a20b01c0b6641c240000000f451241002d0702583c030500000ca08051000e02c89540a80c0140143d80c03002c56100302d5190094000910304200002500c011a00003001c3c00034040d4803003c00d982c030550000c110b01c003101e14220044044c0009000c1c4020040414460800315a500e8000c020340703d80060003030022075061072596444400f03210021000c521084002c12907810003005542c1182d802c500a008078910b41001035501e544020441d07040c480e950b2200004c025000c819140010106540014a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11099980 1250 11098730 11098753
    0x3010606020703051002030903030402010c1401050f04061b02030a0e0312040b1c020702031b010210090606080d0206040b040201030504170706150504021606020a0e09010e060103110a020c10170702 86
    0x145105c42c840c1204042c010802c00000410001c00c5070740190342031038419445062810f0600030300240c801b09200c10750a01052160b0500c0c04211640114044c820030490241200d20340008401580ba04402581040c0300e0b024506002d140040b00541026042e211740500601c2c0d03a083c00c0c2d120b40c2296400c00c0c1d012500d45400d00759038105548481d8041c00841c07034813011f6000250ba85404420070310a400907a141034885034400e2245c1032401030136050034010400f4615004028040a002d861024414030707040081d15440060030500484c1c04c141c1004041d240c0b9001140035040042080c9d4245200350500e41071958020018540907000f03500014110306040c0c080b91900b946130380036900c41c50041c059031050050b0070b03004203502a40400016528003c09038203980d1a00f81040f40c03230380010864000030f500c2c0403080c1014032503032007660100050920400304a0950040507491401070b801001001c1c1c5030f0030420321a050b00442800c200484a40308122034180700811560b03800140c202064450 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 11101230 1250 11099980 11099983
    0xe060f0f07090b040905040606050303030a0b0316050d0602030903040509100501140a020d23070b0405010b010302040f1a0904020c0c03060708190906020c0601060216120b01030602090406050301060602070305 91
    0x903000621403030000b101610301000c2c401c460207540103c0d00c00c669984041717410854140d01c00b10044c60080c3c1a2074803441c141200100034641308048601074001c440b2069040a10722442400f13555004001d6103602c3c0e52900c9500080d00001c142c10440d01c1708010216990341d40c00316181c071440030745861240c2ca90508000500e01c1c2060308007907014000034040056895000310301d0a1a201d594501a001907142d00b0b15001031401c059118a29a070001a02000b40603410070150b110714002c0000303100c00803410004400f01d210310710406000c120007044c1809800200160b6200104000c0c00b031505014121001900300d038018408410300d90b22119400600381010b2000c1c031340c44085c83c01c10214905c0c21455040c410402d15407905041503803441d41c2d80420045905940b0081000f030b003110260b42c2c442001a43c1c0380c130b5030440d00c55080e2800030000ac403400ca40d07160301d0b04247d0001d0070000d1646075a4505000e5008103003804d0b07200d62200d0010800740c40900c2840000d000c2c5a00410406140d428082e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 11102480 1250 11101230 11101261
    0x1e0b040b01150804120503041b080109110a0803040b0a05040306051602010f151a0c03030108030307140412030302070f0506040c0501031508071401050708030f01031104020306030a03120e060f 84
    0x6018450f0304010800410680441c4a210580d1410600d0742c83d0307201c3c50700c0d01c189a0405200148000040c40200341c01d001584103809251152402010064690040200d4600980f058000c1c0b41d100b0070040c0a14103010740504103060240c10107508083d02c0fa030b100825600b0840390a25000c03d02c840b5500e1341e6609025410b41034443c0f00f0304100400d80882c450300d000b18103005800b101044a00c905103564074035011070f80016010002d4035281d50f15460030711745984c13040d10080002440a4909031150080004640131101000301302c0b0500883e640d0180c1c0039402c10711040c1e450407511000c280101f0400c2c0300441c4100d100d0152069014248400074003102e142c1c120300d4031042c032101c106004103040040d03050142c54009200c0008000000c004035058400e01c0c3e07000313000c1c0b030012090144004148440d10b058900c514418150041040300303003c100c0c0421681709074151311001050002c01d010300c4400703a042e6059600456045141000d4a241c101c2c00e4500840e40f00301c0070b041115004038000304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 11103730 1250 11102480 11102519
    0x712090504021309020c0f0f0303010f06090e0a0c05090d03090503101404080f090604150207051008150310020703020604140a020d030e0301181407060e0303071e0b040b01 75
    0x1141030070b240fa18402880039140c02940c1040b540052218050481003020380a81001c0d00101c601c8108100d1040d074480e0004c1c4a45035203100034050214610380038107201400d07240707210150a031a50b1114040710281845446d603c0500c4810025400d00c1d0301c5408920800502a49400d505645040107051400c0505400d1002d4581750120600c0c03081201c4002580107034200c180b150721201042c1d182c491030311410040c48e038003010000c0e0020304078001140d000e44c80706d0140c00743da841c942d07120288a1506042001080001d0402d000074210b6400b000c00710f144002e016085034440700f9040503000483e440b007a010b801681c0241d04010401004030300303103845483c502001c0d04c03034505180d0206a464030f450000500307000c1415241c0400392025032040c1e403080c0412040c001501c40701d040c9001d4540c41c1102d09100360050380b20100358a03004290030200c03050080c0040d450003d607038480610700305c681e105d100320040c042c240031008512807107841401507002c1e0140e0b00695141c0002c4200701400f83c0c1c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 11104980 1250 11103730 11103739
    0x30c070b0106030c02030912071707030302070605030c070209040c0302030f01021209070b04061d060a03050108060601110d0c050106031502280518030c0405070e030c010207080705061e07120905 85
    0x9a4403c0c84d980481500e8501109994000315210310503045405c00455810041c0c02e0100140c01c025058030006408084138081d0702902c0200317498003012162440211519084038604001d44801070030000b81090b0312030700504085815a440750b002038288481070700164404d0b90003103a000000307c3c100c20a26080020312009009480c0b40070000d492601842c8078210a01444941d04010401d120001c6022a04024105039941003541c4000c1e005150070b009405491207850000307807540d4015202e070261000607200505c0c1d1440803102c1100e02a0b111074007101c4030b5484007030003c0080c0742404581c880e290403150241e11103014409030311000d46c07102030840524850020001030f50360860111440c0001e131004880403104204042407a1881c0e07000b00f15002480c080402c41d4495102c6103504442d0400c60541e04403c1c1220f0049035101018091510681c200c200300f0019898500e000b00030f0a800821030400c06d8080850010307a40d00a100103071070201544514854155221a02502904040b02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 11106230 1250 11104980 11104991
    0x1050903100c02070305010e100c0302390106030506040311030a0503010b13030503070606050415030b06090403031d03040501030609020a050702040f0b060f070b0a02030105060a0c1106030c070b010603 88
    0x50010341e0781c854403a06208896610081d03200618400c1c8100b00c0919000802800404421942560340300c2a408402d8200c600c0c056044003124407a0007100d04000001245400402c41c0100b40308280c180c0790300c0500d10030301c40034841d13011503828020a00114000c0001c0c0c00986081c0c1405000392941100074150b40d0400c0207140c00558005090ba41501d0340f03417403401d441d4012600c449111220580000d880751001056101c00c20410307420400503160240d809000741d225081606558072400d00005240101d2a00024401d040109213640e0040c080d242c08220307001031040034107988088030030303034109078000240c240150f580602030075004042040b000c43c6403003580e1174000e1484c004c51900921a80d25201d1203d4525110707040080d91100c000d0415507134146101c00c00090350f0040004a03000401000001c03044000362007500e0496901400c0c030b92400c1c0107282c0450b265081500115002044c0c00300141e1320f03444800c0610703c1072044007046a030714805802c15414541059120404060415 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 11107480 1250 11106230 11106247
    0x60b09060a2106020417120a0903020108060f1c030e0307150c0311120403150e0a03050705070b04060804020f0409030905040f0e01020304031e0f080105060a0309050a0c08010b0105 79
    0x54403510222591407100000c041c002c54100c004200703000102401035400410702203100102100c0ca01000702c9102c0403a41c00c0303814811655440d0040088120200c0e01f100d800700099405040f0640d0320520040005540300b00100c001a00301c00c10000e4020050102000c0c00300f01904105413032110f4904030300070190310345002d001c041e40005044c120820808003400300820103000301c3c07540402401603001e45281c21501480010150450310042c0c4207400d03803500004c2c503500d5912500072049209405403d9148541e103059801c3c1e0310401044070b2510544078000791681c4024050401b401e11917070f42e0022401c05004020b15141000e07182da215500d8800048002600414400101d89050f18007246000c04901e40c4401050480055800c95000000708820140d00410f00412021244062100902140b07421a041ca841d805480d021641c02070060100385404800741000c0350052a000c11002c01c0c5580c4c603800c002207118222450700b551041400050301c203000b51200d005080c60100d040c032410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 11108730 1250 11107480 11107489
    0x11407080405130b0414160801030c15050403060203040605040201030b0603060d030305090304030c0b1b07080a03050702040227030c01050f030c0a27030303050106090501020c040e0313080a060b0906 87
    0x41d44112482452001c4050f055030310290040382c2d407848010700801c02c030f45228007510701c0301d103044a003096940d4026031040c003514018082079050b250082c80c400e04290a1000b8080c105490135040e5080c043d0501001000802c103000541c03080c1d01c46d54010480e81018400034040d1801022410311550041c000c020107900c0c0c10351441000c0c1d41500d07002c074041e196504c20a05522440e040940100740786500441c00350541001081410018070b13001c1d9440c21060040c40d25900300b4003454a0b076411840e13a10740880c2c851070190031890300041c80180790140c1e0144000114010b000711451000038482c140f00c141c6028000300200b08000e09001e403a0002003203002c0414071004200040c3d00101282108046100e68142c1d80c1c14100400119a003907028034211004c54010f100031070000e411300307001041162080c1c01d81c604844040c0c001f001d441081004010261024005005040c4014030200003501041c8801500404c1c140001d00031202c01800c1210980382c0c40310016014a0b03504003841102c0e140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 11109980 1250 11108730 11108737
    0x206070318030e040b1201140601050403050d0503090313090e07060201050705040501120b03010204030f0c080c061204111f0212030f010b0703050702100503010602010b010206040b150109090e0105040201140708 92
    0xd041c500b0f841c65000c0300c030004005040400c02580c0000031002c0b10b001615055002c005054001221101c06a03100401141d062065010040054101060b1015000e001d08081c50b000b002c2c41e000e132810211808001c40c03403810164490500740380c0394124016040424483e2101030318662000384010300d4001405012480b51307218103810004490300204210810381d1000061030f40c001c0c0255034031079882c01c0c44141c0e1803000109542981071041e000a441d00c00050b04224006c000d031045013801140e44030b40c445400c00810640c1c0304182514000440c0e603562001c042c203171140e880c094100341d0190800910340030348070040c9503441c4010030134800c40e91880704d83c06044441e004030403550340701d1902d03080322030b4000d2807002500120070619820a0355001000340d81603c1c0554000c000f0900382900480e035681050f07030040d00b80b06600c000b18900c4c1d001c0740140104640181428411a90b5450135032086910040c070002c1c032655203a040c0411503a110301c011405046a81c01181424520780701c0d10070910 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 11111230 1250 11109980 11109983
    0x203071a070813031d1201050a05060108010807080714120a030206070201060f0e011203091a0315010203070b04020105031e040506070f080103030203090409110402030415110703020303010905060303070506010602010b010206070318 101
    0x20145c5c8000c1c482540c40c1d40a480246281c0c8000780018244040c65002600c8285d07202c501280c003400010036100c000080117030440e0b014000600c250f5242841d1500c001000c0d00105410400c00c0c0d40c1c3c1c01240304208842c51a40c0d129034001c08080c41c2c6542c1c000e084800f9500f181d1000c2003001c10821801010406490550715101c0ca0103994060b03900d8207680e0015290320581e924250048041100e1051034003071842070581607103100348200300f0001243c60f8480c10400405410007800482e0255100300051548044650040c1c28102940311a04140c0081101d007240c03554010410004096407044107540c8240007814012410b504640c2c0c0651a801791080090060799203a200b034040c80300d4061100364651010b0002c5699043c6800c28a0b60700407400340500d03065041004080108401008440400e40c05a01450860f400c259246c8050100901916807511040c0101c8001c01d0b814414a4028440e40d000011030700201d80c000390500500401000a06150500d50014540d0355030b46000001d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 11112480 1250 11111230 11111267
    0x10b01030c0c080d060806090606041505010f0c020301060b04081006060c0206031603020904020705030c0f0606061803010605100c03140307050d0e0115180b06031e070203071a07081303 81
    0x10070074220280010440c1d0781c05004c0d2032050307c09010301d001020490718061035050302d0074050000c00300001c1816203010300c00e150001c0e0320360400884c024404c940000280740700900115209a58200341d220903005a0801c05558001341001c2500f00500d203c6c5800925080c14102054071464000034124080140880d4020780300f200d12040c2c1900c08d504075020610028400c5440d4065410201c0c1c0d01d07003041c1a540d0184c8a2102d0700e81440c140000c201c1c1c481e10008103101d160208034441441e82c44900c41000d42c0540d00c40501241580c1c4418100c1510b5006980307207100c4031054103005142d040034040180341e0300400c00c180443c407a444011500d2a951001005c01c0820751100060b006012400031268000341010001c03072801800b4515a81c40510f1400a002d002e0012003003002502c4161500902c40044500803c00c1c000a00491580521140150f0341804642c0c0c440700300a4035254003803040002120b00b046a6140c2084186800902d00300c0d0a0310130300c25594001e4a0801e81d8034511106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 11113730 1250 11112480 11112487
    0x120901060e01030809030d02070b0306011103070204020a08040219060c02091807030501020c0f0601080c09060a0315020307090603050601020a0b15060c0601140d0506160309020301020304050a05010b01030c0c08 92
    0x4001094005200511440c01e14142640c0c2d00d0818060340d8000c080614800c0c000d26007a546071a10000e020000c1d50005440989140c9030100107441443c1c52a204e00801d010504c03161016a540703101403d103c3e504c6443c1c1c45c58901d400d00c10403e0581c1e5a440b121103c0610701402d01034580d005118130400b81e1b040c2c2d8080215150320701d0f1610044680380d0300e491140302d4141c0200c03c004040d0060141011914102d40d075001c50404410307111502405074805aa0080e510003a03103140800c0401d420a8010f412a032810b900da4803070307050041c2c002901c1c101403a0004240a81660f0090b03012005041511302004030b8101080000c1d202d1990150190020844802190701502d894141e00700043c1d00620003903a41ea0314a0580d610b8000c244940c031701d0550700380405042d07424049003011507950b0101c0604056640c16094600c035109900c40c1808141d1b843c140f81c0010780b070074801580240d00a50007080b8014452030102c0c00d4564507a0081d0406003041a1503c903250440b40460f05207501a091070b84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 11114980 1250 11113730 11113741
    0x13030302130312030b03010501050a031e0c0b040306090308010e040b0a0906020903030a020703051207030807030203090309150c1e0705120a050604034d0703060515120a02010512 78
    0x124000d40001d040041c0020f6242e0706a0f400d94040b5011007416070003071042ea0b1341c03032003040440e4046100c041c1c201c0c0700c410041140c0c040704450340780603144a00d420002890711101e0090403900650400c841e4035a80d00551010305400804541c018654607001080c1464541e403552000d40010b0181c002140c3c442e00c00b1010400c180e01680d2a60310003a00f1652664120b07e0300035074403120343c072003640c3c03a02585141040007108081110b51617505030300d8070300e42034480e0f000440095000614803903640c007003444400340a81c1c0c2c0c00c01c18803015840889203a11184141e402604016484124100d4582c2c3d00042c41c50b105402300d00740e012141c04071075881c0c4c4c070b00110b840e0a00381210001e005205000d0711042100f05600304a070424042e180c0c411000440080c407600100c8013044220b200030030380e11580c40030380403801c2011102461003203070280c0390200d40d203980c3c08040d01c0d0300340d5004540d94030821503402e04d410808441d0000c074000c107006041c1c640306600007030460703c980c4050384816502c8000054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 11116230 1250 11114980 11115007
    0xa020705011404060e0d0f1206050907050d060f050907050d0e03040306020712020f070501030c0309150507091202010203160f050d0906020c0604031709010504080d0201021b0c0102070611010e1006051813030302 92
    0x10300600020b030000c003282c81d000b3380085c060390006618a8240b0302d003000202c2c0c006241c80006041e16809070110380710381c4501409031420340120712002041c82d20368008a03452134083c4003403c01940711340001741e180c041a140c01091a10081000021544001000180788070002208012180207080001703461142d010100c2c09403040c40005844d0000601120600c0d00312035111501c502c440742d40c3c260349503854010491541c030140b48040c0c0103a00511001800c1c08041e0064038020f4418075040c0c02c07002d903903550302d41440032240700c0c180403402d801d40030000a5010300000282e407804681e810b1805080d80d8442c100d00c3c01041000100100200d1072415590007001280c000c0c00da881300700d03040c5c2d40440d400203010b98400441c880c00100c2e4048000e090341d0303000070840c2d40154140c018010880c1801411a1060314060044001e2764076607414002981c000d00809171342d0700c071a030008039050b8104800c8c00580300f0001c00c4069a220a41c003082101400790240e0070300d61380d241c9805130b40ca2210b00e4200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 11117480 1250 11116230 11116241
    0x51203090604080a020109060207031104362d0b0702031c0506040f090209040f030e0604090b1009030308011202010905060f0d05010503030a090e0a020705011404060e0d0f12 76
    0x1a6081507001401045040e0700090240005100b640e40340e10113034030b43c07004130b80b212600c1c4801408400902610340c070303070701d460b40219101d01e02054841c1001c44000300c8100c982c000e0020448410140c040320300e001d000b840201d81d000c0350380e0016065034102250b8601d80400c40403490250103007178a01c0210351401d01c284101c501401c1040106010361000007010b034010718040d50300910603440c0c800300c05402c54945c01039409032600201450381c0e558072600c4022140140c2d241c202c007000700c5400020300595030000504094414448000303040140132003408509441c1540d034030140407920008000003640000014159503004804290324030f8148010b950f00070b10380d0000c9030300000c0465545d4454100c21301900011000d00780902030380c1d90710402d01da143e2040d480756400040f0008014001640300390350780c50300071142e42001032401580f902d0f014210381c0303c00c80b4040c001e000c800030b00050194a0083d4814a20600d02038002010303c0c0384007034442c0d03130007028007400d10131413840040b8124281d0707100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 11118730 1250 11117480 11117497
    0xc060e06071107080a030504030609020d0602030c04030b09030712110309030102120603011a010e040902061c14090303070c1e05120c0d0908060408131205030702010807020c0901051203 81
    0x1120000e05000740301614003003064641104030300c682c003c0040c109000155400c55980c168403101d18082c01c50b00c810f8003400800310141c1e000760190750310b04000b5400e0b02c011445200005034590b196415803421040b86000900071007481d5206024501c00325218010b00c09400b03456007003d060707644001d41c3d540e00310301078140c0310350707055101080b5010b55099000380789105803012002000305154202c2c002d444034100c1c1c2c42c2d45000922108202d44641066409010000d00081038141021043e100b60915149000c242c07031640d41c2c85189840004484024098110304ca66014504525043d0001840803e89a502401e000c0c0ea0260112110981c0e1510a00540e040001e589042038001c55800d401e03440b155020480b80300d0891611350052040301c0502c140c07036109000d860951590307203402c005a045403542d940040b00c02280010a4011210343d06180e070b10543c0036688507040e41c0000340040310010594415074000100b00740413581e46084044c1500c1e81100c50003118100c04458502d035001e01d040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 11119980 1250 11118730 11118733
    0x40b0409090c0b070809040b09100b0307110a050d0207050603010b0a0302070204020f0309060105011404030309050d1403040e010e1005030a020d0804120305040302040608010e060a0b060d020a03090b090303160c060e 94
    0x801300d003407004441c0200130800060710b060241440701d2090000f000800c665181080c00c4002c01484842d00110065401540610702461031140c1041e509061501e00ca00c2260503901084c0c101050903014020390005000407240b860856140c05800c0010784910b082040405a000982e2011980e407036066039000c018040c245034a031310380003903000e80c1c0d14028000c180c00301780380e040d41c0c1c01a0704010302180c050301c1d450f03500c4d14400b514203002d000240130b00240445550418840300a142c120402c0544001c0c11810b44081c550751521440303842110303000d04039082c000b010343c4042c0481d8074000f82c0c4000c02d59065510b00e03000549420941d030540104d80195514000c00d41c15242410790040140007030302e0080b9000c110042e40da84409003203e0000644a455411007000035814401036400003a10401c090485807504510325140822a03001501c14008680d48074482c5003405054039085a220745110001c0d0702d18244052408440b44410a4900030080390020580801c440e0b50030117030308480d4040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 11121230 1250 11119980 11119987
    0x6030c0b2a030a110c1c15021c0f11090609010c140a02010806040e070302010f020a120305011e141e040615020d02010b010503010e04110d0501020a090b040b0409090c0b 74
    0x22000780c583c1c0c000038140c0c0018241e81d0780031440180119218400c11401000e0507075114160b07840075444130203030703c0580d45c0046107401e40c44c05041074001800844004003100e0740c0c000210202c0c4080358070030300ba01c0083c24176002c3c00c030400039407680840324180c0084130000d07110210800100c600b01002080203000b200d1251071101c0759040007410303a4066100b62100e0555544038070501007111035090303195046500c201400c02c0503501450190014060a00c1691021a0310382c94400183c4402c3c22030000013603a83e00100213002802150080c9030960790200c84000d444c0031600d07000c41c00d03004880c1e445181507a48004c8119241030014854100107401444403903a40d10201d007140c2c0c480800031000d0301480e200b2444541c03061040c1d071f0448105848031804c6900300000802c881c000280202d6030080f41b1a0410510380d503200c6e0360800b00b03208100250740d80c940d88400601c0300950741c0c890703851074105000078052408401b00b59000d076092400e00141500709424400f002032001d40c0103021501001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 11122480 1250 11121230 11121307
    0xb03150409060f0c0503090304171203010f03030905010f080f060f0d11120706090311120105040506091c0207030609020d0803070504080105061507030309060e030a020105100906030c0b 81
    0x41e04003aa40b024011820001440744c0309055505200480b0346124540040000303003d881c0d03585c12261106c00074401110b070742242a912150315a4800e822040d08100b003110200201a4486101009030000703103040e00b03c1e81316145000d00550006400c8a150311502000201e454079104004844044014031480307401c1050b0814460b0701e20203040703c900980309036480391103043c4001054000c07248213640d01c20130907155880300b502503c000c1c01a0f550080480705024404002405210700640c000c001414843c1014005546455006c100071700390226081000c2c501143c01090b000b080360340008001c609112144000b5019500c0400c2c014a80380011083c4502c00c1d0340310000e0403c0c0d80b1000d000b007145446050030065280803040382d0282c4250308010f04000030f4440d400c40e00d4070501c200e40101d030003000d4141c1d0304d0854102d10003800050790354104100780080d03406441002017125800400c0501d0464440d042141174a0086e500400800103000280383c007034081c81c1007600300e8100803907242d00ca41d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 11123730 1250 11122480 11122493
    0x50c03120906032701021809060d0201050403060b0a0b030c09010e0103272303031806040b0a090203010e03040b12010f030506010605130b0a0903030815060412050c0303031812070209010b03150409 86
    0x19107c100b801502040000355650600680d402c1ca056016101d0b141001d10b13665410340a09007200f14540c101c110b1220001c0e151780030710040c50103181410740041d1100341603c00103140d42d107a641640e04050070000b492008010b10314050050340082c0d6007601c0755000c0380c14001818601c200c8140001010b503c0240c2c18108040099070240b90383c1c4030400b5050000d2103e1550740c11081e2805040510040041400c1c80c0083c1d00490b180e070b1024001007841a1030000e018115003266005807840040060b04c200d000b2801c0d1501d138090a0003400d40392000b82075480312541c3e410140204000d210b8002490010140c0c0500320782e004021880c0015a02c4400300b82c02880024a442304502040d0b5072000302c0c1d07100c4280c3c2d6002400c1540503119030705017403410f008003120194840042d01d10f801f452200b2031445c0c130309200441c401e800c0380072803d0328000c060415510f8460f0368500d410305510248080701c010790b103030342c8400e0440e404000300c1912929510108591200740c1a9029441072406490200300b001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 11124980 1250 11123730 11123767
    0x240e040312050114010f0e0a0603060501030f021e0c160308040f0602010209010f030b12150103021c030203092103030f0f060105162d050c0312090603270102 69
    0x10a80e00c000105409150250603502d007800b41030713940756200340103070460352080ba0300c0d5141406a2401e001652003220118a20100c1134110400180d280d41050141d542c0500070610f0303031000e0b001c04502c0c00003618001d078155140103501030f1042400007180755640310200064405140744ca0f801e242e070982e80c0e2800f0386446d800351081e86010810342c1d00c0062206e00602c01d4885c007060685601a0301440564110001c4c0b805d620300a5104c030704260701000140c01003210074529040c02c804087c5550540c010401e15481c41d0a44c00c0101c141034a80d000044d6000c07066642c0841c00751a52030b000542804000400c0300d440f130714400c0300d11001c010014403041c241c4c102401303000b54107075688280c2c41d95001100c0520581c41c1c0c11800599280d0000009401699209040c0d140c4000b45914200c80e0190f030b4061028408054496a00c10b4030800c035146070610681d080403810101141c074110070f8101080a074000146040401100203281e04c4000050000e104180582a402150740e25a140c8615900d581c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 11126230 1250 11124980 11124983
    0x60b13050f0a03050d110708010606030902030c04180803061c030201090c090c0f050f09030105040804031e02011d03010b060309070f0509040c150c050a0b01030b060a0506040603240e04 81
    0x45266201c801d5810324003521810740360454040c00c0028980201604d0110541d414100540300c0c510000440c15020b00c21070010307041c66a0302081050080c010146070440107000984a14034007102c800007041007881c0714071195032003007c80740c5a81d203110010310040e10743c003180a02400d2000c2d100302055410340c031640f540751040407030240fa29250000305040300c25140218011624000071001e00d40d000d00003800e43c414506460038a030901c1d020101b42900c00070780d41102c030840085024800c01603001d1258103101d007451100b030040c05950700001c0080150304902c2000010300f100b100b0141d1020b401030010307400050045983c0e401e108080c640c2d80c117224801c14482c3c5040d41c0000c0b5184c9025500d07940916042401110854100300584003590314101291080c072580901c913400003074081c4180038146000742c032029859851424040c003584c41c0100118424070302e4500034009030f50f0b2007081d14181ca84500d00012501003001500e0380d0b080c0355280202d01103d8514000030224140d10100c4c0c03155 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 11127480 1250 11126230 11126239
    0x303010e0613090506060f030118080306010f020303240f0414060a090908030c0307020a0b010305031803060933010905070e061c0c090b0a02011b05090105030a05060103060b1305 78
    0x9842d09000e074046561a4a004100340c0004022681e0381c602084151110302c4010000982a80302003004030012044030b0b400c864900e400310400140e5a0049200c0c040d440d070a0011b1440e6180002c10000d821522403507207262042d6520b420640c0c1c0d01c807400d102040c190040e108100c0001829000e01c0c18001c101c620610960b861a00440c0e0761042d80101d20105a200103800e0954450640c03903e11500020300e01e404500c1220310700c4000c42c1241d444117000303501410180d50782d05105404112240c081241140c00b03030384680306120021500060b41e0650714105450070101d60032410003034049040081c3c040e44480c0000c2d0010513095031076440355000c5ca00070b8640c80c0000314501c05100040c081e5041d410b030030285810410400001542282c40700300b4107860407424281d1506200700103904680729180040c1e654032142c801617180d5620010b0565018103100c2d0030000765800007495407100800c001c02a94030340d00881d0150740641c00c40c070007402e1071304480394503450300d061000c5851000e44507440c4203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 11128730 1250 11127480 11127499
    0x140103020a0f0605030103020d081608120708070e01030507050903101a1009090e031e070b01080c030d03020d020c010603031107060e0a0902091302030702150f0106050301150903050303010e06 84
    0x944248030b40000310381c05034451a055038655020041c80c480d01400a441e000001c1007007100785004103d0100a951207a1101500e84034401d114070380300c48000303054805002031241400059500400c205410100919010400c0e60310500110b9440c0110b40b4050f07050311854884a80c0b075421500204103504401040d541200f0500080043c03c40e40c3c9c988010110303040c4802800005442d4016001c0002040212481e008039048041c0307142901034006040c107240400ca41e003c11181c00050313401001c44600400d04d0504940c002520383da4005440024141c2c00039641103110440c1d0190707455014101c0080180c141d0345d09028181407030f44445a003031400750a03004900c0a01039a080c46031603201920018415003408982c00c029800f5194081d030000031008994600451400194802d004030750281800c20321403103054140301805010101010980c0005000150703112056074111020444441130b003000080d000c2d51703460750541014042d40000000410020800003580f8040c86055501805 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 11129980 1250 11128730 11128739
    0x2150a060608070c050703051203040b0907051e04060e0106020a05060115090911090d210c02030d0c0c08070e1005030109050d120f020d0501030b070c050606090415140103020a 77
    0x215000d034000c00c0003181c0800080780c3c010b8031078002151120710940854850036142d849003450600020410700e00e800000003040304000794004c021750002c0c06040104803035403e01c400604085090720505a10001034010300c1416a80d6804c020001c009650491080756160b17000291551400c0d1400d8419106010002442c1e001c5000c00400000003a42e49004480c200070143c400790400c106050075224040c0280c1803942c0c1d03400392495043e8814070382c03c54524080c4400801d2014400c94640c140040c02c41c0103c007584000c280301081c80309526018410340c80f01c1c94103607100000c1d41c10944151150314008980000100c0d07106001e4080d1115050005680e0f504040c280c8561800081c140c1c1c100d005081a0340d8041d41000044101521000c90382c0e0200310082000c81e048142503001c00d6444200410a1201d80e5103026081160f40c50b211064a4a5840e000d503211005010076025224000c001414070000e0059040303022007450f400e10052031200c4480002e11000c3c04143e200d280d64100024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 11131230 1250 11129980 11130001
    0x40b01080115030203041406100503010c05040e01170703050a080306150903030d0c05160c0f05010305060a1206021603020c0102070b031605030405070302040207050d030b03070605090402090a030b070215 89
    0x741264840c000d90074141e00e095000b24042d40000d00104e5001000a61071081c2c1201401201d1240355510780d1940c582c0c0c5007404040c299920203841c0001d00c4070801050200c1c203000305c440c074199041c2401994954079010348240c5440450b9101038041d0050100c024200240c05005500030302003202c20a10021410b00504090701c20141c400da456401004805543c0c42260090b00c1c41d010705081690800390711004072030388000440e4007201c008034008002d00c00303c06940c100c0b101404082c6400c008906c2c1c610042950f552840c0140b030007000340b841e072080801225030100c61420f03101ca14102055a400c0c035029503580060b403641800350103016000f00e0002800c0b01900c0c03240000e042c20485404c4514020343d600c1c0d0012700140c1e00c50159100100c0036131900c1c0014000140708400502d043d8410000040c205c91041445500c0b83e040b8080030007101e90b0080c03d4801484040317900680d0307521154000f0385114200c2d0300040000c2c503d0001c001c1d041d41c01140000c0403505100e82c00d8410b5560b1900f08 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 11132480 1250 11131230 11131247
    0xb1005010c030e01020a12030c080a02090105070209040f06020412050f16050d020a1a030711071406030613050406020c0c0604050d08090105040305120301030c150801090b0402040b18040b01 83
    0x440c00240c0d140c071481c1c0840d1080e000320400141c180160f0b0b80301461a00c4002c01d100c1d05169040100b0388603200c5c01c00c22580301000e01c1e44014140411410b150091000800c0340c071405074041e20500c0100c02050a03c0100c01c4004449948010215582c9075034105078043c0410f110015980e41c0104140d42c40b00c00e6003c9958043e0701259580e41c04850704000800008004020007660065000b070800b04d1207101c084413000700c020301080c0301900c9151211004045003c1c072840310a03a034024a01c2086412418107081030081e00c221210307a160ba42e041e01080c0004451941d0541c003a040c0001d10060198980c01405090144d4041e2088103400b141880f46e06d01c0f40e40724554000c8a1240c550780450b400901404603518145441b9103865900c0d00d506180050301079196011040001c0104104001112914024091007580052200340b011000d80103480520800404a80b5012012215034841d41210082c0001c50003060b00d0b00b074a00c0c6a92501055801c001e40514a0901003000d41d60040701030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 11133730 1250 11132480 11132489
    0x305070302010914010909021602061317071d070c0f11010e010e1305070e060301030501061509150f020c061809090604150c030213030f03080709140d02030304051005070b10 76
    0x6880406107060a1413009500c2700c01d8018668011070011300c01030355480c0050110440502c0c440410a0034203400344100703100039030f0070304140d40310307150400441d54007580c112801040c0c1c901c00c1449940b0980c042c5c42e107421803013000340b0700044000b1410801c494114104801c24003a030b540c1084807100001507070f6401c034403100641e0101c0c10700d60745c40840310036400840d4440304500d014843e8500440104981303400c00e030021202651150814040d040401ca1610b1450b091403a00e1884140792100c036542c5aa200488182000f07410040d100490340200144105600b01030300d203a0b03458002082c41020b42d0800b5804034072610b601c0c0c01140070500c001403010b000b83e40254031550241100c000340802040c02c1c1390340703a0905800380001e4050f040c801c06072000550140000203c80c806c2898000c040c1640106581c1c20f100480d101800300c140e943d841880c041e1001d4804500f01905400002e1850250382d10190b0b00c4070480110501c0d1039403206c080c092640c410401c42400da19400b0141c05d14003958000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 11134980 1250 11133730 11133737
    0x90b070207180504050a0602040b0c010b090402010504050f220b030f010e060c030709050301020414010f0206011a0901050d1d070807080c040207060906050103080306180f040303022101030507030201091401 90
    0x15941442d07040d690060b034005200701c08444a1081c10703603a42d01070340c125510440c1d66210219a50006140038010b808441074119200195403a01d0742c0040c1450065004090050001c0e20011640f0b031509050800c40e250040b001103444098880e185c4068840c0c032403010301901880c030041030340180501030200702524420260505544900341036045800062483e420021115030008803a1002e00c0144064490b400f080d268541322580050800c10a082c808011907001c08010001110ba111407043c0e4421001419039440740c0c0400100d074240503140300c003540c992508803000c4039095203940780c3d02010595030030740708441d548600260300e0325114441e04001d600b2540d61110245020342c0141102c0b40300751000a81c2040b41c0d29582c0444000f6003048411541c0042400664584042c40c01e086540d01e000c40c00300d03031414503412841100042c0000307042c55004583d059081c102d50300602c00d0420980c890301e00c90342e900d0401c130790b98065038402030740440c0c2c01480104131800c48402e84140b509041c1c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 11136230 1250 11134980 11135009
    0x6080c030c15030c21010609050d02030a0201050a0201090203060a05070908070b090103050414030a08010302010905040c0509060a300c03020906031f0504020a03050f10030201020a030503220303090b070207 90
    0x2c0c25120294802019011a04070402c8883d041002c0e46040035401d400300100d42d049981072003009040f04142e504981e100e4205039800000595000405107122942071070800e49501121605034090207100750020741c1070049004000c1c1819407a84194410b51031380e82c84030000d80d500c1c0e07001c0307884030785902030802d04000400004043d5402900b1042c0c01ca40b241c00b610103404541d2030701d07a0964102000c0b010004e510382d8010015581d004100c50080c0108840070040802d062401401c18820300c2d60040c09104045400e5140720300910750700406407a80c84008044c01c2c00c1c0540c8014240440c00458101880d110140c206e00344070b48241e45200070050715040c916240c9504020003c10307184e02400803041d50300004106512140054186c55136107403000710325824a102803000d01900101400402c0303540480401c0540c0e8009410303030803550542000b5990380c6858034190020019a00001c50000200206070205903240e8003800c10207000b425180815100e06900300d0f01c5012510800140c8031014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 11137480 1250 11136230 11136259
    0x50a06050a0507050318161410031107060f0b100c12020a0c050111010905030a03060f050405040503070215070c14010216150f0e030601061e050a05040306180f0606080c030c 76
    0x15906c6071514a10008036000c6001d5000041e44803001600144018400c0410601c1f40d424400130054260749281000c2c001002e41c4010b01c8818061040b000d061507072980d80c5001c0c1d041c0544c0c8601e5001070090b060a0785000c03108406441c6458054040301d00c004c124100d0500d0302d2001c00c4c120040e503071040c5412035091428004482c4c2000865403425a5517030781500c41c0c0014010401090f90500355140071034203519003441100e00808603442203010b01c0c206010400005c401008a403d0240d04940e01007020029140200150041200c000c2058410070008900c4082611600300c0d200426403c54841c64a0314800c0c40c1082c015115543c80c5100c41c21417000500d018114601f404030640c40c01c440b00e0661440000c0c078000c2c003a0320600c041608080451000d86610280d01e5001e000350800e680b03003000302040201301c1d100743e100c09020241da828000807200b40d1000340e61b071425004013400c9060703129400c0410082800d4898400c0354402c00000710b92074100480d080c070071144028203060040510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 11138730 1250 11137480 11137501
    0x1b03010311010201021c0e0c0d05120714010207060207170702010f080603030705060414060c04080712030908060414060105010e0603060409030306120501060312050403080a11010f09050a06050a05070503 89
    0x707515000341076540900c11181d003409444c420304000316000a010030914003070080c1030b040910450201d4080c00c18220100b0101d140000e40c84030403030500409680d600300a040141c2e0030f0060344e080e02000d5000045210501c0311980141c848a40145002d8140501034500d40000388140c0300b0084c080381c03000c140c0c40c004038003540d1807030761082000d0103503460500c96a84080c01d0507811101141c041c1d000b07048001c0380b0307070041000c2c42c0e00500000543e1301e0039041400c110341d14680c80c480c0c150800c0011483d8000c0511664202c0300a00706001128240c2c01c0c2440c1481e007407a43c000c0d904e0154861080000740561050115150768000035250601c1c0d034858409000103050a00320036401d05403250f0000502862003a48100303e14011000024400e0071480c0c4080fa084442e008481000300c01d11061000c0b41c0c9082c100e580c0c1a0b9681480c15030b028129088a0141c070414802c1aa194070b01081e010030306c00089445140c4034450502001a541c50100160849000340e465800103103003800003440b240360 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 11139980 1250 11138730 11138753
    0x60405060a0506040608011403010606090b07020301141602010b0109050f010c0f050604050f10060501050d020309011b030608010b03010203040c03080f07060906090210090503250306180302061b030103 88
    0x107000480000c0d165000b195030b69102c2d034081e02c0003e0412004004054500700d030207403d410b04030028000c4034901f0200a140c48a11b00400c0807500002030b00f40c00310f6030f09603c84107030030040d0345590f4807920b0184140f400410b0341020000155003448548541c0350b01c0345508a0a607a4014154003403201c1c04401141c00a210400440e258078986004102192082018612640c440c1004200c10210381105500701103c041c07007040710500f0b000e0144426030300001075521100d0030303110040c0c40341c0d41c0c0e41c5040e01400c500082000d815004207401059a60f05400a10581d0321902c0281716180c41403003458203e1108a07000f6100407083c206c2440041c000c1c400a00c2a01080e00d84582400c94030349a80c1c04450b00004102c60035551103940c4411401c10030000e01f4180c81e6400d200241610b440d01203611284030104a103054040700500715954044094900042c5410580820010380c0c0c08081c41140085110140c016100d060002011641040c0342c0e203080000c409403060841c0d00e503584010300f080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 11141230 1250 11139980 11139991
    0x306060912032304030212010b030a06020c0a1709010f0221130b0307050d0606170610030e10020705010b06040b0d0b060d0203090705040c02031213020102150f0907120308060405 78
    0x54400e81c0000303100001900440a11401000713030707105e1551041007d040c04011504215904200c9020102e640204503018001d4010070b016075100707031110003a428924000e10060505a0a40e60b24908240001c06021500c0c82078032100c20400d82254160b980b10540200038491710000050680759110042c080c0000103516680f00c007560f600c41481101e00d8200b2240040042c0000c078030909112024003888004100500b1700040c1040e441050881d040c10082146000303000030750704d4549040c400e40c030111005000e002650210b0b925108104040d5002c804161055030070802610300b03e140a8040b902190407079540680343c8003202c4c402101030421034400caa4401000d028170300340e801c1640003d511400039040034003080317420f02c400c000c2110008809070045500a100d410308450b105011183c010301030034100d4034030125520040b031416400c401840c0c0c03454485000c0c001210082d4081b203015032a94816070308850b4030350b04090007407440c004010b80040c580c60003259803801c10713074000354106 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 11142480 1250 11141230 11141237
    0x100e071806030803010b07060c0306030b040201031d01020c060f2518050a08010e0105010b09130506030c04110406090602060408030424060b070c0b030103020307031203021201030b070f030606091203 87
    0x541e50f0b8480f55581d8100340d0010160110000d030360010000c0c80d21911340050028181008520304540f00c0101a100083c8024103140e0b03640c80c403a801803c680c00345010070403401d000f035540b05184000305885010a40b1300317000040d0070b072010803150a0755003181048103c03610702481500030601d4007115042c948001c040441d404015010541e0303212464100080d010000011030b400c116086924211501607018003601c4030103114900360b965821041e42c40b0400007a2012070a600c1c0c1100290802d10150740d4207510500c3e102c0510741404c3c0c03d10240c4107c0304e482c0c0750208415170300c2c0c0c803c1c0d032200f40031100104501010400207001031454451806449101e1030b490b001c00c13034000501d004450b882d0b0001c042029000c202c1001700a0103010b50ba010304450403041341035515550101e039031080c403070000510141070490740c1c80f040f0b4404d034181d90a074594201c1108095a50f4101901921820f6440000003101880c050607043d001c0e0155070708448055481020302407801c101e08a840041e0201103080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 11143730 1250 11142480 11142491
    0x90102040303031b2a051606120c0203041203180608041203020306060f03090c0d0507080c01050403020f01050a02150103060501060905060712030e030403060204090203010602011b02060a1109030a0b0702100e0718 93
    0x21030810001d0020f1400c14108201900c8c2c00c118001c1e11404051810012050038102c0d031180e8150301105403021281a45440421441d151409460380d503a02d0340d88071400716080600082160340a941503001c0c0b4050500d11441d45030310340048060744412529030b0741000c2c00304100d00d03031031303484000441d8004403000a5681c0901c0400000b02d6007211740d242602c0a5002a009201c0b1004c14442a10206d800b42059880d091444d4081003d0305e001c4072100307042c80f0000c20361040c164028420243d50214040c05c1081c10b60b140e00d445002058207006081c000f07652f101e8081880e0900000320745910b50400c0708600d0004803090114040c010090010405000c240800030010b0320500141c40503003140080581c682d810602c0081c21100000c80e070f50090400107408800864011841513086940c210303022030800340c4459544410301c1002402d41d0103101c1c081d480424080701340502030040d1102d50035110001c02907503004040c1c800826101c0e440780c0140700c080000f104500c40e00110b0340b401d401e02091 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 11144980 1250 11143730 11143733
    0x9040819030b0f010306080c04050a021905070c0b07080715020f070503030402040b010504030201090611070b0409090b0a15051c08030711060702060f0708070207080105090102040303031b2a 83
    0x1008212018400d01003512000e1040c002d203000240880e9244080c0317010000c06140440c4e883d0385c0d030b0801107001d000302d40c0c410100e0841e00260301161040702c08035106860000c0e50b020b00800c1c3c0e0b03210b0a0309490f200070f04180460f4003542041200c003100c8e0421001802d00311951500d00754081548410b0500c15820032202905560220140c4440d5004101644d1640f6107401444241c0e0703071100030030341000810801400141e0f0400d04000c156005c61a14003504030090881c5803404480350820008110b0110b800121075605800c80f00c00740703200d003040954580341c008e50745060307075400f140300700f4402d81100c2d0600c0142070270b950070468200c0803404618660b115881790003080d4400c0c0c8030302e00000c00315043c0350300c519800c1256030f4014a4610041c600d5180c49100b828a2420260420040081d01004610380c11701c20410400a07240540080005003841d60205000b90f000b0b1100701c0100782061010481400c2c000002d140b821956116100c5581f80d4a10403002000f40020384024190f01011450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 11146230 1250 11144980 11145007
    0x2010e0118090906050c090919060315020d0b040908041e0b0f03010e160503010504051302120106090609090206090d1505070f08090c030a02060c01110c0109030e011106010302090408 80
    0x2c0100c00700005050074a402d10105035003001381514520f4400b0828200c2c00c0d10f4454482e41d11080c0c00401c00d0112003040b034680042c01c0340c0d510150284164903c001d20028081d4010480c50361140300400c24100424180800d5554114001d0561035007400200300b055050181c000f100c429090002e080e6684581e00c420b926044a21041c031441004001030103041c030740c1c1600a401c802505503d0403048409080280203120500075540a640c8074404280400d01c9a003c1012180e8010a903220240170101e0390341c024078a0b0322079011400c1c10120b00040054651286400740381d000382401d850607205d041072000c802c07a04c4408a0382031440d9000c4c00003d001500c40c0320701130f94465a500740e00082c0c2c0c1c6402801d00401030503200325134121400c1c0c1c4203681d070300144104603070b9410303115551a0303d07110303a00c14018401181c20004083c0c000800f0100d40a041d404202d4141c86a00c0301c2101804150044840812840c0500010340c060740c01032004d032034400c4a41c0e90043c4142c0c0841d2501500c0c46101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 11147480 1250 11146230 11146277
    0x90c02100905030a091a04090209060702060a020c0102010501060e010909150b04060806030106060503090d0309050f0106030b010503070e090601060c061b0201091104110f07020f040612050f031602010e01 89
    0x681d050f82002c038504d21041d0b0301002c280010240a04801c500700f01542000d4070074402d9102303503109241d0000703d104281e1900d50070ba40350780d90003c2105460300e204a101039210742c1041036240c015440d003000400d10f5802405180e282c0d140607501c0503026424000701400030b2014100c00c000d004010305001803083c044200070000741c1025030b10b03141c2c5414010140750a41e01c154000005100f02030007045400040000d00c0c210400991802054003107403400c1460030250b082030000099400c101000c401c0c0140c035010581214001c6d01121080e6690f4085032003552425a0301203041d0b0011001040384621584000c8440c6006440010700b042c84103998400303201d51000d6900c0982d458081c00401e004804115644c41035080d03406002c807480d03941d81d0140301c0c0720780104500c07036140106511041d51282e10003981c018074050420803143e500c03490100119100d011003203030300d4420310001e10300f098808002e079a90803c88000d205505241c65005480200c28223650604010305036003107904003200110031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 11148730 1250 11147480 11147483
    0x6030e1e120304030f03060905010605090d0201090306060803040311040921050c030703080601020105090703110d0606050301060807030b090304050102061810050109020a02070503010501050603040209040c08060906070813020a090c021009 104
    0x41180017103111801806481c100c0d8000b2203041d2420b0010401150014110345090000b02e0741841e4900b150310058a420500e90000743c00c5604d404800300b45404004000c1003a01c0c001c405004186100d0010802903605c200c00040c004200c01900c0d000810281100d07920554680c1407503070800051600e464a035070001c83c400d0b00010403000a00c000d550f0284a01e0342c01c841c00c44042d00600341103490319800f03020620720759401610110345030b409011155002601a1100030f00a0103903030b50701c0da481565581a0f00041e1080300321800440c1080d00000115422606c041e000f8104c155900494444030041242002100b80103940d1410843c54081c8100d60107010002401600c034404800001e1400f01680c10490280e85080d0050045680d240706507580a54100c442c20500d64580c0b814019038800d9500044a500c90b02e02407000c00ca5020030f1540c03099240c0d640b80d20080e502c410000f8412103112001a410000e024001e021a0344a41c100c48074884c018011a0000410000101c0031aa0400310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 11149980 1250 11148730 11148737
    0x30618030311130608060109080109050c010f09030c030305030a090f03030c08070309050309210601090209010e090c03060405090c030a140106170712020a03080a1806030e1e12030403 80
    0x88610800d5054841c038885100001d181904190140109a407242c40c0c42c0201021312140d0000102144e1007030500401605251000b4480d080d410300d0a150755107180d004c001d01050301060701401142c030911a200840f600030210301c0d061841d54800340ca80364000380444d0825a00c40401d440030500c05888030030718605c6071f540050080f0b06e403200146032800c080e1141042604140316000880c0000040d0b40034542c0890312443c9201100c50201860f03048651482c145029200000407800301a83c05000d030103c003a01d940e0071000140c010000000780440d441381c44010180b001c51118240360344410f9102040c0c8007183d4990802030000791030502c5d07030700048840d810f480107015503000342801542e00071f0040005503407404d0000c035080340d180e1207103000710015144185190f4080d940c0c0d109a02c8019500b040680e030b0385450502c001001e242500c2e14000b0081c0c204503001562902c280308050031070036400040c1a00d0310100713030042a00c9180c00075920103486000a14261404000300460180340320340c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 11151086 1106 11149980 11150021
    0x10203060d061d011506080105060901050a08040f020307091a030c01140a021006060c02030c120705061e0a05070b130203060a050c0d0504050d03060911040b03040c0306 74
    0x50b681007044d82009010309943c810602680240c1c1c480e6503600e0801d81e212020711140784240f03103100e4001385040025400c1e07244946499038116100c0e10310264404110380011340f4041194001035400ca03076980304014220840541003480a20650181102c0e003081c0c8006040518000038403080135a0010300f00303c4030342c03080c05000b4020184013020441103072503003001461752386d401000302e001e44506c80100d0350a190480340d04068951000c0100710440c1400107200b001d07001000d0750300701115a140d905e00104101030180010320b407551341d03041e01d500407802c0c60540407902a090048025043c400c1030096100401c0e401d074090303131859000c01c05450703620741c0000c43d105410141c05140e20f424180000c100010070000b0100380c032071703500f4807070b1585543c612000c40391021030050204008000800140d036800c80550b03841401046e04180c8a603032511910240d510000241c0340015201 = true := by decide +kernel

theorem cover : BRFrame.Cov 10971230 11151086 := by
  have h0 := BRFrame.cov_init 10971230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10971230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10971230 ≤ n) (h2 : n < 11151086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
