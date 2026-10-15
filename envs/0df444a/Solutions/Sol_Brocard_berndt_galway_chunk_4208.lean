-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:30.431379+00:00
-- url     : https://prove2.me/submissions/a2c4c429-b55f-4c4f-861d-9d6e03b94f3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 756654676 ≤ n < 756834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 756655926 1250 756654676 756654733
    0x6081e010c142d0d1e0207020109090b010509100c0b1302030a0b07120612052404061e14100b03150d0c0905010b040e0c0a050706051f060203120a020c 66
    0x10700c1c0480351a00905190070407451a6191500c032042e02a42c40c0911031424001074610705e0851901c00950300203042244144100450720343c4442100340c00b6070240003900c1c0044000792028074100308600c8000c14660041e0000c903003094030040410241d207481409038800320750280040030f1441194030381c500b0001c80108a20100000c501c2c0700b02c60400135000c4c0100a281c020400c451110191500e0703410151182071080c00e0712010b0a6949866040358034883d0859001500040c00702039503009015800f40e40c20b2100c1800c1e0401510701040340c2d02c585090701c04d10700302c0c051000c42a1104d4606078944000c1d00c0f070b81180140d480200100345004065809070a1281a80300202541c4d120700c04150340c826444405802408202005541c0140c00c00e19030080f207001c0780c54608110500b028106004e4401c002d491256100001042c0e280107207055202c000050900c02c8007140d880000a40e6036110b60a08418120f061003c034075204418001e88442c400560003a01ca494100040318502121885204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 756657176 1250 756655926 756655987
    0xc1d15011d0a0f030311010903021c0314042103050403050306271008160e01091a090f0105010f1e05090d06050a0c0e0612040305030a06081e010c14 65
    0x4036400d0382e990000400501e64101c1c40032040d840c0d818003401d00c00620b9550141641800000e100090b408961440c00b0b81c030201e040815001d060301c1c00c81c001d0510b60f201442d200f4284080c8410700010340c00c805000491082d1201e140d0502d03000c11010b880d425100100070500510100c0c080d0b181c04025101c20100300c02e0060046071400b180c01180c000b00b982c01e46245d602031001030010b440c0900c95542d0f40001ca03800101100c1c50150182d01d003030300521590701065540d4004511010318000807a0880d00001d014200c141032803000c40342440800c1c0701e80b6000c104610482100030340500702c0f15100ea06180e090b6155000c00040940c2e061348401242944030303120003844000501300d4401c085c0201c036209000200501031000240c0b124103403010700e41c0706550074851407803005041303040302e076003d907040c0ba105131203444486010300a8001a006a4024082d000c0d40c1d0398805d404010740c80900d81078030001d0180c0094008161480740f55903a207005000010040035401052801030b004802c2180c0110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 756658426 1250 756657176 756657227
    0x915020c0c1305090606030d0f0e130c08060901090e030403020d110d0309030c06080c031b040803041e0f03080f0c0a0b1512032506020c0a0c1d1501 65
    0x244030b9a601464885215554001d21010190401400e035021a09500411008401510242011039529103200800080d92500840c54942e48202c000540941005004829404e14060300d85d4000b11009800307040041c0000a4842860152100c40c4c2600009145003900f10b0b02440804c1c501250242d425050b040f82506482d00d81504ac1c004540c02550380c0a0354908629001c581e1244542c004001c10400c01e003404090140300e01101e4110700e285078940c0031a0460700e00751150f40100c1d404010384d4000440c0010760388411120b0503c2d040c1c1c108403003140b20fa440d40c1c0205e1226809002c00ba0141c101840600c20028080c801002035540001c200d0300002c00036039421140c410126120040c07400b12140d08400c508008a1b82d13110000c1d00006103081c0300b0b603800ca0244410001c01284044a16410041300b40000303641110b130702d00000001d984840103d401c080c804448a4420085480c0c1c503006114103c100c1c40460768080c039035244800d05a080c85c84c00441d507284142904042c0081070041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 756659676 1250 756658426 756658429
    0x206220503040332060411040504030905040f020d0b0a121b120305041d01060e012d0f02070806010e0406020f1c050717040b01060c15090f1103010915020c0c 69
    0x481c0340308000c0d00c040e06101c40e940c1300342d43e145a106600010059620120a01c4005401c880465619a00130b0f60002150798a40c1022079010481e6030086800501d44120b080401000d0380040856803140741c400d018510032030707080c400170790010310425000d81c14001914000500340b2403c4800501d258500744e800944400100c41a69560740d01180030810000703040007071942400c251050043e001468200540c03400d40040e04003403105515034100201489006180078125400c810a110307503044140c648541c2c4c0e60003401004c00d200312180035114801c0c1c0041d2090000171080c0c1a984807114034061030701e4580e52000a500b24000b0341c00c08034014000d1020081c040c1d0164580d49041c890089603609160340064545184207424104c00d070740c01000c1101045040c608107044803140c0c0340c007152000c06400d12440194140c60444145d5081c00d0f04c0c0d1083c4003100750310a01050003151a090000100400c05080b08c1e1500303401008250080106414105a5400b51058820000c00d0380c00c1d8005940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 756660926 1250 756659676 756659693
    0x3062802040e0a0605040b0f1302310807080d05031302030102030a0501090615140c03120f0405010606050301080a020d0606180207060e07050d0b13080313050d02062205030403 77
    0x20030151045640c40104510420103001303d0004120980d0200902040c91010520b04200040d105000f000c0381c00780c8215847d02c80d41204c5040040100144c004e5403e1140e010a00314076a551442c0144c0d180008a60000d010406904076441080100441c0980f4141515182c01c01003080800840d00012080561800c1c0000c45c403c103084503002583e036040100744002c8509540110900200d40c0d6030790343c04030b50888488002d070112941d03420f468078018240c0520b94070035554075080c0701c40e400050107601e40d84110110b0085101d80300078410319480f240104c5603030000748038254082c1c1c04446110094102401010203440c081c0c5c10100d0003685601c92041c5910300c0205000c035076030b80001c001040c480f0030f119526210b0282030140c011729180100048042c46d131000d005c1c1c541c00c8004041441c49000308902d19210394400304458070707450644003010351780d1000c4609941c2030150340f203024403e40c400300e102403003128040e941803034981258040181c00c0e41d0500e811140d51008010210104800c00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 756662176 1250 756660926 756660929
    0x90a03031e1407140c0c0607081912111305060a02071a041e14270f091912031109132301050109140d1520090306280204 53
    0x2460800c032036043c400c500030b001904103400080ca2180910102d11050303c0450b10481d030320380807282191940c606052615546c8101207059210000c0750322102e003900d07045442c1041c45c0c031001d4400c1203064481d142d2008130703100ea000080c1c0ea0383c05010040c402071070510060103800c59648100da07000b503240c10034241700c40c0814015401403080428204180d5452403403502200c05074140e0390380b15a07d07101101201c0340c0c0b081407a43c4600880c03040b01c41d0000100d1701c0d1903400102106040c002c1e00308440b18181c0c466044d19450b140d40200505002545009010407119540c4040c0c940900001508110020805040c5d031121643c0c0800c048a6580d80c1c0221304a25540300317200c0000c8806914521071040d41c01a1030f07045041b81d109004000c0d41c0e130405990350481d840c0c1d0422840c143d2181c00011034a510681d030050000344480c06a00340280e059206803014861628518100860480c200040b405070300c0080e940f5511800010380c1080f420440201402c020340015403030821029000e1040e43c216 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 756663426 1250 756662176 756662201
    0x201030f0e010e07330f1103120703050f040f0312230105180108070306020f21090d020a021e030c1005070302011803051602190f1d090a03031e 63
    0x7041341405444400380340c1000c0d250b4080c0400403104d9081d1300701d00344549040c13141d0062200424001c41464010320040381d01080c40b10540c6da451200d8900c4420800f026500100080d01d4100028045900491224041d41d0041110000b0780c40994003103c0e14040034800c040e207980c88403101c18010042d00d282c44003d502e8011010384030340c141014840f558144100e0a07000406071001000b401e1004111902620b405c1740026036106022583c00c031036449540000185003503030b52112203d0b807016640d094041c0c0c07540e134190b840043c58100c0403662281c0005000c2c0d800a029860250340c41034041050300c4000340502542d4181184500003420104035240540200c5e60010302001015828031030459807400d403a090703240c02805514000c00b02d008072407001d01000100c00301e02095503142c403101d002c2d94140400210304552510000503070780c2c20790310a2001c80703c045c501c0440e1010340c900c11240b08120a1000700841505501c08401408820001c1074981d03c603020108601038a500a441482c0310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 756664676 1250 756663426 756663433
    0x3021f1b0201090212010603380a0911100e01030e100c080708060103200a0905060f091309170a1106240114030114040e030c0a0b0c0c0a0201030f0e010e 67
    0x20300d40103100c8588000b40d007645c201d901d0202e040c40000c54074181440c5581a00030304018150396402600342c030b84e01030307103036170614111410030070240e5980b64000807802485401100d8540c162076061000075441c14036420003140e4540c0d200f04142d40300380d0140810142940440d001d205100c50000100c422610300c0400080c098405c000180340c10802c03154002c0001e00c0c04218803400700c01490b072030f010521090010001c000070000010b174450030244026040003080c4d941d4400d2200c2c611105603204801950042d0f82d030700d00c00740451a4600c86c0c1e01446401010b01d8054445045140c10550b0001e00030405001002c00c50540444003080514441c030130082040128820500d0055160680c0d02c4102d0b0400900b035000820481c1e03800d0a9a04581040703560b046103c071900c002038064103480313003900340b80e1001145c4511070100004119649074003c410b01c0c5400c0d1500c0c0c024064a05c00c4007052445507102079034104c0154466403003220041c40465001131241c1d8105422800d41c0c040351950a40341c0d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 756665926 1250 756664676 756664691
    0x60f0c08130e1f14030c120606010f050c0d0c15051e0108030901170a0915021b0703080708030402041d0703151503060c11030307030f0c030903021f1b0201 68
    0x1402405810f0300910b4009a00321040624034000c524448a07020f0b224a0000c00784030005a5101000301c2e040307101000b00101c2c190880314500c142e0742c440c119111800140303482d4005400394002c804a42108020340c0207880307807030310700c00046e078440580305022140300d0903403030469a1401e858483d590144c0070210141300384002800b1911038825068020321307d40d8108220b40000f60380c0000c3d0200c00a918250a101c0b01d541c1d0281941c024000c6120141c04452442c032826003103502d9a00034150f00702d043d20391b8079500415095041c1c1c1c1d8407950200910f140020844040454240d0000d1540309100130008a00700b8846400500d1904040d0740307030750340740c1e00002c814400c104118a01c2c05901503414410000503402d483e880003110700392f100203010255980e0300702100905c1a035001c000f07800b68208480d640c0c200300e0001002005031412100d950b03440c01500001051284c0038820516401d507005201c4440401d5018441855580500c0801d80d0343e0700071012440c1070001c0c1e0340c0008c01150000984030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 756667176 1250 756665926 756665939
    0x30304030909060506090405041b062708060103080f04120302010e0601050301020a0c02040e0a0b180f060c0d1a040e0a0c0b120112050309090a06050f03010903050301060f0c0813 78
    0x844454024010860615209016641303c401c04d4407244c6d1011030340490745484030f090940940000ba180c9100b00e2003020f40c0481d0382504081e0303940e80c2490729002100050051505580912210302960940c0e0708144010008258098050000c0100400c3e4040c50075540f404020f05000943d602100583d459500c3d204010070140040e0340140000e800075071070034035107440043c940e000011009114681d01d5005c82d2507460f0030485040c90540c403c4c202203c6040c4004045959003c1d1a40600c1c144204011480d40f442c022461310301565120184a0502e0183c0c17442002900c1a240c650911048280b00300000c0c0d55a03015111a200096001d005158028204402401c9098020112100c020800c1807500300d103241032141166080e4050034401550f91500508522503803451951008d611014000c40c03201c83c0e4807140c101c4400f2200001d2415524007030509940da542ca019010860a000400400e40241e45d2852600082d203840e00c40c0c0d003030075950303210584c0100c136801e2000f1412410601a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 756668426 1250 756667176 756667187
    0x1c08042301020d030c021c0c0b010617070327061418010605060f09100203070c0806010509060103050426070f061505060c250305031611060918070c05030c03030403 72
    0x210516803030240402c5c04491030180d034511400c104140744076640b925111130705100307071003c5a48603800584800b031035a40350001460825207100c402c0840b0044c1d00422091802403007000298145000e100444114131540c01c8880ca600020581d907103612100c2020352700880c0042984940d040c401d4040d9501074940c1c1e01c60840702c0742e40105010304420400c0c441c01c0301040003036500f04241100d43c1c6079054074940080f811802200c02c0103000a100d072300c020400c20300c0410958141c84007a100c0c1100c1340e4616004506689098401500d50701c1c141c280d1110030000c0d11248000590004200d610f0510303079955070342c0b1060390700e04181c6141d81d41d003010880ca410300516010061100b1502c441c2000200c0c3c0256444050340c505840307420b643300400b00160000001e00c240115044800d0f2038803080414011714803c1c40d05441110f46005030700d070801961609000f95455140e018000c0b034546414820082182e120252001c410300816801010008400f0002444140c5e5032002440e200d00309480d02400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 756669676 1250 756668426 756668443
    0xd05090d0207091512030504080d05070b0606030c16032001020909061f2703030201020703090605040b18152101060305010e07050a0c0507120b0c07021c0804230102 72
    0x24543d0074140344210b400781c041300c2d401c280e072842000801010101d1806072200c2c4160b40c020320060240c0514080c0907500040a44441c0707000d0284540c1603078404080000700c0c40304561411010b2000e11103d00e0642c807030000119005d10a040100301da6140081043d004900c03151048020ba40000381c0030491706114156030341250313080d10500031404083c00c1c0e0043d1075050301c158804209641d06241d2000903980e81303000700ca400480c0c0c10005141c503824002e01035031020f0419804620036a00002d105840340048a04403150f04040074104003449019001d14a8403641c0c555001001507010702210002d0b000402c40e050031803410108040c001e0321a03140051059000c18203041c40c0c40010810003103001d2419610036010f140143d41ca001e0351100391030050707a10102401500ca2400c02080c0c211b5001c0c0c1c041c0c000c1c0d02036400d4100e1951803406407000da1141c0304009400120f00760381c0304c0c159070001d02002c00c82c034410448541801e45510b00c1c00c0c0c000350f0041c1019982c5001046207551541c05002c0c405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 756670926 1250 756669676 756669689
    0x1516061401030f02130902060706020d14011512062117121602030c0d2a080403170d020a0302040e0606130b09130f06080706170411060d05090d0207 65
    0xc80e5580340d500d0b1111020003607040640201844420000011002d40c40042603da00802c516160011420a08000e401503541040c0b01403510381c00900c1c1454520100d0304848600302c03020214a03400604980542e0740c502c100e40006e407103445c041144004980704c0442031482c00081d01d007040303031030600b0650311441019001c629481000801340740a104232409911440034240035080c0400b00320100d05c2c43c4a190751405880c080c541d015540c0310f034000500681010903c12a0404120503140080617028050b801401640c08000800004080d948400c1c0784100007002d107801c04d0031210b441c00503a4424080ca200003903000900384a03c6240f0882c07240c00440a0f03074114106000061200e40b401000e0090059070100801c40c20304541e20041d46d00c0042120400611181c540005444080d09250180107180d0040e1000441d00c2c80c40b0383d40708a8903401d110b0409003641c445850b40c1304192030320040c04d0741144040003500742a032202c0c000d08d130055000398020045c22080c100001c4c02c140c0c9542210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 756672176 1250 756670926 756670961
    0x9090c0510140a140307030f110906040e0702010b180403120506132c060405120307050a0f0e10180b03060d03110f01090b040c0b0f0d0b151606 63
    0x3112a0780d031102e150301d8060300c0395102d00d035504000b0000f80c80b0311501e111a07012100c000420800601d5150304000b440880c4c042c02406520000070380b045036400b034405800d03001178003400100100205a0035854000c2c0d218000000c40310118804501c0540485c41c0524803050007005110030507611101b4030408101c130200411141c20031000040000a245074041a51910b610781c1d4150180b21200164195412106401d040304101d15017a84620084900365100d01500b07001941d00900c3c007049030702c540c20942d40c591034198000801c2d01d0320f06421030400100528078290703d0a0307071600911b5010110642c0c0351004a05014240750141072050b405c28034a04030148103010550b121300d01d00c484040d170706050a590702c4101c8030140d4541a03162001082560030101c1c00c20a011030456000e00442c0154000c0c1070440d202d01c1c940d00103201d00401c01940006c10130654030841519444020b04000040c80030107080c41084000d403040d0024140380090162440c030141c10041603100380c0400640c45c2482c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 756673426 1250 756672176 756672199
    0x601050301060c06020c1608150c07030503060111120d020d0c0c0308221a160305060901060804050a0b0124020a080f03060612130209090105040f06021c02030109090c05 74
    0x2020ba402c10b00f03008100c10f401086000c10403030b00380a410214440744c1c40c0b00c20650782d540202541c07141030101c0100a031500401050b51080840c0460703440e250952a29891038413203000444009200e8a080700440c0960210941d40160b000e00620f00078008010258a42c8141c1e2008000c407000503105000b4803215500030000250404074103644103115080c80c5540d1050b001d814010f00d07504c0d036402000183e40d41344c841814413404160b5402015040b410390101d4130391203030a42c02c4680680354994042040c600400c0290f00c18500154050b1040040c0c0300510a40d54030035503000d0082c1c0007020450440c008030300b56105080180c1d01c00001c0c0c0d2006009125031503c0351081441b525040018683c0000001602c2d522200101c8848000707c107608002c0c1d00c0c0034440b40041c510030680403403003101c40c1d10228000d02d0050080d54041e40e088a16501c601402d0b035141c000a40c003120303041e08134079000c0c1444030507143c191001d94020804500040f0381c5020a01d40b109030b00d10305030000c0e0f2241c100c8451 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 756674676 1250 756673426 756673439
    0x11040501082a0a020a0c120b0c040807030f2108011e3206040f0608062d0a05030a0c290d0902040207230c0105180904020a0515120601050301 62
    0x1c42c03000d503640144103e03a02c00d540e000481c01c0c01a10440a416a0038804001070440030140000e42850b000b8550b2141d183c48410185649200d144150640365000c02801d01c045102003840c4074509201c2d0000c908072015690000d400000c981caa03800c0414820700040280c3c08100b910f182c520107402d6001c0c2c3d4030300c0c01c104456240d6964a00503440e00a500030705210368045560f40c0751000c01c0000d00c1390707441c2c0350768015843c1041030a001c1c9000180d101008100d0320300b0320340d58a40588031421030007101508900003c504401030501d559501c080c01800000e0103860500c010840075003ea1031f26003805080c10072104108a6050851a984544d8a60354002100181c1680d68100d20580c01140030403c82c00004e0181c01800c1d0080e100a03d880700039201d004401922025050250094503440e0200c2c1006668034024020900c101e100c0c116078a6500d8070741008402da015100600150300c6c01e0311030020039601c04000b60f900780c4e12080040c00104001c40c1c0c1d20001d9003c6824600b2926560500d40d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 756675926 1250 756674676 756674731
    0x408030301090b1c0311070e010b070209090105270f1e100c080c09011e030f1a01170703060b0f030610080708010b07021c060504021801030201050906070602190f1830061104050108 79
    0x115503003291511c074002078050010030b200c001270b001d6085040310303a51030700c580b02e2a40b11070418515000500c83c200100c0300000d11030040c42d0341c4d900c0507114028180c0d5240074144695200281003410400e090742403040b9290b194400b80c1c001c045695001404d0406188020304a03020100800c01401c452400007201d07a82c1320038142c0c41c503101201d440120361503840c03050f40942202e0700042800b000c0443c100c8091682e2102039440341000b110520000c51103183d064500f810b0644555002583e00c8006000c0101c28800500e40284060130380480b03505420480070400034040000c840c000d40729414130056151106200020740c00080c003003101940741d54006841403041554041c00340c0800700d4807e0030b101e1203078151500810404902d803106201004010881e5100301b80080214050144e16843d924801040c4001c0da26101e0903402e02805224943e00380d500481440c01c8038200c2441c0d06000294580121034000c0544400141c940e803d100000d41390003c02440900c002c1e030402030358400c1c7d080b583e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 756677176 1250 756675926 756675961
    0x2e020c0705012604050d090e10060e03030708040f050f190e0c0702030a0308010e240607080c070e04061a1c06110408030301090b1c0311070e010b070209090105 70
    0x2400e10341c925031555408540350341402c0d0983d0500620140c2003005110011403560100e007510f5940e0564107031215088003494205950700c09000c5480c01c01032043d81c0c007a00040070a0b9400404903030400240365035041c03095009401140c420300511400f00480c2c100b188032075118220440b0508541c00c00c0100404483e00c0c64480c0903241c400003004613020f00120400c80d4591034003d420303280050f446040151602e0301c01c0c410b0b82a02d000c280009690325200811251a60084000100c003204143342008500c2d04501e0040d02c2844080000c4150064100600001170400c0c1440d03a8051500c1e01380340040f00c0c51143c09540c4510071000c6244140e5981c0e21a4500c5805518076445483d11406c2c15001022042040702d0b0944e000100881c0005001020314121941280140300d070040400501000700850302c1c8146007443c80449400001e801038402c0750038580c6034011078041650350092094484003e074000c15400e14005203010a50070024170160340611401c4c0244850b0900002c6a0207542c0d06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 756678426 1250 756677176 756677179
    0x90c18020f070605040c0b040b07110603090a020607081b07030311011503020409061b050c061509010501050d14040f0311010b01090b070c12030e030d021c030506040207052e020c0705 80
    0x41e13200141c00c03c4121b1b280c0358090580e24013915143e0380c13a04054107c0d80c4c002d2606a8a203007000d41c03403111501e020403c0301c0c4241402d1020f05904c517410750a200b520382101c5022280607100740680b10355094401214003c00718100d005010803451410302070325449070021104110313410300020038540d80c0b0380c50302c54044035811f903400a480805400c05030300a00700303000001c090040c01c0400c000480d5010001e00074040c0200150344003500c2d10400d0112001500d400b00350815400c60040010758040e0b00074001000d03d260000c20034603107011244645400440e0115030486446105a0038135074041c808080c00e407544002000b40d0880200040c01100e00c91088801000001903031070100285030442600030140840070050740ca00c07620b4041c115085030355040d03001703100b8100c480d51403900c00a1203008200c40b42d080c20740740c421441d900702c002d40001050650059001c112110006400300004040354040d25a0745504401d010f504246d01c204080340100080c1c01413221840c0764030301084100480c1e10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 756679676 1250 756678426 756678431
    0xa0606050922060305062409270111040f09021201150e060d0605150f070803040f0f12020c0307182d0e010606110d080c0d090c18020f0706 61
    0x7240103416036100e150b0344042c0768a050610010401800007006400741e40045914600220750020301c101c520407455440c0c1c2c0c0000104041400401c0c0d03040124004013034001203401445807042d441d800d54211034480202d03c80000b43c10410f038070070a42028050000c1e003006600d00004444203030701954060094004000701842c10400c0030f0701841a010740508003400e11074075041a582480001c103003070301c00c070b9000c1d081d910041448100c1640c00c030b401c003140741c0000508150041e290001c0e030b500014000c58110321900d00f8200495401b03d041140c40703201e144a01200002140300908050039004968000c2c1c2c040078080c880c41d440c0d4040000105144000019481500d140d4420600781c1e1040c84001c1c001066004829103001c0c0c0c0003400059600d00091000300c0d84c40c1c1044900c0c10400c586040319400c021000d55000d8400d90005401208211480d8109581c102c0c80404660240004540e071079117688040080c6c0b40194182d8907941c403021390450400301480a06c078101e109410f0300500003617 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 756680926 1250 756679676 756679699
    0x2a0304290a170a0e070902030109060e190e01060b0705010c090807050a06080a15060903110f0105030a0f0b040c030e0106120506040b130f03081f0506180402160605010e0a06060509 79
    0x803001d074429040e55054001702c840310386d590740c6110000d500a001d403852803030a010010541881030780c101400f501030000841c2d4440d080e00d83c804000d006042d00c1d10210354854000181100e2080054450b03a4084c1000007035012000344003070103005050340031051582050404100560b1940e000c03e04485403410b00d0300c865a1651410401400c10305001c50080040c844c021880950203021401582e1083c40d0000101d04d2000400000c51154414140010000c1002a4881c00c4940042d100002c031010041000c0c8030100004068403081c0c403080300003e544018110b01740100340100d0008101d2401320000344059500c1c0e00c1d03126030000308040e21842c40d1740045034000301e407502c1d024426a00300d600001c0101c10342ca80207101c02c6069a4103295010500603d4a0414101907030b03404940d0020400b501c5c2c030400d41d903d8110510345901d000d41c81a42031001c1c0f0742855824008110151040b071002031658100000a500c0c624040c202d41442450314005110064002c01214030759041110302600c5007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 756682176 1250 756680926 756680941
    0x2703020303042c0705030106121a1c06320c0d0b030a21120b03070501110703061b030e0616080c042301080108030f2a0304290a17 57
    0x10000203003d5144000c41100704861903503c00090340c1610710030b5452a0307221040c6019641510740030980c0c0710041595810007400391070000608040350010240135140340f40c0d5510b81504441550070b03046c241907491030306180f81d07006000c1036020800e4003044030310f50303030501902c0040f20303000f00800600a81d5646401520035601007142100303403076119901c441880c80b0112140641c601d003821110106210160100c4200729902454004a07809402000d0180c98000111245988088094007a028400010000c11030502520101c800070b58003c258481401ba0003c04072407038001620f401d6000181808802201030480c0b4090855501d0025400c0d292803c0c03050071440b40340d20000c1d1034202c0b80c4007011015030781c01071085104000d80315200d05030790b07490341c2640781d115a0b2202d00c03140e001080305010303410440e01e100584406914100074000707101800740c0c6c515401a00111462040041018a00d58171000d40358108180d82d0710842c2400c0c0218405445401c504040c0c0360038440d03a100040360b6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 756683426 1250 756682176 756682229
    0x60a0b0a140f031f2a0c060c1b030306030b100506030103080f210912040513020d060909080d05010f030218090c030723030d0219081207270302030304 66
    0x4100442603101d07121240496101e0040141503171a5400340c1c850803801c25a281d40e240a494144500d03110a0800f000540d030300b100428043c0000f005003c80303502c10703113188904500012642403003514005900c50960070074441c0c00700c00510300c001d101c1001d14240400d0300c820003580c0c111b9030b210701c0707107030b180d8443d484884224000d00c000d003c12031000401d0203603100c000e2010039000d22109026030b407030203448000e03145c128804c0e07005aa4125508418107690780b042a8010708259410703060000f081621a0703100b606850039508161000040031412020040301031250070700400346100c4000d0f200d4a980d020a12000d14100d5005040d0a007000003003001800b17001e00341e610b820050076507240c261112030700d000b480c00845414900c0781d540c00c880051414005450100d6500f0350b002080d22401d00c00b0b01100502a4071400c941143d42800040c0050f14941442c0c1e00038541c41d152102c480740c0241113401c0380000c03012840e442a005100420250310040111006d0b190310140c1511014580b01e0032112 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 756684676 1250 756683426 756683443
    0x1050f07110d030306050906010804171b03041203120915020d0b130c09080a0b0103020906180c09120a1109062107030512070c0b0304140609060a0b0a140f03 69
    0x1005401c2d122150100350303041d80b18000703a0f10100c0b101c0e003181d00d4060044400c2c1c04200c400400032494040c4c1c1101c907440400182180c40c55006915076010b0003a0a00c5045420950100d00080c4150b0b0340f0108058010f01001d40092081c4405c204084860311403c02d040345180b175031810070350f00044400075840903802848260601805214040c0392048054004022980000001a50600303003c41e811401044d03428540741c00c000200560307400c5400b0860361903400b82c0880e510038000041c4d809c4448822194504c2540c0c0d8107000354958206d04144208020600c00f10b0465400100030b117000500d400141d078814480035104410140d50f8038002c6002c081400c01e08a01120904c0083c08150308006031a105aa02c9078060341c0d2a010440c4030034620f40070303212000b400030f20180c401307100c40201c0c60040c6034004c0c001c0d074401b00100081d9021b942081400d03961018903800800410510070070724040d0601e4050b050304c4040907540b80501107181101001c0f2003900c55420f04400303a006a0301088100c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 756685926 1250 756684676 756684679
    0x3100801180c06030b220207021203030601231819182412081c23150103050901060305010e070303090902030c030a0b0103270314030601050f0711 64
    0x21030004100c0124105540d200c0080b614119080030200d12075110f0b0190582c594409442d040000c0c1c14500510456007840000c9200e4a80c00d219070405a070303801305094051120500a1a9a03045c80c1000600d0810403280c00200001c0200300c0d010841c00c100122001c0d1f801509440844044000006200801e81403650400f03e00c0000049510441041883c00007540d490040015402c090a90310400f1850907130342000d200d0313100080110645010442c0703c010302c00c1080b9807070020300014000d00c0e0146150304810069031015075080c605090881024191502e05801c982427401180035244810180000350405465901090110300c09410150140d50302c04000c0c007031042803507607190399007c6510013980022440040002c141d50340b442100c0c003071601401d01600c3e660380c22400354040c101d8017900904169a4035400800b111101e0320b142c600025640d01500d48000508004081c55101c1d10b014400744020024001d0581c0c0110444000c00712085195458008500b44641c5490328000c400307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 756687176 1250 756685926 756685931
    0x60f03060c040602100e07180920010f02010b03061f0b0a02280b0601050a0c06050c0c0c18041106040e070305100e070f050c070b071101020601050111060c03100801 72
    0x1c4080003000b034400d9031216801c4880c0d404042c20200700361020b04042c00c080d504420028490081003110101c10201803100110312000c3c540da880108140c00c01d2112007412415a441100d584d0103a00340b90801050b100a01141e1060700019445040190207230080207881c0005080641d140c0b5240c4008040074202c2c5a01e0f0448070030b0180d110f000e41c84508000b81013104032802030b02d043c11010301c00550000301000d00383e990070006641d25401241a00b0030b00c041000c0800001e030582c01007501c02c8000c1c038009038803040b0048050f8a400c41d010230341c501c5405140043e2160300d0344002200d07845a00500d100321410100000718013140324035000004410010003c02c52517940503004280600b0001c0482480740d5a02c1d590004108810348060001800401e0016089440340000d003440700259008c1e1554185c1e5210741c0d4030141d1240c8021035415406010203551589c05004850040c41b081c01c09a9101e0702a031000c50f1102e00080c46d1f05615140403001c58030303c0220072900b10281c12a01c008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 756688426 1250 756687176 756687181
    0x20109021207031406070c060506010509131406150315011404031a0604020307020d03050c0409020409060504050609041502030712050108160f06090308090303090a060503100905010617060f0306 85
    0x781900c0d00607a01096403440c410300041c0d8911000098814860015552420741012075035494401030040602001d04000781072003079000681d2060400d00c0003030200780740080e10030407076042d5850002c0010a4141704501c0c40e0703401e036045c40c0d061048943c01146035071111420041c03080141e0703401c02c600543c00a040c201080100400c208098000d0140c08000b4402e0301550300c160810050384800c0700c1000041e009110381909040c003a0304500e8000704c1c82800c0e2410b1a07201c1401e1400c0740c04ca81e002c48081525040704010604080c41070303503044030b000d6680204600d8280c031a801107035440c04950900c1503000000850983c0310321400e00003d858403c0900080d40d6400d941603403544041032105033341e210642d000994107541005041150319030f403580d1110070b145480d000480d402c00280707290907000c104200c1d2010780e079002106010700060340301e01e80c6a0900d5003854400036034541200190b01d150800501030b4036080f03c244030f51241248102d2610303a9031800451001452050900c4d050b03c83c0405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 756689676 1250 756688426 756688459
    0x5031f151d0109090c1e120b15040506070c050306130b0601020c0108070e06040b16120306081e0c0406090515031f0c020f0d03090c140901140102010902 67
    0x4002014402980d5004090240a0500c0500780c01005195010034280e48041010310b00ca6080070700300c81001c1c10300010b08046448480384034200710202600040b843c1c05040c06020700b41c454198100317020f9034034150003c2a0003030507180748118003400e403044401040000801914000c5440580f4010303003626803a00740101c4151080007488011200480400002891944001076400d0008016580ea094030f44403180e040e80e030b0961103070800d03030054401c01c804a031310b0030400010420580f21a80c8064400c03224200b0050310880d90141c101014203005003000321550006a0109410f03e00b41007401040da184d0303d9520340307500241050782045c00d000000901c000c1d258001c030700c02c00d002c40303d075115088203c0405490381449120f111004001008810012800e0b81c01410500400c0c0111010700d40b520801c9468030600344400800a926000040100302d07589800358020419608155041440580003890205050040f100781400d003641320318803a0302c00d4000103842034015008421240f004c1c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 756690926 1250 756689676 756689699
    0x304031b12080f010b070f060c0c0501090507170708060604021804051314010c021b0d0506090c01120c23090a0e0603070e130623010611100e0a0305031f 67
    0x12a035a50f2004400000150340c81a142207424965000410124980d40e03a90340000501c42245480700700110441c802000030400d220740a003123030081c00180500343c9050214900744210002c000b02982040d18208103610000030540c0c0c0091007190301586a05003208040d80ea405d9552500b075200e030a1201b8480c20241ca1080c52548900907a4400002038666440c2d9003651b00d00382c813440050340480450303c049050b01c20036024410006000c1c1c2640c4400340c450300e10385031040d1901501500604015442c940c1c025102590300011010b05101c000420750018100411540446000e054041098aa140d018030300711150310030014581810203445e042c2ca04000d41048030514080e01c2040000305c1c0e80113034074500504c5481c8640607558041c0075a600d000151000403031108510349112002114410a5001c1c00d0182c0b0843d95695a0b20040c1041d880c6041242090560083d1500b80461a1030001050012540c2e4160500320341e42e03240c031070400c480704c601c3d48800e03140103841d01d10210b041203480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756692176 1250 756690926 756690931
    0xc021003050f240d0f02040203010b1c06060c0b0a090819110616050d0204212307051002030409020403080c15010f050405040f20150702060304031b1208 67
    0x40e0510440d65049035800e00c8403c8280d20304900849040211803a1402c080d400300c50b10710529000b01c8040c1641c3c00704040c0d0f00f0a0f005034516400104002401c0399229000c80c2c06510810401e10242c0e1408501a080380b00000000d071001c0e035800009001d0300c1898016488480d0b10101d642c0e540d0400300140c068108117070850710f00080601d10a50840c0d44009255802000300068000d511425200c1c1a9010340c0f11100058809800b80320018041c841c46101d00c0e5200450013500b0620030f624500b000340307a0b010740710803034684a000090000d00000041c050043d2407050b90804201d008000c1300341e241d409190b00207080c650000030044200b02c03020015000e90300403181224044500c51103074201042e0240909400e0030031041040181d46002d801244d0801c2c000c034585404c1c2c45031a15a1155503502c0c1010f00394101108068001d00d040040e0b02482c40c0340e034250000c1c200405540091a2444042d00c0a02000704110f1100e0012041140c082f1201d58000c1c00150312945424001d842c04104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 756693426 1250 756692176 756692191
    0x3051f0e06010912080a180807030803100b03100506031e0c04050102010c08090303190b090f041707240b0604030b0f010501111e0705060c0102072108160c02100305 72
    0x2200000a00603494001c101300456000e07280904107103851600b1a03a0908004c2d4000d001d000d803030b00009041e00244400c0c80558000c82085a60f1300d000d62070480e00388502c0c0e00441c00e5140c10402c21008035034032541807060b68000c0314402e903251100082e01d458020042075242101e40c00109010142006c03d000b0011240d00b07070002e0144003444042500e105100700ea031074100350820400100714094038040305101c03004121000034691100004549034460817a101c842040d8110240014044000201e00c60b99000c1c1c459a854000e1540e03484108100340300351120b030036520451604000c202034000c000280c8010300b109840b40c0e6070341004a80d0000c10f55401545401d0340d0700210f1103503c01c1c1d48001c40c01403c5c60050200d0282c94030380781400100303607101d011309000b4503c02245036580c0c03030300030001d00d05039000258031b0b402c0c9410034000380e807a2000545650f0326454194011650014a0107034003490002c4042c010140d0003200b50740803100e05e08000d600c417a01e80b625074459605544402c0c000e021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 756694676 1250 756693426 756693437
    0x30b062a0102090d080d06150c0201030e07120807020d05120307030509070b040527091515011e1b030807020f0601030302210702130b10030b0603010603051f0e0601 72
    0x1105440e1908030b10a4101c040e81090300c03181c4203070200d0090002824054070b09000001c0b82e5640d40220040c0140b0819000000303403000c002c000035903a06020312500030035680f0140c0f403850303e01191300e82102104600104102c070040303503000566a5841d4051709641d04281a00c00803520041002126801151b40c0c1f80828074010200e40061320019124054403006940c0030324190800c010000820680d140906004d62401298000004207040242c003481171381e4000c0a6082012031814440d800040c11074038280c2c496088952185ea101c00d900140b0807503981c0c4604105080d400443d9008801044240252190118030b820598484503441c0b08020983c240e40c110710460030003070b480d02c00c28480038005910a500c102c6090811064415010804001e40c5103010f000e40c5c08120080c0c05069902c20003a5100c0d0314400c0d03402e004141c4011201e01e8a010042041c0c03200001d86a0f000600642c0200360741c5d5000900b000d030340403848010b4003d11112188a0341e0744c3c0c4422101d0040c1c1260700b10300091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 756695926 1250 756694676 756694747
    0x100c06050a050426040e060f120f01110909040f0c0305190606060203161401090c080706020705060a0207150903060504061b0e03100903050f04060e04060b0702030c090601030b06 78
    0x144c0d1451500d12012407403c55407a203803800b80301100000340540700f5940607024981c0c3e10a00c2d91601055543c0c0765402026100003a04000784070308645001034092010032003001030102599035400811b500c41d0b8461184640700c00207040441d83c1014942000313206209903000b00f80003506a1101c00d100701d01c01d250901055846500c02c07600e034002c0d451072281c4071a43c01c8a106c00950b03400045200d1030340420001400003455280c83c0d141000303540c041c80254109a07818001554144500c0300035100a41e0683d250020040000359a4406846101080303202914400101881412200011a00000280700300e05040c2002c04c0207050b06080444014140447c580200340078882d12081001c0c01405004041e8442c00d03040b002d0710051900303c0800ca0300300801c11400c0d8052007d440600740d241c0d01c450340010b1017018001110065008141c5030780d000d1100100680e400903068104840c240c802014a480e4a030058000c0c00b0a0804583d02040c007103886680303489041002203240803aa140c50005a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 756697176 1250 756695926 756695963
    0x108120702060d05040212240f0c07030809011b0210050a06060c0b041a090d03200a11010e01060b0c0c04090f020904030e2e02010e0c100c06050a0504 66
    0x500c20100c000350041428400200894003d42c0940c0d8824000b07050398150220f40c0344500c4c205400440c10350178020640b01c038491079070502d501042d4080b80030b80824416003050028001c1038000c00500034100700300c05001034040d0f0402e4001c60506680b80000c031488c511030420203501c2c1c0003040c0f500741010349420300042d000c0d00c29020704822913029031070314030f106ca445840d42000344800400035070760314064080c0008503c0345851582c0c402d0352200085c2650540c1d40780010150389004441001403d000d55429001800c100b00729844044141441900d04003045201800350011441d10010f42d41303444000036006036007000900701822200250381e0280031940810045840c0040090886191880c4c0c5000500b0451b0301c0c40d812501904082e00301d030004134001510112075021090b0703129001555643c54403039124900004c001e4500092240300300c8098480e80d20316002c4510ba21440c0400102e03032a46010b51041080240c02520a001603d080240c080261105a404440c000704d602c0c09411607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 756698426 1250 756697176 756697213
    0x90624080f0115140706020715110d090201030e0f0d0f0503090a030c030c0b04081b0a11041e11092701060e0a180b01020c0315011a0717030108 63
    0x28000c582204201c0707900f4005070701d4504030244200002d0200404288104035842805003407214801c1d000503039284560324002c04010b808240d4600c9542c18481c980d250608400309541980001000c0007a600302d241c00100c01600f0709450259281c01122445000720b200030801d268408005c0c0c4847c81031545555080721540300403203188110782c00002c035500c0001d11075400076a1312800b0746000c0f1103000c0151101d402030b2000f9103088905c070000146075200302030003085034400100a1006041203900c5030319552404c550390b030b403083d219a544200a0118100458206550100c850703010000c00c520780780344c0c002551103011058861046802d43d500c1700c94070740010111f0720311040e910400d0780c0d20f045c1c0706507004081d0030902e941c4100440d10102d07160310118120903000ea250440400c060350240000380c02e200780c0030001c0303000e5082582507809224001010504403480c2e800400c90407100486461140c0c0a03c000c01408982c140801c0045400000043d41c169001a000d40d40d13280003001240c2032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 756699676 1250 756698426 756698431
    0x11070f140c030601030822060309060b060f1e0d09030c05011505030d03020a020c040c18060503160e03010212010807060e03061b07050f0115090f1512030909062408 72
    0x180b6074844401070000502e4200605400a08150690700c442620307600303800841c106410403c006a600c1030450300b40400c42c0103081c4180303815a01c062928550712180f460510420601410451240444e00031200360401100c8480c88a0682040559900d1400a1600820b020103031075541c00d041515250507140304604044840080061800c4100850150043c2d00062a10815801141da1600e031946036030050b5440300c6029078544a40740082d049030a002c4402d50804000c01c2018002c10090298030500854050140d0070f0903a082c4403e1310000b80a84500c2c0702c86245904540d00000342c140c400a91001619025200d49062605d0f540038556202c1d421104a0f4144850705440c03912015014001c0100710301500c10307945101949030500e42034800240c00704045400b442c2c410004e052030780c803c0d0314074548400340500c12007400700007900fa007640c5030280c07000c1000610034480815010340f4945004000090b402d0054903030725264017000c1c0e002404000c9107010400c1c4101d03141407103000e0891 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 756700926 1250 756699676 756699679
    0x13030c0f080c091e1f03030525150207110a0801020c1509030912240702011a090a0b190f090b0414010b0c070f0b0d0b01080103081c11070f140c 63
    0x82042100061400190005000541e181443c0c217041d28130301000008240181d4060348480742e9440361040802000148110641070084050f100c200c00a141c402007601c022402031005a11240745041940f1401e4808640540c4000c2c0003900041246064029010075000361090f40c60482c100e84000b0b50b0180c00702d9150545410801c9118814603203046019210b200e00f0301154041a20420031072564250000d40c902401100d20401011319424080c10f41c114500300c0801d03403680b00070b0700852440b03400a00650b44540d01ca00d1041990f843e403120904031118410388866480f60740e8140c407035003140702e03008002c1d1481c104084402281464058030403a071030a40e00300c03a40d50f07280c080815059080441c800d8404c0c0500030001a030b9010b40c0e86500064031211240b550355115400c030358022203e160511a05000000380104042016081540d007003c520846007450701001107007040080107038038985003a0b8031000c200c91043c800b10f5120010f01c140b1030100210854103450f01e070f075921866107100d04d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 756702176 1250 756700926 756700951
    0x1031b09120311060405012007030909180203122104020907081b13051f1b0203100507030504200f1c06050106180617010b13030c0f080c09 61
    0x304059200341d120840042d000b80781200b0311a03800d041203410008296020340f00b582d11001000f15255245480c00d2500c182400700c01e1415025a6000d0500c8906100786000030356a640c108a4441d4071b180103a06403540201a600d952000e01c58100e0290002100d203290f8040c0745002c1070352520040c0801e07010365002007985015075600d4400710b90101d40141100c00500d842c03040c4071000c0c980c6030080d15800e00d80e40c543c0c2406500308003e11218800322a18060300382d42040b40300c5000d60300300d850000c030a00700b50341c40c0300d500301d480c000300e45050b600f2107040c2d80707551a00c810072540039419449280110300c144900c0c4211207000030b41204041080703008a9110b6840440600e0501d0040c5101215204007501503414400c08d840c0d80c000c40d0000d0344604003042c20300b0410741c00d42c08a802c00b24050a000d00706010310903042d004c81c44900d0303014041c00750f041c034000031400750401e9100c51800007168030100c0f0450317154440c1d241d0b00c81c40e265880f520100d8440c2e1000420300e450142002d0f803080c108a13268 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 756703426 1250 756702176 756702179
    0x507030c0209090c060c010c03110f0a0c0f05030316030b010c0503180a0305010203130b0a18141c030608070602010621080c0601140f0405060108041b0e01030c030201031b09 76
    0x821580520203003400100b8842c150500c00c90740c517641302070510f1205c60400050040900b030006007d984802403c0c0402000c10014140c1507005401030300c0c0b0742091171400a140103414607006041190882016040780320120401210910070300d43c00300c0c8039a46a07010b0090580503070066800003402c1c100184260018448c0172074104400c103640c0741d4258000d00502840d6902d0300c03000c3c2264000e441002002d210b12000c80d0030301c02d0650000b81c02480d0031000b00680130f0040f404d060b038154042402401020000c554026460b0200302d01110240222036003600340342c00c1c941c00b6006004601c500748640c0580c0b44000744407401841540200c451804041d15080110040c41807040a87d03001181d44190900140091400c08c2040502800aa101d4800c0c003040c8802000150410804050f2041d07060008000007a60f0182d0f40303c1d040755229030202c1500526240c040d46c0e9144c0341c0c202000e0400d00c05c000005001c00403084504490003070b00c0401450b4600131009503007500c04c2c00e4210114050540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 756704676 1250 756703426 756703429
    0x606140108070f051b150609190b1203030a0605240d0510030c15171e0601030e0d050702090c040501090b0d1821030e0c1908030f030106020606010507030c02 69
    0x103c1d500c240d401031038014a0244403100120b0303402e4001c214621151700c20981d4010000b0459030260700444110703048082807800400744500316010070003800d443c80d00c13080803902c0e90301c8440b05416500d40b00c40a0703a44900c1c00c07001a200503c03003489a80c0c03240c482581c030b950100c0b900902e00d1071050100d0000526002c0060000c3c1c01600300a001c0c000c00000f41c00c0d00002240000540307801900b000c5000d0345010244001c001d00d001c0304a6000340c04000341009010640480007044204c0d84c0055840d5402d0b030707561400580013050355444000340ba000e1000420130b850f07881401410030a00c200c4100f0f4640d02e45c140300c03640c54001c6000d56408280215070030700c145585070001d0038003011140008a014a220110100d901080351800c43e22510400b80c10382d008403200d036109105204a2804000002d401816140d80760701d2141c240340a541c01241c050226010103050402402c0940201c0b50344010300131000c41681d109105031030040c00b4030b201040b0700d50301c603074201c8440076056920085600020f40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 756705926 1250 756704676 756704687
    0x12060c0f0e040b18040b19060b180a0b030c090910031a0a0227120604081b0106080102070b040311011103011a09220e0114012c04050604060614010807 66
    0x800090340140c0510803180302ea0020901c4174442d62141b2002c00c0c403030030590313040c02283d0085144010000d00f8100c090100c6070b400c0c01910b9603c0703086100940000300c282e012408a400381e42020007036160001c1008002d41d902c000424451134107403850032559545a21041d00036026020062201d28900b0315041d003401980c1510390000d0085e54014a0020000245407a024a42e0164184100c10800e44e04140c90500a00c048100d1480c020304160314003030380c440790035215240c0c1940036110300e2200d030321400c502540080003070003c81c0001c40d9508054280944114021501140002c0001c4165400c400c4180100e906018100c42c0290a603401c0030014000007a850006110b800d2090020329455501c66003050009803907000e00c1200c000001465070203490300055070315441d070b061010401c291454905c1c4a0304646148482c40310590410304501c80c0c421580b40c601f05210042c42c14401400b03000310302d0314003840c4251400c0045035990501c8000c1507251403040303030200c0c4801000514203401135 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 756707176 1250 756705926 756705941
    0x20c210c01051b15040201080105042003070512130606080a240e160e091f09020d150b0306150918120c0109051203010b04030f0c0e0112060c0f0e04 65
    0xa0402c90650b14034002510700e01004c03150b071000c1951891090000b0355070000c4440780500400d1750709228401e070b41c4a112807110a40c00109080c41000000034803100e100d641540d0001070300a1805a0a0410007400707488041c0d00f800580e4070754030300100058610400940e45a1151b8002001c920150281017200801c05210a01c04500c0707803180407401c1c0c401c2e014402d0000da070030607110000c1c410b03040070307001c0035440e800500d550751a0340042030055215900341b09559015058070b4000c1001d881510201d803e4210346107000b071950b4000d030f2040c407041c5016000310401e00c0042d070854001d550740c0301e414800000b00c5401d05801c0310394500480c60001da240c501c0303070841c0c400c0301c2110304041802e200b090569001240d16125a5911103410040003010300460403000750045d00d4604550405071244041e10907032000400350490b01140004201440c02408000d141e1801540703a02c0d80e441d000d58994840303401c0d040ba50706283c046032400d0140074810080d503010542c0e40e0415085801700512001308400d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 756708426 1250 756707176 756707197
    0x3050d031a0a06110607230d0603060203090706180b1804320a06050f0909010f0c090501020d0804111905060a111b030307150b040606020c210c0105 65
    0x148411480c5441c0e0319100c074014880c0780c1e151007484c06601c80c000d0803d0300250040e82000401c110300b0301007000841d04110200580d2036500c1d92240482d016000800c0264001410f982c000700c20403a0544011601700c3c102c9905445140e400360305c000c40700c030b16550503006401851100b4404010810b0140341641e56400740908001510340c1d45500d01b0450403c1c41500111940a0364041a040071220300310301c1c2c01a00304102440703020b040100203282c0e5405250f2141c003030280000080d42072402500320a12380301d01500c080251132845500109041d12038020507025120704040084118031600700701e4411508500f4240700740b07100c0d60030004002601c500c0b089444141c0100030a040d0b42e0b05004280703110494581110074400b0117105810906c07840a084100d003050180b103841c5840200031502410342c4140c100c522405e43c00381c110300901e40c0054050300701d0719014001c109030360005000e0800c01c8007204c00701040403003560104107071080c1d9800c00440c1d400c06407042400c0c2d4010409031032070110b03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 756709676 1250 756708426 756708461
    0x6071d030610050418080901050f04092307020318040e160905011a0a0c0201200f070806010503071805150613050a0b0a0203091023090405090703050d03 67
    0x224500020700d8900c0980d40503040c5001d03107030b04000510b4248a2000c80c8002452158410300041e100e0a2441c0114a40c441c1404000129072001c0b480d02011200501502102002099404004100108000040c6c2240e9044120100344864000010b50743c030005502000c9100511000500015015004500c4041c1c0700d4544003807082541441810041d200c408000031361585007140d51180c0f516404102c2002e0201040344084c8568070045000b00c1a0b02070078100032900a042110340400c0411030319030740c0e03405094280700c0f400501040c070720120796401c000c58010740d894404043c2c17151142d01c143e40d941c08580b407440596101580000e5440903001103070550b0a981c2c840460210351010804a80d03211040c030342401207180a0180300082d01e4075910160405034040d81c065503070312905d662a44220103800a148215106883c190706080a42048500440714600a1700c01a00200805407056080800240003008001007240440e50072600901440362408000da0041c0842044402286d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 756710926 1250 756709676 756709727
    0x10050f04020d021f2d02100513080705060907090b01021f11031312020102030103020d110d06020f040e010e04020607030f050c01020a2a08091c0b1e0f090607 69
    0x20b02401601a04145d0f161400c461041625100c0c0200c140b0b1103913500c085403814a06406980002c0140405e00240c10003c2c060f22550a03080540048100003040300e40001502401c000001c00c4140c06404610201c0700955191884001510200d420160060380415083e0040143c0d1040460100390010400600402000d1215210340e20072105600941900c1040c1820891030301d07564135003c08644021030955056500240541300b00140203003005500598081070366540e940100421648003100310b507515010032064038550020b2207201c2401c0180800020748030302c121a2544641c0d0300605007031070014183d07816178403045020600700c01c010090000301041002440103040c816403548030b8480440804009030900000d1310100080b401d030641c005800204028155583c1ca40d04440c4000703289142e140c46c0e070103083d01130740c06031422205505200d40f40504a840700d130075201c81c10b5003c0b25503813034040b0001c4591050301c10007540e50100001407941e82c813a614610064850030514800c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 756712176 1250 756710926 756710959
    0x10090f0606030302030318010e0d140d0606080105040b040b13180c0323011e020f070206030c030a06120302030a0810050306040606090e190f0c08030c0309010210050f04020d02 77
    0x96080d50001c6026910000501051107818241141d0301c441e65002404081d980000aa44a20500130101d040c807040e00c5210840701505011340709111533010307041161990703074000103108003028803030075000e80d1410b00b078440780303080c24090741c205000e024214000682c5190640001000710804a0601000c0d26043c0c000240d48600044e0007107006000c0450080210009003000300d030402030605a682c90030000300003210300d206220040b03080ba20b2005880f6415810943c91034403c01500a50100f800000c00150b00b940002460203070305202c50810405448801000104d2800c681c040c0140e07100f885040906407160010580c04800d0002c2240c01a40e40c0011a1508400740c4048411035203d640c14084d106540c451000860102401007081042c402c0c56209000d60707807640a44001040b00201062196141c41c11004000440c200c075030758203102d011541c8981101c1003690042c000d500a980c001740b41c2e406000e0044803c01d001c2d00c229201c5500b00444101900012600084030780741c0c9401c0e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 756713426 1250 756712176 756712181
    0x150c19050c01090906051804031803051506030109170702030a06020f0706051f0608060301271a0114102d17010b091003270303051810090f06 62
    0x25114400604000101e0700001d0049141500140c80d0145000070401550f91030303151030340c3c5d18000120721242c0c40d2681d06046620480424198440300c0501c14004100000000c40541d00c070007800100d60035031160710405080e1244c1d82c20190640007103c1c90803107610602030043c640c0da440241210030015561b0349074000d03600140c58030607680c81c010903c3d0051107070a008590344016011139a01c900e0504840651460030113000d41d030100310401001035a951825406101c0f4401f40904040101744007041c4c0809800c4014811100d403200c0412040d00c4072060201c0c03134181c130351011031070301c80000d46c80910144112150542c000c01c12003041c10310041c40c04010f1120101d01d041e414440070b82c040800a054454501108400f401c0418010402005018151003a20701c1c01c507000014040c0515044028090a20280000b02c400c824003007414065040311100640c03294909000c03c3d03a9018110800350700035044c400301034011030840885030980754001c4100034032440300b816068189845030000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 756714676 1250 756713426 756713473
    0x604230d0509030609060702060a020a0903020307091b0908031905070b1005040b1c030f1103040f090f140106260c0408011407020c01121409010c090f05150c 69
    0x407a000189284481c1001c0c883c46911200080c002c0905040c5810b00941d101c100425114074150b0110341010f08038400c007078030300c01981c0007400c0381c1e8540e868615850085c015401c2084c0e04818850f030f6001424041c105203800c03103600d42d02031410065511502d5000740c0c1d00311281c41c1008020070120b00000d1401108601810194802b003c0a50901042c8001ca684481400d446004542e105100080d034000f0b61080c0554107207810140c85901c0c60040c0c0d40d00c0740340c01042c0c0140c0004075012032103070039035800d00003101d141c2d000600c5058803a070408011601058454043c2e80c0c4401d0041c000c65009160160306241200c0e24000d01c0000b050713141c01c2142d41611028883c200003d001c014251302401041d076803282050400c40d15003031203d000380d41d030030400d01a82d050041c940990450b004065000d603000ba03542c3c2e910440780e490f081c2811402403840030042400300b0310001f0040303510416180780c1d06c2543d10107481915604a22003040503250858400103485218201d10744109100484004c403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 756715926 1250 756714676 756714703
    0x1b0a030227040f110409020901020c0306040302060405010b120d140d020406020703060b0a05130c03110c0c1f0e0f04110c0a1e17070f05011b110f060423 67
    0xa8124840004120603925000b070800111401c01d002138104002e641e040740e048900c410700050f590015600141c2c10684000741884d45030103054108030a040c0c011030111300c2544980001c000c8444003004010401c1000c00360801d01e82d022940c8030071014007c400c1701d407110320700141c81800c1c4100c041009090740d000d504240e0050f04403210070001c0001a024441080a0403079101007041d0402c0017090401140c89030180748952902c80340360132507003e40d01c803410780540002f40f660b030b82007104803265450340301da005107016201e01300918440800f2041a001ca1506a47e00d072102015840c003000b03148281a00d0603580903a481d00701416001d05800140503080118004c0d024180440c203042c20100405102691140f0304080700b0800102d0703084501c805d00c00382ca005103441d03081d14140366001c1d2403641c500400130b40c80e0092281502c5040844203045179600e5035203901807610340450546130390016504150960110010030300140c0541540000008007130503103113032040882c51b41d5142c16194130103c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 756717176 1250 756715926 756715987
    0x80c0a03020f060105280302041d06060f060a030902010e060d0510150e0105030a021204230a0f030c05160609140f0f090a1401080d171b0a0302 63
    0x30180c052060060758040d03940a88001e40c503105c0032904180b01c03060201480d00706501514000c44490b1543c1c0c020b181c0252040202e5200c0400010b0200c00c1241011240e01c1540001030051801c50403468042c03d0182c1000e08001821100360041c02000034100e052000b0700c0084c59864556501400038416103400109d5a420145094408480743c2c2e0000c0c10030f04129460002d045800c83c0710080504400c0ca0840c0d0399543e00c03800ba1000340074508401c8490b02c910000d000034481d4500e103000f0581c1e86041b025640c60340b020003496840743e0f0554010988010052031101207405091070381c500c0380c002c1c0d0507141b00f507440e550110002040d60300000049000c2c40400c0c031510480c000713500d95801e016144034844900207400070700c03100e8042c80f526105464010008681c41c000f0307008101d40c0302e400c64855405584078000b49480e411600c1455000810840d641f01c00d500508404070b001c1c040100c03003c2d1854140f42e4903201e65a2001201105254080040720300441d040c8403070004a00520044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 756718426 1250 756717176 756717193
    0x14030a2406060207060503151210092d120512070903030e0103090b0604050a060b04030503041a19050304020d1a191e090203010f060611011407050d09030c080c 70
    0x31021914181c0100c1e007190b0116106110325900141120342004c01040403c006036982800900c24429a0442e40414026160f44500c4c2c41c1e516008084103078030a10240300d03c001381150900f6807031880340300b4407501d00c1710251003401b00b0010464000e01d0903c0385461460904050421902d41a043c0c400600007107500c4404c2043c5a03000c5410044090240b800384148080c0d500c5811110300050700140c0f050b59141d0100303d620755581d001800505280c0300c195100c9036a41016500d94005100d02c280248050003e0380341c12100744101c580d00149690008112000840b0860b89904020412600240105014004260a00d0101707024421000820100b49000310420140f841018584c1d40c01c0c9041001c0c070386400100da42e00448424a00750002201403480c00040d0141072627105024800d4545032340130900981c400034603c0110354240081c4580c8500c1000c60759559400c49655000600c00e201110300340b0150b0f00400c030641e000385030031128000b482e2140c02d107a50242c0c0d050449079001549 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756719676 1250 756718426 756718493
    0x12040507090b040b0105040e070c020a0b0406030e07030b16231b0615010e0301090605130c15090b160506180705010201060e010b0f450a14030a 63
    0x141c0c640400b81a10280a021101800603005000d54054a6080b050f1b010001d241d442c0301c1c0c3e04a03890180c00070072801c03c50780e0b282032156441c5e119001d01030000b0304080040415a80c00202c03142120307800702000402d69102d002e070b017407006070410101080051015040c85c3c4807a0045000c0c401c074480703990075070f40d03041d000300246003101b1038415094403604000100f021950344a40098905c24081c20414480f03025540024010f020110300105102c2c03500040c4005240c030a98a40c0502e449a5a00c5101d292507002d00180100080c2481000403205035041c0700302c00461014001026500980089080b1907607030b560305282c1d0844001c40ba1181c80290b40d0114501081802c00070102030008100250802d160045d114030140520054240c0000d26a940640d500302201c24071141c0004030044015425140c41c5550041004d54442e01030b0f0002c03080d1810109801c3d4020070310004c0200307041900d800310495000c80c01d081000c0d0b050140d290b072140400c900b00b070009600d034403e080d002c1d0a10f0b022030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756720926 1250 756719676 756719681
    0x20c03040f0b3402102015090f0606010c06091202010b1e0603010306050414160e011a030a0905031c0e07120f0b09120703022407020d030509031204050709 68
    0x50007a80503800105460b0407142c00b2014550072643c060314280003c0302c0001c4140c07051010164000c4c0c9504c24408001b007100404542905250f040d290340e41041d441c0c14040303d9558615002d880303080d42042d004110b1b65070003100d0b9080c00c14030400e404100c16040c0c1e102c1c6144480170304500d0300941d444610201461505000c10201d62824106011582a480d00401c10b58001400000c00d001e94510125052001e054010700250301c030310044030003110482441c0012200a0301ca030303100105d07250001003407210056907486001d00001d201e10342141d613194121b00140401e107600b0384e0640001c00c81d60101c0c0021722034802042c0c40030040400e6210200303051624225080d84901603003529007801e17000190f2031041850745113800400202c4d003a101c0a403040e0400c003051780c00600c40c0c240090309004154001c60f090020303c1c81304590345081d480440c0708242c027801c00c852050050b000010846040c5020360b000030740001c03101080b80c1c00c24000820711030b81d40300d0581e401c0d1425407000804000c4250706c8e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756722176 1250 756720926 756720967
    0x10605031b0a0912080409090c08010c0c030c020d020a08010e03072006031902040b072a030203030d020a021504030512150d021c0f08041a120a020c03040f0b 69
    0x5001c6203007000d1100d0042c141d010380d004510006101000c02010b1107426030945010303012940301005030f81a10325013141c01003204d10500a040d400c00b405c109401c1e01170000c0b6a0395940640b01c40001c101c081c0d0800c4075081058038201d03404070f14010081240c0c2824842c004e100c40c0d80000941c1c2d50806d900f0100c04600c4603034601610b40a209005261540340c98041e40d420140119400301c40d20860b41c1224068043e0b42c0090380d045401090240622802c0720344034602d100c0140c0d4034101074840000700050520030303000194050388204000f81c03180050364007c2103401ca8520664520301740e000307a14150201c0c15201540000c002141d0a00b8190b000505144c00880500b2000d9503a4030550103c0c161a1850502900c140046801c0210042c40c110008020561100c01030011500c5460000303c5a0090b0061203919503104541c0141b0303132108401c80c2c00741c28061040c0615039840d060844080d5000340c42591040c0030912000401148202c048006041c80c1a9415143d170b4400b00301705503201c0b14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756723426 1250 756722176 756722221
    0x5010f0e1e0a05071205030d090b0106030f0c090509060102010e1605190e06040b0d05060f090d03090b0c09031204060801060305150d02040b0303040f091d0f0304170c0901060503 78
    0x11401e00e01c00583c00041c06001c80f480c503800e0324080c1c01035080c20f60a6000302c00b0b0360000c1a0400f81c0070800c1120200c0d150707050700e190b034800301b0280d591b1b451000c041740c008a0004012456080c2c080c0400d02e0126400365100d4414030000c504140ba050000381850700c9003509500303042c203208080c0418a000030740524603403403500070b403551380c0d1400300d80f85040e2502070300e000d000329550f484e4040c9684603910118642a0000100c6840b400c0c290009000340e01c003107600b0300080c01016002020184603009080c0d01c1d1341c00c112980d1103621180c043c88400e81c400c0300402d5040c401c0103801c0c113407050745038042d2000340819152104150715001004d002d8901c018405484005003540092403580e911000c0000d06405507000150101c81001103031a51081e600109443e0b4181382c0d00003080719140d0000003100d10303d0f00d4403c2450403140d01641e60303007203601d007d0440c0da0020711090010ba0179600e02d0003648080c21007240e82903450341c00461803e140a070400c100144000041107014107120580c2c2802862 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756724676 1250 756723426 756723433
    0x12060405041e1a130303060e160e0406031a04030e0427060b041505040f050c1b0c180a0513080406180f060f021b06040605030405010f0e1e 61
    0x2420b036140030390400d01007001d541072a446150325003400322206100100704074050700151141004d610000d801200e5140440c0024148140410102c01c4080c60502980088420312800c111202c0e06445640c0c5140320035410680d00c1400101081010382c01e500800240e00c0955a14141410020603010311038150394029420052280d80c0700020510449074400c00781d02c1880e50450034a001c0018000c40c0f002070354858101145070603498181000101241d00c1221704202c2d0b142c45498400658508980300c6174420424001041d148211280c200d00d03c512000a498501020030001107001050b031245da0715240c076940801c0003428007480340c5500020024048440c1910b20b58603450241720300e000d4101000507081030617004400c0240310001404001c2c00c3c2d00050b43d02d412005180101d40080c900041c4030720b0320800da00307a5050a1440205a01800c418902401d0280c182c03003d91018104850941d69099601d800803011b20454401d00e0719900584041002103895818146032120740044580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756725926 1250 756724676 756724681
    0x3140109030e0d0303090501050f0901061e060f050409020f0301051c051f180b0702060105060a050d090c031e11040212180a1209050a090c0c061d100212060405 70
    0x250040c0c0d034255080e404a41c1c4143d158541c1c602100035020041d0010070560800042c4907524002d89071040c030842c1203000800800c1c0d074420700703417030a01d40c00c0800c0303803040140c1c0400740052841070144504842d00ea050413843c003a520312050041760b001c42e60103444a8000700041c8010300d0505003092502c101040e22490307600c02c5440f1640c481d00c1400d044030130070742c0384201c95001d0000358000c1c0d2149010070a1200501107142005084005c01f221400010b0140b40008115442c1c0b09081e41c0b40e5504544c0d0f41801c1043e44d006800060420501c1642c440d503022200000003150380703c607403088a680b9654818450400c0c0751241c1403200078280300d441240140406032003004c0500c2501e134407003280364030802c1303203502c2c00709541c00e11441813009000c075005000a010755070f80204410003190800c2e00e070f50a509640300c000008441828030a940080c06100c4c1c00c0c0003003941500102584c1e0710041c0490f0039030690300c01d000d00d0030050520b103504081d00030403076182520140c1e00244c4d1000b820359040c03020b0f2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756727176 1250 756725926 756725933
    0x11040803120907150305090c100903080a1b080a0206060609130504080c0a0b01140a0f0e06010e130605031b100c0512030a0b130c050307050a11010f02030103140109 72
    0x9014022041c0085801d040c0015040341c410000b0030002c1660f020480071040399072070004e0181c042103840747c15034403c003443c0201905007140e100307510b144990395a001c01d41c110b41e40e0703013010343c04995000100b009411181c030b040b400c0c114091034194441e030780c2141c0c1c43d2503503c000303418140d0081510344250401c2c0031f000d070503450703034241c04903d01c030400f41c0051203664a01d0130302c0ca20700803420394051501c18444408100a101d54034941070b180c1210000240011036000c0010b42291802400c48400711100304014414090a010740c0201d01410844010416a00410401e00e2a49480714400ba200c0d04c04020702d00702407282041d8460200c542001d465007820204150b442c1c1c01c180c010811036418482c41c1409806c3c00f520711003a182e103000c0d9542e81448030303e0402402c04941d006114101310482d81e5243e152520030031681c0095a1502d50031980d03021000d94071900001e54210034054034000d400c042c12820b200e0b4891040b60008016104d5040d4200149110621003848040c0c4e8074040460010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756728426 1250 756727176 756727183
    0x7020c150c15062d0d080c070b030105121209010e041d06010f0f0f140102340e150411090d0c06080702070612050a0b0d03020604110f0a050f06040305150406110408 72
    0x701e41504e05502481e03d61501b501144200745072030780e190241d6140410070449820040d81250421926480d0342d01c50010700540702c43c41e2400c002a1244108081003482d40600527100e4207a000500c0019480741003102c4540c0fa25101d9040d0711141c00840040c010402d40340e041c2c9010306003201d8404078a9003841c20401010801d030050443c038201a04e900000d903031007000030b445841c01c51400c00454112403040000c1040b0380d1920281c0f43d120000d4003080c1440c4c110220b030b22680b821461110441e80c1038082c0002403158895010101c80100711228a43d1900651007076154800c180004a580ca061402090f001d4007402040071904800400c00c100b59018005001e40c0541400004035521011035120080541404c6950040390156244080c1500030550a104600880b00f81600310314000030407540d21800800913500580110b0144418180898485200440507002500d426140d48565242204010031440981001402c0104025480c045e01014150000145003440c0c10308491644 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756729676 1250 756728426 756728509
    0xa080a110613120804050f01320d0c0512060a060c03081504090b06031e0a0b06030c2d04050c0d0b040f0f0911030607020c150c1506 58
    0x324501c0401c031028180d004585010007404456180410801c00d0f151003c0385402a01c100703446034201c2011008694040c0c0390000c815032000085c0c040c215801c85800c0c45100054090207517515050090340002510307403090800c00740c1c03103441d0785894485502e0041d0710380d0001002c141c0a01608181040034070b0304000c500c600c19605d42080100d03541d0300031740040b8802010268070f038401c1c140f10700c3e813040c05510b6031001d0107030400307400f13a138122003142030804401d0700b9680036003450344d22018102000c51024026140c0101000b4103a40c41c2c50444d000144408442c0ca400120b800c42c6024040e8941c041903290380c0f00702c54140c8040c40246802c042016440c0030388250910707442d48070465546260780d5a4001210f800d02500d0401c066a4003102d014000c0611103401c84050051084005103490009603841c45040e55900030999407048605000104070804403142c8950014803103450a0801400100c6450b00c0a402c1003046190200c104611201e5000f15000101d224005402e03900341c003500c2c0940d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756730926 1250 756729676 756729679
    0x312301a06030c0c12031303030c090810020c070b040801060510081003030806130603080c0c03031c1509061508061c021215090d0f020607020a0f0f0204020a0e0a080a11 74
    0x6803150001c0400504044032510305c007805038000020400070029042c60403240500a44d0200001908600c1c01d42d902c240074013442c140c0b584044c2d204c43c102e1035181c000702078144d013410030342c0d00445d07880280c1810754002e071304200203a946400e003e021a0400100001610b2111314120020341480c1d01485401c800d940009070402007070000203070040e280c2d0b0818109011080c2400c00c500e0760349081007042074101c01c810360701500488003a450149400000c0d151340d0058000c42c1c144108404003000001c00341d1000ca490505040580011a281c852042000801c0c1418000403207440a0f10000d00041c2c0c000c000501c260840208551035070403918040080c964155003040c41e0710b200d05466843c100d412011404081002402c00c0a21180800d012481d0383c0d4a03205e50760104070717103c0140e840e40800c442c5400142c5c402c0c03000304040b500d0070038400b450ba400780801c802801c80b01e40100742a0381c4008060004504c58460404150030305c0480c0304000d000c0880601007005403503640380a4079581001c0036 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756732176 1250 756730926 756730951
    0xd020a170d060506070b04020406080f12030901180f0b06040516110c10031409010509192102010903140f0409020c0102044b0312301a0603 61
    0x140071801159021201401000305641d0f210000c0f0315100f151000210750407801107041690006800300c0001e2221005407007200a05840400744160005a40008106154540d2640844d003c00480a101100503038021500c031a8010100e0424540d84100508400d000c0c924010400101c40c07449e0381ca44101145a20b0b10342c0240380310340b4141c1d20b840d038101081540540b101390611069900343d4085640360001c0c10760448259a030760f146d2802c032441110606c44076001185500c0b048010301e00e01010061250403407281101007061003201c00c032040c111840c0075139035400b1200241908440700d49400344514403110b150001e503d2410b0014040c1c3d116180d11150049185809140203405480c007420b1060f034002181d0260409100c2c06c10131600c82d10a207050006486601d8050091098450151040c100942c007403440e592340700c0d88120002c14401308401c00c2000700241c18403100a21a030744030300702c1980c10219000500300c01c44d540100d01e0890590402c24804281e103404003640c1c0d22642c80f81d402d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756733426 1250 756732176 756732187
    0x240916051008101a0c01050c0712081b030c0901110d0f0c021c050c130c08130219060203090406060504030b01060c0f1509060b0409053019020d020a17 66
    0x50000f40a110341000d04036800710028045428540ba0141c0000070281e80280003d48455510014900c02c0410242c00c0d4000d1101d0307510384178003d11010341c0194020801d0712264080040f54161a007080e600c400e030100340082d424050b5030307221034541c03000c1ca040009890107549502019201d00864459102480042904a0b0039036488030007944400403440100307280c04007145411600c40b21403240d9140f090702c01140d0f00300c441407941b04e0317403001d50840d4550032029215490321240c03080d16850100d911060001042800a4500a0010051125400840c0ca9000c1c40302004180da6854200408124041c081040401c542038030090448540303040051039280c0500306105590403007280035100e0100d451000c2e5680c1030b16407007441114005c44003005030902500400055804885000c0c0c210390214820a0900d004038100700744211600d40e0402c0c01d08051600c0c5042c6411038420b11001808141c0990b0b100b50301401111400d001c0b6201502030783d0140d82c2e034424640d95a00c0d41e111440c0b8007081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756734676 1250 756733426 756733441
    0x606011e09080307050105060a0b1603030506130911010912081801110318090c030103020d170c0109030c0c0b030705030c22090510060201020a0f030905240916051008 73
    0x94001e40a801c0690b41d452a1178206107020b03010980d82075015440415000803442c4501080c1e6480210b0036601c520f10001c240c500300c3c0680b90241145a01081003c0503040c0309a0034401c0210552044c0b4003c2042c0818400140c044a0268060203042d00c03a114040000340b004400c075481750113460b8287c0d2524000380012907501c14009080d4102e8807000441c001c0988000e4501080e036401241c0610050341c400c1c0f02d031122400280310007500407102c075944400240d0743c00c48600c9044001c015450030310103920791041c00d5500c541020380116120042500910042d4001d090107020710742c021910b14100b41c24010038510000b0402100098003265168214080307041000001c086a90700c1e9030495103410404000b043e003901c503a407800741058000540a401070080d0303501c445403511007015110050205902900c59054211031502443e450b20001240000d2000b89488105045590700e10b4100c80300b80c6080e500206022034080000410081c507620390a0159401002d45400c0407983c90740034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756735926 1250 756734676 756734687
    0xd020c21010e060108011b2109020a180f0203160c051f1b0e1003020d0615050c0d0806030601030212011407050c01060b030606120c0403080c0a0b07020606011e 70
    0x24100215402c01e01d10009035440010201d042e03a40c0d510003040841d118801c0541c905010000d60b80200f207032400780f44c1c0340503011000343c5500e410794440811441c11680c00560b10003025003150404d80790042043e0b900300490321801860b80e8942500f146141486425109282280740d0028100000702c500d500800030280801030410b0703d01c5002000c0d8403012070b10a006000d101c00d8002c5850802d000242445110305070000b005400503052807030344203000f80c0c118040e6004039200b00d405030b20303404005200421103100341840300466070303182c0c0c44050002c50039040101c10401c5004201d445018001070b03640200d0164112a41200d11001844190103841e0140c40700350401010030048c04100000550410014944030342403030000c001d11038885203818920301080d103806800000500c1083c1840c814400115044111048102e080603500e68900c11264424404482031f07400c1901e809082200130390307038180c1040e141d0026214510386800024065002d500022a03150584091340d10305a0098 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756737176 1250 756735926 756735979
    0x103090f02121501081c08070905011b0f151506050d0c0c0f03020c010809070803030a09050a0f03030603050607080c09010c0201031b08190603050d0c110904150b030d020c 75
    0x3803410855170f51885659141c41c88219012441c0c2c20364000c801c0300c0c6101d90300c1a8071500b41500e501d480d8030304200046540140036100c04591108116030207011500d4440c0c00e1036503510910003200f849600c00e4900c81503071111030750783c404510525001e00400c0d4011042e00d0340c01e4100c01c0300040355441d0440403034500d00c0141c4007a100619015019050550118040d0020b18080e2550803045c2c6550204594803a894450000290014804038110010a03040944641e01071001c03189918505e442d02110086c1203141200401e585100130400c10600303021450703100c116403c2000d51481c0888404440b445400c00c8e441c10020300c10088411680260701403800305280030b0001040000701440a4105001614070704c90300c581d038001d81c41801401d8051401502d0f8031802403c01c4490520056640d10001c40381103404440c40c01d08038149440300458180700e07501801031101d00782c0c80404050100c0c0e49416078540660000030030001032640000d0720107000c0070242c50510321120014010022000030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756738426 1250 756737176 756737203
    0x30b0a03020d030512090327060712020604031205060a03110a1809030801080c03030f070c1e17060105092d0a060609120b0c0f0912030c07050103090f0212 68
    0x4195010107055002d030103012003074807540c40385111b9151060010740e00c0c080c0f1303003000020b00b40c0c0140700a000c820003c40d481251101074111402c02030030760740341c240706d1100c03030b15980c0180d020703108100038180d1260f50070ba800c684401040007181040804902114044d0002402070803101303c0d12120780d1184403000008040c1c0304114a14621f041c007040025100e83c00301035001030003120021540c208080340441c61010020000d61a0852500d00c09506403c102000d407040c10742c0943c005182540200320b04e4104005101c20340b041d50030510000f244680c1c04000d0462540100014446030b1150111180c00c003034201d04144c9088840c1e0020341ca901400c00f841c800800081d801e2241c0d41d12150000c1d004d450180e1100c0d07108640340c00b140b1a1a40d2140c13000707421800c41c007000c40ca0307101c0c8507801084009007030000b841c41c004041010034107401c1078020410702e0781d2000948101c440010b0001d000a01002d203410300181e8820307100c5640c20347c030082010344542010804044107690812460051061 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756739676 1250 756738426 756738439
    0x1c0e040e0d11070506090f18190c02030309061906030501020414100f02120331030e0604080c0f030114100603050c030c0d050402121b03010b060408060106030b0a0302 73
    0xc48521585a00541c2400c00100c2c0d804055048114004a015800c1e00d50141c22641005200010000d4481c9522543c41d04082d07000c4a4041d0b07002103400440c45460b05840311103041040d424030004651030888203104540080c811300031858004541c05030071460b003260b09101c41d2802c80c0c550000300642d41c0000d0196100040010300c48032030309022801c884c0102d4010103e2021186c0039510040d90440382401038028031500c41e000c51102c000303103400c200d03a4600400c940c031103140e030054581c140340c2d040c0d00e440340d44002090030135900c00000c807104041518240d041a14040c1c01c2680c640c04001c046100c0c000244141545403025485400030007442ca1200310507007050060b543c090141313401004000707410b0100007a10a0161011240078071011a201071800071351442c920020301002e8000c0342d0080c98080c1c5422181d004118030360b010140040b20002c00102c0d0340405085911090029004400a01041064081c0407905904407006420f0208a2005030b0000a0b1200c3e1075401c000c3d132284 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756740926 1250 756739676 756739691
    0x3080c160b250e040c03020309060a2d020910030605030709200708040f050303120103060507020708061602061e0c0a0315030b041e0b01150e130506211c0e04 69
    0x25885500d1043c55207080d03404001020484008409902c01100c01c4035995120f80042543d40919500c1880b500c018041005420050aa09008008464a20a250300340c011407004e049250600c8120800c020900b400c104e034030b15100c00f00b5110b4141c0c0c030030000041d54541850103d661090707649528218041c807144c2da41c240b80d1411002c5a0045e00807407128452003080811182000011547c42403800400c1d400340d41c1c0380d5038840700a06401014041107001d1410001410030b41007081600070f02d03580252100300d242c04840280342ca000103014445952503c0308090325030400c0180160000070800c209555160000b0068028025640312240d84100001c1c002080c8846590001d0043d840341143c48450703642c040c40309188d9081910042d20f10b0300e00400420040d88072124561030300c80d450a1202a0184440008070b10500200c202c042281c0c40b142085900d113001131040e00b014080041030341c43e800c1d001103070680d540d22814400d507650380100c440c903220310f0040c41c141182c004010010300260 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756742176 1250 756740926 756741001
    0x30f0f050403050a0506191e020d0b041a0f030616030504170301080106031203020c07140a090204120b06010521060f030d0f08010f0e040f02010311070f03080c160b 72
    0x18881143c441058803454000d1580c04000b9020308607409500c948c5d0b5100202c1c4482141000b5404020a510110364800607501103032503501a8a2941346800c08002d9903d5030b10303060026649614410b240700e074100008004510f07490b140b50b40f050703000d11f1600050996035454483c040c04820102511021070103c00020034038015003140080d41d205041006000f01c6030fa00c1941a801901114043c581008400303002d6200729000b4980aa00c0042400007450380d51500f000c12640203420130b001802144d680482404000d501c5036400003020b00e0440d14280100841c0507030030390060748100200984c000403640325526000c070642c5200d0020159456140c0910000c0c2035100b05001c04400700360880300006601515041c00d104a90569201302d08580d229a608900c1d0300c1070942c05c0f818150744540c40000000014040c00c3c00b1841035100c8103c0c51101d0402608004004080f4000c001d01000120a21101d01a001048903808201100340303480b0342004131020008021140c01c01c550240814891703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756743426 1250 756742176 756742183
    0x60605030f150901150306120f020d0c1a090f030304050108161202030a1b0801080709151d01080733022b110601080705060d0605060a05071509030f0f050403050a05 72
    0x10754117152810003e0996842182d01292107045010780301c00da0074031003034000d41000d02a61241f2445020405203858850085401e01d1994096031000d600d80811420601d0802c203000c0044074008a0040d400c3c01c0c0746c28002001c0600081411218a0341e2041c0b500c0c0c1180074031030522284520300001c0d0341381d00d0020344660081c08250a032546041031041302c0710b961400340d12a541650001c01c0680482c074208051080540051808040e0140c00c0c5000010b1100e201109a65944205001041071f5403405403c20f03e0100b940c0c1080640d036036000c0010a980c8860151149400c40300101400e460315001402d82c140b441c08502c1e1241603602e4144207400042c80f180d04044110346460b001c480e01820300803d5600c00090151000c6036201150038004c43c904800501803244031400046202610b40e800314915410010004005c614041204020010b41c0d55103107440c01c070039210800071451a520001c0802e01002400b1060180300740308010300b603200c0e5007204c0103960050100c4504400a00e45681d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756744676 1250 756743426 756743459
    0xd1509020a0e0a0b090106080c07140f0609060c0c150c07170306030118080d0b0a1206390807090e090a050d021903050a121a0f04060605030f150901 65
    0x1030140740c40c00e04c0009142c24103449050381c0711603941c9501641d55400440c0b0560004400381c843c00d0f00c2d9450808101030810501e541280000302820650600c41c503410701e030080182524007001800e01c007516030752a00143c0c034120401d417465085805c1d200d141c00c641070b510840c1805800040001d420440a0800c18021401104260000c2041d5440388000b000d100a1002c0c1c01407040b6020001714000b4804c83d040f2900b19103004100d009038660f10107805900d0300f0046022203600b600c03801864290130300d004c52007642c0c01c84051644140408132003404002c80114280205010880001ca0300d1248281041d0002c7d050010064540e41084c48065580f1600300c41d044031244a145040d40c19140b000ca2021203000004103040c102d14a140e4060741e0300e0704640b00b51420000700450141407445507004203114400024507402e000c030191002c0c80145090305150038008e50819030200305003640801142c5e480400d00722042c109444030031034080307440034220741c499000003160700105280c816905020b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756745926 1250 756744676 756744691
    0x5180604020d0809031e1b010c0209040c050d0c080106061103071407050310020d0b0406150807031b0c120201201b03030c0a0e030a03050409022110230d1509020a0e 72
    0x14038041d9400d40c0d81c20b01a900d00f22081c0060f1009c1b9040c0c0041c140405030130b80041c850028200c41545500100f015820380010a94685020010420405000b0b116160103400246000f04241c20b0503008140e5901c80da0400030b00224103600300c0c3c0790200091000c84040c000c000c041c1e840c1190201440c0000e504041000e612a0386010702c4001c491401d44184000c41e14074803911504451084025034880354028100300a042e11414400c2c0903c07485061b900425825403614082c1d2440c90a01c6201d040f000f060003815680362822110520b541e60140c0014118a070038507541d1380c0c0d030484000ca0507a8812003035000034800030007803203040240c0f1005808444105e039209111045007000301540c0761880c82014001c28402c100c140f0400302c1c1a0000c1280c0118100584402c84200c035081090900442e6001c0724149198030074451101c05100956800f4580710b00c1549101080c40000c0300c0d0840014020900812a10359480040c600d801c061141a0002d084003601c0d56076104680c107a020459210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756747176 1250 756745926 756745933
    0x60a080d0c05100b030703140a0b16080f0c1603020f01090b0712020424031b02010e0d050403020907110f0303010b03060112090b0403050c0708060c090405180604020d0809031e 77
    0x4160706143c0d84111815400014010300806245440744a50004100c100c48040d0103a891074001107441040c625005205d140c00d201081514001c000b071001201034100b240558010043c801151605402d0752030b50120304000f1084002c1c2441d080e45002c850008c0407415500b00002d0205000c1c6804005200701b0807030701d8201d00c2000c45180743c822441107008841060080001811070300c5e0744900800b801c10003a040c0054203202c100c0324642030040340a0020300503912034840a40c0d81c4000e00c0b143c9010319607070500c40c1c14113086a0024524801c01840340301006052074020072907401c10009038003454001c0003625500e50b15015444843e81c0201c407010b000c229180c4110410200700d201d0b1030002500b0042c00d22550321a0b50f0100c40301e9029200210340745c46078142c0842d0f009400d01003d406511408186541e03400c1007001d1105031140180030503c4460600c8403a429500f000c6400d541c00f55040b9290442040c03585032000c42c40c06114000c541520811503880800e03021980320180c5803101001300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756748426 1250 756747176 756747193
    0x1502210c190b0a0f021b060403091a03150d1202010b0f060408030909042f0418031d03240405101a0114070605040f0c0e010518060a080d0c05 62
    0x4041c1001c4000d240105100c10b1a000980190728070740c024070100f00c0e084009440d00804407520030003a05e01a9074009035402a400b80f000b00760b0405441001400418099041074410640d91405804010300722100c0940c0d42c8448081c0d035441481051f2000c0d80102403e10044013082c0c020b0007440302901c214099915240c00fa2001d01d04041640c040f902c000300114078115030501801480c11300a842112138017044a0115007041a059100310240704800c02d060f120182242004281d0350181c90101e090300c10034600c840800c3d40210108031100f0028000001c028005001c60315124004469060b01d603a501180000030300000400c0c0d010702d00640445405103e500306c0c0c101150240480c60044800000380aa025409000d00300c9181550800c414101495619910181c860855080f606008074a40a8082021101c1404060000654840810b604110100b48400200003035108a00e024000140d019510715800304064251803003510314076081410090030814903000b0454090054107a07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756749676 1250 756748426 756748453
    0xf130b0a0f0608070302090a0303031a0303030a0213090c0206070c11030d030f14270708120c0708070e04171306120c0e330304080703080a05060a1502210c 68
    0x2c1e200c0e08000200230910307861642d0780c1a0020204005616125100d41ca1145500e40d400e10280d4400c0a1140000d80e1310040000203100510882e000150558545411603800560000f0002d0303108070b16041c408511807281c10412550003000c03a044d9498825400000c003182d41c036400021a403540074000380b100c2d044032005100300f000304607070403510784005500c51041e0100c1014502e00c1265405c09561460383c640c42e0480c200b00c80c0c0000100342d11000070b014000000108115401041031001509110307040c4070052025401c05440503041960101d100c040c400410000c5803080c0c5d248003101841030781e4450f405086d5404c60f5180504070342c500082c3c1d144050085000c0800079100030818046103201182030107010f0345940f150155003000382c0c0040c20340d911400045001d180a241d9903031f203404d45890014145030008004101032070404040c0102d585903209a001a502e0b2107192a240051200e012454005180a1900644030312002004090810001444801c0900301500c819440f0110b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756750926 1250 756749676 756749681
    0x31506031505061021090b060a0506120c03060604170706090801090f1407050d080306041506020a20220e060f0c0a181d060f0f130b0a0f06080703 64
    0x1141150000f0b400f4210101c094405e00d2102c0150341d0341104810041c0158070072034100c40c00490304652040590f0144041482c05065500003030000321019450300010780d440014402002d000040d0404002c0082002ca542e000c0c1910044d2141c41c12420b052214503100703a03514000b601c1407030007086100c80081108003060107281c840c1d6030000148a01c180007503941c4403000d90011400e190078003480401103465925202c007651070794041c4040d25202e0410f0410001200c003402e036028402c0d00010801c015007600410300450031078001c02c505101140301507811300705907006281e03a544901214003503400e0440d80347e612914251403c004200411002c420182c0d00d0001b600c41c00300400a040c0001c2d1030607045001071030744c00e40c1803810f00c81035140748003d100d880317116801c106075191001320f0b0140c03480410420305a100404880d4100c82000d540c020400c001c02c0b000501c0c0c02000d8003114000181000c1d0840d8401210103040d601724140d0381c4c60b4440030320b0041d020f5600000e03c0600810000345c460f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756752176 1250 756750926 756750931
    0x1050a0803090f0a0915171507080a200d0e030313080f040306091a07020a0308070c030e190611060f150d060e011a1c03030213031506031505 62
    0x10020752420240c0c50400001109040c80f0a41c0483da400300031031400664012040c0f0704904000384944682000003800d070300700703034601d50032403035817040c60703009480d0201c2280342e0340201c51418101001c0d150340003010090f041440c0c0f540620031448000d203090a07400b4005050416009000304001040100003d44030701c810b848110a40010003c03500c040f40c040c030b0082004440400501d0301d8140e030f81c1d44040a54000d96001d0f680841552000c10302c3c9504088140d90040307240c1f0181c03840c8040da0740d026104c0d039400350441040110307018102c0c0400d4052074010385111070003008007000d10710a90114901031910b0040000049506c45184400c40340001c2c2c40c2c1c010030082c0a0f041c115541c8422002000503400c0100c3d61007080307200000c000c9242881200b00e20900b00e4004100e8850028050982581041041b070041c4041d21410100e28040e15100003000d600d0300d000741c0c2d03e1030b40311803e2000030301031b0704003420700c00c2588202c40707040b80154411012032b4801d0818a040304040d0118030100d4104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756753426 1250 756752176 756752189
    0x715120207080d1d0a05011409060403120b040621050d0f0c02270a0b0f010c080909040f080d1b05030601050a030903031d0705040e0105100e04021807030b0901050a 72
    0x9100007280400c05410013041c80482c100c04d11107800d60ba004182c5400b840c41d2003511540d544800b100341d00044070143c9940708a4a400800070b0f0709281d5001007068500d4070485001c02d960b0402040e0b00e03034540d00840c0040642d1600a801954052525030521800c00c00444451050765004400980a00407109008515440b6158071003072a4085c04555600d101d001d81c0540b803400024240303480f80030340300d500403144007400148440c4082d003840040e5040303400890601c20f140800000041d0540e0455215030825521101941c44a103860701444401c01c400801c1c07080d001c5110f03c0a44000e40c400000309803090040070324a00100c1d002e07182d920041e1100e80c0010b404101042505000f40c01c10030704c3e24442e1800103070084100d14094960318000200c400c450f040054108010f04d01800742804030107002000f08540d0514407122941080300344036994030051460300082c01e655031032004400b811000c0009811503e00094028018213460549500c40d502001c004110786c105a00e220041e03520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756754676 1250 756753426 756753443
    0xc0f09140301060b0a08100e06030d0507080f071b1208070b100504050a020a08090115050d110d08030402090f0c030114130608010b01120b130e010e0715120207 70
    0x20085a0810399280c000c0154040d07481d03481c0014540c1c040d000a02c280c01c03c81c1c0e0b9a01490a012042200d0801c00d036211403010b852a1042c00310980c0c0c086980d08654910b402c1490303403801c140c64247c415018009102134100d071302181071001e00c44076241034803031480c840d21204040390b201c50034080095030707182d000340c40040d0620041c030010307040c02c48094001e502d03801d2984041e40e40d0000142540c40449040401640204500c2f002d180c2140d01c090300050b922000740009400ca21901224038264460123124480d0002040d06010008a030220304440240485151104500f40291180e00542e000c9020381c0d44000010060355000a070a40510302421340c0901c0c591030041e5201141a101d199a03900408402c40850182c0f000d10924004180d1280045000e40350540094030620104401c1030019060030040c0c0420350341c044000d064007203400c3c0c0c0040d640c0c00040006004110b07940b620034440c49079201c0454501c10f0b100a1103000c051641e20502c0605443d0220811b0b0b0140d024000d00002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756755926 1250 756754676 756754679
    0x408030106051b010c120c05162409030e150c1002090301180f03272913082104212102010b01030e030306010305041e0302100c0f09 58
    0x184603000900c0039155000b5182640b40504414a085503020b01010001c20080042c046e01110b0380c1c05601d82000b446c2c14000d080801d034540d8548284941d6400401400e40d03c0f40501d1040410100025100c1c401c00b410050030725249009049401c02c0f0010b1446114007801c14500f08481200711000341c41040c028201c2820000e0a1001035007100d840144d06548a001c038400401c1e40c04000c035540f034080c4003920120842e07030501901c20a0780c0148040b43c201c0030f00c03903504461703500042001200e0408004c0801f100304a41c8401d51405007506480c0031000c002056004003402c5618032055070708207010360345500c410103040c16001800c51401c04941c0c0003404100f0001841d0140c000c44507010904030758040f919540c6030850540e02c8000c41040d22003038851504046e07070920401d2200c0b1405c1c20b0402050f5800310166a4030b000c0141000c0c1016105c6000030304000c2e940c1805581d04100c0040d110942d02d640c0780103515841c0c14080406954900035460a041d8890307191484910b80302d840b484141c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756757176 1250 756755926 756755939
    0x70506010b0c0c040903120e0304080a03080f06091612060513020a030b060406121d03030f0a14010e1f081209010329100512070c0b06030114070f021606031401090504080301 76
    0x282301088120b0a02c4c003080c400091103c5c0705000381480613110380e880784030a140c08003400c07901410250401e4020f5801c2d0042120001031584503081420701800c01420f543c8620001c980900072540003039401230820b03403100d20b2202d4241c002c0c00c61010030740c4050144516603c14042107000ea4444d0301d001400800c12948051002e03881221919248402c03c0f10601740c8807401451075105a0b64054080705000402203260710520888500303640a824400103540751000311130944501400800d200c1002a450354640d00b2040305290081490700e095400720141010883d0640e08040061030100341814001e961001c1017810601c1e80003240e06000720940150824001103041c422015014000100500d0303060680355800d05128400e15964540103001c640380101c2084009001c01d8060b0f81040030b042800981c0ca0f2642d503200c0340d40e241051005e150800c0492404c075a0065180c0c1540b1200e801040c041e50540001e280340b080000300640a903a10141c91003120021140a841c6002c10300051040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756758426 1250 756757176 756757181
    0x1515040e01180803010f0803070b04230d031d06010513270c03021e010c0b1005060f03060907021b101412090d020a0c150302070506010b0c0c04090312 66
    0x10100c868000140300c03200c856000c02c1801e01c0c0303200740e89072107011004006081d03092071810042d04541c006141031404079036651402d894003410080034082401d964400030940b6160b907801c0403e034002181d00351100c2c00c01c040d00810250b0b0918012101500d412860350100181041c1200c00242c80f072062041003040c84030050803220304074601c80400c0307000f5032007040b000c042c12451030b40030b1071010b081340386581b04104030f1000750011402c80602a50341940d8680e048207403055003541180c140805a610010030340c0550342c0b04c0e044913070711901c0482c0300035226000c0b101462041e00b00381d0706c500c001e44078044140d030340700b4190320003d02e40400f041212940e820107021506610f1a942440c10104800c00800c032425044800c0381c13140100740c6d104000c20351300c04004604042405002504580c440d584034441900c00354081e081c503440000c40e802c0b0a240c840d504a5049d141c100c02520490750312541d81c40450b6001c0b0b010500544500d03410b54006281034400c0600307050341601c5003c0c0040750a80e40301e02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756759676 1250 756758426 756758441
    0x109051302030c0f04140112050606030a0c051608180102031306050c100f1b0503130605090c0303071b1e050d14010c0e0114070b0f151f02151504 64
    0x4200e4020700044c021801d1100c060400f40c03207141e01900c0c02c60250b81c00180000204d50003100c002d0b04000c1400841e851300400c59400006a1202240d20051810207403814400c005003d080c06820300e00900511125402602a025484182085544001004a079a4006d0b9101740d141030802c40700170000c00d4050401000c407800c8600c16126401070030300e642c20032a80d444141270b18803030b11a08040000000d680c1911a2a00e40b814014110305101601d0415401d04240c000c1220b6540c0010403402c0004204900c10004010112959a4010314040e07024695092041c1129445000003241e69480e0610480d8640100c0b080120114903150801030b64501e10134041e54401401103a00d05c3d1800c082c010381e1441422920380421945010b0001060214042d001109000007489000005070080402981210026104803855101d40702c07a1034080c1420700c1025484464001240070510b100b440c1d102d10011702c1e8098070301c1003a14a6415065150444001c1d01c0081c05060060703142c0b805500c0313487c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756760926 1250 756759676 756759691
    0x806240a0c0b060a14091026011404081c09020a080a0b07030515040903200106052701050f0a080106090c0f032a0201020d020c0a020a1707030f08070816050606010905130203 76
    0x5403155a003114245104600000100b480304650548c10802d60034010841c4d01139441254444c6850903444040c2a80980300c1035428030012442800d1406a00f9048100c0894004007d210bc0d00e680d60700e89030780c9034507811040f10621150b000041c509402403003039510529200341701602c8420b0040810004120078441241130040710880a090750130403070000c1002c01c04e8440001400c9050004000005c2000d403600741d40c4140c040300c1411070740d040401c03840c1114826524030306001111030001c0c001d008282c12000c8503601c3c1003000076a81415030484107200d02640c507610304000301c0800c00c60039120b032032840042e0790300c0782c1190b4050684070a10030400011184001810301c100700c040e043c01da0b0700021030908160300805603c01940b400c500110300400d661403011004540215040781c031072000740300c0913103015200c2030b842c2e0170710800400b140c50b9a584801c14690340e55000f4010026100c1e00b00c0181c0d00ca20a840003c0c0341e41d40101c4605050380d034001c24101078200f5014110700a944018280c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756762176 1250 756760926 756760951
    0xc18010504180e0c0d050703080c0c130212060105070807231b1201060602061302040b0405011220031e0c0406060503090607020303070806240a0c0b060a1409 69
    0x24401903034003403209600c0100d40c03000c9a4606482c0240340b0f0441d42c1512148980176481d00100041e00000d1440101e0768081a01ca444069041c5a141411002d0201c10341101d0a0510310018002c0c550003022720f03d24000500c2d0240d142c100c01100d070f80c000c500004010420410004020403032100b0450307000c1107400440f100400b40d4810050400b00c00101d400051045c030861403005181819803146d031010303003600030000039150a100940d101c0380500010045880c446100c0c0c203540319600f1003c14120701070418000703942e5031804902001c0d003101080c1c0b00d0074884a99a030003410141e2940743c1d010402802000280c40c000401404461f40c64000816032084d0750114203182c80d1030107003c0003450341d900d40c81d40340c2c03904442c1c0d2400c00100400d01401c6400800400ca5916005084240c004074144c91300580300480640c104000c05640502c00040403002c100170008a502880f0031015601c00e2148455035201c000a10085007045c2c0900540003480304107030b0090307081243c1e210380d02c80c0407989034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756763426 1250 756762176 756762179
    0xc02060c0901030f09080d060603061706130f200102010e0c130b0a1a041e0f0b03040317091e06010e0a0203220b10050306041104020c0f10061a030c18010504 69
    0x1003501b994840748031114425140c40c1c080006036054130031034005000310b8188a01c50321826000644603a0000d15064100004081c400248042c20802e007262a500c43d0401e4600c07161907a40d01d01d03080d40d03c03140030300560030300512440000c17020400c2c03260301b080904120814985c08100401412900c050f10750400f40008000951038000d03030f40c00c000740805084e415501c07404c06020601c008081001a03400e0280740e001002041171107088201240c2c01c07401c8907502c0e61568a011202da44400c00c3c00d241c25001803052141c6104041420032180a904c00740c00c0603100c4155400d034030380d802403146e212659111000942c2e0540304c0e400540c1c0c054103204203000502c1408034021040c4214070f0061b00c4102c1030b10708004000a1f6040c03960701802e4100d004105c40d180541d5070000c080c10b4144001d024607004078500301180820050007010101210030742da03030000140b030b00318000d00461090394100403040203012000c5616000b03c03030046040e02081032911070b00002920340070440c101c1c51030400004000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756764676 1250 756763426 756763433
    0xc160618060807261f0b0306060a0509030d08092509020706060b0a270806070c03230327060c0906070c06080a0b010207230a03050d02100c02060c0901030f09 69
    0x10000c4c0b006004180c00e11071401d181040f800c0c40060070001040100458205101d1186000c050300c1d40050115104c5965108101044549015400049800d0302c6000c40345204960010141d500c95071002c0c040303802c4c00c0d404120307500c00c041494249031a807080f0070906011064142d0010103000d0300507000490b25564400c2d40701090380c80000e500d40002c644803422070b5102c00701ea12180c042050303c0010b48540d41002c0002da11101d002c2d08103001d0013000c4640400701400707602240401c1004280c1c001c4101d11080080b01a075201b240c0b41c5413070001780c99900800c041061100400b0210000c0240000d0383c50340380000950b031100c00415030200040c4030030ba0008a100c1d00030005000a071ba104840c90070074103099001c0c1c912019060b815900420020f102880500f100070300420780c180341d01081c484031030011840c40b03c03840d08098014024181100741207500010808010141c0402c100070b030444148040341c903003000340d81500c0402010440702840d58441d401c40c40301400b414500207050045660b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756765926 1250 756764676 756764717
    0x30e1204030302030c010f1401051903050105010f0503011d0c090903040b030112050c030705090c091c1211010612121e031514060d050c040b0c160618060807 69
    0x24402c50040e4800614103c9104007805883c0a80c0701e958001d124000310090b040d0176155050194500852140314101040a51210000000e40e0081700030042d5503103c010342d50420070140950740c06582004402c1c42c4020311800310300c2c800340305600581000b0541c1d9040160303981d005012061140f0080c8004101454214000c60007007030310302d1200000f103a80b440d0060403c4079050300030780f01c1d41000100300700c02c0d03d4030130302c159220006900b4a0364901c045000180c10f4840704001035411080d1121890030803844c503015030492081c0741c81320920000e500705240d090368150301801100541902c020740015091500c510641c403440c0c00d12035260811051840524105a250400000d4032055280b804095184044020f44441c01000c00f50400d0240802c4080c450380003070403074040d6104005004030340300c82d040e54007828814840607501d640c0800d0b000d603504d500035210085080091000204d150013108902c2c084685481043d02c81440c04030f06480c1d04100034501c0e800e200034100003420011382003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756767176 1250 756765926 756765929
    0x4090221011b0302031e070c080c010b1503071d1809070609060e03060115020a051f0507050711040e0c030a0c030501060f080709020f071e020102010e061006030e1204 73
    0x240a1110485040c000380c440002c54040c54410014014450b5500e07640e038003444021100400e41e51030328801101d51084010010b45480d40225100041601c190442c7c045054112401c60328400b114000f504540301c151002c01c0481d003842d03c429000d0001c41000e071400b05000f00011076046080c06007c11212081303c071081c90344c1140c40c0c24840e543d000001580644424a4a15451802e0340d010a0352030f001809044001c00c084070240081074802c008413841940e1001c15200761520703110401403400c20a4001c0601c00e41007900080c9924480d1040c0c4102c3d40c0c0082d00014001040400d0100034000e40060310580e005c5c0d8908011551410072060402e00c0c85000000445480c50074400e0840d0401d40101c402d00e11007080c1000701c0000060540c1c165034110300c0c010b82d42d440c0143d001005100704c0200420349508550303e03062018003114410402d6000381c00034400740301281c5c00251520801c44031001c141d0003140c0300380f02d0b0920070741c400325a01685108480e103c25001d4200006908a03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756768426 1250 756767176 756767239
    0x80c0c010e01202d070b01081f0204080a0b19180507080c060304020d060b040c050c15040b0105060c0304050a03080711040b1e04060e040b18121e0904060e090c06030108070302040902 80
    0x44520380c0e101102d03843d03040d27070034140089045040c5800c00c0091611800c00d56805015a041100421078190704203601081003009140104400e50700c40c1e13541d4242c500350301000e846c1801070a80005500c4404599840d007040020a020328546e620707402c0040c950f150410956200e07543d1141403050340c40300e10444d6407581d41a1920b0b519140d81011080c80d201c00c0024098003007000505105c006151400c0e2507055803070803074030b0544030303079402144a286000b590312855100b0303500d00000081c0080d0b0380051800c503000d102d080350007903942e1080c8001d403000001d0580d00812140d1903903015490760a40c92500b06001040072642039522555001c017a0816a401d481841d8103105104c3c401140540c0200c210000c0005007078804400c0c200bc0d007542c00b815108140c40d176565000c40c106c01124030101c0c5d2260600800030001e030390b1185026451550100d0f92058980301d0585d0103400c0c0e1070700c0743c1079904860310b40000380001400c503402d00000d420f1094040b60001e01c0310407181d440700d003064264080c4100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756769676 1250 756768426 756768433
    0x2070203070906090e07050a050405040206070623091516050d090605090d09060e0402070606050d123b0a030b04050309090612030a080c0c010e01202d070b0108 70
    0x4c000e0054221070b8a100490400e900c0070703c04000c203440703c00250041b1001181c000400e076a43d80003060442c4031b81c3c1741c024800e070300e0480c0441c4400640c507500d400300c5800a2046c00b0329521000e40329520b2440c006204100340302840080c519a040c0381e04e4006103070b4545070490629107060200c2c400d8030455203084652507142e500704920b80c807040140603807007042841c010301e110b407604502074181e1010241e218052600001d03640d00703002554022400501d4080c110001610250409645c00d0300306d16154800217034248200f00850700c0c1c02c030108064a810562a102e0120085415560b01c250394a440b9007180d540600000417880c68400c00d071007a40580d010391b0396400c1c2003003001040b82d0000c2c0581c1c4141e0071070294a8000f000041922030b9001c40341070001d65a01d4402210f80c40b405440440c1d4119804c05c81c0700c80e80210190070190040103514890134511a0640e0f10602a004102110f2104c41e001e014440c01171008222280d081221180060f10300703e601d444466001e031098109501031303403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756770926 1250 756769676 756769679
    0x20f0a08010c031a010c080a080a2c0106080708030f070615060504060908190803040302012d05090a020105030c03180a0804052107060c0201020115030f0203190b0c0d02070203070906 80
    0x21381640d804981030004d181080e0b5210507a559280340d40611300d0b00c841084100d80009030400c0326588092140360300f00c464013105440b02174002000040001d400b03904d039400c094000868410001d9008107441c1000c001d1402c1503007145038003406822056081c0c610a448070002c500022340c0c55a10406000300b030341ca00755144e0034110050403040d440d81c400c94442e88040b5040030503904843c151540f0941c400342599581d211420124054211080440021504400c032580c02030444100c1111844c2010001d10940c3d4480c0303241c6407110742c41013010380420003c00010300c580408200555111103e000c0002101d291100c4d080d01d81000a4001c9a098100080070300030f078940030b060220064828803850b0b4030f40e1aa9403140352500c549204003424048201000030840e070003074001d03405403500445606000c80d92410115492040351074241d001b402411590322158414251031400d490b004025440152500040301a040d481075140d6031440d68240106001030340c09206030720081502050118034203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756772176 1250 756770926 756770951
    0x102120f01081b0d060b040212010e060a33110a052d1002160b270604050c1012090c0806090c0d260d020703030b01110a020f0a08010c03 60
    0x40e48003500307042490f06a41d006841d555104280000d841d80558081117035200240070601074010a1050223091501d40e00216210101c1244140300b400c0c100e802001660343c80d04d2202036a0b00040b078900241d14a140110a000745240c074403142e00619241030100346916920050a14030001740c01c07034954000717998440220111480d6034403000840e20004600d02d00202466a407024082040d0f802541c0100b0704007040000403905001c2141c010412171300c41d00e40300819840707821465414079000c910351282c402c805900050042c1c4529808401411540200010881c1d4503611800c2101006403000d0b80180d0f4030b0a80c0500d002d4944038010605a01c1d060640e0141444401011841c050b0302c50041200e0540d0380c0500701c0c0140d604442c0d01c4001040c031002c400c10729100c41460442e04100001c202000a20a50082c0707161402942e04101c07141c0044011100105c101c10711850550040000c107026186c41e1000d9240311070024035450b00c10341e44002d4907096071290b03a41c100c0031a54600492800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756773426 1250 756772176 756772183
    0x90b0a0b090612041a060a0e0a0c120c050d060b120f06040902040e01020901081f030602130816150e0604031e1401061e1511010603050304140112140601050c0102120f0108 75
    0x1c80001c4506802c001d0030210014665a401841d1803a2283c403803c00c06011030164503654811400112f00340300481d103408000e003403a400319034803590041c03030078200090001a180c00d030303041a5144a504442900c2e0252040d841ca070000d4030b40369020360342d000c404e00160340360722500031a03513084e50026860341140070002d07007482c0c2d0041c000b0600410a00c400c4003100e4400141d0000c1d01d5000c0c0e00117849504c0015117131800c80c2e082c0c100f0074451080340040e4021510006107042203d040303810160034024030442c1240c0384038145598542101045c041800051080a0441780001c0a44114090000140c84100c1d09149507030748100c02c1d96481405000c2d0741d44540c08045006180c03a620140c051411091090300d010f0300f4007800800c00f0008006411300000c2d01701e9401103400c101225250394582c0490103045406a5419010461400e581d21040000d1b02409106400c1d64034904501c1d41d4000041d40c06034003444508605544c204800b0412640d515a0140074140a00e9000c09a60420104918 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756774676 1250 756773426 756773431
    0x11220806131203112703070603060806071b0213090f060b100c0203060708040f080f092803110a05210f28020607120e0307090b0a0b090612041a 63
    0x1003600b8140001e810300351141c110340f00038020312940c200441a0001c21504c1c16072031805c1039458000c0110010b030b1154117070481d8045c0d400c640b06482003500c1c0c610041c0c0d01190030044a8484125464044001d4034000c0001080190940c40c040f802220306d640304120390341d481c801100c407903030b0310107403100703a41070008510403d0145c60500054110403a00065a0b400004103400f04100d00100043c2c04c02040c01c1107805e0300c40c2d10000250715012006041c6100c0d8201c1d9212b0743c051409900300c00f5441410401d1b8440d88030740030490740e902d2400d58448bc1d80000c055900b4a0300b1641030500020745440702c07070910501c00c42050341d1091150b9440075042c1000c0d082e04000500b03502c402c07031500c8000141c06231441090303219801010210b0036440030071118040c0d0f040c042c0c40d075141e1146820919401005031015034030203d003960744841d2604030031802c0b12503c5c18070a4200e035562605000901c0420002c0ca01c00c0b0b0010841d07070800c2c01040280204a07001c4038201c80401708862a0fa05410321441940d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756775926 1250 756774676 756774713
    0x30b06030a08030c07030905120102040503060709122a1403190b070c530f07140706090303091a0a0302030a0e0105091f1122080613 58
    0x188961042d2141c1c8242e02010b01140d4070a40005007000406000310740c2c5200510003d440010521072183c005070007034000e882071501078082d21001030800c2c2d2103140b08034183e90f01c0a1400d0300f440f0254503011a5098140003400c041201401c82c421034005c803030803007002130200000f030480050900d0140741c01c1c4900340e0030003212040c1084886002071080d0168607440986807905d400483d1203810b00c072100401d080491075820300f002c2018980c1640c40d0407040b4810340c4580800268070800d42d0b222050403010f0507100c1c4800001e0044103501c40b408070003045a05d014000a40c100d5070302c0360003036003030090713680c000340110b003040604008060f04840352500802e40414168003c00030180e2801e09845100c901c41c0400d42d00000040030461981d0190001c058001c008004a113002d0102c0795552401c1c07100d2822404120340c1d40b42e615585070180c008004003000d40709060507280b4140f0043d1402003c00c000d4a81018000130407504410005144200e00141d4000351151140c20068902401c100001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756777176 1250 756775926 756775933
    0x60a090312110415050d021303050c0904031d13021908010803070f060903051303030305070e0409110603250203210412110c120102030a1524090b13030b0603 69
    0x40204280342d003da804403054000d406016205440c011503a41c820841500890751010130b400d64041c0074001d16000b40d034420821601c51114103410071010403400c5074000c000554404070400b500e045101800704113400980701007c8807071031001e04c000340d8105000d80b009000b240c0400311102e41d4440c624034014080c80300a50729155850719030b040240c8601c88060510b94480030340504040c03240c01180d1185680f112003030a180e44a1070014003a18003515202e0003d043e4000034445171900d80304000013150311410710b10105d00d240c003e100d600d0300f0007031242c0b501103511415a8108101c06208101e0360070203901940e61355105030b410491601c25220700c07805240001d0304110008d4088820303c80d554081d4102690009210080300e0701d400c103403110aa0300f15422107001502c164054020f98010a1411001d002c03055180341c0c0596041c12a1242251940102c40200d1400d0344004400700000d05900d40150180d440b035003801d580394844000386091090203217041090010921400f50072620841c0078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756778426 1250 756777176 756777191
    0xc031401051507211403042f220b01110615010e06030106030510091a120f030c060a05010506070506010605030601030225120905030d1d030a140f1f02070212060a090312 74
    0x2418230b0a446040d00b140902d6801c0c0b12600260301800c000c008c4103070006e1104180ca10200b4101c0882d841100700c1d2003695007044402036aa42c00740444142414440000301401d54910303040e04003601d00c4590071814811100035880395512518001e601a0034691400b00c3c403410a21006d40c1c0c0c0808a81c40b40314040e00d00f8500d00d17000c03040d02c01003000b42901210f83c0344640310200005422b0641000c00c0d011039220000c3c9444200801144040c8a80500b4a00b003226030303698801c1c010507200d00c1c000181a5040000107002e041d00440245401c25010324006082c03250781c103109040a51606c4c91600601d8081101c1000c01c2024001c614080c451071508202240c500030100e0b50f41d0304480c23440700502883c040ca4220307203000480c0580500034001c0845903030440d00e09001310103806610641e4494002c04c0f1500ea8403000c0011203070380b007141c0d1140004040001c40381d400700a42180400b264400403400c002c0c1c0240d04c080016a0140c1c4001c0800980e90781640740c027030302401225060b00107031401d0a21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756779676 1250 756778426 756778433
    0x601060516110a0905011d091203010302061e070c03060506010908060105060c03220501020d020304080a02010815030d020d030b120604080a11120405040c03140105150721140304 78
    0x410060182d809155510700d8101a80003c007550f20380d41203003885a180030700005040c0d240e0401d900110340e000900c102140c44440600340c50b620115000e40b079100c4100b00400050400c140203009403001e03c1703a83c4680c0316840d5410041a4001c5170150340e0480180424000d1002e60311030650059400d003800c605c9549407491540d200c0d24148510f610428002c50798900007002401121481500301c402c2d21a0746400c0c00c03030135410205074010702c0d005100700f07280040c3d030b41e00020840d02581c1810000344000512a4011070b0040c0005000545038112000c182e0240c2d1020800c102d9410001e8002d4240341c1c0c0e00034001811035007860641446540c00d1414203004000108009810542045400da683c20784040c0541d282c86c003032001041c50303104110000f00700c0d0f89440040c1060314021641401038180000045082e501080148042c03481c418004200c20302d0304245626410b80981c0030941400d040762a092100c88100518005152000c042c010030681e2100c00012074100c00b080c9581541450344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756780926 1250 756779676 756779707
    0x150b011b0b01060e1302030a0c0f0228020402120f060909030403020a0b0a03240302090f010b030712060b0f03010e07030c1d01020c210f010608030708090a03170c06010605 75
    0xc182004d010013901c0d41a1140c6a492812800000003e8203540e0380c100255030400824080c01d0728030000ea0b40c01c4582c4003862001ca0b0000b2003800e01c0c0c8042000d402040000512140602030413640543e0030401d14604280450b00c03180310750b03510b904240040c50708906104011500500008941d08100000d1005980315128401030f228180b5819444800c4008103800030500e9220b6001d28142e00700790000580040e120754810f80b03209540b030154549440302d01c41040c00b001c2c0141c6000300014030008000c07034490094010340c0150a0302c0491083c0c0d444113098100d40c0006002602c1c02d8001006000210119508680080f400e2500b00720500118900609481c05c00c800032681c41501000031f60903078402c025662000c1c40080c00f4004202e1407201c0c648030011a03808004050013100055915088184124811a4500c0025525000c035540e2440c00e070750b000d41e46059124801c1c1c01c011000c5505100004841130346040c0b96a66243c0c81c156851070500142e01a0040007000c0208504c1d028114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756782176 1250 756780926 756780929
    0x618021e0f1009090527101103071d0102010f0e0a030e06030405060103021e10030f050f161110110901091211060a050d090602090a0e1003140307150b011b0b01 70
    0x40e001031540c44d003141c50340c6e51030b00302c1801c030307042106009010040703000c04100706d101590080b200300201180881ca01d03e45000443d0010045110700c4110b841280d510919a032424205100004d03000c20311605420440301000b81d8420198012402d0101701604020802c0c1d15004c11211b050035450641d40300d550b52031050000034081e40d181803100391004110311014410b614010403058071818010001802003440404100001e410400420011040300c0c5002e4000d05a080c1203101680c0350340c009860780948403110035a035114a0078500e0003c0450300c2201c0020b200e03c445140c0e11f030303188400101488656040400550704030036603880016848607d44003421800e550154851100c07400076510b03401205000300a450428800004100aa50060189283c1290742040380d03512603500e50340c80c91f012583c007058a5100c04040c0007191004070304241045960045910300744096481e0045c0700504208689019200c03200c1c6034196820215800100741202c50480400701d29445180c25070350306 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756783426 1250 756782176 756782189
    0x6030c011e03090c12032c010815010c0605010f150f050d1523041b0516020a080d09061707020307021201151409160801030618021e0f1009 61
    0x201c0828000b00b262445815004101004000ca681c0000f0f003006000800d6800704a460600a2011f01e0880e40c003001c3c0c40036001c14180c0d105102a83c44440c1680c0010041c20183d05124052801000203545402464064100e001401007407502c3c0c200ca10842002d519404814030030f007078541641265000302a61545a0f00100c04126214050800b40c0828503a40044281140707004403030018800019843c1c08480702a1020003054000c019142070880566000303c0014404102001031701d15182c000c818100d00040040b0003c07691101414941126507160700d02249440741c0400c40a50808070304441550116402221441c19002c000d40324416000002d01c102504c106445010304254400c0d00913000030b5034184001600c81c103000c407a252600b8a0644608135100009040108542c180c907860000341d201c04907541d003956a0180500a00702c88070503003402090f1038801503642c5000000401218201c0c88041460200038400c0c010403c2c94124001d0341031080307620a07540d104500c4c00840d0381 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756784676 1250 756783426 756783431
    0x4050d030c21020a031403070f031109062a0a0f020607031403130b011d130510050c0a1b230f10020c070f08070501050315030607020606030c011e03 65
    0x2a0302c1c20a91607011010000359064210014061494001850101d400d0094a0726002115550440807440c842210004002101c510101d20f115000f50807400c4012003003101031b420003100c10003181140d00040340e440d540b0754112907103000f101d200d20b0400d400d1282900260460305001d4480f45400c80503800024080d480010310b00d400d0502c6840710712041e08804882d0707540c90600b440c0f000d24108241000b5121034140030300020344081d0a20040c2c2c81400404401d080030b0307503000c56603d8404209441a16140105840030600020358400c4070720921032401c2c00c5842c1c011031280102425802c1114441002e11404981d010034030104070141203215a4a440002140315a595400d0407001d15110b0b1041c0b042500028915a0940151400300b441d0300440352142d03940c070110344100040b4400d170403040d00310600c10b000a5100b031000710345c041c181d245003a20002c43e410100346054800c440c140c0050300054144201c0341f401f030202140d26042440e140403540d10310648075901c44910401300d030515a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756785926 1250 756784676 756784697
    0xf050303190e09010303020601051002160b2d070605070f0c081b0f060714040b0a1206051807020c041e05060d05030a1e03090b06090a20070209090304050d03 69
    0x144551007281502d10094410705003541c1d81e00d406983e82d03401f80a1640304040307444061001d00e2001842d203200c2108036680f071249034540380e8051038a60080f0100c44914940e100c080c2002c0007110231488461031211010360740c1c2c0099040400c11643c0c06001c3e64100300b12401802111980107042019650700080d04941d2481c2c00b04417203290040401c1c0f645090b008480c0001c0000c0e501140701e900c291510307110f00101c80448026640d80b4401c90141740c5402d9403d00034440e2081c81501d400c141ca81240c480001d181740c07201d0008030700d000c2d5007000304801d10a00d010461390550510a0702040e84003130fa0b080c0503030504050f007a00c100807204000d19080f55601c0c00158030345e88614a100005810005981e610360091500800c2e018544d0303032a20340070092160801c0140d200b44164040950040c0030300406c2d441321010071042400181800c03070903030744408007075503c000e901050707003081c0441e4003403103070380350f03060320500c08502002400083c2d00e4105110801c00d6440d400b840b50710141d81403908d0400e80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756787176 1250 756785926 756785977
    0x150c0307080612010f02090f01090b04092c0d0e010e010c11030a0b070c0c05030a030c110f06040f050a050603040f08031b19020f01050108030f0c0f190c0f050303 71
    0x40307608000d060f801e43c20701224404c03010280d8020942a4006d8581c04030700d04554006442c1510b040c80b03070301d0090000300800c204285040d0320012228158100031029050800035241c1d1410103900040b1694015554281c1480e402c00411400c100d828208400b4025556001038014444410003404801070015010440d0f6030074403880b00d2300369001c0300707665660411030001000888000f100712041600140b020806190014419509903416130f62400c1011003566040d0443c00c003003036074542260188114000f075a07030709805040030703080542e2050241490700040060454103680014001c0808000f40004242140c010142254006240d181c6d203403500ca941410548e426010341f00a00d0b000f1420804a41c524080300340b811089034201c402c0310304c82b014414200c070000e1080004a9008201003001d103260035019001721b80041094a80f141c024440702e80c103115180e00842030345980d88403800204040d03c0251809488845110003c030b50070800071994034410b03a2204411402250b02c1c09510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756788426 1250 756787176 756787189
    0x141015090e0c04030203060f010e0705070201031d061504051302010804020a21060506101d030313080304050307060c030f05030a021c0b120a030c020d0204060f0611150c03070806 78
    0x100031000600c41c40707280c1542c200c0d11640284c0401c0748a40944401318a0310f0004207100d605803181d80340c0741947d40c2c80c0c220003a101b603840540200d06064548408400c80d0610750101d40d42c4042c1040580304900d40782d224015505003160200d8459440d00702400303400c41800c4020b142c90f50303081c2041804c5403500c3c000181071001a5201a11429041891034403d050380c034a150342440c130440741030003942c07141c00420400140810a510004804440f480e9072003640b42d031480c0440c180a41500e1400310076500d0241d4103403054101c11641d600024003084103040800c8080024505032402007802384a07640d0090801b101800d400040140200100d90b10810340e60494140c001d043c000c1007140e0441180420150080c1c912043c07242c5101d003200e207090307000411030490866160761005042d103255401c2003c0407400d2041640c0240e0b41c1c3c40003040714150700401401400180c2ca41152140c6400d00c42880c10210304c2c1c8094940503800207202810342d2050a40340c000d05141400c103502da58039408a82c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756789676 1250 756788426 756788429
    0x140f06032701380a0303020c011206030308040f020a0b0c06040203070b0903150a0b121b0108010b0723010207050a1b03080f180a0f0e011a0a0c1103010c050a0314101509 74
    0x43c404c22180e000010190006690f00d960042a212070126410040003082159403c0c071015000c60407070000640010b8507481a0220544010f0510100548400366000c03150410f1180e5021544004e007030006518003000b401d4020f0035884201403070031001c400840c2d112544050481440c00901000c1610110550000468600064080c01c1c46194070030003541d5504011044030312919240f0f1100780d055200b443d480341640d0f4002d1041e803410784a961500300003a14020405684040c002900f10042801e00081904070f01501c0180300307459040c14101a9490404648808060b00c4041080002d00707a100f070310851000d221440307488017260382c800302022162911042c0e2184805101060710000c401e003640a41314165031390340f01e6030389030380b501c4031091030301d490a281545007031180c103543d644103101c200c98807480b07104036280a80500c070200342914040b85860b03021980c0452800a1160325114004140900d8407040d400d41c1040c142c449103c00f5640660041c90318104c0b10400d215006407080300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756790926 1250 756789676 756789679
    0xa0c020a141c030c1703042303091203070611040e0c030402010801090b0d1403031005011b060216050102040603050403080609060109031103030c061014100801140f0603270138 77
    0x480701d030404030020817580c5c001c54007180e100760300c208069a80045044042010b410381001507141c045030000f00304811818400b840b503144010442c400000380140600c01d00030b0804403446484a0801d094000b0700c10000b80004110b40c024010030000d81c2c2d101014a0440e100035100040304240d240c0404d20705143c81c040904042a209124003580400200a5120309800a08044419201c1004542030f060a00304032000d1003500484401040c07142d4010300c90200f800b03001c118989115034896081e40c120340c0c01507011076070f100b0802040c15007240306039502160403140940340b482c0c81d030006060701e42180405401c1c100e243c000301c1d9031910304004850100380040116556807500d00100e010400032405011b4800803d940f80c24018201a22001281e13140f031b845180d0141c0c00c0c8083c00b5040b48464001d2584080c44640e2900161103120045019480342e404501c40322903180c0d01e000701101c200039000507a0780b41c101c841c4c2c100c030300707080240c480d0b0600354a030401c2c020058001840744c0c501d01c0017001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756792176 1250 756790926 756790943
    0x114090f27060909070b0d02030702010204030212030d060e090d0c03140706091a0c0d0c05120106120516090603050405100507080a0c0e010e010c0f05030a0c020a141c030c 75
    0x700c08041d06001c15880380900321001c000d03e0b514845215241c18580c410a160160244071804c5200c0303954010315400149031000505007552030700090044220034555100d2508009001d001003102805400090040c66240d480241420300d0034565070560088903500701320001c0c07004010103100d8858121103000c45c1d404952164000c0c2809c60092904000440e00d0520b1241c10011162a0380c1103c4c0c4207402010358641441401114900506502601d4008100003000030854000300c0311006806050b0546e502c0e500a0081b0307441e0001c440000d8182c2c0340c201e24141c2d58203e05a80540554155a4140707000b0626407a580b80c442c0c0f41c20501001c00d51050300f84020001483c0d4000c006921070b105030801070000c00d074011415600d5200b80e0041074005510703518812030300d5000e000c00c0e5070001d200d0b80103102c3c1031186481c1d03241181c218010f000000b80c0007407a01429442c003540c5100113011101840148900d62000181141c5205404134420341211600c070000d050044050404158000c0e44a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756793426 1250 756792176 756792229
    0xc3103020918011d03041511060106110c0a0f05041107060c0f021630140c0a060527150301080303040308090a0210110304170d08060114090f 62
    0x2650352030044881840030661900d1103444c042c0f000d0b02c0c030300350701e11086001035850035042010440d031040c018242c6209000380c80172440900c41040100070f000345019500c0080d4007401460381410017130152002403041c51003c00901c0343d80f2040807058100e401c1218001144070140349554040e005094002d0481480c082070324100c19080240054052034650036601d07234085003011a40b1141484c0100d502104600e8a0500e00758084405601d100e0401c2c0141e1f541c0c1c00382642c030b10000d00050b4140c28000d42100342000c0e40340c2000140c6402802c800e0900508000080300c1445d80b001e014a82500d14015521798020036440f1b103021301d201c0d000f415403841e9a940e101d4650603070301d900030354040300007944800001f0291305003c11554407103540207004100700c1201e03220460b04a210925075520b00c0c041000300254109100020303c103920001c502810b070004182401402c401401007203541441078001c507018034030081d4000ca44021070704840c592031001c2a1404914200d030641d07100f00780025403a10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756794676 1250 756793426 756793441
    0x50d15080303062b020d060902100306050109050105120c03071b1a0c2d040504060f180b0303031603020d092301110d0b04091212050c31030209 63
    0x641c850034040c1c0d01c0103088004080840040c1d4000d011311102c007122001500014580008a110101d0007150081025840b03a00050b185030504444180400c0d030f1030104020a58003e00721900809090800700d0400c034104252407207055005201c40d003074580010004520382e00444600b86240d1039480200c03800c4545185c1394840000941d00600a09100d00000f4000c00030700381200c40d0444800003402440703241c6060328902c60030748407600109100900010840e51602e214810007005035403606c03c070007443e1800b0550103440900e542c02045040c45040c036042c6d240003003100c0d00401c3c006140380c3c00300132034034040307000340542d0942c5d110550901e0142c41c144000403c3c0c10303843c858103910010340811070580840c01c0320408030080020301401d0000d5007026400740d004010310403014001081c1541c00e07640e1510852481404035010440301e50f80c0c101d06010600c18103500001c0c1c0c1d00210b03d000c480b090800c071403c44118240c0f8a608407580022162084810050000d40e809020300c501c41c2029071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756795926 1250 756794676 756794683
    0x14070312021f0204030305180a0b030a0603021813030f020f1603020f0907021009080405090726040213020a020c0a030c1802090a0902070212030304210807020d050d1508 74
    0x62560003410ba458140a0310a80381c030071902141d0341903e80ba841d129a1030240f4038215482e50440754003580c0070078000780c0032400b03c0046204007480b140004416082d0720410954405582084200d00010400c00401e048100000c80d41250181840702d20b0301002201285000310190056031a800790032049450040d65002040c1548d1085801801d0805400244000c44008645803001a44000d80711068901d1961040003900d0043d2280c1313140c03030348071004120314000c25140c08000604004010060208400307081d20302000700600c504444c2055000101c40d9030017080030008140d400200f6000c1140201300c580c1e010742e005000b05841c59580e0610b0002180f06101d2407044600310703030b2000700c05201c030b1084494000740105105a201c0c00c003480d001c02908078130750480c0c00000f04c00e0109031941040016510540c0325014642040d071800018140380100d800e01340302031107a5070052040c3c4a40100b05d0003410b8026107400341d110004205224040c1c4040350050800801010340400c1e41e90011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756797176 1250 756795926 756795943
    0xd0c020f0f19061827240308031008060702030304110d0f1a070f05160f0c0b0d0f020906030a0f0b0d0b040b010608060d030e03070302060f1804181407031202 69
    0x61004003081d0317580703000002a808a40a41c0e10842c91025001c401503806603000900c80c100101e001b06140ca020050806050115041901d881c080402001140c19190041c1e0018102078009045a400e082d5000f80d5280030103000185280500000e5034801c1c0ca42c213101d41e600d980c01041488090751542002c2c40700c180100c4280340e4240b00c8070300080b080f43c002c02d4907189400350b5a890303501d0314002c03c103421940c1840d030504490036140d40300e0210214129081c00e402400000655941d9401c3c0c80c40c250301260b1103904840c64032401802813100b5651614140d0b940310b5012900401c00c0d244400c01c4000602c81180c0642c0c0c0640b80603182c134107002c19150003502c01c40c410036031154140d807114000d50b407407442200c609611004054054000078400c05040e10302c5000a000c88030720300e80b01d40c0000c403a90041c0744100010342c004203882566010b2003c1c0707088480c1c001d645c2004444841441c3c20361801d0801c034054112002d403804049e020b0010000c1c41c00460300718581d155900349000d0000c1d10745202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756798426 1250 756797176 756797207
    0x20703030f110909240108090a050618010b030a02010c0b060316080a060b031b060f040807030f02100e060301050d0215070305073e0102010e07080607020d0c020f0f1906 74
    0x2d8000100c4d004a2490046450403001c030402c0c0300c0c004011700451701800010100301440c0544502100082c104100e400c1c010f5144895020f58090401c01660860740441001403103540520b03006800350741c02210400c18560021a0740c0c4140c3d49020100c1d00c2c0c114580304859000c0c101a50000c2d4018010440101980c411907081c000180344c80101a82c6071204101c3c400000851469003000c0e1805800400340e184e00b00e45250302701552100c0701c1d4104070b000c1e4016500c1c008030450318011440c1034003181e010042141080c1400c07884480c0402c0440c08140030f050f020304144001e010565950a205c0841c0b08e0702003880aa46038814074004086400103501220b008080403a0700f140300e00030524214007034034000141d160b0509640054113424014035405030655507121418401001e080c030803400a0030b0400300400a506118038000d10302842d481c0d65204100302040194016a1a1000b418a80d43d003107400c0d0705004182c500091815000d03580c054180401180d0008116800c101048100680d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756799676 1250 756798426 756798439
    0x17030a0605060c101d060f0f09030c210c0610080d170a0207030c151505060a170406230601020d030207020108070f02070f03030809010b030c030709020703030f1109 72
    0x50721000d100050044081107006908102d0184040c03802d180c3c0f20764200300c0c0d45c15451114003007206a41c0c0c10100d090310042d02c421036076810040c801180c000f036a0380090503800214a001d0110702075986641c004c5004c00300100b400d0380d220f014101c1c440c05655180c01e01b5401e4503006d0800804d44000507405214144950040c011030b5a00e990044010441c84d050200940059503034080310500250f104e040110180f0000314101d0022889007001004a03903424500082c2ca90b0091b0f01d08490324203a6403155104500402034100455030000e111080340d8100c030302404503910b80e40750180241c042c006241c00c1031402c94134116900400005014007400b802c0e002e54001940302c1200300c09903c515030f40a40424024808591b440b032040a144d45601501e10543d4100d5031179654034a00c0648552080d00015050400e2056070b0400703100f100c0e41100110000c100042a8a01180e1109101c0c40761029256020030700809160103900103c08807510004208081c5018442c06031203500804141e500400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756800926 1250 756799676 756799679
    0x71202190309021f09060e06070c090b0f0a050a060815032b1701120c0308030705180a030c0315110d021801030e03091017072d1d010c17030a06 63
    0x842c0304e2a409020311580d0344648070320303050030402d4596210506000360400420402c80b4003084200345020040d040304500030480c21000b03010040e001c034440001510600d04560104010303581c09c00410100c622a0034070928590700d041c1c91868030b014503000c003500b602460692a0400554140030950309142407809049004603150480e1000c540400402c403002d4440e00501201d0f400520140b84d091052a10f07108160300c076912140150010703141500400c0022a0520740e0513031289260180100540f0800011450342e20b401c000c100043c4000350004a01b0310482200c40429003001c0b0007092580e140791341e651400c8407a003000758080c2c2d0030004040c006080503800c541c4640100c0d4886c0c00014010f6050010820400c801c02020302611024040d0000841c00c0a0742c00d142c00c07611484031501c1c2e510440095030341404200d804600c402c101100c44405400c03c464014600d40d00d40128401042244c0b1881001138642040d00080a04840d0103522150200006100294816014484240f0625 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756802176 1250 756800926 756800959
    0x504050a0e060102070909050f011e0b030613080901140703021506241303230d0f020307060c110105040c080c010c0c140406050d05030901021c0807120219030902 71
    0x144410740b141401600648001c2190340d03281e42008600c2c80c040d01c241c030f040d5400c0b41105401c4814009400001100007551f0118290b10b5100e40900088183c024000350710704028803c41c070718400c11005000e83c0021500c00301c2640b00300e55822400c84c0c00c0e8809039540102d400c0c041d540312100d40081100ba100350340014401e081407403075022002000304002e0081016401c500304c0503081445d079484102c00c0d1903000000314003900140d01d10780203502c402e80520b4940e000070900b00200300501c1810f1001d12440b80d840c0d80c0e0300200b140c61054200342c0c00036111407444070484d00d40000c0603000c00e040d801c082c24081840501c1d0100c5044401010480e8466050341e0010340301038003d140d02611780d40382d5003030410803808500e003e2504048010f0001400c5601da00004010804410041d03d0381e034404601203509580403c06060004e504a01004803040007100c01801d003039000307050b40c003040840120b01204000b1501901c3e800d203000d0301c0740c0b07400b101c0c9148018000c01d03e484003070b8421920342d60018642d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756803426 1250 756802176 756802199
    0x30706021b04060312030911030106121a06130c0e1201230907031b0b1b010b0603010b0405010c03110d020d170705340b0601030f0c021c0203120103030504050a 70
    0x1241c5d440650b001d516800308805800501c00f658040c0d640c205008400002c0b56000e1080c0f078003411528096100304401030030b181c800d008400c1d0f4908103400c0041c050201c41c2d51030680d044400f44011034045200484c101e07040702c0b40404490003503000194141c002c80e5101c4190007aa07655000d42410071500354040469080950040d1128400ba400400081c004615a0207842144003500390080c854540d40340c44004040d440b0540c8000d502c044480c0c0c8107002c1c0000c0c003440c00240320840b5810b0031541894000c1c038041c400d911465041c0003020075002d027050b001c0d0403085910703400941520013a8004c11006501c468401d01101d0029505241e01b0b80b0701002c540b1440c1c0191042e546040c20003e0152041d40c1d40005004420301c01e5644030841c000c40000d18014400251084900000504280c400517044d9200ba41020b206181030800710040242d00050b0451028001c5140000611011000342c2c21032250710348103040b1240e0940080309143d0400010411204207840320141c507955010300145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756804676 1250 756803426 756803429
    0x5010f030209280c030e071d0718090e0a0f0809100c0b040618080406030f060602010c0f0518090112120203030906010e0406020f03070e030d112109030706021b0406 72
    0x750120500504043d92010360302801c4400c00303d09000411110000c160391420704283d0001d14812186070300440381c00d00c1c11004d00c4c1c018041c1c0c1051781082085c07603c040748a5445000c0c48500c2646c60084405901003000131401460700803016078404c81050800c60480c1e400409061f005005441c698851036104041ca94403207508404184450741719036031000301808042d1303000b070500d480c40f401560100d50058000d00003072056440000f0340413400c03049041070710710b1984042e0640e4500244540555041219090410010324000760380b008002c2140c00f626010140320394000c03412100114540303e20280c2e50710300a002d0300801c2e002041c04003040365a48411912405a90072401c01044050710b0140040e40041c4140800350520580600b1800c4540084540d500026044000820141400d0054044c00f005514018404001c8003441c03903a1103050f00034240540350b446286854054051050b03600c0c095004084d5043c969a440c030096540310140210940d4015104065841380b13440d114400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756805926 1250 756804676 756804721
    0xd0606090812040b090402090310060504060e06180a020415050702041401030203070303030209010c0807051b100509011103190f0e0d0b010b0a1206081e030a08220605010f030209 78
    0x603e06030401198243d550400760a00e0380083c2c0030b2000040c2c03a0340910281072030304043c0c01c00044091800041009503070242d40700740000042001480b8540e00c030324040319142d0039401c51966a03911a0b00c03002c4024812030f8000b05000b0520000d1503070341070713100340200400c0303008540502c1454000b8214003140036080c80000d6040e4850300b01040000d009401404010360141000c65032810703d600c07404203940c0154000c4400b6000075200c00d1a4803612000c506240e10141e802080c808400d082c007030107610503410000d0500400101e80c43d500310040044501d12007110054103258056004c000e81a042d0000d90300c00170440c208070a5555080212848103029007110352003041ea4070b00202e40d8510b5000081220400c150004400803100700c9029000040440c54020071000000710710700642e01488000301c01d841d81003009441003590344000c0c1241c00c100141041d1400790080d590300142c90004140003015241081d0001501c1c60206c807000007141e000f0355500300269680b406001c2c0c0100c1500026 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756807176 1250 756805926 756805963
    0xa1a0f121903110c280e041112060f0a2c0c0a140d12030e070e090d020c03060f06011e05180619201b03210708031b0d06060908 56
    0x481d180391005c0d52201003110340b003484203107040d103800503078080c0c0204072019a01c80741c820759055200e0410051202c2d0141303c40001d0012418a001c248821940c0075100d010910340307440700403504c04010818002440e0492006d1050289001d0100d80c41d46690350045115911140000885050f061748a9078072440003040d40040d8400356440d04080382c4540018000c05549205c1e18070b07108030810541c1c0c05031080d01c0c06443c1d9840d00006540c1b80040c0c030040e103c01c640040c3d210360040d4900184458000d20200d845901c26070f41e9400482d40111400150984d04400790b030800d03011904100140106084015600902400c100512415218620880080f486108802e0010b01d1248216141f002025500c02000001184c11985001002c0b04490304d0002445102e8496180800c941c101c4445400300c004444090031034071000c180544140075008030b40000001d80140505440000340791a010300c01e540b00c9451f201500010550b9000c0c035004960b0010010948000c0041c3e850b501844250b940e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756808426 1250 756807176 756807199
    0x70e0c040608071b02060c0a05060105041406090601020114180c040516030e10020a260103120c052e050106090b04030311070801140f0a1a0f121903110c 67
    0x101d85030f5180c408a169004d500081c001c0042c0d0741c0d0342c010400400f141c8010000d0303c05605216040038010380c02280700c1e5140178001e81c104000c1c3c15825520490172180310040703541d5000185d01420700c1e16420203124035104104181c4180010800c6680401d030800c5440611001050000b06c0318152036141c00107070070010f0710a0081c465041041c0007000031059840c940403003145c1ea02a0b0b00b160b401c1c1008149050305540d420300321a01c443c003c00101404941300c035403450716074a85071184901403508000d8541e9660003030240410280442c0e54001407490254003101e0120104086844040400a0300b07040000070038034400c032a04415a085196100d02c0c0a1840d81c0688148400030754282043c00740c0000000d41a200384120b000c5080281440440340c81c000c54a08104c2000801c00d1200303e1a000c400302000c010b0341c0c105660040180e80c0d21503800b465a000854480b101c90080041e07101e1700441074100842604e41c003600c28425100c03c1c00d0140d00303030801070711030f4061502c3d9604801c12082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756809676 1250 756808426 756808441
    0x120207060305100e060a080f0d1416080d2a02010506040603020a06051308060a1b090f06030b0402090915030f06060616150c0507030e2e170405070e0c040608 69
    0x418641000740200303c030304025610f01030b02d41030603000380c594402500424000c10759030781c01240d000601c01c107410b8035600d000c0c0603051902500900c00b00c094030580000c01c7c10b00103681c041d1301c01809074501d8012810ec0003e012400d1500b0349038102000019400e020203c0d101d404c09000b403106403580103050780d04460800000310707042c0d000200d0025402100d59400210640284400f0b40100c807001c502246411480452558041013481003004100040c8410005031000042c2d420a0750550b02c5c1c00319070348003514001000380c080d04c240c4a41c0150702809205134510a458450303000c0906400303649103480b09a1900b0b8175140700b185e03241d8109408110403a003c40f858885001c00901c40c094100c2084207040d625021684402e1201000c030320b00059a50605800c40345015105108440e20966105038004210300c00c4903c3c03449054a6041b02c140084050060078082c0304859207000440e618601405e180d60744030514440c21055000d10030200c3c00850341441101c0c1595403070344608505440701803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756810926 1250 756809676 756809699
    0x203060d120e041a01260105060f0d0e0c041107050c0906120a1208330a150305010e070203070503180a180203090606120a08070606090912020706030510 67
    0x600340300800032020a0540c260340d480c0309003107290544c9000ca00c00d102d2064005000c90100c1c40e00d4103809030380f0301d0544070610218100103043d0ba00540b529074888124980d1108140503241031098a1070400342e03008051800042c01031f441031004c4900740022030880c0c2501181c1d00c900c91024040360001c2d41200d4142c1000c0e00042e4103c0d40103420041c0e0354a6100803036040000c9981c0441c1c80e0481d0400740000290310003407180d0003011020760112102440702140001034068400409906030010380e0244a642d4941445c0050103600e451504c41840285c006002382001d01994481c4602d840224070703618800003d4408843e44a402145444001c0d02140403203a6a007048035400a803c01010400d600e10792641c1c404120000c0e8051303160704140b035095040900c02050180160206600d4088800000402d03081c0c1e035400010071607032442107090000c0500910381140c078449007454101c0041003442400d405c100c0c12540e09503a0f109441d46004c038280c5a007520700c4001d0b180c0200f4103215191050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756812176 1250 756810926 756810953
    0x6050c0309060f09090108030d0f05130f2a0303120c0504052806030203180105060102100f0b1e03060a0603030e041805011104060201060605071713031e020a06030203060d 75
    0x420030a4140324860b000241d100744241c0147c45240c0020031003000350382c21070240c40000f0103101030030300282c0b412840e10602e41d5151500613005c20760304a041c0c2e044c05404007820240011f81d407551001031007600c00d0084103050a10003180060b0600c010104024214450340327000d4030740741e45c0b598501446d0400304006800d03414050039008240d441c0480002c2c910140d50001000e00740c4000d41c0342c3c03804400c0081c900781400c0b0010fa99904100c01c1210907a804a94044441050000000c0f001e00c9100303008004e00004600d15001016801c070340d400403c200348100100b07501141111410741c0c480a030b0750141c0b6001c2c8401400705110783c880a40da8501500514402e60b003216440300c0300c1c1802c0d1141802c0d40c25508400120311800107040c4000e40e82030080d40090701580c24460b160041d1a9943e03400840c603081c4402e8500303404920080c14819902407030b402141c01c941c1f81c0d00801e51010241401e450b20740800c074071481c038032040042c00c48c0c003d00903284a944000d00b402c2c03c03220143c445010341600c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756813426 1250 756812176 756812197
    0x6010f050c07090b0a091b030c03140f2a030402010f140a271206050a1e020408060708012108091305010f08061021080d0c0906050c030906 61
    0x611800e2005941000a02e00402d00120007240c410f04482c20710000c0710701500300b00d00250404540404450700328000324107031400342c540050b104e0b0611004600401003078038a91807500381030017884121125604a64022034420100124180c000c0d441d00100485a90308030b140303400d00340002000b5601840034074900a1303203800d1100001c040c10300703400c2266011310728010100300c104011048600340390a44070300c203560344000b421095003428452444868030450092500741c41d031b00015925003107900030700c121403482142001001c05425010010f9040f034014004a0700c54800003401c828410865035040f1040e80d4540d101642110920400d8445d420400351a809030400c54170640d5100c0e040c2c0354403003520345100000c50f9410000c0c0e5060500f00313076111101070350000c024000485180c180302002c442e000c0f0401165045a9108482c40703550540c406001044007107400402c8040d01e4100081c947e40d1903850300501c0741c50710016101c602035504200c0880e48140040c0c046410200024031107101c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756814676 1250 756813426 756813437
    0x20306041202150f0702100c0e0d080d0c020d1803150f1103010b07030206060406030314131206060519260f071d07080c070f0f380f06010f 61
    0x210101000f108001c16500d242843d01d68100700612158184184040510031101c10302c02c015050703d00a040317011100c802c0340f1801c0117001a07020000c1010071a441c0c415194400c9c0403210a692002e0349900390b0b500702d84003043c4101580c0c0300c0c04d850480c0f28020b490b0b0001d4604503400c465101d020050034580b2030000c6841c2d9500c240010050341c04050740c0241414104940d4884140c41d000342071207030203803a043c06182402014000a50081c600414a01c12340c0c1348540c4601031a03058102c44841584003e294075803001200c420311030940c000a050302c0050b211800c2c8a20095406200010540320300391558048215040014440780c070f0303c2c0341c0f00c2c02c0c140403600c01200da00ca0300e0307040c006030358080341c0305061303d003008001c0381c507402c091580c041d015090840040ca0050440c00c602d00c15032074010301c000c10022805040020f030f004074128980e00010245a100d0a144010035608900112200c1c01000d9516101c051070f4082c29252168100326070b40812074403070304019101204010243d134103202c0f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756815926 1250 756814676 756814693
    0x2041a0901270207081e21010e0411060d0903030506041802130b0f1c030f020f030708300f0615041205070b0c01020405041b05270d03080906070c020306041202 70
    0xc00c1d402c0c0d01c00200c140c400c0d90503071300c003140c142c4c08170703c090038003400321440f601000100a1109d1620071107602c00e811503643c1604061641c00224175108510951084d070745018400814554142d01941c400d05083c0c40801002409403006109612800b80080d071080740c40d00002180c0b08150054481e035007014020281b00c00003180011040344803801030705c241c4403010003031100341036100c1100d020a04081c00584803000d4801c207100d40300c2c03141c4840503003e40800a1842c680f0f040744c1c0f81008020840d07880304061801d400d1040c080701b82085e82e6031841015801c0219141d031070104200703111942c645e0449031905143c2060460076210461003a81d15004031440000c030340b0030766030052450444c010001a40c441c02c1408200440f0b0620172070542ca5180344880314001034104044640801c0303d92110311662840c04080b0781400c881d140100d8000b2200607000d01016048a0124010064171065414540c0d5484049414040d0340e840130358158851000306c1d01003100411907188007507807881030300c0c400b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756817176 1250 756815926 756815947
    0x302032a0d051f05010f0614090603090a0302060709050616050f1615050708030121050d0c060501092a050c07140306060a0305070501030b030a02041a090127020708 72
    0x31014181c1c151155040055800c81e8507403415070b07018440310b20034001c00295041a12620714101a4058031003440034030320000024042c64410b4034402d4100810b441d59034945a03400b6912038882d101c00f20058424403005c500d00c035002d10fa0f040e045d181c0150036142400d844580107040c00032a42410340e041d003c1c0306040c02c16071109009050080300b44000e044c0650f4908107039560f820151420380380c10440d050100da40060106c200301c03030450780b400c3d041d0520383c007000c104080590402e0710010705c80d105141070180c89942000003180784600031182000140c2c3ea0300d0801c81621030b40340d9408111440a0f980e960380d400001902d51044000d4940a400e01e41007a140614182450b000000c4852058503020310a01d400c0151561014003500e100501528581d21107503680494001c25040c103480e1411040107450400845e40c40326002001800305038505843c1c45454800303419001d0042d2946400032030025143e15680c00b15201d0303420310681087c000c12020000b50490102126240c10401690707842 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756818426 1250 756817176 756817189
    0x62d0e191d0f012405090118031412040803070f2306100503030702030606012006010e180a0314070602040e040c0905090d1d01030204031704080c0105040302032a 71
    0x5504180c00d6000d072504141c1d201c0408000141e001e0145034030900e40300800c51140c1d40340007001d6955402d100e030302d9024160050303510300503c00c101416904902000014810280c2076404000c80040948400e65040e4213003403e2441140505030302540208200000030301400c030302e07401c80c0f8001d0010100c3c1505503401940225000751210040b54044c03014002d01207038403011940100400c8009524084895003c0f0303440304001021541800492110507089844a17440d000041e81c02c80e0070b694035980c507800080c00301c2c1000e5903184c0d040c4100702e144913514580064540d11450701a22016448011001e01c00c01691100e54102c0e2030a0b000d100c009189110382d103131140118401c1e01840044c0e4144a02c110403518010221100d650000841010072900701180030b003194400603140c070380c000d03a160068010744115071009011000e40b00c0d800c1044500400648251150202034540d81c10001e0300440e46401076000181d03040c0c0005100c4110040c5918031840c504041040d007030208030300900000c40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756819676 1250 756818426 756818459
    0xc01081e0402210f010e060c1809070504120c031b061215090c0503040506070503130f020d02060a0807020c150a030507170705220f0e0c040807062d0e19 67
    0x80c1a91901d0480941100030b124446e0304c03000d84031b0a6401c010410002d54021000c100c01d18ac013480c11000401c8403148104100c0703020702400c2d0800300700020300b4980303145202d0140c441918855440d0b80c0e0000840c40d41c542c11002c50b10345548450802c469107130184010543c80720400c5c0c52101c40e401c0010403c00707a014003403035503000b612420346902e41400d0450410704001c2c04074007081341c1081040f4286c2000042c4004050300070800d400c02c00000c0c800b2500842100c0d2004e54882800300b801d83c078807913101200501c100c0c031950070385800442410600107020180003242007585024000302411610a40c4103952100c00c078900924941c2829001c000800f009540c0840000c60008840a41d540581003d4504052015880511918040c4000c0160b46540a080820070000d00881c2c24001510b0603039018082c032205613040d035a0f5424000d000000c042151810f441c40ca030762402c14011000002c480000c2e02c1c0e031680e8480410500400c80c0c80c0d41c50300619050f0b40382c828000f2038003c504481902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 756820926 1250 756819676 756819703
    0x14100201270b070c03020d0c06110c01060303091d060d0812091c05040e040f210f080603010e0a080a020304090f02070606081c080c0f0c0c01081e040221 67
    0x5503180a41000303a1002001407883c8180043d0705407110000340d00160404251000d45410720179003031280380c0785000d406c0b00c15000b1004c01c0081a200070445041d805081260f109844100359141d40f0540d1035084103010601c10391030481d5000064160a00c4200002c880307103d160000d15245140c14451310f400300c03c0d15641900c1e84100101808281c4001012212051500700380b803c141c600500d85d00310750002031008007c200c01080041c2041030201441e5000d2840120007200007829010081884014a40d07400003c0c101e40b020a241c0d007410b22400861840c00c102514841380983c407000380325404202e5801c00c40c4820400010b04801512888030010b103c140b0240e80c80040d41001d5050301c40d80d40181d00507400080481200703620b40d200800e04001c1d181064010350365503150b030b60303072a020740b0395003010501d000600c4150160002c282d10501c502d007621040502d03141c9030b200b0b440180a002504c980081076401050252401124001b10081028540b56000e203a41c1200340c03c040707404180c1d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 756822176 1250 756820926 756820991
    0x70306030c0f0503030d0c020a140d0201110909070c050f0a0b04050c030102030c0412080702040e0d090e010b16080403020a0305150108030901080a0e160b0d06050402030114100201 79
    0x600801c190340c00080010706aa0022075100380c100000282c42e0b00c02c02e80040b500380d50701c12103140c1c01070092206c4106903400001c82e41d07001c0404c0144a40303c02c0300d2118407005500c0c0c0255500e01d075401c1019100b40301c401a10154030b60341d4540d0290b50381c11921030152003030711483e490140e40b460100905080d0031701ca401c905c1414105890810f16201101072258404c0e40144100320358141c1810a07281103505038052000c080c449414114401c0c8110303103029401a081c0303e040e06130a0000a00003450503200d07aa00410981d403140c203002051402e01803460381d184200400041204204218145680501d40c19840c099803507000039000c1c540d50788100e4850300080c0452030904900310a031401042242d01441c5000c2ca03c0c00000c0140c203004110b010401e03558044010442d904000c0954000d011400005400380c03107080f000d9054111102c0e811b030075420a107000c150303070405c1c8c000c1d17a040b16100c071030b508800001d100400c00300d500b142184000b1907590b40f07055004140c465180218900c000c400c03c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 756823426 1250 756822176 756822179
    0x9020c07030515040218130f060522080405010507151503231207030c0501050c090f0402070c030803040f0602031e01091e050a0f09060209010206060306150d02010e0603070306 77
    0xa410b2500f4400c42d412000b05203810000540c0742c4a03480080c0b10942c8203001d10545e903400501c062045044805450304c0c2205405070100b045590281380280445122040c040c00b401a00b0256091790210082c0101d005000c20001075000750b018201c40e9103e40740c00074130b22540380c1c01402120890214010009081001002400702c000310a80c042c84441c0311241031070a1502c0d1a41c0d89801d0202c02e40034007500043c1d000c003414820003900e001164408024400d5007802c039886c11032a0005500305100c1c031922114148545003601c201ca044550040890740300614540b1141c03140e4100400580b00030482c024100c000890074401103101c0e141619605004100161018410b0b900582050800c18540301601c3d402e0020a00c649035110382502d030210b03040d628504c10f80040e0078112244030302581080d1050040001c50380141040301c03420303400c03a1401d0791100101603460030141d030100c01030744010f43c45101e40c0c10320703071200c0b04d8150043c10448000341c024008a4045d902c2283c41c100003e035113550 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 756824676 1250 756823426 756823433
    0xd06090602071e110f0414100f0519150c0f0501060303080121020f1207080a0605100515160206180406171e160608011e030c0603020309010609020c0703 67
    0x31401150302c1c03d002105468a507a81c6940303038075003607150491080d003508000800b83da03100c4c1c200c8084544a078900001c00d00b02018540000b00140c081c02c41c100c4541c4001090a0926081c17641c10074404c0c1143c81145480c04429800007440e008100e020089545190030102e4040244030301c1a0f442074000044403451400d00070901c2806821101141540344442d00c02c0780203090911400e950100c9105115414620010300021440b010b100c0740c50140c0e070b10000e4400008140000100c1c0182c405104640d00c59a041c410381c00280607955200010490607546d0003850340c0502041e80c84200f99910b03c0103035400151b01600459040e2841080d00b0100b296a0f0a00d03000390801040600001050315201101640c0c480841a402da0070f00c004480400290000801c4410301e500c80c50040c1d00c1d001516020020f005850900440002d401ca41012401c0501c52070400421241c00c071070700c9210642030090440281d1320152800081d503423a9280400c2232580c51001b080101810340040c11001d1443c030b07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 756825926 1250 756824676 756824693
    0x906020606040b011e090905011d160f141e030106033b0c0a1d01080f03190e2206140a0504090c0801090308040b0c16030e0d0609060207 60
    0x20503040c0107600f010340c03500481c1d0708500009a031240a820080d117a0084070702c1142c2220081d030011000c203080c08000244a05100c4604000700d8240800c0c0d11030b551810240940400005900c10009040041340700b0f20034810b5003a000da00c040c862540d40f6002c66141319441d4031441c8401ca41c909000000104480c0f605481020040c82c0c4000d110003070390428420324090462031b40c148200a50505c026900000720074001102d400c04010800009252503201c20104507501f240300344400c15468002003815140004d84c00c020020f1003000f5403800305054100d85d0b0301c0321030001e6401401099040070020f0794a0000c0c041948071401419600c92106500e003c09654071640890b840125000f00714049803201003401d02542d42c05d031004185a03c1c01e1402d60401241c40d4008041546054494000c041c2d0000d4000c1c05140101e021014903107841111082904c030b04810000c03920032010309080040e01842008400120062030a0118580d0381c486d441a2014040126100c075400682a41000b5158 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 756827176 1250 756825926 756825931
    0x5030f0a031a010f092303010e03090f061207390309090606120902030a120504050906120a020904030e030a03080a0c020304080d05220b071403270a08030a09060206 72
    0x1d04e0038003100d150311030014003e96410b00409028a18800302c05106d84c0c00350000c2c006003c4050b00070009541e5001609803603030010b8800501c81c2441481640c083d151120680722151610709020803161504402036451203110410078405a10f5030085d501c80e549401e00c0c1c201582007082c41032403072140da0718008090640d150000501c051a003c010f011721903110b19aa2512594204000740e0ba60940c00000e00d05002d2043c0100b544401c0503808000942c00006001122030580788400d40b600c07a9010400d550b1a5490a19070350760041c544000546454160b880d00140603080103015600c0b0100032134105201541d0603000306000c078040c00031014491141c41d001984c5031001d542040d0070030030b5803915502080c846208000303001c12001c0d0040707405034011905c280801082c3d6881540d9158904c0b00380c12060040d03d58101440c0100503488c4048129a4001e41078000b0307129404460410700c03840407052002d903030003820918020805c640f00b0001081101d1484c0c40d4800d180d85481402403034100c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 756828426 1250 756827176 756827179
    0x16030f0504060c020607050703170a120506061c06170f06061203030f07030204180e0d230c10111210120303020901023a0c020f060705030f0a031a 64
    0x1c000070001603921850801400390b044580c1e0740e68088604000d0716010a07078002600030001824003071801a01c01d00104140320140e25090b00c0c048803900e540702120310440310309821203401c0145001c110f2440d810740d0004e40310502d000418a0300c64210840281c2c022302030701c02c2d560140725450030141003040681c1e801302085680000b1030f020f2003810380e120300018100c1d640711013241020601807806601035038050b02905040c1c10350385500042c108090500014490118003801c8440020070307104c0c0c500c1c0545982c91139078502001980c82d400100e031ba8018400100305020381500a180c22070740e03003d10001600601c03601902c3d042440e249150f410406041d0100051107414100a0300c44140c11039025250135050050302c51a1540044c3d0405da800210a81c4141030464002600707003c20040a80b1115404009198500e8412050341c40041801c0f02030760148500c54090441d19000004000c420310500650f8140b20b120840c1c043c035500320850700741c04030780c41e0070081440300c01e55600c0c010300311070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 756829676 1250 756828426 756828437
    0x6060e01030b312405151c23010c0206060109150903030f1202040e09010b060a080f070306030b0a0e010f20030a0b150304050d0c0224090a09020d0b0f03060a05070c0816030f 76
    0xa1428a0410320700c003c7c0018002904151222103500906800000414643c0000d011800c0320000084d228001101e00c01d021480d209000321718100c601000c8020741107a40ca42141306421350701c0a4030300b5004d48240ca810003900c10b00c0d280400410380050001041d9103404c01800781000003141d401d42c2c003654003080c0039107400e108902a0540c40309019401424558111802c1d803035002040b006400035410141c22852040c0c180112121070340e01c0a6a00b44071070008105641c410880d6106443c80c442d0406088106840f541c200c4103d5035004580204c0c40d02c50009981d0b611402040240622a0010f222283c1c00300c100000e20000340526041c6a219150040003000303142e00052003400c8011031401f6221182d654105031860381c01c11200c032014028285521560781c1d00710400690303c10602d810344c044c1040e01c1c11441d0f08083c4100a0302c0781005000d001d180d070380c00d4031610017003500411240400001300c180402181659004104007401c2d01d143c1042c030f00080c2400b40400140070a030504108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 756830926 1250 756829676 756829699
    0xd0501081b030607050c0c1c05012901030e03130b120702160b0304050a02040e01150f0509071b0c0b03010501081e2206060e01030b31240515 62
    0x354081412a8041d50724244181c82d0381c1311b0ba181030702d818042035106030413078001000081040d400c5180203590510400003400642042c0252600007020f81052205001814210711040e40c005d070407010321100c3e2641100d0804040c1c4042840e007000c60340c0a030354040c400050320001418800341c202d1b40002680010807103002c04202d10f00150119204000300c41d500030010804101d018004403c545400030010b00014100212507802424130000076103108082400000d41c07402d182074641c04176a0f005010140035541d20209483c0b001140c40303903502d001014121600010040303c0c040029240301c4400035200c1d07052200150034103201504000204189000415044200090543c2e0100b842e0034194041030b03440401131109c0c3d1030304400030070341810514080354409924200904890003404407000c9a01d48071500c581c13621402d0700f10110406010142000c01e0900c0e100491000d106036680b07620543c0c0e00400b1b4119805c00103200540784e0b282c00c14003100d800350700c0800b0101c1e5411642d07041c000b07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 756832176 1250 756830926 756830929
    0x9060e030d051b01050f090705012c010c080309060f0a090c1436130f26030a050108010f0209030a0b04020103020f07061b050a080f0603070b0d0501081b 67
    0x31480c0310036007001c00c40002034080b00190a6105220a00854070081c020f03802c005500d91014001102e2a81d103922600d14005020343c450070040501d01c05151130480710b000d016241002c0d0104d8004a42c0c1401003556001e030000b4841d000035032080c190100580003e041a2524a403004005400c0021260801100601048280c54080d00700da01c07580030085c180c2a41004101c2d9115000b61801201c42000144132944d07501d4140f4080c6141c460700c0c9001240d540e4810200429403100e00a00400000111080061500118480c80f81d4183c0c0d41140140076a1410701282d52003114018a1161a01d00402550f0780074010b0f42036806400300c1c1582019400b801080ea10b14103c50007030101c0d2603035004030701964002c0c0c2c101c5041d00e1003440c245690349103a041c41c0f030160111808445080d030060b560003500313612940507103042c0d640540e40c00320305443c4d01c0c5540400d100301400e801e6060049407c002241a1074000520003a003280310082101e40c58042c61030b0030800c0e548400c03050f24a20a403c1c401a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 756833426 1250 756832176 756832183
    0x708010503030909101214070f06120f020d050a0b0102070e07121119021b04020306212d1204030b060d060e06190e07060e10052203020109060e03 64
    0x7204016500c140150791034160114499a42c0d502540e02600840740e90400e10107c0c41c2d00a002d00c0b807450031242c5865550b940d00303000c007040341b00b0107002681d0350107031801504850f0841d0b119103c2c000c402608000ca0140208102d44054920840c9255201c031000c066580600281c0300901c4042a0405d003482c00c2100a48883c440d110b1854406030340e9443c00f020500741006542100b00840c4111a0041500340003a596103100c0540410b11002c902c0c000d00a0701d400c0c001c81c1c0c03082d240507010381042d404502da1304a0b00c03c0c60982030501402039220b450400345000c01da500c0c4030f00f2441d02030040f5544501c941070034500114918210488100414004600d42290076900000150742c0c8500e020000e04000004284401d2a1003d9024010501416010810308903a08900b4030b07100b003112000040038183e0750041ca00c106004982e0070030440c0000d01c0d042001c1031254005090252420361440800d004800c0e5041c002c18401c14071007024400e559100200038090041400d00d0201c10760000000b070b55 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 756834532 1106 756833426 756833437
    0x90706110316060b1c080a14030907141203070602030604060b091509060f0c06040b0f1003120908100c030b030d050f0912070603050f070801050303 65
    0xc001101108072a6a401a103410681c0c00c202590703001c1c098046401d40b60382c480624050341c40c036402c294924141d124030545c1210f40d515203c1c500945104190410301c0b441050600802c0010b40c000100c220903038a1413661311101044d59030004402001c204044074a034000414000c042112a40103180a15000c030b07410f001d22512410781060768010400016488503a0110034041c060307600c80101800e940190920345442000620250b695100b1820162664031000c1000244540c802800760840e03200400305905040101050b03c18449900016050413407802010440c20702130452640180b603007000b80c0e400f04400b00e40c07480041420a0380280860b041000400c5d1a14011421240d000f40648400f400e08908000b184015013007140720681241000040690b890020090f060042c031043c0d6002c0307030514100b45000d490207400717402d00050044c40e00040c0300c0b43d60003109641 = true := by decide +kernel

theorem cover : BRFrame.Cov 756654676 756834532 := by
  have h0 := BRFrame.cov_init 756654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 756654676 ≤ n) (h2 : n < 756834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
