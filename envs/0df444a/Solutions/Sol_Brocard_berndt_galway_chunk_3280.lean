-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:51.576355+00:00
-- url     : https://prove2.me/submissions/43ef83a8-7707-40be-be8f-27381dc4ea59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589748201 ≤ n < 589928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589749451 1250 589748201 589748209
    0x306270708060a0b0313031106010e060d2a0501020106090c090b0304030c1209061d1f05130b030615090a0306090302150109050702100c09051507020312030109050a060302 75
    0x342904040004160008105480c0c0d00a10b2020700300d80000c2c07648038904000100c1042d0f80900007100080c2c2c1d49000f070303e40d0b500d000403400c8c1038981400039040e81c0e0f030320482805003052095809882010000d9104401507610704014002c00b0080300380e0504070b0342442c0000e42522002d511000b411894440c4000344d40c0d5015425a003a64410b0044a56985485c102101e030302c08000801f420ba02c400c04140726445410030400c000300c841684030a441e130304c4001d410b08041c0000c0c003a019044031521240321800c0d04501300041c2e00300705a081072410308070440e01d00c5c94901803a40011100200010502ca80351600c9441715900e040303010102482c2c91303244404103210010a201c02010192500040f00400d0b0003031118861034420307008003a48940e51041c10001030103045c0c807030320058004e8401103150044c1a001d41c010701e100315250307c0103070740c40d0200703004182c1140ea82d0100305100500090005075414042a07803810701442c50a902c9505201c1100700303c0e00041c00c0b101c64185030074010401621 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589750701 1250 589749451 589749529
    0x10e04030305090712170d02040f09150303050a0e01020a05191401022b02040e040b06010e0f01022509020c011b020a020907051615021c2c10050c0306 66
    0x21b8071004075403101c08210600d8285001e40031007025907900124020178010b012054490407034000f0001405a0726214a06030f0503240103010103030001c2d00411180c005e0b0740c0506c9c0c01c2c0001c0881071040712000c0515489030340c148040c200c01c041c0380c401c00d20300082c00c0c4003003502c14450400040c4021031a1824400c95081508120303081c4c1d800034203c40c4150398070600b50390306650041180140705402c0b454549800b43c0e0030380c400c54025002c205c1c1c0c0c40c7d0296546c02c081a80e01a40441a00107003070700001120104840e10017118117a178000d0141401203142000d900182c040441ca60001107011041c070322a180d40d4102901c016421035202d003446c2c40159403030401c466000002e41c180a50b40d0100c481c2c1785461101e40d1100901042410700c0039041d040111350040c08840501c41c69103c408036024203010a803020209a1804004a4103007481d450707403500c0c04d42070101d280c1812104201c155228050a0f1802247c941942072004010483c0c1810006405159807001c01c0c3d441400c045900c1020810b90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589751951 1250 589750701 589750703
    0x5043506150411030105010f090e07020c0a0605090d0602030901020405030a05070807080303070903030509041b111207020d14030c07060e010806060703021f0e070f17030712050d090209010e04030305090712 90
    0x1004840080a20380200b088030060000b2840c1c02b0300e180741c9150007070354680182c03640c42e01404a0350000107560703118005441032240001d090640c0c01e181c3d40c4642c0081d41000d08501e43c5950308101c0000da40e9030420203840824850005088514a040145410f101c40e9500000d9190401c00c10046140c0c0c1c02502030066950604117591618442804100148642e8161142d801141c00c02c019050350802620003843c00d91008a445064652041d60b01030302420038001c0d0822003056080c0001482000d008000d00c0d04e17642240c3c00c20010000700c61400c000340d8004008604800180900b550b8002074a591102080d03070782d5464540185d400079581d0000c07010440c0395200c5040d41c16540344140e00b010040040c00411102e207152907a03444801c1d14614401d03d030000c48008400d0340c0204021081c0c070300040c1c2090305440040c802e0310082c1d44507813104108008131545c51007000016602c1e065124042c200420b6001480e20b0070307107009801c650f0080c0c0030050075800988200203060140700015116 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589753201 1250 589751951 589751957
    0x406151e050408101503080408030c0624010503041b0b120609060604090b0a030210030b030f0a0b06061305030102130501030f050f0c0901142d07030504350615041103010501 76
    0x101d00201754018009116003008045803000540080c002c030340000903141064019013568050345602c0040d1581041e2283d51002000322040d5407101c07503014201441e4072500910030904081950b81401c00508210380048a8860010a440e502003140f1100380713138029420f640110060505800048440c019440b81607121307038603541011810f0b19200188170081d82c1c054080085070021140203405046040c400320302a00c00c0c07410640007081d0001c3e09419090b04281d081d400c0307031114014030480e58852030304060300101084d000905520244000c01180800c503104890340b45c02d00c0c0004041d90040041290450704200602c0700803020040099080101d2403120350303940c01800300580d092a0845000460008041191422a04078105c080310380d829201c900b201240b0311480a40c22805042400750014206000030300540700201a001c01d0030044981010507844007e00c10702d81c2c95074485184520b03800403000d001c0c0082e001e50303104100520480e4148042510070b2040030042c08144034140c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589754451 1250 589753201 589753211
    0x30302062a03090102070b2d040c141c03120507032307110105130b0708040506060d080904090c03060f06050f131d03030108070f050d060b0406151e05040810 69
    0x180d12400d504079465070b07031301001e01c844c68a45041001c071102e0241e501c040b2000d000e0341e45442c0fa03100a241c48c0307100d10f51004028114a08281088051440151a032a000500b516002d90074841c10340641d00114482c1c3d41d00c01c0c0040c0305201c0001038500c00342c900c005141c1002c0700280346240303c1c1c07011041003a0703c100c040d12507074030000111f620020420060304117520f400140701000130181c02d03058545000d1094030302c03036841d505000c48151004540140c031903049000070602c6450044404c110f154000d61009041108100004084854661003290106001901041004a00d0042e80040c1040d6082001854900030220b400c02c89050442481a81d102c002d920441c5c000f580811096480500340044c0b100c40c030980c903940c941c42800349070205e2050711030000c0c0e028112010207007515005094008000c2c100c1d07076050701424500050a90254407100e02044500b880d41e0000720a90a0b070791402100d0102c03903004c08c504007000300d42c3c8003088001c000601c805000000d018000210050300014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589755701 1250 589754451 589754461
    0xb030103150b0a0f0806180d02030703080903040e1501031113061b1e1109061f140a0306031415010b0c070b0d0b030d02012a090b070507030302062a03 66
    0x141c0b03882903080301e81e1000c4d44220125a2840000701d80348100801b54140c2c07403100014183c0d660758090083ca01c401603004200f1640068850900ca64012400070100c1e41010740b681240301000c6070840b0001d850140d2462800400d603418016107240c003003041205460301801828411080c211802544180940c011041c2500d2200000760040180c02c5030b040b0b0210034080d09044140104104181e0f42c4013013000c0100c00e545440c1c03900038000d4100030110700030342d40000c0040d02c1041080c1003441c2400b081c2103203400004000c8004158540c0c45980006455082d40b0703159504001185210059a010a1003401c00540f120480d41c19990800c18041d01c0740e440380c0b00546002c42c40d4005080c9048003088034112200760b1b41100e402d400e400c4041e100f40e4805030208030300f01d030510b0010b610380c0001c0300860100f5001c4200828201d09280c07038420200c41e103501c00c150381030b0700c14a000c0364550310032030040061560500c07409400c07480782c0350700e040c001810f4403010009101440c2429200c0100001040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589756951 1250 589755701 589755709
    0x50a090b0f040f020c120903030d0915050403030c020708070e01062114070306090b0328140a020103060f06090510050702091905060103060302090a02071e080a03060b030103150b 78
    0x1c80203040040041c07008003e40b40c0d20201a421045803d03000c0c0c498400f814a00c00c0c120320550b41c000101070015030508c0e101c3c40b5541c018082c10002902e5072125400c207100802e655024140c8641d0180e107021880e1000210003c2c90960258000b00c01904a510240160f0410404150465906240885078480d10007480c0048100b008001e031416441c1c8800c20081040030007902d84594465101000045c0e40e492076401030f20f103440416507040d04262100009003220310307c3c80041c460f5050301c2e11b0040d25107580d002c4c900c40480d614102c195000e400c044003150303414000c840150401c140c0e01c03031740f00386400c0340a0714a1040340611841406c80508c100c0708180f05070103031042d8030f40041c01703034880307003080e1a0114413100c951850301ca03450b045c20001b581c3d80d4000e000e0001101d5014040c1c80b040d980e100754040c0250003400048841d820103c102d4000c000401c010034020700d001d659803036680c915611002e401c0700c03442d512151240c441840100049500c48210300c030b501c2030040010581158000000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589758201 1250 589756951 589756969
    0x3021e0d0605070e2e20032709010b070201031e0905100c0905210f15062224080f0708150103080a09180c08060a050a090b 54
    0x4180c11451161409003402000e80001d801040c89440c2c4d400d4000e96903080c0549240400f0b00304034100c507004044404000c04186141903000075186c09004141480c807480c280d1800c80c000300c40d03550300202d40d20a0b0030a43d5412101c43c01000043ea034005040740340400c40d0043d052290781c0c05248085001425a40650800b01d1a4080d21580c4070388403003000c000c41b005200c00001035a080c810034100c207580709120b20660075866110384a1414042c541410464142d0404035090703410a11007001c40250f180402803106d0804201002c4e1600100c1d280a0490101004240c00d2050003107040500d0740800780160700d01131641188000c0b4198641e01f403001034450500f4090402903c2c07902000800300d1010400340003011002081d42c041c03a5413a01d285987d00c44169048000a5103200100300046000d8004c08402c0900d0030b017202c03090340d03030035000703042d85150302d0100b40703ca865a03c5510341c1035001d5121948203000712034030031800d818040840d4056405026206020b41d8900e11810f15075140840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589759451 1250 589758201 589758259
    0xf0807060204090c0f03050103050c12010f020a02030714150f220309050103060f0f0909020a0803042c19020307090b040909170a0e010503220b2e0302 66
    0x9560b92940c1d0b0202d000145000c0221000045288220032840c41c841c1c010b00e4102c0750800b00810b4a604548200858016024800c0c0010b6507102d8480c80f420300b860000d0000c0d0306168014503100c06241c2000e10f10042d100c061448580c0000c01701c0c980e0b890071b4038025a00002c000300b06410750766580c95848010000c00107105c0d10000f0321082c600c04c156000e17181d502070702e1080e0f90038484d03566903588007602c01c1e00710302a1411980025074140607120340c8d036024040c0140010a0031040990344c0c2c1d00c3c43d04581c40380d0040351019002c0b10411b40c41c00c01d40700d0139180f8103200c07988140951818038103503e51060044101e18440d03400001007000070784140c00007030140ca051159240c0d525541d20b0020001c0400c0b4404071031001080e109400800ea48000790740340b181d0142c483e540040e030600011034203680024031031244d0302031040b4a12080b190000342240d07218428500d00c0300d1802d042280700080314281c204403001806020040c00a47e010440e24002ca0740c0c180c443c030701c00442c00309003690030b074a003041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589760701 1250 589759451 589759463
    0x8121b0303100303120c0c0f021503010b07110f0d0b0a02091519090e0705070606090e010e0f030a05090402070c03050604051c0806012c1002160509040f0f0807 70
    0x900c00c0404202d0111000c9034425142e42009a10f81e04140d029210003e030b031070010410140d4500d0206001c04071050000b40300401c908e1040b613181084208031f0300280c00c603100c0306a01041110400c558a204070600340801c9903184500f0b01d5402c0000c200140000e4010305a1000720041848000d990301610b03038a440c002c11502d100010b54014403455000001d94401c1041546150b245031400b52010340f050312a01400d0403170382e03550040b080d03845520180040b6a115620080050340d40c000b44921021115140d0000c62015001911a440c0c110800d001e000103030010000440019003160466501c4082910003580b0b8041d03038104060529801d60010300b460140400b04410040c02143c1510444070412040c04002e4032100e04507411072084800e2804110304c000003c50312501060414031901000e0030503010b00e080803000c1080c2d52001020080582d1006000300b912a402a041401030700050316070b04003c1c1303080e0700c43e0b0340c01001c014805024285818110014803200e10219124a50400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589761951 1250 589760701 589760707
    0x3030f09100e09070309110603071707090f0303080601020d020d0e1219080c1902060304031119140d111e10090b0703050601020303070905091e0a05010510050408121b03 74
    0x144e00a030180018046c21a950a20b0542c6209246010016680540c1c000d40d54010b041008218001c1848c04c00350a02e000d0003944940042c962000d100103001641c40f80d61100c1d2203003008800a4540300610010100303542004080d08061540401c80c105901c0c01140d07445101c1f0302107041c3c5c5081008040c2c1c05c40003243c2441107101071100e108010310980000344221050245001950340a5480120b03000354070800400209010a20401030440c8021042c000e44075504180d007514110b05468400841d000c1e5002d960403410318070203019607000600c1506150222000025440f91170321010920160390385003600c2000c400100c200040115010000c00400001156052501a002c421218000068103104c000740a0354804001d0b80d0040626031218607a43e030038403081058241d4000e040040a400000822600d0502d00c40b289028882c24680000c2c15410b060138850680980815070041c444200010001c4800000d20380c0903441c5a4052685c60b150003440381c007048411007804050500c004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589763201 1250 589761951 589761961
    0x30e1314010b1e070305070201080c09030f0c0f0a03080403060f1b020304081b09181207080316110a151107031d010813151104080604050c03030f09100e09 68
    0x9600924544000a610b0300780407480e451500c581e41300d0841c00400040c424845500103501480d6200c0d0442c1c2003c200d54208400c0310086854030503808545402e56000001803500c40c24101d0150f580c0102c103990040c1103a045455092192182c0d203c02408c050b40c400c42c8850403881d0f54020f00800c1c070b40d4441c050f00000100070095881e0000d00401d20240a11440c400c0301d10040500e907102d031300e0064030140780c50b924001c08201c1e40d543c0d01c600c1e114a0090701110300144203a0380c01412001d00ca05801c41e22800c2030b01403200040a2400c440c4107001e80d100d1541070302000083c000340300540c059003171240103d00910740030103880c444591081940b0040b8207541056005481d0800064941c20b000107885040001181c81c2c1205850460039001c01c0585a0003140305c40800401d00c00e00380034045142c600d11104840e1650140d8000001904a08240305c10003038184245002c002e0120000c60070f0a4507244280b01c05e2046001c590b1148280c40440e9407401e024096655900780001c00c842458940 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589764451 1250 589763201 589763219
    0xb0706180c0602010c020114071209050d0c050601080c01020c0904051f0905060601092402011409030310090203150d020f09150102071d06151c0204140d030e131401 72
    0x4140202c1c4055405c0480201415205200307003d50200d001400403420b0f114580c00765210321010620300380b100c0c1c039003501c540803900c1000032800b442e819542d4441d0140c240d080140c1007a0041e0480005a041118100350b00ea03030000b948032000c00200c640c40c04c180c44500c0c0852030300c04d2484034080c01444c085c03078030101c1d074246502c60b451003406030040d100346139110001143e91481e0344c00b0381038501d8a05407004001e810354805145040f800360000003000741d100540409000001c440015090380004200000540341000c01801810130764015801d42c24441390b114000e0b00f1624103d8020700803018914255920310740b80382c406060180c50304030141843c054102c00d03110784010343d82c003510a201c000110100503035421f140768500048407030095202c000401000424001260404650500c41d80c1711b05203128000c0ea4024140c1c0c1c034010f0340c0c0c40c42c001003d010098441010391050280c00a84e41c086500954501c5c003841d01201e2104c618442d86c03031844010160881c40e070200c56040000480d40c0d41c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589765701 1250 589764451 589764473
    0x3090d03020f070c2403050f0115030b031f2706150b0703020a03030c090315020309030c0d02030a02060a0212040f02030f0a0605060307090501031e110d050102030708150303040b070618 81
    0x170102d40d10a0f82c0c4661400d070280c03801525080c00364107001c0c004004c080c41c1400904844d074681e1130089681142000002c1c50200c4020805005000c1000c207405040071610400001480110510480c00c94480b6101c15107440c02402901258507512404245900305135a1800703032151180d21601c440c11410f000359503490b80e500450120340740502e0201c45601407650705044035401000e0300b940c80382c1ea040d244040d41000d401e400007440207200d214114002400741100c0100d440c3d0007142c485d80074807802442e0060243c202d61100d44104440600401462001c59000303401c1004003071481050f20100e41b504400c501100c040f402401150002c2000e180c210501178003085003100c00079911002c01d24112a020f110080c8092901140c8407120880802101d0a69000710041e0300229449008103691501008040b18641d50000070040300a4100700ca4075000400b400a200449140001103541c074490790081da5900c0c14082699002c11055400c8801007145056000740908054644030103c18 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589766951 1250 589765701 589765739
    0xe010b0316140711030c0603060f010c0501060807150201060906050f0402030441010509030301050d0807020a0612150609230d0302011b020102030420061207020706030c0503090d03020f070c 83
    0x2000704803101050341f0b8601c094038003403c0d0080065510622840040d5a941c42201c0215115500c4260010301e01d0424003001c002020071648001c0d200031a02d00080c2160a1038012070722503490000188501d850741040d03c045804103a030010f13501e03180c034200708d040d448518100718920400d000c041c0c0d1112500300543c2d101d860320803000101c500481c440507401da4400b00c82400443d40103000411007840c0420303000c6800740c001d041c03041c58401c164004c0b4003070034815040b23607011440d4500102c194072410b1149494903100704115040d158200313507004007a209140714500241616614003140b0740100d9060195010000740b085800c8107907890041d0180030740648a242546c11100240b02483c018000c59110f51381c80110314114201032002e4007040d4000102041d044402800406514010070030524003500e01c40c1c006068461034090010b060702c0d03804070321200b004030500500080c80d60008030011062054100540c9800202c001c0c0e803240d01400c0d0000c0c1c024240c1c44000038403d21506199501c078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589768201 1250 589766951 589766953
    0x105180904030f0216030f02062a030304030801051f05090102010608010e0c09011d0105010507152910090b07110604030305090901090b09040b0402010216060e0a0e010b031614071103 80
    0x2c4910002c29540305807a4030001c1d000c50640807c900061070031800601039105440c5804007403154407451150703554100700814202d5400002440181508218028010582120345158444041c007030000340c4400001c2c16024481301150107001a8003c0d044400a4000c034002004a141000c100c41d603180410b50205004500050002c220401069520752200c4500d40c0e5414059280030011942648000029a07451401c01c2d800f003030140041c0221513103c042e040c0c084803c00c15140b43c0564850040030024454203645003e2614680c1246514084608444c405500d500613800d0103071626601e08050365003d400010084101500030003d0019041c0c246d80c506016a01d404104007107503000f40c0708070340c001c00c1580058000368402c11016401803041c81503501a00d162054403040900b0f030740106001c00c0c2001000700f02c1d0308040b00c1040044c0002ca00440d96549801002c2490344805000c12444c900700b9003065038014052800da815999003044026a10ba01c14140300305805088290ba40c46 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589769451 1250 589768201 589768213
    0x30706060509090706051614061006081003020405100f03200f0a0b09040605030706030c030b0d12050307140a0f030e1f0207020f040c020c090f0f060105180904030f02 73
    0x1142c01c2001d4068400e040700ca000381100c40c205002903030785400144041011017088800e200004a00d401c003030312400002801092681000e43c86e02076100120f40040302004244800c01c1003078440f44aa1401700c90301540e00080b9a25160a90800503060303030400040120180070000400c48090350018291a02e501c40d0301c0180e42e008104124a244503407500ea1010007441d0505c03141904400038440c200000300000b40e030030b0392100840c2c11f0401c15809a0003096030f030011003480d1a014004c820800c501101e4003140725946640305032259254030544410041c000c0000340010307000b01080159180940e04051701d038410140d00900248624829000007410900c10020006001911003030720058015030041d50490304443e00700079040070740f0580c0d10007684190801583c560388502d0f20002850b60107080d05619200c140002000040d041c203440200c00d00800c181186d25805d0503810070030900e0501c0e0b94240c0c1c08040100d8102d1018101c0c1d00041c410140000c25401c450004080e409903029124 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589770701 1250 589769451 589769459
    0x1609080a030206041104230a0c091a030c070606121703041502030a06051914122107060c09030c150e15040e070e030705040509030d09020102010b1203070606 69
    0x510349014200040c00340c3d12100110740010701c826918615020081c10000c0e481c124000c0d0401e0702103601e02107420813164082032188907200c0c4d0003802c14001d464200000054030340850603004115000100c2000600800460961002e59044a08203604201d00f8003100b91102103184070030390284811603c540810031150070f802e103c030042c0c91085811260300301d038091390032105030003031350006140820940c0d403a0300105059441c032413002c15400303242e600c1480403414800c103040700340c172003105580c401d0801c01c1e5800d102e030800181c00158444480700d03951031200f02d000c020089024944006003102d0800a004a0302580f12140004980c00b514400143c0c598903400f40e261140d40c1e901140c00154051060b151500700b85039402210400e006645240541e144601d50807008191080c1c000200c010055541501d410400e4501400d4111010000da04110300d00e940d076032043c840d400802e46c1e2507110030b10540e03000307510400c0943c001a00702c401c0003080c128030b0743c1ca96009502c1200c2c2585003010200b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589771951 1250 589770701 589770703
    0xb060405071e0e030c04060e1504090c120c0306020c03180a0f05011b080c030a0e0103050c0703030e160b09091806040f081303030f1101200a020c0306160908 69
    0x403200c51010b0b2420010703100741980032030b204214680d00e543c0621800c0c404107800d48484c89100001c20a040307510f4540c0c180f9201113008151a005d445101d01d051040c0080480d003008040d00c00c5510100080d03c44070700c9483d100301100300c654006400e640c400700d0704680d80d85000c0002c081c1c44c40c0e100c100305214600d10041086617625030050800b002d040301402d0155500512411001844008c032078071700b90318543d581000c0c41d80004c089141d25080802d180d0b01d980d401c00040807807614242001d01c51440c181c2a0350312180603881000c0e0415858038805001d00c0c40070701c000c0c80ba03841d108200c00c41305511100380400c5607001d4500a0300480118000540c80120003d1401e100100403014202036199601d500400e0380003c202501c1da814200649104030403503a0032400194441c1d21359509844003440064000340700001001c00316418014001c5210000301034100031031070f60101c0e180c0c0381d60180c0405c074503040c65801403e400d44501c1050188100d81e400d08038000c01d036079641c0c544c0440c0c3c58000c2d203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589773201 1250 589771951 589771967
    0xe030a08010510080f01120203010207080a21051b090414011e050301151205071e0f0b180103020d0f060f090605031f0b0d020306070c0c080c01050f090d0f0b06040507 73
    0xc1c03041e51900040c40003030705045460001f240020005810306211351611545a805800e9420110324044081110812110201c1c7e47e1440c08003800c01c210310749140c264420400c0000e4103220340300d000030360303102946d01c079801481c520303038280c44008a640e1107041c40480702070354119030301400c0d03014400060f0034039050007603115048010b80814161458001c5001c041030382c98004954500540f01c000c114181c8242d40002c1d21303a604040d002c0c61901e09441c10140945940000d04500c1080191003001c210300829401564820310f0300503980c00803040d000c8010001d81c0e600610141c00c01b2000240304464450010030740301500010480c01d6030381c1e4109030792001210454800e4110b480c04818040c15203138400b005030b01d40508800d00002d61030340040c2c140303002181d0187c045000e4000c20018000d0f515107500150808100800701001d01400190143c06240c00e80000c2c0c510000b0504190740307442d406021070350740c4503d0900d40e4844030300c1c2000c419041154078500651800002404051042241c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589774451 1250 589773201 589773211
    0x60106110d0504052e030207020f011d3a0203010e03210c04030204050103120e0f011407080c030310090c0e0904080c070302061c140402180a0e030a0801051008 70
    0xa52440d1910304014094a601242c0419141720329030102c10301954041c04114504176200e9500603a01e200c58070400107000c02c40840581000002e42504035051003c120204420300200d070400100c40070a6600030780c492801780c0f11424030b00c140c030a29903504190500490500d100324001c2c07103c0c40308004400d56900440d800c5035603415038040032113044070580125a40082503c184c00d032400e92260081020b0319800c0c0d10856803015405211070300342d03500030b018420502080724a48601c00700304000034201011080894180500029442c08001410046440d40c1e48441c1c1a680c492601c0801481c1d644003520039085841d081100741001e8601c030300c014011800d402044085552200e48407101d96801058100480d40f2807940080096560140a400e1184401112903018400d842d0801c1c1503400c045105a050b4000c8001d00c40142c2e1126117400d400760440340304280310358130034203104050107503188074044a02000807030742e6082d5408085036042e42c500351040d5400070f201d240c08560710001281c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589775701 1250 589774451 589774457
    0x31c020c0325052209120e090103050705120304080714030d020c0112090f0215220503030f0a140c1b030c0a210204050c0306100f0e0d0c17060106110d 66
    0xb84158980704030303135118014485a041e0311030103803d9042c400311131090360250307031031640503165a03025036000c00c4882c05a41c00f0380c0c10f4031541d4035580d1140d03501d5440d405000d00c00c011003501084284410003c0d00c000b800d5a5040b510a55030f80c01048050001041d0601c1c080d0041100f08007030031340001a0240742542c1039413025446002d16802800905490201712801c000c0d440c154000350341d800b02c1120309141c4400e80345603100b4800c00071142016400317003984552a00b50504000c9554048243c8e0400000760100c1551000c40030021201c040b443d090b21940a180412555510407000610b00348540700a900702000301910002c240d650301c0c49002503940003203241404c0c0940505441d07000c044100c5220f507110540010782c0020150b910454a03006c0c040b6011007002014a0034041110001a1f05d0404800919010200418201c0202152400303410a525100104500c040014004000800604881c0188080100d46890082c418900064a0700c1c00c040490354005c21180c852141c262 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589776951 1250 589775701 589775773
    0x111005160804031d04060803031f1409011712070812011a071b05032a0105071a19020304030315060504060f0e0307050a081606171302031c020c03 64
    0x4420f481c0d00003185813a06070030a8482200103030702d0700b042024502646241c441070043e2100b228601c0c4502e040381c0c2c0b0440d200d04c3d02824110030360f00d13800c444034152a142e008009641100a140626240b402004005880d000043c1681404050300140403480e2440071009140c2e6624a42a02a002c2c1e541d00644069020860b650015004021400c500c1e1016810007101c10703030f14000641007400c2e0038000c40000c0b80c07034012030000d00301070030b46500d55140c01d0800b241404000e4031b50460303d4046a010364408030085012681e0344040c070b0407103900619844419983ca140c039250040282c012444086082100f0140224079640103500395015501999504940294000320840751501c0d6040d00c1ca426014417140030859443c1d840d08000946031070002860480400494068080d245504c48420045002c041d003540500001c101c540205d001c0303807004240c0c005400000c1c24022208100c110b50b02070074069a50842d004100500ba96008406940c00648042241652145980e403c403d41400007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589778201 1250 589776951 589776977
    0x60607150b01090801151a03072c0a17011a06090402160b0f180304080d0f030b090f01080c04050402130c091a030f0a0c1d0111100516080403 62
    0x1030740c0a5a9000e0051404011150b9105030450031500c0d506890800ba0803001014003200031010004410b5801d61b200c0e5528502c4c00e81c50040c500007000305288900f149402004e40c040000b184e004214843c0109082d20680c0c1e030b82c641c2d80c0c41c5010401c0317682195007440c44d010b480350f003d502e0346807840c0e20150040d0714001285003080001e50051a2490403091903041031404108c06041003480b03242c015034140464288042018241c1c401d1011301c0d04141e00401007804a140082084854050f403802e12401803081088280e02500124084641008480040100c5a04c1d22407103c1e04841c04182910304441c903080c14082036030021100603400c6400100c400c1c20007046540a081000064500301682a89a0890640301083e16220320804034021047c010b50303280394070340e03180c0156184a0400c0903507040f0030082d00c14007030110350901c5004c20002d018010303405808125070582080e403c0d00c4580307204440d884010541601c0c0030f10000e04080017400c00d43d01465425000e80c1e00768503503880c54065 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589779451 1250 589778201 589778243
    0x50a120b0a110706050c09030601080d0c0303050a0b0303070f0212121204030509130506030105101203030f060b040806040c090e1e0114090618160611010e0f06040b060607 75
    0x1c0c1c00035019400d004000f0000030a4462003114058494200502c3c3c0c3c84080004240c0b5002e01030f00b0101c050340003030003000c802a412081c0d0b6040c142d45410701203055039403c0440002030465188031601400009180410010103801e5900720038421616002c10740d43e00300c865035407140c0c1490140b8070000c0401108440e001090641540680b0a1800d145019111700204040380745139225007004d6511101030104928081c022558808860358a00c2c0e40146020140e90305c0d02030341e80c40a000e16998071700790a002c2e0410f0700102d003d000e801101a070342d10341d00e95010b40d40f0a81142c084d03500c1640c500c1c000c85c80520307500501540c0c802540040034440343c01100285038207004440180a5943c0340a036010b200201d58203584214024000b034102d0f4070700114850304488070302203090219001540b00000900c2d01a480600752041072615950411410750594010400c0340654a580d201c1c10031a1844001c0008940b4826440b840c0c0301c1849440f81c00601615010b103410052050b1104841c0c00340e2664 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589780701 1250 589779451 589779461
    0xc27060406030e0705181008030703051611090718141027030c030302010c02010509030a030905030c0601081e030a020304090c0309062a020304050a050906011e0801050a120b0a 77
    0xd007810f9490703180da00c1780012460006103034490001600c20081024203060458940004c0010b100036610380102c9685c0100144510520407008500410109062022440d14040b940c4005014800242022072000d0200c0c0c1c9400b04444c40d01103c8000462488082d21907100a4240034003094a0000d11400c1a01c00ca0240c0b00c0c81141d59006402a8950100ca01c0e200c000450084409040060450400a013500c2c989031480e010f6a05150502c41061030003c100d484801c8039250000308000c81c0d1800b90305600c00c00f608892035100f40000400c030340c2c101150000608540006040032800102081034a13030140341000e00250700103210421416000b40c00001ca1042545400680810955a160103c4100013484040841c1031004002341985040700c1614204c81c0d07000545c205841d02c2e001500644107400f604d4003525841e80882c01d2039000d00c500c4100303102000c035049580c1240c003000804980d02403140903c500c052a40001d190241c0f50800d011540e008824400d030755480c103a403040a48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589781951 1250 589780701 589780721
    0x15010318170c01050a0603061a09060609060c011a0102011515210e010902130e0303040213090b07021605041e0e0f0a0515090f062d0c2706040603 64
    0x40030807240c582e402c070070b10032284a070030340c0280069079a040d82801e2040350101200c0701504004008a4130342665008007450348400125010307540d680110300400c4c070034052000c4400803982040d500c144544e10b0750b4004400c440080e4000c028940340c0c0322041d03081d01c034203101d9880c410310800d0318040000e1081a03094094101d40503040000300b8151140021584900440e03952a50f460302c403a821881c08440c05010303000561014000703540007a00c0107480e884054070003442480a0400b5000b011a207411407406150491034260b107506d04900003a441d128900003d00c0d05441800c00410300b4602445141e0381011200600c00f2114011001c010081c000044160549e200718003928019203410481d0900c640c0c0308801418110082400b1603a80020160560b41544c000584660226100148803603002c0020b0381c420003002003d080c4040581542c427400213501e00383d10208070845400000030000c074001803041090148000005030030740c000045c03160350300c040100410800341c0d2217904004210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589783201 1250 589781951 589781993
    0xc060f1603230103061506050405010e06030916150201061a0403110a08030d02120610020a030507151107211b21080108070b090f0120010507020615010318 68
    0xc5100c5101c4988442090348119a0251541d807a035841c0890000c03024007c2c841030829a04082c00c000000e4803030070403204054018580800060008802040301780520100c2e07170600f10a0a403540349088088051400002c090760a002c03001408030285605082130700039401c0c5060070641144d494848183e884d0100c03a034480440030703000c26981e0040c40140441003201000681d1003040050715416800c0c0104028810071408104116564000c6044e041043e07061410aa8400ca2450185010b035810074940c0d402900e01034206507841139000051460030301400310722803c5c402502e803a4103030b10b00304400c0400141140310180300300d2002d03a810400503403041c1e006007108030640744041d003060641c50381d60001800c1c6400400104506200b0840034180031100d4a161040c0c04c40416018021024194100f15504c10401c1c0a5010300501d8028001180028400da003000301000b59586c8090b107010350100c42000c0241d580e03601900c90810111180528010000700640301e40c0039469860480900b2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589784451 1250 589783201 589783241
    0x170702130e010c0e030a0b010b0a0918050a1103040f060518030c07140d1703040336091806050705040509040b091002120a2f0c060f1603 60
    0x440319150144060308501c0c04000940006a2900180b203d0381808005000f50400540c4c100030440c00e40d440c5040d548054005542c0c1c00c02d0741000c46005403070354000c80b50301402569110b5107404941106003c2c0350140030904c20802020596080b034841680e0051148415030a00000907145804c040e92005900d00041c0d000c281ca1159103041da40801c500545e6138104080174400350040c0c0c080e0801c08001941d00c004c409050340c0e070349605101d040c0102070030240d02100140815102c0e2121800b00c1182d0303080f221302800403540030f8508250b20f1302000009010100045805007482c4991801400a901100c2032807000b902c44400800018202c50304003c400c12012407203480301d401e00c6001e00d10a1505a6162510445040c02c00f40407000c030700800b500402c504c1c064001807084032038101880344000500869281010a8810f03040409103400601c11204800c9040c40040640318031080c0c07506541e8550b481032520f20302400c0450394100d01030303550341c82251a1440b03503002040b02c01c0c02e113242c15a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589785701 1250 589784451 589784479
    0x702010e0118030c170606181306021b0c04020903030d020d110403080c0d02010603030e120717031b0127060209090a05070e01030e071707050a060906110a170702 71
    0xc07801807540081d91407150509040010b0300701401c0b17400704045404007501080c141003000510064490604900708011603010a465146500d81102040c0e0f12003001c560b25400c8078100b980f039003001c0070384072140c0c000c3c450203800908050007202c3c044680100a98940080140c00500940041e101030b91841c0d40e5030002c0c80c0300705801c0c000b0000307903014005207070b191403d5526803480c115040c501c101c210b90510008200107a0840f000c10405101210700c9a5800a14185030380317020710369440406040c0c07400b400350b07400701004402003c00144003407a0b0740c081147c980f040c500340c59030b01c5441c001078003030f400c200c40d116a61650500d550318428000985011280c40001d42141e500380d0301070f850240d5070010f03c00060340200000401b03500c282018030103540d02d032220032340380c1d0102c0c07080729024030280440d400e81344000d00400c00035007001440d0411454852030010600003441c00703040d02040b082040101500f1002901c1104143d0060141c001d1601490580e5890b4104c0d8004980044043d007a0038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589786951 1250 589785701 589785737
    0x40b0d0b06161209030503090105030403050d14063f0a14010606090801050f161115010815010b0a05090d12030506030d0c021e0d1e12140702010e01 65
    0x7003808400e00908040c81d80328104050000701c0086100c3c28070840a40400008001100b42c410300c4d0400d0030016160f90781c1d8281983c09100e0300b40082042c80c40c0c800786201c103044410109020720802d50782d40fa10700440c03400c10f0450407008007280800003031060140d65492404500d010144003008280d0308003400c25503d024090784076114800c0d080e5142c0350700340300c0c50b03500014140083c004000240424204001c0d10480c1003c05020310002d401403075280003901b405040c1801299281030202c3e2000d2001d46604048601c1c28020980316001d41200b450280803403488183c1a00c0741491130515000c0d144c04182c4060740221400c60300140c200281d030000c108500300c0d9503e0f030816078a001c01c0701d151800403d400c00c503107403402c941805201207400c000b5803030b2042080400042080001031100c1c41000151080c0c052540c024181e940d85050120110124941c90f602c1d21300c18044041100300422041c0c4100f858811000346000f41030002c0300240d88181210b1a60310010704007060300050000384d03c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589788201 1250 589786951 589786957
    0x121302120606030115060c0204050c2214060403020a06320714030307050412112d010207030f02011d030609010228081305010b2d030d05040b0d0b06 65
    0xc019508503004128007800d003806a46114031050344144a0b03503044c44009010450f402001034006d0740c0d2140007810000d5018115000c04101880c103c3c1409000403223200d40b00428029080c29940705401c0c03200504000c0151021b0343d500801c45543c060606c00300700c808001c15285000c5201c0710084a8640600d401049407110080b81402c945d02c1100d0f0800348641180c803d584441984100200a0300365400800c2d1425151000211a00400903003090300080801c041401d511000e21501500c0503507180008081c14860407900569001041d070040e0b0701c8041910000d81121000800b260043d88680c030742c00c403070a41e0011003480d820300000100e0300c0c0c143c045861040580d40000e01101144041c0d0141c5203140260361765000300510150010301264000c0c1c002903001015602403002c01c182074016480604020b0007441c101e544030403200c00d030702d500390b9041c4910307808120090036a82004254008482c4140c1c55203407400d490580d03080304550100e04d031034002c555600600c2903660303204001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589789451 1250 589788201 589788229
    0xb0f031e1005040c360e070308040b0a080a0501030305070b0408070c0f090f021c020a0512040b0a060801090f110d050a081312030903060b040f09060509071208121302 73
    0x11808902d800c080ba141802c51004c8030071801008071119855400e0117010403070111200368240880e030759044400c92451b04850741c20043c440c980109001c248003990383e018002070911541c0c0c3d9001038403400d40c01400c80f9002e000290010320204402e00c08655a1941c298100380b04000b464581031039516000203c00058020598030030448808120348490b0b40034074a44c0c1d0110103030852501d2540b1040d2a048145050824007203a0045103651406020b10107440d80141c0303c200150261070b19241400d0b00200c1294100000c3d403404d500817454400500c10080d42d241d014400b01c01c1040d03252100b00f4808020708203039a02100c2203030741c02c001031340c1030041190b01440b844c9002c0d11a0811404402d03818901d0304128211402c031032021001c694041d090354202ca030080c4000900f54400d4012901428140920104460802e42c034181000403039407003184100e1035401a07507241074a44034114640c00c42440e0213040908240000b24844a0b0080500d4000c10651060082d03840d455002c180380c0600425 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589790701 1250 589789451 589789463
    0xf0b03100b0c06070f030c1b02010203072003070909031b1104060305100506030c030a0b070e04090302210f0f03061f09030b0708010f1707081009060b0f031e100504 72
    0x14011381a82082c16009001080d05061101c1400300e03100409900e89080902c00989a1030801c2003564000d00403101956000507640a20000c1e074020789800d10641d000890092040c1e00002a400074148140120035905540e0840c0c0c00b000040380c00341015200744265090321515140807074540e154440c20005600c02c2c17001e0301c40c5a403440c456004032840180036030301a07049406a1040c40c3d030301003440d20744142d00a0125002d83c844080c00c44040c4900ca40050b0854a00084801030540000d114a0b00417601900c0c45c117030400f0903500e0300040c05205281c5100e00c02c18842c40300902d40a001031a80190301a2840b8078104a040c00ea0301103650600150000c103415110500600201c064856881200d0381042c0d4040c0d4545107500d003602980c1d1195500c80c1a100d13004800048007808090010b00e882c804894981058a440c0030040c60800022110745141c44241104c03400c00103c2c0706800785004029100c0d4013607812091450b41e80141c0504694045d940c280c14800e0010b201da540106d001e07407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589791951 1250 589790701 589790713
    0x140108010c0e040b030d180e0c120a0b010503060f061608090a09020903100905010b030f0f0c120a02010f02030f07050703110301140115020304051e0114040f0b03100b0c 74
    0x2041c0588640001840c85000d07a080015000c40340e02c000a01c29416503942c03078146008005a203021342d1040040d0001c5110601c80c00c24048207100304806401110724410703000c0e070355031100b1009a04984829903a03a0110707805100007112460300051514807184041d0a030b40c604600854006040030350b14000716501440812014294200120b101000d043d040c9403c502c0c0803c1400080d0352245030005510724aa11a030190040110a421684c003e58001d030458400084840d000d5440e180e1002d0038554920407107560b00482c1c64840100020303400d403400030300104a0590011030b220050003802c00158402040001440a0f1794001041e040f4002c0e40640700e0a41140b5150f2a0140704400d0244241e0501e50505250b03e00401110304540310302140d029115400c101c10b0307003140242d51015501c011180840b2042d5083c078919060829000d903a4140e106500792070511445c096806010601168442e091000201040085400001b06002c50b1201036a40041c90203d030301460044130f182c1c21203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589793201 1250 589791951 589791971
    0x50307050403060e071a0c030301030605061309140f010b09010e07020129130507050313170f04030215030c0403030f05161103120c030702010c06110406020a0c1e0902030a14010801 79
    0x55680c40406c4400c2039185244c140341c0d00e2903690720b01041c0030207003545550f00013203403003a62042000d003250b0300d9003007042c06032aa05041805249074101d502502c64000e20400c4000c00b0418480e088000c00018801d600350b0f42455903003c12003d0007031142d01590350361003204528594171040b00400c211345408203180c8600b4078090015034190018099507103401c05041c04909a044401d5a900c88100c4400708a81080381c14155400412510080350441c1c2c000b80e00907140c1c401c0c10051007903034020f030b5011002140b411690300040c80216240c3d101c0c588140001d100280c8a001101e111610341e1038003a040000460b40311200003981d440850b801070600074007114604042c040324016001140d400ba061080d201d008644910410000904218030710a80c1010090350b81d00803441406c00d100300301e44132525250013956034950b02c40c081c1e4202039a1503001480c0309003a0203091101d01c103c0c992010030351900910001a402c058440801551503018502c050808034810318003c0420000100300c905079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589794451 1250 589793201 589793219
    0x1002070606030c0f080f03040b03131a070c0203190807030503090106030203063111010f2129010f0f05120709050112020f0a05070f0f08070605060612010303050307050403060e07 78
    0x1d1906c042801e4105020130070119410f00c007901d40c8042c0c08840d0f5118002c2d9485c01000711801501c1d010881070302c04084c81143d07607100d40c42004041c400da0850b20002103000881281000c00c0e000204625010003900703000900ca44082d41d088624600042520750722075002030305280d03040320300141005030405a4041410211005150801d881200d4482000192100001404400b0000341440502d200c00e00905102d03003180c10356058007084000800c60301c002c4840181210030240311004c050f0741c000000542c00b10b01180383d40d0805171100381c04200241010b40380080c41c01c5600b414080d041c0a181000e030040d622081c810a80369940c043c1c00c90811001500d40c0000c0f803480300f840c91041c0a40c211042d0740c0000c481030040241402a101d1090b80f9190000c0e410302e0400406040700340e44078908200b52003000d055080e108107028080c0317540d400180b1020b400344101c25030501e03800d81700400219000314020740d003000311841c101d071800d6100d49a403420380d00190000503499114901c108000d0310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589795701 1250 589794451 589794463
    0x280804020901050d020d081e16141f050a0209030109030e01020f1203150607080c070504050f0402031911060c1f05010308030a1107150506090f091002070606030c0f08 73
    0x781c1140c2d241e070549440c1d00806c034403901c0800010b260000010300312a980002111a2002040c0c0d403200039580d9003a401c0107603400d004413404440782c1d215031408094058000c205042a05148034041d904a10700a4000028140240c01d03215141d40c204a40b40c0991020f00603010103d01940313072200c207103e40c400028904446080c4659868218400d500c4c1c559000340100c0f40c015150105082070511030340d0010f4403610803036000520419002901c201e00504c0810710342d0466504450400c5250355250114140c0d0808440003076064020a280d85400680ea07030a500c03449024400c0600701800030000308256a014101202450303021141154070f0b035100f0102140c003000c0804052020354510b41d60144e90b4000a02046000e507200c1000c801182c901c90140d4200d6608064008024440031508100070003050394018065944400010500890715a40134007840c400b030020681c201010004600075004102d01304c9110342c8441e400000300c4c0040000c3c1024200329502c10340710918000005241003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589796951 1250 589795701 589795709
    0x90a030b190c020c09060f091612110f18090a0905100c0905011110020703110606030a0506160e040204030c05090f04020f10020a1b060212130506280804020901 70
    0x60030702d10102007080d0b002c900c110070007200751240e031304944034000041c104c43c11a1418580000002080180952010000ea480c2500c10345686603043c10a044010688540c0001a801c0040400c13041c0e08540c000e00040c5416903402e6800b5031013000720400548011000e03100c030300c50940c94003030400922400307100100740c440001c07008001d41c40c82004040c00d502146c0c440c6505016441c414520784880070b100214048801030ae00b1903440f02c280c58050001c0070703103054421081c411400000d0306030400040301c0105540000003483c0a80d52044031822890800c3c02160412040304101e01c1c02d0348960010b80060f41c402c044d00384400b82801c050148400009040c454008603450030721026880d82d036000048100140d4010810105400c01640b9102c1c0301b4400402003203c108408c112801c95030b288105584041c0e00b56031003034601400066682c09020310842861003007140401c1540340c101c00400c00f02695802c05000d0580d00e40d0f0740030446403070004180c00726801c002004110310748a000c00b4094 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589798201 1250 589796951 589797001
    0x7050912011e090f08030603100207031706030c0d060203060a031a010e060d08090d03050f0d0501180e1b03010b06031e10080c0405071209110a14060d0b0105090a030b 73
    0x48161511107202e00c40d213284002c0c01d41340d00003010070031544090003400301098940b0015562030f4014a001030807115804003074100c4040e0394001c220b4614020031110542c0c50b004144100b806103e0712014029070018001681c095410100000000c0075a0300351120845c0c4880581a950316040d1446a107200080205120703048031380c0082c00107008042540d01c2e840040d80c400380000c20314503058865101e00d5405103511040407540b80170b01045034000134183d4620140d03400280f444000303c07600b039aaa48a0100554004203005100d07071a041403203400110b002000031480410003c04601c044e4400d075021501ca03110411141d034800c4449043c0d43e002200015042041c510f8456055101d00000301c03070500c225140c2001c5500c191241070081500080b1000401591000e49424030700003100c800001d0007281040c3d80003078000c520312512017402e00080c2119107449a007009100003040d402000906100044c071201d10b00340c54180b08140070350312945c0e4091031400c0400700b4491004040003101c0700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589799451 1250 589798201 589798211
    0x1e2d1401090209100e031911030c0301020a1b0807060507200d09094b060509131502130504150b09060717030a1b020105040b040b07050912011e 63
    0xb043d121102d406851384038918001400854100c0020300b0204103590400036010546001c400340f000c048580300d0508821011902c0076248001418240e004402d24100841c1140c1034054110000c5080e01d400c0920804c0443d1814400340c1c1c4034401c030384041c0c45200c00164080f41500d04400c94040040700140c5150040c5076050a01c50001d100341c02d60f02440301516115004c0c100d60710840d03001d0710b01e9a0388160b150721012810080d40003240e9010b001c003002c03003899102e43c1c41c00d001e000c0c8255000c1e0b944c050407401c010303541d003880d00455042a1508640d080121686040d41800a1000c0d0010002c1030302001c4140f8501070421007034801800d00802500d480d02e80800c81d4100c084103c801e104d906884164450344141000896840283c00b0304110b0803002080108400c500c1d80300c0140d08004004804021556030001c0b400c0b28801c8074000c3c0b00380481720104001c50010702d000c44d17200440c2d24000b40b8000c00c0b80045a01484c01c50b82d440340750b0b919202100c0203445d401401c01590502c802c01005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589800701 1250 589799451 589799467
    0x40b010b04030b012318060f060322030215151f0914040204090e01050604060f0b0f1b2b1409060a02161212031e2d14010902 55
    0x3c41080d06200d59541600401010355001454803000103411070010800b19210140a0007800b554004079800e5200c3d003a00380406559160030003e41c0c0c0541d0748841d4100d400c840110108a111b03489a40640941c8500750a0780d50340c0340c8452145208040000e003c03210140c02ca428040d941d8100c00c1d412280e441070603a207108003648840304d40c04442c20101c0d071100807502180420024802c9401c103002060400003080c030460415003065004a078151010040a55102126907070058940a00c43c600c00c0b04001047c030b00d100c070300083d0094141c0303052890346108070700a000b450994100c2d00180c04494075910702d42c9150281b9400401c80700a420b04040001140c0c84100051017401c2200344a04804100040410303c00c001218400e20b044518015203511082010768100c011a030854140340032102240e4154481d000f800d03029a5014000750710760042c0c0140070080d0600714448015842c5110100c0030650f1141820015142000c400040b80c201070b50340081c071442c05070001d070805801000105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589801951 1250 589800701 589800713
    0x703050915060f030d050414060708070308040c0504020304050d0315060f0804060e1e100212070309020301270b10050d02060f040803040b0c060f04110d0602070204090308040b010b0403 81
    0x81125006409480016614800083c90315034122a51a80511448250b0300646030008011f1040c0c2e0000241541031203c04800c00001d84161000245054001c2c408080000c4c01000d405030000c0c42142080c07443c5031100701240880e0421034040c0e4141c1d010514243c001a0544540c80d00c034042e000541140d9400c2980c003420040ca030504210801000100180610206910248488011405450f030f03407030016000070f4451031f0007641e603100350245a114820740c004500c2111a150302c41c5a0a1aa81c0e5072010150020007290740266019500d5094050304450060740344c00d2240b060b50b90100305051035052850300c840c80241203110344810154240041d6841142c4c40c4a142e904440040d0f42c0d121000740b0203c940160703030007505188001302e00451100604006441d0100e41d22040310800c1e620820310300143c5809a501818050407600460142d05040040c40030050189134003514150305580450202c540c820000e60009601805200801940c640f00f14014880c800c000c42c2054103686480c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589803201 1250 589801951 589801963
    0xc03020405241818010905060909010e0624130c1701030b0619090606053c0a0e2706030a1709040603021804060524040b010306180603030807030509 65
    0x1044280b02c01924030700b85669020300541e5a900f07090070190b84c0b1359503004418040e0805a481b00d00c02c440240005400040c14483c2e01048800000240201d855641c03210103401000441c5040c4500c000d020a41302da142d07021a02403582181c480014480880c0a005003410301003402c02600460840040010407070009078960084011560747c800150704200130401e1080d15448007020324100701001400715005405001007507070803003100003580242c042c01e1990300003000301144d11500c080130a201d40c540d041c0103803a441c0100d04008412900400010321402c0358000304190a80340140c0c00459a4210600642c00907000d80003041d41d01499030300c00c1d0203042d441091064050b0041510722099403180c10800003140c0140007021030199465030032540c2c04084a043c0c1e10f150420000c514541c1030800c80100110780b0012396101a00c3d45401c00c0080c01c00c3c0f07035000b410551518004900c004074140c0c0038900c1d2443c46000901e543c51484c028003071450082c21402854a80b0041105070030001c114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589804451 1250 589803201 589803217
    0x604030203100b010e090115261f08070e22170f1315020c1005120c04091e060501030209062d030a06050108090a120809010f0c0302040524 61
    0x443c609070f5800040700c0030f90300329030079a5121001c1d900014440c1c0c01c0c420191303201c100135900c4410340c0c10300c007080c8140712080410542c100d456102c00944811007848502196002070a5031020081c1e88038016450840313213400c42000c00c00014107000c0980c644281d01000c0790b0a9048004001c412500c03550310411661203210141180040c06d1a22641008110b03030416620076400e0703403210384908140c00550b0950790780e03201604c95204146418607003107200d8440070880e0b40c0c5481c40c0000c080541012100003510f120395503c4280404654200380d0b0003032075500d07180300c22070f400741c101c494950006803265980300da0b0500d80304208800031501d4840c1100c0303030031110702c7d502c8554880941103c8888541c00310b121000c0c040c0402032090726005a085841120426690300f00030743c8560221540b515032141c4010101e000c20200c00400d5406924503030360002c080c4000048507204e080410782030f69140c0d0007410000b58001414801c91400407030500c001d40320781c41b0703e00c810710581000e075516120f03601c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589805701 1250 589804451 589804483
    0x2b020304060c0c090f0914070503030301120212010c05120109022d220f05030c0607060c140403030801090501060e030c01082809021c08070f1401091506050604030203 73
    0x40c0020700a6124220300203020076013013005801c00300351008004010384441210040710042551034441400101c00003a00c900901031450340c3d180043e403a100d02c10a4038103d07000108505030414000003071003002a410a19110319644d84802d404c0381134014016002095914414070481104007800304200702002410032040c40d00194602d1042418020140c82250003c240a0507002015096098600312818600080351541c0c440040549030042c24582507000f600a04c0110701207003041d0086034500c5918200f070310482506030000c2100d17520035041036001c50080f03001000f441c43e4600c40c2a00400c000c0c43c00300c042030500000682c4840382081038504000030700f03000c104528111184c0300c402c3e0042075010745418400340c12400203420805400d80c89103007a07802d442c5441740452a006802a44186200d1030414566035909a0b24106c2000340c0d5002007d054101c200703803003440740083d0300b030040d00308905900c0101518400d0312500e401050003514140810801030f01c0000d0904406c8035001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589806951 1250 589805701 589805717
    0x60804080a030204080d020a151e0f060b0c060907060903030e091906030311120310030b0703060b0f09030c0f03150c070c03031706010311030403051c0e2b02030406 72
    0x900403000f900403500b0003c4140107491009110a4000038118402880b8400b0b45003d4104540d001003107810886810078607490045004070350f18400c0e8044420098640c0c40082e81c0d44e00c0f40100f08040d003210248000302d0f0f03c140103016164504005220013030440703142c04c05145041d95002054914503140442c000c81092000c55014010380c94503031031104c1c0d140001c001c030316aa824010030382501c06140310f02d10702a40560910001502007203c0c81030700410b8402c4070542c50340d910036400d138500401041c00c26a5170f900200d0300c58420b20080c2129800351000949880c14042014181070706101050300c102c0740c2c1207400e4010745012403003041c0c408142c0300442e450368071050301980c203204814005013081e6440070040205600f20f803007000154907001b051406643c511005400b1141d0b95492000c5048080c80044e00080c8204010102502c04000d11011802141c241d41e040d10241052840351717801c4140c3d00d2051101094030040710105400c841480c21044200c0a0746a100e0b1340103180401c01f0071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589808201 1250 589806951 589806967
    0xa05040501051c0e070e0f01050109031502090402070f140a031b0507030c060f020f161205030d0501030605060f0402130314070e010902090901150801050f040e030d0209090f0106080408 81
    0x480c3c420140c030280c0d01400602582501e05032210814042c241e0706852181c04209528490081b850503180e06854074242c460071030319031302c4200117404460140305400b04800780f0307603844600142c51f485201e00300c003044201d95032134201b6078542140320105496124007004008641d1162118495100c00810700ea900c0c4414140182041340b0313504042c01400e1030700c10001345103a0021107500386500300e40c2034403400301081550540f00d40c940f50344200c0c44250000140031020b500c002030a0070038442e504584c40e02c2c3c100004034013610002d078400d440c2a03035500c0070020a420600781c200c81c88403040368118a03000c4e4040240c10320210038000500081c52444040003030040c1006808058031a04102080d590303035910201c03019500069204e4000c40300f0100003c0c4071460a40d442081ca22592200d415036803d00c814000c031410340e08038983e0311544403005440484400d0009000000300000050381e144914000d0002c0c00001400c40300e44040740358010400d144d440180b4580166105414079617445034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589809451 1250 589808201 589808227
    0xa0e06031e0f04030f140405012d0c060509150a09060e100b0f011e08070504090c030905071406040b07020f06030901051504020c071406040f0e04060b060a0504050105 73
    0x4065100e00359540708010b00c1900380039544000e2080d8800d80d21091042c3c648102114110500e51912904240600043c0b24560041202034000d40e0007641140a01c40d081002c000c041000c640a00302088003400d01505000040c0101130b0b1000b83c00c401041a02c164800b0355105040051003d1003081c3d60741d019030200003903900a0f050010440c0c04940580103414450f90090400400e07552080742030400150595005440c285001f40c0200000003101c0c145110980d22000010a8101000004c1002080500c0c1c140305401034400c20b170f50005408201303071800514004894100690b00c00d0510101103151ba1980d044605550980941d15240c030307030500c08207041740030603c1c0840e805a8044200015030b10150b000c030b88517003648100e280c12860304d0000d10040b1302ca0506454890b400c959018442e0360f5030000502d40c00c54002c2c0506d8a420303950764101800e403c0c180c00440404c401c460610043c130006006051100070210b038242d01d40038183c030b0013802c0c0f0300c103601c80c00d070601c000400c0140031158 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589810701 1250 589809451 589809481
    0x61d1306093201270908041d061f050d0f1109040f0c0203270a0e0f0c0a0e090c130807150e1c050a1a0a0c050a0e0603 52
    0x50803010510911180c8000c408071200160280d04010041d0719800c0c62111801140c20b0484040032402c20040409110400000c81e000c81403ca41d0f9440e241c05c03500042410008000500c4115030300c5400b4059000c074021f00d2000038101c2803140f840030b00d500100380710010700001c80200e02d00b019a52404020844805052004041c100061428508810402000d001405001e1b01258104045100c0c2d540c0e80b01111498041c084c0180e200380400365240440280c101d40140e0180608006d90b032041c0005030442c50707250001d26400d0f50540c18000940e103641e542c0c80c0c010103140041401c0a024032001889203910000e002c1c030982000000c07070b000b5a5510202c4c0d19124510007803800c4140c0382c03050290f0715482c0c0d01c5075090720120a02d03813080c0284a85082c10036080020240c0c4c01d0207048003aa020010312a16082d1014001e003000300c000070300b6015a4006041412400180e0743c81c2c4523841f001101d42d5084102c00703010381080981c00485d0703c0f04101c40500c274125000c54582d2a4024040c0c8542 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589811951 1250 589810701 589810709
    0x16050307170408042409090f020412060209152d0702120601140604030804050f0301020c0f07030309090c02150c0c0a03030b0f0406080d05030916030b040b01061d1306 73
    0x41d142206001c00e0040280040c015908801d001000c080b4544034503460440c2c90406004c00a03800350824811000ba9400c1036801051f100e601506003a111103001003070702d0040c0400c8138001c1d4005850721049c10032040004030040f0f112a058100300f444004204490480140304007040100d058407413504030014241c481c1c02c3c4c0c0141005550b0f441c0821020340c1c40c4003e0084104800b0b03d050000343c81d00e840000c580542e540704203800d0030039142130f0901c80751040c645811030b03041d5000d106401d04074034100039580c0c1008401005004051442c107002e40701c5042504414240b40c201000e190400307800041100346000b42e000e003030280e540d4807000c00b241402620900c8000380602c0080300107044e4560060030440d141118041c01c114805401c020441d400d9201d540040e801c000e210480c00b601500c050f581c4100c480042ea00150103a40460300d01495542086824607d80c1092105001144c40c005015004c0e504003100321150701d50103804411351105042c1c3c40b440418540303075120302c03182e00144010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589813201 1250 589811951 589811987
    0x70e07020607030e070b0a05070606090509150a020702180a05010b03060108010311150a09140a05090106080403050c03030408042c1302040e0102031018050f0a0b180108010b1816050307 81
    0x8031910b47c030041160344148020b88201d410120301090b070a22600c2524024040c8000030000b010001c2140051000000e00071088140e0a02400000d1b84030605440783c603d025841d65140b03480d20300d00b1001220011303004615890b4041c0100710099802c030450505498002a91075084180880003801d00d101e43d10341c901000c03501068a42202c2c0d000b50f4803509641001454061803420801803001c04040d030f100e6594401d11880040110034014648941c1050092500718070382100300c2c034902e1840d0710a441c00c40d140c120001c0c00300030400128000080a0303034200d0500b013004040c5a4209288500034201c3c001101d8500030b8a421961580d00401d00030b0701c20300082d9260301c1d14050103820342040744100201042449c0d01c58400040e40c0c42005e22540031850760000359107841400c0b20003050390541035500121b0b081440225000c90071806c50080c003040c40082100a1050180003420401c030140029015001041c4881820000c02e0200780c440d07546000d545aa488460171243d9990080d003426030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589814451 1250 589813201 589813207
    0xd03091e051009051b18160216030b040b0105040e0c10030b0306181621030314090706110c010203070209070c0f050f0d0f0516020111031308070e07020607030e070b 72
    0xc001011034117070302e034116030382c00e032008209143e050054985030764128248000e0200000364080b899606056124812441100c60101c03c0e19911000e0307004035001510b8070011802048200310f0085030b82400f510050700e080c0100c90001084070366500c00c8058091040031882116240319120750b00c800b15015008040712203500b401d0076619a001030f070300de0420160240c51030008800e5641910361080364040550003c00d0081000115054016002c0c21400c00d52164500901c00040050481c0240c07400405032119500d048806440c102901198000035004854040c0b0390361380210540b0030702601510780c90340030366030414203c840c005065002025603400c810074074248070000940b00e640009040403140c108060100c01c4c0c640c40c0c0c140407860300042c8100460802c801175a10361010491040c1027500c800301884e608a41140c000c46403003c9124142c0c20100311503081005848010001405c2d20504c1d03080050000b07480703013030090000d008c0c152201450b03440b01404015000c01030000d03141c030640f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589815701 1250 589814451 589814453
    0x11e0c0204150927020105070b091c03020307080709060203070f02120327010e100c06110406031a0d120804170708070203010b03010515010309030905090702030901020d03091e051009 80
    0x34000c044c061112141460312402448482d5004d030b1007815016100c460418404d030ba00e440f44d9010051216240b80580310b1008520703010f0345a40792040c1c200d600c0150301d0f0300d04810000e0004034002c20131810000a103400300300707040e000300c21036900395003040b405403610755640045610050015a42d120920000605001d4540b031000d102068001c40701c40003160122080044a42c8d03001d052a1070380c4030302c0300020444440e014501e1401c02c117128044c0400c42d03440c00d0b103013181c054200d64098400310b5150304020440745600490100950801c0302d00c0010f408184d1a2101d02c03070f090b80440030602c4042d03000b140c02d04c525031800c0c540400002c000c0560b10205131610f1000740e00701d41c1c4203d02a60810901148515042c000c040c4101c40215900048004000044028100c42c18081e0140004d02c080801d0945802c4456442030003142c00841c0d541d00704400091820700201c40307090805103400188800a851200d241443e45c40100c004080742e41e503818940d04082a4040b080720103494280341e04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589816951 1250 589815701 589815719
    0x1050405130608070b03040b07050a02010902030a110a050a030803070e0a0f080d0306080c030d050901050d1805070b0a0504060e0a05060307030608060c090918120304140705011e0c020415 82
    0x1c425100100c003034551304d075544c0703107443c0b514003080c0d0b07000742406602ca0024529511803001f03401108014070020800c00c40751780100303051102d20401074aa6802c0c0141008040c1041680303c0000c010030789076000b1461450703c03241254007000d08004108607001400e0190b5680e1811440b021708101020710092983d1403020503a207040c115184000b09040c094000f88030b600200e070703c02d1080f0018025140740c51150341c044825900400d15203050203800e1061030074404103486092802e07001e0501c080b00501c0c10b400c100d85001050392018410b55401c00c5104d102c154400d080e00c0071943e41e414132080b9851058002880c42c4c0030381d0016508135202204100d0a80e81c035400c01011a9265000e840964903a4220342402d4814010611b030030404000118a40040010b070100043c5850f2080c0d88134906000385c4c1c0d68159009075001c3d41d00248400000410f442c050050380300a05017404c02c0c00010079141c0c03002c0100640c0c904d0b0107083c8040c64840e40150348803504036401a100d690000700c1c0c10f580b691a45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589818201 1250 589816951 589816961
    0x304150e190915061205220b0919030c110a1503020304200a0311030a05070303020319180b0315040c031e05060d02060307091203080402030105100609140105040513 72
    0x10040e079050443c03401003100000d4098040d584141d89101c59040841050340203460b020742020b400104c1c1c0410340e0b14208011611809051090b03a164515062583c8860320702180080f4140c000040d20101100207a004030621550644c070030020f21144451000084030752000341c1c010440c1c45c000180b030109071581070b030065205038400c0c800301c6118029400c40b10101403041c80c201c0d07003200c0000c9041c0b011807580c0701c0000314504000c00316030400030b42e80e8500e8100381251340300f20b0141e4004910b818004e107245030b141410428a01d4000c20750b004004034640803811074424102124000000b198024640640f0710784445000f400c1032000c0709894100600500e408242d40300c000b007090540000780c0001b03000303440c0030308030040848410750303030316002c01010f0307807000d00b065060081c25003000650b6041120141140c074000c2e1a07090355840e043c018103003981c0c001020b03030110040da86c0050010503004800c000588d17942e04401c1c241d82a03540c005031440e1149800581e802101e440b6415141420b98000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589819451 1250 589818201 589818209
    0x11b050a0c0e16080705070203070f06200a0209010302120a12050a09170304030206130e040308061206040210030b030a051005010311150d1814060105010801170304150e19 75
    0x2e01d01c201d42ea4400c45035140d80ca200d072418005a04030005c51009442a07000e4056140010151070045036520a6800c45a5440d0f100720080340e04601034000407072000e10720807070001c01480a420808800d60000d080b0300d40502001b8418200240c100c50399450411015a907594042c058000301120843c1c00707081c03a040950184005400361002050196000040081d40040c1070015400c2c981540d08110081e0411a40207034010040003000400d044500300660007a0b02a8444203014100007080c45280c0100311900c00081e440002801300503140e8031603060f541119403800141d0b0004450019003041441580030301207229554a600d107400312903215070f040342d11820380d020180031480d05100ca04040ba0306000c912003c188540c032180015500009100500030b01c10f14210320042c4e444001d40b8178040202e90036580a500184400d5070401c00240c098600c180f076000004404a081c140e0345d10940c000e0001140041c07c8401c003442c09213200894007240200040c1c81d0480d109418180a446442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 589820701 1250 589819451 589819469
    0x61602040207140c040606080c0901180b03040507090b01020d230408150a0506090a050a0f06030809010908030423030a06240b0a0807030e0705030d0f1814011b050a0c 73
    0x10604c0c0640c6407500c0760700c04445042c0c40d044840d5445101080d819040000600c1c14000014004011801c205912402600442d01070940302d06242c108245007a49541050203001e10300f6415605680c2c000860003104111860300740300c5580300407141042c40211b14102c0241480100303001c5107241c070118100721121407011002c03900d959886480d200351035054855940040910012031509101900503550018214401081501d13290200740d0480305031741d1059038801000305603480e09603030200b245d4005008400041d420300342440b908402d4040107020034041100c4d101140c180d2903c09016a940a540220080240d2a810181c1041e902074070b04400100e8041002d020400c01014015550042039968994081e5603a0304416401420101003071015841403040c001241c2c1d9082100700c140b445d195880b040540d41e0350780f010b450f45070302c0058131a2079200b0740c3c1c080c0a190000d48964410880034a005410384138122000c403c41100c0e003c0103405800b51249130020300c480c100c401021520054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 589821951 1250 589820701 589820713
    0x10506070c0b03071e0207290306011b020904210206190f06090c031b2105070201090b09011a040612110a12050604150504020306150604050303040f0503011d06040206160204020714 79
    0xb4500205c4c640023641c003c24070100d0043d520030111604900705504110724140041c0d00096041041105c0440300203000c0c00642403200c4419020003a610300900040126003415060351000b11500807900454540e104030900c0b400c0070640000d8024404100100514652560300501404040e814441c0381004041242c0040b44030b044808280c00c2c070540104240c01c1010112005400083c0403c2e0441d0b48556170f640200349806119402a1a22000001e0342034402506c943e02d28001f2580714411498210100150000a240714034401c1d030100b03007203903500d200d1000661064481c0e0014140050b421960f0740400c000050080c0c0500c0c02182d01001c10030f40c20b0110010750b03500f00c50094040d0041e60101d22810000500044200e10041c26142000d443c2d04c0403030319540007030f484031a09510f11002000141803c0c807550b0780c003880c141606286000d12480d450342e1210054802030180c0300010751294080380b0745210300307a15035008209568442880c2030155040d80d6001b0004040c3c0104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 589823201 1250 589821951 589821989
    0x304170f01060e01080a0f0807140109030f02071d0c040b0711040501050d0f0f0821040c050f01020d0f140d140709080c010507050307020a120b010506070c0b03071e0207 74
    0x2d0f41c060403a44040010191110183c0e44c40000f444103c0b0112100c49050281c0070010b0014207039103804918503000010031088500b40103000d041d840e01c3c010150b401c40003042c010002c1040ca804503601840c1071071822520381d42d4183c40c2e144916444840b04803000700740e1008102091001d40c1320300104a80912041e42c8410030400407001c68a03004100d03038020ba40307000000e841d4521800c0110301503000c05080c800e0064640043c5c40c051240c07915420321800c10001000310246666001d024203aa05c0c64103c0c5000740040c0d5078001314640740007070001841407888414400c2210391010a260b42001d078540f14240418400703030204070568500c6031452000600030a02ca2840d8008403502c00b801000b40011860041d5203e40c4203c405461a002c10005030000d80c803030b80b0030480200f113844400625400b06003040e408480c0182c00c254481c440800030380000c00e8030204594290b840c0103080607501d40310300209880d281214107060156505c1112007488942c0c01061000441d41da000c41041207800c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 589824451 1250 589823201 589823219
    0x711030c0a1701051f0302010e12010216050f06060306060d1b090f0c0c030905011805180103020a0812030f071206090506041802060f0f04030b09061915170304170f0106 74
    0x1d911580d4803021701c040c10030005580700e070320100c0714444050703c0c05c09207222194550b1f09a90003140c0320741140344507201d410104801004800e00715a4080c02130000c0e42440780000c0e45582001d0f008511a5058180450501205c00390f4403022803580d8101c50929683c81c4403078400f81c5443c1c540042e60b1440d00000c149078038006c1942c0350f5259416590500014140001134414030f201314224404240102808030b0a0741b103d0707101d4803000ea401025402690302d984104224081541c200500380d0300300061b40041a094402603d40020404031980350680d03403240d0031a02c03c40c0e01320b07880921070300340040080c44800a600244c091901501c003844001c0c80c200c4e0b244080038120000a4010000b085204048000b100240190b8a00c24190900c1c20ba0f582d110646507040a03031315503149401400501801c200100b10800e160220b00c2d006010f0f09031000450300c9030440d544152022a8064405494805802d0084030701822080344034124208100840c2545e600d65801d2940c415840c1103004074040390 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 589825701 1250 589824451 589824481
    0x20d08130f1403090301020c032d09040225060509012f0c160303050c0105070903020f0f1203070506091509071203051c0212011a0711030c0a170105 65
    0x1400841210310450701c2d40d56039403034403038402c4101e02d030740000d11151405039028002004146e40c200c00940e21040607440c0c40c07840348050b9001c0380f0b03100c521040f40000d0000203c1610310052003203e00684a045030718000000100c4030b003285005110b0010600204000d036486180038407580b0000308044c000828150144034414640c40d0201d0344034003c8d030810a50040000c0207240c0c191030541e40e405521000b03032800c00d4200c0c2c0003100420404100c20520f02d00c24401e15030701050610305a1601440e6401140e540000b2008031800351320626259a280e8603400600c01c4100c0c064802c90760341d40345a080c482d880300001d03605e44099005540306503404038040301e0383c107000340440c101900c505171800c040440d00c0784006c1000ca05125050001800442d42c8ca04811a0004c501d0409079407045041d00040c80c041c4140c0018824550300411002e00d10200c4090300d600580c414001303056030351200c00091802c00490b040540c8003d5480d804607030800e9552010f803000d86100c00a018a4544e4100800c00c82 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 589826951 1250 589825701 589825703
    0x3120f1c020f270907090303020d0504030c030b060307031b060801053c06030403030e0105130308010612021207090302030f07082d010e07140105041d06130507020d0813 74
    0x42010700841c20905019141040c408a408400200190a800204c0c0e01118100c690101143c0c3c460313003c1090640511076000010180c0c03030002d161505682e5000000b0900b0701028061004c5400050000e4500300002401340d034014801c5281c40c2003088a120790141a802100009070b40180002218100303d14074801000c44841c2000010018401e006c25690602c0c11a10000f000c141c121900740c3c445000944c0600c0c00b90790701145280c40c071808d4500b51071303000e065607100100340c9125001095002004a0568074145814114542c030314111901a004d814481751814100d4820b01c2080350b08085402c0c202c910136000c0c1d03034890911262180d01e810491044600c00d41001d0312280b01c006404c10f00f844000422501242002120f410542c02c4134100e00606900d0b6124402c18040042c8202004401601c00d00e002c500d17042c10a007200d401500f0100c00e0403410444032000c1074890b5281a03a0f06500d801c29601040300b4a03009070000d40da144a59a4400030806c1c24021890762200c0c4545110b00d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 589828201 1250 589826951 589826977
    0xb090f0603040c091e0203070807320c010b03070b030601020c060f18010c060504110330030a0b120c0a09060b1b19080702090a0203071b0203120f1c02 66
    0x10300e0030100720090304000c40d031781c11403001c0303900c0c521801d1714144003860003110282c0c0c0342605841d000070b0207403200a41220000c12500c04c0010001c812615041c20b80545110030145525006420141805880007a0403071307906000302c0d10301242a0000c01301443c4207039405d17822104203030049014083c0910a400310341060240805c04030060302c0391100c21081b60007061401900a242a03220401220820794080f01d8595020100982a240402406100d0500b81c2540114025030314009800001c10061010060001200080420784242c0c13044890000241040e045c500030481019100c541711a4400d2040c0e0039250003003522401d03445441c0030b48034400c00b5076140c034a09007200d02d8074200080d10400c80e0310400c620391241e1101820084140c0b17103d441e20315217944040c4100451a030000740440c640e0361042c0200000b081d400300d0b559100581c80705962101842c18000709040c490071420b151003454002031402c030440c0c0700d840100740d141d00603100f41c3c8000f00a00c2d50070b002e80c0300f000303215501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 589829451 1250 589828201 589828223
    0x1050a0306020a120f090314210c071a0108191a190e0304090e0604020d14030409050106050a020d020a05121606050403030923060703110d060b090f060304 68
    0x1d07110758002e003c000c18500b0180481025562140140c5000728082c0b56610344800d500b80400d5000503691071b07110301c4803030321908203011080c0d10181c1114003115601d6581c4e689005c07441086901c0100d07500f6680250300400312840c0c2e565858840c050038070451034940305114428940d42100441d0804581d03200c00d444100015550701c407403184101900c095118000420280740400c41d911412603251100c0b070155444038604505107088484090714507916401c40d808101c01030b6941c115508041e40d2121407140001100c9800500d5401250090580d00707142100200e0b4298103d00a00b03258803259013140c03c440f446013800c0340c0714800b8120080c0b096014008200020314500054001d08842d0f04c494403554105407180c0d000c0d514256030a501184da0362003a9010b10401000e800711680b096400ea99080e190140042d9440301c00510600800d9a21005c084d400c01c140821200040c6c00d054041c40015158940000e9075400450024400d91070b03c48008642d0403c5d42c152403103240c2010310109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 589830701 1250 589829451 589829453
    0x501091205030f282a090803071712070c0c0b120c090607150207060e030c0703030f090512060123062d0d02041508160f030b0d150605010801050a03 65
    0x2c10882200724040b00d00312440800d040d10001d8401c950410328483c100415040708191704240000da080c44030760401c1070b03140091001042c00803c880c0171035800070411004421201500e142401049000b6100b07070390f2502807040f1550302c900071100560040c4429410b5581c0c03490307052281d00c201451485c420446000080800e94100c4c0504099440039145501d41012580c8032020b8540e83c04000c40d989a000c02d4400074803203948074450070346000b80300442c9810701d00b25540342e0f0f400283c03100604211800980e0108a485003200b07100404028024400c0f01d8404008075842d58824002d4402c0380103001004c0101e078120610f000310410014000754a001c41d96600ca5242c1c18422003003241d07000c40c080010800d010039400a040c04100c404d80103803540d051584480a0070142c0309102c2c10040c2c0380b0309100001c0008003400d04042498140740f5013000703007142c00b500540a141421548152603104600030301140528075038440c40b14100810401d903c480040d034450a00b80119501300d81e40d203100780 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 589831951 1250 589830701 589830721
    0xf06010309020604180e060c0405010516020a030605010b030f0702030415050304140712110f0105090f0f04021828060c060b04020f0d29040c1106040501091205030f 72
    0x50085400504000d15103916041082c440c2400c10440f2a801c80c0c1d5051b08841d041000d0048540100418001c285041d01d050002440d901907402400780031040400100304541c0c07003100c40f00003598060000d100f81c1d03a480319002c0450f002102d21441c0d050303407140002c6000d8400b104072801d44220031508002200c1316003003110990402003003203540d175403031410080030720074100039400c010100c0b07850f0448007081a203071080750080c205640600450422a99101503070700001550305481c015681081a030303080704005254444074500403500180b001500065108094400441e03140042e150b1040e009051313802d070b400700c4a05c043d4440342c0100102d0140021031155691000320342c01618042641c0109600040032a401a40b030410300c1100061405515910350150003d140040310100c081e40c0c4101c90410f1203803c60310640b034850355507280e0414000b405400d081e41e280346d50200303d840a280515201d402801050f9064a0f4544a0750b50b00c00b00c1880386040380d11440b4100f0505000da02c49000030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 589833201 1250 589831951 589831961
    0x801031e021831030e0609030102190201060f05030a020f0103151e050a170a03050912100e1e0a080904060e0a0f050702030702031b0a18090302060f0f060103 69
    0x49901080d0401049034010304141c1070b40c000d601010020755803c007101243c1d201c524081082c261584543c00d40341c00460f41001c03441c18585001c1e03c050780c5d21401080007a00901c52170300004150a480d100000e26541d0543c00030f0b0581d079407035640d0705100e515201055a10840d0301c000952200d090150011503510a802c145505640c0414019110f45c1b1502240400180e60824800c030f81c0c1c10140410080c54158040d1000386000eaa10b4002000300303000181e00c80c20800340290503c00d00042403645074903401c0c83c0542c0440d040b02913a00d0000c0303510b0400c3c0600000b804016071481440b510b08294500900900781c0c2403080d20007440100c080ea91061100d0300510551548290342c1e420016000c07001c1442d181c450451148000b60540724460306408803040070f0304880855000344034010040c1c400045801c081c040000907804418010300000e100646142c000b203515102000120404103500e030000c0c25028403a4003a101703155504446080313034600403290120004140170125034154043d40c48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 589834451 1250 589833201 589833203
    0xb060708070c0f0905150604030b160908070f030510060501020a202e08060f0108040606050301020412032703060c090b03070c02150a2705190e06010801031e 69
    0x10360061155903c0a82c000c04a003940030a60a9864004025181c44041c20603101795204590580c1428110707102c24500c000e0041460110302050411075450034010070001005200c81c104444160f9100d184801030030b00540710449841c480c080300164580075900401041d584185c1c014a01e04186803500c1007100f0881601c03104030500210a2501602c400207140e90080d0300e0840303401c2c907262121201c81510040300540d42040301d83c6050100550305c02401000030320003446c080a00740c0325810980001d241c10380c4841d80c5903200040000d18414a00301c1c0c0400729000303868800034401c5086460f054808407090317200e40ca0500003401d2000441542c041d03051244035140102d50103460f1007000c40d01d503000f503078107601280030041e03541d0461622803100c02c028200d80f45241d080140a210103800d80d4480301c20244421424101c440760241550809001000010300f46901164001c640c082124030310302440c0600034020000910719401104001d0485e584041c800c00341d1308107020604511101000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 589835701 1250 589834451 589834463
    0x14070e0d060e25060e061b1002030402011101050c0d090503040e010e19020906040501050c0a0c09020c07061b120c050a12030f0207020a05100c0f050f010b1e041d03130503100b06070807 81
    0x41e0503012054100407031791030402e2345280140c1d20f081600000d0301162000740780040c1a0b0604041002c154145400d441d9411212400840e00b44400c0c07500302d00b140216003014aa980801000003901060760503110b0048240da590042c50380305803000002a4480c0070991a0420300c100801c1006500c00c400425002c590201600d00c00f07031050b03890511056042d442a4a02900411b03052201e02d000d01448000b0070f20741c1001c41007810391059958001c05031b0f40020309400001d110071901c0c10b004d40400700c0200d501800350760b015185882c090010000c80b030402e40001c0d240120542200300580b00315004607400070000c9c2c50032881d203010081e070f440c411079040c001c0001e0006035100151200070b1031130b6098400c4019184668002103171318211600c1c9007110384038010000700c0700340034541202c0100c4e02c00015030f0003190103465285a0460307481201d1811440e031000044030f50182c50078944110513900c04900342e414500605209100b550010740403250b1112042040300d0000704a90001c0c09880d1040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 589836951 1250 589835701 589835737
    0xb0f09060f0c0403120801080d0302040f03060902030724031805060420060c01061703040302060f0a02010b130506040c020f03041419151214070e0d060e25060e06 71
    0x65100c41068440305c10810200f40b20000501041d5014802007024860314074085040500e040c0d05504800706a21000d400603680300c4411041d502c040c03003000050806005110b48142c060804901d6042c90720f000b140002c0c0c0b5011040640c504495001501c00e50080c00500290b1a00c0d20703440c0072030881d42d2401000ca4400c00150900e5141c3e8400342c8a0181c4540001610a10b000e05412103034010320301000090304100400c0c001030752101c098584010000310b240b0703241e10a2040690043c5100001d4079403240c100c1129160080041c2c11041c072901007601d051025a08200b4241c0e542e082d6a021030905400c140401e1203d18071144900d02003040017080401c05500003444401050010b422100b490300c103603005011000d8100d65424070404440d41d00300318140030803a40700103005020700340d84d0030410441c41c10b124540d150a4000340040e0003041c02c005c82d81c240c0f000740e5503410084240c139400700d1540550740e58501d4500b0020382103d00949685c05403c0d0410f08102151348010403859282041d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 589838201 1250 589836951 589836953
    0x3011a0a0309140a02030106150f0f0e04090b0103110a15030903020a02090c120c0405010c060f021b030a091d0403080720010c0306090b0a18090b04050a0b0f09060f0c0403 75
    0x41850f14408125031400f800c02c00d11180149800d50301355070072000c1c1180c0014146041e2070340c4014602d0707511040740350240721000c603514100c0d816941107420503071090622410f0010710010047c8581240e2185444114a42101052004500507481410710000d1f1a6803030140c154020740200040da031003807064940e9513020741d000826241082c0c2d242220810f01080000751080390180c4150082c1c0e8013100e103400c040c07401c0c0008215020300700d0020b043d241c41e902c409000c1c5500d0b4054038030000a40d258507070b65402c80121140e8940010302840b001911031400043d51030b140084860300d00152400f11007090360703940c409503000c0c0c101070802ca04104043d0705a170210041141c00c0100c0208420010600300c0035404000e083c2e8200340c020070740e100e00c3c04503c41400d41d910131006c0c049400d035981000d4200d180003011401070140c154090b042a1600080000300140411b4591306240f1034000b20303509444001e80b004c150300080b51840102d50094011402e011014800164030101e0120001d18254903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 589839451 1250 589838201 589838213
    0xc060e0f12010911011818020408030304030c020f010f0801031e0b0705070c050a0e040b090304050d030207090f02030907030b040203010906020a0c0b010806190b0402040b19030e0303011a0a0309 85
    0x1c406001c6075140d42d40c24880d0300300201c810414000e4502481e005000158401e2410306200c80d81c0720b40300101c01800e920303440d201c0317442c0c054400810910064940301d07c0d060034003829076904100708a218010502d40a41c15600034808201d403444541d035000020b81c215038800015195440e550402901d0516280c0e0000e1142c4002510032080c580d00d00d81ca071683c61610542a2200e600080e2260814140602c000c803d0702c88030307941c46601702c8010700303040c2c4030040300900718403076074100030342061405184c01c06143d000100c0c241191640c034010003d40031701400311002c81c04252000d0301e60f50040001000071601404005821600041c00066010160380c0c800080b0b81c00340d1082c50101e074604001c03400740054000c900e40141100d07405080703a441c0c0280001c841242d20414042d02980d10f403180c07e000d445940c19a070203041c20b4884c0903a20350040d0700900181c11480e4910000031b003170016002e1f600c81c020094074101c80792559017012108044032400a250031240c1e0060806540d021880c002c619 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 589840701 1250 589839451 589839469
    0x1a1303050601060c0c05040b090a051503030409020c1501060203070f030207120f1a0603101a040c050c0f01090c0302040c1809050108100e1203041a0f060f04090c060e0f 74
    0x100c4d403603400c0084218a8403049200b2a903002510480c5400030260164036205442d0b40d1000d00204001501c0d507982240140000000700c0081e010312010030b005c603200e0a10303030091003860f0700b480486040403075954030450400c001740121001030704140500380024001c01581406a03210780141e61170b07141c036a0715541500e0403a20003039904403000390b0204140b00e0460541e00341113000c1c003003041e014a03240d40032030b568103c0305118411150f0744000c80c0c2d1f001c0110000e03000304804002c0041c8000910014000c2085d00070800074416030103100036a411032481481131a009a50003801c0c440001d145808200c001d202000c0e090040c41601d06c980745c0c0340310000d42160068401c6942c0081c0703650412903020b282070140004010f6a40c5054030050488500086d4035025a5203180c0b003e03941c3c0c0c0e0350f151202c3d66107900008010490011030600900c44158021244220415110028661419410401500c0e08028003600c0842c019100b4803c991080f9001c09034607c0c06403040c0c0c0829043c4001c100300301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 589841951 1250 589840701 589840709
    0x121911030c010f0b010305040b0615040b12090c030303130305090d0204140a0b0123070611030f040b0c1c0e0304080312040b0609010f0b031306060315060b041a1303050601 75
    0x40d66500b1250324000d0203100700c070f40e206006e180401480c600b507070303441000403c0a09401e1103030241c0d84242d203e01c00144c1c1201c0103040781c81300c000d48520902060b5500c01c0415206c00449000c1c032181d484045c1000419a44500d407011325800072400300d524265055400b03d10402c0d040700740c000d002e00c0540c486000340c013040b50f5203a0000605203024800b10f001ca0750061413160400000c1c64907008801119148400247d4100e41e02c1c541e100c240346032920051036000441c0301000b002100700041c0c036141506091141f0700900c202d840d5039441d64030041c480d1003001f6155124405034108000141580d50041d200600c1850481c2d1070aa103c00d074851454000b980d20a0302c003140d0030100700c10020100c3c880ca40000e015101440d2950401c250070040911074082c0109103000130000420102e148014103a800c0d400041c00c01907552a418450107034589400b050a4203410f00d503000a00c0f4140742c0c22034048420585140c01105803000c0700103029800000034100c001c2062070007001080701405124020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 589843201 1250 589841951 589841953
    0x4050a120c0317101703070b190f0908121008030c0f100905060408030c070c0605040e10033915140a0219060e0d050c0f121911030c 58
    0x9a60340b8000b004008400d8145025182800030f0080210401c0c60b98020b46664021481040c1d83c4081d1951460058410281224400c0810b110340c441904001d03460000d00380c5c40a22082e030b440b1660b0801e94111b404014003a0320200720f6102201031010244e0742003441c08442d450015654401c00c1c1c6103400200d03084d44160400305900808400030008108004900300b01030000140c1a2501c43e12032200403c064481003001002554410302001251009580100d2010107139441e1803000f0030030b801c41d00a40441c0c00d42c200204000d0308011042c002140c1d8000c0a00180c0c1254141c003040c41d04412455180b8001203601804000b00002c4035407000d030009460402c03481c049100014484050851007424504040000340090781d4045489000744400503490b107007084c05803420350001c111602c0340c0c102601501d400c0c1c41b840340c0e1050040820f0103007501142c08841450982d10703202c0350281d00d601c50300c0038104042e107001d2100709400803400c000c42c10f0208045103403181d02d50855000036507000203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 589844451 1250 589843201 589843217
    0x30b22021509030f060603061503160303020a020915100f0c02030601092307051207090905130605100f0504090515010305101b080a0b03010b1306050307050103020a080f04050a12 78
    0x1030350904000e8502a24000c40042655007001c02c00700f500c40c14090082703000400b0748c0101a4098800300b09100a03c81aa40000a501d43e03c0c20025240d1000c1da10880c801c003140404918210304480c0c5018000000a01020351140001d00c1aa40365040e01221414040340c42000c0c405079609100e0980281700e03488002c0b61405c060701c000340e10800d044c11051080c103036050074030034001d9000b411b4402e101c288580540701c81c2c03a05482074988071140d52215030454144010001d581c90b26040003229588182c10510941c0c80303000101503c1d082d14002d0b01e00c003104440f010005460540c10802c11103000d0000d40d40104a503d55403100002c00341c009503103542c415a4469081c00c40e91183d40c07140c13052010100710302c404142008104440207000d8008440c0c5440400b0016902940102140340008000060620422120760f002e021503104542c400c0c040e0100000311075000f0300884080789110744c2c400c4042d541d401c0030b070070b035118003d0400c2c5c403244614040400060381010448130707958115211010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 589845701 1250 589844451 589844467
    0x1206020d0c02190609020a0905090c100f021218030109030203070b1e04120909020309070501030b03010c080c0c3d0b0a1712280306030b220215 63
    0x703607030704489041c00315400102042d41c402914009045455031140c4041030842160000445c1100070350041348455103040e00380034810500059620128601369522880c5c44540101640d0540c9801c1e020b00150b0000e80149600d00c01001c000d202d04c0f0200014007145070013140100f821502061012400359000003541c60910160501456100310b130f440040c03036040c0f810440bc00070450050b00040501d201c09042d024014000c044500c0600708a03030046444e4940302100c0f91783c4800d5441914086807500030086406d003418001d5005a01082e2540d152580314980c5c225034507440500000b030755000300001030700001c800504c0c00130341800f4140105211406110030614152003600c006030a01d2501c1182011900d50b81c102808807414848800e04918080c1c5141d420719000142d0b00b03c000b0400200070710782c1800c0c0445172034901c0710040c0781044c1c3ca00c1041c0039400c44c2c50f5400003800305400f0f14000b401d00c40000b24455941142c10103803104404081d40400e4883c16040318bd4010007002007400c0d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 589846951 1250 589845701 589845727
    0xc1107051012021c02130911090405040503070516140105040b0a23030705040509061c060f09170a02150f010506090f040207030804050622060e07031401050f0f062107120602 76
    0x6e40548036a100c200000c841c1030320f12440c0e42c804d25168500542e220000074041c00820300583d400359401c5400d40b184443d04050707121a6943e14081d000d031245000f0b0352900c0c030354441ca047da415240343d080b0040c40c0078404001175403c01c00c00c1400c402d8010301c0c0004040f00d0400c0d10702440c010301c3e16445180c2c03207500305010021504402008203000340d00d46d0314130b50402041c5440050000e500300d640080c0840754461140007500c4041c0740a40488030f10042e030307009003028070020f2a90700c100e40d09584050301e801110002025043d24809002c43c1c003800148502c2c50010028600020003c151403060003032280420184e8022000980110f80f481c0208000e010f000c0c0300103079000314440212845100e0724207161130401840745000c1e0400342c1d00c80e00445485001c000c1e240c0956049841040f8104880d403689019002c111174448400c0450404a690300c1e100000f0f6500426000f0003e40f80102c40d1410010604426032014142e4424002d0000b1450850814101294052a8056641c1c51505a04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 589848201 1250 589846951 589846987
    0x141f03060501031d19020105090d030e03010f0e0d0f210b03010e0c060412080702043e070807060b12031206300319030c1107051012021c02 61
    0x60701034038441413808103400c040820704400c8418400269407008003903000488540c0030b58500641c205201c1c00c202c8003410340040a05610803002c81c000c0c014400398a03040b606845551820800c1a88a5800740b604207000340e05002d00100c13a85480840c000c50080e9802e05801c00100d0551419921780290b4140d040a001c0e10104001c04c00003022140321a4004c6100c91240e449815050400d1038400d00400044504481c401a0010818008591708400440011002d40007600c1c0d07905e2207800310b25a03071240030041c0b19030198000b446401d01c2c80039110384981e9804030108030340080d9150110942965010030584120480741c00441d03c600c0c00315007586010101400061040f180d1907200d070700203c01d01a010510380d42018804da10420005011469030103001c84c078400254400f2180c81c01298181e100c800b04111642c2c601070701c0100800c1158856456004950b0015900e80400e91940d01803048441d08861403c0c005140c08208080044403070f201e02c0c00c5003103107900000c0100700d440c6072402c1c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 589849451 1250 589848201 589848221
    0xc11040624020d090501110a060e0303070810061706060c0d02060a0c020609100c050d0614040c0309020108061011070f09050603070807091a04050a09030210020c07141f0306050103 79
    0x20210307401240b801030321001d500e1003424100682803110807c81e080a1041e80d10903980b1041c248029042501b4031510b079001161704500242448000031a00781c19102e04000f26800ca0321040040c0003c0011200c038024001d1410750046010490b082071000108004945010242d005c0c101500b1b1000128081e6990101807500310f51240050252364140424480007031150400c0000b18050107c0040e20b00b8011880d281c0c2020b8600580051003984140e8600803900381201c040004a00b0703640b00b5804c47d1199500640002e144c076000507504d0414010300c44d110110340c1443c0a160608240d86840c0071429000b580d5078107800030040184003001d0207440c1d00400304030081c0c00040e04140e0820b46d02e02c114132807881101d0301c800902d900701d504034441d400000000780052140c0e00d4607051800c003506182600b140144a818041c1100b40c1301d030b1007038807541d00c0d41001404c2000d00c1c1c2703d204650841e03030740c482691040a80d0004604e460f40c2101045040000d920003098007071070580003500702c4503c042c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 589850701 1250 589849451 589849453
    0xa0801140a030c150c1208040302070501080108060a150911070b0f0138030103050c100203090a0e090102040e0f072303070315090e0a2306070c1104062402 68
    0x1c0d0501c000740705002c0080c15a64828204c4070203000e002021955504e04401c054200c1900d602c0004204d603029041512460086d000c468030f20360748070011503a4980911442c40c0607003051011034194007007a0000c401c9080b490440d0074266450760100c5c0b046402c3d589110240d40b170006509410020044283c85d07015aa60481d10b14035071500baa0403540c401c42b904004541352010078890040e9282441c0211484540031180780c41b036840c0d251803a683c1e40c250a0140c4a10b8124143d840b0880c4000222800000042c0050310038616006001e407546074058100700d200c2d50244004142d0302c40041aa81c0705445a10b030041346814500c40107000c0640d4542c2c400784001003a2990848100c0003c201ea070044040d240009101c1c80f03c0f8050250b00115400c460762050030009070140540340003070562106030150544510785d40040300c0e41c54004070300310000d003403540100c0002074a040c0150141440300d40280140301c518140000050100c5209401842c02d60765162000901c0ca00d50740d80e50100019140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 589851951 1250 589850701 589850719
    0x50a060506091009031e0b360307020409060b0a0806061f020a1a01060e040203060f0d0c090f0614040203040201120519060815220201030c030e030a080114 68
    0x1000714220703200310100316009000204440d81c0d2603124034080c034025504401001c5925100b10040c001550054909540005210002c2800c580b000c8210070f24041c94000105101c1007036174403003551000380c8402031032507000500c0030300d0158585010300c080d000d00c03a25000411081c0c580411015a2103074200080c00d9000c1010081c0a40702e054002c000140f2600344c006010300768500491500181c40030040007210914880900d860401c2c0086060792016140c0164050032002408124002151116400441d034850401c05041c80024501d04502414101000360b89900c80b40c815264040e244aa0696882c50200101c0c0d40700e0203843d4121100302d40c150300c4d42c02c1c41e40008080c0303640d41501d50070860361030740825084802032965080e10f441100c0d0034400780ba41d0700d08160302c5640c81220640c3d50b04000f4001a0103244582d840010500094400c1d070030403140741c0044006040740202d84062586c0d0300180d482d610010009024050340542d282070715503041030ba12044a200c0402118002c45103e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 589853201 1250 589851951 589851959
    0x60605040e01050613090e060f011403120d0612111005040e150f0310050603151b0c07170307060f0b131a1c110d081c09120c0303050a06 60
    0x1004007281120f0040300c03e2910b4240c8004507282a01e1254007283e4068034140da01ea504090101710f0074403504640800c095280c0e80d8200c241c00c01e0b000181d0880d41904506e4100310000700300405400d8101c5410400540e8544890b810020401c0380401543c4030031441c4100211443d03c20700d0700110400c41e250171420039140040c400b00c00700d00600660300c80e040380344118803e038413024040038500f0b0005003100e0800b040c2880a8005107015101b050190264030104081040310174600d90041010440004401c0344c18a6603000f6500007040c8058113000380c800002e202c401c41d211503611000030a019541d01c102c1e51400c14101c8100b945080412030411100007480e41c0d90312110070010100000104a14407a900c07501544120980391603442002d4880800c0c2240c00910740c0020948501032061280343c0710300130090852241d0300010070201c82000500358048100c0d56101c0c200008120108903075900d0340da9180d0090345c60301c00c3c40016070309050806c00d255140c0242d84d0058081e4004000f12420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 589854451 1250 589853201 589853219
    0x150608011e0501080a24140301050603071203050c0a0c061e020607020d0f020c09040f051018020f181602070f0806070f05041805070e040e0d1101060819020406060504 73
    0x8000c117940c0e42d80d555240404554040340c459004c130410b600e800c107420107032140340e1400f0090302141c0182c0a5860640051682d0600045080c01c2d00c410513098842340b02c0e079940440e490352140035030316480d016460351800000c00310f0300c808015141c01d07141ca01c7e2410540503094208120501c000d811036100e5014400901e03004510b00c0d07810713501d07803401005205510078280e10b082038250b40350b500051004204018030042d21100240a8429002d4540381c401c9452244241c5104078010340407c401603000d01c1c01807800074001000382c14050700c180c85480745180d0040c4404012039000c042c1009028010100c2603041c000c1a010700a07400c03032040600e05020710542d607608020000e04c203010902c50944980c0e4010310698004101510102d000c0000210022019200a0f41e901e00801d510381100741c1c0c030f0714040c01060f0215007040000d104882d1094030484c0c4074844456400c109541c0c1d0600440c10350010301c00c1c0723201d001079000c01d0709007807040c0c1c03041c1300480b442648410104072003440140b004903c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 589855701 1250 589854451 589854467
    0x3130b090c100f0918020c0d171306110309070311060403080f030a06050303070609050c04021c05040204150e04140604050304060f03020f0d0b09010b09100503040501150608011e0501 80
    0x40f032030540440070340100c1c199031015844e00001703400700610309003030007150b01900140400d1019401b03803156103001c058103450300703049198502c040384504000500b84800107046100d0f41e90080300c1c08227800c030004081c116a40e000341da04030301a400000081c004e05c00700c10200014000252941842c0902d035403901d81c2c03140502d04050180381c0d03001020410880141c2c215001409004090300c0e40d030311007403070140c0c0104451141102c05001d603080282c1c0758901413007683e0810480c466180307004031868802100920000b40100d03882992895003100000b015080d14003d0300004248000c1410241044081d414034a010318415500c1802048005000407003a43c0498019080c0340000392510300e0182c0c00380c007078490b50fa001c100e80410000c90074001038100d06190764054503400013a0340c1320310002842d84140c081c0950040c00130308540c955540300d100295840b0b4020000000c08030388258290a51488640c85000000c2d01c48005002c4080b80e2018107c582c551641c00040040c03402c0c0018007a94 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 589856951 1250 589855701 589855729
    0x120411100f0c0b0a0e120c010f0216112d04050901020a171e07030b09060d020307180209030703030302030105011d0108130614101a030613110c0303130b090c 69
    0x1d2600390100d1060344d01e0350000f21001e000ca0040c2c40d03001403c21034210940e0000401c4c0b589540c02c008000810700620710031a08040da001c030700d06812140e0340e2540b042c28424141403941216040c0080c140401140c2920241700c041071030060148000c40003000142e0708040c16003450380c3d01c10494000015000340703c03d00c401c4181c500c507111317643d00c074070f80b520580603108264064106000100807000398517602800c1c4070f55080324000c070281c50310000e00c4a11621010002d406600007201809814445202c5c1003070680000030152504140328082070034881c0b030b54011808a600800107201c03940e04245004007500303001142c081c062182800007002a070028111152044d20b00c1044407d112150b004851046082d100c42e14990600c20501000c1140318411003202440c016840c004120913282228003420004040d9841c017440d40c2103200080400000080d0540c0b001c10110506030001c2c0090340c41030703085030091003600707a0b6801c00d1001600010f1840300c0c00d802c00340119003150303204e2500800d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 589858201 1250 589856951 589856963
    0x30c01180e0405150703061d060a170a0c030c0603052202010e0d050313030507060c0510050c1b0d1e020a030c0203010f1104030203070603061211030102120411100f0c 73
    0x10b448a0a01904042c1056001040090712908024907550141c1100381115a405c42d1413000016004100c001d00c00141c5403e94031103e0f4500c204200060880406517260080050340d080a02d83d41d9542000107080e4000c9400b40d1000d40108403042c0c041c811541e209040d00010000008540b640244e07002400c00c000741804100342d00202d01e0b0321044c580d14815544a000c903a902c0b0403c82c2222042811071200300d80714443c00d0070100f4090311821041080c00c1c1d004d80140103040d00e4825101c007030107004040c2c101115040c030050030f80100092004610000d50340141880710440344006210041030301c0c1142e6444280c0c0d110341744280e4006901c826594042c42c00a80d85001d910000340545164000514500d00700708102d01d1590303950005108a034030031021030340c0c0c0c940d5070f040c01d5055407014400c5080c021480c483c10300210fa1000710f0346000c40001000185031411540711f4408dc0c8000355020b8030b081c21041410b0720281840811440d01c00503909010b0010761802c28000c0a19501030401812 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 589859451 1250 589858201 589858229
    0x320240705030f0408031201050103020901090504180606060f0801080304030f030c02150a02010626190305130b0703030c02010608100b0303040e01120b011520030d05070e030c0118 79
    0x1030050a0043d1101c525880582c650b030307140c2e140500c0d60b40e90010001313030f1000401040001a998004d100320740c46440183c441d000f8a80c079003001c00009004480c1c0103d003180080b10100c000480c2c1e0710070100507103107070b0b03da403d001c1ea8080030003405c00030144c0115110740d00c20402840415050b2600b080c0155140c580700c48211018404190186030218070440c0340c020100e07031001c680b501908488155401c4c0e145240d09848841c103102c00c0d884803036050600640008900c4845c1d4180d00c0000d46000e4024103082e454410b03e0300c2c2182080c0c4083e800f0b204225404103048080503414052810301c40c000384003e00c003943c24020a2070711104200030755100c2c075a0300e0072203180d503440520a07035000303060a5800c0600766940c1c103480f038107a20f846802180c00c14581c074000301d0b605203644182c202d4a4100da40e510325030ba565a001c214060065905046284014045112042230038040c6500c11456962018007008140d0145132610424012040c140a44c0350ac1c80200d00d0b00b0034542f0011144141d0b92040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 589860701 1250 589859451 589859453
    0x108040b1305010c05030105010f1e031808040303030501051305040c14130e0618060912070c0321140c060411010306180e0c010f0503070c0302010b0a03202407 70
    0x207400111008024695400c120706403001a4000014504803034080e02d407009868002030301254030140182d00d1a20a0461003000704590b07103c1d80c8680c802103a5000d02c030012035015103c080301d54216510440000352180014002400c10a00c030000035184c8035018070060410366205500c07c400d50040b4840160403440c400d0041d511159600f040004004040090305c00700c0d04001d488400c00c0b00c40d48598130b59090042d10561001804901c600c0d440401341c480500b40d0081082554080401a070303e03158003a50202c0416180c4907880d48210f20a000258008200c14026000c80880060301c541c06101348806403041d040450101d600c07643c003002d03d00c1d0729001000160010502500009100c40c0190714070542c203a00d44c0d000800c00e188107001c6410903030315000110740145c100d00b042d2000400c18800307e80200d00503201901348620178000451131109140c041101010558030a544404010460400c0120142c6042291041c2030b10f441000344000c4400d03105d00941942c004100ca0740c0018180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 589861951 1250 589860701 589860721
    0x120506010e0a03061406220b130c02030c0c09100b0702190b07050106080610050d060915090209100303020c01110f1603031205010e01120f0204022d090108040b 70
    0x1040310600800701c0940b9078aa0800100414105d03003441410b0312004e021030380c18a4948152083d500880020240d160588003211015102c181d8070141c00064003018040c4903502800b440c0342543c0303164010b6482e6182144400c0c0341400b10300f14940a82403606c2401f03098488034592506032001129955a2050030b8030100d038030304a0203810200c654050b8040401e0741619100200049030191000348111500c85003202d07165074050352603407100c074130405040169040c840c0c100d001090140e84005401103d907140e0343c66103104105600320460f607402c03540c03085207840181c0c0c1d50480c0a0a071130341c14a40c119074001e90ba170404a4605d0f814080c50842c45502c1c00010001502003c0001341550300b00e1080327016910762035019000407808103040310700c0052000281e01c140d43c1202d4142c0210007459180003040010762003407903000c0d104a54003410754005a100c0f40014004d9400b00c0c640e08000c1100310801014002000c004030340d0404042201d400d40781c1e404292203411541140d4246040d883e03408000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 589863201 1250 589861951 589861967
    0xf0c12091011060c0c0f0f160b0a0519050706050109061a0f03072d08070f030515100201020d140901181212141003030908030f16020d0804080715030c12050601 70
    0x102d009201c2c03000002030400e400302c0c1918055015080b40700046483d21349ca903007a40541c030036140010b2420710440d42010009034501143d50b06c0d50801600e041480d481d10750035200700740c0140030741648401c000c00a50650a18080b290030300b810900317060140e2003000900501c0098015810001828155030f071010f540d80040901c1c02030b50400a82c01da0309040c0260a4242c1140c084010070090000141d1850290041c14415015a0301c0b1004401035a42045018424110f8440456500348841000742d4007034402c146000700940ba00c03006ea8a4484002070945d140304d00e54054500c64026154002001e061900940c03003800d080c030303419600907402c2c248020140780d0f01020171185a1024008055030554955080c0d1b40a9603036080c24a03203440d40141c0c6da02c40c0c5000d06d82e0301a01049020200d0042d010100c40c580e100416102200351542c48031266500660818520380c0c10152082003907003e01c0030b030040611907604041c04450b0b40c40c031000d0400c20802410441407a00d0300e0005840d0b0f8820303162 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 589864451 1250 589863201 589863223
    0x22151b0f082a0301120501050a09051c020124030c0501140703031107020a03080702040c03051003020d110301021b0d0905010914030c030d0c020f06130b0f0c12091011060c0c 76
    0x209070f4403903035110543e06000b10102c2064410354070340030209540070365030b0042c480003542000c000d003001841103d02c1e0b02c41c0420310300980119580c1d16500080d541e104054000440c0d01c9a182c0a000c40c00d509050304440429401241841144541c1005c03505487c030980340b489416040c00615800000c3ea4000c41c0d104020000350f1014070301e00b01008000304000a0f2140500950f030030040b44007146419011258180d03280c281184894034100010314080a41c00d554038031070000c8030755040410000c6400d80c1c00090003030581b9150040d0b469000e100400015920300014505a80300611300b03000600551003038081c2e011540418210311046484c10001a0005c007406000c40e00b014178003003c000c1058256080803031050018a11001461034200c2c245d0b03040c11b580c2c0c0e500ca0191031070f110740c0e51442d41c881044a054108140001880260140700c0c0098210341a401581d5940780c2804215505d1000d00361103050218103e201c0d41e030348030300040541d41301c420b002e095540c4607111b20701c43c2d14002040103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 589865701 1250 589864451 589864531
    0x50703020a020a0608041a1005040e01060302031209100504210212060a02030912040305062a040602031201120f0209070c02060712080603030304050622151b0f08 71
    0x44002404c80e4441142031240d8002e1502e15101d158503454202100c034142c41d051038490030000148514941684050070044800c00000f999036941d90200303080c480b0445403450080b002180d141044d0900c1c0070400e10440042c64514170701801c1411448204622a41201d03203925500701c11401c5490381441d561043c0000e1040381c85c0c80c500080510041d600c11035101185014800c4d008807007a09403000d8030190b17a8004040d0103a90364003a582d5102c40e4101c6204940c0b02c0712804c0d40200c0f4082e082c024405001c480d03001e03580c1c0c3c1c9503200c5120240700040e80190703002000e6030002c02c007082510b0f09100d12180d0442e00a282034458110803a05000911406580640001200720403c060309050001e110550388680350b8583d101420036480e0302003181c000d071450300402c0005282c4011480480d1002040d4800062000d40a8441c2c944900c03101008182446c1c1d501d0254080d1046056104560202441e00803400da200b01030041a2040140018115040c61404841c4081d8064000d52074051220 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 589866951 1250 589865701 589865719
    0x13021210061b032106091a0f0411090904030f030b0d020321040812070614070815180702030d0605120d081b0a09090f020f040e09100501090b030f1c050703020a02 71
    0x1501c0d01c402810140f2800d988035107081e1021f1414455040c0d251340000b00201300007203000391002030001812009509078a024400c200b41d451654400442602913400780c2d680d0501c0061049010301202c0803121114400d0600b42907401c0140c0d00090b01d00c4802032084020414180c06a003a00d0050055030012803450080ca620101155400d0001d0b2001d140200418407002035020b5a403081e48409440000000d049580003030444400c400011303040d02009010320248101d080a130030b6802c001034442e01d00580002030098000f44140c010480940030440e20310100303000e2600c0e156540c51100000800b4024100001075031001040c1c410a40c0b2040c2e032a000340d45009a0000514040e0640541003c51703162445400156016100f5910070f45e8005040518103418192503d1034005d0042c841d2105210300440050200706600603d8000c0007011004101c0b002d1030810141808248280c0213455400f104840c010b106804070141c00030325080c00c08a070780d0001410100d092107c0c121000e900b15180c1c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 589868201 1250 589866951 589867007
    0x703030e15130302060a05060906061c050a090506241027060206012702090301331e030f0804030503030403020606270403051813021210061b03 63
    0x1003070b1068041c8079909482d5a41d94020181089030401d403030702a085000d81c4005409820703c20000e00c84102d00d03c2c1d4091050344080144400d49a0484901040c0c0351210159020040300300321040c0c00900c00781a9819a40901c40d410b00c4150a498800f803085402001142c4c0850040364060140f00c0c1c503616404984110741d1810389100524850900103210752000062002111424500181c0d001030421658085240e41d40e8042e400c0069201d0781550f0300d00700c0046900f0307002550804c06940009803507550b40d054081d440318004541c80b0100707601600d24642a0f4605404044003a641e00207183e080304109400c0c1a0640c2c0500d8000038014400041440140343c1c0010f0114860740d000c60f07008240e5040c00766010400f00d05c0380d1b0496008d030018804200000d000d24040d1242c1041040100102d1500100080b0240b294100e11111f10f940000c02c402201095125283e03c40d041c3c414ae00300d03152034018002c2c0030340c000d49441101841500d502c013041606c0b4040b403441c0602d400c3c140010300301503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 589869451 1250 589868201 589868221
    0xd0b060315010e0a060207060305180a030905150a08040b04050a080a0801080c100c1202010e120c060106050909070c0807081210050916180504110a090902040b0703030e15 75
    0x6072400901162507020074211a141030380b09941660f445601519069140001c00d502070480600705950000c805007840540c9a0204184001746001c2e55601e04614a072406101d00c110400011400e1240c007080082c1106400000300341c1c00540c800d8002903a517a682c06c09501745610070320300034041140040c100440a605c01500c6060b22403010550711805101410026880d50644150f80403509082e0100003180080c0c80300080c0380101e00021031043d10003003949003002190000454000b1010555240600b420851640500350605061740b40c9009000010300b1408010103600c01c1000304240b51040140a0080d03030030081d804800c050b200e503da4041c55074981011500c18418011f40c020004103440d19008080c000c111030b4401054640d0008000c4030079040b8403c500c0e18125014800040b2a19184512440d50000c420180e80302c411200008001149540c8000d00b07241c01488140280b403064011668050307814100041c12502030b142440c10258070390710340c861040d421020002180d003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 589870701 1250 589869451 589869481
    0xd0509060c0f1212010605030618040303060803032e030809090901180b070206060d030f0e0607080424050901090b0d090c08071503141501020304080d0504032d02060d0b0603 76
    0x980811103084d6030701ca00c0100c0d01344c0012200d1950048040403a8046521210140c9030414040d15000c40c016488900d100e14541c000d80e6254490040c64210403114040d002004803444c0100d00c0e0f00106a140d034484404038065030888a1040c48030001103049094254840c20041d050007403210040d08041c1172000c4051011541e6002501941d4005041407810280c441592607040d2a40c15807541101c0048803a8501080c44c5600f08000f0444000403906043c0900001c2261410034040d4208811180f81004140c2c01024207024080c07003491510f0382c02c0345a0a0603a0050991540c0391480e0b01581d0002c0c0481c10070140c10000d080c14080b940341c03404940d9100780d80703450380b0210a800040001f2030442c1e04010a04040d140a000807035240d008002d289405490148116800c02e511280950f041428800900c000700d2800101041040040e500750400705140c1e035800365059282001c030141050018000a20814000544a5042401c1d600030b20b807101007c7c0405840b883c3c07599040070909 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 589871951 1250 589870701 589870717
    0x6020f0d0905070302040e150424051303021e060f0c09100201090302060714030615120106030c020c010c080306010c061b090e130c06030504020612040803180d0509060c0f12 76
    0x81c07c00448480035440060b0f9803108585036242c02d031055030340d42c88101c4200c102441081c14544070011991380c026040c0145030040c00c914040d43c004500c1890064a841c5484028081c09050111116200300c3e0218495900c0042c55030704030901e98030b01c1410004c500c1814443c03680311000560528449a0551044401c54865000c440b05038a6010b4250755418a6101c24a80724000700002152801c2038048081d444000b85078050804101002038404001e01b6041180000c0d928658903140b59410442036400c9103085c02d190300103101948030b80c8100d100041485042c000c1090382d5508000e8103500c0710481e420324292002001c1000d00004290504a200d000b400322003080c04662844451125118016841400c07042d40c2444d0910a1700a0007000300f00b643d00c0001070000303c0440842550440c40303203109213a002e60340d18048044181700d401d02090140035034054000401240d400400301c800115048800c51345459516101c1490000c4941c0148064021a18203e200b41d440002800c201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 589873201 1250 589871951 589871959
    0xa050406050601140a030902060706020c0d020c061c0c111b0406080c03060f10030503041205061501020d1809020a030e07140306070e03011b0503090106080a0f06020f0d0905070302 79
    0x207803118801144d01d0891000700c0425580d042089440480c020351000c2c0507d88050b00b80381c14403850f600d651040b038202400d125a26000001e046980c01c0e81841400780c00c000480d1103a082c100034038000f009001c030300c081100009650314140600c1a009081008a0700b07600411989202665289102501401c00c0c846008509003030b8003250030603012a009000c107101a00400240d5140f0f80240e0801c10050110210784503200d0b40400821018030041014101c98000d4201c4003407245442880c0030380041c04114800001d04c0813603080da0340407414090010280ca00844500100e0100000140c3e2980c4100d58907071000604218041e0160007405000030001c059030316495507074088075001c02a99070250340c140c101000044465003d040c441c0100c91340039000148180d0800424140380700b01c1844200030032804410040c44036024010340001e024454060b0044030041d076900c2903414010400140f0641d00811140500c080d24800d950b03015411501c00c1c070140703406040c510303129115400203a000f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 589874451 1250 589873201 589873211
    0x3130201171023090c031306020d02030618040b06060904021b0a0c0501020d0f0f030b030102120a05060d03020c06030403020a0512070308220609061b120c031b03150b030a050406 78
    0x118001c0302c09a10f403070001404110041e5201c0412403856407000b080c100300d4408112514021507040d202a000300a029440103035a07091000c100054030001ca4410714448541208110014102036200c03a00210142c5001d03481c2c0c1c045038000780c007078041c1520410300f024136100040c0401c0000660640241c1c02018031500d242d454a004a84552500300204085941e010200c001584200a00300f40c0700074501c1c0018614280d00c0c002400d83e4441c407100380c114881e220500030b0b5607420740300d025044102140c110034054601c0e900070303440381c11030040b140c8030b8440800046c1c10301d802806891202648481651700030700d648041c4400c0d617001580250000b03540c100004100b0320701c21040d50a28000f12025002d886016540c3c0d0380507186901040302c10f2604c0d4421a00c004040404014545d14151200f0003031070144601e5a048075a180140c4040500301001031240094a403080c030000c0001d440d0103d450010341c0140010242243c0c0194100d80b00042000102002903000794040c612401c02400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 589875701 1250 589874451 589874489
    0x9070210020d06210c2102040e0c030c04060f0e0c0405090c0307080604021e030925080c040b2101020712030b010e150a050a031107050106030209070302030c031302011710 75
    0x41300441100c8002d0000c000d0b05405c0c010250441c400b844886880e400042d04e01401e98049829030344161145070031603205106401caa0f01c0e0611a4211014003540c1c1044030903d400d48048a0301405c1c810f00698800801c04034102c840d580c0700303e4014203c00f600b642c8060070540e12035a49640201c0b54003001540e45004186c01d460310b4001c81d80002000c2083c0b0049c0e10011422028580c00542010340c87d10030078100c8a1404601c002903568444106081e40c400b03840e2855003800c10034000c0d100f501c2145008400031055030b0f1070f1035803100050340e081031031346013001d0310001402032003124006002003020f40101b56800b641754010300c118010a80e2410035031070b0b803c0d050100d80141c03408082d034003000a00c0050314051040d80501812021458082140c0ba820781e0902c8055000003c1584c0a9444140c20310a505024040f150007a480340b40851661800e4102c07c8007500024040a200d650041c06843c2513a00c0303941e5000d1301059400396150941444d00101c4140c00452184003001410824084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 589876951 1250 589875701 589875749
    0xb04151407020d0b0603010905010e011a121903050c06040c0612200f0403020904050a02461d1902160b1810200304030e09070210020d06 60
    0x200741c2940a4841031218034103580754403210400a051a40642d030301c0c10070354003045090150814054002c0c0c00010360500000c01070115030740f0b0030b908a0040d580001c002c4940080000c400800030001c08040441c10841e141c122034501c65000380042c144100d0003400140701d25078981300100d48054540114001d6004580015210014113080030304c100410760300240071294008019200b110241c1d90700c1c043c0c8035800103105034020f071026030f204d51100f030b6240114200b4010308044412110840891a40a4054008021100c1480c5910320358080c480041c4c02c1c004801c840042d00f01ca1103180742c10309240d0480da014480c121942000c481904005070280310140c4210340a01c2c0700904c513042e0b0540540c56400c007903203001d030502c0000b03030300d012031424100400d000150140800038400700d0854016100c0703e030b0810b054103240e0b13041c83d01001440002508450132103580d007400d45020003a45d6a0b03010503410040a19000160140002000c4840d00f800703030310400a40c0d03030401c2c1c1030400340e1401d5004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 589878201 1250 589876951 589876957
    0x100903050f030c1c1a010804060209030132040f140a0c0e1504110f0f16050a032709050406330b3901020d140f0f0106050f040b041514 59
    0x14603100c2d840001403031175030351144c43d11592050040101500c1e144030040031900716164000b094850000511400d080c0c80042e0500d03c6070003241c0c09056050382045e440d00501c1500c2040c000b060345002000c0c00c494400140302251455170000802d5074015603481030a2021b02003214085001203003800422458501407150040380b0015450507820450041d625207820b80c802c029400410780107022890941c03000c00ba140300c103107104101a1010134010328000d080840b004403c48407824011141034084040300201c501114000d5230049001c0e1118101240249103445030400e24160480300c0c25034241d200c41c0c0310318000381103840d04a00b041d611101ea440030f01030300301c403000c900342c5500c2c0e12512001d0401200303401c060f424020480a00c811148a401c90340802c1042d5500b80d140c078842c100c04411400ba0300e9011504818000d01031909909403104420f0502600302403004c089036000d00300300e101c400c0e00d002c0d0540410841e0780d1501ea40003050122100008000000e00391218100c00c02000000c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 589879451 1250 589878201 589878221
    0x1309141506060f07080409020a080f07080c071506030318080303090c220f0615030b0315100b07150b0a08120f0f030a0b090a09020102100903050f030c1c 67
    0x34204880d2104010031850703034801003a45680d04030501c8400c1c0071841e00c2c001040140181400142e0f1503401401c040e0000e03000400300d210143c2144200202d8a401a2020f03901c090004d01181d0380d11020300e880030214910720b0591911910b458408010150050070140d100c3c080700505e01d420729a0b500e40e040e030303030320003112654440e030010102c1d50006c0c2485c3d1040d8142c1035820500c0170101c1400d80c2207404460003c1e5080520780d40720b1504010300401d10504085030300e040e14041c170080000f2000301c0c0d5100b08190b10741e5032140c070120004641190349020800907143c0082c0080c0e88134058241962800c950181c00ea94880c68526005240d141074100c050850b0790a2000e85016400d003000c82c405500549011001390008111010b040d02ca440700071351080d103149000250307001241c0c0603c10343e00001400d400c03005141c450300601507030f000071300b0208103001c003000071840c080e02c4c0c5402c64950261a89001d0f0402001c028060400c4406000d8500400841c0341034500d81c481142c00000d507811810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 589880701 1250 589879451 589879483
    0x70e0307080a0210051c020310090b060304170409090f05150421090506030106020a050c04051009020306061908090d020c0904080306030a1e050613120815130914 71
    0xc014181166524072802013814694144600d540f112012550f40b10421b4281036400410880c000445800380f4000d450200300801868101601154144c071000d00701030584510010101c049044840454020b061f0035281800600c109140c80c5070701a01c40c84c8115000d0260b154032083d50340740c03a4070041c8240e4101406440840341200680000300d110542c070000c10020200220702511204004c40c0280350340e5004001c0003a45060050074010003100c0c1a20031400c000600200784228402d02094070303c1e2364001030303990302c030140054103d2140341014415480d00015400c41660491412403090148030140d500c4c2480158040303032516506064194040031030b1001c2404101c0400c00703154042806821030b55000380540781c484954812071594420180c0880740710003003040600082d0b0b04421a0400c0074060411950340780d140e214840320409c200f040c4200042c0d07182d104c051602842e2500a8401142500101d000354007070720007103406031070b18900c03030340f080d80501400541c00119044080d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 589881951 1250 589880701 589880713
    0x102091e060f0f04030605040c09050f0606030601050a03061203091a0405011b140601170c01090b09090402151c0b090403090512071a0310060c0b040b060a0b12070e030708 75
    0x210720b0040c141c00240c400c4186010130712001c40090440e200e4540143d00a24105528528140e40d00307065460061901104420b040302b4400d140d04c9032000c0d00d40000d001d09289844091006084004140031340c0302c05000d03110002c0301c900b4150047c0d54642034441c022055000013040491140c40781c4585d00c2802d0009003078005481000311701c440000c1001d84a0202c140e4014a03000030149050003c4c4c000c980d858003141803004205408010701c3d1207102b005e0130800300a91030926500c5d024066071588900400c1035600150855a030326159000c55030078650355903200c4031030b0700d01070319062a130075040b110041c6480b10002151614881c214400d40e416659032501da400c00b400d104100c0305040c1c090182e84100c01c00030500c95140e00880041481300e110140d143d241200c09010b1890040d4860405c3c0029002d0107404100d11015859110350455256029500d07440f01080101481d64002c0b00b00420105645201150410010b4003c11059940319040140c00040503103c00503440b5003829944030b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 589883201 1250 589881951 589881967
    0x11206020304080d051501031803020c210d020a0201081021170c0c040b01090308120c2502041d0a020d110d121e081f080d020102091e06 60
    0x1500110340c0b00740316250070390508400f04000c03c2900d20544001640c6100740701d100761a5603061142c0340d4140082440858104100d81b0081d49450801280b18011200d1207040f107245400c040703900b502c11540c0b8003114030701201c00704002e4845198110403400591214003164550360907100d0903090341c44011590184204180c101c1c21000c038460403c40d0070ba044900403c141d00c2c00340010304079501011020b810708100280c01c000450300d070f504016061050701502440814140c2c0241c03400040003400d214019103604501e0340042c0901c540c828031042c03003d40a407103504130307440300f10489510a42e02480b004404514403903841b24590070a907529030203442101c0261038072142d111000c60240080c400516a074034082542140f0f042c400ba1a962091181c60f9480f40c3c1c081c1195900019440d690500801606c500402c03507000506084e2440700c55100501101c1c1d40c04415000404404003212076a90164401a02070b4210184062094401c48510142074841c24004102070200138219450171000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 589884451 1250 589883201 589883213
    0x60e010b03130201020a0209190b0a24030b19090e0109210903080309010506010908060903192c13060503100c2a020405090a0c0323030f0903150112 65
    0x61542c2070341140700714058031006d0b840b01840b59020303410700d11045540c03000720800882900c00700030255008803900c1c1810010390031500c401908080c00c040403848100e504080482c054010080803590107424446d003d452002e03030013503d030f0898200b81001e20080c640715400c01d00321001c88201402c1101c401c950f010004807a5021403500440c42e090288185880b07441c0d010254100700e52089440c1c4d50b03903081c00415070b0095001001440001c1c024800c914149030955124040c02c80e0042181b180c44200401403400b0b40c1d2042d181d240e6207000748010040034501e00042c07400c152083c40c003501c030b00d03922b410a40a0f10b01031344e000d4400240081c01903e110520f480014038081070f8850800c01f4549006120b1001e80c12156100c101c0c030028000000d10a00410003181c4029025110740d07840203103048001091154540100c9804c844420854564a9070111224104841c040d05d980800591400019000300107080080005d408946240301e81d035030400309400c004e008940c080f140002c0c500c800111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 589885701 1250 589884451 589884481
    0x1170a0e01020d0204082b09030204020f0906030906041101052107020f0d02010e07060806030a031110140f0601020102040305031207030b0a0b0913060f0b030406021207050d060e010b03 81
    0xc03640005250000120701c0c4012604982c210301065005001111541d500126800d800300349807841c41d0315003040c0f40002810607005c1c2d00c4002d01132a0003107003080301405c950040d604021405801c079075072403510301030240d181c40b41200c0450b00b50b000040e501807503510a0054411724440c140e034000c00c0358600c56004a125000800440031840f401082e04d45540041c0007188044030781e60000b00e090800307108002c0c209080c1e41c010208108203081002910740d0b0000384440b08580500701940300840e40c01002d810001100b8054600a040242d12410700d45880c400510803444562510915113880f001282030344101e10000d01107a00c203001031240c13521401c010f20303000b11141c200041c3d20807030840420940c1d4116403141e091941d0100d0b041000d0700b004003520b032034411261810815a410300c42c06107910400d600802c001c000d4080001004c01c00d40f0b50440f00708100096010b2103629081e04014406e1b80701c030042d001e405040c410000307a49054074003080e05a860201d80a415071361401c00b6600084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 589886951 1250 589885701 589885721
    0x40e030a172a1b06040c060810050901080304050108060303191d0a0e071101110307030c0516050106051002060912070302030d0608060105040b03030403080702120a060c020a030e01170a 81
    0x1c0d502090844a222100302002ca1034650b42102a0f220300f4044464002041859900e40e40360b0400742c03c010010340485c0351142614900c0c1441840c0da2182200f401c04d0350f1050b0031154201e14a403001085200d00080980116002680c450940d5900c0505050303ca00440c51001050241c50200700100750190200018600309030005481d010600c0c0e0008a41d00c62552050483d000410b0602c41c8040c0c1c00310030281c441d00b00c40020301840f82400729803011880000c0c641001c0640d9500101c00c00ca2086045400c0301e02000c0b10051140d01c0d50911a0090100348102c034414140d540c0d50300300070350020404d144035203045409803146075031310b900d4001150b0011a0482c11800700300000c8281140307604c60710000e004218000c3c403e541c100710504c401c03140c003125280d21030760091004100280d074210403180160341c15180c0b02e030b841c400d00030854900100808010035082c20404001500b5500080b54102075010350b03121740315010040011340300114482c003080c140409910002d000110584c010080d42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 589888201 1250 589886951 589886971
    0xb0a020c03190804020103180201080c0d0207050109060c200c10140c160603060323010204120305030406050c030103120e0a33090f1e0f06030b040e030a17 68
    0x400b80b409641106080c00b42002c60700410601055507814841c000c822403800380080038800158001804005c402840a0301c09032001821001c80003042e0195440180d01200910841c081407034400c01034800166810002110052072282c80c00000260950113584a4043c00007014807a060194080801043d08240540000e00c80307400a1048000c103942400c1c4400380655410368003a01e000c1c407400343d2101c0708043c1488002d00200b5a10300b10920f55014106446c0c1c45602c20547c001e0190190742d009480c09000baa505c5014150414021407007684680810801c03135640b401040c40d180001c2c00050210b140e0000004d06c2203008031040c0254090040040c0c80c00e40c0c1e543c404e582e902d0280045143c0d1010456494070405241440d49c0e0346015071420800c019900b00707070024450101506c0348403c144018010500384811045680024000c0c2c0040b9580180c0c581c9005009041c2c00500c042c05580703081c2300d07891480008400e460000100340c3e111000004c2200d008250b00401a10f801d2078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 589889451 1250 589888201 589888207
    0xb04020909090a03030608030901120510090203040b0708011d0604020306182a0405010c0b0a0603080406362601050a05090f010c091203112d07030b0a020c03 69
    0x35079500c2051841020a00010495040b41d858003e056034090740c0844000d50041c481d16000e40c0e0040c502c00703070101c0c120340001529595005010340400d030546c000b031201803000044c04244030b509480503100b0062511188840c6e66203100d10131081e610030880034040701d129404511540380075001540c01810042c4040b070421079250600704c07002d2058840b4080196010b41da550182c15000340d081828010180c01400c02d4a0080040c00a520303445000b44074107a410001401c640440d44400065a040244c4980700c94807440080c1c24071035864070143c401c030222642c81c02c41c000482d440d41d41e20f01204031100c0d0910b1600c2c0c0c10b4407102d460b103404000301400b520b00c1800b004009114140c0304120700e00e000b0900342042000c4504048601040d01510703410046051511508075040c60201c0e500254200811012800c5c103ca6070907078580b180402d0702a01d04e121403406940440403901e452611800c59180c0e110101d034507a10609031000070456000b18002968200703159019140b1680c000c0d060701d103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 589890701 1250 589889451 589889467
    0xf15050a0f183909061d0603040f0b10050a150f051e070506010f050307080a030c02040f15030203070f2601020c03070b01241227032c130b0402 63
    0x1500c0c2d800540c40442d903148819040c1c3d1450344407101d0300044c8080d0403e0a01d6918414001d40200024035015001d80c070000089004c01c40c1c600706504859030000b01c24815414842c116503500303442031189901c0350740714000c04a0441e100301c00c1102c0a4a841d1207890700c07a1100e94050314141c001e402c81e40e00130000c441c1426400d00348000140701c1e9a114901418007503040050000e40d00485420003402503109400c140002000007545000c07294040c2003407004040c543c80018043c100e002040c0e0071113400c020540403000036150303914059038422001e4888a540740c0c500074058034554480c551840c0030f401c84203820081c810b591001180060300015242a00ba15240ca10b150320407402203500c11555401041054441075810300c125030300c03940aa01d0195010002032800c402140e42c882d0241e601c0c4013491403501d03400c1220134900380303d1602e24802c924070705000c0d041c1c0324428680003214401224015000082109008d00c02000a214290846144d1000360041c4640c00d00650015801c0000388 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 589891951 1250 589890701 589890761
    0xb04170403030e0a0b040e0f0a060b2b0e0d0e03010e06270c061803010b120a03021e0604030804060b0d060905010b1905130f15050a0f18 60
    0xc060750094440c810500d000d0418062185100d40c415009020144010b00c0364085c004145600140501c2d9a00c40342d840f03c0300100000d104a030301070782d81000c00140a6481c8505260725140e06d074440b0600141c1c8a05c404070340390680d10242d21758200340c1c02c541468480c080c098400d843d0501800b40000030b0044503000c0b002e19001c004d40c2c122101040f19002d400035040341c540d9040c20415103001401d00c8600715008190240290440180d032020403c81000741610700350300424420a004007185100f402a410051f01c40c200c2c0380c4140e0040c0078401c500c1c2001d0303040380607d82e190464140109100d54464400302c07074019025004a030f4039038480204000c00da540024000c5e8150003554006494682403401c0d0742150344c21083c46000d040c0410040c5505040d843c030010448409543d5404904268048a80107211912101e42007500d800f507140e8400c02540b920700203544040d0782100d29191940803c0e00000f80c036106900d68003584116800030300500750040e1400b000e01800414940c031400d0100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 589893201 1250 589891951 589891957
    0x8060c1b0d030603050d0f021504080d090c0911120115020319050301050907030c0905041104030507140a0b07081603110a1407230f0f0d06090201080c03060108040b0417 74
    0x18000030f031940f90900c10300c003050101c0e19085200d0f0400440f643d04500d006511b90003001c03050011007501000180501031140101c0e000741c0d6403010100700504440c60300e20ac02d45498020031406074130700720b4407c031444030400481d042c800c4210260151a0700e810320a28011841400080850100f481740e81103c02d490750f060000d06d682d03601c500d500d07036040c00180501010010640070415051134108050603802403847c5007520001c1e10081200700448038299094403555000030114070070905c00150740880740356011a00003045640c04040e42d9154950b0405008000c006072600c1802c0102c01d070b00050780040e0040c0d0901c42d0a0400e0070706000c9803103504069150400b565251840701415913004000e105000c0580704900884000e1014a5214080b283c4142c0d601800340d04403994148041d56800c2000005000003807807486050154074010f0041c06000d40d00700d000c0b40c1468081200d84500c842600e00c215410703541d661160b074540d150040700c04400b610a0f5981380040e00104403c0c40c3d00401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 589894451 1250 589893201 589893223
    0x123090109021c0605100c020402040f0909150912052217060622020f190f0215060f0609210a0515010b120711070e09100608060c1b 58
    0x5880c1c407030036080c2c0180c0c02c15882c042c0e0f8480c1d143c090180704507507441c1410440441c0c50b10742261198500c0c80414001c1c451034000890307040000100080d008403940000420512030084d50400845420a020030343e80c45290040550200801b007000700d900c96402740929503d021448080480c0b441241c0038145200d4101011341c120004002c0c3e075000c1c1c00c000040d00203a080d503007a41480300e40501c403d40c041d405050700040319000145510b0301c2c29004280c0e82560344090390800755690b2a50082c0c50b100740104d100016000305401103862011012030184500800f138148001355080e82d0810526074404a203950340000c40504c2e0310070f03030740f190020780942085c10300062201b26100d0a0403840c06c0000603031b210703e0281100051044015172025600d0000c2029020062900c49010a6541d8034044d07036004950310070120005038038124040000d0107100040b081c2d508086840300c0780d405a801c0360083c103140398021001700f03500741100001041e15050b50b80e00003411104d540c085604145200351 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 589895701 1250 589894451 589894469
    0x70e131e02031f0602030301091a09090c1e0a050402071e03110f01050402030a020405040c12052109010c150908030109060603050f0702151806190605010e0901230901 73
    0x403c0004804069042c4044030910020921507140c510000d5482c0b10500840142030380b07804029130045080e581040141e00c0007040001c0030302e00509283c0c1c1e901d8140401501c80c4001d02200402404942035540d0301c2140a4440303080b00d03007070200b80806503002840071501c07401480811210660992610304105200350740390b0903a03002194910b031400084000d60700748c0d40d140509010041c0c3c3c0010380012016410b4030041500e03032b01c509184011016036400200200303115003402e020810302013000e20fa030015051030011030111014824005001d14070740307075000c1071000d80503001241d011850300c040c0c0c082c0801c006c148400255511060f43d0404c0c1e00c000c82050312100c2c1803041c00e4040c000c10354482c5480c210102075140070710009540e4003020a201c40b0709500403010901c02544d0001241c5011000400c45000b810000c44150391240e401d611030711514a09500070485601c1450b80b03503500c0c940141503010a034240b8144503404030024525104c86c54040c0c4a010301038880800450003021000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 589896951 1250 589895701 589895707
    0xa11011406040f020418050603030c0d032712030519090819020a0308150d2003071a0a270b1309020702180a1113081005070e131e02 58
    0x70240820340d582c0000a000050061105201005100048a0f4146042100401c00e40c54100c0401e0840c0300b121780b05500c50048004005086406400c03601c10725400000c00e807050b00c0000b903030185c50490004014840c3c0f9050359030003143c910035082a60800170300525050345800c01c08500d011100d031460200d03a0000040b0f03a109910005001840540c030890016140c02196a0b40061188000410f2040c45c0004e251301c4040c1381e05e80d659a1a0704a6000c013003803203214501c542d1034904440c151031440c42841100d03000700c0ca00125400b100200410850072604240301c1c08070682e0398100384031030800d0b201e0030728103400140c0e9010f903403100041440c1c58001e075580b5169040090070b1981074111915590040041600513100c10201c000c9207031090320120700319141ca0800402810030b68050300454280801c92440c030140c100c020000f1244040c08844030340b161800d5801c09c0e1503084984501044201c0c14034916410700d195035000440466500065020580050583d041640110703c2d000580c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 589898201 1250 589896951 589896961
    0x140d0f0c17070608090303010f0621020307031a010f0f260a0516050c0a0f1505010e01061b02100f050d020310141c061a120d02010b0d170a110114 64
    0x441312907044a1128081c614540c10040b071041600901d214250800c809c0042c0340022444003580050104101d5a09540c0d0341442c2000801803c6504040580e00c910040b00c81080d40c06069039150b090705580354108a060341001c10345184040c050130f11a8504407081740d012840908248612a002d04000000c060500610002c00000e42c14011400e000d002c2002160b80c100000302c50707494540c4030080c52034003856031a10202504020300300381d01090914001040d42c450a00c120b5058030304030354400200c2c4108400480e00302c034843c1c50103904120318044d40418940705096a600c24180e03803c1080c5003500d0724488408907402100c900c0c08080c4004014000101901c5859950700380c21140081c58032811620f101d0280c04031600106815602c00f00d000c03004d080c00346051b1030201e00415283d400314840d4010f039154144085104015460940c00b44100e250a02d00394800a400c42e8031100170b20311290145543d5030240c10550b0900c06043d401705454182401032501981c169910030f9818100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589899451 1250 589898201 589898207
    0x6041416110607081f05030303180c03010b011b111201090204150303080f150a03030c0b0f010e07030207063b060c0906090a09150609140d0f0c170706 66
    0x2a00c0440701068120805100030b0f550302401840d002207140c000341c241c140711200d03a220303981420341c8050340602002c01040703401e5100341100402c0ca84604150780d80d008182c404c0500300c40c0005d5403640894855042440e00d01c0350707501d000c8111882290031020688400001854240050b50f001a0584d114000c010460806005503100300c807034262098101400c41d940900001c0008007038102604041c40010b041d9000c0710196030b822a0b010b0042c144d1541c40703050041c04140050001d562480041c800306140d40507024655040700c02c2040024403d450741c60048002e9071041070f0655003588c40d00c41c4803450124900502e140e84440022009040c0c0403201c7d4100341e801071600c01144c0d504200104510b840d0341500303c402610301242c519a544155000094100042e07800a901c0a8600940c0140040300c2c0404c200c155621904e0b070b240b1056540075800d4814141c0002150043c61943d195000140081d420300712a900c1060302c43c5074246c0301c4e010703070781003c000b455000340030b078003107074007041445d030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589900701 1250 589899451 589899467
    0x1d01151403150f0603011e02040905060909190f0b0a0c021b310c050424020a0204020f0d0e030316020a050601050907110f070f1707090506041416 64
    0x403040e009880c4016100312090140503004002c40304828600340084d40b90750302903100d07405400075100c0300e10314040014000310080d0440d00400c04403501c2c1c40f0101c0c0003440c04005040c4a07a070028000c02e5205a0900d0b4141005001001141c2c1c1d180c91682020000b9800000039219449200c00061251040ca81c000d140c000883c2d41d102034012441c50310380705610b030302c221081c07803460a80c0c03206490518160111140d5400c2a06842124600305140410550060080003210014151340f030ac111100d03041500c481003e0300700e14001d0780c0200342081c01400e094007e008a165a00881750500f107400b07003100b081e10b2032544032144036003000080100300c14140760300544810491004150f40c074015035600350360b80c1e030601440b8403403801c00c400140110702ca1816100590014010f5981c80031113040625901c4c9280d0103540722a02c40f00b007011604e54020100034818107104002040035a28110300130008043c040e00603a00283c44000c110701030003030004128060040940c155055200844004081c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589901951 1250 589900701 589900739
    0xe1b060726071e0204050903130905070c020301020d0f060f080601030b0903070206130303020706080c09091b0a0801050405060402041215180f05061f091d0115 70
    0x14024403a52010580c50041044008a0340003919041007010004006038021088000c2c5800d844200c2804483e80d41c26108040354400d660030700082e1140c09041e5142d01075000e40070342065401c60108040801d54110981080c440e00340650100c182d900480e00b660b000740c0c580c071962619100c14000d001e906100d044018040002d00d030940700d040400003078484104ac4800307403518031040e02040f2410710030300c01c80d42501c0c3d0003007080e80c0d80c03910a01003084403203142c070007a00503000c3c6c51030010741c0c00e0164460900c1003000e8000340380750607451010018800c1010300b6040c4411041c06003541d0016002c0c00600d0340c0341288e01d9044466143c2070401007910401003560703018a0051000b0845484c8400b6903980c016413100c00e1226055254407128000c01d400c0d01a008003017a1001d000061103000790341c210605006400f501d950b81d495041540500b5010302e05144901041d00c020000b601d008e51140320140c0684100500b01c1d14100c6055007543e80c00501e50300340c0e05004400b0002c2c0c8811503104000c035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589903201 1250 589901951 589901959
    0xa0f06110c09070c0206031f0f0608220b0711070b0d060519260d030f0b090f0105130f050f010f1203022107021e1003090506040201050703020708010e1b 67
    0x1e481e00e40c0c0001c101c500c0000b8006c1c0900804000b00d50000090264161121140000340c03004130380d250300340c40c0c6c0b00031184203060100300c201000c110010141c0010000c402d410003040c4075015183c0e078076000c86000013003c1c20b08200c000001080150001d06c03000c0010040165482c0d250500070341d02504440c1c03146d121505c0340101e11944420001005c14440031a40c901d11107003101021990300d89484803c0c40510f01007401054140c1c0302c144d4140d480082030401d0094200100c40c1c1036014000004000d5403e1140031540400400240c5001140310b521104a654081075100c0410f00b00700640f001916262280d9200d82c006110700b060b00b004031402130580c402c3d020034100386910007944400c5038a030904009808002c421140100080c00c9900880d03001d000e81030242003a40030310305120f20b81c640340b03031080442d0b0903600c142c5072081c050800d10755041009000141c64690054440c0d0340f00e039400310290701580c18001016070f0288525200510414090091000e213010300210700c2ca4428822442 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589904451 1250 589903201 589903219
    0x615080402030706140f0d020301091413081e041205191e0f20190e1503011d030903100c080610110106061e020105040201050304060b0a0f06110c 64
    0x5a42d00148000840d880750401989041c0e503074490350b403544103204500074000800940720722000c40c2030b0300450403500884820800c200d0f01544d04880c90b04207554041d00d0114903680c0f003011444010050100d500401d07d03901541c01d00750b0040000d0703001a4040940b50b01c01c9901003042c094280580d0004403014805d1403681d580d1076a60652082d0301c20046d40202a21440c131004210f2421512951144c0081c1c1c44810255104018180450b2100e4118003500c940ca5030242c1e8420320359104c0b8250362240c0b40b40102940c5411004640c0f4801c101d42e00c0e03040d9250044d0084503410810408c280042080266030342c1c02c4840b003030510740502042040031700781c03809180300d204a900107805508120200c0381101106000d8808032a038081e10002c18209500c1e004c400110709130000707018201c0344112100c1514460b1030300416800c0b504111000f0b40820420000280040c900b98084110171000610b140c05c5c1c41c1d02c8204140c2203500f03e401140100d5410b045224503424100300c1412903000131984084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589905701 1250 589904451 589904453
    0x51b01031806090201020309120f0f030f070204110d11031b041401050313060c020c0f1002030a12180321050601140703140f0909010b03010303090302211006150804 72
    0x804900008041c01169945403c5821a031090049811241c0d0080441109003500c0d03e0f404d071281d0380c9805c600158415103040004d0b1540110a0300c1c1caa4004104007410300341e8036000d1201618812402ca03102c1c2d4020001c1354a250000e200d072003030012081c1e0100c1d40342c1c9072444041407941c5503450f45c040d100c10180020000040d035209a2101844280f90040c1c0341c0d01d803d01c5a080d0401450001000d490070841c080c80c41e1540080d80d00d241520484011000076080743c10302c130841c1d2038400c4400040e0400c0000481c00360291a10300481c00c4e11000004e81041e0407020041080c66905c0c0840000c0e002d0164030b100941c0760f0b00c20721000c600a0004010604100c000a0030200610140c2c403030041c008900d003001d25004500d00d201c0c15241c03066080d41d4005d4008944042e5001a50303040c802c0c54444008074091280c58203030381c10f81e503041d15003045c03060031034003044900c0341a0784448203800354103400e241861209210340d1a0f1003550400100e03909040407140d040b00100000c0000c01c004c2c14500b040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589906951 1250 589905701 589905731
    0x3050109052e0b040906050a1a0108010305070e04031112030a050a051006081f080a0212070605031b0d14060f15190c020303041e0603090f0605070912051b0103 70
    0x3589110380200b00140003040e0002040140940d260040d2a0f20303c1d0400700300d40050160480c1d0400104890141207405000f8010b5130804401e0101826030b501c8402c061009058240b01181c100380a800c0c49018400c2c1807810034a006000c0030203008100003c010311a088205d4023807181c00c0741c8182c0c001d0050b46400d60240702c4682652150008001101c5d0114814103241c0d605210080180290800c20544429aa9a403850070800482c00365a00200000000c038000c20804260381d0150380303840c50343c0c80b01c0e41c040b02c03a0480d61403081503100c804c1250714a4140c49200756028038596456062480c40c0140403c904400840b01030360069562140308500e01c0d00100c11a850703a50002540078107900e815408030f42c07815800400070340510002902040c4694405c0c2c5a0340c1d20702561055181c0d0036210501181940d036032110050800128003c1d11300010010f4200543c8401603142030780b072660303690842140d00704003030358140d4140d088001d00e070040e44d080280c01c1311020003e080900100d40782d15103103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589908201 1250 589906951 589907023
    0x5030a0204090602040b07030302180907230f160c08070614180a1215060f0e090f011a0114090604031b120308011707050102060c0c0102040f0305010905 67
    0x1e225507a5035448104001c010303419180506000c0c85032070340b500340924020b03000750310010108011000c02c0310400501c1c07520740380c45403041c01641c0c0c2d1101e4440a4810045840301d19129885030140180700045144041101514001e512500b081c01085101e040039206041c0036002080300b03030464402880b182c1c0c4c100d103454060819410300241c3e0b40504002c40c0d48900d041c49007040d8440014200001e01c1c0e424615801d0b001da000e011100c28a5a06103e09012161207203d40f4007027506955003002081d0102700c2181e40040c0c0c800940e8107010309807440b1800c491680c40c40750180340341113076030712229644a900c011208040c601001d24003200c03140051480c1c0114403004000c41c1c402c1032a01c14142c02c0644403001003025042c4c45001da9010718003e81405024080c25040b02040b201102400c0da001481e80c040b00d1045c4c014042c1a182c00380c840c40940d00c00e4039806080d6400b0800000d100c0d1508251328000d60155000050766131040c50700c50b00b0030f070700c2c0011100410070105460354a101070480c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589909451 1250 589908201 589908203
    0x6040506060d020f0406030506010303120e0d052109060106120209091501050c0a0b0f070507020906090603010b06070c15020304060f03020304030306051801050a0501031503111513050f0a05030a 85
    0x4030400320105100044c0102070b45503900d6085814240c0020401c0b0002a500303050700c0c400c0e00c94803840302e040f0b0b9100d000c850034a07240b160326a11107514a035846020b03200a02d00240046000700b009075140100110b0b111040d10b8074920b44d0702ca80c004200340744d40440070000c0c0105402080d071a01480c200042c03030b100f6001e00f41010501c0900851209a07004004598003c1c50a00030340b2210380c840c6c10239100c007130b0044448414a41d039400000301c02d64416412140300b6903006019000da500c46c2001e00441d118001c2c41290159600c40c1c08005a5550300c018241c054440d03e0903c170700d1801d01c1076904400d4140c0005000350f50062005200c81c81c0c200c07411800321380307803480d0050700c0c2d903031340c0c10201c3c01381642e94001078205245000c9203443c01c18071a0018103840c0c05992802e0b0b0150fa6200440448070549118841c8040804c01800022030b114810311404000414801d08403c4126591110340e01001142d00c02580741c03007040020b4101a076400c98601c00c11642e0041d01c52800010035201c3c5c00480d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589910701 1250 589909451 589909459
    0x80907030b0105060c1c020601031a0603031b030904020408031305010903020108040303050403020c0406140a06050a200a02150c0d1b060f09060c020f010f0204030503040e0c0702040504030906110604050606 90
    0x60a500c5005c810480c541201000c0c0713002100e1052060350203503c4a80078081601c1d840d40c0c45941650b45e18803000d032035001d0326018004525001e00c0304445400b48110842031405070000700098400c50360350b400500050410b040185645944071440e018180700550300c40d905020075510108007503030300004003982c090b4040c00d0104803665545000c9003071442c91300c19664400e14021000ca480746d24020407140805003070b41d82007440e42c1c94204c15a880c0c01583d0342400020031215910b05046410300940d5141c1c1070903012103000700c3c1907500242d000200c0d090780045648011402c03807400002001710745504401c5082c500401d900481580a04001103200680419158502006203140300d50200d040c45412000800c4096181403009440c0c41184442248540c249030961010038114401c4030200c9610000861400e4504100301a022500a1102c0d1206d0014031003000561181c2c002d03684124031a5640c2c1803140e0800c2000747c0f803490095001c01150307002c0e03810040001e000103030098001c074040b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589911951 1250 589910701 589910707
    0x141818130b0712110a0f030b0604060e0105040b040b070b0c040302010210020a1b050322151b08070f02010f030c020606120703062903031801121d060106080907030b010506 75
    0x4a01a40c0c0c1c0c5001c50b40070f40b0600e1801c052540d400c00000d014011481d8259681400030800c03020840603034010201140e8400e9040100b00440c41c01014149242c031018140313542049c1c0d032228000c03d142c120b0f90101011200002c0e1407030030444482c042c183e110200c054558146811500000e41da40c1295489002041c0d00058100f60700d40205a880c1003001d0110540005111030b140081e10b03500b0118607216202401c1e03807022015184408001c042d1050b030603c4601e00c0407010011140c003000860407030700140d00e00728000d0201e1090401800d0040c0107214042d02200741d803000410700c040407030710203040600c0c00706003412150b80814201e4010b142250118a1000f0070500300b414a6003642c00248018905081c0304010002d981d8904041c00e14142c003d0f460210540900da00c3c3e200c0d5038101c9074024241c0041080a6000d114444064851750400007043c0f0110900000210045401d4464a0380008010498903500810703203544504c0000c040e021092035503440d0304455006000d4984038140c08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589913201 1250 589911951 589911961
    0x50d170f130204091202062409040c08061501090603090b061203040b12010905060319170702060d05090105060625110405100608011e060c03141818130b 67
    0x1440e5421040b50018020050038a80d0300d001425105007840c40c3c000740c0200700004801c1c1c5d10346413038107444044540100252202d11810080140b00c001d004840d080701c260b82c0844d80000c2005920b104940c0e0021401008981d81c00240c10188540c2c0282c2c00c00d030501c12140001081e81c1c1000d03070041000d80d4041c078500c101800480c1907001e50f802502d00418007041389500c0980d1064028125440303407504104544a0b00c2c240354807403030407000d25103c040d550140f030000240c1001020442da000d4101d850305042c81a40002c0b400e902c00c41c072402d0000d03218800d00c110312100b81306068010741f0803110503103050101210062021000603a10260f1803a4005410a00441c001c82c000880c100900800c81450400440c1c080072646015050018801e0030020540e07a520300c0078502c0c0c664803186010211460818200c0c1c584000f14001c030100310018404c07680c40c130f41c0c080290825102030403860040e12001c000340300c9000d01081a407041007600e03c082c40380c481072948400000b86c0d006044142d1aa4503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589914451 1250 589913201 589913221
    0x30f0b0f010c0f02060f072f01180b032805040314071109181b011706031e01060501020d14040b13080303041203050f0405120a09081009050d170f 64
    0x3c400083e4028100044410443d00711b5402051018450b1903142c049250800c400410078440100b0501500300c064203c1d0843e41c000c2c0368038245140c4550841348aa9168803041c1c41541055039100c0111341c2c2c42451805101004c0a2240c10343c0400d1003c0000d45059180240001c004081c41d0044401c009166014004103009100850f00007400d5500c61742054280a420080039500c420300f140034401040f5402c10b003109200160040503501c02c107a0080d0040300110301e03a03029150a5252085055100400d4540c000c00c0400380440360000036130130700c0d2a00190811503000007820030800e130600c90400b40c440b034006413000d0300d0070512103c0c1c80d5055500d0901511040c1d400010151001000f00003c00400745000c04018075155014006601c1c1c002140030310341c1043e5401802d0350000101881d0f02407002d8090142071070649010312010395a60b04041c20b009680365010402da80b210035405c2403240c10084054950b11034500684030f003d1032941c42e00101c4003c0c02440020116102146803143c0e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589915701 1250 589914451 589914473
    0x60e01092603031503010c0216052b0605060111071206020307031104030605040218060904154512080a0b040c05030403121e1104030b01030c06030f0b0f010c 69
    0x206040c1240da40e818490f41c0c68465800340e8683d45d10039800c00c143d03001250b01c0803030115405d104641c0b42c580818240030030014828000010810500e41031000041c01000e1182500000d0340190703000140381c100280014404d1807415841c0da025402501c0401544104283c2110308a0f00305100503103a40300c0c1d0070700f1809001e080303e14161200d03001c1004810b20460740d00c09801980708903130921004414100f03403038403034a0448003658003d0017180042c0120707081c1000310501c50461000000c10380c5403103a55962001d40c1d08248001c008101c1c100c06008c120401180c00243c0840440c3d415a80b12a03803a4401980d154140d5400c22842001241c8070400d2504a00e2400b0001441881440310b0311000401580049409500180106c200c60202078140d10450a4000c840b114001c41b030105030480f80003a195180009149076420030000003ca02005411360103503100d0325001040d14980500241030304c42541d50b81d010300f8078102d611303031065813900d504020034642070030260207201c00b900b49241a04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589916951 1250 589915701 589915769
    0x160b22080604080c1c0504050415051f080c160314130e1f080601272309030406080621010c020c04180f0605180f03070c060e0109 57
    0x1c801c800902040142c414054000c0d0ba80842c222000500b41e402c880c0d03450306580c0d90341008924100400e00c454180703504105802c01c1c29400510500765601c001c03503d0080120038661011804440c010101d6502c04040c0d600300b12200480c50174424141b400c6140d6405000c0c00070700740003008418800301905401034580a041e1486a0503109a45010206070080120b401c000b80081d541e042202e07183e2502e5403070080d00c0d1944001c00c2113a0900c507201c5c85441791480b00c03403003245400800941101d05070180950341148061441301925500b2800751048c24041c0c103a03e440d82051109120550b0f01c040c4070f60740483c040300c06e03c20b4800c100003085017000414000100d01e500704030b110807101d60006030310807041c401594204402a0000340d000b03264681248000c29114241000d4000700703d0940219070415001c505c0e03070700301807400d0781c41c5440d080060b612080b064001003000c0c02400641102c070350040c08103061000d0000d0b02800020b002040f01c1c000c0445108050b0304010701c10601a0420301300d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589918201 1250 589916951 589916953
    0x90507090f0203010603050c0a02060f060310020708070512070f0809010c050115060e01170c1b06041b05120618190503041a12071b0206030c030405160b2208 69
    0x2681c03071040800a58400d004200200b820b00022420480345003084411315000f981c09052644c540101118551201404c20395140c41002c400c2001c1c03203540c0c4000d042c42c80c4184000c540e81e2001d8986581411850105c01c0b000e40018441003021a600c084000e064030741c0310f079a25035141c10010060310454003040380a80598a0201c0101e02d40d864661200300f42c4084d900c6040c1020700b0320340119100e80092110312101d20310322002c80e08034080c880c0a48214504a9800d94548030001100382c5805003c4405440d181082020491a8241481088003500c4180c92002c0c1180404564990350f20740900000303000110f404902c0300b00c850a12081511201c8140c425085d043d440c103107503649030018040d680301e00003007101400300c1e200300c403049901343c0d0b07115000308149a035003610507078007008002c401d900150074008800c80141c2e00d950040d4840c1072101800c1d40c89007001d0624600d007541400c8080200120002c060007449060819a4401a0903080030031010819251034901c05429030700243c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589919451 1250 589918201 589918211
    0x3100902070c092f0706060b1309050402180906071103070c180e010203070c110306063607120b03060403120e0f030f07021305010b0306090403200706121a0409050709 73
    0x406200c2402445d40b140221800e01c1410340710045a03500c0e04c00d05407102d801400000b010406070005400c1280c1c054001001e0b201d03802c40502e484540150101d40d00200d5411003001c00141035040080300003841802c80055003032014135a28000b1140040c069041c102c100600e0001d0500d0b0b198200c0500c00b1403020080d03480b030078030400140c40c003150b04a0484d0800d0310050000701d54180000d402e84103810007099962404005005440ca0755011070308000d540080324002480f84918802d200d0064000382c1d2031f08070510360007208404459140c00800c0c860340081d0140000309901c01500c051610003100c000a13103002d101002480c0c1381900c0c034114801d000c0841d540300c901c0030107000f50004a000707036160402c4c00000050003003210000d0064035405401440800c000341000c00f59554040c1c82030601c0038540301d54151211016402d6940b450003648907420501c4480d43c410040882004d07d80d005000c10a080190b520301402d8079608580510f0340c0d0f040400900400f001030600402032013504001e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589920701 1250 589919451 589919531
    0x2030a050d030b0d021509010c0804030b070e0301020c21040e04050303010f0803040b0d090303020d0504051c0e0a09020f070213051b0c100903020f1203100902070c09 73
    0x51101c1c0201c4403200824681084080d00d401c0c40684a001c0550041c030340e480000081e54030421070340060300990b0403c0b540714507000000d61440018409940540c0981c2c2d014030300305070010a07080841d810140645d0040c0441150f0407030000311070190244403c1148102c000e42d0a000d01c0314000c9030f100d00900f0350700c1c03404d120074001c001c8010740c1030761241e841101c103c986400c071065483c41070384503001310000100308076540f54489a00c1701d07020720b12a10700507160881b840385c0d000c243e80098505440a400c03070303148400510001d04219104402a050600d8105240e100003948102d2510520b1840c40d0001040344000384031000722803115074020444414044120304003001004100c2d0251840110381c00d0015901c0b003000c003940c481c46ea80750300410001c481410000e01078142820210158480c1c5030f80d04a941605201c0c192070680074601c402e4503841d01300d1004002400c02c7d0321800c4082e104002000203c0e01105013181030341c42c0d04c4401305052400e0f01c080743e06a04140e00c107d164001c0c00718400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589921951 1250 589920701 589920703
    0x1403070b0f12090c060a030e0f0109082b09060b0907080603120306030a120809160b040315060305030f0901170f0c0a020709020a1223010504180501021b070611070b031302030a05 78
    0x115036404600b089803032742440c1c50305c504d0032148400c5c1d024181c06400d000d24818100948148007a103504208004502001c0c6810301003035501c5000c0484003642c0701c003911607690400101c05075002c200361034407842d64140000865100c002a1490703030b8528000000254098034100714003c40c3c940d102d0642c0380140e0784a0f4008060401c1a102c101141c091030181101540403500d000040e1034420301414a000d1440e40c03030304506115480450001c0b900c50800001091060001c1d0500c1c56154100d942e40e038400e04001840b41c0c03080c206c3da120882c070601c28461215804010103030300c5200b0141842da80c21a4141c1a464800f0643c48128482c0c0002611000c15500c4115110082d50048003803240300307401e0b1426804100c0d0701d20903603880c0c1c40b1540104528607064110441c03050200b051402c4100b81038071003a080e80e100280482e03084800040c070000b070b12010001e9070020312a83c90701d040480c0003801c5250700c410551103501c4120b02e011010481000480c0c40c200e42e101d9004003200e81d0350307141d4503142d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589923201 1250 589921951 589921961
    0x6030e01091e1401020712110a05060103050c010324032a031505010806090a03050f090a120b1003050a02010f0e0603070807020606121903020c06041403070b0f12090c060a03 76
    0x21514084080d983e00300c2c00405009503504240e119001000020031801c0c11514018660594202d0348038520200d00819820704c03c480c080c50103078024000040080002600b55031001d4906c10400c02c11a0000c0c00c1400500070003015294040d0017000380b415520b06010b008000110f5111040e51580c000104210030100700b4070182c000c4a90500c01a1707070f100396441d1a540201c1e0b40c410707640c101210001c00a0301c900020040b031003070014610b041c07582c400042240c210741038000304100c0b10003001c4841488140c02d0f215500c051500740a041090070f584c1c0d01601e900c201c540c02418802900205400303a80540796a01c8400c1000d0501030300e0745000c2d1002003502d035003591040d025024103408103101d030402035051840c1c01c0d81b102c001c000c10900000800001c1c981e001c170680071030081903410307100c55840600800007418008140c128071309a8034100b40c2403041d50307848494004810040004000425030a680d40c0d200122000802136031507840f203909180003801e049510142c002050840c00350180c1c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589924451 1250 589923201 589923203
    0x90f06030c0322021c02190e150406060c0602250f02010f0e0a1e080706090602010f021e090406051c1709061c020c0d120c0e0a06030e01091e 62
    0x40314088030b181c000700020f6114464400780d080a100a00550480250030790104268070150400340c84055441103d803100e44950007100b41c0e142c0490501281c050307071285010240700c2c05c640c02c0104603c3c000c40a0400111b0550051120f500071940304001e103a20004402040c680b41c0d210b902d0003140340742448002c054440100e000c591403000c03042c0158031407110081c6100c00503140104460414003800e40200d00118003040b000702e02c4501042c954010300540005040070b40b140c000c00344c14150040e003511000019455010b2052014010001d02c0d00a5040b0503a40f548e8015581c4603900040303805080c0390303040180c00c49441c0500c2115401c4a107003118202d802100c08084070110301d42e040c5042e120302404103038080001c1c00b40c00c0d5042c4045134289480800d40d20018502280100c03081e05103200204908086801d004a074001c3c40d80d54024400c1e0301d070040c81d0041450b180c504c0001d4021109000c0c8504041e603c003101c10b24103201350b011034140c58100400e0740180442003400508000322500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589925701 1250 589924451 589924471
    0x40c030f050a0c090b0f1b031308060c040902090d02030a080408010c0809250e040303090c090e1e070e1f060f02030412020607060905010b090c04031106090f06030c03 73
    0x103140b808580c85100842c42c001e40d5403991036803901da110300440d04200141440002c04002035407088855080104440b80310202442c0c8880028030346041c01d0402d640901116049481005266407401d021101642c1c3c400000680f24840360010071500307109080300a4261144619040600c4860000b900031501010000c2c03100e07104020703003142d2420085d900b488059010082e00b104800011b600007002a110311908441c00d65219039070804001d041d5070650219980c0d44400c4248808550841c0c00340c040c0301c00600026001780300304c81c3c0d6050502c41c0005c032046103042040104509124030401401c0c06241000d103414031040305968051040d1554040040c03030000061311500503d003445660103680c024500342031500c0d0103010344000402c000caa20140400500d03000418038886c505401d4050000000c4040420307080c0080014040c040f42ca100740140700c20030001e51140b0944047e904140da40320345402c01d20000c40c14261021440c0e55010101000304410070034523034080d52040107102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589926951 1250 589925701 589925711
    0xf01060510210e0a0f020a0e0c0307080703020f0a02030408010b030610092d09050c09060d03270b0309060c071707020102120301060c0b0610021e030702040c030f 71
    0x301003004900d1240544804034402011030280345164620616200303201c40008100c1c014049290b50401d1001982280d49528500703d000546c28000064405030800204040c40c500781381609c0040c0c1d0100601c96020802c0d0341c00045d900510a0301030350740d034034120040c0b25207644002030069180c2e0400d0007030382d02c0c562a29890042c01d14000a90314015800c60044800641c01c0400b500c02034058220515541d114504d140c004629078800030190000f003004c00050704010520b0450709201070056001e1050b50340c0424050682d0b07819014080a541c14102074440014011000074800c4980b000c0b10082181c4803000a07507400c402000303501c10b05242c070640703a050782c0341c1c2c4042206018010000d132043c2801c0d001f40c2e00c4044c8100050420380e00500444810107080da40d1050140e109821503000100e6403100c2c0c3c070410140d0f10a842d0001401c4072103080400b48440000c1d50380360801c1000c1d140362955010700d034409c08180102c2d0780c180d401500a0148200f08203003e40a0070702c2d5000c4000d00c500d44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589928057 1106 589926951 589926959
    0x120c03030a0908010e060f06060912070603021209061b071104050903090307120218040f060501030b0613020a080a110c0f0105010501170f07210c020f0106 68
    0x1a628242d01500b0300350705a083da000030024401641c4000f081c0900d400c40d40c00242e51180c0183c841e540c0b94440103000941200000030703405003a0083c0c050100d00c5a505030010440001ca2400c20700d59500c900da0707004c0d5988000c82e40904c00d41c50030102c2170042e00400c4000c2c511039000345a81c07a00300701001e0020701107541c00c0d203038410650300c00501045141420f203d410300910540c588040c20f40f4180d00030441403060314009403c900c62072800a0100412024215070790354100e01e08000540e100d00d000303c45600107a070040e00c21064004030000c445842d008407142860342e907442c10130342c0e00c507400c0b0030004d071a00d25034101c48454140030329510740c141082608103080d6000700200392949400000f400c0d19010103d0140c0303050320b4104200855503c2004183c10142c4e078030b4024022802c9181c950180070001c0c203060006420980485041540000e04094031844c14008000040c0d403 = true := by decide +kernel

theorem cover : BRFrame.Cov 589748201 589928057 := by
  have h0 := BRFrame.cov_init 589748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589748201 ≤ n) (h2 : n < 589928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
