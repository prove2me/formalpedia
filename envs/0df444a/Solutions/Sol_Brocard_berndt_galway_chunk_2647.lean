-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2647
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:50.85298+00:00
-- url     : https://prove2.me/submissions/783e5900-6c97-47e0-980b-a9f861605747

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475899280 ≤ n < 476079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475900530 1250 475899280 475899293
    0x9090b040207050a02011101020f04060305040204111306031e0f0504050c1c030819091b092714100605030601050a12141f051519061116030609 63
    0x44016203010314010040003020440000d40d40340256420319190040740d20900e2542e009014106980e0034456002400040b030541c1a04090b0095008036810014180741450412540c8100c500d0b20703803032009100303080280b01c2c0aa4020109501580001000e1020490045081311002d17090101c4581d130b280709210600208002d0001854000d6854040070b043d01401144002400d01008041000301c10000d01080700702c0c0403e48100d1895403041c4080815441c00c2407001c0d40c0d070341e107520f0762048203500000c40c9882c2d030148291840c14064420384419086c0c0030000300310350b603c40c1650084003050750000c02ca42d080288490300320032030100140940c02c003410903017418010703440140304120091050054402c1700c528019401e90220321080a0003035030100d203041c500d40c064038955441211045e4030f044405900a20311500020704a0b190324031094080200d4205641d2580803020030f070801c10703c035403801500160f07107a556040071a040b100e403152a0300049800c94000f10b41042c3c40700080004c04c0758 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475901780 1250 475900530 475900541
    0x30c071a0403080c1312050c030d0201020a0f030b01030209090c1308010e03030703020a020f060c030403030533030102040b07080c0601121e08120a0e0c030c031b010314070909 77
    0x410210060303240c10a901c004010100107003503040d40140c005001108203040c1d00c094002041440e40d407504c2d002607030070030640300c0f0300c0c2d00036581c0a0b0042c4480b9042980c410f01c211100c248003034503210b040d1440d80c00201c000b8401c8405081c149542003105640360b81d80c8100052081c942607458a0380c60550540a000c40c0710f03141d00c002a1380c0c2c10302082d60980c2c0340c04403d4960080d014540141c1301c840c1e51104a281c041040485503c0740219010b0204a803581402144200e010b61410b01580d12410400ca0904501c1007880c4040f01c40068001139407a0300d00041488440014000741c2050b45407085603000d50702c10340c400c41b81044001900c070040b01090107a503004100014072084003402c6901c400c3c41d1020025900c2081c50100d1150004201040d0191001614000310800c813616181525400500b02144444194401c1149003945403800243c40d000c1c4000c007030040d2050300c14800c032802a1074000600130b81070648400e155103481210780c550500c00d4445070342d823159262070611003804886 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475903030 1250 475901780 475901813
    0xc01020705010c0b10030b04050102131202100807090b04060c021c03200a08270603060d03050d0605060712030f020301050a0312180909050c040504050c190b030c07 72
    0x400c450300401a9a070024200260140c000340c100c2c1540c2d803841c0300c040403440280c00040c00c00482000f03000512105601410303040d803070004050718a035102c00c0c0c01038680059100081d8001c122000054490740704030f11041d0405d1481c202000055200c460306d4100d0b8005030008000918099040c005500d800d0904200382d0080140602010509480c01007000d071125862040c801c103000c6c4070812081d000c10042c400240c009010035220b00015071004500c0101000600101a0100c0ea200042c1b41002c00c41e80210b40043c400300341c00326a80e4082d609a003089014070340a03070380c40d03200283e6502c03060700800a952080c00250012645207030003604a4030195071040d001c51044c80144802d8882140d2403040d40c0d0044000140704911f00002c07503000311115030f4420240b59100000524565940005207240d1058064400241c0d44505110464400b202d000e0300c0741d0701104c0d86500c0ba040500200d000042000b801c803440c1030300c420100c2110341c8180c850082850000610f0f1060081040c100c59006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475904280 1250 475903030 475903033
    0x9011e0f0b07150615180807170f01050601020303060d03030b1809070b0327030d060e010f120507050907171e060d0b010603020f040906030803040b06100c03050f0c0114090c0102 78
    0x40c2d041407940035800403000980810700011000c0381030740c1c00d036121b540c50007007031401c080340e041540300d24610680a1005a107000c081c4540a0340c1c40d41c1d01300c1030040d24800c107010b034000d50540d5038103002c011503000089802da09041e03888800079110303203504031240c4800c510154200c2040c10f140300e0191810455074041c1040c1b032030510901c02d19840004401c04da41d800c011602c10584500130300681148a0285010062031503d08002a038140070385940c1d040304c4074103152003241e0390b4402140814500402004146030800d00303085c41700e80380103481140c01065030b143c40355030349440c58184500000250b8405c6880009402005428084080e074644e100d00c003543c4180c0c2e8151583c0d00c40b07000b203806016002c145500403036101d002d102c0c0e060659000b440e039102c0074010955079080c40c90042e8402e03541642d91404d41800030740b05080c001c460700300c11000342c0c2c0c0c0d02c0400b03c6952400c0b00e0355000005201c00f810410801005039030780074014207440440b034800c01c079502d09045c0e42403803604e90202d042c3e40c1907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475905530 1250 475904280 475904291
    0xa170102070c0e040c0e041104052406090a0513020405100e0f100804060506030f1519050108030703050705010207141509060c1b01090b0c1c05040209011e0f0b0715 72
    0xd000001204226130942d0500145600d6501d03000710b20748e04a01c0001c0c2c001c0d01c0c1100308481c11440f110401c00c800d1200c2c3d0101110400c02c0240145803003070051841d00b2001c0e40f21b0801090901030071f88075a10f100c10f6401801e154071140055400d16203070450400080c074003180164140b80c0a1004550302d0000c80e00310400b99a6002c0141005c10f0003800030700504d995100007445604c050010034208140c04c0181c03443c0f5001300590550540c400d40b4103420401c81050f816954107190b12441e4140c8a140c40154242111650100c5195000c40b02c2160555000c3c00520001502510ba00802d410b680c800f0705012007540c85c0780350142e41c0042c40d244c07407a403007401840551b0210344121951100042c0c1418400401d072908a4058221201e0040480040c502005201800580940788818604002c2d1742c051881c02118801d52700142c4010307601c04104401044415205900c00c0e1505c80c0a440012103e95035150410f0044e515070301011082c100020484c040001d042c1d060542468801001c020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475906780 1250 475905530 475905533
    0xb0c03070e090601020a05070b1206040501050d0b040623190b091503070b040b0a0f02210307120906060801110c0606010e0307080607030b010314040512090a170102070c0e04 76
    0xc0c510074072048601800d1140c0105050ba4400d0040d54801a0000210b030b40c0c440d946d230104440d0340d01c0071494806410301e1001141c42450039002d5241280d8005001540c018000d80310240001c1001d0306c1101d00701d68540c41c2c500c0f02081d0f21040c44118060800501840c0741106140390100c42c2c25000d580d041c0e160020888840e514410210b0704403104040c0d4288288181000ca854009182c100860f130001c003180c00504920428020a5110741d207035101c503111049030600742ea40e4941146414480300300304410340040011140955885801407611507043c0440c16031a0040300d40c000b00556003039803204018419070200340030f506a2520705c41e81c0c0700d00c5e00303005002054544501500342810403082d00c04609141c1c0d0200046009464a001500c000c5d0401d00000b030000c1100c0c441c0c09010905000200d0728a904000f010752065811001a049045d49010001e0f0f81f23500c48102c456000e100c941d000324040c90760320005450451040b000680d66401e5081c2a9140102680002c0804021100300f00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475908030 1250 475906780 475906787
    0x8091c030603020f220c0c0f060c03060e01080604112205090105012304020903011103070908120a020c0d05030d0905102f0322240c09050d0c0503030a08040b0c0307 72
    0x400710a017190000890807040341c000c8032540294000501101104540718083c400954095019481e091314100b08140c4d07914a202301c180b1f000d2160440540000f400580407689840b03548113582c0780101303100d1f04002030010340b031403a1400c1d00c00307000139665800410821010034801e01e4090591441c90f8145011891000208100039010140c021900840c02000d9500d00b50015590810016030307a07526440e0420000304107e5441c420080e9902c510640c4d4026040410101c81ea5001585d01914103000400e050000e0b001c0407440448280c0720400228601111038410481268031a03000760103e80610102039040c0c0390501c44250f001c80e403403880c003980107400d000a0b40300303904904522a00d0782d49141d44180440c0d023101030044041c01160541d41001002039130300800103400301100001c040b0310010307001121507440c9081c0c080741c5018000c2c007451074401401086148a140710049054032140071a0030b603008851501d001c1200101440b08102e0243c1c0303055030104890104504600d002c0318000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475909280 1250 475908030 475908079
    0x4050609011b02041b0207060c0b04060b0f031b031e060f0411100903020102010e010b0306130204090501020d021308010b0a05040f0b120d110106050d0308091c030603020f 75
    0x1074103100c82100c4080300c00800c0c403031150720260000c01c1040f140a0404020315404104424070005001315440420b036203019140c02442c41e078020114070944e039507a681d40300080003420b01c415400841d1002da260196010410200c0040d4264100c03c5680c1d0349006040c98001807040174500b2841c400d411640d844d100065403644040c0c055000011078855041a224126a0041032908220000030b03a041d0550000031f1103080b20310030790003040381c02c4c40344107910300320303540d68010303c1c0c3c150007800109200b0f00f80c1080e400745040c00108001214100759889a0072a80091042d100b4641c0200d0150440309426466400600700c40b8001d028401a04000502e0441f460140c94404c650303d0360001e000c101c2c00d52020b880b080c1f000e00424481c4a003d0600e1341d45003148071030000002c00b0f09c0d0b040038008006000d490129030300074003011581410b659040e104800e004100803c0d0b4851040300700704880c408211403950f030000d900c0c009000760440c01809940d240c0310810500808180c0000d5801003100e002c41c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475910530 1250 475909280 475909297
    0x609090a020901110307080418090b0103231c080c0406020d080c0405091f0504020c0a0204020a1b03080403080708070f0e04200903070e010509040b09070f09020d11040506 75
    0x50b0341d400580d00580d0702e002568000e06482c400400c05908014000d4000e20550750b6007941c0304000c0050f24079040540ea20814018410341c5a44010030000c0e00e24121685403003102041c856024912221892803c00c240c1003440141e502031000e071000c02d4100044c0c58002000045151909042440203076a0350b5020f0070400030000e44030000b610f44a0483c05031005450020500d60341410411a10740100d600c003031040b640d002c0210000911031034540b0071035041c0607888000d0320349107440383c0070031000390481d40401050003040c5405151265002c0e483c028140d12984445206003090704004101c404000e08040c1808009410301a01a42000300000c1d00c4c1c1092826440c074100315804200a4982a95480c03850102541703120440780151000d80a000025800c82d440c65940742e40c510a000d400307109507600890014045404105040c4130623502c85c82c3d460440e010306c0e555051802e115091984180c600fa580440d800ca1075031104d0081c0640c080a0246060078541004005211403007101030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475911780 1250 475910530 475910551
    0xf0c0c0b04050a14010b041a0d08030a0b2101320702070308030a20190503180d0c05010b0a0501090603021b030a0e0a0f0f050d02060c0618010b060909 66
    0x790400804202c0c104000e5407102c03e200031144409191030182150781e404501c2903083c5a6146045441d05401000100d00205103000803000c0e510740c40703890341c0081d0842d40d07003e844004410081e02c94859848025480c2c46507404100c111812403400c450745221811104501d160091600303020080c0300c20707290007900c0381006540c2c84008040c2e00d8985a81d2004040ca40c001c410404404d100382c0c866068400d280070b1801041c4d00c00c43c0b004610740f0070203500384007951007072a020380d06d98400c40145034003460300c880c00c43c1108061040307241340102034110200040c103c1c91803103041200038040d0b05041c800945004909904040c0064245025800b07610304041c0e01080c00e008091110403002c0014450780c0981c1c1c0e5401134901c00a140425003031009000c0c00765000d000401c03540d001d201c0070494480940518030b45043c0003c0059120807000d043c0c1c0c3c000403d20020160040a0100c240103952000702040384d20300880900e070030340f010a00d11501c200b0040c020002543c5034880d8140d4041c20410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475913030 1250 475911780 475911803
    0x1703060f0906010e0d1209090207050303070e0a08250e04050a060f022203030f020f0606130b030d09030212030405060706020313080d0c08010f08190215120a0f0c0c 72
    0x40101c5403003030f080318100e501000c45d08648092100c0c0d0300414280840c150f4545886a0f21a0901d500764410090000d10b1a8003c10020381241d02c01d41ca100418a0300030203412180c1e540d100039524200c825204201200c4010070f2500c96055071061a038000c203480410341d10541f402c0c0e2074568031010300c440050302c880d8461801e01524820750341210541050000c11030902c01441c0c250707522013941400110040342d0240900c0d05002c1c00059440c4120240c180180f60643d03e8005101e4460082c100b40420b0740c0d2917200c1c113141c1e80ea090000804103440f0b903a030a1405483e500401c12030816206072251075410800c01403109881e2482160600b0781c001c2405a601d40b01d03070890911203444200080d166080103d008202d9501c80e401810b5942a6580c03044800e980f1164138003c41c92051007203114039404a00321503591b0300c400542c554038a00051014101c4140c2c1401951242e10034440905007000704404c100f105070f80d41c4a03107032222242803810030400c822200042c1040107280c3d0007811544590 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475914280 1250 475913030 475913041
    0x30f18100b130f0204140d0f1407030c08031c0606091a09030715030e060c030601080a1b0e03010f090327080a210c0309060e010201020d090f1703060f09 67
    0x40350300b00030b85107001004000618070214950000d40080c040c4008802e101d071034015880c607100b41000c0417550088065000b07001e503940c0f0760110702109c03c4544200c2c01090400004505212010801030400b0006150b0711441d1042d90b00d0711800c603c440492241c0b90a0080c480c1e142d00c02c070b00e041520418004060781d0300404c0300c601c869000340034032140e041c070032640041002145081c5806a01000383c034203005c1150143c0e1100d4070f8003001c440744011004140000b50042d031107004070320b030894002039000a00c2407500c4c0c428240924450244070200d000703010100700740d060034030942120b031001ca01e08004041c11540c0c018140008110490752107140300c5498009030302c10b086000000c102d601c08686d440c041e40d00e040610a0440416040010b0b11050454542805028a80601d1340c4c559150b01c846401c04000780d8a030800151070504565007408030400800075071107282050303401289a0301d6000b015141c122030384403400b032903900745c9031041c024040e00e031710f441007006201d40c3c08403072090b020341d1031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475915530 1250 475914280 475914289
    0x8190509040204060306061206030b1513110a020d0e0303040302150c03030a0603061d06071b080d0e06060118091e05040b0106030b0609010203041e1802030f18100b 72
    0x310503549501520001c2d00044940d050b9005a0440b10243c46080303c520a2400c5042214290301c03016006e2080030b0000707100e00c45100003003180b4a40c018030f00e08035030740350002d00c800b20303110300c91840d400e2840016520344140d01048608240d01072481c01c1800c60b84440e0100e6160701891100071b014207030003003544c0e040c2040c1700b00f61a407107a450b100b140e4491400311000340240c80c10344410b5441c1031a044204140794200c40052181600c1400100074640700c543c03048401062060084600c60110103007000040d900307100030841c074040214003160204108074407a041140c081c2081d41842344146000c2c000a4000e0010f0341150b42e20080001c1c50800c0b08080c0b502c14034400c040300ca01d545090300704400c21520b40f480a0503907102d594104010440700042c0b007032500c91060300320f000d41d2040c082042401e80d103240c0c2d6005070b03080300c004190455030703010042880003030752061880c01078000c800c114400107007e0006500213805400c032801201e40c80c0c00390380c80d002644e0b5046501e60b100c034206141500e0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475916780 1250 475915530 475915537
    0xe1506060c1603020a06080106021f02090d031808010c020a030f03110408030a030605060301051e0609061207170402010f0f021204080a0605010e25020a02091e090109081905 76
    0x2006030640d102c902e8611600741007810640012446210010f1700031540d18456030a10f81a19415002880d10040184408141c052801e1f0f44c1c1041d00c2e02004402c03420b458001460404500c070b6155201c1d201540c011441c4251025049a0481d0380f414050101d041c1d400a01450390755017605054841c0b08280304110090200c20303049030880140042d00150b0840000000c0082000301d030703801c0203c01d44031020400d0900c001e00c6910313441104e403604843e0740e0340300340e403080c617100001054640b6150144022410315081200b0801500d45c018080090381904011a4024000f0600c469403c40c6000da00107030000a89000300010442d00d00301e20980540200001080800d099115035195547c07501203950302c011030381e0100c981505110000400b041015100d50084102d03e00c0c01200030011110211500b1102d024001144900304030440903880b25500340380500c5c03480c828802c2c00d1114006181440c04003074003207010b513031500e6a08004111014280c0344904100c003800b426002211004664500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475918030 1250 475916780 475916797
    0xa0c0c050405180f060f06011d0301060f030b16050a03021b0f060907080303090705040e1608060115050a020c010e030703060f0b0108070518060f0d150611010e150606 73
    0x92401e818011012102100c48040486543c110b40200c00890035860315010182d40d03c060015010780814040c1d03020301d5192180001c90040070f951254032100290951700203038003a10269400903018000d00407440ca007544d0141d02c800030074444d022030030001032103032080c10110b80400d5804a1231440207001301204078103038000d040c200c494000d410100c6648900050320115210300c20034000180c1030724040140c3e8440c8070003c01038079110f03241c0030038007000e4007004410000300c0c0210403d4a502d00080e644920141c100c01d0020211036043c968182c0480005001220601806218010781c460b400100c3c2d9590301c600f071810801e4440340c140828030388070050300700400e020709002800010b000c0a60204444038403d81c1c4035990764a0b4517100365401d203d030041803880301c03084000c64101810680002d000124046c9007482c64021008410300441d004641070b00000d6180c000d080180e01e81c070513a85c41c280d8240300001c0000100e0746812541c5d409480440610204c52180001e42c0f03503542d0340544180303c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475919280 1250 475918030 475918039
    0x30911061908060111030702060a031103071d0a12122c0a06230a1b030c06050a050c1204020f1002060915270a080d021e0a050a0c0c05 59
    0x141499840191507050081900780001c20300c0c0001155580700700d10940055280c0310283d440d00049809202e9164850f9060030b060645400d0500081e4402e80011442102c5613600c0d2001d0850001840560041008070b252051580020512403410004002c07005d05522001000707007464403440946541501c54105040c200391206c0b010790020f036601040c010020111200d0700c1143d20f481d01681e8681f11300300300c0015058400792000412800d00010b000031040350816100a10704040ca81c40141c0200c00e04a0000d8810b02c03186040068034018150403030a81c81060001c2d1400c0e0110109034001c49240070100c6140c1400b007000e40d00d82100d080c41018029020106a0b081c00d00c0103903079190150380486280c4180600242d904180140c12802010781000803059108002c46610414901c4031016400c0d01800910302c0010b130024004004484440d0350142c1c4545c031100c8201c1038003051100000190100f04240072100303134040304941e0005101d0511540107a01400d280d01d001e03200d0340100307800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475920530 1250 475919280 475919287
    0x150611010e01050106261302060d0b0306043e061e040f060807020d0c0f110d030305102913030602040e041709010e13020c1b1f0c0303091106 62
    0x203184e80207119010100c4d407110301b0540e050b190415501c0b406030882c0c51204001d841c2c14128014a0704100505040502c1600410080d03000000641040b80c250340844d0141a035003911200302c216150810901c0c0124000080c0c0c0401441c44190002000301c070143c460000003ca00000b00b0860000d020701c40071400c4010f46071605c2e1070420f2080712290003a803012032004000036003e18800140f4000340c5415984081e4001c09554a1603441805020100c551203030b040507030141030700c0d00c1211280041c000e0303a001c2014240182e0601449010341c0101c0240c0c0c260040811800007034800f000c5200d0582c81000380e030b44440560501410f0850340000b4161400020000f0704984c00c19112400381d030040b014004c60f40b94080c8242d00600c81d045120707020440d40035884240d480c004c0c01c5140804c4400c078000d45003001e03141480e07080c40140040c0020091408601c40c03454104100c0580c0c0b00034400b00a403680801c040d00c090901101050001d04050b11409400204490940c05004107180604000e03107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475921780 1250 475920530 475920539
    0x270106090f0b09061509060706060b0706050a1503020a1514041409010f15120e070617090d05030a0c05070611120606040506070f05011d150a150611010e010501 70
    0x42c00100b4003561080040d03102045492420390401c580340c141c41d5407807074a410304402c00c1c0065034100034000c2e90719554400c00014072100800003840d0803489060002a43d00d8501821800c0f10a1502c3d40f02000c14000b90034001600c0d054106015503204140c0601d5a0f004240700b218402100201a0404800030800040c5040c50001886c003003641103d2403080380e80c031060b902d152100c2c0fa2150302d0340030b51038138001100140652520b00d510300c482d40000c10107540384c684062030458998001030010305110015005640740140d89600120742c1009000c000e444042c00520070700019004584403903985440d20a428000c00c222006580d0110040c048103000c890503141d0360b00040f40022888441500044061800c1d004490035540001c01540c1800441e0301d4080d07103002944d60465456680b2131512000c00c2071240c41e189042001310080001c440703800d00096030450b01400841c0840e080082840d003100541040f103041e03450078508009019100e00c4080d003d003000700a104c0d113035480c0c50001705 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475923030 1250 475921780 475921811
    0x31c15120323090405040c090e10140906071b120504091d3012160207140907050712090503010c08060a0605090a0806090c12010527010609 61
    0x3201600a894051118050500b000c44020000d401074100c4102003120a000b40782035808607070080d00a418078158640c4446010702190b16240025055600200b83c00e9545241ca0051028070400c40e07070000d9442c1842a40c80d80e481c180079041d0307401d01615503049000d010b070003801304002c80c2c3c1090000d0307903141c00c0c9900602158424000d09a502c1c0c10060341080d90049031085400200d0501c009208a40c0d9440c240c0e264550340c0e181290310018020346040d00c1d100310f4800340c00284500013600c4074504115804140d1001103100280941d00201380c200311304000a20104660001a5403068080d036841c00c1c101c4152080020007440d5000c0c8408503140c07560321081803000d8805c2900200000100d4a600381c1310408201c6d5501d1744580700e0b1005014042c441c00c06070902040190503100071503202d040070f6081c003804032901d180726800306a05d02c01c58501808240300329141c0d10020002420301c10151500e1440c04901828080c0d944c6038101e2801b40b09502c1000203004100c403c11568030340f80c071400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475924280 1250 475923030 475923059
    0x180b040b0403110313181e0c0206061c17070f05151f171204031104050c0703020d0e12010608100c0302041211060909070507050706050301050102031c15 67
    0x1a400640515020035240e00000308803108040115174030765820f46040d034a030f00c44c4044502d25959282d19048000e200b01c1010b5400201310090602c04110780107060303c02440c0002c0140075501c40c0d40c5005465010402050891101c99049040001030180b01c03405050340e8410741d000148103102402c084c0d0248080420b1466a01c080f442422400351103648090214112541501c214820351035010801d1400040105d400000d1110a032208000100a007040c81c0d04158030548510322b41701c0c581019460b280c801c50b82c0c424070003003201d4201070781a10b0096584130060004400d00c5524110028136a886400084200110304024003c103a2034011440c2c5525100c2d072052505406c00c040e05804500a0081e50152603030325400d96011841501d5140740056001151600708504010b5203c454546448082c415285074482076582d0906180691500202c3c3d4003100801006000504c21b903a40842129030b00008500443e4013518007a072010300a207030480e9015403400072203000040002216400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475925530 1250 475924280 475924283
    0x70f0c02011b21050903070504180507170610140f010915051b0312160507120309020f0306060906131d010c02060a06080a03140904050103050102190203130306180b040b04 75
    0x800d401c0101d41900c41e809405c1203039074180c11400302481142081e901070002c0001002e00e5100c1107040361907650401c044c0341c00170501903003000c000c0c0100b40300402c007141d00a50180103e100b00c61511803510301d105145117085102d480419501d2203540e00c42c82598000e0202c070958800c4450398120060031580c04490141d1550300b82e0589201c030408080300b612031080035403a8040c401e61f00c40016071054042074080006001090001c50040349403101203180220040e240000d4002042c010001410303a1108041c1c481d51142c801c00120b0b03202c00e4202500000280c800d8100580700c4404a8090803a40309500100f511903100829054030541022207420140c1d02919001e48a50703a0503400d81c0c5403401501c01b950702188001e000a0b20400c60010740c4c00121444600302801c0f10001000d4550030fa10995440e034021801c0c5070103510180b2010380c0c5800c640000c5160402202c1c500400d640f403844090440759540302c00b4038005c010030660004281c0d000040340c190b49001d2a00c1c41480e41c00b503c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475926780 1250 475925530 475925573
    0x18070e0601051207120c0f0e090121051c090302090a0504240b060f040e160903021302210406060602030c250506031306060512100e010e0f0a120305070f0c02011b 71
    0x3223480da9041446141e811385c0c2c01349585900815406600c03446011040d90200c1d010310815210182e05000c540d01d4400c507418075540c4101d450301c1c50040000708203018040d02d0200d4607110601c40040d06005c4c0481d8412a091601d0302d140c03071020900402000184140e0f5003001c000a928400104240014016108000c280301c11503110005450003a00d20040ca00000c504a07041c144003520b00b0540c1007200d0551290090f1030724080e03506540803086803040c100c0c7ca00916100784070810650380500c1c00a000e07140300071070404400d8581c1c80e690700030304000c40301020301009100b43d04681c84052100500b1010300125500c3c14021b041440c0d2540f050f0056900d503190480101c1d461504c0201500f507140d03200300500050346049580c0340141064145e2101e81d659401960440100c14451000b0410191018003000441c608015040c541544001010903144c43d0401001c20703044070840990f2581c0717180441015420344010307105000c1002e103601c54800030b40795040c01c02500c8022111030004001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475928030 1250 475926780 475926797
    0x11070510200f030f0304020609040e0604050c01020f2e0c0507140a02010c0602180405190b04060e0f040602040b0304060e010e0a03050313051518070e0601051207120c0f 74
    0x303501c50b031200c01c9507003400c840341c00400c400c040041c4900003554005000901c114582420040010308403104402c810400e60007a8042000b40101402114921882030016020030100c11b842e107038aa41c218850042c04000c1440080820b008541c1e0008020042e95410000017000e0b01018016801c0f400048038100c2609105040308a004900c11a8880d0b040c1c542c1c0e990006596600e402a4004498078080040c0d0042076420075500d44c003c071401130803a40c0b010076802110004d00c0d400c1d20181c10603680228203103c4100881c50640c1c0c03041d6806040304e020001c840d00d562800b10003a201c0e40e071047c00d881d003000c0144014003540b07500c403203c40b01d00305c00200449640000800d841e050b041c0c801401003241803000440100d82c3e800441c00c500c3c4104181d81c1c2c1d072440203c00743c00d461400e0302e01180da8007000003101c24981d420407407200038003540c446030f00480c03038a0000204148541a4203d01100004000c15101402010f40900380d40c1c02940900c80005644801000324402024620000307400303e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475929280 1250 475928030 475928087
    0xc060302040602030f03070c050601140a050f0d0303021b25080c10031a061303021215070f031b03050a0b060702150a020304050612090c09090a020111070510 69
    0x203108880444289402840c01c02c0849940b0400c1900b004100c503040c07140b40140318000034401e0060034081c05a500c000c00c0082c0c00c0c14188441502e00780c2006020b2525028003030384941c1c4000c0e403c80748552502d800350381c0d03e280c20150306100c807400e45e55601500c41c4c40b080004aa00540c540545c07200b41c45543c42555903154485546c80e031642c903400d030b004841d00000130300c018442d411402c81d44203e4000e0004031031010001c6001c9034065200305a8800c1c10040030700840c5480e2906150043e0510024203405000a0741c81c0c104040c05000710041c08600038030710549078000c0e004403001c1618001105203030362444e0f001a0140c503085552003160b500e0f00d4030b02c01c140e2500c9015105040e4000d003064071509120340f846c1d0066488014a10150700c07007404000744aa8902d4014a88a14001d0010340541001d4101034508000e500810f0f00c54403c0d10708008030083c1c0007d40340801d5409203010300c0c0102c5103050082c2806000d400240d003003410601c244802030b40099203403101d01d070110034650310b00011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475930530 1250 475929280 475929287
    0xe0604030f0216060e150c03040f08100b090708220f0606051f051317100b0d1718040203101403030702011e030b030a0605040203010c0801080304050103021b010203130c06 75
    0xe901600c00440c451401c0c8800c2c0e030030701c082c400030984041c4005500c0e103103241c2e021520f95000340d0300140ac1c2107100700c010311141c2428000c00300c3c100c0102c1000d00000c03185038009080c18200401c6c0c8005c0221500020341151004040e41e1400350b220105801078080c6030030900c03c00300e146042542c05500b00307100000c017418175882d401c030181080e645c0f0b41c60700108880119441d511001e80494155450000405e40d4031b1604c020440001c0080000d041400100300544191646020303031a02c610b1490b100e0101181d4003500d15030036189040003c81d83d9200c08216203030004611079445070460700c0030081101208440403030320291200c540c03006035103a141c00c00b01035480c0b1503940024006070a980d0141501ea03400e003d142002c88840c14080385840580d0046031410600c01020b031380306500c9005100035800c0a221f256a154003078502110b9941c14223102940d240702d07900c2080e0400d0303400103050784040404000b120007009528002e5659003401c0f003110000078442a0140c0b00700301c5624000450030b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475931780 1250 475930530 475930573
    0x1504031412041a070605010602031902061003020112090f11041a1f020703050f01051e0412081003150b0a05120a02040c0c05241b031302040e0604030f02 67
    0x202120258a0203041c07041444051603c8800c9401a4005003e41d100082250189501811443d4000e6031660303003591310f0540310010f55183c4025504101706004030f1307a0304607109405072078081c2030515180030300300000c000501c018100a0202d1800c040e12104100f0401c4881040100842c1d051003082c2c28645061040034080745040d51050400700c0010300000d2b4000d56001c141d5003401900c00c0a603807902c07001e08012055405102030307503441003003280051500d82c6d070304201050701c0503141c50b51406554804ca82c02c2c880e03290205103c03400c80060107015040c1d007148051584107441c007004c00100090000a00148c01d405441140c1c5c400e00400e542c01c0030640ca144011004000780341d0708803150248002025610341c1c200400104205280215008000340b071040c06035615010f108040c204050350022501030900d000141c0c01c1d46180600003410400d0341e4101a0726142420b504442c0c3c40010020858006400020300802c01080309264116246900a2505400743c600c015405002c0c0110801d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475933030 1250 475931780 475931803
    0x4080105130204230103020409060e0307060e0709060605031308040f0906080d050708070b0c0702150706050610050a120204081207030906081905040f0606140a05030a0b0f0901060515040314 83
    0x403010001003002d42342681092031000d000d40000524060b03503001103829a4003003202070720100e40712803800f16450020402c1600030302c0111001c010050500314014064480608605a00700301d0412600c1070046000c00c803401018600c042170725a0f80c0e01c13a18440504014030550600307002d148410245680101c0c11210400d5000c10242e14040180d900c070700c10102d014211000516080c008140140c84400003ca0080f902e11b2403907886100c0c0381780941c2622001480640141ca40726440260280c01400b80c41e040c4045052074490300c1c00c03038000c48009004e0b9901040e514892030802004041c010001040040c0c042d0351907070885510b413002698100000c0e200c6428581c0c80c08004038507a8000c0c3e1103107402510540f90403002c020789440d040195409a04039001d00700300015206800e207400001c1a00600058000d01230030302040d00c4503840c40c8401421910300c45040d80000da080c81e020750000d8080c03d0700410031005034510444035912134021b800100c1e10134031020030030802c5000c00120440c400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475934280 1250 475933030 475933091
    0x40c1e06090e0f01051c02030304120203060901061a0702180a05180a02060f070305130b03070f3207050709050a0c05090916030207050f06090c011701150504080105130204 75
    0x30f905c0e0409122001d6080640c800031941d024000f040140d40600c01080244403500b0034030041d070b03079030300401d42800406400c190b0310b40c0c03508008102c1d0070940e041007042c500340318a12070b80f0307010b403800802d54207410b4110400c641c0c0d190108021072455641c1c0404d0040300c005c0d144a415025a42c00246d940030782d404040e5005000707011151480000720b008200301840ba01e403050404603088441791400c0c04540110082007008410000401c4d4070000340b54050406d450318501c10b428800714a9180c81003181e00b06000901000c550504116102c100c8803103035805401c40759026a00c5501400401d0156845603009090024218003e4132030001d0b03036038114004100380015100c503209001e00340703e0403452900740741d001d00444022070005d000c03079107070b44107a40c0103069140f034010135907420304810406250510000a5010159208806030365041d40e1503c0d0f0624141c203012038080d0b446002d66800882558201403c001c90441094540e00b4468802d6500748402c01c28410103003404c0081c19a042000f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475935530 1250 475934280 475934311
    0x307110d03090902030c040503010c02070e07020318060a0e1005041409011805090c0d050705030d030e0604060c1704110306010e01060210021b0303040305040e0c0f12040c1e06090e 79
    0x10f41140d0084d034000130003a15061900e556000441d00b500c1e48a801b84015170003901c4104003911000744000ea00403d00d102540c64500514a8411964035803001280940b0012503800b800381d01a001c01d44a80724018648121642c103a440288203a1090060b4140050083d101601e1400c2c92030444d8181d50840c40b00000305030074180407a00505006001e040d280c85141c0c40364145d92500107041c2c0d680f5015001600f03907581070100741440c08920f62554130415203042e0341205d0001000c56020341059014401040901100034110f9590001e100c1a44000346110240400c0284610b181e2070728080a41c00e588503a0380c1c0744081003080a007445142c015801c08102403080d4031142d801803140e42d00400703021510310590780050380b03980c20881e8110040751000501317101071510a202c040c2e100c1c05000815180501b0510a50028003403219480c0b4105035690100d0100220b0b40c410388090300c80160900350303107801c80d1601d1015124510869000c1110b0031b201150744112100f18074803070031950003035001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475936780 1250 475935530 475935539
    0x402040902030c060a020304080c03030f160303020904020d290a060f02030f040603061a1c0f0e120a0e0307080d0f090e070c020a08030307080c0c01021b0307110d0309 73
    0x2400d4490422039050050740205002c5544400161102d004560b0055031074034141000185005d50041c241c82c865842400343c1850a0a9001290340070303107a0061440300c82c803852a0a41c060f0150130303892544180080303203440e441040c035444074505280c0100c4410016410741e00001040396142c58294125025110034010180100c92070074842040788122858010a079032200c82c15040ba40080c400641c9400c4100b081c81400240d070b0140041c400000b514100000c0c0300c04004102e902c118988a41e142d15505e549812544e00007480d49a000d0142c9881d0250410700d0300c42c070b40c03124540c00040b80c80c0d04120455401c0006107602525901d00041c050448010002c1e14003a200d6a450b40801007140c1020400348400c6074154083d50040d242d0540949640c03041000c01001500084c4650b0300500c01c0113200c1c0d078007020742a080510080084e6555141c5411140a0710912043c0d00c80358080e03c0304d0300e803d241c1c000b000301003050047c00e01c003100290b07a20410089220640d40a000200103030414132 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475938030 1250 475936780 475936789
    0xb0418020114030711010f0608061608041b0b0d05091b030c04050604020c0a14070b0a12092d06050a02040303050a110114040b160f0c1506080114011503060501080402 73
    0x16001480c608240c100d017010f1401d22400d5640400252402ea51600410003400000b0800d2a8000110030a01041041c1c414001010408014405800c86207480c0e90503008203400d41d0b02002070010605c0b03903956414140c81c0303031f0003510050351254a140f05201301e1240b01b40318000901c2c2e10f6a0010040d00f049040c4600700000350001601c42a8400e0342009000e0759100200712070400b09215004141e05003829841d1182820171903480802c118004101000700c455000780110180c25010900252629150a24400c1c81103103040d421808060145440c600340f0a001089000c64421202030000b5500c0040c0c4c3c1382030303000303a1200902243c428407042000303d0090304e808080c01482000090400c458100b001d4402c5000d56080e02c03d11b10034001c1c801c07041c00c4e8880f406c1819656080000e07091601181c0141100100c2c540a05011003040c0720002400041d00071600034840304000f80000b455851030b11010840c01c1c814102c40b0480380c544404414064090001165016141d05046944903020311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475939280 1250 475938030 475938037
    0x180d0503041b0e180309060415120e100e010c0206040b15030d050a0201050709030c06050f070c080606030d030605030303040b06030a0c240207030506181204090b0418020114 76
    0x444120721088200d1015000341250740000306a0f060041041c0d0516406040b250320311000341c1c001ea41c100300549a52906c546003200c6c1220503000141c0d02c02059240200c0384444444c1e0341640d00360800c0c50000d0170680c000f80001c24a03940c080d0422065020ba18a9030896401130207000241c1c00c5203000402107100300c414994015840745110701880207000000e41003040e0a500d05011610100d042c00c1a183d09108051f4001428103241d540e207815034951910340b01003846810100000020301003e04032034281500d00580c0d100b80b010074803948882c0384130349500c001c855403802403043c10548203295100e8012101150000f50195103503465903105c5c071600030001400c040e09403003040c04400000c1c0b11521600c0090031100c174004651500c20400004c0c1c603d880f11b41d01d0856014070342c00c1c400b240004ca5440e40140a1001002e401e402e0001d220707041a44440700304003940e0000c5030004141c003591b0003400121808032410032680e00a1160034035803151280e8042d0010f10ba40e01e8000403644484001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475940530 1250 475939280 475939283
    0x9040303110705030f130608060f040e150901090b0708041703062d1905061c090209010e0a0606080c030624160605070309120305150904030804030206180d050304 71
    0x7568507184032511500d1035540030000c801050400010002c61070034401c00040090551450721a009042810014076004001845184501d56500040d1a104010000484504410001685646001517055000b081100c4065440c4515000000d0400384100340c0700344140d070b100d003921544008010b440a02600024285500a4000c24903081111802c48000101c400d08441d44c046601036038040c011904095a00f4048001380f011051155070b4079070302074900041d4403030070b840190340c0a41c103603001610403010041d42103a02c0c2d200105050902c18900d80c494801e01c04280510b540c2c6880840c0d19404c103d4101c100300d1410b101288013868550210740c03504111402e40c0725a00d0b811140258584c0c88101d41c1507142e17141c020321408100c650b010303450340307d071145c00c08000c0d00b0b01503100d030740800448442840c00c05903079a000882040003164400340e8504040c5c4500c0091402c2e04e0040d00524080e54140c01612514000074080e00c4040c50240d40280d80c0350243c8040c580001040c1c81d2034101810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475941780 1250 475940530 475940561
    0x315100303260c0d061a04030314040306020c07150903110f0409051903020709024608040317070e101e05070b0c0a05030411120a05030d0b0f09040303 66
    0x540800d25260303111060007440d20700d0242e0380e11310018020300c045440c90342c003001e40e014544500301c00c50603420701541e080341c0d01800e0200c91200d804409201921541e00020310892012401c9110440300188890903214000c0f100d040400c0f15080a441d0101c1511006045201c00a000e090320309082d00080003a00c000f4001040003032040da0340710b00b4800102d405401d40d45a01d1000814140e0402409004050502c0c00310304d05a07461110321109800030641c0345021990f0340b00c0e25a6100d11100320228006803400702c2810700d9492500400d074100542e01078000076820b00d991030420a020751094050a1507880301005800340b0818805a81481c0348030009200300316a044009038014040c0015100c015540c0c1030340c4009a140212500c180a03008600004050100c0146a5003040440344c1194000880440611418001900d803401c180c0c0c010f07400c0c0c0580303940542001000000740601200080c0240102c011000902040d0790654008030342c80748400c0b001c2008030307000b0b41c8400e0507001c60341c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475943030 1250 475941780 475941827
    0x7060e060403080709170709050417160314030f040b060d060e060711070f140f10110d02011802040902150a0503010812041d0621010b0315100303 64
    0x42140d08045044805038040348829007000380480c0d0202c02d160141c03a00c81401904030360840071266441b0344078060030030700b140d40e08041014041d000c14003400301404800384660f103d031509d00f401c55591505108802140401308198103000d010303029030b84900360b5514070b90001d81d41c03600d0304502480094041138129554940308404030303910303008034145411108014000d90030820401040b0300030003040c08640713403c644c40a100301c109507100c10303007100c0d5a0210a10b4032902c0c8070014000c584085691036102ca1442e00c0c2c904565003104c0750325850700c6240140c403118400024241c0c02e850088640b0405171405101c86401460280c2c40015094005045031000b801c01400011250b07100e074030041c1c00b0650200041181020402a82e01903450080c0300a06280c5002070911085a8101d1400b64115409000440f0340d2a0700d0700c41c02684002c00e041d2141e03030100c081c0c500e000f0b15103c581c1d14002d001d0303082500c509264481c400c5005646858607404c0052640d20f08580c4040409554058859100b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475944280 1250 475943030 475943051
    0xd09081c0203040210020708070b090114042304051504110d0207051506190e07030b1c060f021318020c0307032a020a060e0303090a030b010e13050d050706 68
    0xc0c0c5801090300c8410041e07a03400c02d80100000c0000c41450642198451401403100040120f20003040b2000c2c0d03114281c44468500058030690080c149101d154070000c2000a4a000308500c5a8589032910054007032a03a4118144000c4d01c2e011034415660342001c145a440b50305060f44103869200d8021074050808045201c90010303030384100c80c291210362001c0b08010445804000440d080141107070441840d071707031000040e0700582c941d00c50b0307000450619000800440c002e80000c3d02200c0d0050215400c030b0540c03040b440107596441d506480c00b0f45000c01c080c0081c2c00c207100f151151050a1a842c002c5440c001440c070341800d212003903081c880e80034080e03440c208a080001e0005607100742c85085007220b44984510301e000e20030a808803c1340c500e050010140c0c68040c02c2d0401e41e145451b0005403503e082012920718030803480c1c00e80d04403466510000900410850481c145c2c0c150a6895107541c603082a0309000050380240946290841015050154003c5005100751032107800040b4015270030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475945530 1250 475944280 475944307
    0x31504060314060f010e04050601060f12111e0906250f06020d0c0e0f0105031518160908030414040605062205180f04080f0c0d0f0c080d0908 62
    0x40d002c0034220394041e0050215451003501e08a001d402411780d20350444c80c1c65112075648a00601c10724003448a031003055900c081c071035140d4002c0f01d4840f800a0190045e07207a132914131540320716842400b080801420308480300311031044840c04103004007101d0526406a04410030414410121107000d500e04c100c10001039500500b8000d0385025070303001038841c80040c10b9a42031350321200030003040203440089000241e640000c2e103545c507103081ca071490f05c03540d41c05c0c0c0400c200f0450300d141e03991010100210210040d0b03e082424814100742080c80340080b68054259492042070040c9070707440d0000d01c00bd1100d110356191044030080001d1000c511590f0b114081403091b80908e07281c50034442035110640d102151078603084010302040d00c08004551120103040c0304100c01418a003040103491000c5418020203806843e042d1019000250350b030032440400c56035941c81a0400000314030400c400446142c05107910b030303022580141c01d070307450310013a030f0601c90080244450480e0403800500c2180000082c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475946780 1250 475945530 475945553
    0x90b10142107050405030106050631271802031207080d020d0b1e0d20060f0c0d050708040303030c11010c0201060503060c0408120d0f05040f02100f050315040603 71
    0x2e600c40130b56a50600041c1801e60341203070000c0c0c2c05010200300400c10560f4000700080c60030b025040c00740c400d80305030000d4503000c034481d8400b012092104404014412112016060b0310b40c0d120b40802008000c08c01d0490a8880b490010754903410444031074000c1030b40390340184580c2c1c0c40784404a14150350041c202040360000030b039020343c8903965480c0400d40d0400e000048404440201c6001ea946e8a00c00090210010514020106141000509040030a10700c06030701ea0200140b8a50304d9181300121201150801000c2c00710394411030301940d980500402c101c80c03501c1d800c0017460b46040d082d510706034090411400030078100314406140c080000c4003841250613039070b026800460128030304000c051030207902504902000c0b80c2040100410000020200741a90804580c40d40b80c00d241d4001000803da60119080d046050100f084108211030f040120030500c01c4408070001228820b04841d82041007541c0000310b00e040010a00030700854503c0720301e00c01c0042004c9100d684968a80d01e4130203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475948030 1250 475946780 475946791
    0x13030203060c07021206010e07031e0614150c3a03060807090b030a02040e151005150705280606090c0e03030a050a14091801090b101421 60
    0xd10103e454421403406040d00f407540003c44000740741039410301d1700307808000d02c000c1d04400030716507503c198040c511410003c1034010f0300710150400042d6520305281d40d86d03900700f0300007512071b818400d000005400e011043d50000d1445c0c0e00202002c4400c00000000710180d20a000c0d800940141c46a40240f0b80040c24201c0c10502e13640450f003685840e08203454048640c1003090041d040034042601030300c0000315a07041c0384c1c04807008a01101002e0800c0c1c100001c800140d03058110210800c8070f10781d0682a98421150192014207880ca082c020300c101d01d024500780103059400c007500c1d5840d0462107070703c0003c01c3c40845204000c20340c21a501d41003101e40551110400c1d80d1100c6426060780d8210180311101075058020718600550003a00500d9841504185000d12200000d01c0f1a640510405d80b104440c0103840135132500303020340c80040300b068240300d1a5412401c24200b40040d09041060903450401c549070b8001c1070400700510b00d019003101c140403881d0310010710201034241084442c240101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475949280 1250 475948030 475948051
    0x41e090207060f0b010905010806040c17090d080a0b060304020d021f02060402030c0109030c060311070c17010606030e031605010b090f0f06181f0b0c0d030b03010b030606061303020306 81
    0x50034080040043d6112085032a06125486e1360070451a40c03c01c0300c02d544400c0480d40028242c26403a42030f1400520b20502e01c010640311000c12641d00c00000e2004040c404035241d02000b80e5803100e0810647d804009a5504401305001060050918440a100d502e20041410200600700300c0310000070140c4401c064010786c030040500095040034003840c46440d4013840c00b5448107095072650620025240725607010140e940e2601100b540050080c4c4045991001040c50b40e00c0e5a000d9023406000c0ca01108010b40d440c0c0000019a0f0780241b1680c1070002d003040146003040c04a1504000c0342400090954155407074091780001d0f59114090140302d020b990b00055038508145102001c403903802000240504030f044019031000d01111440c550040310700300140c4c0030313009160b500000c032005540a524442004522078800d80700224440c204410981d40411106907078004046c240d502403004142c1580000c408600d0a041540080041c1e0060400307980396282c4d2503010a140c407500312030701da681 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475950530 1250 475949280 475949291
    0x906110406230f09031c091701091e05012c0d0807090920040308070302070b160f020d0b010303030608010b0301140103030c0212030a0807032906030709080610060f080c041e09020706 80
    0x1940192129000462304000030070016049a49920b880d0941c100b00c2e141240481040ca410010300b500400401003c00d10180700419612602c01c80b09107441d649031801d8001c60b802c10354018400c0074424418a0301e03070344540b001c40c03821558000414210180342181178603001203415000059005000862040b010a50383d0440350030f00a0a01c5000d03040600c1d0a8410800d10781500c1540810085031508096aa10740031507520004d01d030380840708801404005c41e00000402e151f010391000d011191580d000b4007140040401301800c03206001c0c09240c20760090001031010a119507001080d0a20123850850120960300c01d0701e2860304040d0700c0400143d000c108225407a40c5c9800303120108045880c0a4100610042051280d0108440801c0c09210f000c000103640c1d03171090f16900d000341030b42d205807074850074200c01040c96450070340a80070100c0c019182000d03c1c07501c210f18162080f02c0c0c0c0b05074030b801c2ca41804040c0601c104079500400344000c40c00800701e034085084c030003401b54030300c0364000140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475951780 1250 475950530 475950539
    0xc2003130510050909070e0909070503010e070501120e0304030818180903090d02131811030313090c020c120a1a0903070206030a0906110406230f09031c09 68
    0xc100d00140c2005000b80b410941c641c02d659009404d45940e4601100c3c100c0a6644024085a900292403041c650121008091051040d000301d0750105684003074000703000b00404440c015070f40710110710440e070004540c1391076460310021980c03001043d0780d000d0041d2072a02d5502c2e22035203a290020039020b4185074085d00f001d1468034145429860001500c81c418144e46415400291a409490910381c003075015001c15a08658a2840c810710303051824070104564040b02c4007025940d55406411114200310b03105040d45807a00000b9a54020350039800d28200508220542000e01443c140000c00d40c45070413003003800c03903580341c080348028503241008004183d9242450401546850032032006030501e0b000f40400400e0100440d20131940540f000d944e0380e140c200c1000d008040d140030182c0041e00e080d026020003414200141300300c44055845240905c0462911141c076a00b007100711309243c2081151480c0d8101e5030b40500b01c0c2417002030680d46850b00801030a040803001254010003c1d078a01000d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475953030 1250 475951780 475951807
    0x1208060405060d0311010902120d020c0d020a0326030406020c0c120303010918050106060305060907050a02060f070302072012030301140105031306020406050d0506011b02040c2003 79
    0x550110046800703104500341680410600040104040d040194040928010349404d401088205a000d04031144d9032440391250341e1603038014101c590050240d001140034524020389100c1c40150000d00c02ca503040c0c6103a480322080c00200c0704a001d8010843d450500e00200780303000c0c40c81180076000150f581c00105c00f0842c107040c030921100740b02d4034251000b101390f100c001040d2415a1381d8440001403400c20303030003180481965010000d00382e6007428008220303207915400c180e008000a9440d25841e844400003520280120040352005900c43e03030010b600542c0146015030040e1040c1001440c001c2d80352503e0700c04045501d1500d803140c842e403040c40e00d00d0a10025a0241410440c0950704550600001c1c0034021400b01080d81000008004202080d500d00315104045500c010110341c2c0d85e50300c40f8040e0242d004402041300b858544400100d941d40122500c41e41120303002000042c200e0140d00700700003400e00102c40e908000203001c0540c0002d007800203032000d80d082c100c011502c68034001700c0302c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475954280 1250 475953030 475953047
    0xe010f110a02060f06010e0307030f0302061308030a05061c030903170f040b09040b030619290103090305091203090a090606080403050708130902030405070f1d04020d02030a12 77
    0x4045800d02004000c030226408110640c1280c4c115044107402d8841d4030049519130782c502415a8180642600001080350f0f0410616055100e902070340c6880c0d8540401103801c1070309042c05420b04508100060381c2e41e0090707118070390103100245003006448860742d040c0ca02000406080300410303500c410520501a0440040d1805840c040440d4644400c0410740100c0d4010b03131040c55000744002c00c1c40c04240d5225004004c60190140858a062610130202c0c403001800440000020b0303e00040240c80384202e00d411207480e428140c00c0e142c9a0340060044005080340b460581c01c00509001103555a500c00c000c8080e00388506006546071a080c80800c001c2e81e4847e4060524146003010400c45281c0050703000b9403043d058140142c44103a1800c05507000c0c4542603451110409008000c19441c44640c00ba40c0524080c008459040707461360811858440309000c2c0c0b03e0084c10031b4100c544004120031480741c0c460720161000b11205800c0e070120b40303015035181c400c40c1c142c0c0401d141d001606034000b014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475955530 1250 475954280 475954301
    0x222106050f130b19092d0201050a050a030f05090d020c03030c0a030f090801110403110301060f05040216021201020304031b0b0105040905011d031c11030609190e010f 73
    0x4030900303040c800785402c44a45000802403500000030300041c8000d21800c00c000f50207044090a00c50108079103050080008070a003c40022020410003124000c141c1604001c0c842d410f848080c03601400400c141c031141c01c0140e52208040c0c6503000c0c0030114002d40030303107030140000e0001000a420780380b80103030900c844400c1e074074040da0090024070b581107030018241400030740608150203285142c0c04210b9240c555900803085075820700034103c66100001c0f000340200da009810104400c06180101403c5e2021441940d0700e20b10168803d006506d800d5000f81940080700a012800c052107901080d29801803800d2841140d5010041005268128604044120702100d1000408000b9038a60b01144010b008190003947e1ba6001d150804c1800d5002c0174540c00410032a00202000309440e42d603031fa20064820322120800d0034221211001c0e40946040b42d801c1c3d0080e1400d6a17950000e100b2400c1c0001e00c0e55480789030b0800300d694880998810300d10143c4a910010070403001e88440c0c2c6c82952090341350b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475956780 1250 475955530 475955551
    0xf270806061c0507050402071a1006080a0903022a040f0203220309300b04051b130906020f0301060903051504050606010e0a0f060503010f0b04030822210605 69
    0x540c200043c0046500015244111001030312800c04d0308002c0a0304182c107541020900d004018002aa0400900d4404440c07240e0744854560303840a2400b420707541e1084c401000341e0f200490705001510701c1c60400380000c07600b409a08519104000240a982c2000c8400d1000c0707030b00005014491800c0c00c5030307103000c001c3c40c2103c00b100e0702241e4004054000900c80c4c10b45140703030744000c40d1004040107085001036507400c284400d0a03d550800440c50381c800d4030111140d100b1254025408910a40032002e050360040a00340807004461100000e032013110000c40c1c5041d820010703c1080717155031000e18040c11199079090715450440c5032440c500111407090448004c0340e1410080020310005045502000030728111740075081d01c1010030501506034010700240c04000c50041052a03104c00079504941d0894210110b4542c3c4181d121038a1081e4003000d898000c0400090060104440300c4940700e0207030810b100e1007142e6031922000502d404801c0c0070b9405101c040d40100340040e5000b40b40c0c10900045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475958030 1250 475956780 475956829
    0x1c0519031a0d0b010311190303030c021b01021207140303160e03010b150912190201031d0a0b0403050c0109060603020906191502010905240c09010f27080606 69
    0x2c5483d090610148001803018105110491841d1103180b42e1800c0030200300e4021307041c1030300d914015002e0034030120754600510801c06071302c4045c07541e5604a0001c00045e000340211001c0e8420a0b043c0f94070084054409401030b01130b40451800c200015442511130041c0700600f6a0400d9009024100c40744c4018402e0381046030354070007551403404c151442103980250603640c403006c501141d01116041c0544019000b20400c2020000d40d2030300104409100366401c0001080012840c240e241100414040300c3e4008400180003c1980c0da545401c01d0080c10305d41c0c10040e000724940d094981030f94080b142c480d01c60300104114140703507100c10b411290031104616048030001c025101014244030341611101c2400468403000c3c000c6d4045400550880240c0d02d2030707081c48143e4904042200340c51440b200e010343c001012200303050140c6015000507500c0a0310100b44400460702c030600400c1c0046e640c2c10a1903c9513451500040d03140c02000c40202500e1140f40c4141002110904400961190400c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475959280 1250 475958030 475958033
    0xc100315060f20010c0e03060c0706090f060c020717010203191d0102030c04050f0a030b0a050a0e03070b04030e0d1e170f0409060603020c1c0519031a0d 67
    0x54102009480035803504180703500041004680c854030000c40e14200c00080100e0f07054150040d000300c0a400c0c45511303001d948101e54000c2c580d880e4401c40b201d41c03046c58140700c140c002851581140d00c010740184000c80103041d0b2031711a00d00311407224a01d02c0259003c4042081114041c181d01251503a2f420004c41c1585400316200c803552030021181c00d5405e5032a48040514910a203488041e0000300f0021074580c075004450400704e0b40940180d0f84600c0100400100b58502901e0090075240e018102001c80e0f1a120802d80142002401b980b0423551200b02562890400300040c2c510760b800756220506505042c2030181010b180c0c020154041d070441d003115004180b0b041000810306000c4000d00c0c0401095040007220780071107041600d046100016415001401c0c50040d2003941c6c543c0004228150b07885109804074070480c50044a030341c11070304822141400d001440440600141001442c098208000c0300108500803c1c2074042a51101840c090310f420981c0a417800303005850034400180503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475960530 1250 475959280 475959311
    0x51306050904120201021b0703140105090304060503100e2508060325091104030b070201090314090406090e0f060f040317150303070305120a1104060e0f030607020c1003 74
    0x100301074844040302e0141c0100f80e00c01d50441341d81c00c801c2c5a075543e500f203501510715200c4a56210641d0a0850141010348041040c850b070b500a0108034019403900d07180040580700f03078200034403580d4000180c00f000120917101001c220f209922003241c444e00703200880e00c441c805400c40f500300010456104100702e11500d0000d60040c000182c4110b181130341d626005000b01d02c009503041104820300b004004408100b0860150090700e10035080e0507030982c0c80206c12400c0324800100540080c08441c1030740301070220302000f4000c0080141c0089040343c1ca0f01655020368500c005011010b61242e82d4180c00d042051003c1904007031110482c892606241d180181916102603071400b060b0070b4000415410740303c9c1d88031944000740150540e5210304480c140a4443e4204562031250700070b2283c0000e901c4e1701944105080b910b400083e1074141428031600300c8400f000300310345941000d039882c20310f100343c0d5040041500c620829401441c5018854081c042c00d120400c481c2000d01d410821030710400c555 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475961780 1250 475960530 475960549
    0x51305070909060e0f16081c030f1803091e0e0408031018090b090a24021303060b010f02030708070b041502071a070f0801090f0b09010f05130605 64
    0x40c0c03040040b5407000c03281003000c002c01208051041ca8810350350b1010146101045205440d0f40031007461545913690401c00b80c54200c114051000700c401c01c036028415601903445078444030022071002a071540141c48900e40086c60342c20a03408148160740070401c801d9078840850913040c0c1030480800051174218400505080508000c215407400300006820708403100c01e2100621071092582d40c8000101c401c08002d0051f00c0c802c0da181c9602c08002a003914000032072a80040c0d0001000000400b040c032001e02c0b40840e403000c1401203400300310015145804c00240c801550040c00c0011b40c502c802d200160096101d098075805540040c844400443d242d0425130f00523540003880f5030348641c1d5600e000581d4254514105840320710100341e41c0c00f4031086820540704c03403094466440c0e00c0e4407844019104040c0c2c01d42c10b00001004840140301c1100160800102c0121540300030600a480340001a03003481e091708840c0400c6c8074240c0402c9940f804000c21482c40b41c138003504020740750900010840100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475963030 1250 475961780 475961789
    0x1b0b030f0423070e04110604060f0f03061d09010e030c0115050d081c1407051b1f1107020409080c070b0909160e030118020f0406060f0c050705041e05130507 69
    0x245050000b4050050922403d265001b00400455803070386c4858028141140c0351011000042164800d0500729000b482603d003502d802941c80b0161403282c901042001c5802800050103540324041050b00d40707001c20291811954407c000f0841c1e86015840c229640002e500c60b074072401a1a10890202c0c026500b1224500410b80910041030a094003450142004440da0f802c60300b0880200043d0643c0a40503017142c90304240a810b150280c2c0710f1a55940404821081c0c1810b0784002580c02602e4039802040780c41c076400c48407070920145030009422110384500c1900d03100d4001a0b101910345050100340007a059003100f103030524841e00082140160010070603140799819115154405008048103020701c44010000c0c00310701164582c0c0c6490380f9440c00c040703001d03010103c6611400e141ca809180207039050b0759200c201400b060f450131280660000422394981c020b495001c6059101c1e4001c90352000c24550031102851458070000c4e0445074014081080c55000300e0b8a0000224041052810cc1c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475964280 1250 475963030 475963049
    0x17130b0f06220e030711040b18060d061b031407020718020a020a060609061401140313020d0c0b090a120f0b18060f04050610080a1b0b030f042307 64
    0x400030882c500b070007002e10406480036840003080a20030802c2d00a50700c201014180d806200c18104441803040305d55900c00d000c8139640700c58001581c681060003003805c3c018003981012540c0380540780c2c2c0e1188076060040450000340c9810640c015400035a095680002440c8014614203203030030181c8102d1000c5c001030030080d64000400c1e0300c603180b080003584040c54114900300000c2d683c3d03181120080586114004003c0b5030b03140b02c0c5e411580910207405064110b680401c2ca140d90f4001c000031403140d580400c9a12058000024001c5030807404907101804101c90483e40da01c043c0e10402c403008905034042c2c440001412450000181c4034440310103041d510181c1c1d02c1d001d441d004081e200500c00c40c550050300e0300c628010441c40c00081e030050380c0214000d10a890341a01c1d13065198845903014020416a64000050707480081c840340144926030319510310220125445001d42c010341d42c0f0548004c058a2a402c3c14801400700106020350800100d1095059550056800d6515140d080c450b0080c80e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475965530 1250 475964280 475964329
    0xf010f020c04091a0a0c0807050a0c0213090b0a050405011a061c1b0e090703050c18010c140109050c121b0301020c061303031b09140117130b0f06 64
    0x10132440001841c2c6090b1403180201a520304035001c903006146006401000981960110345064018421100c52107059513440c115a81da0b038007404110750044408078513460744c500f805030101d81103000480c0a1903c9200c0468103040c9400c100d401d5603104001101d1410301c84c071264201e560b40004607101d0404280c80d0f040405451b841ca00020680c9610030010017040b0100b040c80b59500c00d061003583d500403038800302c154603615011030440c0c07421a0759010303060b400c0000c00c54058030800c6500c481001450044035182c0e2075a40c51449542401c90344402da9164482201080824030112a170600240d500551100c0540d08640e0b40341030401401d0007001e01e61800b11840d480c00c0d0111201e110358003007255200d092071094100bc242910f001034002a280198014900500030002d0001400c02e6a0f03200307025007090701011001c64042c031558144292a03210402401d2013240c9030780316038803031451071581c17449604240703600c00030041001c1103140c40d0300d04101c8640e4411060081c005d000550321400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475966780 1250 475965530 475965533
    0x10c02090702010b03102009010e0d050304090921020109020913052103060a0f0806060609060c010518011104080d050703020304090e07061e0c021e0d110f010f020c0409 74
    0x40118624158042c01403599160106c0030641000b0a0040a60400310145101e80c03c50110783c080c1402c1c160024503c1c0b503d40c7d1162611070819412340d8055825079181541d00e8603c0e1085a4030b1f500c085400f0a4100482150310462480010030b80e43e050009204400080c0c0c006040f1580c020407480724072014016000501104100341074600f11407440d104640d210329510060036800403200c0c28441c02c1b034804c001c00e55081c003c0358281158032583c014400e903100e010820000e41c0181c125690020010711640d00c07610401d0080a0084108100f9201420b1011841c0d509480caa1b400324051103c0c00c10040001c6080007402031b6020040d4a0900d0701c0302c500d841e00f02d00390300c00d50340008603140c00d144560351004000308450b4111041c1e40c88051032418904080c1c003001c50981e4031500411624030010000d8100500030100701c0c5c03260004030304011148000a461012500c600b0b6805824003455006c050803c00a004031182c02420303d250086606500207541d001e10414607401152621b50000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475968030 1250 475966780 475966783
    0x71b2310180320120606030601050a0e0403030b010c080d050103030221121f0e0105031006060518010504080f0a021801050a0909050a0c030b0907140a05120312040f120905010c02090702 81
    0x100741d100042c8400c0a52119540320341da45d82007600c0907842409660000184c0f480c100c03501d030048070310308191803109a686071400c0d070041c492015210f050101f1040e4413400034030084004c0c50906640c0c600003503154198207000b49058843e6000d107018100701224520014a02030982c1c04501d12013866101990300c003071030103199801c00c01c0600c200511640c40400ca905c00e503916a4141d400517022030351500304080c4d607007007034412a216200202e0010400c040c0001f240042000c00503a060500e146031640da580001e2900a183c001494150440e0717400100714600200e002c01402113815612006504020002c1c0c2409014400c50340419a00d0340042c041041c03d020200d00641c0007420000007641d6424118041c0b1805c83c1c00a1036030099000124801800303469060300e208000e400041140c0c1018203002040302e00c030520380e0b0035100c00d1185a00c46514106200c0c801c500c0307081c910665500a1914941d5144005c0d81d02d070911500007000d01040c1d92100c084400742d501100e905540d900d84000a9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475969280 1250 475968030 475968083
    0x1006171002131e031103010207020f0126090d030e0123070311030a05061801031e2103020405030708030c060a270b0709060212071b23101803 62
    0x441c0e6600b4440c0c40000851100a104a030f005001720070304085100e007014201d1103014030095000d865941d1060311075106000a11305101040500580308900c3e526507030b40e40004986180840d88071408a00340d40303a03d400341e1603178165868001d02c610075101c00c10703803c01054900400e01400700900040c1502c1e102e500000d8a03c40c00494055880c10600c4c4440d0180c0030481e0190301400c1144100098074011203000d9040343d4100070700740380103603854600c0341c0d10321081c0e00d041d6a12030a40c80003007804a05401c994032103102c4c9890060340c0c2d900e0320040c1801c0108641c00310a10380c00c20301c0441d090401c0419007030390105030380d42d0001c1c3ea6a01703552203007a000488010700c00280720140701901044042425240105265101c0380790b040d81e6041300300c2c0d0314690541d0401041c40107104090000d000d5001502610300b9840340c07a8070254880c580e8030000b40d22810ba00c00e0b100c00c1c98800920608040301c1d0003440106505e004001c40030483e0324110840301c10f110050001088401d4903100c00c4158004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475970530 1250 475969280 475969289
    0x424050a05060403170a1b0c0e070c02090406020a0e03161a0309100203040f0b0f0f100602151305190b0a0b0f1e03070906080c03014109100617100213 66
    0x2201003d1f07420108202100360040e8031403c0a140c0118007214000c01489812980c0181036440b15035941d03841002a400c102d44820502c0300c5501c11600e01d640501c040080200c40e040c1c011103441c07074550000c042085485074018100001c009100303da2102240082d004c2203c0500943d0b291030310300c0c105000071141c01c07001c0e0002e1680010f20280c14070004015001d40c042001200880d01c40301c907622070b4a65107119983c003592015100300114048828160703407000e02d01700701100c042ea4070740710799003406140819008030034031402001c82004007490340b42e41c1140745480b0400c0070754042c1e408148080b01040e0b00512035524400c00d03659030301798075041d0100e0742e501509880c0040c1d40d4000c0b60b800380c2003a000d4900356000b00394500380a4101442050740d043c14040c10040b0300056032612020101e189000d00c50b18a0403c3e690600d950400c0148030702480d140c00041200c00104001d030012a0999003050703801d1a040c09407403101c01c0d00011203e0b81c0f44c8003c4001683c0342da16206039803856809a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475971780 1250 475970530 475970567
    0xf0305070507060204061710060203040311040f09050303090105090a1a0a09060c030e12210c0c030f0a0323061011060c0c0f0606011b020424050a05060403170a 70
    0x100421b038241d0081503e5243e1100340e40c1482d02d40c0358900300d05442002400f03614016070050000b00081100f07400b810340c5070300020b0400501c000f101a101c5090ba60781701020748980c3e00010034030903050024412150303c540c0c5580641a01035480d6039499004040610000130a40030401040951145500040256603c44002c0120180c3e00d5006000717400c0000b065a464040c51035184500e041000482d40942901134040d00d42100030300c030710141c031000600180c151440a03c010001c031030040000784482119810242d03160746805800070151140c03052501e42c60f1000300e6a0948159101023400c1d08503408466030300c07400b89140011980e1443d45868020184580403e012451090030001c1800030b0340c031429140c41c3c1440316080c030381d210425543d19000a00341d0303500700f1803160344810510b075a80c40180086100e02c542c0d40c1c0c24415020265401101001c1c1000800c198174140c48500c0040c1802c0c2d0300d80d03003094a10703192008201c001555006005400103809020140f056681c403014281640c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475973030 1250 475971780 475971787
    0x90618230303011a0c16030c030c080a120e030a02042f0309031602010309020301021804150302030a06090309080601060914040509100b010917010b030d0e010f03050705070602 77
    0x40c034103408115560018450300c02a042080380c110040126410384001105108400d1008205140700b5449a88a01000c3c001c06510400b00b0154203424001540108a020441801e40c140340c1407401c080c2e4031840d129440451080b0014000c5009010b0b91800c40c1032040e0078408440209050501c1c84000960040c60700144000d5180741c0c0ba40700c14035411311441502606248840564948015107188249620030302c0b001840d034500094a40d00c4d81c0c0306140104000d0040c0d0b0120f404e9802079440c1041161114010708454140340c49a003000d000004050742c600b0340b954012a0b22010300400180c4444e0b2a540000b00f41801040050021304501081303440700d684d44e8000070170241c1035000d41240c03d0700c070140c2c1e00e03180d2626024841c040d0f44a43c010385041c2d00550420001000042c410780e041c4485d080e00018480c50811300050700d1401c5000101d600e100c0b00b0205410110610b00090922044082480b83c90368000e018440704038490a001445850725003041d5014015070100a000c04d0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475974280 1250 475973030 475973033
    0x17040519090b0a1d07050403120e1026040f05030c03280e1009091506020624060a23090108090a052d0102040e1009140a090618 56
    0x40040421525a40410040b00e1000c02c1003056000c014418102c03e440040100d44038101080d460507000b02c850704065282c1981c039921155004003901d4890042109021604410b00303004842e13584106483c5015203c9101e01c40d00e0100406020341e40b40c94400c03103800018108014040100401504442141e40300c601098126580c0d40c40700721000c0c480300b40512808066a000c00c0d103800301001a8403400d4800a00d04244691070741d11f02e0019040243c01100001d21840600c02c1c1000811002d9403034094070704000e40070349040c0d07001d03000d02965009852014a50540103803000d9080208a1340c03240c1e59280990215072024030403808414031600000d000865181d0f0100501c500002a200c0540075a036403018640c84c0e00c07c50f02c0c040c180f078110712071a01814085401d95030800d04003807900f40c840c80b00c50042da4220f80240e00524000015a020301240241d014802001801104824400025160b0805411001c060700c00c035080313500c454042080121540080094019031036a030841380101c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475975530 1250 475974280 475974319
    0x3070e092d03070602090303070c0e1e0112080f2b0b0d0f110301150924060903030c0c0512010c0807030e07140d0507080606010206070509010c170405 66
    0xc6902504141c00c044500c05a60020070100001c10a42880554103180706038440101950143c42165032601082008500007103400800034044c0c1101000d0301c4403450640b41041c154501c400c622a188054400100101c036005a9047d0300503070f0200081d034542e05844030010050144100c0d030340c12100d00013030300300380e4990fa501105100403041d60107001c0700c0c4250051114544130008050180c0b403000c2c00344030100d40088018082ca040190000402c0d030300520030652410030030b800500344191103180260451042124004003039840703a040f401c215103055800303031071140244001028002d1810000092140b6210040c00428024100400c0403000c80c2c091802401034459081c08580380e000031030310003403182c89220315811314000104191401d01024103100c0c0c40244000d6840705110008400050040c0301007001030846100500300c50401300000380c24920010308080400506006001a076030b840000301a40d181c00c0410314034080e10044071a00c1e10b01c1190465500031070801c420540072403c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475976780 1250 475975530 475975543
    0xd11061306230903060609040512040303350f070509120a031e0e1e03150a0501060e090403030509100c020307022115150901030c06170702190203070e09 67
    0x41201c594000752204041d4283c0202c0f4075450700365001400050441c10440401504140107070212403c504840320340c480b072584140c0041300026900c92040201c007503c0e4017a0030710045c0082d0240170b0300c00902003521031004000c1130352601425090124043ea4054011a03114141c0604450746580c00350442640d61460b14004500040c039165031021314611040044510300e2090fa2000c0d1000030a40401000051509801702058100440e0960742c1e130b0300308403c01100300103040c052540d00d0018541c00454070141d0040c0e080c0134100054032841e40e11546a1944541d060030002640d84800080c0d601e400d202c1d00603080703038510701824541003a070004058494903100311400b10911480c00403001d111448034040300500d40c080920044100c0181c20119807098202610500d0841c0d0080005c1d0100000c0c4e000361808040441b05100c10340d8050b5022a1102d101030242d9010b00300894000c0d0b071071200c60741918903a540610018115a018001c00d00207202d20323014500d20f8245190741648511 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475978030 1250 475976780 475976807
    0x180219091104080d0206100603200301060e1903080703050c011e05010807050d02060702060a0c0605040b0a06121515030507030b0f13240605030d030504050c030c0d11061306 76
    0x894200c0289011748000b4559114051480035400807918002d4140c0c05010100001d1800460350f403c4000f071a221080518024400c44d52007012641d51402440381010368210a08a075079100c10090003c40d030301004641000e90705141c100da450385500f040d640144100c1d00c102d0207400d2011310303010545036203410042c165030f403007410303201401e03940d001f00400d0240d1404000d41003030050203200094907040303014012035040c6042180200c0260354030700b01290003c40d0116298a0064144200ba8003c0d11480002c1e003d083d09854141800707449440b8903d090041201340181c403103100300f40122501c43e0a00007154000216900540c992a20a140304004c58010f10b4004070000001c29001c0c04013021700e01c082d080455901141780b8400c07400b012141891400488540795480040c00d0b0320100b00c00302c000e00b0f0554002078142000d103406800c082c4d46010340340c0309601520700d0704010341e90041c08220342540111a81c014402c000302044050080000d184250720100400050180c0c10800955425 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475979280 1250 475978030 475978033
    0x30b010f0201060e010306020304051504060606090e040305070f0305040b1315020606061225050c061530010204080d080906010e01090b1306060203180418021909110408 74
    0x110303022008a08841007842a103c0507019040100046285d690081d41c0142c00b4505841c6000c0da401489541e20305c0540f422100c0c80da44010410125030b002031804041e00515070780303000da0304040d1130041947c02006406001c00c0c9403030180b00205406081103400800d900d460080e01c1d081c030441c50041c4850203104428090f0300e12000c482040d880131407120b2013600c000b007405041420b803c03401003219100401c0c41c00c418a001107502c8004424000760009142203684065491000358501401c02101800c10007a45d81300301c015510030b40d07130801050341000c1c9044405800c5042c942c441d0780325400d02c0300d07401600c1d40f00107408101c480e4041480040c50136251122443e0341c65114285c6d907107840910569400e440160014080f4220701c0d0825006507000402400d044104043c07804201c4030203901c044003507400020050101d0070382c0307048002c110404607030400a0300f4100482d0010020650310007031143c601022914000c1c1404a003000280910410800ce01d1303a248141c80d040b64428040d00d40e8a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475980530 1250 475979280 475979297
    0xc07030b130215070803240306101701061401110a08040f06090b030402030d0804020f04060f062c0f0118090f39020a080c1b0a030f110a1203030b01 65
    0xf04440742044601d00c650000082d440c541e80c050300c0028480d00c2e1001d00301c490740301b007024540316a4100120b6004022202c021007000740392002c9120034800041c032040c0c0c40e03414480b003080056041046110035450a0070240e0804110001a07410125807d5004228900c041f03404500004d8480403013003a00c0c0251603459007503848181d030030319501084078000d6160384031884030700146115441031904240f000e00380100510b0188002410394406420031002130308008010004180c0c80080a42c5030064034885151100342c001341e601c2e6042d000c0541600440500483c0700709030344148000321500c9840450049541d8032801140050040041c001000e182060140140ac103003a0806140c26904c8010050754617403010078880c2c40c4801d1061000541c015801024041203c00009040555418000d4640008104080b0b00d07032042420b4490f0184548850500005015450520089401441045803c000940020040c0107203400c06021038040c2c41e000c404154040c0c00050001c1030903201d8010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475981780 1250 475980530 475980559
    0x22030f111905042c012f040e100b04030303020307031a0d1103011d010504050607020a1e0206070c08010f050c0a200f01061d0f0601140c07030b1302 65
    0x2003003641c40401d1140c400d20300400461030a80d111070000003402501d604c902e04422984020fa0800d02910070b030994481c60b904405881b0b41d03000c0e14201325601c0350303a4825619641141c03010f003c1c60280402a01d9102d000ca52442e850807074950003022034204060b5150f460b0b250040294000303485890100381000c81c55038034852910750307050041c3d0010b0b0020700302000540714401d4002c02d0380c0301c41d901075507680482980211641c4507000c40d84450400880c0e1030a092804924000c1c004060401715000902900c000510b07464440c580a20304640f880d440310140d00000f080c0740300710f4000a01c05280040f00240241e0103401c404000440140200300c9a522803540802c00c0c0b00340103a00d0009500142a0070f41d0725000d80c0386894125400c42104c00b181512003a441c00c540550700300c07004d0f4039203801041030000e03051140c10f035100044503494606810030000182040e4034002400c09040c0000c00c200200f103404206100042d90001d4482038282820409612031042c411001d0b03016040b00f8042d1207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475983030 1250 475981780 475981789
    0xc02071409040f080408010b28060f0e0d060614040e060601030c0302040306021201300210031506050901020705030a0c06081b030408030a140f070522030f11 69
    0x411200c420004030030092158082024070341005108031440c054408444002c07814141c064006010510000200c4c85a543c04120f061185080c101c100703e1854400341810600484070901206c62a00380030540c03400b10030701554203000206019400948030048030050080581000084640300d40140a0050901040c8015102401904181d507400030b0041045544660b0103440701ca401c5140c014106503e903a5810705a90100031400c488540b5480180514130300500d42c0340c3e41000c0c541c820000e0300d4420045500040c28490042c0c410402c41c080845400d020f5048120b65100c1100454112174961a026000350002d0020900522a00c54081418100000c1e1143c485800c0100c6c10ba416160400845404e200180490320059000f407806c1c0d020134405003e107010342d00c41e4041c05d032685001003840c011125840500c00308120001c0a003c460010600002c3d08500140f034083d5540c001050b0b60b951085210303524041c980c100d440004248000b0003500e540d9180f0030001d00c0659800f01c1e0402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475984280 1250 475983030 475983043
    0xa080105150309150721090c060804050606041a04020c011e270317040b0604050c0a17040c270e01021314030715031e06080307140c060a120c02 63
    0x4024030381c0a20501c0c0d408500104c0c809030320064034501860200025042c0309601c4680c0c03640a2101c0ba190071682c020410804801800707040c6500d450b607050314194131801e41d03401c80645024091941c401c02221010072040c2d10051414014106658070420010000d000f4032400c0c0d620540322000320052144c03a07820b130042440e41c0c810503003003100865090310701c001d00d1001c9000403014001340e09280664070a0402685114500070140b0b4401440c0500178801035810041c02c180b041a4208001702c44d1a070041c01000340700d000768408400c3e17991140b80905401c85680c0090b14610b42110b000c010034444542980448000f0007001d1064405c1c00b03180600b40c2c051041c000f500c1440303a01c0c081c410400081c4d58102103040080c1142c9040366250075152009060400c0f04001a895040708402030340c54a03002108200780107010400d0a1410070482d8481c0514680104181000c03000c2c4482c0c44002c2000750b001c4031000703151554402d40300d00064002c1603500c589905080c24140c41b074001c0c1c0d0021402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475985530 1250 475984280 475984291
    0x160201021c092d0b040f0605040b0703030b0d150207050f0d090605031e0f0601030c0c080901030e100e03120114090601052104031101180804050906030f030a0801051503 74
    0x684141ca4280303035042001d00407081070000141c040442040030241c01ea0103e0303000304807103003510380d6a81c2040ca007681130515175004001402000c000c00c02130311220b0004c83d110301d50036240014100c60070000040381c014050030060400c1c04544c00f10800c09100340c0c020000180f0a104450408405ca00b11986514034070300759030003042c4015820402e00380100c00641c0d000081c0c0000001d625000c190b200b0b002c0e0000d840e5209401c2c5601d04005940d40c07d4458607650f2040340c203003000070503403035540d942c81e611807000000c0c101030f1180c10340e2072503803030401c49644250314041c0300344607400950748996a40d4200c0c2d20242074401410000191040410420301903e07840a801e400b02a07949100569859024601e65403a0380f070702c2c00c01e00c1d203465440c1102d54000c0d031190307650100380c1000a0703140742950041c10716603582c02815a007800015a862080b2005c0b204160742d5240300d079841100007070405041100c00c1d6102c0c0800104220381036400701c2c0603810b80b01304807442141161003100f215100d002c119030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475986780 1250 475985530 475985537
    0x319050f010e06130509070e010b0712050a020102360924010e0d11010909151205070305030a031b05030601021b030c0607050609070b0703020d140d02160201021c 71
    0x501450940d41c09050f44040c014004a42480a0710310b035208840d000c0300e1110342900285018044142501810b500500b002c503242030400c0002d440d09108080c00841e43c0e4280500002c0d8500740e40d000390159004882110322901c81d0030300c2c11042d44a40c0c42d1540702070f40b01001d10040a0b039246420a14240121400c2c2c01c44075079030104110031115003145215117410700c840c170b000c1000305944400c803080840b44030b504800e540e00c10140000d055100190842450702d81400c519074918000008003c0c210b2f010485080c0c05000b40d4140541002d803190070203404c41c04002030b00b207091a010307002200b10184551405120348031420040303425001c25101c0b217005030850b400c001540004aa500302640d40000e040c0c1c0c1e4100340441c002105d80c0d1040004a901c1c0c1c012004200102d0010b2204800802c200802c0e00d250690a0fa802505c81c040d030380701c001c184802c050312020045070100541e036034103941080031590f542c0c0d00300280040f88010b032005c030f0040c82120800065108001000205141c540c0c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475988030 1250 475986780 475986811
    0xc0302040f120f02040516021528150602030c0f010c0512060a0506160515060609100513060908061b0f0a02011e150b0405031e0a0507060203031905 65
    0x21080d070005240d4000707440602c070344010440580c1c5d80303208060040c01e2601e070107920595101c401a0400e808405101c0c0fa102c4c2e1113041040000c074034600481190220300c0900b10f21103d404244009001c0300040c2000c0320b00d500e10204220350000010500c2c00c1d40c40c1b046812661030300305d8540c00d071680300050200050040c1b03c40a603214503000c5403900441d0040a0702d074031580351800705845820101b591b04150290710003403428070070207001604841100109204240c034241703001c18428822819090b00a941c4901c018004900c42c40c140c0302d52078512a00c071442c2590740e0030000c02092942c011400903008d8600480d1841c1079420081050700120381070541010020505481d10390045010402955241d1007035440c0400500038103603084010307110000d18040301d10304c1101030054940040100706820002802655000134821106038503520905142c2c0c4040f0a4076070034800795141c0240180f25026000c0b03400394010014600c00e0900324600340c030507180c0d00d07a207206450381900c1c824141086c0c0e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475989280 1250 475988030 475988039
    0x14060f0f10150305090c03100203060a120c0e070203040918060c0f0c030522170f060c0d090611031008010510050d122c1c02010519110a060209040c0302040f 69
    0x203410242c0d0020071740c003c0c0c407402e035a4640440e08044904040c0d0100d9076000040101a190624804001d450411062001201a559000315581290044a01c81c580c1600011810f92080003120302a2207081424060321140403060202e00648680c2115424102080400114422504029001803030b58503505140080e8030300b51010340c00107024003130b40c3d07030200c9810302c0340090408001e00520008690140b568509020700703080102c002618070311900f01b10b050210515050b81507803101100c1c40000145c881c01c3d450460024071031001a4054a000881044031092048107403108451500380280040d9541703100301251900a4003c440e800f44100040340e0110742ca4800441d03082c4c001d4205016070100c0e2401504086c0300c02070f0803120002c214070941e00613060480e501101989071450728819400194000380040c000c881d8000c3d10414245502040b66100728100c801c04030081d419184025841d0404402039031003c00707903a01a90400400d4020345110344201c0d000c98034401d1481105070b0a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475990530 1250 475989280 475989287
    0x1103070e0112021b03041505070308040b0a09060f05060a09060f030303020c0c03010203270102090105040918021e041802030a080d0204080709050a0b0f0a0b0714060f0f1015 76
    0x82c900d510201d258203000b5408a40c003440079288800d02c0880c000d40e02c1d141b400320080b40109000b0511810003106020410000790802c8425401940c41001070707034240e60b136010f400000c2c009004058003460400c0000c481c4012a43d101d51300a81050b07500200307607500c1c1d4400304142c40c2d040c800e402c1c0c0b900700a402003011910a6007e04003100e0300c01d042d5402c1c2d1100e40d00107802d90304162460040c0d0324001000f4426a0891400c0b051000201802036007000350310700010303003107004501c2010001615002221440b1601080c00120603600501518041944980c901c03181d001126425000314541060203003201c8030074220a5107158024018003d62007681e40f502800d8105100c0403038032513000e00c80070464000070f0000781d01034045c41200040510704544204251409058058040c242060000010303490b0907800c0b2060b80d080381029503a030082d030310740700d0120400b00d85008d5890050100380a05a44050241c0e40904042c0c10036506a45460026280c0b40c016481484102003c104000161307a00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475991780 1250 475990530 475990547
    0x50105030d0f030207020406380913091704081501030f030e0d0b040b160507030905060306180c040303021e030a2a0b06030d090b070605060d020d0c091103070e01 71
    0x8a03460013604002e161350204040d6520b0303800510142840141041c5500c80144190303092611300020081c0551390803900d0841d5204418050340641d0310143c684109816580007c440345602600341e04403003002e013141c40300540041c040c2d105c0c10300413001800e40c0d54012150203070503250801c90820300080d45640544040c0c40c821450350700710300292005e4001c108480d0a1070f02c9140501c003000480e251034014800520307000685441404814027800c804a42d01400d124191117040da5003540da07440f03ca0005610680401c08803a200b104103040201502c5003030040c000b101e1103034088441100c058000110b241e41031103080f1742036510510113140b645103d034002c5848400340036032201454680f10900d11480340110405d8034400803840601600b4101041b25441c416480d2905110700b500701808490644100480a40855107a201203411039651514454480d540140b5107200c0000354601070003011980d00c16114894603000c910451004040c048034483c0c8016628140c6881c1c1c80e038019955101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475993030 1250 475991780 475991807
    0x1d0a0f111204110a030308041e1e1e0f0b090102030c0f070606090c230301182a081f030c0501030f090b1008120c0c060d09060c03050103020f0301050105030d 69
    0x2010b6483c0510903031290001c0030040d5009076948807041c9030908020395412136604020b501001a4114000440c02c03c000d02140721039104c8090540401c0e50811100803942d81024952100c84a1f241320b04220b0118004104a8847c1c2103600b920f0742c42c007482d0740c02c038002200d100c05182c01c10000844141140390080103080d114180000d40c0c0fa49070346410013119803210b1603501041496108121103d01d034036085808443c2e16a5080c50b56060640541c9840c0c180650b070040c0c2034036607030181d1415030b0701d0951301d1031124486000b1104040d0084024039110081d070f40001c241c403040c41d000031140e400e00481400e8036008040700d0b501c180740100441c01440c1a900000310b89070f0b5800c11400003510f500070750780190800003501c41454140b01615003007454100000304178200400c85250b81c1c0d900840c0503020f05c4400c1398440d80318884d10091030058604242e005094611b0840300401058059121354140c0c3e009980714142d120419080c90b08a8030280102945584001c4042c820340c0d100f00103208003071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475994280 1250 475993030 475993043
    0x11070f0e0c13030c0b030a0e0c1302070311120406170103020d0f081e031914070e010207090507050406030c0e24090a0f060f180506030a061d0a0f111204 67
    0x359803a00c1380f10044260b03070080e40d8071090000511030806c0060062502c40c0b00104054800b50340f40c00009011844000451521a900807414200740b50080640700340030390039981541d00c081070b0003210150a6100f80030791320201e0700d08901c010b1291884001035040e2540604802d00d0a002034070703a1444040801c804642c2c03900f0810140e024040109120ba00146044a5071034030380c1802c410002030700801c64156403040f8504400f16215201c51819590802000c1c1803c089240d01040100d04112040d0060b208141c18a024031612641c0a0003c2007181c1044e5030401100d4440142103904022420280ea030113590381c0356440f00c44803400c244140d030046407240180f03480d4502c2c002c100c43d030743e10b40d201e00ad64101600b810048182c000140e940d0301201c4d03203800380045401101888401d103660054600600011001982ca03d03125800300d009030001410076002d007031800c80c2c451690801211540540c0f0f0420303402d4071403803400d03009080155200380c0956003003540c81c080c80500300e403000b401918032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475995530 1250 475994280 475994317
    0x3030c230102180a12020a050f0406030209040506041b0602031902030408010f062303060f31020330071518170901050904020c01061511070f0e0c 64
    0x414401d100030110039054040904420301943d040040b07490a40d4085200303026440751180060b902d9241e00e00549400700d50405a80c0c5031407004c5002055960002500141400244000d014001448510a40c03242241d0101c0d802d20507a4000c00340314522a05000d03038400d10a0521000200350081c01d072001c02e10489007401c1da0b5800c1142074901c900d04103074169580e000c0600024014100000d1080c0320965080d881070030f0000482e5451600405500d1081d0072a00402e03094078852980700380d032106411008400f05d050400000e01010901c0040340300f441001e01d501003104804191140300c2143d0000b001200e460f107051400c071340d800004116800b22005107607c1d034580c1c0f58480d00c035064001042ea000b44c01500d04e0460700403074403460890314400c0144200c08203607078880101c40c0c1070705058802688030305403206a03502400303d680009201004511541101c2540400c0308001c400140c400c591040b07a80b10105148010180221030304410001d000881071039102c0001c040403a00c110300d8552 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475996780 1250 475995530 475995593
    0x603141501020c090112140304080703031409041505090f0708160210020a0302040e0a02180d061508010b01030b01111903110f030d0b100206041502091c050601080703030c 75
    0x81d00d0007608404080704880d181b41c000e00500544c5d04001761070b0b0f000250b180034203200086d540c03440c0f988002400c0220038545461803480c524161030803000043c1040c044048002c90b200e04110b001c0c0506405004580d00142807080c1c840301b072a00520554442070308a440303000350004505044643c440951041c60000300300c1000900c0100451041d0343e800684031424103014000c0301c503015142061150040c046180800014091a00c0072181120300102d0000b9900d0b01c880039150b40c142031281c0c01e030004000039001e2019006030450050998017000018210b5005441045400410010503800b081410b00500004040420090f002e8200b00d1000e881c491040f5280480d22054a801e5402c04070b03500b40c882c5054082c030640e41d80219014440300d504400002d5a0745801000a49902c0d02080c0c81c000d10100c17a0b044400c1d4a0001d41840045000300f00000061100c1c0d000031034040c03140b80f0000515403000f04030402a640e00d60f03240040101961940510302c600a42464054100c440c01d024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475998030 1250 475996780 475996789
    0x1060503061306050106081927050a0615030c1514210106030908120c040902070602030117030f070f051905100f060501022a10180603141501020c 64
    0xb84141204154008401110301e00700c3e05462069016600b0b2120500034080c219680c448a0b8040e10424100044d490105100c00703200b940c500d441081c0503004107100141805008a9004402c82c0070b00c00034401800c3d101d00c141e0342400c081c40081d051000e0350b85c081c880481d0004044030009000e140005201400c1c01a0321240d912030012030803000c0c504454a90031903040416140100294201000713608065124034116100702d590b039101c02c20348640064066a039007025140540a0380b0070841d200c0c1c82920346a00254801e014421705c800110a8802c0038103000001c41c0c0004400b600454100b0b10395594581b90030005850441c0c942c040c2404140030801c49051a803000d6001c0c0009142100c4080e1039401190480042210198141070040c040d0f039800284940c0f8080d81c28030007001d016070b070700004074031305158007400d0354010010007a04c03264683c40520351903001c20f0504112151903071440d050f011100407000603810940308000281412002003c010303034004041c0182c2e000081d10304c0004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475999280 1250 475998030 475998043
    0xf041a180106030e010903120b0d0501020a021b0f03071208040b0a0507021828140c1e0301080601030803040203010f06060f1706090402060307090f0609060e030c01090902030901060503 81
    0x2288500c1040010070406074107018410528601c0d1000b0040f0700c0305500d0090208003400f0458102940302c000040107511104518110325801c44021511303006100802034031003034030b0001034000c00c9201c8226031052415082c50000040d0080003010450f24140001803e00e04054040e584a0820301c8001400703040c8400421325402d181d6180d9540340c2d02841084204101c0f9482525068200d100300a49100703520304c03c0f005900c4501010846111140150f00904a4602e00c820b6851002c402e1060f268560400b40c1401c42d007984020444c0110034900c40d909010034031941d6400c2e40b00380010801b0179114402980c025001400114444100400c40410345509900c45400140c0d07201c0c203a00400d0f8000400e281e15040c1349403800c114102a400903680c000041d102a104510000c0403402da80d001d0201640180082d20b080d101d02c90740c40c9005000d00e9002e104141c0070480d040300d840c2c0a0315000c6419907049005031102a4828140b0240c0802508000c1031446039669502010845039000c1248 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476000530 1250 475999280 475999309
    0x61b05030c0a0204060b191b05010906063818030313050406050d020f060c011401060f09150507120302091522061b0309180e06150f041a 60
    0x2c00d18a82580306000888201d135110030640d60050090040b111003c1000c80b024090a00d00b22403140c00c1c0c104247c0340d15044c0100140b0b65031070503003040f0802c00103811440480d640b6502c207541078080404a122441d4911454004150188a103000040d0744240030309403050001c2c3c2d080683c1414500401d2a55005600450150713080c240100042d01d09401210050300084e01c041c807950255a010036109460100d000380302d1a40412a50170441d82548464000c014100c400c10095130740d108050850354643c20548009080e00f94042444810705008200100349a540c6a1800a19880e201091486607124600301602080400d0681d03843c458074000780c000407020980c1d52111b40d0749182904500e040684041e880244c03003005806c0d0424504c0d4101e44024400c00c2010116180031030b11540c603030304854038a481c6880c030300030b0444890b44000c4140e44a01c00300d1703499031a4524860014154605a55400f00c00e42540001d11706094000071076504100d441d82c1340821b09580001d8020044846 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476001780 1250 476000530 476000533
    0x605100b0a0e0a360b061b011109090c03070c172503050a0507080903060f0403030507091401120b0d0303020c070906261005090c01021e07061b05030c 66
    0x1a442e200c2d20780641400700030203581d10401c440c985450301021035152824480a00c444820a46840070310558225405104d0001e00169444410340c41058019408000044080d8a000d800c41120900355013190310120008001000d6070741c1c0c6200105655200402540c10442c55449000008805220f000e443c03d0645102903110300300035040c518851400d504420b201824003485502103600b1404a410084040c0780041e81c44655041030821441002803994062050030b040001c0b2039440c0041c14040c030302c40e590500c035070b840e8060100c40c00022806000b60383e80050310798000a42c0030f0402c110b06485000400300704103045200280c020400c0c1d40054010907000110440780c0c41041c032089000d0b210441301040303900c4c2045c009950f003c90524107109600742d01c00c0c0e0301d15a0101003184403d40108550280520316040b1403003601d2303d2458000d076003d480341c00c40c013103d1000003008464280341e98100811210389010012925124180e5032221644146803107100403441c148004d11000d0721150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476003030 1250 476001780 476001797
    0x409050711013315030207021507030201020403170a2001140906060901060f3005180d0c0213020315121c0905010e0904031b140f12070605100b0a 64
    0x8005841001090303480c00a180340803c001c0c84008016071401189165601d001a00d035500e40c404240c6609038841d6a841605000c1005020503034150010001e40b84665903003501068180311b40c0801c1e0048119101c0410510064800340740c80c1502e580d580b12002000205900d02c00450240d1007003070030313a804400d43d0041e008101040c00c0c0354001034010049071502108090080c0001080b00e18502c5100d1604481547d030000314194400403682d10b901c1e205410000342c00c05425900035182243d03003034034140c001c9262a5200c0c50240c240d03203c61640150124249006c41000b0300700945c4010b050401989208100c81002c0d00e411340304042c510005002042020f280c0300002e608104188075010400c01155014000780c0d07403040c00031039069000d49800380c00d03840d07902d8140c500c00c240b44211b1422130050020b80051101c0c03445044440d0031910203541c8842000d101c4140c84c0d103410852081040801c200c8540020340543c05958000d60307164144007400d131101c01c413006130b50015000d13800007200799 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476004280 1250 476003030 476003081
    0x10e2107031b05091b070804170c03010203090d110a0b0c030702010f110726030709061403010609150302090301020d0204171614130612030f14040905071101 69
    0x2c860028014405251501040d450300700000c0100d4001030150303600c214071495525107a02840c041d01c3c00540e01c001c1e04c585450f150842c805200382c0e503540c0448030348182118090681011310032640202e0304400980001c541c01c00065540081c0c0080c4002540729440a040104016002d15401031400b150f030325642e8201060000e007599102181801c00610304540d41d03c05502480032500e0496100b03000a005031500b0202c08075242c003101c5141260f05c00001000207056100c0c9504d001d0b0b0324641c41d80f071182c51644911150a0000740607040104822400502c40700c032510058400c00c440600c0c015143c004981c01081c20380c0c000c0d0f0000742240c1e07004901070007440320f074041e490494480c0800400400311001c0c00c002070b04030a8230034011451441c2540100948030301e0740302c11210800308418092559580d94410711000442807d44c00101640ca1544d4140e21610311885042c5201c41201d003818103100407100206005014842841070052401c40010400e004680740c14589421200311400c51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476005530 1250 476004280 476004293
    0x7052211090a0918020907031503050c0112050f070315030c0f05130905120a09030f29070906030f09060f1416080a05100302030f1b0a050f010e210703 66
    0x190010000c160800200c03140d62400d5030805100705170102c0b540c100070707101e081099000b0422230001503001c2d0f8803100b0100c144100010207012080081ea10140c95032410080c0700d044400564280c1140d98405000c140c0d164402e8000c2c0b95100f5800000000703c139078982d00d0a11025103039100c0c0e001c201650301d0400c01894001466110340907030680178040f503140350f941c2c0741d12000741901080200f01c010556000d090310551506010b1580a000c85001c0d1300c840c2045842d01005104414040003c00d0148050700340312101d8a0107108076032178075442c080c02c1035420b602400c0a84404008555686000404902580148040301020720400104600c0b20300c080c0e20380134002490300d480b4240c07030f0300007510990703004c1c11881d800419880001804c0d01c50b800c421202c03030103907440a5418494492100041200800c040503e1016028100c11001c100010310a031b0454074441c4550050030b0b1010f4403665401408200c005e218018000c940301a500c4688084070103001c003408400c1d038800d00f41402003001c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476006780 1250 476005530 476005549
    0x501030c0906271505091903021c06021603050703080603030901050d180614150306100b030910060b09031e031611030a11010810080705221109 63
    0x2501c0e00158007424804080c02401c5580c0705840d42010612400d55420b14482401014202030400849000b0012100522a030040300310103100f003a0b01034900150407681c402d184122680a055000c0b0143c604100c02c5026100c0031064030b0311a0200a480c0300017a040c0c0b8102030740343c4a0780396140c42d01220f0a00410740e0030014002800396004010b0011181e0f0054280d40306409082c0c40404c503900b80391101c0818a42448004003120b0030302039821220000c00c0140c038418103003802c1c40680351040d90200741c0e48000544600112884280c018003140c105100115400120402212580c802405502c000c840ba0fa0b40032816080010a601d0120324050040580740ca08018002c11900c05810a41d0b450b171207500c004a0f00140d14030104010010084400c030b8000c040107040d00e000c8202d07818040302d4000d005010a000030000b9000828102e0469500c90039140300500a02500b414002801540000a01c0883c100140cc0303821140083c940d029062801c841d1201c86501c0d0041c11040c4002c450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476008030 1250 476006780 476006801
    0x7050307030e3009090106030e0f190f0f02090a150503010207110603040f0f0f060609020313030e0f0306010f1401110a080315041b0e421201050103 65
    0x10003207a101410012000840b2442e510f0300e812120501c0980c03540740a003480740c41040c43e080f680d9900002050781c2c05600492907540c1c901c0944400340110004a500c0b50031042d100041854042403081c0400c0364800b25244080c81020000120780d19030b00002d2072000201d0340c4845180c0c4800c1134940394105183d01d100144001e4000f982804d00581e42c40810318250350300070b4012100030001034203001121a010454581288140d2900a8242443c0c2c1c62412415420340385141880000550381c602403003228801d50b51040c1096242c850356600308c0d1808401e8803000e511500c7c1b104201c0d032a540c00e010103402000d0b103180d000000c1c0e262800c4c01e000303031a41940e5181070140c82011b00003100d41c04500e400c110b81d406a0384695959078204408032222558007625040b510300640c488405140044507115040c660300c84c0e00c1900355078002c000c0c0391142640c81e04421a4000c3c01d50201c9052414240b0004610038a0841060440013840690360130041455010010701c1d4010009540c0500c103030072218 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476009280 1250 476008030 476008033
    0x6082a1b06090d0c0b180705130b010305061e04090c050424060c02100813120225080a060f02070602160309050402270409050303090d080901060806070c050c0907050307030e 76
    0x1c80c1c0380c68902054100400381501c1d80907402a40c1740000050041d20701402c80241107e01d48027480000c0d83c01440d0b1501480d02007440e10000c01e100b0f1424407400c40412445451400e540180e10040c80f000c0c1c401c100b4104c13015190004003007026945d030b00454400007144801031100140e001c0c80c14640520540c00030052002c11440e004c05a26150b0107880400302609003500c89444942c05220034880c0f01801030301c00c5550044420b84280d0100c1c003484a003004980c81064194030140c046040c9109119925a03580940304401c001801e0360403440720399000d0303440141066a2070701c1c2c030380030303070b030040544109040142c1e8101040641118446024280c00e40b070450515601d440781c01d405c0e1007240c180140fa800002c054203407a40e100c0d0840c1f00600d0b44502525104e0070207040882d80c1d04ca81d1121200032900b400006441154148205030850b06100c0003080e060302d6102c004c2c2c1d150701400c903082d00c480c09848082d160a880d864241409908107584041c1c1d01c2c1380281b070060484000d072410154a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476010530 1250 476009280 476009297
    0xa050d0f0501060c0209090f0a0f060b19090e0307060908040512010e06040209061306030303050a061a040317070c03080703261503070807080f0706082a1b06090d 71
    0xb080c4d0020404114030703810345a9103006c1d166075040a00d8040840c4103051944200c01c4680100411301c68404c40c807a200d19803d0203405450420044d1101c10720200300000182403a00304420411500080d041c1022003064a14260403602e88200781d07201408141d0780050001010041c5041055074820034603034503070081000480d0007407095119000170b000a0710808075403010500d56682c0a909103019880103d040006580d240782c0980604801c549840e072a40c50a080040c07884031218034401e0304c100b02501d6074901030460742c4d4503a00c0a101c0c008242c1040b414070011340000d0405e0b05541c00346001d80a125110b04403890014040c0c0b04000409140e556608601d4140c0d5940390740b060340003814550003242e80411032000c20701d0890140c1c0801c0355441441030000300800049120306c1070b4032411081c0d98a881d250041507410103000c0d980700c0070100031140c5800785200e4003000105d0200007801c60070300e496024a4850a12040b00184c550207070402e03c140a503518041007000e00000c51414240d07071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476011780 1250 476010530 476010539
    0x30a06061124042102010b030d090803071502160515010609051e030c0303041415030702061503010b04061d0609060a03081b0106081011030f0604090f080a050d0f0501 73
    0x7002401e501209040740703910400f040404c400002e4020000d185103401401006410700000d01a2040d090074900902440d0130000d6103c1c0304800342d809941500e80210f14000440c1e507404402c000d07442c003205200e0f500344151003140b881554150552030180d402002c4400d01d40f2030b6255080350603804242070111000c5d040144d910381022034040c210f450a02c0b001d190650710042070401401c40111030f850702000502058400344900480109001520b40c0c41b000806003503944031600c001e58012000d64884c00c00104000514031080030750b80700180000c0340c01a07105020505454a58002883c41498088900c08000c803081e15940d03c42001c40b1400504c0c1041000b09501c0502400040c04240000840300c0c1d00038514807e2442118101000f004056500c0f0a2140c99030300815840c03c0c01414002c00c0d40d00201c850041d80d0141542d001914404d450b49020440200780c140000c44015120107a00004141d80304080d12081400380c1390a5a68040003480380d040340e802c504211004c0d07240900621 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476013030 1250 476011780 476011813
    0x62018060414040203100e180708011103040b04030207030f03211a190b070503042c060907021606080601031d030f0c0307050f0a0b0105031b010f14030a060611 70
    0x603010200b5100140d0320340345d06c4008141003045d81c05c548a00030030081030041c0780441101c1035403690442c8060b0303042c3d00e4485c03011070300780c5003a0003800712400c10030310200c0c000c9079000d8045a00140300340101c40c25943c0d6540c8450303200001c0c3d4400e5012965100d070002c1108030804503801d6010111604100c200a1030110f04601d10301c1c1e840c038600070601e089400d699582541d0074107003c0e140003008503172944882d140044e45c96115002e05440402d2036080484994030450341e500306410940d86000c010303518182440305003040100900218402ca0410720b00503842d80709104090162a0345440d214944900050259900100c0c0b0004407508000c1d400035614001c01070b9401c80f00c0442c0210717990f5040404051a601411501070618001c40112081d90311f4005090004e00303102d60a512526aa41c90402d0788070110340306042da034500e1101c84041150b1190451691031692803c0041d10120344210050054000302c991180e0160380b44010720400350030031080003240321503000400142d4030a90482c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476014280 1250 476013030 476013059
    0x102030c1209010e0a031202012a050904020d020d0b09010f06021203100e1501080f090316050106090c0903200d081c090b16020105010803070b040620180604 69
    0x1c800554001c6080481d50384116401288150700034412200c1503120300705851040e034450400c801661038004064640b000034070744a2112102d082c00107150340540041550207500810545502c698200001c068554552010f0300041c1c1d0009400141d41c0c00403014024041e1044c2c000403014a00c50604006866001a103c0071403c445001c151301c03625000d00412003940b00d81c100e16a0718411030708015014a208002e4041c0960903038600805803a102c2c101a100d02e41991900403e4200700160b0421240446540f14a507114400018005554400d08008c0f40c105148400000742030440810500a074001d40c4c045060b0346012840b0301c86851800146100300000008102520128035241d0443c40b1103101c200941d511941070260034141d1030080454001102c88045449448503018102032052181505854a400044d494503c96446040120000601c22281d013501d4040801c02c0b4002012030303200a801040d801c61701c500b81241d40440303075240743e480180107810600c0100000720540c0b02c034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476015530 1250 476014280 476014303
    0x2010e070303180b040803120c0f09010e0a1707031106040f030210032c011505130f0b100e0a060f090603050403031b05130501030b0643020108060102030c 68
    0xc2d07144000c0071481e0342c01d003c18590000304102d1001c20000b501040c04002024100c201440b081e001c1d40d540b01c100140c9000310303009010888000d20240a60354003c0d005000d40002c0100145441562683c4d43ca02c00c011841400c0e0b0a83c200000810402c6460904c100704100200e03a442d00742810911004c1c0004614030010303105811600341601140d002c1e078484460080010040e54030030310320f1b80641e003000b400060120600d6180c030040c4a8440107803d800426030308010814258520f0440500020707124040030488540d179075010306101a9509040d4032541005c5032100f084250714070007041280e0010368800c105225400c0e0642031030980c824004c00035582030342000502e949031030800300c0017021040038848171111000355207504c0390340150150800c0440c2e500e8415140e9100c3c001102500c514041264101d070701800210002d40c005117000f1001000b000c24088442e003491000d0010301810aa0000c01c0c0d450701c2506000c0d07590082000d0360240083c0010361600045010880c0d4801356040b2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476016780 1250 476015530 476015537
    0xf0108041a130f1b06050705210d0f0f05010e040b06090a09050607170a020901050306060f07080301030f0c0906140d030e03030a0504080c0102010912030e0c040614010f02010e070303 80
    0x4800c144039840100c605030b000400c0d808645424a4640981007004d003481c1003420300340b00000340703251246040f03503940c0e5400005006090035084018050b8182008003121400c1d0900072811300d007200d40b0540081c9a00c0710008280348804140c00400c1358010f0700200c8401c0801c10401000c50101c07030401c0e821840603a074043c086e039100d04080d8010300e41020024698003c00040c0400701b60720401c0c280704001d604d00108095129201050b040340700d001c0100b800701b602840051018079000b000b800b80e002c01d04000510340100b540e200c22540e442600102c41184140303103032005110411410320081c00020004202280c00c0c51603201000c0101c00301341e4450b40607114601c0426204002041c1c85147c054201d0f61505420040174201d50030a0261800c94894811303400c039158414050703054140d030004908081c501e0041800c8000d0500b0003030500e030501c201a00801b403601c56214400041c1020b24501c1c01100c2e00c0400104500f0103142d24a045a0401841c0c190003039011803244200c83c0d1504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476018030 1250 476016780 476016833
    0x120d0f0606022e0507030c0f0e0d0305090d0b0106021014040b0408070c05030304060302070b0f1b0f191e0201060b0301050d0c03060216031413062d020c0f010804 71
    0x1d40f044004002401100005050809000842e6090781001d041c000c015100c00c03411446081040f138082c55803840507039000004440e02070220b8080d0000b403a06203000380010000040075104c083c1040d20a905c00001030740a0420500b03240da0520440003080642004180141099210200f8201c4045d002524004000400400300300301d0105c018000c02000c1e094940b100e035254800f50007504400800d40e890b980c00d5001980b0000d8201c46603214010b48011031880300e01c0e001c0600e0658120140c6a240b0b860b0820050116280d4552282c501c500c03941d42c1c1c21102580d200c0602090709401401c0c105584c1803520a0046a44130340c00c0e24150344003561044508880c1c0e00b0001c9940e0580d610107080c031840051222581d03281c840c08820303041d0207034503032644140c022100c008107071180c082c00c10b0034031100702814440e0600c5161410303945046074403070701c101407076200e400c1c2d0008103600301c0d170710150b804007032540707110f092002c1d103036141a10074202402c0610f8280c4401c40c400c00c00c045820346405004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476019280 1250 476018030 476018083
    0xb061201020a3e0105060111120d0c05070605010803030117030a02100b030705041e060617060d03090b0c0a03030b040204060215060102070f03110a05150702040504050f120d0f060602 80
    0x10200c00342c3c0c004081841446004815056008060694606000400f041d200204090780017454803010a04c800c8000d180c20300801c0200b0090246104000801c2003c04c45140414002e000c1d040c0600741860103103680c1e524121076003034000307092200035055030800d001000001e03401041c040b02d482c100c8400422050855800641011910b401c0203500c01c1c0381030250702c00000e44119440c0203200b070fa0410085581c58800580300092501801e030744e00c039600400641c407803c1070051028030038030034141003051039200d020211244e04411010f02d015440b5940410a045c0c0c14000d0040002c01a80e04601e8603060442c029111245408500903d0300d012000c1a030710392080045800400f000066141150780300e151140c1c0000356004000d101d411000381c00300f103d281c4411a12242507614016071700e068029401e10010700001442500d8030302440841d00780b012400d001c010180008048416962030905145004a41e818184100e20328a0190705000d01c58000400c8854000324120380031180f81d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476020530 1250 476019280 476019347
    0x601060e1e211002090a06090b0a0c0f020406120b01090c0903061a030a08043f0f02122808030c03150402070305030403022a01050d0209030105040b061201020a 70
    0x408415426124490803000083d2072907010b04256041140d1403030580741c0e154002c039003c074103600494100800c10400c488401e4001c0c40c017042a640308482260000340241c00040488140703074400c14200c559030b800e043c1040098010180504141b071802c124110400000400e810349500000345460340d03810041d00b061203004a131a94210b402021103040e0f8895281c0740005422520951496100100a0100b0340781181e42c2013030080c1350131641c800003d00c2030083e1144121405030130785040140d98445005601e07144803184d00480450700401903e841c81500c1c1368114801700740f20404610310510400040c50310720860790060030340545207443c1e8071404485000701c0c000a48155010f0320000f21070b010540c1200282d881107002e03400b51200703000b517412403010321000d0340004910b03400d40944035600ca40c0140302030b10000300045401800d0603240008642100c00c161800d45216440004028803031030140030020304002c00d03100035030a0a1300264003500031503803003c0c151407100c800070a40d0b40e5081c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476021780 1250 476020530 476020579
    0x4031e02070f0b0705070e070c0210031404030905030c0102031804021b07062102130b030a0902040e0f06010b120112080702090f0a1104030b06090a060e01080601060e1e 74
    0x4140784000c003660b41c2d800c011482e94840c0f4022170303041c0260640045c13242d0010908500c19901d40c2c44210155a1540c204201d0a1807564880181039450f0303007140c1181d1100030034a100364469220210482c0c10181010b16080b00042003c0c119801000000e2168820b04900507000c5000d45026803190b841c50403188dd2920301e40d0801025118001300090310540c4000b03910794280c24042c540d40211160b06002c0141c3c402e040c0c80c05a1103000c4c0a041040d91810300080d6071022550703100064007152680083d080c0e83d2a180c04541c03e61120404d0400040188034040c01070001401d01741c50820000109020110f05100d0a4254070300013521100b40f100800c100d40f2040e80c01007030356540b8980000c035003640f240c055a00786140c61810401000b981302c00d030100c0341920f800508400503640c031641000b1000c240201640c0c40152640400a280ca5464a0b003038040c6c11102c7c050301081d81031141c020441482981c51130b12a0085240f100c100500324060549503627403da402d002e6151094091a20010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476023030 1250 476021780 476021789
    0x9090e010b0904290103050c1e03030f070c061b060c02070512371e06090b090d14070809040e071403240708070c0f0b0103110904031e0207 61
    0xb14400c1104001000740c90130305140d004180e000105036005001c3c2000b00007408010002d0b48030394800590380c54201c1c000b8802c80001c0c004103403000100804281580c1190158484851011035010200004000054080c00381864400480c0b101200c0d2904003c0000c1009416a980c9054180410b407007440701a024220291031441c0700b8100c641c0a0351360311061a995a00c441650000c281e04d0801c585400244100104610740c2019a035141c2095a2036078410400b1091615000030780001c4c20350003096440c600172500714000d0b1030445403443c103261140740e07403904104624402da08404038904c1900c0d48036030002550f980b2014050080741c000d10044170101e0301ea100f12400010180800740c203503c49088290103072039094100c0f40403025071260b002030400105400d6800251500d10031038105511140c1072506102416042e203a080100040b58070079542031541e03c0050040c011345000007009404207480610442c034117038170020304c2c4050f0101d140902006c0314001a45003442000003c0241 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476024280 1250 476023030 476023039
    0xd0504030e040b010f080604020a02071a041701060f0b030613050c13060804081204020a030b010605040509092e0608030409050f09030406020714010309150905011a0109090e010b 78
    0x6040604014001009000d00e080c0300d1424403903000c2c00c95102e4082035455180c161a1281c140c0c0f511010000a9000752580c101107225403030000039485840100018820681e440d02940d450a00c0100325540f110f04184034042e80c10f000c0100b01e03285018403a04200d071200f25500351a601e8840000389200c081c000b444600505080038010119840002007110582468840c2c0040750341d40c2081c0d0300301e0702c200c2d0007400c4006d003485040d042c00f0001c4000c5520501c010312105c47c003600c950b41c007400c03036500fa0003803000504041000c2c030050900c075014607001a2058000d00c6101522000240010480140c144241400480f40080c150b5140c02450240a504003a00e89071501d130705424005140494450980c0380840c40452a0a0004001c46041d50100d5000d040c105040c020520600c48410b0760650400d070b5035907040300206802d400c50907007480b0182c0001c02c00581c0d81c24014291001c0d888030f1410342a003950101d44036038114401204079040005c0210b41909442c030086d00408019094a401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476025530 1250 476024280 476024291
    0x30e0a0e1f1e0807060e06120624040602010c0804020d03030e071a090a1d0a0903020c1c050606101205090102040305030f130f030b1f03022101110a0503011a0d 70
    0x20380300780a0945030300e43d003200c0300c00f661900215001e481000826421800030080c15940000390416079900c500c0180c0303522929040c0409a120140042c00b6500114078041400d00c241d99080c0940310750b003d8030746042d00031818260001440400c1d840c80080c00e00d961b038920341001300d02c144040c90042000c20703515210b421440721801025400907441611488841c1804180320b11420594003001403c10303a00d054558580c2030060041401200a4040d4440c01c0e5000c402a0307202100a1011001040364407044000c916059203801030281a480c810307500012400641d40d881403422418115a0740c0200702529000f02e00d500a10031078002400c1c0d800002070581c9100103420041c00708400c40d41318481d04556443d101c955026040c0002800f500c2460003107a140e201c000e8440c01c04140c03007946108129075a44c001402522480f845a42c09042050844003950081c0700f058182a80e6a0b1054079028185034010018401401445140403088680c0d20383d80c0030132810350b14010b4004000b0480c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476026780 1250 476025530 476025569
    0x30106030e0106090203010f15020a0f12020607140915211f030803041709040f2009030a0b07120f05011802120f0603150a09030e0a0e1f 60
    0x6080411541d410560070182c0c00204540b20784202d0b0f0480348001106000b41e41001c00029280d07550794030b100304512075000810302140843d201e20b80210310800c21111000c0750703400d0107802d01400900c03407000d100d0303000240b008121480e02140e000a43c00c81c1c03000b03a03450842840710f8a50058000c603013407070003418690049000351001d406015090182c185424050015040d07240c64526010082075814180041400182498159800b03129103104507400c1400d02e5000c6070846c1c1c0c400600c101015115240144611481800c00804d00c1000401500d03140445001c242c0d6402502c000401d000083c00015060074070413199103c1c05505590280807031310781c0301c01d00b0340608403c0c000c0711807400e000020441001c140b88220b40d14050062084181daa80f200907901d0102c00c000e192581600880701d0411820b000400030b24854041e85400040c902c095040003464507110203011070080c003c0b09002c2c803070740d1854029142e000303800302500f03151440303120f841c00e400c898194002066100781c0c0c8004003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476028030 1250 476026780 476026787
    0x604080408061f03060506060702120703020a06030b06190513120c09060e0f04060f0212040b100308040b0a090e091e0601050a03140f060718050a0605180d0206030106 73
    0x49490040032900c00d9191001100c943d2026059400c0d0942c00f00d410401c0040e4154201a038003e02c01040d00f401c2aa0715004284c640303101201d5401d0940007100140210320705800340c0e6010300f40307a180030000060181e000c1030081c03007450001ea89140307220f07a0b6800312503c00e40407607220b10f40421024042c1c1d40d0302c00d03101c84070f9003014030200c9200503040c0022880000c0f40c801c0700111003402c824061a521913034504098040c0290094401545417103034204400854002070050000036052141e030351400d0b04000200810160112041c903181641c100003044205095070103444a80740e85643c0c80203e1001aa00000c0c1030780444020390070101000700d4020f01280240790300303203440b02c241c03602c8032000c0300c00382c444909000302d650000f00444c0520100d00501340c01c9c01680c12910031541d40800c2e02480c20f01e0084206d850b60001910484890140c00c105098a001080d095420f00f0503a410128090b00318020342d21103488180c50881840f1725a640d4080c0403d0054000d00626a80c4d45c5615004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476029280 1250 476028030 476028037
    0x40602041a0d060608060108040f0f1b0512010b030d0f0504090c0c060b0a060f05090a0905090d11060103050c09090109020a03050d030e0a112e0f030606030203130b1008060408 77
    0x56a024600fa100052280c02854054401c2105030346040d0941d840d56184021200c518009071078000401e51108001a15401c900c983c60089400403ea114500010458405034034942005680d040c40c0c41c80f901c40d01c00165540408540d4144040701c100d51100440c3c05018690082d03103014206214455599000700300b01d0a1139000340000c2c007800c0c03024014850b50041e140704900000d0708800d80342580621034405000100c90050000c8006030361181c0700b03429100c09442032049030f006244c03c1e102e0a40c1129400c8041d1442102414166140d40c8990b1b4644035002c0c4080d01800054001a0645000b9440f0304100c560003000740481e19102d081c056504d015580103280400e1a03e0b003024128140000c024500c0755004070b441050f440801e090086a18510680c03200054041d03955070b018410000314109103003483d944143c05017881d20401000d0750380c039500020505204105008a402c015201071b01c070540c009007440f40329202d81d0344e4114241034a1380120460b010307800603c400c1000c0c01006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476030530 1250 476029280 476029297
    0x3200a080913050f190e0f160807141c14070e090c0d0204090309050307030b04151e091b0605030f0a060b031f05150d06091e05040602041a 61
    0x14007040d07000071045022075200340c80c002207411301e500004032001414441501344040d048001b040441d407030f03d11145094a4062284043c2d0042807501c9400c05103580c0c035200901c16840100328091500c07610f021082004400207018000e0040484000c00b010140350744500d6220710090300d2108241b451030340ba07801070b01400c12440b85180c0459441c420001c3e110300300000040c180004806a90308200c0281140f0348110240b040e507580c0010305a8007482080c1c015806081a4000762404c1d10302041d030f10000320309500501b86010200c0c22645103000f81030095a010803c009440c4501b81001e88030b0002d540b00b41c04d084041e071580441d2055106003d1802803984100d00e440c50b8440c680003206032401c9010340050400d007807000030050601d002a500c038401031990000c00294035080450311003803450076081c46550f400108007608400700c1c4038240091214810800c6014101071a005540604482030140c042d151000729007400580e9045a0091158059141c03d00c0030390007000303e154001065 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476031780 1250 476030530 476030539
    0x3031503081b0d03060602030a0507020d0b040f030e0a23181315091a0c0409050103061a040b03030313051c020a05190807060903050903010f0e0d050f0703200a0809 72
    0x8110012034013034003a403010303a0b10a401550901c0842d81c01180d06400848003641e00040c891004c0001c1800140706a003d24024110040e404076142406000000e6442000c3d01030350b51104100107101000341c1501e04500322140c1c05942c20071000c00039028541c5204220321000c2c0c070000340a89140100803c44000d4455180703030081c0580403100801f02c2d001c111010303241c41340c00070010502c800c0204400ba400100d02e0885810aa107800640c8101d40d000d8200b11401366136261643c001c2807017415184e0b00c48038100c6091010491100c0442d072280000303002c6511403143c0d190742da0700b00a024009408071041901c1d08980448407210020355030407208100352040e001d14a2008180a07d0322413004489804c000304a141c000c80f655180014450364209400300030050104580968080c000c00304051b51807840860ba13884003810407400c1c20755006100040c407a00b0024004207009000c00d0b41c030415014140a820480d2802a01403882c402207102c06082c058110786800704104140a000074200545 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476033030 1250 476031780 476031793
    0x1401050f01050a09090c090b0d05190606050301051e0a0e060907031202030f07020607020402190306080c0f031f0b0901120308010b0a021c02010b06070605010503120906040303031503081b 82
    0x12840710807541c0175000501000e103414030621020340242c210701c80d2440080c000e00200e82311625101d0503c4640100704a241215401280c18000680241000351804030020005410030210b980e400701c6036903010b41780c000508800100034410035802500d08100c0c007826261685811f60003191100c2c06030204480c0c0308000c034281090305100100b92a0f4214040c900b5a01e030904075000c00ca41d80e040705100700d03441502000001e042d0b1740e803400140105c0000341c6020814904025200d0309100070121818080c80e0701c0342d03074070000343e0b03000072080b1046650f02d811003088440201038a024180b00d480c4681c00000210000800c0c903164110302402c14040c1d42d4642590362101102040d500c117421103034005074403c075650390b4404074860f60381d0b08000007800001100141c007070100c1c1054100e0001556126a0344004124500781407094545c9403040310041460708800100207000c90047d404041c04155561005c00090307448103005401450b000f49405031100d05141003c040446103021a40a134003d12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476034280 1250 476033030 476033039
    0x20606150901021b04110a031d06060d1707020603040b1006080c0a1107080f030c010605150708070c1a03040212060c030c0a03060b040b0a1d0a121401050f01050a 71
    0x51064580401e0705034081c0c01c070401820f80400b52021002c0245038025503a40c02920b40340c3d00c0130010001d10f221914041207410854207401c8444840f08409030707a5804c2801004002d0790307040d038200c00c5181d025240300707801922079401c1d10030b5000d000d00003034011000000b4407083c805903000f03491080c16078100101100b46c40d65403c5070881001d0310740c00c4a840092200381d80b001c1c054410028107124050450b810242c0d41d000a500e019840c807551030950700002001155102c007070058201414090b1040c040c4802c0303181c0707000d10758403402401600303003040440d03003804025903a81c40c0300040c8944c1d0a0040d4118040340c9070602c03a4420f81b01203109140310010040b421102246091240e008440703c81d04564807c02c00b54155030004a81e503081642d52000464000e040101810241a5280207587c0760742580e18044c204a84221545e02c808090482c0d201041ea50b00e00f4040c00e031210001d0b1038000190030700c2d0090380f01c1c50808160616509000800c50001c0001d50802c2c101c44044440031390080d9070f07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476035530 1250 476034280 476034319
    0x3151e090c03022d010507080702150306032503060c050d1427122d04080712210314042001030c1d0102120a08010f060e0d0b06011101020a020606 64
    0x40c00c808010340c8250f04c107540c1c1158050800340030344501a0408500d030a0840e40004c200c8241d02c100300301d03d568088241302e02410204440e20240c1941162901c01c2e0500b2003102d19040510311000381020b49400010324150320440c1a41c071006241d01003882107085120001c071102d2012210610524100065180100d45207000d14000c0d03104180a400e42030310a08940c2c03190f41c00390201c8200072000c01d070703000711078140c5540301a10400071850561f01d407400e00c0360b481d0030250158031550108240b0085e800c0807a250718000040c400380b0010791340001c2a6620203602a0011b018440b1140718003004000610041d0380c01d43c078188080d030310480313180e200b0900103500b2107000b110280005140d011842d0390542541d4490b000302801401210000b05210220f802d56500c4107010701c0001d030132803004000200400c14000060701041c201001a04601c0010400840306060041d221802c110080f9400b1b0340035440c031000e41100b800080d551071410000103550341c4c0050b108103014810326060207258000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476036780 1250 476035530 476035579
    0x1c0903050c0609030a0533160e061e090f010c080301270e0109030e0103061d0c0c0a0f030f0516060f1509090201180305120f21011d0103151e090c0302 66
    0x10354012481100d00341c0c080c1219540903140c5d082d1340180f800c10135200a00e0901d071008101da000782c00b00c0c503920144cc6007486403d061401100d0b052080c10220500001c92072026607056440d03020b145104400c03121214564a60030600c00b403421480c02c1001d50304960190003480c1c180e4002e4170340004204001e0011821200c1a01c0b41c620003044140d501c01ca00080d400e4405c7d0022600007209003441c420440c01800c2c00280b0008641440c3c020b41e81d202003540100c14a80c03280d6071814481e0810310810b07510340c205442804020003190383d901100d02100c42e158486540c45003900440c4070b100d074a511900005040402c4140d0220f0415540d8440c5040c2c02d10450080e00da01074080c0a40c1d1510580c0c1c91b010360054070701038443d48410b0101181d11105221409034240c4908900c64041d40f4040c907030340420042940007556890350100505c007242002050724041e603400400081c0d0380e81800c890a0031445802007401da62030030800c1030740034004680d820806481c02100c83d24412180324078010039401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476038030 1250 476036780 476036791
    0x405070e100c140105071107080307030203070f02030a0b01080120070818130905060a11090a050114090a03050309010801080a120503070e121c0903050c0609030a0533 73
    0x40401618450692044040071581d51091039000d00f60042c00342a2400d40b1012034070900018400c03030344007820301e07010800c1c0c0c0e00928251010b5440c100903602c0007912841580000381c8556070101000e42151000c0120000050300495512050358480000d4bd0207840351441020f0510001e1060011301c2140340b04590540d940862440d18200150b1441090700b00100d036550783c80b66031583d20f0000e1492600a6440080c81240a08100e01e01113134034604407010102c66854100e030a0051044076141c0518140c141c54003400e00c0080700c0321a40c170045040c0b003089111600504003000000c1080300010182c07942160980354038110340e03210300c0101d81d00c14800c40041d09032041e02d015032454502a000951f04020f86103404c84020440c40040f510410b8040074603480f0358801309024610201803e107001c80e8590a28118034040d00d0f40e110f580c0e682c943e030300b40c0c0c3d4801c42c0000340004c0c050350200a1900680d501c0300035a010811005100103105c41501010003141c40320740307041506020702d00700191184 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476039280 1250 476038030 476038039
    0x30c050705011b06051e04050c15042102040f0c03060305010501080303160305090a020d030507050c0f0303040923070f0e0402070b070f110316020a0f06021906180c050405070e 77
    0x140154a8481c0500170203411140104804008100041e4120074414403450064000300400d011070340a00400700c81c040c00f02d03221040180010b10100b211107944142d50315107054081c68138409400090000c1c080358011304500c42c82d007000580a07580541000c01100d0282000300000e0780e9442780c0719180c1c80126141e18244420719010280c041c06030340100d40043d204001c68110102a5000c00c5000001d2102075010480200e851400c110003008200300c0d1440964031401418415004030f80d481c0114069016400c1d1501e04498400000f4100028141c4401e0496001410401809440340c003460748107200048098461a0310390506000711403043d40d01080c62001a40c0d148412a82095803000060070000011078074003052030104003a25420142410050070400c0520400040460a90001440c051600c00030070090f070b0003262403400e1100041c41e0000b0289989802c07002401c18141d076032045054111610244400d001d13210b03040d900b0580b003c03c0b407522109015030300d803071101a20300c0d0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476040530 1250 476039280 476039327
    0x30613030518091003231c0201180b01050108070e0a12030509030601180c1701030803040201090b031311041b0e06040b160201093213020304030c05070501 68
    0x80d00c203400030302c802c50105501c2e0041c801e00d80700040c0004001c1c4c0f5080346041c041901802407080039240d00c000c0c1940031003c024680d002000654442d1204051481d400c20b00c24040070b4918000c3d00b0405601100c00710b14000c041c40c84ca410001850203018550008014000017030714a0302030900c2070b808640007001c1000311480d120b03041d0588000b5100443c2000018082c1c4c0031580c404202e054080d19100030804500d0550300e00a10850380c01004a82c10484070042c4900003c9039007030744a0640c0d400171030803036480d901da00041c0c40031856a444032440700e1000040110000b45507120990191144020f406100502c5041205443c0524289114510315a91846909000f9028901c0000c1c1c00741c005410680d540c42e2426540c0c210304210f01088040307819110440da807000c1400064850900ea8008080340707907d80320914001c601c080e90103540362110120081c4d030f46203600d03d2441d400100656481c40c2a181c000c25600e0740000440e014441d0f9103001c103856004041c00900003c3c02c00b2000070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476041780 1250 476040530 476040533
    0x9072d08060a0f030b25120b0a1a0a0521010602010f05090d270602160906030512030601031d0a1709030c0105030406020403060c081b030c030a020d0608010f060f05030613 75
    0x50110002c2c2160340000a90851280302922007000d00140320219161440c0411906000c21f05584124000354411075200c03206200705401c600d2403c800203411041a902e130100c8500945135807141c110600300c4500200291441032480d401c007103060711140e0b8001d10004070040c2c4013005a60084e0b0340218590040030f04070312a94404d114000a180c0074144800038907610985242510f00d040d0001d0005802405d40052070414002c0b0200080c4115071041040c28038503220316032940c030b40c03003401c0141717900000104d45260b00c290020013424915084e0a250181c4014103140e85035401e0204a6052103602e0310400d07004940010f0301c400c0180039011700388403104100111500d60004008550a0b41e0920011011500c1032081d40e00003e5140c9031380c20b0901b40010880c28412455072021036091042040040b5006000c0642e50400990b0310050380358070403008280090f00403900114000d40c40c00462968103152600403404031140c2c11041c458080d140c2d4145625041d0444034a2040d040c810b98000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476043030 1250 476041780 476041793
    0x3110409030e091e0114010c0f031e0302030a0b0a05011413090c0509090a0204060207120503190203030612010603050a0b090307060c1809140609072d08060a0f03 71
    0x503615200707281c00d0030354260301800580d0121060f110702070b002e50001c60b030340705160303507400180d000d0800041d140d682c002444000070020960110020002400d0011640c03c0500545001980903450a0100311244d22680700900a4000b21840f01c0c1e2281040080172450405401560641d841a502c0c40b00c140490b0140d01907a078401109012010180c420004105000744200001020b4554810f41d8480c01103042180440c009084450366602c100000c00810b60000350034411190142c08040c012109824840e007035002d02c0051700e04490f07914403000202907011004502c02d5000700d841c0c0c4a11200d40300600d00700d440c3c0340002807442d400b84410501041c40d50b80c425600100c450102c03072804030316030f89803815560a107080202040e2203104115942000312905c40203802041810080c1c0030b001c060004100002806940c010700e40c090204030742c3d42c400c25651582c4107070164040b00041c000c410840f40005090722040c0020010008101180b0740655000212417062828000c041e05644404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476044280 1250 476043030 476043041
    0x90702060a20040305010203070e01050f03040f082107110703110418021309021c021021060605070c0e100b0c15070818060702030f130b04180b0406031104 68
    0x9401208181e0780c2c09120024400041c0f02941c0b1501c00540c80c0d08000001034000f10b00300d01860706000f010b00a80b0b40b480c1a80c015030f1307841a0003000050481425080c00692880790741003c43e007010032894290740c0c11200e20031a82c01100140e03140c0c08032070520610192601d80302c0c04020a004440c86a5158620701030300f0400d41e808901503078110700d601580c0050031004c9900c08184205031102007000039803403c6001b05501003003480ca940c01c01c1072903600103901d40200f804941d0500002c0406031907170803620031040035900c05c441e00030044c068030f07520046c12540005000322002d03400d22070085079105c00510311501030320b8030445268155040103207000c2d09070000b1189251910070684e1400072580402d11107401031445032a80b02280c00e04d8440100c50000300840801e0651000e402d00840540c000704840d212181854140e48401614000c0c6c807020780c0e16440303c103110201040118411a0351700c414504000b803030700c08200c1242c842003400160b4643d0b02c8003030301e0341c01c410452601e50700741364208 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476045530 1250 476044280 476044301
    0x2090d02010e150307020f0616090504020304060f061205060c0a02061306110d0204061d01050414030a0b1819020a15050c0a030e030f011a0d080c0109050a0c05090702060a 75
    0x70f14580741c1c16184000d5001101c2503001680307c500c0303180b24a241407045039040381c00403080c3c020102d200034000c1d10540c10b510903540035580c0080020140700c1c6543c07010005141610341880704030342e03d2040ca101800041ca080d2582d004070000f21b070340c3c9209041180c00c1840150041c0c1060380d035240d8001280171802e0307015580d094441000400c00c00d5400001c00241200780c0e03006031500e0906c14002d04010004078180f44110101400b10034580c1c00c00d00780c500301c4920103044c09a6074200e07004a41464140c5900034044040c0c041404565180b1108520022001a04907480b030442010040f1030480c0d60030010750850040e1030141310307181c190301d00b0103103041c158102039103010a00c000691600c80c0c1c079002500011501e5615451615040c070a01400a00c00c40080c800c2d600807180101004411210f0584900600715406d001c1008510a81e003c1e140080d000704168070b1f242c04e249440780c242590840700c1c902c152001141c14506500100c0c0102507540c01002c443c2e49584221004207400b150 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476046780 1250 476045530 476045539
    0xc0118090209120a060c1403090c04020307030b1201141612051e2703040b030c09011803060204050406060306030f020d1416030b06040506060a0503100515091302090d02010e 76
    0x507102d40c1c241c020086980007070b02c02e080010b14090404d0004124603201d00080c3e2047c0d104205008101c1c800250865007603074119001a0b03a602e5440b81a00100f017400741c42504030500c016480304104040d40b19040e04000d0100091056464007410301c0d100c4442c0070403a01141502141414424060307100d242c0c03001d1100350450490054004990761540c0c00c803070300c0c1406e140740f0340441c0b065410074445440342c1302004006d50403e81025881c05450000810b0f82d2400c101c04121811141e202e04205e06521208400c2070007642e45a0919101a6210b40101c2d80502c0c01d089000883c02d11a202d18030803030b03410002a40030000d040d4204040c0c9540d0134400d13900c1185c466190803c100f802e0000e0242001da05440020f0780740f8511346008001001461107104a280504000c0c1c580c440c10111241040d40b49003041d5a90364444440800d40309580080d5044400824030741041e066000003000314100440e01285070f408072410280c141e2091a20064005c200c2c00040001035000d80f000990100c4003c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476048030 1250 476046780 476046799
    0x40b01180e010f151b030c171e030624071406040318031112070f09020711040c210f1d06060a050a0b21040507031205120430080106020c0118090209 65
    0x84032303100c202625000c961502800060381203848102550400203007002440c1c9a030852401c40b0001d0082c640004000b00080d002010003002c2c5c4140d038040b544051707032010854005034480031803156500c43c2100c04601040d901a00d6021007404080a001241c1c2d004074022036075094601401060340b02e61244103c64400d101011400001d0903040402a12084e2801601e4401e5420000301c500c645d00003150185160041200149234003400c440c002c00c00203441c24a1410100605500503c21002012552460491800d51410383e1250400c0e4001d2001c00f201c030184c80342402c015100260b881155440341da038000401c81c8440c404c015290f80040b101e4000240b0415141d0300e84134420840781214260404c8109108110784801c0c0180d41685515105050644400018104610103040038185000300a00102c2000004003070001c01452104030200312861000b0103810340d5028042c107000760195000c2d281965104400c002e028081010890300241d151020b100025800030180703c0d040107401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476049280 1250 476048030 476048033
    0x121403130b1c06030b1b040b0301050f030709050c04051f091a13030f06141909020a0b2206032007020406050604081b060306030a02040b01180e010f151b030c 69
    0x43c4a07120007140200030180862500c200b1040f50700303841080000c1d904501744410301c0700c98401025a41034817000e03034600c2d0211703e07a0700000307181030300a900c900388550070401004036190301c50010b40101d031002c0d074100c040c3c0013412510514130f000d13034500d41c0b0001e86490000c10481c8054942c102e0f00d07440001105107000b070801c0100043c040c0940098a004990300b6030381e01002180e21034002041c6810000703218030b040906502c9010f07030568440903aa03d072240e00398415036681c44682c5004082607880c075a0740c2c241c04140e4400408800450f0f14540d4068080011342d54003a008056407100006812040c10030420400181074000203000c0e80c02c0b6548880119468494070002e0000d45144c1c802800300b10610112031182080c1c81c502903003c0d00d400d105000303154600180e50017003240d0454020034588000c0c401201c8900c0c04880d0910144d264440021b000090290098161164003008940c2d460302c0f054030b007070b41307100c10304c281000201c500301164101034030b48508102d042d104c0c0c503080d903058566 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476050530 1250 476049280 476049337
    0x5070c0308070311220e07080a0b131a0109061803060509100c020304080106060f08040809030a053708040308030c041d06040b090c09220501121403130b 67
    0x30175443c81e40071074030203480c0c82003d80362140d80d0002c1100801c11011803501e004001c00d40f02c40640203010854480c2c0c009902136440c0c6020111061400c0350400c812a4408035990041c1d4035104110301007040210003286a520403004901d0096540d0030640c401da2550352500c0040c14010b041c0100c0d40116525114000442d00510303903032680982c000d5460718145552142100d219901c00c000340501c80c90440c000e82d0304078103641ea005406c03030040c6403100c01d03410120b401c0110303951000300f046c0241a500e02c200341000262821003038821000d0703900d811110b1007104040e804c03294054100351080c0400c10009205500441d071100c03180b0f500d0b03170030f09641d000f03281d480000443d00545185803100030030505040c20702c10101c1400d0202e41512050031700e1000300c000b40c480c600d1118010140e58903609108000f00011074000e0081070810011981c1d01e02d100510300001d2141129001e04980d411110351400100340c84200e00c010b084161454a80703010440540d000340e40822502002e404075102190300c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476051780 1250 476050530 476050537
    0x3030f0a0e0316051f12090f12051e0c030909040302070e0a05040b1303140904022a0d0c05030904050411060307020115121a0402041d07090c0305070c0308070311 71
    0x103183c076201c0c801909080c1048810444105140100b44943d8414003043c2c0e805516416040c0040b20006252101c03801c244004074121100034282d808244c1445103003035404401800040c3c1918001c1c034610a0007541c9840c103210356140400e030399006020b180e540d49424082c45400900c2401101e6280e69204031034004c0c00021680c44600700d03510010401845518030449a2000b0421038000300310710295400b03030038032034561059031450342c02041502007915298111455031a2803c0080611182c2c0e9090603410040306260213200e0240101c2030403168064803a99074016803110245060418402c20301004090041040c0d841000c000254051525440b00450007000c0540c0003003007001c3d0f80501500113034140d07403105000c9110f20f07e001c0301089000d061308200c800906409081c1d61500d0000070003a00082c1491495810030500e0b81c00c9050f00080d000d0101c0c1c0c0040000d00200c10000b0041d4120760044820070041521816841d0010344104001a03200140e41070001d40300d150103c10349000e80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476053030 1250 476051780 476051803
    0x5101a090f07020105100605030a0e0304091e0f061a09010306031203090201020f06010f1a0702040204230a12030f020a0501020301081e2b17040305031f0503030f0a0e03 74
    0x690242407001d040d83c2806043e40c400c80c42907407120358030303e003c0c03000700749100c0200121201ca0b521405042848801c1c0300310b4005000005040c0050703a02c03030b00210381c0704d00e10701c841d4a0301d103107010410700d034264490041c281203d00b102e10780c05010114290b681501e9004040050405a5483c0080700040c6002220380c00341900d69000140e043c014030019252060600e21b014460b03020b403004000030342c100087c4100b0365184500e0218621441c60200c000b07030050fa40b00950250022130f01080c14610302242c00c130080c8084080040982184c07042c004030b688140101005514110001804240205000c841c40100c80c030484080c00007a4aa9608980007a000220a03410410903441031140640003016240000c0780a808c1d42d00d40307907150384225a0403180d03100c0d41c00e01e542c007085041030040e0280e00c1c0240c51000c12041a04c2c043c0390007003a0f584100c0b211811009403c001840c14001110b48106840014004515240041d81710b5601c0790410901c0404000c444d10701c50600d41c805105529001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476054280 1250 476053030 476053051
    0x1508031e27030f0c031207050705030a030305070f0e0a1a120a02030702010b030f031909090509010c03061d071d03010f060504270809010c120206100603060305101a09 73
    0x1015060406003442030f02c820300030f41c2d0352281d040d4864641d00480e40c2010400d414043c0340d40e848040c40e0481c18542c060340b149a0500a4201d1f4400b0301da05904100d10038a4a0f40c4c80050511440302e0903201074442924140e00201c070003200740070711118112104140301040009900303184020300300c8222500c0854002c1b07000d0360040b0922030000d4090040c0340d00010700301c02a200c10240c4d0f5013681d969018074803840ea00703510041d41c201c3c01507014290300c80162443c1c0c80c083c0014a440c44d80180a42303041c21440c0c0010f80ba1000004990040c9160b091041d8508082d02d617494803058412904190100d9110800c9607005131071946a40d001d10820440424502c008203806141c00108422242d103e035950700e040c03840000c0450400e03828038108030f410303601c109003075100c62128004070350101a0000061042d95000c0950142c1a00024401d200f011200003500c009619040124203035011880003c10640c0004000c4003200c1140e0010318444407901d401d0301c011000403000dd040a1400d0341d41d064032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476055530 1250 476054280 476054347
    0x7090b1c060b1b101802060304080903030304060207110105070210030c03110a0804020f010c122709090b0916050d14070b0307090e07080f0a06091a01031508031e 71
    0x4a0a1001c1c00020040c01ca0030020450000c003060091190306174000d1051000000140c00c00002c0c2c01a1801010040e0490b0b4030f80c94589040720003580b10340b0302561125a0481d46445541c4503c0460b606903030b01801e071001a442e8004140d01500300023190906140c7c5a1442c6440610329001030102142e0710350b901c20307207410203006001c14540388040e4a410001a210036002043d0610b0005421007014074001c64203d507030088100d501c912644004070045248140001c041031950000c030783c0b0038020140200c56840f00d1000c036588400000c9039003600040040200210320304002181e213000d006000420070031500000b11414462590400c446540d004014040700662220109000e481c102070032101c1303401d203990060300c1c0303d03001005919010000000074a140e51190082001003040d6401405401c1d40c81c640340300c0c1542808900e90000340380200c18071503003e8a104840c11284100069460805448e11241c50240080100c18a98108001207001c84110120401107e0380c01d08101c50f2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476056780 1250 476055530 476055577
    0x9011116050a17120c0f1207210903020c1012091b0b120a020f0d0c05070b040804050f0405040b010e0903040f06120b06091008091e01050a0507090b1c060b 68
    0x1da04c140901403031050780040c048030403110000c0045504e40c0544a00f40d403c00c0d40d8207141190600720b4900002c51000b074081c1c90042100702078024001c0140b0076001e07070301c07216520070502403035100c41001840003942000c0d444442c40b4880d0300140b04c09008404030109010602c5da580c1000c4010307400505407120020313148440102c01c3c20041e401c10281241503150107070308008654540a0201c20340e08407560345900c1c180082c02081203c0e00103a002800242d1440d1504114245400900c5418001d0340c44224250340c030301c0c052040c00c1c4034503403001c450012030b400c01c22501c45a010090409601344810132006c126510a4082400100103994072002c0100c1200d413442c3c299805c540740c40d0302030282808254510303510516220400c00462038000d82c40d9580c800c445241142c00c02040070010112403404044c5001900100e118024803030040c842e40d100e400040f00e09064030711880b030640c6018454807880102142c00704080c4074154402080c1d1a0f102c8205000d0b070740c0301c042c24540c4800f00340780300790 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476058030 1250 476056780 476056807
    0xb070c06020f06010312080a0f0c0f080a02090d0609170c06061c051011090d0b04020909190f081201080303060316140d1515030b09011116050a17 64
    0x4002d018a10103071056502d50390340e449000c410481d24005000e00c11000a1501816900c801ca07082941d01d000c0c807920020650207840e078002d401002e80001d8001e80090b110045600070cc1e2041d18016010004055694651f00d000307001144045031110710003020f407441c0c4900040502008008a1701030301e194100300302002001010045c100ca41d12452000d40d01c085440460008140940000d010032a0b25a000c0359400398803a00e105941c0c050401003802c0140008280c01a00c42d40c400da640c141543c9460031410384c1c2d0030360b52206408485440d016480000c0c141e643e04d1140c1c51065214904120300c016001e00b481100340c0082219501c003104008607443c0070413056801c0c65519034a40c00841c207040000d02c4103000440c1d040d0080480c46009000c0051a01d8011000c01501d82c04124001c0b0005840340c45c02030a10058400d00b003c1070120708120410b2141c05003085880c0251440c101546450078050103001c032059a69020b5540d0840100b2000d200c00802411504c184075070300c055030640708 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476059280 1250 476058030 476058043
    0x40204060b03010b1207080606070b130804090c0216121b0506040b0c010c0e010806100c050303070206070f0305070c0f0f0209150a060e0a1e0801020f04090e010203060a090506030102040b070c0602 86
    0x2010010310300b0508c0001c6d1541000c642c000350300032b4a17400040d9a003801341e101a61880360000c00d00c0100007400650743d07a00d42d00500c41c41c09660b082c0c4072020300e14240210310704418054120b100308800031040000c0d003e201090381d2040303102c0d071b036844c4240d54000040c0c3d150070a900c90303c05480006042815080f080c400e081d40c11400c1d003400c40c20200e05800003080c50034010240d83c00344252280101406009482c520038082c0c0c08002c690341ca2800f0300303009480c0e400c00e8075071302d020484051a007401a402406101d104182940d038007140002680c0301c030342082c06106400c0c0d0744c0c0a00a011000075031540a1414420100034100c8210040790000b404155400d07a803006041142e1810100081e40d50314a80008941c54a10320920756410030410005000d5030f6031004019610000e001004845d941c0c010f0421100702d000300b040540070ba160604d090b03110482e0f00690001500109003c44441c0b40c0c01240c02c0500940010b0800380c40308804500d030350052505503100c801c0e24200300a141d5042045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476060530 1250 476059280 476059291
    0x20102071119030201140c012c0708060a0504030e1207060e04140402060c0c090f0108010c1103190221090906040912123c060f0b03040204060b03010b12 67
    0x400244459010744401ca50001d400001c5c1045400a00440c0c04007004069800f1355540300e00820441e13114520804014140094440c0703040c940e54080700714104041960001c070b400b2034026010707076594a00c9170b0005090082c000c609201100c000c032505a00d0340603d00c1c0d64406040014a81c0340d00b46540980034a4406d424180314500300b401c60b544159081241c40d40065040e20229140c00e5000c1d049803c004c000054580c118001400700301826078400704d000d049800b040c2c020400300103542e10840b120880c0521120107079104200748429005c0c030180b0b001c2000b905c0d02c161910042c0507142e0035203241c15800006000c41c00440d060740c485c54060042d0303400080448040060018660752145441803d646803c24005001042d684401041e04004010442c00c0d03035891005102c440c1e00c0008001c003000c0810742c00d03404180c54000d000c003440740200b50361101c4820a25240f8205982c10070b580300074812a0410303101d2000280b140c002c04040c0d40600391601c1d00756213076940c1c03003070503010148020305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476061780 1250 476060530 476060539
    0xe07080f0a060807210503070b070305060604151808030d020720030a0b0406060503060a0e061303090915180b0102060c07170d0212070201021b060f0f070c06020a0201020711 76
    0xb0100074180000600f10300312800006404e5176012140c00c013044000300c801015140c1d010024070b408c100205030350720510400c0c65803410803107034450b079040c407940b4052030045461051401c13440b036074541c1c010f50b40783c04084035400c150a0500c0d1213001c03039400d541000b0302d0011003d8010480b1030800418801c02c1441c0310301403081030341c02440320001030360310509244041c01d009146d1020500348503003504000081c000150494565041800d0340320010001c20040340c0140c0039800110b140145508c0820924540568a0800850801603000c0c024000c500d940c0c98400304086000071001d140090840b0800b03028240020400400d200182c2490002410800e1003c810091a40000c0401070381003082d90603880c400b5115000b22650100034443d0f00541d201259520381000b1081c1e9054008060200346404441400103450040c03555940065800701c0b42e06500c40c1c00611881e55a0b036a07503511005500c0d183c10000419159941260f000c100c3c030000507500024a00705118503105160b894160944 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476063030 1250 476061780 476061791
    0x10e100504110d03170906010e090307051515030106030807020a0e13110103384203070810060504080a15060b1c0c0f23040e07080f0a 59
    0x2038415400c40070070032041c0e110f4103a154910b0145440380c0b180841794409a081203910b81000e1010a07a83e17802441200030f000d1994000070882a0048155030b41a94450300600b071050280741c0520300d03000e004044d03640380c0441208a6240b65003d004180055014401040d52020b80c1c0c014070000c140e00d90030205039220700c0d40903c01d980070708901542c01d494010aa007450040c2c1000100c0180c0440c09140e20214500002d00f15a640380c2c00307111000c00c22644117401e603885400140100040f200300000110a0211146665035284580c0d66a040103070014001c115800c1035022510f030740054400740c0020f203103e0200920030010442c00e0024140d28280709080c245811010b5903500190100244044010a0200c2c200000d9030041d0b400b0705011640c0366100e91000d4014051740da41031a51004040c1052104c0030114010309030300c40c802800c1e07514080156800f5072811300c51070340c101040c00c119004000003d559400c981420f4040c008a44d20b40c011b07814980c24000d0500c402500500c0e80768a0710 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476064280 1250 476063030 476063033
    0x603051209010f0c020105120f0a060509070903030503040c0510020a060b0d080702190509131a040305070807050c0907030902040c0215190609020f12070e031e01020c0f010e100504 79
    0x45105400b403c4180b400c44440140791004944501540362904080601241072003e032440048140f0f10841c4030b010200b0509a4800412030410b005a80320300205c0c4000f071040c00860311800080d50700c50f009100035441d2955907804900716074400701d04400183c0002045000f0007010b4051081c417400d00312a040302aa0305c43e01c42690920a420000b44946c5428542c0c0a001c100f8003c81c50080000521a01c0103240c0480d0380314006006150840d4101c108107034200070382c2000f00c04030740a640c0680d01c0300c2c10500981d4038082d40d80d000800c00d81d024429610715411aa5410030702c2c0d40b1404456030301250142c41b40c0f041c0400d4501305581c450640d0000b0b00070140f11343c4203a1036983d00c142c0e504038001c80800c6109640c0300400c00741d0000405a400000c05940146041c00140700c11510980d052425548545044820101c02c8000541c140c00141c2c3c14901c9444140640740c6064041d400103161946da03034080c42c5010700d58084405c159443e02100c241d4034074244003008442e91740100500032407806 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476065530 1250 476064280 476064287
    0x90203060f010e030c03122a03030a090c0801021c0c031e020d060314070f17030f0703090e0a0902030105130807060c09030b070e10031a0123040306060305120901 71
    0xc19081d03040000c1c485440c80750380e60412101300c4582c00941510010210b021406465a00515171071000c8141d9400c080f0900c51074400c003c21414031400a1070031a01c86100f03000c081d000d41541511000801c090200740b501084c030043c204c6095a02030403007040071051151059076034403c0b01005261034140815406c400d040d141404000f0303248001079842d80d201d003806000303008a41014112202140c00ba0480000c0042c0c1c04007901c0400a4101e0754030b5683d40a0a0fa0b00010f0402980b240c000344014648450034201034000617102e030802418464540442c44610b0b40308866a4031620b4a540c0c002086d07041c00c1c40b0751604a08000c1e501c030b48508094881a859118900340103007003654403030079000e80511500c0303030744081c5030701c4140701585061019004018031551040b151040703c07142280d0040302d00900c9803d03008400c03002035800c120200401960961006801c01002012007000c0b084200c1c03c02c0001c20146200c3c2c0000120141507050035841c0c01d1581c0c0062820748c6041203e07004e143e81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476066780 1250 476065530 476065549
    0x30712140a0e04200706140606040e1009050403030209011d0f06071a0403020318010503010501121505060c010c020c0a031e03020c180106111c0e180108031309020306 73
    0xa003030500721005020b807008900200148030070124094566038031070500203401c0c1c0007080c0d070901458050228030704101c040e280c40c000c203842c4960b00590400c01007141c14505409581d114203504400b02009659422030000d9440c03c440440000b580050900c10315038200810424145503807203400c0301d030100c16000c210580042440345101d000c010448400301f01042000e40c040000b05045402c2a041a140180d40c0790031031200c0304251250000c0710b03541c0303500c030341e09a03812101d05958036034214514940240040014044140001c0f1700798078085101c1e210040185407007000d2100004044003801402800e100080e0806c510074154030b13008001180342d0100d07241d000c1089101c0c41d04003504600c1c0981c03601c0754801103980c22095500c2c07402d03000d0300d402c1c40450407600309403682c0d950510901c000d00c0e00d450303e104203002c62820b03074403c1031142485440d004100d100050070304d03200c0700c114512208805000364070400e1164000200001c0340c2400d6007a841c000c1c40003827025801c50a108000507003168 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476068030 1250 476066780 476066797
    0x5070c03030f052716060306030209070516120c1704061106060f01110a0609061d010903081501020a02090c04090b0111070308030c0405060a030e010e0309010e090901021b03071214 79
    0x602d85021485408007032000ca0385e91581800c00d1070f4443c0d034806020707028000511040e8403400300c2c3c07400511564060400c44900c030729140844c5581c8010b0740c0d40c0000011003024843d0802c000060b00400060f05a043d081c58000c420b4a2580c489280c031700c0c01019a11104a0b80305160090410300100e912480312000071100d090030806000c001c9180c0a5203403150700c22001e0041800d1625542c1809050317401512031100d01400d00421203402944282651a208401000141c0c1000010030200c541d81d04020b0280c01481500e02c08006900000d012074810740340d48100c0c4000260801c0085481d214000d8140020309003203480c03d11030713050b0030b0311a003a92001400c4081c001001480e00c03103400c01118040c00300200b03015220382308518010014030602500440540c038001050341070006c0001a2602404160b450100e2040c40d40c0031700bc80386d60054812521903400b40035650860300c1003043e02600c8022400103640b0340300300d420700f4500c58a00d6091801400000c09030074200070302c18421144a41c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476069280 1250 476068030 476068081
    0x9050307060f2403030f0c03051c0b040f14090a21120e0a0c0506030115050c1c0f12050f01140a080d0914041a091905070c03030f05 58
    0x9500c0900400900403124940000003040c850f4032221140780011841900d0080d518a00302e041c00300000d4a41e08802e0001602148050120180d82055040f0340a440503290902080c0e0380c8030071004ca07040d9501d4264002141d5214201071590b0003030200020344c0b00701d19038000c10300080a9140d051b03000c1803401e1151203c98284030000350250241c1d440d0140d010034480304026400022112035258414024100c4d043c00c001500010145420800d80c1d058400089040c2100c0920350001c1d00d00da801450310b400c442c0184054001c2580180c1e0780104030f900b280c1c032819181482a180145001e001e81198620700c0d00c1e16050142820b01c1d0003409054502010009915000900010707a01e00c441341c0c0080b4540c0f08070a60315000960107500801211040320881c050000060104416294401282002c41e6010941200c040c5401c03800d05811003000700c48800c14640c2c1002140c15198111108070201d900c40ba100802c15604d8400d13a02c08507502a410005814880011a104020b1103403c0c0f444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476070530 1250 476069280 476069291
    0x4063b10140c0d200a080a0504030219020307090629120609060120070f060504050306070f0c0f11210a080906041d0a0b0a0f05060d02270f03010905030706 68
    0x10011139807014141100711100d241d89041040b00d0380c0d8140c0d01c1a40840e00082081012944541c203600400780641e6141e000340c2440704100c5440090580c191038140d91620410000140303034a1a0722541d0003130000900c6401384000c903e80e401100e11050002138003c1392041151700a56803030740e500250800800c468404a03611454012a00d40c40404010081540440145100b10038001100c0084070510001c008040380e4a110030b031081d000310300c1100d8040c0c0007000021401e130b00c00c103400d10b1001c2e81c0d82404d6008084135100c0c13454000d00f03840d007220b81980421558815290100c01401c10000001c5410059080b070391130103480f068208001000030704041048841c50380c81d501a100508034189500201da840b0722802c0703a0841044c0c07070f0690510700c0c0c101640c519050440c203e0041e9000039804a400914040a21083c0c0c0d101141d01c0c8955a428024640300d0040328241d801c0c0e40307500038bc00007481c00c1103a0400102c4025100618481d0785885030410008002105840206402a03c002074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476071780 1250 476070530 476070547
    0xc0e1315020c030d090201110a020d080c03040f0303020d1814010f0e03010c0c1a0408040e070c1a0f10062703020301110403051506010804063b10140c 66
    0x680078068445105000211300a100c14030a50301a05245000341c0c0c41904403028034440c19112182c815000e50000d201c0c00315000031401d070070000e040448201088074038003555030202035400a0180c2084006800c111142c001c041d60050030f1803c0c00780c802d40141d0040b80f5080074004002400c500c56414040d0602c5d84862060080011501c00c1402800078040b09403c50801080c26200c120100c0341d490020382409003600c0c0c02c1e02094812503126005901c0c242c2000500107006100405801c00c000303490407a0b8000803000000c0341400c82c000701c0d00500b10b0820f080500a6841e008007c249210150041007142c55440900301030110032010020a50b501886040d01c01c40c0e440340c00194042d070801d0704507c0501c026800404c21603001c3c0c0c00340d500110f41e00412401040060310414009049030011801184880d844205c0c2d00d01d05881c04142201c500c00d40140050030280400d803100429002c101c07880c4d00c14052134441005030303c000c00c450314100307103c080000740141c44004160350202e209117 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476073030 1250 476071780 476071823
    0x1060b031e0406090819020f0c100804051614040b03161a0712050304050d03090308010e1806100510020f0622060504060c0e010e09010603150b04030f0c0e13 69
    0xa0342a0300440782e10794503800580349070000309a1101032401441a40846404100c012420364189c0f000103004caa00700e14080d408941c00749014109490318041c003508240c1040e58007070440c0050810050a00c01c041181d420130080300c80d20039125010f82c1000c500c44d07000d0300010300d1440599980c102e000f01840e11410039a5642c0c0158507008051220591030015090f81210140d4401c0d07100d5401c603081c031a00035101300c06648c14580000d010a00ca20014007503110328601c0d040d4042007030340704488107840c0c20742403604d0640162070011055460b9102404282400004400c032110380d40000c0286160301c3c5146559020001c0034041403070a412503106c0900c403845550400076800010502c1181000d0914900405040c240080462344200000c2603c0d4013503160a00c2c0c01034014510525603103440020313006024824650310089041910201e00054642e025002841c003807505c12140a0a610b051108500e041d0000203c81d281201003200d00314602d07a892106035800002c6c588ca0314140f02641 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476074280 1250 476073030 476073041
    0x91315090e060a05100b030f1b12010e1f0e040303090c0303030203060414090604230d050306040e030f16060f1805060105090618100e010f030501060b031e0406 70
    0x2a120310305207080d110168400003007550040710100810800782d1101c040301040d042082c0305000302d8060030320000e032040c00315610365540403000c0d4118184c000b4003000304110540c40025881401c082c210014041d28082440305a401681812a440701a40021000e040d420051240d1600b12590b100090304151180d0004441d842e442818900f2407526450050f001c1d41007254942d0240307141c002446ea146007a00381540c011000c9a02030701075511035855940400d1480e8a2032117158250782c0f232640400804115030904010030f40c0e6250740301d080000410065031034144240d1342941c07040c0540f44219803c5011283d0320841701c019100944d100f803400380003400070b43c1221a00719240c030350040e00c3c40020a8004030818400d1041d00e1481e070302c420802c1140c50013503170b44540200d00090000c1d07091400c0c0d181a070b00030b12100485015581c0d12400500c40303d400f600105040e1421081c01c10410000740a15000750542c0b101580c1180741101045011452a8050301000301003800803c09006059000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476075530 1250 476074280 476074289
    0x130501051b070f330b0d0c050906040e0d05090f03030301050f0111100501090c0f080106080c09041506022a09130318080705030d02061003060c09170604030e06091315 73
    0x100306400c101c10b04801c0071001d1041300103c0075040010401d01451300030540044564051049083c803030422052200e4240300074100d60b0000d030f5480503c824088100074074001c14034151f071016952540b58081c08886540c00160354000d600602c01841280d60350754203800b890800b8a062040e00009500e0180fa0803490421100c1e010329040000c41d17401101c1c9c1013031421000700e0300c2c3e40010107181e29003240c08035024810900010441000f04410540400c014284460300a101083c88124481c11040e05461a4403072070159109100e000088414000c40b0400700d5101ca40e0b40103040600d00c049100c402c3d005209000450301081c50b0000c01d801020b5003072045d012b10f042595420f840301c2c007095503100e841c000ca902c20700c507046903907101c0c0703100107410b40c070907a030744090426164a580d0740c20015001c00f01000302484000000840e241c10020742e1410802061001014a405c050030054000c0303a041d09490b003c1e08007000080030340d4462401704552506007a2001480c5448004816680c2c02c15410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476076780 1250 476075530 476075573
    0x5280f050105060109050603040c0608070e060412142103041a091e120d09060e1213050a030209070c050111130e01061b060203040807020405130501051b070f 69
    0x89181805030541c001407003080d0a8032414480b684403410440b0501049500a040800c00c000c1401070300c1c46440311680154090500d03850700c0038000c00040c02a00160002034409400c00a540b050114031150001c10b9088180a42420345803544a0840c0d0545966145406d403400404070b820404004040c810f60101d003c03149103281404507589445140d01d00342d00940404043c0040590b8101144001411030311891683c90007042d0140b05011780650142611219542c0307400e40741d8000b00780710402c8103400d84040b1603a9182e030040e40c3e03e07600d001134110780e0003551005420b00c01a01c80310f88550304842282403c00240758589001405005259030784117007640c0c0481e03040c100d40c403221104400d40d905204246503a81c1c0b45c0d6021a0310100c000309840610030780d00e11080c00706945030f008580041c0100d601c00e19180b60f0703070003080c180d85050712408a5440c5407030102c000e1141c00e00c12079802c02180125074441800308100d0341920302030440b01401551029800804200040d0015200d4584820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476078030 1250 476076780 476076803
    0x6050d090f14060708070e21150c03010f0f050109030b091c2d020a081e070f06050a11040515091203040e011401141b0a050d03060902070528 62
    0x20010f42c40303240079100e801c041444030000c03940c4140640117041001d08054441c100c9007003170040c0307018144c3c81d4101c070b89000c0c010048070301014a040c030703c1c491058440c00e140c1982c0c2e514041d6100b0315045198881d07882e103d460300c4140903603a8010703441d0013200d8125040125a80f101c54495050003602985200c5c8030704520721492040740c00504118502c552480500040c0d001c880f1841c82c40d5100b100028016042140c1c1c10002880c06406442d004090814098000c80d04202c034030a103901801c0141e6824941300184010052503004a0350300c032814207420300c0200015500f400ca913000b00e008481c481d501200714807028404900a031180a6030050502200c030704030a0040d6100d40c4a8090a20903074614000450b151040380c030940c41c900010395400501c590813a9000e5225008446c22885030411085549003c010810940701c10038007900180c210055410805801c4072602d9001c0c0b503c00d4014005034000c2500826410364030010286a02c3c0010040c074040c3d4143c0d07030b02e00d60046c00d503141d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476079136 1106 476078030 476078063
    0x101a0301021315021c02060a0f1b031802031002030f0903030705191e020610051c020405040519050105060913110d020a090c0203090a0f06050d090f 65
    0x784140ca417801e40100f56900d80341207a80421006074056000d2010081240c800d04000c11308101c420081040c0b1402c049940c5441550b40c8414036076038440c542004e80000000603076040e8000c3c15a1a06c083e444203000094106444003015512100c000645219000007104e000e141a038403032609028000d0720030951406102000c0d810031510760380d007036200b80010b100f4a0780000035802038407403407605944440418016070704c101d03c41c01000e00030911081480700f41b10f150980540e03000c281542e407801e00d02d00c3d018480d102e10454554140f10304013400010751003140201407c03507003e80603032151080740341c9400d460b50740503000941111265100345006150105c503035101500550b01141c0d15038103141180d0108140f00f015810008403901e080c6080c00c0d540010385480c14241103e1420301000905500403c0c106035a0255a100c0c01c80c117120304581401c5015030b1010f140031010208 = true := by decide +kernel

theorem cover : BRFrame.Cov 475899280 476079136 := by
  have h0 := BRFrame.cov_init 475899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475899280 ≤ n) (h2 : n < 476079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
