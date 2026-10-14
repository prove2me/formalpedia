-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:31:04.156929+00:00
-- url     : https://prove2.me/submissions/eed72a08-c676-41a5-a6ed-9f646f6ac475

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 608992805 ≤ n < 609172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 608994055 1250 608992805 608992817
    0x121606060803130306020a0203040f030f061d060106030c09052d0d030203091504050a06050702010212030603190303061d010504140601120b061b0a020906040501050a03020d081e0a03060501080403 86
    0x132000540307540141c03502011500c1100c0c20300741d44141004a9104552045e9042c036000c1c2800d2081c01458000e10a6040103445041800900107401d9550340c2c00502c50310040554034040c4c8148a88141c104200901004042c0c1c17194024107810580320008608080c0d84000c80c4100301d020500305410300303030781542d01600514100080542401290a040301d424140400104004581030351070390b070a080031f0b2443d43c1d50704d0344a076080d100182ca0640428001e020301c4501380104440c0307640018028901030a21803d040101d45e4525007600a01226000526103041c0c940c1803d254000c0807001c0c60490f90120760905c540729400c060b08061100c255403850000d809088141804089a00181c0010001601041ca42064103266040d20411522080715a0b00602c0d0300c1c10552406540440d0410400c480c104800c0d45024000340c00795005100c000e020340e0f40d4501c440141f003010f1f000d0700d201c03030742520013100b090a0301481100d1a03031068080300d01003850084082010351198841c180f24503415183d03030f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 608995305 1250 608994055 608994059
    0x20a08010806012d03060608031201050a21060e06070f0e0405040309051c05030a05041403010608031b010905010501080a0213050601140d1b030f0f02030c09011112160606080313 78
    0x4012621410113030400312141c030440020008000d445100000d015440145443d516061440d0402c2300069102c0da101750460a0141f01c1e1140c6183d1001d4000000358072504424050301c0e16002070404545440014040d080c01c00c080290000040752880426581e26008098490200400c0312810b036805000038002010902070350034150700c402c1c1038440d02c0c48a01410306450395801d14581c002e0b0f51036000540f000c2810880390400c80407000c0a14800c43c02400b8007420204043e80d01e005210102c80308044400d00014074003029407040c250183c11100912442d80c5400348150354046680040b030080c24105c0340c0d6500c103000d80c40380a01400059403240305170049071000b1303c0a6041640400b42580d030390303030740000e480d0300180c84020351092917180402d951801d14440001c80e007401c20500c0d40c15004204010340c4158641c2211800304003420b007280f40c4100400c9140c1b500403030f80800c880b0b8174000505040502d110012000441d48114400c0c04420344402c4603e031680120601c442c00c104030034000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 608996555 1250 608995305 608995349
    0x7020d020708191b0902251505061c110f0d03020c060a090906030501050402030f03070308041106120f10061701030803090a150902090601140306040c02031611130203061509030c040e01020a0801080601 88
    0x71079074000c900140111204080125100c01c160507055048802c0d22100d514691141400c4e8000537011604440e20360f030520980e02c001c0d460f2181c58000e24441c0500041104480f4080d980c2c51000c0e08049c2c208000c0c06889103010350003003d058500780c5c07003803140b4004840580000002c84071582c3e8160b99a40c42c5e0b48599480300002140d00b41d540754045801d001d40030012821b0b1400b18400c1c55101c482c0c90403401c204201170744010b01c0d80c000720b0401031010030321101002000415411298013907a511354a40d0350301031050514100c55030007800c42c08070180311880d800954000d068454021126642587c407800c1c015030741880c035464540c143d408144001142482c00c0e90040c0c80909560050b0303440c22100040f070725220103030200200e500741090200c07480d1a0501344503081d503514084e003007185141000c1c00040c2c04102e10203050084031500142d958582d460520030f0060040001d001409820700406140d4043d4000c610964001807912000040441d40061514104d407092056019075000341c080c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 608997805 1250 608996555 608996561
    0x2b020301120314091221130b0c1006030c18020a171021060614060301120836010e0f040f06051807020d020708191b09022515 55
    0x384034803449018451000d10b51516454204071040390805800240a601c0501a0360165203085020100301130003010801e021f400e40e00360903030b403092070703070645491500c9034262800301c680200034900f509081c000010840c8014000d01550400744800880401404001e0b0482c041c001c1e804c00090f01840d078507901c12080b08402504150b0103800c803040292208020607009000328214000f4010552130780c4103101c002d202d40c4c00600450305800242600c4100042c029000600420404c400441c1c1c082c01008500000c4900c1112b1700203c107012980f40010040c800300080c840040c0c2100a102c105050758890f00b00200c01c4100144010700369003204007804020003140c0d0000380c2d05580e4030004941540d40b0b030500b403c910003e072031803c080d1802503002401c00060701c82e541c00795442304100b80403004000c5107210b10304090300c01030031030007402c3d0a2995100312440014618808480c1c0c0104901c0c20680060a4031380c000800e00d0390b11408240d0503820031a03081000341c010007034000300c10441c0603950 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 608999055 1250 608997805 608997827
    0x4150315030609110901060e01170f01150207180902011202070b011e03061a0f0306010303050d0c09150207091803050f131e0e06100c060b060f2b0203011203 69
    0x120742e4a422880361300868140c040a821000108059843c0b5103a69030f80031660450107020200003031001e09062100c174810a206000d4100c1c07641c240005172480c02c1c0f081000d0300081502004142032120384400380c80083c04422000e9000412545491050140078022540d4441d40030880c00404e038a069400400310072074400c0070701d01ca02c1070507000000c11502e000b00d034604480c64024106400c00d0004000f880b00200c86041e000360001e100410129802c54151101640c03100c00200b2a510700d41400c4414404503001044510409095100d4460b8001019015120129030030080c2c035071407003484130b26289060802800102c2c10030440b03961300c3c010300151490030320307001c0200b20322a00c030101d40c901c060004040c000103044201c010805840921400754002e00d00f6985441d01100070300008122404c64040641003d0f00d03414000c2d1183c440004580c01c00131030b02002600e0f204140c542c0c1034a4036580401e908944042e20826607004464400c40e4100c0c0c0f640ca245030a240d0300c9a5054458034146 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609000305 1250 608999055 608999063
    0x2190c050f060c061602010f06091a041407211112010603020c070314070e1315090305120603151303090f060c02150f0304081b0c011b05070801090804150315030609 72
    0x20086d0032010903141c054000038201da52400304407040c0a5010410100b584100a8403c2d03003004561030f0850b15000c8215040b0ba480d103000cfc1940b07620600c102c45a203500b90400c001d018038003814247d8504000018043c440c10100ac074280d181d0f6070b450308030180d005048042c0c84640051700b0400000e0030b4030402444464400b01078030551a40e1300030940201030215a50710b0000ca0034a00e1808104240600d2a140025050100451502528010014080d0351a007441d9980d00e60701082103944c04012003401c004580c1d9858140d46080c164a42900c8162a01200402c1a8010108500710152155419070b891a9a50328140b01a40c080120481c514420310341d002e1010040d1a400040311b400031880346008070000765071241411018110641205c130481c250350880740034206145c1e030010401c0701191010500c00c40800c4181021307400c0201383d074004401507103410000b50800800c10042d10440e11b0100300b03401e100b04104c4054003070361450800306c81182c540003070910020310541d00503070109001e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609001555 1250 609000305 609000311
    0xd0606030b010e01081006061b060905060a2403050a08070813060509010e010f1205070207080307050708010b012610080d0309062004030b040302190c050f060c06160201 74
    0x18a40358074407000001e0308140c8904071054018050010100041a54409208002c1214500e480c4000b0305251004412100d50b44444160600740809501b0220a29400c0001e0707803c02c0c04d06a80a40091600da480050100d110703034400c2d13030945d8024003040216a00003002d41700300785c240c3e03507101c102e41e104090884080d00180540c81d01d50500405800240c802919900d40d110f41903000900440c504180c51410005000d54406005500c0328a203205810550f2002c1a13980b5100380603420240650404800781c400411541c1c14444002072420481380488003c119810660b801143d40c01c24120541c55007000356012907501e0a4030051466001c00c0001c0b01c3d045040e108c070069410403100c888140c0c00a91102644400e00c1040d100d09903070b01805400c0c4600e07584000361410244d01a5100c00f81c60520010b00140034103000744140507400414039101d859030107640c40c189c58038a095010b10303401181e5001800c0b80c1810081c046400b80755140000301155605c00030611190a140c00e00d170411075403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609002805 1250 609001555 609001559
    0x20a050c060702030c12090607020d1110091701050412050a091d0403020c0109080a0230030304050c030a0809040c020c030d170a020a052a160905060109030506060d0606 74
    0x281400064000c0c0c0540d03020b5a56100a1150761b450030442135100e113412501081401c0441d0740f4502103490300c9a040c0c503500c4c00c400260a02d2200b4100b008a01a00a01c4d00c5c910300449950184040068442c08040d4040c02191402500d088900848004052911aa603030740c2c003480c05580a0460001c50f032420a4000d5110208240c01084140c1e0302c03511840c42c8030502082540501188040341d900780303800141c00d1318081200d5a2882d82e03410107405000c660030103540421880386200807851014030001c80800e0213100140c1c2d60352080790f00751500d02620a98081c00c0c540403840600e650342144c01903040000ba0030800c0002c0055000c5c080940c443e401c1447d4503520240407030550301c0020b485440403086a01132000030440010040d01c1024030400001100c01d4010094078445c0d180440742041d03002e5244a001d104c0010590369900380c2c8100c0c180c0900d51060b10101000b40d81c418407040c0110f84821005544011035404000e00a8005030001002818900c0c8020191802043c01091300e40e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609004055 1250 609002805 609002827
    0x2030705090414030414040c08160c06110c030c0601080d121d0a03030e0706022a011b080a0f080f0f09100e0c15040612050a1d07030c0f050a0306020a05 67
    0x1751199003d800503401c1c280e5802035500e882e00c0b5501883d2500c1c1007803035151806c0c8600ca10110001240d0360b051224a90080041c09080e904c40140020040d01095a944100700070503501d8025500300d03980da2003040c001199910000c5030b208201d900c02d40343c0106c072540c01d0034144060076990349000d80c00d401e042400340d8407140c20071482d02140d0003514005103c4440020407820700c1c0c1c640e00241c00f55072068001c0b0312440025018804104011201c0c0441c405230600101e038043c2d0900c402c1c00d0078141e10300b507800c18441400c00420141e061900c440c80c6540c5400826134860300c040340c5018002417000b00041103079500201095201c1c0b00b074004c0d01c12a0300307030802b8002242d04100d041c540903441140501c1c40c5040c0704c1c00240e003240d1403401c21401e180c54188020061340480030400301442c0c8a10104040040170f40010443c1c003078107010020b54040c58064160b494109100c00c0d2201c000300800015944407203c3e601301030303400c06030600d4045810b64492801a5103c0e1000d2801c010342080500c6200c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609005305 1250 609004055 609004057
    0x509010c020607200616060b0a030b010807090c0806030c0d03030617060115030e19020f0a03120201050c0f0f070206040f0e011a03070804121205010605090a0905040203070509041403 80
    0x94403030040300c81c210606100483d0381ca50905407017030050000304840d175580b072400e0401c0003486501510110300c101220340070030078000180d44010000f00b5503d00114000201082a43c280d4251103001c0040c000700500480b072007001034174140d03096005081c800d40507007440e000d4000e0080c028100415025901c40701048075041806116202ea04110f005100c0412144400342c1c254141d89420300c8104c4014004e540c40c0c0685950785210102016640011900c2d6110030003007004000702109445962410040c1c1e140340c88500b4207006520749130000c0c01c195070711400d80300c131250051060740c180000b911000a4503841100140d90150043c03200242d85805402207001404e02c80c0001e08e40d55150445140ca551a10303c0000150030041c001c2041d641d5000c0807007540290440c0508082c80680030b029540080050a440d4406041000120781c0d41d40010040107800740c1a25280001d5941c3d41006044810a5800039416049000100414500450cc554020703005440d0b07884e20303003081000c103451 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609006555 1250 609005305 609005317
    0xa17070b0c0106060e040b091305190f12080c04150203040308040602151003170306040f0501060806011403011d2203030c14090310050c12010b030117070e0402010509010c0206 77
    0x407aa448500510009600c04941e11807044103030340601005a2280c001904004010710864064a0b5805000d083c400104022007079214403c141e0042c041030780c00c1a030011040c0d088162541e07950b8641e2594600e03c2008141e114003181c0c03561500345400d0401c28613440410316660021844284000b02c0807458050090004050b103400401c07180100314503507218284000c10b84980f040e41c0d42e0b0300300007085024041d150b10840f81c92a543e41e0f581c0c0c0500090050480240035554289021700110304c0c2e81d000b4010501400b001d0302d0741010740c1d04c1c172039041c407a52000740116031110031001c0702c10100d0040c0c0355119070407040656200d1000030450740400076140c00940b00768000386c0c41709810b1203540d42200e404003c07104000c000728500300caa0008a1366406071005941455079035030000400b1288100107480301b40c183d0110303504055179200090342c0160000c0c02003041041340c1560700d0200c602c0009014003143c003a401d00e42c0d41c658903a0010340b1142c00c100c2405041c03107030210351080180c0d110001852 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609007805 1250 609006555 609006577
    0x1415010f231b0105060a031104091a1e060d021c020f030609031e0403320109060605190602060708040510050f1e0714030901060e091b0f0a17070b 64
    0xd01100040b0242961005080d07540250301010b400c0c0b012441070712449219940c00e9501041014003480c1600600c84080081c00c009412903007845a400000000f4444107202022000c08603194281044800171072500025480020041c01440700041106000500ca0006005401940c0f0090103c0c2c01c084080720100304070307000040d13507204c005013501c407003000f142038910001d040c41d09540d2001041035903a008103030742076250310340c1034001da41d1346c0d62110710030101800038850a0110700c1d20002602d000d0043c03620911411500b000b409851154080c100e5246a0040803541c5508500b079030015405081550340c1d000f43e01007044045000e00a540c0542c2c0d461500c03d0302403501e40b19400000010811048210f100c900600c42e4043d0700c45482e410360326502400f1a90303600d40544031401800e45512030100812007504212051030041003010182d0a18a45071410414140c10462114505500d0741d50060345440d05110f4807030724140000d0312103e204103c0d80d40c180c65000880d910382020501107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609009055 1250 609007805 609007837
    0x806220917040e07020303010501120209040b130f0f0506100f05130f0e09010504080a0f0e030a03050a080c03040b0103140f0a05031b01020309060a0c14030106031415010f23 76
    0x81d028664442ea40c1c07013241d0744091429941000c000078150205080f41c0140d254010032855960390f51035109510440b801024082c0b1170340c500c0c60341c0001d00620650b580000c0c1c0f1700b5000040c01c815078080d8a22568000b401071641800240f02039a4a0300209200c0b400c005060003807188680c0c0c640701580107068020400300d801407070406841c201e1000100030000c56414102403100265052081d03412030070013070a0507810031558000071180c84080041c0250b152040131703186030605410800400c541e80d07041d07541e02d459070b41e0700503001003074882a0b60041800342c000c0b004001068005003600344021040302960118041182c00303624001c16810280d0300364100140000062205003a1038034090084402541180b501c07a80403511600f0081004071075030380302c0c11042c22661081441c1201c50540305501d80d01c070350719900d00030010103540490300c00c10411800810b280988020a4201020b0142c2d56050740da8414a000c8404007200b0024185d1220b00c4030780d40800c8400600502030002d0b1105140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609010305 1250 609009055 609009059
    0xc150d1812031a0f0d06060f050f120309010e04090506090f010515090f06010c05060907080d08060d03120f020c2d030409050709090903030c0f080622091704 69
    0x441010750980310400d052400300001c1c02580340051800c0c40d54030482d1442c40d555030601c013250480481c48030080000b4549a400310701c4541c000e0603030041e10304c15100000d2038103c10302800f00e2403410300c20345610b0b54014071410440358030540c1c5000300304101920100720143c840c1d0718035141c030100781d540c1c162542226640c1c00607480c0034428141e0140d101024400c41100002c00305022110107049582030680c02c80024290b030340194580c58400d54440700f00c48191800003031035901d034019802510468007840c104005024410f01d102c2c0d015150092200c00700c00c1c0c00e65000e58503424003060301c9842c180c4880c0c0074107410a051011307081c4640880040c210f5802c024400284400200036a942d240040d1600140310030300010076038080d180b58000c0050151505071040d82c034690207a020341a40b900340400e180c2050b03815004100706c900907403503c528103d0401e8040d01d1100342154010381210200c440f0060f5501040b07285101e610104d440007401ca00c054443c100071003035000302ca010049d000501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609011555 1250 609010305 609010313
    0x70207031e0302012f0f090303030f070e0306070e0103151a070318030b040201110307020a141e060f070c030203101b0302030c0f09012d02010f0e0c150d18 68
    0x1031441210312842c0307900f040926260082da60304005a45002c1603171404210346103204003000c2180c0e1480001000c40e526803030161501074505400f20345a400003200400b48040354140081c00d00c1c0202e201780c94555101c55220011001041142501c0000c0c60041c44001010040d00600000c0390b80c0404050350756403078034140504100f4800c460341c688404c40d12820004214030010590300240e09181c41003c6181c110681403541c0284000a903028052000c001850300c141504e00b0030424050790446001008002500d07418a500804240c00c41000c014000c94480d5071802084001c0c403807501c2d00400f54894000c240b4040300b13502d072480d4856039460007404110001c0c1e10310315000140e207001d518618055240e0415070040502050302c1c0b0401082810640e03014100e00e00c010000e04400e504a250300100d40758800e042800d6140c003551034100100302074001c501410060310114001810b0074004642030207a00e400d40c400341021000705020780d040d40e410f40e000d0b520f5142085040e601c501c1d0780300d083c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609012805 1250 609011555 609011561
    0x40e0601080c0f09130822031a090a080a1205010801051e042402090619080105011713030e0607030f120501050d1b120804030512041a03070207031e030201 68
    0x21840d2207444220b03aa00c906035140c984040c1d000c0c0e00040a0341c64841c292400000c0350107100381003443c0794440c2070368000341c142c4284a4011072707015540390810f4115004c003640c0d43c079074207540326100c640004111102082c2ea100c01061981b4861400c90850001640450104d880070b810642c0720fa5100e07030601c20b205104d42482800b5038150043d1140604240e03550310340368404140020b044034100422020882c02550507101c1c100c4024008030380c1c802492071420030310428044444085032248001198651181d403036011000a081408407040d00e40740c64082003010040300c124108100101811841c1d00c503200070f0012640300b611210089080c458001d8619114040c0101d250b40c50403004021a640b00400507001d99040b4802d18950040703049000c1c0000d06a801c116004042c508245042145800c000c0044a000300c0c20703030700c0541d50003100411300e1245114500c81e20300080c04c1c14110b160030031b0045800107441d004031a0240d03526039030024000d2415012161041d8101d00203414950280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609014055 1250 609012805 609012823
    0x3060603030408150c07020d05010914240a0e07170607080c0d2310031b06021c020118030305091006061d210a020a08010506010219030509040e060108 66
    0x8010390b09140c14031071030300c0d5200070005400b440940c082d408a10504000740441d41c00940140c0190203003c038508103a4081c0c482444210313000c0d403c1341c0a44891f4840400c07180130380001039420307400c8241042c0101d450150080c0c140d80c100c81d81d03020314820000707040055a009210380058078158110204041e030524100510010511000d402044003001b0007404480010356103020014003520300c204020136880703100580d1141034a8035414050740682508100b01101d110322401e0310b4111030300c10751150f4446030344506005039026411064448204040c5603001464601c0000f0ba041c21444108010003146c00e01079010950398014000100010b100010754010f00850910140f80703890750041030080b00d070b0b0040700c0b03204804280b8103240e034078110a01049929076900d8551f40c0402c2070f00c1c60320f511862104038490f82d0290170014030020103000d0030b4070515050b0003810041c50781e9070403503501d208120401c40030004200a80302d015601c9202e52419104414010704442d030506142d14906000a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609015305 1250 609014055 609014059
    0x1e0402040306061719030c052d011116032105041101090e040213050a02130f090b01020a0c0905060f060d0606020705030a150f0902060c03090907090e0414030d1505030606 75
    0x1000c03120345c0f00b810102d841840d20350305150188003000f00f8181942486508866240d030820301c00c40340900c0301e040b0b48481c002603030300d60000c02000316001003a00b5a40f15000d8040101c00d003d030650b20200e4001c04800b10f042100c00d849580304100400140100c1e64222412182003490800b0794404c2d59000d940b07080581008162003c150529400040d0038a03059040d03118000e80b14000241c020306a40c050f01d5100394403104801032a0348880b4480c60354091801400400d52911b9024030bc00d61001a02c10440e6410080b11021a420b00b00000050100107114540048201e12030b00700c661110001440e40074013602001950500b0204000d041c00f5080c1d001501c607902040210003c0351407002c0c541481180c0010004000c2d45001444024158800010398450030100d2030680440c0048010f000f0714031300700c40c131784603503501c020003690b81020328000e0000504031b0380006000104030480c10f01044614004690400249003480300542e2814590f103105c42001c000d08010a0804201c40c507082001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609016555 1250 609015305 609015313
    0x60f1a010206040f081605030c010e061017160b030906070f2a05060108060a060603020414120a02040e010204030c080c03210706091a061e1e04020403060617 69
    0x55880001d40e50400a44058045141c3d15042c80030409000101d60010410420824884c503045c141940c5a0b081810b4034011542801034207403030b191010610510655100c00019281801c00d401084a4241c04030000d07028480d04e00c6103e0074030001d400500080220f1000e40744d8a2400403800c038140600500101d05019218015030500c5070000d45255031940d02151511401d40100600e079038a000c0307150080d280f07004810000c030704850041000d40c8140d02540341840681e80c0e07450304801320310031440740c1c0180090300300b41d000e100e203405980c416450b411b01c802c0f902484907a40001d0100c40600c4420020707a9400501001000101c04000b40100305900c06080c14010303401c0866101c03540f5400c555541da01d00d21500544017144029213980036048101040040480d150207900c00e0400450300d581881240000340e61413501c000d4640900845210201000c0902001e11204414100c440c20080b0746a1a01b044291502d2014000550007900c0200d5000d03e019000044650101040030503a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609017805 1250 609016555 609016601
    0x60f030608070b0906161202061e0a05041b0f090c050f09090702150a09110f01090b13170307110105130b030c0c010c020606011b110f12030304060f 65
    0xa020411104030f4400742c40c01e541c0d441650000403141d1140305840c0e103802c569988000c041c07140d0513151544035020391302158642c0d141d1040c1010529501040e450890b41c0c0d120001d220582e00d40c000540141c811811490540c01000640207099504e80000b0b5003050041020081103205004a510050703584c14054604144492400e6241c07055585086c0950400004140064820442c00700021201c40030400c907424803010314800703041c0807007003070303c43c01d0101c0c2d41e03ca454580442c1d28507002c10b0503120079015624188101c0d09507048142e84040303402c2c42520000f810020b6200391410207034540c0103107a80e0b12040c0390056455003004a540c3c1005000e02c0840612085914048159039a85004070b440e0760726200c035103106116a00c140c6240f94201144a546150006403590040401762180450301140081d461460040404003502c000d2a00783c0080c00e606000045501c0740a0107030840f03c035581c02c04411461641300741c030112062607a803202d044106480e441081c5524010340348041c0500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609019055 1250 609017805 609017819
    0xd02161d01120f0503070c03060605040225060b060a0201060305121614070f090b01080108060717062e0905010207151209060e011d19120c0813060f0306 67
    0x210500a40104a810091503803e00c404100b4016206034004100d99070f41d4514940885c4405d218481240c216040501c0410715203854003c2da0303645014048200f100e52107407546008100025082610403550f606a03071900c940380c0070001c0462510540000c11514910700e0458174042c500d0f0400420190140110440000c5818840d100c076034010f4641c060080a003000325040c05031643c02116914072556000030400b80d00d030003403082000c003600c61201e01c0e039035400e40b40d460b900c0c120761500029100013843c0b90a54030101401d500510050500c8031010052101504c003e0348480801c19920f01181071500300d15840313600762000c0d08080c03019088013480c0030600708840b046100800180a241c2c070452034201565400498560b4201d04203000520090307103d00c1c02003044014041c0c81c80306074981541c240700300007000d115034140380341120003101864480451b4001c1061043c410840c07501100c0300845d0304a0b01034168103034182d400c1c8000514204028280030100784a0000303050a26074100400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609020305 1250 609019055 609019109
    0x81f050f0c1309020307030f050603150115110a08070c08070602030a0518041109010e01050717030403051308011e0912030e01060302090f010e1f05041505030d0216 72
    0x10014501140d01c80240d6810b140c00e01002d50820b0310150301c040304215040b41c5c950002000010351090030409030f1074034003c1c03589510980a4080d01040c0b000c00401403100546452008100c00e4906014180100c0701103905000c0306480581d158800407440c00207000d0000c40050080070100002e1402c03501e48100651a8014030310000107000010655448a4280038403d12050200170800c00800780c034584580400e0b00000714050010356184000d0000e035000d0301c1280d6a507074100000b150b1445540f00303030302c0165000800803810440b0502c05075100307244002c0c0040c05000c14900214a500ca04040351803c01c80d140040040642010307451404221200801104104c42e8a004185040e454074040d014110a510094000d041c407020050b00013408800b040c1a90320540e0044510380b60039000010b21400700f0541c1e200031904600801161400c2d0b030240c1002814802405403007070351500041c4c109140309a1620150704112880d0300c2e02201614843d02500103004486c80740c4007400d03001e41c65 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609021555 1250 609020305 609020311
    0x9050c030d0e13110a180b0f04030b07090e0f04021f050904272003030702090c090a030807030f020606030f2509060f0f0f0302090f150901081f050f 65
    0x841208156074011900e5404c955140c00d19032035400d50710880b090000300102c404c0000310908620034440402c01900250443d5005406403520354181801c1d91198540e102001d0541814440ea0100000c0e48040e1203800310311960715071070110003e1500c1d0050010403400b0300b401041000c200d01074825055040401c0e06c2d100e15041d1000142ca1110b081003041043c1c940c10034042c0040700707032080c000700501c1885a440c001402c1286502c83d14101c0181075403030203001d000075030000d41309000902040c030502c040e10310900010050107003951740e919801810f5010401c03c4d0300080455200000e55501081000e41244068000301220300000d03d94648030010810041c14149110501c1c100d002131020f034400c080c02940d031041122598400b240c5c04c01d82c12920880d80c00c400c1c115000103584a004100c0c0c0216038002e0164105a9281486030702c0908000f0182d4070301410320212042da5480b030525090203400600300400400c4841c002a03ca0340740f05c1d40c0da40a10501300380030002441c00c111803007a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609022805 1250 609021555 609021559
    0x91805010620070302030613170c0d11100f02040503150108100b04090803070206161103041a0d050f0a0608010b0a030215041d041a07021c111009050c030d0e 69
    0x10710b00446045550410b0030340d80c40a5814070a600034000e8039160071481d9210f42d4440c0300202c070050109441d600c114050100c5c800025003049240c84481406200042150100c041c190307040c0c02420100d103803c6800b0018103081c225030101d4280024103082110084101209400b400c06600d804030b6695100c0c640902b610449480f0030a4001c6500c0d42c1d00070030003842d0701c25000da881e490b103940020f695260888030350180300c214460060001d402059111800540d03003002e14540f50510421940300c400540c07060010300c07010003c10b14010003500c41d07240201400d03c810042420b0500450003601d0305500b001306241d1610141c0b06440d030b42e10b80880f0031294150707083c0c0003070009849010400d004070740c4800d442d42c803030401c5210b1b05d035408070540b80b0880c4a041c0c5009a4206141e055886400454400f00035912409280b10b0002a0072101c9005501500d0505002c5443c0b04409003810b40c5940018501c0703849940110410809001c1d8039100c00701070700241200d000002c03000b0300310800c08203154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609024055 1250 609022805 609022847
    0x18041503021c0f06020309250e04170d0507030509010e03190504050901171b180a060b0c03040f06080f1302030a0f0f060e07060c02150d06060918050106 67
    0x1450800150303840c8090141c000f490007080c44040c1c00c2c003401a50041b2450640c078020005c00b04240c02500c0b96401505501c140781c0c01045040152441042c0300c0500191203904d02c4511405080c840c0c03c00034010000242401b09141c100030390081d041c3c0c0c0c0003505036034a99041c1030100000b680000190781881241105420200011100030744184c0300c0e40d041389400881c4200040b031a41c8a40305142038007103c500032940a10000246549603a04c030043e540d034003820300440814400d1800c10695040040700d5000a9003035685c120340203ca0303100c401c0c080141e0b0004a400c20134080307070f13030021070050040b418007a950340f070301d00c40d40d0250b02001400000e00907040326803038041d500c041002c40c8802d5804100540940341e241070850032202d1026040310903a083c40301d01c0380728003400b02e028000c94180307449034804d49082d90708029520304030141a446030f250a02108000b0003040c00380b20010071054a13000c0340305080c411030610000c001d940d0354010341e00700001040a641c1c00240c0d9094064046005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609025305 1250 609024055 609024079
    0x240f050a141612050418110a030c111608070b04080303010b0313020d0605190e0c060c15040b060108070207150f02031204060b0f0d0b040305070201140f1804150302 72
    0x21190b602d41c010b80505045191440d05000d950080c0040c000e403415640c071955151080582c41d070903181d1204050603801000d0051400d0b050180d0002c04001003c0d0410131900b40390441c03030302e180c241c40710501b03001403842010802c925041813007840c000e0031518684030b1900b410400859601d100c10712800741e500e980000011201100c144581e41d80c0e82d8014002c0030b81c80c1450910314080d00060f04c0003035070102004400c5480031050302c9115002c541c0c820152509001200c1000269001420008041d0080d4882d1000b00a425040e080c0b2440c810500c4180c43e017000c20004200700002452102558800a4207005074101c00a640c5e0070000c85203010810b681060400f01d05500071302c18215060369415040c80704000c1190410301c1e6040d41551809000e1131010108409401603142c064a03000068004c9008a4850030040040a0042c140148144004003410115238000c4181c07a100942c0032501080d0b0b212009908100702c10304481c140600171600c0018030000c0000d10000384180070100c25 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609026555 1250 609025305 609025327
    0x7300b0f0604121b061701170c01030b010c15020307080f01030c03230303090106051e010c0b0c1b0a0b06090c030a15120309030506280213240f050a14 66
    0xc00e05052042007070342c20000780da403080035101c02c0005901ea03d0380c0d1b00c60400441c0464003c1508010005400003c01000444000640041100c0384140341001940b080d840b0108202241032a05803d003201c00598900d06600700030040d080107000f8400300040c4000400101e5052041c0000303403038001c500c84161065401c08040c0b1818001c40f00d000c1800040100700d402481984144c08446056529011407034610642800010340d0301a5540030a84180d041004240035401c0154012140c4120070700d054400c0d40302c900450846922445a6401400745030200081321f08050b410080c00e0b00d14105904203d0100c1d201400020080c00c803103503a034480d501181c41da1803002401402c0d007001c11340b5811000d0a00509a0034980400c1c1d6440c841c1401041c803000080714400e100501000c64140e0301c0540e8141140030f903001d400b400406074003020010078144e590b9100784450402043e9428510880c1510261400c8146445501030040030b00c1461281a04848034a1180450060295480c506891 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609027805 1250 609026555 609026573
    0x807141b060a0b0d0b1e1f0504020c0d1b021513080c01080c0705070302120c0a0b1206190e010902070210110c12210714010209060d0507300b0f060412 66
    0xc6c20701d1328070b140206001ca43c2a09003403616001000000203481d09841d001804140c0c4102c0300c041403a54030049406d501c4034071890a4806c10707458500d207000d0f0348020380c00060304510f0525546a103d40c0018000040d0000b007800711008003958000b0708885c0c0001d100207003108a0007030012198203000604002000024804a0040d550007040c2e5030004040c04a25603840080c42d2542c0e0080800007800308141e80c08406464520000b000114040c1e59420240464105038818108000302c1080d000f2580c242c034050004d000c0c0a000d0001605d032001d038010025030980f810829000c3c80b00c0610304c103165030b00124002004c01002c0d142052940c4801031340c41c3c5040c04d40070a80d55004200c1c00c11509403000c21008002c40c90003070079141d020b1610401024203d105000c1e04130740c8103504010030303039030360381c0903042030350301c440c99040c010200d84d540221f810800c1901120400c0d441e554000d00c01240c0a2442084000c03a01a10556155003810002c07540b940f090303000d41e94440341030816007010060800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609029055 1250 609027805 609027841
    0x305061804050607021203010317220b1c0203040b04110a090911040605091603050c22050102061b090d02060421050c120a030807141b060a0b0d0b 64
    0xc14112403600d440d003007503a100c07501621040d0040c040d14041001c43d4101e00141c9050701d4010040c0026081550b0b0010302070340c008191000030b62042081582c50b0558103114000402d50a45a555904540d156450244042e00000c0071003030310600600000c41c00d414222680107601c103804266201c4114002441989180d02c070100d00742c01c10701002d040080c030000c2d2050301e000540b020300c0340c56141c3c42004070114088851050852400d07280e1000d42c2c3c031035044544c028002e524801d260540058501d03050240c40412008810080c0a04000c02e5074100607199001010340780c1c1c8100304044a03100d000381d1141c004228401c0d601400403006656601c803c46008014100d5109000d80c000e40040340c0c2c07960402003d0703603d80510350046115003405c4c000c2151201001e40500028079150b0703016034160300c0280c95001000607140058038081d424100504201d11480a10b02c000b40800081c2480c060009000110311410326181e10003c1d2990040c180340aa0f120b8028a070958402c0b0450342201715070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609030305 1250 609029055 609029089
    0x160f2105011e0b04050105030a0816020f1c051005060d11041113090b090112030f032007210504120809061801120b03030d09030c02100e1903080901030506 68
    0x1c5503501da0000c602c1c1d0f0219070a94025102840344d03070799481c05c2685408000350040c00820b41040001c0290481841419880744014201160b0384003030300c041506040701c460312003803140e82400d031001800780c100715911480c640e403030b8180b0641c580714001c55500903031920002d10794134119602c580c1c0e5039a113400c0b00d001c4d4146a00780c1c54445441c42000d0780841c480b80b24503000645081c000303004e80e080ca103120318160780d0810007031840001c0603030b012a5110101c1c13498200b016610840102c8103560f20407034184441a18240a8036545207041c084000c561044240000c02c030b01d1035104035241e400c5803e40d4201c13004c6000120750b00d400e5041c400781c0f80c03050641c950f41c002e031f0020f103441c03d1000c00120814680000c0e170303400002011980c6101c040300c142038561035140c1c0c010700c00000000220f8000c442100d00c00d00d4400f0059010740e010940c5004002c40f28004554010342010741801d00c08160312401e012040980042072454403490618410484058101901c0c0c10018481d40c0f1086c40e00d02020920b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609031555 1250 609030305 609030341
    0x1b0e0301020712020d180302010905120a02090c1801030e0a020925030f0c0806090114150304080d110708030c13080a060504170c0705060c120c160f210501 68
    0x9002002512540714190980210f64010000c03070481748101d0911b4140c0c0e50607110210424100010000b52005c1c4800349021071250307000074001a220744001d0b0b40291a41c01d80e0071344079034120b0000c51203040c184803070604241c985002c0c0400280c00041d04424550107407070303040668444c40d0b50950000b51614880710b080b205400d007039480c40d80c558400c0c40e41c6011000c042003a208030200440709620705030342c0a9401307011040103000c40d03a102030000c81c1c40c400c02401010b143c0601c1c4401412500112000d039221200420a00c04442040c001d92060b01800c40440d8a0540c256a607025180800750248110300c501003440443d40610a40f400c01034031a02d0101c0d00300c05181c0c0f4100340070308070442d03045418088a00700900584483d00030744013603d80031805000c40d14100014007010790000051010380e8842d0340110904025450020701c4440780b080003400025041d0320101605131f1582c4c0c03203051a00f4506000700001e40c520040d0040c889407644000300402c05034103001d4058900d0400b00c0d240d001d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609032805 1250 609031555 609031583
    0x3140c0a150e0d21080702070e0118110c01060e010f0b0a0f08040201020a020604080a060b0a1206020f09150711090708010e040c1e17010b09040201080a090f060c030f1b0e03010207 79
    0x70300805da00384601c440e9404c90380e600f070311a9035880300403d003842040075406a0307030110195107805800040c500c081044c251410101588102401e44074641e20a05101c003441c4010700c4419049051800039003290000c6a00c1c1005c0584024407003d880c0466104010424004c103085a10078843c14a100d600182a0303625162241d01341070701c40c0b0070010304840d40d51401c0c0c4071026504081c182101114100c04045020b08008d446180103948071803004d10703181701e08101415044d91441704030940320060280040e114003852601d0018104840c00481c800c5101104002c00b07640d104413054156140b40d02c21020580311440d00c0d40030180e00b40c00c0b13402091075440450101e140300301e0040040300c00941d441580c041c001d0b14a01e08903900312040076045003c0e100040d01550252019a80244425000292501e0a40c440c0b840702000307040700300c034200d483d00d1190b2641603250042a0a14840c0d180410041401c040ba44204001c00700100c1c051181000708442d590b07800791b06443c10a85c00200451b60f1075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609034055 1250 609032805 609032807
    0x70c210c0611060603010c1e0e03030d0603031107050604090902030102071a090c0a0f0e100801020708030a0c050c0d0e010e0301052a0322080403140c0a150e0d21 71
    0xc6890300c0b00190610680b030005449190501480207076510607145c4c441c0d400001c0400c07211910003414008180080000005400e440c00c000410b455041c510000506c1c50039403500401c160621551000140c4c040c43c800d008954500c0b00b01d9084401d09a40081c404040348082070180c0103030a0082c180b0041d401c1c100002600164255100342900070607130f08a031000c1003c1000344816805018031b070503400b820502c4600104040d042d00300c010b0041c3d14030f059685e00c5045e0b003645c0c825402114019800700c00c0c0140952a4080d20840024a0400c0b82c14040c0c82c5800558440d2340c14031410401c9000020545140d00070491203201c5080640244107926005d01090040420307181e2400c0c10400181000d040100c41d1800c0e41c0c0921517601d40c565101220020b0440005078088042c1c038511790810000001030000000c0707100d218446400703040111b100000304004540d955000c50b40d00007007101c4c00d0381103992046101d07000c0c96080700c601111803014140780304041c400e030b112a0100424480303291000c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609035305 1250 609034055 609034067
    0xe060f1f0c1205040605030a0b040e07062c0303090f06090d1a0105040c020303180c06040303080f0c0412031d030d020f0616080c030703090602030c07031202070c210c06 74
    0x156008050042c0301e1010164100c3e80303031080c0c0c071500d4001242071010403c5040903404c00840c3d07060040c00482c4a4640055039418003509a2001000c08d01c80d40b000e104c0b901e024508401700064145a6009034085c44020a0f10303403044503003540c440c43e00450380c007a8a940343d60540d1807802019040703403440c1c0344900d00800f0b1011004103645454803480300001d02c9107400e00071800308845981c0030314107680700c40e03031600070240901d402c02c400380c0034404070052170f0745400c001f400066001e41d80d144c0050401404800220030050101d808540040205200c81c4c4080b01d91280101c0e413629000c81c0280030340034103c44030782506040f2030b454041d0322910403486500103a4201c50704824010354485032200701c00948802c50009140c2d012a58a4000444000001c0091a40b0050324100410840c0c066590601244e00c01c0741d1a0540910106801060642c001a07001e000f0303c07001400c40c90701e01581c0321501c0c000c0545c852801070003070440400000315588031404203130700d84c8000c0b002c0003561101005840c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609036555 1250 609035305 609035327
    0x11401030f09030c0b07020a06140601030b030c100e01091d01030b070e0a0302040203181c020f01020f03011403030708040306021b01021305040b01021515190e060f1f 73
    0xe410088400401641d601c2503294107030385610740881040c4559250710724908020100c000790300480f8030100c0814428056039880070f40c401c2c0c600040e460490002b4040b101071140980c060b84c8000e0801c40540c948000030703501c40301c403030804007008002c00004941141d8250040e03c05803510301c0301654018410000941030b61304ca002400b04c56a80e03e05d00319012003c2e0800140e00ca800c1510810160816a00035a0001c103030040100020082050f100e01d07041c164480070240c4ea42c0d142d508211954140a4445050304000c001d6280000b50360b0704d03c50074081070240e000c04000310080c03614141c2e0204115158907070720041c20b548032682c908080b070003904444ca00c075800c0e011703660302380d81226010710071203d02e80381c2100e61209150602c03082c40020b01085c03c080341980f00c0e01c549025640c5031111014420748071442403910000c40b610501034a600240200d15aa0b0981081484492042c2c488140c0c003560a540261444c48074000044030340c11000078012051b0388903101804665440304020038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609037805 1250 609036555 609036557
    0xc0225030c09091e1713030f05071502030909041e020316050a060905130c120e010e010b01180611120c030a0201060b04140618060f120921030a060e011401 68
    0x1d41c01280c94043d01240501000060040854101d036000c2004d007031011b400c260303035003442c561b1402e07840c0d540e1003802d1200e1050640d00c0da844403200708403111040e44150303000080f5101560034209030f6004109031460240000303010200c0384040c40c7c041108441e40071032550300201198a00021416403012140e400d006186c010042d48401044080c0105250300498101402c0c2130081800111408010021090a4002c0185501440f001c91980c2e0140c5500c04100c1000040c0c050000c00d4801e084565040c2090b0500103807005000740905005800703c21503e01d070500c80c1c51020038030103841c01c01040d418070602000e004a075050445070008094000c1c2c21498000b000140d0711004105010b0045210784040c1550054800c056411720748060040c01c0111304c018010000402c0006040c0e422074090b2070304003000804e40030f8240303107400c91080d0401680c0c0f0151082040c44c1051500251041642c0f80b03032140000040340c2d4105113548090014400300c00d541044e543c6901030180321460a071080d41c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609039055 1250 609037805 609037823
    0x2503030b01080f0411040f1b0327120219030c140106030b071202071505060a09050c070b090c090412271205070f030803040c090c0225030c0909 63
    0x4030306501860031103008854015401e009542c85545620014000e0780e081900640c0344c4c0741036241c4010703e0240031001d2040b56001800c07000700c420000c044904400402680d4800101c52a0300301014103140c40e00c141d0440041d41c1d0440b40444141c1c901402030078808a00084ea01940c01031581c4015100e038810312968034844403031404004542aa03405010180501a00c40041130342240031341039200980f070340c2500c0541054482d07110840b40c1e440c40350400c0010f81e110390030001d40f49004565103000e0a041902040710f03003440e408400e018006c001c0b000b0800b030140c1d40800e41c03051041100740d5aa190003003240b180307440c0619080a95138044881d04c00851200070751314483d4602030140c049074041405890709038918103894404000b03440ca10945940c01106804107000c8500c0542c68059401454503642d282024502030f5074580311980020b2103140380000d217010303a550204640459840b00100150182c0860508041c483c41c294030051840201010004845965070480010140941c0701c2d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609040305 1250 609039055 609039071
    0x702160306061a190e0f03070e06030105010b07050c0415091508011a030a0b100e010f0f0506070b070c110d0501092603010308070503190c020307050103020a09050f0303250303 77
    0x100c85006602103285002c61913414480840c0c0f10b800c10042c440c90003081c2c284040b21402c00319043c03100d2034101590320416003003041250704090007414010b0040345c41d006d203003c00d65120242c8807104494660700c0b40e900c13488041c004a4101c1c0c40c000180082c0b240400450180e0041c4100818035031044001c0c80d401d00659408001c0500c5c070318a815a0301801402174001c40b95240556064000c1c0000c45da800301d0031700440c07626aa202c1590107880c486003030385c8502d814031800080540c0c2c1d6a10107840f500c810400500001d4807125000e030070000a062181c4007070070340e28000540d0911100880d070040e440a482409000c0c054020f00181ca0003820041e01107405034244441d0003011034022600d0090400c01000000c15000084c00040e0291041c0e905041c9002d054800004181d81c11200107413a44c0449425440d007400540010300d400d0070118a05107058102034007107042442098803c0740701d01d00d603504a0300c062085450030318000308140402c802c2c80500c500c0001508100390002464001c2d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609041555 1250 609040305 609040349
    0x60102121e0f0315150d0f090b131407151206080111210c0f0a030204091e1d07150c05010f0509190201080f06042301090c08061503070216030606 64
    0x1040e1160340f5071a619103031070071503070312240071f0411001c01c101e426a841c0300e40f0010464000040e0b0290100006100802900e070a041c60005004d04400210740c00100040080c0300d03082506003240142410498a02000403a46000410556001c80019405c1461982d04281821700800e08641d141d0b01c18841c0c04261001320351020803c48c0d08090100e0104640070030313401600c0180c96454010326016140588a511a60903561000c00c0d011004940b40742034080c8490741c4c00ba200703458117a2213a0301d0080710035480442d600d585601c600d00000e042040306d248000c0c81108842c50064000c0000c1c88007240c00e01401e030040034211901002030181c40e2804108803444190b102900d60165114882602c0d450380c82d0440050203480542c0c040c0e92501c10009841d1700244581c850340076031840310100d41c9000341c01d505556a090100c0100100f1108000c9585c0d50070112070b82d5001d07051142c0d500c0344d8880205910f01056140c4078100d0980d440c00001c00c01c03101d90003080030303183e8402d8800a800f0822030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609042805 1250 609041555 609041569
    0x7020d030509190b0d05100f090902040b030a0b01051c0b010b07051603030e041503060504060e0c011b140102120405030403380907260f06060102121e0f0315 69
    0x280000344008000d07a000040d52904402d0f004a0400603c16003c8d9440c49051540d04e084e500c840c25482d11000030405524142c49143c0842030305402405114213a0355641d417a05105008580c440c0f005140401000d10688140010380c41d400340b0851107550b100d60541380c1c26001150b08880174030441e6901c54521a0700703100c2d9001c403a456160201c01680700d4007040080c2480da035000740c950506143c000301065583c003030580201d0046c4000544000d00e81040c0341480600c1d80b406040c0452880c0d0155100c02d0703039115180a40c0c012609103114103125942c02c0c007a11882c0c010640040c580020b01c018440302200070001c691050581d4040d984001c031100010204042d90246182890700c410608251044a0720754480c080f04184c400c00341e1605003008407180c1a460071340c0302c1e0705c1d00c82542140d10801c00c04081c813801c2030801002545400e00000350340700204d003000c0e000c06401044801100083c1040c403880c04007920b08154032540203290f122451b400413a41100104018220b120507420241 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609044055 1250 609042805 609042809
    0xb03010e07080c1f1202190c02130506100c0501020c1f05070f0914030f0d0c171602060a02010b060403060504122309060906030a090314090603180307020d03050919 72
    0x4c0800200c0b890400003550840924071031a038100344c0030011030102c4e54015507002c0030983e154503910040340c010f005009165005066012980b4038100c1480266500c14180d41d01588180c41e02c0c0031050114503016000e8011410030540301d02c64200361035000300c0c0f03c005400b41c0c541c01e09010061666072250131200c0b02007108001c00444c4084c2818003060340c90440d007403c5000050211801500680000c500c0c00140d0305031800012030341e41007441001020111702180c086240300d054286603603000c1025103486c1c4408000d04c43d90000424100c41c0e0700030741002c1c00c3d140000708030340d484130b64a0401e031024140480e0100d4028000c40c000d817000350b004050580620310341d460402c5400b46000c256201503030000c4640e59000e1820700030038110355034000045100340002d00340400e07800e10b01d1602405d048100341c0c0d500b1811030184000442c035100d68060303961014041d298801d01402c8a04441c2c00e510500c00081c0d00301e01e24207000d0083c50b40110003800c500c1c1003610780d40540d1054950003035040f400380c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609045305 1250 609044055 609044089
    0x510031503033209040f09020a09091b0e10050108070806091b041d0601080106080406051905130c0f0b07320721020303070201120b03010e07080c 64
    0x80001400424070070450f00d40c41d080c41c14400c036085442d1841c91210100e04443c8107602c0000003c500200d81400c0c0210b40001e140c00e24280404120f560000f208421503000d07021071a50341d040098148041c00c0c2c600283c4114060010f1080d40d11303240452182c1070101c40f00680040700c441c00148551060000911412050b0384d046603d480d006c0c20000503103000b030440c0e135080710700080c643e03040c1081e40000c00050209149124801001c1128007032201c1c03000703241a040c080741a00401180e0340101c550356000780c1c003100c00507203982d03800084d00351200a500020368280c07170f02040205110025012520b01030007440c0d04030f402c84c1ea400e50034080c1e80c602d0054440480080c07200c000052000c540000240781e2000700031001146011040703a8400c4807001d40681c66218010170007015105030181018001809110382e50341c3c207140c020940ea0310401c00004d0420011041c50140841c0c194000c6010502c020000d0140185814080b0b0307841045029059850045e44180d20045c0b900c0c01c00c0c10b0800e000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609046555 1250 609045305 609045341
    0x3010f030c0b120a090303020c01060e09010e011803030b031623030601120312140c120601020d09052419020f01090b07080403020304035109060e010e07051003 70
    0x1c4d02c030540040c1410180480c2815024080110078070000e0003002c010f805509214600c51804210050a40714a0108130045034501030030140e00310100300b00010b5250305820301040c000c04440c0464500074105c0c00d00f100d280141c08022558804a42681d90080070b051340125002e14510109601c0d21401e00c20411071007001e4240c400005d0181c9151700848110f1400000c0c580c16441740c00e003070404125407541d03125100240b052542055280120b401030402e2000b014210302400b0041c04031200ca000300c0e441400c0701e00d1170170603100c1603000724420448103000c07594503441c512681c8001c2c10b540f00c0c0103e015002d8000b40c5412008144a0342d40703c190480600c1d1700c181c68420381529a040064419400c6000801c000310208204c0e1441d8802d65807103814104010144840d2803183d080406a400c0004c03000005400a9843c03d44c840f07454108800c0340000d200700e15160100c010001040900c2c9a135090429201d140340001c00d646007100d070259851507000510314001c80442e40f6181c50000344800d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609047805 1250 609046555 609046561
    0x2160504110412240911060d15180c03140c030c0c060906071d090703020924090306011707060c02010e040f050103140708070b0c03070803010f030c0b12 67
    0x34003900400d0109140115461030640c40d0030036508444010341c2d082e02d00344503260035412070034100525054001c004041c1004a1000e65032400000e403460410139220320001700d081c0d8038598281c2d000750b50300c1c0b030011889440380340d5a141c41c04601401c1104450303210710f0020300f280f400d40680100c1007400d03000e1009420b19602c041584e0076070303000507008080d410300a1048101a40b8100022409941440028140c61400050040207094017185070175801c2a030364402d031240d84507280015080841410050f890f02c00c43e2000c82d20b50501030030034500b0500c0c22000c144851014400030700740c2c210254140c0f00385030b0301c0c2d079502401c00500103a1200540c3c0304603020055140b01d45281c0440b1481450101540d00c00c1e03100040580311035100b281000c5a50384010001c03c00e05201552100c0e01a07805441d0040c680141c240e203494281c400c3c075034902c0b4000b60210b00000d0900c200d1703c41c242c0c0803920079142e50f103c03c002800601c55010881d107801c0d4134140802c1c0c5240b0401610b50b01c0c14070b400b01d003030165 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609049055 1250 609047805 609047809
    0x7031e020703031506120f020403050318150403151b0c0803070e04050a0509011a0117102612070809041e050a020706140f0105190803120403030c021605 67
    0x5844540140c00f05980c8071041c1e00c140761100c14190041106030340d480002000259103004a5400001900c0358502c1004104009580441038400b88003014180030451062640411607400720701000d01c200d4074000034080208040d005050b06060f003030810810031001000400a0034240070040e500100e03110b62116000110f035a03008580c442c41510780f80300800307000c4001c5002d440d010744821f01f115843e801002a0311400740300714029625030440794000e0403079800c0040c0c00803901c50074481080b883c50780054001514403160800500d01003134400203500c4a030342c3e03c0114020080110b10107010f024129005031003038800703441c61103801964241c60070056004100050125481d507100310f4400080e200e0381081d4621584d4400e505801016903202102d01d0b2185c1245d0b038426901003524241c0e010f000d148040100c0017810341380252241e4041c40001000d203814401c66500c0ba894610000808294200c0301442d21406544a51000d1181044d044012390700c4072620002c07c421040030100401481c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609050305 1250 609049055 609049057
    0x21203070509091005040e070608010b1308151e0c18120a0c090b0603010b0702010302090d120c170c1203190509010603021f021b1f09050907031e02 65
    0x44016401c2691904071404003184544004440c040030f650321810040050f81001d02030302c0a005e07107c00141100c5814140e0240882d50107008840c06100d0208800d08400341074034013100a0010309080320070085241840413051081101e428030100e1400602c00702503415006200e0003414410750907800c1c002d40707a9160741c4003500c000903103a005803c1a1104440b900912508040600900794118224280400c00e401c3c0c650808810b03010b01c008000411031702407002c05583c00140d0919025aaa1055100241d410140300101900d042000e40a1203840d070341002a840b805885003c0000201c1030b0034a5007411070007012083c0c0ca6a401c18080c0e03120400e09040296404144503010154035404220402c04030f4004607800902695200014820341c1741810f1008c030b22114681c141d00001503020070003074490088100e2400c4419010364004280c1d641d11103201c02c0c0300c030b040340c1e1212490f104440041c030b400d807144a410f019122010224004030f12a020751000b60302544c4c900458060049443c5000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609051555 1250 609050305 609050311
    0xc1208030606070201031d01051005010e06090405040f021305090c01031e050619030501150b0406020307060903211b050c0c0d05070305060115020f0a110d060e0316060615021203 78
    0x109079840781d15034061042203041d82c90311f894003030000a10323141c00c2c000b031075881c0c08a4202c14144144a01c18146550320032080f0351180400b034402240c2380c0c41d1854211480c950a0800a5002d070040f640d120044c8110b0788141e10544100003110840c4480318015000c4801010200d0311100480040c44242d2081e030300035540000c005400f09141000130041c4281c03500241c1c00440b0a651070340900c0001442070344c45480070b000080d000c10300e0107141c020702175502d00c15020b0003890301780c60f00501418140204200140c24040020034100d00408081440082004400a111521082c00d00350545407044042d18a1100b00f10000c000c10440e032410000280740600080364244541c2d500440041e50612502c2d009084007000c4440000050328007a00307100d200724682e181c41c1d10014901c1d000c84d40044104079284000da50024590105040c0903019048601e1000340341d2000268400b16601c980202d003040c10b003e120200001c9440d03030322f0400320508000780c050040e480900b5001c40040181c1c02550 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609052805 1250 609051555 609051557
    0x1230721080f06090411031b03070b040510120e120406080a06030209180a050a0f0b0f150409021906091a0f041a0c0703050604020a091b030c020a0203011401030c1208030606070201 79
    0x1b07101320780680040c0c83c16401104100c85040244400340040c1030402950016100c07e08006040c01c1c20a00030030700003c0b80704208400c2040c021042600000d00d81d11214071180000190752007640c80801000b40d5901c5407044100241c07903000003943c40606c0f4030465041e2035008002500c01e803110035944400700703030700313401211b890054140079400120100301803a0043d20900b00c207034605e241810f00c4108084010031401071400b18070200590002c1071140d1175054841100c00003961822400030800562203041e52030001007142d0404110f10f81c10209180880d2880c0c002071aa0250100b2014854080c0e10f005403000e120a0105005000040540440482000066030305100b001360007d444c142417640180c62a4108105100a600b80718a201029002e282000d10110454030000c401404900b14041c1c10181e80d9851600d40324405e001000c2d405070010003e20038140c4001c51445091800c0c40704555040c4245000203014401d241555451074101c1c04580c11542e82030b0501c20304c0c3c3d0001c0001c81c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609054055 1250 609052805 609052823
    0x1020c1f110d0608010c020303040c09050c09060c101b0c06091b030c090507110606012d0816021218150a02030a030507180501230721080f060904 64
    0x1d4002a0100080c1c892501020004641c4a2901e600e903400c503900300214a0031500704004010200d07486001035400c84088003400603499884030440c0b540b07402500c2140d07a0159000078000c005540004a810401c00105010044c80621540d04158078506240220100b08451410b00200e4443d500545054bc0111820501c2c0c20401a00950b2408150021101e404200380b0600051120313108880d40078810b070601106080060b4003d541c0d03a40024000b03810085080305c01a050780c0d801026009412910304503000000100e02c000d0a400300854900302250020400300c03058a10010b50704003004103800c01203103400c0300344100340c800300d00c0d01008513000b45583c501703d0a05850340004180345800781d401303151600b8202d10700030159900500701c0d40403c0256202c0c50112202ca190748012640f007400d0026201e072a40302d41050320118602c07031024040c400314800c0c044c01141c003591100743c100d030303909004007500d80c00058038420010b0711140300c407699200000f50707282001c2e84015080f1307000725032076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609055305 1250 609054055 609054071
    0x411030c0f0d20310204030206042705090f16031a070309020319140a08030115020f0601060f080106080112110d1b05100c02150a0921030f0201020c1f 66
    0x3040c420800b44441c10451101010035076000d80305520711401c02d04c2801c2003035282c549560001805030007640102d40030404110707a035080c90703000d0b441c00c075400c0e10320181c0030b00041c41c111b1902c03030301c88140744103c01d05070140415440408540e440c0c004d0a5076403107980c40504200c04003070a100c080005120300c050503a50024580940c0c1c00b04001a11103085588585155210380762542040d1030381054544154040d028802c005190141903c0c107640b15940005004590201308030315000900035154414020080086100d0354004000c40543c2c0060b160031003030343d80c7c503030080390781107001d01c40c080000313148214000004281d90015501c1507401081c062a800150700ea50365407208441003900a074032403a50030499030038003181280d64107155013810601d528480c0c0100e050134041c0c00003410b01c0000056143d00c0180220b9806018000d40383c1c9400e105004142030011092480f03400307401181544092100b1a40705008803112003195030b02402031091a4501415072000600580d0310303054440c005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609056555 1250 609055305 609055309
    0x16061e02030412090504090210081e010902030105030115060c1113020a030c110c0102060f0a06180509070f0602190c080f0109110105070803010b210411030c0f0d20 72
    0x107580124002c65424054541280e8080c000c10440e520050207241840800d00159030b0ba18440c0341d291005040454507641c848020881d80792000d40800000314030300b00049450340307042d03000c4c6050391000d8008114007101e400701017003030000d2446418000f0b94190740c0200003901d2000003c500310350140c400d81080100d44003000c280c0c0c01c102e610b0340020b40d4601400c41c0781030740000b0361194802c104001e0609280c00800003521890b0017031120384106205000f28940100079809200104001100354400e0307072403454518050f0106440b508418401c0c0340b00450381c5140c0440700b404031001c03900101891010511500041100c40005a44035103001c040010000014000302d40c212074400c0001135112140c0c0780070300040541042290402109224240000300303c0801c40c1d040d90301e032108040c1c035030400c580e0303a6000c1c0000105c008001252241800200b0004c064207006400044041c0c0d04901003201c00e004400118100707007503004c08002c440d030004c610f010001180b01000c4142002000804da40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609057805 1250 609056555 609056557
    0x3020c12030f0402090a0219140c07030305070309050f011d040b040612050f0102030106080705180613051f02100e070e18100e030d020903240907080316061e02 70
    0x5116600c2c010700c20100011490302c8001c00758440130400003142003030540441038507050b4802a40e01c040c0041e90045522501a07003050b14902049034040303e001c180c0341e190040c1581c001200c11004103044d4003000c00e55103090b90f484420910f0682d00c41130351240d501080c41e48413400140094026982d54100d02240e181c500404020f0038002204134403900c0c0a14100380f4142d1407440403000d90341f040c00180724407030f44074039603e400450920f403550715040b0841c15807504408180c1c149500a400240030103840c035008407014100c900c1101c8010401440440c2c0040c91908004008010b070031030044071900c0501c0d0b51060711889892003c40d28001d4071400b100d1800c0c6402d95001c0055a00708500d45803541c410464003400d002d12050a1114001c02e0000c643c1d2401240c8200201caa0040790180546e01c00304a10034020a60b42e28841c00701007103090428641c0c005039401c056030f00030034901007004000041110400100407081c12544e1800b07840384002040d9401c13280060754890041561541c10b43c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609059055 1250 609057805 609057811
    0xd2c03090d21020c0f0103231905011203090909050d050d021c020d06060c05060103060c030e010213080706021902040e0703230c1008041b0b0d0504170304020d0303020c1203 76
    0x500200b2500d82050104405e100c3c140510b1030415040400081741005050f0400a800d80f08044050342901c44101030403080c0a20044444014a42800080d039201c0040707080302c0590007501c2e40e0700125100d840440079220341440c050b040794001034002d440300744588010148050002c60060420303550b512554038501a034490441607640104204148480034800c000c0107005a0428285107020b954403da00c8140c14880604910703a50340c0900d0800380660488800020040000c41d956495850f00c0074480c9041e0040408a100d010404038102e4000a604055070300000c083c640ea01d4921341c02c00001d00740965403c415406000c03000000155110030b22a0f0340606050044141c1070f60b00861480c0c5024000350034480ca201c08101d0300d819800200e0250042d8001600b44c0607400e000006018016941d4404400285c0000e402c42990700c40364002801a40310b0f0030209001c0d400c50821240e640016907019500040c0076a8182c00240039a00419001d041182541d041c2103a4004070300c0950021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609060305 1250 609059055 609059057
    0xb2209020c060f011d041b0f0608070215090c060f070602121f0302090a0504030e22060f0f0512010b0d06020703080f0c090d02150d2c03090d21 63
    0x102e41880302021071000c1880c0034110000d80d00500059046402444000c040c0c0090705a8064451600c0c90b0f00d104000c0c40050584000041800b594481e03001b8a20141210007130014010f00c03401103000d5001c030800354080c140a1009200800000f1f0412a0585c0b0614050103540003c1000000241e20390028201c02d60b1614000c07041494aa03110011f840c001103c51380d5421407510040c80182d8401c1e072030980154588100240035660b0340340a4404800da01700680d4803003040f0201c0301d44451410207487d11b882c0c0038802032141c140d85184c0884180024040c10300706d002c1d001c005101c6070400c840c65800340e031080d1002140c0c0900e00c0c0045902180e0311041600c241c1c2e0001400703018180c0210415070001070145101c4c0d800c0c80d041c516400c0c0ba000e102c120034410309481011a0a56540035141040208900c001c00d82d20b0701603c500c18001d010000c008484844016080c903490305848401618242d5040091440c05a288081200710032170218112101c41a4030080068030b62203040e41c084008032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609061555 1250 609060305 609060313
    0x141c060f08030c0a0809041e020912160504051b03040f020f09190e120c0c0103060b1c1808270402070c03060c0c0219150302040b2209020c 61
    0x50000320100414941c01c14403050b80200900182e0703420004944090744d03000616552103d00d01c40024015083c1140341110a801011400c40d000d4496070003003800c0740080395001c980f00d0300109a00d807102998490b01e004400d450b00e08000e60704040e00942d511000600300704512249201000505d27820030380f816540c60312221102c0d8114203054002902c1c4000c110f4201c9102d2801700c0304104d400d40d6541c078032001d0030f4a444002109880400103011a41d182401c034a80b107085440d40c181c1d803014112040c500003410001f001484040c5107040b42c01c82510200040c500401c1c1ca9903034006021000101c15281741e42c0110310340801c0030300c0003500d43c07500391304000b4600c58000c601c9210184c175070b00c21035403059204104031700018240105020403268841c1d800b080c1164001c0b0300765085440218060341008100410b1006032000c5280b9101b540c9024020f00780c0302100a50841c100d009600440310401801c2000f000f2340d58410380d405184004180d0360f44243c81d00d9510100c242d822a60800009504c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609062805 1250 609061555 609061559
    0x30601060f090902031614090d0f021008060306070c0f0b0901050717150f0a09050c070515040b070804020a0302040c021501050d0203070501120b091006020d090f06141c06 75
    0x3070b1007010107008000e090070035425424401e489070b0807907a4500e420020b200324000403051501d010429101c2c05100244109074908560401e000e0201c2040412485819070007200c08040e4041d4002c3c47c062900500140300035030b1103000580b510352502c90251010808800c564001800600d107181c80360044400100d407e09125902a1490044020350f0440442d810100f08511540c82e584504d4800b0031034000c102498034001152048040e501300391405800d001c00c018410180b58000d2078101d2061048400c030082c0c0c42c0e0714418049086d24010010500075000c00d483c01d224001940d0401c0c00102200d641c940e807580080d088608420f444030142c1c128008005240300c800120300e00420b4140c80c40502d002441c1e0000e61100c0c0c050080e94184500401d04c9441d0703040b9503001448c1d100028011200c18240b4041664140c111032148800500c1200c03a2145510302c038420f81c5084400c1058031f01001820081c041c0c0d51001108a5001a0102801044c5540e024032440c44107210001c68006034042c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609064055 1250 609062805 609062807
    0x1b0c0301050a3c09080f0409060e010f060816031805070503190b18030c010e010510060c0b010306020a0e0a1e061403060f0a090905011413050303150d02030601060f 72
    0x300c480b5840185000080480052101441603014400c90003c44000f80708401c910700401d15024400c1d914007001c0020401040d1500560b001d042038843d00001001141c0e80c03240e400d0501c0c122030040c20005220540400d800011602455004848900740883e06000480340244200a4084152035560055008200300c4c01c0c2032161051000505c08184100c004903250051072040c09404040301541d4091840c0307000c80c0c28803da071100124540240452080c0c02140750207040103031030703444119800c030302e0004049002d0340f01040129423000768210203a2075030322013000941003100c41d0007d1042250902c1e801f6a80d00071610040d0a8a0009803d1008040c0c41d42d00303010441e800800c00c0c04240008110400015000c1c0d0340d11020071650305030030b440040c000c600514459400340c0380103400c3c2910700b0100071041d00324004488440304141c0150f034440407100b40c48040b00501400680080000c11040070080005c070380040006082c0480d46421940441e01d4000264041300c005404040320300095 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609065305 1250 609064055 609064091
    0x30507060f2903301303050d0c0f0611041a030103050c010503060a17030d020a02010e0f0d09180e0706050a1b120e0d140a020406090c02031b0c0301050a 67
    0x700d1000d007600807520b8125000c00c2d0380c1c040c04800e000e00d0400400039140c0c1c081c825444502c0c052442c100072600c488406038012070152a50004072130078040c600c0055041803107403030481141a0400c1e078000c2c01e0004e40e01d8460080c0700000843e045004108000f2030800520490380b6804001c0515460713aa62550400034284800803429070b04020b010420301101c0e5035004070b0503003503030350504062140059800240b0310314400d1540100301d01e80045030b400c00d0943c040d48480d03101c0c030883c001c1c2ca80e8151403111054550940c1000d080c0452840f400130310000e070001418560351101004001100368030350301c040d80b5050099210600007100040d845404540c0070303195010001c0101c8004440e1185d642d168103401d4640c502c0c210070001000350f1900c450741c0300c202c16000c15810a1202c040e454042c030714152550b03501c02040e4000e908100d8002031602181c494040095080d5014500340700e01102e83c0f02019130001e050701142e220b00744107507034142c0d000c0c42250301a040b45034001841840b1318040d1040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609066555 1250 609065305 609065351
    0x8030f13090506090c0f0c01110301150f02100e160f18200c0109020901030b18160b0c03130f140f030c040e0304090504080409050108120a0309030507060f 68
    0x16090030b12080c80a25203500c00c1841c0c12440c071003112510340c8400800300715107014507038403c0e1b465800c0590038103e1107048401141a20064100155200e50711101961400502c00d1a000103a20a1040c2c901c2200143c1c409140e420314002610586088107012031421075043c0c211061441555608000440008620945050b4801011f0210354892622142e0314002e03484050051400007850f402108029403140130455801001220a96140d081028203580304a0f204000903030140c000e030302c0d00000011404403211100760800f40c0b09041048281707150b007040c468180c4610051107007440b40c01c10300b06000c0140402825120401d4506402645482c0140054500500401d050f002d12600d02290700300c41c02400b86c42c00700b01d6550008149103548940d03405170100782e1600c0300b880700700034440c6c2c018001c441e81807009000590700e542c10030341c852440e10112032103050208105100e09010380c209524940c000d08140b4180721140e29220705070780003d0b01c24071003182d403a84103a0482c140760500c505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609067805 1250 609066555 609066569
    0xf120908070b040e060604050910061112090f0303190806010305060402070807030f09120305040e1e041121100615090e0a0207020d1208150a03081308030f13 69
    0x1410303450b01c2d0801019200354000c40ca100610b001c00218a6160001154002d0001409180c0035242c00741204811060030f01034000000d82c0c458600c00450700020f0300c0300e001803600c031440d8504001c0704200104404031052541d0580810700c5913642a540b0701041c212001d40984039001c00e481e01c00001822a00c000304040d00c545c0c8140801d07008502d40c1400d844140e6818102000c0d0540540b03010f42d8018500d0b48014080ca207502c9450b0101079000002e001101c039800d030364580340e4550412044003007041c0358405903034410940000d0049680090344006807030000c0c0009014008000d05910035000c800804000c0f64410081d200b100341c00c03072007040c0007400707071000e1540c0c94121070a0040c1421084c2c400e0780601c00100700401c01520103a03040ba40410b500424103d9900039529290400403601c00240b004a50030f80300207803002941e0607104139900801001219000c0c11340c5d07150030b502e81100841c4070241160034400f0500a40130401030081c080c102c841140c0310b450905408070b00e42c0c22500582 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609069055 1250 609067805 609067813
    0x50111070b0109020a140c0f06060901081c2c101701050f0a080712170a0207150e0405090f0f071802070317040b01051302071203050a090f120908 64
    0x350100391545549410340711090750142e81d54040100444503404000c8146030001c0c40098403c4e100a40042c031320b40960040da0984d6580d507260400c2150701c1c2402d01c908450b5801541d00c10b600c07074840142d4282c00414a00303021f47c2d01c040000403503200121f4010180008243c4c003030b0005031481c0501c1c5011380e1070f60034a0880400844c4010003406100c1c1071003070f40c0c01085001294840c42d591800300c072001e45210012604034503500c40074017011059151040c1c03000241800c448031102c140300200d82c41c42125070020000207151018908400242c50620030401207550100c4080350b03124003c07540103003145401000f5080300c680342d142c01c0152400c00c085c42940110001c0003000c4850821070b000f026450001130302d0350780342c2c2002d454603054007100b14003207401c02c0d04220400051101684c141ea609803800d0115021188400c03041703106030348000e404510032100d503040c040c1c403176003056074011141600800e110700e00c6e17a01d5685030060800c040340c0302c1c0303001c0140000305a03020010f5001058000020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609070305 1250 609069055 609069067
    0xf0b1b0d020d0827153103051204060504051009020f090a021213110d0809040b030106050d0614071704080a090b0c010c090803180904061b020307050111 67
    0x307980d038040800c40e0720900c6500c000041001c0400301820551000c003005414022130019900303a1030f43d0410000e80c50070b95011001c0380320030010301d58030071800d031501c40c030080005080079100355480b4010b002101005801c0010280e5a58070905990085120341c0c2e002ca806d0a0914045091480003c0b1512442d441c0000402c0980d550080c0c0f503100d00c40550740b18945403541c0700307408042d12940010704624034050b01880741541d085040324484a01403100004440c0c06202000400c8140c0c500c050600070092244003814075042d03110004c40d0070b004000060041c0e0307460229008011404003622400c2d5a860050001c2000d01d44040e44410075280070000e003010704542e8400500094006050404003080c0010254002c0050b02c0240c50001c0c3e800b921030005c415614041c01c640c4400e4800104003210014481c0b20000544003207048101050145118a405201a10400070300981c0c1403a200c4030824285030780194400100141c0d90b0140d55182054101035094075004e482250f02e0110070061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609071555 1250 609070305 609070307
    0x2f0d02060a0b1503060303070606030b1801020a0816020f070b21010f060c050102040e1302030123070e130203070c0b18030d1a150c0106050901030206070209100f0b1b0d 74
    0x1440c1c445144007005aa00d17615042c02080c510300403104000d180c10318020000c810701c000c2842080c0f0401414066501860701148440d00b80c1c002c0a1701ca0740841c00b50f002003980111800500011030032607204070740c1c01042000995140441c0e580c05810a0100000d14000362000c1e00c0b40c1f4000c410308801040850b514103119000c0c0d8410a00c03c640400640146d00e1080000a40440e00200600741c4459064184503034070140400c2d158804a1181d803030069554050311415003a015410300c10b10103205940c1d1a40404e445070030030f42d6101380e4085e41c101c0d14500e0381c0003588044c6000d00f8056030386c0c182d805481e15240c04000e0700a42018900080204814060000001110302c1079941c400d003c10003140c071580401c0c9009822401a0384040745010284010500c2e42c0900003013025600244051070342e44080c05607000c828040a03401100c05c00855015081100129411010803a821141b89a80745e0607a084281e050300050a600c600117009481e403e90a403400d4540010903014025248103994 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609072805 1250 609071555 609071569
    0x209131d2d010b0d170409020d06140301050915100305100903030c0203040b0a0e0d050d2c0303070611190f021506061e09030307050a0b010803040302030601062f0d02060a0b 76
    0xc4010803030b01780c20ba198030038204d00d5400c1d50f000b00f080b100c0540d02c1d021030220000241910b80245031043d192000b82010f14501401041d0040580f175000d0301201e8030b2840c140880f100010900315014050400001c001101041040381b000380d070792000150a40685070042c10b4038110081101194000c3c003007031120b01041d00072a09030178054107019910051140210b03c6005039160090464050f02ca02c0f03501c00f41d00402061008002d00f02105e005449000800c6000da00348840c036505540180580070000380c2c20b50006d01c80700c0e40010030310300349024004045151441c0000800000d006132160b052019010440c04030b40c120091031101041c54030101244290150440c1000e4a4043ca0803910703a030900d1604852150f4009811340f80c1d00c01050a1007036490801034000ca030b40100210000070b14002c048107640580e58002c0c0a0301d8544d29204003110b041d80010b240ba00c43d0008003440000450540048521012060307015084c02d440e406d80180c03d2620007040c0501143c01d090325403d069031400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609074055 1250 609072805 609072829
    0x302061603060602070e0405010f2f0f040501080a0b03011b11010b0105180a0f0b130b0708032d0f010602010b1e010c031b1b090209131d2d010b 63
    0x144245c0341b04d030b85900b0300d140502243c0038040c4443d403501a9926000c2e4414084141c00c0114208052070718615006040140c842c003100c80890344030501c0140260340c030842c480c9421207400c0202007884100100080d085800c0500c44542011103210341c0c40032103070040d00c10040c4541110007009000000c0c0c001030941d200e8a28401c4059030396640b42c48403a81e42c04140c6026002301800b161a4503210720501c001076000c10300c800c0e4004001100050841004800c80316610b500440d42811901c640c40f1a0013003000701c0440307000c1c07a01c1d0b407200c0d440c65220045446124000d1203e5680f00e0f03526045010b82100c0c891340c50940980d44812600030100502c064490b2203003c20b20b030441c040c40103810219607410201c01c40d410b40201c01c2c00440180038103584400c2d4030381890038648551998450320079007284180d01e0115003190f116402c07180c610601d544140f003140076031030003403501070780c26480c82d4102044100c014203015100d13100c040d180907424809061100341200200010081640041c040000034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609075305 1250 609074055 609074069
    0x6070c233a02030f0f010519090c09021e0a0203130801180308070e04051005010816120504061b11010605010203070b0a020d1b030b1306180c0516030206160306060207 73
    0x428031240443d10f041055075a00c01e14201541c0500180c00d0145002c0c200503200a00302d14020020481c2e146414458040c079241c0c8449401c156500e4012198041e41000701c8640c0e407043c1c1010810f0b0b035405981d006004a900c554040d5549440d0b03c3c41e119500d0025401c816403980c0348c804200411620744603400340d1150141000c1e4a581e40e084c00841d0b40d82c450f0f0f104c03140c000d8181030900480b14a501e40050944109032a20b1445075900d0191a03c0c0c00d00c80e00d0090009101c1c600484000580c9520050f0468003803000440c11110315070426080d07003003d40d1032400050b0101c0c10f03d5500340083c402c0c140030f40400d2026500d03140254a401c040b841003d061400c44075400104420150069400710603a44142003040510b1088000c001d0300400105511a005140c4c031240c2c0340391829148503400030380e102c0c20445079000e8161030150005140851101d824804100181401c042405140107802803080c1c5c011300c283d00e17015020910f003000c182c451301c040c0b50401009105160700403581d0000da13000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609076555 1250 609075305 609075409
    0x3090606120c030d08040606170a030c02180408090a0522270c030606090203061c23010e071d06090c13141f05040506070c23 55
    0x101c03401d490405444107516549449504444038029410011071440742e4050354003048900c1e600c10740e026613480500d07400e1009402003904503001a00612154940600141c010201c0081803c940e4a8418065405807401c031004140440285061810140604800c2d41c0c111100000b2500803c560420b01180f0741190703864001034261403884800c42c5102d0945a08071190194090900c0c00b103c030840c1c08191840c0381400e0010800e13480714001c40380074060103024a10034649503078074994541d12070001202d0340e200e04c84186415850502c02c00e0030490f80030000044050f25450040e217010500da202a01036550100045081400381e002954801d400b62448082640d510361400d5043c0300350803004100001d50540407070682c1610f0111194858180c8a000c070980c00c81e04400c3e5690044002c0000141c02040107000e036042250103816024410f081c0c1c640940d1304c0d03500c401202619800308070407401c3c8900d091f402d14a8800c400050301c0d00b914141c0c04100560706096028200219150000006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609077805 1250 609076555 609076579
    0x545030a02061b0d03060323030912010c1d0d140a0b04060207020f06120c130b1b011401080c0105030c0d09030206090f0106060e040b010908030c0c04050c03090606 72
    0x505016600e40c955005000340c1d03880c03940e00002d440c2c40700d002240c6241c42c8103411500c99002d000780b15010540e40c1148c903171000c0154a0707100c2d021110034201460301c24081480070002544030050317050f8802d020323200003141030203291000920310b800035604042c00902402c0e1122442c1c0f6099010703003503150400d20038102613000c041703d64580141004028080c09406080005001c0c10f64041d00885100706c0c1c02c080140d050104001240c090010212107614000f0049079000350004000c1104406500680c102142c3c1c43d003904071135400040b20921034503081280c50b080c20a0a10603001842018050621a941882100d507620075009914074180315001011032500103a18040c1c1c1c1050341083c809104909152074000d4030342c0700c1603904004600c03034a4035100905406018944c1031720042e50f1410480043c100402000e40800030803136062240c42a0086a4103900f400149210808040101400c4000d0000d000c2103030700061403005103200034014070000400c04202582c01034021100d100f0000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609079055 1250 609077805 609077809
    0x80f0c180409020402040803071401060f08150925090501150909020310030c170106050103051905040f12022a0d02040f15080a230715020f0d0545 64
    0x81b0440e0869503c0d4800410003608002e20300c1c7e881c45034511050b00921000760360b440c082c03586210764010140760390840b4020b1110150b807001019802480c01c0c08641c25030030302541e6400903016011741d2107040500c10308140b1041d43c050151038010642c000362030041100d5510010124401800745401c110380000201c2d032110054100381c0f000d1508041c5141c100385d03544011001080200074804002c0d402d000e00025198064030031188540c082800c403d00c8130b0502001c6a008090081044441d08544800c9030045500701091520441550b0000c0182c607801001000403100f034a0004944904003102600e1036858a44001103440d0381560049046039914220034082d05a81c001c495883c4024140040c03103030000079070300d03a2483c01415800034070181e10181021100300851110025842882d0402042c01403d0101c0c00d90b84091059443c03018000f61201c2c2000050204040090303000308d144804c40080803060b02041444005c1c405c50005041020407282e000c11100300f104090b1421801160703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609080305 1250 609079055 609079057
    0xc09070c0c050618090615030c0a0201020c0303093d1a040e010f0606080c0f070816110a1d07050a111c080c130b07060204030210080f0c180409020402 66
    0x182c4002040310b03443c1c04629a445800c196410011032058804a000c130f021070900d00c03002c1c0100110003401e40c0c65a03a03003541070703680350340311b0300e4007908545d030800c260b2500c0384e000d1000e10b004182200141030030b0b0303419038240180115000d803550a400c010041046000c0340c075582c07801c0140d4543c140414129040e51181c0c0c80441c103000200c2c0c20909080038042d4410301940b03d50f411466280040051a8603024201d0b41c0c0d40c022100243d100204008a5076194510000741071041d1007503a10394a0140031700440da61003004800116544058040c504100345003481c2c0789400b42c85c8405d4031140703c0719400c0b40000042005032800080c03000001d2001c1440c3e1060109107080e4000d40708681d200c1018010340c01e1001c034035980c900e000801807004144154140c50072070302e0101600e0200e88040b820007401c1e156681c03007500200d9a60341d007000004010f03200c00c4a0100032480e103440c1e00b50783e490301e00c5220100f0a001004803031481c40c101b21210000e8003107058440218015070b4000344c50519403001c1402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609081555 1250 609080305 609080309
    0x100504080303041e0f0b0103030207080708071e050607060902101407122007050901061b08030718080f0105090601120f0f06060b0d0605010306030c0e0a060320010905030c09070c0c 79
    0x30318078071202e2038800c1c01b01d40805c00e81241e01c02c1d400c4130b0509a84038041034035541c00380914683d6030130140d02080070b445040c410710001c00300d400080f407a0f59a5540059525844140225011178075080503500390300e05030000f000032110901382021510310604041e60700e44140640109540e0500e01c1c2d61307650314810300c11801e40c180c0b8806005451614900301c19138504aa01c00c4510039800d0400206d484e43c0304000042c8954000c00120403070000301d665035001034000409e92000c01c0140b0030900c91400c0003050640003031103428090400c0d480c2c0c80d030f485429240024040c08660f48100010880168504c04c124080e6810001c5041010900c0c031300b60b002d45c4070655000e44007074203068001c100080c4c5c1e000204084050034a0030012155200c00640036030300603210185c9010f40e034403020003180440f200c10b0b03a0310048500700050f56039121794580c0703040a60701c01040c00d62040c02d075140c0e5003940c21100e510041c140440091034007002c2400084c4010500030621030420140036019001c0010620503500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609082805 1250 609081555 609081563
    0xb07020c0303180405011203020a0b1503030703090302210606010f050702090106030506090f0f06060309010b0a0305010c03181707050f0a050a061109010e04020c0304090207060b100504080303041e 86
    0x569050500302169805184480f0301303100e00d242c480001103001e48040034005a5900d60051f00d0014800e80b01c11540460051a040c0011030501549904d50f900303100030040c81c2d100e41c99969a00c1d08600501110310030080d441845c03200d00004008440390001001030f8081000d00c0e0210850490038400c4480d40240c42c40250000b0207c8000301d0040d426070040c5200309826140a101a51514070042103a00144c0b035040440c02e402c404034100b804d24a00840d4001640341c000702d407120035040401c4100b905136100741d070b959643d174002115659060090403514034080b00ca01085103c10b441d181d1040c0c1300842110380c1407070006994030030040103114aa480c0000701d02650f02014a6003440c80e19084003d2040b5580d61500c1190040c800b42c120a41d8070045040c0d460041d00c501502c140b100030751001c91410031130302c41440000f44242450004002c134600c250310205241c030710303002030006603c0d510340349405005041c081030180d52800801e480d0300c290030541d0714540308a481011001e100500d400a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609084055 1250 609082805 609082807
    0x7021e150f18030f03070311070b0f0601090b0a02070b090411030108010f050c0a080601320c0c01080103020d03052203030e01120b0607150e030c0a05010608031201030b07020c0303 79
    0x401d25900250700c200d40001c0c0401d0307840d42d44020140c0341c0c0314188135110a1041030020038611032195000d0718407040e40700f540e685802100d41706e001201030111141d0480c0c41e8140100320342540d004008000504d81030028504010041501075103400c114094038514641c040b91100b0295202d41102d00e4104000c80c089540f0750b100c0c00f22038080d0241c0c89c080c6810a09010105580e1502081260b80a1540f683c0390500c1d900d580c00111030711414285842069100700700d441481d200d80982c02804c411103240040d94842900d2501400c000c040f02c951414080354200400140c0c0760100445001945441c02607550700d400300300078038400c1c201010b4011481004901101301038101d440e00b030100030241c032488080d11101c81724038292200385101ea50090003e02c40d0303c0010b150406140f06c3c80c10885804601c4000c1340c1c0c7c5d450f00e0b503003000c19198600e900000381d00050000070f1041038090b020502c05140360002d59841e90f064440184801130801c40381500080d01c5502c00d0203110b1f03006100034123507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609085305 1250 609084055 609084061
    0x8090d060603140c0a050603060906040f0e0c180f010605070f05070b070b0a0b0a120323030115020304060c030e01030b030d120b0406031e020a0b0a031d0607021e15 72
    0x41c0c01080c0300b44881d03d22481a0402e5158601e03000c0021012100c000305010f29683e60102800b8180030064141c50708141c50750001c4461686c140140d6005404c2c0718000c15002003a2001c200903070f554440d4400c0a4000740c028401400920b000381815640e5904010340d0f01c0006103000301c603082c44090003078500c0c003c07541d000c10b42c1e101c00e600525800f0300480c8000c506446190f010000c8a220080c096030241710014108002c50690302c052124074024203140021640854441e0b81d0005072420303102102e0700000c01841540300c01ca106810011061008506160134041e0260200304040000382c10b008140c12078a20580c841d8106181c1d00c08043c0680b092071617901005000d0340c4903140d0b510b03800307410100c0d030f80795905007841a01e04890304504620812498002c0603204055240320503a00040c0c46507004c500102041e000b401036103419940040e40ba0400206107190710010110510583c00c01d02c10b10047c1c0307600080034001d1040304035a81d240540314031406860034450040b85040b150f80300d010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609086555 1250 609085305 609085313
    0xc08030301150e03150f0a0e070f0519080d05130b0c060a0e032a030f03070c050705040c0e132c010f02040e0c0f07060f0207050c091308090d060603 65
    0x1c001245182900e030500480300000402d62151710000845060b900d00d64002200084451b5450380c10050301c50303001031010b07081808141007590170b406c141d0600c54000d008000a06010325052144001e2451845100b401e1600d0242c41d400d10003000310800801003203924200c9850880310008210303940c0710030b0395103a202c82c0071520b500017142c94801051414488841135031022044400c0f1401c020036807022041640441c1401c2d5160782129020341c0700900c401b07089280f034080110300404041c2c4400da80310750301c1c0c0f400a10702916500240d00030750404844581c10b03504415503508031102203402024504c0080743c640d0042c5040e00804404008a010b0603035601c4480182c4248010041c0c02881b041c0061014041030f4030980c4a61011002e2000004400741540805024000c2403280d00c1c0d071500780c0d152100d2080e220940403680c01141d0000362507040040c104150003d000b000e0b00e2230700385071070051806100c006842c28040c004030800100752109a896810b0508840d80c4034100b08241d94990070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609087805 1250 609086555 609086579
    0x60213060e030706030507050a1b080c06040c120305120702010b0306130605162a12050301150207031518120320031012060f0624050c15040c08030301 66
    0x1800c1e9000f03004000001c26050f11a0017000e00c00c4040342c8510740b8080e0030081c115075074004840d0700301d0840c001c0086200001d102d800200441c0f07012400074006801d190925508900c0e20b40d0000100c1c01541c1e814038000307a0850f0691341e2030551034200c0710950751040720a034007411070580d42d00e0381030040c1030412011103000034071068031600a550400440d6103424501200f0032002540101041d041d00000020315159881c1d0105180030454403603046906075644007a814185041301e000c1080400140301080d8250011080801f551000303003c06482c0d40c8070100107000038564a4269601d0719007007032120000c2021303280000d038000c0710700b0b200c2d0360020390041c02003200d00c40d4412040b1103c083c050041c0b908000b6240140000d82600000515041281d11100303c1c0500494a080e114042581101864882c9178000c0813254052a841036145000503250b400407038034071062003814040e00d182c0180000340b8a044500c2825000170580700d0741044802ca100941c010b18103440f0000c008500c10076150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609089055 1250 609087805 609087827
    0x105090f040e01020414090108070e061305010b1c02070b04060506031e1e0f0d03050414060a09110433030b04060b150306010503070f0e06040b090f040e061306021306 73
    0x440754015071b4080020010050400c0c455a502580070207400c0c0300007651035222540150b8010040000c2218052011003681e200340c1c0551003009002c40d5405049240084151400c1c0c3c00c2001180707488102e1b80ca0351101500600013400c990b80c0c604c00141d40340c8081081c1400c0c00d25410b008007041c4201119140c0d034106255003c45203c0c1c0560712a021700c00001440d031160100d41d0094481c0a85041084009100007442a1240c11a100010265000c00c3c04a2030152608000106002c105800c04003840c60540e108030380198640303c41c03910155050010b50010440840f400741a01c241801c1070803010b030310794001604080f14501404208035031503202c2c0310074403000e0710031041180340c0c4c1c0c010f000c0902084441c04d020600c10000280b90307038403e1084207850711950400b0103002041f00042403d980058003c103145580c001492030040c50000040104404125418004200940600f60715000068a03402a1049021b0180108203041c0c06a52007031032107441d6055182c8da02c03440100480103503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609090305 1250 609089055 609089069
    0x80106120c080f03030a0903050412120809160605180613180902011e171305010b030c22020706090b0717070f0c02131b0f09140105090f040e010204 65
    0x300000503001d03008280d690f01d0a0a42c0065415613031007039182400341c9070303490701102080410440480c0340c414844813514682d028840c004460841c1d6940a40984005048543c4a500401e8a11001c038111381403a8143c60703661030704584900404151440c0d880404003a554006008180c0d00000400c581d040400c0300c0e04540001038105001c0c125108a43d1028000790000311400140311440e8410340b80a13240c20168a40444008803421360201071880c140d07880300d007400038920002d0a1103024020401c0e001001c82c040e0003607082040c0051042201114a407211007001e06071f06c580c1510301c3d8161001c850b004442400b20b4240d0340b03000001d00301c00b22a80d4001ca1a2840308805410350001d0341ca2144107a40c03543c0102000301076041e00c4c102003500c02242d0018240405d1b4022079483d00803c8a03425924524040c005401c0d5070192600d000340480720100503400404000035078100591607040103003800d1580d6548039420100c1c0507152014045030308a410020200c0090b1170550040040b100c5d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609091555 1250 609090305 609090323
    0x1805121c1a010f030902031b0f0d0b090106141c0507080316020a080d0804062f0d05160c061e1b260402090903070f0b010305120301180506030708010612 67
    0xe81d00081d01205c42650001c0c0d0140c2c02950b03549030804402041c401c1c0100020684a00c41c2c40000008080817445102110480840024009184401d0203188064800c6290b0300181d60f90803004518000300301c04042210090020504c024840d0501206d400b0b001c2080650b55101000e4411a00c81c440c010b004238000c0c51b002d05d00180510340032800912000159540701d1040e2116201c0030040e0040c0134603000324403104144242800e070600104101c80c42804926034944c0d5103030340220100c80c0d00401550740300c10380525011200c0d600c0011202e2556024000244550f218003184540e10110100c0d41e41d03c914011072140c03511031140d5494400081d5580304a13048250f9403401c3c90001c101500300e16458042004a001441c202c0e00203503000741b007402120304002c1c0d540c50307402103022082e0090760300c4078035000144103004080c00761060313892860050600d95494910003100c07102d10800c484410701e6441000c2540c941e01072144200918000d0002c0c0700b03080d00c4540394907041d41440f108490070b6013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609092805 1250 609091555 609091577
    0x60702070e090c0f010513061214040210030203041a0a02190f02100e210301080709090201120e0709020d0608070909020f01050a0c15020901031805121c1a01 69
    0x490712489100d103030703280003501c41d0f21080b006011031014807a20850606ca030600080e60113070700c1c0e0301c6850020301150f80c9000c0072881ca80c2030b0f42d00701c4541600b0850711509140801015031158500b11072a1410345c81c00580d07a0ba1503060040b0040902c403040300c9404501418040704090940292503500c107140030100c044104d40c0c1094400107481940d0b100035130441031074006c411a142d805131024080500541d180c3d51500c44480c0d03415103140040b242e448101100510260208200003009840011810060000b042d00003810510050f02e6070085240c0383d209001602e0004e201c00402031840020035512010300c03000031030291202c1d018100040c400c0e1000046c210042c1c0c010505d24175005460b88817803801901c01102c5661150441d401406000c10400c40005c0042d4040450040d0703125006807204a4480010152078816420564200d101001382011a90104400d00018458800160384030300070100010710113040481c0c10304451800c42041c1040c4540040244c40d64000d83c1c458400c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609094055 1250 609092805 609092819
    0xf050708010312050a02120408030c0706080c04030809030109050615040c050f0f0306010c050709091109160e030f03131508010f05040c030b030303040c090605040c080406240806070207 81
    0x10400744409005020256001e0300c803213000740c0c0148256030080c4190b5442141c24110131031298007036802030001d907000040c104000c2c4820f01110000d0700380e92610340b100b0f051404000b07200d80502d010140100744001500300c1d05603025030090440c242e121003598010300c0c1c0a03881454025030900d845001da8280006800428800c0048034034040000c044c2c1410b04c288000c40b02010741000f02070a0511000b101102c0c0401d03002c02a241c005c100c0d111000c27804013942d2500c0e1100c141c002c00c400d4010140501071202450310000402e540003000d1030704002c1c45609c800020302d0007400c944a10041d000001d059040403c3c0d070321010701521b8480704042c0c042d00c0508000c48002c5024420851442c0310311009200a03d003580040e0754800c041d180124202641100207810b550041e1000c4803207141c208820041e0210314064900100300880301004140010349024150280040004012a50710100b0380c4403003010420100c043d80d884ca00b5640c1b8103491f529a00c2d600e0109a5003403001d8450548000b0f80301c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609095305 1250 609094055 609094067
    0x105041b0605160f0309030503040902071a070507021926010e0d0219150618050c040b07151508071406070c060e030f01051303120e0a1719030f0507 65
    0xd2180500d00701040b20305413202071030540c01900c120b0410040403000004a07030104064000303840c44960040e600c035450b180c00101200900014403080494804200b4001d81040030741e911180c0645d199425124182c07a81090032506410103640384908442d4800d0846800c0d4982c1e004040040c000c00c589000c0503c11039803442c005a03d200140d1104045552120030140000c80071440b4002c1904d903000c0310440f9a094884270781115084404494004c0002d1215004040e0042062007840d85014100162421248648480a00058031742444a801c000180c1c0c46852100ea1003c203025005807107819454440609103d008030f4142d0200c182c692a181540c01c071940385900c03449101c41c070362402505613030841014401c1c41d414000c40078402c1c030480303080c002e81d03224500072004120410700a1030060503190418451000c41850310600c8140200c0c0050309103291600040080c1a140d50340034080c01601c185003401600a8404090300030b0290140c00c410300c80c2446150a10041e9100c200403200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609096555 1250 609095305 609095317
    0x230409140d021014220501022a0606120d050c07050d080405150c03030411030316030305100b07080405040b0604080706030506120d090620010510030209071e140c0105041b0605 77
    0x22821000c03200030485078210f05c24440c05125100160070040740c000a00311050604032908445004040b0000101c00b05100485e48890308882c000c000064080015540c0c4100c4140c42d820f01030b0020701c030507400d9010003c4400501005120750090718070740c81c201250343c01511945004004206c0c06002e01c100c000f050760980c0101400a500b50b9440b521030b202c1d080104034015400d030004101e4403081c0c2c605004942e440d680030f40c80215a50400c034040240510790740e8044401d41c1c0e42807023a00002a80c980c02c890445200710b034082451448840040c042c0e03c26684100d0942c03040c01c00004019405400107886104200c0b403603c485100040c01c551144801c040340343c009101500103104040c000c1c1020403a00c00d20728000c0c008810010080e608480d0190740300703056034850f01410011844c004015550180c42032502240d00303651b220720510080050800342c4240a40c4a211070043c21007a000c0e10098903104009108a040a0400c500d40001400003409515114100400d02c10300840481d09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609097805 1250 609096555 609096571
    0x1517070608190c0306030204151503091e020a080601031209051804061a033a090608070c200f0f01120b03030c010203010303080907230409140d021014 66
    0x2580500b8010300000505541c1014001e256445101002603102c0c7d1042c00b0540c26603413032501003507061a04075070101241045200405050119050001e103404038160100c00c0f0401c2004005409480061092002c54108040c10301c034800000040c802d44400c0361340440010b0300c0e007941241e01d54080c80502210a040f03000d94501701d1011500080965000c1d51b0200001c1d18605828110381002034240341c4c4994042e64003000703007490b055803017404180310318408551448a1050f07000043c0040e06940c1e0500c502401d01c105038001440c01401403d4400945900c0010131408200c030a0142d520021403a801e90302440611108540a040c116070f04034404134141c4900840740100c82c4001d015100300341a40390940000c0c004180850000d002a50295100f81c8454803e0301e8007203882490600f465104070050703040f2010a000000603203080c1040000207803408200c003070700c60410024112170352a90180c94811805007070104c07580807580e584100d480c40c2081c0240c0d980d00c8030194010800382c9140c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609099055 1250 609097805 609097831
    0x10e0d0914010504031a06031c0302270f010f0c0b040f0b09010603030203040b0a140a02010c18050a0e0403020114071e020f060619031b1a120403050d1517070608 71
    0xb0354079141807546a4061f800401b124006400c0391144502240103c0c00d550201c0d80100791003014560098800c42203030300f0b901040c040450040c0008180f41107141c20315040c00121304e02da0003402d200302d2008000c039410078007941d02e900302441c00342450000b0b9401aa00511b4880c0455440b00c1c040c02203104883e015030080d402e045c14140d580242e68051030445051000c07135281d1625840382da0014020340300d002d07000050919071010000d0502c41400520300603280d0070715001d100e640d40340758481307099800c0d080745c8034000ea50350302d80cc1c1e0040a00d411141c8807610803804110200e64010000030380311892030f48000f006442000240e95a2400980c4031946030003030350004005040007a2001200c9070300b0115071652a5803030b252207115081c001c1300020829003500c02402041d4000e5544060608400d18841c0303026112080d00d0711600b0090401820800b0015105503000780300d4000d910f40702241c5a0094a00d41d49005202d55110180c21440e024000c20500054441c0a0800140300301c1030395640c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609100305 1250 609099055 609099083
    0x40b0705090a0e06031f0204060306050604030f0609060209060720060c060c131a030a110306010203070f0501020f0408030d0c0c26121509090c010509060903010e0d091401050403 78
    0x100c401e0003c0100016014407450001c8000c40444c030b041c10307554004070040142d40f10b0508000500381c1d038550300143d000b034004100800008404007100e03a252600400c0000c1d003062103150490103485110b420a600560208059041c401c000d092440301c4105080c80d51050f43c4008203004181c0140b030f02000d05034000c0710010306001ca2035001010304650320300e080d6101c3e0b0344070310725040d28040c041350000080d50080300700030340e44041d44188034803c2c4c0c02121050951a0900000b952845038800082003e801d880d800d0f41002400d4040d100760480c00c3e0744880d240c03601c07403070210303070325041130362855516801e01d40d50307074600e500958010030030301d8103c103a0000018030a44820203480c030380c00301c0780044030f4104100103050700c230000c0ba076001e20240303041c4d848410001410091200c001906e0421260024095a2081c0c0c0c0c004046801202043d150350340c5034806031000900400810324608034500a920034079401e0380d401040d0405071000c0c4507940000c41c08150044600b0b001d00d00005116000d03c002c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 609101555 1250 609100305 609100319
    0x9060f05060913030c0f0b1609050108160c03020f0d021b0a0e011e030605070e01020d0e1e0103020403080703110d141804090f030306180203040c03060506060d02040e040b0705090a 79
    0x9100201e000f10140143d8004550f0f8486903011f003242c800b80140102c12184030955800031140c1c1c000c00c024030b024105403c00405001000d09107400035001d00010340f841e0000c01d4000d2040c3c0c1c1c13050700600251240c00398400700c040d46800a02001d1b4290300b1035660000703014038000079144117a4139000703003000141c0e08100358441001034089424000385071715540000010100e0040c544620300035aa1080d901700600b00180c504175012410342c0900003031154801440d2100580410142c5140806031048400000181c00922070b41e080034080348000150402410340007a00000209c48031821500c3c0c2e0752039842d08031020071410400041a100401104a2040c5288040300c03c4549c014000100003000e60383c0c0b803c1c8104961000c41c08241c4a450030000c0c004101044801c0d100d52a200b0741c510303c0c01e940c640a00a0b10760000528041d0b030346012a500c1d40300d036810f5454100080381e0455845403900f40c0a882001d08490848421485400107417043d0711030f4068a10202028056140c540d0508407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 609102805 1250 609101555 609101567
    0x427080c0c19030f150f020d05180a1b17010b120604050a1b17060f0112030503040f080f0310090b01171303122306030303061f0c0609060f0506091303 66
    0x2100345eaa51200c00d0a40702c8104035440346684100340450016a2100d0b1102d4510130350350002c1503136203d02009100d03043c0e05e100200300e40c11855400048038800030100c0c1d0321000a14030542050310f0402207103000c0006170205500207552075a080b1074980c030702d90b003c45400d595200708403401851a0003500d0541d000403005080342848042d00c5524402d46078549600d001c252101c20480d283c0d582c00302c02071060404801412038058130340d0310011b10f003014150b10060104d10000c2c10003841c0d809682d500b13605001040c1c00362046214039414603656400c105845418449440c00380d0304c1c1c45864140740010540c014200d0040034890036a2808540d59070741402151400801003e03024820340c10428100144075100710724202d002d00403c283c1000740c8060301480c8840c000e100e14001e9200700148944d80e40d81804201049800003c80c080b613401c904003c45407103e00307401c000c080707a06140c2480c04000c0c40f50440401c60440500400c050341d644802c00c0880c40b01521204501d0380089464804284100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 609104055 1250 609102805 609102833
    0x803180102150f0a0b03030316081f0816090c210f110c010b030a1a151005190801060504060507081c022a0c0427080c0c1903 55
    0x100590308021140b912203480c1803030071a00980c007424210100540e10465104202c89040d06600a40c114a0310f042101e109a412403003050a009621002507040c0a142419000301100010444150780d070343c94440d51385072420080d0b2000c0045d0a5008240c65520788101c1030188215641c900441050358116038071074150800140d5030507101d001c1c201c2c0c0c0302000e0003407582c643c0014007969542c0044030507090071141005081c2c0d00c01e070021540303100400d21001e5001d699940000c1400400d4588400780030394112808680380e00406580d5102c298150448081c0807034100380c5002c9251003460210465600c4000d00859003c03c074144010b00071203101d031016040842c45640540d103494030300da0720010921848800c0200040d000504500c1c41800b40614804c1000103485110004ea209290325031944410104c01e802580e0f140300e0008001a010300c50119500400765904200501e400c1c4065940d1040b054608540f007450180f01880c01c099007400c0c0c11918249010341010f042d9565500390010701 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 609105305 1250 609104055 609104057
    0x30414030c060c0918010f090e03090f060912010c0807030f1407080c0c01241e0e062125120b0603030702130b0f01031e0905030c0709091b08031801 65
    0x20b41c10030005c490403081c8481c041d204e0543d100d404646050045c0098a00d020b100c04640d400600401c201d5071911015000016400c50340d40d40c88060250120b07201c9460813050b01c1c0c0d19824500c80800c0507030084080742c0142147d940c00c0c080900003030542c20a8a44c94080c3c003080b40e641400244085100d02150380e041150390a2085c60142c0b0f1900b07407401c2d502d640040c03051056410303407005034503285a401e840082a4100700c00307074081100504000144024402d024850740710000142480d41e5000320b40300031007940d0a02146800d0f0000042d40c0e02e21030036100e10790b0614100d030340320f0f0002c2c006907030032040b034500e030081d80c442046503aa00700c94140040c0c03010b0341520050200d03100582e0b544000c0d0000104007000010820b210504018208020001da141418038080030851a8040c1d480a401c0315000c48001003500000c5d4902940345100700c13440c0e141c072070007114008507210440790000d207540c82c0030300305505248103201441c500202d00c178440c0c0015a441000380e204141200c960101c801101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 609106555 1250 609105305 609105319
    0x904050916140306150d031206050a090207060506040e0d03020c01060302060417071e1e0e15121b090711060a06150929130b030414030c060c09 63
    0x85880501c02440c1c10140000c180b8100012042c2010416103500254003110035000464000115080b8095060007600b008072940100c490200681c0018004007405801c0c500c000350340d40403110080d04881400c82d41c1d1814040032175141d19142c0103070f00824100344054009003403c450107400a500410016006540740c040000259854001810050480346880a10301100301a80703810300802d0b030401032004420710000325080c0c2c44c0c4410788068629a0a1692406051000713980d0640c400d0b83c040c20321800c40d0700400c610811052500c0000d8401580e41c0d0143c40c6101c006c441e120f030014000c410102c000c00054000d00e103800004c094011700c0ca41000145038419215003810408101e030041541c9407184030800c614406a48127121555072881c180d031081c1d0403d4070256081456961401d4014007400200800300100030450b90f000c0c2c2c2424400014682e210341c2c04c42c1e5600100c1d010360701c42c06003000381d1050b400080100d485403d5000042c044c10b60302c1c41100c4007990889070b6841e0300000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 609107805 1250 609106555 609106573
    0x111f0f06080601061106090712081b060408040503010c090302090a11160515010e190507030b040f0605090601080912280e03330a0b0904080a09150509040509 69
    0x40144107407400f0307101590791220307040c2c17010450500c2d281015003800010b50000004000c13640c045031031040c03010340c08191140c0c2e5400301c140c0806520501c08102c41c260140c18148020040520700400844006074001c0c00710300c10002c41a5110010343c0300c069084080c150016042c0d100d0740d03114181c6d070345018010301d0030001c00c6034003100f05460132901250303030340d0110b18001d015a400b50b0b145401007501c43c0c5000440c1c5000c41c00300c0002c1002c515818003440e1a800800c143c14040e4008400107480608200714bc07281c244c00641c0038111350720455005030316072130202d51654405ca019030300c6081d024004049658180107151a1a4010610901d01c2e00c1c0d140c03808003010842c41141a18202590364450051904808040c100b0030360580805911090607030700c54a0682030300c0c1449021030760407100c3c030050740c90150440142113041c00b07490348004603c0c200030070401101d000d456054040c0e6a40c4130140e45640d850303c020b0603903511140100310148004405440d087d002254011504400e96880c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 609109055 1250 609107805 609107819
    0xc0f030304080702030601090204120308040c0815010e0606040602031c0b1305090606010e01020717070305030304080d0b3f030a030c02010516090b0f130e0403111f0f06 74
    0x50010794040310100d0380010800107602c3d0400c040c901401510070110316161801414070603084180500405200306000001d0900c0150300350400100385003003c0c1d0302c0c040b44980d5000c0340700c0e00902400d1000d40c1d000e00421081d0514005540c19220b56030025850181d45003035642410180044060807503131180103d0300c1649a55001e40703101100808045424141030790002c4c18420001c16903030401210400500242c0e0380020300c00102c458200d0510306411840c6040b600b00046a0009452032100005010030041610000e1030b8580f4640b00c2000030b01c12040030072154644682024076152181200b86c000003040c41c1d04007040710b54400c0000c803442908d100c2103082da008580200c0c0466910503404c5015602805120360005145000b0f441044080d04040c04010f118080c0c41c4a4020128000007034503036403401c0b590f1f4484035030390480c040c41d41c40c400b02c074112404031800c40c009002d6080040d04c40720001a4203589080403960303981d0f03170401407103010010b01c0d090f00c3c1e81d01000d89501000a0103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 609110305 1250 609109055 609109057
    0x12140c0c071e03061817090103060b030c090a080601032607020414060f04021306030506032b14120f0a090c0b03040b010806090318011e090f09020901090504020c0f03 73
    0x80121110480c02007495810300d4005c9400b2490f104000203508902ca100040307030804014504010504040e0b00c4400c1e03600100c0081032950404020740400005000b082040b10015010105040319245101c03900ca07940107031111400e22000340b0800c000e05503500b82c400d20603420001c002c1c8900400d0304103100d5800040c03e4030b010511340c51b883c40d103800c180045400c103084009102c10066a06503d0051880c842d00b110030442d02c2a0030070141d072800461196a0188580201c4a018a202c1510040c2c20460900411a4405001d01191001c50003408992405080e980c645403202ca03000d24680e40c18640440300c0d24000e00c1a118203a9652007040003c03068040400504400c1d80341170341700c1c40c0500e403084d689401030b041a440f55010504200086c40d0010803508100c0c0f441c80c420740034100300c000503a00e4101e40780c11881e0a1103140c480381c81c0f16074804408021262980380515400f45c0c3e8030030342c000320310407441e0050010301340c2e00c014401c0b414950004e000c03406980c0100c500b05400100000e0031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 609111555 1250 609110305 609110339
    0x3030a05040c051e13140a0e010501050d02010c021221040510020307050d050702060702060403111305011211030a05030a02033406050907150f12140c0c07 68
    0x401540c0e80c040c401030000440c1c1d00c80241070181c41c003100d40c00c100b1110100300142007140310b00ca0034024802c5038000c1c01c1a00002c0c481c03040b000002d212420041c46100280500ca641c85103150310380f20001445203070060b0030f2030b0255010785641184004a8007070201c1c011100d0542480c901c00c0d40340c103290403880240318a01d03040112340c00d251550f08000402000c04c900c1010501103520a1010501040c0c010449658000d07e40c00e10350781c2d0b070040344003040080c010741001951113040441c0010510012160911a80c0411100c041c1107009850652040343c000303010740d0740f00c0c2000b0850f00c000901042104061000002e0440b1105001559018950b602034580e0900582000c03c45040c41014031343d104c512500d4240d01251030309442001038076003411550020380310303a8a81c00840d21445040c4845c5e0f0107001c1c002c005001d0401c109030083d0491070140844400255640c0c00810f0290b46031145210144100107a410681c4605100007195004041e01c0c000b24005c3c031034006503001c080172568207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 609112805 1250 609111555 609111571
    0x93c0b040f051209122b03060317040518091e1204090b13050106051905071205040f12020a260d021c020309151e0f040302031c170402120303 62
    0x80c0d540090824031050f49050401c905d002d51000301003c50391003d009104425104000c03110a5400c014401100502580d51000c2e0082d2201045c6142c1a4480802003090300c00c15105900313980811154081c0f841c0d4102c400b036115401c61101d807611741e0041d1503620030080c03849003203403696940c0c0d000c03107101c0d54015400f90110300c0e6228080010340c00e040f907001100ca01e419108010035894920058010b10580080e0a03c503080040021103c9001303000742d43c005504500c0c40c0c0c3d481c600c000005000c5900c540120160304000e0000018071100ca030810a5950707502802c0d1440d100e1030081c4600e04900103644199860700403285124410b00100009000e10307416034003c0601102c00c08088240e0a03a2060b002c0441d0820018102640c8441c1c9000790585018180d2076030312a040c144003410111050794a003885540001c613030030301215940141003500d0084007920010f892082e480c0c0000a40e22180ca4081010745c0040c1e10644440c083c00c5030b10600182c42c40c1e032551620304c0c0303140c00c51b403040340c1401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 609114055 1250 609112805 609112807
    0x10c0218090f0307030912020d0f14071203021f09140a0308060406081b0301060f0b03040611040302130203150925021b0919093c0b040f0512 62
    0x80750750003002102a40b0040402951810040f918000c1c02d4101c03a01442c03401000703070308844c3c0864a03105060800c03a504454954059621803803c05840720701103101840302d00c070f5032101040701c0270100e035032001143d410b400402080f55070746648444001038000e00c800766070741d5450350004240c0f004680ca64141311603010309210002484c0103407100710050300b0503008070b00d010024004150005082801800d0840f00c2a03800001d0100003405030415403c00f05000251001c0040e0b2035052501031409580724100a000c08140310240b62201d026900c80a035211078070040c411404485a4002c541144400c0000e01000c01144049004982c041da0501c000300401c502c2546c00800c1044482da20000c40d00c05002082c654140c840c000004000c14207120b00944008030b03c6c1c50802c07221060203800c07292000e000086580c144000036510000103140d41102040300301d003820030b8000c24072025402d01e100240c00c403030790f5855410075020000c2c030407521142e265a594002c10800c01c91048004010a004c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 609115305 1250 609114055 609114061
    0x33412030f11030c070f051009020a0e07090608090c0907050a080f04030504052715010801060e030715020321100503070b12060307150203040905070c030e0609010c0218 74
    0xc0031100641d81407084285030103290501c00000000b101d0f000000c2082083c0c40d841141451813440006640003810341c419010004036004030f68100305581402100c00c00c80c2c40707640e07100762103203a03108850390400110301010500c28107015040c241e400031085021540703030a80b2100810500c100c02d4510700c0209a0108001034000d601170059540102c004086000c82e0406a601800394081e074050b65205828102030885502117644030880b0100d040382d8540d40d58141400350b070b04a401c40c4200e09000400e84400030801500a85414894020280041c401d2038507190032202c1240c8035020110071800104105105248810603110800c0019400e04030700303040011041c101c0c1b00e003070fa000d40e01981100e00b00300403240402080d1403e40f904840d0740501070351584002400c00c49141c001c000c03440346404050000701e9002001d030054540c00c000420950312564425500c503c49031000a0005404100050305400d00402500c140c66040c10300c50300c020300ae6030010b0700e842503614819440d0301701d40b410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 609116555 1250 609115305 609115307
    0x100308072010020a110607020402070c05040b010f080f1e1008010605150d0906290a0905060d02130b0301020a0215011a0304060b0f060c0a0b060f03033412 68
    0x94030150460031128200c4010610001a40740c071541100900340c0321701c822111300d82c1d032a110304442d0480d500a000b103544122510301501640201e000e81c3c0e004d5850f2151500055015a510b401c81050720744a0381d2140c1d559169040044500400203544071954044245450750080012401010301030380d00040242000300190842c0e8030399100340e1182900e0b2a03003280007024402100d146107005000496086040e003000d0010b0300d010680380044d000600700a8001c2c2801600080e1005401ca48006015654404541c19150140d8503542e00c64404000400186040703441c00c00030f12116000804c1c05405000000e089070040450380c0b007d03800c140082416032503d8000749014102800161580c40c010148108081c00004d00c0180100c0c2c0d10961300f020303a65240807010a21000038503290751010300d858501d40300e92041c0c0b400c955000034800801c0b0280740c0501005980d00700031780154140920051048604d424024801c01c69010501080113061540002048114040e02456028111100c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 609117805 1250 609116555 609116603
    0x1050607080301181803360e1302030d08010e0a020a050405090a091202030d0e031204140307051e0c0a15030902010e150301030515070f2a0b0604140903030f10030807 73
    0x140c1301420712000b5501c2c49030707103045490403020b030b074140c90051295a40e842278a03884005820006903151142000038888181d100302c40c28141d4084001c481c4507500c0d042c04082c140d010307c2c1c442c0008510240700610890805110740c541c0070402c01d90100301c0042c241c41d0144442804009040143c2001a0751045901940a510b441050f4940154a04220a2505240410080d0004001482c562240031205404000b81c031001c030340101c02d03103411010f030241c8007222159510b0540000d00503201000b03041c2c80e115003100e08641e0b4905010b8960581d00d1000c400504000304200c0c14402214158035194488895811500940c3c2014595a50450411526000346c40740f241c0c544007032020420407210740c8044020b00300855400e1a1103c0400f241e4010908a0150a94032011040100701c40501110340042d271b01910058404001c0c00a101c1c4410303030001c2040310794400590003080415030400b0351400036980601010000402c094503642d98400740d5022240940b225090100310203504d4006003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 609119055 1250 609117805 609117857
    0x12010c0f0c020f01110a1718010206070801091d1b0a0e0405100507090806100f08010b0f06070303060b0a030204030506060a05011727031201050607080301181803 71
    0x4108050a1081c1d5030009981c482d012001c1410803450008940d407424080107400e2906030721452074400c042ca50710b50141e464001c42119074540120302c541c140503500110342c440c010200740e691007025a003070801c07001c0a401c0f008108607000703550a8902d000d003442480506400c00d040d103031483e0440c080e9420001400700c5074118441700d0145030140f06c00100001590b030850100030801052079550254183d8070700a0b546e00083c0c0d00d0156404000450220031010020f035000d010820104581b1038003101c2c01ca4882003561600040e8264500c0001c0c41d004001e880c02d10320030700e800b042040e156020300d1041e800411604011a402040031300c2004000d00c49554088000d49a0003545450080001e01620390418030150b00401c0801240c0010411310120600600310340e9401c040100c030118403640e03944000349503180c000c403c1c000032409283c40c00032140e255030820255410745c0d00f86a070100d1600e80760b6906c8a0526a0740381d500c040c00e0042603804e18a6802602c0ea6450740c0403d0750101c20444a030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 609120305 1250 609119055 609119057
    0x20f04110904050a060f150e040501030807020103050121021504050616050f0309010824060a0203040306050a02040302060901080a15090c030b0f01080106140d06081e0c180a0b12010c0f 81
    0x4001800440b6120010801f01c0e480d98004450988544405031907a400d1a0500382c0c100c3d09140c000f02c1440b00c494020403100380300780c2c0c0c100510b0382c6e0391035070804c00d41d942c101e05a0b060300b14203002800f61400c41001161540d200396520b2400c2d54403400281c80b540290002e0794003041601031b05050000c14895108452500e07000340d85031803080b600007405114001e000300002c24150f5298040c0481041284c1d0030b03006e01500c50b982d00d4010010103075490f08603200c1128100e003014002400781d1218000e1741d085943c0030342000d06068104005580313112006108141c1075980d40200052260790040440c002e0030540380018041042c00c8008095a034803510280c0640309103603100400742da200000724110b039040d203003044a081d0110707100b030343c40d12500140740c4240b420103402040b500c2003c038564201c02e14480200c0204114031403101d444071148900c6541c4414440ca003100010300c00b0801e1540296001400034403e86d0344000503081a00010007107026070755950203492803c1d006014121710f4000d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 609121555 1250 609120305 609120311
    0x703060830070503090d14010c1103041a0d0f0207060b01030b09010b18040e060f1602100f021603020f240112030e0307241d040504020f04110904050a 66
    0x807200d8800360451209445100c000c0014440703003407007030500c03c0d80d401203802418048900f0060420003480c4c454401c0f291140d510344401117012074000c000e810075800d0f6403400f0b1030400340761110310416100c00c45180c0002480c2002608071408507071240c09d150035070031200103899884030300300070701201c00d40b00c0114141441c001d5015501d03030760546414111000e40c03200540d600000c0e8038468441030700602441e08070741083c00001e003144012981d80e1084421521200c4242d81303401182071041002ea0950000da001840e024154605a421150b519005804007518007a5030401548030f04c00d100c1c90079401a08003d03036003114000d082c451030442441c0b09001d41c82d0314094884050950b5410310440706c641d211640201c0030140900585520b0400080c1a02c01150f901e40903d003101e0300c01580d00111003003841c00030030345034001c44c007d00f80114001c1010759141d1000061000400001d442682c1c4001d8060b041030b0b003a501c1340143c01058004400864a07608181c0a02003988d1003d8601d103207540c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 609122805 1250 609121555 609121603
    0x41a0c0a021002010e15040212190f030c0c170d05030108070e06030c0a1502060708040b18101d0c061603080a060807062f0d0e03011407030608 63
    0x6840c815541c04030348955030b08900e20800d0740140101d500c01e0f2124010041c01000540000da121031140d40217690b50b090b070409d102c0710345460715501a607160f130445105000401240703840c244426024401d0815002030300d000e403101c8501040942c0047c203202881442001c1001040c00590041656414450308550501c1807041e1107003020f015070031403143e42d0360002e40c43c1e5404100610154002034000144182c45440c7c204225038190501400b6100c1c08002c03034610380c440c4090510994101e01c1e8401180c4804d1034200d25001d80c4004400700348250840c400d82c000c214800c40302c81441080c00d51126150683c012410040000f44040c426034080c00f80c00001e0f240c42d41d410b42400d500d131070042c00342c0c0d40f401d102000901e01034009640e680b290a0011401c0f540120061400140040303100d204c112810040034205600c5194070308140d000315a0700303407959014015070100460024000f1814005c00100c100406c5002c545610019441e480e0030094042c0502405490040121070843d68a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 609124055 1250 609122805 609122827
    0x280921020d050f040e01030302010e1513150f05070305070306080a0b0f060111070320060918070e0d050a020a0807030b06060304060207060207050601030c05060a081302030f060c041a 80
    0x8620079403001c18800c0003c2c0c41c1c0003450010080350050151513201e422156140d0600034020b1100c04407404581c8500c147e5090305035030390064a841148842d0ba501d0b100500d5941d595a10745084035aa550030341c403003800210440d401c1c050203200c0c0140b581e000910f80341090f4010195865a0300060840e0482000304020807100000035501c078281003141c0100d0303200c2c00012610b481c42580188040e024060005c0100b04100035011000b1101c00403070154030801904000d010b201d4800310990001d05040301e2103002c001c030414140d0241c5c56041c00e811010213503000c902d8802c1006c01c1110160020703a80d038021864241c00c440c000e401d0800c02032000b1411a40e42c48071000f00908102d10900000c40090308110b4141c040f1110303641c2c4403000790340315991494255a203080c01e0004840d48503080340c000c80c41d81020f0040c0c13407400c55980eaa20002d80c03941a811208502d00d14000e80e094080c445003030b8071098040084500070300c564041150740f80d00c1e0041c90002d45040304007030090307004c04004040c034107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 609125305 1250 609124055 609124063
    0x507050c0402031f09020403061a1305041e061b03090b010608040c12050c1f0e1912080a080702010603020a03030e01020708011a031b0607030828092102 67
    0x5440252401a43c9884140500c60240e4910100c400300c0301e402c1d000416550659009041100e10415052000002100c500c201040302000f00542000851104035001901c40c0c212903045030107440b05246110385654806c02040f440c2000b41c52458035070001400d0141070725000039500e103591404000f000f0441ea00c0e484d004e50180700d14020003c11030003003014400001100d00c0203001d0600d0754240006140781040d180c0c03126401c800e1058105000180380c1e08049603004400c002e190382c50700c07220001081002800c0c014005410b410310900000411520f140184800816025100080e2112004000204009401000c1800310390403d8010401a29030442c5241500c3e40340c24801240c00c1440c1c0101d15203030413680081c480d907082ca01220b6100c6880244010f4610080d01680c580d10b02801004810051849803541c2200c1c04004d03042c00300c1d210301d8030140c010403901e07004241101d104505036455010304c0c40080d4034564800b100e00402c661403256255410038144e1001c140500c0c1c45003e900c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 609126555 1250 609125305 609125323
    0x240f05151219110a0f0f0908031903021e070b01121110030207200f180f090f0d2a03140903191223070201050f1621050705 54
    0xc0c03403803260680104408581c1140319022100c94000f030f103800c2006001401840800ca055004c21b40300d808491840748914816000da0700b141c401903203021030903401c03090303100407181c040d100b0154240041c02c881c10158071800d10880e180c1c509162551443e00740b010b41040c061f40a1941d40f418441c00000184000301317080102002212558096025200181c005e4403401200420101440442402031002d2034041d8260603000c5e20303d940c0b809810130500201c8101d4245065060b8603d0000030001c10f102c5000395480318980e410f580e40b20105080c024035004828000601007030f0103500580303461681203401c0c1c0c0131044185c1c07801c0103441c00d5100940400c03100111482c0003000090405182e0300c00b0064202c4030052034807485894801401c2c80f00d2200740e5074082c4c000146c138400a4124100030440040d0341a40ea10410b02d1410b001d5071f00541d152b51142100100f0000c00b4011521743c582080584a0864014645210303610b005410102c564807240c42040c0a001e024007982000c00e00c000b42c04c00b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 609127805 1250 609126555 609126571
    0x703030305060d02060d2f0909090f03071a07090b16061b030b15031b09010c140a0302120f09090907090c050d0b03060103080a03240f051512 62
    0x14454075003501250003103c0d003200207904040005040d031540d4010341d00142c91041070380c04001004044084c0ca540d58071008040c032803000d1052041c100145404114503811260140c11100141500b074021f03410340d0001d080c180d40c2040e081c04454019241c4503821640100580340040d00c035414014031031a02c1c041e550aa07495069021906000c00c059540304880709078282000103040b80740500018054007040220f14050381241c8000e01e2024008820303a409880002e4038090031001d072100d80c0080f40c010350803403030400c02c0e51103105011401c58601e4051100c002c5015064090881c10060714059407400d21040c03d0608220700d06a405090b81502c00c400d030b01300c0f58901c890300c8d0b5044491074040d00d5049260441e207003001a11890760040300500c495107006000703000c10381180b001c042d2260b82c00d200c00f4103100400c0165540d0305200742c0c8604030407144030001020a41e00e2140b86c00071601d6540010000301d00c5041c052005203403000407092402da01c41c000e03610341070300300760030f80e4101c0f9002e4200c407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 609129055 1250 609127805 609127811
    0x5060406050a0306171b0f0f010c050a0b0f251b060608010e010c090801090b010b0f130e07230f1c05071d041a0118080f0303070f020a030207030303 65
    0x4108940329420001c01040100c0c000c120324007060246a4440e83c02c1c0c6c2c5100391035000328650390014100040c041d561050b000b001842540f05040c019218000c9988044445000d080c01c240c0001ea22002030b240508000d412404807880c011501c0070031a500301c500000c082d9540015140744d0755200c5840c4151945a22002c1041c00c464a0910007030101074220480d0f950038094107101f41001507100c0c40051085d6942d80d020710b030380e81080e03500b2212a680042d080d00e092703900602c04400c00300014007241580d4280d1501c1c0403044440400828180d8001800c0c0641c50410300c4821036206010514583c4c1110003d400300c0003032100a001c40c0300d002000c07032072140041400e5402806400b0144e41048004100f8483e619105000405e46180304a45090f60121046410802d00b014801c8100001b00300881100f81c0100c1801914a400340b400c406106548607280403c01e46020b001160501500000071038403810310040c05400585840001411035001071220808203a001415408803078140c1000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 609130305 1250 609129055 609129067
    0x90b0402100905040f1a0a06300507080f0c0a0e0d05070b030a0f0c09080c09180102180f10050706090309170a11100c080f07050a03080711070506040605 67
    0x35500b100d000c1c0e0100b64413a2030b00c00b110202541c16044241a0200807260900480d000820042c40c0b02040c02500001101000b05d11245048182c10300300c1d0106c0780480c220101e48803103200d8140c1c0e01c1203c0d0030000451405c14413411400c00910150030440304403140d8104807540400400c0a503240215070300c21032640c0700d0031048c00824408074025004030f80313840356240340151f031413000703800c00143d19580e262801c04804000d178420340c564000d8481c45400743c00145407410800a040c44080c100506880c407280030340d19000c809100402100541c4da6590000541d484100500c5520b0030074124000d41d800001c8103004d69010301262a05039001e0000203d15030141802c0b680c2402a8200c403001544842510481a00020781c0e001032520030841224201000300a010507542c0700d031240390200da981e02101e40098410005482094880c10b4101d0400c1c51070345620f0b180c036448003002c1e4049422001445030b02540500d00b0030500883c500108106480e0001081140c821403082404001c2c0c04280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 609131555 1250 609130305 609130307
    0x15170a0b2d0a0f09141603120c060e07060221070804050d030201093002070b270d06090209090604020102062403070b030109060603090c05010c0320060604050a090b040210 75
    0x20500040541d800700320000310b1303181606244804602c6000c85d1711409444010015074601c2100540780d01c0751091102c2d418460301a908040c0e170900468015071900c01038020701408004000003861968000c1040800c498030f8144a604e5401d41d215040780200401400320388000e044608071002035848441c04000e500701240148a205402032450300380e40344140d01000d50b02d80f50303803001011080b00c540b030b00c00090041e43d440c40c040c4100301a95170240a6154120407a070103029140411020b80404948c8000001d60b203070000100458842c1e2360348801c5419804e14080c2c080d4441c0b01080200064207150300041d5503240000c0c41c49400b859140391145100c0144040c1440400c2c014044880064884952000e140c2003409030152003031400c0ca000451a20034000c480074250000d40301c10503241490011210014101d40c207400348042c10514545524240302c4241c45020240050481818400c041000342c60019001c542900c0c00c002a0b1800b143e04048204d4100e94112400c0c6403100325010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 609132805 1250 609131555 609131561
    0x8120606040b2113050a0b06190e07090b042709020301140601030e120301170309030a03230a120c0905211c0504030615170a0b2d0a 58
    0x80000414800b0526000c01005480200488003e0304034418403a43c4180ca2610130071601e020280141e40892a182c000c101040d818940002000d0314101d52020104280c1206410641c0705601c080900004c01100c1540200c40700083c00b0441002440c1c03925200b031200c00080580d9441042f1346580886180307540084e480000aa80c1c05402030111042c4580030160410045170744074080b9050408075512800c1c041272000140e40d8040405055900f010054000201b56510004007031204114000d116a000c005a0092034429038030440311840d901071310b000718699203051000c01c52042c80341022054201044420310616038000060f0300480354800c4940038002d600164000a045543c240b03840704007140302d0080074040088901d840946000f84c0303400c000100310038000400600c0140006401c0d900004841c00d40a421450a036440e0300701052030040310500c0010a62009a9160810800d400001e0744411200c3e402d102c6404c41081490400300c0e03003c0103910000c8204001000744520b58 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 609134055 1250 609132805 609132809
    0x10020c0c090403020c0a050a060512040501090605090304031208060a05040c0e040510080f030c03070f0c1503020406030c0801050307050d1a15180c040303030e150721090812060604 79
    0x1c1406140d810b180c10302030b4071064005134050040300c1000000c5880e0504400c0301c4115801035840b41c2c0342c0080e031107062a4500f80600201d40b203548864980001c1074144c01a80c0c041c10200700990342d120b2540ca04074041c000010041070521200310200010369850b603078500110707a8195030204a152010704111808006a84a168040d1034401880780080c1006400f900b542e030f101c0c0444d00710740f4a03110302c550390b0b004141c014203940d44204480d0700001c44a9503681c200c42e1081401145550711a80451020080c074801d50000a6004c42c08000141c0d15004d0000310f03e80b50b060400003541810003194640c00140901d03402401d0380d805080c100603032806450081c030b0f10725884802a08080c440054032076607007224a03104040195200107019002c800c2d190081e03403015103042c90540340d690141d014000c1101c010701c250055000304076903030305144010703846014159201c03a03070302e0031158a000b015030118501d4a0880c0c588400e80001402c40e40c02c46001001720904055155203410020340b09100b26 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 609135305 1250 609134055 609134059
    0x709060e091f0b0c0735030f0f090f040e1e1504080d0b15030f1306020a081609050108010e0a091205090307090b090a050c090307140a061110020c0c 65
    0x340d0000510b0703210090103003208000f04410340309010786d2100160817072260002c50300c40070111506c2e0034191102803100e112915405200303407400d040b190301105107940c00400e4500d8103550001080300c080e141c01002d0322007000341103a04200340c0c2e00508107960b84200000005600001415034942541c0081101c441d00703144400000d51079142a260491440d0054452000c0d69820701d082d11500d468520b03480c044501a845c0e0700b9044d80d50356100c94098180103401c031042c1801c0c40c05002c01080c12070000389203014054440c01d09504002000c8100d150320200f502040043c5024144226079204460504580b450105461282c8031040c0140081c4a140ca0080000000c07588201000360010b000e070090440440c00d44011980e03035407036281682c40b001040c1c0d9000e08503a000a600780299440300740c210300e0313031040141801c0c9050042032521805401c8040c18013250000903c103880c0140056010708211320304141c01d1101404079070750310603e200d170603212031b50049555460074104001c0340f401d103140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 609136555 1250 609135305 609135361
    0x60901120b0402031c090e090607080403030c1206030f0c050109060c0b060307081f0e0d0c080a0201140109021305040b0607021e0d081c0608030f090a0306110405090709060e09 77
    0x2140b0024081103507d21441e0400031001f0b0001d05a000003044051080c4607546481c2d070142d42c1c503a4220020115688400244850b8000c0c4500c241c43ca880b6000146108200b0010600c1180c2090003620b0502da10046c1004141c1c401889850740c03000c07040034480d0740003440343d41903241d100010341042e030700b034022003503910030483d803110000d150040b03454103940c400340100160004032842c04d8481400c50321840208000101400004440b200140700c00a65440001110030190745100c1c101082a80700d00c00e01500410b42c03140070f40c201c50b82c0000a120445d403c000440508020810030300501078040e20400400d00d1041140800054065034032000401c50402560f84c0e00d0002220b030440050207164448201050742d42c101d02e845038405481810b0b0040d424540184140702e503545c40001c035103421500d850310000000e070480c024500800603002250b92070380c1c105410b00c140940001c1c590002c01504000401c01c058210826549070751040e50741040395500d01d148003459000e00040711070302c202 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 609137805 1250 609136555 609136603
    0x1f020c0f0d060c081f06051c0b0405070906030b0d170c0703050a1a0c0304200102010e01111801050f030106030c110303130c0f0b0405060717160605060901120b040203 73
    0x83d01c0209648549603901e000d85d10740064030016142007030a80034280120700100001d14601c1200181c2601141d41306038045600800c1c000811700b91441a0380303200104107070400501076a41c140c00780700c010b10b6003078076100c0382d4240783c0d1500742002d9142c509999640303800091890740310f4014881e0380b0245070000221483c941541c42d204902108040c0349070018006d1078046513007041c004007124043ca401003048101d050001e1004c2c000680111082c6042d5966261030983c200400c0c040d0f01d01c01c904212200f5140c003001c0141001d00500d4a56041c10061700300610390025001c90243c90640b002460006110700c01c0880a81e02005101c07081036182c880032082224003405280100741c140d10803801109404da40e0380542c10303104114010500400c0c0d0500060005003840e80140001038010001c803000b841420018405030340c00400140f00c000c01e074070a51002e02103e8090560081c0003a00da0004941c0361420004202c04081e6005103840103c00204d4150b540800c1410484841d845011032040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 609139055 1250 609137805 609137807
    0x60709050907030513020108090c220506300307171801030507020309041a09100e150a050409030c020603070203041e030506060622141f020c0f0d060c 66
    0x429910499100d00c00101c005085184a8010b0501603034018030302d0b00e8602616030054480f07901c020701d00c4c1b07001d1054000d40c00389542d0781c21038401610700c00e180c2503001d01440e1500d0401c4d500001c120314015285e01054030030990404c0302020341b0b440050021543c494920030780a040d0b100e50680901020b0360500f0400b2080b440c03900034810703c68581481034403104080010740a988003103c2c0900982c006200e080d920741000c4e0405003000080c44007542d070036110007000030602e002c103640036031a06450410070301000c56601141c03074108103984081c20020101d000043c2d500401400390300d00540c2c54038080001c150146903649501c1c1ea0040005031a0b26241800a64139003151043c40c0e802c101c0011072420010591400c1c0c0c0a07640c10102500003951074609100d01c66000303a070fa403e80000e88500309400c81e5640480500600602c81035016001c0c920000c00002c5036401e18516081c0e0103010030741180c26000102a40401e41c1903401c0c00c21114801c00207500b9030a0728001a014501b0030309510484c0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 609140305 1250 609139055 609139067
    0x111040b121b041e0302030f0c1c050604030f1107090c2703022701120c23040e030c03040807030c0b0a05030a15210b0a0216061d0607 59
    0x38103900c03049031241c0d035010022807480650b1002c510560004000c00c1c02400150384011181050518400308100d96075400f02c1c2c5000802650290160080b80c8042540e1601c11b2903031200d4950200c42c00624003190f25015110a80136100030240107150100180560056403030364601c0031110300b0b46845036918546840035040d0408400000364941c480c0c1c500030020241e900290342108181b60400707034156405e1111042804840144072001c49403990542409080118042c1660303151040e1168810300d811090048142c01080f54010300004103a5502814500000381e948100c030045005018414000d040d4412140000701c7d90200040101c0e003200005011021a840750308280300b1507a844201e080503000e11100381001440400100380522482d0700002c01c012110380c0c030b51010540d1084101075152003600030000c0c841e45880142e06002d05c040100d640103c90361410340c0380c00540c1103451240200c40340010f102940d5400d44404181c20006140480a0b251085840d1814212000380403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 609141555 1250 609140305 609140317
    0x609060906070203070816020103021c0c09121515050a0303050309071415181e040b060c0a032d091a0f18150d1a180106110111040b 58
    0x106100c0d400120b100b8900c00003c4511807a08811103a0500214151701101c1034051007040e41015001c0c02900c03068900d8041048040d00c10700000112164003010240641c0c2d41640101c0015041b0510381c004611494420400c0d9102080002501d01402030022030203103003074000b43d401c0040c02002008058000c001036005000c0d100481c0c44c06540c0710302440060599080ca5604079828107040565400c4d0071018100c0c3c8101d0110390042064500041074000d80d8002c442c82c2401c820069074015030400740b24040006800f07231207851410000700f035a507581c0c4000c22401802c02c078940c542c44580c1100b082c0c2c4117002821081940c81d241d81d481c0001000f841d41c502400c854900c903d2008410006400203d4405414000d441e03410310300b902d107070440c0c00254104010341041003c0c042240c0da084040c010079405140480001d80003410360b42620f409021244003074015124004250b1990f00458061411110300b0300e82000000340060a1501420199900b07036441da4005c140442c806c0c4100c406460 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 609142805 1250 609141555 609141571
    0x60d0518010f0e0f070602031215131b0903050303071101090c0602010506010207080715030203090307050d091403010608150c040e25082701111b0d111b0111060906 72
    0x3100c280b040128580311809440341d00050380c07081040301103002c820700c2794507880012580c070b82c2011555940880d086002441100d07a41540c1d6204180b4040d070880400400d650052070100b4030b503400c5a407915038030b2201601400500c541a410010031000c250402003200b40e221381e48031013a0f559424040d001c0e240680384a070160081703c0c400f043c0407100052080840f15640c90803c400d18481c00c080d0000c0d40042d0400c5030501081140c0c0d00800d0080014005485056441c003a1140c50800f6408500500350510b42c8241d0501034200f00d6440000f03940203108d01351241c40d480c80c0e15202ea10041520590744400c0402092408010980000004d070386c2581c00708100001d18596104411107001d0703c2114240000c0100c81890289001c50344c49081c03144020000000311041c2c0b001d008280c0ba0441888030152040020481c5c42043c006d00418000c0605414030209981130804001c0c2c482c41030703400401911601035880280740e0301c04c160031541d01489030151035460400d5020720b9111402224028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 609144055 1250 609142805 609142813
    0x906070c0317121317070c080d0e0303030f071b030f020d08090a1104110417010b01030605010f030b0a091404050c101403270703050f0102030402060d0518010f0e 71
    0x395086000b50102d034040314500c81031444039520400320b08001c040c1310b00152078072034016015418601c1c041c801026183c1c002c2452402052078822010b151551500c000d80402507003482c44101d43e06c00000380c039002a5641c4007000745a1765614100c500d0000407000c4d80050300030030b0205041c15044840007203020350030b40c2030f00c5d10404180800e4403d1031040e0f4540c48030354803c1c500c1d00d000c00d88803107030410060401880401d12a001c00145205a000b030b4000c60464000c1d509440c0f1030600c00d1040840d607801c01e09007030205510300070003e4071203003940521605254840c0400a0a5582c4060300d8000c3c08000f4400c0020b0440e034103407044c0ca01000c81d0211458402da1070305d00c8603850607030050340c1091071590311042b59000000d030900300c50300051700c084100740600303a41c0151341301e60b41403880d0011004c40080006d42d25508056142007120f1074a5591644108140405030300c03040d080700c405008005020501d41c80746480e180c901030903010b04008551a080380c1481621458120b2500501c07904111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 609145305 1250 609144055 609144083
    0x8041a030112080304170d150504050705040b03040c05090f1f0f060507060207051c02070906140d050a0c0e0105040b040b0d060c14030a020d050c09240906070c03 71
    0x444424030081c082d44071035600791244400042c00d640015503015202e400c0c0184c2a0403503103071b000416000000300261180d140e4415920451600701e40030010b0000301c8040c045402c0c81e41c4060518800d80c01484050348000001800f480598034420009110240800c4100d240ca80618210200c090f151908500d0f2a08203400703108903000483e40550b88010280f44040d031800390165405d600122044a2154081c84080041072042c42401e04009c100b4201c0c002208a401000342001000d40043d4076982c904034040c0301e205078040050445800582c5c0c2c82d070309241107051052801c510080d00a00049845001040700051760101e00c1c121401980c0601030000954100400d40307406890060304205c1180e50103012445981008010014509206c00740501682000d0030913407040f40c507041d1045d0005910341401039580300b141d0780203c1001c115070a00050400042e121145111240740c200301b8442c01d0062068000121007003407034003c1480303603a1100d86c60300ca1021102413000782d0b1264908506 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 609146555 1250 609145305 609145349
    0x30509040b0414010608100503100903080601020304030c0b0f070b31080f130302100c02010206011d040b1008030a0e24040b0c190b0f070e0607080d02070602070804 72
    0x80f584003c3c040d4140c0a0f05a08010085503a00c0005003134000c0d40078281c0c2c0000b45900d05100518001803841804030b408149801c0c00b91444902400503411540100f10030000f00f40d002c07541d00141c2c2c1040d03c000e0b95034503212039450554040c1c8500a80f1500d188418424000210103400700040c450355000540050f0340074001c40400040e0001400c1004100820210640780d0f07001829008032480c80c402040e9207075000300300c2840700800c0840114511a56840c00d641c0c0400c03030140186140c1c1040b100200747c40f91924082480580300a01303082c038450101e00607404a06090016110090487e41c40c1d2580d010010060b510a1100600404440c0041101c010303e1501000200344c94184251516140c04000c4c0f100358880380304078106010304284a0f0040e9000e01c610965a400f4000c079220781c0c201304142568111002d0041c10034855911031520460b11b40c4016216a903401c030915980310412500d110010744101032004201510010f5010304028090700038009944000d54041c055101c110a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 609147805 1250 609146555 609146561
    0x906270b0601030203071d04020c061f1a040302060703030e012f0906030c2107110d0215060f01020c28091a06030a140108011a010219020f01051303030509040b04 71
    0x1901c05c0041d401c1c0a1450b801f0340395054004011030003600c010314008039040c005082c01000c2d0386c01010440c0c0314211920401c0d4500c039250141582e1112244052080e46c50304541d0304c034501c0004e01800c000300c1c588007458000d6000e1092080e2110090001007030503120040901d007141040c014001c80d088003100c50754669819100216400344c21a803964440703c02c40a81d50b0402030000007005603a0103040c1d01801e8000885004002c2030f01c4007241d8039212a01c1034106503a65240004541c8140508074001d403401542d2a007216042d01c40c20340c0a10800d004030f0404200340f0034540c101c0300b140f8400400c00002c1001401c4d80c41e0140850b282603071944101d6054131003450482d58203007490315400d00646805401035400280d59040014245101c40c50140c0c241c4090b0f120180ba40d540d240c01c4131440c40050141e210100d024070103800711070404561500380c0b80803000040c2c092410b0480d1550281d01500032a000d90b00207030300126101c0d5503481c0080c0140d04c08a5282c2c001c508025055000c0d0500d40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 609149055 1250 609147805 609147811
    0x60503120c190c08030c0303010609150e011101090f0b090601051903023d020c03031e070314130f0f080615010918092003060a0906270b0601030203 65
    0x1000d00805501449591041409040b040c1c81074081040b00090195080004111048814000e0f5880350700d45600074000104503071081c820000700603c800c2c41d046e480806808200f03000d00b030a81c01061529681d41c0102403440b00100301c035442c0e908010901c000c4200f05885075808100f00c0307019a88540c1030100400900c00038400b40180d01105000520b0300303810000840303608440c291002e1090f82c0f4441c80c005801c41c23501118030349a8010004031a03060091660315202a0021481c149000c0c0d6000a5a0000e00c000810705c840032641004241c440c1d42188075959540103c0c40d200c801541860317402000c0c074400c4050402c0654400a440103c003800c0000700c996201c0a030800d581c9070051541580c02c4520040c0c100f00d030003000822682d5210300d9800107285071140006007034000c0d00d061200180c0c248005041e42418100c0554650f400260f100d9000b458000e011540310300d107240c800c01030195881e10040420600341d217000e00c2c2c9a403d151001e558014007440a00da2a114010b60881c8016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 609150305 1250 609149055 609149077
    0x702030601060c0f0218071e1d0d0204020703050c06060102011808031005100203071104201c060e04121806030c0c050105010b190f0903020108070c0b04050106050312 73
    0x22001080014000c010710940f0601030307240901120000c3c2d000840b00400d1074550305041d94101c0c14000400e5010748a0030211041107070901003254000d20180202011025044050850901c0842140c891034048089681d01410640d12018240760280c0030390400120fa0901c1c0c030503240020802c0d881402400780f40004290000c2186183d03461301100d40c0e03c01485d196107150041000a440c0e00c45040042d0420240d0b4051a00d03208541b43c1b125000f60364100103881a4180baa01000d8100d40c450480610007205246030342d5000070780362051825101c07011a65804e0301e4030400281c04041129103502c95031145200c0c0580044c3e0071821399403143c000d40300220f070301200d810502c446402a0701c4a2140022030901244803116507485074203492090300000040d0303a0100d00740c0d10a07030035842c040c103459500b41040402c00b044000000d003074070307003503c03001e4100449140422640d0740107120209149803c401701908918240c104180079080c9442124028802c002c02d0120b07034010202910300e10414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 609151555 1250 609150305 609150313
    0x2d06061b15160201024008030d0b0f0f191701150509040f021002070320150a0507060216080a020d08070c0c090905010e060103060c0e010809030d0e070503070f1a070203 74
    0x2490b9054004a81010414240c100316455102c088000308071b000d070300501c1850021540c0740301c107070390040c00d950b1081c44413805418040c3c142c180903650088a862960000c4da00d40075a040400002401100c0d0390f400f844984440350b002010901d0306404c80041c2c25034812a080031a65034070140320f80380400b10b07005400042810001e0300140b50034107800843e1005881151642a00c0340c540038813040c041a1651080c40c1178118404041c107010740d00f81001d0b100f9555150524244510140c580e21800400410942e800113907900c0c0810b000c001d550740b450700542c01a803140706050002c0e41e501200301d81c0c50041143d034000603074428410350811032466400354000140750b142c991400040d01601d030f000c94072035480b880c0701c5241c104104403c40c002d45c05001c01080b40041684098064030032407a4040c100146401040001d040010885402c2540c0b1200029495103960f5082d00b809500c0e00400d5040c040c114002503402c40380d003c50410745400078840c695410821a00e06024450240003e4060b04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 609152805 1250 609151555 609151597
    0x80f01060c021224040507060c15020c1609150e0105030c09040c0b07080706050106033c020406120f0605011b110402122d06061b1516020102 62
    0xf40101d0450125014400300c42c10000494881e10004107040003050480e25410104000d001c000c11955008207524100000840c403c3d44880c0c0180c07509400c0810388a4000a1000d45042d0400c01c150300002c07010040c22404c1e8440400001802800d612404813083da018013048103810344000c503048400c010001c143c0081004c09114901c1b0380100140e40005c08002c0007c0d0700c43c4030303000804c4000e108220040e9100303e5403829404a0b0810307080314080501d04003511040c03078400784000e48502c001c1a005e001140c901d419600c1e0850341c041d0210ba8880c0040780000700190013520058800e10008414400980600b4500040390f0481c41542e00060400304c2e00c0740306140036a10200c20a00a40300d01c03da9101c1a40850240e82c400740c81d040c0c5005000003003040040254040240f149521017515500c0450003401d01e44080e0040d18140c4070b29000650142d0815903006540650b11040081e41c11004100c4104007101d4030031036001c11039440b072032010500288103108a507129000d200319000160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 609154055 1250 609152805 609152809
    0x317010b0a1d040e010b0108010e040f020904150905030d0e0316060203070903081c0f0e060406020307050d1508160602070b030402040902040203090c0111010b0105070605090118030f080f01060c02 86
    0x105015a002a822109280340c402c26107607030245204084203400081043c0c3c084800042c00150160b02c01194025201f0034000003410440f484420302d40c0403102c00489441c0c0d810401003081409116420f400c1ca00801da0302041000300141100b0446e480041058180d0480300d692a4400c100212646250500b908400034095038051600180d4a1030404c001d030b81c80c4d58a40301140e000440002c2d25181030032910b2024031150003044018452074034103200c102c010500d004d59524025100401d103a03008070015604502c600162050640c3c12803081c8054040b0031450400d5142e5801030348c0f000c0c00740d0206001120b500700c002c082245c21990042c2203081c030b0314562808135080940200e90103501c50300e14001503500ca0000d540500c00c4007014210000005002501880381c1e1124401140d040000c41410751303800405541d0a40c1d0400008a44d5940746206580148140b81060b10a42c0003100780c4c80505510103501409000700340c0301e10240340c503118840406c8020900c01c030b50000d6040c0607010014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 609155305 1250 609154055 609154067
    0x100f09110d1802030613060f020403030507261b060112050304120f02060708090a0603060513230c0a030507090f0611120a0201090c170a0f0804050303030f040317010b0a 74
    0x14002400c0038106414043e030000307040c01c1c801d0340c00340500304661200209100c610720a900b00001c00d070501310320b4107103165005811170042c4940980218a590075400030f4034403444c0390046c0d20fa8141c24403561010881d42810750b003015003c10f445d441c85110000300e00340c614203444001150b0800c0007941040c1c078007015004ca40c0340340e440440d1000045800900142c95080c05012003500c508512500d41ca8004203120f49040c50343d000e01d0801d0305108041010703803649901128841014400032031055561407050f20180b0520345030300b204051101c20440b01403064000b4107112245581c0030702071511480401c036407400302070140800d2403003102010000c1034019044c0041d004902c0d0b06480341007101800ba5003140d0010001d44005d03035180d40e01041000500404c1c10041d05215a050411650b99205541e44091016009000001c00c08401c000d00c40c80074251002042d004045a42e603140c03c02201341d4000d026502140451310340c00340082900602d1004d24180c4841030442c5040c17100c8550101c5030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 609156555 1250 609155305 609155321
    0x24030c15050702150412030509030d020a2303040f121208010518091c091706010e0105010e01020717030901031a010e091503070e01081e0303060d030905030303100f09110d 75
    0x340401c01c07000030203488929030690047e010b91546170f00d0304000360030b00d424103886480440071500b14804a0303000031185201407502845504e9500c6408000b100750704d00d51703c2550411036085818410003e07850400d00889084e02e445900454214403000c107041e0341c400c80070700805500c0b100d69640c2080e09000131954551102d201c40480e90b4010040ca64140070382e40702c0340d0b4000020308161040c08050049003c51501c208000300a24081d89400c060030b00f14401801038a0400c12400014880c5078820041000070780144107031000302e112248172459895014010480c00b090510b0340c030044511080c204008100e0041c0c407401070745010282004038141000b8a10300301ca159640901e441c40e2402c201d00400741c00d003c8c010300325650404410600d006107201e000ca001095550010515600c04010f4070b402c0442a2005c01408005107801c0e82c00380c1c01d640005030507110100811207045440041001200c2d0070380780701b0ba03586845a06040c10744100d00c2c080c5808a904014541d4080680d80c07000314 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 609157805 1250 609156555 609156589
    0x3180406031e0c0519030209070504050907020c010315030f020f0103110703050301091b1b02031c080a060504020c0a020906030c0411030405010506010804031b0624030c15050702 78
    0x665a0300c82e40d94a032041c4140ca200c00c10359042501c86401c00c5859001500a80707400c03280d010350303240d0001250041d508513000003405814108041648680030300d05079005003500a009540d0741c45c0450000f50348074111148135000905218101b09071803900030518054035007140d00020099225002c2c00000381c104440141010395132195102000d12110141c030391640720382d032403580e2549445d00a8054400b810034010295408504c2c101186400c010100e0100f544100000c480f11002d00000e800c1804034000b038940300304081c0f00c80c50034561200720039201e5403042c1d108100d565118400d01c001c9000308162000760b45d2040042c0c0c0c0c0549000c0c0c41c2c6c29808500181140c440b44401000305080d40c09000100c58150000300a0004110080c0a4168414004e19000082e0300e01031b100108007030800f80d00010701c2d0b21085c102205000c01078210030141d040d2200fa0345545000080c5690f01d0364100e100540740c41100f8100858035424011240e0b0600d0607548d40d0a0401c82142c08004040344841030101c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 609159055 1250 609157805 609157811
    0x5030702070803041d0109022109030f31031220010219120207020a030b0c09031c0f0302090915060706060f05090105030105070f1b0b01090c02010c0c05031804 70
    0x189900c2c003003000f400508002c028100e01e14135001d0144001c2a01030300440304840c0180321701c070030303010b4030640c0d00c603040c41e07408182640380d00c405503418214854030b080c1d20300c103120028101a8000b820340710303006803454400002c603480c5400e06140c0064900c9000003040400ca2007400504030b440f900d611581e00a041c0c440c07901c0f518880120781d0032680f15036443c40e0040b29030b521b00f052040d00110444c41c0203041d040150b1030255154001450f40d002400020705032403140000c548441c0e003090690360a5031010b0102e40302070390f05450780308001e108000e400700003841d12400b050349244a8000d4038406440038280a200c0d841e610031003a041880400205e030040d4080c80000b000c02c40c03d00031540100880000c101d202414078080c8442500140c0025000b603040c0428800d03c3c3d6400a40081507209500e001e01850309031600204440e00c001c84043c000d2040c0c000049000c00c1654400411072110760020020020b407a00159101580004098019001403200d0462440750007400700043c0c1000f0400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 609160305 1250 609159055 609159059
    0xc07060e0a0915080106051c06020f07140a020f03070302220e060709140103020a080703090602090d080306180105011b0c1215050108030913021c0507020604060b010c02100503070207 80
    0xc031040702e8000c4080c1e036240240b02010000e04c01c0a2140d0000b4100580b0752901c01009504405804031200600400b06a40040c040c01c0300c0c104c4500392000550720081004583c0c0301a17403415505c824889003070b4032600c10b92092400e24031300041d201c0c040303a5001d0700110540320411204208400c0302c01d850040103848200307a1000603010b100b40c0d4030404503138455a0420342000340b02c044a035140d408080c10b05104002c01180d981e04048030340e41c02440c038a0081503a03107151409601034082c04030081e8028105002c3d07102080204405144039004c150383c030034a042d0301c0d0142c843c04042c0c06e1181c01e000c1003200c00316080390300c045101000d00300c0c002c050f249961952103e0354000003e2103001940c445820a01da120081e1450103102c0c01409100e00560030480c8680c0040d5400e0300052044581d9640000c0500500040b0181380701c0c6444444400c00640c904404080d445401c2220203c03401864004280c501c2d41c05004800905900038107442c03c40007a845040c3d4013540082c080a0641c0300e40180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 609161555 1250 609160305 609160319
    0x13062702070b010f180c05040504090606030203010203010b0d051006050702010c1412031e012111060f030609160804020105250305180603091b21070e0c0c07060e0a 72
    0xd42d4000c000039401c5900c8185000c2c8107090315008002114951410800400d002650110548040d030354110390025a40d010752800c40c0040c2a01c1e40000c1d0154000300000403101e2104c4040d15103032950b9442401181c2d03468900914988040c0070302c1000c0360051117404007551054400c0e084d054400d034800402e0090003041c039880c1881480e4083c03000317440082000075802070300703030f001400c02404140000c1a504109040c102000c419a03046d050406040034403042c071042c25950060050301130640da550f01c81d00c0780c01d0141030740111440c81c080c08094001c542c14004440c0d902d0796594180e0303180c00c2c0640b940d13401103485500a580041900b60002110f400a030b1041c407002c19098820b841c0e407959002c0d11540b400710030007602045441941e052007000144200420a000344280c2100e0384100d10030681c000032150001c09a09002c0f058110220082100c0001307040f0068171141c200f000c0c1966603001c2040d0b03180c8107201401d603161300140c5d0104a030030300801407000d0312140200030008803038507149 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 609162805 1250 609161555 609161573
    0xf020a1e0c081605100c44031605041202061b15040209060a0506030105040c11120a03060f03111e041107020901061403070e03120c0c1306270207 64
    0x3e8045812180b04007040a1300d0150000d02da61021070516881d248110b444a20401c2c0124413164010305c640c4200805003406201054844a480d400d8032182007080d03031216107a504219200c012110765a4182d14401e030145c410745d02120251a0f204560903020303400d1082541210200c151460320a004c522680c43d0305000e424803080030000c90b07204030314141c0104440e40320050101c5000301130250003800079880c1c5a084906440c000e03100890180c0c5007503c1101d48405480c02101c00d03001d043e001d08060000c2c4001000c61000f0b82c0d905010313007a140c540c0003100e0400d92100602034080171152440a05140d10b06110041103a203402c0801c511440c0850191748140d0b0a2004440b00014440218034120402c1400b405c0b1614001c1c034007a054603800c0d0501e11010f0901c41c00d114035164000380d907580400150b420b80d40d03203100355a241c0440b460425905c19491121303500c1006484c6c0454803c4d141444ac1b041100c030481071120000d114070540101100d645082840030342e1f000c00894000c54500c00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 609164055 1250 609162805 609162823
    0x110715030f0b1504140a0f03030c05010f33090507030617010e0d120b0607320c010f0309020a0305031201090c200a020d060c0f020a1e0c08 61
    0x18901061030310001e2059011545030040c56841800c166114070b001000c02e5054800b680d0b0402c00001c440001ca400154408080380c2c8448085100d100001c030070140d201080ca801d4511500003072080112010140702552000d51114014201521181ea80130842080340c1802543d0f140300204007546800c0e510302500e40c22108031010039144c401c1000241503920820440000710070003008000c5080d69a9610b505c03030300c2c0710380c020030050561700002e00800c2d602c54906810010455661a0442d02e00f5441811100c01c02c2d880c0c0624210480d22421013003040590b41003040300207418044010320064805469180311071041560312200318006032980c198000145008400442d00c54544040e01e90410703405800801d00760382825000c40d405074101c184401d41034600c0040301e046016401003e80b038803114500207548140503001c560148907542c0d05c2003203041c003195140380c00003003880c200b42e036981c080035001004078000303594a07503c9014010585402038400c40c404414503035140c07007091400000d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 609165305 1250 609164055 609164057
    0xf030306090c0901053c0c06010b130b0304030309020a05091302060c1207060605092d341d0d17130e0601030b0d020d030c02030322030b0601051306110715 68
    0x101c5140c0c0001c0042e20a00e4444486c000c2c036107898003080241182e10b03004184265103503114041200320420703020305002d902420052200341d13200c1c50300e428010064480004140e000d05184000445c45041c00901c1c28803410340b0f04011174040c201a400e120003903102070001500ca006444000f001c42c00c0c1c050060134402d014041c0403c1c214248001c11034444000b4007000c03100840f054920356090b003944644418085006011041c0356140084000c5084d41c22206103149003441d42e100602038100b0b0006041d0a03015031314150b120602e84000461b4074060400980d101405040c0600000d080698251a58800324807881c04c1c500750011000360101241c11042078803810307204101c0c0c3c659140c0f08010359110116440d0b081c0011a40100791a108405400703800c2001c0b409141d002e540f01001104c84600c00349003020340601e6070050307100780040305000454801d800d940204100d90301c00d0040d03c2218140b1151101c0741403800d4003d0364004a01143c025184c00350100c00100046d14098808600d141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 609166555 1250 609165305 609165367
    0xf01060803070c0602010203071b061104090203040507050a21140d050406030c1e080601030621060e0d02032a150a0b030a0330020a0e030f030306090c090105 69
    0x1451400c0c983c86501c941150046a105000f08003d560b0b1040c291000800104140c82e4980201e0510344050101e0411510200c0000600014440641da00452050780a10151180309885004100415005201c0d103c44002120070306d08400e404521070300845481100c041980c420006025810260150203a0300450b801240400c5043c0e054040e9148a04403442e000701e424032649181c01c51101c000c400f80041141d401c1c006102640a5031000000d060360a00c00040344590b41c58054000d102c0000c120340860401e081681d50707510010750500d0f40740e0150040c500701050554011242d080002c0383d00941c81c606000fa0038081014440c03a41d0fa4220007202003818609100403409071403a44030254041c0c2c0c044d0000301c01007503100300c07404a0014a55181406680a0f039680004803040341002d203c1144002810141103030400000201c0c400164141c40107408482007a1b80c50f8003040b00c00e02e070803403003950019085490300c2e0000d01000105060041c140701c5650110500342d00c81c4a00d2442c4840d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 609167805 1250 609166555 609166567
    0xe0a05010207020a3305090306041124090d0503040b03090601031e05150c0408010608010c090e040c05060d091401091b0315051015030b18060f0906030f01060803 71
    0x304204c116001c1d1031100280c01000c50b0398807080180e45030010220074241540e0308050802d07031045e000c9a400040090032520282032a091401181c0304074207556110b00c00c02d0302c4c0216000404185031030742c1000040302a0a0200303040500850f00e5403110100c4150208000109081590301c5c09903008a00c150300400d0550704600e803000600702030310f607060000d0340750006002c0050000501c08922881040c103500c901e881d06980c803c07540c000ca4020500d40e5003801c4012331402c005500c803004000e078a070b540044c259980c1b03085084c020800c0e500941f00680a40c030a00c05401d200700144850701c48600000307840e0b02d164490418200001d00024061b035180c1d2070346001d10103550354841e840c0b90b491600c409814610b5484034128100700ca40e64010584a0300000c80400700384c1455001001490b1120b81c21503480c42c4010010144181014410b407540c12142c0c0d80005070400c074901c00c0d20701406109151080c0010031105a400070912a03051003400c0c040c030030284d0b0a0007000f0083c07088200849d140c03030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 609169055 1250 609167805 609167809
    0x30112050708060a0209270a150803070318140303070609030513150f0503060f0d0807050115061e0903022e03061a031e07021c09051f080601120e0a0501020702 70
    0x148125407900644044443c284c1e84015400c030702c1540141040c1310004454022100407010b449490f4094007040c007020445c0c905053b0403110095401e103420181500e85501c582403c0c861940004401750103030b01c10306c04040042c000340d1100707803043d001303081c81da0810784036020400400002e60801d0403a0520400300d030200c19007180001c0b07680c05030390170001c0c214600b00c03020958081c101006248591310401c1b8050502c0210421140320701d070001c000b8441c55449444200031240e071803141e034000621b1106007405c0c0c12040f410740604425507a5400e49110b14540070004a4102d00301e842001310048070302c445003011034030182e800310b1140f0b032004510a45001d1050100702c2c054071070aa80c0081c100201301b00820171400500303c410803042a4000340d119100304a1401104602160250300b17070840c0a00303100d8002404000702c1c0e900b22a5040d5002c90342100002d40d039410410b03440401c0001c008070361258003510b0300b0340b0300030345c0705000080c0f1a9480100070720701740c1503440a58050b540024940254 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 609170305 1250 609169055 609169069
    0x102090a09020d15050f0f0a2105060f010302030303040803071b060605010f090e06010507050a05010c020a021c050c131104030f03080f0c0706230f01091d03030112050708060a0209 79
    0x60b0051008890515140801081b00401c01c0d05160384514203a141030213040c3d490030103d40140c20000c0325504000030036a10140d50440d03107075050f44c180c454040052644000d000400e4103a0340d002c0c020f9411034543e41d541401076003000e011101813040c0042e0051000a80b1f540d54041d540c021000450502c1c6068009000000c61803a160304000d0002c80078400101000c903000e400072000e181544c4e41e01d040b41482800c03d0500a0010255404c140022403a82d0307000440c684840e000301c0d002c04038820842e14203000701c401054001e10036007000701d0503240c03031505c00d000b05250f542420300800d42e01c070031440300480c40e030046c2c10072145800d10441c07601c141544030f8a03091307202c0f412640f4980a07041200c8500141c2c090000014500e40e00c904d9100c5051410740c0c0c10840c440f042d000001518203195081d40030400e030900502c40114a0012004904510990040107001804001d103240d6402c0c40002480c650300c3c1041503801e0f100d58a00051400410000148203c0544000680750381048081041c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 609171555 1250 609170305 609170321
    0x909060a060f0b040b0f070f0b060120060609070e040f14060a05180408090405010b03040302061f0e1b0406090303260a0e010b120109020913080703050a020102090a09020d 75
    0x815074a1603401c3c040c158905045605072108042e043d5194043d1880a620610034140010200810a02010101b20601c06c405000d40781c00d0b00c48a41803000e140c203003142000000320300001c69010304040365540c00c0c1019080c2c1c0201952400010401182c6d0104040d21080f41981141680d0341c1508028500032081c43c1d500410121000d142443c03401c000204494404411241c11040e403401180810a0b00021160341210150080c095580d48000b41d801d2600112801c0e80540120380014a1031101c070652204002c540c0283c80000c54140408408a10001400802e0b580134007003c26040540c87c40180c001800155580c01c0c07400d0071403800410642020200d41c180040300c103184034201141d15055580480b40b0764000aa40c1412040709000d44525059960003049480542c440c10750190020007415009944074070749521003180c9880d800c0200030015190700b40502401c80080c2c482d50060203c21010310001d070800780520005024003021f03500080d200303680003032a0b0101c8043e034050400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 609172661 1106 609171555 609171569
    0x41b120c080c0a080709090f02032508030408070b0f090d15061a0307050a0c05070b030a110a090b09040e0307060f0509031606020304110909060a06 65
    0x18405694091440039000d0b102c50000c2c83d052041c440c4003140c020400500309a440e02090354000c0000030341c100c9109031022400301c00740ea001c120f05120f604e602d4041c07003108495040c802100d1145a8415142d580060008001010022801008840a8100383c580d0740703115801d851103c3c8505940319034000e0b00585080103000390030100b10404c030b110403010040700c0c3c0c807200302511507200c1c107142125540042000030400e078850805401a6450b50502c0d40c1c02c9030b8a6900c0d40e080c2601070308400000710000c0100454141d0394000c01051202000c10b031481c00d0607100004003030035854003031201883c000003507401094650f030b070144007a8258102a240c80d441c480c0341880103044070b003444141b841d00f860041054480e0110880d40d02074805041e0400d040d0301c60362420302039040108203403189981d4036003400c030944807001e50390300c506009800350049260001d645030032110030303030400c003 = true := by decide +kernel

theorem cover : BRFrame.Cov 608992805 609172661 := by
  have h0 := BRFrame.cov_init 608992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 608992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 608992805 ≤ n) (h2 : n < 609172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
