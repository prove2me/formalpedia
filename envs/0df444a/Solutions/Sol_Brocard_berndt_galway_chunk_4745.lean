-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4745
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:00.527146+00:00
-- url     : https://prove2.me/submissions/6c04acd2-d3c3-4eda-9f36-b46939f01a5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853237410 ≤ n < 853417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853238660 1250 853237410 853237421
    0x172413020d0b06040c05040b0403110a0f080607030507080105011b03210b0a050a0608010e0a0207060f0509060702160515090a0306090201080a0b0109050f030c04050403110c0109030c0306110d 84
    0x20002c1490a080c581c1c00c20003522048801d50080020602042c000d04054138200d4084a03401411052284a0030000c42d0442240354080000318050200014092001061240c4151320996040015950b1002e0580384c03500e00703000d03590004003241c59070b04600c031003140184041130013820f02151200d03501d07501020501d4070755103008280391a222042c0c0903082100001d000341038111001880c09082440013490404144200ba400c0104000030642da10183e034111886550040400d00007002c40da51040d000e40400d9413001c54911030300c80082d10261001c1028000f407103010360303020f04e003a00c0e2800300710384440c00c1d00c000b19681200f08074a008966a141481c00258422800450b804078140001b4128200040c0401540c0d4104010400303180c0c2d12410310700c143c0f14200c1e07080c07201803201004249460108100a03400914100521080c544c0206624420104000440f40c904110100445a5074501c1c8002020300700d0310703441071002400da03030400b20031050316175105401d0003201e001c0a01070341d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853239910 1250 853238660 853238663
    0x9231005220624050c030d0c090b07050304060905120714120105130512190c0c030b0f161103030a0b1912060c08010b070f02010203160507172413020d 66
    0x81412102060100f61810006415040da081190030b012001c6610350301d91040c4484004001d07901e040490540303010300c0c2442d0182a17035500c883c0c0c0303a84452800554950140c0551004940102070014880c0350007911032070400900409040c0fa64a403504100c01c0044070905e4a512440c852104a284003007440f0740340c41007060f120009064101c6041107400d02d80e2030290601d01d10410000c000e907a1a103d10200f501c6841464440f144280318144100c0071116500000d00300d1844206008003e400c41140d140500d841158596400000301400e0354880d0000c418101281c009000143c001407059024485034000034143c0300da03114034080742e02c2c560070f0260844a0740401101004c2c06018051080c828002900d0070144d5213941010030310707038250150400082c00e0184c08040d480459209200b960681c3c29814006180510b1134a01151606d0150262500c3c072924120071940211001442041300074215545000d070f0448103888020004006180f8201400c4244001d401a201d11080746a031030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853241160 1250 853239910 853239929
    0xc15032f0751090f03080702011b020d02070e060f0f04110c0f010f05040c090f060503060a0c0810060c0803100e04060203061206010308031f080106092310052206 71
    0x1288600b20000741a07040781c0400940038500344111001942031400c0b080c40c1138150410207516514031074202d02601121b0b50f480640e13080040d400c8200c82d00010895031254070b0b5000c1da00c607035444090520060300100e85142e444001c0ca00f0042550500b520b0b0150301c80800b400115549060505182e42688a00307405100c50340114411101844280700b24083c1c0304001d8018095410180c035005655981e601400450603a259441c03c4405c0041d40504000d05001e020f4079120314041030688001c050350400e40000c900c842001803508080010072506640494803a01d01c80c008644492107507030002404456525820800402c44060b01001c00d803081d0311650015942e882c7c001c0a02001d10036126030706240342d11481c0140005010201030300d6100205006c9030103c01c88001c1c0400d00c00c020365001d0b13803c95181c030f20701140c8180c00c1e81210403002c2c4440c806120000400000303180b1030f8011a4440c145034200b241c203001610b0400186e000042e0440310f00d040100e5680b0b1031404030ba1250744a0586c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853242410 1250 853241160 853241273
    0x70803011202121528060b0c070f0819051204030b04020406060c0201171b03040606080105100b0d02030604060504150f12030c0f0c15032f07 62
    0x8503d040c2441e1026942850040c0140d0021400000050300c005403102a5030301100c05000b0b2101354500029645116410090244598840e10f50344180d2060103013808034054400e01054480352160020115442c0400034540d9000300e00302c00220302e00500048a15020300c0c4121346503cec00b8000035002945c01003100c1003003410240304100456106500080a00450320001800760b0380041034400005803513070200700a6074480881d0aa00b017041c0c450406600c5010050006100d034a0344010156501c0d0320081084d516055100c1d040040c051090b90380d00310007007240f0031510350b0135006140c2024010308013041040e1200c0016041da204040051006040c0c00001c01c20250303c01c1070305d4010464015101010201510000c0200c404807130064400316211081c00200103050583c18020404801c50800c0303d40c0100c130040140c810741c1001407506901c4184000e9a01c2c1d03008289404c004088006880c0c0340701561030341003c52000911650445224220640c14003850074010f0700b02c00801400e001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853243660 1250 853242410 853242413
    0x709060501090f0e0a0906020c0d05031f051f050d02030424020306060d0b0f0907020a031107180c0c020301020a050d110c060711030c100b0325060e060708030112 71
    0x21108a40e4000307990f00701a030030304020803407100c0d880a820141e4901c012442c0c03d11030410b10040e120750205000c1c40d02c03d06103251000c59114000e54013039000030000c210398058a4254400502e07c9005050384400160300703101c1e00c072581070b480c0c002503103281c00e100303041490b801c481100700c2c0c0003140c7c1034803000009642c0c00b068095024030140e512107040070441c150b050910103d182030003209a1416690780e9030499480d541d4400120384038001005001c0b8030395190040c0f00030f44940724520f040b004074200d00381d15490b480d03010400009803800c241c071a80311183c2502c500006080602800c100380324542c42c3c0b00015031001c0c0024580000103880d00781d076170468006a9001c5a84860000080d103a041c0710089803842d01050183c1c0000c4545407080c5556040c500300c80c02d5103b20620890107103d01e07040900b56400c16000310307002100850a071100809020707041d080c0c1d2003200c448851002c9108005000c0c55008441510800348050502c2d820504d0302c3d625a89140d0007a044040080c032040721510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853244910 1250 853243660 853243667
    0x5040501020105161b170a0324031128060807021006030203030711060f0403060917071101140c1605040c02030705060105060714060f07110a02010c080702010309050709060501 77
    0x181c200b004104c040c1c01d40320440500505540320f4101d0b403120400c25440210900844d050b0400700e014000d0491a0381c4c24112802600400c17a0214810310380304144460828141301c4811442120b030011003110310541950200600b460f00c036040300310761680780c00b46142e1502d520203440c4003919540e240c007200790070300a001074644042c2c891074000351400c060041c801a240482510000c5a102e207844400c024141d0003d50b55002d648000e51701441d000c40d001003401355a4021840d054001d08031411032500d01310443c0c0c9948290349015000c0220407080c01400c1d4421074201c10515903070100ca0b030070030310300c0c400241c01c0c0510360501c61030000310b0120034071492819201e800c8080d41d00b070000794a0511f0641d1b034192580814402d4a00c541400703e0024207210011950003a480043e1003510b00600e03054150003802c0c170081e1840400981d8203071a200750040000350a130301c029016199080705070500d5075080f441ea800340000b24100b503151001880001c1c1c1c00c000e1600030700110600890003a04040004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853246160 1250 853244910 853244921
    0xc0306011a1914210a05280f0903030b09060901060c20041103152b0f0b090601081023090f120d0f0501032102071203050405010201 58
    0x80c030124035200e10a2208000a0844103201d41c0d002c2c80e034562440040381510190080c0010b000d1401d0001810b40003410321040e805809610304003d19419100e00050404903403007102c40610010507a00c035101c424103254400710b07055040c5403010030112050425070054402080702200401c2c0c60316800c1901d03140c4120010342c80300041d502c082c1e0b90f40c9807201c001c0c480709840d140a0056921441e0065112121803030515410b500a841440210980503035a8403a40c0b00b1102114034442d000040b041920703014000307014004c208400034480c152200a45104d1b024603017400c560390740008440c0070001d01140301180c415105040903050300c2d850080c00c00e0814000003045a1007902c1c0c8a0441580c0a181101c04d68010800400400070303682c0c140091300d42810b1891901143c855514070858805c0030500a0088105500c030034440c0c10030791407840094030300c00c1c0001000541c0c2c00c03c0305c1014901400c4180c035a00154411079241a070b036500c030368010340003086042d8000303100050148074a50302401503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853247410 1250 853246160 853246169
    0x11180301052517042109050303091201020409090f0c1a030a0b060903010911012007031b0b0c03041a211b0c0705120708100209150a020c030601 63
    0x80c00546840780054845154080c200c0c2001c00d0900720310740c0c140f0320a8200b8444480e8441e803843c82400c1c681407080f00c86601c00c4903002c101c5c0c0c4c0306030b1240d002d0707100e54042411100003600840c2440131600c01c0003645c10b106030130382c0c240c0d40d820300000841d0201409110316440c09003d030160510f606007030070220202c2c241c100205240807048000d15906803001200c2e403012811300b00203803041084000034514400c03010300076410744c01c08442c0300034042466040800324100340c070b800309031401e458040307010300001d004107480d0b50300701c001c003080450310420b50740309040c0110800c1802c542c0c480c0c1048945401008100800d648041414400d0504122505810590403100d00d41003050b8042040340c031400c400c52101a01c0318a0021405090200c0c170140d401030000ba000341e4490112005455448141d445620721918a1401d154007012022902009407082c80c1c0c080c0205101c9205010040c0d44030414654000703046025209480d0302110140400003141da000d404210451010546081010b070071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853248660 1250 853247410 853247413
    0x1002010b060d1d0721020121050106110703030c14070b0712081005090a0c030e150610030504051002090109050d0302010b190b1c020d050414061b090d0510111803 71
    0x91000c12469085d1803180f003030900c24101d80c01802c2c030048583e011940300c03480060815900b901004c030425000b40b81a110165100014078545e109200e40d688140e100c0900850f1403020030002240d22603510110805e80d18041b20b4140b40d8840c404a040ea0194400303442d544c03a010129101d4a0b8043e0405401480c07840c46c26840300d00f0702002502c1a0b801407c00c0f210fa40e507a0300004d040e035009800014002000d03d094a40403240040d103019140c40840b029403203809224210340250780a440750074062500a0003d1980d6490a41034500940c48084205d042c810341202c0002d950340c809185010b2039100750b0000c2408800305042c044608180e2040154030380000e5400c2c0903105141045d54210790722a62100007024040710044000c1c440c4584100c120782c10300040200307100044140c42c05665014041741c506503102100e03082c2c0110003244820200340c0c2000710320180d241c0035200072401400740060700d03024414803109400b16240ba5141d00400b0101007445811128400ca50140c2d06209a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853249910 1250 853248660 853248673
    0xb0a0801140d02060405040c09030b090a02030609010c09210b01060f0e1e010302070c03061503120206070f08180607020d02010b0f090a050c07170310080a0b04021002010b060d1d 78
    0x42c0018945d000310b0103441d0141e5912520351100c1c85c0b15014620003150818040d400c0303820100d40d802d403034944444090f03000784600d10104801840501c00e030795403c4490f07038442c413846003040c8010481d0000c40c0c00d0925104908200080400c100380b24603802040706403143d4150b4a11094094800f21510004901c5a40b2a68540800500b00444c96410200902c0c006a907101a4035181c2c1c01c00700303183c10281409141040000c0b20001105210050301d00030401d481d074241c0d01041c104d03503544d02182c1c04c1000600c4099030f0f2004501a45181da00848a11030041c0c1e28031061202c3c2d440d01300105c40c00001030348000741c5001440e03028440c8007a149025200b03400c0080680b80402c0a401026029a0a02c1c1da140300151080a4110540e18881c0d404a4003080d40900c06501c0c0130316420595404043d03901030480098840350005100203640d070300c103008810a41d43d41e003c10510401034580c01044d952501d2011009030349203402003920801107840001c3d420380c07408200c21100b80c851601d560550081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853251160 1250 853249910 853249913
    0x90c080708011e0b091323010506030903120606360604031109040309080d02331f1703030115080f22081c2a08040501060b0a0801140d 59
    0x890250064400e4420200e90ba000000e0120301d46c2c0e00e260010100c0b040c50300300b40c400c81e241441e034040141140c81c090380c550350340c907101084001d200580307000130240d10400600c2c041c42d480c3d890059102c007006001a0800320004151041600513580b80000c030364442204220000102500c000c0d9450141e5071242400e08556440110951000031140b2503521440010201403040c0a82070290042800b600e0494810303203400396482e028502412003081c9000e00340c80450030741074102d0011031890207030b801c42c0e9141c03084030001c0190310b682810400150f41f01e0205030345940710342c079403540c04401c03000f55529031600001c0a01c207040c2010702e50030030042100740403d03d01c5201d502500f00e140c6040c090340fa8a12075440c54000c4002c00e1000307240490105509409078180a840400440111001d00465044104510000040410520f082d00d103102401c1c00007441140c107603a00038442c0c40009030603600e07500901c103541c20a62258002540c010014402d400342ca040764040140d0948080b42014800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853252410 1250 853251160 853251209
    0x30c1c1505070507060504051903180b0a0c030c031e0c02032b120213060e040c03060501120b03031c09051b09181903050c010606080408070807020109090c08070801 72
    0x11188090700c217945503404101032010070b0004d80842e545034080e0059481d070900e000741c030341c0444032450703e0f00002c142000582080000e04555a900301a035405030700d00c60035941681ca2050301c3c91300b42c08200654000001413040d20310310903802c1c046501d40714024000741c4105450008140b21940c6215559006c406c1004034056150300d0b2060b0a040c880110000c5501308030007070051a03452002c101460400242072600518581c9031075506590510140f61514015410380300d0230300c1454001412185220348075030306903101c40c19500e402000c0e80e14021280302000c0b009408125071a00c0c41e03950b088081c003013003410001200c8144000760311220301e510440c00191400c200420414030001041105000c80200303221101103028142052520701d42d050400600a0300654040c4d40c1a40c42d2103404a1f000d4010f036030302480349512402d074030f183c0100e95444a0f01c5810a6404a040c4029400003081140043c0601401d0041c56900c030b01c1c0c0c510380b001000700744000c181d00c04540309513140c501c010980314 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853253660 1250 853252410 853252417
    0x10302011b080307031424090c0d1e060806010f0603020918040302070603061703041802040b1210090504020d0b0601020f0706180e0603070e0402030c1c15050705 71
    0x409081c9800e0010000056810701d50000d440100311100000801003081d0301030303110000300c00e0628800f6078956035800921120307808060684044d190319403885040d5140c000315003940f241100c01c2103400d00d540d440380801070303070344903022141c0445450008101040d80ca1240760010b19150008100c203500d42210142a44854010b601c2056000102d0241d603443da000d11071050306005421201c54034050400a46520f564004e40002074181400002e80c0100d2004400f4114043d8001c1d40c94a403030020300092002c4811180980d6035000c6c400020454a114040c1402003908100e03c1400d02c0c0c041c114041e500650382010b05098500010300003d625000d00d44020694004ac1210b1541c45410060f45403042000300d9091b28030842d640031a61030350040045108041a01500110984910b0f103984142c404407501038041d4044e10081106068103829650010f0001d000d80342c40352040c0c0040b40c400c13580240031031220124401a03e003080001850481300700d40b0480c0c200200c0c14400e00040c440d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853254910 1250 853253660 853253663
    0xb04030309020607080307020c012c0d0516080616080112110f03030316030b09070f0c06110f070311010606050f1305190f1403030406120b0315011e0e0103 68
    0x150350303407100011074950004450400f50001c0d80d140d128604518000d545034401070322140028203001298500c074006090380101d038500c09450101032041402400b0340c124901100780c5443c030844009100700001483e40c080500207840103400c0502d8030b504410b400d2004518040100031981c001000403001e0948031243c265881213034500701c181e8001c0000d14420824894a40c0360000209001714189545400c0d0031111094405100c40f850b0003003080304800c0110341c0a0003080034090404802440b03101c03a076503020f1099a0000d00010341c4507404203241c20424041480c103100103005010b0540005508540800803002400014141000241180104a0306584102d004100b141c1e0b035034291a40d403800b074100030b01200c0c1c84080c0d403400701c00c00103a00d1042c41000300c0020008505001000d00058010001070011803500d490050200d0700706d1070310f58120820903640d89a03503680e5902442401c0721407200034400815541031500030440f1000c074440c0818010f24104003009006849540e45044a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853256160 1250 853254910 853254917
    0x6140d060801060f3503120f100801110304020d0f0f030f08011e051c050105100e070c080307300f0c020c0f040c0504181401150c0605100506040602030409180b0403 72
    0x105d0505250b03d54052038140040a00ca508104400c900122140c01e214031004c4100740c16907561900b4050072074040c517000410030501000001e0160809551284510380b186803012041c0c081e0b030b02d0300070010320071703800440000d600c80d052000002e60004056001d0f041607a1645103124031852110915209881054000e00c0500c459402181100050145240d0031000034081864040c4150b841041c590140032035445080003c203110038403402c504555035600150300c5245485401e815190b80000e60f103c03244403c00e0304141070056944180920054544d07100214040386c19611a0040d150360a104508544c0111414100d5589001e00039007150800d880c0001e01440c0240d040f0b44912840c0c201c82040b0351000c01e820728000ca941d20400c2c60106540d125403459807207451484220340020300790f0001405002d0001c003c200c180d445a0b400100d0284c0e01e0341c2031550f507030208106800590118001d6040400c0810a08851340207022000d6525500007443c0e500c02e58034504c0c0200d01070030103800c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853257410 1250 853256160 853256249
    0x60317121302030708070b030412050a09090509100c0201050f0601030506220e070f0303030507030203060a23130b0a0e04120809070308070602181906140d060801060f 73
    0x9540f030a010107005801150700342e61580d601c8441001c81070b4000c4e1001c5a603c0c40040140040758401c82c04d6940c0c90317001c0e41e0b072000700300e2420501030050140901048003a00510a0058501c1c0c0144611140240755800104552410400310402d6500c02007107241414103210400c807195603903503400c01f8000880c543d05000c000300071000e5002001300e00c0c01c00007503104504010540c54040b0f143e0000326071080e6070503c0a50754640c42101030313000960300150003031020345007448140c803c1c898120210300a84503402c1004050000075813040019840a101c1d295500c00c08161800c140c1c3d107200141c13038682141d01184c1090740d80c0c0000720451038039107070410034000046443d00405004410095411480703160300c0b000c15050080c020340c80381703080e00c000d950009594030081c240401c0740c441650500d800305920614181d4151001c0032801007001e800b4008000d818030300ca6072441858007a105410001985c107003070042c81801e04070107401800c1d82a503084d403681c09c1e0f544090100800903010500c01d028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853258660 1250 853257410 853257413
    0x90105130902120f1b0d03031109090a061d01050319021f0305071205251b05030714160510110a0302100506010f050d050714030a0603171213 62
    0x30182240c00035800303c0d2200c030140402c40005420030301081181c080c0c9024503c50b58480d003580c03079580b001c141c120011101e800b001ca0301983c0010b02144020500c9407a0002c0080000c500010071152a030000f541c0b07141c240f02c400d50180c400340c144146a00303000074a50400f00004c2d5101c2c4018850801c0c6034800003c0e40c04c41d140c9240b01030f614140e10115203000d00d000e401c081c1c01350400700c0b81e140c0000c90000222210021364011a03000e00c8101282400c802500c40302005078400d1a55a2002d00007280c18002c0c0c0882c1041c41d8041c20781c02071f8091a2500e0f040c1c500419905090f10032031145601504c0b003110400403030031808040390811103031841610503076802920100c42e003180c00c41581c01600a85400c0c903030040f03000c0400c8034030b0f075200708007503a079200c01034400384541c11100000074820300400c83e52410f40d502c20350308600d05007010103100d42e100f04084040d40c0101d620400e51340c0c64000c200104010903040301ca4202d0201070060401104940b41d400049000740100c4141c1c040c5001b810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853259910 1250 853258660 853258699
    0x20d06021204050102030a1811120f07080304030c15051b100c0e10140d02090f101d06090f090406090b0a0e1908032a040f1d06090105 59
    0x505650703440400358141d10302400d0090007504110342211805003041000c01c01e00c00e0710700706640100d900040095915410030244903915a99813404050b61040b949410010ba44c2000401e0051617150000c646c0c3d1380c210300d072540d106041a4401c11811500300510003040d50440d0036950b404420980500a030780415080c03601d4815100700c0c01d2001303454844926001c540c40b81010700204425140016007603201c40040b501c081041086034404041030002d44441000d540040120107030050180388404140000184440c5203811503d0100340714030411030042c880c24bc1c111120f0201112a282001d00c2c00c0e0110b0b00c69500100040e20074141040002d04100d10340d031001000719000000407080e4030f0020480402820325400c06801e038880c40010110400507580e1040b6040e6000807a941181c0f100c49a0780c1d824154070030004216840001e1a021040111018100900308001a80d03441480c0080c501003012008004400b0800c0c03800810210b030715101072090440c0d8094401291a01c040d41c030b0b26 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853261160 1250 853259910 853259917
    0x1050c0a020904200901060f0e0d0c06080405060a060f14031905030309010608031309050415050411010905100c0b060d021207030605060d0f1112030a09030c08030c0a020d0602 77
    0x3507204041d00103010500c90301c000c2000844210f038a403445240ca056007041700400d000d1040c2d600080100c0d150303154151060204640c0319101500034241140b00d5a0780e07240302e80303081d000200016180e408002c140007040007e02d4100040031800c00805040140c118070011440c05003124880c0d0740034128171542c50420101c07030070418010f15104070035140e140098499000382c0d0100001d46c00c10f84042150380001c000c641c0418161100350300300525140a03000a44401007054414101c0040d500c0c00c804241d0045500c21407103909500300450340c900014001c501c403500454042c1507200520805181c010152040064112034110069030702c28000810303c00720200007e41256040c0c1080300e6054000500e281601d1040c1024000e5076501018840b00d101e03907400182146808140074004520700030aa4440703a40080c1c2001c140f00c0811540b00c1c950391026104100082640d0010410f011514a02c4406088078002540c58187c81000250f610b43d05120060b20410184080d00e082080b5641203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853262410 1250 853261160 853261163
    0x140408010c031406031b1203160309030627031107080d0e040c1b200406080a1506061202030c160f110f091609091503030306170c01050c0a 61
    0xc0c80010141c0200801030900819519000b0108801054003894080340911281680410540c40c95424504000300b00361808a0910781e07010411122090b09070041a00079800e01036261801450328502c3e040d41114035290640140e50545104021114440d00c0f07680703100360709850002d000039070380590b03942401d82940c40102c4a104e07454075880e01d16001200b404920508076020080b411142c402610200c1e018207402010485100c084800200401106a09280d031011090a07500140b0702090403a400380e0004609503014085080800c0448920210794010f0310178140290392030000081c5c0182c04c0002010111a00480014880d456a00a990a0544121403c444007540e41011172408010703110550342c01da00d030000d800050804540b40c2403440c0000c0c0061201d90345280304608a102060100020002d4880703001030207a220340039018460294510000c540352552602030b00720b6125600104844215402d481c0042402280080c030001c801c0c24010350b07441c0c1c021009802d0104140c4d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853263660 1250 853262410 853262413
    0x402031503100e0f0106063006090902030c031f091a160216061b060207060c11010b0a12020f180106031b0e0901090f060302090a0f06050a0b0a140408 66
    0xb5402840e1180342c12030000d440a5409a402030640881c070365090750242e004280c0401c045140d0610545240c002001200100194800281d80425016019980142d00810303281c0d464111030015840c0c1070014020a0104400400c00b541000300c030390441c1c0005441c120086590382102c94144508200340304400400d0300c0d4082054900b03c8080900c4034250298074005100b904001021716003802000c0068800c01e440b82c02a68007541c030f5480640c09005c40443e2400d40902040d400104240620140f200141d1071368911100d440102600311080280c85a21440161000304019800f5400c01c910154040c1c80d5121410b40f805d0100310300b041c8032040c00b2010401c40000081035136040d07101612414030040b420007640f2403400211940729007110f950780d1102e50003004000e8048075034800200c00c1c0801c500800c450360349400040c2c3c4502c0441d050322459444086081030311802c1d11036180a80b0003110040d00507801c05002e0f0429000780d0a1503010300a40f228088000048107055800400c1d2100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853264910 1250 853263660 853263673
    0xe011202130915030503190f020703050a0b0a020f0706051501090e061003020906030a0e1203040b15030c1009030212010203131202010f05041101030501080f0307031803320a110402031503 82
    0x48984005c0c0020124030713000030300d510b488c0c000c50070301c08140f0400b12030b000001000e4a607441e443e402c3c0d03100c0c0090001a8042d908101d004844064407000d40581c9000d00c1c0b0001d410716000b207414807103c800c001050f0402150300310900c1006038914015410041c01e03101104000000c0740150000d2045600d07040c0d02c01004400c00042101c1608444042c0700d550040e40ca583c2001c001441040c00280d4005181640c40b0000850300940d0701c8440501940050841c1c4065200801243c1c0640b480fa10b15030009001080500c10750401d0f4009050f0045030000841c61468103000d580c104c01c40c0c8030002030800c0b2240c2410034400d80701b5000110f041042c03580411050400d80f5100e00c0e00d000c03504030140072a007000b00000f000480490038a10922054001d1454038074a5038040300c06900c0040c0c10b43e209610110080301254140c00b049009401089910304040d41c980c0c04559025065946200305034026110380c0009611203010403600082030320056103903210500b0040c1d02580241c141509481202d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853266160 1250 853264910 853264927
    0x302040e0601150f051801090f0b040f080d02070506130504020301060c06050601080403020706050a0c150204081b100c02041d0c0f01110c060714010203070e011202130915030503 78
    0xca00700e0304850010103c040001d1030354000b80ca1484404400b0004a5030601c141042416242200c0780d1710501450250112a19280950b807521182d070040e0f4002440410103125000c801640c5038090903501006105980c80305600030756950040c02060300a0038003241c080194032181d12007001600e070040c000e648070340c0c403034400501e0285418410358051342003a001c500c881d40211181c074045c45d010f40c060a040c80c1007134829200bd900c00340003001000058140000401d55000068000390004280903941d2864043e4040c58198a18140c0c00340d511006441402541c0e0301d0080c3e803142c042e609045a50500500020b401440020826045485540b0917441e03c00400b040c440b40e0f8090450780c01200000070001100d0b1400000c1849044c2e5100c249444018036040016000041c40340c86420000300342001344ca400c1e42c00590710400894402c40c066030040d80c01c82040900300d0840340d000c42c03c141502d0718a0000300c0303140c8118402280d42d0300070600220208184640516040003c032a9a600703403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853267410 1250 853266160 853266163
    0x3030a050c0a050a0b06041a131d01050f0f01050604061d0406051e011d090402040513020d0f0308010b0306010509041d0a0b09060a02030f2e06030212101d100302040e 73
    0x1b2500350b0b1041d858001c40d00c04901e0544c2c015114280301810080c8002c58000c0b0800083c6141d2090034610a0049150702d0000000d0003064412094000f00706800c1c01e041c4c5100e0320306681a040248901001d000600100f603201031460b079a48001070281e59150540700210b80200078a400c4242c020004451003048603480f40302400f403040081e66014001c1d040100c16850004100c110b2580c01030065011a01610701600641c0e00308040e40047c50710000b803540040d24090080104991900c80c0302c400105160300000c1d0706004109050803075203185024000204148111070201c0d1166039928942141600c4d8910240c10311458101180ca0041590078810300d03e0004543c924610312615002464445043c020b880c0101d0b02a582c4a07010344030380345000759890400603000c8107002000b4281559625680004000702510303100141d0711b00c2c01040c0c46891000080c03102c100c5140c10001080321080310365401d001841c14110200380b58a855240c040f03041c404d03a1010f5480360038240120fa51040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853268660 1250 853267410 853267433
    0x91131180f050c010906030b03070612060b030f0f0f010614030405101a040e010e031c0e0102031e0a090b1f170f0d170f07030e060a020c01060605040503030a050c0a050a 74
    0x3000d880d80901203a0306c0100710103032000124115015044402c0401001e030207941c00f071900380f030b1050b400315580d521020108000e40007100c079084c1c1080301100b44210101705100d195004010400c01a210b1760408401801d07040100303640042c604000800902400400d0000d2028442c01100c10b0068010901c11071000200c0710503100d11842c5004154005140f0510070f0450342c00c0036001840c10202462000c04482000e0780300d1403801d94482850008035082032005500c2503001880c48500c00103c0070075503200740340c014104080a480e20340010302150703409090a40c0481d44a4072180c0842d48100b0a2002805c1944404840c01514101044c064000b041411021201c43d0448400034170b5848103e03540c040c664100100641450045102c0340031004d00380d43d100a01c1c0c02d0110380d03010803480044c0340513811070702076406641c08200c1003468542805110300901140c40c0c04e500301402c1070002510f906c200d644a0040c400009a03031148540c040c041015101d4005080c0c0d44441040d0509080e100d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853269910 1250 853268660 853268683
    0x30b1f03110f0a181814060103060f090215031003170a08090d05030406020901031116110a060e0f150309060f10032013091131180f05 59
    0x205103040c80c01160501d40f01003400c0755086101c401e0b403403424481200040c040e101c41000310000d035404075400b08001c0c1500507148910b032802010709614508000b403c0701e5030700640280c2d07581000788020160313881441007002442110340007903403505c03910140070888038551310080c554104504d009000c01c42d400040c005540d926120540b0390340d1100d00300c45d214001034000300e010070011310204001c511aa070113001e401e54181000280100400d017240502c0d00080091030f244520890032404108907081e03501342c0701c01c0a85004451310b003824406010f01040c96031450003021400100c14071a44c5611048404800e0545001e40d40c1c00d100c00709035180d039022246218644c85d00004503402c0c1d04502105411070703800c19012140f0398451b80103074200d400722581d0f0503032044005d96648050032191040013032007172144045500340c50104080c0320600c1c4500b0440e005d41200700c8081c0e402c00c042c51602d08003449250000059444000e000b26114412115000c0e07c010020480001003040c0010300002c01ca = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853271160 1250 853269910 853269919
    0x306031a06190821210a09080c012f040e090a17030709050d0f020907090503030c0a02090903040f03020607050327010e0916032a0305011503020f04030b1f0311 70
    0x18040b076010030113601c51300e041c0c00754a200c2100300d07903c0c59003090f10058012006450100c2c0c0e0b01a01d80754103080f0303002800006041c3e591900081415010021109104076620710040c401122580c41401d442c081c40c45010b00c0c00700380c0750000b0601c5006000000c815a4000b0081c980b0740385043c0030241035001201c011011a4820101240b00c1c9050014041055800400c5040b1701103254240300036010050031060a00101480100f01a501800035085034641e020062400203114010030061010190007100300d41c100300400d0003e42004c11502060b01d40555001c0e41d01c5880d803422515500c0342003884000011228030310001801c9006202c0f042c3c85003681d41c241032900203420021000c400350f0b440d01e0440240000c00e4803d50182d0031a003095100c100500204400ca80d038500300f41c222030041280060398a03401030200404040701d500c03020025190440c10312010901401c4207114500010300160303d600c001480d000000b60310824850012408418001d982c0e14140d0b8510591030b400c00d04c034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853272410 1250 853271160 853271203
    0x50a080a02040807030f02010e10110111390105070e0f010f08160c32030f070305070f061d010507031103061219080a020c010306031a061908 62
    0x80810324001d4400381c0d2507150103081c4103813440d44c900d01c90320440c910490510090000111081d6103200038040450b807542c940c002c01d5124a0f00c1c950845403e1482201c140c43c040c40741102044103403224290448494407032401e41950011100442c0c24500d13142d6a25600f0a020404199400340715110035601c241d990035002000d20b401035403140055201c000004607243c3c0002c0e11461a4202e0f10242e0103d4140201e10030400d40303e58200c08030a03c1000ba113010121a00d854494070000d00203203640101c1e0156003000302800991006210303000c0090704000c00400c2c45424003a00348a8004000d50207003040101d06d400d0384070000142d044001d0f640c51546000c0024440a0082c06641100c249040140b49555611020848144404102c0461130303c43c1b0800250314000080989403240d0040b80a10707200c03002200300a2a101c2d200c40d1060416090440c00c100041184c4ac4a074003007144154801025074035503020603c144210f600600c070b51f03508200c0006204002048054014100b10b101300b48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853273660 1250 853272410 853272421
    0x1308071a0a0203031f120602030405060f090316240f0c0e0f1c0609030203030f1005060f1b071d0a1a06030a02091e100f0f0e0109050a0303050a08 64
    0x505000c0c6112020142e0801c10004880d9041090300344680101502c11030706170358840d1085815041070010072507000341e00206010500008000c1240d10440b029486484c51510f211415101d00681d20110200c0c0710a400390760802c2664101607080d00580001503186034520104070000d044103c0c0840c03a92490600003001c01b503c1107001c0030701400b000d03120700110100001400070954528008207240c1040700881000500d00c0c1c052111180e000ba4011500c03410007410303004110300042c1001e03800000200080041d61110006d03505048441ca01d1140c45141031100310440c004000c901460a0041e42001300c0d285001d01d2440702110005400e10129a542e4005101281d040400c0e080010145500103003030b502c1c00000859200c01d0841e405400c1c075800a010a2240c241c41e02d80301d880031b2005400c81054140320076484074001c4070340340c0036030242d5034841d0103440b00c2400c503070540400091007000d001c140d0041e00000001d05c0c01502580280d59a4107004000303410a480d013800080121000c502d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853274910 1250 853273660 853273709
    0xa030c0201080f060f1011190210030501051305091903030606020c1504050402090604030c0e04060b030606010c17090d0602040603060501050712050912060712240515130807 76
    0x91113100f02415203104d841c1071204201c0641003018102c000c010301200554034842041c00b80c02e011404d4040c0d02c0311130030002d10402c5001400028141d0405143c40010840c40d682c41d815048015010768001a8513164040c001e81064507003200c001c1d03c08044101d00040542c16803140080f5000d960075038100b1901101003284100312507110030000c802c188070600052909600810800704010445803402e0350307982c1c4e50500c085072548200c0e0604d41410400c0305004217801800d80400c022406024107291a20001c1e20510000704c0c042d0041b00c1c80b04407482680d0601e011900900300c010281d040c0752043e868244040d5000307000d5032000078203102d80007c255016109407581c05602003607030750701200c00742e40031681c0780c0281142d5035000b143d004055400740010300205000d2008d80da5620410f02d060441d500554100310a0510700b43d503040f040c0c00b01c800c4141a03107020740340b04a600d00c1d003090242c4800742c0c0c14051040c4040d41c040d034003000022000d034000b50700340c12202d2880402552100c1d450510707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853276160 1250 853274910 853274941
    0xf0816020d1a18071e150509010306090b060d050a1e02071e02010203030705030c160b1f0b0d0207080d05010e0414030414130e0d0314060303030403020316060e0a030c020108 76
    0x5055000890a01170f12100300d9080b41a04003580f9402c03525a52050209814190403602030003080001030058610750745402008003808180302c00788030001c00e010108081c0d120b0b040f00e0340400390341ca4020402151494003d00b00c4910780e075078000380001d44055118000d44c81080c0440340b90003101072a01d00307030300144003800d2040d070140c002c0c6040d6071721170606036420780c001400d41c1c0701c60700100b1404070111300041c44084280d01401128100b45009400514050100c0500315040c2c0416402044224440760031601258a002c2025807030f030000307285c4503080d4000c82c099800308074100343c00030800d114250728143c8903a0003400c43c0280d600390120074a44a21807030081e05107150000364110900c1c10052803500b0394510881c0d0000e000348000c4415818400064400000a520f40e05a90005a4035110290700300900300c01951450038560380c081d69034440c0c488800303103140d8a82c1065080c1b03d49a800144418103203010b44040b40d0940c41c0042100c450410201d000c580303180e01250020714042c102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853277410 1250 853276160 853276201
    0x50c150606070803071107090603260f09030a02131b030b0f1203071407050102010b0301020c060412050f0406171f062124120f0816020d1a 61
    0x107542c5841181d444142007948020140c6081c00110300c000c6541c05030401031000203110403000050540e0451400b040758040c071040c154040707d00380b0807141000160104654500818100d42580c640d00500400c0c140303d0985000f07540483d4120f4402c1742822030380c20100400c40003030100c03a00240d0700a010f41c00c88081c084520303007200c0700301800c030340905100d007052030f00103040e40450303040542590f0b480b80710700154000d507201900602c00c00c008070758090050168800c1c2c02c138002c2d400c1c000d0aa505580e20350300107101608014039208142291401482150041440040708a40c0c0c0c07038607200041e004140d00740003596001f8054000541107050140620034403030410551180041ca004421142c071840d1490b441340141c3c1d201011a00003140384100d4481c80201c40818031180302074a02d241c1c646034150b200c82e80b0500a403500c9400500c1680d000300c4001e034810651034854141d00104680c07032808540007508907d040ea81c0b82e0a1244011070307500800c41880900b80c40c0e0f56210145085440c0f070304072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853278660 1250 853277410 853277419
    0x2010516032016260304021e130903030b030c0603041b03080f09100e0d0308040623090706110d0f09050424050402040b0f18030706170f01120618050d050c1506 70
    0x203d0014a40b601e0030b5130180740d2521211122520340030005800044c10050809150361380c691f10b004040d0903008dd045203c0c03084010701803005001c0b0101d80184002080144403070a942c0d000d1042c04109000317040916003102415495802d910906c2101c1d9001100c41c81c41040012105084a446041158409030006c0d0040b01e0803e456503040d16001000313881100e4954403050b0b4490181150240826040303080743c910040c5003004064141001001c2e0450010401680b102142051000904040f00e403a249051030328107004520888401c503060304920340c817500b4400408030140b02070500080c041c402850280c01e1322340d20703410803040b4420b600c00c1d0038a003507040c441e040142a444010b410a90048804032801010640002e410a0701c0350700024046002045404010409600c0540c2c3c00301482006d4521541080300408038648000700080c08a42c0303c003032604c41c206900c020a05155030150455101050503800a403480c0c0217400500c04a2107241080103400d103049006a0040c00041d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853279910 1250 853278660 853278667
    0x10b0a05090904020f1207061d01021e1f1b0e150d021605010507020f0d0912060e0105071e030b0603040b1e1f060201051603201626 58
    0x900340016600028030136a0f01c2041c44020011079190414200c4092820070058201681000c10240411825400a4020140e4100003103400c1c2d03000034080f041810034a000c80014080240200c2c9094030b0040c204040c41415070846698008540004a08040160800040c0c0209842c122100804c0030034440d0302010100c02d102404d21500300604513141410800740c6041100f0b180c5444010403840708a030a42e54032810400d00c56414410080900300b484090078a440d03030510000e007a80e0440c010042c415420728000b00411080b07a000034140340c03030b040090025180040015281c0c0508085030a000410442c4030304035107202e0710030b40701e909000521460454481e078a462402d0440106691281d10f0b40c0a4401c1151030300d029046e104240703010b054a52411207040c42c03c0710002551108055a040c6802c2c032010144d0011381c0540e200041c0f500280c90600c174641d401c8100000204a1b049810001d00c510410402c83c4806e4011401804100d2030896501516050b0010f005007a10020100780f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 853281160 1250 853279910 853279927
    0x22a0c010c0308060135010f121e1e020901082a0a0f030501050a18031704020604092316080106180b0f13050306060102100f1d070e010b0a05 62
    0xc09086420100600d00000b11491000c200c6010200301100c802d500f000c46505c0c07100d4046c038507840502403c406c108400c280c9141c80d0041e8800329122000400031f40d203880b59a0140080e540e960b943c00f9030060442d400051510510394605201000142c2c003a00d1400c1c004140c00c00000380310160b071002d8454841d050030000b840030703030000c44280328164040c0141c0b0000421b17560031410400918012400001c082c2000d80c8040301b15802c3c030900403000d80300712a1503800310b07030000c2e49070310780143c078200300340c03055540f03100085042c4a10741003920380d58900a815a070219030080f6681c204a0b504800040a4848600001e2003d00c003021110000d454200107002107171060032499507103480c8982000000391100c01080075508202c40e40d44601c0c1c804034595804150801c080c02c0103183c15400380a9900300000001d454100030102e9580940c1c0b1640712103800d4071984d201c0b100c10014020004822503100780700e5903e0740c20900c903032480d240c003e80c00032545060b40c5084440786901c2e51105403605604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 853282410 1250 853281160 853281167
    0x1a01060302161707240b400c0c110d0c06050703110709020c010c0e100e120a03030c0206150a03060504034103100b1309022a0c010c03 59
    0x2895410203120301800f0301350020b02140600320325402420282080400324140c80c00c00c0b10481d5030f80501c1251074090000e10301389030b0060300400400c20612148854058a01400c0c000c00204034440b0f01032401440d06995903102090340c00715071160020300310800003401007201c0c44000c4070014004d014000400c1080600440003401d100d446401d195010001454540742400c10a03802803801d03d40011b800d5030800401c0c85001c2d80090b450138000d00040400c004224a001d20356807070f4080c03100607108000c459a403845851110a4180120b85580c540340c50024080c005816448025104010200f03a46100b544007405d030a21029000760941031540d02c4041c058880038005800b4400404802c0c42e007200c103076121481110301d840ca110442908201c42068950207080d505a02d41d00038014000e40d5000041070303904031003421040036140c80c00c1c404040c404401c80d40c004011b032480061403d480a811010003080741075a00ca09584940b04042e0950b2a607000a0300a0700141c0d4408400c1d00081c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 853283660 1250 853282410 853282433
    0x10f140409051e0f010e0106031a01081f1409100e04120903060c020c01020607020c09011a040509130512040b090907020115030507030c05040912050a1701031a0106030216 75
    0x502c3c00f80b001035407900c850031824401d0135160030038581400c0d80140403202e4010000d9004201c80e280c20820010340382c010486d8400d10088084c10400210b0202c0e1120322004588c002d048200544410100e079214184516070340c41d1000f0380d0180e14a080050010742c80024103204403540007801c0b14181d5120b03520381402e2003103940d0b43d006000b84c81d4004008035400e4450740c0b146120701d0f00200a20030790743c0006460b0003001410041158070401c1000415200c80d07000c04e0442c0e480130728010a100d1170b801c0440d001c0c020f51704156080b400c04010810b0241038410301c8001a401403090b02d468000d0b00440d40002c0c41140208044075008100b07125240c1400343e80e80350300502d00d20000032020580b07140c034004144140d005a0f025804454140b040c4103140380d0b624002d04040b901040300c49a243da80640c500d00149412042c09000315181d01c202e4041c010760880c008201450550030340c0c49103040c03968640030200c4055511008000440d21034041d108981003c99140b030b182c0300840c041c3c0e484444821 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 853284910 1250 853283660 853283671
    0x1305031905030d0c1b050f0105060306091b061b070906150c02010c0c030c0909111c03050c03120703090605090a080d020f040e070f020607020c0a0905181b010f14040905 74
    0x80c04121069003951750003502007189100310050310784031001129032030948602a100e94070a0300030700240300d40c1b41d40000c1c40105510b2000080c02c1d0006100e0001076041c021012074580380308006000c452498404144d5606848401404000b860385840213886840e103000c89903008200e61003000710156009507680c281091103411041c21a41d100e5030703010040b1034140d0000f980c2a481c3c03074010080003084440741c414020b06907101004900c4440307e01480d2201c921029040c84800102844860000e101b00c500c4c44082c030480c0c0b19070341031a140081c01400212020781e00245060041039912402160728100d6641109031a0708040c0701c510300e14001d501034004c00030030740c0e020800010000340001310144680c0300d6803a041c180400220000e410220700030b03c0e81c0b08640021406540c82c1e640e5140003011345509400c00034072683e4043c4505420180e1440108aa00c00c1e40c824450901c0004000084890b00b0781e00c0d124925640381c0152001400c1444100d2205001d21051040604503408bc80e84803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 853286160 1250 853284910 853284917
    0x5043b1c020c01120902150a090e24060c0613060c2c030c03100e15040b041101030603022806091d04020f0603091605061c0e0c061305031905030d0c 65
    0x5c2d90250b0000e1468961f0b00900880c41c880407606049280c1c00104800081c4440041c5880d0391403ca11810f180031504001490307030f010083d0420380070351503040507201121494030880e140303030601d111101c04440140b001111114240300b44101e0f441d00c81e0110500404200d00e00000100c02c0008005082841c2c943c0c0d030b5007510a00e040320306d031560304100d0300000d440a21400078158481000d40c9080803d618007803c032010501c5c00784000100700900d040d900130340001c03459000c0040880103d01802c3c2030351010b0340c031448441103d49141c17007145440001c034909600308044565240300c1a40c05008901c18400d1190b0602c480042028803e0000d0350302c2071008001c1304191100d00c0c006001a002594500c01c0d5501c40c0d82d0803a03070043c4c02252117010b018221603190515140c12084030b100490a129150000c0c0c03101c04c5101c440e1000c00110102e5800140300c980c5603000000003910304900c03440b940b40b292081c000240380c81908038180764800390700a00603510b040c6081f4813140142c0600e1000d1001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 853287410 1250 853286160 853286171
    0x803041a0c0414220f0504120306152105040b0907060f0203070201030e1e07150311091c08030c070b10050303191b08090f150405043b1c020c0112 64
    0x154540c85c0f01c1c02c0d80c560740700400081c4900303150900b821030148007004503090500c1c0000a1240f0325261402004d0100145448403011105241000d852491a0308108400e03040800b40701c10407410301e15143c4240180800c485409039142801c59110292888810258000f00320b84c2c000741d44283c01c410ba441003000c045840b41e5004074801141d000004080081d5034000e1402030203c0c42c22814112910a55468140f14900c0d5107000e001180c49031b10400381c03285911080b0400d04100b0860b0f00c403840b03071f00940c100340c492410311011840d40c1c1c48030b0b00864034003540d070300020000e10100860304d041e118050300840c01c0c40c003c4a00803080020800c010818000c3c079038446100510302040c041500c500c0340799107548400e4a4000e118003024083c212a1103113401c400c20704144003003041034404851048401290208842c3c030071191b0f0100064521042c0341c1d0406115580e1750a46c601d034103d90041000300c0d080010400c00b0700200c1c070081401040160480c00090340250b11427210400c03c0d44115000150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 853288660 1250 853287410 853287469
    0x3061c020d030f08010915050409150f0f061d070f17091612030c0627110f0603070c170c060f0a0c0306050a090510030803041a0c0414 59
    0x241d07920071680480c00200c0e1403214403036980d40983d881d401440c549800380181c0030041d103901000ca00f103000e5180a80e607248074610502614012000c02075828007001c00c64142000b0007840035104040f034281d5198100f00b40000e240200c0c2481800000d080c000504071911011000c4a4070300b01003044800f089403031900320b43c04200f0755810502811082e002000a0645074810122042d010b40c0915500440241d5501c086a00840303c0900c03c0d62064000440600101d6101c00d038401c0c6860101c00c20f044100306104206042308144031000080381d00030b601c05c072030900b0080c203444126403460010302030200301000150404030410800300207040c05c900b0705c1000303040c403071420208440d034022866014003172090318840d83c818010003591510b01031001d20f0074500402c64960b0940325145003076a40c5d000242c01e82141c0703d0707107402459012203103039640d0401c1e09028640310024600c0c002c8007820040031503c5003582d681140d007201c20310074040c00744141040402c4080705420b0140c50600c0c1642440e45d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 853289910 1250 853288660 853288669
    0x2e0207080a05070209060d0218091015050f0a0b040b1e0d050a0b030601121e0f050706030b190b030403020f031902160602120a02070f060e2403061c02 66
    0x1400c00181d075074961034043d580100800b485014003181e00a113400400e030030250303c82c3d008100380940c1c00c11040e41c1c0c94440020032864170a40101c2051468508028510a020003401c103c0c1110012074034841c01401c540b0411418044502c0b4019024404020410002c02010080c01d010b10f005107901000c1041c0c0100c2e00d481d540302921114090b541c030401c000d8005542d1103210200503058000b84240d42c105443d11509034456003000c0e0091140035070701c1d604a00c0503034809078055805503640a44c0105442d01c0e590b0f61109020345c2010a003045600001d900b0005919000c1d1074009201d2859a132420344034a05951010700150114010340c1e10740e1009600410003050a108940d102e2207000181d400e0080c208420040300003040b88441b82c0400020740c1c0014030b5500d031042814015543c100f03d144c242e16110740c0b0b41c0b000e00da5070116200041c825030400007104196030155140c0c900215036001d8415100382c0d00d0702d500308810342800854400d0404d090807200c3c18802c03081109029207640c0000c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 853291160 1250 853289910 853289917
    0x807060513050609010b01081906080307030f0f080903191b15062403050907080f030307030501080312220203070b1902072102042901112e020708 64
    0x10080010000c040c0002c000301049001d50281483c8000c0001442841c002031006001078030101c1e41c11120389215a0226030340e40201c0c01020180c00706d03036642c0701d10f1801503c640240055207000c00e416403005090240101c07500c0d44581c81c2c1e04050f5240000203600c0c540300c0102c40c41500104046035002070046156081c1e80d8000900403d01040c511241001890aa41d9940c00c03a88160a0052041d280c1c1c100344035401213400000d04000c00c4541e180c1110318500f51083d44849440e1162801581080368040000d50042940769414030007607803526040c1d503a034407408030818203580840b80007856284030701002000b10903001403485428807003900003070310300000341e000121246c00026501200e010304c1481b040700700760940080d049281c901100145030074000c804000c142c03803014924204656032640b0049844000c00100c410280240060b8850464003000031400f040c14803c1c000c2c4036400000c3c11000b40c03524404280d802441150103040b5540c038411700044400c0e0284012400501a200078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 853292410 1250 853291160 853291171
    0x9020d0e0313080c030a230c15040602211b0102091201060e06190b09010c0605070f021203190b0f0301020712030b0415050f01090e0c21010506031308070605 69
    0x35142d2a08106040c3c0c10807000e44072152003170b84552040c000003981016513003000030204209a03a5440c4800d00103040144801500e640454402d4145003810354140c0a00180d502c90b07030840e100310b000d0300c0e400d42a5600a98030a420b001702842400105000100b1a00f1514a23810001d410b00c0b8100f4081905100044411007181e515980203009400c0c0c18034680354090001ca42c1100b68803c00034030111010348a019807500e03070500262003886030f40a82100038100c1c1d402801000945030090005125071f0314201008018080c44010101e07002800e0180e9005140c1d1906140d4050622a2840e00402c02c00c001c0c1034200c503120701000c41540d400e2014003c8030b4000c090803032600055a800070101c61002c0000e5208a180c00d16018a9105a07605401a03030002d032a0030b500030b40500300580b51388481e5800100d6129850082000d00b61065015044071510010481d005200301c4441c004501400d01070150066000d100184450444540c1040c4060007450028034141c50b03616950290b4008558 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 853293660 1250 853292410 853292437
    0xd0203060a0f0906140402190804050a1b0e0f06031c020a05010e010501050a090c0507112101061d0108060f18061302100810090f060b0c0c01030b030d0909020d0e03 72
    0x1c0066551482174204014401c6404615110402c1d1190510f4006540440100843c440009003004010040c0003821030b040a90510b1824446c1004080c00005004200b080f0303c0100124085151961f4024010f103001170160000690118540c4000b04502144000310b100300140100420820300ca80f11010784e0310000420998100024410300c60305580c450120030380781c1800c00c04d050742d00c4025511415481401c040c060f40b50300000076008440c052144080f4076072036904800d038100c1544028126809a005803806c011000301040c2e85030340900c154100d82d0003840005030703109510f00d6500e5000c1d425041c007951200703607a0403462a0610441e000c20000b8402c00c1003005520b0a0104001001442c1c5405509440d00001d503401c80f504610031082c0c010f4450703205c0386103180c450308040050720b03140350b43c44e07111924141e80760398030140041d0181c0801d10303141d401122402d01050241d000d00840e10b4032209145400301c410001d6106444041c50556a031541c0d0919890a200500c0042c41d2002c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 853294910 1250 853293660 853293671
    0x201090b22060f1d03070317060f1810050a030f1518060902010801051219030201020f160b0604060e0f0a1803080910061406090a0f031a0f07050d0203060a0f09 70
    0x140013840300c004980303081003290301c180100e80010b548100300d040540c0100440400c103481d001c0c042020380448a036603d0303101d13140340d40e82242041c0c1042c0c074510031b4156607042d10032203a86401b07018444042e80800303040310300c411001c100411007900b82c1030688404403a0014110a90000400484007aa00d04960031030719182c241095690140d29030b805000c3c03c944998690101c20001c568030380c0090300100040c1c4a10114105143c001c0d41510007500c0014501c41e41e408007243c52416058601000325035000f901400f2590301d0030720303125000681c0c501c04e424904549038108003850648004000303000c039548038607040780d070019034134a0240102d100c0c1e1510820350810780120750600704043e031036828041c50b100c020000010f02c03401150481d08107a4200e40c1d650308600100d00b8401190f04a406904202000001040001c94422007a80e1880302c40d807069031183c4450113072125095400d9030009100b44522404e091090f402180c2040e030040c10a42d02030b076625507201c043d854075401003403015a140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 853296160 1250 853294910 853294931
    0x70c0e1008061b0406030903170907050a0902193e0d0e03121e040b0301032009010614070b0708060a090510060f02030d09051605010201090b22060f 65
    0x1c1209582040e50078410b02091552420003e09900a5208880426441d03444650034180140c400880f81c1c0d20f0701411000c2481c10a015980e41c0c6100c0c82150300a0091203000200c0400500c25100846504080181000e94a510031100c0c2c003500422000003080540a5071a50359000560174481c1e4075a2403d00302d09000032100e0b0323003001048008901880510807401c00169400718075401c10854021480f91903441d0090f000c00e2a44040307581081b910800603000c104c40e01c0c0140514103d9100c0e1010a003221510020003520100e40310900f0b81188450700144a4907010382c0c4665152500c07542002d0500708144c4900156040c1070341c1c2034021420b41d000307108490030a41a4040580702404052119003070a01c00c20b01c00305c8031b0b4418001080300d8020034218603032003801200c0500051440a0180801c542003e5440e03500080e500a10142404d1b40026154010701415031001e0f08048800165600d02400481d06c5604282000d40300050b002108000b480c20320441d06910041c0c1c4d00000c0b032030b901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 853297410 1250 853296160 853296163
    0x20412030801061803060c0c050a0c0f0b1201062001020a0906080c0418020306060403380105010206151302041706060105031303030e010b1809010f0e0304060302070c0e1008 76
    0x180c102d04100110150b82813411015900e0b100d013103030b40c80a030005600100b808121500c49074800010804d008030110710b003d00c03e010840c82700340e41e5550a017010550341c4110300c0409106615045252150810040200a029202e90011a000100714403000d0702d007102c0c1a42203901889038100416400302c07041c0060341e40710300d02c030f54003001d00c55030381e4501418000d0000d641c080380080c51000c2c3c0d070000006031407074a401003540c00450b40f101c100c0722410002c0342d6000c030307240b401c007200402c2c1220102100d1005101840e00750480c0c01c1a00076001310348504541c00340c00010611180e401c88001c8213074000c80c4d18280300070030042034610050244622200045828000060704640c100724003441407201e8213403602044400c0f0390340741c180060305410917001c050143c60b045242560140c20b080e4050264990069020b1240940700020000b54442c071140b00120343c0308000c0d2505603481032200f403140c18040d500910521340a500303042106940c404c2180c450b07140881b141e8007200c100d80c400300104c080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 853298660 1250 853297410 853297427
    0x21903060c090b0c21120c0c060603010b0904020d0203151008100b181306050109020c0c0409080307050a03060b0c0c1905060702090c0c162c0115110102041203 70
    0x30444944e141c88500c3e5000d81d80e07044d90119152103459104003400c0c100c0290801c0703403801c199038442d60169141030010201280c101c100011003500945000403180e24041c1b15815154034001c01c9941070341c84503001d004511480c68000c0b41c1602c83c1d4440742660404404400d403154803003030f002c0c0030890300300070013141031203484082030882904081d80f49420742d0301ea00103407410401c0103422000583d50400d4148260b15070400c0940058501070002c11800e4182c0c00916040d14090215400102540c0c1031104a0ba081e00380a0800382045c0081190300d80705000429083c4800d1401181e8252a00071207407490384411003104c6254040411a40182084409030401c130555941420101d46004049010b9200b5098024400c00344540080e0303070030220b07005455215280c4000c0362461813150b001e040c0314110b00c3c051400d40c8c0404030f00b03c080026071000842e603a0810380640140c1a460301c0a21060488107059103024044d95152601c1402c1092001e00001c110502480c24104018240640b4230b04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 853299910 1250 853298660 853298669
    0x1401050a061508150d030c0f0312051503120309160e04032304060c140d1107050f060714010e15070e091e0603031e0c07050303031e04021903060c09 65
    0x9101c03010403140d1144c4460403000d0a5060701d401c600d0803540d19040b01d40c6105404c004000540d9000e1501c145a4400c070b00030446080c0718802c2000d0746840700e2550110720a4003540350316601c800c0c0d116900030b804002070340d048180c000454080a0f05206c00070101c420541101403070301061000c00043c5a408200f0f40580142c00140036001803000c6944032882c070560250005120780515040100481c10f01400103540c00b0b007007a60b242c1003a040740101200300f01000e021306880b42440c049260301d07045600034488107008081625144955903240c0070307500074040503007565503940e44402d0004810b205914404504040341c2c4024034008001420b41018040c144d8003d002e4201049814031100000c04c080d004803540c1d108983d503940700000e01d14800d088115101800d0300340304e210405020400340c011204200c041d0380d05180c0300c901349640d03404101d8084440b4102140c00c105120310b111380130360704940090111071503500b05110078030b0080e10b01c2e07000b102c10540d101d810100b500c0d0300541c1c000281 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 853301160 1250 853299910 853299917
    0x10c050901200a080c011e0c170a020403080307050705160b042303120409060e040221030702030303130b13080a030b0604091404031202160f1401050a0615 68
    0x88008002010059031082a514402c0da2210020b03588504003e90090203511070b01055484001c4041e66001e005520f034402c00ca007401c100a1041d00c07a0501130170712200c80566501210701c1003030211400c4000040d04101c01030b50b003040301101091040c0e0082d40300f12aa503c5180c1d88117110f01d805031604640410840340507111000a0189202130400c440454201c0c42041d918040040300303151800044800c456458406c0f0340c1c0e00190036880078090070840b0324900c0104041aa98114000b05403022100250f0058a0307030000e954014201d4100811103d40c88112400c00c9103d07800710385154070540b8001001088100f0b50810001066039995000c864622000303070b07111103a541c0b80d149009401200703061544035100c40040d17803104000e890003054202c1062002403288480c032320555500741e80540c0061164000c4000510150080381c0e20300c90300c0d81c2015900c0c0056150303402e000c000d102040301c1182e04118030040c2d00d41d09026550103001017080004016103400d4100e8030311041002e5210a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 853302410 1250 853301160 853301167
    0xf011805040b040303110c0f1e2107051603030905040e0a030e090a151e050a0614031b07050d1b022d0a24090e0403030b0a090c020f010c05 61
    0x202c1c00c0c1121078120360316040104402e115a0030f00802c502071040c1e4496140f2800c0083c01c1100300000e05030503072540d40d1500745003401e90644802d440340003041c20080849250070505820007003c07802000074034020007c0d0790004803540e2041600b0007040c0d00a40024142000c240002d01d440d1240e1103888150b00c00070212450166005814040d60100c2e141c800c0c650b40740003a804203001e410409030030008c05140f114464460300643e40780305040c03081441194804a01240c5030501a0380307103040c1d40c041d4841040384807110718955466403000340300700641122064803000ea0041c58000d032110500c51070142000d04040c0c100140801020203808060001c140701003000b68803048209450325001c801185940418420300300001000c4a8016030807005e0300000003112000030078180205400c01207002c40182c240d00c801c0f54040d0050240704144060080840c000034048d40c40082500c0700602000b246690760b044103400c03140d80401080160304200c0b410323445120288200340600b145410450b04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 853303660 1250 853302410 853302413
    0xa06090924020c010905030c0d0207051c050c0d060c030509010b220b0613061d0105041e0503010609140612031614010203150f100e06070f0b0f01180504 67
    0x1e10300484000800c1c07036060707803041c41203819404850b0301000d40402413264070b0f41031030003e50702e9201b072078008080c0c0116284200c08510100e41401140d000600c030800440050204081c1c66007000c900712046e104000380e04d44991a803004820b084c03402142e0014110300d54000107420f850000f002000e007a40340c40001d01d1503540d1150aa6542e082912003110038501c20a601c000a04171504902c0d440320000c5082d02410314100c0c501c0c416160035035030305543d2205a4400151060100b5109804900c0a10007800703420002d031104201c11961100d00390310143c0c6d40d0042070031140107421128244d900c9069800006041c00002034201c03c0036240b050410f008100229100e001d1312942030800c0703000303d846200348200d00d080788a864052000031552402c0081d0f4004244801450090290b0824080701c4403614003400c0d05200180c258613810080d02c88542006243d074041c203011120a0902d0340c41c9404071b007000031141d00c02d4007407002c000c4c1c031941031112440c4003003012001c4401d118107050806c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 853304910 1250 853303660 853303673
    0x10f0507140a03090b0c0c07120206090f1f021006060509030c090402180c13060f08010915080a1a0c16020f040f0513020f04020a140a21050a060909 65
    0x25028200e411007500c0e401900b500b240508889840030b40805800418000022541002041000200c400b203071641551011198815000c40c030340658411403e02ca00c1115045c929110f407810140188000020348520502e801141c0d801c10304140113134030999801a0324460f501c10040640080d04283c4e09284080300000c2e9a15684603807640101300f904046011922488498081030340f00500d103c800c0e00e8030201400310303500944003201418407043c5e000509107019152340c44842005607140403007a0f01706140080900449045240b00198504000074042002d02c9070700700240c495040014002c4015007040c2c04440e0203440d445c1e441d10200074a90600d0103c009244483e54196902c040b481c145d42d00180042c0345801c1c40810003810003040110400f801d182d03000c5468804c441403009210b100003407004a010381d00582012550702c2d55241210704010024002c219810315100b0741d600d0030250b410324040b448030340c288286d9841d103007032000113075a038082d240240c0700106080024800648900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 853306160 1250 853304910 853304927
    0x20306090f1e1501031b0b030f060f0319060605030f070605040312020a12030f0c050f0a03020702032404051c080627131a060603010501050d0f1409010f0507 69
    0x41000010150902d0840c0500f40324030100d141c0e240c2500c01841d80d5a040000c03003c84085000c21940d00f04540115003c045201905d000d40c03000c651f81d07201c96403880c0a00418242c481005a0301d440740c82c0c03d000310f6031001611031000e00c2c420507021620750300d01000c1c54501200b058070840b040e08480010b002e00d5911a040e40e0861340c00091008481400140590516101c1e160150000c1350b81c0900018264254212000000f84e2803010015400c90b90000c407601d0240c11310400049000300901d0b00660303c02d030013422240740010150b5000b05207100329030080250710011849003040c0ca4081105102d0180300c0000441c15156500c50364005a00000713000040090030103104400e515195484c5190740c815a08074441d001c0c1e1070601d1fa0421701c08100d11015040d00071940c4611300315103080d0b035405044a55001e100d014100900f540d085c58015242ca03002224614641641c503100100d8002150188440001c07224050004504106c13101909480d0703490811101c1c7d60800c000d01200ea035000021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 853307410 1250 853306160 853306183
    0x20f0123161b0309180207030f0f0915050405210601081504201002010e0f0c100305041403030709180c0804080d0e0601090e010b15040603090204020d0e0a020306090f 73
    0xc042c0d42007658501a00e0401e013507042115401c5140c1c0409298641c00d90041441d10b010751651101000c40c0c0c5421640106244051000694020020130518a4004104001e0003d50034241e050540f01c101095810605c400d8041e240c1182041c045503988041c4a00e0b405401d101e00500101c8885090140503540080e00c0102030030260050405c05074070701c1101c01c0c8119070041c208410b0210f0070000070701900e8421041c2c0c116000b100b0800740705407800100040000c902038080340c00d284600c2d00640003848003c1094403090100f2006103030400050006512400c070644400306010b00b03080d044055110305166107014039280c0305120102030741105540d07500c2039114000942d9805107440d02c101929902204021505c00e00c0008200007a998000752107440000008101136403106081001e00f500b08407200504200406c411f1000c0d40c400e410040202d400904094130380000603502c0c1080356220003039009a50062944103007146001e000481e040540c0c00d0041c02c4501d00e80074000d840c0c1400381030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 853308660 1250 853307410 853307447
    0x714030601030f080a050705010c0e030d090305071e030c090c0801090212130510020403061e09080d02090402090a06050d06051e06070c0e010609080f010513030c03020f012316 77
    0x6042d45c1540c4500100c440003a40807000f130103140484d14000e00100c8142e800b45200b801422048050584280d5602040b070f50000003c0000a161030b881a41184103050544103c101050001c4041418040700d0320050290480008060300c51410041c60804180c100b040e1041c010060107201704180c5000d690820141c140c19404802540b40c96440c3c58112110b01000500100b4004140070603607000480b40745c080600500b103015003d4a09080303410003040145819018413041240d10590390142c07460f100050401403034010404001388001c0ca01e5800340c000140c2c000f0380000210319038003c101c010b0a00781c80c5880c81c03005001c3d035680d4401400340e0b254042d00b4085002410300c84660f0078040245815241a642135071a09030080000c2c9860107400403500c074050b01040c4d401014819944a032900713011542c00448a82d0702111001401081a4114417580b00250155082072103044904003070120003103011010002d1800300414002c0041981013540a0a039501f81e40140e800140820450b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 853309910 1250 853308660 853308667
    0x60302030403140d150b21040320160924031101030911060403060c0f02070e060f061c050108011409100513060f0207061a030a02060a0219050714030601030f08 70
    0x40c141c4001c00003000801354118105c400066412031560003013840c001040d0280181d02460010040b43d06020f82d0700400180030784000c000301a810399001c01030f8000110596844101c610500c0c03c0c0c0c0c0e5440d401050800c1d1b595040c0141302100c8801c0c01c00507441980b2848069455503d800660412400e805810705445004480030001021205d01001c0c00041aa648582c5c81c0c1c20b041c070040411400d1748001c611181640c006507800007643c0f0302150307241400d041141e6a608140405020303524407058109005000000750042e4501404c1c200203040c0a00142541c0342c281c1c243e080d41ca091022114400703d074003c0c000000d001181c03241e032407094030602046586514042e0900226040302c054005450324030f031001c03860b2064000f42606402664240428801d8801451080300d440d00d03101d9140e804840140014101030f006451070000d40c1c01a20880c0e46146825110b466003280c04481c280c010040074008005202d680449444041c0d00800196042d0fa03110800000410340c00382203042c012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 853311160 1250 853309910 853309927
    0x6050603070f030506040c0609030c180f020c0f06010b0a1b020f0d0b01030b0604021c1a100c0506011a0406030b0f061c050106020c0303090108060d0b10030c06030203040314 76
    0x7080a00000c10414600b80e08055490030720130b45610094404850407070741020000b4000d407003102a901580e40081c182c1d50381a1808140513212441c0d07020302403102b9280d031413415a01e4031a00c050074a03001082c0145c01c0701c1500f1000c440c14074405030402e5444480620011a03005d5221342401c410343c0f49100085a001d03911b000254603002440440766002e201d60010504104195801c0c90403130f131207035040004940b40c440800051780903880e04043d064640004010680b001500b000400b503010003424411180700300045140c80701d00c10540408200d04418480401c2410044180108841c00d600d82828107a00c440b41c000c0c1c80b8070301c40c810404d911a841000c6594404120b450401802844642d841d51140d01c4200444e40b400d00305c030b0081e032030174000081803400400d041c0307503400b0000c029610303003a1000c00540b4100005480307650050200ea003400c0004243d460064060010012080056803441c682155030b2829030b044001014010300520000981125000c03020b220340c11f24a58136490070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 853312410 1250 853311160 853311163
    0x1509070803040b1309090209070516051603021302160f050304081b0111011a1c0203030c1507030c0219031116061805090f070207171005060102060403080406050603 72
    0x54100d1490380c000007800140040a410003000c1412a9030b07414061076035110700060441d544d0460217500200100c001031200c5205500505500144200461205d40e1648036240340c60001d00c1c2c0140030011102084c0107610f0030f140080d00400181005500e003054150002651080d00c00c0300518100c400710030034041080610035100500018001c42d21594540c0485200c0012610409404100c00340e031255030044041c000d03841410030140741013858684d90014800d25003030072240f10100c2c05403070b548003005079400d200421352044001c0c000e010b600c0300c0744c00c0303100c0d4003030040c0501d003e061034075092048160f004100c6a90f051082ca11041d6110a60704003600ca803451a182c410350342c0103001c0d0b040004809242d5290a480580d5155001c0921220b0010300c0302e0070343d004003607211210310006105034240e021182e40c0b10a0380c2c4180ca08041d5124098121400b0303500b501c641580101c0b0003508001e00511071175600600c00d01c000c1c00e25003081e4502819080d0040c10140c82203465000240c2a600e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 853313660 1250 853312410 853312423
    0xf051207090230010e160e01050c0c060304052503030f0806010c021906090803090904021009150903060b0a0b3f041103010902011b050a02040e030a020705010f021509 73
    0x10760f1449225652008241c41c0a0500340201c6106003000c002090703110307407000c07180b170081000c503180c42020041c00e00054520760088265480c041c03050121424a40e2252406180500e07c124020180001003040d80ca1141e150b403505c008500091440030400702c4d6020032000d06000d410b0600b4a4a904d400c801280c10444e4080040c1d000b01068610310707600d00700490b10a00b1102955108440103880b034880d542c0343d03c540e6803226401351200d0042405440d00c41507010000e11981030040308a961044003a074410030190b440400318181c048108284405030290360a0003c00311a0626403a0412040422501030f815211179084038100b030302e6051849035162000107600c01c0101074038000000c00c1145040030110f90031106208030a030b0101650a050041c1c4600c02d9050b140c0b025034100c400500c42c2d41c0100305006982ca0301c580101c040240e2214403618150741030b2000950759a035448036001e450140f07a54030042c1004400320314206990342c0800c2c5c1024405a00030380e01e0240c3c0310708800601d00320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 853314910 1250 853313660 853313707
    0xc12030f090c0b090103050609060f120f0105131106030f071b05190c12051908121503010c0e060f070303021207030b03060c1215041506090f0512070902 67
    0x1c8042c501040942024002e850501800da800f400540e4500b0b081c452140e1041c2c856680200c030790b00c043e0246240004002050b9035142d02200c2c8100690703400c40b400d5440c141d40c0340c50240010700222003800f04c50819000c3c42e580942e4010300c0c0d810101020b5500c410010610f0003004001d00c400341d6403111050f086001d06421400700c03480d024051665004d52541c5c0d420441d40c0070310a0000003103020040b440300d00b181e50031501400c3c0c3d284240e40d8135600b1404000c4c0481d040182086075074000d1440ca0590f6019082d46007609440341000402c1c1821203140000e100d043c85000c82840201da515503088030601d000300c22403c0e440d40d50501e8150003038010040099070700040103041040007541035010010038941241100c3c403544525400540d0b0b4450850b041101d40003900000d0280d040b1030114089851001e800020001080001d01c40756581c142c0081c0b00040c10000c04005a02c52214070a024000854161418041503400e01c0d40c2c50202e032046e107860b150041092038500c080c60300f20b6210748 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 853316160 1250 853314910 853314923
    0x703021216151d120d1e0e071716090b0a090f02130e0705090913150507030e0c1e031504080306010909021804110c07060503090c010c12030f09 63
    0x25488410054042c144655000500030300140d5000c1d243d0100150000c80250740f10016460400041c4802001c2d02e000303c0c445034529482e000c400500c180710702c076004000030351030094200c09007007403641c49520305848610007941d88500c03840349006850201150407160111000101000944045146401207911120041b031400110700c100400035001030400f90b13004070035441d10030388600c1c00505840e0300b40e070751400054092007004041d0411406c2d10b83c20407988060300c000d00c403056940c0c0e1000800c581150f2482078550042c4000070ba098040ca65580c210074014040f00c0c00c5d070101050b401180700c3ea442c0c800401e00f504604290310148942c0400743d011141c1c3c00c0c0d6505c0c060030225070942c419112a80001c051b0b02380044d80701c00d64401c0e6094a000d1390700b442805a40002000041c2041340380c00c06085404210040c03450700200241c0e0004c00e000c0c0c072075a85928000e0940390520a404034414148900f68a091000640c0305040c0110a8110b040014220003100c1c1c0c1c150061141906c0100b11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 853317410 1250 853316160 853316183
    0x10f11070f061206080a0302030a0302030604060b0301060f030f11160c090c0c05151512121602010e03060f01380405090a140a090809100f0f0201020703021216 70
    0x6150b84461046240404407500f41305050351a90b85c07565841d00b90300060300581042c08075029051098004540000f0002c0002c42e03203d8441203a556180e000382e102c0130115071005108079000341c00d4090011022860340302080890401180b01001e407107440c941001703214000105404200400c06120041c0101c480c081100241040014010070032988040e9007911441007102c0d403402428040d54400d030f03a01107441220407156800d0011441c001c0d032001d0300a00a040c60f0744040c44082d03006c0d26403205500410605d4003900e00014183d4407001d44180d001c1e030003d800304000c02e0445e0514604580e84241d100310207420180c109e000b41041000c1c40b401c003050800380a41001d00701005001603d00403294025241c4480c0900d10481e200d060064062560080000702c24141c81d50041e00b545008134000c0c0d2408801e400010f50003074288074420b02003021021080d0402703502030f002503422a081d0008500d040c084d43ca020f07680d503014039004c01031400b0005640500d80c3c440300440c018107034800000d010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 853318660 1250 853317410 853317419
    0x601090903050c12220614070812151c0b040206070c0e0a02070b06040506030a14011119030b010809060f04020a0902030405070806150f0402031b070c060f080105010f11070f 76
    0x2850340c4941c5d0034481e642800074094803e0300171001c0381e03421640b01d0344642d66041c25050700611650441c1d002070303c0e1034000303001e400c1c02d40042500c4e40d4818615651040f0046a01d13030100591040c0a8500c4000030701c51480f0400090103507a20720b504a90110303412034aa040610303041c1c24001c0b95804c1700c2946107001c01440f401c034081d0740180c01d41034801d04915005682e0541444201c5000f111000e60680c00f42062b00003045070800c0c16105108040700208440100d9070b2840d61646c48184181c1c012030906904c1195954148200500d511003444c00841c039040180811340e0320900901000c1241c00d00401007001c560f42d1500020040541c04400d40d100c0c85d0a041590b1100501e218201141c0940000036200c04100c41040c0e085003130007090084140c51500a1200a400003490000202044c80310340c0042d6501d107002d4170000b8492003002051320300b054401020201c0c10740819040c007a2510042c4a0381c0e800c120003d17526840351914403404080c0c032401901d409020f60020080094084001c103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 853319910 1250 853318660 853318693
    0x150405031b030c0907120519020a02100e12030c1309050901020306030c10120506030a05150a060e060a0b0702031023010e1e0406060308030a140610020601090903050c 73
    0x4400703100b00c040d02e000e40100703414002402000c850310400540300c2c1441d5041d00e0081c0d072100e6006060360b881c155855035148050400c9074441c90039000540d010690701d0304d1a0707683d4040c1d0013054104c3c1e0040c7c22402440b07035082446000250030181c80070400320f074113040c0d805c842e1040e03001444030850910103400c248841a0003584262000750285c007810401c001d0034280034000f02d80c252982e42d00c0302e0712100000400401050040c000c0c542c10f004030030003040450010054030000001b010300103405400e111501904840030350348140c4602c442003040210343c1d42d9034410303076040f80c00456010760358050703510001b800d01001c200800c40303440c60b08500d091510405892038680da0013585280806903250f1002c4905100f0031111114481c0c4d0304801d20003800303084c0360040d03082031040b040801c0389a200e644001c05a00103c2d406070400d0b588442c40c4252101e120380050704080c01307a45009031100c042c113000327417a00c40501551084603142c8494000301845041141d400700034517400c4d5112004a1440301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 853321160 1250 853319910 853319953
    0x109062408030307050901020f0d03051e0405030403020108042a050a05010c0f020411370c02090703050c130f08060906160806130e0106030c080a030503040215040503 73
    0x1200d4030009a510340ca106090020030059441c1c0c20300850459544084c1192a41c3c0b043e40f400b0b0450103a041d114544034800c0003091410310719500c011980389032006814010841c90070b42069082411400d001c04160040200e4003a207070286801c1c0819036440c28000101c00d104014212081c00004c46d000a440290f41e907881a07a60440b04503200d19a1440115440480d558005d000c540d9150001001454150b0250b0100d0800340400c83c20700d48811543d540000540e0003981103900a0a0f0061411384105070000542c1c7c15030425014070111500844c110700300040c001000e05030350324003007040b40d6101e1007910500c1c424500203c10745504c648628420002034802c1c88039a12640001c2000588045085c030301c84d03801301031020054070004500729100000505980d8004e10342d81000054854075008140170188520004540c1516520b0402400e913080e61280009030450440b9a0019501c04112500706804a400e01e40d40d010f500d079203a41c940724070f500060b13162151404404440c99120003d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 853322410 1250 853321160 853321181
    0x3030b120f0c0d080f03100b0f030108010b0a030827060c0c040b01080915040609080d1d0d0e01030b120105130318060504030605100515042603030610030e010906 71
    0x9603846802900b080c001c1c403403010b98000f00b1091080c041d0f88035030114200034550105508007000c0000380d454440c00c51961058822181602d00000144011a424060240c491609840710300e29a8659140d0801c103005d000c40c04400104095400051003c08190040e1600d900908041e5a1807074240e0f001d5079a02c49425050085043c00068800e0f980103020301c41c840c4c41c0c01c90281c103481001c020403200001004004480b1240d44400100228030704001a005442c5222000641b11480c03000e11070a0421854141e89968030412202e207050364015812081e1440a007004502c000e0b404000036841400f03501c60303600c80d47c605010003210048065144411034081c0c0c1b40e4881203800c0c01a04030003103005000702c02c08508104010400200070780c0c802c40e80a5200700604003001d880b040054a4041e0004544144a00104080c0034241d2804045104641a002d0f40e01013102180c5140d500c90100400d081e00c41c2842c0c8040d6070015003e500412502d5088000030044030310103140060080030350824 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 853323660 1250 853322410 853322413
    0x31902010e1912020a0c03080304020108060f061e0d050406020a080903090a060f0c060f0b010f0804020a030f0c0b030702031806070c1a0909040b06090708010f1203030b120f 76
    0xd940c03a0100000ca41c8802441c000d0018001011803a100d03500d02e18000f901030b4045201e499054004115607a1002000d07522420442da070700d0616000040100401070410780c030503000d0345075203141903586000300c1d541c2c58002105e009a190709011492040d010359054912054102020002000002d44c020610300040791034100c19a112a9011a0369010320300080303800ac000300c02c7c1840114006c003d0a1032010203031521001c0d000f000e6481c54256182140c0003015075849000d100213a40e08007030130044003aa40c0c900040c1c90319140e000504041d1070303848090682c10451000c80240800c0b9140c0340003900060350001d6582c03c3c0410002e56a03440300301c0c4900c0481e50140240722900c2c00e08115049103070000540c016103410190344070384000c0c00c0480d0050014003007200240d582ca07440d52151082d80a44080345a03407520500307014828070014000010080d02000501012741100c80000544881e4130100705d141446282c140c0007068201c180303903440f078205d240010800c02c00003040c5866040d140d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 853324910 1250 853323660 853323671
    0xe0c042f13140a0924061803230f0606010e040504050c01030b032a090a09050a0605040203032107020f190f0213050103030c060e0a030c020603040309030503190201 72
    0x4032815010300710a080c1690318818080194080c600e00a01d01150010071030f8450a0361500400e08a502040128494101540300003103982c0b2081c5a00d8000c020a041c140001d0016450051204600f0b0100400d009000250003600034000036058901000d08800c488041e100742c0d140c1d5a80e20b804440490000d4000d41c41803c0c941003901545014550060060820007001030042d4050b0401c0ca12a54040c0b15010480810f8050f40d00b0049030030b103881d10140c0d030844158084c0b0240041c0142050090740c148000d41c00020000246100c125408c5a40002c2c15200e42c80064114480e10f99600d4034407108104602040803208296801040746030210380c100e2071f41444980e210280081204040c22032440424041140d01c0300e0a856a031000f800c000c481c84c1040f0004003260000c1e00154000b486060030001040075a100700b00451105130700400190340e80d40c1e0000c0840c0b03950000240075113008004102091b016844840240d0b9102c0160384d10361010354100c800e1408004202c1c0010760801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 853326160 1250 853324910 853324991
    0x70324050906101d06100c2a0506040e0f040c0f03060608010f06030201020d11010f0507020c030d080103020906010e270a1a03030702010507210504090605030615040e0c04 75
    0xe4428400903c1c5052400c80d42e1360002c1121443c0c0b8280c0c48000e100703102c000d100000c0c0d0010343d0519081381d22800450512442c10080c0c8d44a00711fa04644c1c01110108010300c00a90030131501c1c0c1d40151048100703100790707076546400b176241d0035542e1005a40320b045030350120411155810110907a0300c4d1200801c51101c505084800359050381c8006400741c2c1204140562062080901b14201c3d101d1740000304400da14400b5046c00c81300215100001078200204c02e5002d86010b005040c3c0044070f070300c2c4c00c941075411a0005000e84601801003030500c5140c407542c00941d1102d02e00c400b49003d03041140790341070021202d003440d250030490310136480790b103000c010302400811140058000030f0007400643c20100326a005544c20f074811501075851a45000c0160070b0030038458448030800700340703956858660340380c800448283c0f00c264101601c680c1003241040303110101001c0c074103035210341150007194803103c14158505003402101105d8015041c1403150a04291080d5080708042c0c2a110383c0702c81d004074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 853327410 1250 853326160 853326179
    0xf01140103031407200d150b03160303050a0804020d020409050a020f0612060d050c15040e160f030c140d0615030b06030a02070317190b040e07032405090610 69
    0x1d01c1c6000f0402ca20b17480f4194101d440e5554250603014000e46650400c6642d500c0e0440c0820030f050000c030072941c0310700c030010050505000d00031001c0100c00d0480d1060703086603005426801540050410401401c0c0080c0a6503031350f06603803080b550060801c11003080d250414a4481603201400d038000c1d0902e000246042c10100200c8110010340c281c901c090341c889000300484100014415200c40c03080102441c269603612a1218104450114941e643c600d44610101c1c140402070450540e00401c415180000e80c1002000d10444558600064410301c0b001c3c041c0c5400c000c0031710300e030b02251011400802442040c1d100034103232140d07490810800342e904c09080701075840c4002d9150b0080c60601c04111901c1c221f8002d0003450f0f100723060945045007008030002e405041180d1030b030010210520311085521680c4074280e43c0e408151401d00102421030400766880c1d034a440b00a1a4080107503140301603100780d909202c004000900207020034184280e00d683e591400b6070302c001903810030410020700c11303c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 853328660 1250 853327410 853327417
    0x7030605010b12070e06120406020408030f0c010c03060e010b090d0b0712060e070225030206030415050a2d0e06070f02060c280e0d050303070201110909010b09030f011401030314 78
    0x8001d0580b441c10300c2130381c207d8041c140041c1c021200b0701c1d028040410001414005402140400d4170056142d2441590407820b4401e01c034046001d041c504103050105615000340241035070301c03049649076201e1a0902090402c021440d000d020105600b0901c61a550300c0058004100e00d000018010582c560f003c00a251009680010151b808502080d688540c00b074184244082d071a45040e49640d503940109005a001710b504498500e0360442c00c403002d44951140e00d4001c2c070000800c104240441e21001600c60220100020010b285e03642c204225426070004032000e051002901e00c0340c20300910103407441802d25401000f5020300c0002440e00340d4410107803002d52605074003000440c02c110300010241c1a1101500c801c00c0100c040c4070032203072034000d500c800081c402c00c001c603641d190650b402401c40e5401000c8880c0e8040805c65281240e0b500141c1a0540381a524040c0da61354004001900e00303110380e144440554201701390f0102c02d074082001e0904030380c040d8503801100a40350807641098030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 853329910 1250 853328660 853328687
    0x1080d03020f04060806180f0f0f04200307050a1805070206070c08070609060c08010f1d0a0e012304060606080c0d0c1b0f020f01080402030a03030b010207030605010b1207 75
    0x104140410001588030700345c61030b01300350042d00d0300001d4041c0c0c4401c142510300440e040c50601600708203004e2400c49052940c1d0344802c43c1d03441c40d180d40c107107aa0303101941202c101c150002c2e01e0620b0a2543c0981c0d00784a108000c080007403040070900c1d036410400242d99118001490380038588070020300d50328000b26840f449188141e40e00103ca9006690f0070100d40c001003c203540d00b1340c0e0340d2640c1c0001050341c0b00300300d0b4166481e210103642e07600d0204100425005900140140e55140d0807211400128441c81c0380c100040071008505041e44615040c010440b440d03000100303c840400140d06619444bc83c51701486c01101309000c81611084291401182940d481d520103200304480c0d60390703804507031203100028200d01e8a0381c000d1000414a6601000311042690080f000c41024000c51402590950b416a000e09058601c0d14040d00007a85079400300c4006014107895403184a1968800d0045c40c01466001c40104500e58541004000c0340c1c0182e0b03060800d07100c50601040b032280c0500c054231041c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 853331160 1250 853329910 853329937
    0x50609010f0b0a120203070503150a0510050d0908041503050601020d0c0209040320030a030e060705040e0915100e1003200105040b2b0b030c010f170f01080d0302 71
    0x703490200c401000c0c2d400303103803103008100803103608003030032021800150b01031000395a900c1d413a400c044546c0b801007106528690302c80c100c15402000951101c580451880850b820202e4892904200d498050040408000d100c2c9078001004a540520700000c01c4000f103040d60b0411a941d651001640c1c1d52000c218000085039020103030304010710b80050041d40c4241320346081e50761040203031049600340700100c090f4030fa0b6410229030520703000d6052044555803861080200114200b40d440130f85144114010700c966044408000303101c44208202402191103039010310038240c41d15031414501ca030000d00803045203e144e1004251065811202e040941c4c1c3c0100c0108040f440000c1c3c8180165505d40d00141804024440003c1c15200d0a0241040801110303100113000040c802c402024500d40d150300e002c451419000b810140c50014613041031003003c1c28035042c11884c00d00d00340e40080b850b2810b544010180410042ca250305400b030503048411100c203d5003100c170070030401d13010b070f00a00f0b0703a040c0c0d003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 853332410 1250 853331160 853331189
    0x1d0105030a080d09020301110a110102030105060a1803080307031401050414070f030b060f0c0d0f051e07080d0902010306090b0102100911090a0b01020c101d0a05040e06060405060901 80
    0x442c4100000300a00780e182c160000310703c6440d0b030100b03003034030100701280303910042c0401d003204e0445d00600c008900c0c54054008625640c10000051a00d0003807591840c02c0001d40d4130851107664000c50a100615009a8459102c0c604200b009018000222041e0745800c4440e000140c54140350048220510502d12035002c1030355042c0c4110703648001c1820308401c05490701115029501c4040c01001c252500300b490346c0e0740b109003d0151b031070701b02d029140901300490740318002050f41d8040141d40c401d150055108164a00c060502c2c40c40d802594405454504001070b1701e0030142e101d41c4814038486c400e0320103011003680c071308107041201c5100d41020f0258000f5a000b04500e0802c0c2d2200300b00c2031107000f6070340c1b50300403410100c0c100950440300c0ad594550395100300117071581c0410000030444804c54449500c56950700d401170101d94410003251136003081c11207002043c0c0c6c401d140000a0000034004000e0380c1d0a1500981d51000c0689410340500c1c9058046080c0d0b0402403107481c180c456007004d000b0b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 853333660 1250 853332410 853332413
    0x402030a02040b04110703080906070801050303030f04060f02040b0c0f070522200307031a0105040b1e0c0714040603050d0c0602070605012606040302120a0203070c09061d0105030a 79
    0x340c10394010b01c2c2e9100390754422585c8084c41002c05480241d0003581c0304100d43c6800d05001e860094050014001e020200700104a42d950000807a03511002c0c042c1800303c50307192031030020050402e0b001030140707850010402040c4c0b0030344800a810b8446048003222081c9001c030902903115603140c06403541000d400c010303928082d0030545800e0784007402e00c0c0d00040c081e13003901402941620358100400c400f60b000002c1c80303102903241c024261b10300500d0890b62100a0070030006405842144a0010400000b00e2210620414890840c001c0110101342c40d41d40e614000c40036458980c14080d0318001070555502e059181407a00c0b030070b41900d03800310050079080c00e08002600d5031000c80d002112610b40801061000070940d00405000b48981900d008600480c03110320420320f8545641c0c1903950340001c0811012942c0081c0038405440780002c40c0f580c030350744c900c0120700f91300c03a001020f00510460f98000845900c1c43e400b08040b118400c0100f5600408000c096102400c21f11500d585035008100342d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 853334910 1250 853333660 853333669
    0x50a030f0201200705280f03020306010b0a0c0b0601021c12180215160f0b06010906111e0705120303090c124206030c011701150203130807031203050402030a02 70
    0xc0d01b0003000d0191035901008840e88440c1010fa42188100924540f000c00450a0401005000d0407400c02590b0400d11424001480c62a64400240008220a001c035407264020f001d10a030850031480c5a030321003030110748060240d403401c0316410b13003540c600284a80c1c400100c036808003042d640101043c1824800d4010704009401c40070404c000000c0b446504000076040c45104900e00d480740c0c4030415140751034000901003504036440310081c4010304604201c0b60a0204481c0c031140700d401001940c0164200d9030340e1500605070005508078440201c040c9141400002a600c030b03003a000c0441d003020000c80300b8003c000302ca2500403a450361014200709041c0d1180d0390f604109124a03103e40c00c01e10460000e600e40100402030343c0c20012051700a01155040c148a0486521f03400e0901c0c51a00902100703094990905114081d110114000b2005905209004481c0200111054096441e841e00311941d15495644021920003644215000525002c2e000da1807060750018045d0281c0d40c2180c0a00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 853336160 1250 853334910 853334929
    0x1d0c0f0d060e0c030715080c04030206070f0303020f0a02160816060311090d06140a0b06040b090d061b08100e010e090106050a18050603030f0a050c0106050a030f0201200705 76
    0x8011600400d035143e030003500d00300b00c280c000300782150070400f5102c04400050000080505035085c8071100304002d00150300e07a5030407039002961240d481298601d00c0c2c01c040f1f0090140c580d004802c000c00180c55000c01c0d50020380c0c49035000c401c0b501540c0c01039450f820140c1e0b4030003240f092101100209d0042083d02c1c000d900605007084030340b004034681072040c00062200003200d00111036682d41c41c4614000d05076885a01c90340001c2003036041003210b0000c000181c060191b8400c500106200040340c3d800c40d118071042025aa40c0030409216200c942d040040c42c0c007003400380310000501ea10000074900e4000007604c07030455201041d145100d900f0f00c4448135100e84014481006592182c4001480da04c0b03080c1703140c0007413000200c8443c0381d0148014410036580041e1005100c0c1d4414884583c1c2480c0d1081143e03103c000340c1c2072480da25400155a24050a40d0360702c42644402456800814404501922002503200343e17200c444207451505007104400e540310b5000040c0c0d0003154240301d242050500f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 853337410 1250 853336160 853336181
    0xc0a060e09100e180d022b03060905010b0316170f090f060708270309010503041a0112060c18051c05030d0f0c051c021c1d0c0f0d06 58
    0x2c4401e8503440e00d000c003100300c0007070b19a0007208108400403201140117011034900c0ca4107503c05025003401188051040f040740c0c850600c007070013400c3e00302e10049020b540200300404000105115540c0d4401c042c20341b50b04212014032001180002d540c2c0c046102c2c14480e29030000720000401151168130001010b408010081001031140d23940c0d4031403034003042080d14460361183e520300482d0318000e015240d140342006c52200c0c103500318603400d03203400c40048142c4085510a2800030740703d668a01b48824654800308000000583c0d21001043c4414413034001114103020b40000d001007401000215683c20a9181502000800038001e11441c5485040c01000c0a00300204908003c600e0322645c1c19276005080c260708103035458100b100d4031162382c058201014200d003030440c105138100001315052042d5200c41480d82d5400103600c4103024030710302c5040d242c8800401c100b0500d0703044000086c4d4500500201100e5218440c3d065255142007001c1004c2a1405040d20403100a5551014081d210b01a0b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 853338660 1250 853337410 853337431
    0x312270d090905072a1403040803221203030603030e060c0a06110904021b2e110f0a02060601080108010e030a0806031e07090c0503150f04090b01170c0a060e09 70
    0x70103100a05070100108041e10122403204281030203182458825441b4406021107130804d04c02080342400100a40d0400b04491240c803400b43c0e04402d400b407000d0b003642c12800240c484c81c1c2c2c0c0c960074103515511034011303203101f030b16144d4a2400e102c042100d90300400b00010190381c40b0710303000000100140c00c01300b2580f00600000741000c2c000f100080503070300803014a00003000d22211640b40010104510090381c048107000140c6c508401e44d070840a01401d00c1c20070407441c1c03205c022840c008400422500c035040e0420009486040407040203488400540e6841d00152030600086030382c107018410060010000c2000718a8220900e4041c1c6840000070402c5501d0b00030b0641d0408400302da8500c00e000500c508001e81507580c10041450210740c2c0143c20502003040c140100000651031828006025500f101d611042141d0300300020040c00740401c000744840161400012030182f1104444240074426082c1d420f00c5440c1da05000781d040c214451040020100302d400c44440c1451680142c11481205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 853339910 1250 853338660 853338677
    0x50619030e120f070b010e04120c080c0105010e010501030e0d080a1a0303191b0201020d08040501091211010e151b070807050a0b0703200c0312270d09090507 69
    0x180490200e4000303c00e003004010000030340c03034200603074840e403140504a01040d408881c142601d0316010245840750b11401d20150b503c4c29010722013020181c0c0c00c2800302600900a560311100000f810620a1090501203414090750143d01e800100300045003080d41d954507402541c1d00f04041c0c024092101e1407040c0c50403c07680104054a05000508902d03603c0711816400d0740d5080e000600003804c50303081701c00600301030b00f502c00182c1c0d010400d8040b103103452500d1082902c0e603040107030051465140052221000c58402c2103050b40094840e0040100d000081120400085030307e81c81e00e6100a121490401070000140703115003a01d42025034101c0781090608000782074ad907802065010940c19951a40078843c590200610403010560200c11840c09219640d81d550219043d000044401c0e040b9200104a800720754004005981d1215032a8810141c20306009072100c00c910600c2c0d00260701c24071010042503903800300290899100201d60784a01c100da2805032034200419014000008220498 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 853341160 1250 853339910 853339933
    0x1c050f160503130f08060c0a12050405060103050c010c03020c04110f07030512010b16060c111506030106060f140702010e0901031406070212070605100305060906040c050619030e 78
    0x80c0100410144104020360351074598420505004405910486000c15508024800c1d0b40000c181d03241c01503044a80707640c40700800304003940d00998014100d003201c1c0c9418104070a100001070600d048034000c50554001d8801e0340c00440d551700c1040c40250250740301040510741c504040d40001000c9038200d0445051007950100b845140d404018283c000501c013258000f120044449800e004121800c4400c0c03800191038540c0301000c101742001350030640c0d52008090514003461442105800c00000e480c580084180e0451507401c0540b9254029072800801140941c0114003880c0c54290783d444251a05c054001140510790000300e0803410041d44200c28001c40d110b421806000e988600800f101d01d101014513a850101300034032581c03c541c050070b0800c0f0103c1004088481a0740c0245010840780e41b8408541000c214551005086114450400041c16008511107004620801829165550f03a408122041c0078950810303031101c21040c44088014000c0d8080c4101e034040341d06842264101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 853342410 1250 853341160 853341187
    0x120f10030f1a0405070627150e060310170f0a0f08190801170a12120905030301032904080906030a0f090c0612090b0a1d061014031c050f 60
    0x43e01c0840300d551000005000058100e408280e0b01c0c2000441d1f4850101e48030302c00042e00166200c1d10f03a40701c180142c100150381c4180c08100d806a0007810556903070501001207000180302e03100f030128104102445001c4810042081c0720008052401450034031420b88901e850441c020000700c1c1c00060422180165440901c0300117220045034896022a62500c00e2205005c01e0141c200d82058119020240004a0054a5210b95a403602d051850740c83d4821480340101058040070785144400310000003007040303840211324038004207203a144005480003052007440405a900a00352101071248990780e0070240060b540c4828079280204081030138110541c125a03100c5416501448450820320560750000c0c549184104440400c101c460b44648851544140c054080c8045c547c0768140a0f20129110500425151098042daa00750528122422840b45c00c5e20405010404a00510310f491a0201e00b08551106200300141010401c8604540c079500c204900e8090075400c6c4030b00004880b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 853343660 1250 853342410 853342463
    0x20402090d0609051c02010504170a02070b03010803090a1208030c030c0702090f0f010609140d420c020a030c0203010e1207111915050702060d02120f10030f 69
    0xd0f0f01900340e485d110301e03003080c0501c03045030010107580c103080911000031807890301868102501072009441340402c046c12810280958406207034500301000200d141c220100c01008802c82c01c5902e01c03170140d51a40d000444010000025041e40710610004c1d25480c00c0c270340110341c07240d0410304452034150203a0000743c0c203d00650740b0500900034030040001c0c518012900340c1c0035241d2400d200303110310310700021581608010404540140c40c00c15904040105036009221110701c40440095444044a04d07640c8240c07620140b1990700d0744031140100c034050a4070400d07003072040310303400fa207004a0161403d6071103070b240e52030481e01590381e44202da40000040c0a5500303001060f008040c0e450801c4e091603100700481108a504c03507845590007501e50400c1d124000200d0b400d201d8041e401e0b08061b10192258082c602d0042d4121800007401e00050304580d004180f25550040c402609840700c10841a0903042121100a04030500f0000d0000c03075910f80380c607800c45110300c1a0020f0300c000020030007c401c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 853344910 1250 853343660 853343663
    0x825030e011409070b071a0c070c06140f03100f08030903060f0702190c1206020409051f0b13180c08090309030303011701380418020402090d0609 64
    0xa6495400144000c401e000c0c080c4040c0c82c4940b01c06040c01c100030519280d40300c612035800d0760f880005a040404c04103909110040403000b03101200c510b4158040384444e031140d00102d90400c0f94901c04a0f0960207211003401f400390380400c05040101c0f0030701c0e418180d88003030001107040c0010100010300c05180d03d0301502503d40340c0c01450725850302c8020b0629084028005400c01c1e03070700404002e02c4603800102d22038401001c807407074080106a428810f907052100e4204844906540340d4510900007a50010070848658810802c041d69901403241c442011403140e141c07085404210800c10030380648050f118003440c0703c210000e116580c0041c008240c3c40b85010520998035402400e00e000c0e00507120582c400c06031006589070000000010f46c40340b105002d0704402032040b882043c80c08100b580f04081410b40605001d92950143c17010300007610010401244044008038100e0301420240155800f961b880411070760220b80355402c10010390090003034a074010002c800c0450104213280120700c402c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 853346160 1250 853344910 853344917
    0x100e060a02071a13050f1e012003100f0807030309060315031101030e2a0306010b07120e0d03120e070602120d0902060712080105060a0f030903021204030309050a0807150825 76
    0x145c000e1800341503844032087d006203260345041402000e400301004288185c90020f180340d81d80ba07403070050303002e5034080e0341d0443d610020940c0b40103d14a100020341000b983e001c1c1d103506049540c0c941c3c0072020764000500c8540000f00c800070420000d014041c0b034407001c1d541414017143d0802407010580c68000b40030320701d51042c20442c0c0380b001d40c1e40440e010b032001e21005401400c042d60410102000520a04000404185404030101d42c1c3c940310fa0540100008024001c5c80090715600b0000d01070000040b544070090b141817045010903a0016052080b2411500507200701203c04010980701e420503105420300d9a12244c6a10043e43c070380005018071031003088004490380c03a01c440100b0344041600600d000d07200820005d40305e40c0d00200f11043c1c0b10058036020a503101d0ae441d00301c3c01c003502c914400d44404004240402010b400c0202e50050340c02c00c0d107088400c1075442e0082561170740b040c8518115101c0c0148040d0707641d03100d40002c07540000841c18002a44041078403240f80d2210014001000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 853347410 1250 853346160 853346173
    0x40617010911030a081e0405130e07060e150309010605030304030309080d0c17090a051309140304030210140705150a051e07030e0f100e060a02071a13050f 68
    0x410400c0c4058582d074201c140c009060302c10455079031003080d20600a40045a05400800ca6440000141160040e102c041c2c2880460030004a4000281c00020359511450081c07180c08075500340300356880300a600c00207200955140190b4080c0e4419880a071003005a035407500800300e00c40e142013000f840294481c0c1e0754200b8040c60240c2690401a0520201082195502018001c90600d440c2c0e10303903000400200e1651800900c1c00900140140d42c41903401c0076200a1610441000758081d0007098060b1041c001c0700890104030179180d00c25400020351001c181c10150144603c120b6070700700e45d9001e614541d494003115031185440d01440104044152011b03d003000110b01180c014207800c03401132085641000080303841003c081c04020000010543e503140c2e02c0391201d104000c0c11204069807015030f00050140b45003103000d41490454051244208004551002981e02c00c440c81c05402c030000041c00440002100300d07140c0081c01003600c00b00445100c001269041c48040b07410480318005082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 853348660 1250 853347410 853347413
    0x290106021204060203040302060912070e01180b1e0d1a01090c02030702030a0303020f0f07050706300b060f0c0105160e0a030b06040e0a05010b040f0603120e0406170109 74
    0x15040704155001e1400d00140800c1094540000c150707003d40354115601074564010201090108100b502c030311089100c1d51500007021031401607414180e61410300c2c1e4513800e46c2c02e80303c04400e4412803480707281c001c0f00d80c80240301c10135138560340500101e10050400710000c6860b1501c07442d40d95101411407101d45140010460700c3d420b44140500c88050f40042c41c184a07690700080e480340151100a800d03d600041c1c240c284100a808403241a000710071240d032501883d040c550355400c0c5500401c800326a422410741002e0401c5607201545594807900720500149031000c82001c0d2030381c502c046810000c103101800c400d140c00350140c83c62415400001500389001240d00c0d00c85121031174503034107000c00001c901c041c5481b941314840a403a008500411140c031203902090003002241d010394941c2c0120340c1c000c01048010341080c08007030400c403010300c240070650194400729070540c40000d000b2164060120078040c01082c201d8030b0f44100800018500d55500c2929603014a10350401100c2d035512801c840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 853349910 1250 853348660 853348663
    0x4060e0408090f04111909121a0a0204230102070509040b1b0c0a06020c030706060b04080106050108060f01030b12010c0e011121160602070b04020f04050601050d0929010602 76
    0x440c0403800712070034002e151170a9201c46003486584102c2a201c1030700000c5000e56805020b200e030007440040f0503c6202a46401c202d44003104880080391103d4001001c200c852100b4000d540580701c9185400000424507014500d4180089000d181503028011001440eaa614544580309030700a0840d0b068078901468240aa40c003250b484288582d02071081d20301074540001d403a103095520010051382d0310704481000d4518003610303070001d01e000e05090021403400703020340190040b240454003d000c03141d1035600554814908807032150b082200000b6100c025807080d005180345034005010301e440303a404001071909441c018090000802d00311010103a00d5640072214549405024001d803090800300742c00c5c1051113800d890511030b14000485d445501c1944800c070500181c1e80490115940c0c02146080081e20303130200d405912607810483c00e0000790a081c05024840d02059450502d030006104044000780f4440c1c8080d9551484210704004c850f5111804107815003602080408546c50140c009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 853351160 1250 853349910 853349929
    0x41e0509011a10111c0801170307020603150406090e0c0d0203030a081f06170601050a08060913080d141e0408090111060a15050307060c02040b04060e040809 69
    0x300301076890110809410384007081c4152411400710b03061070710b041400381c048070034001d1180707000800d000d0804400d0000e440005540d080c400d0907111041070381c2e0b0340d51050710350380c040540000700c503017041052000618040d001554840314034000d00d00c1403d54203000c1380c00c444590300144d00c410307075622840124810410145d58070180450311858072500d07690100c0e40f0b034000c0200e00f50510014002083c4104040f031151030751190318034180352819545090040240d448141201184d603220004102c140d44280222041d8010f503807500380c0c1545407001800440640148035041e800f140000b1000003490180003000c01d421501c0f40440c084819a00303030080340300c001d001c686800440070192554000d428100941c42901b000b060390315101c7c60b01c01620300030008030840045000364400c0100d101c44982c41030030162813820800d10915203a4003810381d00c0c0e516000d20000f00301601c600c00011300c0e1030341040f20140006007010440703aa0b1080f08100841094500b140c0021000c00c0818090034030203d00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 853352410 1250 853351160 853351171
    0x1611030610061e02030c0328080403081821030a240303050702030c04050901150522050c0f16030810060903060207031107120203070f080d11010b041e05 67
    0x58400d490044040c01032020700ca50b0310543c1c4410249000054024810744600c440b40d101600d5940d40500c4000403a80e080b070f02d0304682c3d0b062616043d07124603c07802c00140316542c5511341071090f8640c41a56170500d1241c182074a0103101e0324440006684401c0544034558109404140d1203050102004040d900d910016448a9000041945070a0f1008440008894050a00c3d60f0340300e9a80c000300e03081550300c0980310341044c1003e05101c01488158013070504050b1350003200d12416150010400384840302e460762a24028468040781001513150b104076000860312540514000d103034818041c050f00814140b01d51130b8040c80e8604149a001903840364441d40c9100c440c1c0c061400e103100a010541c1c5c0e404003800c2e440d0b011440c1820940644500c03402c0c03146080c00c50b05400c0da07034000d13035403444203441c8100c2c06401041d03030014004a450500c40b003a50301030405440312a0540408545411a01c44208415900d0300c0100f04a5102c074881c2c0e141074001c800c00712801d40e80c1d5041c0034040d90301c041e20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 853353660 1250 853352410 853352431
    0x3060506120304060f2c0306090a050607030b0a03060c0513080c0a03080702040b18060112050603060103030e180c03040c210b0603011d0a020306070c0b040f0816110306 74
    0x15218a001c01008032002e80340c4604288084d1032070204100c0310724805042c0d403480000c0f1003160305518070413034054420a01c8110b0848030103598001e10940c444e02031500042c1140e0108000c603540c0d03400b94000c0b0b05003603000742030141100d07a2034851105482104034002c01203000064220141e0001203180c1000e40a00300041c0140180700b004242803100511005e0701a4070007244d850b04654950f00030b182c581200800007a5542c0d0402105801b4540944030140401d00d13017200300014000320f004480c46407800a010b00381985c65902c081c0c070f41c0d4440c030301e45540c0300705000c0600068491015400d0b0107032000f42c1c203060300c0e49400e1074001c1040e04103400505401c21503408281c80c1d2045400300a02d4558480e0121286031119008213026120000f0a24810a00240b6107590340000140180e90580200d0855000d0b0712016000d407004200040d0180c200d6840500260102d0201d5214015031485101001d02e030016840404041401f9150101c4890716040c10b6158149000c1000a0700005400c1e0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 853354910 1250 853353660 853353679
    0xc150b090c16030e2d13090f02100201090b0f06011211091009050d03020a110604031509031206080d0909110d1a0607080304120309031b020a05030709020403060506 72
    0x740d030180c14181c10080401c00c51038891130b0940c0310102130150200c1c49043c000a2110300102c0030f940f14003000043d038040e02e0040faa412a560050181c261401d030403036648941d110254090100e00c11b0481d02c16015592651481030005601c120f01c244508030724400c0e005a81404000144011841c0d801008480d0410010038041d202800458080941c202c4040c03003a0071442e94140c0320100d19030312550303100a24242e100e05141c2c0100d5041c022070b22031000e500b03c0ea20b06404100080c080c03400041c01c2c40184810903444500d40354088900f01c0c1c024284070342c484400c501c02e20b0a80c0d0b50340e080503100350010010382d4621500500308001601020342d01384030760b1801581d0000039006100e02c28034040c0c0c0310071480f180e402c140c8441181406000d4006643c0d0050307802c0070b1009900c2aa0708544d0702405003440d00501c3e100307100e150340880c0d0599400b1242021623940140048101206030390210403604001916901001340d140100240c0b840035841c1c40c558107207030045810050005008030481ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 853356160 1250 853354910 853354927
    0x90606090a0b150a11011b05040b0703030f0f060603050a0c0e061c2a02030405031024090c120b0619090e07031a032a010c150b090c 58
    0x1030080a60026100744001800504500050183d9a10400c0c00000e1400000e94141581d440b646669001d90400024485d146aa028401c10160308101d20b034000f500600c800e0110301020401401498001c1c500810990035040441c0c01f01c4965100c10070364680d666108100481c1c0501865600c0036400d4410080111035060250a400c601c0b148240310711000516060f00c40c081c02120040300b8007030307030040064001041d8034900e911080c02c612550007403400324940000d48000126825a00e014010301a0340003019821409001d0348105210081c0a5001c0d09c000f0410321502e460040444080104183c0c40340c10024045000248002071500e00b04180404203881e104110749100705100f104000340c41541c1e00c1100e0550342078009951010f004018840d1980c0d050700500002203008181c804040c0804003050340e602d03050202010103070105841c0e08074014032a00d0380c0d030103450181060100b9141e150f40d0422031108010940c1071803907950440c800182070010000c0e43c0010826005490807442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 853357410 1250 853356160 853356169
    0x90c08040b01181e0917130513020403050303070c14010e0613060e06090c100f020a030c05010e0a1a07050307020a0809040603121d0603100e060f06070b0a05090606 72
    0x14041c07a84024820003c8942c032500c0c603808800703501c08446901981c036040700002d1014000108003912440390350500100054094030489003041204100c44142a140c40c01388142c000004002c214416428000080403400900080d4410a001c0c3d861070b0400d00207162551040c10a01e0003014603038500841c8140e04900025840d412020305150039421201500c1c1c11000341103070400b004141c1c002c03c03050201c0514001800a5845802c580c220004c2c5200041116113420741520000181d1081c0c2c01c020229010f40caa951100303009800200c0c500c42c101c18828648103c588085880c110861000c04050884403001600400d403440c0c4203180d4140004001c0d603900c3c840d44050a10300000400024035a02c07680311400855020141c1c0c4042c01003080301070692036000340b12064402900105142c646000780850703114a41410030610218203049240929201c0140441d402100400360304003155074000103801018424000c0300390914040010f40d040d148041c0c000c81441d844602801540e0782d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 853358660 1250 853357410 853357433
    0x9060e0607020f0402090a08030301180b0d020d05120301060f14030c03040209130611090112270312050a0e070f060504170c101e54090c0804 62
    0x404454404441090100040080c81001106c55000e00c01d443d00240b0342c1004006103040f6440e04088104060310100c03200140c4001c619020303031001d51200781400514000c1403413414940507508481c0c2140b06c032100084503130720a0300311501240d410594800f8555010600410030300400035050b080d8148040000013a0201500c020320171001003000406101e07aa20454142c0c6822803414482182c0e28031b86500194044600b09000410342c910700460032006014808a0300714071000e02c2e510750740c65910f41c050f422800204604028558007400300e004c07041d0149900546803598002000443c0711410303450203c107640000840064501c0c10000c81d900401a10101c0b00301d00b1828803408075150740c543c1000001c414165100340078a0350784c400c04d41e1041490080c3c01c0008925104900c00e400b09640428078241080c0210000342520fa40c218038504400e03114015040e02c0c1889041c00d245400c103108074081c1810030342c4d10740c00d07410011080d071030240c2614411581000200c6040603100c0c4d186030503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853359910 1250 853358660 853358663
    0xa0c050103020c030d0f0605010306080d02070504020f0702030109050d03200f090409411e07120302030307030c081623130314160303080c04090f02090109060e0607 72
    0x41c0c2c04504500f05950900071648485408407040250f580e901c61144020051400307194000303441c291010440041c0000c100d418458141c00401019103080e080001950214a11580c0c0340300502c14180103031000d010b240d01d541d00c6035014044d40100c800004003120340803903120560402c40811041101d0382d1100329666a408855420f980d00889000b041c058151140b00410201440c01311b290a41504071004400c0607a40e454560039110400012200101400d203801c40350b0400e0101c403010b95080304c102030203103104a080e0f41c00c260340c44015818035040c0c0310301640982c0000041020b09070b8148a1400302240c1d074204068030782070001c0481540ca40e03a12144c41448000740c0c00c100007d124005415980e5403940307099981e404611078450078401c051004442c503890b074084585040d1004507805100010700c005000744c1601d0b5440171036a020014200070f80c0790703500304800f0440801d60f00400892100c0c40d0800340c5d552004100041190126911401c20004c40380310442d41961040100c0741c0a9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853361160 1250 853359910 853359917
    0x50a020c2d03090d14030708040e0a060806090304060354030801051002100c050405030c031513030c080a11060f0105030714030f15010e13020a060809030c0604060515030a0c0501 78
    0x61a00176116882e5208542c00503205440200340042d20800340c420180c401c1410751030600810765a072042942d2240b0559244e03413140c009020030702c0000e1096000d64460150403810b2032580e07416801c04c444001090b60b01002c0030940300b411312240b42d0381d01215100e2515003141d8800d2860143c9000b000c621060107814442c00903540c0003002a0f10800011400140c5a03204106000c0aaa00644958418442c181c000c0c0240364165015240c0823950710750206d19210b8000c41c0d0741d03a03442501c0d6000a02807003141403003624240c0c500824140005807501e1940c1da100d0a00d141190748209150040040240c0c402c402800d005002d02c1d10300bc2486002c40e5107034113002c00345440d6000081d081c40102156128140704042c40d0181d0386a0641c0941d04865070001400c0441c3c4810010080100c10140081e402c40d0f02d01c001008454800d80d881a40801d0202c1075034104040301c40038500306213054509803000d035102c60a1182001c07040c0c61011000c841180102804030303103a9601003d000a42c420745051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853362410 1250 853361160 853361183
    0x1b1a0a021201120c180e060c0910090e2205010f0504021815040b030a02060c0601090e0307120804030c080d0e07120c030b10031202010509010f0b060904050a020c2d03090d 75
    0x102501c64020568806d80181601c243d4509040411202d400840f011032141045c060071b48055070243c0788007000c1d100182407103910342c0e40d4401c4424005200018034064040d94141ea0000309200f071049034040840e11401041c103040c40d0041150303c0e00c1007901209001102d9042c4544110f2103110045450001d4034041509030950700064240300f21448040d422060010351203c0300c400101c0c08505135003080d4030803c1645140c03008035a4a016000c030040c401a0381809440000307002d000001e030300502c03a141442c1214031030755890f80180c000491001100e41c45070071000072a0000e004440141000001c01c0b48500074549603510b814580e0700c00a021004e542c400300e01c0062200382000040d5400a51002050340c1c00c0800034000c2004540007852540ba24103400c4d100c800e00e018000040100800d518202405c0908020040c1005026000d0761075082000f800050f0040c02406a0300040110038a044940c844803900007010035011143c0d55042041034840903a41c032004801072940100c086401d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853363660 1250 853362410 853362449
    0x2060103061d0303061315030b040515060d0803090c0d05010911270621030a031407050f0a111204051801030f08070f1b180c1b1a0a021201120c 63
    0x1f04a10009a200c01c1800c00d00071042c0100868401d000ea0301c24422207214204980d0050f40c1c9040c1030f15200d80c800800602400841c0f20307003000e990403041e01c80c01d9400300d0f40000001200c82d0484030003100c503651a0b4503640c3c280000c80507001c0d000e00c000d890381021002c1000456100d0129200c00040031030114020505603280c03140000b084041071003011102a040c0da612a43d80e40281507a01c0009081000d20960f91a8074201e0501480d4645c5450341804400c1240030840c1d0000810381c0300f0041e0b4902400803050080000460034000d01000c079541d03905110601c003a414001903c0c0d00450b88400041001620039105c1031401508150b019403034041e40d1800041880750788001a110201007040c0d11954104c200148c001c564040c0f0100720a200c0d0314a0139010b50725000398030f20115880307940c0001982c09000000102c2440f408907000c0c5918180c01c035002d80541a520903070441d070f0200f50101d181d4220342d2401e015000b030809030b41079424980c4d95a1003801e03160007040d0010005064110703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853364910 1250 853363660 853363699
    0x5010506190c06023123010338040b13090203120f040e06040c0801050f01050f0f030105100c08180a0b16050111121308040b0a02060103061d030306 65
    0x440303264044000d42d542c00c002102050504081c5040307545214241c0020082151425299021a0410001030314010100c03001d12030450109050141496109c0d180c03ca130070031305103041d450384240301c0b444103141e1413a021500c2400440d03000f50390700852401c2c0c00610f0550752020141c030115294040482d4520052001c02d0805101e4440d01c0e200260104602c2d400c9003901016200350382d03606560707402c05d030340305800c0100b5110302800c0721022410340700051203982041c2c007060111110604201e85400180029039880c5e40c051034807011440000300042c0418030f010482c0000490040c60010b407019011384411002c2c0c402c146040c1c03407640a40c82d00000946801119174014883d909045869000c0f101d55042450302c05941100d8651820308280107031941d04c0142c500c0e1042410303a041255803209245072103520801c100340d89a6409000000700c1c0410a001400e480a80ea80036103200c0d407651030250306403450040340d050b42e08128108588440e5000054940c01304d000c03602400c081041300e4410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853366160 1250 853364910 853364927
    0xf0b07050102190507020118030321022205030d1e050904060f06020105060420090427030f0f080114060714030a02160e060303031b040f0e041202010501050619 70
    0x410f405075000d1a0140d07550741080141500c07a00030388503540011144035a01030341c400756020090105114203003440d24425020f400c0b010348030202c03038010700d821034030f0302440881e20260401c0003c2d401041018080c0d41000d00444018040c46c0c1422004000030722400340c0b65a1f00145500100480403c440480b69100e400000041400b18031f110345603500c85d44024040c0408a690500441c02c08c7c07455180708090400429411000a10560501d90b04c84100800380000032061003d41c82c610902c0740004081d503910001252007519400e8000f48100000b07130501606040c0ca81c00d00000307000400058000003206800801c0c12907103166100040e180c404184810351006100c0d500c00403801080e55500040d6501c00c0403030703110090818950710b00550701d0b0b0000032106180c02d50001c0c800300c0d07004207104880c1080290303200d10b028100fa8035034480b46d1424109030320084000d0240742c1031005000c1c0a4041212070079240c8002d00480d07060402051461240301000100e40c000c104201d02c001e846034155 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853367410 1250 853366160 853366177
    0x901020d052b0c020118120f020102040e010902130801020a050909040201020f010507050a110c0f04092303180f090114010c051005010311100e01080c1213060b0a0f0b07050102 77
    0x24100b06442c1c08a8400402e0844034041c003541c41c00b6107480d14440748040c0a003007581c3c0702580010301c0046030070072959100f038940008107564080c41b000c01e0200c4000a45030280552500058030707001c0c00e60620480440c2940024483e0740304024825125611000703e0701811070a85070a8144e0702c0e0303403004034601071052480c0c0115510707120a00c044c0940c008014110894075136111441c804100842c0b9440d14a000c030210361050411090405608260300310401180c00b03640c1000000c006c5030a02d0319510004281c000964100150782000720300707a1a50328400c2d0005a441d49011000c0c00b0114442e030741c041c05022440e2044410107031b066841080c00c4483d0742e074003400740d5664241a40c0d20034050f180038002203801f80130094400740c0790709041d40b041d5841000c50f903036041c101d007040d4019140c0d545d000d84410510b4804000103100098070100850017551550804107200c0901d003020750456848900407445084000c608100d003029103a0a00161a02140100d50350801441c040c4d00a11983c3d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853368660 1250 853367410 853367467
    0xf100806070f140405010801210f030203190c1e0501020c01091b0b0c03040605280215060603070207050f0f040c0203040e091c1206030203030412020a0b0901020d05 72
    0x10001010b03403040e2074409081298503034001d280e5480c9809201030186001c0e02d030016008200400c02c400350743c2180c51450b00815001a200ca4003522840302d90b0408803401c3c0c001d644002030340f0465540b484d501000300c6555141c00e403605602d903031302d050322940c14610016881c1401c06956080c081c1c01e6046507000307140d500080100700741e04e240605680781c1041d542c492070031400c2c0000800b0700d1501c08660712100e040020f5846c1900342142540c2d9038100a40e101081101e07064243c070002d04005c00065044060f40051940410a20300c001e0261001401c050045a0500600903181d4002480c0e5084d1402160b01038401c0c1c04900105000056070740c000d540c0142010f0850081d50b8000c0300502c00d41e13000b042000c03c0c0d952200f6980740e8689941aa41c01c5800b003401c4408805807145c81c2440405440c0003021505503501d4000034a10342003038020820709140256808110b1038034192200040548904070b9040002c808000703519640d01c10b03810018860005014015000e100c140c5500172051150b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853369910 1250 853368660 853368673
    0xd020304230a061b09031410020409050906090d0509040f18061b020105011215091202030415080f13020312030106051b0615060a020c09090d170403080f1008 69
    0x41c1141e48680440d025261030b0f242c80b00081d0080f04000a910b01c00556441d21004d2524540c0e600c1c200ba0054901c50307095028000e0030300444242c90004000502940e000031401b07080980c1d04c03608001001d4414030559012128400b110360b000419103001803012100040c0c3d940b00700141c000649001c002c5c3c03c0d00010170800c44030410078154400b00c1e4401042c1d21426074114a044180d08031407081c02811400900003960340d00040350a510480d044c140c1301804140c4402035554903058040704070216015800c085010b00200004e10041291044103241c19074040c1031004d400c4000e010040c1400c410a8141141c49055490030064040d158180c50700e801d81c0c0e9130350385a004146401a0071403d1840d40b14190013a140000082e00da03002d6400d81d00f0055584494104120301d0307a00042e581010350042c40046001d59603100440384c80b4a404001910000e140000020582c25030640e020707150b81005c00c1400007190b840400c0b942d105071030185181c542e8894a00100c14500c440e441815140b0031f10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853371160 1250 853369910 853369973
    0x5151c0b0d0f080c0d14070b13080a0c02010f1403060f120a08070303060f082a030f0705100203031611150a140f01120803060420070507050d03050d020304 68
    0x100004c1c03480c0c40c80d5405603a0102c40039031040300d00900241e40c08400c248180601004075000701d60072504030000505241c51499255101203441d0004554580410b0003042d01d034081d560082c8602d01d0034002490302003098032000a0140082c0805400e1034003894520340404425202c024007030710f00800301d604942c945521403500f80a103a0240008800290500800040064107003407540107030f13041c05028209202601040000018901204c260a034400d03203d40d42c0c40ba01c051041410744040700000c0e04149050005022040341800407050855104000f0080c50f040300340b00700300c694010b610340005800d9035034030b1491401410311b04032114654102c0c02c0c801015401d034454410200b408981405030303643c01444080308102403194103040c0300b01d0b03480c040008481d14000d540c4454000c00004c0c0903046000e0083c48040380032003411340d10b28001080402d00c442001004020b24049900c02c03070086030303550010454050401c05003106600403000c28100001814103c0011003641103580700300c920b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853372410 1250 853371160 853371173
    0x5071115040e100503010903350a06050f1807140403060c0905010e0301090201080c07080408010207080319090519030e0301151d22020d061505151c0b0d0f 68
    0xa5440c0d0b071140c0080b400c0013400b42010700501981c0b5416403070311140070a061310003951540300d280c03400c0e0000001c0d0550062408103400d215010f042d80703420014185081c01c0c1401341d41e00e404800c252003100e071115008000c003c0340d503003294444503502e8146d1400f0300c0e9501c882d0036405917810040c2001e0a025501243c154000c0c400c1080b40c009989103804111900245400c0702c042080190014901a0020b140064420002c090803442408031a1400d0750703444000b822600200c0302240c094000000748042c100b40f407840003250030074545040050001a695103a40c4005e21340007000b595005010341010315014039034280c42000f0140080c003030820305540d50688601980907600246000003640c0404a20103160244660200c2030044c02d040410b41004260a6074401e00b00d80c005002c40407400010960f015899540342c040020311145802c2000304944890143c400045030041071010101040030440b03070300c00e1580f43c0d440006030714050601241034146403081c0582328035610407401041107113 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853373660 1250 853372410 853372439
    0x50f072114060913030e040209011107030f0201110d051c18030206012d0302150c030d05090c100509331201050103020309030a110312010b030a0e010209010507111504 73
    0x2084800e1040c44d0b41c2d03441000c041c0c003030b90800640019541e51200f080e41c103041d1300800c00781405051181864038060b007654038ac014680c1040300d040d810f09144100f1940c10100206c150703014100074180c41003682c0b0700246540140021050b042000007440c08030441c1c0c0358804c56041c05400d88800d0003406500f8080d50f90318081c4034080c2e840c05400e4402c411550040b42d408140c107410310030803050916507020040d017400c03555a00e90720701c8810006101c02c800100000c0014048a5601140341e203000041d041c1000284002e10303025a59a6150035146a80601103a9203108125198440410303102c2e009403091203041c0801003007101520100301c0001c0700034090b004200707010008500e96a00c0e20011070980c0025610441554000d010500b14036006407242865820400b0840e401c007030704940d81280d090800c1e0301c804010b410020510940c4000c50060b04400f000d40c10081d07140a80b00f0700000c2c101d20804401420070f0b0540340380030341243d881d602254104090b032042292125201c0300342420a01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853374910 1250 853373660 853373671
    0x110d0b1f12020f04020c07060903030311041511010b10030f0513030206010314010e0d030615081005060a020f010e0105010608010602070521010b0a03060e0c04050f072114 75
    0x10000181a5509611854000e00703540038580ca2100020055080c441c5070007070b0303140f0240c2c810b0b02804003050480080102038001d21080c1d450401061450802904035070040c080120f200d90700300010701040f0404090f25004140c01d1900e07422725101040340500410305400d0059101103055107044405030325401a190a6408606c200000e0f00c8100c1c9822407000450307401000740c1c22450041021072000710516564416010000c183c1803184442c142c01d040103412204046551200140074403c02c0c810402e502810ba82441101820318440b4007004003590320070a4402c0f080003030151000c81c4280311940110411800a00c442016a20914060f1400340240d03000128214000180144001254030403140013170f00403151003403412284100c0d809844184031041d034950a02c03001c3e640715000100300440c001d00d40001d222100d244218103000c2000d0301c051045080509102c4a04280d11202ea001002810008140c03000352201c803818916400c2c0f500380c2d1074500040354a40d0794410010354400e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853376160 1250 853374910 853374931
    0x41e050a060e011d1801090305030a140f010b090f03070b09030d0816180510022b1202070f020a140901060f0e0f1f050d061d040609110d0b 61
    0x864a40140b840140024440c48482c0f000c1c00390350501140180e0b00e840e400021080030300b807034050020740182c03e580c01201c2c201c0020f1400010440a206240700e0540b07691480140300d13245003481d0b0955220141d06010740411101c0005131403000f55940301c4a403440440103410346943c265202142c03c42a0448206e01e402030003000390b6101464071a610382c0388280c1c5180e10070080d040fa948011240407403001592940a0540c00003c1307040d42d580c28014405c02440d038010001440c10900507020040c160654142408044060760440d6030084c140c00d070b0303503c0c102000503100c07202400d00c141200a18503029421200c0154082085190540744041300001583c0c0d070760246e6640c0500310744c40c603480c000321000203610181c0c2150f10f250010319980e007480010400940300f41c85401d82c00040d01ca000341e40300445d01c00604070180301c0c40d600034000180b5034414100c9190483e406401054480100003c0409541d800300c0001c001e1080b5140743c003803502402c22002d8400078500758140345010303100310251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853377410 1250 853376160 853376171
    0x10c0806130b0d08090402070204021623100222171507080a0b030a0605090304031b080729070b06010e0a03022b0503072105120601050702041e050a 65
    0x302500c5000345001c1d038001603c0051261003e0312a04440c0e08003043c0e4982c416020400180540e032180042c06203450301c1816444841603038604034840030754100380c0303200c01c420342c0c018001d150304046029540072241420242e84c44000c490800940718942052240c446035001020074074607540445489102c0c800350440311001184994002000421100c1c14000342c4824009000601c203500701d14103292014040700c403c90600d58452050f920f04807001050366201003400c2060103e28400c3c0035002d859400fa0141c02c84c2400015a140ca60701c0c040c45c00b03540b0407070500c0e041d005802070301004408443d02c2d4482d113892051400c1000000244e4540f4006603540c07030722810070302d0020103840841c4d600030400030340302c5010702036a1560300e118140450000103030ba400b507022607018001003040e03d20500f6000d940002c68421000c02d100c810044108001c07042c4042041c100f40d031008140c01103001d080c83c4e92201d02520009018050304090b1041c81d0042c481e03900107030110354000300c1c01000203c805000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853378660 1250 853377410 853377439
    0x11041505160204110c120306040f0603020906120f030a050703030c113408070806011d060f061606150b0a050f07030e090907031109010530010c0806 65
    0x5050045103001c0340c1c030004410300403005140603448511809180c0203200e003480d108552082c108503000e10381500c402d00000c204089460144030300c0b1148031601da0100050b40c103507001f0035043d1000401160040c40800c103190b142701c01c20017180301003100c49401c9076a0740c81803c40050240d0820300b8118086030604000d02d00e082c1c000c0500a84542491008044502c0500307000141c10b0155080d400d550b03400c0d041c08034488403040001c94003518826004020031403500300820f1a01310140d001150300d040104600d000c800306041da647e000a4121381ca9a0b01b40d40d513400207081882214640c0c2c1d030040c080580e1404220045d000801004c0340b00043c09540c0356251580c105510840c401c1d0030010324100856a0300e618024042c001c0240246042c50007081200d000c1000740e481a1102c220f1903001940810800135a1180d60141c108140d90306106940351502203208518401000070895903003145103480e68040403001480440c4c41802072080070a1000d015042c130005642e494000e00b54908a920f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853379910 1250 853378660 853378667
    0x50a0213060506030601030c0306050d05031c05041a0402150d0903080c0408030d1805121c0204050609040203190c0c0b09030a080c030903070c0e012301021e0c04110415 74
    0x402c031000980303218550b94501c80110010920300c0c40c64810705503202c101290340e8551803904144144540b00450381e0384880c07400c407140300002c5a9964242403c003820440010203a680f4645030310419040c0d0102900c40d440085c50b0120b030b0015500c8158408104115100c500d81c00c141031690198694503c3c5840c0c01103203107024822800340300181da100300103001410b101d5900c90001d00710100740c0800310304031994606040011184030118154008103980f1910251104510350310b420091045281a1808000c51007d02070440d100c1d00c02c2d603010000500c1c0702c90390742483c1d50154010000304a02e91040760081c1605410b64400e680c400403000005181c1d0000204a86080c095034903040d659030365500e410f501d541d00041c600c5501d400280074000004a15501001c040d000c0c07444404155810714030b280385148541c11014501001201c2d44850316600811006610582c20300c00b421412030981900f407070130200c109229009440d00c256550001e080310701900644419407614907172035a0040049 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853381160 1250 853379910 853379921
    0x3050f070c0320010813020103090c03060207140c0f10260714161e060615110313031506030f0503030a0b03160509060a090203072001060803180607020a03050a0213 72
    0x5a011505d00800b090300c244100c00c0d1051003520526001c54216502e42d034040c0d982556510450303646802292000800c040e8000c58034091420f600100b5507122004001103500540c2541a4041d522402d40091050300c645108210049140007036542410b01c4c40044000d400100d0ba40f8000610314920701200030400340498200480900e842e029000244e11141010f03c0303e001d04d03c0e204c01c0c2c454808000076000e405040c00610195110f4440c00d5001013010780b058002d003002206941041082100003aa0501c000d01941d42001501c060907104107a0301000745856000540707211841ca90b80e408002d80000214814014100148031501030f0405043e65034200d802d510710052010f6809000c41c0c02c0c502007056000e5030080c080d425540e611010041240d0054800d800004d0b90000c00e0748c4040580841a2134280040e4001c00c081403400842a85a006181d104070944a21800700c0e919a528042038444241d002403026021956034504a1381e50502c108080340905242036505202184038032a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853382410 1250 853381160 853381223
    0x2160c0510181503021207050a0807050405100807030e0f06040519081605100203133e0402040302060c06011a03040c1e091815020a0c0f03050f070c03 66
    0x580c46001c0c108002c98442c3e8050342421400c241d824002040c0040c42c2480960150300103803900b550f600581c0200604c1c076100202544280041000200402c3e20391420102c20010b641c42e05040d240c840b2002200a0048003141c0380c102d10480d010407246c0c5201013016801644a030f41100c611180a280030454007644a1024104c0d04040c0f1505a038200703001d44a05032903201d4020307510311900d40c01c0c1040c101d0b00140c6858101040b180d221404210405038000c40c25403c000601d2780001c1e600030b03000e10a202048684882d259a1000c810031034866030191000307590300514807510703020751010341591030100b489041d405101051440c40354030715540899005a80200c00341c42c0060910b01e440b40000b180140c0d0040100e00400b0000d0b861186206403040c400380504400d00c20740e01c604003018240907414104036242c1c410000303416002d40009e280f0340300982c88050b00d800d044a90600361201e001d41303a00ba03145800006074103001c03c0200c80c00c80007900c2c402d180000d841c200401c5c010050071171054a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853383660 1250 853382410 853382447
    0x40b0109170f1005041235041505090304051507080325090b0a050318011a12010b0f0f0a0e150a0b0319150305190506060102150a050a02160c0510 64
    0x848022030340c45102c01c401001f401481404c4400008040c0a1000c0c03000c401550311100440140010451101002c8032030040c451418007590516440070394030fa101b2485202d200780c194a41400075030055409480a15410481c00e68032480c1c55000340f008034090503200c00d10940300f9044500d40c0781c0074440e102d00b682e040b5900d031400c0810440302903c0c41e9202070518954082164039280c0340c000240100801400c100050301081c10483d0709002d41b40903600300c5402d459060450300d004540310106807044c2000f044800061070901400441d00241068000d80d4180062600300300904040408440445030248ca41c10b080755035680030042e0501056406111007078083c02401d5000c81103400c07101242ca4503903992103a0f00d030b50381e81c0c0510700033055805981c0318810203621810b000007442100d911a0080c00036141c3c842100c0600001c0441c010308010100f07503580007051020210754159200304019030319141030035038641401c6800140b9403017902d101c2c0c0c0c20842205001e41c07049102d80e0507041e2200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853384910 1250 853383660 853383683
    0xc09030115151d0301150302011805031507030207140f072309100f03031205010909050d03091b1205060a02040b040b160206071a090a0b06040b0109170f100504 70
    0x10b4100c0b100c40210000100708203155070300d45140c1d0740a2007200841e40c0076480849540d407441c0700140200c901907141c28031040e12518204181d40f00480c4443d41e41e40d145010714129a18864240c00a00038504050106524248140b041100000e00c1d2189501c0840071511aa5620004454050301145803186880082e001e40ca24600b0005005908800050804000903440c0c601c01a0440301d1a48150b001840c07481a0340c0320003c4600c00c1c240580541c00003031103d1101a1a004d0f0344044501605041541d140301c0c16042c00070341807800030404000c82441d4102680e44814100443c0d043e50243d9039030041c100030400c03810035842290221445802c81d00c6c245850041c613445140c01008041c0391107a8050440700050b0b8403800100300c0380707110701803c80c1c51214440c04484802c0005120303540c260b101d074400c87c011810b00024503610803c111b41c040b4510303c08000484402c8074a070302034800c020110009664101022580f20811100f030750454024910795007610303040e520182c0b405041e041712013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853386160 1250 853384910 853384949
    0xd052515060e130b060127062a020d0305120703051f0602060105010f02070b28020309030309060c0f0106080c010f090b0a27150f020d1e021002030c09030115 69
    0x4e0035150b01541c1410611400d460f01001c80d0301100229240030f1031030315548010320000f50845400c1320303034410031220508416a0301100b20b40031590b4034800b078460742c0ca207071100d42007610682c2207900c400d401030355402c4d080c00c0035080170780540000d0300c10f401c803607488146c0111051441700c9400100c0d2110390041c0784591074640150307100c60400c404070046014031400443d50802c000f00400980001850400c490680d0000840c8a9240c07a010001150410008100385a6001080d502c00c0e050407103100e41d6805822000718909500d459041c038140d400c0c460001013181012a0302540000c003070721030302c00d80c034040c000c01c8032812917a00800018030301c184101d42c6803920a18500d048486105e40203d40c0d600c240070700001d0340d081588240303000d01240b07840300c0020382e02c800341c06c40d14103050009006511455401500d907561211050f4000c1c4044c8a0540b22188200008845070300701110440d034900f0580160480d6600c11070015002c0e60800c5500309c42c00005802610440314200342031004074074030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853387410 1250 853386160 853386173
    0x2030105211b030a0501091b080703080a18170109260301030f030302040509040c0f0902030906040f1707260c0604061a090702030d06080105090d052515060e13 70
    0xb600c11054051046221060004000344140e00309940034500644407074509281c09001159190402d0300c06d40c1120a081000030070080c155080914036042c050781c2e85416050855151509501c00d908450f0448a4000c5542c0c3c194040d04950707004074040d81042080a42d184500c590240c81c800200f0020401000880c01c400b10b0680054401e140140c600383d52800010342d001c90030f90381030320704106801003046000d8401c103140c0c0003020f07441c40940c11468148d03141511804000c00103021400021400b8080161012032480920442c400d180e84a45480c10283c03540c0c101d80180218909022000c100303442e5401d0191a40025140000c02c0c4036071b035960b0340501925146007004c240c0f0381400b592034101d54909580e1841526241d00841e103070046407401074241c50032640442e00e1a450081480010080407400c416060300328200103950308800841e01801c402d070070301450350055030244810200982287c100007004d031080070501403680c6030500012104416104103510043c10154480024607 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853388660 1250 853387410 853387453
    0xb06130c090e04060905060c0d0e0106060c0206071b0902041418010303110c04020d0203091b150a0e12030909090607050927070e031207120311070c06030203010521 72
    0x13281c00c020442920320340c1c8891030b010040c0c9140e403100c03201050a120717240c194820f48922045103c000d004680c6400c40207803103042401c3c0064011000043e4800038000c02044400301c005454000002c0c0e96650b810b640002c0d00940101941507009005040a516101115100d80e1124800076000d0741d1071503400340e0300c04600b4006600b03280102410080aa0b407540302620007140c62040c0940e03a86440d50b00c8600304003880a030285003541c800c0201206480d082030b5274402100758100242d40700f05c03001e4161010480d2000c13040d80008170005880380c141c40480030b412054415941c0004585070f03248140c2c0c40d00000c0310701f40c001480500c00342d46246001d2a07202103500410302c0f4880810511014074040c03030320484015004c20b100b00314030f04850804004080d0310780c42c4641c000d030500d505955506000704106001c4001c140d00c0b99002d0b103155141c10202c1f11140d901c03045050140383e968202170042d400034800d5a06c82c00b1120000c032401c99117900340400f4038002c08007600c504042d14848200c100b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853389910 1250 853388660 853388663
    0xf030509280606030809090609040b04151401081c110a1707050d030e0606012f010605030616021b0d060c05040909110406090209010206041115070b06130c090e04 71
    0x400c800070101190091090101460240010603510700c000818041c18641c09080705024410540c1000301007011030f052a9041036101c1a113101d86510078090102030188440d4031200e07030800400009112030b0014803910500d00700840301c61170b102c0d00d800c00e940041540c081039215412101c2c503500040c82034040d9100351a180e0440c0c60410b10030391181403902c5030b45101000800d03030302c0c10407009100080114660052003440e01c07206180c0e00e8100342c841c10404084400042004100c0c000c1510029000072010b8103014080700d94910785080c5580c48403400441200142c0903a184c100001090f04000ca000c00304003405410307140c00c4583e110401010145904810444c0a20020407803071300350701880c00c01d03502a40b2181d120020880401003110220350082c9a2944100007100403a60040349450344641c100001265460003140800c00751143c41c0802c00701c070200000c4a40411004248a0b8001c202c1608d40c0840043d14203a40310803508500c1c1050701040c5881c0081041e008000540b95206 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853391160 1250 853389910 853389973
    0x304150e010c020f070609050402090307210b0603060403090b070c0b0a210525140f21010b040b1e0c0303040b13080d0b0117010f060f030509 62
    0x1450005008121003540d0404812039440707035040718a00f03504000310744c26100712101901a02d484c11101504950092240901858012502c401195418000c00b402010070103002c80c2c4000000c2c0884141825180c42228001400c40c00700b001400c0000341140304503810303110183c0c2d080c1072194480c0c05402c07400342200e020600c4440460802910380141814a846888041d503888018105072060602d1005c0420900d19040030880c124450010070803007041110542809010100f4017207454000501010005000c00651501400302220040035290140340290700804080300b004490901c0a210f40b0900842c103000601010034894000c0c00e86030182000a88811101c0555038201c2d0464401d14000e90404000c00041c020300745251a441102c500d0f46580103d0741d645c801104d8090040207070380c030b2642c3d60441d0f13141c1c1e4000c1c0d5150446806160040c403503076035242043c491789141c0b4054130340028800c20741c00c60664043e01610303000781c007041c014042000071100602c040d1208031400d091034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853392410 1250 853391160 853391183
    0x2190b0711270105041a0f190906030807110d21170108010212010806090a110f090f0901270605040807080a0909050112050a02151e07050f0c150304 65
    0x2e01c054240d4902502c1c014100400590f140c40704120844010405201580425280e2401d480e41c6004200400001c01c071100d446000d00007415107103520343c641242c54250b103890004001c0c00301c1d071005446118410030303c42c103242030900244002c542e101c80004040100b01031684078000d07046220b0742c030f00b12554940460784a200c4520203046d10821382c410269650700142500050200c0303001c0e00e015006060003081c00d810a009455aa0480c207031020f00701c682545c5002d0072039030342c030a007640404034010580c801e2400c12080c42c80000505480c0080070391b10b41160046040048e012000d0481205030380c5004880b040d49a24019000c0148101e505c00300401602001031107240142229640c2ca0740d6540c0000e0078100c1c0e4108840701a082400d0041d8145c281c040007840014603100b0342641030314125088900c241001d9900d00030500d002d2583d00380b9511030440c13200d201c0003804c3c08501032000c98904594144a49448100b18000550802c1c12190b8024219851400442c0c01a109036000440c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853393660 1250 853392410 853392439
    0x160308071515090203040606060c0203030f1806180118060e0d050a0203120301090513020d030f0c05100c021501050303040e09120a0914180a0c110307030c02190b0711 73
    0x202c0b00200e0704004051035020003848180841442060040c0485041c04401115240c001a64900a040c07100c00f0484e40000d4400a010140c1d400d14803c3e40c0150000392036401c905507201050703002154160000380036400041c0c524860b4520741c41241d9040d00c6140410401005001b4800508442a02e00c0d100d07050041c3d0042e00c040000d640c902c1c00034100e084d101d50500500c00c0940e80007400201d4080342c982c060002503943e403044401600e80c503091066030300340e10700310584000e040c1041c09011806a05510580300980d85c1200200000c42c1c0d080c0e03003612090041444807101c080c091190103500a020134001001e9080440741c03c081c0c800c0440382d41c1440e00702da601050b4401d04c108030002d004180200450118038203900c01e0124112619540c0c100d509901c05490040200380760059501d4a015440b1540244a03c0e1a0129682d06403650346405040150242c81e140b032040380600303400c6005002c1544541314801c1950000c844440c50003500b600c542c1000300d69000d10940c00301d050000c452 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853394910 1250 853393660 853393691
    0x90203030910080910140601050c0c121609020f0403020f060d020705150106020105070c0303050c090307031b06090311100909140603010c0c0b0c070606030b0c09031603080715 77
    0x581220896548403c94540005024100075946002a1155040004414020341d82c040d805030f00550a1030151340f03400b50440d8242c60134480401d42604482410200c0190031808101c44244000f00790b400d5981d00d039501009012480303015030410702540180014801442c0004028040c908028601810034406a042c0c2040340d0000100307c1d0b680d8869080da041003004036484500405070390000b08642d1410130b1000e0070301c0c001c56000030300301076494000480036003410050b40c44180d000b404581c0d89d16144c1c41e000b55208026400d5910444074171800040305842102e114047d40ea01a40d41c103110b22013503081c403400c1d448441c841024000e0200021640c0c00092203200c06981a101c0343c0112130800900341400c44070910152002c100c050320010001c01d12015660f504041040c07000390350764559080000c014038940d080280348502e1941404400181c200103004414011001c2e28070f4803003483c0000041d10250710004081030400e004000129054901d1114004031540011a00410600049 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853396160 1250 853394910 853394929
    0x12030314130303140606030412050c1e0c09040f061e020a0f1205100608041a04030818060f06040b0f06270301020405010e09130606030b04030809120d0902030309 71
    0x1d030004440080c907100b41507040c01446440503185071100d40c54100400800c43c00c0c80001d1000c3c01849504120441d8244101d00301c400800d400010350b501402c3e80455488001912013620320315104003548a00d4a141000d1002e006031b078009a852400280c45c5d40c0c86e0060a50380c2c1480b180748440310701d4071400c2c1e0b41e14002080800400d50f00c000b2072000f11007000d0300d100850f030100014186004108000414071144100070f6440380c0c04c1075201580d603441c000a9500030318403140e00920021051004158000b400c180c01549803668a000e0400c1c012030144e0ba814086940d80e62030b0001401040301c80c01d02c0e034400d00b0784d1040a080d641408bc140c00100d00550b0009500b030b0300188040c05072106800c1250f00d10441c61108070000c5d454545807a0008010780d02c0e10081c0d03032240407a0404034641c1102ca04c146003e00b80e00c20414047c213507690034440c03909035003103500f50007290071000058000324000c14096a80311001050a00f0941498038141c02007101c850202d0f09032004202000c0359030b40d00c0280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853397410 1250 853396160 853396171
    0x2070b04030b07020f0708070b09041d03070c1703040e071206060509040b03030c10022104120806180c0901050c07080d031805150604090609030206090105011403060112030314 77
    0x902e600e04200318001d00c0d0a07880104405ca5402503241488a98800300e0301c50110b50040c0404c60312088180d00160042c28501145c03c04c0d8400c584247c1c881e0040400a001002c0c01400c050150941c1c07030002560341d0180070b8884040350000c20090000341400b02c40c3d50307003001240c54050703010540d12070758804070b81c0c5982000d40480c1000c00d40080174034040c0101c030300c0520190040c50a101203813450320364803503656001c001500e40103d251403034071105190700078009032084800016420942814a1920071103454480001c1c48180010720031704210300000084004008441d0003940e406903086142d8100217483d90410100702301c510840d244c1000303104007a04107500500302d1940b02000140c22205005240c0340d08481c03910159010a8003c10361540c100c030b41074020413965a40c0f00c0010000c0c14100c00080000b0301d0007400c0c80c20b06500090305803140341208000c05c416604c8030b8801021000540f0380ca9410f83c0900010b0000d03850881000380410b119040100300400c1030811942c00c002c00700d0b02e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853398660 1250 853397410 853397423
    0x61104150309052404060e0f0d1e08090307031419091502010624050712020a020f090114041104030b07020f0111040e0606161b1e0b0901080702070b0403 67
    0x1002061080074066001c070005020030705501c00030306240404d141e0900a0000d00101d98409504030440020b203c800100c0310f1341025100b04608100c0d01901509452442c2c0c0800d603801c081503883c580c0102c0342c40380101030180c002c3d41000d0540c1d600711851405150030340703803544040c0113000c0302c52076600c0c618007522481c2c0c85108120b814a18a0030718100422010411681002c07420840921125042e508680c2407041c829245071a0704001c0d1998440c4000080030380103200c002490150340031a250100380e20072189011302c0c503c920100142c02000380034006426203012001188c5140960000c900f01081140341414541e49031200202a20f04460301c0c40560054111a42c02c00c4080c808c1200307134a0342c82d1400e0300342807c02e090017000c0c910050410b80624800901c48804050f50355885a9081e44203950601020240914602b01d1002d8030425041c50f800b040845242d401c40d80500303003a541340110080c1403880c804011211742c1d401401201c1980101070002c1034805484000380040c600464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853399910 1250 853398660 853398671
    0x42109050909033105011808030d0f0c030b01050406120b0904030905120a0b010e19060f090b0301020405030c04021c0603030f09120b0a0e1005240604030b040611041503 74
    0x1108020741a18584103000303040c03400c4c220a507940c0d0460098105545003842d1000c01d040c020005100f00c00720b2600002c1c86031002107245440401140c108652140101ba41032004c4140c8440c2681551290b034955800708800703000c01d100b0584216070011442c0070000300401c000100101082d803404c810368041e4000b40c48030601b03100d11708000107003051252032940109031360b04882d01c0c0c1c01240e0506000da60023070b00420010030070001d00411130095071460703400c040080715070700c40f4108480c0c074480c0310f20001c20341024074241c210325041c800d440848202401078030420144804000007548101e400d01c0518420b1082000144031600c1028042c501c0303030b01c1d004901c130000c450180444507540d0240f0b458850084003040098209a9401d8200031203060120321002d0701c00c81c032401d14900b000716a6000e07142104011108c081150301c11180641d00e200300541c6d00a400501c04648160301029101c2084540414006a41c1d503102007007041242c40030342d04081d00c41c11200ba491002203200c0c40003e4441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853401160 1250 853399910 853399927
    0x902030703060e0c090f010c05061314031e071a04240b0105161412041a0307200106031505151f0c060e1608120304210905090903 57
    0x14842d00303001d0603418810220610f00703403083c0c1c500c1384510a41c15008200380140c0b42031302e07402009030100c030a0740081501d050345410041038003074948500096036a1442030309440c080039004001c6425500300c543c0f10850320485c8070a88856a0311802081310342017540c09840650303404845000303019034858a400c04420700d603503201c1e50350b09485441c41d1112900c0e0154500140c1e81200896051302c0f64003007011468001030414080701442c10704808614000c2d01500034000254034000e00c160782d1401c0d10420726100440602c451760108031481e0300407880c03e03144100d280240040b680154014180081181d84e202e55914100c544403281c1300780095203650a11400810004441c0381020040c1d80051055805040c0c050b0414401c10404050006800d40340c000d10029400075000301d440207080b1028120344030030f0451001075a2013001014090265107911032030503413080b00d005139004100c09020074142c040034401400c44d00c0040044c003001c0080004c00792546e41115220714a07420180d921803a09 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853402410 1250 853401160 853401167
    0x60f090803121f0302030f0c030f0f0c060f04091802040e0105040b0a1a040c08060310140f18010c1107080601031520030f24090406050702011509020307 67
    0x140c0100c503003a081400000350381d01c1c0c0c0c0d8aa15a0208000340d4410424840c8000b8071603a44840d04060b415014108156106440000b00b4a040c028168219120051a60751443d241d000303424003880c282e00f20350307040d0030f040c41c10724041c1066500e0031120520b050b5440103540c044581c05100340040c0f20b43c002d03507a419483c1c144a40710a00b0300c01c000078080c0c0d10785a0344070b80400740c0040c2440c24483d550760f0700352170161100800b0b5400d55001b4000704041480c1e0700c0007809030803040360f50510a01c250318900c440740c140c5010f03c9002940302d0b0506600c03a01d503102e0300116410b0050007400d0070202815802c10380c0c038090084c0c40440690352500903e0803000100903084c0103094001302c15590101c0300410024080c6940341d50008443c0e900020255100f28560200114101180460305004820b101d503005203866218051620302030444a10303031034080014000c0c07074081122940a81c00500080c0401d600350846a4004c0d024400040e07045200302c000700650000f5045446059030100400c00f01c03980 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853403660 1250 853402410 853402427
    0x60609050d0b2a030f011a040308040b0a110a1b090b0102070b0a052106040506041802010e0f0d030503040b062b0602040f081c0e03070e060607020406060f 68
    0xd46501050714070315122031110400180031030344414418074002c0b82c1c283c8008808084100400d0000fa600c2c2040e8550f924051005e02420810303000c460001988170007410121411a940001600d0515140806105468101c0c00703a582c144480c90700340c180c05150030b200d00c05540e446070680201050001c94001c0c41c481c0d01d81c0000d503050b0700d04035015044e81c0c1c00044407404c441c940c1c00381076a10030440b101103c181c05011440700c20348580040c0c544004a01e0882d2500c01c810503100ac201d25074852003008140d0b0900c0d111940504e440e03103c0c0c0340c05035104000d4250342080c0644100300c0704c4140004100c0109407a07200307800142010003444200138512041e01e810406c1112007240340240740304813032580ca03042c1107490b000360311107040308040049980540d00189445101644055520004503845499140661665170140303020142c0c1140290a000030401c0b0142c020403030360b424440494500c1202030001c9600c4a42400b0410041c0d4550052001034a51503843e0310102ca0b204c44090460034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853404910 1250 853403660 853403669
    0x504061104170d18120c1d0a11090a0b030405120307020f0f07031e03141c0b030106030b180109021509030d0809060703110c070801020a0e041a0d03140d060609 70
    0x7a411400c2c8030300302240f10000266011825060100f404c5880c00c6c2c960309950343e01404800020450310000100d11018003032060440100134031141400d0074850b0100d202e101d901c9588000060024402000b4003406150300c140300c3e0f42140c0d900c1c0b00c1c0f040100d820350812940000103a100145001c014402446050802140c92005029540c10750380c0d40c02c50400388984103400030003039204080506105003900440a41c000d0b00c187e66031414081242e07007107520205c00111050804030703030044a0034148141c104032170304444c000016488080c045a410a904502401690740300c00562015039078506240b1400301c0300c030f44500da40301c0051091504006410401030180b0141c0020880c4146010440e40c1e400501454001040719000b00c83c4496402440c0620303540b40710f40600842c5000c8d0550080c00560000d07142d040c440503100c801c00c010754581c0c0340c0d544054444428446498140034220b6615184242496a07101e6640640001d0680184808070b10641d250002001419007040382c241c09030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853406160 1250 853404910 853404917
    0x106090605031903080601050d0e06010905091b100903021c0b06010206011a030403170a060e060f0a051318150b010e010e1909060305010203090c0a080703060504061104170d 76
    0x5404429008030b01101c035400103800d10405c2c40c0090805ea21500440706034001c0c8030410403000000144044e81c81c6402d00800300d50340d00d464085030348440c00080760301c0c4500c10100c0001c6110b074218103100c800c110402e140302c04e0200c030000110042c0d444500c008101c5036441c0840b180340c0b034036043c0114038101c0a0002c40c103541221f4010301c00305141885c85031803011105c11156480d180c6160440d038480070701c41e041c61084104002e2192030076454002d4021104178603c0d2219603207950307081022186403204001d6100c545102c040010b0b0038148600d41da01c2080c1500026a03816002c003003800c1110389602190f18807a08012010120b0300d601c12800601801e19015901d00780744000a400305000d520309610a0040d83c0c00301840300c00b064161b1003d00040103090003c80c0ea00c4ca0414041c0d0000e640c400c00900482400400a09001c0820b60448280400074030020389107495400081c100a0410340c0c0f92516040c10028110071a4000d100134288012140341e0528103800140c1414140100e00040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853407410 1250 853406160 853406173
    0xc06041a040201020d03020c0307060f051f0503150406020c0d0c0b100e0103020f040b120d020f030306091801150f03020907110319030b190510020d090905090f0a05010609060503 78
    0x2d80d03400142800052618240180e44440c02c00c481d81c61400b6a6100620a50601e22030010803080c03a00002e0250641c049120102e041c1c01c2407003495031099000e80d942640c061803192004000c01000c560b009401124014500208006001e08100c0041c2620003c10403001c610b00c00c01c81c8041d00617910103488080c1034007190411640641d00c0c01c042c03001174440c02c1905034249199603944d0011705c011000410304200b19090100d544c3e120300303507008503901601501c807000c00822004000c9134800d100042080105e80e66030300c212205000306160005103996500d0449491000034808403000d000d540d041460701078514410481241c900900b008200440e0807404241740e10004142d41c0100349140c4008421095214101d00528114910a50004102d0382542d00f075050085070384140c40055411103100444107405a0740c0d4101544450005104c2c40342c2006003c0c031540c0b080e9007200305003043c2c0f50442e002d1100720780740000c20750040e0b45503507488608000400b49407041c81d00505058014042c2c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853408660 1250 853407410 853407413
    0x613021e011d18101a0c0309040207030c0f030503010918021012090204090605040218040f170f0315130b01090b0a11060c04090f050906060f04020c030c06041a04 71
    0x424100800b51040a4401c00306442c5035a0f80e80022903010108a000714262030511194581c25816226410348010740b82518000320445030120b80201812100442c40d2800120512009511074041075003040ba0094408002510340300303070422164065074401d40c6a5040c90002c5048810340c07444510308408a000c24801a10b44641071407a01045080140c0740907014104680034109201000350301c80c0ca022070f02c00400c034943d0712070b074003031030080d90700f0341d02588202510380010105032030107042a003a00601380002854480d07140840c0306c00340c0f5040d0414201c05d6083c0141e4000b1358107803d041d0720b1018204020305081c0200076841c095030328140424041ca00001e804d0305501c1c004c070070000400180309826180a000c64070965212102102c0305464030308803507036042d040740c0101002035043c00c400814011050080700d015035000340103441c2c035072601002c1241c0c60300d50500c919046a028005031100803401c0c00035008008104000d8507a500d040d24088070141040b16500041d078102e40d048c0b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853409910 1250 853408660 853408667
    0x609090210030915020c0312010806071b051005040609260f030604021909060f23220f0602060f15060f090a090f0e010b0310021b0613021e01 62
    0x803070304511820001422103250420b50031004144d03040c07101c8a8000a081200a41d0000c01810350b4503c0c4403001031140d0302c03015000d44903801130716020f00007103000b800c049030390b43c002c42c900254503c56821101196034840000d010340c0c0080ba0161140742c1d03140040c800307000b1005072003540340c1254001c0d0003c0130741440c07003015240607040c4520040207021001920301e444035030444584143e41c4200303c8140400a1008054400d60300a0300c00048481e00d0718442203016241107980e41100f09010f484018030b03000f644d00d4030b40001452802124031100c50800c450701c00e404050240ca00c546c0101301d010b0401401a20740a0040c0c1041104001c1c501001080314050122209520080311f00a82d5807100140712000c5010309949241e0149103407100158041e003940c010070f080205240280700f60700c1c0720441503088079040f04865030184c00542001c000da9895500410000b000a803c1c00c13a644107003258545400c00466401d04c2c00e2035592250b400307514040d400d00c50300c02c800c880380d5100000c0c0e140000707 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853411160 1250 853409910 853409929
    0x40b0f090c060f070507030f06150e1b0f0904050c0a0e010c08120c0403060f200c0a020108060103090b0907330f03090b0a1a030318091e01060503070306090902 70
    0x241c80850081130381010044140506401140c00001a40769410b941c1424002424064a200400030b01040001b8034080c4220b000d42c410229500310a81c00c1e0040131040c8800d600c01080449803070000c01000c052503595101c2d940c05519180d940700d485103130f4110054030002c0c24080d83c0d03040c41034503000d040c00980588101d42c83c00424004110b05502c80d920300f0491030096400080c4031505000b0040f5404641d58490507074040e4000741d0441e01809001855800d00c600c980220319500b02c0030701d00c005540291882500004189000100e9850b81d403140b089450040d540e0840d6a00210001c1080455220042101146a19170389042030100310807045000171259041060200b00020b011031113002e54049984560031251040c02c038078002c4410002448010a140580b07110715000401c5c07428000181d444103002e003000c1c095110000000c110f03035107000600751018800c1080071884a800b41c01c0405000740708546401e0f4607401c01e030388040c00303550864008851082c601408000507a4610620 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853412410 1250 853411160 853411177
    0x3020601050609130209041e020a0e0d0506040b07021908030a050117070608070c02091602060c0307051c0b06041509090203060a1809050105010f091a0604210506040b0f090c06 77
    0x41c0d51b002100d0103c0d0190480e00250408142d0742140f110720b41c00c4503001020003482c90350316007000d0142d4500f0030001d00760035800541958001000100010b160485864002006004859907030400ca1880000d2181c000350840300d0350070210910400500c94045d290160842e04040383e40800c14a032800c2d81e0742c0b400d104450400c80b900c07000c1025140181101700e143d07500617004100b90324010541c1c4020902080e402c8006101e4440010b007104000ca090368095100b60380c0d82450246c03010b107403074040700074024000f8403981e450007808426a04c0e1402030000b441c4060440044820341c400180103950141d110354055401002089400d507a1001d1000680f14040070217024000382c80354400060000200060a562034080007140113840258828122a070311f0001384000400401c004003003087c018069a00705209001c14000c4400c9031004694240910313402c0c0c0c20921460700ca09151510a0390152100070146003400244000c00c0509540400c81c0001090440603010216116124210b403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853413660 1250 853412410 853412449
    0x171c0c0206031504060b030402090a05040201050d0c02070510020c100903030207151209060509160f0605031b0f0910111005060f03100c0315080607050d0f0c0c03020601050609 77
    0x28100c4041c14a00c420980d00203030040000c1c944507800400547c6c001e490581c8145164000206014454000c0500c1554180e4800303040c502c0e00d01c000c1c0050305100d6565001d6004840d0003141b2611f49e0705480350446c1c0a0b038000c00741301c901c01c018030120440b290b00c500100044c410051000c41d400103100780031114100761040c4910403070720701158910010b40c28640e0341782c00c090104060100c141c00071401641d0202c1502c41c1090150003221300900d00d44101c078441c5581642c200081805000a554041e040e121800c0c84409641c1043c6543c2e8081888218030b000c002c41d606c0054100344d90009196055820300c00b40b40444500d000d580c071703003030122404042c1303883e1070000f103080d02c651141c00500300c0c010f4101c8406c00c0324000c042019100a41000000a191003c503e0003241c00203400c00440c3d030104054a41c2d600c1c0c0c000300325082d50051b00100070454968400395007490b001e00c203003c510180b680d02d0006001c10b5140081c2401410380c804c0d403180c038007807004200715a41d40e009c3e038041c205400d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853414910 1250 853413660 853413667
    0x20a0308160504120b011509080c040e2b120203040816060e010e061506070c03120c0b0c0316020c1c02030a05010c0518011e0503040c030804171c0c0206 67
    0x5412901c2d0f01c21500000782c0700580341c12040412071350030380982c181c40e22041d0311010807041003011134040701a4400e500741e40c1c0c4451034901040c2810380c44903002120701c0c1c00b9503000420583c4450001e00d1507030900382c10f49404c040c41100e8241e1090f240a0074450a11082d4a18106511008500c0c010980103460304042d40d42110104035140c2e00040a4000c0743d4001d0007207018a2021f2910b807142180d0480e5400b00311f03010a0003900d070100c1111001a4400140b0700c180d42103072940000302c0c01207480281401090742103280454200310b100e07403241800c2d0714241d07071700c2c03911154409040401c6110784040d5440003c3d6200140c3e1140d1542c1d9507144c1e801c80500490421780002840c00b24800000b038403551803c4010308600781d02034000d00c4541000030391541644041c0004403000105107103031800b903801103200d00b401396100d1b07001160001e0080c43d1507502141c4070303103c403500c2794001e80c80300e030091004440014071a4418020007404501c0481403402170382c0c1c4450054104101000024415007000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853416160 1250 853414910 853414951
    0x1090e1b040e100518010609110724060b0901021b1014040e1807060f08060913050609100e0c18070908010e0c120307020f06030c0409180210020a0308 66
    0x1006141801a400b01c4103104c1401c092820208800d90b0301030350811035091400100701e0392124002c15800c00d0682813071614091541d01c0c2c6e41c1e401c290700060000074403a04202016412050b01810300508100f0b134a840e0b4640841002902e003400348001d0318141e101c80c0c46c129034640c0d2058143c1d40d803651b0701d090250341405111031861861040343c20416074141860700f8040c044038100f4603201c7d0021004101d6060036116141a503c44e1801806000092194000107809040c40009107400c0900c1441c41540c00c9a030390f4880303091400c00c941c489015405103081e4501403070f00340500001c91400601070103105400e5401b1035402c0080003100c081c0e280106011a4020f132260503c0c03402480380400800c503261b4400c0e42c450710f030705c009011144030342c00072085810107100200c00c540c00a0b50050140f10004000d4051201306d0300001c0c800080b20b08140b00c0014a98403e000303001218104004d10895841948100100f1804c007071244000c542c0030b2548000003e400c019a2500130800d0345003610340075600e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853417266 1106 853416160 853416163
    0xc030313110607051b010e04020d0f1508030d02030c090d05251203030b011e031e020f03180a1406160216090207050c1801090e1b040e 59
    0x801440950317022188401c40c1c1d01a01030426807000c6040348002130498200940030700c0021f441d110502c0501c82540300f0004d00700600d1002d080c40c01e04150f00c4d40d60340c0c001c803030f00600d07550790010200300310b83d481d0703819110a05401000b10084100510300b036074455103051b6007404a0940440314100441d00303134203141e040c0c4070100665803c0ca48182c0b812030280c000d06081c1030511111480c0d03c080340b17044182012100c203042d100400c0080c1c0c100760700b60f003102c14444241034003071043c480c0c01c110200050440e60003080e9440c008103150b004c403c2c1d590900180c50001030070643c103024000213102021802c14410300f1842d00003245c040d040b1710266102e900305a030011072003001e07030000d11890580d50b015001c60340c00761048403170301240c0d2004503400006903e084007001c10324400400c00a45a1f00a09143d41280006400c0f10a02c00d00c8586c08001c84040440c411900e41d08003040b044070 = true := by decide +kernel

theorem cover : BRFrame.Cov 853237410 853417266 := by
  have h0 := BRFrame.cov_init 853237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853237410 ≤ n) (h2 : n < 853417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
