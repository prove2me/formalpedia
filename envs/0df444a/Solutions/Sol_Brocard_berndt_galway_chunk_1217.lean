-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:49:12.915493+00:00
-- url     : https://prove2.me/submissions/4059190d-579c-4b05-8ec8-5495d612dd9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 218705035 ≤ n < 218884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 218706285 1250 218705035 218705041
    0x1507080c1605070303050c070e0f0f070c2001020d050f0a1b0606060f0905040c080c0306030a051603050d0212030a020d020d020d20040605070b07020f030a030203010905100518 77
    0x41c8144216410b40c814210b40c445540c078640904079030006443c0c00e18a005000e400120780002c0200b032407052980ca43c0c2020f4661301d40d02e40380c0c600e0b00041d2100d410418210110000110b480e038640c405010011503030074503000104002331820060006000810006005601442200d00c05a074a0440c50341070102c0d80e8028076155203c0d0a507070b01030141140c3d08190001440c60780014090080c10341540c2c0e00e100680d2100300740011f40c0c0355007940c0300010328006c0010310388290b030402842d0884802804d41c5c0300948281c0380e091070301403846000020040031907410801c10208001c18210a6854000342220046030032040d103403408014580b0884540000f201403e10626504070745030307404445011900c40000c4a08880204000d040401c03226910a440c50b171050f240400b5542104c025a0b149807038504a41d0340c2c0001c0c0c04000e8002401d41c071605016080040081c009004020141c1c0c1e030060304c940c54800034a00741c41c8050300c010781140c807000040c0b09a407140026064035007202c440d080041c0e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 218707535 1250 218706285 218706307
    0x9090906040c1517090a1b0503060106030e0d030b01050c03072a121101201e0f0718020c060103150506040b100810091104030201080603150610030b130b01021507080c 73
    0x984804000701891415500589546547d01c59101030301c4099040755040da8071840e090b000c880042c0d49180c1a54013000c031258440380300350000c0c40c5032801850b01034100210f4540742c0c1e1842d0400f0300100c07102c1d50300344188004411030344421502c0500d4070300300303462151a0200d021420035903401d0150070740520b00c4080000380d0090358402105214030145018003e800c01d81d15484007181900c0381c80d40700340403001250204001a042901003d610080c0c903105245c060ba241070450110200000d00da002d00c00c040c0040420311402c0e000314055000c09c107495031500c11904c100c441c02060180304d5844c02c0310100c0140c990103c4d0207010846800d0a90403912030b120603074240101b69021501c03550601c030301011800b2202024100300e83c070030380394080552208010551540c5103441e400d007001c0b1700480010710300d2902d00c08102c0c5840c2e181c1800035042090344c2c081507000c024006501161520303003480c644c0650317040007486404900c071090380445061509000b40244070141499440751004914002d5003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 218708785 1250 218707535 218707543
    0x2202090c0c030a080f090105010e0612120403030503040c0b120103080d0b030f0f07060e03121309020703080114010f02100b03190c0603112d09090906040c151709 71
    0x207096281c0841e038803903d42007401890311004880d030f164948102d07004900b107814140110f03416a80310400300340300c81d91020b0a2240c003010880001e4031511851010b0801982c00301c0007040694006d6854590b01c1c0341c58101600e90000b2a801405a030400300901c0d241e60072903808640c1500d90103d201e5a0354065018008060070000030324507418080d1600c0c02c0260100040d030780c0c8603607030104159807420742e490304207450008040c0c0c1c00035010b0304400700138105a03c508004103607010000784051122915210b107482243c00018040340414080001400b50803201e1014811a0030246018410103420100c001c1d11214951040c40c0e5042e29849880d9050354140000c88120001680103402e5091368204480c03c2400c4d48611030100f4a04940f403004500c0303204c102c030001840e0001000c000180322040c21030025002c0e40000e10a9410b00442196903240300e00d02e4080d804000c001c0400f03081c079003007401d207924484e88a0105030110311852004150803809881485250f42c402040c80c1d52403041c50740c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 218710035 1250 218708785 218708797
    0x3050f030901060302032401120c03051002070516180b0a090903030518070506071b0f14040b010906120f0e010c02070f06020a0309030b2502070306052202090c 70
    0x8910008030030001907020550005048138021011602c6501c050b05000040034580c062012407154401d0041c031174003500c8656152594801c0c103851851554030b441d4541000b82c141440c4000c04d4000490303006000302045030540b4003034544115030700b00f450710403202c0d00c502042aa1405140d02c0c1c1031080c8035590707103a001900803d40c044d014003c81c00d661030010024a8115440c1d1280441c0300008090b442c80000d07407030107403640134011916040d180d0301d5802001101e0311810250009090700882c02d043d65501c2d039801410b0320b00446000ca0310b248104000d81e01052040c504002c4c940a00704000c503404070f04220350300814440000c0107484040c1060140c5480c90400150b07600b0710384040000c0f640050341004480d00c1e24260818076444440407621904601001340004840d05420f10120302a840100d030080c000c201d142c031402980c0078016004403450041c00000d038200120030000c2c05428090300744d100074982d600701d44401e00740516000c10303520b0342c901a004140350000500400610411142 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 218711285 1250 218710035 218710057
    0xf070e040525020724090803032707081608011a0306010603020901020a0204051807080102090108040803071b0b220c12080d020f07060b04020a0906140904020309010209120706020a020603040305 85
    0x21480d005e00440e5203401503001d010000802015001860240c044140c9015003092141314210b84905142d54108410741c14561089014910000440c540108005408100007030010500945044800d900311029000300c0740b800360f200d40c0f40800a62300800ea06055503014200181c48985520040b8603000404100075081031070841801001c0c46426072424200c0c140904813600d454a40f03240034240d0059460017401301e545200854001903050000d998801283e02e0903e5800506607090b582c1c40d91009000d8070594400c10500c0541c5d0462464003c001c81d0907500700c0006202962282021941c1d442400d00e16012410094100044031080310420b010542040d0b4403040c500a000856a104400031204145402c2120456080034000c7e0707204110140c94002c3c8071361808809950458401004002481c004c000814031680c0e00e00c00381d0701510000e0001a2901e581d503052281d20020f620506441d03512203042008100d500156101c00700e90b059811a8880d103d030b04c1c00781e82d540203c0d4010a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 218712535 1250 218711285 218711309
    0x2060613090b01080106051009030f031b02060304030e0301060609122003030406030c0f030507081605090d080c010c0504050603180c0411091009050f0d0f0501050f070e0405250207 79
    0x140040150880300503540203e500c440034900340c05083da92701605110042031944007401900c04203000700c41088000b0f040740c0529403d04640d0707000481c5544210740850100c1c11403010f031119420240701e1403025000343d0800e00300650401e80034400b9130940e4900107002e88030740e0400024401a280c051303a401c1c3c101408494590707860b004003502034101003040c0300000b0702640d1000806407280c0501c038000c2d001a2281e910907106c0160003039594000351004c01c2403100c04c206000841e103d8501102c1220302a400a42d01c900e00322800f10b0940751444452003c1100c180024481a41d81e00200c0b80c10101f454094103950381085000d504001c0c2800c10f00c1c0c1d00925242120a00000343c60062110080403038814038800c044403004e580e44d5901340523880c7c010700c1100c142c00d210300303100c000303a0b42480c0140030b0011489419070b07540d420f48a00301d9142d40070240c00018030116580200215441c0d02c81140c05101c0c501e00217040c29542c0c0c5896030108210100a00798402c2d8500034400c0402518440b1394907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 218713785 1250 218712535 218712539
    0xb060409090812100e0c07061e02071502030103020f121903050403050d2109050307060504210e06090d1b06050301140f030a3804031e02060613090b01 66
    0x540d500c0e000701400188400c510300010b0014804000130009031020203003010050344804910001d0f03500300d000111120b82e900c28030181035688108201c0c903211100607015940314141e1401070f03030f414201401c441c00705005000510060740d45114031407240074107850000c4030a500c2500c46240201101c0f00d084592100036040c41890750000c020029030340500102c030490110102d04950100f84070301041d00c44c941c20400d80070300580541000c2000d5000e40d085a0400380e0580703c1804803401600e00322a410b40d80c61403142c100026103100407400c004d50910030846e07000400405e005200740200f50780302d0006602d0340c0d0100080d0101c2c1c440c000c10071204031081d060301c2e404050150744c42070080c1e803040008400910207502d0301c9071407189a1394014002c0c005100c2156600d5529640380600b100d44112800010000406c4200d201e644500b603010345001c150900e8200901803201891488880c5540707004042c01680c1c0008a8540152058444c4451055420240002000040c4005003080801c1e000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 218715035 1250 218713785 218713793
    0x180b130f0809040605030c010e012313090b03070b1806040305010903030504031413090b040e0f070603111219020c0f06010806011d160201230a0e1b040b06040909 71
    0xa016030b400c0c01c0d2820003000c0c0d100e50400d03075919080b501050001c1d4036041c50b40c910394851000c50303140006101003200c1b90620a24200c2003500121041c0b02200d5095030100201c14140c000d00c070200a042d0083c000160500300c1d4104207200d621010f00c0203044240c0207e42c240c84800c2190003c41e0000c00030427108980e4078008001d0300007550240d00007214480204a000020011540070380740c08506280d0076413501d4a18009031406c2e51010b94071035940e0955540c0308c00c041c00064401e000fa4400390103058201800a0304540000000006000080c0448405039604407110381d00040c0395100b8080d2003120b42c0201010b40b090702e50051007401040381c40c903d0804001b03955410b0f00d041805861b00c03680c071090342c8502c40500280000c2000482d00c00b041c1c0780d180d05904000340550510010901c50407200e806810170b405034544092440c035602c10400913954030b1080c2c2004180c50005061032008000403841048401000648076a5981c0700c008010741d5107a080760014200070405028070000741c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 218716285 1250 218715035 218715037
    0x25050a090b070609050607020d0c23032b06030309060503040f02041104091d06010e04050715050901030c030e07090f0b03010c09241403090a05010e070810180b130f08 73
    0x3012540d9206d010046104603001007a9100c00b42c02aa4074103006400075182d00f0885124a002c240f001c4040300f04580e03241000784000c2111040054100070301384010f00d00c0c140f8030440700700090b05003031034014140b0000e584101d14200b102c003580f800035240e4445040c014003034042114001c0d4000c0c5440324010078140c48902130800c40312590420400700c040510b100c68001c0031a000c5100e40d0b04100d00600a00c5084507419803c140910f00300d0340901e07250f6403551883c20146010303901003a0080b5416501e981e040c0500c3d4500c5007545800d019008118084940d01c20142c05030004007a21802c910f603644074030342d1000d4603028004009010f0180c101d1809444600740c0d00950140c21032019030100e8005610f440000a0445961100100d20f1112070000307140d04081d0070324800340103150300300f00410310901a00300d40c103031414041c150592405129a203080c40185652811505005d40c00110140ca44600348415801584010840e5948003081d0320720800c0171001029220b112203043c0c10310403000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 218717535 1250 218716285 218716301
    0x92f07081b070303031a030105040c03081b0f070e0601020327032103040309051801091a0d0302060f01120506011406040509011503050a05040807060e010209120a0b25050a090b0706 79
    0x40e064680e146c030b000c0034076090740c004440141403c0108030381000010b003c9802031018880800d5944000d0f00c094000380e0401c01c40c0b28610055510a0405025600310f01104d9600f180f424002945400004c105230380c0c075006249039040b00c42840d62000b075a152020b20016034004110601d0541000b0040c041d0049904159405c6d0000b44096001058030300f00050b00a811010645400c0da0503882d060140001d00400b01c445101030316005980311203a10703100d030390048091081d000740000c0e14050200e9405010140d01415403034002110f00310105001040b0319040d40c3c401100c0c2140e41a0b002c010800c64483c9501040e00400c98100014030900c4034440c0800d030500956040c029503c49074051810345005a80203040705c503003080000c001851640c08141135621640025050011842c001041030940b6022090950488000401000014407902d548004681c0324100c1c220202c0045504a013003051014080c0080003a42607011070250202c0c0000307001d05400c2c103a41c0c0e800e0303107005000b9042030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 218718785 1250 218717535 218717561
    0x515031203091c050f03091e15160903020d0503041509140d15090c05120f011d060f0406020c030f18041103150a0e01092f07081b07030303 61
    0x101507810801032858642c0d0343c1c48111580c5141c102118003005505a9101078201d000364400c0d412a1901c0d04542401c1a000c5580100680045080185512032900c0020445564001d03281c81c1030102680000c01801680e4060310010030100091418a2440c03107580c210700c0005c4400e0b00180b030b03040da1050417401555540607603207580901000074003004d5a01040000c20f0800740c041070046990483d400606041d001d0850b6a82041d92540450b85501c03d040000c0b20799081500c030244404001d0140054030014441c15022044514005544481d8044c01e0541d1040307030400458188180340d01940c0036041e4104c152565069181540740050f8028014000c2551804c1101450740c6081d100f0f640440d00d50058880c0b55980780d074200006180c2e5540d00d9540030304140c1c0d02103034204150018a0103000c0e81500001e00d6100c0c2d08910030b401c540c81080c0e21154954201500c1c400c1c1114003503600741d56103e10001d0320354005c010f01c56900c1c8482013030038040e4031400e40d00205250749a08805a03030145 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218720035 1250 218718785 218718793
    0x102250512040e0708060102030d0e03180d05030d0203060315010915050612011503141509011a0405130906050f06010305071d060706020c0304140301060902090112051503120309 78
    0x28004107403107900540c860200e03107103030040024048038003950603907601900500c1607900d082c1c0c1c803403209070888280c00028540350b40701040c0b000e001004d403a11300f00006002c540f9074902080f9503a455543e44154503e0b20310b07154011001c1001c17918101311284100c4415150b03000690b8507904c4600050204606520000c02c0d4880005003c0c1020700c12529030144d1060f04803c507a003441d104201030801d420802c4100b680d555040d104240d40e9904203401240c00705404565090180c0420000b88410307001501c0000c0e00e25045060354041c801243d0444005940030f031104d42910003003000825038000b001c0c1071541408104840d00552120b2188101800d1700d00b000b864a407610f04444d6000c030f05c00c1402207840b41c0661b004451a00001420380b4a01c154800f5207403802c1107564600710341003540115980805901510854500ac7c02441d01a0664040c1142888800c0000900c0030706100f201e100c401c1d54503404180314a0000150983c40c410140c1100c0122100e0740c180c1d41c180d0f00840d0345d40c2c100c2c09 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218721285 1250 218720035 218720053
    0x207150e0c041404030c02011b060518010b01020304060305040602270910050a0e0426131203050a0309020406150f0908070303020a08031008120c0118032001022505 72
    0x303041e108103d5119800202040d503076640380e605999021444c90164180104440010000600070307882400709446150b01242e98201031900701005e582e005121500d507414450039010304d99000007903c080719003d28001c80d1036103560900c1c9000f4031555903c1c640c072842c2c0103d0303030144000608034012030320005e90b82c500b1650703a9a107854400700181e0052550040c2100810001e221030040da0ba9045401102801320096151050456400f50b00d5403800f50f070000810300e20207450503480b205009080781c501031407a10001350750007030061051126420a05036200c044505545450b0710401c090321880b0b0005881c0500c1c0e89000e001d19035030003a2400041d0030301c000841c601c440440c01d0b6040b254150000c0080c3c80e00c03540e910f0800c2d0001484a04422180040017401600c100507190141d0f5001144035510580e0700a80c82c00d54a540081050440c101c0707140e8400268014410100c0c1c1c02d1503c0c00f1610859048942400b91103080c0320107a228103920312055172014030807903100107030f071150040f12403401b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218722535 1250 218721285 218721289
    0x1503020304020f040b0603060d060e07060c02010f050a0206060112090203010908030105041d030403060216061503060c020c0a1403070e0a05060405280507030612061a03030f0412060207150e0c 84
    0x41c0c1c0507101715000030050010820904124030f82e03c044500c0b903400850030208803c0014901082684a4400640000e02c1c0109550300400814940b1041d03150013482d100300500d000e0764485001e043c02c0d0400100350001c0d850841e056010744802c0358018001d2010582c58108190142c2085c02928440e52a12a00c61206c03850411800d61440520000e58141461a1100300080d0020081e00c1000b800c1e400807140021080c0c030481083c094040a00c0c5201400c40c00d12108488020700e040d01503600520403000380b645d0314401d5400707e1b0002c1e5039000b0112182d801082c14650107078041100c1004840500c007500c1e80c150000342c40f81d03c064400704081d61320851241d405008440c02040300b03c40003d0f0052403006e8607040140c4c4640e59040100f4910303504d00c1d101d4408403a003401a510385540d80200100d45030f140400c0e2020410407001507060240300c0a401580344524450008102e40f0400020f0030040c0039010b0703a41c3d290704000f115602d2702d00764040501620510852000a00038000d51503168 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218723785 1250 218722535 218722541
    0x206060a030201020a080304080405100906020c0a060c0b090f01020d02210408041202030106031e050106050a0501210f0c090f08030304031e03060918030305010b07020306041b1503020304020f04 85
    0x202d4050340100314401d0242c0f0b407207001c0d51018000392000d4000b08004a529103030708248281d0600a5640c00500c40d00d0203600030f04108070080490300ca010000c40c2044100c1d80000030300f50881e040480524151591104e240c907001c1864610b68107540045111481e680c055809007803410054220b8141c1c06415170103840c0709000480d8010620641070206111484410010010491000e40000384036a00d0343c82d004a910001c8244803e203030702440c2518201b140c20701412008003010741c1c29589031400c6c9000a003a1078040ca4110700f410004400e50807121105411808480c071401000f0003074121815001402c0402c0c038099644059507014001410030300000880b449103406a40b400baa0a000c0d100c03224144050404202c100341c2c0301c40010a0304c0e1154400c0741c207000d25600c030703408403400280380240c1540c2d0141c2c4144a1850240543c4000d80c802040055001d640702060246c1d40c070488041a0301c1c0300858008510244400d01c0c940203994243d40218002d6008481d004c050340b05810400c030507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218725035 1250 218723785 218723789
    0x51608090f0d080c070f0b0105040e060603120913060b07020315010513020c0c130614030f0a0b070212030f040b13120f0e061809090604110d031106040507060206060a 73
    0xa2540401056402c80c1d12a050b01a04421140c0495180024039118440341420984042e41c603c501300c8010800d070301c4d1a210b03015483c043e140180410340b50102c0000d80b21b04240b4003100066000103400e4035507a1b02ca00503000c11a43c1044200801d940f00c02849201c0d4000080890003440b40c01114601c0b0302490980e24101c2c0c600a080148030f002003003030030020350881d002d205242c0c0b248500f4070700c840d41d03440c55882504400c804001002851312181d40091400340c2c0e03445e80203810100f1b00110b1148007240724601c01c0c0e0010280f8a203902c6210040f450500b2250400081850200074030034448407194410303024a0103846125581e445403050f101c01d00405144c002c090310140c400200903503009000a20100d070346400d142c5000b00d030b00c1010907041d80c041c0036019024054a5404645840c00900d61500720503400e00800e514a025940c0f60f45800c0020842c41c40307000c00c00c5450003094419a9500c003000c0400042c2c886c3da00b4a0b01d441c603917401481c0901d0016001d6400015014104428400d003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218726285 1250 218725035 218725063
    0x301150206061e100302040b120417040302010e12033612030306100302090a0311090a060e0a0b03010902181608060a061407060e0f0706030209060307030b030c030105160809 76
    0x15064600f807080240e001044c0075500d090580a1000181180f08100540420707070000c6956a074900d0316144c02180c40d03442d820000d0801000384401e0000d40d920a11650500342c09481c83d0f1640c4038030002a624500551041c0780c802c50000050440310800120080c000b60094008400704444420800151000c60004e0512030b9005100181c41e41c90076400c100f0b0150103500f80149040600c0380410501310361a007040d82e8a80894501c40214148608440d9210100d204204210713424803c2d0030300b0074400646050f0300c403910748012481c140e07000c0d44289400c6500410908003d05c0c1c1001d8070310101380890381c64070005a5610608a0b80f802009041c0c4505002860401d900e8148041510101c42a5030700054540c0140728007000240b01744140751030084c03250002c02c00003c0c071403103940c90050290001d40070180144170300700d0039855000a6036084102c81c20081564100b00f404240780c00d28003800e05038150309020a000c603001315001049021482d82d039445060340c0d43c10252598034407490103911 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218727535 1250 218726285 218726329
    0x3090603290103180215120f06010c02150f030f0f18030913060b0d020310061805040203070203090901090506040b06090a031211030a02030307091706061014030115020606 75
    0x7100561003580305014150f40380780e80b0541809160003082c0b200a4600500342186d00c0041e0b001c807144002c003092503022400b400048610714001c000200403107400c0c00c00070f0145014031424801c000340041550070803c0c21685039900d0b480c2090301041860000e83d00b1440c00c00c0c0c802c000c504180048002d8000b55100d8000661901c03c0341414090b0103d20001c4007069103a031584040317242c5040c070005282002044c140543c0f03d04112440e008401d1240e4080414001149500c50ba41407080200300c0444a0881d001602caa507807050503815407044e0341119607c46a8000041140303029940058006c00b400e981c2009501050070034040244565819168000d140c4201000019442d80c040d00f01e080c660315100c12458a46c4e0840c80ca141c1000f1b034100c002d608003000300710b06181c1c0f10303480e5001021800594502d032200040d80607281c2501030f103201c2c001e903800380e421000c1e01e00500a1320030b88400da50065503203680d146407402e002102403840d44018040c420110340c9615042501a07070002c1c0c40b813014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218728785 1250 218727535 218727611
    0x30912080c04030209091b030d0f05340c0510050304020f18040308040501050c070312112215170109020307031107030305092a01050f04080a03090603 66
    0x54a40c010000c00341802150200008001612801482c1c2e00440c0980003c1c211a15880d148a41102079017a09500a52101042c400b105030b00120694a030121030030425614402e8014030500c038207031800b034000c8405020b940c0200106080320340e10b081c01d01852820740c2007a1030358104001e181c0d41d2592000043e106101150152402c03025049071140b00408407250079600c92403119140c04219025000300e500b280402003031010078010280c0c000c8184a181c1d01e4002143d0b0040c01280300c1c04c00400260366543c240c1d404a10505080380d0300320031071624507220050001c80c0185501d030039004544043d000003000b201d05034040c50319101030b00445200c401c41682062082d0740203400c000c054004054564842c0b00e01000020020529240281c4d004a064500002058038021a0802403007440780340180d41a43e51140d00c490801030202460055503134100d1b41100002030140c0d800510503406500c204004254003c10107900722035054070117100d00c20108842d01d080c0c00075451302142c03610400d014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218730035 1250 218728785 218728787
    0x304060207171006170706091d0601030605090115090e01060f0807020a0609110306061002100914010f0204051011030d0903030213081e0105042105070b0c19030912 72
    0x401c0300c0c4400e908441c03c0d0300d1001c07100c0054400592124407a12600b2004441c090402e0040e48003030103050414107406480c0000d000060000d4141465131201d140010844c1c41c1c0c800e401100007450018100900c0b561514203100d0380d02d00c6505505d0225000e0600090800c00aa0005040f07400c1915074000f040c51200e02503820b01002040d00045024004040c8006121807044507191401418880418054241403600e00030026040b14402c101c0c03403480e5a6100d60028140c54510788003040403488540e03a1a0030700e0b1416924080c66503550a00c558564110426809171045620031503442d00c0d031001091083da901c2a200500b00c0759604104903a24040040783c200d000c00078803a14005207807504500091960740e10700e40100140e45c0003c13140c44c0101c10881e1154242c2d0283c00002c01c1241456600c00380d2105c1240201305507000c06100480d0360364019819108907a82206803411030786020406403805902c02d280c81070192034404282c5245510a114036002264020506050050b036040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218731285 1250 218730035 218730059
    0x180b0708040c0b16060c2c130f05071404080d0305220b0106020c0604050d0620040306090203060f04080d0f060801021c05010512070909081603050c010c020304060207 73
    0x8000c1d1003610402d000090440503607001021080110704540300d50b0413242ca8400c1c20ba46031003005104102c0044425599012502c5106c0e6100b0403ca03040c441105950021410707070591004c0c1092003078641110f90041507003c0c0c10683c81130760f0607a00d10a075900d0049202019020381d0080000992003240c0310b0a54a0180d4856074102c180c0501d481500311400084a55400d80e500d022204485001e00412040d5010000c100c001c1c101140e000f4102810300c00803409021b01c0e49000380c01d1540b50080359075400b035040c1911035007000050320a0b03a01c03622400c001c4013424403558220b02170b220344000510034104180c0000e020b680e20807a92490440030108000142428000d00950666140300001e078010003440100860307400b441e0905103070030209040030111201640424010b000b60248801b00f440003046600990301d07006070010305100581000400d6001301c150740300342c1401c081035403014035030040c015040040d85080280300c2523807520320880e03c90140f8804c000c003591280c0c00621012210360 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218732535 1250 218731285 218731291
    0x81501080f28060b0d0305070c0e090c06071506030503280519141306031b0c0f03050403050a0b0a05101424040603020405031c0c06021b011a0301180b0708 68
    0x80000c84c48050540c0083e040070051041100406c100140040401c4018042c1c0d600505000340e85d208103190000c441a103403545400903a20904001900204011060104da00340b1b64900f6001c201140d00c074501641e0f80d60044420780c01d9000d51310b0003004954a800c0110250000701d80d60b00d4240070f000015141c250322141014030030321440202c030011080b24503010306025400510088211443c0000103800c8485800c0c1c015044144094004030094010f40b95000e016401980111000a50304088915010f00d410041090260300220028040c0c98140a4003844003a90100615114203103d0301410943e0f00ca00820b0400402010540d45000742410010b00c1c101c2d403540c1e10980c41d44d007400109610507000900402e80c08641030001e130504008100c18218503815000b0500010b80029018152101d00101456000610b1041c00c09005904c1110200c00754000d0000d90110350000c070010a011100d64082e600e0081070040400b98080d100d460f00c0d422030300c4102544c8401408a809032002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218733785 1250 218732535 218732543
    0x501061a090f0d141c170105060f0307090b0c0105101403060103110607080706062c01090f09020306040302070608060d020121021216170925081501080f28 68
    0x40701005840100074480301205112015412001c40030481d4050184004800e0201c0700c6d01e0040011f00c020b4032040200d60320603583d004200e4407596042030441e401c02c0d903504115140000803c1c41100d401e01504128021200e540b07003580c600f511214080c643e00072181900d0340c103520040041012510701840e0541041c00038020fa46402c00b103840d44402d55102d1207040b545035036641d00410072202e06184140b5241001070407140c00e1080401022141e14060059003083c942d50b081c0880707554503135070221540e280e014045d1200d91030310b41030107500e4000ea40b0601c40881d901400082c5c540c904a0071a02c9010f905840d210001108951100c8034801e27410038960305541c3c00c010103040b110000340b80c0740c4100300c404102110900140701c0145401119611058a014400301b03000350180045041030702c8a9100500011189241200e045c0707a80c525401b2000a000e080340800043c2845842d090503940f851080328884c034001c10929594030024140d61544801d9041c1250154241a001040c99805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218735035 1250 218733785 218733803
    0xa0f0204180b0105120307021f0207181b021f180204090803070e0d03090b0c07170115050d050d200d030203061207030201091a0409090501061a090f0d 66
    0xa001e030840825120703580c0650740d0b03482500040019141c403541c0c09003564007440103541402840ea022428036520141c0300d0201441c1c074015003100c0c40c820040072008041d5480d113000f08044171541a401041d54003c0a1007000880200120b118000541500181900b0107004200440140400020710003e48a0070715420b10240d4000541e0310f90058114181c0581d08407940c9007001c410180c4a500d00a0440c0e00500e400c00003c808a500140810300300d070400454241e07100100044281410400c0d000034280c90a8200368640c0c07407a05621220a1a6807104811030103078951080103580800000000e2066001312440102c2c01d00c184410b00c0da0b039080500222584440c241802e050540c8240302500082d4088200202458107003140341c07211800d50054005a4110313000202403414901584015488440e0460f5240c40082d085900814524004200650051622a029104c07a124081541140100600702c0e00c98040440311048801844510081c0305031042c069079240401007900c075112 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218736285 1250 218735035 218735051
    0x8030a050f062d010c05160e150d02040e0c0907110c121002070c0803030103080a090e0702071e08070305210325090503010c12110403050316020406080a0b04050c0f030a0f0204 77
    0x10080240100c00b5500d481f0012186090451010005030300a21b104250700380e42c143c4941a48809064034141601a1400300d0b0000708c82501901c1c0000a025254002d4205020800500d9004014020858401055517001040201004003000301001340c03640c2504002c140000486103540249440ca204000c0c0104681d6100b0b400b5065420980c016945100300103140800c413948125030b00c4c082c000c0022075403442c0c04c142000035984c6030745000e8903503c038503140394408080340c568a0600c010071083e41101d0240da100d10702207441e0b1020341058090101d14240105400b40c5900541e8824070880480a8040c1540816426400d1800100c541400020340020403503803005c0c005c04908161548400c1004070140100e442191002554541000030600c4107100003000401111154441996000c90b80e414070f0001800a018030b41c4031102c01c0c03003030171005020441880003141c80f0714010011386501605400521041c6980211100da240d000203100c0000a20108411074500d4006000041c40c60 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218737535 1250 218736285 218736293
    0x71412091501030813120b07030911040603061b050a17040f120c0309050603090a02210619060602070f050603090708030a0210051311060c0a08030a050f062d010c 71
    0x14280c02c140ca03041000a0182c403442d905c02c0c44600103154035689060000481e440f143c0100300e000e0720340350400d82c54101a409001d06101c2c5c4501c0440e0041042100f1513407480c02e43c00034804244400e440c000d041145d01c51190103641500c414904d41c0d02d642c2003010003401405e5180390b00500c03c0342c856507401e510b0342c01720f034881345401d00c801c586494611420505003805000c22142e075004620810b0b0400800402c0030300461015502c0d036042c0c481214020000e4001030441c0b802c242d81d40c500c0e10030a030800821190081d036111114130300040030010651601c1d402c80e2640124040c03024889100901040b1509080000b1544545034106540b442a1100111419a400a820344006074000c0d0030500840b5204d2042e142c0016840d0000401d0540725624204c0c941c0038045032034401c41e008034507400b40d02014404008055444960305590b4503011501900500082e5101200301006800140180c00d0007a039804074036440b85070b4100118003900e04034003030181d194441810400c210035184001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218738785 1250 218737535 218737573
    0xd020d0510020a2607090603020c032502090a050103020618040e0708031b19420c03050f0609060a031401020c0c01020327061204120807141209 63
    0x8190700340c0c0c4088801c0420700712006800820790700044440d902d50217000150b82c01229810031561281009070f1100500c6c2c2a65085000c0e65240c0380c0c000c01c0700340c2881c10b8042c0c00d440b6001c600f442101c80c10074a4540810980882d942400020f4104c14100494400d4141445094406100007440480d00540346924182014039035400010b01d94004140c0c0082405039059000c14401480010040c0204080d074203d621540c55101034081d14031482c6076419486030601504608116a0095504000c141c68521003100480b040e05941450a03004c409880d22900400740140004445980d440d2250300030022070b80e801401c0301da404050324000100142d10f00700c001c03640744040300005171110710140100e03051031806200c03141190010000c0240307103009842030b03078440035a940401400c1d50141c00840c4c1c071882004100020100c200081004101035a8803c0d914108035030350307640c401e481e0114140c4140382d41e03c1e4144100d4400307002a568404a43d8452603010911400f01c501d0000000711407655 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218740035 1250 218738785 218738797
    0x706050c07080c0a110102150412020102041d0103050c0a230a1502061f05060307050322050307060f0209060d0504020612040b010603061d0c03060d05010f0c090506090d020d051002 79
    0x44d081070001d241400205140815205404e002500240e5580e8a0185010000a2004151002a00208010500c00d5047d14050070f48c40a4448a0b9512000d540440c000300340310442d01841011401c01d040d040201c103600c1112135008030f409404451b01c6800306501800e2403080e8210003ca100083c0100d004080700e14054269000340619041080c10311204582c201030744c0c849500e04213802c020588612080b40c0d8003801a1900540fa074407201180a84c0c410300340c001c042580303030000f0010280030004c0002c1c42850300c01c10041050006000c6505c0507802000722403640704005001c50510b250741a00601d5005100501041c0740258180060340c07551000d5a094654400ea00014001c2c1c0380c241c8120f202402c520780442c02a401603a00c0504400401030248011050100c00b20700d007601e681510010b440e80c410000e0100d9848030141d80b0040215550050020700342c00740c0042c450074881e00300d030400d880141001c1c003509015001c2c031020303070003008044034a4804d12400750381c0380016101a2103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218741285 1250 218740035 218740057
    0xd032109050d0f08011505040510171e0a0501210501020405030303040b01080706020102030103050604082a010c180812030c120114130c1707110703080d0c0c03050706050c0708 77
    0x4512590001084588140c000e401c1b80d202070740d568441c0c143c001c416101115070441e01240f40c400301002c01c0f80c1a64442c8402d1510f510840140700292440c4030404060107010064902144ea8420350082552020310660801d41c0d0f41424107001604190004084035001314009481c1540da039000c06d1039503104860555010310100c3c0103014929003881260300400326031000754159411a1641074480d0000b41000380a08000554074183c03d07101100c071190b0003400c60600c4403010b010056a07000e0710007042c0d09000582441c074800043c107900e5941d1800e440e110401442038005d84000c615080c1c3c0041d081d54007038a8180000e009511070300701a1400303000703d00154004100071000740040203101281280b5018207040208100c282e200380b0ba010040c003000a14002c03504d45000c25a20124885941c030700078055020044140520360004128064001c4d104025000c4811004c4510700e03040c82004000402c01c022040110b640d40d0406508050903001007498443c2a0781e03880c400c4e03030000b22504 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218742535 1250 218741285 218741297
    0xb091810060e09092a130c0f0c05070e071106010b1c0203010302010c150f021206030f070f14061c05070f03060b040902030a33050d032109050d 63
    0x30101c16401070700c02e40c0c0c0072070036950b0300000e0504110090b1504420420b000c04850940b001d8400c4401221130700b07009100181000b442c580482c500803001c0d00820790807501144020007045c08280c4250404100507800c500540f0405041841074951480050034030002c000e007070641c14442c41010300c141402800302c455160f5440412040c08034240078004000c0300c03001d02c103200420160b42c0107248040e525510090f240d401c5014207141d40000c11202d81510a40b0740f000c0340d520304c80d071140028603004040440850f108280f2034216955100300324020140f2080c40d40908203c5280d0b40e0780300a12001d402881c06083c4001007600c007030b481220340c0c101c0c4c0560380c9400c144004903070885503d95a07590649414003400d810b1043e0440184618414100b072107a0010001c0c0f1401c46c164802d90107094136400482c3d0080910215501c600d800780740341c06520250610014180c5080c8102101056041d10355a03442218210103210f101d2054520490041c0c49036018000500c1c240f00e036150383c0c86203407144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218743785 1250 218742535 218742539
    0x4050702030415020c0f0d05070b040b041d07021903020f0d030f050604090201020d0e01140f04031211060a0b030f0a05010c0906051e0901050403080304060504140312010b091810 78
    0x40e0580c40c2d01040c01c54159000304401500c40c0d1260104a40c5401c0c0c07c0d0784020f43c20030607240c4146010001e0384a040391000102d000300e220800e5400070011501c00102c080001c1e10076a4000c55080c10586521016921500242c109156007680b101c2a0a0003401030350f1181c859111100e040015107441d160002e035407110400e03003502c103910179a078011000341c400704962030460340085c0d520007c000f01c0006210369001100e445030301c2a40202d809081d0105140e440b8642d005660341d140d04180030071104e40c08203001919036a44201c0e154004000c4620041c065501e90a03068402800ea44003070541500400116400224042285100103440ba5000099555507480c2c02007408c0a075410001c2003000400411030103402548900b40007030031210403190342d000c01c01e006880d688195031008003044008020081071204a502c0644181d0040085260343c1440c42c007055124413587c6400c000f20060b0400500c00c2d00c17144005000e40e030b0030203402655a00e2908005072220403041300e441045400203d02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218745035 1250 218743785 218743799
    0x3090201030501080a0b0106030f0e0a050102070201080105180c131d010e280b01020102090d1212020403120e040f0204080c03070504230a110c0606011701180e01020405040507020304 80
    0xb03290060003082c01400c5440c225a842d40036050061180004250f1910405a0980d1181d80300e03030400f1641c04110340503207030b0b81e18100340070750400d450990203c4e150300000203190800e480307018510004e14041040c10350f54616001000d40010562a4250300880301c00f0170f034080c003450b090190401c14605041c080d85072100c4107041c13910042c0820000511204c100540c51101f50041d0420710b18100c1c080f0b40741c0785050040380240a041000c0da031000940703108105110001c00f03561f40916956079207112446e26215281e0607031145200082c0080d4001e620300c070b22a803180c02000c50401c001030000c00c0b2040e40941403010380c0c2107504880850341240314038100f185010400d600081c4810744040c402280b4960080031000d1b10740d040c54002d610040001140c181c05640f203143da4a004042d40c94a130403079802400c0da502000c4a505012810188203809000300b00301546049482111549401e03640185c1e281c00540014101035101c1c0d0f40034040410b59a8450044521866417980156283e5240c186 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218746285 1250 218745035 218745041
    0x306100e4209060303180f121c020f03040f050906010e0603010902043b0915010e150a0315020f04080f0102032205150613050108010209040b01050306030c040b0d060c0309020103 78
    0x40b00f90303c642c0c030400c5641103444c0d10402c0c80140c8502210418600007141c00412101c1022403c45402da014001a120054001c40c2ca110120101c41d4200d40050202c0303100c41da0343e4802c0e4020f0382c0b072208090904100f03070b2030311902480d0b2158041c5005030220800f034000c2800707900207030810940b540d0042014481c0b034040380d12030306048500441164629403801181902d40300320305c5000035007400c564001076858008020f030201e42d00040c65030b2440c1d5a901d00f400c210f886410b841240300c0e92a0ba88100c1e02918113440c0300c1003541c1e00a0f98501c10301120000c80303030095120b0000112168024000065402001d10006c040c4100310390003d40d036072400054000040e560000c18080c0310428000ca44c01080c4001011030078440e41d000c2e11500c548a01c0c0001e0300302e824801d50900060306050020414002c107402401c5181c80903203092100d92903900c01501c081c00210b034029015442000c0000041c5043d400ca1244a0005000104003100b81e40b10f03c010385200103100c2004c02d89a10400f011960f041c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218747535 1250 218746285 218746291
    0x11202040e181c08041709150c120415080705030103050304180b0619020d05310b0f07020f150307030504020109081b0306100e4209 58
    0x400440c54607040508611252802900100d00c00c00300d00000c01281c0b808101c15403042d411805001048054503e004140c048221012503504a860003009400c111400c1a00c0700c0280c010202e00a00b543e074002010240c0104206108a20501da40d1805001400d002000900a02c2d00712218000c5008405485010050501810484200010004036101000340c1c2d00740c3d000f2100d07180e08940000321302c5c00603050240c50558007a0f00001d4560880e040e09603401c001602e2602a038000c052000c1003503a0341e000d407410b0b1603002000c008401000701d0140749415540c205010101c2c61250300d883c034840d61034014428109184000040d01420b610345400403005d2500111214800d040c080040101c031408042c12201c203050700e5034041001c5a00600e401700190010342c0455806040d00e0108030030f070000619455000b4003424000c95070b001c0d0b40042d22000d0300d040801c0e030303075298441c4400e610181c15410741e0490235a9418000c540c180000c0048084e0301c0310010740300101ca2140ca02040102400a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218748785 1250 218747535 218747567
    0x10504060c050f070609230102030907090b0105070611070c0308040f090606050910030902040c03022101060212031801051503010f0501030c0605160b010312110a0302060103060c1e020c01 82
    0x1e108142c0c800c0303c100c0440e5500c80d0303c000c021410b01e9030351920640c142c0070704c003030300e0044e044039251490701040541c0590f100d801d88601300d41e1000d43d1100710b50116266840414001385040240c200031403960b4000c280d01d58480121189862a280c5484503d103e0302d40040300c00c50342c006420000041c2044508003d0303d600301c82040400e1400c1d80141c040d2080d1000c150151807000d44513000e090090b0f0101020300c0c1c01070000e1010413507040c0000c0095102d90408001074500640114100402d01c040354140c46640c2c006007030070340c441c106645554000401e06511001100f80c6520b81c80001c0c041d060281206c20000c14014492808240c256916410000c41141c0741c5001000859001006c040c1200d200c1c1c109a541c4112901c0152540c5c5140c40000d4800541c4500000810820142c0302000461540e0340713070001d41d2041d910940300c80241d6405001130744040014000310b0a9a03007d4058065a41080014001b5584820701c0500f14000102e0241c1c1100c07100e0074403560020610000903445d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218750035 1250 218748785 218748787
    0x1231111002071d010b03070f0c05160807120c06080c0c1b011403070905010806150304050a0b06060310030209060d1e031d010525150218010c0506180c12010504060c05 73
    0x14105d4403400740c013001300800304103d2000c203079036121070046010000040d082800d47e41010040401114000b0003440346c14221300c500d2074001010b4040812241c00b0387e40c001072601c9800c1c600b400888039440054500704030000e04100d41385803001c041185864400c01501035041045040002400320b0100d0101c00100340e40030410000d41d10350111084d01955030900b007954203038803004003181c40b6807a450031310700c05004000144400d00100007025442944199800f445641d40c4078140318041c0420340c2c40d032442810600e002e000605e44a00c80e20b5010700082c290b04e02003507180d1621503070300000000321960707401c13030303450300c200f85540a02060894425000b440016019090009140c1c2c4100300502c04c0781035400160070b07500c210002083c81c28035044211200880c40001e205002940300e42141e5810101e00e141011441d405011303507140881e00036000c1c08050f0340d590040c5e200051501c001e190312340900740c1600e4240c1d480d03d03003a40115140100000d040c0c5890714140c4101c0d540f4070848014840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218751285 1250 218750035 218750039
    0x30c040c081605041d0105040c020d090b0a05190f0f02010203011202090606070c0e0114040605010804111f050a080a0605030618010b0d06021231111002071d01 70
    0xe00900419000369040500c2e41d0341c1c0805100c121040d0082d41c018101192a010346032000490030a0700d0380c140e58084030200f0081c070544000341e90720b0007a0354401c07010588941c410030100b11840080c2140c10a6401c0040c03600b1050b4141001c07002c24403010602003012100b128400c0fa51000c1045a034290a0008514550410125400d842c1005030003e204070140b00014003140c80709001d07100c80070740c01f840c01c1e02e04e180c48454005031500c090180e1203149092001074072107443c09005000480b00e0685940d00642c5031605d07102000301607405a2900320449a584c10b88002d8aa84a0324038004207640d21500c1d0030071a98000c0036002d025100202a40c10244e06000969001c00c26036001040b0607907280480d212a4189405001a06641c80c2c0c000b1000a03407006110f8190001d1640d540700140080e070341e540d80090b040d0920b2820240b44581781100e82c8241210240c88081000e860156100c58008000303100040e018030303607080b480001a04000c104200140d0030032071801a0440c4d55561003880c0d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218752535 1250 218751285 218751287
    0x30405041107110d0803180c0406030f03080717010b03060402120f0604151a0903073308090d050901050705071d0f0108030304020f040e062802040803040308070203011805010b030c040c 81
    0x200001e4400000c250982114200c0d2260800404100b23003030203403090005503542d0600341c00640002c8002da020990010001d22880d20884640f201c0110b007848820040c0d080c211a5003582d00700514980d0080c1c1e082000d1402c0100440701d40c3d114102c4004c03080745524020341800141e82d01c3e0400701e0b00c0c41c6040075052040501c2485400000c042c400b020315140c44108002a02c2e0100c80d6100c02d50f0b1141310305503551a050300b0590180d007009582100d51003492031010032162050100d8482001340c10420300d40d448140303d00010042148140741c46400d10714680c4800342000c074942d2102041302c003000c06500d080e060303900590764007030380c40c0d403400074107614082c0c806849100080c130092080010035000b80166845e9400007520644480444907140b4100303450b03a50000411070a41c444180d250501030f07070701003503000300c80a8072100c1003c0d45c2054956a103140e000e4005140c100e81c1552a50003002134500601461140c59014a0000c620900c0c0c07103040c182040c05031a10103001c3d030705280e0640402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218753785 1250 218752535 218752537
    0x120f12090a0b0d0b0d030c020f09011d061f020105090f030304050619090c03110102070503120403020d050c0607050a030315030c0b0703020c1003090203011a100f02030405041107110d08 81
    0x90b072014440956404903071030000300a01d0250421036000712110010020b056000030b001e8081c501c00e6070903200c000c00360300820001040911510016402c000040214800442c41c495080100035010104034180c03003001210080c1b04526980c0103079941d1042048280003000700f00c11003031060015514504054956a0701c03039400500c82414110042e00c462403801003a44155481c1d9005807030544801e8480c545040b80f20740003443c96005100e0403a0124a514010803406618050141c03036034a03040c9580d09005010885200954441c059001d42e0381c43c54440500030140c4500c84d602038600c03061140350103000c5405600380c6ca03400310580507090001451003031191040c3d6040304807c0d03403100407500e012440c1c641e680803c50b80002c0408440100b15406800c80c4000340c0c42100288058024007609108400550542c02e50043d00c50080100d910f00541c600d00d0355944502c1560b14041d01c3c1e00100d41a50344128101c0a00300e4000340881c00c2c41140c0c14820300301c600440d030f07068404603d5291001c2c1c2e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218755035 1250 218753785 218753789
    0xe04110d0f0c03030503061306080c0418120905030706030605030d030e0a023a050a030f11070b030414010911060f071a0f0c0f030114010e120f12090a 66
    0x11411a5030400a108480c040501141c0d800300c0b41c0807540e80c80e8680101207800681c0c0c01070142c0d01200401201c0d0f04c160003002c007502d000000400c4034210b04020403024001c0a69643c0c0d40159180c1103402068014500016103222a1608812280781c2006d00d4a4102d02d80c0c072401c1090b203031920501c03080c1e4000c1b0f0301c44000c180528000c40c4203a084002281090b8440781e00962041c03007040c0f90740c10300d11038004001c244114140c085500424130068060580c03640040100150042121200084c0c02590101900e641c1d41c80c1101000510000c21464140107401550f6001000f0042108004402036030307150110221000784404480c590324070004c01442e00c4c001c0d01c03420380401c1000b0425810000d60314402d4024210403103091030498408850076043d2284500640190009008000130b072044941f08000003680030702e181e10300007680c01d440006404080c10007204041321082c0d80c0e5030a5840803413001c481b02801900d031890466034940310040c0d060031800c010611080005607a40322030b02c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218756285 1250 218755035 218755039
    0x702010f0629092d0306060a0312301509020a0210110405030d0305060f01030923010f11040305060903070c0e060103020d0515030f120d020309101103150a03080403060c11010501080c09010e0411 85
    0x11511982c0b010054030324131008990803800712f507644140b400014541201c003880e00f620740701c800450b46505040c41030b07100c1c5510030800350b0f006650110000315280d10400d44513520b43e09090800380c032007001900344004030f552440065100c2c001e00855140548103804441c000b400c080080d2a0301e075840038691200700341c0c05603144e03200030036059401341300b900325220b0b4840da0b81c8100016a0201520481900140015641031060000043d1014000001c0311800358105602000882c034243d540d00c00d11074000c280c14105502417000035001941d500505000318004c000c0340c1c51210225003454944403001d460301540d82d0055a084091110782c001300d0349404041030700540d80c0e5864203600c0b45482511245840311b58500417289010300841801386000320124840421030380c3c812420042c01034800e00001d400345900b003004200003232190384101d8040360107007005000240c40d0317405942154800d900024031a00421030403c6181b07401c886090143c40c0c1c00d0300d043c07120b00303194443c1d4520600c8000748038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218757535 1250 218756285 218756297
    0x2618040b0f040f09050d02070303090902030609190213060c11030c0121180317010905070e0904031803080301080717070306050702070e0702010f0629092d0306060a0312 74
    0xb001e003ca20740c2040450f2504907044803002602e01307100030342e04e05007848183c000803c50740011903810320718000c40380201002045450962100107807601d4400c91184444101039007004002004440345050034014412901e031480d11110305e0809950712541d02810600c61780240e003020b0030b681c4e000301540a1074492014102d410710305108050340104030802e50103c80b4140c0e10400002c2541c40b00304481000c01c81d681c00c400907640e032800c00f425a41e040c3c2c0c00d8404100321240403000e80c200a51440c3e13115001e40341818201d486501c042a0000240c1c005030380c0c01c440000140003d01c0d00b048240010300040d0061101e0901c00408151502c005000c0204002d071100045072000c1e10801c124000b1342000c40d0100d429080081010f40202000303524044014200400060f0360016042c030b0b01091441c0d50b00b88032046810159040460340141d0581e6400608052220344003c0b181c040f1560041a40389481101c407885010103181c88001800940705581c803d20074400141c8200041b000e10507142005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218758785 1250 218757535 218757551
    0xf0904110303040902030f070201060e2e1212030501050618060a03020415020d03200307200304080303041704050612040602070609051b030d09060c2618040b0f04 71
    0x1074110f10881d0b0105000d54008401d000d5a00902843c40d4050f0509400802404d69510103000c903210303040321051494000319401c51050308401c20108030400300181d11030721803074407140380842d03031f1101c00001c0d1560f03402152584a00d40d050310420703025000c21540c03941810980d40c0301550308141c010b41280a006c011078545407a07402501920090030280c5007030920a18001c07002942c5801c0b548900c00000c1c2082540c140a4800418000c0340141c0401100d00d55954001c055500302042600d1510004a0710110a6040300c01d00c0500b024180384006103030f50b810705040500c0c43c43c00003000041c400104200070021992207408031031044102e01c940200a540d1414040001d00038050041d2149040180e0300c000c1140108080e407010603000120720b044c8400b48203040d071b108013054414001c2064a44184180c1d4020081c10452038451007405440e10585041c121001880d41030880c0444800300320351400700040f2844039280c55080e80e007040001111000500ba4a654035080da0145a0320041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218760035 1250 218758785 218758789
    0xf10030320010501030b250e010503090c130c0e060301240512100510030509071e0306020a03060608011406033d050f0306010e060906061306050d0b0f090411 69
    0x54285150303070034000300119a5030b400c02d4040b0790801c45d11001c8030540340038412a4184c0c101071408040d1804d60399507428503640401540c465002404214003071007290ba0141c41c66030348184405240301613400101d00940d05000c050400a180101700344100e5041c03005021409812040c0d031080c00440c15030b0602ca0300c0c10001921036218501800400d130f8003e408204800407000e402c102115016a521004004400d4045040b0360096854148030b8011180812210540140c0d28010b12442090f0410340303a502d54800b400c0786d010307040d8400420b4841608118258016018500410740413103048403001c890000030314188002095402c038010b01c0144808607840d841d040d049548030100c00030000070404802c070320500c03220f4401e8521070344261500c80d4a40c1008070701c840c100d465100758000316031515820401c0c40781c001071005030000c00c184498500320308140c506500a12450b12001d90f01c401c040140d60546845075450360003401d810b20500d00c640c07160040706502c02c2e0043d8403402e500c007034180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218761285 1250 218760035 218760077
    0x30f0f0c0806010605190518091810060f0819081605030a0e10180e0601050702060a03090201090608090c010327031206050306101203180b120f100303 66
    0x1001e8024400d1100101c0c1480e0032400400100402c6020701440c040e1420044a80d8452007502402d0441c00d0301802400d401c041803915040740c505440d1140070284030350300b80d250000a007540d03c2110b884400c1004014074a2582c0d0005d402540042d00340f0520700301c0140c145882056006014440001d2521040710403010400c00e155881000d4a60365a06084002c2034000c1080e5454030804040d1100303a040d83c000c1d00c0e0340070b05001c100b082421040c40c0c5010810001801001141805410050200180ea90070010421982c181c0c60006034000c0500004110307149d42d03001441480043d8007804040721000034440e000c1c01e8246004203a20b8800010710b4803441d00c031180c15840d003c503140d01008143d0811803150340f20318211803c1020742c0d0b032071080665171041030350b201c0c003100b0103040e051190341e0b28020000300702402810320003000d40c0545948403801f540360f88018402840403e00c04000c880340d0001540000050034000d8130f608001c0d00350000b0031704901c401024080c1c00700c1c41d0500161200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218762535 1250 218761285 218761289
    0x120311070b0307021630020a0504020408060109051509010e1302060a020f0f0a08040515040506030c07052b180e07021f060b090603060d201801030f0f0c 67
    0x411500d80300e0903c902c010750f807000b4941d51411054040b080110f00500002c0084501e0490080514400d44007000c90705e0180300110705c00d9800c007003a040007007039503140c5000403c0200b007401c004114644c902200f043c225075018209003070000440d0360389040c503900c0303075405410f444c0c041e1015100c540310022561508071081400035005080480c040d1202c07070b0049070103501b03509042c0681d4150044801081e4581d000341034014058134040c041031050f410040e911149400c546819240f81546032800107026410444225111400004044003005418004001c0f648448007450441d02082c01c1c096100b60341c101c648104125580000400091100890000800f80550444442d040281c0000d44071008020101d042103481d56540001c01964810003040f078486000017800d1a4000d42002080e5002420041c1c2c400740e002c4244002c0f41942214080820a80f1307541d40c45200b03008284543e440640b281c080203140306900400109011414144803541e03c400b1004000c0fa0901d85201880219 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218763785 1250 218762535 218762549
    0x907110604060f0e030408120c031c02041d16031a040f0e0606090702031801090801050906041103030702030a06020903030712020f16060e0111030d09030306030c060912031107 77
    0x80244002d00c801e0f64003101480d503143c0010b004d00040c000c0d4080d502d120703521400c0702d258016019010b00310210f401400c035118042060b2403421900031450106491411600700c3c05950000781041002c840d03940400a003407052910324828540040482c090b404181e04040926440315450f901152080b480020081d0005000704000c0d0515100280203000d01d060940b01c91080802240f450720b00700c00d07400c1c07003071000d94020f51401c4540c0000400028090619605002400c080481c030304200380225441545d03088001d05031860f203400d000402190504115010303403c10009400940c40100d22200d405412002c0076a44101c03050120303145100380f050203003501241c1d000c1c2808042d80898000740317110b403140071110f45c0c001030f10b00c1c1c091000700d5200381c10111340c081e5075040c8030354049d00d0404110300d0070b2001c0d80e0070304600d00441d0090752102e0404400081d0348640c01e208000107100d2010140c143c6280ca040d400c0d0404031140592030400303d020381440130070082c07030581c1c0004000300c0c1e01401c22 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218765035 1250 218763785 218763793
    0x6030c0406030f0b0a0213030f03090f08060708010b13050103050606090303120702010c0201050f040b04030207030c080703021504060503010e090309061204021201050403050409020a0201291c020f090711 89
    0x542c2c280005a000c81000490b44c191407040410701c42c00490090b13402681c0d03c0f002c5208040d1459844034411010102c003102401508000010313980c001540c1036000f03000000103000c0c50300d00304100401e07840d1f0581104c58030b0801400015038148801c8500000c3d5002800c2c0058580c842000089050064103004e5506100c00900c1281185021000a020740b28a400900c4410704604081c1e0907940116210b0302d0201503440014080385c16030030040d40183c000c0c0180c440f155102d855150b5185999048100541d01a486c00c00460411000c03144008a2607000503082c142400e40041c907611041c03144d04922101c9401040340e0340c0c1c1c02e0080f1691408002c00e05560341c951a6000190b0a1044509070710803981101040720140d41030017074610036603140c1d0307482c1d00e81410292800c00035040800318800315940c90525540c0c04001000c88440b0b103840980700c079000102941003000210f503542c580981c2c130030400c1c074850050b21515505090b0480448401106030b903580e00c00c6910581400d42450580b20b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218766285 1250 218765035 218765039
    0x1062304090b1305040215030408090d03031b0306031e02120105091f150b13050405040f050111040b032d1f120510020310051906020d08091506030c0406 67
    0x4010b9102d1008644103491400c18000003c0124086800031940a504003203480381c55075811112200070b6502c244110441c90605810002240b01100041c00440200b0750f81d05030701200c01c021115000542400c1d10b4280061400c40d40c4518460749081021410845079010b075108550340d80709040d00c1d00c02440001c000d9441e06490023540c4040441c0040c809490410100210024038011b00d20020b9640c140707c100e0a1426040700b45d154011030010204845c0c134107001c40d1550b43d500031940542d010340321400e01404a418018212020f04032060720b408002c100400500d0310000960743d00174003451031100c0c0e02c20407d024182c3c010441e52007400d0740f2041001c200d61440b0f440b40c0c01040b01a41c442c040316054450f08181140c420008028020b64001c401034555003200d5001594007040c44200d01d551150f0712408140071144603207560f0048030464100780403841c1e04000113020342000740340421150034100e440d223840713034040c1c1d0500f10082041760000d0740c180c808014001e02403601400c1005829 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218767535 1250 218766285 218766299
    0x203030d02090f0103020c1c0e03010207060212131a0405010f05091006081b060c0106091b17010f0302060a27031403120c0c150a02030126030301062304 67
    0x54000780c541031294155481d4100c0d0f44d4400c2c07081c1e8820400c6040288569903ea5803090715900641c0300250800c02c21211941043e1002e0000e04200380c4100005a00c0b4045100c10320300c101001090400c80001524005000c07600400000c0300c0e02c03812644881d850b0b140c80c01d045001d07003641c840c1071620034281000e0200c80d550020b0420541d00381c1c036004210458039003a9481e101c1003541e01e110a10000c2040d08985860030324020700940264400000d9803580d6112000141d44814030541801e01a20084031f001c1500200c0260710000308a90380e10503036062100d442c0c44401b039404042d01070100803810002c0071f400354002100800007411601401080c07982103110050150000700d59a5070400341381030310000004195050403160003010145c0b44c1c2c40d640042e2054000800c50500f61050540041940300c002111601031b0304040d202580e2581403494000a280041c0000c2c0351015a020400700328540c00301c207407410341c2e40614041215182101244980c461903015124a811f40050000707000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218768785 1250 218767535 218767537
    0x61005070c170c010305011401031104030203010516170f13020105090a0b04090f020c0304060c0302030d02030408040e06010c111e0616140601080a030f091706010906050d03090504090f0203030d02 86
    0x100302c2c000c1100d409600000044040da0401c0c4900c42e8507480c98804400c103580203400c107110b02c10030746c0315850429540740c00003402e40c0c205a540001e080c08500340207402d00d9018424600c040748080c0808958203144000c1800408010a21002200b58201c55021607108100b00c07104941d0013805603018030349500b00458998414800c1a85083ca01603452a0030403d0703009a901810f2020051400c02d07150003030558000e5400d440c11411800200191111840e492020b18050760190440580b154109440c02c03088000260115040c050324030030101c002240b0044482030030f40240e4048800b8959003a0f210a04032084010540c002d0012403240c201c4108601074003603490040b40c0030f010060500400340e071120002e001300c04d020342140f16101d0101c2d0040b040321048807503a2900003541c90341c0d409109180f4400385886d0000c0c0d001100108102400c5008003409031000300d46040c1905590b6601502d80310b814400c150185032201c901805100c0c00c80c9072030340c2d9190003409680d07448400c0b008040c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218770035 1250 218768785 218768819
    0xc0c031a01080f010b0a0513020717030105010f0e09240406060c05010b0108010506030705130902210702010c0c110f120f01060b0301033201061e0506030f061005070c 73
    0x200f80704048403011601c1c81400f9800c10b0340d074050b0411910380e04007400e00030404500030198803d00e03020032014000030341018880110580301051180c4950404000500360b1700005081420412034a16072901580c400f05556044030941e540811605c2e854980c07444416024124070b64420714207100011151341000c0179403601803080000700050180e200054030210420700655800080c140000340015003e1001481c0303498420514a4035550b650000c00240e030702c441c1e080002c2241c825004005448100340c02c0750071040b2800244040c0c00001c42c02080846013940c05030581030b40080301401d0340c8501c2c84040e00d00b040a001c10b0554403e07900340d183d03910034594115089610f000c1001030071804800c180c0f03040e40d500c10708c000c030305181100412485609902c032000d1989644017542240c0308092040600810109460800a0319081c810021020b01c0390310035400307030781c0400412043d008031903d400d41c4608115400e694984018201310740707d002e1128018a80b03008482c011640b00201d055082c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218771285 1250 218770035 218770049
    0x120109020c0c1f260708040303060e0c271e041e05090609061608090f1e100501051c0f0609060504020f040c0f030e0c090a05181204060c0c031a01 64
    0x143c0300006000c080c4010004101010f9138030b0800e070101e0751540c030072116039820601900e070101d8010384a00d0194400e80781565003420b0b8150000381c1c000c2e0104442500342c60300101035107401c0c020600001207024bc00b030081c10801a4400b181420044c2e5075076174401e200326082d5081c0b00c04020220500d1400a1100351011802d51041000103041c14900051480c0315024640d500030a03030812040a42b91880c025243c4056806021020000081d0800480c2540d00841e11000c000c0c6103038440042c200b00300210710700c0c00d10382024018000e588a0200c22442c4021038a0011140c10a905140e41180003100d001010541806107020a0103e00d81000303000d54021030300810258884420041100c907008804008540c1100d002e1540701d0003980000003081012003503d0105412000040784000c0494a40c104281c0d64014010469040b41c52078940c0c01c0140020026241d070030450703840c140510301c500c0040204c5022250100840100204000c56008071514480502101c45400c0c0003c240201c0b8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218772535 1250 218771285 218771297
    0xe070215010303020d050706020409090506061306030503120907050307080c0a0905072705060c0703050c15071b0504090f03030b01050f0906070203150403180506120109020c0c1f 78
    0x11280002508a40c102e0364550000c05035506610006d40d100c0c0c109803011380d4803960a100004d0111018000d500304244a038000d408245072100c104640340c0c81c201c4008038418074108081c00012000000c0303810000300100c2201d07071980e0301c1c200d451420200ba00110307018015007070001341c4890002900700c2003032412910790f000e141e03e0304000c404880d801c07521000040c02620000c80d00b100b80c107455000442c80f0900901d0700c151504041141c0d07520a414044807544602c03c10400e200040c0102c141c01601200d0014109402d449001d04074003c11101811241140e45c0c071703c0c0f503010b61142001c010034000e00300303009041c86400c0a407980c00700d40401b5030201b400d00704000c016600c101c049440d0b42ca2802001c2d07041609103400d100d15600001c1e800c0b82c0600c218500c040d105040c656010313108500c00d41d50441070300c0241400700000c18480d480366000784411301c076400c8400b0307d02c4803013030660b4801d200c01602c0d070401001480c40c042d40028000d802c1058082c0e030043c40c000c403c102003400032442d1158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218773785 1250 218772535 218772553
    0x50a03030515090105040209131e1107210207030b0703060e090a0507120c050a080f12030c0d0b01050909010f05120f0304060f0c1e11060c07031e0c0e0702 68
    0x4a000b841050155544006214010700191609a0261401c01c001604055100714031a00c7d14044516400300d540120340440b01007014243e460040c1103103885001030060504105035141030145183c1004400c020000310303408140c80d031080008100458120b2002890b5050030100600203200c1405203140e49050400055405800001d5220703905a0000007030100c3d078075180072024103c2071843d0840c0c0f40b2800500004450760323400210005004220302520001d816016264503040c400754441c00717084814000c00c01d0085088c02901c541922040c00460080c8506004907044c0c4a112119070340318008074000b04002e001c1c0c0b0711030020382d0010341d01707000c55030700201c0c40030b54681c003489111f49661710400c014032a81d441b404031400e24041500307000c43e0384406552440a00b00c0481a0b404492403424400014020360408800c1e2a41e0300792860f914001c940d05689460310710310300000c1c00281e202107408405400034003071818160b811600c05a9400c0e04c4000d0300c401d4075000d83e11840144603a00e08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218775035 1250 218773785 218773801
    0xb1603060e190203090111040f090b0d03090e180a060b0f030f0307080f190203030405070f2319030302010510050603190903030207140303070809030a0c020415050409050a030305 78
    0x424010315802c10714008042c050103011002e54802481100c255484490500b20b6000d000e0140015007070f0440a5000103040480d080c040302e1006504503c9010f1020221001c41d4102903c0c3c0300391a0181d011814903940d4000d1480d1041e003800f582903480c03184543c40c4060049a40c01200304020841e0310030b1403070b01040100b50b61404101148007603a0020004040096440d030300804500d40c050808509101080e441d8002d44400e1801700c0e0090380000080100300103050003200c01801c0c8800024018034188083c0317920306050049806a051800c86e0810929aa440c0442403100358443c001c02e2110748906d0000d01800301520082ca00361003404022400b858101d040e24841c03800040c0035411700380d03001d02e0000035110600054090507405c1100c0004545000400513210903504000d503030300c0c20a600002d120603002480500c1c9500705000c0c1c48013081c0e2110381036110035011140402da040524880c2010304002d40c0c002030f881440d08081000b0040301248003000f05020362030801c1243d0310342d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218776285 1250 218775035 218775059
    0x3140307050c060f0714030615070804090b0102010c050a0f030b09090a0303140606070f1406100e1f0909020609040608010e100203091c200106080c01031503030c08070b160306 77
    0x144d0360011500c0c040342000e40d00a046c02940d0701c00401406901d24100b071261680781c0781d00003502035440761400281408902081e0041e150352110a1008004480d04110300901038012005004100100311824191051180d0000c0c4500e042c024004809c13820480107441d59001c1c003c0044010a0400e00c64014140026410610403400904018034103145a680d161085260034400c81c0c0d03410500c9400c050000017003001510507640000110313001420b1481441000c2c100624915928200c0b00100214004183c010402c0b20622080402c0300b0f103203407000402034003464800035042481e00308000383d08101500a041d00b00324010540c1c049030440b820300e03410b0303100444030000c1e1640031001c041544008103c034500c100f806441c0108200c03404001c1c86101d0344950006850703d0391144400d2207411801d1088204840090a041121300c441c1c00d0030114400851001900340b01c0205400400e000882c812602c1c4203a000c0049540b51400c1503964444640101001d00000d1400300040380a0841807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218777535 1250 218776285 218776291
    0x61b16240203041212022401030314070f080f1b160f0f06080615070309050a08070812160c030602030a0b0603060f0907091703040e250c03140307050c060f 68
    0x4074511084c0380454507107424207648041298118807490311000016a400e071000c0c0c100e1030829480c0d45041d495420b004200d5510b800d890003e46004208202c001800682450f041c25480724085840d0040e820300c0030540d0240c80208044074035501d46200100358041a900010140003052030364950701c4994100007000c0354019503a00505544050200c00e01480350142e2280b00103280c1940380015010002d0140c02000003100407849484081c006881c04800c4030300940325040081600d0b074a4030510650b540d9401c250340000c80d0000448004162440043c0d005480d045481e40c1d44250380da2070004002e600c2181c1c03401c034107460082d0301282454240c5c00c403406014000c0144c6044030525080000443c4050031080070f010b0289030009402000c1601d07580c201c05200302654549151181d10140d00038020312021210103c462070540400342c0383c480b04044001c0d403a10001808075841d00746c510b03040c0151003081d8544040100300e96603034000700600d001c00e40881511a1a01c65043d0140c17a85815 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218778785 1250 218777535 218777549
    0xf080a0c06080a062102040501080102030c04140d02030307050f060915041101170c0909060603090a121101050f2205100b0402090616051b061b1624020304 68
    0xc0c800800001d8850001d040c0c01c0b1195120020314907990f00300c0c40b500040c1c000d525802c403d8601001005625181c810b1b41d0040c41d4200003903245182c00a142c880da07219600807910490000301000440341c41d01780400140b940e010b400c80b66a6025030820301d64800900d0741d580094880c04d00091306404001c41d43c4400403101c8610004292140d42e07402a034090440a89410405407802c0c5951900c543c50003030340110390700c20850f6541e440030018008040d41c01464103008010410a005050400180c0c5544d86a0030980d80a082d8801c03003000c40b03406607256038038030613507003010f0500255030100391059028200d12041c03070006140d244614008000030941c050f0058010080e42d1440145640201d620000000c1c8018a403010300000540305812803100c0103034942e0711030141001c1100800410302c4142ca030864103034102e1040c0c2e000943c94413581e00200350380f0660a1000ea400182040718020030074542d500c0380d40403501d5140c1c02c15040200030510302040c0030b01c2c400350001c82c008402c9509490b00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218780035 1250 218778785 218778803
    0x32a0304050705190b0f1b010c08060301110903060a0b0111010c09060e01080405060105010503070e0301060f0f080303010e070302071103010e100c05040810180b010f03050106060906020a1103120f040f080a 90
    0x11b080c071042560040120714912400d4803800401840e404c0c03280e129240304030b0700d450245050110500d800c4907802844511540700811442d00c0f69540091429401507405101082d82c0c4010030040780c800d07110801d5849150f003000c414040d0345811145003403e82d1043c1d40d0300e00001c00c1c01401110500c40c1a01c0250141c0c001a00622041d440344004581c8511181012024140500046400c6440661120320403c1c0a030206210004d0038200c814001c20310200150300f1541010b1001c004c10b40c1c040c0101c01495030000b8040208a0408444081701100400801481e4100340d0348644802801009490b041c3c43e245540107a1405201690700751002e000080103070391714103101c180003020f042d54205001004000d403080010401420301e8007920030b103070601c560180b448c03401500f9100c1c2070b006a07060004081c000d0101035030010780d2107512908803455070007a400351404a42810304000d4101810b2000280c1020701c1c002d1540107004907403110b140710000c0b6984005c00c680342e200c042001417800c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218781285 1250 218780035 218780047
    0x606070b1f08070b0405090106050703020601061b020a03030528021509070312020a050d0201090807030503191b020f010903200309040c090315090305032a0304050705190b 75
    0x200c18154080071490105072071829440b094000c1c90140e1552004503243c200003410300c03060810041960051019040a0b400c2001c155030182d200d6005015003000c00502244410b525486800d00140c1c013030f00600401c0403242c03241001480c6034040482c1c00e01c131080c034490004014410241d03030450b104441e13000d00100002021048085403020f8441540c07481030101c0880030407400b43c0801d1440e9025002041c0302c01141c9803c80c14809465901015645003402820100d0a10300c02c03280020703418a040f9640c0c1d510f40c000e07010303072140e0103d1000d8102d00e8513038480031003001031355012030300d4000750220f6807809100b062050036580c6c81e0b80000c000803241c14140c04000d01d42c14090030728001e004152414080640e010800310b6042c81421000070b10400c0e010814011a00e40c10b15011060071000d215140560318040c001d840040d00fa0400e403030710b800c1804e046451480206400040390303a107050352070405041a9698620f40d01459204900d4580b02d000400140c0403038200300d030104030303035181050307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218782535 1250 218781285 218781301
    0x308072a050a0803070806191401050a180305070603060512192118060807230412060203060a060207150309030e0d050a0302010507022b030b0a0e06090606070b 70
    0x203910a208884a104a14000c0d00041071807001e1842031600707940341c00c03142c500f15040001d01e0305001c0d0254001c0a40d180c060143c03504100300c0501100e0b003070910710340e1940d02c040109d0350078000c1c14065088142e201008000c1040110b0468101c841694044c00015100c20811400b00d450305140034144e440300c0312201002c0c0007958442022402802e09001d440104080c41440501440d1001e00050701d207903661110441c2201c0d0700d8050030292412204034900014040c1064448913071404480d142e4a01602c0132000480c01c8030017800d9881154001c1c0c2d04103150400280d0003d0f25402d115910560002c00c06500c00202841120501d184030b0f565a20107480c103400804035581c05504101c9100d0300280d981d10b903000781300b4140c0d1160340241904849401c00a0031550041e00e89030454200d0f003005840b5030490703280e0414194001802e41142440d905003030b001400a50070140d007001d40c01c1b400050503034154072858841c1c402501c1202e1035a840c401007040c02c3c07003405401000c820425010405c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218783785 1250 218782535 218782607
    0x60304020f010c081b0105130b0402090a2003180c060d090f06090f030917030a030e031207020f12072f04020d0b0a05190b0d0603080f0403030807 64
    0x600381814101580c0f00c980e110794200d40e1264031801c0c0f8061500c0b25180910b40b091181d264400ca1081100d01001020303038944001034400350000e03124110a5000c110702c04083e42c4808200391010017117050103000b04822610b190811034440c1d5900510b04d586e00c2c0d003400042031080064500034460791410444200c4040242070304403058600c0d0b500c0742c61800004034144a078018003801468000e01100661900521005080c0c11055884c0191110f85010f4240001070b00d10000d00c0b8100494004480c10341c0c03074134600505001204500300c010501c1034031a00403c8a5000b0070740041500c140240881141c480e0340f003040d81c010f2881c1d485102018200380c0e001d2880700150340044e45401110a0300000805a03081000ea1403505aa00d0500740b1491038407904544c010402582c11030124400c41c1c10305e50400c0c2c101c0c40b40040300800002d980400e41d145d5800030001e1a0b121118a40f070b07800c00c4810754110b400c140411070200c1c8055002c14030f1203009510700c0300e0a94a450703400c2e010070b0717048144a0304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218785035 1250 218783785 218783809
    0x907030203070f03110d030c05010903051b010902061b010e0a0308060918070302040b010c060507120b180c03090a14010f0b01020f07030201050d09140307020a1e0311010903020301050711010c0e06030402 89
    0x3007220710218440090270070b0142c240114040d50b540d60725134050200070315100940d0b844140300d903850910002c0041e01e070402901e050b250319020081c0303910071080c0e9a0380503084058802c0800d000b41e4201104043c1c2000c0307040e002300300c25a15040c841c1d51321013020224120307504500e40c0703550140d0801c000614240d0011680c000341807401c4ac0c1480d065a8503e000c3c0c98060f150200480c109142c92a0410746da80b040c442d20f4041110140e1603244603035800d82d8802c00107403030291703c1c1d00300000141c4541c904010700c0200390340c0314004040f50b13905a41014001c0015208000c2c00c0c1c5d041021b441c0341980300003565205500340c00c0140c01610f113140d0054401d644a59040d0010a444143d0f46002c160010344505030500c800c800b07556605d410748100180b405c40c0d40c110032004040c209044040c2c00c0050515800d49074884288000c80c840100165515145a400254158200820808440ea000c030071107a5030b40d441c1c0028004200c64182c192210b40440b0b100d076170055400e1001030058642044078140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218786285 1250 218785035 218785037
    0x42612010323150a0f020703050313020f09070809010515030309040e0708070305010e060109290102071502010b03070501020c10030f02040302041103090c011d010c02180907030203070f03110d03 85
    0x290001c2c40d1420207003820b00400300d205074188018108644115503024596040e0042001103140460300e650141007400042c000c00c44551110003480215120300346d0001c8490002000c0300d22078517000000030404c1c0b00c1100c640445500381804150000302d9090811080c0c0c900601075400c180c0d0342c1c000c0c04001e000e403008180052240000c0002c0e000c50600107100a540100300200c2c1c40742048420a00e4000706a22100c1c80078074010234980c0c16031200c01707981c0403080c030329001140101001004034a41511a08900c83c0aa09000d403921541d40543c41040c4002c4c1c103806a9070510741d52001a600c43c841705590076000840f00340c038070307030941d00c26449a0219002880d005040a0f101e4011070129906005480001000001400450913040003248600402403800941c90a203501d0151440b0301c03000c1c00d480c14080302500c080115503403810803c129038281e9450003075500d09241c03170315aa86192310040e03020b40266880852802c0740c0620800079250091041200c0c1c82c2c804060103a0602080e03c2a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218787535 1250 218786285 218786333
    0xc07060902010c0c0b070501061e17070e1005090a0504030e060a031b0f020f010506010504030b1909080301050a0905090c100c0c030305030708090d021515090426120103 74
    0x3c00080e001385000e40601032003a0125201d8820740b03051400c6034200c0e00f14410071080e0303e0100780701040f1003100b5070954800140034500c0c000032500151508541e508031456219a05081240c0d0031880c1070448100c500c211072110042d01c980c80b1140c21544196030240000d00aa2030022281c20944010503a211080c0750004058511103a41c03440e0f0305000d100c20380040c14802d0f00d904030642c10044024042a040002c10640c14140006462403055110040c541e00e8214000344c1000f00301020b0b041030340c0d000d400c00c0c0419902885c14206031ba200340501c078442e01d089440461515410710440c1e20900c10a401851041c6a500030000d01c110000e201508000c102e020110009866000071030055200b919195101e08040300d000c0c000402c014442070003584624040c0b080c50707500007900302900207400c1c13680c1c0d040d454022645c441000e5070092190003c0b080400e00081005c0050443c9080c0403507420b81124807190201d064103489400711700c13510715a0080c014004904a0804a03022036030440280c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218788785 1250 218787535 218787557
    0x108060f060309121b07080f06011208120a1e091a090705120106030b070f0503042307080304031104020f040605090402090d060519110a030209060c0102040305070f05090c0706090201 80
    0x3130040c03a404040701404a0000603e03c21805c40208101805801c1440c090070580108103080359039120144210403a201d00009031906105000c1d080340c86c502d00d201044203c502d00807020390b01401001141030b44902d2100c001e101c21088900c204d61340300398041103d880340e0740907501c60803039120054151410390040c0b54000a03213648510701c01020403460000070400520714100f07010340d000010551420712040030252003070140e0120031654007036807105541d0501c90b852008800d45520100b008516441040808904010008043c00c101d0b0320a0300201c1240006001780801d80c0aa9040c40120720010300080c08181e005102602d02810003070710050900000c007000840a01d04000b040d20125501d0041c859007820003c58098190303804801400600c22602441d035080c03160000301810140e000c60b045c0110b40d06d180031585050400c600a42d103e07074803800c1c4188c41c1c0b00705206662803524000380000b0b05060000d0124400e920301d5107806e0810081e40c6030f480140c003514400301c1c1040954000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218790035 1250 218788785 218788813
    0x9040906061d04120305010312050a02120c03120612030405130b0d080702090a09021c020109050904030315150c151508010605030f0303040f02011b05011a01030b0108060f060309 78
    0x403803a5200c451000c0003285042a0400c4043c803410244c00c42c003003609050051020070950f80c1d0a09031450a0301e007942c1c1e1841d0801080782403121100501c00010b90004200d1440b6500202902d0040800080c6c4542500c9080411050752450312008070150030600040105240400340040040001c03031000c22900c078500b0008030b00c100d4074841281c2c03a000c0401c181e4294107141e00c1180e030040c100300d0300f0490000036800290307581d03e14400d0f80c10b004587d051843c0844e48101c1c502002400c0190984000c0d00b424a40038002d059a003001c081e649071814400145a4104a08208494096102c60185200070740307031000544041c00f0480d4901c0e80390b4603009044051310311910003c00c103400002404509040400d0704041c0300080d80c0555500500c1482f01140c0143c1803403100c0c0e942400e0001412420100c849800d0070303010000b40241d46068016079072260700c030642c90402842680c040200c1403080c80150b034000f80581e0801c3e04981260744032007103030600c00000c64016092008032840a0310700c40c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218791285 1250 218790035 218790059
    0x12020708010c0c0c05010c031709030c1e0607090f090b01030207020d03020609100905121b03040e060307171005040c0801020f092422170a0201090e09030904090606 72
    0x7a400010f0051103d4014401c5201121016060074a045d64000005480c01401540300d0640384030340011241c00318502a20400455180c0b880c06019112202d100c03020084006000389060111402000005190305114131241025030b9031083c010003a16040550701002000020001e90600d036080101d000943d94541107100305e1842540146210b240000002e42811000c1d41111032060406042030000760001c5410308001010046c4142c075403150180030141500902010041400000780100b01c452003001d100340320754015411201003d960380e14500781d200c2c1500e010840c2d5040340114003d81c8506030803454015010713540a42a16445458290890b0f0004c5d0796100c2104000030007440606165026041903100c8111142c0300075121615003840f84101d1035611007480304840c400d0301c81d0803c0050300020380100c0c0400410341303850341e81640e91407200c0c600c244d001c43d007a0640080c02d5502550308500c591440e8001d1400c0148140c00c1c030015282912045070800e880d1040461048641c43c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218792535 1250 218791285 218791301
    0x10e060708100e180c01091a0c0102040b0403140706020a120e030c090c04140f010e0105030a1104030b150a03030e060a0207030b0a1d0a030822020d0302371202070801 73
    0x145013400d00303071882c4505071510a0305400d43d414000040070401202c0e6403c41940812076001900350380c0c0314420300020340207100e99002288542004103012050100100c20340d010a18000200d46080e91a5042a039407911154002070440b620094041c0050340300d070021a522840c0a8121282c8204d070000045004030704a409500f00c01020072b04101d0100c800005000388a000c0d951607001d21200c50008040c0240c018165040c4000000458100304d0030380c0c4100f400d1014010210745554036444d20311480e480c00d032070443d600c003520b119500b060300e4140e4850040300c0d070507120a010390004900380103242d0440b0454070f066004c2d5400000201d809400002d200d0489480000380841c2401c0c02000304c4e071070103129600305038005010308001030f1300402400c0e00401c004202c980d240113034002d01603011228170002508104040c40140806400040d2a03001d80c5281c070030380a402c04d420720342008c1212420280e100c02600c0450702c0c008100303580500d10402e0300a10542e5480c0303440303081c4035096074629 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218793785 1250 218792535 218792551
    0x120510090b06010906230c030c0708030901090b0310061409120607090b030408090d0c03140106031104150302040b010203070b010f05040f020f0a0f030b0a090906050603010e060708100e 81
    0x80100b11030756a02802c500041c1516080c03d046054210410b4120000340c100182c008600010b80011501800c0040d100840c0e19078085804040e205d0b202951207800c030310f1015021503121400818586180c800307480c0b09009604004540314641442200c012071424040e803041b6004202201e1b96072102c9000040000d94a0028a01030070a00e078000d00030003182d440215081000c0c81032000050682c0121f5520035000c4138001d032483c116080c00449100107500050002180303005d01414010706400141c201c9000c1d00440710201e01080a010a4a040c01d10358854403910a03024001481e0648c441e0b88840720610450341801d01a5035120400e090a80207001c5045199208000900e013500440f0790b01a1000c9083d401c2c20312200607155140a0810104240a07010500c80c116601c02e5202d1210314200400c0910420366400102000304402002522005c0c00d1500046003414140100007520701c492000f0080e0f0795801c08110307103205028029400ba040756650005031045c050300e1240c050008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218795035 1250 218793785 218793803
    0x40206041a04150f0512070210091407060221130504060f081002071707020102100609020a0914030604080c12030a0209040f0c0806150d2a0203040e0112051009 70
    0x78108051683c0d01e228500ea001c100210700d4030a0200c5d880030590b010030380d451103074104503214400c05a08208240f258040054074003640c0c1018096444c00c0c41c03d60001c42c405643c0501c4d01c0d904100e0300ca0082d0940c520f4198100c56000b00c45e00c0d2500014500344081340c0c0300c00c0e103454440001409880e0107501180d0306200107401407201c10802e01c0710300710040d42140c08610300240d664503401580e030310107040340070f021000c03400c4015a4001e015603041e06980d010708120b82d0f9240d2507100003d400040f01e504c0021411000070500e02030005003090100301c020014000c640c0d0b50760340c24050740d00c0724080c1009030081034049070410400c400554001c1e40c0185015841d1030100c0c040c403003203a05a02d070301002c035420001700014080e04140b0998204400b5154130304100c40b02c0400c80010f1058161300444149000302a465100304d1070f01c0e00d49400c0c1a80d807101c2402004046c100c1e524010f602a180943e600b04004001c01c0c010130950740c2d0114461015a210480f030058101c0440720315043c25102d260b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218796285 1250 218795035 218795039
    0x70b07050105071403090706080c070b0103062424090b07030305010611060f0402131409030706050c03010e0a09031103120402040e0102040803030c0306010e09090307120809030d05040206041a04 85
    0x18101d031041c00c1440038000340a0440c907200b42007551f5101944558000d000407a408501080748a0003180d80d5030b42c000503500c06650b900d26080300107002c900e40c0304850056078040d00030303400103841040045401c0d600070300b050031044001a031520407820a0b800240040d01c84001741045c0d08078090081c007030007514001900d601d40a400380603d4805181148903410100c204540c0007200480540c010760140c52003004949010842c0c0c0041840c5050300ca1121010820402e40030400001001c4552082200344159100d404421800340400c2c0180c4030215081d42c0002d05414441c0d00011003680a450541350b1000d0117100c25056900c100c02010016200388200301c190b0809000310821561040300852510346080140c41e120b002c041d02c1e50090510000c00f040b8580e125031020141c4a4000b0200b00c450301b0070f8160b1554950090004844120300407958250081c041e04806210b80c03071141c0950300c0c00031610600001804001c1080380e000d03000340300200e003182040d400404200140d0074403d036154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218797535 1250 218796285 218796287
    0x3030809070605040e0a0f111204110108040b07210e030901030615092601050f04110d020d0201180b0d020d1524031e0f14071d03070b0705010507 64
    0x211140d0003000078044100001c02c0b4400c0000601a07202e016521b00151031210700200c94080c1003c0c004880304810041000e8a004030317410844d90040d4480c540403111200010010748800b8001c4034080c0100010000089559000d10295509030602c050a81d1351316400d1030713100301180e8618030040c03290380c004103580c00fa55030144124000303000d041e0b1242491720202c4000a1985003d030045c0740050300040b0500395030788e10010b26100c901030200001d20080c40c00030400d01c62480c04076019205060744a030055201c0c246403039403000f142c0d0041c09100c10b001c0700f40c006449080100c2c0f41c21804112000b4006803143c10000030700203c2d40705090160740c9044005000060700c65a030000e40e02030f100e408041041501441c2601000302074505000703152920b4880c1940141602c0540c560407446282510210880580c800382a4444400041000c21500b800d41121480c0031148900032030800031001d200000111115002004c000342180c54040d190380302e11a080e005030a049589030345880601a080b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218798785 1250 218797535 218797543
    0x30f151807020c0a030b130c1203030b0127171005011502100b0a03030309020a0b12010e011202090c030a18050d02012909060406050405130302010b030c090f0705090a03030809 77
    0xa4411900c19214074111b031924600460040c20076205c50070944680310800960783e0540005017894503501c0e41028840c18050081d101450380c1c01e0001e0f0002000604d54820030700c522000402c020001c030100350820005e200c10441a1249220074416482484400c0d070407809003030301821801080380103040440d54082c0c5054002e1a5031404c007401c0248621917612810070b4002100c3d01884c0109002e0814008500181019040703440b50b20000607000c07480d80b9213920094100d4566400d00095aa694800c2010403d1040c0c03000f58440d1300c1101041c15103002001840c3c1001b850800041c210181071000384125100b080200c030399030003e04a415000380c0a104846107040030b84201c3c0c8d00c0301c1009800b0302000000b500d80340c0c81200f03a940400c01c2511b40d81d1040000c2d00014100304050704222103191600598580308038015030038100e070036a4509001c02e80381100c2c00d01902a2883e602c808248a051241c01441c200c1004414881001140c1c2c510355940004e5000b0740711010207040000d201424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218800035 1250 218798785 218798803
    0xd0914060a2003071e020f150601020c130609021c060f0503070303050304080405040204030f052e02090d120903050111031003080309011d0f010b0411030f15180702 72
    0x20503280020030b100e01403009451803408055010140d0fa00d03501c5001c190f505004400814088444002c20550016000600d454a1940f05e400300ca000c00444610036031000000c0350011b0041c0c100d80c62051080c10310349005810000145004102d0541b5001040e01300d811006140143d0711140025881e11070079485601d000d40100300c83c900c030150034030020030b64a5907917200080c01c01c0780000028050050003c251000307004010025035461741e5a0402c200c80c01100802900c81d0b0088080c2d84000e45403510070101c1c0d10714480380704411000403044807402034020181041c1c211078002103101c00208c008400c00c000d0801c44e00c540200a00b50b003091030854003012541c8190010400a000020105030075610490740d118442c5942c0b540c41d180c10300d01510b003444141400215086a100d0533800100f05008100814402001810200300c1001306940e004541041c41d581c040020034103011480902c00e600210403030f945440380500d0b8000c203001c00e08110403002c402c201d800510030895410700513085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218801285 1250 218800035 218800051
    0x7051c0203010501141305030a030504030302100b0307120501140c030f0106030507050d0f0e06010f151803030509061b1e0d02060601180512070f06020f12030604020d091406 76
    0x401d41d8100300c0003800c2c4840702e800000e01d0717100c0807a0700b40e07980f8407544510000c0c00303026064030b6070b810311b030300d4060b02c950024001200940505004102c4a0303810344100c102d600c07002001041d0704e0389803009035424910b61240076a059500d034240103000e030742c0f84506180585101c50300d080c0e803407801d0706154407000d0b010382144080504100034001c00302e6002041d569111440307240040c60481d541000c030010f01d89070203580302d207024a40c00010260b503208840340c11225141d03000d62080101140c1107035810a04501410354200c109014404030740302c0d8015040c5030341c02501c0c05217041c00c5041c040a0306c91115a2440c242c0c2c0c002c0c0c020a0f04184120035049a002084008110708545d80301c01948550008042c6410400c0c00011800740c0c50080070003070000c0c06c003c2e01103010803084401c0c9c2912580280202c4c201219404e0700000c085100103052004408101c004c9c00c4c244c40030071000c3e0704941c40900541c3d44242c003400b44400710b0700d25100d401074180c0b003200c1ca00c124441426040c0c1c140364005080310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218802535 1250 218801285 218801287
    0x1050f180109021312050a02012307150b06030103110102010c0f080402150d0906090b07080c0a1805040e0105040c24030b04020c06041a010f032003120307051c02 71
    0x212001000c2100074150b41005a015858041070994019085003c1e4044000c80c0582e003080018803202150015149000383d80e202e08180001100e007a0b6040d84e0034900480e020104066804600d040c2400c1c098042e4840f0080303007038140440000c185070020b801c256250507007003105625640c1c0900c2640c4d809c84d824140707801c100180b5040500b020000410207806540302d425008818039030103089811400c402070f402c00a91003581043e400400b5521400c480804030000490386c600d0080c102188124400943e040c0382c407040280403145142d00345400c445405260f80c1c085111b58550103804002d141075000002d081c41c1500341103125108036400701124001c0195012540000c800351511401054100410300da213500317002c10300912a141c64004280140c009000800030100070300d80304283e8440001a26988451402d40078400c80d100080a58071503924036000c03000108803404107080300805460003080703011104402648201c035914002280040c20b000062503c00204005c3c80400f0021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218803785 1250 218802535 218802559
    0x301110d0b18250207180207020f040f090501060b03090d0f020705030d0c05011b0504120215070c030317060609210d0f090f0305280512030105090a02120403050901030e070e01050f 79
    0x2644c6c8030800002d03414003a03000900e407010754541e80861200000058010420300780c0c010b200000502d200c4004072410b5080a600040ca02da0240990f40034102820141c51080381c086000d0b0361010b0000804015801800800192542c007486100c03140701950321108541c807900d00c0c0c0703a801c40d03003000302c000b02c4600600760060405500c4015035050744c69080b4020201c40c03460002511103003411900e00f07815040040d03850100440d400105086030304c26114002370384505000700310700d588101c801607089142840040043e24103840c24515168070007400c268034030b0385812042d040c84080e04101012507020b02401100507807002054005010840c0d085401605582c0c650341c071014003040c04445a071503601c48a0010303131744141100c3c8159201d402c81d44107240301c150401c55a0001d120300d5105d034103c1c2c4009591020305000310f41540c1c0c0c05c1040034107035070380d85d035825903141d0031030452181019a200700c0030030080d03030030000d10700640228400984558035280411614a980707100b0315004018512036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218805035 1250 218803785 218803799
    0x606092b0302030a090e040f20060d0b010f140706200c0106050a06020a0c0e0a020906040e09010f0501050d02040507021f140709030c120305070c0e04110301110d0b18250207 76
    0x1c4648450f0300941800c256901500c250b01c0f690500009c0550020380060301c070b4028031b0300d503101020410081e291b0100c3c0d40f841081c155004600000c046201d80b500304a50000a80103501106c6059040f202e0486580300128002c290340e0801c92060102d40e42d505018415442c040801070b00910240c4024168840e03503a9417401003028034481c51054104000204101c1d80c3e05030103444501c1400740c81d081c2c80d107a1b01d00800b00110410340d44201c1c01d520b00300e2103050710103840c080c11381070342c6010300315484000b456800d000081000824903c2140500f112400c0c465008420640d02c00f0800c902c0403400d014186001400400b026169609111030708804000055202d0075a00403150086035031030910780a4142550345109255005042c610245070100e5010f400e4000d8074020b0703001e07200d034400441d460400d040c201e400b411400003400b6001d03c40c2c4400d1014a0300500000700024001080200700e4800b0401700640940c6c00d100f81c8a00054040400c0e0341000e40f030000a062031004001552510003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218806285 1250 218805035 218805053
    0x1103010b07150612120306051f181e08061e01050111100906020409050603010905120a1101090803060907080411010804240e0d05030606092b0302030a090e04 69
    0x50402e040c401c1ca284160025030f00000c028111030450301c0300f600041c43c01c0364080309407511800100e81f40c03110205460500401c40c200186000b0000c101c14070002200b81c45650007120036099000f2030120215001a4101030312400d01e142102c0d003450b20741810340711030404000600c0a00e85040540917400c0c071105014425044440c00c2c03c10505d000e00508001341003410130340c0e06d1103809040c00000410055a0f40c0140111040810100105d41354041054261072440c1c0014241d50b001d21010701911655400900c2d80d4109030403c1100b07400420090f80c02e4801032202a10815400710400c800d074107148a007154041201d261081803440d2540d1060080c90785441007504100f0110009410010542d080d511890036005000004010f510181e1014000400d00608107026000041e22020300038030540c1d014400003000c803806c1c07210a45c10301c000c8031080c1d03030700c20101844043c0d0343c40c81805040460032124040c0c1d001d10780d12107651a01505c40300c555031003c43c50320b01d640e08010104410750 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218807535 1250 218806285 218806297
    0x10b1503060f01020321040c0524030603071a07050c060c150a0e03180a050303120a05040606120b0a0518100531020901080c0a06030c230d1103010b 65
    0x1100c8101142d0b000e00101c2c618050509451002c84241e441e194141101289551203548542000d600c92030f214410310940c800080c034101690900c15100e40000c000c0d400c0078590105001d02158901075851020300c945540000c044100040c0010706001403000500000000d15000c2d40c502d86000504624035584003601c05171003841900c100080394450340181c01981c10303003034030400f2640c03270f11a04030b49040000c4880198a1050340884030000f10b500f008026a1864126000f1068441d542c815103440900f02c000e00440e03c040d51540c020038140300603d05070800038099218500181f5200c0a04000c4500c0540508280401c000000001c8203001610080b0040248000b01c0c65448220380c224a000d882c11301c4142c0c0c07890113480e6003280c98104500d80c106500880f90000d140c0d070398868a0343c486002c1500c1e01e802c02c45891040c40324500a8214034180c0039145095881440240c2a140003c2602d2640038156903000420741007848640c0a04c4810103c3e4100007407443d49440b1721030085204031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218808785 1250 218807535 218807539
    0x903030804030c08030a020c21090f0f030f1015030209131703070f02120a08010b070507030b010b0319061511100f0504120903050705010c060e0709020a02010b150306 73
    0x40c00000301058411680000d08651001d005138a0341403222012000e0342028885034000d100d0740c11200c00c84d400324000103a00c050181c100d40d1512174200b00b0300a07600c0f401c85040c1c0d040a450040000c4075101000ad220340048200007414040381c9407010300040d0303a10905010001080c01d6014000740e91002e1801d41c100900007900f50071882035282003042c68504440034600c0003804810480c07072507080114011051a254242c941d07002d082d11148107070b80545c824400000e1110001486004086e500a26100b40910300f141c803070503540c0d91b58036820702c401d030001d000000d030110500c44400e509820108421207011000e2000504140c0760010441e40717082c020042103c060b4248a480009214050088064410502440c543c068003075001d41000d440403501c1d02c480d000944041403141c0b440d0300a4950040c0640400343c42c14004492582031400b0549202e035644c1201c2029607008c0001e100103009104000d0f8032195036550190841c0c801e66980d40c01941410040180869400200c962000701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218810035 1250 218808785 218808797
    0xa08090c0a15030b040c11070e190c02030d24150807050306060408010f2a0503070503041109040c06021b0102100f0905061503100903080f0615041d1006090303 70
    0x4802d608801030a003c450064000303207407418420340c0590005040148100b591304176489140c0d149800034407045c04417800660a65643c4892030030341c11541180c01e06044610461781055241050b10b03003120f103040100004507035100d0845070314100c4030341c95000805070551707000a142c0002e00043c100540c01420001004400000205aa5550000d03940540100d8000300304250340e020513040207000351503094031000550703640c103811035038440b81001c40383e4000d07502c080c25034407110400d85039900080c20440c2c20785c4101600d40401e481d011406840b40f4000e01c028100300e841c05101030f0402c882c8483c81180d04580e02d20229151342c000900e002ea04901c4440061070000700c41c0d5070001480c003c44010401d025520510803140b041841c10198070204038103407000c1800451150040f0303103082d03400901007200800061494800c02d108a40e01100c068804c1c5103d40045404580a0340a40c000d2100603d580001004070810b00007d50780c01107400010090071400d0400103418101144001420080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218811285 1250 218810035 218810069
    0x1a0a030e070b0a170604110a0f03060e090a060c05040807032307060f14040608040303090501060e0a0c082a0c030c060703020705010e010504030e04020703030e0d050a08090c0a 77
    0x8801c000420051018003030040c2c0319501c400c00200042a120320112403480c90b0030206001d403a09110380c0381c480300301d81d0b1401d160540d401d005841d505101e0242030280366030350304005850250701241d14070440da00f6000e404840d00c10300c0d0001c2207078440c1c0310420420905000910425400117111030503030741c010761400e2a43c007105041d4210154000c0d0715074a140981880017030b030960400901d00d1680c0341c60300e51800341110081008424001c0e4400c10000445030808180464042c0e801000120300406c004220079031151081d0481c0c00094800302105a45d4140c003808690303000800766040307075500d92604810a50342c1755908404070403040f2803c2c40c0c480000c4c52001044104210743c2c0c404148400d65406141c03044004d0003d401640c004c0d14994204521000da425040c0b141e144a2581a00c403541004070003424003000303400c43c04c011014182d0740c0c401c40c089800c04020400412216550301036443c011940c0090800d100070f860710030709070f100034400a0305a0b1140d81040c180c50109440040c488 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218812535 1250 218811285 218811311
    0x6041107080414091305150405031908010614130b0a090e1905070201050601021f090c14030c01090303020c01081506070308040b16140901020a080f040303091a0a03 72
    0x4460040000c200020015002401c4000c1004403c040c0d1003c460b100b8880e40c0e00c0e08241102094204001c01d02c2d008a50601420810754880a42190040f0f044904060a581e5580d4207547d8808010700845c0c99000100081d0741d1000d5281481701010078081c1c01e100c035243c880300901c24503000340161404003140041c10f191280c1c0c1e84038000e10046e0000e0b203290a00e4440084e22000d103c0c2c44010560030f050000e0203003070050240070301070901a40203000c501600d540361140c111102d4104840b094a1b4441c48002c2805600754201518203400c40e4039001c0e1005040518003420803044a05101c1508070400120340c001c80c05007070340c0c4030a0803c01c6942d503c2340301041c00f01590314030807a4000b80120b0b209040c1680120303118403c0384200600c01c06500d81c480e4540c24842c142000740b000030a20078883d04101d0800001c0d054168042c01144c0f5840d00c0c80d40c8126150708070303411060103100c3c042020801c0c1036118081d14002c014a416804401650884000061085281300001e15840d018481e07150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218813785 1250 218812535 218812537
    0xc18060f02121e0f071e0506190e010608300301030303110f0703080702060a05090c0d1b1d070f09031103281b0b0403170c0a06061d0f060411 62
    0x1026149a41c0384c1c0d290800d00d2012940d400c43c43e000e5a8401900d40070000c851400e45201d81c0e5150040000d01095844c1028011848070302c0143d125515111107114003090b4090055801920300d11000d090b6840c1c524006003401c2c246e2200c01c90044100c050220419a46d0f8800c407819242c041c60045448440031b030551082e4819480c1c05c4407004400108001415070008034207001d40744a90a2b0390b0240c8410000005441098239001920341040448041c00c0c03800070140703d885441a0b004c03410882c00101c004408001c0c0d98401100f403107040c100102400400d094007a40580d042c01c04680048041c1c400030824042400018141d0700720820f20200b5030342c208140c5c1d40e554140c0244555401c0c1780f0302c41607085228560215000d032141485008200303a1840004140c882c2c040126081c1451912480d2440141500d640f003418010808000540c10601199403114024032010910b5860460350601404280303a070310303007000c080c0414802148035034080316030045001c48020500e60746003c0d5210302 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218815035 1250 218813785 218813827
    0xf0a0f1704080403021e0310090203071505040f061106070e12011104090c110604031b0c0f140603070f050a170108071a070507030308040311010c18060f0212 69
    0x21080c0c40d2030400003002452001001503a00c01e680389450b20301400c0d900b4040032035030848070b80d040c5c20004000d50703101c649a011351142d50000301102d5440b9550034503c02d48640303550780c401c0040c6000a040c0b1050790000400707001080e07149040b5001ca041460010b4071600003402201c1084001c0e40e8802c4c0e50707031b00e103070010301f100054030000c020280c0212034120091340248605c0410300e0804043c405446e0089151480b4481c000028102c2a521a0f07011141c1000014140da20410015101c1307002c61483c2080707502a0001000044000c0e003012101d402da075150701c0d03440e0300ca00d10800401c50711507441a40c0d60036854490611580311511300d4415140182d0301c0c00007400080c5181c0001640b01400500c0320116041001c407a5003079000310811000d0f40c4101c0401400a600510307003000024803400c1855030003402483c0034808080e10380e103101d094404940340b50001032a4007440000c43e80c5281e44080007003a00c1e007020203240d681c0400203500c50324080642c2c0c860080206521200c8000d01070f140761 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218816285 1250 218815035 218815067
    0x21c080601052809080f07120c0b040e04060b0a0b0d050a06090c02010605120114010b090102070314010515060306010c060f020d0623090105150711030f0714060f0a0f 73
    0x2038543d07100042208010443c0045400040b0745200015050074041450a00b03128041d014041850400b140c4107450f841a2000310780c8114003e5000407002407000240000e4602d00344148100e0400e411300105840320480034521610303004808222400354030302140d0402215a002050582c0c03801c12803401090340d40d0200c07000c20304210202d40718690640c04401921411191405d0303101900d11150300b01e8100c0b002500c189800800140421810800502107000052045440980d129503400c0d032000307a03003103051000e13a4507002400004400100d440203140410381d01142540782101c0020304a40d0000c50242c52903540382d00e00f00030500260101c503c1a8991030047c0295a92003100d1003e1001e40e55a610404540d0348a11f0540d103041200c0030304842d801001c2000c202118803801456034400407080b00c0000b00c5100440e000d4901744191056141d1540151507400d03d00b00314002c804483d101540d100340c8040050380980000c0c0703400d0394100e10303942c50141c40146640300300b03890206464140c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218817535 1250 218816285 218816317
    0x10810050411070b01081603140c03070306022107200a02100203040303090816030312150306020306010905010c08031303091701050105040f1e1109041404030e01021c08060105 77
    0x1032520b8407000c020129a842541d5a006581c1d0f6821410f448051002c41698003407035030881000400d11100d03001c038000170034a05980c0360501c04c00000c0d00e01320709030744112001600410280712304c10040d0318120180034680c0400c81c4503d00564014a8682e13100d540c080e5400700309a0360504960304110b228250307a4050240ca20b08111044040c0d40c0360054441200040c481005c00f00e0344103804213060040720810b8240c280d2941c1540d4003680c200200812070f0101503035880c0921103071a10600e0328401103000f15070050b07032030905400040c030101071900414184200040c4031070000d024001100c1d4072508c0e0002803000c600c104c1c54101c8441d0f6841d44518500390694004c450b0b01e04043d44918100c41085904100c002000c2c81544d0644404240c0d8900c00c0c0b10381c054144880c841c4d604410800410103908514001410001504807450030582007010108d000400c800c25401101d40da080c802c0c24002800710035001c1d45034856030b5400d01e55000800901da004030302c0176400f500580e517030002e000c8021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218818785 1250 218817535 218817551
    0x210c03031216020712060f0e100b0f03030f030109020c0c03060907140a03031d06041701061503090f0602090d02040f09030f03020406120e0307020604030b070806100e0108100504 78
    0x8070241c482900c06664650002440c4000140000380d403500b20382c04800000c500c1ca0441d200c08004081d0102c0300144c04e0b40b54032010001240900c00e12442d0001c5481c00515460188203001101e004500840c5c02940100000c0c10100308081c203403411940d85400150f66174242080403403e05000300d002580502c100414442e10703100100d4003105403a075110007161003080b1402042880b00316840041c001c580220b0101c1d16600094030b100c0c001c0c1c40080e20031403800c0c1d0f84d0841c40d0810f0b400b044421843d0303591040d007400341485020804111140d1031500b400b0b03201550722803543c00d03010010700070600365001a05220f03030784800d0305120304940c000313004105480d8601000b2002c4c2140300300450004440b51014241140244207490685205a0710384810081c40c0d801013008040c084400c1300d8510052268800507546c0c2c1340103001851040f411025141420240a0103a080180a0130b01c44c50401c0c0745601e4195108010400140c0c0174680364202d921540b50b00f614484090300040c4d04a8201011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218820035 1250 218818785 218818807
    0x70804050d08070501050a020403031d01090e070f0e04060305070605180d0b160c03050406110703120324050906060304030c050a03031a0628050d0507021b01020c210c0303 75
    0x142100f14001e50081c0215035440d04064101c1c8207030300006020a02c1c5c041c8003001041d4410070f484c403590043c1006d401540e25003080740854941140c00c1c000080e40c140a10004980c02000c4030030715502990140401400c680d100b0752501c1060081d4000c1060100e5481f00c007407070b10b12118404001c0504007503080310160508122803181261108085040c03407440f0502e55200740b0080d21200d030542c4e01c80341000d080c07000486030f0300c1c00c007051880e4910840f540800841d0081c0d5074402d8952094900003580741c02c0400d108442031044000098018001d00c0401a907224810402c0d030019041310354940d00c1e50343d031034140e410f00c0f082c480c090034910480040c07804040c4c16a010000c80c40b00c0075851042880b20f203040080c113103d410b0b04030030014075600a0b00c0e1001e4005070001007112143c03c105003401c540a40f0907017110f0084420400681c8045501c4003000040c40700034491003802c0c8050614400743c5008280ba806035459600801c01d85c240c450140d4810611400c540a00020300f0f603a40c0d800802d00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 218821285 1250 218820035 218820037
    0x9010306111207030b090915010e060a030b0c0c120304050a1101140a030c08010f03020f09090a050a0c032f0907021e060a06051818070e010b030a0507090f0308070804050d08 76
    0x107045d81c0101005800b080001000181c00c2d1020041c401d40c40c80181e003010b0304640308000180c41507402c402d0004001c8001603011a00c0b031b100302d413485422601c0c1d0b1801540c1a240010500e840a0020410414880490004030b2111201074002d00b1030202d1810150040f1100101d001320b00401c4440442c584000540c560000680031040da500e0b4000360340c8511400c0c2c0b038400380c0c1c0300080d8000003a07200f06040307041c0b000303010342d208200c54144c680d09001600c4180c05d001c0504011140b2211040d010310401c206c1802c0301c48400050151050409039240c0c2080c081b10380c01d200d440c07143c0c48210018008034400c01c03840d072000c155110400407040700560515035030003065070303204130f01030900101051909201c91314684134403ca60000d5070a8a070b08116010081041c4041c00481c05141d8002c186013044054140c0204142c001c4181d5a15102e40043c00720364019040c042041110340c004c1011000c035074803000c1034940000489a40b0941480c0211103486164801500061101540380c1400b050388 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 218822535 1250 218821285 218821301
    0xe060a03091202010506061b030d0212010305010e15040201031d03041401080c0702030601050114130e01080607021605011808190201021902060a030905010914010209040b0a050901030611120703 85
    0x34000e0441c02c95060050b0b007a00c100319055500248140050080c416454060303040440e5842c050324174202d1001c82003826680306841c28a000c146075401002001800d1003040da0031900c4001600c41090400341e40c54072010081d202904041e1240c003c40079113040840c0503205141450110381d600c9a4a0500c4040c0200141011b800300d110800042c58a800041c225018190300038040c00442c0e0a0030300540300c4040f021284500030506000d1101110142081e8401410940d0b6240e040fa614000311a8070f0302000601c840300b190486c440e403a400d50b087c80c0e030301000d0f0344090030f261910f001e00300418021001180e2140070f8034481d1030800403d810342c5050b5194043e0007030b401d840e1416078000864113040d00ca0b510003034126200f045000e000a02c0795101c035009520420000c10014410b480b2076a0f00c4140404030185654002040115880c0c140b00d6502c40c40030648410040514000c0041d401d070005100260540d5154070344180010165400c54140e0908090034050360b007001a00140180002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 218823785 1250 218822535 218822543
    0x30601050c0a1101140405031510121b0b070c03080d330602070803090409060b040c0206010e0a0608061501030213080c180c090d050c040908030f130201080f06010e060a0309 76
    0x18050b500617055168225002d40c5e101400810b0403207a10041c040400900600c04030300100708101c0401c0f1030290000b0036003a0b50041c40150034806140720140300e0340314154020006004104545400a0f07058020201100e82100015480d507a600d00300700050305024031020319280c003940c00312401c0803e01030b1400d400c0f074815099111280d1a484140d17940c0090713005420490340240101c0c585494141c103d0210310780300c0c030400f08000114001003000e6035180203600000d6000000140911085a07000344d031700c000c0f02c02c02408424540b6013219107810000d030070b07806a6071903111fa40303040e0390003a01120107000c40181c2140000354dca0712066140c9420b10603281c840d401508078038402c0b22128950324020303098214840d183ca050383c010420860300722003080390316000300d00100072503503550300c02c1c0c01010780035041c8a590b07454800c230f96000c2c04000500d500401e4000d0b82ca8140580da05c1804141e002000145404084e00d95030010b0380c5507280c110100b41d2103400010700244242d03050300400081441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 218825035 1250 218823785 218823797
    0x8100f08010614090c1e09060316030c02010c0c0b040807050a0c150804170d060b030108030c07051819090818030c0d03050915040906031a01060306120206030601050c0a1101 76
    0x42403007000504c080035950003416200500640f2030780e2106034650010040304072512403800d6944001700d45107401c05c0701e03100368a15120070103d80894042c0180d080c00120303817008021a0b032240402a01280034010702903c1805060009420041c01004480075623410204585180754036282209040c0403600596140b03001c80021003000c0b90040ba0020b02035a402030145909503440d05c1e200c00035400190080706090745840c1c00042090301e001c01140600710f144d01955940503000391039803409403180d10213406050380a2205242140300d01038030707400000c1d4580c0d0501e440030900f441d1000c0c00ba244400b401407040002d10005060052405890104041d41039600c5140d150f02001010902d524000c0d021071f00070040e0b100070307160680076000704040031941c0900b07194071110b180e002c5a002c0d40088030440c071041c80c4210101100e600c07050062442d45420300c01c8505156079160b83e540c105070000e004441c0400840c025a00440544991035450301c111107901ea110300b403410365904032244050209807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 218826285 1250 218825035 218825069
    0x607020607080721020d15140d021003140f01060906020a080a050f07080a0e040609020c0606040c12060806040b010803040b0a0507030903020306190b040b090f13080a081b180108100f080106 83
    0x5035230103100c2c8c200341000340b10443d20120b940038003400c1c641d800c1e007103030800d903075641c5002a140900503141e001d90300b0032100409035810320384003030416061038100000350360024414000003901c0000715021401e4901d0710a440d40e000401d240c042c0d008080008240800203d4094006a44001c03c110104070444082c415a075641e0720000491062207184030702c0e904a00c0008003281010b07000414803100c5458142c9049000b41084070454a031038100210319007001051005001d2011012400b415100c40038614007480d00c52454294810400303281c00b0b000004c141d40c8141400f034200d800007036402038162002440d0210703103c2c441c407580480384840345181044000c8142840e108a10164030058a61410390f01e0b00000031110002c01031038000c41c583c507400e0200c00035008102418040c00c56451b040c5107804e02c0c2981d500c0742c1680b06d102c0190008284003642108140705103c51030810700382050710719911064240c004842c5550010300c1884c001110001752048158008011500343c42e052000c6d0702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 218827535 1250 218826285 218826299
    0x10c030b010c110904020109150e0f030f070e0604060b0a050c010f020a05120c0c0304080609100c1b03030e0f07050a0e04020a0302090703020c0a03080105030607020607080721020d15 80
    0x10301c00c0000fa1010510103010140303402d01d212404d070014014100108403e0350740b010481e90360451080034002400850340c0d040c050400050255007090304030b0140c85000050555259581010b01c21203003c1075042003c21001d444951000c030151a5001a15688125480015160b0791001808019540c42d0540180c01030309544291202a031a43e501c60745800d6000000c004150300142001804103000c22182c0f40407003003040180000e005000240803986803c0c1100740c14001e4a100e4030070580d060050740d8410541c40415458800b400606888803081b0701d0904400500303c1c880c50085070301c11840000049080010031030202c1b001281c001c0c0180d5219502414620000d42e0001d411404141c42400145032a0f900c0381d0f44441c0c107140040c05c2841c072481052030010f2a120a07804540448014800b0342424852640d200105000802a80c01c0040000300029030040c000d03020020707400000b48031a01d0500c01700b010441e080300b080d926820104041c01c000c00c107943e24400400c02d50040010740c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 218828785 1250 218827535 218827547
    0x90b0a050f01051002010b130c261305010b0a06020601080f0c030309100c0b04030804060605030d0c080c010608060c03010e010e04050709200c010b04110f07061a03030a02010c030b01 80
    0x40401a54480440c0d20f00014015541c004400c03840a5541303071140041140c680564100c02550710a20200d003980300010090140e01c41c149118604d02c1e1038200000c0d154102441094000100003450b401c010550300f001c034010141070700d543e41c0c840344200c0001040c950000d1710787d05980e043d00070354151030720030f00762039981d480395454441d0175410512042120b1301d0460341112285440303092606035041143c0d981403202c80304036401c80100b412402400144080c503c10ba4018140c00c6d00107000c0844c0c03404001d0081c4603400002450008001390029035208203402100c0105001c2d8111000c078140154a030b0130a40007402040301d0142050000070f000d0080190890281c0e4100c0702820803070341480d0048012301401400d80f09001d2424000d603503060880001020310a2a40000140d10440f40c0d0802007900c90f004031000c40d1400602141d010042001d00319150709900a2001946020061400d29125820900c02d40c1c14000480c1c082c40e90354040d0040300c00b00030103540070012010840019250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 218830035 1250 218828785 218828791
    0xf0e030d11010c170105100306080304080d0207060305150d082511151902190302030c070b0906090603060a090e0313080d120b0a0308040602010e0c062107170a090b0a05 74
    0x8604401380c0108510b0400ea0102c1e01e425000b86804900d0503180c010007403441d07005a10881c0c1940c802c00d2111011541030010001a104903d014401c07401c1989000042d5598403811501c0303100c03203041c01820040c64104940071904103500212400d12400840051808a181c0076111142038a1074428149071603200b010b03850441c003c0260030000c035409410303200c4181c0f0b40740c0000d61084556091203403040d0003121513041c0c4658001c580d15803208441a0a01e4084c1c0d1048656800511800074141d40e281c0075240351000a81d18240c6036641e102c00901ea0314800e9101100d40f0745404a01c01940d40044000c041c40700d00c800c2007411480d0303210406a03691b9644603aa03400500042c8400310340c0a01074000411000d401805003004c0354494071600300541c05a40b203500940c0d034600c102243c01d1001d0118282c191402c489041c100070b848684118404e1030440c0c0c22884034501400118528007074950030b0f4a0041c201c0c0e900d8894989501081c00401c0c44074001e03207008685400140c190300c3c2038054688 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 218831285 1250 218830035 218830067
    0x906060b041a1204120c1a070215010f06050c07030c0b0909090c0607020f0409020a0602010f0b010504030203070b090d0b0c04060801170d1107050402070606050f1801060f0e030d11010c 81
    0x803d9556a05c9a5101c1785640c21880c0801c03410414400100e15042c14501081284200c030103c1420601d6001c3d19104040c1d801d1101c0d6a00c40c0010001d42c1541182a411580d95007005caa0b900c0c2d10004d90303801c1007180d400003080c8001c140f9001c06c0e4200b00001905034800103880030340d50b41d110030f041c035a5a030541340b60341c1c0e078400000c000d440e0060a0092204031205000341002c58507640c560700180c0442c51681050300181c0d520507400b0301844181c0951405907100f030030b2140c0f0309170035900420b45880140c01a07074007031540011540307201d031036580344400b40507000b1340044854145608000b003103a00c01c0c440c46c0c0000e0401000442e010f1100d02c0d4004841d00414000c001c242445041582c030350103060324001306801110b40025107619940024210544103840020382103080104000c041c807030100400b40241c03c0700d0386d40c118081541c91080e066681c9030074030399104007203110b040b00c202e43d248100310b426000d615003002619411401c2d1080c81c1c0a03140c000e00c40705501c03140895450b140103680d40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 218832535 1250 218831285 218831317
    0x10e04110319110a0302130903030c0e0924060c07060801050103060605160206040b0a0c2001140d0f060608070f2a1e140c010203120105040f0906060b041a 68
    0x7a00240e10b440d2450300203c40500840000d40e62034000580d0500035502000f2203a45488802c01055850302ca00381102c1d1071400c0051514003100c0109a00342001000040c0c100176000210a81954004118510142c000c18466030b0306140303192070340c81d00e060344680808645020008030b550742c0039000703407000e64810780c4e41c0c5414050700801c90354020848940a0f40c101d0820400403407848075032001071a452200d5141c1e610400058034180810900c480900b1014480f4161405410f80e401607500040da1211010340b6181c190070042c1c280208200e01c813000c034852800000280301c0c0e41099a0900c2522a07032619542d00c200a00c040c0c84440c20b03028004807044c40d02c805070b14280032a020005184d4090300d2805d88094011451202781007800c1026260903003c072440ca240c0c1d60040180c1001c1403020310103142002c800003085000b01d03106018481c41251154a150444121035112851007174021400303000e1255542100213450b0720a02401c4494404074202c8002c5001d6902101d004895440700740d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 218833785 1250 218832535 218832583
    0x30406090311010203100503100902011b03030b0918010e010504080904020a051c020403020a091b0318061113080106030b16050c011104170c0d021314010e041103 71
    0x184000c0c8500300c012828828051a030b144410000d01c003441c800d000300b0080300c11240c20030040500e402031411785044014181030000380141d0f4018400b29a00d441c0b00e12540400e4601d01d0164045c120700c861f4607800001c000f040080640805416000010180e0700801000c0841540c1e2400c0c0c81d41201c0107802200c3c200801071103402e1943c000e1184080b1854034504081c03c030714148d00b2010440f1922000f031074000c2814015850b250074004000e01c0b445600304840207801d1420041c007604042201c2c00d02d43d4590041c010280d110551040007903101e08108001d51003c00042c2540d0040c110b4422081911900800c1c5544140304503400c0c3c9401c1090066075588002c0d40907000302d0205401820043c042c0700b40e00120381c09004414041400a16030b9071242d0428011698000d11101003401e90361007090700d104503444924446440940503241e01c88003002c00e801d440d0190000c012415a007106038030002a5205101000c240039500c00e2001d240f031071144808155072800d050340d4410b40304200c0300314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 218835035 1250 218833785 218833793
    0x12030c0b1e01260303040c150e04020a03140603071a0a1b0c180902130e0c12071410051b013c2906040f0f15030507050304 54
    0x10869000034820120300000d09042a1502198400e80c001c0c00401103081c0116042c4a0001211040380c0000f0004c0d0308514194036034401d5020984030382e01507003034640140324206200c2c080c41d01c5d541101920555a43c1070012008006001ca014401c44200c2d40001240142c60045424001c50310641c0e81d41114265040400782903502007040c800511502c08400d2003180810340f401c0f41410301490b010152580342c0034800d80020140c900d11a8441d18040c03140c0016074500b01e180702840c00101000640e50310300011030b072801241e8504035510101c0d8403080c8061080c00141d50058030b4030481420301c503445140a00c441a01c2d030010540205078140615648401d514081266070b00030f003000401d000c821900d0b010f0185081c901c25800c854204040c01c541038400c1d40e840703c0286840c00c2c00304814880c000000a1610082c05c4640c0c11408241154070195a64802d1b10007a20300d16020204540e514a4a001032015610651a140b00501c1c0c56205207802403040911409607600c42d80d1560b512551 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 218836285 1250 218835035 218835053
    0x801051303030b030a0209070203030103060e0d09030b09070506030c0903010b0607020a051009052101051006080a020a0908030c060405120901020a020f120106090204050103240519080102030708040c12030c 90
    0x80c2264040c46400c1c1190091f948561340d450003180280c019655079411410040300350340f4902d0140411b548000f4201ca405030b806201e030340440350040c01c405855181c0d107d0150610080742d00c45036003c0c10100c18041103260030b400600c480e00303084008020115031501031100318000c0000103903003d042d03150204030078100540180b02c0210b152402d94411600c920000c7d90a03c0c140c40060b00454060510981d6070909104094006485c0224140740501d0024014450780c0000c0c01000a03a40224130b21350154022038110002d40191390a403030303c0d082444503055550b0400c8806542c2c1e4458100c6c944444a8a4801c6910800d07041c0e000c1c2581c00080d40038051845070f400d05094124800301c081b030200030b00a1242c14040c7c904480096901d41c58240014140e9140180d5244007019442c4502a030784518540e0000700c640640d82044000c4645500360006540343c0e0104007654000010004807980c001402403003940305030030f20444662210071000c1c25030008407000b804a48290400c00102d40024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 218837535 1250 218836285 218836301
    0x10b070503040305010509010207060b0f0a0620070801020a081b0a1b02030d0309050c0a0b12060d0215070c150f0c05030c1905010e010506030d030f020906160606080105130303 77
    0xc0032a4a040c0c0e8079941e4034216001181e2252160b580404c80324108412030141a5110070111081038080014000160425019200c1d1000303006801900075692004820300403402c482600c1510b0b070b000c0e40d8155050103540445e20110004940c40c0002e40c125115080b251041c01320480d1150803c0d642c1c0100303a641c0e841e44408141102988454400140d40800060050105075600401e070240549042840c0c9481c51082d01d20030304403020144150072112007a98100048043c4540303107070710340340b0219000c108084030103908800f0818a0f8200b10490000038030800d0710072105641100c0d5245030120b1f44242d2909000009201030300090401881030144007820f034000e030141c07890084104400c03860240002d01c1c5503007420f04205410b041c40800c0c03280761030010a50000740018076011000a403101040c1001c0e60a00d5960200c0c06841200c6d41e06035070b1490b40281080340e0b91028081100d00601440c0d8040350440e0170035501284440d018041e29001c0e0010003c80740100c04a5a0190b018281d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 218838785 1250 218837535 218837543
    0x90e0603010227090609060d0b06060d050708070e0319030804030e060406170f070804080a0207151e02162309130506010603060807050103271b120209010b07 69
    0xf0b00002c0ca9204060790340200b500600030160061004020611103140001003149105080c01c2c000c22450341c64140001c4540e81c1c4c011854042555190001400c034080c60b000d0702e60983c90030040080c000e4000002074080c0b506612a111407800e48400c042c0d80e68023914500002d10307914214180020b0068400f141c01900c20b0501c0c101015140001c5a200c0d003040d882500041c642c0002952140500303265260080540410500d0314a0321030006008901c000d4002050800c0c00240c1c01c0d40c141c824440031000e8000c03c10300419421a64200a20350b40b005008805040450518a0021400001c006007854800640b01c41c010380703010740320002c034001050001206411542c0e0014240d4072100121310407104a003036201c006495042c40342c81d000c4142c0100e003d05290410038040c0fa00009039030800c4850910b000300d01d40d00d800d1100d180c4d241d003101d500d1a00010030301c0541e00300112203030307c480d0707483e88036803100041e17944c4101002025001d44006508144590300500c00b0301a02e0b0b004244060103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 218840035 1250 218838785 218838787
    0x723030c030a0e061c0204091d2d01020c0a0b0f090607200a1203111804051806040f03022119020f0303100504061a031603060b0708031b030403090e06030102 69
    0x4203a1513a1414445c802043c25520380c001418400c3c0307000381c42801004168039002883d41280003901641d0b80300a00d5084100700b6040941c1030f0380040f801a2050401d0701c900080d91a4000800001ea4402801004952854081001503146107048a655120700c50100003492240c48403141030312a50b11020440341e4500c012405402c55031410002d0349006032098003c080d8001c0314240080840b500741802904e4914200050905014182802c080701501210300154644a031011f02c1c0c2245403224840b030840c0030310000c1000f0700c10340540400845020745c0a40d86001807101c8507034040340701225950001141485841030704030894211803290742142c01101c02c407060151810b46540c20842d0000d0564044401c1840039003054080d8100400780c40144c0030302041844502da80d81d0000900800ca50100b510300c60321143d100342c10040040c001d1058683d610200c1e400c1210241d44200c4001801d40c02501134060030044c91000c81e449280c2658810300103d06100d0445d070380ca40064480c541c1590 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 218841285 1250 218840035 218840047
    0x30307020715320406051c090201050307121e092315060301141006030f050103030806061303080c0c0102010506150403080703030b1903140a110d030c080723030c030a0e06 75
    0x4818004c0010300090b0300d5680e120280a84002e079050b4082d04129204d070301b0300b2044030050760084c0527250408264140400c61101140503079004080b0464183d00034280724403840780404040d03000c2490540120882c030b49085081001030760b0148042c9502c1c05c00da00640140703000300303c2c0d011000d41040c0d0050000c0fa54031410300f41c2c05400c00050b190040710f142006001c004c0d8031740500c50404544440034081c8183e6246403405031000800500c2240039082c0002c00000b0188a01404409180e000d480e841e220800510119580e80d10040941d01542c40d0002142241c40d009480110040042c0f0036145007030301b141d450f503855801040c8100e0a064941c031a440141d82c0c1d01c1100006074551100c24000e03a461810031300886220000070a10a4003d4444040403034003082100c81964000e03900d41028584601d000c88201010b07510207405480049010410840035010b200d00e401a14081c0c51100441c1501444e1a0300c541c8c3c0d03070210654020819403000f940030704140e41a40300c000300303102c5c00d00d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 218842535 1250 218841285 218841377
    0x1f09020d0b040c0f08011203200c0904110f0901030b040f021207031104060b090d02101b0f0b0106140a03051806040605011a0c120d09020a0305030307020715 69
    0x9010b0100c0c240454400341d00407820503441170009004011484504403e40c2c01501c004e8030809140d804041465005090f807881410104055000d281c00a0450700345443c00d400c1403403090504c022018420180216040d45518002604606032034003c840800b0036202e40c1d850840d141e11000c002c0340c01c08054032041c05018001c1c403044004600407014051494000700410085031030b0b43c3c00040040300309001c4020581c40b407011000003d64152404415425011429120309500002a402c03074103407201c07081c0812403030000d150400c5104982c0c003055030743c075007609403000581e12079401c0c116941400071962851094100725044501d84440703109040202c0c0030542450f0045405036141c0f61208010040c890744482596807004801044c2400e141c8020009902c80003103600441c031070386001c41d8075403000c00541d203e0502c490303000741560b840350703520324106071260421100c400150040c11000180c28034034607049028079440e035036104000c2c29100b600031543d2640000c000e82031002c041034a1011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 218843785 1250 218842535 218842541
    0xa030e040510051011010b0901060816110f071e120303020d0906020a0503091e07062105071205010e06060304060507020127110f010c141204090f051f09020d0b04 71
    0x82d484d81c2c1d8a483d9445d400c549001c0c2507440410255018242074001007002c00c1c0d00151301034003d05c581224002810000c0d40440b04800342c445510801d00400710348011240c0c00065450868603444800600070501200c02d06540c0414440c03407070142c0c0d0300d90302500080d00c00d1b4003c1c030010160000004030070741c0c6525044100d0f04012624008a100002403111101d0200a800301d180c0d03141ca010000201078207043e0fa21781040b072185c142400480411000c020a040d2100c0b5003a001e410410040f62501c09801019034241c4090175104a1411001054000591042600c6000082c103038a07d0b6448950350f050041a0060111085550310160f031203140b02090103498031f55212500e1800103101c0ca0074150700c51a5030f0081036205800a07440d016599070421843c08085030401010000c035225400c45600b00520f401c9000d80408000802180800c01035000683e101c182180030403156035101c2001006001d14030000040c210308481c1040110030315002000801000c56000c240807540fa40402c0c20707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 218845035 1250 218843785 218843809
    0x506130b0d0c0e040605010504090b032517010e07050d1a0c03010906060c120f09030503040e0109060e04031e0201060f15020607170112171206030c030a030e04051005 73
    0x2282e48074200a280c6540c0090b0f042031a0604940c2009003501c3d00001800c188224401d42c1001ca40f01e1503800800e030790034480c5400d590324007000380f102582818904070b07146801d40036250705030070120304074040340c3c0f014810320128141e02c2000300b10503410f11042000c82c844090049618910021011504890443c0d0f002e000320405040349881c0c2d410100450f080e00c04941001c820003200507108070201d60301100101c02c290450810700d07544041b03281c045458050540000c0d00d0b5120010700022041c12821b000c83c12110419020807006440d11501070000304141c0780a00011100034a05502002c41b018590354003025000009140341c0d00c0ba06480b41d81400d5002000300103590f80000803450b01400000d511100c0c601d426101040416007203180b4a5060003400348a06c02102130504001a500306c074980b66815151080e01c0f83c00301a444c0c804104201e55a600030701545200030f030b140c103001a4001c801503158a075803003802415001d2000800c802407000030022164100014152180e50007166 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 218846285 1250 218845035 218845057
    0x3060d051605040605060a05030a0902040b0307060e0406090c020a020918010905070801050108030301030c171e010e0f070b0d020f040f1701050f0103200f0301050a060e0901020304030203040506130b 87
    0x51000c2c03074102004200c5100d64882030142e101008140380007036004080743d0780450764030000100c801060000c100200220b500c80d40c1c141c0308120011544503001249070800c4201102d05103c115107501502003034034200000c0501581c41940341c0001490140c20329030340030144040305141e4200500805007520320b8000140c82c990003100f0305000e0040203001d902c0c0500030202c0158695451a6148440d811091203600c001d01c2c500401c14a2021052101340300703000c840380c00c08050740d403d0071025000b40041d209484c41c0b44112103501441020120b019000c8030b02010103c0c1c1040308000080c4040d40c080c903099500030104010100d000e024080307528010701910485407041c1d00080da02e40382182e4000d4800590040d0f0072004000160044042072100600c81e0f9455220f0119080480c468480030340e5840c0d415400e090400282c500264020700c1103504401c203105590b25a01000c0d400c034882a40c001d40107800c104010311560400000401c0c015492f110359105960b0740c0e080680c21034000c140c02c55 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 218847535 1250 218846285 218846323
    0x16060905012408030406091203030204050307030b18070b030a0f0e030f070c0b0408030f0c01200d0b040504020a0e07050d0c0e0120072121030e06091203060d05 70
    0x90b801001d9918024050030070400154500f17810010060003a410b00e00c04ca4075000082c608101c201807003601501c000740310190071104e00320380320b02d000403c804089030700c60050b4000402000c826100010400200d03541c41c45030b5032440c0c8400c1c1a40e000f801100c0c95401c24030380c4440c004030011804100a0030b2200101d04101d4684407545050443c1070450361145034411000d1000f444180004000c688285d600c10401c0c075a281d03d900520360141c029444640c180031410900010240900c00081802a0b8114002c0103410005410481198029100603401ca200203030244011400c51074281c2d0000a00c0c1081410a01443c411380240d52045c3c42a6000440100700070056581012065000540785078524030104000000155545158410340840c01c14070003030034410020701d81000d00d0058008000c41000d407060f12000d81d043c03001c00c402c6000681b60410380d0b950300e00b010034824020a822000b501b0b600c00b007420703a5101a0409040283e004a10000c6e0000044007000485d10b0060700b01d14403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 218848785 1250 218847535 218847581
    0x17060f09130b0709060905010503100b07050106030302010b0616060e0a150e0d0f080a2f030f1f062307050616050a02030406051602060c060a050a111606090501 70
    0x1590560740d01408034004d0080d131000a2000c0d64200360b2003000d41d40c007803030600e4980d81e600c0c0001c9010720b0250722550703001c480040d418050200c11741100060700d00980090251211303400070b121291041000b455003c003402c15107140094041e40121900d03000781401c580c840d00f116210a08a08145030440c3c03807907030340c48074804801c41046c07001306641c20642c2080d02140035050f00c0617180d1200181320704580ea948076804501056106480042c101d9030481c85020100e901c0900b180c954400e4600e03282c060001d400044600d40081080300881314002510600a8680070064030703607018103400303400e112040410348c80d66440f105001c0e0180ba4000e500814280c01c1065180c0842c1d14401c1152040080421407451503030703000000c035003c81c0c54a2030500d50342c0055040740107040c03c01403002940300400151184810000242107809520549420040c584600c00c0505c02c8451141020311840c500b844884a803202d0100a650460301410f00420022043e595081c2143e9000000b943d2825061680d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 218850035 1250 218848785 218848793
    0x307060504080708011803030213080d091a031b030702030d1406040b01020c0321090405090c1207120f0201030f05070f020f0a020a0e0402060f0c0d1202070317060f0913 74
    0x9400051035a04020040c42500b800b006c004440300840250074143c0024100811202c82c880c118020240710041e1034049407a550010594244d41c0b040300d070314403104071104010710182e50440b4081c1c0c00324080a00c0c01000c034030591601d900014018410f41c0400e0118240c1401107016a024443c5070f001034056510b0070604010854121109150455015000d0408941c03000036403924034204060341758912010700144283c1e24400d003d8240c0c0c00030300741024802d076540c00044002d041d040407038002c48500c43d40700c03006641e007006115008c2400018840400818100c06072006458010303d4045912006d00400c3c900b80c86080d201040040c260701c0704001034540c188070292a644410014049219081c0c0024140541e680100b421100001c40403808540e036403821252450001b014254903480e80c4a442c9881e0005900c1c0031b80824130452551444240b9803086400d40c981c141c80e0603400b4256448002c0318910300412150b000100000030880d01d0741c0c1c1c051503911900c0070745844c5984852500c1c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 218851285 1250 218850035 218850043
    0xf01030f0c0b07151b2c060d020315060f03011509080a0c0501030606090b03041202190501050105190e0a0c0203130e1503030421050a200111033105030706050408 71
    0x82c0b600d020ba541084a001c0081d40540d648413120944460318100300301c07031303c0d415800c842c2140c6400d0703002d00300151220234584290040e41c4107800d9000140b00d0002d076001072003ca8840e0550010381c5440400040c010203515601c1a60440303240d1618500031515000214034040b030031036040d10000c0000f2800c011a43e4140141c20190155140c03240903c3e24210010200740800750009107100c0c0d028004a003421700c00c10402c084c40c003003440c00e40b800314420b0138110300800080c05014001e1300705503c407001c13142c1d0901076070088a51215040c5120395600001703000a00031035074404114007040040301d098554500c00600034010b02c500003035003401c009100c0048003c00402a5009420a2104000504400e0750b0010343c8102403100100c506480d01d0309a00300244000000d14403800c0b40342211030035155616181d0703c80e6003030300c0d400a90706a070240b1f0b954070301418030600d0f419090840962300c0303140b10031030304041d07040d00c4c424410710070f07031250002030070103d89820070703400581d01180402014034104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 218852535 1250 218851285 218851301
    0x130b04031406071d040504020f2d1509010305151e01030f0c0f050a03140a0b1002010b030c0f010513061e0504060f03051e090d11060f01030f0c0b0715 66
    0x404c0801da0a0301450000d280300c45546685480b0325502c000080964440030684410b60318010941461410b00e04056110714008007820095030710740c440300c0c0d03031907081003e20064019203480d40c00c0d041c1079842004401030400100820041e410a80d84452a41c070f41c41581d40106420742c0208109911981c001002c64000d50701070881e4504140140c1001130700030a400e10f1094240c80d0413941c40c1e6003103405601400070110741028200440d020402d1954107540000031240048840b65082f4903007241c12401c2e00c40c03c3d0302c0039034550000c2d0324490451501b80c0110b250410b0605110b410000c101c48194004100e5130310090218000c1c45041e0100d01c192000040303054004d04180d8182403c28000034200c60440c103008080c1070b6030f5401b1840184d0200360901c13003030064900000e99450140d08551b1a560700e40d42820100307054014803200d0900108049114841140781250180e00c0c40d01c55121144500d601a51034a0482d08003058881400d00180050b5010f42c1c0325100e40b49404c03c217031080342c80d45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 218853785 1250 218852535 218852537
    0x303020409181515030507080109020901170715030b2805030d0807050d06050423010902270415030f03170f04020d031103070308010e1003030f0302130b0403140607 72
    0x12a0b1207000158011140142c52141c100c03001a04220041002c03484021135080640203105d000c40008040805400c40c002041c400c0c0e136089c080382d0342c86050841d480c00c00103640800382c00c0400c040c04101e07901002d0380641080303440d01040d64000a00400ca014035190700d42070252900381d480410b8840752220fa4001060305500800c10740c3c032800001010741c0c0c0003074040c0382042400103490f41c0c40e02680c4c0080e0042d110081041181108841e407040311014040000581e161204000085107400b91003036074004201d0300b4210b1260b26221001c091901c40208905501c0b035601d520303e4a04411558114001e58460443d00301c0c0c02e11241800b40414882c2c1c0c2480d01c00464401c20405640c600103501500181d05481040d80c00040b4038050b90703000a0250404262710003c40e0aa051580c000d41003412200d000f5100b000c29114003000d9541d401c642d0201602140402e2140b401c158800e900030640c841096452103034035522283d10f412a903000d5030041c1d8010380e01003024480388070240900c580210301c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 218855035 1250 218853785 218853821
    0xc06100608090622061a040b040209010509041104170f0c03010b0f060a1403072a021005070507121217061f1e02070611060c1c0f090303020409 63
    0x2c603642e568504004000c0714030081250011144011001d000b480c0a0b513001c4000e001041d01e0042ca685142500c810061249080030400c0c80903003401d100310b600448044c1d40c1d042c540201401030001824450700748100c00b4804010000701106108458a1200808805801c08110385000c080c5000c0d040481140700c1c0c1d24141d00f20038942c1c1c030070015200d0000242c440c6511091005002da92a90703131250810800701e00001080300c4507510070000010340f00e01c207024600c58891a02c50204600340020029007062000010307800b0a80110060039900741b10f0303821180c106403922036a248c0100d0a5008940321040008090489a000750001241c00114000d0071940d00d003410000f03011000ba0091b0444d4141c0c02114001420300c2121032076804892503000300c0d00110184c400035541c0d41c0714071031000080d16480c1c490304800310104007940100d103c5a003030790910405084208041005c201600405030780c0711f00000c92000c040c020b030401d0314003d480050b01c4034a01128141910300244011800c088 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 218856285 1250 218855035 218855041
    0x60c200603060904050309040c1e0302040f060525060203180105062b240c020d0507030f030e1615020c01170402031f02030103050106060f0512070e060c06100608 71
    0x451105807039000d40c2c00c5800c0c1e620344c0c44038249103003144102c0e205250403500b0420b0320ba034480d800480210b942945440b003180c030710103401400c900f2401a40112000307900c10960811059108202a02e4980c4c039500e2903020611024442c80d001c080d0154084500d19004400c11201070148001e80b040004104001e00651411400042158030000080040a0005920380d20000403a5241102183c1e000d050390304c0c0c0b50001141c0c0c403240c1000901a10b83c5c14101820403a44600c04100095001003a448150a107101598203440100c1d21200c88020159641e40d42e04121030100514207004806519010003a41003010703c0c2066441c440d4000c0540d800320741c298400e66405144980301c520007001c1d130748880e1100c2c40001c2c1818903558009800ca0042281034407002010390055040b248508002c20880b50340e02e4050380c080a80c442e020011445c00d0040c1d03441c20700616007156102c0154030f070400303030100c4880020358981c2103140c047d4219032011040050b021031f506049030103003e00b03040c1800d0520b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 218857535 1250 218856285 218856289
    0x1005010b0406020d080c040801090614060105040302150901020a080d020901090929030106050d2001020c01170712110406090803030606160804081e010b01080402090a24060c20 77
    0x603901c803a400400c040700001906d07005071481501c0140403c00300911100d038190908002414041e4900c0c1d02c080c0d849404a0318541c000c05c2203a0881b43d0281a424a902151180b01d030543c001241e080d05500030380e511000010800401018000c8103c0f00060b1030700b140f140014034050306034114803102c91600d0380542d032000c0d01040b00702c0c2481d182c8244a00b4002c110000c03d000d400302d03038011a040f42248406c0c404100e80c4582c200c4040041c00704d81c50b0003200540049a4072040b1000c45400b06107100541c0500c1e5100c000023950001c0d081c00c040411030604143c2d00101d4119041c0450340318008501131020b5a0300401210040c90480021804d505142000032680d1143c01d0040a0100c10300340e040c0f0130091141c05440003004020184c40700340c80c038014982c1c001350198050000f19480c2c0f08400900d9800389001c103006e0354003e4600d0700c641d52525031103001050051820580c19005010310b008202003035081c1c0014010a0ba18100a45000c0c43c10311038514071740181410712001c0d104600a90f0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 218858785 1250 218857535 218857543
    0x801030b1305030d0216050a1101081e01050f011701170708010e2509060605031b0c1c1b300f030207020a0302040f14090309060711010905060c1005010b040602 70
    0x5084d12410041e03550000068141c0300e00c1441a00920a0140100080078041d000150a030501c0b0280c1703c03d01a66501a0000c3c03440070790814010041480f01c0040c0201c2c00c1c404c021000350007040c1481c2c02e0b080107182d00d010a0807001d9004002c11000d2100d801c00541050100c0c5006045010091152583d0340072155250b610b11030031020056840207910110380102e0744004000d18403c40c00700101519546c004115902c102c031402a00300e40e81416641c102231003801c9900584401d0043c18411120480d001005034103d00709900308a0b40400c00040700c02141c024801c040d20a186000780d610300807044d101e240322801d000000208040400b040460b4024041800c088103501c0d0050b85c03108540700103042c0c04900c5c2c001a400600c0e01c040175488400f00d90042140c0c40d5200700b02199556200b109903902c2c4140704440c1e40004091103100001101c2507d94111002c1c1410301e50300c3d00c1d80b540301107485904006c1d44000294060f90006018514603ca9603000d000c103015030701d24050600c0c0d4007a40e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 218860035 1250 218858785 218858797
    0x705060313080406020604110d150b040204050604090e06090616111903020a11060f0f030406020d02070c0f0f050a15090b19090509150d030219030801030b130503 71
    0x50000000003075103081145200c0020142d202c03072180d8030380b038031120000d5440c038040b079085482000038034403282c0342c2c40c0104510006c1c6500c1124024200d10204203040a0300f0b4504056030400c0c1c0a00c000302d482d646000240c800703044800400684050a03044c0c6a10b0441d01401d1a403c50300f020051007052030007514000c08480d001d0400d503842e03044030310040f80b401002d0100005000003401c401c80415601094905116025001c0c07011929807810410045210384d90509508038800c02800210150690107141c0c003d00840c001814001c20380070300c000781d9210407070858292403003820600030000d1054042010b4404030b52050700850400c0b0124090132814041d40c190360038103829003140244a8140c1a000c2c00301c4142268594103030700030b25405420741900c0322003c6030030a0408516400d0482065200300d901c0103031a91981840030910440c1c40b403450068007140542c07450710244041180140c0082480b03a07540d054039614509111011200140c02c450054207500b80c2c00012940020075a28 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 218861285 1250 218860035 218860039
    0x140f04020d08041d0712050108060712060302091f06090509070c02030c0a0603020a090608090706112a0906010c0b010312170c042412020906040506030a051f080705 72
    0x242038242402c0450140c090360740b0040c151a1040083c0380000020035005010780c140361108000c0030030300c1e5000c40c2500c174240521040c070740c004800554524840c0c920100d1001d1105400540f080d102e0700441c3c1c0aa40c215000d030014401400010403009080744400c00601d140d1a0214035141010001303240c0200c0600740004100c1590090760030341d503041c064000c13400b41c01800d000100d03070b031040040d019420840c0c13a070000c5146100300090035800b40740703550721541d02c0300c02038107105080c030205aa0503040c1e0000c44419200d0550740c03250120074010030300c4450003560440f034283d40401c010010400c00c01080e00e4100681c1c655440002400300fa03500d810350703900107155a103410300b1740811a058003500340c80d64580c10760101804000302a8100034025140c001c0760b840e0ba820715407502d0b8400d140c003010003800051800407403560100700c00d5010b0500d51300300030030840c80c0aa075a00000c00035081034900f07112055991050180703040b8041c040100c01c1c80011502c55405140202081d180c03511171050324 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 218862535 1250 218861285 218861299
    0x90a020607060b060d0b0901060c05030706020c030c060a02090a0f03020616140a06020304050d02190605105d1406040c180207200a05090c0706140f0402 67
    0x104011500803d4028201500b07082c0c5800390f07580000050070b03500d803001d8020030141002054a6100d0042015010340020003186041c0c3c140e510507000358055030910556000600ca0a51644010310585000d050804070140c0c4440294040141c540704550200786405c0700d4590420060719079400355a9450b440d0043c1c0741c202d10140c01d20700d9036a00c03a800303e0740c05401503000c4c000800801350302541c0290301440459403250040102645d0343d48003580c003441c2803024440034400003011078000c1940101c2c03d1007000d428540d903140d03280070b80c200c4050501a022483d12030400814010201d1004c0020706003510840b480d2100303d44510f1420081034800028032025480140103e0b030b88120f042c4031021003101e030f013480c150901c411440303602d0140e0740180132028120480402c09000341c4d91500d4110004051017034519006582000c140003115401114003003000649035544544a840b17807003640407071079407202c1916201040300c004c403c10400c083c070418103100030f02c0014480158082d5050381e1038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 218863785 1250 218862535 218862547
    0x40b1b03011211220e010e070614031806010e1f030c06050a020a170702011e0206060f0d1b140402070503071b0902030106091a09030604021504080106140307050306090a0206 76
    0x40341403201071300b00700c0503100b10040040d00400403540c072091400d49005c00030012610002801c54680c201e911511000501c2c0f210b10314102c18442e00250b41003123440c102c0401c480142220641420803d03407250510550300401c10480c10781442e0114150b01c01342c036120242e04e00719039480d400d1072954000c500412401140c1c085446008200c0181169004248210361084043c203800c11275000c2e95089001800c540d516040400c0030548070410950a0313005000c00390743e84028040c280400b02c00309940711007510700e010041100801a501d00842c20303003c4070809070034104844504544100010f001d41e00c1004220040785004c8291910164054200000580b1005184d104111103070031003c3c00a100100005080b80c2011103102124030311b64203003081c0b80e0300c2001c02e1414090200020303019001400001c0c01840c0030b240d4144450352004403039080c80c0c1c40d070192508484c60340d001060b410b503581030840490b00e000c02c071031802000300301c0003080b65140003450300c0e44400324024028010440400c4c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 218865035 1250 218863785 218863789
    0x70309050108040f2d080a09060c08090409060f0f090303060b04030c090507030b122103090c0103111306020a020f1212090d0206072015070816020306040b1b03011211 73
    0x1703817440c008480b5801030940c40b146d080c008110b501c24990003001c074400c1d440c0001c103d4020b884106126401403100383c01c00e00190b080c0030181542c8101200c00d50390f1030038040311705d041501c074181050380b2101000440241600e000780c1140e032290001070803c2c00a0004100040c1104c1c0c03510203a6071a408003050503100d6080680260040d441010350240c949003540702c1e1414009084c602c0c1c0c0390f9003040c440d40200c4410b1540b1091100759440080c2ea080310316807900c1c03540079805c0040c0c0b04140a100918020000c040721035148000d4101e0310041e00b29800c0c03013055152640980400440884d001c1151030803040b00b4070781e2045000c0039130340007081c04504151780e03a507203c0044490030340141c49290340d018275182c0025203019042100d00000d240e510441001c1c2400d0307000d4141454010b000d2840d25403562142012504601a021000000201d150380140c03000e1007a80c0c0104d201e03810f42121802c1c148030101080c40c0071003205680076001e00040058480704800d01080503000102e0941e80c0900c100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 218866285 1250 218865035 218865083
    0x180e0708030a052104030504050f030c040e01020903120a020d080c0d0606030617120301050d060b0301020c0a140102070c0e040305071a09010e010506150f160305070309050108040f 79
    0xc0004224040420b40c0c078807990300708004001c59003006050000c00c03025582410002c0d1410b0354094001403003407005000300d05100c100a1004440103044032498100d59001800352811a1801089a500442d206a203403c0c1000000d1401e2250107a8900340062103a001356950954014a406c0004810201c2d0791088440121042050302e510140f004903141e29000c3d001e804035216070704061040b4482e484c00800007140d90341d0300c45288107200345103910308420003503482d803d410140c0300b15a4034107034000e0b40d94003403000740300b80350b4900054101c070511400c1100248051005140a0342d0040021074005100f5180a10035102800051001a20b032401c040304d60340509200103000c54807a9121202820801031298441d440b010028004180c082003c5800c0e1103082d110300360041c2c15240203aa50461401c0a4030950410195081c01e0000301d41d1620750303040b8054000e40101e10005402400d059020008030054082800e221030a030905a0700c0580c80318035904058800c070510300c02810781c0c2c400b0340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 218867535 1250 218866285 218866289
    0x20d11011b030f0e010e0d060e1e070f050a0f21080a020114011505090f0105160804050f060a0c1403090d140114091209040b06042904180e07 62
    0x3080c007200c07484461502604456085070500089030315120b4141c0258440c115121201d03401809240d144106130f56424058424040341d40c0351400f4601c0e84911012141c2483c0c5c901412003030003080558a003100c0c0e050020180d07080b082c05603c03d07800074007081c14a01808412104c206840400301c034000350047e030390300c0070845000301918800035000d0103076541504125104c450398041811142d0b03a800005083c000c1100d01c10009c15005d01038580c1a103081c02201c9090001810424a8400131510b9003c44001c00d40c01201c08600115041c4241d081c40c1d0030860703a5440646281e45400050400a13010450621004101620f0540907100c03852060083c0c4401d800702a0490380505418a855400040070321402182580303064083d1400d0f01d2001d00150299a08002510030002e04205d02d0310154020b1a0547e007050300c62007100055241c0c6030040000700000350301031400c02007141b1521040c50440c100c02a00c0d41e0144814010f031900c441c2c2e0710142008400c400691100c108148505040141d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 218868785 1250 218867535 218867567
    0x4150e060301180515011b1703040503031501020c0901150c08030a06090506090402010f08070c1e05010f0603051b040f05090319090605040314010e06040507090b060304020d1101 78
    0x400000f42d4814981942d46040900a4003800741c1e0761180c1104c4581c000d084c05142c006032a00384940303600c41d1340d0980d010300c060082110510042440c100f00c9040d52081d60221101c0e440041041004c4126103140305041c1d030244080c1c51070307410b803500140e42803106014607003080341a234148000d418000c11040201d240c3c00000d06c0d450386460f0440c880148400d1107410509400c0000040c402d281c4525000c0c8074a0b030584410403112802e40f01203c00700f000074160014004080c00c6c10010804015203800c0309082248050700c2814a03150140c00c3d030315400c1c00300ba4440c1c01d0003004d000144000c10b0a80101c051800c01e02d40b10100c450026020301007600303913103541a1805051245000000c40200b0360310b4500f151810150203403030800c035601b8141c2d00c242d60000340117020074000120a00650141075940c2400422108030a8a00c80e040c2141640c084545600480741000b03036a400e03014084a4071030440301c06003949001e4021800c55a00490020988d080c00d8500000386d03800342d0750300401002a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 218870035 1250 218868785 218868787
    0x705120c100c03050712090203070605090105120f010501120e070b0903010204030b010e0a060b040803030a02030703090b16090602030f04030210020109050729070218040c0b0a1809020301080304150e06 88
    0x28800003e80108001e640c1940003458060081c00070140394050246040d5010f0002c216440c600780e02195150442401d1710304004042161a071040c5020411501504207902c801001d94500300c00036041e407941924800c80740c0e040c00c2104002150104088048546c03441910f6500c10000700003034028419500000c05540440001140e003618440300940b02d0011075034104001342e154041c103e920f00841c4a120100c4d442040007420f224a0f6802844e007288950402244003009603455081c508011101b025200c00c000d107210503821380c403000c4e4030020515400510314012100240020354800c50001a000780b00302001d00003194801d40c04012116044000e40314140d44808142420819040e8803450501640c503954892401c407401700c548065005104041c02d01500c41c14242140e0001c0054981d400e408000150200c0184000c2900c3c0007075546d6110f503400d18101c1001d01c4481504030300d0b0345a206100522091034004104c4041e60040c0ca0020354005000d24111506941c900300e403600800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 218871285 1250 218870035 218870051
    0x5060f0a06020c040b040b030d05070c150e130615082a0406030c020c0a030f050a081c060f060804020d08090a0b12060301090309150507170705120705120c10 69
    0x242c082685446040704a405000031088041000181c030f203000051649a00214486d40e6201e02030001003280910038414274a50503950f00700d00c1e0000c6c1540c0c102c0300100c1e2a148102d022440e1a0190300c00400740046c04110f4281005000103000c40d203410f070792050104003004506504c4000342c6003d0200d1180d100d221543c404d52268a0f00c6801c180301d02000719003443c8080c41118004074a0b402c5164014100040607860b680b600010915040740076900b0f4010490b122002c110048014081071007a58900204105510b00000884a055002c9000054a00000d12131b040e4031172891500103404446825160742c0c6030900c0303441c40c0300e840c40c00c1c0c0e03100b80448070001d0746441e003c024284840d020003d81403550f444a050500703a4018200040002e01f031260148643d10340a0b5031410142031524185003400141d03940e9825040400d00c0c07180c1d106401188182c00c101301001080c0f00340b608001e01e242400c010380d40d590b555640300007081c4c0e00940080b5a0074151101080107800a41d03d035501440504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 218872535 1250 218871285 218871287
    0xf0c03050f15041502071401060e2202030307030302030601090e041208070815010f050c06010b0304050105071b12110d0305040b090109080912030f0d0f060608091005060f0a06 77
    0x44420780d444181c094810229008003405940a2042d80c011030b110094500d45801070000b5404914200d50024808800c00040701c4240b003400040e22164841d041301d410f040b01c04c1a0403a030381310102103241364620005401610f004c03098031a929414100541c8030340301c1e0070050780c4000080d0050720300204404100024000e203c80f181403481030540301c6601c152204881141d10142c1256064091114100c4910042d40300d035100e40d03d80340b428a012401c0151005466083c1902a40f1182c040e440100a103c01c5c04820302c54580c00850742d081203080501803030508402c410702d500d00940303140110000c4229050050001c10400740c060026180c171025040d101400504080c1c40a0b95001c0003038000450941d01441042da01e29005407280741810030310380401c02d4400103220400300310701041c0410400a000da40c05040002c1c0300b020003150070003690304004c048521075405901044041420301c0000c24001c90505c2820440c510041000c0d6268400308408500340030015801092510002801c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 218873785 1250 218872535 218872543
    0x1b1804060b040507080402031e011d01021c06031524091407031e0207050102090406030c150e0109140409021201020d0509060907061101090503041503050a05090c0d0f0c0305 76
    0x6410840301000f254803268011954400c4c2200d009415500c100e20012185d054480502c4400e50040008a031007880300c1c440142c01048006008816034002c51b00d40058601704881c030f281e541319020b04125407482d50301c40c0d421800c6003d01c4456619507680c112059000c001e10003241c014074251a254a255450841500a15076200f441e6603110f141000b08010500c00d000c1c000040d02040110100c500f1109203250003503000c075000300c0d040e40d820803800306107132203034000d1900541c0a986100703201c030b01d849444a00e1000b032507030000410500366447c03211a0381120000e0240e610103146400905140c0000c280240b5881d000030303601006951f010340000405400401200b091181c0900c040e0b11915410340e0b50301019030300450103403c003910134013807940300f02d01c2c1c240c001d0312140c00414010b42c1c50311a54107590054110100c5020034040205681342c01d07000b07a9412805040d4108481c0c9858640c050b146c400700510184104824803072007041c404401030854003113070000c401090071a503e2030141c0d03035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 218875035 1250 218873785 218873801
    0x70c0303140c040e06090c0f0c0319020705010f140412050309030a060209030c0d110603070215010b04151b1e06050c09040b0303030709090b15070320030a021b180406 73
    0xc140f0300c001400e5050070601036010b41c0090b4001400c000c0e0b58200354200741c204040b2703104944410f105001808514485440303907002c40da0040c00c011820840010142c41c0342c071940c5000d00041030008400b241c2920100c400f01d03914200381c540525040c4c90300c64114820300c40c00702c1d81803064801b464217125059004080c0c489044003181c11211502080c0507100c07454007400b4024003004c000d00309960501000941d070044c02c074410788030410b82404221ba5910003e1704094203180c0b021800703201100d0b1150b40c400141400d402c0c90740c0080104011507120300c005c814003c201422104098590071100b1000900441c0e001105000314a060b292010b00d0b84c02c20b500f003e218508208240082e0308010044902801080d580d0446041c104aa078002a0101c00c5007150000c0311440c0007c04003000b05d0150250070320a0b07448102c504415603448506a1047c0000b0343d5a41041003510306241d0000b91900d2503c0821508402a100d800e001940507402c050503c0c00ca085203100704020050b0700c6d84034201c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 218876285 1250 218875035 218875049
    0x81b031810060e060d0606030f0803070e043c060314060c04060c1b0302220b0a060f0e03010209031c0201060b04030f02041e0e0a1502030906070c0303140c04 69
    0x1440000d001107007068802c24414112680c2d10440401d40c0760400154259400c0c0c0170b2040805c00320b64907540e881144165040c10f59a500010090042030b60f40511100301340319088030144455442402134030400c00440d12580180407214070704e180748440c0307880440c414840100c000c0050aa0701c0c2001d84440043e000300221a009080004415903498010348042c2c0da466691451120f42c103590340301007a80040d41041c8044070307600d000030041c0d99444024095403015028800355240d0301036050162020400414410310020740c09000c01540119132003402c2c0800c0c50140c0e20000345c44082402032080c40c48031501405100b041c0560b85840505c0300341c582c581035000f086400ea0355404001903002c2c501008102591003c4002c02624103904014180c21101811032003800d2003584050484460b1a068a0590000b284242c14016101024402c9a0540c5400c1d455071810f54952521904002d01030414032208030300c0355060510070342c0a89054240e01d40803008a040c101032640403030300140303c2c1b02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 218877535 1250 218876285 218876293
    0x20a0f0807091a0d030909060320030604080a030f09020604090e0d1b0b091009120f081509130b070210060b070309030204050c09090c041703040f06081b0318 69
    0x81c140394540f00d0508032841c0080c600c00071882035010807000029446066041000d0103402141c5003070203118442c000c0d446041c8100c015400c03850b1030081400309540d103078403c0c0c0140d0704200100391800111000903416141c0043c0303410801e03052a0007008030181c0a504500041401700360403400d94000b4030741941d1902140d94142c902c5000f01e07900210300c3c40000d910250f401c010000a00c00803145500102c1950076a044e2a83c054104001c0701e031240d00a40780300f0018540006015009040d0040036040c600c1d20284d40d140c680f4128400041c00380740715000c3c41e9640000340888004191003817813154402c507503440700d04010800954540742140b2107003181c1d24104c8005180b02c81e10b0704481d031890b80344c1c43d03010b1000c0c0b41d6000c11000b08030090040030041804c202140d425a170f00300303400b44110b06041503903440304c1c02c00c01d0102101035800b03c2d40c0e036164000c002c02d00c001050035010800301c801d02d25001c2260350f075040400c00f000c2c0201e508880130a002005110900500b01204148040d00208039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 218878785 1250 218877535 218877539
    0x100b0d05211e03042a090f020c010c02070e01050a050d23060f0a05070e030a03031a032410081c0201020d02120402101818020705030a17010b0901080f0405010603020a0f0807 76
    0x6204140e015502d2030485071750001c00b004561807a8008180800355141c0060800b142400d00b542554501d00c510320060b00520301c00d00c12200070a034a103001d40000e81e10501d0031405d1601060751309468140c09402080038440300003024130002010315a00c0e841c8000d4440d0313802e040000103072602d02550250420b42c20400003440481c42242c80807981c0a005009000e041c6c41500c06400620910b07680a030b001c80e002c0c000072001d40b01003103c941ca10112020070000d803290804d03c51503a8102070101c03135050042c20010400100001041c040304d8030346a030784071010b40031f01c5c000340e00a22500520203030a50020414004440c0c090001c1031103140290b4114403c1401d0f000115070700140d44903072041b0400c40000903c2804e00b05e580004041052003001440e000345900c0e41407039904092a0a40044c0030f0b004101a044039035020a401440403002d4107040410810000e05070360030080c003503551300010100107001d026003500404011500039080e641031544030814048008024001c105c540d200c0c0c6500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 218880035 1250 218878785 218878823
    0x90308090f15060607050c060a17060a030f02060d060906090606120902010504060c030504030b01080303011707030b0406050c09040509030414120d0e0a1502100b0d05211e0304 77
    0x240000b0041c0301c2c0030500b26940d09010000a9080901c0584061060a0f154159900c40d9030080102d1007590f2960802e00541c2140c1b020706000c01040c02d4098114400c0400018104110852110b581201c1c0135449202c0b1481a8005000c513501c600c04040c10100e00040e92038250b44403506840c201c1c0da500170503a4000401005517082824006c2c0055010803003080f80320311840f41d15810b240300c0d25010f0b01c4c2039541e85031486181c0080e00022016080080108071350002200203880313400756030b005844c0051031920b40d4012100d00800150400d601c5200107140070130b04408442c00c6403001041004507081540100c0d680b41c010f4000c00b42a9400c281d4148401d2030481c002c06241400a4014010248151300441e41f032100c0c0c8000d5600010004008203008800300c000140d604095401000c2c081d2440300c0000544241440c40d42c003c1480e0810038010440104100701403421400c2001c04050300910420660304c070f100b50328611109600b485940c50015400154042c5000e0490380c0900748203140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 218881285 1250 218880035 218880043
    0x18060f0b01170a06090e010605030c01020616031109120a0341091309020f04020a020607080903040b04060503101d0a0e0c0405010b070219050130090308090f 69
    0x501e000c0303480c0101d0078210790300c2000d106a0200b003510b400f20740255110520b00c02c0e034410010388010750351100801e0246007401c00981b18050000d1006040c0750904038000d50001c4070880700d51080607201d1050b800001c991104030764081c6030150442040312041d118039916034aa40000b100000c02080000c4c1422b81c0e8070b0a2070045a400c00c011004034064064074403103250172500618140b100c01d11245d100d0380d41f5007985013212028404080741e1203415104005045215a0106c2d103d10320600048805581c00503030103a100740030f400c0044d400d031a11031441d482c50103698460f01940100040203d2001e80c0f09016500034051200c0c0080d225881c0c0c0a004e516805601115440036808000100140d800740c000c200e190a0001c203880391490050081402d80344c0c241c101d03041c9034100040d02411420600b41010440c0d0f2030f25642e05610342410b0000707168002c2103501c4164100c1d9603480c1c000c0c040300500c0105c900d20044004202c00c2c4081d1501414000781212030303040a02491243c0b680b9150086 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 218882535 1250 218881285 218881301
    0x72703150e010507050414130b040207080705010c0507081210150203040501030510050102120d181406130c06210c030b030d030204120b040809130506030c0117010e091018060f 77
    0x1c040e100c010220781070007214080391060303610089d104e00d29a1000e03203985c8000e00b1003500035500a559001c3c20b041c99400d5030f104264031010008100100b0010501c81d900f6036506030070b0386228000c0c980314034400e00b8003860b141d00640710900306482c0e0141c031103400000403c1125401e8909001c159130701481092040c5031303071103000c2c00341e0403400c0031844580c451b40c002d00090312207240000d06000416105d228030780140e481103421803003601c80600504020004d00e40d102e09141107480389801c00e9030301e03440101c0d911303c01d940034040c00b81804408419241c50341036504032840740070084a007206000030054060440c245000c0c0c061014000241031007402180c080d110b0500e4030b10b0b01c0e415240d0715000300500003030040d141c025091110080940d102c05280940c616039031804900c40c20600304040c10002c156600c41c0c18802250200402c0c47d120503181e5045179400c4800c00c84075a9403122582c14031038050b5940b042c80745010305808041e0354503202c80c241030340188020482850241c1602c001c480c450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 218883785 1250 218882535 218882549
    0xf0c01080c040b1e0403050601062a14010b0d12080c03040c1202010903050f060a060801060e010e04060e0d0c0c170303151c0803011409072703150e0105070504 70
    0x2c020074442c00541d030b001041c9100100b19511462604032180640c150426007003110103400c07020040181651002100740203a04802143c2c901c85000701a280c600203400600400d20761003400c11a940301000c1d4008142c90901421400100259103821b180d20321010803400e001c5551030010501c68850141601d100341d40c400d0018170510f0034900d402002e521b074074000700e041100100700403000403000c5c810420050461740040003981080d0110300140d030f4043e04160066854107500300001441c041c2c4080c1100c400814000d295203132820054060000482e04040d10701c104680c5140f81c0764007070103007088240039410034a280c03500d840c02c1508a61415442048552007407002c00c110440b1070f01e00001d0040010044104102e40c0043c0c40c0d400740744039200740e03803080c03010004000540c0c040592220101e4100e13000c40f020f2400d0403002d461608507515010a03c0c0460400720710500903084e400b03010b540c010310008a219401d0342e0000142044407a09a501d50900002c11011170240060710300751204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 218884892 1107 218883785 218883787
    0x307081c06140d02010309020613060203040608071b0b1015050a02010e030c060f0a0609020f1c1a0103020a170a0c0908060c030114010e03010e0f0c01080c 68
    0x30740b03501000c89070410000a044660b100a20380090b1542400c00040d2200c15002140d100d0007405c0e000b107042d80340c4450205182c0d0f0000058000c407800c1c0d0f41d4590490f51010b81c01c640c0b01c841181480c10030314040d01c80000007008180c1ea1517002141d00407001140c1c0e81c60210300700b038191000c541c0011840000d802c401d02c960a0190144d0a040e17000210f241545115a10b56180c03802810703400c504c84000041106024180c00440051183c04820b43d214040303032008401c0b56000e040c41141d4aa4007607640c0d84024001c0c001c2c1501d40345420382c85880015100300642c00395105c0c1000f00b007084440809030300e10403e003004150081c49040b4002070aa1944900602001c202c0d400c28940d0fa0710082c05c1020802e2603c04030780c159215200180c2801042074010703110140d4608503a503043d42444c041036045c14002601029a01440044801518a000c01506c04e240160785110f24a50 = true := by decide +kernel

theorem cover : BRFrame.Cov 218705035 218884892 := by
  have h0 := BRFrame.cov_init 218705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 218705035 ≤ n) (h2 : n < 218884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
